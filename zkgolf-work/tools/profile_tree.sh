#!/usr/bin/env bash
# profile_tree.sh -- find the most expensive declarations in a Lean 4 project.
#
#   usage:  ./profile_tree.sh <project-dir> <root-module>
#   e.g.    ./profile_tree.sh out/sha256-hash/sha256-hash_aristotle Solution.SHA256.Main
#
# Produces, in <project-dir>/.prof/ :
#   modules.tsv    per-module wall-clock, slowest first
#   decls.tsv      per-declaration elaboration+kernel time, slowest first
#   phases.tsv     per-module phase totals (elaboration / type checking / simp / TC)
#
# Requires a completed `lake build` first (so imports are cached and we time
# only the module itself).
set -uo pipefail

PROJ="${1:?project dir}"; ROOT="${2:?root module, e.g. Solution.SHA256.Main}"
cd "$PROJ" || exit 1
OUT=.prof; mkdir -p "$OUT"

# ---------------------------------------------------------------- 0. warm build
# Everything below times a *re-elaboration* of one module against cached imports.
# Without this you measure Mathlib, not your tree.
lake build "$ROOT" >/dev/null 2>&1 || { echo "baseline build failed"; exit 1; }

# ------------------------------------------------- 1. enumerate import closure
python3 - "$ROOT" <<'PY' > "$OUT/closure.txt"
import os,re,sys
root=sys.argv[1]; seen=set(); stack=[root]
while stack:
    m=stack.pop()
    if m in seen: continue
    p=m.replace(".","/")+".lean"
    if not os.path.exists(p): continue
    seen.add(m)
    stack+=re.findall(r'^import\s+([\w.]+)', open(p,encoding='utf8',errors='ignore').read(), re.M)
for m in sorted(seen): print(m)
PY
echo "modules in closure: $(wc -l < "$OUT/closure.txt")"

# ------------------------------------------ 2. per-module wall clock + phases
: > "$OUT/modules.tsv"; : > "$OUT/phases.tsv"
while read -r m; do
  f="${m//.//}.lean"; [ -f "$f" ] || continue
  s=$(date +%s.%N)
  lake env lean -Dprofiler=true -Dprofiler.threshold=50 "$f" > "$OUT/raw_${m}.txt" 2>&1
  e=$(date +%s.%N)
  printf "%s\t%.2f\n" "$m" "$(echo "$e-$s" | bc)" >> "$OUT/modules.tsv"
  # cumulative phase table is printed at the end of each run
  awk -v M="$m" '/cumulative profiling times:/{f=1;next} f&&NF>=2{
        t=$NF; u=1;
        if(t ~ /ms$/){sub(/ms$/,"",t)} else if(t ~ /s$/){sub(/s$/,"",t); u=1000}
        name=$0; gsub(/^[ \t]+/,"",name); sub(/[ \t]+[0-9.]+m?s$/,"",name);
        printf "%s\t%s\t%.1f\n", M, name, t*u }' "$OUT/raw_${m}.txt" >> "$OUT/phases.tsv"
done < "$OUT/closure.txt"
sort -t$'\t' -k2 -rn "$OUT/modules.tsv" -o "$OUT/modules.tsv"

# ------------------------------------------- 3. per-declaration attribution
# Re-run only the 15 slowest modules with the structured tracer, which tags each
# declaration and separates the Kernel node from elaboration.
: > "$OUT/decls.tsv"
head -15 "$OUT/modules.tsv" | cut -f1 | while read -r m; do
  f="${m//.//}.lean"
  lake env lean -Dtrace.profiler=true -Dtrace.profiler.threshold=200 \
       -Dtrace.profiler.output="$OUT/${m}.json" "$f" > "$OUT/trace_${m}.txt" 2>&1
  awk -v M="$m" '
    /\[Elab\.command\] \[/ { t=$2; gsub(/[\[\]]/,"",t); d=$0;
                             sub(/^[ \t]*\[Elab\.command\] \[[0-9.]+\] ?/,"",d); sub(/^✅️ ?/,"",d);
                             printf "%s\telab\t%.1f\t%s\n", M, t*1000, substr(d,1,90) }
    /\[Kernel\] \[/        { t=$2; gsub(/[\[\]]/,"",t); d=$0; sub(/.*declarations /,"",d);
                             printf "%s\tkernel\t%.1f\t%s\n", M, t*1000, substr(d,1,90) }
  ' "$OUT/trace_${m}.txt" >> "$OUT/decls.tsv"
done
sort -t$'\t' -k3 -rn "$OUT/decls.tsv" -o "$OUT/decls.tsv"

echo; echo "=== 10 slowest modules (s) ==="; head -10 "$OUT/modules.tsv"
echo; echo "=== 15 slowest declarations (s) — col2 says elab or kernel ==="; head -15 "$OUT/decls.tsv"
echo; echo "=== where the time goes, summed over all modules ==="
awk -F'\t' '{a[$2]+=$3} END{for(k in a) printf "%10.0f ms  %s\n", a[k], k}' "$OUT/phases.tsv" | sort -rn | head -15
echo; echo "Firefox Profiler JSONs in $PROJ/$OUT/*.json  -> load at https://profiler.firefox.com"
