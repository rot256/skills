#!/usr/bin/env bash
# Two-stage declaration-level pruning of the flattened submission.
#   stage 1: closure computed in the full project (seed loop for textual keeps),
#            pruned package built in the isolated project, unused-list fixups applied
#   stage 2: closure recomputed inside the pruned build (drops dependencies that
#            only existed through shared auxiliary proofs), pruned again, rebuilt
# Usage: prune_pipeline.sh <scratch dir>   (expects out/varbase-submission to be current)
set -u
export PATH=$HOME/.elan/bin:$PATH
S=$1
ROOT=/home/user/skills/zkgolf-work
MAIN=$ROOT/projs/secp256k1-scalar-mul
TEST=$ROOT/projs/dce-test
TOOLS=$ROOT/varbase-port/tools

seedloop() {  # $1 = project dir, $2 = SRC package, $3 = OUT package, $4 = seeds file
  rm -f "$4"
  for it in 1 2 3 4 5; do
    (cd "$1" && DCE_EXTRA="$(cat "$4" 2>/dev/null)" timeout 900 lake env lean $TOOLS/dce.lean 2>&1 | grep -v "^warning\|^$" | cut -c1-160 | tail -1)
    mv "$1/dce_ranges.txt" "$S/ranges_$(basename "$3")_$it.txt"
    out=$(cd $ROOT && DCE_EXTRA_OUT="$4" python3 varbase-port/dce.py "$S/ranges_$(basename "$3")_$it.txt" "$2" "$3" 2>&1)
    echo "$out" | grep "seeds\|deleted modules\|kept modules" | cut -c1-200
    if echo "$out" | grep -q "seeds: 0 new"; then echo "converged at iteration $it"; return 0; fi
  done
}

buildtest() {  # $1 = package dir, $2 = log
  rm -rf $TEST/Solution/Secp256k1ScalarMul && mkdir -p $TEST/Solution/Secp256k1ScalarMul
  cp "$1"/*.lean $TEST/Solution/Secp256k1ScalarMul/
  (cd $TEST && (time lake build Solution.Secp256k1ScalarMul.Main) > "$2" 2>&1)
  grep -n "Build completed\|real" "$2" | head -2
  grep "error:" "$2" | sed 's/.*Secp256k1ScalarMul\///' | cut -c1-150 | sort | uniq -c | sort -rn | head -20
  grep -q "Build completed" "$2"
}

fixloop() {  # $1 = package dir, $2 = log prefix : build, apply fixups, rebuild (up to 6 rounds)
  for r in 1 2 3 4 5 6; do
    if buildtest "$1" "$2_$r.out"; then return 0; fi
    echo "=== fixups round $r"
    (cd $ROOT && python3 varbase-port/fixup.py "$2_$r.out" "$1" | tail -3) | tee $S/fix_$(basename "$1")_$r.txt
    grep -q "^fixed" $S/fix_$(basename "$1")_$r.txt || { echo "no fixup applicable"; return 1; }
  done
  return 1
}

START=${START:-stage1}
if [ "$START" = stage1 ]; then
  echo "=== stage 1"
  seedloop $MAIN $ROOT/out/varbase-submission $S/stage1 $S/seeds1.txt
fi
if [ "$START" = stage1 ] || [ "$START" = fix1 ]; then
  fixloop $S/stage1 $S/build_stage1 || { echo "STAGE 1 FAILED"; exit 1; }
fi
if [ "$START" != fix2 ]; then
  echo "=== stage 2"
  seedloop $TEST $S/stage1 $S/stage2 $S/seeds2.txt
fi
fixloop $S/stage2 $S/build_stage2 || { echo "STAGE 2 FAILED"; exit 1; }
echo "=== done: $(ls $S/stage2 | wc -l) files, $(du -sh $S/stage2 | cut -f1)"
