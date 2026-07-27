#!/usr/bin/env bash
# Rebuild the zkGolf loop runtime (projs/records/prompts/targets) from the zk.golf +
# Aristotle APIs and the public challenge repo. Idempotent. Requires env.local (keys)
# to already exist in this dir. Run after any container restart. Location-independent.
set -e
cd "$(dirname "$(readlink -f "$0")")"
source env.local
REV=041c6e7ebc06f5cbfd534c2a19c4120f3de62435
[ -d zk-golf-challenges/.git ] || { rm -rf zk-golf-challenges; git clone --depth 1 https://github.com/zksecurity/zk-golf-challenges.git; }
(cd zk-golf-challenges && git fetch --depth 1 origin main -q && git reset --hard FETCH_HEAD -q) || true  # pick up newly published challenges
rm -rf proj && cp -r zk-golf-challenges proj && rm -rf proj/.git proj/.github
declare -A MAP=( [gf2-k12-compress-canonical]=KangarooTwelveGF2 [gf2-sha256-compress-canonical]=SHA256CompressGF2Canonical [sha256-hash]=SHA256 [keccak-f1600]=KeccakF1600 [rsa-pkcs1v15-sha256-4096-65537]=RSASSAPKCS1v15_SHA256_4096_65537 [secp256k1-scalar-mul]=Secp256k1ScalarMul [secp256k1-fixed-base-scalar-mul]=Secp256k1ScalarMulFixedBase )
for slug in "${!MAP[@]}"; do
  inst="${MAP[$slug]}"; d="projs/$slug"; rm -rf "$d"; cp -r proj "$d"
  for sd in "$d"/Solution/*/; do [ "$(basename "$sd")" != "$inst" ] && rm -rf "$sd"; done
  rm -rf "$d/Tests"
  python3 - "$d/lakefile.lean" "$REV" <<'PY'
import sys,re; p,rev=sys.argv[1],sys.argv[2]; s=open(p).read()
s=re.sub(r"lean_lib Tests where\n\s*globs := #\[\.submodules `Tests\]\n","",s)
s=s.replace('@ "main"', f'@ "{rev}"'); open(p,"w").write(s)
PY
  python3 - "$d/lake-manifest.json" "$REV" <<'PY'
import json,sys; p,rev=sys.argv[1],sys.argv[2]; m=json.load(open(p))
for k in m["packages"]:
    if k["name"]=="clean": k["inputRev"]=rev; k["rev"]=rev
json.dump(m,open(p,"w"),indent=2)
PY
done
uv run --with requests python3 seed_valid.py
# Cross-pollination reference gadgets (donor sibling-challenge .lean, context only, not compiled).
# Must exist BEFORE gen_prompts so it emits the CROSS-POLLINATION directive for these slugs.
MSOL=projs/secp256k1-scalar-mul/Solution/Secp256k1ScalarMul
FSOL=projs/secp256k1-fixed-base-scalar-mul/Solution/Secp256k1ScalarMulFixedBase
for tgt in projs/rsa-pkcs1v15-sha256-4096-65537 projs/secp256k1-scalar-mul; do
  mkdir -p "$tgt/reference"
  for g in EqViaCarriesFlex EqViaCarriesFlexT GroupedFlex FlexInstances GroupedFlexInstances; do
    cp "$FSOL/$g.lean" "$tgt/reference/$g.lean.txt" 2>/dev/null || true
  done
done
mkdir -p projs/secp256k1-fixed-base-scalar-mul/reference
for g in GroupedEqXV GroupedEqX MulModTargetW MulModVariants; do
  cp "$MSOL/$g.lean" "projs/secp256k1-fixed-base-scalar-mul/reference/$g.lean.txt" 2>/dev/null || true
done
uv run python3 gen_prompts.py
mkdir -p projs/keccak-f1600/reference
for f in records/keccak-f1600/*.lean; do cp "$f" "projs/keccak-f1600/reference/$(basename "$f").txt" 2>/dev/null || true; done
echo "bootstrap complete"
