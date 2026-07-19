#!/usr/bin/env bash
# Rebuild per-challenge Aristotle project dirs from the challenge repo, seeded with the
# current leaderboard record, with the dependency env correctly pinned. Idempotent.
set -e
cd "$(dirname "$0")"
source env.local
REV=041c6e7ebc06f5cbfd534c2a19c4120f3de62435
[ -d zk-golf-challenges ] || git clone --depth 1 https://github.com/zksecurity/zk-golf-challenges.git
rm -rf proj && cp -r zk-golf-challenges proj && rm -rf proj/.git proj/.github
declare -A MAP=( [assert-bytes]=AssertBytes [sha256-hash]=SHA256 [keccak-f1600]=KeccakF1600
  [rsa-pkcs1v15-sha256-4096-65537]=RSASSAPKCS1v15_SHA256_4096_65537
  [secp256k1-scalar-mul]=Secp256k1ScalarMul [secp256k1-fixed-base-scalar-mul]=Secp256k1ScalarMulFixedBase )
rm -rf projs && mkdir -p projs
for slug in "${!MAP[@]}"; do
  inst="${MAP[$slug]}"; d="projs/$slug"
  cp -r proj "$d"
  for sd in "$d"/Solution/*/; do [ "$(basename "$sd")" != "$inst" ] && rm -rf "$sd"; done
  rm -rf "$d/Tests"
  python3 - "$d/lakefile.lean" <<'PY'
import sys,re; p=sys.argv[1]; s=open(p).read()
s=re.sub(r"lean_lib Tests where\n\s*globs := #\[\.submodules `Tests\]\n","",s)
s=s.replace('require clean from git "https://github.com/Verified-zkEVM/clean" @ "main"',
            'require clean from git "https://github.com/Verified-zkEVM/clean" @ "REVPLACEHOLDER"')
open(p,"w").write(s)
PY
  sed -i "s/REVPLACEHOLDER/$REV/" "$d/lakefile.lean"
  python3 - "$d/lake-manifest.json" "$REV" <<'PY'
import json,sys; p,rev=sys.argv[1],sys.argv[2]; m=json.load(open(p))
for pkg in m["packages"]:
    if pkg["name"]=="clean": pkg["inputRev"]=rev; pkg["rev"]=rev
json.dump(m,open(p,"w"),indent=2)
PY
done
# seed with current records
uv run --with requests python3 reseed.py
echo "projs rebuilt with clean pinned to $REV and seeded from records"
