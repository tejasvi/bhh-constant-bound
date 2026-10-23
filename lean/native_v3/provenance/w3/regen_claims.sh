#!/usr/bin/env bash
# Regenerates W3Prod20/Claims.lean (and Grid.lean, TInt.lean, Nondeg.lean) from scratch: the Lean T classes (TBitsAll),
# the window-3 C evaluator run with them, the claims with their margins, the t-integral target (TintCalc) and the generator.
# Run from the root of the release tree:
#   bash provenance/w3/regen_claims.sh                 the grid (20,10,48); checks every intermediate sha256
#   bash provenance/w3/regen_claims.sh 6 3 12          a small grid (end-to-end test; prints the sha256s)
# Optional environment: W3_REGEN_DIR (work directory, default ./_w3regen), W3_NTH (evaluator threads, default 24; the
# evaluator's values do not depend on the thread count).
# Needs: the Lean toolchain of lean-toolchain (elan), gcc with OpenMP, FLINT 3 with MPFR and GMP, python3.
set -euo pipefail
HERE=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
ROOT=$(pwd)
N1=${1:-20}; N2=${2:-10}; NT=${3:-48}
NTH=${W3_NTH:-24}
WORK=${W3_REGEN_DIR:-$ROOT/_w3regen}
for d in BHHCert W2Cert W3Cert; do [ -d "$ROOT/$d" ] || { echo "run from the release tree root ($d/ not found)" >&2; exit 2; }; done
mkdir -p "$WORK"
cd "$WORK"

echo "== 1. the two Lean tools (core Lean only; built from the release tree's BHHCert/, W2Cert/, W3Cert/)"
rm -rf tools && mkdir tools
cp -R "$ROOT/BHHCert" "$ROOT/W2Cert" "$ROOT/W3Cert" "$ROOT/lean-toolchain" tools/
cp "$HERE/TBitsAll.lean" "$HERE/TintCalc.lean" tools/
cat > tools/lakefile.toml <<'EOF'
name = "w3regen"

[leanOptions]
pp.unicode.fun = true
relaxedAutoImplicit = false
autoImplicit = false

[[lean_lib]]
name = "BHHCert"

[[lean_lib]]
name = "W2Cert"

[[lean_lib]]
name = "W3Cert"

[[lean_exe]]
name = "tbitsall"
root = "TBitsAll"

[[lean_exe]]
name = "tintcalc"
root = "TintCalc"
EOF
(cd tools && lake build tbitsall tintcalc > build.log 2>&1) || { tail -n 30 tools/build.log >&2; exit 1; }

echo "== 2. Lean T classes of the grid ($N1,$N2,$NT)"
tools/.lake/build/bin/tbitsall "$N1" "$N2" "$NT" tbits.bin

echo "== 3. the C evaluator with these T classes ($NTH threads)"
gcc -O3 -march=x86-64-v3 -ffp-contract=off -fopenmp "$HERE/w3_arb_dump.c" -o w3_arb -lflint -lmpfr -lgmp -lm
W3TLOAD=tbits.bin ./w3_arb "$N1" "$N2" "$NT" 3 6 22 "$NTH" 1 48 > phi.txt 2> phi.err

echo "== 4. claims (relative margins 1e-7 below, 1e-5 above) and the t-integral target"
python3 "$HERE/phi_to_claims.py" phi.txt claims.txt 1e-7 1e-5
tools/.lake/build/bin/tintcalc claims.txt > tint.txt
grep '^NUMDEN' tint.txt >> claims.txt

echo "== 5. the generated modules"
PKG=W3ProdTest; [ "$N1 $N2 $NT" = "20 10 48" ] && PKG=W3Prod20
rm -rf out
python3 "$HERE/gen_prod.py" claims.txt out "$PKG" "$N1" "$N2" "$NT" - \
  "the C evaluator of the window-3 certificate run with the T classes of this code at relative margins 1e-7 (lower) and 1e-5 (upper)"

echo "== 6. sha256"
s256() { sha256sum "$1" | cut -d' ' -f1; }
if [ "$PKG" != W3Prod20 ]; then
  for f in tbits.bin phi.txt claims.txt tint.txt out/$PKG/Claims.lean out/$PKG/Grid.lean; do echo "$(s256 $f)  $f"; done
  exit 0
fi
bad=0
chk() {  # file expected-sha256
  local s; s=$(s256 "$1")
  if [ "$s" = "$2" ]; then echo "OK        $1  $s"; else echo "MISMATCH  $1  $s (expected $2)"; bad=1; fi
}
chk tbits.bin              f11e6ed9f2491efb3177c4ea23cb4c500fbc9206d4c2a4a03dd248fb12423fac
grep '^PHI' phi.txt > phi_values.txt   # the PHI lines (the last line of phi.txt holds the run time)
chk phi_values.txt         bf8db7bebac5fd2197d39963cb5d5443547898d82746ec8c46aa7b96666bce75
chk claims.txt             d0dff06b0f72941cd1a0a17def6aabc01eee6515adb674f0feff31129ca8fb38
chk tint.txt               cb5f3b7341016661e49cfd1a689a208ee37baa88a5bb53f102f286e18eff2dc2
chk out/W3Prod20/Claims.lean e7156d0609bc98dee12458e9c01730c12c8109dca8d09864dfcbf234edd6d171
chk out/W3Prod20/Grid.lean   56f451341fa595de09c45353ded79a3be213b5d44539c5041dd51620c713befc
chk out/W3Prod20/TInt.lean   0a0ae6db1158e3885463d71563ef0948a7ecf39b56fe9243499258b8f5e5e142
chk out/W3Prod20/Nondeg.lean e3efd887fb314e5fbd6bb5fd2667a365660f95c9d25879514055e1470b393d3d
for f in Claims Grid TInt Nondeg; do
  if [ -f "$ROOT/W3Prod20/$f.lean" ]; then
    if cmp -s "out/W3Prod20/$f.lean" "$ROOT/W3Prod20/$f.lean"; then echo "SAME      W3Prod20/$f.lean as in the release tree"
    else echo "DIFFERENT W3Prod20/$f.lean from the release tree"; bad=1; fi
  fi
done
[ $bad = 0 ] && echo "REGENERATED W3Prod20/Claims.lean: all checks passed" || { echo "CHECKS FAILED"; exit 1; }
