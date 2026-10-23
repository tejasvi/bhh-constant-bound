#!/usr/bin/env python3
"""Claims for the native shards from C PHI lines (computed with Lean's T classes, W3TLOAD), with relative margins.

usage: phi_to_claims.py PHI_FILE OUT_CLAIMS DLO DHI
  PHI lines 'PHI k j mantissa(%a) exponent' (value m 2^e); claims 'C j k loM loE hiM hiE' with
  loM 2^-loE <= Phi (1 - DLO) and hiM 2^-hiE >= Phi (1 + DHI), 64-bit mantissas, exact rational rounding.
"""
import sys
from fractions import Fraction as F

def main():
    fin, fout, dlo, dhi = sys.argv[1], sys.argv[2], F(sys.argv[3]), F(sys.argv[4])
    out = []
    seen = set()
    for line in open(fin):
        p = line.split()
        if not p or p[0] != 'PHI':
            continue
        k, j = int(p[1]), int(p[2])
        v = F(float.fromhex(p[3])) * F(2) ** int(p[4])
        assert v > 0, (k, j)
        lo, hi = v * (1 - dlo), v * (1 + dhi)
        def mant(x, up):
            # x = m 2^-e with 2^63 <= m < 2^64
            e = 63 - (x.numerator.bit_length() - x.denominator.bit_length())
            while True:
                y = x * F(2) ** e
                m = (y.numerator + y.denominator - 1) // y.denominator if up else y.numerator // y.denominator
                if m >= 2 ** 64: e -= 1; continue
                if m < 2 ** 63: e += 1; continue
                return m, e
        lm, le = mant(lo, False)
        hm, he = mant(hi, True)
        assert F(lm) / F(2) ** le <= lo and F(hm) / F(2) ** he >= hi
        out.append((j, k, lm, le, hm, he))
        seen.add((j, k))
    js = sorted({j for j, _ in seen})
    for j in js:
        for k in range(3, 23):
            assert (j, k) in seen, ('missing', j, k)
    with open(fout, 'w') as f:
        for (j, k, lm, le, hm, he) in sorted(out):
            f.write('C %d %d %d %d %d %d\n' % (j, k, lm, le, hm, he))
    print('claims', len(out), 'j', js[0], '..', js[-1])

if __name__ == '__main__':
    main()
