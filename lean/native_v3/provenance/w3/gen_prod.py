#!/usr/bin/env python3
"""Generate the production modules of a W3 grid from an untrusted claims file.

usage: gen_prod.py CLAIMS_FILE OUTDIR PKG N1 N2 NT CUTS
  CLAIMS_FILE: lines 'C j k loM loE hiM hiE' (and 'NUMDEN num den ...' for the t-integral target)
  CUTS: comma-separated increasing j thresholds c_1 < ... < c_{S-1} (or '-' for one shard): shard s takes the claims
        with c_s < j <= c_{s+1} (c_0 = 0, c_S = infinity)
  OUTDIR/PKG/Claims.lean   data module (no imports): def claims : List (Nat x List (Nat x Nat x Int x Nat x Int))
  OUTDIR/PKG/Grid.lean     the grid and the parameters (dtl 3, T 6, kmax 22, lsub 8)
  OUTDIR/PKG/Snn.lean      shard nn: shard3OK over the claims with c_nn < j <= c_{nn+1}, by native_decide
  OUTDIR/PKG/TInt.lean     tintOK of all claims against num/den, by native_decide
  OUTDIR/PKG/Nondeg.lean   W2's nondegOK of the grid (pair entries), by native_decide
"""
import sys, os, collections

def main():
    cf, outdir, pkg, n1, n2, nt, cuts = sys.argv[1:8]
    src = sys.argv[8] if len(sys.argv) > 8 else 'an untrusted pre-run'
    n1, n2, nt = int(n1), int(n2), int(nt)
    cuts = [] if cuts == '-' else [int(x) for x in cuts.split(',')]
    assert cuts == sorted(set(cuts))
    nsh = len(cuts) + 1
    claims = collections.OrderedDict()
    numden = None
    for line in open(cf):
        p = line.split()
        if not p:
            continue
        if p[0] == 'C':
            j, k, lm, le, hm, he = int(p[1]), int(p[2]), int(p[3]), int(p[4]), int(p[5]), int(p[6])
            claims.setdefault(j, []).append((k, lm, le, hm, he))
        elif p[0] == 'NUMDEN':
            numden = (int(p[1]), int(p[2]))
    js = sorted(claims)
    assert js == list(range(1, len(js) + 1)), 'claims must cover j = 1..ntv'
    for j in js:
        ks = [c[0] for c in claims[j]]
        assert ks == list(range(3, 23)), ('k range', j, ks)
        for (k, lm, le, hm, he) in claims[j]:
            assert lm > 0 and hm >= 0
    assert numden is not None, 'NUMDEN line missing'
    d = os.path.join(outdir, pkg)
    os.makedirs(d, exist_ok=True)
    def lit(c):
        return '(%d, %d, %d, %d, %d)' % c
    with open(os.path.join(d, 'Claims.lean'), 'w') as f:
        f.write('/-\nClaims for the grid (%d,%d,%d), from %s: (j, [(k, loM, loE, hiM, hiE)]) for\n'
                '`loM 2^-loE <= Phi_k(t_j) <= hiM 2^-hiE`, `t_j = j 2^-3` (untrusted; the shards check them).  Data only\n'
                '(no imports).\n-/\n\n' % (n1, n2, nt, src))
        f.write('namespace %s\n\n' % pkg)
        for j in js:
            f.write('def claim%d : Nat × List (Nat × Nat × Int × Nat × Int) := (%d, [%s])\n\n'
                    % (j, j, ',\n    '.join(lit(c) for c in claims[j])))
        f.write('def claims : List (Nat × List (Nat × Nat × Int × Nat × Int)) := [%s]\n\nend %s\n'
                % (', '.join('claim%d' % j for j in js), pkg))
    with open(os.path.join(d, 'Grid.lean'), 'w') as f:
        f.write('/-\nThe grid (%d,%d,%d) (NSUB 64, no vertex pruning) and the run parameters: dt = 2^-3, T = 6, kmax = 22,\n'
                '2^8 sub-intervals per t-step; the t-integral target num/den.\n-/\n' % (n1, n2, nt))
        f.write('import W2Cert.Table\n\nnamespace %s\n\n' % pkg)
        f.write('def grid : W2C.Grid := ⟨%d, %d, %d, 64, false⟩\ndef dtl : Nat := 3\ndef T : Nat := 6\ndef kmax : Nat := 22\n'
                'def lsub : Nat := 8\ndef num : Nat := %d\ndef den : Nat := %d\n\nend %s\n' % (n1, n2, nt, numden[0], numden[1], pkg))
    preds = []
    for s in range(nsh):
        lo = None if s == 0 else cuts[s - 1]
        hi = None if s == nsh - 1 else cuts[s]
        if lo is None and hi is None:
            pred, desc = None, 'every j'
        elif lo is None:
            pred, desc = 'fun c => decide (c.1 ≤ %d)' % hi, 'j <= %d' % hi
        elif hi is None:
            pred, desc = 'fun c => decide (%d < c.1)' % lo, 'j > %d' % lo
        else:
            pred, desc = 'fun c => decide (%d < c.1 ∧ c.1 ≤ %d)' % (lo, hi), '%d < j <= %d' % (lo, hi)
        preds.append((lo, hi))
        lst = 'claims' if pred is None else '(claims.filter (%s))' % pred
        with open(os.path.join(d, 'S%02d.lean' % s), 'w') as f:
            f.write('/-\nShard %d of %d of the grid: the run data, both directed recursions for every claimed t_j with\n'
                    '%s, and the check of their claims (native).\n-/\n' % (s, nsh, desc))
            f.write('import W3Cert.Rec3\nimport %s.Grid\nimport %s.Claims\n\nnamespace %s\n\n' % (pkg, pkg, pkg))
            f.write('theorem shard%02d : W3C.shard3OK grid dtl kmax true %s = true := by\n'
                    '  native_decide\n\nend %s\n' % (s, lst, pkg))
    with open(os.path.join(d, 'TInt.lean'), 'w') as f:
        f.write('/-\nThe t-integral of the claims: `Σ_{k=6}^{kmax} C_k >= num/den` (native).\n-/\n')
        f.write('import W2Cert.Shard\nimport %s.Grid\nimport %s.Claims\n\nnamespace %s\n\n' % (pkg, pkg, pkg))
        f.write('theorem tint : W2C.tintOK dtl T kmax lsub claims num den = true := by\n  native_decide\n\nend %s\n' % pkg)
    with open(os.path.join(d, 'Nondeg.lean'), 'w') as f:
        f.write('/-\nThe nondegeneracy check of the grid (rings and the vertex paths of the pair entries; W2) (native).\n-/\n')
        f.write('import W2.EntryDefs\nimport %s.Grid\n\nnamespace %s\n\n' % (pkg, pkg))
        f.write('theorem nondeg : W2C.nondegOK grid = true := by\n  native_decide\n\n')
        f.write('theorem chpos : decide (0 < (W2C.mkAData grid).ch.lo) = true := by\n  native_decide\n\nend %s\n' % pkg)
    emod = os.environ.get('W3E', 'W3.RecSound3')
    with open(os.path.join(d, 'Final.lean'), 'w') as f:
        f.write('/-\nThe window-3 bound at the grid (%d,%d,%d): `Σ_{k=6}^{22} C_k ≥ num/den` under Green\'s formula and the\n'
                'vertex lemma, from the proof modules in `W3/` and the native checks of this package (%d claims shard(s), the\n'
                't-integral of the claims, the nondegeneracy of the pair entries and the enclosure of cos(dθ/2)).\n-/\n'
                % (n1, n2, nt, nsh))
        for imp in ['W3.Final3Of', 'W3.Assembly', 'W3.PassSound3', 'W3.Laplace3', 'W3.Disc3', 'W3.TriplePrimCos', 'W3.TriplePrimAsin',
                    'W3.TriplePrimGeo', 'W3.TriplePrimRot', 'W3.TripleEntryLV3', 'W3.TripleEntryTri', 'W3.TabSound3', 'W2.EntryBoundPf', emod]:
            f.write('import %s\n' % imp)
        for s in range(nsh):
            f.write('import %s.S%02d\n' % (pkg, s))
        f.write('import %s.TInt\nimport %s.Nondeg\n\nnamespace %s\n\nopen BHH BHH.W3 W2C\n\n' % (pkg, pkg, pkg))
        f.write('/-- Every claim is checked by its shard. -/\ntheorem claimsChecked : ClaimsChecked3 grid 3 22 claims := by\n  intro c hc\n')
        if nsh == 1:
            f.write('  exact shard3OK_spec shard00 c hc\n\n')
        else:
            for s in range(nsh):
                lo, hi = preds[s]
                conds = []
                if lo is not None: conds.append('%d < c.1' % lo)
                if hi is not None: conds.append('c.1 ≤ %d' % hi)
                cond = ' ∧ '.join(conds)
                if s < nsh - 1:
                    f.write('  by_cases h%d : c.1 ≤ %d\n' % (s, hi))
                    f.write('  · exact shard3OK_spec shard%02d c (List.mem_filter.mpr ⟨hc, by simp only [decide_eq_true_eq]; omega⟩)\n' % s)
                else:
                    f.write('  · exact shard3OK_spec shard%02d c (List.mem_filter.mpr ⟨hc, by simp only [decide_eq_true_eq]; omega⟩)\n\n' % s)
        f.write('/-- The grid conditions (decided, with the ring tests from the nondegeneracy check). -/\n'
                'theorem gridOK : GridOK grid :=\n'
                '  ⟨by decide, by decide, by decide, by decide, by decide, (BHH.W2.nondeg_spec nondeg).1, of_decide_eq_true chpos⟩\n\n')
        f.write('/-- The window-3 bound with the certified constant `num/den`. -/\n'
                'theorem w3_bound : W3BoundAt ((num : ℝ) / den) :=\n'
                '  w3BoundAt_of_checks passSound3 lemma1 laplaceBound3 discBound3 recSound3\n'
                '    (tableSoundOf3 (tripleSound cosSinTSound asinTSound triRangeSound) (lv3Sound cosSinTSound asinTSound)\n'
                '      rotA3 reflA3)\n'
                '    gridOK (by decide) nondeg claimsChecked tint\n\n')
        f.write('/-- The same with the constant written out. -/\n'
                'theorem w3_bound_lit : W3BoundAt (%d / %d) := by\n'
                '  have h := w3_bound\n  unfold num den at h\n  push_cast at h\n  exact h\n\n' % (numden[0], numden[1]))
        # beta = 5/8 + C3 + C4 + C5 + num/den (box part constants of MainBoundsV3), rounded down to 10 decimals
        b10 = (6466117723 * numden[1] + numden[0] * 10 ** 10) // numden[1]
        f.write('/-- With the box part `MainBoundsV3`: `β ≥ 5/8 + C_3 + C_4 + C_5 + num/den`, rounded down to 10 decimals. -/\n'
                'theorem beta_bound (hM : MainBoundsV3) : BetaBoundV3At (%d / 10 ^ 10) :=\n'
                '  betaBoundV3At_of (by norm_num) (by norm_num) hM w3_bound_lit\n\n'
                '/-- The same for the BHH constant. -/\n'
                'theorem bhh_beta_bound (hM : MainBoundsV3) : BHHBetaBoundV3At (%d / 10 ^ 10) :=\n'
                '  bhhBetaBoundV3At_of (beta_bound hM)\n\nend %s\n' % (b10, b10, pkg))
    print('claims', len(js), 'x', len(claims[js[0]]), 'numden', numden, 'shards', nsh, 'cuts', cuts, '->', d)

if __name__ == '__main__':
    main()
