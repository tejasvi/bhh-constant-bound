/-
Index bookkeeping of the window-3 table code for `par = false` (`W3C.rawPairs`, `W3C.mkPairs`, `W3C.mkTri` of
`W3Cert/Rec3.lean`): the symmetrised pair entry at `(ir, ir2, d)` is `symPair` of the raw entries `pairEntryF` at `d`
and `-d`; the stored triple value at `(ia, ib, ic, dab, dbc)` is `2 · up48(ā3) + T` of the triple entry at
`(dab, dbc)` (computed half) or at `(-dab, -dbc)` (mirror half).  Also the rounding facts used by the table
soundness: `upq` is monotone, and `up48 a · 2^-48 ≥ fx a`.
-/
import W3.Glue3
import W2.TSOf
import W2.EntryBoundPf

open MeasureTheory Set Real

namespace BHH.W3.TabSound3

open W2C BHH.Cert BHH BHH.W2

lemma flat_lt {a b A B : ℕ} (ha : a < A) (hb : b < B) : a * B + b < A * B := by
  have h := Nat.mul_le_mul_right B (Nat.succ_le_of_lt ha)
  rw [Nat.succ_mul] at h
  omega

lemma rawPairs_eq (td : W3C.TabData) :
    W3C.rawPairs td false = (Array.range (td.g.NR * (td.g.NR * td.g.ND))).map fun idx =>
      W3C.pairEntryF td (idx / (td.g.NR * td.g.ND)) (idx % (td.g.NR * td.g.ND) / td.g.ND)
        (Int.ofNat (idx % (td.g.NR * td.g.ND) % td.g.ND) - Int.ofNat (td.g.NT - 1)) := by
  unfold W3C.rawPairs
  simp only [Bool.false_eq_true, ↓reduceIte]
  exact foldl_rows (td.g.NR * td.g.ND)
    (fun ir q => W3C.pairEntryF td ir (q / td.g.ND) (Int.ofNat (q % td.g.ND) - Int.ofNat (td.g.NT - 1))) td.g.NR

lemma rawPairs_size (td : W3C.TabData) : (W3C.rawPairs td false).size = td.g.NR * (td.g.NR * td.g.ND) := by
  rw [rawPairs_eq, Array.size_map, Array.size_range]

lemma rawPairs_get (td : W3C.TabData) {ir ir2 di : ℕ} (hir : ir < td.g.NR) (hir2 : ir2 < td.g.NR)
    (hdi : di < td.g.ND) :
    (W3C.rawPairs td false)[(ir * td.g.NR + ir2) * td.g.ND + di]! =
      W3C.pairEntryF td ir ir2 (Int.ofNat di - Int.ofNat (td.g.NT - 1)) := by
  have hlt : ir2 * td.g.ND + di < td.g.NR * td.g.ND := flat_lt hir2 hdi
  have hidx : (ir * td.g.NR + ir2) * td.g.ND + di = ir * (td.g.NR * td.g.ND) + (ir2 * td.g.ND + di) := by ring
  have hb : ir * (td.g.NR * td.g.ND) + (ir2 * td.g.ND + di) < td.g.NR * (td.g.NR * td.g.ND) := flat_lt hir hlt
  rw [hidx, rawPairs_eq, getElem!_map _ _ (by simpa using hb), range_getElem! hb, flat_div _ _ hlt,
    flat_mod _ _ hlt, flat_div _ _ hdi, flat_mod _ _ hdi]

lemma mkPairs_get (td : W3C.TabData) {ir ir2 di : ℕ} (hir : ir < td.g.NR) (hir2 : ir2 < td.g.NR)
    (hdi : di < td.g.ND) :
    (W3C.mkPairs td false)[(ir * td.g.NR + ir2) * td.g.ND + di]! =
      W3C.symPair (W3C.pairEntryF td ir ir2 (Int.ofNat di - Int.ofNat (td.g.NT - 1)))
        (W3C.pairEntryF td ir ir2 (Int.ofNat (td.g.ND - 1 - di) - Int.ofNat (td.g.NT - 1))) := by
  have hb : (ir * td.g.NR + ir2) * td.g.ND + di < td.g.NR * (td.g.NR * td.g.ND) := by
    have h1 := flat_lt hir (flat_lt hir2 hdi)
    have e : (ir * td.g.NR + ir2) * td.g.ND + di = ir * (td.g.NR * td.g.ND) + (ir2 * td.g.ND + di) := by ring
    rw [e]; exact h1
  unfold W3C.mkPairs
  simp only
  rw [getElem!_map _ _ (by simpa [rawPairs_size] using hb), range_getElem! (by rw [rawPairs_size]; exact hb),
    flat_mod _ _ hdi]
  have e2 : (ir * td.g.NR + ir2) * td.g.ND + di - di + (td.g.ND - 1 - di) =
      (ir * td.g.NR + ir2) * td.g.ND + (td.g.ND - 1 - di) := by omega
  rw [e2, rawPairs_get td hir hir2 hdi, rawPairs_get td hir hir2 (by omega)]

lemma off_lt (g : Grid) {d : ℤ} (hd : |d| < g.NT) : (d + ((g.NT - 1 : ℕ) : ℤ)).toNat < g.ND := by
  have hND : g.ND = 2 * g.NT - 1 := rfl
  rw [abs_lt] at hd; rw [hND]; omega

lemma mkPairs_getD (g : Grid) {ir ir2 : ℕ} (hir : ir < g.NR) (hir2 : ir2 < g.NR) {d : ℤ} (hd : |d| < g.NT) :
    (W3C.mkPairs (W3C.mkTabData g) false)[(ir * g.NR + ir2) * g.ND + (d + ((g.NT - 1 : ℕ) : ℤ)).toNat]! =
      W3C.symPair (W3C.pairEntryF (W3C.mkTabData g) ir ir2 d) (W3C.pairEntryF (W3C.mkTabData g) ir ir2 (-d)) := by
  have hND : g.ND = 2 * g.NT - 1 := rfl
  refine Eq.trans (mkPairs_get (W3C.mkTabData g) hir hir2 (off_lt g hd)) ?_
  have e1 : Int.ofNat (d + ((g.NT - 1 : ℕ) : ℤ)).toNat - Int.ofNat ((W3C.mkTabData g).g.NT - 1) = d := by
    show Int.ofNat (d + ((g.NT - 1 : ℕ) : ℤ)).toNat - Int.ofNat (g.NT - 1) = d
    rw [abs_lt] at hd; simp only [Int.ofNat_eq_natCast]; omega
  have e2 : Int.ofNat ((W3C.mkTabData g).g.ND - 1 - (d + ((g.NT - 1 : ℕ) : ℤ)).toNat) -
      Int.ofNat ((W3C.mkTabData g).g.NT - 1) = -d := by
    show Int.ofNat (g.ND - 1 - (d + ((g.NT - 1 : ℕ) : ℤ)).toNat) - Int.ofNat (g.NT - 1) = -d
    rw [abs_lt] at hd; rw [hND]; simp only [Int.ofNat_eq_natCast]; omega
  rw [e1, e2]

lemma pairEntryF_eq (g : Grid) {d : ℤ} (hd : |d| < g.NT) (ir ir2 : ℕ) :
    W3C.pairEntryF (W3C.mkTabData g) ir ir2 d =
      ⟨(entryF g.prune ((Array.range g.NR).map (mkRing g)) (mkAData g) (mkDData g d) ir ir2).1 == 1,
       max (entryF g.prune ((Array.range g.NR).map (mkRing g)) (mkAData g) (mkDData g d) ir ir2).2 0,
       W3C.lv3LoF (W3C.mkTabData g) ir ir2 d⟩ := by
  unfold W3C.pairEntryF
  have h := mkDTab_getElem g hd
  simp only [Int.ofNat_eq_natCast] at h ⊢
  show (match entryF g.prune ((Array.range g.NR).map (mkRing g)) (mkAData g)
      (mkDTab g)[(d + ((g.NT - 1 : ℕ) : ℤ)).toNat]! ir ir2 with
    | (cls, ab) => (⟨cls == 1, max ab 0, W3C.lv3LoF (W3C.mkTabData g) ir ir2 d⟩ : W3C.PairE)) = _
  rw [h]

/-- The stored value `2 · up48(ā3) + T` of the computed triple entry at offset indices `dbcN`, `dabN`. -/
def triVal (td : W3C.TabData) (pairs : Array W3C.PairE) (ia ib ic dbcN dabN : ℕ) : ℕ :=
  let te := W3C.tripleEntryF td ia ib ic (Int.ofNat dabN - Int.ofNat (td.g.NT - 1))
    (Int.ofNat dbcN - Int.ofNat (td.g.NT - 1)) pairs[(ib * td.g.NR + ic) * td.g.ND + dbcN]!
    pairs[(ia * td.g.NR + ib) * td.g.ND + dabN]!
  2 * W3C.up48 te.abar3 + (if te.tcls then 1 else 0)

lemma canon3_iff (NT dbcN dabN : ℕ) :
    W3C.canon3 NT dbcN dabN = true ↔ NT - 1 < dbcN ∨ (dbcN = NT - 1 ∧ NT - 1 ≤ dabN) := by
  unfold W3C.canon3
  simp

lemma q_parts {NR ND dbcN ia dabN : ℕ} (hia : ia < NR) (hab : dabN < ND) :
    ((dbcN * NR + ia) * ND + dabN) / (NR * ND) = dbcN ∧ ((dbcN * NR + ia) * ND + dabN) % ND = dabN ∧
      ((dbcN * NR + ia) * ND + dabN) / ND % NR = ia := by
  have e : (dbcN * NR + ia) * ND + dabN = dbcN * (NR * ND) + (ia * ND + dabN) := by ring
  have hlt : ia * ND + dabN < NR * ND := flat_lt hia hab
  refine ⟨?_, flat_mod _ _ hab, ?_⟩
  · rw [e, flat_div _ _ hlt]
  · rw [flat_div _ _ hab, flat_mod _ _ hia]

lemma mkTri_get (td : W3C.TabData) (pairs : Array W3C.PairE) {ia ib ic dbcN dabN : ℕ} (hia : ia < td.g.NR)
    (hib : ib < td.g.NR) (hic : ic < td.g.NR) (hbc : dbcN < td.g.ND) (hab : dabN < td.g.ND) :
    (W3C.mkTri td pairs false)[(((ib * td.g.NR + ic) * td.g.ND + dbcN) * td.g.NR + ia) * td.g.ND + dabN]! =
      if W3C.canon3 td.g.NT dbcN dabN = true then triVal td pairs ia ib ic dbcN dabN
      else triVal td pairs ia ib ic (td.g.ND - 1 - dbcN) (td.g.ND - 1 - dabN) := by
  set NR := td.g.NR with hNR
  set ND := td.g.ND with hND
  set NT := td.g.NT with hNT
  have hND' : ND = 2 * NT - 1 := rfl
  set L := ND * NR * ND with hL
  let hb : ℕ → Array ℕ := fun b => (Array.range L).map fun q =>
    if W3C.canon3 NT (q / (NR * ND)) (q % ND) = true then
      triVal td pairs (q / ND % NR) (b / NR) (b % NR) (q / (NR * ND)) (q % ND) else 0
  let G : ℕ → ℕ → ℕ := fun b q =>
    if W3C.canon3 NT (q / (NR * ND)) (q % ND) = true then (hb b)[q]!
    else (hb b)[((ND - 1 - q / (NR * ND)) * NR + q / ND % NR) * ND + (ND - 1 - q % ND)]!
  have hT : W3C.mkTri td pairs false = ((List.range (NR * NR)).map fun b => (Array.range L).map (G b)).foldl
      (· ++ ·) #[] := rfl
  rw [hT, foldl_rows L G (NR * NR)]
  have hq : (dbcN * NR + ia) * ND + dabN < L := flat_lt (flat_lt hbc hia) hab
  have hbb : ib * NR + ic < NR * NR := flat_lt hib hic
  have hidx : (((ib * NR + ic) * ND + dbcN) * NR + ia) * ND + dabN =
      (ib * NR + ic) * L + ((dbcN * NR + ia) * ND + dabN) := by rw [hL]; ring
  have hlt : (ib * NR + ic) * L + ((dbcN * NR + ia) * ND + dabN) < NR * NR * L := flat_lt hbb hq
  rw [hidx, getElem!_map _ _ (by simpa using hlt), range_getElem! hlt, flat_div _ _ hq, flat_mod _ _ hq]
  obtain ⟨e1, e2, e3⟩ := q_parts (dbcN := dbcN) hia hab
  have ediv : (ib * NR + ic) / NR = ib := flat_div _ _ hic
  have emod : (ib * NR + ic) % NR = ic := flat_mod _ _ hic
  simp only [G, e1, e2]
  by_cases hc : W3C.canon3 NT dbcN dabN = true
  · rw [ite_eq_left hc, ite_eq_left hc]
    simp only [hb]
    rw [getElem!_map _ _ (by simpa using hq), range_getElem! hq, e1, e2, e3, ediv, emod, ite_eq_left hc]
  · rw [ite_eq_right hc, ite_eq_right hc]
    have hbc' : ND - 1 - dbcN < ND := by omega
    have hab' : ND - 1 - dabN < ND := by omega
    have hq' : ((ND - 1 - dbcN) * NR + ia) * ND + (ND - 1 - dabN) < L := flat_lt (flat_lt hbc' hia) hab'
    obtain ⟨f1, f2, f3⟩ := q_parts (dbcN := ND - 1 - dbcN) hia hab'
    have hc' : W3C.canon3 NT (ND - 1 - dbcN) (ND - 1 - dabN) = true := by
      rw [canon3_iff] at hc ⊢
      omega
    simp only [hb]
    rw [e3, getElem!_map _ _ (by simpa using hq'), range_getElem! hq', f1, f2, f3, ediv, emod, ite_eq_left hc']

/-- The triple entry of the computation at integer offsets, with the symmetrised pair entries. -/
def triEnt (g : Grid) (ia ib ic : ℕ) (dab dbc : ℤ) : W3C.TripE :=
  W3C.tripleEntryF (W3C.mkTabData g) ia ib ic dab dbc
    (W3C.symPair (W3C.pairEntryF (W3C.mkTabData g) ib ic dbc) (W3C.pairEntryF (W3C.mkTabData g) ib ic (-dbc)))
    (W3C.symPair (W3C.pairEntryF (W3C.mkTabData g) ia ib dab) (W3C.pairEntryF (W3C.mkTabData g) ia ib (-dab)))

/-- the stored value of a triple entry -/
def stv (te : W3C.TripE) : ℕ := 2 * W3C.up48 te.abar3 + (if te.tcls then 1 else 0)

lemma triVal_eq (g : Grid) {ia ib ic : ℕ} (hia : ia < g.NR) (hib : ib < g.NR) (hic : ic < g.NR) {dab dbc : ℤ}
    (hab : |dab| < g.NT) (hbc : |dbc| < g.NT) :
    triVal (W3C.mkTabData g) (W3C.mkPairs (W3C.mkTabData g) false) ia ib ic (dbc + ((g.NT - 1 : ℕ) : ℤ)).toNat
      (dab + ((g.NT - 1 : ℕ) : ℤ)).toNat = stv (triEnt g ia ib ic dab dbc) := by
  have e1 : Int.ofNat (dab + ((g.NT - 1 : ℕ) : ℤ)).toNat - Int.ofNat ((W3C.mkTabData g).g.NT - 1) = dab := by
    show Int.ofNat (dab + ((g.NT - 1 : ℕ) : ℤ)).toNat - Int.ofNat (g.NT - 1) = dab
    rw [abs_lt] at hab; simp only [Int.ofNat_eq_natCast]; omega
  have e2 : Int.ofNat (dbc + ((g.NT - 1 : ℕ) : ℤ)).toNat - Int.ofNat ((W3C.mkTabData g).g.NT - 1) = dbc := by
    show Int.ofNat (dbc + ((g.NT - 1 : ℕ) : ℤ)).toNat - Int.ofNat (g.NT - 1) = dbc
    rw [abs_lt] at hbc; simp only [Int.ofNat_eq_natCast]; omega
  unfold triVal
  simp only
  rw [e1, e2]
  have p1 := mkPairs_getD g hib hic hbc
  have p2 := mkPairs_getD g hia hib hab
  change stv (W3C.tripleEntryF (W3C.mkTabData g) ia ib ic dab dbc
    (W3C.mkPairs (W3C.mkTabData g) false)[(ib * g.NR + ic) * g.ND + (dbc + ((g.NT - 1 : ℕ) : ℤ)).toNat]!
    (W3C.mkPairs (W3C.mkTabData g) false)[(ia * g.NR + ib) * g.ND + (dab + ((g.NT - 1 : ℕ) : ℤ)).toNat]!) = _
  rw [p1, p2]
  rfl

lemma tri_getD (g : Grid) {ia ib ic : ℕ} (hia : ia < g.NR) (hib : ib < g.NR) (hic : ic < g.NR) {dab dbc : ℤ}
    (hab : |dab| < g.NT) (hbc : |dbc| < g.NT) :
    (W3C.mkTri (W3C.mkTabData g) (W3C.mkPairs (W3C.mkTabData g) false) false)[
        (((ib * g.NR + ic) * g.ND + (dbc + ((g.NT - 1 : ℕ) : ℤ)).toNat) * g.NR + ia) * g.ND +
          (dab + ((g.NT - 1 : ℕ) : ℤ)).toNat]! =
      if 0 < dbc ∨ (dbc = 0 ∧ 0 ≤ dab) then stv (triEnt g ia ib ic dab dbc)
      else stv (triEnt g ia ib ic (-dab) (-dbc)) := by
  have hND : g.ND = 2 * g.NT - 1 := rfl
  refine Eq.trans (mkTri_get (W3C.mkTabData g) (W3C.mkPairs (W3C.mkTabData g) false) hia hib hic
    (off_lt g hbc) (off_lt g hab)) ?_
  have hcan : W3C.canon3 (W3C.mkTabData g).g.NT (dbc + ((g.NT - 1 : ℕ) : ℤ)).toNat
      (dab + ((g.NT - 1 : ℕ) : ℤ)).toNat = true ↔ (0 < dbc ∨ (dbc = 0 ∧ 0 ≤ dab)) := by
    rw [canon3_iff]
    show g.NT - 1 < (dbc + ((g.NT - 1 : ℕ) : ℤ)).toNat ∨ ((dbc + ((g.NT - 1 : ℕ) : ℤ)).toNat = g.NT - 1 ∧
      g.NT - 1 ≤ (dab + ((g.NT - 1 : ℕ) : ℤ)).toNat) ↔ _
    rw [abs_lt] at hab hbc
    omega
  have m1 : (W3C.mkTabData g).g.ND - 1 - (dbc + ((g.NT - 1 : ℕ) : ℤ)).toNat =
      (-dbc + ((g.NT - 1 : ℕ) : ℤ)).toNat := by
    show g.ND - 1 - _ = _
    rw [abs_lt] at hbc; rw [hND]; omega
  have m2 : (W3C.mkTabData g).g.ND - 1 - (dab + ((g.NT - 1 : ℕ) : ℤ)).toNat =
      (-dab + ((g.NT - 1 : ℕ) : ℤ)).toNat := by
    show g.ND - 1 - _ = _
    rw [abs_lt] at hab; rw [hND]; omega
  by_cases hc : 0 < dbc ∨ (dbc = 0 ∧ 0 ≤ dab)
  · rw [ite_eq_left (hcan.mpr hc), ite_eq_left hc]
    exact triVal_eq g hia hib hic hab hbc
  · rw [ite_eq_right (fun h => hc (hcan.mp h)), ite_eq_right hc, m1, m2]
    exact triVal_eq g hia hib hic (by rwa [abs_neg]) (by rwa [abs_neg])

lemma upq_spec (a : ℤ) (dtl : ℕ) :
    a ≤ W3C.upq a dtl ∧ W3C.upq a dtl < a + 2 ^ dtl ∧ (2 ^ dtl : ℤ) ∣ W3C.upq a dtl := by
  have hm : (0 : ℤ) < 2 ^ dtl := by positivity
  have hdiv := Int.mul_ediv_add_emod a (2 ^ dtl)
  have hr0 := Int.emod_nonneg a hm.ne'
  have hr1 := Int.emod_lt_of_pos a hm
  unfold W3C.upq
  by_cases hr : a % 2 ^ dtl = 0
  · rw [hr, sub_zero, Int.emod_self, add_zero]
    exact ⟨le_rfl, by linarith, Int.dvd_of_emod_eq_zero hr⟩
  · have hlt : (2 : ℤ) ^ dtl - a % 2 ^ dtl < 2 ^ dtl := by
      have : 0 < a % 2 ^ dtl := lt_of_le_of_ne hr0 (Ne.symm hr)
      linarith
    rw [Int.emod_eq_of_lt (by linarith) hlt]
    refine ⟨by linarith, ?_, ?_⟩
    · have : 0 < a % 2 ^ dtl := lt_of_le_of_ne hr0 (Ne.symm hr)
      linarith
    · refine ⟨a / 2 ^ dtl + 1, ?_⟩
      linear_combination -hdiv

lemma upq_mono {a b : ℤ} (h : a ≤ b) (dtl : ℕ) : W3C.upq a dtl ≤ W3C.upq b dtl := by
  obtain ⟨ha1, ha2, ⟨k1, hk1⟩⟩ := upq_spec a dtl
  obtain ⟨hb1, hb2, ⟨k2, hk2⟩⟩ := upq_spec b dtl
  have hm : (0 : ℤ) < 2 ^ dtl := by positivity
  by_contra hc
  have hc := lt_of_not_ge hc
  rw [hk1, hk2] at hc
  have hk : k2 < k1 := lt_of_mul_lt_mul_left hc hm.le
  have : (2 : ℤ) ^ dtl * (k2 + 1) ≤ 2 ^ dtl * k1 := mul_le_mul_of_nonneg_left (by omega) hm.le
  rw [hk1] at ha2
  rw [hk2] at hb1
  nlinarith

lemma Q48_eq : (W3C.Q48 : ℤ) = 2 ^ 48 := by
  unfold W3C.Q48 PR; norm_num

lemma fx_le_up48 (a : ℤ) : fx a ≤ ((W3C.up48 a : ℕ) : ℝ) / 2 ^ 48 := by
  unfold W3C.up48 divU
  rw [Q48_eq]
  set A := max a 0 with hA
  set c := -((-A) / (2 ^ 48 : ℤ)) with hc
  have h1 := Int.ediv_mul_le (-A) (show (2 ^ 48 : ℤ) ≠ 0 by norm_num)
  have hA0 : 0 ≤ A := le_max_right _ _
  have haA : a ≤ A := le_max_left _ _
  have hcB : A ≤ c * 2 ^ 48 := by rw [hc]; linarith
  have hc0 : 0 ≤ c := by
    by_contra h
    have h := lt_of_not_ge h
    have : c * 2 ^ 48 < 0 := by nlinarith
    linarith
  have hcast : ((c.toNat : ℕ) : ℝ) = (c : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hc0
  rw [hcast]
  unfold fx PR
  have h2 : (a : ℝ) ≤ (c : ℝ) * 2 ^ 48 := by exact_mod_cast haA.trans hcB
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : (2 : ℝ) ^ 96 = 2 ^ 48 * 2 ^ 48 := by norm_num
  rw [this]
  nlinarith

end BHH.W3.TabSound3
