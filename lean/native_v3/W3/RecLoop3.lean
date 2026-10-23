/-
Window-3 recursion: the loops of `W3C.runT3` as exact `Nat` sums.  A sparse row `W3C.Row` represents the
function `rowVal r ca D` (sum of the mantissas with state `D` in the segments of previous cell `ca`); the MAC loops
(`macLoop`, `segLoop`), the transitions (`transLoop`), the accumulator (`accOf`), the row construction (`emitLoop`,
`pushSeg`, `cbLoop`, `targetRow`, `c1Loop`), the normalisation (`normRows`) and the mirror copies (`fullRows`).
-/
import W3.RecPush

namespace BHH.W3.Rec

open W3C W2C BHH BHH.W2

attribute [local irreducible] W3C.NS W3C.reachable W3C.trs W3C.cls

/-! ## Array helpers -/

lemma getElem!_push_lt {α : Type*} [Inhabited α] (a : Array α) (x : α) {i : ℕ} (hi : i < a.size) :
    (a.push x)[i]! = a[i]! := by
  rw [getElem!_pos (a.push x) i (by simp; omega), getElem!_pos a i hi, Array.getElem_push_lt hi]

lemma getElem!_push_eq {α : Type*} [Inhabited α] (a : Array α) (x : α) : (a.push x)[a.size]! = x := by
  rw [getElem!_pos (a.push x) a.size (by simp), Array.getElem_push_eq]

lemma getElem!_replicate {α : Type*} [Inhabited α] {n i : ℕ} (v : α) (hi : i < n) :
    (Array.replicate n v)[i]! = v := by
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_replicate]

lemma NS_pos : 0 < NS := by rw [NS_eq]; norm_num

/-! ## Rows -/

/-- The value of a row at `(ca, D)`. -/
def rowVal (r : Row) (ca D : ℕ) : ℕ :=
  ∑ s ∈ Finset.range r.segCa.size, if r.segCa[s]! = ca then
    ∑ q ∈ Finset.Ico r.segStart[s]! r.segStart[s + 1]!, (if r.st[q]! = D then r.m[q]! else 0)
  else 0

/-- Well-formed rows: previous cells `< NC`, states `< NS`. -/
structure RowWF (NC : ℕ) (r : Row) : Prop where
  ca : ∀ s < r.segCa.size, r.segCa[s]! < NC
  st : ∀ q : ℕ, r.st[q]! < NS

/-- The structure of the rows built by the recursion. -/
structure RowInv (r : Row) : Prop where
  ss : r.segStart.size = r.segCa.size + 1
  last : r.segStart[r.segCa.size]! = r.st.size
  msz : r.m.size = r.st.size
  le : ∀ s ≤ r.segCa.size, r.segStart[s]! ≤ r.st.size

lemma rowInv_empty : RowInv Row.empty := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro s hs
  simp only [Row.empty, Array.size_empty] at hs ⊢
  have : s = 0 := by omega
  subst this; simp

lemma rowWF_empty (NC : ℕ) : RowWF NC Row.empty := by
  refine ⟨fun s hs => by simp [Row.empty] at hs, fun q => ?_⟩
  simp only [Row.empty]
  rw [getElem!_neg _ _ (by simp)]
  exact NS_pos

lemma rowVal_empty (ca D : ℕ) : rowVal Row.empty ca D = 0 := by
  simp [rowVal, Row.empty]

/-- Appending entries (and possibly a segment). -/
lemma rowVal_append (r : Row) (hr : RowInv r) (st' m' : Array ℕ) (hsz : r.st.size ≤ st'.size)
    (hpre : ∀ q < r.st.size, st'[q]! = r.st[q]! ∧ m'[q]! = r.m[q]!) (ca D : ℕ) :
    rowVal ⟨r.segCa, r.segStart, st', m'⟩ ca D = rowVal r ca D := by
  unfold rowVal
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.mem_range] at hs
  change s < r.segCa.size at hs
  simp only
  split_ifs
  · apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.mem_Ico] at hq
    have h1 := hr.le (s + 1) (by omega)
    have := hpre q (by omega)
    rw [this.1, this.2]
  · rfl

lemma rowVal_pushSeg_gen (r : Row) (hr : RowInv r) (cb : ℕ) (st' m' : Array ℕ) (hsz : r.st.size ≤ st'.size)
    (hpre : ∀ q < r.st.size, st'[q]! = r.st[q]! ∧ m'[q]! = r.m[q]!) (ca D : ℕ) :
    rowVal ⟨r.segCa.push cb, r.segStart.push st'.size, st', m'⟩ ca D = rowVal r ca D +
      if cb = ca then ∑ q ∈ Finset.Ico r.st.size st'.size, (if st'[q]! = D then m'[q]! else 0) else 0 := by
  have h0 := rowVal_append r hr st' m' hsz hpre ca D
  unfold rowVal at h0 ⊢
  simp only [Array.size_push] at h0 ⊢
  rw [Finset.sum_range_succ, ← h0]
  congr 1
  · apply Finset.sum_congr rfl
    intro s hs
    rw [Finset.mem_range] at hs
    rw [getElem!_push_lt _ _ hs, getElem!_push_lt _ _ (by rw [hr.ss]; omega),
      getElem!_push_lt _ _ (by rw [hr.ss]; omega)]
  · rw [getElem!_push_eq, getElem!_push_lt _ _ (by rw [hr.ss]; omega), hr.last,
      show r.segCa.size + 1 = r.segStart.size by rw [hr.ss], getElem!_push_eq]

lemma rowInv_append (r : Row) (hr : RowInv r) (cb : ℕ) (st' m' : Array ℕ) (hsz : r.st.size ≤ st'.size)
    (hm : m'.size = st'.size) (hpre : ∀ q < r.st.size, st'[q]! = r.st[q]!) :
    RowInv ⟨r.segCa.push cb, r.segStart.push st'.size, st', m'⟩ := by
  refine ⟨?_, ?_, hm, ?_⟩
  · simp only [Array.size_push]; rw [hr.ss]
  · simp only [Array.size_push]
    rw [show r.segCa.size + 1 = r.segStart.size by rw [hr.ss], getElem!_push_eq]
  · intro s hs
    simp only [Array.size_push] at hs ⊢
    by_cases h : s < r.segStart.size
    · rw [getElem!_push_lt _ _ h]
      have := hr.le s (by rw [hr.ss] at h; omega)
      omega
    · have : s = r.segStart.size := by rw [hr.ss] at h ⊢; omega
      rw [this, getElem!_push_eq]

/-! ## The MAC loops -/

/-- `macLoop` (`UInt64` products) adds `mulTop` of every entry of `[q, e)` at its state index plus `off`, for
mantissas `≤ 2^62` and kernel halves `< 2^32`, `< 2^31`. -/
lemma macLoop_spec (lower : Bool) (rst rm : Array ℕ) (k1 k0 : UInt64) (off e : ℕ) (hst : e ≤ rst.size)
    (hm : e ≤ rm.size) (hk1 : k1.toNat < 2 ^ 32) (hk0 : k0.toNat < 2 ^ 31) (hv : ∀ q : ℕ, rm[q]! ≤ 2 ^ 62) :
    ∀ (n q : ℕ) (acc : Array ℕ), e - q = n → (∀ q' ∈ Finset.Ico q e, rst[q']! + off < acc.size) →
      (macLoop lower rst rm k1 k0 off e hst hm q acc).size = acc.size ∧
      ∀ i, (macLoop lower rst rm k1 k0 off e hst hm q acc)[i]! = acc[i]! + ∑ q' ∈ Finset.Ico q e,
        (if rst[q']! + off = i then mulTop lower (rm[q']! >>> 31) (rm[q']! &&& m31) k1.toNat k0.toNat else 0) := by
  intro n
  induction n with
  | zero =>
    intro q acc hn _
    rw [macLoop, dif_neg (by omega)]
    refine ⟨rfl, fun i => ?_⟩
    rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty, add_zero]
  | succ n ih =>
    intro q acc hn hin
    have hq : q < e := by omega
    rw [macLoop, dif_pos hq]
    simp only
    have hrm : rm[q]'(Nat.lt_of_lt_of_le hq hm) = rm[q]! := (getElem!_pos rm q _).symm
    have hrs : rst[q]'(Nat.lt_of_lt_of_le hq hst) = rst[q]! := (getElem!_pos rst q _).symm
    have h62 := hv q
    have hmul : (mulTopU lower (rm[q]'(Nat.lt_of_lt_of_le hq hm)).toUInt64 k1 k0).toNat =
        mulTop lower (rm[q]! >>> 31) (rm[q]! &&& m31) k1.toNat k0.toNat := by
      rw [hrm, mulTopU_toNat lower _ k1 k0 (by rw [toUInt64_toNat (by omega)]; exact h62) hk1 hk0,
        toUInt64_toNat (by omega)]
    rw [hmul, hrs]
    set acc' := acc.set! (rst[q]! + off) (acc[rst[q]! + off]! +
      mulTop lower (rm[q]! >>> 31) (rm[q]! &&& m31) k1.toNat k0.toNat)
    have hsz : acc'.size = acc.size := Array.size_set! _ _ _
    have hq' : rst[q]! + off < acc.size := hin q (Finset.mem_Ico.mpr ⟨le_rfl, hq⟩)
    have ih' := ih (q + 1) acc' (by omega) (by
      intro q' hq''; rw [hsz]; exact hin q' (by rw [Finset.mem_Ico] at hq'' ⊢; omega))
    refine ⟨ih'.1.trans hsz, fun i => ?_⟩
    rw [ih'.2 i, Finset.sum_eq_sum_Ico_succ_bot hq]
    by_cases hi : rst[q]! + off = i
    · rw [if_pos hi]
      have : acc'[i]! = acc[i]! + mulTop lower (rm[q]! >>> 31) (rm[q]! &&& m31) k1.toNat k0.toNat := by
        rw [← hi]; exact Array.getElem!_set!_self acc _ _ hq'
      rw [this]; ring
    · rw [if_neg hi]
      have : acc'[i]! = acc[i]! := Array.getElem!_set!_ne acc _ _ _ hi
      rw [this]; ring

/-- `macLoopN` (`Nat` products) adds `mulTop` of every entry of `[q, e)` at its state index plus `off`. -/
lemma macLoopN_spec (lower : Bool) (rst rm : Array ℕ) (k1 k0 off : ℕ) :
    ∀ (n q e : ℕ) (acc : Array ℕ), e - q = n → (∀ q' ∈ Finset.Ico q e, rst[q']! + off < acc.size) →
      (macLoopN lower rst rm k1 k0 off q e acc).size = acc.size ∧
      ∀ i, (macLoopN lower rst rm k1 k0 off q e acc)[i]! = acc[i]! + ∑ q' ∈ Finset.Ico q e,
        (if rst[q']! + off = i then mulTop lower (rm[q']! >>> 31) (rm[q']! &&& m31) k1 k0 else 0) := by
  intro n
  induction n with
  | zero =>
    intro q e acc hn _
    rw [macLoopN, if_neg (by omega)]
    refine ⟨rfl, fun i => ?_⟩
    rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty, add_zero]
  | succ n ih =>
    intro q e acc hn hin
    rw [macLoopN, if_pos (by omega)]
    simp only
    set acc' := acc.set! (rst[q]! + off) (acc[rst[q]! + off]! + mulTop lower (rm[q]! >>> 31) (rm[q]! &&& m31) k1 k0)
    have hsz : acc'.size = acc.size := Array.size_set! _ _ _
    have hq : rst[q]! + off < acc.size := hin q (Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩)
    have ih' := ih (q + 1) e acc' (by omega) (by
      intro q' hq'; rw [hsz]; exact hin q' (by rw [Finset.mem_Ico] at hq' ⊢; omega))
    refine ⟨ih'.1.trans hsz, fun i => ?_⟩
    rw [ih'.2 i, Finset.sum_eq_sum_Ico_succ_bot (by omega : q < e)]
    by_cases hi : rst[q]! + off = i
    · rw [if_pos hi]
      have : acc'[i]! = acc[i]! + mulTop lower (rm[q]! >>> 31) (rm[q]! &&& m31) k1 k0 := by
        rw [← hi]; exact Array.getElem!_set!_self acc _ _ hq
      rw [this]; ring
    · rw [if_neg hi]
      have : acc'[i]! = acc[i]! := Array.getElem!_set!_ne acc _ _ _ hi
      rw [this]; ring

lemma idx_N0 {N D T : ℕ} (hD : D < N) (hT : T < 2) : D + N * T < 2 * N := by
  rcases (show T = 0 ∨ T = 1 by omega) with rfl | rfl <;> omega

/-- The triple-table entry of segment `s`: `2 K + T`. -/
def kkOf (row : Row) (K3 : Array ℕ) (base NT ND s : ℕ) : ℕ :=
  K3[base + (row.segCa[s]! / NT) * ND - row.segCa[s]! % NT]!

lemma kHalves {k : ℕ} (hk : k < 2 ^ 63) :
    (k >>> 31).toUInt64.toNat = k >>> 31 ∧ (k >>> 31) < 2 ^ 32 ∧ (k &&& m31).toUInt64.toNat = k &&& m31 ∧
      (k &&& m31) < 2 ^ 31 := by
  have h1 : k >>> 31 < 2 ^ 32 := by
    rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_lt_of_lt_mul (by omega)
  have h2 := and_m31_lt k
  exact ⟨toUInt64_toNat (by omega), h1, toUInt64_toNat (by omega), h2⟩

/-- `segLoop` as a double sum over the segments and their entries (rows built by the recursion: mantissas
`≤ 2^62`; kernels `< 2^63` through the `UInt64` loop, larger ones through the `Nat` loop). -/
lemma segLoop_spec (lower : Bool) (row : Row) (K3 : Array ℕ) (base NT ND : ℕ) (hst : ∀ q : ℕ, row.st[q]! < NS)
    (hinv : RowInv row) (hm62 : ∀ q : ℕ, row.m[q]! ≤ 2 ^ 62) :
    ∀ (n s nseg : ℕ) (acc : Array ℕ), nseg - s = n → nseg ≤ row.segCa.size → acc.size = 2 * NS →
      (segLoop lower row K3 base NT ND s nseg acc).size = acc.size ∧
      ∀ i, (segLoop lower row K3 base NT ND s nseg acc)[i]! = acc[i]! + ∑ s' ∈ Finset.Ico s nseg,
        ∑ q ∈ Finset.Ico row.segStart[s']! row.segStart[s' + 1]!,
          (if row.st[q]! + NS * (kkOf row K3 base NT ND s' % 2) = i then
            mulTop lower (row.m[q]! >>> 31) (row.m[q]! &&& m31) ((kkOf row K3 base NT ND s' >>> 1) >>> 31)
              ((kkOf row K3 base NT ND s' >>> 1) &&& m31) else 0) := by
  intro n
  induction n with
  | zero =>
    intro s nseg acc hn _ _
    rw [segLoop, if_neg (by omega)]
    refine ⟨rfl, fun i => ?_⟩
    rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty, add_zero]
  | succ n ih =>
    intro s nseg acc hn hns hacc
    rw [segLoop, if_pos (by omega)]
    simp only
    have hs : s < row.segCa.size := by omega
    have he1 : row.segStart[s + 1]! ≤ row.st.size := hinv.le (s + 1) (by omega)
    have he2 : row.segStart[s + 1]! ≤ row.m.size := by rw [hinv.msz]; exact he1
    rw [dif_pos ⟨he1, he2⟩]
    have hidx : ∀ q' ∈ Finset.Ico row.segStart[s]! row.segStart[s + 1]!,
        row.st[q']! + NS * (kkOf row K3 base NT ND s % 2) < acc.size := by
      intro q' _
      rw [hacc]
      exact idx_N0 (hst q') (Nat.mod_lt _ (by norm_num))
    -- both branches add the same `mulTop` terms
    have hm : (if kkOf row K3 base NT ND s >>> 1 >>> 63 == 0 then
          macLoop lower row.st row.m ((kkOf row K3 base NT ND s >>> 1) >>> 31).toUInt64
            ((kkOf row K3 base NT ND s >>> 1) &&& m31).toUInt64 (NS * (kkOf row K3 base NT ND s % 2))
            row.segStart[s + 1]! he1 he2 row.segStart[s]! acc
        else macLoopN lower row.st row.m ((kkOf row K3 base NT ND s >>> 1) >>> 31)
            ((kkOf row K3 base NT ND s >>> 1) &&& m31) (NS * (kkOf row K3 base NT ND s % 2)) row.segStart[s]!
            row.segStart[s + 1]! acc).size = acc.size ∧
        ∀ i, (if kkOf row K3 base NT ND s >>> 1 >>> 63 == 0 then
          macLoop lower row.st row.m ((kkOf row K3 base NT ND s >>> 1) >>> 31).toUInt64
            ((kkOf row K3 base NT ND s >>> 1) &&& m31).toUInt64 (NS * (kkOf row K3 base NT ND s % 2))
            row.segStart[s + 1]! he1 he2 row.segStart[s]! acc
        else macLoopN lower row.st row.m ((kkOf row K3 base NT ND s >>> 1) >>> 31)
            ((kkOf row K3 base NT ND s >>> 1) &&& m31) (NS * (kkOf row K3 base NT ND s % 2)) row.segStart[s]!
            row.segStart[s + 1]! acc)[i]! = acc[i]! + ∑ q' ∈ Finset.Ico row.segStart[s]! row.segStart[s + 1]!,
          (if row.st[q']! + NS * (kkOf row K3 base NT ND s % 2) = i then
            mulTop lower (row.m[q']! >>> 31) (row.m[q']! &&& m31) ((kkOf row K3 base NT ND s >>> 1) >>> 31)
              ((kkOf row K3 base NT ND s >>> 1) &&& m31) else 0) := by
      split_ifs with hk
      · have h0 : (kkOf row K3 base NT ND s >>> 1) >>> 63 = 0 := beq_iff_eq.mp hk
        have hk' : kkOf row K3 base NT ND s >>> 1 < 2 ^ 63 := by
          rw [Nat.shiftRight_eq_div_pow] at h0
          by_contra hc
          push_neg at hc
          have := Nat.div_pos hc (by positivity : 0 < 2 ^ 63)
          omega
        obtain ⟨k1e, k1l, k0e, k0l⟩ := kHalves hk'
        have h := macLoop_spec lower row.st row.m ((kkOf row K3 base NT ND s >>> 1) >>> 31).toUInt64
          ((kkOf row K3 base NT ND s >>> 1) &&& m31).toUInt64 (NS * (kkOf row K3 base NT ND s % 2))
          row.segStart[s + 1]! he1 he2 (by rw [k1e]; exact k1l) (by rw [k0e]; exact k0l) hm62
          (row.segStart[s + 1]! - row.segStart[s]!) row.segStart[s]! acc rfl hidx
        rw [k1e, k0e] at h
        exact h
      · exact macLoopN_spec lower row.st row.m _ _ _ (row.segStart[s + 1]! - row.segStart[s]!) row.segStart[s]!
          row.segStart[s + 1]! acc rfl hidx
    have ih' := ih (s + 1) nseg _ (by omega) hns (hm.1.trans hacc)
    unfold kkOf at hm ih' ⊢
    refine ⟨ih'.1.trans hm.1, fun i => ?_⟩
    rw [ih'.2 i, hm.2 i, Finset.sum_eq_sum_Ico_succ_bot (by omega : s < nseg)]
    ring

/-- `transLoop` as sums over the states. -/
lemma transLoop_spec (acc : Array ℕ) (ns : ℕ) :
    ∀ (n D : ℕ) (g : Array ℕ), NS - D = n → g.size = NS + 1 →
      (transLoop acc ns D g).size = g.size ∧
      (∀ D' < NS, (transLoop acc ns D g)[D']! = g[D']! + ∑ q ∈ Finset.Ico D NS,
        ((if trs[q * 8 + ns]! = D' then acc[q]! else 0) + (if trs[q * 8 + ns + 1]! = D' then acc[q + NS]! else 0))) ∧
      (transLoop acc ns D g)[NS]! = g[NS]! + ∑ q ∈ Finset.Ico D NS,
        (cls[q * 8 + ns]! * acc[q]! + cls[q * 8 + ns + 1]! * acc[q + NS]!) := by
  intro n
  induction n with
  | zero =>
    intro D g hn _
    rw [transLoop, if_neg (by omega)]
    refine ⟨rfl, fun D' _ => ?_, ?_⟩ <;> rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty, add_zero]
  | succ n ih =>
    intro D g hn hg
    rw [transLoop, if_pos (by omega)]
    simp only
    set g1 := if trs[D * 8 + ns]! < NS then g.set! trs[D * 8 + ns]! (g[trs[D * 8 + ns]!]! + acc[D]!) else g with hg1
    set g2 := if trs[D * 8 + ns + 1]! < NS then
      g1.set! trs[D * 8 + ns + 1]! (g1[trs[D * 8 + ns + 1]!]! + acc[D + NS]!) else g1 with hg2
    have hs1 : g1.size = g.size := by rw [hg1]; split_ifs <;> simp
    have hs2 : g2.size = g.size := by rw [hg2]; split_ifs <;> simp [hs1]
    set g3 := g2.set! NS (g2[NS]! + cls[D * 8 + ns]! * acc[D]! + cls[D * 8 + ns + 1]! * acc[D + NS]!) with hg3
    have hs3 : g3.size = g.size := by rw [hg3, Array.size_set!, hs2]
    have ih' := ih (D + 1) g3 (by omega) (by rw [hs3, hg])
    -- entries of g1, g2, g3
    have e1 : ∀ D' < NS, g1[D']! = g[D']! + (if trs[D * 8 + ns]! = D' then acc[D]! else 0) := by
      intro D' hD'
      rw [hg1]
      split_ifs with h1 h2 h2
      · rw [← h2]; rw [Array.getElem!_set!_self _ _ _ (by omega)]
      · rw [Array.getElem!_set!_ne _ _ _ _ h2, add_zero]
      · omega
      · rw [add_zero]
    have e1N : g1[NS]! = g[NS]! := by
      rw [hg1]; split_ifs with h1
      · exact Array.getElem!_set!_ne _ _ _ _ (by omega)
      · rfl
    have e2 : ∀ D' < NS, g2[D']! = g1[D']! + (if trs[D * 8 + ns + 1]! = D' then acc[D + NS]! else 0) := by
      intro D' hD'
      rw [hg2]
      split_ifs with h1 h2 h2
      · rw [← h2]; rw [Array.getElem!_set!_self _ _ _ (by rw [hs1]; omega)]
      · rw [Array.getElem!_set!_ne _ _ _ _ h2, add_zero]
      · omega
      · rw [add_zero]
    have e2N : g2[NS]! = g1[NS]! := by
      rw [hg2]; split_ifs with h1
      · exact Array.getElem!_set!_ne _ _ _ _ (by omega)
      · rfl
    have e3 : ∀ D' < NS, g3[D']! = g2[D']! := by
      intro D' hD'; rw [hg3]; exact Array.getElem!_set!_ne _ _ _ _ (by omega)
    have e3N : g3[NS]! = g2[NS]! + cls[D * 8 + ns]! * acc[D]! + cls[D * 8 + ns + 1]! * acc[D + NS]! := by
      rw [hg3]; exact Array.getElem!_set!_self _ _ _ (by rw [hs2, hg]; omega)
    refine ⟨ih'.1.trans hs3, fun D' hD' => ?_, ?_⟩
    · rw [ih'.2.1 D' hD', e3 D' hD', e2 D' hD', e1 D' hD', Finset.sum_eq_sum_Ico_succ_bot (by omega : D < NS)]
      ring
    · rw [ih'.2.2, e3N, e2N, e1N, Finset.sum_eq_sum_Ico_succ_bot (by omega : D < NS)]
      ring

/-! ## Row construction -/

/-- `emitLoop` appends the entries `(D', acc[D'] wc)` with `acc[D'] ≠ 0`, `D' ∈ [D, NS)`. -/
lemma emitLoop_spec (acc : Array ℕ) (wc : ℕ) :
    ∀ (n D : ℕ) (st m : Array ℕ), NS - D = n → m.size = st.size →
      st.size ≤ (emitLoop acc wc D st m).1.size ∧
      (emitLoop acc wc D st m).2.size = (emitLoop acc wc D st m).1.size ∧
      (∀ q < st.size, (emitLoop acc wc D st m).1[q]! = st[q]! ∧ (emitLoop acc wc D st m).2[q]! = m[q]!) ∧
      (∀ q, st.size ≤ q → q < (emitLoop acc wc D st m).1.size → (emitLoop acc wc D st m).1[q]! < NS) ∧
      ∀ D', ∑ q ∈ Finset.Ico st.size (emitLoop acc wc D st m).1.size,
        (if (emitLoop acc wc D st m).1[q]! = D' then (emitLoop acc wc D st m).2[q]! else 0) =
          if D ≤ D' ∧ D' < NS then acc[D']! * wc else 0 := by
  intro n
  induction n with
  | zero =>
    intro D st m hn hm
    rw [emitLoop, if_neg (by omega)]
    refine ⟨le_rfl, hm, fun q _ => ⟨rfl, rfl⟩, fun q h1 h2 => by simp only at h2; omega, fun D' => ?_⟩
    rw [Finset.Ico_self, Finset.sum_empty, if_neg (by omega)]
  | succ n ih =>
    intro D st m hn hm
    rw [emitLoop, if_pos (by omega)]
    simp only
    by_cases ha : acc[D]! = 0
    · have hb : (acc[D]! != 0) = false := by simp [ha]
      rw [hb, if_neg (by simp)]
      have ih' := ih (D + 1) st m (by omega) hm
      refine ⟨ih'.1, ih'.2.1, ih'.2.2.1, ih'.2.2.2.1, fun D' => ?_⟩
      rw [ih'.2.2.2.2 D']
      by_cases h : D = D'
      · subst h; rw [if_neg (by omega), if_pos ⟨le_rfl, by omega⟩, ha, zero_mul]
      · by_cases h2 : D + 1 ≤ D' ∧ D' < NS
        · rw [if_pos h2, if_pos ⟨by omega, h2.2⟩]
        · rw [if_neg h2, if_neg (by omega)]
    · have hb : (acc[D]! != 0) = true := by simp [ha]
      rw [hb, if_pos rfl]
      have ih' := ih (D + 1) (st.push D) (m.push (acc[D]! * wc)) (by omega) (by simp [hm])
      simp only [Array.size_push] at ih'
      refine ⟨by omega, ih'.2.1, fun q hq => ?_, fun q h1 h2 => ?_, fun D' => ?_⟩
      · have := ih'.2.2.1 q (by omega)
        rw [this.1, this.2, getElem!_push_lt _ _ hq, getElem!_push_lt _ _ (by omega)]
        exact ⟨rfl, rfl⟩
      · by_cases hq : q = st.size
        · subst hq
          rw [(ih'.2.2.1 st.size (by omega)).1, getElem!_push_eq]; omega
        · exact ih'.2.2.2.1 q (by omega) h2
      · rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : st.size < _), ih'.2.2.2.2 D']
        rw [(ih'.2.2.1 st.size (by omega)).1, (ih'.2.2.1 st.size (by omega)).2, getElem!_push_eq,
          show st.size = m.size from hm.symm, getElem!_push_eq]
        by_cases h : D = D'
        · subst h; rw [if_pos rfl, if_neg (by omega), if_pos ⟨le_rfl, by omega⟩, add_zero]
        · rw [if_neg h]
          by_cases h2 : D + 1 ≤ D' ∧ D' < NS
          · rw [if_pos h2, if_pos ⟨by omega, h2.2⟩, zero_add]
          · rw [if_neg h2, if_neg (by omega), zero_add]

/-- `pushSeg` adds the accumulator times `wc` at the previous cell `cb`. -/
lemma pushSeg_spec (r : Row) (hr : RowInv r) (cb wc : ℕ) (acc : Array ℕ) :
    RowInv (pushSeg r cb wc acc) ∧
    (∀ NC, RowWF NC r → cb < NC → RowWF NC (pushSeg r cb wc acc)) ∧
    ∀ ca D, rowVal (pushSeg r cb wc acc) ca D =
      rowVal r ca D + if cb = ca ∧ D < NS then acc[D]! * wc else 0 := by
  obtain ⟨sca, sst, st, m⟩ := r
  have he := emitLoop_spec acc wc NS 0 st m (by omega) hr.msz
  rw [pushSeg_eq]
  generalize emitLoop acc wc 0 st m = E at he ⊢
  obtain ⟨st', m'⟩ := E
  simp only at he ⊢
  obtain ⟨hsz, hmsz, hpre, hnew, hsum⟩ := he
  have hwf : ∀ q : ℕ, (∀ q : ℕ, st[q]! < NS) → st'[q]! < NS := by
    intro q hst
    by_cases h1 : q < st.size
    · rw [(hpre q h1).1]; exact hst q
    · by_cases h2 : q < st'.size
      · exact hnew q (by omega) h2
      · rw [getElem!_neg st' q h2]; exact NS_pos
  by_cases heq : st'.size = st.size
  · rw [if_pos (by simp [heq])]
    refine ⟨⟨hr.ss, by rw [hr.last]; exact heq.symm, by rw [hmsz], fun s hs => by rw [heq]; exact hr.le s hs⟩,
      fun NC hw _ => ⟨hw.ca, fun q => hwf q hw.st⟩, fun ca D => ?_⟩
    rw [rowVal_append ⟨sca, sst, st, m⟩ hr st' m' hsz hpre ca D]
    have h0 := hsum D
    rw [heq, Finset.Ico_self, Finset.sum_empty] at h0
    split_ifs with h
    · rw [if_pos ⟨Nat.zero_le _, h.2⟩] at h0; rw [← h0, add_zero]
    · rw [add_zero]
  · rw [if_neg (by simp [heq])]
    refine ⟨rowInv_append ⟨sca, sst, st, m⟩ hr cb st' m' hsz hmsz (fun q hq => (hpre q hq).1),
      fun NC hw hcb => ⟨fun s hs => ?_, fun q => hwf q hw.st⟩, fun ca D => ?_⟩
    · simp only [Array.size_push] at hs
      by_cases h : s < sca.size
      · rw [getElem!_push_lt _ _ h]; exact hw.ca s h
      · have : s = sca.size := by omega
        rw [this, getElem!_push_eq]; exact hcb
    · rw [rowVal_pushSeg_gen ⟨sca, sst, st, m⟩ hr cb st' m' hsz hpre ca D]
      congr 1
      by_cases h : cb = ca
      · rw [if_pos h, hsum D]
        by_cases h2 : D < NS
        · rw [if_pos ⟨Nat.zero_le _, h2⟩, if_pos ⟨h, h2⟩]
        · rw [if_neg (by omega), if_neg (by omega)]
      · rw [if_neg h, if_neg (fun h' => h h'.1)]

end BHH.W3.Rec
