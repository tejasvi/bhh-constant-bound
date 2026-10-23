/-
Window-3 recursion: the target rows (`W3C.cbLoop`, `W3C.targetRow`), level 2 (`W3C.c1Loop`), the
normalisation (`W3C.normRows`) and the mirror copies (`W3C.fullRows`) as exact `Nat` sums over the row values.
-/
import W3.RecLoop3

namespace BHH.W3.Rec

open W3C W2C BHH BHH.W2

attribute [local irreducible] W3C.NS W3C.reachable W3C.trs W3C.cls

/-! ## Target rows -/

/-- `cbLoop`: the closing sum and the new row (previous cells `cb' ∈ [cb, NC)`). -/
lemma cbLoop_spec (lower : Bool) (rd : RecData3) (rows : Array Row) (cc wc NC : ℕ) (last : Bool) :
    ∀ (n cb : ℕ) (r : Row) (cs : ℕ), NC - cb = n →
      (cbLoop lower rd rows cc wc NC last cb r cs).2 =
        cs + ∑ cb' ∈ Finset.Ico cb NC, (accOf lower rd rows cc cb')[NS]! ∧
      (last = false → RowInv r →
        RowInv (cbLoop lower rd rows cc wc NC last cb r cs).1 ∧
        (∀ NC', RowWF NC' r → NC ≤ NC' → RowWF NC' (cbLoop lower rd rows cc wc NC last cb r cs).1) ∧
        ∀ ca D, rowVal (cbLoop lower rd rows cc wc NC last cb r cs).1 ca D = rowVal r ca D +
          ∑ cb' ∈ Finset.Ico cb NC, if cb' = ca ∧ D < NS then (accOf lower rd rows cc cb')[D]! * wc else 0) := by
  intro n
  induction n with
  | zero =>
    intro cb r cs hn
    rw [cbLoop, if_neg (by omega)]
    refine ⟨by rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty, add_zero], fun _ hr => ⟨hr, fun NC' h _ => h,
      fun ca D => by rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty, add_zero]⟩⟩
  | succ n ih =>
    intro cb r cs hn
    rw [cbLoop, if_pos (by omega)]
    simp only
    have ih' := ih (cb + 1) (if last then r else pushSeg r cb wc (accOf lower rd rows cc cb))
      (cs + (accOf lower rd rows cc cb)[NS]!) (by omega)
    refine ⟨by rw [ih'.1, Finset.sum_eq_sum_Ico_succ_bot (by omega : cb < NC)]; ring, fun hl hr => ?_⟩
    subst hl
    simp only [Bool.false_eq_true, ite_false] at ih' ⊢
    have hp := pushSeg_spec r hr cb wc (accOf lower rd rows cc cb)
    obtain ⟨h1, h2, h3⟩ := ih'.2 trivial hp.1
    refine ⟨h1, fun NC' hw hle => h2 NC' (hp.2.1 NC' hw (by omega)) hle, fun ca D => ?_⟩
    rw [h3 ca D, Finset.sum_eq_sum_Ico_succ_bot (by omega : cb < NC), hp.2.2 ca D]
    ring

lemma targetRow_eq (lower : Bool) (rd : RecData3) (rows : Array Row) (last : Bool) (cc : ℕ) :
    targetRow lower rd rows last cc =
      ((cbLoop lower rd rows cc rd.w[cc / rd.NT]! (rd.NR * rd.NT) last 0 Row.empty 0).1,
       (cbLoop lower rd rows cc rd.w[cc / rd.NT]! (rd.NR * rd.NT) last 0 Row.empty 0).2 * rd.w[cc / rd.NT]!) := rfl

/-- The closing sum of a target. -/
lemma targetRow_snd (lower : Bool) (rd : RecData3) (rows : Array Row) (last : Bool) (cc : ℕ) :
    (targetRow lower rd rows last cc).2 =
      (∑ cb ∈ Finset.range (rd.NR * rd.NT), (accOf lower rd rows cc cb)[NS]!) * rd.w[cc / rd.NT]! := by
  rw [targetRow_eq]
  simp only
  rw [(cbLoop_spec lower rd rows cc rd.w[cc / rd.NT]! (rd.NR * rd.NT) last (rd.NR * rd.NT) 0 Row.empty 0
    (by omega)).1, zero_add, Finset.range_eq_Ico]

/-- The row of a target (not the last level). -/
lemma targetRow_fst (lower : Bool) (rd : RecData3) (rows : Array Row) (cc : ℕ) :
    RowInv (targetRow lower rd rows false cc).1 ∧ RowWF (rd.NR * rd.NT) (targetRow lower rd rows false cc).1 ∧
    ∀ ca D, rowVal (targetRow lower rd rows false cc).1 ca D =
      if ca < rd.NR * rd.NT ∧ D < NS then (accOf lower rd rows cc ca)[D]! * rd.w[cc / rd.NT]! else 0 := by
  rw [targetRow_eq]
  simp only
  have h := (cbLoop_spec lower rd rows cc rd.w[cc / rd.NT]! (rd.NR * rd.NT) false (rd.NR * rd.NT) 0 Row.empty 0
    (by omega)).2 rfl rowInv_empty
  refine ⟨h.1, h.2.1 _ (rowWF_empty _) le_rfl, fun ca D => ?_⟩
  rw [h.2.2 ca D, rowVal_empty, zero_add]
  by_cases hc : ca < rd.NR * rd.NT
  · rw [Finset.sum_eq_single ca]
    · by_cases hD : D < NS
      · rw [if_pos ⟨rfl, hD⟩, if_pos ⟨hc, hD⟩]
      · rw [if_neg (fun h => hD h.2), if_neg (fun h => hD h.2)]
    · intro b _ hb; rw [if_neg (fun h => hb h.1)]
    · intro h; exact absurd (Finset.mem_Ico.mpr ⟨Nat.zero_le _, hc⟩) h
  · rw [if_neg (fun h => hc h.1)]
    apply Finset.sum_eq_zero
    intro b hb
    rw [Finset.mem_Ico] at hb
    rw [if_neg (fun h => by rw [← h.1] at hc; exact hc hb.2)]

/-! ## Level 2 -/

/-- the entry of the source cell `c1` of the level-2 target `(ir2, it2)` -/
def c1D (rd : RecData3) (c1 : ℕ) : ℕ := trs[rd.nb[c1 / rd.NT]!]!

def c1Pi (rd : RecData3) (ir2 it2 c1 : ℕ) : ℕ := (c1 / rd.NT * rd.NR + ir2) * rd.ND + (it2 + (rd.NT - 1) - c1 % rd.NT)

def c1V (lower : Bool) (rd : RecData3) (f1 k2 : Array ℕ) (ir2 it2 c1 : ℕ) : ℕ :=
  mul62 lower (rd.w[c1 / rd.NT]! * f1[c1 / rd.NT]!) k2[c1Pi rd ir2 it2 c1]!

def c1Idx (rd : RecData3) (ir2 it2 n2 c1 : ℕ) : ℕ := c1D rd c1 * 8 + n2 + rd.sb[c1Pi rd ir2 it2 c1]!

/-- `c1Loop`: the closing sum and the level-2 row. -/
lemma c1Loop_spec (lower : Bool) (rd : RecData3) (f1 k2 : Array ℕ) (ir2 it2 n2 w2 NC : ℕ) :
    ∀ (n c1 : ℕ) (r : Row) (cs : ℕ), NC - c1 = n → RowInv r →
      (c1Loop lower rd f1 k2 ir2 it2 n2 w2 NC c1 r cs).2 = cs + ∑ c ∈ Finset.Ico c1 NC,
        (if c1D rd c < NS then cls[c1Idx rd ir2 it2 n2 c]! * c1V lower rd f1 k2 ir2 it2 c else 0) ∧
      RowInv (c1Loop lower rd f1 k2 ir2 it2 n2 w2 NC c1 r cs).1 ∧
      (∀ NC', RowWF NC' r → NC ≤ NC' → RowWF NC' (c1Loop lower rd f1 k2 ir2 it2 n2 w2 NC c1 r cs).1) ∧
      ∀ ca D, rowVal (c1Loop lower rd f1 k2 ir2 it2 n2 w2 NC c1 r cs).1 ca D = rowVal r ca D +
        ∑ c ∈ Finset.Ico c1 NC, (if c = ca ∧ c1D rd c < NS ∧ trs[c1Idx rd ir2 it2 n2 c]! = D ∧ D < NS then
          c1V lower rd f1 k2 ir2 it2 c * w2 else 0) := by
  intro n
  induction n with
  | zero =>
    intro c1 r cs hn hr
    rw [c1Loop, if_neg (by omega)]
    refine ⟨by rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty, add_zero], hr, fun NC' h _ => h,
      fun ca D => by rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty, add_zero]⟩
  | succ n ih =>
    intro c1 r cs hn hr
    rw [c1Loop, if_pos (by omega)]
    simp only
    by_cases hD : trs[rd.nb[c1 / rd.NT]!]! < NS
    · rw [if_pos hD]
      set v := mul62 lower (rd.w[c1 / rd.NT]! * f1[c1 / rd.NT]!) k2[(c1 / rd.NT * rd.NR + ir2) * rd.ND +
        (it2 + (rd.NT - 1) - c1 % rd.NT)]! with hv
      set idx := trs[rd.nb[c1 / rd.NT]!]! * 8 + n2 + rd.sb[(c1 / rd.NT * rd.NR + ir2) * rd.ND +
        (it2 + (rd.NT - 1) - c1 % rd.NT)]! with hidx
      have ev : c1V lower rd f1 k2 ir2 it2 c1 = v := rfl
      have ei : c1Idx rd ir2 it2 n2 c1 = idx := rfl
      have eD : c1D rd c1 = trs[rd.nb[c1 / rd.NT]!]! := rfl
      by_cases hp : trs[idx]! < NS ∧ v ≠ 0
      · have hb : (decide (trs[idx]! < NS) && v != 0) = true := by simp [hp.1, hp.2]
        rw [if_pos hb]
        obtain ⟨sca, sst, st, m⟩ := r
        simp only
        have hr2 : RowInv ⟨sca.push c1, sst.push (st.size + 1), st.push trs[idx]!, m.push (v * w2)⟩ := by
          have := rowInv_append ⟨sca, sst, st, m⟩ hr c1 (st.push trs[idx]!) (m.push (v * w2)) (by simp)
            (by simp [hr.msz]) (fun q hq => getElem!_push_lt _ _ hq)
          simpa using this
        have ih' := ih (c1 + 1) ⟨sca.push c1, sst.push (st.size + 1), st.push trs[idx]!, m.push (v * w2)⟩
          (cs + cls[idx]! * v) (by omega) hr2
        refine ⟨by rw [ih'.1, Finset.sum_eq_sum_Ico_succ_bot (by omega : c1 < NC), eD, if_pos hD, ev, ei]; ring,
          ih'.2.1, fun NC' hw hle => ih'.2.2.1 NC' ⟨fun s hs => ?_, fun q => ?_⟩ hle, fun ca D => ?_⟩
        · simp only [Array.size_push] at hs
          by_cases h : s < sca.size
          · rw [getElem!_push_lt _ _ h]; exact hw.ca s h
          · have : s = sca.size := by omega
            rw [this, getElem!_push_eq]; omega
        · by_cases h : q < st.size
          · rw [getElem!_push_lt _ _ h]; exact hw.st q
          · by_cases h2 : q = st.size
            · rw [h2, getElem!_push_eq]; exact hp.1
            · rw [getElem!_neg _ q (by simp; omega)]; exact NS_pos
        · rw [ih'.2.2.2 ca D, Finset.sum_eq_sum_Ico_succ_bot (by omega : c1 < NC)]
          have hrv := rowVal_pushSeg_gen ⟨sca, sst, st, m⟩ hr c1 (st.push trs[idx]!) (m.push (v * w2)) (by simp)
            (fun q hq => ⟨getElem!_push_lt _ _ hq, getElem!_push_lt _ _ (by rw [hr.msz]; exact hq)⟩) ca D
          simp only [Array.size_push] at hrv
          rw [hrv]
          have hs : ∑ q ∈ Finset.Ico st.size (st.size + 1),
              (if (st.push trs[idx]!)[q]! = D then (m.push (v * w2))[q]! else 0) =
              if trs[idx]! = D then v * w2 else 0 := by
            rw [Finset.sum_eq_single st.size]
            · rw [getElem!_push_eq, show st.size = m.size from hr.msz.symm, getElem!_push_eq]
            · intro b hb hne; rw [Finset.mem_Ico] at hb; omega
            · intro h; exact absurd (Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩) h
          rw [hs, eD, ev, ei]
          by_cases hca : c1 = ca
          · rw [if_pos hca]
            by_cases hDD : trs[idx]! = D
            · rw [if_pos hDD, if_pos ⟨hca, hD, hDD, by rw [← hDD]; exact hp.1⟩]; ring
            · rw [if_neg hDD, if_neg (fun h => hDD h.2.2.1)]; ring
          · rw [if_neg hca, if_neg (fun h => hca h.1)]; ring
      · have hb : (decide (trs[idx]! < NS) && v != 0) = false := by
          by_cases h1 : trs[idx]! < NS
          · have h2 : v = 0 := by by_contra h2; exact hp ⟨h1, h2⟩
            simp [h2]
          · simp [h1]
        rw [if_neg (by rw [hb]; simp)]
        have ih' := ih (c1 + 1) r (cs + cls[idx]! * v) (by omega) hr
        refine ⟨by rw [ih'.1, Finset.sum_eq_sum_Ico_succ_bot (by omega : c1 < NC), eD, if_pos hD, ev, ei]; ring,
          ih'.2.1, ih'.2.2.1, fun ca D => ?_⟩
        rw [ih'.2.2.2 ca D, Finset.sum_eq_sum_Ico_succ_bot (by omega : c1 < NC), eD, ev, ei]
        have h0 : (if c1 = ca ∧ trs[rd.nb[c1 / rd.NT]!]! < NS ∧ trs[idx]! = D ∧ D < NS then v * w2 else 0) = 0 := by
          by_cases h1 : c1 = ca ∧ trs[rd.nb[c1 / rd.NT]!]! < NS ∧ trs[idx]! = D ∧ D < NS
          · rw [if_pos h1]
            have : v = 0 := by
              by_contra h2; exact hp ⟨by rw [h1.2.2.1]; exact h1.2.2.2, h2⟩
            rw [this, zero_mul]
          · rw [if_neg h1]
        rw [h0]; ring
    · rw [if_neg hD]
      have ih' := ih (c1 + 1) r cs (by omega) hr
      have eD : c1D rd c1 = trs[rd.nb[c1 / rd.NT]!]! := rfl
      refine ⟨by rw [ih'.1, Finset.sum_eq_sum_Ico_succ_bot (by omega : c1 < NC), eD, if_neg hD]; ring,
        ih'.2.1, ih'.2.2.1, fun ca D => ?_⟩
      rw [ih'.2.2.2 ca D, Finset.sum_eq_sum_Ico_succ_bot (by omega : c1 < NC), eD,
        if_neg (fun h => hD h.2.1)]
      ring

/-! ## Normalisation and mirror copies -/

/-- A row with every mantissa rounded by `sh` bits. -/
def normRow (lower : Bool) (sh : ℕ) (r : Row) : Row := { r with m := r.m.map fun v => rnd lower v sh }

lemma normRow_zero (lower : Bool) (r : Row) : normRow lower 0 r = r := by
  unfold normRow
  have : r.m.map (fun v => rnd lower v 0) = r.m := by
    rw [show (fun v => rnd lower v 0) = id from funext fun v => rnd_sh0 lower v, Array.map_id]
  rw [this]


lemma normRows_eq (lower : Bool) (rows : Array Row) :
    ∃ sh, normRows lower rows = (rows.map (normRow lower sh), sh) := by
  have hid : rows.map (normRow lower 0) = rows := by
    rw [show normRow lower 0 = id from funext (normRow_zero lower), Array.map_id]
  unfold normRows
  simp only
  split_ifs with h1 h2 h2
  · exact ⟨0, by rw [hid]⟩
  · exact ⟨_, rfl⟩
  · exact ⟨0, by rw [hid]⟩
  · simp at h2

lemma normRows_get (lower : Bool) (rows : Array Row) {i : ℕ} (hi : i < rows.size) :
    (normRows lower rows).1[i]! = normRow lower (normRows lower rows).2 rows[i]! := by
  obtain ⟨sh, h⟩ := normRows_eq lower rows
  rw [h]
  simp only
  rw [getElem!_map _ _ hi]

lemma normRows_size (lower : Bool) (rows : Array Row) : (normRows lower rows).1.size = rows.size := by
  obtain ⟨sh, h⟩ := normRows_eq lower rows
  rw [h]; simp

lemma getElem!_map_zero {f : ℕ → ℕ} (hf : f 0 = 0) (a : Array ℕ) (q : ℕ) : (a.map f)[q]! = f a[q]! := by
  by_cases hq : q < a.size
  · exact getElem!_map f a hq
  · rw [getElem!_neg (a.map f) q (by simpa using hq), getElem!_neg a q hq]; exact hf.symm

lemma rowVal_normRow (lower : Bool) (sh : ℕ) (r : Row) (ca D : ℕ) :
    rowVal (normRow lower sh r) ca D = ∑ s ∈ Finset.range r.segCa.size, if r.segCa[s]! = ca then
      ∑ q ∈ Finset.Ico r.segStart[s]! r.segStart[s + 1]!, (if r.st[q]! = D then rnd lower r.m[q]! sh else 0)
    else 0 := by
  unfold rowVal normRow
  simp only
  apply Finset.sum_congr rfl
  intro s _
  split_ifs
  · apply Finset.sum_congr rfl
    intro q _
    rw [getElem!_map_zero (rnd_zero lower sh)]
  · rfl

lemma zp2' (a b : ℤ) : (2 : ℝ) ^ (a + b) = 2 ^ a * 2 ^ b := zpow_add₀ two_ne_zero a b

/-- The rounded row bounds the row (scale exponent dropping by `sh`). -/
lemma normRow_bd (lower : Bool) (sh : ℕ) (r : Row) (E : ℤ) (ca D : ℕ) :
    Bd lower ((rowVal (normRow lower sh r) ca D : ℝ) * (2 : ℝ) ^ (-(E - sh))) ((rowVal r ca D : ℝ) * (2 : ℝ) ^ (-E)) := by
  rw [rowVal_normRow]
  unfold rowVal
  push_cast
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Bd.sum
  intro s _
  split_ifs
  · rw [Finset.sum_mul, Finset.sum_mul]
    apply Bd.sum
    intro q _
    split_ifs
    · have e : (2 : ℝ) ^ (-(E - (sh : ℤ))) = (2 : ℝ) ^ (-E) * 2 ^ sh := by
        rw [show -(E - (sh : ℤ)) = -E + (sh : ℤ) by ring, zp2', zpow_natCast]
      rw [e]
      have h := Bd.mul_right (by positivity : (0 : ℝ) ≤ 2 ^ (-E) * 2 ^ sh) (rnd_bd lower r.m[q]! sh)
      refine Bd.trans h (Bd.of_eq ?_)
      field_simp
    · simp only [zero_mul]; exact Bd.refl _ _
  · simp only [zero_mul]; exact Bd.refl _ _

/-- The rows of all cells from the half. -/
lemma fullRows_get (NR NT : ℕ) (half : Array Row) {c : ℕ} (hc : c < NR * NT) :
    (fullRows NR NT half)[c]! =
      if NT / 2 ≤ c % NT then half[(c / NT) * (NT / 2) + (c % NT - NT / 2)]!
      else { half[(c / NT) * (NT / 2) + (NT - 1 - c % NT - NT / 2)]! with
        segCa := half[(c / NT) * (NT / 2) + (NT - 1 - c % NT - NT / 2)]!.segCa.map (mirC NT) } := by
  unfold fullRows
  rw [getElem!_map _ _ (by simpa using hc), range_getElem! hc]

/-- The mirrored row. -/
lemma rowVal_mir {NR NT : ℕ} (hNT : 0 < NT) (r : Row) (hr : ∀ s < r.segCa.size, r.segCa[s]! < NR * NT)
    {ca : ℕ} (hca : ca < NR * NT) (D : ℕ) :
    rowVal { r with segCa := r.segCa.map (mirC NT) } ca D = rowVal r (mirC NT ca) D := by
  unfold rowVal
  simp only [Array.size_map]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.mem_range] at hs
  rw [getElem!_map _ _ hs]
  have hiff : mirC NT r.segCa[s]! = ca ↔ r.segCa[s]! = mirC NT ca := by
    constructor
    · intro h; rw [← h, mirC_mirC hNT]
    · intro h; rw [h, mirC_mirC hNT]
  by_cases h : r.segCa[s]! = mirC NT ca
  · rw [if_pos (hiff.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]

lemma rowWF_mir {NR NT : ℕ} (hNT : 0 < NT) (r : Row) (hr : RowWF (NR * NT) r) :
    RowWF (NR * NT) { r with segCa := r.segCa.map (mirC NT) } := by
  refine ⟨fun s hs => ?_, hr.st⟩
  simp only [Array.size_map] at hs
  simp only
  rw [getElem!_map _ _ hs]
  exact mirC_lt hNT (hr.ca s hs)

lemma rowWF_normRow (lower : Bool) (sh NC : ℕ) (r : Row) (hr : RowWF NC r) : RowWF NC (normRow lower sh r) :=
  ⟨hr.ca, hr.st⟩

lemma rowInv_normRow (lower : Bool) (sh : ℕ) (r : Row) (hr : RowInv r) : RowInv (normRow lower sh r) := by
  refine ⟨hr.ss, hr.last, ?_, hr.le⟩
  show (r.m.map fun v => rnd lower v sh).size = r.st.size
  rw [Array.size_map]; exact hr.msz

lemma rowInv_mir (NT : ℕ) (r : Row) (hr : RowInv r) : RowInv { r with segCa := r.segCa.map (mirC NT) } := by
  refine ⟨?_, ?_, hr.msz, ?_⟩
  · show r.segStart.size = (r.segCa.map (mirC NT)).size + 1
    rw [Array.size_map]; exact hr.ss
  · show r.segStart[(r.segCa.map (mirC NT)).size]! = r.st.size
    rw [Array.size_map]; exact hr.last
  · intro s hs
    simp only [Array.size_map] at hs
    exact hr.le s hs

/-! ## The mantissas after `normRows` -/

lemma foldl_max_ge (l : List ℕ) : ∀ a, a ≤ l.foldl max a ∧ ∀ x ∈ l, x ≤ l.foldl max a := by
  induction l with
  | nil => intro a; simp
  | cons y l ih =>
    intro a
    simp only [List.foldl_cons, List.mem_cons]
    obtain ⟨h1, h2⟩ := ih (max a y)
    refine ⟨le_trans (le_max_left a y) h1, fun x hx => ?_⟩
    rcases hx with rfl | hx
    · exact le_trans (le_max_right a x) h1
    · exact h2 x hx

lemma foldl_rows_max (L : List Row) : ∀ a,
    a ≤ L.foldl (fun acc r => r.m.foldl max acc) a ∧
      ∀ r ∈ L, ∀ x ∈ r.m.toList, x ≤ L.foldl (fun acc r => r.m.foldl max acc) a := by
  induction L with
  | nil => intro a; simp
  | cons r0 L ih =>
    intro a
    simp only [List.foldl_cons, List.mem_cons]
    obtain ⟨h1, h2⟩ := ih (r0.m.foldl max a)
    have h3 := foldl_max_ge r0.m.toList a
    rw [Array.foldl_toList] at h3
    refine ⟨le_trans h3.1 h1, fun r hr x hx => ?_⟩
    rcases hr with rfl | hr
    · exact le_trans (h3.2 x hx) h1
    · exact h2 r hr x hx

/-- Every mantissa is at most the maximum computed by `normRows`. -/
lemma le_rowsMax (rows : Array Row) {i : ℕ} (hi : i < rows.size) (q : ℕ) :
    rows[i]!.m[q]! ≤ rows.foldl (fun acc r => r.m.foldl max acc) 0 := by
  rw [← Array.foldl_toList]
  by_cases hq : q < rows[i]!.m.size
  · apply (foldl_rows_max rows.toList 0).2 rows[i]!
    · rw [getElem!_pos rows i hi]; exact Array.getElem_mem_toList hi
    · rw [getElem!_pos rows[i]!.m q hq]; exact Array.getElem_mem_toList hq
  · rw [getElem!_neg rows[i]!.m q hq]; exact Nat.zero_le _

lemma rnd_le_pow (lower : Bool) {v mx k : ℕ} (hv : v ≤ mx) (hmx : mx < 2 ^ (62 + k)) : rnd lower v k ≤ 2 ^ 62 := by
  unfold rnd
  have hp : (0 : ℕ) < 2 ^ k := by positivity
  have e : (2 : ℕ) ^ (62 + k) = 2 ^ 62 * 2 ^ k := by rw [pow_add]
  cases lower
  · simp only [Bool.false_eq_true, ↓reduceIte, Nat.shiftRight_eq_div_pow]
    rw [e] at hmx
    have h1 : (v + (2 ^ k - 1)) / 2 ^ k < 2 ^ 62 + 1 := by
      rw [Nat.div_lt_iff_lt_mul hp, show (2 ^ 62 + 1) * 2 ^ k = 2 ^ 62 * 2 ^ k + 2 ^ k by ring]
      omega
    omega
  · simp only [↓reduceIte, Nat.shiftRight_eq_div_pow]
    apply Nat.div_le_of_le_mul
    rw [e] at hmx
    nlinarith

/-- The rows returned by `normRows` have mantissas at most `2^62`. -/
theorem normRows_mant (lower : Bool) (rows : Array Row) {i : ℕ} (hi : i < rows.size) (q : ℕ) :
    (normRows lower rows).1[i]!.m[q]! ≤ 2 ^ 62 := by
  have hle := le_rowsMax rows hi q
  set mx := rows.foldl (fun acc r => r.m.foldl max acc) 0 with hmx
  have hlt : mx < 2 ^ (Nat.log2 mx + 1) := Nat.lt_log2_self
  unfold normRows
  simp only [← hmx]
  by_cases h62 : nbits mx > 62
  · have hsh : (if nbits mx > 62 then nbits mx - 62 else 0) = nbits mx - 62 := if_pos h62
    rw [hsh]
    have hne : ¬ ((nbits mx - 62 == 0) = true) := by simp; unfold nbits at h62 ⊢; omega
    rw [if_neg hne]
    simp only
    rw [getElem!_map _ _ hi]
    simp only
    rw [getElem!_map_zero (f := fun v => rnd lower v (nbits mx - 62)) (rnd_zero lower _)]
    apply rnd_le_pow lower hle
    unfold nbits at h62 ⊢
    rw [show 62 + (Nat.log2 mx + 1 - 62) = Nat.log2 mx + 1 by omega]
    exact hlt
  · have hsh : (if nbits mx > 62 then nbits mx - 62 else 0) = 0 := if_neg h62
    rw [hsh, if_pos (by simp)]
    simp only
    unfold nbits at h62
    calc rows[i]!.m[q]! ≤ mx := hle
      _ ≤ 2 ^ (Nat.log2 mx + 1) := hlt.le
      _ ≤ 2 ^ 62 := Nat.pow_le_pow_right (by norm_num) (by omega)

end BHH.W3.Rec
