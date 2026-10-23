/-
Window-3 recursion: one level of `W3C.runT3` bounds the exact recursion.  For read-only data `rd`
describing the tables of `D` at `t` (`RdOK`: weights, the inputs `N`, `S`, `T`, the triple kernels as directed
bounds) and rows bounding `Fx n` at scale `2^-E` (`RowsBd`), the target `cc` gives a closing sum bounding `Clo n cc`
and (not at the last level) a row bounding `Fx (n + 1) cc ·` at scale `2^-(E - 14 + PR)`.
-/
import W3.RecLoop3b

open Real

namespace BHH.W3.Rec

open W3C W2C BHH BHH.W2 BHH.Cert

attribute [local irreducible] W3C.NS W3C.reachable W3C.trs W3C.cls

/-! ## Indices of `accOf` -/

/-- the pair index of `(cb, cc)` -/
def pbcOf (rd : RecData3) (cb cc : ℕ) : ℕ :=
  (cb / rd.NT * rd.NR + cc / rd.NT) * rd.ND + (cc % rd.NT + (rd.NT - 1) - cb % rd.NT)

/-- the base triple index of `(cb, cc)` -/
def baseOf (rd : RecData3) (cb cc : ℕ) : ℕ := (pbcOf rd cb cc * rd.NR) * rd.ND + cb % rd.NT + (rd.NT - 1)

/-- the triple index of `(ca, cb, cc)` -/
def t3Of (rd : RecData3) (ca cb cc : ℕ) : ℕ := baseOf rd cb cc + (ca / rd.NT) * rd.ND - ca % rd.NT

/-- the MAC accumulator of `(cc, cb)` (index `D + NS T`) -/
def accS (lower : Bool) (rd : RecData3) (rows : Array Row) (cc cb : ℕ) : Array ℕ :=
  segLoop lower rows[cb]! rd.K3 (baseOf rd cb cc) rd.NT rd.ND 0 rows[cb]!.segCa.size (Array.replicate (2 * NS) 0)

/-- the input `4 N + 2 S` of `(cb, cc)` -/
def nsOf (rd : RecData3) (cb cc : ℕ) : ℕ := rd.nb[cc / rd.NT]! + rd.sb[pbcOf rd cb cc]!

lemma accOf_eq (lower : Bool) (rd : RecData3) (rows : Array Row) (cc cb : ℕ) :
    accOf lower rd rows cc cb = transLoop (accS lower rd rows cc cb) (nsOf rd cb cc) 0 (Array.replicate (NS + 1) 0) :=
  rfl

/-- The accumulator entries of `accOf`. -/
lemma accOf_get (lower : Bool) (rd : RecData3) (rows : Array Row) (cc cb : ℕ) (hwf : ∀ q : ℕ, rows[cb]!.st[q]! < NS) :
    (∀ s < NS, (accOf lower rd rows cc cb)[s]! = ∑ q ∈ Finset.range NS,
      ((if trs[q * 8 + nsOf rd cb cc]! = s then (accS lower rd rows cc cb)[q]! else 0) +
       (if trs[q * 8 + nsOf rd cb cc + 1]! = s then (accS lower rd rows cc cb)[q + NS]! else 0))) ∧
    (accOf lower rd rows cc cb)[NS]! = ∑ q ∈ Finset.range NS,
      (cls[q * 8 + nsOf rd cb cc]! * (accS lower rd rows cc cb)[q]! +
       cls[q * 8 + nsOf rd cb cc + 1]! * (accS lower rd rows cc cb)[q + NS]!) := by
  rw [accOf_eq]
  have h := transLoop_spec (accS lower rd rows cc cb) (nsOf rd cb cc) NS 0 (Array.replicate (NS + 1) 0)
    (by omega) (by simp)
  refine ⟨fun s hs => ?_, ?_⟩
  · rw [h.2.1 s hs, getElem!_replicate _ (by omega), zero_add, Finset.range_eq_Ico]
  · rw [h.2.2, getElem!_replicate _ (by omega), zero_add, Finset.range_eq_Ico]

lemma key_N {N a b c d : ℕ} (ha : a < N) (hb : b < 2) (hc : c < N) (hd : d < 2) :
    a + N * b = c + N * d ↔ a = c ∧ b = d := by
  constructor
  · intro h
    rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl <;>
      rcases (show d = 0 ∨ d = 1 by omega) with rfl | rfl <;> constructor <;> omega
  · rintro ⟨rfl, rfl⟩; rfl

lemma key_ns {a b c d : ℕ} (ha : a < NS) (hb : b < 2) (hc : c < NS) (hd : d < 2) :
    a + NS * b = c + NS * d ↔ a = c ∧ b = d := key_N ha hb hc hd

lemma idx_N {N D T : ℕ} (hD : D < N) (hT : T < 2) : D + N * T < 2 * N := by
  rcases (show T = 0 ∨ T = 1 by omega) with rfl | rfl <;> omega

/-- The MAC accumulator as a sum over the segments and entries, for `D < NS`, `T < 2`. -/
lemma accS_get (lower : Bool) (rd : RecData3) (rows : Array Row) (cc cb : ℕ) (hwf : ∀ q : ℕ, rows[cb]!.st[q]! < NS)
    (hinv : RowInv rows[cb]!) (hm62 : ∀ q : ℕ, rows[cb]!.m[q]! ≤ 2 ^ 62)
    {D T : ℕ} (hD : D < NS) (hT : T < 2) :
    (accS lower rd rows cc cb)[D + NS * T]! = ∑ s ∈ Finset.range rows[cb]!.segCa.size,
      if rd.K3[t3Of rd rows[cb]!.segCa[s]! cb cc]! % 2 = T then
        ∑ q ∈ Finset.Ico rows[cb]!.segStart[s]! rows[cb]!.segStart[s + 1]!,
          (if rows[cb]!.st[q]! = D then
            mulTop lower (rows[cb]!.m[q]! >>> 31) (rows[cb]!.m[q]! &&& m31)
              ((rd.K3[t3Of rd rows[cb]!.segCa[s]! cb cc]! >>> 1) >>> 31)
              ((rd.K3[t3Of rd rows[cb]!.segCa[s]! cb cc]! >>> 1) &&& m31) else 0)
      else 0 := by
  unfold accS
  rw [(segLoop_spec lower rows[cb]! rd.K3 (baseOf rd cb cc) rd.NT rd.ND hwf hinv hm62 _ 0 _ _ rfl le_rfl
    (by simp)).2,
    getElem!_replicate _ (idx_N hD hT), zero_add,
    Finset.range_eq_Ico]
  apply Finset.sum_congr rfl
  intro s _
  have hk : kkOf rows[cb]! rd.K3 (baseOf rd cb cc) rd.NT rd.ND s = rd.K3[t3Of rd rows[cb]!.segCa[s]! cb cc]! := rfl
  rw [hk]
  set kk := rd.K3[t3Of rd rows[cb]!.segCa[s]! cb cc]!
  have hk2 : kk % 2 < 2 := Nat.mod_lt _ (by norm_num)
  by_cases hkT : kk % 2 = T
  · rw [if_pos hkT]
    apply Finset.sum_congr rfl
    intro q _
    rw [if_congr (key_ns (hwf q) hk2 hD hT) rfl rfl]
    by_cases hq : rows[cb]!.st[q]! = D
    · rw [if_pos ⟨hq, hkT⟩, if_pos hq]
    · rw [if_neg (fun h => hq h.1), if_neg hq]
  · rw [if_neg hkT]
    apply Finset.sum_eq_zero
    intro q _
    rw [if_congr (key_ns (hwf q) hk2 hD hT) rfl rfl, if_neg (fun h => hkT h.2)]

/-- A weighted sum of the values of a row, as a sum over its segments. -/
lemma sum_rowVal (r : Row) (NC : ℕ) (hca : ∀ s < r.segCa.size, r.segCa[s]! < NC) (D : ℕ) (f : ℕ → ℝ) :
    ∑ ca ∈ Finset.range NC, f ca * (rowVal r ca D : ℝ) =
      ∑ s ∈ Finset.range r.segCa.size, f r.segCa[s]! *
        ∑ q ∈ Finset.Ico r.segStart[s]! r.segStart[s + 1]!, (if r.st[q]! = D then (r.m[q]! : ℝ) else 0) := by
  unfold rowVal
  push_cast
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.mem_range] at hs
  rw [Finset.sum_eq_single r.segCa[s]!]
  · rw [if_pos rfl, Finset.mul_sum]
  · intro ca _ hne
    rw [if_neg (fun h => hne h.symm), mul_zero]
  · intro h; exact absurd (Finset.mem_range.mpr (hca s hs)) h

/-! ## The read-only data of a level -/

/-- The read-only data `rd` describes the tables of `D` at `t` (directed kernels). -/
structure RdOK (lower : Bool) (rd : RecData3) (g : GridR) (D : DiscData3) (t : ℝ) : Prop where
  NR : rd.NR = g.NR
  NT : rd.NT = g.NT
  NTpos : 0 < g.NT
  w : ∀ c < g.NR * g.NT, ((rd.w[c / rd.NT]! : ℕ) : ℝ) / 2 ^ PR = wC g D c
  nb : ∀ c < g.NR * g.NT, rd.nb[c / rd.NT]! = 4 * b2n (nC g D c)
  sb : ∀ cb < g.NR * g.NT, ∀ cc < g.NR * g.NT, rd.sb[pbcOf rd cb cc]! = 2 * b2n (sC g D cb cc)
  kT : ∀ ca < g.NR * g.NT, ∀ cb < g.NR * g.NT, ∀ cc < g.NR * g.NT,
    rd.K3[t3Of rd ca cb cc]! % 2 = b2n (tC g D ca cb cc)
  kK : ∀ ca < g.NR * g.NT, ∀ cb < g.NR * g.NT, ∀ cc < g.NR * g.NT,
    Bd lower (((rd.K3[t3Of rd ca cb cc]! >>> 1 : ℕ) : ℝ) / 2 ^ 62) (k3C g D t ca cb cc)

/-- The rows bound `Fx n` at scale `2^-E`. -/
def RowsBd (lower : Bool) (g : GridR) (D : DiscData3) (t : ℝ) (rows : Array Row) (E : ℤ) (n : ℕ) : Prop :=
  ∀ cb < g.NR * g.NT, RowWF (g.NR * g.NT) rows[cb]! ∧ RowInv rows[cb]! ∧
    ∀ ca < g.NR * g.NT, ∀ s < NS, Bd lower ((rowVal rows[cb]! ca s : ℝ) * (2 : ℝ) ^ (-E)) (Fx g D t n cb ca s)

/-- The mantissas of the rows (fed to the `UInt64` MAC loop) are at most `2^62`. -/
def MantBd (rows : Array Row) (NC : ℕ) : Prop := ∀ cb < NC, ∀ q : ℕ, rows[cb]!.m[q]! ≤ 2 ^ 62

lemma b2n_lt (b : Bool) : b2n b < 2 := by cases b <;> decide

lemma inp_eq (a b c : Bool) : inp a b c = (4 * b2n a + 2 * b2n b) + b2n c := rfl

section Step

variable {lower : Bool} {rd : RecData3} {g : GridR} {D : DiscData3} {t : ℝ}

lemma wC_nonneg (hrd : RdOK lower rd g D t) {c : ℕ} (hc : c < g.NR * g.NT) : 0 ≤ wC g D c := by
  have h := hrd.w c hc
  rw [← h]
  exact div_nonneg (Nat.cast_nonneg _) (by positivity)

lemma nsOf_eq (hrd : RdOK lower rd g D t) {cb cc : ℕ} (hcb : cb < g.NR * g.NT) (hcc : cc < g.NR * g.NT) :
    nsOf rd cb cc = 4 * b2n (nC g D cc) + 2 * b2n (sC g D cb cc) := by
  unfold nsOf; rw [hrd.nb cc hcc, hrd.sb cb hcb cc hcc]

/-- The exact accumulator of `(cc, cb)`: class `T` of the third input. -/
noncomputable def accX (g : GridR) (D : DiscData3) (t : ℝ) (n cc cb q : ℕ) (T : Bool) : ℝ :=
  ∑ ca ∈ Finset.range (g.NR * g.NT), if tC g D ca cb cc = T then k3C g D t ca cb cc * Fx g D t n cb ca q else 0

lemma sum_if_const {ι : Type*} (s : Finset ι) (p : Prop) [Decidable p] (f : ι → ℝ) :
    ∑ i ∈ s, (if p then f i else 0) = if p then ∑ i ∈ s, f i else 0 := by
  split_ifs <;> simp

/-- `Fx (n+1)` regrouped by the state and the class of the third input. -/
lemma Fx_succ_regroup (n cc cb s : ℕ) :
    Fx g D t (n + 1) cc cb s = wC g D cc * ∑ q ∈ Finset.range NS,
      ((if trs[q * 8 + inp (nC g D cc) (sC g D cb cc) false]! = s then accX g D t n cc cb q false else 0) +
       (if trs[q * 8 + inp (nC g D cc) (sC g D cb cc) true]! = s then accX g D t n cc cb q true else 0)) := by
  simp only [Fx]
  congr 1
  unfold accX
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  have hpt : ∀ ca, k3C g D t ca cb cc *
      (if trs[q * 8 + inp (nC g D cc) (sC g D cb cc) (tC g D ca cb cc)]! = s then Fx g D t n cb ca q else 0) =
      (if trs[q * 8 + inp (nC g D cc) (sC g D cb cc) false]! = s then
        (if tC g D ca cb cc = false then k3C g D t ca cb cc * Fx g D t n cb ca q else 0) else 0) +
      (if trs[q * 8 + inp (nC g D cc) (sC g D cb cc) true]! = s then
        (if tC g D ca cb cc = true then k3C g D t ca cb cc * Fx g D t n cb ca q else 0) else 0) := by
    intro ca
    cases h : tC g D ca cb cc
    · rw [if_pos rfl, if_neg Bool.false_ne_true, ite_self, add_zero]
      by_cases h2 : trs[q * 8 + inp (nC g D cc) (sC g D cb cc) false]! = s
      · rw [if_pos h2, if_pos h2]
      · rw [if_neg h2, if_neg h2, mul_zero]
    · rw [if_neg (by decide : ¬ (true = false)), if_pos rfl, ite_self, zero_add]
      by_cases h2 : trs[q * 8 + inp (nC g D cc) (sC g D cb cc) true]! = s
      · rw [if_pos h2, if_pos h2]
      · rw [if_neg h2, if_neg h2, mul_zero]
  rw [Finset.sum_congr rfl (fun ca _ => hpt ca), Finset.sum_add_distrib, sum_if_const, sum_if_const]

/-- `Clo` regrouped by the state and the class of the third input. -/
lemma Clo_regroup (n cc : ℕ) :
    Clo g D t n cc = wC g D cc * ∑ cb ∈ Finset.range (g.NR * g.NT), ∑ q ∈ Finset.range NS,
      ((cls[q * 8 + inp (nC g D cc) (sC g D cb cc) false]! : ℝ) * accX g D t n cc cb q false +
       (cls[q * 8 + inp (nC g D cc) (sC g D cb cc) true]! : ℝ) * accX g D t n cc cb q true) := by
  unfold Clo
  congr 1
  apply Finset.sum_congr rfl
  intro cb _
  unfold accX
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ca _
  cases h : tC g D ca cb cc
  · rw [if_pos rfl, if_neg Bool.false_ne_true, mul_zero, add_zero]; ring
  · rw [if_neg (by decide : ¬ (true = false)), if_pos rfl, mul_zero, zero_add]; ring

lemma zp2'' (a b : ℤ) : (2 : ℝ) ^ (a + b) = 2 ^ a * 2 ^ b := zpow_add₀ two_ne_zero a b

/-- One product of the MAC loop. -/
lemma mac_term_bd (m k : ℕ) (E : ℤ) (K : ℝ) (hK : Bd lower ((k : ℝ) / 2 ^ 62) K) (hK0 : 0 ≤ K) :
    Bd lower ((mulTop lower (m >>> 31) (m &&& m31) (k >>> 31) (k &&& m31) : ℝ) * (2 : ℝ) ^ (-(E - 14)))
      ((m : ℝ) * (2 : ℝ) ^ (-E) * K) := by
  have e : (2 : ℝ) ^ (-(E - 14)) = (2 : ℝ) ^ (-E) * 2 ^ 14 := by
    rw [show -(E - 14) = -E + 14 by ring, zp2'']; norm_num
  have h1 := Bd.mul_right (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (-(E - 14))) (mulTop_bd lower m k)
  refine Bd.trans h1 ?_
  have e2 : (m : ℝ) * k / 2 ^ 76 * (2 : ℝ) ^ (-(E - 14)) = ((m : ℝ) * (2 : ℝ) ^ (-E)) * ((k : ℝ) / 2 ^ 62) := by
    rw [e]; field_simp
  rw [e2]
  exact Bd.mul_left (by positivity) hK

/-- The MAC accumulator bounds the exact accumulator. -/
theorem accS_bd (hrd : RdOK lower rd g D t) {rows : Array Row} {E : ℤ} {n : ℕ} (hrows : RowsBd lower g D t rows E n)
    (hmant : MantBd rows (g.NR * g.NT))
    {cc cb : ℕ} (hcc : cc < g.NR * g.NT) (hcb : cb < g.NR * g.NT) {q : ℕ} (hq : q < NS) (T : Bool) :
    Bd lower (((accS lower rd rows cc cb)[q + NS * b2n T]! : ℝ) * (2 : ℝ) ^ (-(E - 14))) (accX g D t n cc cb q T) := by
  obtain ⟨hwf, hinv, hbd⟩ := hrows cb hcb
  rw [accS_get lower rd rows cc cb hwf.st hinv (hmant cb hcb) hq (b2n_lt T)]
  set r := rows[cb]!
  -- the exact side as a sum over the segments
  have hX : accX g D t n cc cb q T = ∑ ca ∈ Finset.range (g.NR * g.NT),
      (if b2n (tC g D ca cb cc) = b2n T then k3C g D t ca cb cc * Fx g D t n cb ca q else 0) := by
    unfold accX
    apply Finset.sum_congr rfl
    intro ca _
    have : (tC g D ca cb cc = T) ↔ (b2n (tC g D ca cb cc) = b2n T) := by
      cases tC g D ca cb cc <;> cases T <;> decide
    by_cases h : tC g D ca cb cc = T
    · rw [if_pos h, if_pos (this.mp h)]
    · rw [if_neg h, if_neg (fun h' => h (this.mpr h'))]
  have hmid : ∑ ca ∈ Finset.range (g.NR * g.NT),
      (if b2n (tC g D ca cb cc) = b2n T then k3C g D t ca cb cc * ((rowVal r ca q : ℝ) * (2 : ℝ) ^ (-E)) else 0) =
      ∑ s ∈ Finset.range r.segCa.size, if rd.K3[t3Of rd r.segCa[s]! cb cc]! % 2 = b2n T then
        ∑ q' ∈ Finset.Ico r.segStart[s]! r.segStart[s + 1]!,
          (if r.st[q']! = q then (r.m[q']! : ℝ) * (2 : ℝ) ^ (-E) * k3C g D t r.segCa[s]! cb cc else 0)
      else 0 := by
    have hpt : ∀ ca, (if b2n (tC g D ca cb cc) = b2n T then k3C g D t ca cb cc * ((rowVal r ca q : ℝ) * (2 : ℝ) ^ (-E))
        else 0) = ((if b2n (tC g D ca cb cc) = b2n T then k3C g D t ca cb cc else 0) * (2 : ℝ) ^ (-E)) *
          (rowVal r ca q : ℝ) := by
      intro ca; split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun ca _ => hpt ca), sum_rowVal r _ hwf.ca q]
    apply Finset.sum_congr rfl
    intro s hs
    rw [Finset.mem_range] at hs
    rw [hrd.kT _ (hwf.ca s hs) cb hcb cc hcc]
    split_ifs with hTT
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q' _
      split_ifs <;> ring
    · simp
  -- computed vs the middle
  have h1 : Bd lower (((∑ s ∈ Finset.range r.segCa.size, if rd.K3[t3Of rd r.segCa[s]! cb cc]! % 2 = b2n T then
        ∑ q' ∈ Finset.Ico r.segStart[s]! r.segStart[s + 1]!,
          (if r.st[q']! = q then mulTop lower (r.m[q']! >>> 31) (r.m[q']! &&& m31)
              ((rd.K3[t3Of rd r.segCa[s]! cb cc]! >>> 1) >>> 31)
              ((rd.K3[t3Of rd r.segCa[s]! cb cc]! >>> 1) &&& m31) else 0)
      else 0 : ℕ) : ℝ) * (2 : ℝ) ^ (-(E - 14)))
      (∑ s ∈ Finset.range r.segCa.size, if rd.K3[t3Of rd r.segCa[s]! cb cc]! % 2 = b2n T then
        ∑ q' ∈ Finset.Ico r.segStart[s]! r.segStart[s + 1]!,
          (if r.st[q']! = q then (r.m[q']! : ℝ) * (2 : ℝ) ^ (-E) * k3C g D t r.segCa[s]! cb cc else 0)
      else 0) := by
    push_cast
    rw [Finset.sum_mul]
    apply Bd.sum
    intro s hs
    rw [Finset.mem_range] at hs
    have hca := hwf.ca s hs
    split_ifs
    · rw [Finset.sum_mul]
      apply Bd.sum
      intro q' _
      split_ifs
      · exact mac_term_bd _ _ E _ (hrd.kK _ hca cb hcb cc hcc) (Real.exp_pos _).le
      · simp only [Nat.cast_zero, zero_mul]; exact Bd.refl _ _
    · simp only [zero_mul]; exact Bd.refl _ _
  refine Bd.trans h1 ?_
  rw [← hmid, hX]
  apply Bd.sum
  intro ca hca
  rw [Finset.mem_range] at hca
  split_ifs
  · exact Bd.mul_left (Real.exp_pos _).le (hbd ca hca q hq)
  · exact Bd.refl _ _

end Step

end BHH.W3.Rec
