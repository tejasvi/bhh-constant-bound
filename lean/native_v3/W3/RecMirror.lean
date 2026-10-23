/-
Window-3 recursion: mirror symmetry of the exact recursion.  The mirror image of a flat cell is
`W3C.mirC NT c = ir * NT + (NT - 1 - it)` (all angles negated).  For mirror symmetric tables (`MirOK`: `ab`, `sc`
even in the offset, `a3`, `tc` even in the pair of offsets) the exact recursion is mirror symmetric,
`Fx n (R cb) (R ca) s = Fx n cb ca s`, and so are the closing sums; hence the sum of the closing sums over all
targets is twice the sum over the computed half (`W3C.halfCell`, slots `≥ NT/2`, `NT` even).
-/
import W3.RecExact

open Real

namespace BHH.W3.Rec

open W3C BHH BHH.W2

/-! ## The mirror map on flat cells -/

section MirMap

variable {NR NT : ℕ}

lemma mirC_div (hNT : 0 < NT) (c : ℕ) : mirC NT c / NT = c / NT := by
  unfold mirC
  have h : c % NT < NT := Nat.mod_lt _ hNT
  rw [flat_div _ _ (by omega : NT - 1 - c % NT < NT)]

lemma mirC_mod (hNT : 0 < NT) (c : ℕ) : mirC NT c % NT = NT - 1 - c % NT := by
  unfold mirC
  have h : c % NT < NT := Nat.mod_lt _ hNT
  rw [flat_mod _ _ (by omega : NT - 1 - c % NT < NT)]

lemma mirC_lt (hNT : 0 < NT) {c : ℕ} (hc : c < NR * NT) : mirC NT c < NR * NT := by
  unfold mirC
  have h : c % NT < NT := Nat.mod_lt _ hNT
  have h2 : c / NT < NR := Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact hc)
  have : c / NT * NT + (NT - 1 - c % NT) < (c / NT + 1) * NT := by rw [add_mul, one_mul]; omega
  exact lt_of_lt_of_le this (Nat.mul_le_mul_right _ h2)

lemma mirC_mirC (hNT : 0 < NT) (c : ℕ) : mirC NT (mirC NT c) = c := by
  have h1 := mirC_div hNT c
  have h2 := mirC_mod hNT c
  have h : c % NT < NT := Nat.mod_lt _ hNT
  have e : mirC NT (mirC NT c) = mirC NT c / NT * NT + (NT - 1 - mirC NT c % NT) := rfl
  rw [e, h1, h2]
  conv_rhs => rw [← Nat.div_add_mod' c NT]
  congr 1
  omega

lemma mirC_inj (hNT : 0 < NT) {a b : ℕ} (h : mirC NT a = mirC NT b) : a = b := by
  rw [← mirC_mirC hNT a, h, mirC_mirC hNT b]

/-- Reindexing a sum over the flat cells by the mirror map. -/
lemma sum_mirC (hNT : 0 < NT) (f : ℕ → ℝ) :
    ∑ c ∈ Finset.range (NR * NT), f (mirC NT c) = ∑ c ∈ Finset.range (NR * NT), f c := by
  apply Finset.sum_nbij' (mirC NT) (mirC NT)
  · intro a ha; rw [Finset.mem_range] at ha ⊢; exact mirC_lt hNT ha
  · intro a ha; rw [Finset.mem_range] at ha ⊢; exact mirC_lt hNT ha
  · intro a _; exact mirC_mirC hNT a
  · intro a _; exact mirC_mirC hNT a
  · intro a _; rfl

end MirMap

/-! ## Mirror symmetric tables -/

/-- Mirror symmetry of the tables of `D` (offsets of absolute value `< NT`). -/
structure MirOK (g : GridR) (D : DiscData3) : Prop where
  ab : ∀ (ir ir2 : ℕ) (d : ℤ), ir < g.NR → ir2 < g.NR → |d| < g.NT → D.ab ir ir2 (-d) = D.ab ir ir2 d
  sc : ∀ (ir ir2 : ℕ) (d : ℤ), ir < g.NR → ir2 < g.NR → |d| < g.NT → D.sc ir ir2 (-d) = D.sc ir ir2 d
  a3 : ∀ (ia ib ic : ℕ) (dab dbc : ℤ), ia < g.NR → ib < g.NR → ic < g.NR → |dab| < g.NT → |dbc| < g.NT →
    D.a3 ia ib ic (-dab) (-dbc) = D.a3 ia ib ic dab dbc
  tc : ∀ (ia ib ic : ℕ) (dab dbc : ℤ), ia < g.NR → ib < g.NR → ic < g.NR → |dab| < g.NT → |dbc| < g.NT →
    D.tc ia ib ic (-dab) (-dbc) = D.tc ia ib ic dab dbc

section Sym

variable {g : GridR} (hNT : 0 < g.NT) {D : DiscData3} (hm : MirOK g D) (t : ℝ)

lemma ring_lt {c : ℕ} (hc : c < g.NR * g.NT) : c / g.NT < g.NR :=
  Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact hc)

include hNT in
lemma dOf_mirC (a b : ℕ) : dOf g (mirC g.NT a) (mirC g.NT b) = -dOf g a b := by
  unfold dOf
  rw [mirC_mod hNT, mirC_mod hNT]
  have ha : a % g.NT < g.NT := Nat.mod_lt _ hNT
  have hb : b % g.NT < g.NT := Nat.mod_lt _ hNT
  omega

include hNT in
lemma abs_dOf_lt (a b : ℕ) : |dOf g a b| < g.NT := by
  unfold dOf
  have ha : a % g.NT < g.NT := Nat.mod_lt _ hNT
  have hb : b % g.NT < g.NT := Nat.mod_lt _ hNT
  rw [abs_lt]; constructor <;> omega

include hNT in
lemma wC_mirC (c : ℕ) : wC g D (mirC g.NT c) = wC g D c := by unfold wC; rw [mirC_div hNT]

include hNT in
lemma uC_mirC (c : ℕ) : uC g D t (mirC g.NT c) = uC g D t c := by unfold uC; rw [mirC_div hNT]

include hNT in
lemma nC_mirC (c : ℕ) : nC g D (mirC g.NT c) = nC g D c := by unfold nC; rw [mirC_div hNT]

include hNT in
lemma d1C_mirC (c : ℕ) : d1C g D (mirC g.NT c) = d1C g D c := by unfold d1C; rw [nC_mirC hNT]

include hNT hm in
lemma k2C_mirC {a b : ℕ} (ha : a < g.NR * g.NT) (hb : b < g.NR * g.NT) :
    k2C g D t (mirC g.NT a) (mirC g.NT b) = k2C g D t a b := by
  unfold k2C
  rw [mirC_div hNT, mirC_div hNT, dOf_mirC hNT, hm.ab _ _ _ (ring_lt ha) (ring_lt hb) (abs_dOf_lt hNT a b)]

include hNT hm in
lemma sC_mirC {a b : ℕ} (ha : a < g.NR * g.NT) (hb : b < g.NR * g.NT) :
    sC g D (mirC g.NT a) (mirC g.NT b) = sC g D a b := by
  unfold sC
  rw [mirC_div hNT, mirC_div hNT, dOf_mirC hNT, hm.sc _ _ _ (ring_lt ha) (ring_lt hb) (abs_dOf_lt hNT a b)]

include hNT hm in
lemma k3C_mirC {a b c : ℕ} (ha : a < g.NR * g.NT) (hb : b < g.NR * g.NT) (hc : c < g.NR * g.NT) :
    k3C g D t (mirC g.NT a) (mirC g.NT b) (mirC g.NT c) = k3C g D t a b c := by
  unfold k3C
  rw [mirC_div hNT, mirC_div hNT, mirC_div hNT, dOf_mirC hNT, dOf_mirC hNT,
    hm.a3 _ _ _ _ _ (ring_lt ha) (ring_lt hb) (ring_lt hc) (abs_dOf_lt hNT a b) (abs_dOf_lt hNT b c)]

include hNT hm in
lemma tC_mirC {a b c : ℕ} (ha : a < g.NR * g.NT) (hb : b < g.NR * g.NT) (hc : c < g.NR * g.NT) :
    tC g D (mirC g.NT a) (mirC g.NT b) (mirC g.NT c) = tC g D a b c := by
  unfold tC
  rw [mirC_div hNT, mirC_div hNT, mirC_div hNT, dOf_mirC hNT, dOf_mirC hNT,
    hm.tc _ _ _ _ _ (ring_lt ha) (ring_lt hb) (ring_lt hc) (abs_dOf_lt hNT a b) (abs_dOf_lt hNT b c)]

include hNT hm in
/-- The exact recursion is mirror symmetric. -/
theorem Fx_mirC : ∀ (n cb ca s : ℕ), cb < g.NR * g.NT → ca < g.NR * g.NT →
    Fx g D t n (mirC g.NT cb) (mirC g.NT ca) s = Fx g D t n cb ca s := by
  intro n
  induction n with
  | zero =>
    intro cb ca s hcb hca
    simp only [Fx]
    rw [d1C_mirC hNT, nC_mirC hNT, sC_mirC hNT hm hca hcb, wC_mirC hNT, wC_mirC hNT, uC_mirC hNT,
      k2C_mirC hNT hm t hca hcb]
  | succ n ih =>
    intro cc cb s hcc hcb
    simp only [Fx]
    rw [wC_mirC hNT, ← sum_mirC hNT]
    congr 1
    apply Finset.sum_congr rfl
    intro ca hca
    rw [Finset.mem_range] at hca
    rw [k3C_mirC hNT hm t hca hcb hcc, nC_mirC hNT, sC_mirC hNT hm hcb hcc, tC_mirC hNT hm hca hcb hcc]
    congr 1
    apply Finset.sum_congr rfl
    intro q _
    rw [ih cb ca q hcb hca]

include hNT hm in
/-- The closing sums are mirror symmetric. -/
theorem Clo_mirC (n : ℕ) {cc : ℕ} (hcc : cc < g.NR * g.NT) : Clo g D t n (mirC g.NT cc) = Clo g D t n cc := by
  unfold Clo
  rw [wC_mirC hNT, ← sum_mirC hNT]
  congr 1
  apply Finset.sum_congr rfl
  intro cb hcb
  rw [Finset.mem_range] at hcb
  rw [← sum_mirC hNT]
  apply Finset.sum_congr rfl
  intro ca hca
  rw [Finset.mem_range] at hca
  rw [k3C_mirC hNT hm t hca hcb hcc, nC_mirC hNT, sC_mirC hNT hm hcb hcc, tC_mirC hNT hm hca hcb hcc]
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  rw [Fx_mirC hNT hm t n cb ca q hcb hca]

end Sym

/-! ## Sums over the computed half -/

lemma sum_range_mul (A B : ℕ) (f : ℕ → ℝ) :
    ∑ c ∈ Finset.range (A * B), f c = ∑ a ∈ Finset.range A, ∑ b ∈ Finset.range B, f (a * B + b) := by
  induction A with
  | zero => simp
  | succ A ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

/-- For a mirror symmetric function on the flat cells (`NT` even), the sum over all cells is twice the sum over the
computed half. -/
theorem sum_half {NR NT : ℕ} (hNT : 0 < NT) (hev : NT % 2 = 0) (f : ℕ → ℝ)
    (hf : ∀ c < NR * NT, f (mirC NT c) = f c) :
    ∑ c ∈ Finset.range (NR * NT), f c = 2 * ∑ h ∈ Finset.range (NR * (NT / 2)), f (halfCell NT h) := by
  set H := NT / 2 with hH
  have hNT2 : NT = H + H := by omega
  rw [sum_range_mul, sum_range_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mem_range] at ha
  -- the halves of the ring `a`
  have hsplit : ∑ b ∈ Finset.range NT, f (a * NT + b) =
      ∑ b ∈ Finset.range H, f (a * NT + b) + ∑ b ∈ Finset.range H, f (a * NT + (H + b)) := by
    conv_lhs => rw [hNT2]
    rw [Finset.sum_range_add]
    congr 1
    · apply Finset.sum_congr rfl; intro b _; rw [← hNT2]
    · apply Finset.sum_congr rfl; intro b _; rw [← hNT2]
  have hlow : ∑ b ∈ Finset.range H, f (a * NT + b) = ∑ b ∈ Finset.range H, f (a * NT + (H + b)) := by
    rw [← Finset.sum_range_reflect (fun b => f (a * NT + (H + b))) H]
    apply Finset.sum_congr rfl
    intro b hb
    rw [Finset.mem_range] at hb
    have hc : a * NT + b < NR * NT := by
      have : a * NT + b < (a + 1) * NT := by rw [add_mul, one_mul]; omega
      exact lt_of_lt_of_le this (Nat.mul_le_mul_right _ ha)
    rw [← hf _ hc]
    unfold mirC
    rw [flat_div _ _ (by omega : b < NT), flat_mod _ _ (by omega : b < NT)]
    congr 2
    omega
  have hhalf : ∀ b ∈ Finset.range H, halfCell NT (a * H + b) = a * NT + (H + b) := by
    intro b hb
    rw [Finset.mem_range] at hb
    unfold halfCell
    rw [← hH, flat_div _ _ hb, flat_mod _ _ hb]
    ring
  rw [hsplit, hlow, two_mul]
  congr 1 <;> (apply Finset.sum_congr rfl; intro b hb; rw [hhalf b hb])

end BHH.W3.Rec
