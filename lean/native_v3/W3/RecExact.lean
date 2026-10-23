/-
Window-3 recursion: the exact window-3 recursion over flat cell indices `c = ir * NT + it` (the indexing of
`W3C.runT3`), with the automaton tables `W3C.trs` / `W3C.cls`:
  `Fx 0 cb ca s = w(cb) w(ca) e^{-t ub(ca)} e^{-t ab(ca, cb)} [s = δ(δ(init; N(ca), 0, 0); N(cb), S(ca, cb), 0)]`,
  `Fx (n+1) cc cb s = w(cc) Σ_{ca, q} e^{-t a3(ca, cb, cc)} [s = δ(q; N(cc), S(cb, cc), T(ca, cb, cc))] Fx n cb ca q`,
the closing sums `Clo n cc` (closing values instead of the transitions) and `Phi3x` (two increments).  These are the
path sums of `W3/RecUnroll.lean`, so `Psid3 (n + 3) = (1/2) Σ_cc Clo n cc` and `Psid3 2 = Phi3x`.
-/
import W3.RecUnroll


open Real

namespace BHH.W3.Rec

open W3C BHH BHH.W2

section Flat

variable (g : GridR) (D : DiscData3) (t : ℝ)

/-- the angular offset between two flat cells -/
def dOf (c c' : ℕ) : ℤ := ((c' % g.NT : ℕ) : ℤ) - ((c % g.NT : ℕ) : ℤ)

/-- the weight of a flat cell -/
def wC (c : ℕ) : ℝ := D.w (c / g.NT)

/-- the first-step kernel of a flat cell -/
noncomputable def uC (c : ℕ) : ℝ := Real.exp (-(t * D.ub (c / g.NT)))

/-- the input `N` of a flat cell -/
def nC (c : ℕ) : Bool := D.nf (c / g.NT)

/-- the pair kernel of two flat cells -/
noncomputable def k2C (ca cb : ℕ) : ℝ := Real.exp (-(t * D.ab (ca / g.NT) (cb / g.NT) (dOf g ca cb)))

/-- the input `S` of two flat cells -/
def sC (ca cb : ℕ) : Bool := D.sc (ca / g.NT) (cb / g.NT) (dOf g ca cb)

/-- the triple kernel of three flat cells -/
noncomputable def k3C (ca cb cc : ℕ) : ℝ :=
  Real.exp (-(t * D.a3 (ca / g.NT) (cb / g.NT) (cc / g.NT) (dOf g ca cb) (dOf g cb cc)))

/-- the input `T` of three flat cells -/
def tC (ca cb cc : ℕ) : Bool := D.tc (ca / g.NT) (cb / g.NT) (cc / g.NT) (dOf g ca cb) (dOf g cb cc)

/-- the state index after the first point, for the first cell `ca` -/
def d1C (ca : ℕ) : ℕ := trs[4 * W2C.b2n (nC g D ca)]!

/-- The exact recursion: `Fx n cb ca s` after `n + 2` increments with the last two cells `ca, cb`. -/
noncomputable def Fx : ℕ → ℕ → ℕ → ℕ → ℝ
  | 0, cb, ca, s =>
    if d1C g D ca < NS ∧ trs[d1C g D ca * 8 + inp (nC g D cb) (sC g D ca cb) false]! = s then
      wC g D cb * (wC g D ca * uC g D t ca * k2C g D t ca cb) else 0
  | n + 1, cc, cb, s =>
    wC g D cc * ∑ ca ∈ Finset.range (g.NR * g.NT), k3C g D t ca cb cc *
      ∑ q ∈ Finset.range NS,
        if trs[q * 8 + inp (nC g D cc) (sC g D cb cc) (tC g D ca cb cc)]! = s then Fx n cb ca q else 0

/-- The exact closing sum of the target `cc` after `n + 2` increments (twice the value). -/
noncomputable def Clo (n cc : ℕ) : ℝ :=
  wC g D cc * ∑ cb ∈ Finset.range (g.NR * g.NT), ∑ ca ∈ Finset.range (g.NR * g.NT), k3C g D t ca cb cc *
    ∑ q ∈ Finset.range NS,
      (cls[q * 8 + inp (nC g D cc) (sC g D cb cc) (tC g D ca cb cc)]! : ℝ) * Fx g D t n cb ca q

/-- The exact closing sum with two increments (`Φ_3`). -/
noncomputable def Phi3x : ℝ :=
  (1 / 2) * ∑ cb ∈ Finset.range (g.NR * g.NT), ∑ ca ∈ Finset.range (g.NR * g.NT),
    if d1C g D ca < NS then
      (cls[d1C g D ca * 8 + inp (nC g D cb) (sC g D ca cb) false]! : ℝ) *
        (wC g D cb * (wC g D ca * uC g D t ca * k2C g D t ca cb))
    else 0

lemma Fx_nonneg (hw : ∀ ir, 0 ≤ D.w ir) : ∀ n cb ca s, 0 ≤ Fx g D t n cb ca s
  | 0, cb, ca, s => by
    simp only [Fx]
    split_ifs
    · exact mul_nonneg (hw _) (mul_nonneg (mul_nonneg (hw _) (Real.exp_pos _).le) (Real.exp_pos _).le)
    · exact le_rfl
  | n + 1, cc, cb, s => by
    simp only [Fx]
    apply mul_nonneg (hw _)
    apply Finset.sum_nonneg; intro ca _
    apply mul_nonneg (Real.exp_pos _).le
    apply Finset.sum_nonneg; intro q _
    split_ifs
    · exact Fx_nonneg hw n cb ca q
    · exact le_rfl

lemma Clo_nonneg (hw : ∀ ir, 0 ≤ D.w ir) (n cc : ℕ) : 0 ≤ Clo g D t n cc := by
  unfold Clo
  apply mul_nonneg (hw _)
  apply Finset.sum_nonneg; intro cb _
  apply Finset.sum_nonneg; intro ca _
  apply mul_nonneg (Real.exp_pos _).le
  apply Finset.sum_nonneg; intro q _
  exact mul_nonneg (Nat.cast_nonneg _) (Fx_nonneg g D t hw n cb ca q)

end Flat

/-! ## Flat cells and cells -/

/-- The flat index of a cell. -/
def flat {g : GridR} (x : Cell g) : ℕ := x.1.val * g.NT + x.2.val

lemma flat_div' {g : GridR} (x : Cell g) : flat x / g.NT = x.1.val := flat_div _ _ x.2.isLt
lemma flat_mod' {g : GridR} (x : Cell g) : flat x % g.NT = x.2.val := flat_mod _ _ x.2.isLt

lemma dOf_flat {g : GridR} (x y : Cell g) : dOf g (flat x) (flat y) = doff x y := by
  unfold dOf doff; rw [flat_mod', flat_mod']

lemma sum_range_flat (g : GridR) (f : ℕ → ℝ) :
    ∑ c ∈ Finset.range (g.NR * g.NT), f c = ∑ x : Cell g, f (flat x) := sum_range_cells g f

section Match

variable {g : GridR} (hNR : 0 < g.NR) (hNT : 0 < g.NT) (D : DiscData3) (t : ℝ)

lemma wC_flat (x : Cell g) : wC g D (flat x) = D.w x.1.val := by unfold wC; rw [flat_div']
lemma uC_flat (x : Cell g) : uC g D t (flat x) = Real.exp (-(t * D.ub x.1.val)) := by unfold uC; rw [flat_div']
lemma nC_flat (x : Cell g) : nC g D (flat x) = D.nf x.1.val := by unfold nC; rw [flat_div']
lemma k2C_flat (x y : Cell g) :
    k2C g D t (flat x) (flat y) = Real.exp (-(t * D.ab x.1.val y.1.val (doff x y))) := by
  unfold k2C; rw [flat_div', flat_div', dOf_flat]
lemma sC_flat (x y : Cell g) : sC g D (flat x) (flat y) = D.sc x.1.val y.1.val (doff x y) := by
  unfold sC; rw [flat_div', flat_div', dOf_flat]
lemma k3C_flat (x y z : Cell g) :
    k3C g D t (flat x) (flat y) (flat z) =
      Real.exp (-(t * D.a3 x.1.val y.1.val z.1.val (doff x y) (doff y z))) := by
  unfold k3C; rw [flat_div', flat_div', flat_div', dOf_flat, dOf_flat]
lemma tC_flat (x y z : Cell g) :
    tC g D (flat x) (flat y) (flat z) = D.tc x.1.val y.1.val z.1.val (doff x y) (doff y z) := by
  unfold tC; rw [flat_div', flat_div', flat_div', dOf_flat, dOf_flat]

lemma inp_ff (a : Bool) : inp a false false = 4 * W2C.b2n a := by cases a <;> rfl

/-- The state after the first point through the table. -/
lemma d1C_eq (ca : ℕ) : d1C g D ca = sIdx3 (St.init.step [nC g D ca, false, false]) := by
  unfold d1C
  have h := trs_good good_init3 (nC g D ca) false false
  rw [stIdx_init, zero_mul, zero_add, inp_ff] at h
  exact h

theorem Fx_eq_Phi3 : ∀ (n : ℕ) (xb xa : Cell g) (s : ℕ), s < NS →
    Fx g D t n (flat xb) (flat xa) s = Phi3 hNR hNT D t n xb xa s := by
  intro n
  induction n with
  | zero =>
    intro xb xa s hs
    rw [Phi3_zero]
    simp only [Fx]
    rw [d1C_eq, nC_flat, nC_flat, sC_flat, wC_flat, wC_flat, uC_flat, k2C_flat]
    have hv : D.w xb.1.val * (D.w xa.1.val * Real.exp (-(t * D.ub xa.1.val)) *
        Real.exp (-(t * D.ab xa.1.val xb.1.val (doff xa xb)))) =
        D.w xa.1.val * D.w xb.1.val * Real.exp (-(t * (D.ub xa.1.val + D.ab xa.1.val xb.1.val (doff xa xb)))) := by
      rw [mul_add, neg_add, Real.exp_add]; ring
    rw [hv]
    cases h1 : St.init.step [D.nf xa.1.val, false, false] with
    | none =>
      rw [Option.bind_none, sIdx3_none, if_neg (fun h => lt_irrefl NS h.1), if_neg (by omega)]
    | some s1 =>
      have hg : Good3 s1 := good_step3' good_init3 _ ⟨_, _, _, rfl⟩ h1
      rw [Option.bind_some]
      have e1 : sIdx3 (some s1) = stIdx s1 := rfl
      rw [e1, trs_good hg]
      by_cases hc : sIdx3 (s1.step [D.nf xb.1.val, D.sc xa.1.val xb.1.val (doff xa xb), false]) = s
      · rw [if_pos ⟨hg.1, hc⟩, if_pos hc]
      · rw [if_neg (fun h => hc h.2), if_neg hc]
  | succ n ih =>
    intro xc xb s hs
    rw [Phi3_succ hNR hNT D t n xc xb hs]
    simp only [Fx]
    rw [sum_range_flat, wC_flat, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro xa _
    rw [k3C_flat, nC_flat, sC_flat, tC_flat, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.mem_range] at hq
    rw [ih xb xa q hq]
    split_ifs <;> ring

theorem Psid3_eq_Clo (n : ℕ) :
    Psid3 g hNR hNT D (n + 3) t = (1 / 2) * ∑ cc ∈ Finset.range (g.NR * g.NT), Clo g D t n cc := by
  rw [Psid3_succ3]
  congr 1
  rw [sum_range_flat]
  apply Finset.sum_congr rfl
  intro xc _
  unfold Clo
  rw [sum_range_flat, wC_flat, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro xb _
  rw [sum_range_flat, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro xa _
  rw [k3C_flat, nC_flat, sC_flat, tC_flat, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Finset.mem_range] at hq
  rw [Fx_eq_Phi3 hNR hNT D t n xb xa q hq]
  ring

theorem Psid3_two_eq : Psid3 g hNR hNT D 2 t = Phi3x g D t := by
  rw [Psid3_two]
  unfold Phi3x
  congr 1
  rw [sum_range_flat]
  apply Finset.sum_congr rfl
  intro xb _
  rw [sum_range_flat]
  apply Finset.sum_congr rfl
  intro xa _
  rw [d1C_eq, nC_flat, nC_flat, sC_flat, wC_flat, wC_flat, uC_flat, k2C_flat]
  have hv : D.w xb.1.val * (D.w xa.1.val * Real.exp (-(t * D.ub xa.1.val)) *
      Real.exp (-(t * D.ab xa.1.val xb.1.val (doff xa xb)))) =
      D.w xa.1.val * D.w xb.1.val * Real.exp (-(t * (D.ub xa.1.val + D.ab xa.1.val xb.1.val (doff xa xb)))) := by
    rw [mul_add, neg_add, Real.exp_add]; ring
  rw [hv]
  cases h1 : St.init.step [D.nf xa.1.val, false, false] with
  | none =>
    rw [sIdx3_none, if_neg (lt_irrefl NS)]
    simp only [closeVal3, Nat.cast_zero, zero_mul]
  | some s1 =>
    have hg : Good3 s1 := good_step3' good_init3 _ ⟨_, _, _, rfl⟩ h1
    have e1 : sIdx3 (some s1) = stIdx s1 := rfl
    rw [e1, if_pos hg.1, cls_good hg]
    rfl

end Match

end BHH.W3.Rec
