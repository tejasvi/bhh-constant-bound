/-
Window-3 entry primitives: soundness of `W3C.triRange28` for three convex hulls of points lying in
scalar boxes (the abstract part of `TriRangeSound`).

If every point of `T_a` lies in a box of `pa` (scale `2^-28`, and likewise for `b`, `c`), then for `u, v, w` in the
convex hulls of `T_a, T_b, T_c`:
* upper end: `|u + v + w|` is at most its value at some vertex sum (the norm is convex, three times), which is at most
  `√(ax² + ay²) 2^-28` for the boxes of the vertices, at most `√mx 2^-28` (the loop maximum), at most `mxd`;
* lower end: for the direction `e = (ex, ey)` (any integers), `⟨e, u + v + w⟩ 2^28 ≥ lo = Σ_s min_box ⟨e, ·⟩_lo`
  (a linear function is minimal at a vertex), and `|u + v + w| ≥ ⟨e, u + v + w⟩ / |e| ≥ lo / (2^28 enHi)`, `enHi ≥ |e|`.
Helper lemmas are in the namespace `BHH.W3.Prim`.
-/
import W3.Interfaces

open Set Real BHH.Cert

noncomputable section

namespace BHH.W3

open BHH

namespace Prim

/-! ## The Euclidean norm on `ℝ × ℝ` (through `ℂ`, as W2's `Euc`) -/

/-- the point as a complex number -/
def toCx (u : Pt) : ℂ := Complex.equivRealProd.symm u

lemma toCx_add (u v : Pt) : toCx (u + v) = toCx u + toCx v := by
  unfold toCx; apply Complex.ext <;> simp

lemma toCx_smul (t : ℝ) (u : Pt) : toCx (t • u) = (t : ℂ) * toCx u := by
  unfold toCx; apply Complex.ext <;> simp

lemma enorm2_eq_normCx (u : Pt) : enorm2 u = ‖toCx u‖ := by
  unfold enorm2 toCx
  rw [Complex.norm_def, Complex.normSq_apply]
  simp only [Complex.equivRealProd_symm_apply, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.ofReal_im, Complex.I_im, Complex.add_im, Complex.mul_im]
  congr 1; ring

lemma enorm2_nonneg' (u : Pt) : 0 ≤ enorm2 u := Real.sqrt_nonneg _

lemma enorm2_add_le' (u v : Pt) : enorm2 (u + v) ≤ enorm2 u + enorm2 v := by
  rw [enorm2_eq_normCx, enorm2_eq_normCx, enorm2_eq_normCx, toCx_add]; exact norm_add_le _ _

lemma enorm2_smul' (t : ℝ) (u : Pt) : enorm2 (t • u) = |t| * enorm2 u := by
  rw [enorm2_eq_normCx, enorm2_eq_normCx, toCx_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs]

/-! ## Maximum and minimum principles on convex hulls -/

lemma convexOn_enorm2_add (c : Pt) : ConvexOn ℝ univ (fun u : Pt => enorm2 (u + c)) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have e : a • x + b • y + c = a • (x + c) + b • (y + c) := by
    rw [smul_add, smul_add, add_add_add_comm, ← add_smul, hab, one_smul]
  simp only [smul_eq_mul]
  rw [e]
  calc enorm2 (a • (x + c) + b • (y + c)) ≤ enorm2 (a • (x + c)) + enorm2 (b • (y + c)) := enorm2_add_le' _ _
    _ = a * enorm2 (x + c) + b * enorm2 (y + c) := by
        rw [enorm2_smul', enorm2_smul', abs_of_nonneg ha, abs_of_nonneg hb]

/-- the norm of `u + c` on a convex hull is at most its value at a point of the generating set -/
lemma hull_enorm2_le {T : Set Pt} {u : Pt} (hu : u ∈ convexHull ℝ T) (c : Pt) :
    ∃ V ∈ T, enorm2 (u + c) ≤ enorm2 (V + c) :=
  (convexOn_enorm2_add c).exists_ge_of_mem_convexHull (subset_univ T) hu

lemma concaveOn_dot (e1 e2 : ℝ) : ConcaveOn ℝ univ (fun u : Pt => e1 * u.1 + e2 * u.2) := by
  refine ⟨convex_univ, fun x _ y _ a b _ _ _ => le_of_eq ?_⟩
  simp only [smul_eq_mul, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd]
  ring

/-- a linear function on a convex hull is at least its value at a point of the generating set -/
lemma hull_dot_ge {T : Set Pt} {u : Pt} (hu : u ∈ convexHull ℝ T) (e1 e2 : ℝ) :
    ∃ V ∈ T, e1 * V.1 + e2 * V.2 ≤ e1 * u.1 + e2 * u.2 :=
  (concaveOn_dot e1 e2).exists_le_of_mem_convexHull (subset_univ T) hu

/-! ## Scalar boxes -/

/-- a scalar box `(xlo, xhi, ylo, yhi)` at scale `2^-28` -/
abbrev Box4 := ℤ × ℤ × ℤ × ℤ

/-- the box `p` contains the point `V` -/
def inBox28 (p : Box4) (V : Pt) : Prop :=
  (p.1 : ℝ) ≤ V.1 * 2 ^ 28 ∧ V.1 * 2 ^ 28 ≤ p.2.1 ∧ (p.2.2.1 : ℝ) ≤ V.2 * 2 ^ 28 ∧ V.2 * 2 ^ 28 ≤ p.2.2.2

/-! ## `triRange28` restated (definitionally) -/

/-- the vertex-sum value `ax² + ay²` of a box triple (scale `2^-56`), as in `W3C.triRange28` -/
def vTri (p q r : Box4) : ℤ :=
  let sxl := p.1 + q.1 + r.1
  let sxh := p.2.1 + q.2.1 + r.2.1
  let syl := p.2.2.1 + q.2.2.1 + r.2.2.1
  let syh := p.2.2.2 + q.2.2.2 + r.2.2.2
  let ax := Max.max sxl.natAbs sxh.natAbs
  let ay := Max.max syl.natAbs syh.natAbs
  let v : Int := ax * ax + ay * ay
  v

/-- the innermost maximum loop -/
def innerMax (p q : Box4) (pc : Array Box4) (s : ℤ) : ℤ :=
  Id.run (forIn pc s fun r s =>
    if vTri p q r > s then pure (ForInStep.yield (vTri p q r)) else pure (ForInStep.yield s))

/-- the middle maximum loop -/
def midMax (p : Box4) (pb pc : Array Box4) (s : ℤ) : ℤ :=
  Id.run (forIn pb s fun q s => pure (ForInStep.yield (innerMax p q pc s)))

/-- the maximum loop of `W3C.triRange28` -/
def loopMax28 (pa pb pc : Array Box4) : ℤ :=
  Id.run (forIn pa (0 : ℤ) fun p s => pure (ForInStep.yield (midMax p pb pc s)))

def sumMid28 (ps : Array Box4) : ℤ × ℤ :=
  ps.foldl (fun (acc : Int × Int) p => (acc.1 + (p.1 + p.2.1) / 2, acc.2 + (p.2.2.1 + p.2.2.2) / 2)) (0, 0)

/-- lower bound of `⟨(ex, ey), ·⟩` (scale `2^-28`) on a box (scale `2^-28`) -/
def dotLo28 (ex ey : ℤ) (p : Box4) : ℤ :=
  (if 0 ≤ ex then ex * p.1 else ex * p.2.1) + (if 0 ≤ ey then ey * p.2.2.1 else ey * p.2.2.2)

def minDot28 (ex ey : ℤ) (ps : Array Box4) : ℤ :=
  ps.foldl (fun (m : Int) p => Min.min m (dotLo28 ex ey p)) (dotLo28 ex ey ps[0]!)

/-- the part of `W3C.triRange28` after the maximum loop -/
def triRest28 (pa pb pc : Array Box4) (mx : ℤ) : ℤ × ℤ := Id.run do
  let mxd := (Iv.sqrt ⟨mx * 2 ^ (PR - 2 * W3C.SC), mx * 2 ^ (PR - 2 * W3C.SC)⟩).hi
  let (ax, ay) := sumMid28 pa
  let (bx, by_) := sumMid28 pb
  let (cx, cy) := sumMid28 pc
  let ex := (ax + bx + cx) / 16
  let ey := (ay + by_ + cy) / 16
  let lo := minDot28 ex ey pa + minDot28 ex ey pb + minDot28 ex ey pc
  let en2 := ex * ex + ey * ey
  if lo ≤ 0 ∨ en2 == 0 then return (0, mxd)
  else
    let enHi : Int := (isqrtHi en2.toNat : Nat)
    return (Max.max ((lo * 2 ^ (PR - W3C.SC)) / enHi) 0, mxd)

theorem triRange28_eq (pa pb pc : Array Box4) :
    W3C.triRange28 pa pb pc = triRest28 pa pb pc (loopMax28 pa pb pc) := rfl

/-! ## The loops -/

lemma forIn_list_ge {α : Type*} (l : List α) (init : ℤ) (f : α → ℤ → Id (ForInStep ℤ))
    (hf : ∀ a b, ∃ b', f a b = pure (ForInStep.yield b') ∧ b ≤ b') :
    init ≤ Id.run (forIn l init f) ∧
      ∀ a ∈ l, ∀ K : ℤ, (∀ b b', f a b = pure (ForInStep.yield b') → K ≤ b') → K ≤ Id.run (forIn l init f) := by
  induction l generalizing init with
  | nil => exact ⟨le_refl _, fun a ha => absurd ha List.not_mem_nil⟩
  | cons a l ih =>
    obtain ⟨b', hb', hle⟩ := hf a init
    have e : Id.run (forIn (a :: l) init f) = Id.run (forIn l b' f) := by
      rw [List.forIn_cons, hb']; rfl
    rw [e]
    obtain ⟨ih1, ih2⟩ := ih b'
    refine ⟨le_trans hle ih1, ?_⟩
    intro x hx K hK
    rcases List.mem_cons.mp hx with rfl | hx
    · exact le_trans (hK init b' hb') ih1
    · exact ih2 x hx K hK

lemma forIn_array_ge {α : Type*} (xs : Array α) (init : ℤ) (f : α → ℤ → Id (ForInStep ℤ))
    (hf : ∀ a b, ∃ b', f a b = pure (ForInStep.yield b') ∧ b ≤ b') :
    init ≤ Id.run (forIn xs init f) ∧
      ∀ a ∈ xs, ∀ K : ℤ, (∀ b b', f a b = pure (ForInStep.yield b') → K ≤ b') → K ≤ Id.run (forIn xs init f) := by
  rw [← Array.forIn_toList]
  obtain ⟨h1, h2⟩ := forIn_list_ge xs.toList init f hf
  exact ⟨h1, fun a ha K hK => h2 a (Array.mem_toList_iff.mpr ha) K hK⟩

lemma innerMax_ge (p q : Box4) (pc : Array Box4) (s : ℤ) :
    s ≤ innerMax p q pc s ∧ ∀ r ∈ pc, vTri p q r ≤ innerMax p q pc s := by
  have hf : ∀ (r : Box4) (b : ℤ), ∃ b', (if vTri p q r > b then pure (ForInStep.yield (vTri p q r))
      else pure (ForInStep.yield b) : Id (ForInStep ℤ)) = pure (ForInStep.yield b') ∧ b ≤ b' := by
    intro r b
    by_cases h : vTri p q r > b
    · exact ⟨vTri p q r, by rw [ite_eq_left h], le_of_lt h⟩
    · exact ⟨b, by rw [ite_eq_right h], le_refl b⟩
  obtain ⟨h1, h2⟩ := forIn_array_ge pc s _ hf
  refine ⟨h1, fun r hr => h2 r hr (vTri p q r) ?_⟩
  intro b b' hb
  by_cases h : vTri p q r > b
  · rw [ite_eq_left h] at hb
    have e : ForInStep.yield (vTri p q r) = ForInStep.yield b' := hb
    injection e with e
    rw [e]
  · rw [ite_eq_right h] at hb
    have e : ForInStep.yield b = ForInStep.yield b' := hb
    injection e with e
    rw [← e]
    exact not_lt.mp h

lemma midMax_ge (p : Box4) (pb pc : Array Box4) (s : ℤ) :
    s ≤ midMax p pb pc s ∧ ∀ q ∈ pb, ∀ r ∈ pc, vTri p q r ≤ midMax p pb pc s := by
  have hf : ∀ (q : Box4) (b : ℤ), ∃ b', (pure (ForInStep.yield (innerMax p q pc b)) : Id (ForInStep ℤ)) =
      pure (ForInStep.yield b') ∧ b ≤ b' :=
    fun q b => ⟨innerMax p q pc b, rfl, (innerMax_ge p q pc b).1⟩
  obtain ⟨h1, h2⟩ := forIn_array_ge pb s _ hf
  refine ⟨h1, fun q hq r hr => h2 q hq (vTri p q r) ?_⟩
  intro b b' hb
  have e : ForInStep.yield (innerMax p q pc b) = ForInStep.yield b' := hb
  injection e with e
  rw [← e]
  exact (innerMax_ge p q pc b).2 r hr

lemma loopMax28_ge {pa pb pc : Array Box4} {p q r : Box4} (hp : p ∈ pa) (hq : q ∈ pb) (hr : r ∈ pc) :
    vTri p q r ≤ loopMax28 pa pb pc := by
  have hf : ∀ (p : Box4) (b : ℤ), ∃ b', (pure (ForInStep.yield (midMax p pb pc b)) : Id (ForInStep ℤ)) =
      pure (ForInStep.yield b') ∧ b ≤ b' :=
    fun p b => ⟨midMax p pb pc b, rfl, (midMax_ge p pb pc b).1⟩
  obtain ⟨_, h2⟩ := forIn_array_ge pa 0 _ hf
  refine h2 p hp (vTri p q r) ?_
  intro b b' hb
  have e : ForInStep.yield (midMax p pb pc b) = ForInStep.yield b' := hb
  injection e with e
  rw [← e]
  exact (midMax_ge p pb pc b).2 q hq r hr

lemma foldl_min_le {α : Type*} (f : α → ℤ) : ∀ (l : List α) (init : ℤ),
    List.foldl (fun m p => min m (f p)) init l ≤ init ∧ ∀ x ∈ l, List.foldl (fun m p => min m (f p)) init l ≤ f x
  | [], init => ⟨le_refl _, fun x hx => absurd hx List.not_mem_nil⟩
  | a :: l, init => by
    rw [List.foldl_cons]
    obtain ⟨h1, h2⟩ := foldl_min_le f l (min init (f a))
    refine ⟨le_trans h1 (min_le_left _ _), fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact le_trans h1 (min_le_right _ _)
    · exact h2 x hx

lemma minDot28_le (ex ey : ℤ) {ps : Array Box4} {p : Box4} (hp : p ∈ ps) : minDot28 ex ey ps ≤ dotLo28 ex ey p := by
  unfold minDot28
  rw [← Array.foldl_toList]
  exact (foldl_min_le (dotLo28 ex ey) ps.toList _).2 p (Array.mem_toList_iff.mpr hp)

/-! ## Single boxes -/

lemma abs_le_of_box {x : ℝ} {l h : ℤ} (h1 : (l : ℝ) ≤ x) (h2 : x ≤ h) :
    |x| ≤ ((max l.natAbs h.natAbs : ℕ) : ℝ) := by
  rw [Nat.cast_max, Nat.cast_natAbs, Nat.cast_natAbs, Int.cast_abs, Int.cast_abs]
  exact abs_le_max_abs_abs h1 h2

lemma vTri_cast (p q r : Box4) : (vTri p q r : ℝ) =
    ((max (p.1 + q.1 + r.1).natAbs (p.2.1 + q.2.1 + r.2.1).natAbs : ℕ) : ℝ) *
        ((max (p.1 + q.1 + r.1).natAbs (p.2.1 + q.2.1 + r.2.1).natAbs : ℕ) : ℝ) +
      ((max (p.2.2.1 + q.2.2.1 + r.2.2.1).natAbs (p.2.2.2 + q.2.2.2 + r.2.2.2).natAbs : ℕ) : ℝ) *
        ((max (p.2.2.1 + q.2.2.1 + r.2.2.1).natAbs (p.2.2.2 + q.2.2.2 + r.2.2.2).natAbs : ℕ) : ℝ) := by
  unfold vTri
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast]

/-- the vertex sum of three points in three boxes: `|V_a + V_b + V_c|² 2^56 ≤ ax² + ay²` -/
lemma vTri_bound {p q r : Box4} {Va Vb Vc : Pt} (hp : inBox28 p Va) (hq : inBox28 q Vb) (hr : inBox28 r Vc) :
    enorm2 (Va + Vb + Vc) ^ 2 * 2 ^ 56 ≤ (vTri p q r : ℝ) := by
  obtain ⟨p1, p2, p3, p4⟩ := hp
  obtain ⟨q1, q2, q3, q4⟩ := hq
  obtain ⟨r1, r2, r3, r4⟩ := hr
  have hx := abs_le_of_box (x := (Va.1 + Vb.1 + Vc.1) * 2 ^ 28) (l := p.1 + q.1 + r.1)
    (h := p.2.1 + q.2.1 + r.2.1) (by push_cast; linarith) (by push_cast; linarith)
  have hy := abs_le_of_box (x := (Va.2 + Vb.2 + Vc.2) * 2 ^ 28) (l := p.2.2.1 + q.2.2.1 + r.2.2.1)
    (h := p.2.2.2 + q.2.2.2 + r.2.2.2) (by push_cast; linarith) (by push_cast; linarith)
  rw [vTri_cast]
  unfold enorm2
  rw [Real.sq_sqrt (by positivity)]
  simp only [Prod.fst_add, Prod.snd_add]
  have hx2 := pow_le_pow_left₀ (abs_nonneg _) hx 2
  have hy2 := pow_le_pow_left₀ (abs_nonneg _) hy 2
  rw [sq_abs] at hx2 hy2
  nlinarith [hx2, hy2]

/-- the lower bound of a linear function on a box -/
lemma dotLo28_le (ex ey : ℤ) {p : Box4} {V : Pt} (hp : inBox28 p V) :
    (dotLo28 ex ey p : ℝ) ≤ ((ex : ℝ) * V.1 + (ey : ℝ) * V.2) * 2 ^ 28 := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  unfold dotLo28
  have hx : ((if 0 ≤ ex then ex * p.1 else ex * p.2.1 : ℤ) : ℝ) ≤ (ex : ℝ) * (V.1 * 2 ^ 28) := by
    split_ifs with h
    · have : (0 : ℝ) ≤ ex := by exact_mod_cast h
      push_cast; exact mul_le_mul_of_nonneg_left h1 this
    · have : (ex : ℝ) < 0 := by exact_mod_cast not_le.mp h
      push_cast; nlinarith
  have hy : ((if 0 ≤ ey then ey * p.2.2.1 else ey * p.2.2.2 : ℤ) : ℝ) ≤ (ey : ℝ) * (V.2 * 2 ^ 28) := by
    split_ifs with h
    · have : (0 : ℝ) ≤ ey := by exact_mod_cast h
      push_cast; exact mul_le_mul_of_nonneg_left h3 this
    · have : (ey : ℝ) < 0 := by exact_mod_cast not_le.mp h
      push_cast; nlinarith
  rw [Int.cast_add]
  linarith

/-! ## The theorem -/

lemma fx_max_tri (a b : ℤ) : fx (max a b) = max (fx a) (fx b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (fx_le_iff.mpr h)]
  · rw [max_eq_left h, max_eq_left (fx_le_iff.mpr h)]

/-- `triRange28` bounds `|u + v + w|` on three convex hulls whose generating points lie in the given boxes. -/
theorem triRange28_sound {pa pb pc : Array Box4} {Ta Tb Tc : Set Pt}
    (hA : ∀ V ∈ Ta, ∃ p ∈ pa, inBox28 p V) (hB : ∀ V ∈ Tb, ∃ p ∈ pb, inBox28 p V)
    (hC : ∀ V ∈ Tc, ∃ p ∈ pc, inBox28 p V) {u v w : Pt}
    (hu : u ∈ convexHull ℝ Ta) (hv : v ∈ convexHull ℝ Tb) (hw : w ∈ convexHull ℝ Tc) :
    fx (W3C.triRange28 pa pb pc).1 ≤ enorm2 (u + v + w) ∧ enorm2 (u + v + w) ≤ fx (W3C.triRange28 pa pb pc).2 := by
  rw [triRange28_eq]
  have hS0 := enorm2_nonneg' (u + v + w)
  -- the upper end: a vertex sum
  have hup : enorm2 (u + v + w) ^ 2 * 2 ^ 56 ≤ (loopMax28 pa pb pc : ℝ) := by
    obtain ⟨Va, hVa, h1⟩ := hull_enorm2_le hu (v + w)
    obtain ⟨Vb, hVb, h2⟩ := hull_enorm2_le hv (Va + w)
    obtain ⟨Vc, hVc, h3⟩ := hull_enorm2_le hw (Va + Vb)
    obtain ⟨p, hp, hpV⟩ := hA Va hVa
    obtain ⟨q, hq, hqV⟩ := hB Vb hVb
    obtain ⟨r, hr, hrV⟩ := hC Vc hVc
    have hv3 := vTri_bound hpV hqV hrV
    have hle : (vTri p q r : ℝ) ≤ loopMax28 pa pb pc := by exact_mod_cast loopMax28_ge hp hq hr
    have e1 : u + v + w = u + (v + w) := by abel
    have e2 : Va + (v + w) = v + (Va + w) := by abel
    have e3 : Vb + (Va + w) = w + (Va + Vb) := by abel
    have e4 : Vc + (Va + Vb) = Va + Vb + Vc := by abel
    have hchain : enorm2 (u + v + w) ≤ enorm2 (Va + Vb + Vc) := by
      rw [e1]
      calc enorm2 (u + (v + w)) ≤ enorm2 (Va + (v + w)) := h1
        _ = enorm2 (v + (Va + w)) := by rw [e2]
        _ ≤ enorm2 (Vb + (Va + w)) := h2
        _ = enorm2 (w + (Va + Vb)) := by rw [e3]
        _ ≤ enorm2 (Vc + (Va + Vb)) := h3
        _ = enorm2 (Va + Vb + Vc) := by rw [e4]
    have hsq : enorm2 (u + v + w) ^ 2 ≤ enorm2 (Va + Vb + Vc) ^ 2 := pow_le_pow_left₀ hS0 hchain 2
    nlinarith
  -- the lower end: a separating direction
  have hlow : ∀ ex ey : ℤ, ((minDot28 ex ey pa + minDot28 ex ey pb + minDot28 ex ey pc : ℤ) : ℝ) ≤
      ((ex : ℝ) * (u + v + w).1 + (ey : ℝ) * (u + v + w).2) * 2 ^ 28 := by
    intro ex ey
    have key : ∀ (ps : Array Box4) (T : Set Pt), (∀ V ∈ T, ∃ p ∈ ps, inBox28 p V) → ∀ z ∈ convexHull ℝ T,
        (minDot28 ex ey ps : ℝ) ≤ ((ex : ℝ) * z.1 + (ey : ℝ) * z.2) * 2 ^ 28 := by
      intro ps T hT z hz
      obtain ⟨V, hV, hle⟩ := hull_dot_ge hz ex ey
      obtain ⟨p, hp, hpV⟩ := hT V hV
      have h1 := dotLo28_le ex ey hpV
      have h2 : (minDot28 ex ey ps : ℝ) ≤ dotLo28 ex ey p := by exact_mod_cast minDot28_le ex ey hp
      have h3 := mul_le_mul_of_nonneg_right hle (by positivity : (0 : ℝ) ≤ 2 ^ 28)
      linarith
    have ha := key pa Ta hA u hu
    have hb := key pb Tb hB v hv
    have hc := key pc Tc hC w hw
    push_cast
    simp only [Prod.fst_add, Prod.snd_add]
    linarith
  generalize loopMax28 pa pb pc = M at hup
  -- the upper end in fixed point: `√(M 2^-56) ≤ mxd`
  have hmxd : enorm2 (u + v + w) ≤ fx (Iv.sqrt ⟨M * 2 ^ (PR - 2 * W3C.SC), M * 2 ^ (PR - 2 * W3C.SC)⟩).hi := by
    have hsq := ivMem_hi_le (Iv.mem_sqrt (Iv.mem_pt (M * 2 ^ (PR - 2 * W3C.SC))))
    have e : fx (M * 2 ^ (PR - 2 * W3C.SC)) = (M : ℝ) / 2 ^ 56 := by
      unfold fx PR W3C.SC; push_cast; field_simp; norm_num
    rw [e] at hsq
    refine le_trans ?_ hsq
    have hM0 : (0 : ℝ) ≤ (M : ℝ) / 2 ^ 56 := by
      have := sq_nonneg (enorm2 (u + v + w))
      apply div_nonneg _ (by positivity); nlinarith
    rw [Real.le_sqrt hS0 hM0, le_div_iff₀ (by positivity)]
    exact hup
  unfold triRest28
  rcases hsa : sumMid28 pa with ⟨ax, ay⟩
  rcases hsb : sumMid28 pb with ⟨bx, by_⟩
  rcases hsc : sumMid28 pc with ⟨cx, cy⟩
  simp only [Id.run, pure]
  split_ifs with hcase
  · refine ⟨?_, hmxd⟩
    rw [show fx 0 = 0 by simp [fx]]
    exact hS0
  · refine ⟨?_, hmxd⟩
    rw [not_or] at hcase
    obtain ⟨hlo, hen⟩ := hcase
    set ex := (ax + bx + cx) / 16 with hex
    set ey := (ay + by_ + cy) / 16 with hey
    set lo := minDot28 ex ey pa + minDot28 ex ey pb + minDot28 ex ey pc with hlodef
    have hlo' : 0 < lo := lt_of_not_ge hlo
    have hen' : ex * ex + ey * ey ≠ 0 := by simpa using hen
    have hen0 : 0 < ex * ex + ey * ey := lt_of_le_of_ne (by nlinarith) (Ne.symm hen')
    set n := (ex * ex + ey * ey).toNat with hn
    have hnr : (n : ℝ) = (ex : ℝ) ^ 2 + (ey : ℝ) ^ 2 := by
      have : ((n : ℕ) : ℤ) = ex * ex + ey * ey := Int.toNat_of_nonneg hen0.le
      have : ((n : ℕ) : ℝ) = ((ex * ex + ey * ey : ℤ) : ℝ) := by exact_mod_cast this
      rw [this]; push_cast; ring
    have hn0 : 0 < n := by omega
    -- `enHi ≥ |e| > 0`
    have hsqh := le_isqrtHi_sq n
    set R := isqrtHi n with hR
    have hR0 : 0 < R := by
      rcases Nat.eq_zero_or_pos R with h | h
      · rw [h] at hsqh; omega
      · exact h
    have hRr : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hR0
    have hRsq : √((ex : ℝ) ^ 2 + (ey : ℝ) ^ 2) ≤ (R : ℝ) := by
      rw [← hnr, Real.sqrt_le_left hRr.le]
      have : ((n : ℕ) : ℝ) ≤ ((R * R : ℕ) : ℝ) := by exact_mod_cast hsqh
      push_cast at this; nlinarith
    -- Cauchy-Schwarz
    have hcs : (ex : ℝ) * (u + v + w).1 + (ey : ℝ) * (u + v + w).2 ≤
        √((ex : ℝ) ^ 2 + (ey : ℝ) ^ 2) * enorm2 (u + v + w) := by
      unfold enorm2
      rw [← Real.sqrt_mul (by positivity)]
      refine le_trans (le_abs_self _) (Real.abs_le_sqrt ?_)
      nlinarith [sq_nonneg ((ex : ℝ) * (u + v + w).2 - (ey : ℝ) * (u + v + w).1)]
    have hl := hlow ex ey
    rw [← hlodef] at hl
    -- the fixed-point value
    have hdiv : ((lo * 2 ^ (PR - W3C.SC) / (R : ℤ) : ℤ) : ℝ) ≤ ((lo * 2 ^ (PR - W3C.SC) : ℤ) : ℝ) / (R : ℝ) := by
      have := divD_le (lo * 2 ^ (PR - W3C.SC)) (R : ℤ) (by exact_mod_cast hR0)
      exact_mod_cast this
    have hval : fx (lo * 2 ^ (PR - W3C.SC) / (R : ℤ)) ≤ enorm2 (u + v + w) := by
      unfold fx
      have e : ((lo * 2 ^ (PR - W3C.SC) : ℤ) : ℝ) / (R : ℝ) / 2 ^ PR = (lo : ℝ) / 2 ^ 28 / (R : ℝ) := by
        unfold PR W3C.SC; push_cast; field_simp; norm_num
      calc ((lo * 2 ^ (PR - W3C.SC) / (R : ℤ) : ℤ) : ℝ) / 2 ^ PR
          ≤ ((lo * 2 ^ (PR - W3C.SC) : ℤ) : ℝ) / (R : ℝ) / 2 ^ PR := by gcongr
        _ = (lo : ℝ) / 2 ^ 28 / (R : ℝ) := e
        _ ≤ enorm2 (u + v + w) := by
          rw [div_le_iff₀ hRr, div_le_iff₀ (by positivity)]
          have h1 : √((ex : ℝ) ^ 2 + (ey : ℝ) ^ 2) * enorm2 (u + v + w) ≤ (R : ℝ) * enorm2 (u + v + w) :=
            mul_le_mul_of_nonneg_right hRsq hS0
          nlinarith
    have hmax := fx_max_tri (lo * 2 ^ (PR - W3C.SC) / (R : ℤ)) 0
    rw [hmax, show fx 0 = 0 by simp [fx]]
    exact max_le hval hS0

end Prim

end BHH.W3
