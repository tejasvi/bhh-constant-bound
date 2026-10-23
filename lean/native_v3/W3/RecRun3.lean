/-
Window-3 recursion: the data of one run `W3C.runT3 (W3C.mkRun3 g dtl par) lower j dtl kmax par` describe
the tables of `discOf3 g dtl` at `t = j 2^-dtl` (`RdOK`, `L2OK`): weights, inputs, the triple kernels `e1^j` (from the
exponential tables), the first-step and pair kernels.
-/
import W3.RecTab3

open Real

namespace BHH.W3.Rec

open W3C W2C BHH BHH.W2 BHH.Cert

attribute [local irreducible] W3C.NS W3C.reachable W3C.trs W3C.cls

/-! ## The read-only data of a run -/

/-- The read-only data of `runT3` (as in its body). -/
def rd3Of (r : Run3) (lower : Bool) (j : ℕ) (par : Bool) : RecData3 :=
  ⟨r.g.NR, r.g.NT, r.g.ND, r.rings.map (·.areaLo.toNat), r.rings.map (fun R => if R.nflag then 4 else 0),
    r.pairs.map (fun p => if p.scls then 2 else 0), mkK3 r lower j par⟩

/-- The first-step kernels of `runT3`. -/
def f1Of (r : Run3) (lower : Bool) (j dtl : ℕ) : Array ℕ := r.rings.map fun R => kern lower j dtl (W3C.upq R.euHi dtl)

/-- The pair kernels of `runT3`. -/
def k2Of (r : Run3) (lower : Bool) (j dtl : ℕ) (par : Bool) : Array ℕ :=
  pgen par 64 r.ab2.size fun i => kern lower j dtl r.ab2[i]!

lemma runT3_eq (r : Run3) (lower : Bool) (j dtl kmax : ℕ) (par : Bool) :
    runT3 r lower j dtl kmax par =
      recIter3 lower (rd3Of r lower j par) par (kmax - 3)
        (normRows lower (level2 lower (rd3Of r lower j par) (f1Of r lower j dtl) (k2Of r lower j dtl par) par).1).1
        (((2 * PR + 62 : ℕ) : ℤ) -
          ((normRows lower (level2 lower (rd3Of r lower j par) (f1Of r lower j dtl) (k2Of r lower j dtl par) par).1).2 : ℤ))
        [((level2 lower (rd3Of r lower j par) (f1Of r lower j dtl) (k2Of r lower j dtl par) par).2,
          ((2 * PR + 62 + 1 : ℕ) : ℤ))] := by
  rw [W3C.runT3]; rfl

/-! ## The run `mkRun3` -/

section Mk

variable (g : W2C.Grid) (dtl : ℕ) (par : Bool)

lemma mkRun3_g : (mkRun3 g dtl par).g = g := rfl
lemma mkRun3_rings : (mkRun3 g dtl par).rings = (mkTabData g).rings := rfl
lemma mkRun3_pairs : (mkRun3 g dtl par).pairs = mkPairs (mkTabData g) false := by
  show mkPairs (mkTabData g) par = _; rw [mkPairs_par]
lemma mkRun3_ab2 : (mkRun3 g dtl par).ab2 = (mkPairs (mkTabData g) false).map (fun p => W3C.upq (max p.abar2 0) dtl) := by
  show (mkPairs (mkTabData g) par).map _ = _; rw [mkPairs_par]

/-- the triple table of the run -/
def triOf : Array ℕ := mkTri (mkTabData g) (mkPairs (mkTabData g) false) false

lemma mkRun3_e1lo : (mkRun3 g dtl par).e1lo =
    pgen par 256 (triOf g).size fun i => 2 * e1Of true dtl (mkExpTabs true dtl par) (triOf g)[i]! + (triOf g)[i]! % 2 := by
  show pgen par 256 (mkTri (mkTabData g) (mkPairs (mkTabData g) par) par).size _ = _
  rw [mkPairs_par, mkTri_par]; rfl

lemma mkRun3_e1hi : (mkRun3 g dtl par).e1hi =
    pgen par 256 (triOf g).size fun i => e1Of false dtl (mkExpTabs false dtl par) (triOf g)[i]! := by
  show pgen par 256 (mkTri (mkTabData g) (mkPairs (mkTabData g) par) par).size _ = _
  rw [mkPairs_par, mkTri_par]; rfl

lemma rings_size : (mkTabData g).rings.size = g.NR := by
  show ((Array.range g.NR).map (mkRing g)).size = g.NR; simp

lemma triOf_size : (triOf g).size = g.NR * g.NR * (g.ND * g.NR * g.ND) := mkTri_size (mkTabData g) _

lemma pairs_size : (mkPairs (mkTabData g) false).size = g.NR * (g.NR * g.ND) := mkPairs_size (mkTabData g)

/-- The triple kernel entries of the run. -/
lemma mkK3_get (lower : Bool) (j : ℕ) {i : ℕ} (hi : i < (triOf g).size) :
    (mkK3 (mkRun3 g dtl par) lower j par)[i]! =
      2 * powK lower (e1Of lower dtl (mkExpTabs lower dtl par) (triOf g)[i]!) j + (triOf g)[i]! % 2 := by
  have hlo : (mkRun3 g dtl par).e1lo.size = (triOf g).size := by
    rw [mkRun3_e1lo, pgen_size _ _ _ _ (Or.inl (by norm_num))]
  have hget : (mkRun3 g dtl par).e1lo[i]! = 2 * e1Of true dtl (mkExpTabs true dtl par) (triOf g)[i]! +
      (triOf g)[i]! % 2 := by
    rw [mkRun3_e1lo, pgen_get _ _ _ _ (Or.inl (by norm_num)) hi]
  unfold mkK3
  rw [pgen_get _ _ _ _ (Or.inl (by norm_num)) (by rw [hlo]; exact hi)]
  simp only
  rw [hget]
  have h2 : (2 * e1Of true dtl (mkExpTabs true dtl par) (triOf g)[i]! + (triOf g)[i]! % 2) % 2 = (triOf g)[i]! % 2 := by
    omega
  have h3 : (2 * e1Of true dtl (mkExpTabs true dtl par) (triOf g)[i]! + (triOf g)[i]! % 2) / 2 =
      e1Of true dtl (mkExpTabs true dtl par) (triOf g)[i]! := by omega
  rw [h2]
  cases lower
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [mkRun3_e1hi, pgen_get _ _ _ _ (Or.inl (by norm_num)) hi]
  · simp only [↓reduceIte]
    rw [h3]

end Mk

/-! ## Indices -/

lemma dOf_toNat {NT : ℕ} (hNT : 0 < NT) (a b : ℕ) :
    ((((b % NT : ℕ) : ℤ) - ((a % NT : ℕ) : ℤ)) + ((NT - 1 : ℕ) : ℤ)).toNat = b % NT + (NT - 1) - a % NT :=
  toNat_off _ _ _ (Nat.mod_lt _ hNT)

lemma pbcOf_eq (r : Run3) (lower : Bool) (j : ℕ) (par : Bool) (hNT : 0 < r.g.NT) (cb cc : ℕ) :
    pbcOf (rd3Of r lower j par) cb cc =
      (cb / r.g.NT * r.g.NR + cc / r.g.NT) * r.g.ND + (dOf (gR r.g) cb cc + ((r.g.NT - 1 : ℕ) : ℤ)).toNat := by
  unfold pbcOf dOf
  rw [show (gR r.g).NT = r.g.NT from rfl, dOf_toNat hNT]
  rfl

lemma t3Of_eq (r : Run3) (lower : Bool) (j : ℕ) (par : Bool) (hNT : 0 < r.g.NT) (ca cb cc : ℕ) :
    t3Of (rd3Of r lower j par) ca cb cc =
      (((cb / r.g.NT * r.g.NR + cc / r.g.NT) * r.g.ND + (dOf (gR r.g) cb cc + ((r.g.NT - 1 : ℕ) : ℤ)).toNat) * r.g.NR +
        ca / r.g.NT) * r.g.ND + (dOf (gR r.g) ca cb + ((r.g.NT - 1 : ℕ) : ℤ)).toNat := by
  unfold t3Of baseOf
  rw [pbcOf_eq r lower j par hNT]
  unfold dOf
  rw [show (gR r.g).NT = r.g.NT from rfl, dOf_toNat hNT, dOf_toNat hNT]
  show ((_ * r.g.NR) * r.g.ND + cb % r.g.NT + (r.g.NT - 1)) + ca / r.g.NT * r.g.ND - ca % r.g.NT = _
  have h1 : ca % r.g.NT < r.g.NT := Nat.mod_lt _ hNT
  generalize ((cb / r.g.NT * r.g.NR + cc / r.g.NT) * r.g.ND + (cc % r.g.NT + (r.g.NT - 1) - cb % r.g.NT)) = P
  rw [Nat.add_mul (P * r.g.NR) (ca / r.g.NT) r.g.ND]
  generalize P * r.g.NR * r.g.ND = A
  generalize ca / r.g.NT * r.g.ND = B
  omega

lemma b2n_mod2 (x : ℕ) : b2n (x % 2 == 1) = x % 2 := by
  rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [h, b2n]

lemma ite_b2n (b : Bool) : (if b then 2 else 0) = 2 * b2n b := by cases b <;> rfl
lemma ite_b2n4 (b : Bool) : (if b then 4 else 0) = 4 * b2n b := by cases b <;> rfl

lemma cell_ring_lt {NR NT c : ℕ} (hc : c < NR * NT) : c / NT < NR := Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact hc)

lemma lt_mul_add {b n L q : ℕ} (hb : b < n) (hq : q < L) : b * L + q < n * L :=
  calc b * L + q < b * L + L := by omega
    _ = (b + 1) * L := by ring
    _ ≤ n * L := Nat.mul_le_mul_right _ hb

/-- the triple index of three flat cells in the tables of `discOf3` -/
def tI (g : W2C.Grid) (ca cb cc : ℕ) : ℕ :=
  (((cb / g.NT * g.NR + cc / g.NT) * g.ND + (dOf (gR g) cb cc + ((g.NT - 1 : ℕ) : ℤ)).toNat) * g.NR + ca / g.NT) *
    g.ND + (dOf (gR g) ca cb + ((g.NT - 1 : ℕ) : ℤ)).toNat

/-- the pair index of two flat cells in the tables of `discOf3` -/
def pI (g : W2C.Grid) (ca cb : ℕ) : ℕ :=
  (ca / g.NT * g.NR + cb / g.NT) * g.ND + (dOf (gR g) ca cb + ((g.NT - 1 : ℕ) : ℤ)).toNat

/-- The triple index of three cells is in range. -/
lemma tI_lt (g : W2C.Grid) (hNT : 0 < g.NT) {ca cb cc : ℕ} (hca : ca < g.NR * g.NT) (hcb : cb < g.NR * g.NT)
    (hcc : cc < g.NR * g.NT) : tI g ca cb cc < g.NR * g.NR * (g.ND * g.NR * g.ND) := by
  have hND : g.ND = 2 * g.NT - 1 := rfl
  obtain ⟨hx, _⟩ := off_toNat (N := g.NT) (abs_dOf_lt (g := gR g) hNT cb cc)
  obtain ⟨hz, _⟩ := off_toNat (N := g.NT) (abs_dOf_lt (g := gR g) hNT ca cb)
  unfold tI
  rw [tidx_split]
  have hb : cb / g.NT * g.NR + cc / g.NT < g.NR * g.NR := lt_mul_add (cell_ring_lt hcb) (cell_ring_lt hcc)
  exact lt_mul_add hb (code3_lt (by rw [hND]; exact hx) (cell_ring_lt hca) (by rw [hND]; exact hz))

/-- The pair index of two cells is in range. -/
lemma pI_lt (g : W2C.Grid) (hNT : 0 < g.NT) {ca cb : ℕ} (hca : ca < g.NR * g.NT) (hcb : cb < g.NR * g.NT) :
    pI g ca cb < g.NR * (g.NR * g.ND) := by
  have hND : g.ND = 2 * g.NT - 1 := rfl
  obtain ⟨hx, _⟩ := off_toNat (N := g.NT) (abs_dOf_lt (g := gR g) hNT ca cb)
  unfold pI
  rw [← Nat.mul_assoc]
  exact lt_mul_add (lt_mul_add (cell_ring_lt hca) (cell_ring_lt hcb)) (by rw [hND]; exact hx)

section OK

variable (g : W2C.Grid) (dtl j : ℕ) (par lower : Bool)

lemma t3Of_run (hNT : 0 < g.NT) (ca cb cc : ℕ) :
    t3Of (rd3Of (mkRun3 g dtl par) lower j par) ca cb cc = tI g ca cb cc :=
  t3Of_eq (mkRun3 g dtl par) lower j par hNT ca cb cc

lemma pbcOf_run (hNT : 0 < g.NT) (cb cc : ℕ) : pbcOf (rd3Of (mkRun3 g dtl par) lower j par) cb cc = pI g cb cc :=
  pbcOf_eq (mkRun3 g dtl par) lower j par hNT cb cc

lemma tC_run (ca cb cc : ℕ) : tC (gR g) (discOf3 g dtl) ca cb cc = ((triOf g)[tI g ca cb cc]! % 2 == 1) := rfl

lemma k3C_run (t : ℝ) (ca cb cc : ℕ) :
    k3C (gR g) (discOf3 g dtl) t ca cb cc = Real.exp (-(t * ((((triOf g)[tI g ca cb cc]! / 2 : ℕ) : ℝ) / 2 ^ 48))) := rfl

lemma sC_run (cb cc : ℕ) : sC (gR g) (discOf3 g dtl) cb cc = (mkPairs (mkTabData g) false)[pI g cb cc]!.scls := rfl

lemma k2C_run (t : ℝ) (ca cb : ℕ) : k2C (gR g) (discOf3 g dtl) t ca cb =
    Real.exp (-(t * fx (W3C.upq (max (mkPairs (mkTabData g) false)[pI g ca cb]!.abar2 0) dtl))) := rfl

lemma uC_run (t : ℝ) (c : ℕ) : uC (gR g) (discOf3 g dtl) t c =
    Real.exp (-(t * fx (W3C.upq (mkTabData g).rings[c / g.NT]!.euHi dtl))) := rfl

lemma wC_run (c : ℕ) : wC (gR g) (discOf3 g dtl) c = (((mkTabData g).rings[c / g.NT]!.areaLo.toNat : ℕ) : ℝ) / 2 ^ PR :=
  rfl

lemma nC_run (c : ℕ) : nC (gR g) (discOf3 g dtl) c = (mkTabData g).rings[c / g.NT]!.nflag := rfl

/-- The read-only data of a run describe the tables of `discOf3`. -/
theorem rdOK_run (hNT : 0 < g.NT) (hdtl : dtl ≤ 48) :
    RdOK lower (rd3Of (mkRun3 g dtl par) lower j par) (gR g) (discOf3 g dtl) ((j : ℝ) / 2 ^ dtl) where
  NR := rfl
  NT := rfl
  NTpos := hNT
  w := by
    intro c hc
    have hir : c / g.NT < (mkTabData g).rings.size := by rw [rings_size]; exact cell_ring_lt hc
    show (((mkTabData g).rings.map (·.areaLo.toNat))[c / g.NT]! : ℝ) / 2 ^ PR = _
    rw [getElem!_map _ _ hir, wC_run]
  nb := by
    intro c hc
    have hir : c / g.NT < (mkTabData g).rings.size := by rw [rings_size]; exact cell_ring_lt hc
    show ((mkTabData g).rings.map (fun R => if R.nflag then 4 else 0))[c / g.NT]! = _
    rw [getElem!_map _ _ hir, nC_run, ite_b2n4]
  sb := by
    intro cb hcb cc hcc
    rw [pbcOf_run g dtl j par lower hNT]
    show ((mkRun3 g dtl par).pairs.map (fun p => if p.scls then 2 else 0))[pI g cb cc]! = _
    rw [mkRun3_pairs, getElem!_map _ _ (by rw [pairs_size]; exact pI_lt g hNT hcb hcc), sC_run, ite_b2n]
  kT := by
    intro ca hca cb hcb cc hcc
    rw [t3Of_run g dtl j par lower hNT]
    show (mkK3 (mkRun3 g dtl par) lower j par)[tI g ca cb cc]! % 2 = _
    rw [mkK3_get g dtl par lower j (by rw [triOf_size]; exact tI_lt g hNT hca hcb hcc), tC_run, b2n_mod2]
    omega
  kK := by
    intro ca hca cb hcb cc hcc
    rw [t3Of_run g dtl j par lower hNT]
    show Bd lower ((((mkK3 (mkRun3 g dtl par) lower j par)[tI g ca cb cc]! >>> 1 : ℕ) : ℝ) / 2 ^ 62) _
    rw [mkK3_get g dtl par lower j (by rw [triOf_size]; exact tI_lt g hNT hca hcb hcc)]
    have hsh : ∀ P b : ℕ, b < 2 → (2 * P + b) >>> 1 = P := by
      intro P b hb; rw [Nat.shiftRight_eq_div_pow]; omega
    rw [hsh _ _ (Nat.mod_lt _ (by norm_num))]
    have he := e1Of_bd lower dtl par hdtl ((triOf g)[tI g ca cb cc]!)
    have hp := powK_bd' he (Real.exp_pos _).le j
    refine Bd.trans hp (Bd.of_eq ?_)
    rw [k3C_run, ← Real.exp_nat_mul]
    congr 1
    ring

/-- The level-2 data of a run. -/
theorem l2OK_run (hNT : 0 < g.NT) (hub : ∀ ir : ℕ, 0 ≤ W3C.upq ((W3C.mkTabData g).rings[ir]!).euHi dtl) :
    L2OK lower (rd3Of (mkRun3 g dtl par) lower j par) (f1Of (mkRun3 g dtl par) lower j dtl)
      (k2Of (mkRun3 g dtl par) lower j dtl par) (gR g) (discOf3 g dtl) ((j : ℝ) / 2 ^ dtl) where
  f1 := by
    intro c hc
    have hir : c / g.NT < (mkTabData g).rings.size := by rw [rings_size]; exact cell_ring_lt hc
    show Bd lower ((((mkTabData g).rings.map fun R => kern lower j dtl (W3C.upq R.euHi dtl))[c / g.NT]! : ℕ) / (2 : ℝ) ^ 62) _
    rw [getElem!_map _ _ hir, uC_run]
    exact kern_bd lower j dtl (upq_dvd _ _) (hub _)
  k2 := by
    intro ca hca cb hcb
    have hpi := pI_lt g hNT hca hcb
    have hsz : (mkRun3 g dtl par).ab2.size = g.NR * (g.NR * g.ND) := by
      rw [mkRun3_ab2, Array.size_map, pairs_size]
    rw [pbcOf_run g dtl j par lower hNT]
    show Bd lower (((pgen par 64 (mkRun3 g dtl par).ab2.size fun i => kern lower j dtl (mkRun3 g dtl par).ab2[i]!)[
      pI g ca cb]! : ℕ) / (2 : ℝ) ^ 62) _
    rw [pgen_get _ _ _ _ (Or.inl (by norm_num)) (by rw [hsz]; exact hpi), mkRun3_ab2,
      getElem!_map _ _ (by rw [pairs_size]; exact hpi), k2C_run]
    exact kern_bd lower j dtl (upq_dvd _ _) (upq_nonneg (le_max_right _ _) _)

end OK

end BHH.W3.Rec
