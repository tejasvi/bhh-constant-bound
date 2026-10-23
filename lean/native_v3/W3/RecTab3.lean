/-
Window-3 recursion: the tables of a run.  The pair and triple tables of `W3C.mkRun3` do not depend on
`par` (tasks give the sequential arrays), and the tables of `discOf3` are mirror symmetric (`MirOK`): the pair table by
the symmetrisation `symPair` of the entries at `d` and `-d`, the triple table by the mirror copies of `mkTri`.
-/
import W3.RecIter3
import W3.Interfaces

open Real

namespace BHH.W3.Rec

open W3C W2C BHH BHH.W2 BHH.Cert

attribute [local irreducible] W3C.NS W3C.reachable W3C.trs W3C.cls

/-! ## Without tasks -/

lemma map_task_get {α β : Type} (l : List α) (f : α → β) :
    (l.map fun x => Task.spawn fun _ => f x).map Task.get = l.map f := by
  rw [List.map_map]; rfl

lemma rawPairs_par (td : TabData) (par : Bool) : rawPairs td par = rawPairs td false := by
  cases par
  · rfl
  · unfold rawPairs
    simp only [↓reduceIte, Bool.false_eq_true]
    rw [map_task_get]

lemma mkPairs_par (td : TabData) (par : Bool) : mkPairs td par = mkPairs td false := by
  unfold mkPairs; rw [rawPairs_par]

lemma mkTri_par (td : TabData) (pairs : Array PairE) (par : Bool) : mkTri td pairs par = mkTri td pairs false := by
  cases par
  · rfl
  · unfold mkTri
    simp only [↓reduceIte, Bool.false_eq_true]
    rw [map_task_get]

/-! ## Sizes and entries -/

lemma rawPairs_size (td : TabData) : (rawPairs td false).size = td.g.NR * (td.g.NR * td.g.ND) := by
  unfold rawPairs
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [foldl_rows (td.g.NR * td.g.ND)
    (fun ir q => pairEntryF td ir (q / td.g.ND) (Int.ofNat (q % td.g.ND) - Int.ofNat (td.g.NT - 1))) td.g.NR]
  simp

lemma mkPairs_size (td : TabData) : (mkPairs td false).size = td.g.NR * (td.g.NR * td.g.ND) := by
  unfold mkPairs; simp only [Array.size_map, Array.size_range]; rw [rawPairs_size]

lemma mkPairs_get (td : TabData) {p : ℕ} (hp : p < td.g.NR * (td.g.NR * td.g.ND)) :
    (mkPairs td false)[p]! = symPair (rawPairs td false)[p]!
      (rawPairs td false)[p - p % td.g.ND + (td.g.ND - 1 - p % td.g.ND)]! := by
  unfold mkPairs
  simp only
  rw [getElem!_map _ _ (by simpa [rawPairs_size] using hp), range_getElem! (by rw [rawPairs_size]; exact hp)]

lemma symPair_comm (a b : PairE) : symPair a b = symPair b a := by
  unfold symPair; rw [Bool.and_comm, max_comm, min_comm]

/-- The pair table is mirror symmetric: offset index `di ↦ ND - 1 - di`. -/
lemma mkPairs_mir (td : TabData) (hND : 0 < td.g.ND) {a di : ℕ} (ha : a < td.g.NR * td.g.NR) (hdi : di < td.g.ND) :
    (mkPairs td false)[a * td.g.ND + (td.g.ND - 1 - di)]! = (mkPairs td false)[a * td.g.ND + di]! := by
  have hlt : ∀ x < td.g.ND, a * td.g.ND + x < td.g.NR * (td.g.NR * td.g.ND) := by
    intro x hx
    have : a * td.g.ND + x < (a + 1) * td.g.ND := by rw [add_mul, one_mul]; omega
    rw [← Nat.mul_assoc]
    exact lt_of_lt_of_le this (Nat.mul_le_mul_right _ ha)
  rw [mkPairs_get td (hlt _ (by omega)), mkPairs_get td (hlt _ hdi), flat_mod _ _ (by omega : td.g.ND - 1 - di < td.g.ND),
    flat_mod _ _ hdi]
  rw [show a * td.g.ND + (td.g.ND - 1 - di) - (td.g.ND - 1 - di) + (td.g.ND - 1 - (td.g.ND - 1 - di)) =
      a * td.g.ND + di by omega,
    show a * td.g.ND + di - di + (td.g.ND - 1 - di) = a * td.g.ND + (td.g.ND - 1 - di) by omega]
  exact symPair_comm _ _

/-! ## The triple table -/

/-- the decoding of a block index `q = (x NR + y) ND + z` -/
lemma decode3 {NR ND x y z : ℕ} (hy : y < NR) (hz : z < ND) :
    ((x * NR + y) * ND + z) / (NR * ND) = x ∧ ((x * NR + y) * ND + z) / ND % NR = y ∧
      ((x * NR + y) * ND + z) % ND = z := by
  have hND : 0 < ND := by omega
  have h1 : (x * NR + y) * ND + z = x * (NR * ND) + (y * ND + z) := by ring
  have h2 : y * ND + z < NR * ND := by
    have : y * ND + z < (y + 1) * ND := by rw [add_mul, one_mul]; omega
    exact lt_of_lt_of_le this (Nat.mul_le_mul_right _ hy)
  have hpos : 0 < NR * ND := Nat.mul_pos (by omega) hND
  refine ⟨?_, ?_, flat_mod _ _ hz⟩
  · rw [h1, Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt h2, zero_add]
  · rw [flat_div _ _ hz, flat_mod _ _ hy]

lemma code3_lt {NR ND x y z : ℕ} (hx : x < ND) (hy : y < NR) (hz : z < ND) :
    (x * NR + y) * ND + z < ND * NR * ND := by
  have h1 : x * NR + y < ND * NR := by
    have : x * NR + y < (x + 1) * NR := by rw [add_mul, one_mul]; omega
    exact lt_of_lt_of_le this (Nat.mul_le_mul_right _ hx)
  calc (x * NR + y) * ND + z < (x * NR + y) * ND + ND := by omega
    _ = (x * NR + y + 1) * ND := by ring
    _ ≤ ND * NR * ND := Nat.mul_le_mul_right _ h1

/-- the computed half of the triple blocks, and the mirror pairs -/
lemma canon3_not {NT a b : ℕ} (hNT : 0 < NT) (ha : a < 2 * NT - 1) (hb : b < 2 * NT - 1)
    (h : canon3 NT a b = false) : canon3 NT (2 * NT - 1 - 1 - a) (2 * NT - 1 - 1 - b) = true := by
  unfold canon3 at h ⊢
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, Bool.and_eq_false_iff, beq_eq_false_iff_ne,
    not_lt] at h
  simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq]
  omega

lemma canon3_yes {NT a b : ℕ} (hNT : 0 < NT) (ha : a < 2 * NT - 1) (hb : b < 2 * NT - 1)
    (h : canon3 NT a b = true) (hne : ¬ (a = NT - 1 ∧ b = NT - 1)) :
    canon3 NT (2 * NT - 1 - 1 - a) (2 * NT - 1 - 1 - b) = false := by
  unfold canon3 at h ⊢
  simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at h
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, Bool.and_eq_false_iff, beq_eq_false_iff_ne, not_lt]
  omega

lemma canon3_not' {NT ND a b : ℕ} (hNT : 0 < NT) (hND : ND = 2 * NT - 1) (ha : a < ND) (hb : b < ND)
    (h : canon3 NT a b = false) : canon3 NT (ND - 1 - a) (ND - 1 - b) = true := by
  subst hND; exact canon3_not hNT ha hb h

lemma canon3_yes' {NT ND a b : ℕ} (hNT : 0 < NT) (hND : ND = 2 * NT - 1) (ha : a < ND) (hb : b < ND)
    (h : canon3 NT a b = true) (hne : ¬ (a = NT - 1 ∧ b = NT - 1)) : canon3 NT (ND - 1 - a) (ND - 1 - b) = false := by
  subst hND; exact canon3_yes hNT ha hb h hne

/-- the block function of `mkTri`: the computed half and the mirror copies -/
def blockF (NR NT ND : ℕ) (half : Array ℕ) (q : ℕ) : ℕ :=
  if canon3 NT (q / (NR * ND)) (q % ND) then half[q]!
  else half[((ND - 1 - q / (NR * ND)) * NR + q / ND % NR) * ND + (ND - 1 - q % ND)]!

/-- An abstract block is symmetric under the mirror map. -/
lemma blockF_mir (NR NT ND : ℕ) (hNT : 0 < NT) (hND : ND = 2 * NT - 1) (half : Array ℕ) {x y z : ℕ} (hx : x < ND)
    (hy : y < NR) (hz : z < ND) :
    blockF NR NT ND half (((ND - 1 - x) * NR + y) * ND + (ND - 1 - z)) = blockF NR NT ND half ((x * NR + y) * ND + z) := by
  obtain ⟨d1, d2, d3⟩ := decode3 (NR := NR) (ND := ND) (x := x) hy hz
  obtain ⟨e1, e2, e3⟩ := decode3 (NR := NR) (ND := ND) (x := ND - 1 - x) hy (by omega : ND - 1 - z < ND)
  have hxx : ND - 1 - (ND - 1 - x) = x := by omega
  have hzz : ND - 1 - (ND - 1 - z) = z := by omega
  unfold blockF
  rw [d1, d2, d3, e1, e2, e3, hxx, hzz]
  by_cases hc : canon3 NT x z = true
  · by_cases hself : x = NT - 1 ∧ z = NT - 1
    · obtain ⟨rfl, rfl⟩ := hself
      have : ND - 1 - (NT - 1) = NT - 1 := by omega
      rw [this]
    · rw [if_neg (by rw [canon3_yes' hNT hND hx hz hc hself]; simp), if_pos hc]
  · have hc0 : canon3 NT x z = false := by simpa using hc
    rw [if_pos (canon3_not' hNT hND hx hz hc0), if_neg (by rw [hc0]; simp)]

lemma mkTri_size (td : TabData) (pairs : Array PairE) :
    (mkTri td pairs false).size = td.g.NR * td.g.NR * (td.g.ND * td.g.NR * td.g.ND) := by
  unfold mkTri
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [foldl_rows (td.g.ND * td.g.NR * td.g.ND)]
  simp

lemma foldl_rows_get {β : Type} [Inhabited β] (L : ℕ) (G : ℕ → ℕ → β) (n : ℕ) {b q : ℕ} (hb : b < n)
    (hq : q < L) : (((List.range n).map fun ir => (Array.range L).map (G ir)).foldl (· ++ ·) #[])[b * L + q]! =
      G b q := by
  have hlt : b * L + q < n * L := by
    have : b * L + q < (b + 1) * L := by rw [add_mul, one_mul]; omega
    exact lt_of_lt_of_le this (Nat.mul_le_mul_right _ hb)
  rw [foldl_rows L G n, getElem!_map _ _ (by simpa using hlt), range_getElem! hlt, flat_div _ _ hq, flat_mod _ _ hq]

/-- The triple table is mirror symmetric. -/
lemma mkTri_mir (td : TabData) (pairs : Array PairE) (hNT : 0 < td.g.NT) (hND : td.g.ND = 2 * td.g.NT - 1)
    {b x y z : ℕ} (hb : b < td.g.NR * td.g.NR) (hx : x < td.g.ND) (hy : y < td.g.NR) (hz : z < td.g.ND) :
    (mkTri td pairs false)[b * (td.g.ND * td.g.NR * td.g.ND) +
        (((td.g.ND - 1 - x) * td.g.NR + y) * td.g.ND + (td.g.ND - 1 - z))]! =
      (mkTri td pairs false)[b * (td.g.ND * td.g.NR * td.g.ND) + ((x * td.g.NR + y) * td.g.ND + z)]! := by
  have hq := code3_lt (NR := td.g.NR) hx hy hz
  have hq' := code3_lt (NR := td.g.NR) (by omega : td.g.ND - 1 - x < td.g.ND) hy (by omega : td.g.ND - 1 - z < td.g.ND)
  unfold mkTri
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [foldl_rows_get _ _ _ hb hq', foldl_rows_get _ _ _ hb hq]
  show blockF td.g.NR td.g.NT td.g.ND _ _ = blockF td.g.NR td.g.NT td.g.ND _ _
  exact blockF_mir td.g.NR td.g.NT td.g.ND hNT hND _ hx hy hz

/-! ## The tables of `discOf3` -/

lemma discOf3_ab (g : W2C.Grid) (dtl ir ir2 : ℕ) (d : ℤ) :
    (discOf3 g dtl).ab ir ir2 d = fx (W3C.upq (max (mkPairs (mkTabData g) false)[(ir * g.NR + ir2) * g.ND +
      (d + ((g.NT - 1 : ℕ) : ℤ)).toNat]!.abar2 0) dtl) := rfl

lemma discOf3_sc (g : W2C.Grid) (dtl ir ir2 : ℕ) (d : ℤ) :
    (discOf3 g dtl).sc ir ir2 d = (mkPairs (mkTabData g) false)[(ir * g.NR + ir2) * g.ND +
      (d + ((g.NT - 1 : ℕ) : ℤ)).toNat]!.scls := rfl

lemma discOf3_a3 (g : W2C.Grid) (dtl ia ib ic : ℕ) (dab dbc : ℤ) :
    (discOf3 g dtl).a3 ia ib ic dab dbc = (((mkTri (mkTabData g) (mkPairs (mkTabData g) false) false)[
      (((ib * g.NR + ic) * g.ND + (dbc + ((g.NT - 1 : ℕ) : ℤ)).toNat) * g.NR + ia) * g.ND +
        (dab + ((g.NT - 1 : ℕ) : ℤ)).toNat]! / 2 : ℕ) : ℝ) / 2 ^ 48 := rfl

lemma discOf3_tc (g : W2C.Grid) (dtl ia ib ic : ℕ) (dab dbc : ℤ) :
    (discOf3 g dtl).tc ia ib ic dab dbc = ((mkTri (mkTabData g) (mkPairs (mkTabData g) false) false)[
      (((ib * g.NR + ic) * g.ND + (dbc + ((g.NT - 1 : ℕ) : ℤ)).toNat) * g.NR + ia) * g.ND +
        (dab + ((g.NT - 1 : ℕ) : ℤ)).toNat]! % 2 == 1) := rfl

lemma off_toNat {N : ℕ} {d : ℤ} (hd : |d| < N) :
    (d + ((N - 1 : ℕ) : ℤ)).toNat < 2 * N - 1 ∧
      (-d + ((N - 1 : ℕ) : ℤ)).toNat = 2 * N - 1 - 1 - (d + ((N - 1 : ℕ) : ℤ)).toNat := by
  rw [abs_lt] at hd
  constructor <;> omega

lemma tidx_split (NR ND ia ib ic x z : ℕ) :
    (((ib * NR + ic) * ND + x) * NR + ia) * ND + z = (ib * NR + ic) * (ND * NR * ND) + ((x * NR + ia) * ND + z) := by
  ring

theorem mirOK_discOf3 (g : W2C.Grid) (dtl : ℕ) (hNT : 0 < g.NT) : MirOK (gR g) (discOf3 g dtl) := by
  have hND : g.ND = 2 * g.NT - 1 := rfl
  have hND0 : 0 < (mkTabData g).g.ND := by show 0 < g.ND; omega
  refine ⟨fun ir ir2 d hir hir2 hd => ?_, fun ir ir2 d hir hir2 hd => ?_,
    fun ia ib ic dab dbc hia hib hic hab hbc => ?_, fun ia ib ic dab dbc hia hib hic hab hbc => ?_⟩
  · obtain ⟨h1, h2⟩ := off_toNat (N := g.NT) hd
    rw [discOf3_ab, discOf3_ab, h2]
    have ha : ir * g.NR + ir2 < g.NR * g.NR := by
      have : ir * g.NR + ir2 < (ir + 1) * g.NR := by rw [add_mul, one_mul]; exact Nat.add_lt_add_left hir2 _
      exact lt_of_lt_of_le this (Nat.mul_le_mul_right _ hir)
    have := mkPairs_mir (mkTabData g) hND0 (a := ir * g.NR + ir2) ha (di := (d + ((g.NT - 1 : ℕ) : ℤ)).toNat) h1
    rw [← hND]
    exact congrArg (fun p : PairE => fx (W3C.upq (max p.abar2 0) dtl)) this
  · obtain ⟨h1, h2⟩ := off_toNat (N := g.NT) hd
    rw [discOf3_sc, discOf3_sc, h2]
    have ha : ir * g.NR + ir2 < g.NR * g.NR := by
      have : ir * g.NR + ir2 < (ir + 1) * g.NR := by rw [add_mul, one_mul]; exact Nat.add_lt_add_left hir2 _
      exact lt_of_lt_of_le this (Nat.mul_le_mul_right _ hir)
    have := mkPairs_mir (mkTabData g) hND0 (a := ir * g.NR + ir2) ha (di := (d + ((g.NT - 1 : ℕ) : ℤ)).toNat) h1
    rw [← hND]
    exact congrArg (fun p : PairE => p.scls) this
  · obtain ⟨h1, h2⟩ := off_toNat (N := g.NT) hab
    obtain ⟨h3, h4⟩ := off_toNat (N := g.NT) hbc
    rw [discOf3_a3, discOf3_a3, h2, h4, tidx_split, tidx_split]
    have hb : ib * g.NR + ic < g.NR * g.NR := by
      have : ib * g.NR + ic < (ib + 1) * g.NR := by rw [add_mul, one_mul]; exact Nat.add_lt_add_left hic _
      exact lt_of_lt_of_le this (Nat.mul_le_mul_right _ hib)
    have := mkTri_mir (mkTabData g) (mkPairs (mkTabData g) false) hNT hND hb h3 hia h1
    rw [← hND]
    exact congrArg (fun v : ℕ => ((v / 2 : ℕ) : ℝ) / 2 ^ 48) this
  · obtain ⟨h1, h2⟩ := off_toNat (N := g.NT) hab
    obtain ⟨h3, h4⟩ := off_toNat (N := g.NT) hbc
    rw [discOf3_tc, discOf3_tc, h2, h4, tidx_split, tidx_split]
    have hb : ib * g.NR + ic < g.NR * g.NR := by
      have : ib * g.NR + ic < (ib + 1) * g.NR := by rw [add_mul, one_mul]; exact Nat.add_lt_add_left hic _
      exact lt_of_lt_of_le this (Nat.mul_le_mul_right _ hib)
    have := mkTri_mir (mkTabData g) (mkPairs (mkTabData g) false) hNT hND hb h3 hia h1
    rw [← hND]
    exact congrArg (fun v : ℕ => v % 2 == 1) this

end BHH.W3.Rec
