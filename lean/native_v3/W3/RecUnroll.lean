/-
Window-3 recursion: the discrete bound `Psid3` unrolled into path sums over cell sequences (the pattern of
`W2/Unroll.lean`).  `Phi3 n xb xa s` is the sum of the weights of the sequences of `n + 2` cells ending in the cells
`xa, xb` whose pass (after the points `0, ..., n + 2`) is in the state with index `s`; it satisfies the window-3
recursion (`Phi3_zero`, `Phi3_succ`), and `Psid3` with `n + 3` increments is its closing sum (`Psid3_succ3`); `Psid3`
with `2` increments is given directly (`Psid3_two`).
-/
import W3.RecAuto
import W3.Defs

open Real

namespace BHH.W3.Rec

open W3C BHH BHH.W2

/-! ## Optional states through the tables -/

/-- The closing value of an optional state (twice the value, `0` for `none`). -/
def closeVal3 (o : Option St) (a : List Bool) : ℕ :=
  match o with
  | none => 0
  | some s => s.close2 a

lemma passVal3_eq (aN aS aT : ℕ → Bool) (k : ℕ) :
    passVal3 aN aS aT k = closeVal3 (runPass3 aN aS aT (k - 2)) [aN (k - 1), aS (k - 1), aT (k - 1)] := by
  unfold passVal3
  cases runPass3 aN aS aT (k - 2) <;> rfl

lemma good_runPass3 (aN aS aT : ℕ → Bool) : ∀ n s, runPass3 aN aS aT n = some s → Good3 s
  | 0, s, h => by
    simp only [runPass3, Option.some.injEq] at h
    rw [← h]; exact good_init3
  | n + 1, s, h => by
    simp only [runPass3] at h
    cases hr : runPass3 aN aS aT n with
    | none => rw [hr] at h; simp at h
    | some s0 =>
      rw [hr] at h
      simp only [Option.bind_some] at h
      exact good_step3' (good_runPass3 aN aS aT n s0 hr) _ ⟨_, _, _, rfl⟩ h

/-- The closing value of an optional good state after one more point, through the table. -/
lemma close_opt3 (o : Option St) (ho : ∀ s, o = some s → Good3 s) (a b c : Bool) :
    (closeVal3 o [a, b, c] : ℝ) =
      ∑ q ∈ Finset.range NS, if sIdx3 o = q then (cls[q * 8 + inp a b c]! : ℝ) else 0 := by
  cases o with
  | none =>
    simp only [closeVal3, Nat.cast_zero]
    symm
    apply Finset.sum_eq_zero
    intro q hq
    rw [Finset.mem_range] at hq
    have hne : sIdx3 none ≠ q := by rw [sIdx3_none]; omega
    rw [if_neg hne]
  | some s =>
    have hs := ho s rfl
    rw [Finset.sum_ite_eq (Finset.range NS) (sIdx3 (some s)),
      if_pos (show sIdx3 (some s) ∈ Finset.range NS from Finset.mem_range.mpr hs.1)]
    show (s.close2 [a, b, c] : ℝ) = (cls[stIdx s * 8 + inp a b c]! : ℝ)
    rw [cls_good hs]

/-- The transition of an optional good state, through the table. -/
lemma trans_opt3 (o : Option St) (ho : ∀ s, o = some s → Good3 s) (a b c : Bool) {s2 : ℕ} (hs2 : s2 < NS)
    (v : ℝ) :
    (if sIdx3 (o.bind (fun s => s.step [a, b, c])) = s2 then v else 0) =
      ∑ q ∈ Finset.range NS,
        if sIdx3 o = q then (if trs[q * 8 + inp a b c]! = s2 then v else 0) else 0 := by
  cases o with
  | none =>
    simp only [Option.bind_none]
    have h17 : sIdx3 none ≠ s2 := by rw [sIdx3_none]; omega
    rw [if_neg h17]
    symm
    apply Finset.sum_eq_zero
    intro q hq
    rw [Finset.mem_range] at hq
    have hne : sIdx3 none ≠ q := by rw [sIdx3_none]; omega
    rw [if_neg hne]
  | some s =>
    have hs := ho s rfl
    rw [Option.bind_some]
    rw [Finset.sum_ite_eq (Finset.range NS) (sIdx3 (some s)),
      if_pos (show sIdx3 (some s) ∈ Finset.range NS from Finset.mem_range.mpr hs.1)]
    show _ = if trs[stIdx s * 8 + inp a b c]! = s2 then v else 0
    rw [trs_good hs]

/-! ## Cell sequences -/

section Seq

variable {g : GridR} (hNR : 0 < g.NR) (hNT : 0 < g.NT) (D : DiscData3)

lemma edgeN_csnoc {n : ℕ} (c : CellSeq g n) (x : Cell g) {j : ℕ} (hj : j ≤ n) :
    edgeN hNR hNT D (csnoc c x) j = edgeN hNR hNT D c j :=
  edgeA1_csnoc hNR hNT D.toDiscData c x hj

lemma edgeN_csnoc_last {n : ℕ} (c : CellSeq g n) (x : Cell g) :
    edgeN hNR hNT D (csnoc c x) (n + 1) = D.nf x.1.val :=
  edgeA1_csnoc_last hNR hNT D.toDiscData c x

lemma edgeS_csnoc {n : ℕ} (c : CellSeq g n) (x : Cell g) {j : ℕ} (hj : j ≤ n) :
    edgeS hNR hNT D (csnoc c x) j = edgeS hNR hNT D c j :=
  edgeA2_csnoc hNR hNT D.toDiscData c x hj

lemma edgeS_csnoc_last {n : ℕ} (hn : 1 ≤ n) (c : CellSeq g n) (x : Cell g) :
    edgeS hNR hNT D (csnoc c x) (n + 1) =
      D.sc (cget hNR hNT c (n - 1)).1.val x.1.val (doff (cget hNR hNT c (n - 1)) x) :=
  edgeA2_csnoc_last hNR hNT D.toDiscData hn c x

lemma edgeS_one {n : ℕ} (c : CellSeq g n) : edgeS hNR hNT D c 1 = false :=
  edgeA2_one hNR hNT D.toDiscData c

lemma edgeT_csnoc {n : ℕ} (c : CellSeq g n) (x : Cell g) {j : ℕ} (hj : j ≤ n) :
    edgeT hNR hNT D (csnoc c x) j = edgeT hNR hNT D c j := by
  unfold edgeT
  split_ifs with h1
  · rw [cget_csnoc_lt hNR hNT c x (by omega), cget_csnoc_lt hNR hNT c x (by omega),
      cget_csnoc_lt hNR hNT c x (by omega)]
  · rfl

lemma edgeT_csnoc_last {n : ℕ} (hn : 2 ≤ n) (c : CellSeq g n) (x : Cell g) :
    edgeT hNR hNT D (csnoc c x) (n + 1) =
      D.tc (cget hNR hNT c (n - 2)).1.val (cget hNR hNT c (n - 1)).1.val x.1.val
        (doff (cget hNR hNT c (n - 2)) (cget hNR hNT c (n - 1))) (doff (cget hNR hNT c (n - 1)) x) := by
  unfold edgeT
  rw [if_pos (by omega)]
  have e1 : n + 1 - 3 = n - 2 := by omega
  have e2 : n + 1 - 2 = n - 1 := by omega
  have e3 : n + 1 - 1 = n := by omega
  simp only [e1, e2, e3]
  rw [cget_csnoc_lt hNR hNT c x (by omega), cget_csnoc_lt hNR hNT c x (by omega), cget_csnoc_last]

lemma edgeT_small {n : ℕ} (c : CellSeq g n) {j : ℕ} (hj : j ≤ 2) : edgeT hNR hNT D c j = false := by
  unfold edgeT; rw [if_neg (by omega)]

lemma runPass3_congr {a1 a2 a3 b1 b2 b3 : ℕ → Bool} :
    ∀ i, (∀ j, 1 ≤ j → j ≤ i → a1 j = b1 j ∧ a2 j = b2 j ∧ a3 j = b3 j) →
      runPass3 a1 a2 a3 i = runPass3 b1 b2 b3 i
  | 0, _ => rfl
  | i + 1, h => by
    simp only [runPass3]
    obtain ⟨h1, h2, h3⟩ := h (i + 1) (by omega) le_rfl
    rw [runPass3_congr i (fun j hj1 hj2 => h j hj1 (by omega)), h1, h2, h3]

/-- The pass state after the points `0, ..., m` of a sequence of `m` increments. -/
def seqRun3 {m : ℕ} (c : CellSeq g m) : Option St :=
  runPass3 (edgeN hNR hNT D c) (edgeS hNR hNT D c) (edgeT hNR hNT D c) m

lemma seqRun3_csnoc {n : ℕ} (c : CellSeq g n) (x : Cell g) :
    seqRun3 hNR hNT D (csnoc c x) =
      (seqRun3 hNR hNT D c).bind fun s =>
        s.step [D.nf x.1.val, edgeS hNR hNT D (csnoc c x) (n + 1), edgeT hNR hNT D (csnoc c x) (n + 1)] := by
  unfold seqRun3
  simp only [runPass3]
  rw [edgeN_csnoc_last, runPass3_congr n (fun j _ hj => ⟨edgeN_csnoc hNR hNT D c x hj,
    edgeS_csnoc hNR hNT D c x hj, edgeT_csnoc hNR hNT D c x hj⟩)]

lemma seqRun3_good {m : ℕ} (c : CellSeq g m) : ∀ s, seqRun3 hNR hNT D c = some s → Good3 s :=
  good_runPass3 _ _ _ m

lemma seqRun3_zero (c : CellSeq g 0) : seqRun3 hNR hNT D c = some St.init := rfl

lemma expoSeq3_csnoc {n : ℕ} (hn : 2 ≤ n) (c : CellSeq g n) (x : Cell g) :
    expoSeq3 hNR hNT D (csnoc c x) = expoSeq3 hNR hNT D c +
      D.a3 (cget hNR hNT c (n - 2)).1.val (cget hNR hNT c (n - 1)).1.val x.1.val
        (doff (cget hNR hNT c (n - 2)) (cget hNR hNT c (n - 1))) (doff (cget hNR hNT c (n - 1)) x) := by
  unfold expoSeq3
  rw [cget_csnoc_lt hNR hNT c x (j := 0) (by omega), Finset.sum_Ico_succ_top (by omega : 1 ≤ n), add_assoc]
  congr 1
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_Ico] at hj
    by_cases h1 : j = 1
    · rw [if_pos h1, if_pos h1, cget_csnoc_lt hNR hNT c x (j := 1) (by omega)]
    · rw [if_neg h1, if_neg h1, cget_csnoc_lt hNR hNT c x (j := j - 2) (by omega),
        cget_csnoc_lt hNR hNT c x (j := j - 1) (by omega), cget_csnoc_lt hNR hNT c x (j := j) (by omega)]
  · rw [if_neg (by omega), cget_csnoc_lt hNR hNT c x (j := n - 2) (by omega),
      cget_csnoc_lt hNR hNT c x (j := n - 1) (by omega), cget_csnoc_last]

lemma expoSeq3_two (c : CellSeq g 2) :
    expoSeq3 hNR hNT D c = D.ub (cget hNR hNT c 0).1.val +
      D.ab (cget hNR hNT c 0).1.val (cget hNR hNT c 1).1.val (doff (cget hNR hNT c 0) (cget hNR hNT c 1)) := by
  unfold expoSeq3
  have e : Finset.Ico 1 2 = {1} := by decide
  rw [e, Finset.sum_singleton, if_pos rfl]

lemma prod_csnoc3 {n : ℕ} (c : CellSeq g n) (x : Cell g) :
    ∏ j, D.w ((csnoc c x) j).1.val = (∏ j, D.w (c j).1.val) * D.w x.1.val :=
  prod_csnoc (D := D.toDiscData) c x

/-! ## Path sums -/

variable (t : ℝ)

/-- The weight `Π_j w(c_j) e^{-t (exponent bound)}` of a cell sequence. -/
noncomputable def seqWt3 {m : ℕ} (c : CellSeq g m) : ℝ :=
  (∏ j, D.w (c j).1.val) * Real.exp (-(t * expoSeq3 hNR hNT D c))

/-- The path sum: sequences of `n + 2` cells ending in `xa, xb` whose pass is in the state with index `s`. -/
noncomputable def Phi3 (n : ℕ) (xb xa : Cell g) (s : ℕ) : ℝ :=
  ∑ c : CellSeq g (n + 2),
    if cget hNR hNT c (n + 1) = xb ∧ cget hNR hNT c n = xa ∧ sIdx3 (seqRun3 hNR hNT D c) = s then
      seqWt3 hNR hNT D t c else 0

/-- A sum over sequences of two cells. -/
lemma sum_two (F : CellSeq g 2 → ℝ) :
    ∑ c, F c = ∑ z : Cell g, ∑ y : Cell g, F (csnoc (csnoc (default : CellSeq g 0) z) y) := by
  rw [sum_snoc, sum_snoc, Fintype.sum_unique]
  rfl

lemma cget_two_zero (z y : Cell g) : cget hNR hNT (csnoc (csnoc (default : CellSeq g 0) z) y) 0 = z := by
  rw [cget_csnoc_lt hNR hNT _ y (by omega)]
  exact cget_csnoc_last hNR hNT _ z

lemma cget_two_one (z y : Cell g) : cget hNR hNT (csnoc (csnoc (default : CellSeq g 0) z) y) 1 = y :=
  cget_csnoc_last hNR hNT _ y

lemma seqRun3_two (z y : Cell g) :
    seqRun3 hNR hNT D (csnoc (csnoc (default : CellSeq g 0) z) y) =
      (St.init.step [D.nf z.1.val, false, false]).bind
        (fun s1 => s1.step [D.nf y.1.val, D.sc z.1.val y.1.val (doff z y), false]) := by
  rw [seqRun3_csnoc, seqRun3_csnoc, seqRun3_zero, edgeS_one, edgeT_small hNR hNT D _ (by omega),
    edgeS_csnoc_last hNR hNT D (by omega), edgeT_small hNR hNT D _ (by omega)]
  simp only [Option.bind_some]
  rw [show 1 - 1 = 0 from rfl, cget_csnoc_last]

lemma seqWt3_two (z y : Cell g) :
    seqWt3 hNR hNT D t (csnoc (csnoc (default : CellSeq g 0) z) y) =
      D.w z.1.val * D.w y.1.val * Real.exp (-(t * (D.ub z.1.val + D.ab z.1.val y.1.val (doff z y)))) := by
  unfold seqWt3
  rw [prod_csnoc3, prod_csnoc3, expoSeq3_two, cget_two_zero, cget_two_one]
  simp

lemma Phi3_zero (xb xa : Cell g) (s : ℕ) :
    Phi3 hNR hNT D t 0 xb xa s =
      if sIdx3 ((St.init.step [D.nf xa.1.val, false, false]).bind
          (fun s1 => s1.step [D.nf xb.1.val, D.sc xa.1.val xb.1.val (doff xa xb), false])) = s
      then D.w xa.1.val * D.w xb.1.val *
        Real.exp (-(t * (D.ub xa.1.val + D.ab xa.1.val xb.1.val (doff xa xb))))
      else 0 := by
  unfold Phi3
  rw [sum_two]
  simp only [zero_add, cget_two_zero, cget_two_one, seqRun3_two, seqWt3_two]
  rw [Finset.sum_eq_single xa]
  · rw [Finset.sum_eq_single xb]
    · simp only [true_and]
    · intro y _ hy
      rw [if_neg (fun h => hy h.1)]
    · intro h; exact absurd (Finset.mem_univ xb) h
  · intro z _ hz
    apply Finset.sum_eq_zero
    intro y _
    rw [if_neg (fun h => hz h.2.1)]
  · intro h; exact absurd (Finset.mem_univ xa) h

/-- The weight of a sequence with one more cell (`n + 2 ≥ 2` cells before). -/
lemma seqWt3_csnoc {n : ℕ} (c' : CellSeq g (n + 2)) (x : Cell g) :
    seqWt3 hNR hNT D t (csnoc c' x) =
      D.w x.1.val * Real.exp (-(t * D.a3 (cget hNR hNT c' n).1.val (cget hNR hNT c' (n + 1)).1.val x.1.val
        (doff (cget hNR hNT c' n) (cget hNR hNT c' (n + 1))) (doff (cget hNR hNT c' (n + 1)) x))) *
        seqWt3 hNR hNT D t c' := by
  unfold seqWt3
  rw [prod_csnoc3, expoSeq3_csnoc hNR hNT D (by omega)]
  rw [show n + 2 - 2 = n by omega, show n + 2 - 1 = n + 1 by omega, mul_add, neg_add, Real.exp_add]
  ring

/-- The pass after one more cell (`n + 2 ≥ 2` cells before). -/
lemma seqRun3_csnoc' {n : ℕ} (c' : CellSeq g (n + 2)) (x : Cell g) :
    seqRun3 hNR hNT D (csnoc c' x) =
      (seqRun3 hNR hNT D c').bind fun s =>
        s.step [D.nf x.1.val, D.sc (cget hNR hNT c' (n + 1)).1.val x.1.val (doff (cget hNR hNT c' (n + 1)) x),
          D.tc (cget hNR hNT c' n).1.val (cget hNR hNT c' (n + 1)).1.val x.1.val
            (doff (cget hNR hNT c' n) (cget hNR hNT c' (n + 1))) (doff (cget hNR hNT c' (n + 1)) x)] := by
  rw [seqRun3_csnoc, edgeS_csnoc_last hNR hNT D (by omega), edgeT_csnoc_last hNR hNT D (by omega)]
  rw [show n + 2 - 2 = n by omega, show n + 2 - 1 = n + 1 by omega]

/-- The step of the path sums. -/
lemma Phi3_succ (n : ℕ) (xc xb : Cell g) {s2 : ℕ} (hs2 : s2 < NS) :
    Phi3 hNR hNT D t (n + 1) xc xb s2 =
      ∑ xa : Cell g, ∑ s ∈ Finset.range NS,
        (if trs[s * 8 + inp (D.nf xc.1.val) (D.sc xb.1.val xc.1.val (doff xb xc))
              (D.tc xa.1.val xb.1.val xc.1.val (doff xa xb) (doff xb xc))]! = s2
          then D.w xc.1.val * Real.exp (-(t * D.a3 xa.1.val xb.1.val xc.1.val (doff xa xb) (doff xb xc)))
          else 0) * Phi3 hNR hNT D t n xb xa s := by
  unfold Phi3
  rw [sum_snoc]
  have h1 : ∀ c' : CellSeq g (n + 2),
      (∑ y : Cell g, if cget hNR hNT (Fin.snoc (α := fun _ => Cell g) c' y) (n + 1 + 1) = xc ∧
          cget hNR hNT (Fin.snoc (α := fun _ => Cell g) c' y) (n + 1) = xb ∧
          sIdx3 (seqRun3 hNR hNT D (Fin.snoc (α := fun _ => Cell g) c' y)) = s2
        then seqWt3 hNR hNT D t (Fin.snoc (α := fun _ => Cell g) c' y) else 0) =
      ∑ xa : Cell g, ∑ s ∈ Finset.range NS,
        if cget hNR hNT c' (n + 1) = xb ∧ cget hNR hNT c' n = xa ∧ sIdx3 (seqRun3 hNR hNT D c') = s then
          (if trs[s * 8 + inp (D.nf xc.1.val) (D.sc xb.1.val xc.1.val (doff xb xc))
                (D.tc xa.1.val xb.1.val xc.1.val (doff xa xb) (doff xb xc))]! = s2
            then D.w xc.1.val * Real.exp (-(t * D.a3 xa.1.val xb.1.val xc.1.val (doff xa xb) (doff xb xc)))
            else 0) * seqWt3 hNR hNT D t c'
        else 0 := by
    intro c'
    rw [Finset.sum_eq_single xc]
    · have hc : Fin.snoc (α := fun _ => Cell g) c' xc = csnoc c' xc := rfl
      rw [hc, cget_csnoc_last, cget_csnoc_lt hNR hNT c' xc (by omega), seqRun3_csnoc', seqWt3_csnoc]
      simp only [true_and]
      by_cases hb : cget hNR hNT c' (n + 1) = xb
      · rw [Finset.sum_eq_single (cget hNR hNT c' n)]
        · simp only [hb, true_and]
          rw [trans_opt3 _ (seqRun3_good hNR hNT D c') _ _ _ hs2]
          apply Finset.sum_congr rfl
          intro s _
          by_cases hs : sIdx3 (seqRun3 hNR hNT D c') = s
          · rw [if_pos hs, if_pos hs]
            split_ifs <;> ring
          · rw [if_neg hs, if_neg hs]
        · intro xa _ hxa
          apply Finset.sum_eq_zero
          intro s _
          rw [if_neg (fun h => hxa h.2.1.symm)]
        · intro h; exact absurd (Finset.mem_univ _) h
      · have h0 : ¬ (sIdx3 ((seqRun3 hNR hNT D c').bind fun s =>
            s.step [D.nf xc.1.val, D.sc (cget hNR hNT c' (n + 1)).1.val xc.1.val
              (doff (cget hNR hNT c' (n + 1)) xc),
              D.tc (cget hNR hNT c' n).1.val (cget hNR hNT c' (n + 1)).1.val xc.1.val
                (doff (cget hNR hNT c' n) (cget hNR hNT c' (n + 1))) (doff (cget hNR hNT c' (n + 1)) xc)]) = s2 ∧
            False) := fun h => h.2
        rw [if_neg (fun h => hb h.1)]
        symm
        apply Finset.sum_eq_zero
        intro xa _
        apply Finset.sum_eq_zero
        intro s _
        rw [if_neg (fun h => hb h.1)]
    · intro y _ hy
      have hc : Fin.snoc (α := fun _ => Cell g) c' y = csnoc c' y := rfl
      rw [hc, cget_csnoc_last, if_neg (fun h => hy h.1)]
    · intro h; exact absurd (Finset.mem_univ xc) h
  rw [Finset.sum_congr rfl (fun c' _ => h1 c'), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro xa _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c' _
  split_ifs <;> ring

/-- `Psid3` with `n + 3` increments through the path sums of `n + 2` cells. -/
lemma Psid3_succ3 (n : ℕ) :
    Psid3 g hNR hNT D (n + 3) t =
      (1 / 2) * ∑ xc : Cell g, ∑ xb : Cell g, ∑ xa : Cell g, ∑ s ∈ Finset.range NS,
        ((cls[s * 8 + inp (D.nf xc.1.val) (D.sc xb.1.val xc.1.val (doff xb xc))
            (D.tc xa.1.val xb.1.val xc.1.val (doff xa xb) (doff xb xc))]! : ℝ) *
          (D.w xc.1.val * Real.exp (-(t * D.a3 xa.1.val xb.1.val xc.1.val (doff xa xb) (doff xb xc))))) *
          Phi3 hNR hNT D t n xb xa s := by
  unfold Psid3
  rw [sum_snoc]
  have h1 : ∀ (c' : CellSeq g (n + 2)) (xc : Cell g),
      (passVal3 (edgeN hNR hNT D (Fin.snoc (α := fun _ => Cell g) c' xc))
          (edgeS hNR hNT D (Fin.snoc (α := fun _ => Cell g) c' xc))
          (edgeT hNR hNT D (Fin.snoc (α := fun _ => Cell g) c' xc)) (n + 3 + 1) : ℝ) / 2 *
          (∏ j, D.w ((Fin.snoc (α := fun _ => Cell g) c' xc) j).1.val) *
          Real.exp (-(t * expoSeq3 hNR hNT D (Fin.snoc (α := fun _ => Cell g) c' xc))) =
        (1 / 2) * ∑ xb : Cell g, ∑ xa : Cell g, ∑ s ∈ Finset.range NS,
          if cget hNR hNT c' (n + 1) = xb ∧ cget hNR hNT c' n = xa ∧ sIdx3 (seqRun3 hNR hNT D c') = s then
            ((cls[s * 8 + inp (D.nf xc.1.val) (D.sc xb.1.val xc.1.val (doff xb xc))
                (D.tc xa.1.val xb.1.val xc.1.val (doff xa xb) (doff xb xc))]! : ℝ) *
              (D.w xc.1.val * Real.exp (-(t * D.a3 xa.1.val xb.1.val xc.1.val (doff xa xb) (doff xb xc))))) *
              seqWt3 hNR hNT D t c'
          else 0 := by
    intro c' xc
    have hc : Fin.snoc (α := fun _ => Cell g) c' xc = csnoc c' xc := rfl
    rw [hc]
    have hpv : passVal3 (edgeN hNR hNT D (csnoc c' xc)) (edgeS hNR hNT D (csnoc c' xc))
        (edgeT hNR hNT D (csnoc c' xc)) (n + 3 + 1) =
        closeVal3 (seqRun3 hNR hNT D c')
          [D.nf xc.1.val, D.sc (cget hNR hNT c' (n + 1)).1.val xc.1.val (doff (cget hNR hNT c' (n + 1)) xc),
            D.tc (cget hNR hNT c' n).1.val (cget hNR hNT c' (n + 1)).1.val xc.1.val
              (doff (cget hNR hNT c' n) (cget hNR hNT c' (n + 1))) (doff (cget hNR hNT c' (n + 1)) xc)] := by
      rw [passVal3_eq]
      rw [show n + 3 + 1 - 2 = n + 2 by omega, show n + 3 + 1 - 1 = n + 2 + 1 by omega]
      rw [edgeN_csnoc_last, edgeS_csnoc_last hNR hNT D (by omega), edgeT_csnoc_last hNR hNT D (by omega)]
      rw [show n + 2 - 2 = n by omega, show n + 2 - 1 = n + 1 by omega]
      congr 1
      exact runPass3_congr (n + 2) (fun j _ hj => ⟨edgeN_csnoc hNR hNT D c' xc hj,
        edgeS_csnoc hNR hNT D c' xc hj, edgeT_csnoc hNR hNT D c' xc hj⟩)
    have hw : (∏ j, D.w ((csnoc c' xc) j).1.val) * Real.exp (-(t * expoSeq3 hNR hNT D (csnoc c' xc))) =
        seqWt3 hNR hNT D t (csnoc c' xc) := rfl
    rw [hpv, close_opt3 _ (seqRun3_good hNR hNT D c'), mul_assoc, hw, seqWt3_csnoc]
    rw [Finset.sum_eq_single (cget hNR hNT c' (n + 1))]
    · rw [Finset.sum_eq_single (cget hNR hNT c' n)]
      · simp only [true_and]
        rw [Finset.sum_div, Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        split_ifs <;> ring
      · intro xa _ hxa
        apply Finset.sum_eq_zero
        intro s _
        rw [if_neg (fun h => hxa h.2.1.symm)]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro xb _ hxb
      apply Finset.sum_eq_zero
      intro xa _
      apply Finset.sum_eq_zero
      intro s _
      rw [if_neg (fun h => hxb h.1.symm)]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [Finset.sum_congr rfl (fun c' _ => Finset.sum_congr rfl (fun xc _ => h1 c' xc)), Finset.sum_comm,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro xc _
  rw [← Finset.mul_sum]
  congr 1
  unfold Phi3
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro xb _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro xa _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c' _
  split_ifs <;> ring

/-- `Psid3` with `2` increments. -/
lemma Psid3_two :
    Psid3 g hNR hNT D 2 t =
      (1 / 2) * ∑ xb : Cell g, ∑ xa : Cell g,
        (closeVal3 (St.init.step [D.nf xa.1.val, false, false])
            [D.nf xb.1.val, D.sc xa.1.val xb.1.val (doff xa xb), false] : ℝ) *
          (D.w xa.1.val * D.w xb.1.val *
            Real.exp (-(t * (D.ub xa.1.val + D.ab xa.1.val xb.1.val (doff xa xb))))) := by
  unfold Psid3
  rw [sum_two, Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro xb _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro xa _
  have hw : (∏ j, D.w ((csnoc (csnoc (default : CellSeq g 0) xa) xb) j).1.val) *
      Real.exp (-(t * expoSeq3 hNR hNT D (csnoc (csnoc (default : CellSeq g 0) xa) xb))) =
      seqWt3 hNR hNT D t (csnoc (csnoc (default : CellSeq g 0) xa) xb) := rfl
  rw [mul_assoc, hw, seqWt3_two, passVal3_eq]
  have hr : runPass3 (edgeN hNR hNT D (csnoc (csnoc (default : CellSeq g 0) xa) xb))
      (edgeS hNR hNT D (csnoc (csnoc (default : CellSeq g 0) xa) xb))
      (edgeT hNR hNT D (csnoc (csnoc (default : CellSeq g 0) xa) xb)) (2 + 1 - 2) =
      St.init.step [D.nf xa.1.val, false, false] := by
    have := seqRun3_csnoc hNR hNT D (default : CellSeq g 0) xa
    rw [seqRun3_zero, edgeS_one, edgeT_small hNR hNT D _ (by omega)] at this
    simp only [Option.bind_some] at this
    rw [← this]
    show runPass3 _ _ _ 1 = runPass3 _ _ _ 1
    exact runPass3_congr 1 (fun j _ hj => ⟨edgeN_csnoc hNR hNT D _ xb hj,
      edgeS_csnoc hNR hNT D _ xb hj, edgeT_csnoc hNR hNT D _ xb hj⟩)
  rw [hr, show 2 + 1 - 1 = 1 + 1 from rfl, edgeN_csnoc_last, edgeS_csnoc_last hNR hNT D (by omega),
    edgeT_small hNR hNT D _ (by omega), show 1 - 1 = 0 from rfl, cget_csnoc_last]
  ring

end Seq

end BHH.W3.Rec
