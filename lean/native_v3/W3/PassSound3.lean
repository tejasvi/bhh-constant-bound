/-
The window-3 pass and the value bound.

* `lemma1 : Lemma1`: `0 ≤ Val3 H ≤ g(G)` for a spanning subgraph `H ≤ G` on `k ≥ 2` vertices (`Val3` is `Λ` of
  `W2/Graph.lean`, so this is `Lam_le_dcG`).
* `passSound3 : PassSound3`: the value of the window-3 pass (`W3Cert/Auto.lean`) is at most `2 · Val3` of the graph of
  its input edges.

The pass is handled by a prefix invariant (`PassA.Inv`), as in `W2/PassSound.lean`: after point `i` the state describes
the graph of the input edges among the points `0..i` (equal labels of window points mean connected within the prefix;
every prefix point is connected to a window point; `cnt` is the prefix degree capped at `2`; `u` bounds the number of
points that left the window with degree `< 2`).  The facts about one step of the automaton are finite: `PassA.chk_all`
checks them by `decide +kernel` for every state with a canonical label list of length `1..3`, counts in `{0, 1, 2}` and
`u ≤ 1` (312 states; by the invariant every state of the pass is one of them, `PassA.good_of_inv`) and all 8 inputs.
The proof does not use `W3C.reachable`.
-/
import W3.Interfaces

open SimpleGraph

namespace BHH.W3

open BHH BHH.W2

/-! ## The value bound -/

lemma val3_eq_lam {k : ℕ} (H : SimpleGraph (Fin k)) : Val3 H = Lam H := by
  unfold Val3 Lam nLt2
  congr

/-- The value bound: `0 ≤ Val3 H ≤ g(G)` for every spanning subgraph `H ≤ G`, `k ≥ 2`. -/
theorem lemma1 : Lemma1 := by
  intro k H G hHG hk
  rw [val3_eq_lam]
  exact ⟨Lam_nonneg H, Lam_le_dcG hHG hk⟩

namespace PassA

/-! ## The finite check of one step of the automaton -/

/-- The canonical label lists of length `1, 2, 3`. -/
def allParts : List (List ℕ) := [[0], [0, 0], [0, 1], [0, 0, 0], [0, 0, 1], [0, 1, 0], [0, 1, 1], [0, 1, 2]]

/-- All lists of length `l` with entries in `{0, 1, 2}`. -/
def cntsOfLen : ℕ → List (List ℕ)
  | 0 => [[]]
  | l + 1 => [0, 1, 2].flatMap fun x => (cntsOfLen l).map (x :: ·)

/-- The states checked: canonical labels, counts in `{0, 1, 2}` (as many as labels), `u ∈ {0, 1}` (312 states). -/
def allSt : List W3C.St :=
  allParts.flatMap fun p => (cntsOfLen p.length).flatMap fun c => [⟨p, c, 0⟩, ⟨p, c, 1⟩]

/-- The eight inputs `(N, S, T)`. -/
def allIn : List (List Bool) := (List.range 8).map W3C.inputOf

/-- `0/1` value of a boolean. -/
def bn (b : Bool) : ℕ := if b then 1 else 0

/-- The edge of the new point to the window point `d + 1` positions back, as used by `W3C.St.step` (absent window points
get `false`). -/
def em (n : ℕ) (a : List Bool) (d : ℕ) : Bool := decide (d < n) && a.getD d false

/-- One step of the relation on the positions `0..n` of a step (`0` the new point, `p ≥ 1` the old window point
`p - 1`): equal positions, equal old labels, or an input edge of the new point. -/
def relR (s : W3C.St) (a : List Bool) (p q : ℕ) : Bool :=
  p == q
  || (decide (1 ≤ p) && decide (1 ≤ q) && decide (p ≤ s.part.length) && decide (q ≤ s.part.length)
      && s.part.getD (p - 1) 0 == s.part.getD (q - 1) 0)
  || (p == 0 && decide (1 ≤ q) && decide (q ≤ s.part.length) && em s.part.length a (q - 1))
  || (q == 0 && decide (1 ≤ p) && decide (p ≤ s.part.length) && em s.part.length a (p - 1))

/-- A path of at most three `relR` steps (enough for at most four positions). -/
def path3 (s : W3C.St) (a : List Bool) (p q : ℕ) : Bool :=
  (List.range (s.part.length + 1)).any fun m1 => (List.range (s.part.length + 1)).any fun m2 =>
    relR s a p m1 && relR s a m1 m2 && relR s a m2 q

/-- The facts about one successful step `s.step a = some t` used by the invariant: canonical labels and lengths of
`t`, the counts, equal labels of `t` come from `relR` paths, the leaving point (window of three) is joined by a `relR`
path to a point of the new window and `u` counts it iff its count is `< 2`, and `u ≤ 1`. -/
def chk (s : W3C.St) (a : List Bool) : Bool :=
  match s.step a with
  | none => true
  | some t =>
    allParts.contains t.part && t.part.length == min (s.part.length + 1) 3
    && t.cnt.length == min (s.part.length + 1) 3
    && t.cnt.getD 0 0 == min (bn (em s.part.length a 0) + bn (em s.part.length a 1) + bn (em s.part.length a 2)) 2
    && (List.range (min (s.part.length + 1) 3)).all (fun j => j == 0 ||
          t.cnt.getD j 0 == min (s.cnt.getD (j - 1) 0 + bn (em s.part.length a (j - 1))) 2)
    && (List.range (min (s.part.length + 1) 3)).all (fun j => (List.range (min (s.part.length + 1) 3)).all fun j' =>
          !(t.part.getD j 0 == t.part.getD j' 0) || path3 s a j j')
    && (if s.part.length == 3 then (List.range 3).any (fun j => path3 s a 3 j)
          && t.u == s.u + (if 2 ≤ min (s.cnt.getD 2 0 + bn (em s.part.length a 2)) 2 then 0 else 1)
        else t.u == s.u)
    && decide (t.u ≤ 1)

/-- The finite check, by kernel evaluation. -/
theorem chk_all : (allSt.all fun s => allIn.all fun a => chk s a) = true := by decide +kernel

lemma mem_cntsOfLen : ∀ c : List ℕ, (∀ x ∈ c, x ≤ 2) → c ∈ cntsOfLen c.length
  | [], _ => by simp [cntsOfLen]
  | x :: c, h => by
    have hx : x ≤ 2 := h x (by simp)
    have ih := mem_cntsOfLen c (fun y hy => h y (by simp [hy]))
    simp only [cntsOfLen, List.length_cons, List.mem_flatMap, List.mem_map]
    refine ⟨x, by simp; omega, c, ih, rfl⟩

lemma mem_allSt {s : W3C.St} (hp : s.part ∈ allParts) (hc : s.cnt.length = s.part.length)
    (hc2 : ∀ x ∈ s.cnt, x ≤ 2) (hu : s.u ≤ 1) : s ∈ allSt := by
  obtain ⟨p, c, u⟩ := s
  simp only at hp hc hc2 hu
  simp only [allSt, List.mem_flatMap]
  refine ⟨p, hp, c, hc ▸ mem_cntsOfLen c hc2, ?_⟩
  rcases (by omega : u = 0 ∨ u = 1) with rfl | rfl <;> simp

lemma mem_allIn (x y z : Bool) : [x, y, z] ∈ allIn := by
  cases x <;> cases y <;> cases z <;> decide

lemma chk_of_mem {s : W3C.St} {a : List Bool} (hs : s ∈ allSt) (ha : a ∈ allIn) : chk s a = true := by
  have h := chk_all
  rw [List.all_eq_true] at h
  have h2 := h s hs
  rw [List.all_eq_true] at h2
  exact h2 a ha

/-- The facts of `chk` as propositions. -/
lemma chk_spec {s t : W3C.St} {a : List Bool} (hc : chk s a = true) (h : s.step a = some t) :
    t.part ∈ allParts ∧ t.part.length = min (s.part.length + 1) 3 ∧ t.cnt.length = min (s.part.length + 1) 3 ∧
    t.cnt.getD 0 0 = min (bn (em s.part.length a 0) + bn (em s.part.length a 1) + bn (em s.part.length a 2)) 2 ∧
    (∀ j, 1 ≤ j → j < min (s.part.length + 1) 3 →
      t.cnt.getD j 0 = min (s.cnt.getD (j - 1) 0 + bn (em s.part.length a (j - 1))) 2) ∧
    (∀ j j', j < min (s.part.length + 1) 3 → j' < min (s.part.length + 1) 3 →
      t.part.getD j 0 = t.part.getD j' 0 → path3 s a j j' = true) ∧
    (s.part.length = 3 → (List.range 3).any (fun j => path3 s a 3 j) = true ∧
      t.u = s.u + (if 2 ≤ min (s.cnt.getD 2 0 + bn (em s.part.length a 2)) 2 then 0 else 1)) ∧
    (s.part.length ≠ 3 → t.u = s.u) ∧ t.u ≤ 1 := by
  unfold chk at hc
  rw [h] at hc
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := hc
  refine ⟨by simpa using h1, h2, h3, h4, ?_, ?_, ?_, ?_, h8⟩
  · intro j hj1 hj
    rw [List.all_eq_true] at h5
    have := h5 j (List.mem_range.mpr hj)
    simp only [Bool.or_eq_true, beq_iff_eq] at this
    rcases this with h0 | h0
    · omega
    · exact h0
  · intro j j' hj hj' he
    rw [List.all_eq_true] at h6
    have := h6 j (List.mem_range.mpr hj)
    rw [List.all_eq_true] at this
    have := this j' (List.mem_range.mpr hj')
    simp only [Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne] at this
    rcases this with h0 | h0
    · exact absurd he h0
    · exact h0
  · intro h3'
    simp only [h3', ite_true, Bool.and_eq_true, beq_iff_eq] at h7
    exact ⟨h7.1, by rw [h3']; exact h7.2⟩
  · intro h3'
    simpa [h3'] using h7

/-! ## The prefix graph -/

section Graph

variable (aN aS aT : ℕ → Bool)

instance seqAdj3Dec : DecidableRel (seqAdj3 aN aS aT) := fun a b => by unfold seqAdj3; infer_instance

/-- Adjacency within the prefix `{0, ..., i}`. -/
def pAdj3 (i : ℕ) (x y : ℕ) : Prop := seqAdj3 aN aS aT x y ∧ x ≤ i ∧ y ≤ i

/-- Reachability within the prefix `{0, ..., i}`. -/
def P3 (i : ℕ) : ℕ → ℕ → Prop := Relation.ReflTransGen (pAdj3 aN aS aT i)

/-- The degree of `v` in the graph of the input edges among the points `0, ..., i`. -/
def degP3 (i v : ℕ) : ℕ := ((Finset.range (i + 1)).filter (seqAdj3 aN aS aT v)).card

variable {aN aS aT}

lemma seqAdj3_symm' {a b : ℕ} (h : seqAdj3 aN aS aT a b) : seqAdj3 aN aS aT b a := by
  unfold seqAdj3 at *; tauto

lemma seqAdj3_irrefl' (a : ℕ) : ¬ seqAdj3 aN aS aT a a := by
  unfold seqAdj3; omega

lemma seqAdj3_near {a b : ℕ} (h : seqAdj3 aN aS aT a b) : a ≤ b + 3 ∧ b ≤ a + 3 := by
  unfold seqAdj3 at h; omega

lemma P3_mono {i j a b : ℕ} (hij : i ≤ j) (h : P3 aN aS aT i a b) : P3 aN aS aT j a b := by
  have hle : pAdj3 aN aS aT i ≤ pAdj3 aN aS aT j :=
    fun x y hxy => ⟨hxy.1, le_trans hxy.2.1 hij, le_trans hxy.2.2 hij⟩
  exact Relation.ReflTransGen.mono hle a b h

lemma P3_symm {i a b : ℕ} (h : P3 aN aS aT i a b) : P3 aN aS aT i b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head ⟨seqAdj3_symm' hbc.1, hbc.2.2, hbc.2.1⟩ ih

lemma P3_trans {i a b c : ℕ} (h1 : P3 aN aS aT i a b) (h2 : P3 aN aS aT i b c) : P3 aN aS aT i a c :=
  Relation.ReflTransGen.trans h1 h2

lemma P3_edge {i a b : ℕ} (h : seqAdj3 aN aS aT a b) (ha : a ≤ i) (hb : b ≤ i) : P3 aN aS aT i a b :=
  Relation.ReflTransGen.single ⟨h, ha, hb⟩

lemma degP3_succ (i v : ℕ) :
    degP3 aN aS aT (i + 1) v = degP3 aN aS aT i v + (if seqAdj3 aN aS aT v (i + 1) then 1 else 0) := by
  unfold degP3
  rw [Finset.range_add_one (n := i + 1), Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · simp

lemma degP3_zero (v : ℕ) : degP3 aN aS aT 0 v = if seqAdj3 aN aS aT v 0 then 1 else 0 := by
  unfold degP3
  rw [zero_add, Finset.range_one, Finset.filter_singleton]
  split_ifs <;> simp

lemma degP3_far {i v : ℕ} (h : i + 4 ≤ v) : degP3 aN aS aT i v = 0 := by
  unfold degP3
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro w hw hadj
  rw [Finset.mem_range] at hw
  have := seqAdj3_near hadj
  omega

lemma degP3_low {i v : ℕ} (hv : v + 3 ≤ i) : degP3 aN aS aT (i + 1) v = degP3 aN aS aT i v := by
  rw [degP3_succ]
  have : ¬ seqAdj3 aN aS aT v (i + 1) := fun h => by have := seqAdj3_near h; omega
  simp [this]

lemma adj_d1 (i : ℕ) : seqAdj3 aN aS aT i (i + 1) ↔ aN (i + 1) = true := by
  unfold seqAdj3
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _⟩) <;> omega
  · intro h; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, h⟩)))

lemma adj_d2 {i : ℕ} (hi : 1 ≤ i) : seqAdj3 aN aS aT (i - 1) (i + 1) ↔ aS (i + 1) = true := by
  unfold seqAdj3
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩) <;> omega
  · intro h; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, h⟩))))

lemma adj_d3 {i : ℕ} (hi : 2 ≤ i) : seqAdj3 aN aS aT (i - 2) (i + 1) ↔ aT (i + 1) = true := by
  unfold seqAdj3
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩) <;> omega
  · intro h; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, h⟩))))

/-- The edge of the new point `i + 1` to the point `i - d` is the input `em n a d` of the step. -/
lemma adj_new {i n d : ℕ} (hn : n = min (i + 1) 3) (hd : d < n) :
    seqAdj3 aN aS aT (i - d) (i + 1) ↔ em n [aN (i + 1), aS (i + 1), aT (i + 1)] d = true := by
  rcases (by omega : d = 0 ∨ d = 1 ∨ d = 2) with rfl | rfl | rfl
  · rw [Nat.sub_zero, adj_d1]
    simp [em, show 0 < n by omega]
  · rw [adj_d2 (by omega)]
    simp [em, show 1 < n by omega]
  · rw [adj_d3 (by omega)]
    simp [em, show 2 < n by omega]

lemma ind_new {i n d : ℕ} (hn : n = min (i + 1) 3) (hd : d < n) :
    (if seqAdj3 aN aS aT (i - d) (i + 1) then 1 else 0) = bn (em n [aN (i + 1), aS (i + 1), aT (i + 1)] d) := by
  have := adj_new (aN := aN) (aS := aS) (aT := aT) hn hd
  unfold bn
  by_cases h : seqAdj3 aN aS aT (i - d) (i + 1)
  · rw [ite_eq_left h, ite_eq_left (this.mp h)]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (this.mpr h'))]

lemma em_ge {n d : ℕ} (a : List Bool) (hd : n ≤ d) : em n a d = false := by
  simp [em, show ¬ d < n by omega]

/-- The degree of a window point after the new point `i + 1`. -/
lemma degP3_old {i n d : ℕ} (hn : n = min (i + 1) 3) (hd : d < n) :
    degP3 aN aS aT (i + 1) (i - d) =
      degP3 aN aS aT i (i - d) + bn (em n [aN (i + 1), aS (i + 1), aT (i + 1)] d) := by
  rw [degP3_succ, ind_new hn hd]

lemma ind_comm (a b : ℕ) :
    (if seqAdj3 aN aS aT a b then 1 else 0) = (if seqAdj3 aN aS aT b a then 1 else 0) := by
  by_cases h : seqAdj3 aN aS aT a b
  · rw [ite_eq_left h, ite_eq_left (seqAdj3_symm' h)]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (seqAdj3_symm' h'))]

lemma degP3_three (j : ℕ) : degP3 aN aS aT j (j + 3) = if seqAdj3 aN aS aT (j + 3) j then 1 else 0 := by
  rcases j with _ | j
  · rw [degP3_zero]
  · rw [degP3_succ, degP3_far (by omega), zero_add]

/-- The degree of the new point `i + 1`: its input edges. -/
lemma degP3_new (i n : ℕ) (hn : n = min (i + 1) 3) :
    degP3 aN aS aT (i + 1) (i + 1) = bn (em n [aN (i + 1), aS (i + 1), aT (i + 1)] 0) +
      bn (em n [aN (i + 1), aS (i + 1), aT (i + 1)] 1) + bn (em n [aN (i + 1), aS (i + 1), aT (i + 1)] 2) := by
  rw [degP3_succ, ite_eq_right (seqAdj3_irrefl' _), add_zero]
  rcases i with _ | _ | j
  · -- i = 0, n = 1
    show degP3 aN aS aT 0 1 = bn (em n [aN 1, aS 1, aT 1] 0) + bn (em n [aN 1, aS 1, aT 1] 1) +
      bn (em n [aN 1, aS 1, aT 1] 2)
    have h0 : (if seqAdj3 aN aS aT 0 1 then 1 else 0) = bn (em n [aN 1, aS 1, aT 1] 0) :=
      ind_new hn (show 0 < n by omega)
    rw [degP3_zero, ind_comm, h0, em_ge _ (show n ≤ 1 by omega), em_ge _ (show n ≤ 2 by omega)]
    simp [bn]
  · -- i = 1, n = 2
    show degP3 aN aS aT 1 2 = bn (em n [aN 2, aS 2, aT 2] 0) + bn (em n [aN 2, aS 2, aT 2] 1) +
      bn (em n [aN 2, aS 2, aT 2] 2)
    have h0 : (if seqAdj3 aN aS aT 1 2 then 1 else 0) = bn (em n [aN 2, aS 2, aT 2] 0) :=
      ind_new hn (show 0 < n by omega)
    have h1 : (if seqAdj3 aN aS aT 0 2 then 1 else 0) = bn (em n [aN 2, aS 2, aT 2] 1) :=
      ind_new hn (show 1 < n by omega)
    have e : degP3 aN aS aT 1 2 = degP3 aN aS aT 0 2 + (if seqAdj3 aN aS aT 2 1 then 1 else 0) :=
      degP3_succ 0 2
    rw [e, degP3_zero, ind_comm 2 0, ind_comm 2 1, h0, h1, em_ge _ (show n ≤ 2 by omega)]
    simp [bn, add_comm]
  · -- i = j + 2, n = 3
    show degP3 aN aS aT (j + 2) (j + 3) = bn (em n [aN (j + 3), aS (j + 3), aT (j + 3)] 0) +
      bn (em n [aN (j + 3), aS (j + 3), aT (j + 3)] 1) + bn (em n [aN (j + 3), aS (j + 3), aT (j + 3)] 2)
    have h0 : (if seqAdj3 aN aS aT (j + 2) (j + 3) then 1 else 0) =
        bn (em n [aN (j + 3), aS (j + 3), aT (j + 3)] 0) := ind_new hn (show 0 < n by omega)
    have h1 : (if seqAdj3 aN aS aT (j + 1) (j + 3) then 1 else 0) =
        bn (em n [aN (j + 3), aS (j + 3), aT (j + 3)] 1) := ind_new hn (show 1 < n by omega)
    have h2 : (if seqAdj3 aN aS aT j (j + 3) then 1 else 0) =
        bn (em n [aN (j + 3), aS (j + 3), aT (j + 3)] 2) := ind_new hn (show 2 < n by omega)
    have e1 : degP3 aN aS aT (j + 2) (j + 3) =
        degP3 aN aS aT (j + 1) (j + 3) + (if seqAdj3 aN aS aT (j + 3) (j + 2) then 1 else 0) :=
      degP3_succ (j + 1) (j + 3)
    have e2 : degP3 aN aS aT (j + 1) (j + 3) =
        degP3 aN aS aT j (j + 3) + (if seqAdj3 aN aS aT (j + 3) (j + 1) then 1 else 0) :=
      degP3_succ j (j + 3)
    rw [e1, e2, degP3_three, ind_comm (j + 3) j, ind_comm (j + 3) (j + 1), ind_comm (j + 3) (j + 2), h0, h1, h2]
    omega

/-! ## The invariant of the pass -/

variable (aN aS aT) in
/-- The invariant of the pass after the points `0, ..., i` (soundness direction; window points `i - j`,
`j < min (i + 1) 3`). -/
structure Inv (i : ℕ) (s : W3C.St) : Prop where
  part : s.part ∈ allParts
  plen : s.part.length = min (i + 1) 3
  clen : s.cnt.length = min (i + 1) 3
  cnt : ∀ j < min (i + 1) 3, s.cnt.getD j 0 = min (degP3 aN aS aT i (i - j)) 2
  same : ∀ j j', j < min (i + 1) 3 → j' < min (i + 1) 3 → s.part.getD j 0 = s.part.getD j' 0 →
    P3 aN aS aT i (i - j) (i - j')
  cover : ∀ v ≤ i, ∃ j < min (i + 1) 3, P3 aN aS aT i v (i - j)
  u : ((Finset.range (i - 2)).filter fun v => degP3 aN aS aT i v < 2).card ≤ s.u
  u1 : s.u ≤ 1

lemma inv_zero : Inv aN aS aT 0 W3C.St.init := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, by simp, by decide⟩
  · intro j hj
    have hj0 : j = 0 := by omega
    subst hj0
    rw [Nat.sub_zero, degP3_zero, ite_eq_right (seqAdj3_irrefl' 0)]
    rfl
  · intro j j' hj hj' _
    have h1 : j = 0 := by omega
    have h2 : j' = 0 := by omega
    subst h1 h2
    exact Relation.ReflTransGen.refl
  · intro v hv
    have : v = 0 := by omega
    subst this
    exact ⟨0, by omega, Relation.ReflTransGen.refl⟩

lemma relR_P {i : ℕ} {s : W3C.St} (hs : Inv aN aS aT i s) {p q : ℕ}
    (h : relR s [aN (i + 1), aS (i + 1), aT (i + 1)] p q = true) :
    P3 aN aS aT (i + 1) (i + 1 - p) (i + 1 - q) := by
  have hn := hs.plen
  unfold relR at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  rcases h with ((h | h) | h) | h
  · subst h; exact Relation.ReflTransGen.refl
  · obtain ⟨⟨⟨⟨hp, hq⟩, hpn⟩, hqn⟩, he⟩ := h
    have := hs.same (p - 1) (q - 1) (by omega) (by omega) he
    rw [show i - (p - 1) = i + 1 - p by omega, show i - (q - 1) = i + 1 - q by omega] at this
    exact P3_mono (by omega) this
  · obtain ⟨⟨⟨hp, hq⟩, hqn⟩, he⟩ := h
    subst hp
    have hadj := (adj_new hn (by omega : q - 1 < s.part.length)).mpr he
    rw [show i - (q - 1) = i + 1 - q by omega] at hadj
    exact P3_edge (seqAdj3_symm' hadj) (by omega) (by omega)
  · obtain ⟨⟨⟨hq, hp⟩, hpn⟩, he⟩ := h
    subst hq
    have hadj := (adj_new hn (by omega : p - 1 < s.part.length)).mpr he
    rw [show i - (p - 1) = i + 1 - p by omega] at hadj
    exact P3_edge hadj (by omega) (by omega)

lemma path3_P {i : ℕ} {s : W3C.St} (hs : Inv aN aS aT i s) {p q : ℕ}
    (h : path3 s [aN (i + 1), aS (i + 1), aT (i + 1)] p q = true) :
    P3 aN aS aT (i + 1) (i + 1 - p) (i + 1 - q) := by
  unfold path3 at h
  simp only [List.any_eq_true, Bool.and_eq_true] at h
  obtain ⟨m1, _, m2, _, ⟨h1, h2⟩, h3⟩ := h
  exact P3_trans (P3_trans (relR_P hs h1) (relR_P hs h2)) (relR_P hs h3)

lemma good_of_inv {i : ℕ} {s : W3C.St} (hs : Inv aN aS aT i s) : s ∈ allSt := by
  have hc2 : ∀ x ∈ s.cnt, x ≤ 2 := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
    have := hs.cnt j (by rw [← hs.clen]; exact hj)
    rw [List.getD_eq_getElem _ _ hj] at this
    omega
  exact mem_allSt hs.part (by rw [hs.clen, hs.plen]) hc2 hs.u1

lemma min_succ3 {n i : ℕ} (hn : n = min (i + 1) 3) : min (n + 1) 3 = min (i + 1 + 1) 3 := by omega

lemma min_min2 (x b : ℕ) : min (min x 2 + b) 2 = min (x + b) 2 := by omega

/-- One step of the pass preserves the invariant. -/
lemma inv_step {i : ℕ} {s t : W3C.St} (hs : Inv aN aS aT i s)
    (h : s.step [aN (i + 1), aS (i + 1), aT (i + 1)] = some t) : Inv aN aS aT (i + 1) t := by
  have hn := hs.plen
  have hm := min_succ3 hn
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
    chk_spec (chk_of_mem (good_of_inv hs) (mem_allIn (aN (i + 1)) (aS (i + 1)) (aT (i + 1)))) h
  rw [hm] at h2 h3 h5 h6
  refine ⟨h1, h2, h3, ?_, ?_, ?_, ?_, h9⟩
  · -- cnt
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hj1
    · rw [h4, Nat.sub_zero, degP3_new i _ hn]
    · have hj' : j - 1 < s.part.length := by clear h1 h2 h3 h4 h5 h6 h7 h8 h9; omega
      have e : i + 1 - j = i - (j - 1) := by clear h1 h2 h3 h4 h5 h6 h7 h8 h9; omega
      rw [h5 j hj1 hj, hs.cnt (j - 1) (hn ▸ hj'), e, degP3_old hn hj', min_min2]
  · -- same
    intro j j' hj hj' he
    exact path3_P hs (h6 j j' hj hj' he)
  · -- cover
    have h7a : s.part.length = 3 →
        (List.range 3).any (fun j => path3 s [aN (i + 1), aS (i + 1), aT (i + 1)] 3 j) = true :=
      fun h3' => (h7 h3').1
    clear h1 h2 h3 h4 h5 h6 h7 h8 h9
    intro v hv
    rcases Nat.lt_or_ge i v with hvi | hvi
    · refine ⟨0, by omega, ?_⟩
      rw [show v = i + 1 by omega, Nat.sub_zero]
      exact Relation.ReflTransGen.refl
    · obtain ⟨j, hj, hP⟩ := hs.cover v hvi
      by_cases hj2 : j + 1 < min (i + 1 + 1) 3
      · refine ⟨j + 1, hj2, ?_⟩
        rw [show i + 1 - (j + 1) = i - j by omega]
        exact P3_mono (by omega) hP
      · -- `j = 2`: the leaving point is joined to the new window
        have hn3 : s.part.length = 3 := by omega
        have hj2' : j = 2 := by omega
        subst hj2'
        obtain ⟨j', hj', hpath⟩ := List.any_eq_true.mp (h7a hn3)
        rw [List.mem_range] at hj'
        have hP' := path3_P hs hpath
        rw [show i + 1 - 3 = i - 2 by omega] at hP'
        exact ⟨j', by omega, P3_trans (P3_mono (by omega) hP) hP'⟩
  · -- u
    by_cases hn3 : s.part.length = 3
    · obtain ⟨_, hu⟩ := h7 hn3
      clear h1 h2 h3 h4 h5 h6 h7 h8 h9
      have hsplit : Finset.range (i + 1 - 2) = insert (i - 2) (Finset.range (i - 2)) := by
        rw [show i + 1 - 2 = (i - 2) + 1 by omega, Finset.range_add_one]
      have hlow : ((Finset.range (i - 2)).filter fun v => degP3 aN aS aT (i + 1) v < 2) =
          ((Finset.range (i - 2)).filter fun v => degP3 aN aS aT i v < 2) := by
        apply Finset.filter_congr
        intro v hv
        rw [Finset.mem_range] at hv
        rw [degP3_low (by omega)]
      have hd := degP3_old (aN := aN) (aS := aS) (aT := aT) hn (show 2 < s.part.length by omega)
      have hc := hs.cnt 2 (by omega)
      have hu0 := hs.u
      have hcard := Finset.card_insert_le (i - 2)
        ((Finset.range (i - 2)).filter fun v => degP3 aN aS aT i v < 2)
      rw [hsplit, Finset.filter_insert, hlow, hu]
      split_ifs <;> omega
    · rw [h8 hn3, show i + 1 - 2 = 0 by omega]
      simp

/-- The invariant holds after every successful prefix. -/
lemma inv_all : ∀ i, ∀ s, runPass3 aN aS aT i = some s → Inv aN aS aT i s
  | 0, s, h => by
    simp only [runPass3, Option.some.injEq] at h
    subst h; exact inv_zero
  | i + 1, t, h => by
    have h' : (runPass3 aN aS aT i).bind (fun s => s.step [aN (i + 1), aS (i + 1), aT (i + 1)]) = some t := h
    cases hp : runPass3 aN aS aT i with
    | none => rw [hp] at h'; simp at h'
    | some s =>
      rw [hp] at h'
      simp only [Option.bind_some] at h'
      exact inv_step (inv_all i s hp) h'

end Graph

/-! ## Bridges to `seqGraph3` and the bound -/

section Bridge

variable {aN aS aT : ℕ → Bool}

open Classical in
/-- The degree in `seqGraph3` is `degP3` for the full prefix. -/
lemma degree_seqGraph3 (k v : ℕ) (hv : v < k) :
    (seqGraph3 aN aS aT k).degree ⟨v, hv⟩ = degP3 aN aS aT (k - 1) v := by
  classical
  rw [← card_neighborFinset_eq_degree]
  have e1 : (seqGraph3 aN aS aT k).neighborFinset ⟨v, hv⟩ =
      Finset.univ.filter (fun w : Fin k => seqAdj3 aN aS aT v w.val) := by
    ext w; simp only [mem_neighborFinset, Finset.mem_filter, Finset.mem_univ, true_and]; rfl
  rw [e1]
  unfold degP3
  rw [show k - 1 + 1 = k by omega, ← Finset.card_map ⟨Fin.val, Fin.val_injective⟩]
  congr 1
  ext w
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk,
    Finset.mem_range]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨x.isLt, hx⟩
  · rintro ⟨hw, hx⟩; exact ⟨⟨w, hw⟩, hx, rfl⟩

/-- Reachability in the full prefix gives reachability in `seqGraph3`. -/
lemma reachable_of_P3 {k a b : ℕ} (ha : a < k) (hb : b < k) (h : P3 aN aS aT (k - 1) a b) :
    (seqGraph3 aN aS aT k).Reachable ⟨a, ha⟩ ⟨b, hb⟩ := by
  induction h with
  | refl => exact Reachable.refl _
  | @tail c d _ hcd ih =>
    have hc : c < k := by have := hcd.2.1; omega
    have hd : d < k := by have := hcd.2.2; omega
    exact (ih hc).trans (Adj.reachable (G := seqGraph3 aN aS aT k) (u := ⟨c, hc⟩) (v := ⟨d, hd⟩) hcd.1)

/-- `nLt2` of `seqGraph3` as a count over `range k` with `degP3`. -/
lemma nLt2_seqGraph3 (k : ℕ) :
    nLt2 (seqGraph3 aN aS aT k) = ((Finset.range k).filter fun v => degP3 aN aS aT (k - 1) v < 2).card := by
  classical
  unfold nLt2
  rw [← Finset.card_map ⟨Fin.val, Fin.val_injective⟩]
  congr 1
  ext w
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk,
    Finset.mem_range]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.isLt, ?_⟩
    have := degree_seqGraph3 (aN := aN) (aS := aS) (aT := aT) k x.val x.isLt
    rw [← this]; convert hx
  · rintro ⟨hw, hx⟩
    refine ⟨⟨w, hw⟩, ?_, rfl⟩
    have := degree_seqGraph3 (aN := aN) (aS := aS) (aT := aT) k w hw
    rw [← this] at hx; convert hx

/-- The closing value as a function of the count `n` (as in `W3C.St.close2`). -/
def cv (n : ℕ) : ℕ := if n == 0 then 2 else if n == 1 then 1 else 0

lemma cv_le {n m : ℕ} (h : m ≤ n) : (cv n : ℝ) ≤ max 0 (2 - (m : ℝ)) := by
  unfold cv
  by_cases h0 : n = 0
  · subst h0
    have : m = 0 := by omega
    subst this; norm_num
  · by_cases h1 : n = 1
    · subst h1
      have hm : (m : ℝ) ≤ 1 := by exact_mod_cast h
      simp only [Nat.reduceBEq, Bool.false_eq_true, ite_false, ite_true, Nat.cast_one]
      exact le_max_of_le_right (by linarith)
    · have e0 : (n == 0) = false := by simp [h0]
      have e1 : (n == 1) = false := by simp [h1]
      simp only [e0, e1, Bool.false_eq_true, ite_false, Nat.cast_zero]
      exact le_max_left _ _

lemma card_filter_range_succ (p : ℕ → Prop) [DecidablePred p] (n : ℕ) :
    ((Finset.range (n + 1)).filter p).card = ((Finset.range n).filter p).card + (if p n then 1 else 0) := by
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs
  · rw [Finset.card_insert_of_notMem (by simp)]
  · simp

lemma len_filter_cons (x : ℕ) (l : List ℕ) :
    ((x :: l).filter (· < 2)).length = (if x < 2 then 1 else 0) + (l.filter (· < 2)).length := by
  rw [List.filter_cons]
  by_cases h : x < 2
  · simp [h]; omega
  · simp [h]

/-- At the last point `i`, the points of degree `< 2` are counted by `u` and the window counts. -/
lemma count_le {i : ℕ} (hi : 1 ≤ i) {t : W3C.St} (ht : Inv aN aS aT i t) :
    ((Finset.range (i + 1)).filter fun v => degP3 aN aS aT i v < 2).card ≤
      t.u + (t.cnt.filter (· < 2)).length := by
  have hu := ht.u
  rcases Nat.lt_or_ge i 2 with hi2 | hi2
  · -- `i = 1`: window `{1, 0}`
    obtain rfl : i = 1 := by omega
    obtain ⟨c0, c1, hc⟩ := List.length_eq_two.mp (show t.cnt.length = 2 from ht.clen)
    have e0 := ht.cnt 0 (by decide)
    have e1 := ht.cnt 1 (by decide)
    rw [hc] at e0 e1
    simp only [List.getD_cons_zero, List.getD_cons_succ] at e0 e1
    rw [hc, len_filter_cons, len_filter_cons, List.filter_nil, List.length_nil,
      card_filter_range_succ, Finset.range_one, Finset.filter_singleton]
    split_ifs <;> simp_all
  · -- `i = j + 2`: window `{j + 2, j + 1, j}`
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 + 1 := ⟨i - 2, by omega⟩
    obtain ⟨c0, c1, c2, hc⟩ := List.length_eq_three.mp (show t.cnt.length = 3 by rw [ht.clen]; omega)
    have e0 := ht.cnt 0 (by omega)
    have e1 := ht.cnt 1 (by omega)
    have e2 := ht.cnt 2 (by omega)
    rw [hc] at e0 e1 e2
    simp only [List.getD_cons_zero, List.getD_cons_succ] at e0 e1 e2
    rw [show j + 1 + 1 - 0 = j + 1 + 1 by omega] at e0
    rw [show j + 1 + 1 - 1 = j + 1 by omega] at e1
    rw [show j + 1 + 1 - 2 = j by omega] at e2
    rw [show j + 1 + 1 - 2 = j by omega] at hu
    rw [hc, len_filter_cons, len_filter_cons, len_filter_cons, List.filter_nil, List.length_nil,
      card_filter_range_succ, card_filter_range_succ, card_filter_range_succ]
    have e0' : c0 = min (degP3 aN aS aT (j + 1 + 1) (j + 2)) 2 := e0
    clear e0
    split_ifs <;> omega

/-- The closing value of a state satisfying the invariant at the last point `k - 1`, when all window labels are `0`,
is at most `2 Λ`. -/
lemma close_le {k : ℕ} (hk : 2 ≤ k) {t : W3C.St} (ht : Inv aN aS aT (k - 1) t)
    (hall : t.part.all (· == 0) = true) :
    (cv (t.u + (t.cnt.filter (· < 2)).length) : ℝ) ≤ 2 * Lam (seqGraph3 aN aS aT k) := by
  classical
  have hzero : ∀ j, t.part.getD j 0 = 0 := by
    intro j
    rw [List.all_eq_true] at hall
    by_cases hjl : j < t.part.length
    · rw [List.getD_eq_getElem _ _ hjl]
      simpa using hall _ (List.getElem_mem hjl)
    · rw [List.getD_eq_default _ _ (by omega)]
  have hreach : ∀ v, v < k → P3 aN aS aT (k - 1) v (k - 1) := by
    intro v hv
    obtain ⟨j, hj, hP⟩ := ht.cover v (by omega)
    have := ht.same j 0 hj (by omega) (by rw [hzero j, hzero 0])
    rw [Nat.sub_zero] at this
    exact P3_trans hP this
  have hconn : (seqGraph3 aN aS aT k).Connected := by
    have hne : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
    refine ⟨fun u v => ?_⟩
    have hu := reachable_of_P3 u.isLt (by omega : k - 1 < k) (hreach u.val u.isLt)
    have hv := reachable_of_P3 v.isLt (by omega : k - 1 < k) (hreach v.val v.isLt)
    exact hu.trans hv.symm
  have hn : nLt2 (seqGraph3 aN aS aT k) ≤ t.u + (t.cnt.filter (· < 2)).length := by
    rw [nLt2_seqGraph3]
    have := count_le (show 1 ≤ k - 1 by omega) ht
    rwa [show k - 1 + 1 = k by omega] at this
  have hc := cv_le hn
  unfold Lam
  simp only [hconn, ite_true]
  have e : 2 * max 0 (1 - (nLt2 (seqGraph3 aN aS aT k) : ℝ) / 2) =
      max 0 (2 - (nLt2 (seqGraph3 aN aS aT k) : ℝ)) := by
    rw [mul_max_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)]; ring_nf
  rw [e]; exact hc

end Bridge

/-- The pass value is at most `2 · Val3` of the graph of its input edges (`k ≥ 2` points). -/
theorem passVal3_le (aN aS aT : ℕ → Bool) {k : ℕ} (hk : 2 ≤ k) :
    (passVal3 aN aS aT k : ℝ) ≤ 2 * Val3 (seqGraph3 aN aS aT k) := by
  classical
  rw [val3_eq_lam]
  have hL := Lam_nonneg (seqGraph3 aN aS aT k)
  unfold passVal3
  cases h : runPass3 aN aS aT (k - 2) with
  | none => simp only [Nat.cast_zero]; linarith
  | some s =>
    simp only
    unfold W3C.St.close2
    cases ht : s.step [aN (k - 1), aS (k - 1), aT (k - 1)] with
    | none => simp only [Nat.cast_zero]; linarith
    | some t =>
      simp only
      have hrun : runPass3 aN aS aT (k - 1) = some t := by
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
        rw [show j + 2 - 2 = j by omega] at h
        rw [show j + 2 - 1 = j + 1 by omega] at ht ⊢
        simp only [runPass3, h, Option.bind_some]
        exact ht
      have hinv := inv_all (k - 1) t hrun
      by_cases hall : t.part.all (· == 0) = true
      · rw [ite_eq_left hall]
        exact close_le hk hinv hall
      · rw [ite_eq_right hall]
        simp only [Nat.cast_zero]; linarith

end PassA

/-- `PassSound3`: twice `Val3` of the graph of the input edges bounds the value of the window-3 pass. -/
theorem passSound3 : PassSound3 := fun aN aS aT _ hk => PassA.passVal3_le aN aS aT hk

end BHH.W3
