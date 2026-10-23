/-
Soundness of the local g-table check `localOK` (`BHH/GraphK5/Local.lean`): if every edge state passes it, the table
is sound (`gtabSound_of_local`).  Induction on the state: a state with digit 2 at `p` inherits the bound of the child
that agrees with the completion at `p`; for the other states `localOK` compares with every completion.
-/
import BHH.Graph
import BHH.GraphK5.Local

namespace BHH.E

open BHH.Cert

lemma firstTwo_some {idx : ℕ} : ∀ {n p : ℕ}, firstTwo idx n = some p → p < n ∧ idx / 3 ^ p % 3 = 2
  | 0, p, h => by simp [firstTwo] at h
  | n + 1, p, h => by
    rw [firstTwo] at h
    rcases hn : firstTwo idx n with _ | q
    · rw [hn] at h
      simp only at h
      split_ifs at h with h2
      cases h
      exact ⟨by omega, by simpa using h2⟩
    · rw [hn] at h
      simp only [Option.some.injEq] at h
      subst h
      have := firstTwo_some hn
      exact ⟨by omega, this.2⟩

/-- the base-3 digits of `idx - c 3^p`, where `idx` has digit `2` at `p` and `c ≤ 2` -/
lemma digit_sub {idx p c : ℕ} (h2 : idx / 3 ^ p % 3 = 2) (hc : c ≤ 2) (q : ℕ) :
    (idx - c * 3 ^ p) / 3 ^ q % 3 = if q = p then 2 - c else idx / 3 ^ q % 3 := by
  have hP : 0 < 3 ^ p := by positivity
  obtain ⟨m, r, hr, rfl⟩ : ∃ m r, r < 3 ^ p ∧ idx = 3 ^ p * m + r :=
    ⟨idx / 3 ^ p, idx % 3 ^ p, Nat.mod_lt _ hP, (Nat.div_add_mod idx _).symm⟩
  have hdiv : ∀ t, (3 ^ p * t + r) / 3 ^ p = t := fun t => by
    rw [Nat.mul_add_div hP, Nat.div_eq_of_lt hr, add_zero]
  rw [hdiv] at h2
  have hm : c ≤ m := by omega
  have hsub : 3 ^ p * m + r - c * 3 ^ p = 3 ^ p * (m - c) + r := by
    have h1 : 3 ^ p * (m - c) + 3 ^ p * c = 3 ^ p * m := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hm]
    rw [mul_comm c]
    omega
  rw [hsub]
  rcases lt_trichotomy q p with hq | rfl | hq
  · rw [ite_eq_right hq.ne]
    obtain ⟨j, rfl⟩ : ∃ j, p = q + (j + 1) := ⟨p - q - 1, by omega⟩
    have e1 : ∀ t, (3 ^ (q + (j + 1)) * t + r) / 3 ^ q % 3 = r / 3 ^ q % 3 := fun t => by
      rw [show 3 ^ (q + (j + 1)) * t + r = r + 3 ^ q * (3 * (3 ^ j * t)) by ring,
        Nat.add_mul_div_left _ _ (by positivity), Nat.add_mul_mod_self_left]
    rw [e1, e1]
  · rw [ite_eq_left rfl, hdiv]
    omega
  · rw [ite_eq_right hq.ne']
    obtain ⟨j, rfl⟩ : ∃ j, q = p + (j + 1) := ⟨q - p - 1, by omega⟩
    have e2 : ∀ t, (3 ^ p * t + r) / 3 ^ (p + (j + 1)) = t / 3 / 3 ^ j := fun t => by
      rw [pow_add, ← Nat.div_div_eq_div_mul, hdiv, pow_succ', ← Nat.div_div_eq_div_mul]
    rw [e2, e2, show (m - c) / 3 = m / 3 by omega]

/-- a completion of `idx` that agrees with the child `idx - c 3^p` at `p` completes that child -/
lemma completes_child {k idx e p c : ℕ} (h2 : idx / 3 ^ p % 3 = 2) (hc : Completes k idx e)
    (hc12 : c = 1 ∨ c = 2) (hb1 : c = 1 → e.testBit p = true) (hb2 : c = 2 → e.testBit p = false) :
    Completes k (idx - c * 3 ^ p) e := by
  refine ⟨hc.1, fun q hq => ?_⟩
  rw [digit_sub h2 (by omega) q]
  split_ifs with hqp
  · subst hqp
    rcases hc12 with rfl | rfl
    · exact ⟨fun _ => hb1 rfl, fun h => by omega⟩
    · exact ⟨fun h => by omega, fun _ => by simp [hb2 rfl]⟩
  · exact hc.2 q hq

theorem le_g2lb_of_local {k : ℕ} (gmin : ℕ → ℤ)
    (h : ∀ idx < 3 ^ (pairList k).length, localOK k gmin idx = true) :
    ∀ idx, idx < 3 ^ (pairList k).length → ∀ e, Completes k idx e → gmin idx ≤ g2lb k e := by
  intro idx
  induction idx using Nat.strong_induction_on with
  | _ idx ih =>
  intro hidx e hc
  have hl := h idx hidx
  unfold localOK at hl
  rcases hft : firstTwo idx (pairList k).length with _ | p
  · rw [hft] at hl
    simp only [allBelow_iff, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hl
    rcases hl e hc.1 with h1 | h1
    · have hd : digitsOK idx e (pairList k).length = true := by
        rw [digitsOK_iff]
        intro p hp
        exact ⟨fun h1 => (hc.2 p hp).1 h1, fun h0 => by simpa using (hc.2 p hp).2 h0⟩
      rw [hd] at h1
      exact absurd h1 (by simp)
    · exact h1
  · rw [hft] at hl
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hl
    obtain ⟨hp, h2⟩ := firstTwo_some hft
    have hP : 0 < 3 ^ p := by positivity
    have hge : 2 * 3 ^ p ≤ idx := by
      have h3 : 2 ≤ idx / 3 ^ p := h2 ▸ Nat.mod_le _ _
      calc 2 * 3 ^ p ≤ idx / 3 ^ p * 3 ^ p := Nat.mul_le_mul_right _ h3
        _ ≤ idx := Nat.div_mul_le_self idx _
    cases hb : e.testBit p
    · have hcc := completes_child (c := 2) h2 hc (Or.inr rfl) (fun h => by omega) (fun _ => hb)
      exact le_trans hl.1 (ih _ (by omega) (by omega) e hcc)
    · have hcc := completes_child (c := 1) h2 hc (Or.inl rfl) (fun _ => hb) (fun h => by omega)
      rw [one_mul] at hcc
      exact le_trans hl.2 (ih _ (by omega) (by omega) e hcc)

/-- the local check gives a sound table -/
theorem gtabSound_of_local {k : ℕ} (hk : 2 ≤ k) (gt : GTab)
    (h : ∀ idx < 3 ^ (pairList k).length, localOK k gt.gmin idx = true) : GTabSound k gt := by
  intro idx e hidx hc
  calc (gt.gmin idx : ℝ) ≤ g2lb k e := by exact_mod_cast le_g2lb_of_local gt.gmin h idx hidx e hc
    _ ≤ 2 * dcG (graphOf k e) := g2lb_sound hk e

lemma localRange_iff (k : ℕ) (gmin : ℕ → ℤ) (lo : ℕ) :
    ∀ n, localRange k gmin lo n = true ↔ ∀ i < n, localOK k gmin (lo + i) = true
  | 0 => by simp [localRange]
  | n + 1 => by
    rw [localRange]
    split_ifs with h
    · rw [localRange_iff k gmin lo n]
      constructor
      · intro H i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · exact H i hi
        · exact h
      · intro H i hi; exact H i (by omega)
    · simp only [false_iff, not_forall]
      exact ⟨n, by omega, h⟩

lemma localRange_add {k : ℕ} {gmin : ℕ → ℤ} {a n m : ℕ} (h1 : localRange k gmin a n = true)
    (h2 : localRange k gmin (a + n) m = true) : localRange k gmin a (n + m) = true := by
  rw [localRange_iff] at h1 h2 ⊢
  intro i hi
  by_cases hin : i < n
  · exact h1 i hin
  · have := h2 (i - n) (by omega)
    rwa [show a + n + (i - n) = a + i by omega] at this

/-- `localRange_add` with the boundaries as separate equations (keeps elaboration away from the ranges) -/
lemma localRange_add' {k : ℕ} {gmin : ℕ → ℤ} {a n b m c : ℕ} (h1 : localRange k gmin a n = true)
    (h2 : localRange k gmin b m = true) (hb : a + n = b) (hc : n + m = c) : localRange k gmin a c = true := by
  subst hb hc
  exact localRange_add h1 h2

end BHH.E
