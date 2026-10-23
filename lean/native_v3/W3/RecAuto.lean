/-
Window-3 recursion: the automaton tables of `W3C.runT3` (`W3C.trs`, `W3C.cls`, `W3C.NS`) against the
automaton `W3C.St.step` / `W3C.St.close2`.  The reachable states are given explicitly (`reachLit`, one kernel
evaluation of `W3C.reachable`); closure of the reachable states under `step` is checked by kernel evaluation on the
explicit array.
-/
import W3Cert.Rec3
import W2.RunData

namespace BHH.W3.Rec

open W3C

/-- The reachable states of the window-3 automaton, explicitly (breadth-first order of `W3C.reachable`). -/
def reachLit : Array St := #[⟨[0], [0], 0⟩, ⟨[0, 1], [0, 0], 0⟩, ⟨[0, 0], [1, 1], 0⟩, ⟨[0, 1, 2], [0, 0, 0], 0⟩, ⟨[0, 1, 0], [1, 0, 1], 0⟩, ⟨[0, 0, 1], [1, 1, 0], 0⟩, ⟨[0, 0, 0], [2, 1, 1], 0⟩, ⟨[0, 1, 1], [0, 1, 1], 0⟩, ⟨[0, 0, 0], [1, 1, 2], 0⟩, ⟨[0, 0, 0], [1, 2, 1], 0⟩, ⟨[0, 0, 0], [2, 2, 2], 0⟩, ⟨[0, 1, 2], [1, 0, 0], 1⟩, ⟨[0, 1, 0], [2, 0, 1], 1⟩, ⟨[0, 0, 1], [2, 1, 0], 1⟩, ⟨[0, 0, 0], [2, 1, 1], 1⟩, ⟨[0, 1, 2], [0, 1, 0], 1⟩, ⟨[0, 1, 0], [1, 1, 1], 1⟩, ⟨[0, 0, 1], [1, 2, 0], 1⟩, ⟨[0, 0, 1], [2, 2, 0], 0⟩, ⟨[0, 0, 0], [2, 2, 1], 1⟩, ⟨[0, 0, 0], [2, 2, 1], 0⟩, ⟨[0, 1, 1], [1, 1, 1], 1⟩, ⟨[0, 0, 0], [2, 1, 2], 1⟩, ⟨[0, 0, 0], [2, 2, 2], 1⟩, ⟨[0, 1, 1], [0, 2, 1], 1⟩, ⟨[0, 0, 0], [1, 2, 2], 1⟩, ⟨[0, 0, 0], [1, 2, 1], 1⟩, ⟨[0, 1, 2], [0, 0, 1], 1⟩, ⟨[0, 1, 0], [1, 0, 2], 1⟩, ⟨[0, 1, 0], [2, 0, 2], 0⟩, ⟨[0, 0, 1], [1, 1, 1], 1⟩, ⟨[0, 0, 0], [2, 1, 2], 0⟩, ⟨[0, 0, 0], [1, 1, 1], 0⟩, ⟨[0, 1, 1], [0, 1, 2], 1⟩, ⟨[0, 0, 0], [1, 1, 2], 1⟩, ⟨[0, 1, 1], [0, 2, 2], 0⟩, ⟨[0, 0, 0], [1, 2, 2], 0⟩, ⟨[0, 0, 1], [2, 2, 0], 1⟩, ⟨[0, 0, 1], [2, 2, 1], 1⟩, ⟨[0, 1, 1], [1, 2, 2], 1⟩, ⟨[0, 1, 1], [0, 2, 2], 1⟩, ⟨[0, 1, 0], [2, 1, 2], 1⟩, ⟨[0, 1, 0], [2, 0, 2], 1⟩, ⟨[0, 0, 1], [1, 1, 0], 1⟩, ⟨[0, 1, 2], [0, 2, 0], 0⟩, ⟨[0, 0, 1], [1, 2, 0], 0⟩, ⟨[0, 1, 0], [1, 2, 1], 0⟩, ⟨[0, 1, 1], [0, 2, 1], 0⟩, ⟨[0, 1, 1], [0, 1, 1], 1⟩, ⟨[0, 1, 0], [1, 0, 1], 1⟩, ⟨[0, 0, 0], [1, 1, 1], 1⟩, ⟨[0, 1, 2], [0, 0, 2], 0⟩, ⟨[0, 1, 0], [1, 0, 2], 0⟩, ⟨[0, 0, 1], [1, 1, 2], 0⟩, ⟨[0, 1, 1], [0, 1, 2], 0⟩, ⟨[0, 1, 2], [0, 1, 2], 1⟩, ⟨[0, 1, 0], [1, 1, 2], 1⟩, ⟨[0, 0, 1], [1, 2, 2], 1⟩, ⟨[0, 1, 2], [0, 0, 2], 1⟩, ⟨[0, 0, 1], [1, 1, 2], 1⟩, ⟨[0, 1, 2], [0, 2, 1], 1⟩, ⟨[0, 0, 1], [1, 2, 1], 1⟩, ⟨[0, 1, 0], [1, 2, 2], 1⟩, ⟨[0, 1, 2], [0, 2, 0], 1⟩, ⟨[0, 1, 0], [1, 2, 1], 1⟩, ⟨[0, 1, 2], [1, 0, 2], 1⟩, ⟨[0, 0, 1], [2, 1, 2], 1⟩, ⟨[0, 1, 1], [1, 1, 2], 1⟩, ⟨[0, 0, 1], [2, 2, 2], 0⟩, ⟨[0, 1, 2], [1, 0, 0], 0⟩, ⟨[0, 1, 0], [2, 0, 1], 0⟩, ⟨[0, 0, 1], [2, 1, 0], 0⟩, ⟨[0, 1, 2], [0, 1, 0], 0⟩, ⟨[0, 1, 0], [1, 1, 1], 0⟩, ⟨[0, 1, 1], [1, 1, 1], 0⟩, ⟨[0, 1, 2], [0, 0, 1], 0⟩, ⟨[0, 0, 1], [1, 1, 1], 0⟩, ⟨[0, 1, 2], [1, 0, 1], 1⟩, ⟨[0, 0, 1], [2, 1, 1], 1⟩, ⟨[0, 1, 2], [0, 1, 1], 1⟩, ⟨[0, 0, 1], [2, 2, 2], 1⟩, ⟨[0, 1, 2], [1, 1, 0], 1⟩, ⟨[0, 1, 0], [2, 1, 1], 1⟩, ⟨[0, 1, 1], [1, 2, 1], 1⟩, ⟨[0, 1, 1], [1, 2, 2], 0⟩, ⟨[0, 0, 1], [2, 2, 1], 0⟩, ⟨[0, 1, 0], [2, 1, 2], 0⟩, ⟨[0, 1, 2], [0, 1, 2], 0⟩, ⟨[0, 1, 0], [1, 1, 2], 0⟩, ⟨[0, 0, 1], [1, 2, 2], 0⟩, ⟨[0, 1, 2], [0, 2, 1], 0⟩, ⟨[0, 0, 1], [1, 2, 1], 0⟩, ⟨[0, 1, 0], [1, 2, 2], 0⟩, ⟨[0, 1, 2], [1, 0, 1], 0⟩, ⟨[0, 0, 1], [2, 1, 1], 0⟩, ⟨[0, 1, 2], [0, 1, 1], 0⟩, ⟨[0, 1, 1], [1, 1, 2], 0⟩, ⟨[0, 1, 2], [1, 0, 2], 0⟩, ⟨[0, 0, 1], [2, 1, 2], 0⟩, ⟨[0, 1, 2], [1, 1, 0], 0⟩, ⟨[0, 1, 0], [2, 1, 1], 0⟩, ⟨[0, 1, 1], [1, 2, 1], 0⟩, ⟨[0, 1, 2], [1, 1, 1], 1⟩]

theorem reachable_eq : reachable = reachLit := by decide +kernel

lemma reachLit_size : reachLit.size = 103 := rfl

lemma NS_eq : NS = 103 := by
  show reachable.size = 103
  rw [reachable_eq]; rfl

/-- The index of a state among the reachable ones (`103` if absent). -/
def stIdx (t : St) : ℕ := (reachLit.findIdx? (· == t)).getD 103

lemma stIndex_eq (t : St) : stIndex t = stIdx t := by
  unfold stIndex stIdx
  rw [reachable_eq, reachLit_size]

/-- The index of an optional state (`NS`, "dead", for `none`). -/
def sIdx3 : Option St → ℕ
  | none => NS
  | some t => stIdx t

/-- The reachable state with index `D`. -/
def stOf3 (D : ℕ) : St := reachLit[D]!

/-- input index `4 N + 2 S + T` of three Boolean inputs -/
def inp (a b c : Bool) : ℕ := 4 * W2C.b2n a + 2 * W2C.b2n b + W2C.b2n c

lemma inp_lt (a b c : Bool) : inp a b c < 8 := by
  cases a <;> cases b <;> cases c <;> decide

lemma inputOf_inp (a b c : Bool) : inputOf (inp a b c) = [a, b, c] := by
  cases a <;> cases b <;> cases c <;> decide

lemma transTab_size : transTab.size = NS * 8 := by
  unfold transTab; simp [NS]

lemma trs_size : trs.size = NS * 8 := by
  unfold trs; rw [Array.size_map, transTab_size]

lemma cls_size : cls.size = NS * 8 := by
  unfold cls close2Tab; simp [NS]

lemma div8 {D i : ℕ} (hi : i < 8) : (D * 8 + i) / 8 = D := by omega
lemma mod8 {D i : ℕ} (hi : i < 8) : (D * 8 + i) % 8 = i := by omega

/-- The transition table entry of a reachable state. -/
lemma trs_eq {D i : ℕ} (hD : D < NS) (hi : i < 8) : trs[D * 8 + i]! = sIdx3 ((stOf3 D).step (inputOf i)) := by
  have hk : D * 8 + i < NS * 8 := by omega
  have hk' : D * 8 + i < reachable.size * 8 := hk
  unfold trs
  rw [BHH.W2.getElem!_map _ _ (by rw [transTab_size]; exact hk)]
  unfold transTab
  rw [BHH.W2.getElem!_map _ _ (by simpa using hk'), BHH.W2.range_getElem! hk', div8 hi, mod8 hi]
  unfold stOf3
  rw [← reachable_eq]
  cases h : (reachable[D]!).step (inputOf i) with
  | none => rfl
  | some t => simp [sIdx3, stIndex_eq]

/-- The closing table entry of a reachable state. -/
lemma cls_eq {D i : ℕ} (hD : D < NS) (hi : i < 8) : cls[D * 8 + i]! = (stOf3 D).close2 (inputOf i) := by
  have hk : D * 8 + i < NS * 8 := by omega
  have hk' : D * 8 + i < reachable.size * 8 := hk
  unfold cls close2Tab
  rw [BHH.W2.getElem!_map _ _ (by simpa using hk'), BHH.W2.range_getElem! hk', div8 hi, mod8 hi]
  unfold stOf3
  rw [← reachable_eq]

/-- `t` is a reachable state with its index (as a `Bool`). -/
def goodB3 (t : St) : Bool := decide (stIdx t < 103 ∧ stOf3 (stIdx t) = t)

lemma closed_dec : ∀ D : Fin 103, ∀ i : Fin 8, ((stOf3 D.val).step (inputOf i.val)).all goodB3 = true := by
  decide +kernel

lemma init_dec : goodB3 St.init = true ∧ stIdx St.init = 0 := by decide +kernel

/-- `t` is a reachable state with its index. -/
def Good3 (t : St) : Prop := stIdx t < NS ∧ stOf3 (stIdx t) = t

lemma good_step3 {D i : ℕ} (hD : D < NS) (hi : i < 8) {t : St} (h : (stOf3 D).step (inputOf i) = some t) :
    Good3 t := by
  rw [NS_eq] at hD
  have hc := closed_dec ⟨D, hD⟩ ⟨i, hi⟩
  simp only [h, Option.all_some, goodB3, decide_eq_true_eq] at hc
  exact ⟨by rw [NS_eq]; exact hc.1, hc.2⟩

lemma good_init3 : Good3 St.init := by
  have h := init_dec.1
  simp only [goodB3, decide_eq_true_eq] at h
  exact ⟨by rw [NS_eq]; exact h.1, h.2⟩

lemma stIdx_init : stIdx St.init = 0 := init_dec.2

/-- The transition of a good state through the table. -/
lemma trs_good {s : St} (hs : Good3 s) (a b c : Bool) :
    trs[stIdx s * 8 + inp a b c]! = sIdx3 (s.step [a, b, c]) := by
  rw [trs_eq hs.1 (inp_lt a b c), hs.2, inputOf_inp]

/-- The closing value of a good state through the table. -/
lemma cls_good {s : St} (hs : Good3 s) (a b c : Bool) :
    cls[stIdx s * 8 + inp a b c]! = s.close2 [a, b, c] := by
  rw [cls_eq hs.1 (inp_lt a b c), hs.2, inputOf_inp]

/-- A good successor of a good state. -/
lemma good_step3' {s : St} (hs : Good3 s) (a : List Bool) (ha : ∃ x y z, a = [x, y, z]) {t : St}
    (h : s.step a = some t) : Good3 t := by
  obtain ⟨x, y, z, rfl⟩ := ha
  apply good_step3 hs.1 (inp_lt x y z)
  rw [hs.2, inputOf_inp]; exact h

lemma sIdx3_none : sIdx3 none = NS := rfl

lemma sIdx3_some_lt {t : St} (ht : Good3 t) : sIdx3 (some t) < NS := ht.1

end BHH.W3.Rec
