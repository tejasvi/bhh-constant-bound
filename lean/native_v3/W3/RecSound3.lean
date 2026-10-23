/-
Window-3 recursion: `theorem recSound3 : RecSound3`.  The outputs of `W3C.runT3 (W3C.mkRun3 g dtl par) lower j dtl
kmax par` bound `Φ^d_k(t_j) = Psid3 (gR g) _ _ (discOf3 g dtl) (k - 1) (j 2^-dtl)` from below (`lower = true`) and
from above (`lower = false`), for `3 ≤ k ≤ kmax`:
* `Psid3` is the exact recursion over flat cells unrolled (`W3/RecUnroll.lean`, `W3/RecExact.lean`; automaton tables
  `W3/RecAuto.lean`), mirror symmetric for the tables of `discOf3` (`W3/RecMirror.lean`, `W3/RecTab3.lean`);
* the computed rows and closing sums bound the exact recursion level by level (`W3/RecStep3.lean`,
  `W3/RecLevel3.lean`, `W3/RecIter3.lean`; loops `W3/RecLoop3.lean`, `W3/RecLoop3b.lean`, `W3/RecPush.lean`;
  directed arithmetic `W3/RecArith3.lean`), for the data of the run (`W3/RecRun3.lean`).
-/
import W3.RecRun3

open Real

namespace BHH.W3.Rec

open W3C W2C BHH BHH.W2 BHH.Cert

attribute [local irreducible] W3C.NS W3C.reachable W3C.trs W3C.cls

/-- The normalised rows bound the exact recursion at the shifted scale. -/
lemma rowsBd_norm {lower : Bool} {g : GridR} {D : DiscData3} {t : ℝ} {rows : Array Row} {E : ℤ} {n : ℕ}
    (h : RowsBd lower g D t rows E n) (hsz : rows.size = g.NR * g.NT) :
    RowsBd lower g D t (normRows lower rows).1 (E - (normRows lower rows).2) n := by
  intro cb hcb
  rw [normRows_get lower rows (by rw [hsz]; exact hcb)]
  obtain ⟨hwf, hinv, hbd⟩ := h cb hcb
  exact ⟨rowWF_normRow _ _ _ _ hwf, rowInv_normRow _ _ _ hinv,
    fun ca hca s hs => Bd.trans (normRow_bd lower _ _ E ca s) (hbd ca hca s hs)⟩

/-- The normalised rows have mantissas at most `2^62`. -/
lemma mantBd_norm (lower : Bool) (rows : Array Row) {NC : ℕ} (hsz : rows.size = NC) :
    MantBd (normRows lower rows).1 NC := by
  intro cb hcb q
  exact normRows_mant lower rows (by rw [hsz]; exact hcb) q

lemma getD_eq_getElem! (l : List (ℕ × ℤ)) (i : ℕ) : l.getD i (0, 0) = l[i]! := by
  rw [List.getD_eq_getElem?_getD, List.getElem!_eq_getElem?_getD]; rfl

/-- The outputs of a run bound `Psid3` in the direction `lower`. -/
theorem runT3_bd (g : W2C.Grid) (dtl kmax j : ℕ) (par lower : Bool) (hNR : 0 < (gR g).NR) (hNT : 0 < (gR g).NT)
    (hNT2 : 2 ≤ g.NT) (hev : g.NT % 2 = 0) (hdtl : dtl ≤ 48)
    (hub : ∀ ir : ℕ, 0 ≤ W3C.upq ((W3C.mkTabData g).rings[ir]!).euHi dtl) {k : ℕ} (hk3 : 3 ≤ k) (hkk : k ≤ kmax) :
    Bd lower (outVal (W3C.runT3 (W3C.mkRun3 g dtl par) lower j dtl kmax par) k)
      (Psid3 (gR g) hNR hNT (discOf3 g dtl) (k - 1) ((j : ℝ) / 2 ^ dtl)) := by
  have hNT0 : 0 < g.NT := by omega
  have hrd := rdOK_run g dtl j par lower hNT0 hdtl
  have hl2 := l2OK_run g dtl j par lower hNT0 hub
  have hm := mirOK_discOf3 g dtl hNT0
  have hrows := level2_rows hrd hl2 par
  have hsz : (level2 lower (rd3Of (mkRun3 g dtl par) lower j par) (f1Of (mkRun3 g dtl par) lower j dtl)
      (k2Of (mkRun3 g dtl par) lower j dtl par) par).1.size = (gR g).NR * (gR g).NT := by
    rw [level2_size]; rfl
  have hrowsN := rowsBd_norm hrows hsz
  have hmantN := mantBd_norm lower _ hsz
  unfold outVal
  rw [runT3_eq, getD_eq_getElem!]
  set L := recIter3 lower (rd3Of (mkRun3 g dtl par) lower j par) par (kmax - 3)
    (normRows lower (level2 lower (rd3Of (mkRun3 g dtl par) lower j par) (f1Of (mkRun3 g dtl par) lower j dtl)
      (k2Of (mkRun3 g dtl par) lower j dtl par) par).1).1
    (((2 * PR + 62 : ℕ) : ℤ) - ((normRows lower (level2 lower (rd3Of (mkRun3 g dtl par) lower j par)
      (f1Of (mkRun3 g dtl par) lower j dtl) (k2Of (mkRun3 g dtl par) lower j dtl par) par).1).2 : ℤ))
    [((level2 lower (rd3Of (mkRun3 g dtl par) lower j par) (f1Of (mkRun3 g dtl par) lower j dtl)
      (k2Of (mkRun3 g dtl par) lower j dtl par) par).2, ((2 * PR + 62 + 1 : ℕ) : ℤ))] with hL
  rcases Nat.lt_or_ge k 4 with h4 | h4
  · -- `k = 3`: the closing sum of level 2
    have hk : k = 3 := by omega
    subst hk
    have hpre := recIter3_prefix lower (rd3Of (mkRun3 g dtl par) lower j par) par (kmax - 3)
      (normRows lower (level2 lower (rd3Of (mkRun3 g dtl par) lower j par) (f1Of (mkRun3 g dtl par) lower j dtl)
        (k2Of (mkRun3 g dtl par) lower j dtl par) par).1).1
      (((2 * PR + 62 : ℕ) : ℤ) - ((normRows lower (level2 lower (rd3Of (mkRun3 g dtl par) lower j par)
        (f1Of (mkRun3 g dtl par) lower j dtl) (k2Of (mkRun3 g dtl par) lower j dtl par) par).1).2 : ℤ))
      [((level2 lower (rd3Of (mkRun3 g dtl par) lower j par) (f1Of (mkRun3 g dtl par) lower j dtl)
        (k2Of (mkRun3 g dtl par) lower j dtl par) par).2, ((2 * PR + 62 + 1 : ℕ) : ℤ))]
    rw [← hL] at hpre
    have h0 : L[0]? = some ((level2 lower (rd3Of (mkRun3 g dtl par) lower j par) (f1Of (mkRun3 g dtl par) lower j dtl)
        (k2Of (mkRun3 g dtl par) lower j dtl par) par).2, ((2 * PR + 62 + 1 : ℕ) : ℤ)) := by
      have := congrArg (fun l : List (ℕ × ℤ) => l[0]?) hpre
      simp only [List.length_singleton, List.getElem?_take_of_lt (show 0 < 1 by omega)] at this
      rw [this]; rfl
    rw [show 3 - 3 = 0 from rfl, List.getElem!_eq_getElem?_getD, h0, show 3 - 1 = 2 from rfl, Psid3_two_eq]
    exact level2_phi hrd hl2 par
  · -- `k ≥ 4`: the iteration
    have hb := recIter3_bd hrd hm hev par (kmax - 3) 0 _ _
      [((level2 lower (rd3Of (mkRun3 g dtl par) lower j par) (f1Of (mkRun3 g dtl par) lower j dtl)
        (k2Of (mkRun3 g dtl par) lower j dtl par) par).2, ((2 * PR + 62 + 1 : ℕ) : ℤ))] hrowsN hmantN (k - 4)
      (by omega)
    rw [← hL] at hb
    simp only [List.length_singleton, zero_add] at hb
    rw [show k - 3 = 1 + (k - 4) by omega, show k - 1 = (k - 4) + 3 by omega, Psid3_eq_Clo]
    exact hb

end BHH.W3.Rec

namespace BHH.W3

open W3C W2C BHH BHH.W2 BHH.Cert BHH.W3.Rec

/-- **The recursion.** The outputs of `W3C.runT3` bound `Φ^d_k(t_j)` for the table data `discOf3 g dtl`. -/
theorem recSound3 : RecSound3 := by
  intro g dtl kmax j par hNR hNT hNT2 hev _ _ hdtl hub k hk3 hkk
  exact ⟨Bd_true.mp (runT3_bd g dtl kmax j par true hNR hNT hNT2 hev hdtl hub hk3 hkk),
    Bd_false.mp (runT3_bd g dtl kmax j par false hNR hNT hNT2 hev hdtl hub hk3 hkk)⟩

end BHH.W3
