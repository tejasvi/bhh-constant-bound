/-
Window-3 recursion: `W3C.pushSeg` with the pair of `W3C.emitLoop` read by projections.  (Checking this
equation makes the kernel evaluate the automaton once, about 30 s; it is isolated here so that no other proof needs
to reduce the pattern match on `emitLoop`.)
-/
import W3.RecArith3

namespace BHH.W3.Rec

open W3C

theorem pushSeg_eq (sca sst st m : Array ℕ) (cb wc : ℕ) (acc : Array ℕ) :
    pushSeg ⟨sca, sst, st, m⟩ cb wc acc =
      if (emitLoop acc wc 0 st m).1.size == st.size then
        ⟨sca, sst, (emitLoop acc wc 0 st m).1, (emitLoop acc wc 0 st m).2⟩
      else ⟨sca.push cb, sst.push (emitLoop acc wc 0 st m).1.size, (emitLoop acc wc 0 st m).1,
        (emitLoop acc wc 0 st m).2⟩ := by
  delta pushSeg
  rfl

end BHH.W3.Rec
