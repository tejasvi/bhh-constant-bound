/-
The window-3 sweep automaton ("connectivity + local degree", the automaton of the window-3 certificate with W = 3),
core Lean only.

A state after step `i` (points `0..i` placed) describes the window, the last `min(3, i+1)` points, newest first:
`part` (canonical component labels of the window points in the graph of sure window-3 edges among `0..i`), `cnt` (the
number of neighbours seen so far of each window point, capped at 2) and `u` (the number of points that have left the window
with fewer than two neighbours; the state is dead when `u` would reach 2, or when a component leaves the window).
`step s a` adds a point with the edges `a = (N, S, T)` to the window points `1, 2, 3` back (absent window points get `false`).
`close2 s a`: twice the closing value after the last point (`2`, `1` or `0`).
-/

namespace W3C

structure St where
  part : List Nat
  cnt : List Nat
  u : Nat
  deriving DecidableEq, Repr, Inhabited, BEq

/-- canonical relabelling: labels in order of first occurrence -/
def canon (l : List Nat) : List Nat :=
  let rec go : List Nat → List Nat → List Nat → List Nat
    | [], _, acc => acc.reverse
    | x :: xs, seen, acc =>
      match seen.idxOf? x with
      | some i => go xs seen (i :: acc)
      | none => go xs (seen ++ [x]) (seen.length :: acc)
  go l [] []

/-- the state after the first point `y_0` -/
def St.init : St := ⟨[0], [0], 0⟩

/-- replace every occurrence of `old` by `new` -/
def relabel (old new : Nat) (l : List Nat) : List Nat := l.map fun x => if x == old then new else x

/-- add a point with the edges `a[d-1]` to the window point `d` positions back (`d = 1, 2, 3`) -/
def St.step (s : St) (a : List Bool) : Option St :=
  let n := s.part.length
  let a' := (List.range 3).map fun d => if d < n then a.getD d false else false
  -- new point first (fresh label 100), then the old window points
  let lab0 : List Nat := 100 :: s.part
  let cnt0 : List Nat := 0 :: s.cnt
  let (lab, cnts) := (List.range n).foldl (fun (acc : List Nat × List Nat) d0 =>
      let d := d0 + 1
      if a'.getD d0 false then
        let lab := acc.1
        let old := lab.getD d 0
        let new := lab.getD 0 0
        (relabel old new lab, (acc.2.modify 0 (· + 1)).modify d (· + 1))
      else acc) (lab0, cnt0)
  let cnts := cnts.map fun c => Min.min c 2
  if n + 1 > 3 then
    let leavingLab := lab.getD n 0
    let leavingCnt := cnts.getD n 0
    let rest := lab.take n
    if !rest.contains leavingLab then none
    else
      let u2 := s.u + (if 2 ≤ leavingCnt then 0 else 1)
      if 2 ≤ u2 then none
      else some ⟨canon rest, cnts.take n, u2⟩
  else some ⟨canon lab, cnts, s.u⟩

/-- twice the closing value after adding the last point with edges `a` -/
def St.close2 (s : St) (a : List Bool) : Nat :=
  match s.step a with
  | none => 0
  | some t =>
    if t.part.all (· == 0) then
      let u2 := t.u + (t.cnt.filter (· < 2)).length
      if u2 == 0 then 2 else if u2 == 1 then 1 else 0
    else 0

/-- input index `4 N + 2 S + T` (the order of `itertools.product((0, 1), repeat = 3)`) -/
def inputOf (i : Nat) : List Bool := [i / 4 % 2 == 1, i / 2 % 2 == 1, i % 2 == 1]

/-- The reachable states in breadth-first order from `init` (the order of the certificate's automaton generator; computed with fuel). -/
def reachable : Array St := Id.run do
  let mut states : Array St := #[St.init]
  let mut qi : Nat := 0
  for _ in [0:1000] do
    if qi < states.size then
      let s := states[qi]!
      qi := qi + 1
      for i in [0:8] do
        match s.step (inputOf i) with
        | none => pure ()
        | some t => if !states.contains t then states := states.push t
  return states

/-- index of a state in `reachable` (`reachable.size` if absent) -/
def stIndex (t : St) : Nat := (reachable.findIdx? (· == t)).getD reachable.size

/-- transition table: `trans[s * 8 + i]` = index of `step` (or `none`) -/
def transTab : Array (Option Nat) :=
  (Array.range (reachable.size * 8)).map fun k =>
    match (reachable[k / 8]!).step (inputOf (k % 8)) with
    | none => none
    | some t => some (stIndex t)

/-- closing table: `close2Tab[s * 8 + i]` -/
def close2Tab : Array Nat :=
  (Array.range (reachable.size * 8)).map fun k => (reachable[k / 8]!).close2 (inputOf (k % 8))

end W3C
