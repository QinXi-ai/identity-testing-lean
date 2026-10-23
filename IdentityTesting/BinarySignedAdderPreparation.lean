import IdentityTesting.BinarySignedAdderDispatch

namespace IdentityTesting.BinarySignedAdder
open BinaryArithmetic BinarySignedWords

theorem copy_left (s : State) (ht : s.temp = []) :
    Runs { s with phase := .leftCollect } (2 * s.left.length + 2)
      { s with phase := .rightCollect, compare := { s.compare with left := s.left ++ s.compare.left } } := by
  have h1 : Runs { s with phase := .leftCollect } (s.left.length + 1)
      { s with phase := .leftCopy, left := [], temp := s.left.reverse } := by
    simpa [ht] using leftCollect_run s s.left
  have h2 : Runs { s with phase := .leftCopy, left := [], temp := s.left.reverse }
      (s.left.length + 1)
      { s with phase := .rightCollect, compare := { s.compare with left := s.left ++ s.compare.left } } := by
    simpa [ht] using leftCopy_run { s with left := [] } s.left.reverse
  convert h1.trans h2 using 1 <;> omega

theorem copy_right (s : State) (ht : s.temp = []) :
    Runs { s with phase := .rightCollect } (2 * s.right.length + 2)
      { s with phase := .comparing, compare := { s.compare with right := s.right ++ s.compare.right } } := by
  have h1 : Runs { s with phase := .rightCollect } (s.right.length + 1)
      { s with phase := .rightCopy, right := [], temp := s.right.reverse } := by
    simpa [ht] using rightCollect_run s s.right
  have h2 : Runs { s with phase := .rightCopy, right := [], temp := s.right.reverse }
      (s.right.length + 1)
      { s with phase := .comparing, compare := { s.compare with right := s.right ++ s.compare.right } } := by
    simpa [ht] using rightCopy_run { s with right := [] } s.right.reverse
  convert h1.trans h2 using 1 <;> omega

theorem route_left (s : State) (ht : s.temp = []) :
    Runs { s with phase := .leftRouteCollect } (2 * s.left.length + 2)
      { s with phase := .rightRouteCollect, left := [], arith := if s.swap then
        { s.arith with right := s.left ++ s.arith.right }
        else { s.arith with left := s.left ++ s.arith.left } } := by
  have h1 : Runs { s with phase := .leftRouteCollect } (s.left.length + 1)
      { s with phase := .leftRouteEmit, left := [], temp := s.left.reverse } := by
    simpa [ht] using leftRouteCollect_run s s.left
  have h2 : Runs { s with phase := .leftRouteEmit, left := [], temp := s.left.reverse }
      (s.left.length + 1)
      { s with phase := .rightRouteCollect, left := [], arith := if s.swap then
        { s.arith with right := s.left ++ s.arith.right }
        else { s.arith with left := s.left ++ s.arith.left } } := by
    simpa [ht] using leftRouteEmit_run { s with left := [] } s.left.reverse
  convert h1.trans h2 using 1 <;> omega

theorem route_right (s : State) (ht : s.temp = []) :
    Runs { s with phase := .rightRouteCollect } (2 * s.right.length + 2)
      { s with phase := .arithmetic, right := [], arith := if s.swap then
        { s.arith with left := s.right ++ s.arith.left }
        else { s.arith with right := s.right ++ s.arith.right } } := by
  have h1 : Runs { s with phase := .rightRouteCollect } (s.right.length + 1)
      { s with phase := .rightRouteEmit, right := [], temp := s.right.reverse } := by
    simpa [ht] using rightRouteCollect_run s s.right
  have h2 : Runs { s with phase := .rightRouteEmit, right := [], temp := s.right.reverse }
      (s.right.length + 1)
      { s with phase := .arithmetic, right := [], arith := if s.swap then
        { s.arith with left := s.right ++ s.arith.left }
        else { s.arith with right := s.right ++ s.arith.right } } := by
    simpa [ht] using rightRouteEmit_run { s with right := [] } s.right.reverse
  convert h1.trans h2 using 1 <;> omega

def arithmeticReady (a b : Bool) (xs ys : List Bool) (c : BinarySignedComparison.State) : State :=
  let sw := c.result && xor a b
  ⟨.arithmetic, a, b, (if sw then b else a), sw, [], [], [], c,
    BinaryAdderMachine.loopState (if sw then ys else xs) (if sw then xs else ys) { carry := false } [],
    ⟨.collect, [], [], []⟩⟩

theorem prepare (a b : Bool) (xs ys : List Bool) :
    ∃ steps c, steps ≤ 4 * (xs.length + ys.length) + max xs.length ys.length + 11 ∧
      (c.result = true ↔ value xs < value ys) ∧
      Runs (initial ⟨a,xs⟩ ⟨b,ys⟩) steps (arithmeticReady a b xs ys c) := by
  let s := initial ⟨a,xs⟩ ⟨b,ys⟩
  let ci := BinarySignedComparison.initial ⟨false,xs⟩ ⟨false,ys⟩
  let n := max xs.length ys.length + 2
  let cf := BinarySignedComparison.advance n ci
  let copied := { s with phase := .comparing, compare := ci }
  have hleft := copy_left s (by rfl)
  have hleft' : Runs s (2*xs.length+2)
      { s with phase := .rightCollect, compare := { s.compare with left := xs } } := by
    simpa [s, initial, BinarySignedComparison.initial] using hleft
  have hright := copy_right { s with phase := .rightCollect, compare := { s.compare with left := xs } } (by rfl)
  have hcopy : Runs s ((2*xs.length+2)+(2*ys.length+2)) copied := by
    simpa [s, initial, BinarySignedComparison.initial, copied, ci] using hleft'.trans hright
  have hc := BinarySignedComparison.signed_comparison_machine ⟨false,xs⟩ ⟨false,ys⟩
  obtain ⟨j, hj, hjr⟩ := forward_compare copied ci n hc.1
  have hcmp : Runs copied j (afterCompare copied cf) := hjr
  let routed := afterCompare copied cf
  have hl := route_left routed (by rfl)
  let afterLeft := { routed with phase := .rightRouteCollect, left := [], arith := if routed.swap then
    { routed.arith with right := xs ++ routed.arith.right }
    else { routed.arith with left := xs ++ routed.arith.left } }
  have hr := route_right afterLeft (by rfl)
  have hroute : Runs routed ((2*xs.length+2)+(2*ys.length+2)) (arithmeticReady a b xs ys cf) := by
    have h := hl.trans hr
    cases hs : cf.result <;> cases a <;> cases b <;>
      simpa [arithmeticReady, afterLeft, routed, afterCompare, copied, s, initial, hs,
        BinaryAdderMachine.loopState, BinaryAdderMachine.reverseState, BinaryAdderMachine.haltState] using h
  refine ⟨_, cf, ?_, ?_, (hcopy.trans hcmp).trans hroute⟩
  · dsimp [n] at hj
    omega
  · simpa [cf, n, ci, BinarySignedWords.Word.value, signedValue] using hc.2.1

end IdentityTesting.BinarySignedAdder
