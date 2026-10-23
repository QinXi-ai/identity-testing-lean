import IdentityTesting.BinaryWorkspaceCost

/-! Physical cleanup of every rational-multiplier stack, with an inverse layout.
The setter is a fixed wiring of the same 69 stacks. The locality theorem shows
that updating one selected stack leaves every other physical stack unchanged. -/
namespace IdentityTesting.BinaryMultiplierStorage
open BinaryWorkspaceAdapters BinaryWorkspaceGrowth
open scoped BigOperators

def tapes (c : BinaryRationalArithmeticMultiplier.State) : Fin 69 → List Bool :=
  ![c.num.mul.factor,
    c.num.mul.shifted,
    c.num.mul.temp,
    c.num.mul.acc,
    c.num.mul.adder.left,
    c.num.mul.adder.right,
    c.num.mul.adder.work,
    c.num.mul.adder.out,
    c.num.norm.source,
    c.num.norm.work,
    c.num.norm.out,
    c.num.temp,
    c.den.mul.factor,
    c.den.mul.shifted,
    c.den.mul.temp,
    c.den.mul.acc,
    c.den.mul.adder.left,
    c.den.mul.adder.right,
    c.den.mul.adder.work,
    c.den.mul.adder.out,
    c.den.norm.source,
    c.den.norm.work,
    c.den.norm.out,
    c.den.temp,
    c.norm.gcd.div.source,
    c.norm.gcd.div.bits,
    c.norm.gcd.div.divisor,
    c.norm.gcd.div.temp,
    c.norm.gcd.div.sub.left,
    c.norm.gcd.div.sub.right,
    c.norm.gcd.div.sub.work,
    c.norm.gcd.div.sub.out,
    c.norm.gcd.div.quot.source,
    c.norm.gcd.div.quot.work,
    c.norm.gcd.div.quot.out,
    c.norm.gcd.div.rem.source,
    c.norm.gcd.div.rem.work,
    c.norm.gcd.div.rem.out,
    c.norm.gcd.temp,
    c.norm.num.source,
    c.norm.num.bits,
    c.norm.num.divisor,
    c.norm.num.temp,
    c.norm.num.sub.left,
    c.norm.num.sub.right,
    c.norm.num.sub.work,
    c.norm.num.sub.out,
    c.norm.num.quot.source,
    c.norm.num.quot.work,
    c.norm.num.rem.source,
    c.norm.num.rem.work,
    c.norm.num.rem.out,
    c.norm.den.source,
    c.norm.den.bits,
    c.norm.den.divisor,
    c.norm.den.temp,
    c.norm.den.sub.left,
    c.norm.den.sub.right,
    c.norm.den.sub.work,
    c.norm.den.sub.out,
    c.norm.den.quot.source,
    c.norm.den.quot.work,
    c.norm.den.rem.source,
    c.norm.den.rem.work,
    c.norm.den.rem.out,
    c.norm.temp,
    c.temp,
    c.norm.num.quot.out,
    c.norm.den.quot.out]

def setTapes (c : BinaryRationalArithmeticMultiplier.State) (f : Fin 69 → List Bool) :
    BinaryRationalArithmeticMultiplier.State :=
  {c with num := {c.num with mul := {c.num.mul with factor := f 0, shifted := f 1, temp := f 2, acc := f 3, adder := {c.num.mul.adder with left := f 4, right := f 5, work := f 6, out := f 7}}, norm := {c.num.norm with source := f 8, work := f 9, out := f 10}, temp := f 11}, den := {c.den with mul := {c.den.mul with factor := f 12, shifted := f 13, temp := f 14, acc := f 15, adder := {c.den.mul.adder with left := f 16, right := f 17, work := f 18, out := f 19}}, norm := {c.den.norm with source := f 20, work := f 21, out := f 22}, temp := f 23}, norm := {c.norm with gcd := {c.norm.gcd with div := {c.norm.gcd.div with source := f 24, bits := f 25, divisor := f 26, temp := f 27, sub := {c.norm.gcd.div.sub with left := f 28, right := f 29, work := f 30, out := f 31}, quot := {c.norm.gcd.div.quot with source := f 32, work := f 33, out := f 34}, rem := {c.norm.gcd.div.rem with source := f 35, work := f 36, out := f 37}}, temp := f 38}, num := {c.norm.num with source := f 39, bits := f 40, divisor := f 41, temp := f 42, sub := {c.norm.num.sub with left := f 43, right := f 44, work := f 45, out := f 46}, quot := {c.norm.num.quot with source := f 47, work := f 48, out := f 67}, rem := {c.norm.num.rem with source := f 49, work := f 50, out := f 51}}, den := {c.norm.den with source := f 52, bits := f 53, divisor := f 54, temp := f 55, sub := {c.norm.den.sub with left := f 56, right := f 57, work := f 58, out := f 59}, quot := {c.norm.den.quot with source := f 60, work := f 61, out := f 68}, rem := {c.norm.den.rem with source := f 62, work := f 63, out := f 64}}, temp := f 65}, temp := f 66}

theorem tapes_set (c : BinaryRationalArithmeticMultiplier.State) (f : Fin 69 → List Bool) :
    tapes (setTapes c f) = f := by
  funext i
  fin_cases i <;> rfl

theorem set_tapes (c : BinaryRationalArithmeticMultiplier.State) : setTapes c (tapes c) = c := by
  rfl

theorem set_set (c : BinaryRationalArithmeticMultiplier.State) (f g : Fin 69 → List Bool) :
    setTapes (setTapes c f) g = setTapes c g := by rfl

theorem update_local (c : BinaryRationalArithmeticMultiplier.State) (i j : Fin 69)
    (word : List Bool) (h : j ≠ i) :
    tapes (setTapes c (Function.update (tapes c) i word)) j = tapes c j := by
  rw [tapes_set, Function.update_of_ne h]

theorem update_selected (c : BinaryRationalArithmeticMultiplier.State) (i : Fin 69)
    (word : List Bool) :
    tapes (setTapes c (Function.update (tapes c) i word)) i = word := by
  rw [tapes_set]
  simp

theorem tapes_cells (c : BinaryRationalArithmeticMultiplier.State) :
    (∑ i, (tapes c i).length) = rationalMultiplierCells c := by
  simp [tapes, Fin.sum_univ_succ, rationalMultiplierCells, signedMultiplierCells,
    multiplierCells, normalizerCells, rationalNormalizationCells, gcdCells, divisionCells, adderCells]
  omega

structure State where
  cursor : Fin 70
  core : BinaryRationalArithmeticMultiplier.State

def view (s : State) : BinaryWorkspaceCleanup.State 69 := ⟨s.cursor, tapes s.core⟩

def step (s : State) : State :=
  let w := BinaryWorkspaceCleanup.step (view s)
  ⟨w.cursor, setTapes s.core w.tapes⟩

def transitionTrace (s : State) : List BinaryArithmetic.BitOp :=
  BinaryWorkspaceCleanup.transitionTrace (view s)

def advance : ℕ → State → State
  | 0,s => s
  | n+1,s => advance n (step s)
def bitSteps : ℕ → State → ℕ
  | 0,_ => 0
  | n+1,s => (transitionTrace s).length + bitSteps n (step s)

theorem view_step (s : State) : view (step s) = BinaryWorkspaceCleanup.step (view s) := by
  simp only [view, step, tapes_set]

theorem view_advance (n : ℕ) (s : State) :
    view (advance n s) = BinaryWorkspaceCleanup.advance n (view s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simpa only [advance, BinaryWorkspaceCleanup.advance, view_step] using ih (step s)

theorem bitSteps_view (n : ℕ) (s : State) :
    bitSteps n s = BinaryWorkspaceCleanup.bitSteps n (view s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [bitSteps, BinaryWorkspaceCleanup.bitSteps, transitionTrace, ih, view_step]

def initial (c : BinaryRationalArithmeticMultiplier.State) : State := ⟨⟨69, by omega⟩, c⟩

theorem clear_all (c : BinaryRationalArithmeticMultiplier.State) :
    let n := 69 + rationalMultiplierCells c
    (advance n (initial c)).cursor.val = 0 ∧
    (∀ i, tapes (advance n (initial c)).core i = []) ∧
    bitSteps n (initial c) ≤ 3*(69+rationalMultiplierCells c) := by
  have h := BinaryWorkspaceCleanup.workspace_cleanup (tapes c)
  rw [tapes_cells] at h
  have hv := view_advance (69+rationalMultiplierCells c) (initial c)
  change view (advance _ (initial c)) =
    BinaryWorkspaceCleanup.advance _ (BinaryWorkspaceCleanup.initial (tapes c)) at hv
  have hcur := congrArg (fun w : BinaryWorkspaceCleanup.State 69 => w.cursor.val) hv
  have htapes := congrArg (fun w : BinaryWorkspaceCleanup.State 69 => w.tapes) hv
  refine ⟨?_, ?_, ?_⟩
  · simpa only [view] using hcur.trans h.1
  · intro i
    exact congrFun htapes i |>.trans (h.2.1 i)
  · rw [bitSteps_view]
    exact h.2.2

end IdentityTesting.BinaryMultiplierStorage
