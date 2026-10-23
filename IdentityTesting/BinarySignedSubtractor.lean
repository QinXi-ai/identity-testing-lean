import IdentityTesting.BinarySignedAdderBound
import IdentityTesting.BinarySignedNegation

/-! Subtraction changes the right operand's sign cell in place, then runs the
actual signed adder. The sign update and submachine dispatch are charged. -/
namespace IdentityTesting.BinarySignedSubtractor
open BinaryArithmetic BinarySignedWords

inductive Phase where
  | negate | adding | halt
  deriving DecidableEq, Repr

structure State where
  phase : Phase
  core : BinarySignedAdder.State
  deriving DecidableEq, Repr

def step (s : State) : State :=
  match s.phase with
  | .negate => { s with phase := .adding, core := { s.core with negativeRight := if s.core.right = [] then false else xor s.core.negativeRight true } }
  | .adding => if s.core.phase = .halt then { s with phase := .halt }
      else { s with core := BinarySignedAdder.step s.core }
  | .halt => s

def initial (x y : Word) : State := ⟨.negate,BinarySignedAdder.initial x y⟩
def output (s : State) : Word := BinarySignedAdder.output s.core

def advance : ℕ → State → State
  | 0,s => s
  | n+1,s => advance n (step s)

def transitionTrace (s : State) : List BitOp :=
  match s.phase with
  | .negate => [.readCell,.branch,.xorGate,.writeCell]
  | .adding => if s.core.phase = .halt then [.branch] else .branch :: BinarySignedAdder.transitionTrace s.core
  | .halt => []

def bitSteps : ℕ → State → ℕ
  | 0,_ => 0
  | n+1,s => (transitionTrace s).length+bitSteps n (step s)

theorem bitSteps_le (n : ℕ) (s : State) : bitSteps n s ≤ 13*n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      have hc := BinarySignedAdder.transition_length s.core
      have ht : (transitionTrace s).length ≤ 13 := by
        cases hp : s.phase <;> simp only [transitionTrace,hp]
        · simp
        · split <;> simp_all
        · simp
      have hi := ih (step s)
      simp only [bitSteps]
      omega

private theorem adder_halt (k : ℕ) (s : BinarySignedAdder.State) (h : s.phase = .halt) :
    BinarySignedAdder.advance k s = s := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [BinarySignedAdder.advance,BinarySignedAdder.step,h] using ih

theorem forward_add (s : BinarySignedAdder.State) (k : ℕ)
    (h : (BinarySignedAdder.advance k s).phase = .halt) :
    ∃ j, j ≤ k+1 ∧ advance j ⟨.adding,s⟩ = ⟨.halt,BinarySignedAdder.advance k s⟩ := by
  induction k generalizing s with
  | zero =>
      refine ⟨1,by omega,?_⟩
      simp only [BinarySignedAdder.advance] at h
      simp [advance,step,h,BinarySignedAdder.advance]
  | succ k ih =>
      by_cases hh : s.phase = .halt
      · refine ⟨1,by omega,?_⟩
        rw [adder_halt (k+1) s hh]
        simp [advance,step,hh]
      · obtain ⟨j,hj,he⟩ := ih (BinarySignedAdder.step s) h
        refine ⟨j+1,by omega,?_⟩
        rw [advance]
        simpa [step,hh,BinarySignedAdder.advance] using he

theorem signed_subtraction_machine (x y : Word) :
    ∃ steps, steps ≤ 4*(x.magnitude.length+y.magnitude.length)+15*max x.magnitude.length y.magnitude.length+28 ∧
      (advance steps (initial x y)).phase = .halt ∧
      (output (advance steps (initial x y))).value = x.value-y.value ∧
      (output (advance steps (initial x y))).magnitude = (x.value-y.value).natAbs.bits := by
  let z := BinarySignedNegation.step y
  obtain ⟨k,hk,hh,hv,hm⟩ := BinarySignedAdder.run_signed_sum x.negative z.negative x.magnitude z.magnitude
  obtain ⟨j,hj,hr⟩ := forward_add (BinarySignedAdder.initial x z) k hh
  have hfirst : step (initial x y) = ⟨.adding,BinarySignedAdder.initial x z⟩ := rfl
  have hw : advance (j+1) (initial x y) = ⟨.halt,BinarySignedAdder.advance k (BinarySignedAdder.initial x z)⟩ := by
    rw [advance,hfirst,hr]
  have hz : z.value = -y.value := BinarySignedNegation.step_value y
  have hv' : (BinarySignedAdder.output (BinarySignedAdder.advance k (BinarySignedAdder.initial x z))).value = x.value-y.value := by
    change _ = x.value+z.value at hv
    rw [hz,← sub_eq_add_neg] at hv
    exact hv
  have hm' : (BinarySignedAdder.output (BinarySignedAdder.advance k (BinarySignedAdder.initial x z))).magnitude = (x.value-y.value).natAbs.bits := by
    change _ = (x.value+z.value).natAbs.bits at hm
    rw [hz,← sub_eq_add_neg] at hm
    exact hm
  refine ⟨j+1,?_,?_,?_,?_⟩
  · change k ≤ 4*(x.magnitude.length+y.magnitude.length)+15*max x.magnitude.length y.magnitude.length+26 at hk
    omega
  · rw [hw]
  · change (BinarySignedAdder.output (advance _ _).core).value = _
    rw [hw]
    exact hv'
  · change (BinarySignedAdder.output (advance _ _).core).magnitude = _
    rw [hw]
    exact hm'

theorem binary_signed_subtraction_machine (x y : ℤ) :
    ∃ steps, (advance steps (initial (encode x) (encode y))).phase = .halt ∧
      (output (advance steps (initial (encode x) (encode y)))).value = x-y ∧
      (output (advance steps (initial (encode x) (encode y)))).magnitude = (x-y).natAbs.bits ∧
      bitSteps steps (initial (encode x) (encode y)) ≤ 500*(x.natAbs.size+y.natAbs.size+1) := by
  obtain ⟨steps,hs,hh,hv,hm⟩ := signed_subtraction_machine (encode x) (encode y)
  refine ⟨steps,hh,?_,?_,?_⟩
  · simpa only [encode_value] using hv
  · simpa only [encode_value] using hm
  · have hb := bitSteps_le steps (initial (encode x) (encode y))
    simp only [encode,Nat.size_eq_bits_len] at hs
    have hmax : max x.natAbs.size y.natAbs.size ≤ x.natAbs.size+y.natAbs.size := max_le (by omega) (by omega)
    omega

end IdentityTesting.BinarySignedSubtractor
