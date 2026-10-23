import IdentityTesting.BinaryInterpreterMultiply

namespace IdentityTesting.BinaryInterpreterMultiply
open BinaryRegisterMachine (Symbol)
open BinaryRationalRegisters RationalComputation

def readWord (r : BinaryInterpreterRead.State) : BinaryRationalArithmetic.Word :=
  ⟨⟨r.negative, r.num⟩, r.den⟩

def leftState (r : BinaryInterpreterRead.State) (right dest : List Bool) : State :=
  ⟨.left, BinaryRationalArithmeticMultiplier.initial (readWord r) emptyWord,
    r.tape, r.address, right, dest, r.saved, r.copyTemp, r.record, r.numWork, r.denWork,
    r.phase, r.readPhase, r.splitPhase, .joining, .denCollect, .seek⟩

def rightState (r : BinaryInterpreterRead.State) (x : BinaryRationalArithmetic.Word)
    (dest : List Bool) : State :=
  ⟨.right, BinaryRationalArithmeticMultiplier.initial x (readWord r),
    r.tape, [], r.address, dest, r.saved, r.copyTemp, r.record, r.numWork, r.denWork,
    r.phase, r.readPhase, r.splitPhase, .joining, .denCollect, .seek⟩

def multiplyingState (c : BinaryRationalArithmeticMultiplier.State) (tape : List Symbol)
    (dest : List Bool) : State :=
  ⟨.multiplying, c, tape, [], [], dest, [], [], [], [], [], .halt, .halt, .halt,
    .joining, .denCollect, .seek⟩

def storingState (c : BinaryRationalArithmeticMultiplier.State) (w : BinaryInterpreterWrite.State) : State :=
  setWriter {multiplyingState c w.tape w.address with phase := .storing} w

theorem reader_left (r : BinaryInterpreterRead.State) (right dest : List Bool) :
    reader (leftState r right dest) false = r := by
  cases r
  rfl

theorem reader_right (r : BinaryInterpreterRead.State) (x : BinaryRationalArithmetic.Word)
    (dest : List Bool) : reader (rightState r x dest) true = r := by
  cases r
  rfl

theorem forward_left (r : BinaryInterpreterRead.State) (n : ℕ) (tape : List Symbol)
    (x : BinaryRationalArithmetic.Word) (right dest : List Bool)
    (h : BinaryInterpreterRead.advance n r = BinaryInterpreterRead.haltState tape x) :
    ∃ k, k ≤ n+1 ∧ advance k (leftState r right dest) =
      rightState (BinaryInterpreterRead.initial tape right) x dest := by
  induction n generalizing r with
  | zero =>
    simp only [BinaryInterpreterRead.advance] at h
    subst r
    exact ⟨1, by omega, rfl⟩
  | succ n ih =>
    by_cases hh : r.phase = .halt
    · rw [BinaryInterpreterCopy.load_advance_halt _ r hh] at h
      subst r
      exact ⟨1, by omega, rfl⟩
    · obtain ⟨k, hk, he⟩ := ih (BinaryInterpreterRead.step r) h
      refine ⟨k+1, by omega, ?_⟩
      rw [advance]
      simpa [step, leftState, setReader, reader_left, hh, readWord,
        BinaryRationalArithmeticMultiplier.initial, BinarySignedMultiplier.initial,
        BinaryMultiplierMachine.ready] using he

theorem forward_right (r : BinaryInterpreterRead.State) (n : ℕ) (tape : List Symbol)
    (x y : BinaryRationalArithmetic.Word) (dest : List Bool)
    (h : BinaryInterpreterRead.advance n r = BinaryInterpreterRead.haltState tape y) :
    ∃ k, k ≤ n+1 ∧ advance k (rightState r x dest) =
      multiplyingState (BinaryRationalArithmeticMultiplier.initial x y) tape dest := by
  induction n generalizing r with
  | zero =>
    simp only [BinaryInterpreterRead.advance] at h
    subst r
    exact ⟨1, by omega, rfl⟩
  | succ n ih =>
    by_cases hh : r.phase = .halt
    · rw [BinaryInterpreterCopy.load_advance_halt _ r hh] at h
      subst r
      exact ⟨1, by omega, rfl⟩
    · obtain ⟨k, hk, he⟩ := ih (BinaryInterpreterRead.step r) h
      refine ⟨k+1, by omega, ?_⟩
      rw [advance]
      simpa [step, rightState, setReader, reader_right, hh, readWord,
        BinaryRationalArithmeticMultiplier.initial, BinarySignedMultiplier.initial,
        BinaryMultiplierMachine.ready] using he

theorem core_halt (n : ℕ) (c : BinaryRationalArithmeticMultiplier.State) (h : c.phase = .halt) :
    BinaryRationalArithmeticMultiplier.advance n c = c := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [BinaryRationalArithmeticMultiplier.advance, BinaryRationalArithmeticMultiplier.step, h] using ih

theorem storing_initial (c : BinaryRationalArithmeticMultiplier.State) (tape : List Symbol)
    (dest : List Bool) :
    storingState c (BinaryInterpreterWrite.initial tape dest (BinaryRationalArithmeticMultiplier.output c)) =
      {multiplyingState c tape dest with phase := .storing} := by
  cases c with
  | mk p num den norm temp =>
    cases norm
    rfl

theorem forward_multiply (c : BinaryRationalArithmeticMultiplier.State) (n : ℕ)
    (tape : List Symbol) (dest : List Bool)
    (h : (BinaryRationalArithmeticMultiplier.advance n c).phase = .halt) :
    ∃ k, k ≤ n+1 ∧ advance k (multiplyingState c tape dest) =
      storingState (BinaryRationalArithmeticMultiplier.advance n c)
        (BinaryInterpreterWrite.initial tape dest
          (BinaryRationalArithmeticMultiplier.output (BinaryRationalArithmeticMultiplier.advance n c))) ∧
      bitSteps k (multiplyingState c tape dest) ≤ 2*BinaryRationalArithmeticMultiplier.bitSteps n c+1 := by
  induction n generalizing c with
  | zero =>
    simp only [BinaryRationalArithmeticMultiplier.advance] at h ⊢
    refine ⟨1, by omega, ?_, ?_⟩
    · rw [storing_initial]; simp [advance, step, multiplyingState, h]
    · simp [bitSteps, transitionTrace, multiplyingState, h, BinaryRationalArithmeticMultiplier.bitSteps]
  | succ n ih =>
    by_cases hh : c.phase = .halt
    · rw [core_halt (n+1) c hh]
      refine ⟨1, by omega, ?_, ?_⟩
      · rw [storing_initial]; simp [advance, step, multiplyingState, hh]
      · simp [bitSteps, transitionTrace, multiplyingState, hh]
    · obtain ⟨k, hk, he, hc⟩ := ih (BinaryRationalArithmeticMultiplier.step c) h
      refine ⟨k+1, by omega, ?_, ?_⟩
      · rw [advance]
        simpa [step, multiplyingState, hh, BinaryRationalArithmeticMultiplier.advance] using he
      · have ht : 1 ≤ (BinaryRationalArithmeticMultiplier.transitionTrace c).length := by
          cases hp : c.phase <;> simp_all [BinaryRationalArithmeticMultiplier.transitionTrace]
          all_goals split <;> simp_all
        simp only [bitSteps, transitionTrace, step, multiplyingState, if_neg hh, List.length_cons,
          BinaryRationalArithmeticMultiplier.bitSteps]
        change (BinaryRationalArithmeticMultiplier.transitionTrace c).length + 1 +
          bitSteps k (multiplyingState (BinaryRationalArithmeticMultiplier.step c) tape dest) ≤ _
        omega

theorem writer_storing (c : BinaryRationalArithmeticMultiplier.State) (w : BinaryInterpreterWrite.State) :
    writer (storingState c w) = w := by cases w; rfl

theorem forward_store (c : BinaryRationalArithmeticMultiplier.State) (w : BinaryInterpreterWrite.State)
    (n : ℕ) (tape : List Symbol) (sign : Bool)
    (h : BinaryInterpreterWrite.advance n w = BinaryInterpreterWrite.haltState sign tape) :
    ∃ k, k ≤ n+1 ∧ advance k (storingState c w) =
      {storingState c (BinaryInterpreterWrite.haltState sign tape) with phase := .halt} := by
  induction n generalizing w with
  | zero =>
    simp only [BinaryInterpreterWrite.advance] at h
    subst w
    exact ⟨1, by omega, rfl⟩
  | succ n ih =>
    by_cases hh : w.phase = .halt
    · rw [BinaryInterpreterCopy.store_advance_halt _ w hh] at h
      subst w
      exact ⟨1, by omega, rfl⟩
    · obtain ⟨k, hk, he⟩ := ih (BinaryInterpreterWrite.step w) h
      refine ⟨k+1, by omega, ?_⟩
      rw [advance]
      simpa [step, storingState, setWriter, writer, multiplyingState, hh] using he

end IdentityTesting.BinaryInterpreterMultiply
