import IdentityTesting.BinarySignedAdderRuns

namespace IdentityTesting.BinarySignedAdder
open BinaryArithmetic BinarySignedWords

def afterCompare (s : State) (c : BinarySignedComparison.State) : State :=
  { s with
    phase := .leftRouteCollect
    compare := c
    swap := c.result && (xor s.negativeLeft s.negativeRight)
    negative := if c.result && (xor s.negativeLeft s.negativeRight) then s.negativeRight else s.negativeLeft }

private theorem compare_halt (k : ℕ) (c : BinarySignedComparison.State) (h : c.phase = .halt) :
    BinarySignedComparison.advance k c = c := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [BinarySignedComparison.advance, BinarySignedComparison.step, h] using ih

theorem forward_compare (s : State) (c : BinarySignedComparison.State) (k : ℕ)
    (h : (BinarySignedComparison.advance k c).phase = .halt) :
    ∃ j, j ≤ k+1 ∧ Runs { s with phase := .comparing, compare := c } j
      (afterCompare s (BinarySignedComparison.advance k c)) := by
  induction k generalizing c with
  | zero =>
      refine ⟨1, by omega, ?_⟩
      simp only [BinarySignedComparison.advance] at h
      simp [Runs, advance, step, h, BinarySignedComparison.advance, afterCompare]
  | succ k ih =>
      by_cases hh : c.phase = .halt
      · refine ⟨1, by omega, ?_⟩
        rw [compare_halt (k+1) c hh]
        simp [Runs, advance, step, hh, afterCompare]
      · obtain ⟨j, hj, he⟩ := ih (BinarySignedComparison.step c) h
        refine ⟨j+1, by omega, ?_⟩
        dsimp [Runs] at *
        rw [advance]
        simpa [step, hh, BinarySignedComparison.advance] using he


private theorem add_halt (k : ℕ) (c : BinaryAdderMachine.State) (h : c.phase = .halt) :
    BinaryAdderMachine.advance k c = c := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [BinaryAdderMachine.advance, BinaryAdderMachine.step, h] using ih

theorem forward_add (s : State) (c : BinaryAdderMachine.State) (k : ℕ)
    (hsg : s.negativeLeft = s.negativeRight)
    (h : (BinaryAdderMachine.advance k c).phase = .halt) :
    ∃ j, j ≤ k+1 ∧ Runs { s with phase := .arithmetic, arith := c } j
      { s with phase := .outCollect, arith := BinaryAdderMachine.advance k c } := by
  induction k generalizing c with
  | zero =>
      refine ⟨1, by omega, ?_⟩
      simp only [BinaryAdderMachine.advance] at h
      simp [Runs, advance, step, h, BinaryAdderMachine.advance]
  | succ k ih =>
      by_cases hh : c.phase = .halt
      · refine ⟨1, by omega, ?_⟩
        rw [add_halt (k+1) c hh]
        simp [Runs, advance, step, hh]
      · obtain ⟨j, hj, he⟩ := ih (BinaryAdderMachine.step c) h
        refine ⟨j+1, by omega, ?_⟩
        dsimp [Runs] at *
        rw [advance]
        simpa [step, hh, hsg, BinaryAdderMachine.advance] using he

private theorem sub_halt (k : ℕ) (c : BinarySubtractorMachine.State) (h : c.phase = .halt) :
    BinarySubtractorMachine.advance k c = c := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [BinarySubtractorMachine.advance, BinarySubtractorMachine.step, BinaryAdderMachine.step, h] using ih

theorem forward_sub (s : State) (c : BinarySubtractorMachine.State) (k : ℕ)
    (hsg : s.negativeLeft ≠ s.negativeRight)
    (h : (BinarySubtractorMachine.advance k c).phase = .halt) :
    ∃ j, j ≤ k+1 ∧ Runs { s with phase := .arithmetic, arith := c } j
      { s with phase := .outCollect, arith := BinarySubtractorMachine.advance k c } := by
  induction k generalizing c with
  | zero =>
      refine ⟨1, by omega, ?_⟩
      simp only [BinarySubtractorMachine.advance] at h
      simp [Runs, advance, step, h, BinarySubtractorMachine.advance]
  | succ k ih =>
      by_cases hh : c.phase = .halt
      · refine ⟨1, by omega, ?_⟩
        rw [sub_halt (k+1) c hh]
        simp [Runs, advance, step, hh]
      · obtain ⟨j, hj, he⟩ := ih (BinarySubtractorMachine.step c) h
        refine ⟨j+1, by omega, ?_⟩
        dsimp [Runs] at *
        rw [advance]
        simpa [step, hh, hsg, BinarySubtractorMachine.advance] using he

private theorem norm_halt (k : ℕ) (c : BinaryWordNormalization.State) (h : c.phase = .halt) :
    BinaryWordNormalization.advance k c = c := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [BinaryWordNormalization.advance, BinaryWordNormalization.step, h] using ih

theorem forward_norm (s : State) (c : BinaryWordNormalization.State) (k : ℕ)
    (h : (BinaryWordNormalization.advance k c).phase = .halt) :
    ∃ j, j ≤ k+1 ∧ Runs { s with phase := .normalizing, norm := c } j
      { s with phase := .finish, norm := BinaryWordNormalization.advance k c } := by
  induction k generalizing c with
  | zero =>
      refine ⟨1, by omega, ?_⟩
      simp only [BinaryWordNormalization.advance] at h
      simp [Runs, advance, step, h, BinaryWordNormalization.advance]
  | succ k ih =>
      by_cases hh : c.phase = .halt
      · refine ⟨1, by omega, ?_⟩
        rw [norm_halt (k+1) c hh]
        simp [Runs, advance, step, hh]
      · obtain ⟨j, hj, he⟩ := ih (BinaryWordNormalization.step c) h
        refine ⟨j+1, by omega, ?_⟩
        dsimp [Runs] at *
        rw [advance]
        simpa [step, hh, BinaryWordNormalization.advance] using he

end IdentityTesting.BinarySignedAdder
