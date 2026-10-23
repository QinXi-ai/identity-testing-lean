import IdentityTesting.BinaryWorkspaceCleanup

namespace IdentityTesting.BinaryWorkspaceCleanup
open scoped BigOperators

/-- An arbitrary untouched collection of physical tapes and finite registers. -/
structure FramedState (α : Type*) (k : ℕ) where
  frame : α
  workspace : State k

def framedStep {α : Type*} {k : ℕ} (s : FramedState α k) : FramedState α k :=
  {s with workspace := step s.workspace}

def framedAdvance {α : Type*} {k : ℕ} : ℕ → FramedState α k → FramedState α k
  | 0, s => s
  | n+1, s => framedAdvance n (framedStep s)

def framedBitSteps {α : Type*} {k : ℕ} : ℕ → FramedState α k → ℕ
  | 0, _ => 0
  | n+1, s => (transitionTrace s.workspace).length + framedBitSteps n (framedStep s)

theorem framedAdvance_eq {α : Type*} {k : ℕ} (n : ℕ) (s : FramedState α k) :
    framedAdvance n s = ⟨s.frame, advance n s.workspace⟩ := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simpa only [framedAdvance, framedStep, advance] using ih (framedStep s)

theorem framedBitSteps_eq {α : Type*} {k : ℕ} (n : ℕ) (s : FramedState α k) :
    framedBitSteps n s = bitSteps n s.workspace := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp only [framedBitSteps, bitSteps, ih, framedStep]

theorem framed_cleanup {α : Type*} {k : ℕ} (frame : α) (w : Fin k → List Bool) :
    let n := k + ∑ i, (w i).length
    let s : FramedState α k := ⟨frame, initial w⟩
    (framedAdvance n s).frame = frame ∧
      (∀ i, (framedAdvance n s).workspace.tapes i = []) ∧
      framedBitSteps n s ≤ 3 * (k + ∑ i, (w i).length) := by
  dsimp only
  rw [framedAdvance_eq, framedBitSteps_eq]
  have h := workspace_cleanup w
  exact ⟨rfl, h.2.1, h.2.2⟩

end IdentityTesting.BinaryWorkspaceCleanup
