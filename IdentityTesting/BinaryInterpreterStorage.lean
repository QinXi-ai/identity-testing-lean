import IdentityTesting.BinaryInterpreterLayout
import IdentityTesting.BinaryWorkspaceCleanup

namespace IdentityTesting.BinaryInterpreterStorage
open BinaryInterpreterLayout
open scoped BigOperators

/-- A bijective wiring of physical stacks, together with the cell accounting of
the concrete head/symbol transitions. No result or time-complexity conclusion
for an instruction is assumed. -/
structure Storage (L : Layout) where
  count : ℕ
  cells : L.Core → ℕ
  tapes : L.Core → Fin count → List Bool
  setTapes : L.Core → (Fin count → List Bool) → L.Core
  tapes_set : ∀ c f, tapes (setTapes c f) = f
  set_tapes : ∀ c, setTapes c (tapes c) = c
  tapes_cells : ∀ c, (∑ i, (tapes c i).length) = cells c
  initial_cells : cells (L.initial ⟨⟨false,[]⟩,[]⟩ ⟨⟨false,[]⟩,[]⟩) = 0
  input_cells : ∀ right c w,
    cells (L.setInput right c w) + (L.input right c).numerator.magnitude.length +
      (L.input right c).denominator.length = cells c+w.numerator.magnitude.length+w.denominator.length
  output_cells : ∀ c n d,
    cells (L.setOutput c n d) + (L.output c).numerator.magnitude.length +
      (L.output c).denominator.length = cells c+n.length+d.length
  step_cells_cost : ∀ c, cells (L.step c) ≤ cells c+(L.trace c).length

variable {L : Layout} (W : Storage L)

structure State where
  cursor : Fin (W.count+1)
  core : L.Core

def view (s : State W) : BinaryWorkspaceCleanup.State W.count := ⟨s.cursor,W.tapes s.core⟩
def step (s : State W) : State W :=
  let w := BinaryWorkspaceCleanup.step (view W s)
  ⟨w.cursor,W.setTapes s.core w.tapes⟩
def transitionTrace (s : State W) : List BinaryArithmetic.BitOp :=
  BinaryWorkspaceCleanup.transitionTrace (view W s)
def advance : ℕ → State W → State W
  | 0,s => s
  | n+1,s => advance n (step W s)
def bitSteps : ℕ → State W → ℕ
  | 0,_ => 0
  | n+1,s => (transitionTrace W s).length + bitSteps n (step W s)

theorem view_step (s : State W) : view W (step W s) = BinaryWorkspaceCleanup.step (view W s) := by
  simp only [view,step,W.tapes_set]

theorem view_advance (n : ℕ) (s : State W) :
    view W (advance W n s) = BinaryWorkspaceCleanup.advance n (view W s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simpa only [advance,BinaryWorkspaceCleanup.advance,view_step] using ih (step W s)

theorem bitSteps_view (n : ℕ) (s : State W) :
    bitSteps W n s = BinaryWorkspaceCleanup.bitSteps n (view W s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp only [bitSteps,BinaryWorkspaceCleanup.bitSteps,transitionTrace,ih,view_step]

def initial (c : L.Core) : State W := ⟨⟨W.count,by omega⟩,c⟩

theorem clear_all (c : L.Core) :
    let n := W.count+W.cells c
    (advance W n (initial W c)).cursor.val = 0 ∧
    (∀ i, W.tapes (advance W n (initial W c)).core i = []) ∧
    bitSteps W n (initial W c) ≤ 3*(W.count+W.cells c) := by
  have h := BinaryWorkspaceCleanup.workspace_cleanup (W.tapes c)
  rw [W.tapes_cells] at h
  have hv := view_advance W (W.count+W.cells c) (initial W c)
  change view W (advance W _ (initial W c)) =
    BinaryWorkspaceCleanup.advance _ (BinaryWorkspaceCleanup.initial (W.tapes c)) at hv
  have hcur := congrArg (fun w : BinaryWorkspaceCleanup.State W.count => w.cursor.val) hv
  have htapes := congrArg (fun w : BinaryWorkspaceCleanup.State W.count => w.tapes) hv
  refine ⟨?_,?_,?_⟩
  · simpa only [view] using hcur.trans h.1
  · intro i
    exact congrFun htapes i |>.trans (h.2.1 i)
  · rw [bitSteps_view]
    exact h.2.2

theorem update_local (c : L.Core) (i j : Fin W.count) (word : List Bool) (h : j ≠ i) :
    W.tapes (W.setTapes c (Function.update (W.tapes c) i word)) j = W.tapes c j := by
  rw [W.tapes_set,Function.update_of_ne h]

end IdentityTesting.BinaryInterpreterStorage
