import IdentityTesting.BinaryArithmeticCost

/-! Reusable cleanup of a fixed finite collection of physical Bool tapes.
The cursor belongs to finite control. A transition inspects one stack head and
either pops one cell or moves to the preceding stack. It never resets a word.
Other physical tapes can be framed: no transition accesses them. -/

namespace IdentityTesting.BinaryWorkspaceCleanup
open BinaryArithmetic
open scoped BigOperators

structure State (k : ℕ) where
  cursor : Fin (k + 1)
  tapes : Fin k → List Bool

def cells {k : ℕ} (s : State k) : ℕ := ∑ i, (s.tapes i).length

def potential {k : ℕ} (s : State k) : ℕ := s.cursor.val + cells s

def CleanAbove {k : ℕ} (s : State k) : Prop :=
  ∀ i : Fin k, s.cursor.val ≤ i.val → s.tapes i = []

def step {k : ℕ} (s : State k) : State k :=
  if h : s.cursor.val = 0 then s else
    let i : Fin k := ⟨s.cursor.val - 1, by have := s.cursor.isLt; omega⟩
    match s.tapes i with
    | [] => { s with cursor := ⟨s.cursor.val - 1, by have := s.cursor.isLt; omega⟩ }
    | _ :: rest => { s with tapes := Function.update s.tapes i rest }

def transitionTrace {k : ℕ} (s : State k) : List BitOp :=
  if h : s.cursor.val = 0 then [] else
    let i : Fin k := ⟨s.cursor.val - 1, by have := s.cursor.isLt; omega⟩
    match s.tapes i with
    | [] => [.readCell, .branch]
    | _ :: _ => [.readCell, .branch, .moveHead]

def advance {k : ℕ} : ℕ → State k → State k
  | 0, s => s
  | n + 1, s => advance n (step s)

def bitSteps {k : ℕ} : ℕ → State k → ℕ
  | 0, _ => 0
  | n + 1, s => (transitionTrace s).length + bitSteps n (step s)

theorem advance_add {k : ℕ} (m n : ℕ) (s : State k) :
    advance (m + n) s = advance n (advance m s) := by
  induction m generalizing s with
  | zero => simp [advance]
  | succ m ih => simpa [Nat.succ_add, advance] using ih (step s)

theorem bitSteps_add {k : ℕ} (m n : ℕ) (s : State k) :
    bitSteps (m + n) s = bitSteps m s + bitSteps n (advance m s) := by
  induction m generalizing s with
  | zero => simp [advance, bitSteps]
  | succ m ih => simp [Nat.succ_add, advance, bitSteps, ih, Nat.add_assoc]

theorem cells_update {k : ℕ} (s : State k) (i : Fin k) (word : List Bool) :
    cells {s with tapes := Function.update s.tapes i word} + (s.tapes i).length =
      cells s + word.length := by
  have hfun : (fun j => (Function.update s.tapes i word j).length) =
      Function.update (fun j => (s.tapes j).length) i word.length := by
    funext j
    by_cases h : j = i
    · subst j; simp
    · simp [Function.update_of_ne h, h]
  simp only [cells, hfun, Finset.sum_update_of_mem (Finset.mem_univ i)]
  have h := Finset.sum_erase_add (s := Finset.univ) (f := fun j => (s.tapes j).length)
    (Finset.mem_univ i)
  simp only [Finset.sdiff_singleton_eq_erase]
  dsimp only at h
  omega

theorem step_potential {k : ℕ} (s : State k) (h : s.cursor.val ≠ 0) :
    potential (step s) + 1 = potential s := by
  let i : Fin k := ⟨s.cursor.val - 1, by have := s.cursor.isLt; omega⟩
  cases hs : s.tapes i with
  | nil => simp only [step, dif_neg h]; change _ + 1 = _
           simp only [show (⟨s.cursor.val - 1, by have := s.cursor.isLt; omega⟩ : Fin k) = i from rfl, hs]
           simp only [potential, cells]
           omega
  | cons b rest =>
    have hc := cells_update s i rest
    rw [hs] at hc
    simp only [step, dif_neg h]
    change potential (match s.tapes i with
      | [] => {s with cursor := ⟨s.cursor.val - 1, by have := s.cursor.isLt; omega⟩}
      | _ :: rest => {s with tapes := Function.update s.tapes i rest}) + 1 = _
    rw [hs]
    simp only [potential, List.length_cons] at *
    omega

theorem step_cleanAbove {k : ℕ} (s : State k) (hc : CleanAbove s) : CleanAbove (step s) := by
  by_cases h : s.cursor.val = 0
  · simpa [step, h] using hc
  let i : Fin k := ⟨s.cursor.val - 1, by have := s.cursor.isLt; omega⟩
  have hstep : step s = match s.tapes i with
      | [] => {s with cursor := ⟨s.cursor.val - 1, by have := s.cursor.isLt; omega⟩}
      | _ :: rest => {s with tapes := Function.update s.tapes i rest} := by simp only [step, dif_neg h]; rfl
  rw [hstep]
  cases hs : s.tapes i with
  | nil =>
    intro j hj
    by_cases he : j = i
    · subst j; exact hs
    · apply hc j
      have hne : j.val ≠ i.val := fun heq => he (Fin.ext heq)
      change s.cursor.val - 1 ≤ j.val at hj
      dsimp [i] at hne
      omega
  | cons b rest =>
    intro j hj
    have hji : j ≠ i := by intro he; subst j; change s.cursor.val ≤ s.cursor.val - 1 at hj; omega
    change Function.update s.tapes i rest j = []
    rw [Function.update_of_ne hji]
    exact hc j hj

theorem advance_halt {k : ℕ} (s : State k) (h : s.cursor.val = 0) (n : ℕ) : advance n s = s := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [advance, step, h] using ih

theorem advance_clears {k : ℕ} (fuel : ℕ) (s : State k)
    (hc : CleanAbove s) (hp : potential s ≤ fuel) :
    (advance fuel s).cursor.val = 0 ∧ ∀ i, (advance fuel s).tapes i = [] := by
  induction fuel generalizing s with
  | zero =>
    have hz : s.cursor.val = 0 := by unfold potential at hp; omega
    exact ⟨hz, fun i => hc i (by omega)⟩
  | succ n ih =>
    by_cases hz : s.cursor.val = 0
    · rw [advance_halt s hz]
      exact ⟨hz, fun i => hc i (by omega)⟩
    · have hs := step_potential s hz
      exact ih (step s) (step_cleanAbove s hc) (by omega)

theorem transitionTrace_length_le {k : ℕ} (s : State k) : (transitionTrace s).length ≤ 3 := by
  unfold transitionTrace
  split
  · simp
  · dsimp only
    split <;> simp

theorem bitSteps_le {k : ℕ} (fuel : ℕ) (s : State k) : bitSteps fuel s ≤ 3 * fuel := by
  induction fuel generalizing s with
  | zero => simp [bitSteps]
  | succ n ih =>
    simp only [bitSteps]
    have h := transitionTrace_length_le s
    have hi := ih (step s)
    omega

def initial {k : ℕ} (w : Fin k → List Bool) : State k := ⟨⟨k, by omega⟩, w⟩

/-- Reusable actual clearing run: every workspace stack is emptied by head pops.
No arithmetic-machine output stack need be included among these k scratch tapes. -/
theorem workspace_cleanup {k : ℕ} (w : Fin k → List Bool) :
    let steps := k + ∑ i, (w i).length
    (advance steps (initial w)).cursor.val = 0 ∧
      (∀ i, (advance steps (initial w)).tapes i = []) ∧
      bitSteps steps (initial w) ≤ 3 * (k + ∑ i, (w i).length) := by
  dsimp only
  have hc : CleanAbove (initial w) := by
    intro i hi
    have := i.isLt
    change k ≤ i.val at hi
    omega
  obtain ⟨hh, hs⟩ := advance_clears (k + ∑ i, (w i).length) (initial w) hc (by rfl)
  exact ⟨hh, hs, bitSteps_le _ _⟩

/-- Generic storage accounting for an actual small-step machine. The caller
proves its one-transition cell-growth bound from its concrete transition. -/
theorem iterate_cells_bound {α : Type*} (next : α → α) (size : α → ℕ) (C : ℕ)
    (hstep : ∀ s, size (next s) ≤ size s + C) (n : ℕ) (s : α) :
    size (next^[n] s) ≤ size s + n * C := by
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    have hi := ih (next s)
    have hs := hstep s
    rw [Nat.succ_mul]
    omega

end IdentityTesting.BinaryWorkspaceCleanup
