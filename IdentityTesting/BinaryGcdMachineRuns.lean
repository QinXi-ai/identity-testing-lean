import IdentityTesting.BinaryGcdMachine

namespace IdentityTesting.BinaryGcdMachine
open BinaryArithmetic

theorem clearQ_run (d : BinaryDivisionMachine.State) (q : List Bool) :
    Runs ⟨.clearQ, { d with quot := { d.quot with out := q } }, []⟩ (q.length + 1)
      ⟨.dToTmp, { d with quot := { d.quot with out := [] } }, []⟩ := by
  induction q with
  | nil => rfl
  | cons b xs ih =>
      change advance (xs.length + 1 + 1) _ = _
      rw [advance]
      exact ih

theorem dToTmp_run (d : BinaryDivisionMachine.State) (ys tmp : List Bool) :
    Runs ⟨.dToTmp, { d with divisor := ys }, tmp⟩ (ys.length + 1)
      ⟨.tmpToX, { d with divisor := [] }, ys.reverse ++ tmp⟩ := by
  induction ys generalizing tmp with
  | nil => rfl
  | cons b xs ih =>
      change advance (xs.length + 1 + 1) _ = _
      rw [advance]
      change advance (xs.length + 1) ⟨.dToTmp, { d with divisor := xs }, b :: tmp⟩ = _
      rw [show advance (xs.length + 1) _ = _ from ih (b :: tmp)]
      simp [List.reverse_cons, List.append_assoc]

theorem tmpToX_run (d : BinaryDivisionMachine.State) (tmp : List Bool) :
    Runs ⟨.tmpToX, d, tmp⟩ (tmp.length + 1)
      ⟨.rToTmp, { d with source := tmp.reverse ++ d.source }, []⟩ := by
  induction tmp generalizing d with
  | nil => cases d; rfl
  | cons b xs ih =>
      change advance (xs.length + 1 + 1) _ = _
      rw [advance]
      change advance (xs.length + 1) ⟨.tmpToX, { d with source := b :: d.source }, xs⟩ = _
      rw [show advance (xs.length + 1) _ = _ from ih { d with source := b :: d.source }]
      simp [List.reverse_cons, List.append_assoc]

theorem rToTmp_run (d : BinaryDivisionMachine.State) (rs tmp : List Bool) :
    Runs ⟨.rToTmp, { d with rem := { d.rem with out := rs } }, tmp⟩ (rs.length + 1)
      ⟨.tmpToD, { d with rem := { d.rem with out := [] } }, rs.reverse ++ tmp⟩ := by
  induction rs generalizing tmp with
  | nil => rfl
  | cons b xs ih =>
      change advance (xs.length + 1 + 1) _ = _
      rw [advance]
      change advance (xs.length + 1) ⟨.rToTmp, { d with rem := { d.rem with out := xs } }, b :: tmp⟩ = _
      rw [show advance (xs.length + 1) _ = _ from ih (b :: tmp)]
      simp [List.reverse_cons, List.append_assoc]

theorem tmpToD_run (d : BinaryDivisionMachine.State) (tmp : List Bool) :
    Runs ⟨.tmpToD, d, tmp⟩ (tmp.length + 1)
      ⟨.restart, { d with divisor := tmp.reverse ++ d.divisor }, []⟩ := by
  induction tmp generalizing d with
  | nil => cases d; rfl
  | cons b xs ih =>
      change advance (xs.length + 1 + 1) _ = _
      rw [advance]
      change advance (xs.length + 1) ⟨.tmpToD, { d with divisor := b :: d.divisor }, xs⟩ = _
      rw [show advance (xs.length + 1) _ = _ from ih { d with divisor := b :: d.divisor }]
      simp [List.reverse_cons, List.append_assoc]

private theorem div_advance_halt (n : ℕ) (d : BinaryDivisionMachine.State) (h : d.phase = .halt) :
    BinaryDivisionMachine.advance n d = d := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [BinaryDivisionMachine.advance, BinaryDivisionMachine.step, h] using ih

theorem forward_div (d : BinaryDivisionMachine.State) (n : ℕ)
    (h : (BinaryDivisionMachine.advance n d).phase = .halt) :
    ∃ k, k ≤ n + 1 ∧ Runs ⟨.dividing, d, []⟩ k
      ⟨.clearQ, BinaryDivisionMachine.advance n d, []⟩ := by
  induction n generalizing d with
  | zero =>
      refine ⟨1, by omega, ?_⟩
      simp only [BinaryDivisionMachine.advance] at h
      simp [Runs, advance, step, h, BinaryDivisionMachine.advance]
  | succ n ih =>
      by_cases hh : d.phase = .halt
      · refine ⟨1, by omega, ?_⟩
        rw [div_advance_halt (n + 1) d hh]
        simp [Runs, advance, step, hh]
      · obtain ⟨k, hk, he⟩ := ih (BinaryDivisionMachine.step d) h
        refine ⟨k + 1, by omega, ?_⟩
        dsimp [Runs] at *
        rw [advance]
        simpa [step, hh, BinaryDivisionMachine.advance] using he

end IdentityTesting.BinaryGcdMachine
