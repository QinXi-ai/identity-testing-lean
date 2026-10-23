import IdentityTesting.BinaryRationalNormalizationMachine

namespace IdentityTesting.BinaryRationalNormalizationMachine
open BinaryArithmetic

theorem nToTmp_run (sg : Bool) (g : BinaryGcdMachine.State)
    (n d : BinaryDivisionMachine.State) (xs tmp : List Bool) :
    Runs ⟨.nToTmp, sg, g, { n with source := xs }, d, tmp⟩ (xs.length + 1)
      ⟨.tmpToN, sg, g, { n with source := [] }, d, xs.reverse ++ tmp⟩ := by
  induction xs generalizing tmp with
  | nil => rfl
  | cons b xs ih =>
      change advance (xs.length + 1 + 1) _ = _
      rw [advance]
      change advance (xs.length + 1) ⟨.nToTmp, sg, g, { n with source := xs }, d, b :: tmp⟩ = _
      rw [show advance (xs.length + 1) _ = _ from ih (b :: tmp)]
      simp [List.reverse_cons, List.append_assoc]

theorem tmpToN_run (sg : Bool) (g : BinaryGcdMachine.State)
    (n d : BinaryDivisionMachine.State) (tmp : List Bool) :
    Runs ⟨.tmpToN, sg, g, n, d, tmp⟩ (tmp.length + 1)
      ⟨.dToTmp, sg, { g with div := { g.div with source := tmp.reverse ++ g.div.source } },
        { n with source := tmp.reverse ++ n.source }, d, []⟩ := by
  induction tmp generalizing n g with
  | nil => cases n; cases g; rfl
  | cons b xs ih =>
      change advance (xs.length + 1 + 1) _ = _
      rw [advance]
      change advance (xs.length + 1) ⟨.tmpToN, sg,
        { g with div := { g.div with source := b :: g.div.source } }, { n with source := b :: n.source }, d, xs⟩ = _
      rw [show advance (xs.length + 1) _ = _ from
        ih { g with div := { g.div with source := b :: g.div.source } } { n with source := b :: n.source }]
      simp [List.reverse_cons, List.append_assoc]

theorem dToTmp_run (sg : Bool) (g : BinaryGcdMachine.State)
    (n d : BinaryDivisionMachine.State) (xs tmp : List Bool) :
    Runs ⟨.dToTmp, sg, g, n, { d with source := xs }, tmp⟩ (xs.length + 1)
      ⟨.tmpToD, sg, g, n, { d with source := [] }, xs.reverse ++ tmp⟩ := by
  induction xs generalizing tmp with
  | nil => rfl
  | cons b xs ih =>
      change advance (xs.length + 1 + 1) _ = _
      rw [advance]
      change advance (xs.length + 1) ⟨.dToTmp, sg, g, n, { d with source := xs }, b :: tmp⟩ = _
      rw [show advance (xs.length + 1) _ = _ from ih (b :: tmp)]
      simp [List.reverse_cons, List.append_assoc]

theorem tmpToD_run (sg : Bool) (g : BinaryGcdMachine.State)
    (n d : BinaryDivisionMachine.State) (tmp : List Bool) :
    Runs ⟨.tmpToD, sg, g, n, d, tmp⟩ (tmp.length + 1)
      ⟨.gcd, sg, { g with div := { g.div with divisor := tmp.reverse ++ g.div.divisor } },
        n, { d with source := tmp.reverse ++ d.source }, []⟩ := by
  induction tmp generalizing d g with
  | nil => cases d; cases g; rfl
  | cons b xs ih =>
      change advance (xs.length + 1 + 1) _ = _
      rw [advance]
      change advance (xs.length + 1) ⟨.tmpToD, sg,
        { g with div := { g.div with divisor := b :: g.div.divisor } }, n, { d with source := b :: d.source }, xs⟩ = _
      rw [show advance (xs.length + 1) _ = _ from
        ih { g with div := { g.div with divisor := b :: g.div.divisor } } { d with source := b :: d.source }]
      simp [List.reverse_cons, List.append_assoc]

theorem gToTmp_run (sg : Bool) (g : BinaryGcdMachine.State)
    (n d : BinaryDivisionMachine.State) (xs tmp : List Bool) :
    Runs ⟨.gToTmp, sg, { g with div := { g.div with source := xs } }, n, d, tmp⟩ (xs.length + 1)
      ⟨.tmpToG, sg, { g with div := { g.div with source := [] } }, n, d, xs.reverse ++ tmp⟩ := by
  induction xs generalizing tmp with
  | nil => rfl
  | cons b xs ih =>
      change advance (xs.length + 1 + 1) _ = _
      rw [advance]
      change advance (xs.length + 1) ⟨.gToTmp, sg, { g with div := { g.div with source := xs } }, n, d, b :: tmp⟩ = _
      rw [show advance (xs.length + 1) _ = _ from ih (b :: tmp)]
      simp [List.reverse_cons, List.append_assoc]

theorem tmpToG_run (sg : Bool) (g : BinaryGcdMachine.State)
    (n d : BinaryDivisionMachine.State) (tmp : List Bool) :
    Runs ⟨.tmpToG, sg, g, n, d, tmp⟩ (tmp.length + 1)
      ⟨.divN, sg, g, { n with divisor := tmp.reverse ++ n.divisor },
        { d with divisor := tmp.reverse ++ d.divisor }, []⟩ := by
  induction tmp generalizing n d with
  | nil => cases n; cases d; rfl
  | cons b xs ih =>
      change advance (xs.length + 1 + 1) _ = _
      rw [advance]
      change advance (xs.length + 1) ⟨.tmpToG, sg, g,
        { n with divisor := b :: n.divisor }, { d with divisor := b :: d.divisor }, xs⟩ = _
      rw [show advance (xs.length + 1) _ = _ from
        ih { n with divisor := b :: n.divisor } { d with divisor := b :: d.divisor }]
      simp [List.reverse_cons, List.append_assoc]


private theorem gcd_advance_halt (k : ℕ) (a : BinaryGcdMachine.State) (h : a.phase = .halt) :
    BinaryGcdMachine.advance k a = a := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [BinaryGcdMachine.advance, BinaryGcdMachine.step, h] using ih


private theorem div_advance_halt (k : ℕ) (a : BinaryDivisionMachine.State) (h : a.phase = .halt) :
    BinaryDivisionMachine.advance k a = a := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [BinaryDivisionMachine.advance, BinaryDivisionMachine.step, h] using ih


theorem forward_gcd (sg : Bool) (g : BinaryGcdMachine.State)
    (num den : BinaryDivisionMachine.State) (k : ℕ)
    (h : (BinaryGcdMachine.advance k g).phase = .halt) :
    ∃ j, j ≤ k + 1 ∧ Runs ⟨.gcd, sg, g, num, den, []⟩ j ⟨.gToTmp, sg, BinaryGcdMachine.advance k g, num, den, []⟩ := by
  induction k generalizing g with
  | zero =>
      refine ⟨1, by omega, ?_⟩
      simp only [BinaryGcdMachine.advance] at h
      simp [Runs, advance, step, h, BinaryGcdMachine.advance]
  | succ k ih =>
      by_cases hh : g.phase = .halt
      · refine ⟨1, by omega, ?_⟩
        rw [gcd_advance_halt (k + 1) g hh]
        simp [Runs, advance, step, hh]
      · obtain ⟨j, hj, he⟩ := ih (BinaryGcdMachine.step g) h
        refine ⟨j + 1, by omega, ?_⟩
        dsimp [Runs] at *
        rw [advance]
        simpa [step, hh, BinaryGcdMachine.advance] using he


theorem forward_divN (sg : Bool) (g : BinaryGcdMachine.State)
    (num den : BinaryDivisionMachine.State) (k : ℕ)
    (h : (BinaryDivisionMachine.advance k num).phase = .halt) :
    ∃ j, j ≤ k + 1 ∧ Runs ⟨.divN, sg, g, num, den, []⟩ j ⟨.divD, sg, g, BinaryDivisionMachine.advance k num, den, []⟩ := by
  induction k generalizing num with
  | zero =>
      refine ⟨1, by omega, ?_⟩
      simp only [BinaryDivisionMachine.advance] at h
      simp [Runs, advance, step, h, BinaryDivisionMachine.advance]
  | succ k ih =>
      by_cases hh : num.phase = .halt
      · refine ⟨1, by omega, ?_⟩
        rw [div_advance_halt (k + 1) num hh]
        simp [Runs, advance, step, hh]
      · obtain ⟨j, hj, he⟩ := ih (BinaryDivisionMachine.step num) h
        refine ⟨j + 1, by omega, ?_⟩
        dsimp [Runs] at *
        rw [advance]
        simpa [step, hh, BinaryDivisionMachine.advance] using he


theorem forward_divD (sg : Bool) (g : BinaryGcdMachine.State)
    (num den : BinaryDivisionMachine.State) (k : ℕ)
    (h : (BinaryDivisionMachine.advance k den).phase = .halt) :
    ∃ j, j ≤ k + 1 ∧ Runs ⟨.divD, sg, g, num, den, []⟩ j ⟨.sign, sg, g, num, BinaryDivisionMachine.advance k den, []⟩ := by
  induction k generalizing den with
  | zero =>
      refine ⟨1, by omega, ?_⟩
      simp only [BinaryDivisionMachine.advance] at h
      simp [Runs, advance, step, h, BinaryDivisionMachine.advance]
  | succ k ih =>
      by_cases hh : den.phase = .halt
      · refine ⟨1, by omega, ?_⟩
        rw [div_advance_halt (k + 1) den hh]
        simp [Runs, advance, step, hh]
      · obtain ⟨j, hj, he⟩ := ih (BinaryDivisionMachine.step den) h
        refine ⟨j + 1, by omega, ?_⟩
        dsimp [Runs] at *
        rw [advance]
        simpa [step, hh, BinaryDivisionMachine.advance] using he


end IdentityTesting.BinaryRationalNormalizationMachine
