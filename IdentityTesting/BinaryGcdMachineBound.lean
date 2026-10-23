import IdentityTesting.BinaryGcdMachineRuns

namespace IdentityTesting.BinaryGcdMachine
open BinaryArithmetic BinaryLongDivision BinaryWordNormalization BinaryEuclideanRounds

theorem divide_binary_eq (m n : ℕ) (hn : 0 < n) :
    divide m.bits n.bits = ((m / n).bits, (m % n).bits) := by
  have hv := divide_binary_inputs m n hn
  apply Prod.ext
  · have ht := trim_eq_bits (loop m.bits.reverse n.bits [] []).1
    rw [show value (loop m.bits.reverse n.bits [] []).1 = m / n from by
      simpa only [divide, trim_value] using hv.1] at ht
    exact ht
  · have ht := trim_eq_bits (loop m.bits.reverse n.bits [] []).2
    rw [show value (loop m.bits.reverse n.bits [] []).2 = m % n from by
      simpa only [divide, trim_value] using hv.2] at ht
    exact ht

theorem gcd_iteration (m n : ℕ) (hn : 0 < n) :
    ∃ steps, steps ≤ 40 * (m.size + n.size + 1) ^ 2 ∧
      Runs (ready m.bits n.bits) steps (ready n.bits (m % n).bits) := by
  obtain ⟨nd, regs, hnd, hd⟩ := BinaryDivisionMachine.division_run m.bits n.bits
  have hdiv : BinaryDivisionMachine.advance nd (BinaryDivisionMachine.initial m.bits n.bits) =
      BinaryDivisionMachine.terminal n.bits (m / n).bits (m % n).bits regs := by
    simpa only [BinaryDivisionMachine.Runs, divide_binary_eq m n hn] using hd
  have hhalt : (BinaryDivisionMachine.advance nd (BinaryDivisionMachine.initial m.bits n.bits)).phase = .halt := by
    rw [hdiv]
    rfl
  obtain ⟨k, hk, hforward⟩ := forward_div _ nd hhalt
  let d0 := BinaryDivisionMachine.terminal n.bits (m / n).bits (m % n).bits regs
  let d1 := { d0 with quot := { d0.quot with out := [] } }
  let d2 := { d1 with divisor := [] }
  let d3 := { d2 with source := n.bits }
  let d4 := { d3 with rem := { d3.rem with out := [] } }
  let d5 := { d4 with divisor := (m % n).bits }
  have h0 : Runs (ready m.bits n.bits) 1
      ⟨.dividing, BinaryDivisionMachine.initial m.bits n.bits, []⟩ := by
    have hne : n.bits ≠ [] := by
      intro he
      have hv := value_bits n
      rw [he] at hv
      simp only [value] at hv
      omega
    simp [Runs, advance, step, ready, BinaryDivisionMachine.initial, hne]
    cases hb : n.bits with
    | nil => exact (hne hb).elim
    | cons b bs => rfl
  have h1 : Runs ⟨.dividing, BinaryDivisionMachine.initial m.bits n.bits, []⟩ k ⟨.clearQ, d0, []⟩ := by
    simpa only [hdiv, d0] using hforward
  have h2 : Runs ⟨.clearQ, d0, []⟩ ((m / n).bits.length + 1) ⟨.dToTmp, d1, []⟩ := by
    simpa [d0, d1, BinaryDivisionMachine.terminal] using clearQ_run d0 (m / n).bits
  have h3 : Runs ⟨.dToTmp, d1, []⟩ (n.bits.length + 1) ⟨.tmpToX, d2, n.bits.reverse⟩ := by
    simpa [d0, d1, d2, BinaryDivisionMachine.terminal] using dToTmp_run d1 n.bits []
  have h4 : Runs ⟨.tmpToX, d2, n.bits.reverse⟩ (n.bits.length + 1) ⟨.rToTmp, d3, []⟩ := by
    simpa [d0, d1, d2, d3, BinaryDivisionMachine.terminal] using tmpToX_run d2 n.bits.reverse
  have h5 : Runs ⟨.rToTmp, d3, []⟩ ((m % n).bits.length + 1) ⟨.tmpToD, d4, (m % n).bits.reverse⟩ := by
    simpa [d0, d1, d2, d3, d4, BinaryDivisionMachine.terminal] using rToTmp_run d3 (m % n).bits []
  have h6 : Runs ⟨.tmpToD, d4, (m % n).bits.reverse⟩ ((m % n).bits.length + 1) ⟨.restart, d5, []⟩ := by
    simpa [d0, d1, d2, d3, d4, d5, BinaryDivisionMachine.terminal] using tmpToD_run d4 (m % n).bits.reverse
  have h7 : Runs ⟨.restart, d5, []⟩ 1 (ready n.bits (m % n).bits) := rfl
  have hw := ((((((h0.trans h1).trans h2).trans h3).trans h4).trans h5).trans h6).trans h7
  refine ⟨_, ?_, hw⟩
  have hq := Nat.size_le_size (Nat.div_le_self m n)
  have hr := Nat.size_le_size (Nat.le_of_lt (Nat.mod_lt m hn))
  simp only [Nat.size_eq_bits_len] at hnd ⊢
  nlinarith

theorem gcd_run (m n : ℕ) :
    ∃ steps, steps ≤ 40 * rounds m n * (m.size + n.size + 1) ^ 2 + 1 ∧
      Runs (ready m.bits n.bits) steps (terminal (Nat.gcd m n).bits) := by
  by_cases hn : n = 0
  · subst n
    exact ⟨1, by simp [rounds_zero], by simp [Runs, advance, step, ready, terminal,
      BinaryDivisionMachine.initial]⟩
  · have hp : 0 < n := Nat.pos_of_ne_zero hn
    obtain ⟨k, hk, hstep⟩ := gcd_iteration m n hp
    obtain ⟨s, hs, he⟩ := gcd_run n (m % n)
    have hsize := Nat.size_le_size (Nat.mod_le m n)
    have hsum : n.size + (m % n).size + 1 ≤ m.size + n.size + 1 := by omega
    have hsquare := Nat.pow_le_pow_left hsum 2
    have hprod := Nat.mul_le_mul_left (40 * rounds n (m % n)) hsquare
    refine ⟨k + s, ?_, ?_⟩
    · rw [rounds_step m n hp]
      nlinarith
    · simpa only [gcd_step m n] using hstep.trans he
termination_by n
decreasing_by exact Nat.mod_lt m (Nat.pos_of_ne_zero hn)

/-- The actual Euclidean stack machine terminates with canonical gcd output.
The cubic bound follows from the proved binary-division execution and the
linearly bounded Euclidean schedule. -/
theorem binary_gcd_machine (m n : ℕ) :
    ∃ steps, (advance steps (ready m.bits n.bits)).phase = .halt ∧
      (advance steps (ready m.bits n.bits)).div.source = (Nat.gcd m n).bits ∧
      bitSteps steps (ready m.bits n.bits) ≤ 400 * (m.size + n.size + 1) ^ 3 := by
  obtain ⟨steps, hs, he⟩ := gcd_run m n
  refine ⟨steps, ?_, ?_, ?_⟩
  · rw [show advance steps (ready m.bits n.bits) = _ from he]
    rfl
  · rw [show advance steps (ready m.bits n.bits) = _ from he]
    rfl
  · have hc := bitSteps_le steps (ready m.bits n.bits)
    have hr := rounds_bound m n
    have hprod := Nat.mul_le_mul_right ((m.size + n.size + 1) ^ 2) (Nat.mul_le_mul_left 40 hr)
    nlinarith [Nat.one_le_pow 3 (m.size + n.size + 1) (by omega)]

end IdentityTesting.BinaryGcdMachine
