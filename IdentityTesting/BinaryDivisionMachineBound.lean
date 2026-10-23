import IdentityTesting.BinaryDivisionMachineRuns

namespace IdentityTesting.BinaryDivisionMachine
open BinaryArithmetic BinarySubtraction BinaryLongDivision BinaryWordNormalization

theorem digit_iteration (b : Bool) (bs d q r : List Bool) (regs : BinarySubtractorMachine.Registers) :
    ∃ steps regs', steps ≤ 20 * (max (r.length + 1) d.length + 1) ∧
      Runs (ready (b :: bs) d q r regs) steps
        (ready bs d (digit b d q r).1 (digit b d q r).2 regs') := by
  let trial := b :: r
  let a0 := BinarySubtractorMachine.haltState regs []
  let ad := { a0 with right := d }
  let atrial := { ad with left := trial }
  let ai := BinarySubtractorMachine.loopState trial d { carry := false } []
  let z := (subtract trial d false).1
  obtain ⟨n, regs', hn, hsub, hborrow⟩ := BinarySubtractorMachine.run_subtract trial d { carry := false } []
  simp only [List.length_nil, List.reverse_nil, List.nil_append, Nat.add_zero] at hn hsub
  have hh : (BinarySubtractorMachine.advance n ai).phase = .halt := by
    change (BinarySubtractorMachine.advance n
      (BinarySubtractorMachine.loopState trial d { carry := false } [])).phase = .halt
    rw [hsub]
    rfl
  obtain ⟨k, hk, hforward⟩ := forward_sub bs d q trial ai n hh
  have hf : Runs ⟨.subtracting, [], bs, d, [], ai, word q, word trial⟩ k
      ⟨.decide, [], bs, d, [], BinarySubtractorMachine.haltState regs' z, word q, word trial⟩ := by
    simpa only [ai, hsub] using hforward
  have h0 : Runs (ready (b :: bs) d q r regs) 1
      ⟨.dToTmp, [], bs, d, [], a0, word q, word trial⟩ := rfl
  have h1 : Runs ⟨.dToTmp, [], bs, d, [], a0, word q, word trial⟩ (d.length + 1)
      ⟨.tmpToD, [], bs, [], d.reverse, a0, word q, word trial⟩ := by
    simpa only [List.append_nil] using dToTmp_run bs d [] q trial a0
  have h2 : Runs ⟨.tmpToD, [], bs, [], d.reverse, a0, word q, word trial⟩ (d.length + 1)
      ⟨.rToTmp, [], bs, d, [], ad, word q, word trial⟩ := by
    simpa [a0, ad, BinaryAdderMachine.haltState] using tmpToD_run bs [] d.reverse q trial a0
  have h3 : Runs ⟨.rToTmp, [], bs, d, [], ad, word q, word trial⟩ (trial.length + 1)
      ⟨.tmpToR, [], bs, d, trial.reverse, ad, word q, word []⟩ := by
    simpa only [List.append_nil] using rToTmp_run bs d [] q trial ad
  have h4 : Runs ⟨.tmpToR, [], bs, d, trial.reverse, ad, word q, word []⟩ (trial.length + 1)
      ⟨.startSub, [], bs, d, [], atrial, word q, word trial⟩ := by
    simpa [a0, ad, atrial, BinaryAdderMachine.haltState] using tmpToR_run bs d trial.reverse q [] ad
  have h5 : Runs ⟨.startSub, [], bs, d, [], atrial, word q, word trial⟩ 1
      ⟨.subtracting, [], bs, d, [], ai, word q, word trial⟩ := rfl
  have hprefix := (((((h0.trans h1).trans h2).trans h3).trans h4).trans h5).trans hf
  have hz : z.length = max trial.length d.length := subtract_length trial d false
  cases hc : (subtract trial d false).2 with
  | true =>
      have hb : regs'.carry = true := hborrow.trans hc
      have h6 : Runs ⟨.decide, [], bs, d, [], BinarySubtractorMachine.haltState regs' z, word q, word trial⟩ 1
          ⟨.clearDiff, [], bs, d, [], BinarySubtractorMachine.haltState regs' z, word (false :: q), word trial⟩ := by
        simp [Runs, advance, step, BinaryAdderMachine.haltState, hb, word]
      have h7 : Runs ⟨.clearDiff, [], bs, d, [], BinarySubtractorMachine.haltState regs' z, word (false :: q), word trial⟩
          (z.length + 1) (ready bs d (false :: q) trial regs') := by
        simpa [ready, BinaryAdderMachine.haltState] using
          clearDiff_run bs d (false :: q) trial z (BinarySubtractorMachine.haltState regs' [])
      refine ⟨_, regs', ?_, by simpa only [digit, trial, hc, ↓reduceIte] using (hprefix.trans h6).trans h7⟩
      dsimp only [trial] at hn hz ⊢
      simp only [List.length_cons] at hn hz ⊢
      omega
  | false =>
      have hb : regs'.carry = false := hborrow.trans hc
      have h6 : Runs ⟨.decide, [], bs, d, [], BinarySubtractorMachine.haltState regs' z, word q, word trial⟩ 1
          ⟨.clearRem, [], bs, d, [], BinarySubtractorMachine.haltState regs' z, word (true :: q), word trial⟩ := by
        simp [Runs, advance, step, BinaryAdderMachine.haltState, hb, word]
      have h7 := clearRem_run bs d (true :: q) trial (BinarySubtractorMachine.haltState regs' z)
      have h8 : Runs ⟨.diffToTmp, [], bs, d, [], BinarySubtractorMachine.haltState regs' z, word (true :: q), word []⟩
          (z.length + 1) ⟨.tmpToRem, [], bs, d, z.reverse, BinarySubtractorMachine.haltState regs' [], word (true :: q), word []⟩ := by
        simpa [BinaryAdderMachine.haltState] using
          diffToTmp_run bs d [] (true :: q) z (BinarySubtractorMachine.haltState regs' [])
      have h9 : Runs ⟨.tmpToRem, [], bs, d, z.reverse, BinarySubtractorMachine.haltState regs' [], word (true :: q), word []⟩
          (z.length + 1) (ready bs d (true :: q) z regs') := by
        simpa [ready] using tmpToRem_run bs d z.reverse (true :: q) [] (BinarySubtractorMachine.haltState regs' [])
      refine ⟨_, regs', ?_, by simpa only [digit, trial, hc, Bool.false_eq_true, ↓reduceIte] using
          (((hprefix.trans h6).trans h7).trans h8).trans h9⟩
      dsimp only [trial] at hn hz ⊢
      simp only [List.length_cons] at hn hz ⊢
      omega

theorem loop_run (bs d q r : List Bool) (regs : BinarySubtractorMachine.Registers) :
    ∃ n regs', n ≤ 20 * bs.length * (max r.length d.length + bs.length + 2) ∧
      Runs (ready bs d q r regs) n (ready [] d (loop bs d q r).1 (loop bs d q r).2 regs') := by
  induction bs generalizing q r regs with
  | nil => exact ⟨0, regs, by simp, rfl⟩
  | cons b bs ih =>
      obtain ⟨k, rk, hk, hstep⟩ := digit_iteration b bs d q r regs
      obtain ⟨n, rn, hn, hloop⟩ := ih (digit b d q r).1 (digit b d q r).2 rk
      have hlen := (digit_lengths b d q r).2
      have hmax : max (digit b d q r).2.length d.length ≤ max r.length d.length + 1 := by omega
      have htrial : max (r.length + 1) d.length ≤ max r.length d.length + 1 := by omega
      have hprod := Nat.mul_le_mul_left (20 * bs.length)
        (show max (digit b d q r).2.length d.length + bs.length + 2 ≤
          max r.length d.length + (bs.length + 1) + 2 by omega)
      refine ⟨k + n, rn, ?_, hstep.trans hloop⟩
      simp only [List.length_cons]
      nlinarith [le_max_left r.length d.length, le_max_right r.length d.length]

theorem division_run (xs d : List Bool) :
    ∃ n regs, n ≤ 30 * (xs.length + d.length + 1) ^ 2 ∧
      Runs (initial xs d) n (terminal d (divide xs d).1 (divide xs d).2 regs) := by
  have h0 : Runs (initial xs d) (xs.length + 1)
      (ready xs.reverse d [] [] { carry := false }) := by
    simpa only [initial, ready, List.append_nil] using init_run xs [] d
      (BinarySubtractorMachine.haltState { carry := false } []) (word []) (word [])
  obtain ⟨k, regs, hk, hl⟩ := loop_run xs.reverse d [] [] { carry := false }
  obtain ⟨nf, hnf, hf⟩ := finish_run d (loop xs.reverse d [] []).1 (loop xs.reverse d [] []).2 regs
  have hlen := loop_lengths xs.reverse d [] []
  simp only [List.length_reverse, List.length_nil, Nat.zero_add, Nat.max_eq_right (Nat.zero_le _)] at hk hlen
  refine ⟨xs.length + 1 + k + nf, regs, ?_, (h0.trans hl).trans hf⟩
  nlinarith [Nat.mul_self_le_mul_self (Nat.le_add_right xs.length d.length)]

/-- An actual fixed-stack execution returns both canonical binary quotient and
remainder. Cost counts the listed bit actions of every executed transition. -/
theorem binary_division_machine (m n : ℕ) (hn : 0 < n) :
    ∃ steps, (advance steps (initial m.bits n.bits)).phase = .halt ∧
      (advance steps (initial m.bits n.bits)).quot.out = (m / n).bits ∧
      (advance steps (initial m.bits n.bits)).rem.out = (m % n).bits ∧
      bitSteps steps (initial m.bits n.bits) ≤ 210 * (m.size + n.size + 1) ^ 2 := by
  obtain ⟨steps, regs, hs, he⟩ := division_run m.bits n.bits
  have hv := divide_binary_inputs m n hn
  have hq : (divide m.bits n.bits).1 = (m / n).bits := by
    have ht := trim_eq_bits (loop m.bits.reverse n.bits [] []).1
    rw [show value (loop m.bits.reverse n.bits [] []).1 = m / n from by
      simpa only [divide, trim_value] using hv.1] at ht
    exact ht
  have hr : (divide m.bits n.bits).2 = (m % n).bits := by
    have ht := trim_eq_bits (loop m.bits.reverse n.bits [] []).2
    rw [show value (loop m.bits.reverse n.bits [] []).2 = m % n from by
      simpa only [divide, trim_value] using hv.2] at ht
    exact ht
  refine ⟨steps, ?_, ?_, ?_, ?_⟩
  · change (advance steps (initial m.bits n.bits)).phase = .halt
    rw [show advance steps (initial m.bits n.bits) = _ from he]
    rfl
  · rw [show advance steps (initial m.bits n.bits) = _ from he]
    exact hq
  · rw [show advance steps (initial m.bits n.bits) = _ from he]
    exact hr
  · have hc := bitSteps_le steps (initial m.bits n.bits)
    simpa only [Nat.size_eq_bits_len, ← Nat.mul_assoc] using hc.trans (Nat.mul_le_mul_left 7 hs)

end IdentityTesting.BinaryDivisionMachine
