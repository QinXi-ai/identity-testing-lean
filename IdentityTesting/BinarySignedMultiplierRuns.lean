import IdentityTesting.BinarySignedMultiplier

namespace IdentityTesting.BinarySignedMultiplier
open BinaryArithmetic BinarySignedWords

private theorem mul_halt (k : ℕ) (a : BinaryMultiplierMachine.State) (h : a.phase = .halt) :
    BinaryMultiplierMachine.advance k a = a := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [BinaryMultiplierMachine.advance, BinaryMultiplierMachine.step, h] using ih

private theorem norm_halt (k : ℕ) (a : BinaryWordNormalization.State) (h : a.phase = .halt) :
    BinaryWordNormalization.advance k a = a := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [BinaryWordNormalization.advance, BinaryWordNormalization.step, h] using ih

theorem forward_mul (a b sg : Bool) (m : BinaryMultiplierMachine.State)
    (n : BinaryWordNormalization.State) (tmp : List Bool) (k : ℕ)
    (h : (BinaryMultiplierMachine.advance k m).phase = .halt) :
    ∃ j, j ≤ k + 1 ∧ Runs ⟨.multiplying, a, b, sg, m, n, tmp⟩ j
      ⟨.outToTmp, a, b, sg, BinaryMultiplierMachine.advance k m, n, tmp⟩ := by
  induction k generalizing m with
  | zero =>
      refine ⟨1, by omega, ?_⟩
      simp only [BinaryMultiplierMachine.advance] at h
      simp [Runs, advance, step, h, BinaryMultiplierMachine.advance]
  | succ k ih =>
      by_cases hh : m.phase = .halt
      · refine ⟨1, by omega, ?_⟩
        rw [mul_halt (k + 1) m hh]
        simp [Runs, advance, step, hh]
      · obtain ⟨j, hj, he⟩ := ih (BinaryMultiplierMachine.step m) h
        refine ⟨j + 1, by omega, ?_⟩
        dsimp [Runs] at *
        rw [advance]
        simpa [step, hh, BinaryMultiplierMachine.advance] using he

theorem forward_norm (a b sg : Bool) (m : BinaryMultiplierMachine.State)
    (n : BinaryWordNormalization.State) (tmp : List Bool) (k : ℕ)
    (h : (BinaryWordNormalization.advance k n).phase = .halt) :
    ∃ j, j ≤ k + 1 ∧ Runs ⟨.normalizing, a, b, sg, m, n, tmp⟩ j
      ⟨.finish, a, b, sg, m, BinaryWordNormalization.advance k n, tmp⟩ := by
  induction k generalizing n with
  | zero =>
      refine ⟨1, by omega, ?_⟩
      simp only [BinaryWordNormalization.advance] at h
      simp [Runs, advance, step, h, BinaryWordNormalization.advance]
  | succ k ih =>
      by_cases hh : n.phase = .halt
      · refine ⟨1, by omega, ?_⟩
        rw [norm_halt (k + 1) n hh]
        simp [Runs, advance, step, hh]
      · obtain ⟨j, hj, he⟩ := ih (BinaryWordNormalization.step n) h
        refine ⟨j + 1, by omega, ?_⟩
        dsimp [Runs] at *
        rw [advance]
        simpa [step, hh, BinaryWordNormalization.advance] using he

theorem outToTmp_run (a b sg : Bool) (m : BinaryMultiplierMachine.State)
    (n : BinaryWordNormalization.State) (xs tmp : List Bool) :
    Runs ⟨.outToTmp, a, b, sg, { m with acc := xs }, n, tmp⟩ (xs.length + 1)
      ⟨.tmpToNorm, a, b, sg, { m with acc := [] }, n, xs.reverse ++ tmp⟩ := by
  induction xs generalizing tmp with
  | nil => rfl
  | cons b' xs ih =>
      change advance (xs.length + 1 + 1) _ = _
      rw [advance]
      change advance (xs.length + 1)
        ⟨.outToTmp, a, b, sg, { m with acc := xs }, n, b' :: tmp⟩ = _
      rw [show advance (xs.length + 1) _ = _ from ih (b' :: tmp)]
      simp [List.reverse_cons, List.append_assoc]

theorem tmpToNorm_run (a b sg : Bool) (m : BinaryMultiplierMachine.State)
    (n : BinaryWordNormalization.State) (tmp : List Bool) :
    Runs ⟨.tmpToNorm, a, b, sg, m, n, tmp⟩ (tmp.length + 1)
      ⟨.normalizing, a, b, sg, m, { n with source := tmp.reverse ++ n.source }, []⟩ := by
  induction tmp generalizing n with
  | nil => cases n; rfl
  | cons b' xs ih =>
      change advance (xs.length + 1 + 1) _ = _
      rw [advance]
      change advance (xs.length + 1)
        ⟨.tmpToNorm, a, b, sg, m, { n with source := b' :: n.source }, xs⟩ = _
      rw [show advance (xs.length + 1) _ = _ from ih { n with source := b' :: n.source }]
      simp [List.reverse_cons, List.append_assoc]

theorem productAcc_length (xs ys acc : List Bool) (h : acc.length ≤ ys.length) :
    (BinaryMultiplierMachine.productAcc xs ys acc).length ≤ xs.length + ys.length := by
  induction xs generalizing ys acc with
  | nil => simpa [BinaryMultiplierMachine.productAcc] using h
  | cons b xs ih =>
      have h' : (if b then (BinaryArithmetic.add ys acc false).value else acc).length ≤
          (false :: ys).length := by
        cases b
        · simp; omega
        · simpa [max_eq_left h] using BinaryArithmetic.add_length ys acc false
      have hi := ih (false :: ys) _ h'
      simpa [BinaryMultiplierMachine.productAcc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hi

theorem run_signed_product (a b : Bool) (xs ys : List Bool) :
    ∃ steps, steps ≤ 20 * xs.length * (xs.length + ys.length + 1) +
        4 * (xs.length + ys.length) + 9 ∧
      (advance steps (initial a b xs ys)).phase = .halt ∧
      (output (advance steps (initial a b xs ys))).magnitude = (value xs * value ys).bits ∧
      (output (advance steps (initial a b xs ys))).value =
        signedValue a (value xs) * signedValue b (value ys) := by
  let sg := xor a b
  let norm : BinaryWordNormalization.State := ⟨.collect, [], [], []⟩
  let m0 := BinaryMultiplierMachine.ready xs ys [] { carry := false }
  let z := BinaryMultiplierMachine.productAcc xs ys []
  obtain ⟨k, r, shifted, hk, hm⟩ := BinaryMultiplierMachine.run_product xs ys [] { carry := false } (by simp)
  let mf := BinaryMultiplierMachine.terminal shifted z r
  have hm' : BinaryMultiplierMachine.advance k m0 = mf := hm
  obtain ⟨j, hj, hjr⟩ := forward_mul a b sg m0 norm [] k (by rw [hm']; rfl)
  rw [hm'] at hjr
  have h0 : Runs (initial a b xs ys) 1 ⟨.multiplying, a, b, sg, m0, norm, []⟩ := rfl
  have h1 : Runs ⟨.outToTmp, a, b, sg, mf, norm, []⟩ (z.length + 1)
      ⟨.tmpToNorm, a, b, sg, { mf with acc := [] }, norm, z.reverse⟩ := by
    simpa [mf, BinaryMultiplierMachine.terminal] using outToTmp_run a b sg mf norm z []
  have h2 : Runs ⟨.tmpToNorm, a, b, sg, { mf with acc := [] }, norm, z.reverse⟩
      (z.length + 1) ⟨.normalizing, a, b, sg, { mf with acc := [] }, ⟨.collect, z, [], []⟩, []⟩ := by
    simpa [norm] using tmpToNorm_run a b sg { mf with acc := [] } norm z.reverse
  have hn := BinaryWordNormalization.normalization_run z
  obtain ⟨l, hl, hlr⟩ := forward_norm a b sg { mf with acc := [] }
    ⟨.collect, z, [], []⟩ [] (2 * z.length + 2) (by rw [hn])
  rw [hn] at hlr
  have hf : Runs ⟨.finish, a, b, sg, { mf with acc := [] },
      ⟨.halt, [], [], BinaryWordNormalization.trim z⟩, []⟩ 1
      ⟨.halt, a, b, (if BinaryWordNormalization.trim z = [] then false else sg),
        { mf with acc := [] }, ⟨.halt, [], [], BinaryWordNormalization.trim z⟩, []⟩ := rfl
  have hr := ((((h0.trans hjr).trans h1).trans h2).trans hlr).trans hf
  have hz : z.length ≤ xs.length + ys.length := productAcc_length xs ys [] (by simp)
  have hv : value z = value xs * value ys := by
    simpa [z, value] using BinaryMultiplierMachine.productAcc_correct xs ys []
  refine ⟨1 + j + (z.length + 1) + (z.length + 1) + l + 1, by omega, ?_, ?_, ?_⟩
  · change (advance _ _).phase = _
    rw [hr]
  · change (advance _ _).norm.out = _
    rw [hr]
    exact (BinaryWordNormalization.trim_eq_bits z).trans (congrArg Nat.bits hv)
  · change signedValue (advance _ _).negative (value (advance _ _).norm.out) = _
    rw [hr]
    simp only
    rw [clear_zero_sign, BinaryWordNormalization.trim_value, hv, signedValue_mul]

theorem binary_signed_multiplication_machine (x y : ℤ) :
    ∃ steps, let s := initial (encode x).negative (encode y).negative (encode x).magnitude (encode y).magnitude
      (advance steps s).phase = .halt ∧ (output (advance steps s)).value = x * y ∧
      (output (advance steps s)).magnitude = (x.natAbs * y.natAbs).bits ∧
      bitSteps steps s ≤ 200 * (x.natAbs.size + y.natAbs.size + 1)^2 := by
  obtain ⟨steps, hs, hh, hm, hv⟩ := run_signed_product (encode x).negative (encode y).negative
    (encode x).magnitude (encode y).magnitude
  refine ⟨steps, hh, ?_, ?_, ?_⟩
  · simpa [encode, value_bits, signedValue_int] using hv
  · simpa [encode, value_bits] using hm
  · have hb := bitSteps_le steps (initial (encode x).negative (encode y).negative
        (encode x).magnitude (encode y).magnitude)
    simp only [encode, Nat.size_eq_bits_len] at hs
    nlinarith

theorem run_signed_product_canonical (a b : Bool) (xs ys : List Bool) :
    ∃ steps, steps ≤ 20 * xs.length * (xs.length + ys.length + 1) +
        4 * (xs.length + ys.length) + 9 ∧
      (advance steps (initial a b xs ys)).phase = .halt ∧
      (output (advance steps (initial a b xs ys))).magnitude =
        (signedValue a (value xs) * signedValue b (value ys)).natAbs.bits := by
  obtain ⟨steps, hs, hh, hm, hv⟩ := run_signed_product a b xs ys
  refine ⟨steps, hs, hh, ?_⟩
  rw [hm, Int.natAbs_mul]
  cases a <;> cases b <;> simp [signedValue]

end IdentityTesting.BinarySignedMultiplier
