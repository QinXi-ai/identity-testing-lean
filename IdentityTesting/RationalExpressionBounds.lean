import IdentityTesting.RationalExpressionCompiler

/-! Explicit work-register, syntax and call bounds for the expression compiler. -/
namespace IdentityTesting.RationalComputation

def RationalExpr.weight : RationalExpr → ℕ
  | .operand o => o.slots + o.encoding + 1
  | .binary _ a b | .minimum a b => a.weight + b.weight + 1

theorem RationalExpr.weight_pos (e : RationalExpr) : 0 < e.weight := by
  cases e <;> simp only [weight] <;> omega

theorem RationalExpr.inputs_le_weight (e : RationalExpr) : e.inputs ≤ e.weight := by
  induction e <;> simp_all only [inputs, weight] <;> omega

theorem RationalExpr.work_le_weight (e : RationalExpr) : e.work ≤ e.weight := by
  induction e <;> simp_all only [work, weight] <;> omega

theorem RationalExpr.compile_calls (e : RationalExpr) (d : ℕ) :
    (e.compile d).callBound ≤ 2 * e.weight := by
  induction e generalizing d with
  | operand o => simp only [compile, RationalProgram.callBound, weight]; omega
  | binary op a b ha hb =>
    have h1 := ha d
    have h2 := hb (d + 1)
    simp only [compile, RationalProgram.callBound, weight]
    omega
  | minimum a b ha hb =>
    have h1 := ha d
    have h2 := hb (d + 1)
    simp only [compile, RationalProgram.callBound, weight]
    omega

theorem RationalExpr.compile_slots (e : RationalExpr) (d : ℕ) :
    (e.compile d).slots ≤ max e.inputs (d + e.work) := by
  induction e generalizing d with
  | operand o =>
    simp only [compile, RationalProgram.slots, RationalOperand.slots, inputs, work]
    omega
  | binary op a b ha hb =>
    have h1 := ha d
    have h2 := hb (d + 1)
    have hw := b.work_pos
    simp only [compile, RationalProgram.slots, RationalOperand.slots, inputs, work]
    omega
  | minimum a b ha hb =>
    have h1 := ha d
    have h2 := hb (d + 1)
    have hw := b.work_pos
    simp only [compile, RationalProgram.slots, RationalOperand.slots, inputs, work]
    omega

theorem RationalExpr.compile_encoding (e : RationalExpr) (d : ℕ) :
    (e.compile d).encoding ≤ 100 * (d + e.weight + 1) * e.weight := by
  have h0 : rationalEncodingLength 0 = 2 := by
    norm_num [rationalEncodingLength, numeratorBits, denominatorBits]
  induction e generalizing d with
  | operand o =>
    have hd : d.size ≤ d := Nat.size_le.mpr d.lt_two_pow_self
    have hp : 0 < o.slots + o.encoding + 1 := by omega
    simp only [compile, RationalProgram.encoding, RationalOperand.encoding, h0, weight]
    nlinarith
  | binary op a b ha hb =>
    have h1 := ha d
    have h2 := hb (d + 1)
    have hwa := a.weight_pos
    have hwb := b.weight_pos
    have hd : d.size ≤ d := Nat.size_le.mpr d.lt_two_pow_self
    have hd1 : (d + 1).size ≤ d + 1 := Nat.size_le.mpr (d + 1).lt_two_pow_self
    simp only [compile, RationalProgram.encoding, RationalOperand.encoding, weight]
    nlinarith
  | minimum a b ha hb =>
    have h1 := ha d
    have h2 := hb (d + 1)
    have hwa := a.weight_pos
    have hwb := b.weight_pos
    have hd : d.size ≤ d := Nat.size_le.mpr d.lt_two_pow_self
    have hd1 : (d + 1).size ≤ d + 1 := Nat.size_le.mpr (d + 1).lt_two_pow_self
    simp only [compile, RationalProgram.encoding, RationalOperand.encoding, h0, weight]
    nlinarith

end IdentityTesting.RationalComputation
