import IdentityTesting.RationalExpressionOperands
import IdentityTesting.RationalOraclePreparationExpressions
import IdentityTesting.RationalAlgorithmTraceVectorBounds

/-! Compositional subexpression bounds, with a polynomial bound for long sums. -/
namespace IdentityTesting.RationalComputation
local notation "L" => rationalEncodingLength

theorem RationalExpr.ValuesBound.binary {a b : RationalExpr} {s : RationalRegisters}
    {A B : ℕ} (ha : a.ValuesBound s A) (hb : b.ValuesBound s B) (op : RationalOp) :
    (RationalExpr.binary op a b).ValuesBound s (2 * (A + B) + 3) := by
  have hla := ha.eval_le
  have hlb := hb.eval_le
  have hz : L 0 = 2 := by norm_num [rationalEncodingLength, numeratorBits, denominatorBits]
  have ho : L 1 = 3 := by norm_num [rationalEncodingLength, numeratorBits, denominatorBits]
  refine ⟨?_, ha.mono (by omega), hb.mono (by omega)⟩
  cases op <;> simp only [RationalOp.eval]
  · omega
  · have := rational_add_encoding (a.eval s) (b.eval s); omega
  · have := rational_sub_encoding (a.eval s) (b.eval s); omega
  · have := rational_mul_encoding (a.eval s) (b.eval s); omega
  · have := rational_div_encoding_le (a.eval s) (b.eval s); omega
  · split <;> omega

theorem RationalExpr.ValuesBound.minimum {a b : RationalExpr} {s : RationalRegisters}
    {A B : ℕ} (ha : a.ValuesBound s A) (hb : b.ValuesBound s B) :
    (RationalExpr.minimum a b).ValuesBound s (2 * (A + B) + 3) := by
  refine ⟨?_, ha.mono (by omega), hb.mono (by omega)⟩
  rcases le_total (a.eval s) (b.eval s) with h | h
  · rw [min_eq_left h]; exact ha.eval_le.trans (by omega)
  · rw [min_eq_right h]; exact hb.eval_le.trans (by omega)

theorem RationalExpr.ValuesBound.add {a b : RationalExpr} {s : RationalRegisters}
    {A B : ℕ} (ha : a.ValuesBound s A) (hb : b.ValuesBound s B) :
    (a.add b).ValuesBound s (2 * (A + B) + 3) := ha.binary hb .add

theorem RationalExpr.ValuesBound.sub {a b : RationalExpr} {s : RationalRegisters}
    {A B : ℕ} (ha : a.ValuesBound s A) (hb : b.ValuesBound s B) :
    (a.sub b).ValuesBound s (2 * (A + B) + 3) := ha.binary hb .sub

theorem RationalExpr.ValuesBound.mul {a b : RationalExpr} {s : RationalRegisters}
    {A B : ℕ} (ha : a.ValuesBound s A) (hb : b.ValuesBound s B) :
    (a.mul b).ValuesBound s (2 * (A + B) + 3) := ha.binary hb .mul

theorem RationalExpr.ValuesBound.div {a b : RationalExpr} {s : RationalRegisters}
    {A B : ℕ} (ha : a.ValuesBound s A) (hb : b.ValuesBound s B) :
    (a.div b).ValuesBound s (2 * (A + B) + 3) := ha.binary hb .div

theorem RationalExpr.ValuesBound.square {a : RationalExpr} {s : RationalRegisters}
    {A : ℕ} (ha : a.ValuesBound s A) :
    a.square.ValuesBound s (4 * A + 3) := by
  have h := ha.mul ha
  have he : 2 * (A + A) + 3 = 4 * A + 3 := by omega
  rw [he] at h
  exact h

theorem RationalExpr.sum_valuesBound (es : List RationalExpr) (s : RationalRegisters) (B : ℕ)
    (h : ∀ e ∈ es, e.ValuesBound s B) :
    (RationalExpr.sum es).ValuesBound s (2 * (es.length + 1) * (B + 2)) := by
  induction es with
  | nil =>
    simp only [sum, List.foldr_nil, literal, ValuesBound, RationalOperand.read, List.length_nil]
    norm_num [rationalEncodingLength, numeratorBits, denominatorBits]
    omega
  | cons e es ih =>
    have he := h e (by simp)
    have ht := ih (fun f hf => h f (by simp [hf]))
    have hroot := rational_list_sum_encoding_of_bound (e :: es) (RationalExpr.eval s) B
      (fun f hf => (h f hf).eval_le)
    have hsum : L ((RationalExpr.sum (e :: es)).eval s) ≤ 2 * (e :: es).length * B + 3 := by
      simpa only [RationalExpr.eval_sum] using hroot
    change L ((RationalExpr.sum (e :: es)).eval s) ≤ _ ∧ _
    refine ⟨by simp only [List.length_cons] at *; nlinarith, ?_, ?_⟩
    · exact he.mono (by simp only [List.length_cons]; nlinarith)
    · exact ht.mono (by simp only [List.length_cons]; nlinarith)

end IdentityTesting.RationalComputation
