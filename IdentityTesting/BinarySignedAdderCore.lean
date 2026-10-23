import IdentityTesting.BinarySignedAdderPreparation
import IdentityTesting.BinarySignedArithmeticLemmas

namespace IdentityTesting.BinarySignedAdder
open BinaryArithmetic BinarySignedWords

theorem run_add_same (s : State) (xs ys : List Bool) (hsg : s.negativeLeft = s.negativeRight) :
    ∃ j r, j ≤ 10 * max xs.length ys.length + 5 ∧
      Runs { s with phase := .arithmetic, arith := BinaryAdderMachine.loopState xs ys { carry := false } [] } j
        { s with phase := .outCollect, arith := BinaryAdderMachine.haltState r (BinaryArithmetic.add xs ys false).value } := by
  obtain ⟨k,r,hk,hr⟩ := BinaryAdderMachine.run_add xs ys { carry := false } []
  simp only [List.length_nil, Nat.add_zero, List.reverse_nil, List.nil_append] at hk hr
  obtain ⟨j,hj,hjr⟩ := forward_add s (BinaryAdderMachine.loopState xs ys { carry := false } []) k hsg
    (by rw [hr]; rfl)
  rw [hr] at hjr
  exact ⟨j,r,by omega,hjr⟩

theorem run_sub_different (s : State) (xs ys : List Bool) (hsg : s.negativeLeft ≠ s.negativeRight) :
    ∃ j r, j ≤ 10 * max xs.length ys.length + 4 ∧
      Runs { s with phase := .arithmetic, arith := BinaryAdderMachine.loopState xs ys { carry := false } [] } j
        { s with phase := .outCollect, arith := BinaryAdderMachine.haltState r (BinarySubtraction.subtract xs ys false).1 } := by
  obtain ⟨k,r,hk,hr,hb⟩ := BinarySubtractorMachine.run_subtract xs ys { carry := false } []
  simp only [List.length_nil, Nat.add_zero, List.reverse_nil, List.nil_append] at hk hr
  obtain ⟨j,hj,hjr⟩ := forward_sub s (BinaryAdderMachine.loopState xs ys { carry := false } []) k hsg
    (by rw [hr]; rfl)
  rw [hr] at hjr
  exact ⟨j,r,by omega,hjr⟩

theorem run_arithmetic (a b : Bool) (xs ys : List Bool) (c : BinarySignedComparison.State)
    (hc : c.result = true ↔ value xs < value ys) :
    ∃ j r out, j ≤ 10 * max xs.length ys.length + 5 ∧ out.length ≤ max xs.length ys.length + 1 ∧
      signedValue (arithmeticReady a b xs ys c).negative (value out) =
        signedValue a (value xs) + signedValue b (value ys) ∧
      Runs (arithmeticReady a b xs ys c) j
        { (arithmeticReady a b xs ys c) with phase := .outCollect, arith := BinaryAdderMachine.haltState r out } := by
  by_cases hab : a = b
  · subst b
    obtain ⟨j,r,hj,hr⟩ := run_add_same (arithmeticReady a a xs ys c) xs ys rfl
    refine ⟨j,r,(BinaryArithmetic.add xs ys false).value,hj,BinaryArithmetic.add_length xs ys false,?_,?_⟩
    · simp only [add_correct, Bool.toNat_false, Nat.add_zero]
      cases a <;> simp [arithmeticReady, signedValue] <;> ring
    · cases a <;> simpa [arithmeticReady] using hr
  · by_cases hlt : value xs < value ys
    · have hcr : c.result = true := hc.mpr hlt
      obtain ⟨j,r,hj,hr⟩ := run_sub_different (arithmeticReady a b xs ys c) ys xs hab
      refine ⟨j,r,(BinarySubtraction.subtract ys xs false).1,?_,?_,?_,?_⟩
      · rw [max_comm] at hj
        omega
      · rw [BinarySubtraction.subtract_length, max_comm]
        omega
      · rw [(BinarySubtraction.subtract_of_le ys xs (by omega)).2]
        have hv := signedValue_sub_ordered b a (value ys) (value xs) (Ne.symm hab) (by omega)
        cases a <;> cases b <;> simp_all [arithmeticReady, signedValue] <;> omega
      · cases a <;> cases b <;> simp_all [arithmeticReady]
    · have hcr : c.result = false := by
        cases he : c.result
        · rfl
        · exact (hlt (hc.mp he)).elim
      obtain ⟨j,r,hj,hr⟩ := run_sub_different (arithmeticReady a b xs ys c) xs ys hab
      refine ⟨j,r,(BinarySubtraction.subtract xs ys false).1,by omega,?_,?_,?_⟩
      · rw [BinarySubtraction.subtract_length]
        omega
      · rw [(BinarySubtraction.subtract_of_le xs ys (by omega)).2]
        simpa [arithmeticReady, hcr] using signedValue_sub_ordered a b (value xs) (value ys) hab (by omega)
      · simpa [arithmeticReady, hcr] using hr

end IdentityTesting.BinarySignedAdder
