import IdentityTesting

#check IdentityTesting.countable_characterization
#check IdentityTesting.countable_characterization_realScale
#print IdentityTesting.CountableCharacterization
#print IdentityTesting.complexityScale
#check IdentityTesting.complexityScale_ge_one
#check IdentityTesting.roundedScale_le_twice_complexityScale
#check IdentityTesting.RationalComputation.rationalComplexityInterval_spec
#check IdentityTesting.RationalComputation.rationalComplexityInterval_positive_spec
#print IdentityTesting.RationalComputation.ScaleIntervalValid
#print IdentityTesting.RationalComputation.RootIntervalValid
#print IdentityTesting.RationalComputation.rationalComplexityInterval
#check IdentityTesting.point_reference_exact_minimum
#check IdentityTesting.finite_small_overlap_exact_minimum
#check IdentityTesting.MomentTesting.hasIdentityTest_moment_of_finite_support_sharp

#print axioms IdentityTesting.countable_characterization
#print axioms IdentityTesting.countable_characterization_realScale
#print axioms IdentityTesting.complexityScale_ge_one
#print axioms IdentityTesting.roundedScale_le_twice_complexityScale
#print axioms IdentityTesting.RationalComputation.rationalComplexityInterval_spec
#print axioms IdentityTesting.RationalComputation.rationalComplexityInterval_positive_spec
#print axioms IdentityTesting.RationalComputation.rationalComplexityInterval_at_one
#print axioms IdentityTesting.point_reference_exact_minimum
#print axioms IdentityTesting.finite_small_overlap_exact_minimum
#print axioms IdentityTesting.MomentTesting.hasIdentityTest_moment_of_finite_support_sharp

open IdentityTesting.RationalComputation in
#eval rationalComplexityInterval (k := 0) (fun _ => (1 : ℚ)) 1
open IdentityTesting.RationalComputation in
#eval rationalComplexityInterval (k := 0) (fun _ => (1 : ℚ)) (1 / 2)
open IdentityTesting.RationalComputation in
#eval rationalComplexityInterval (k := 1) ![(1 : ℚ) / 2, 1 / 2] (1 / 2)
open IdentityTesting.RationalComputation in
#eval rationalComplexityInterval (k := 1) ![(1 : ℚ) / 2, 1 / 2] (9 / 10)
open IdentityTesting.RationalComputation in
#eval rationalComplexityInterval (k := 1) ![(7 : ℚ) / 8, 1 / 8] (1 / 8)
open IdentityTesting.RationalComputation in
#eval rationalComplexityInterval (k := 1) ![(7 : ℚ) / 8, 1 / 8] (1 / 2)
open IdentityTesting.RationalComputation in
#eval rationalComplexityInterval (k := 1) ![(1 : ℚ) / 8, 7 / 8] (1 / 8)
