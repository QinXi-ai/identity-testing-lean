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

open IdentityTesting.RationalComputation

#print rationalEncodingLength
#check rational_div_encoding_le
#check rational_sum_encoding
#check oracleDyadicPrecision_encoding_le
#check coordinateInterval_dyadic_grid
#check coordinateInterval_step
#check coordinateInterval_encoding_le
#check coordinateQuery_polynomial_encoding_le
#check coordinateInterval_precision_encoding_le
#check oracleCoordinateInterval_encoding_le
#check rationalAllocationCost_encoding_le
#check oracleObjectiveInterval_encoding_le
#check oracleBudgetInterval_encoding_le

#print axioms rational_fraction_reduction_bounds
#print axioms rational_div_encoding_le
#print axioms rational_sum_encoding
#print axioms oracleDyadicPrecision_encoding_le
#print axioms coordinateInterval_dyadic_grid
#print axioms coordinateInterval_step
#print axioms coordinateInterval_encoding_le
#print axioms coordinateQuery_polynomial_encoding_le
#print axioms coordinateInterval_precision_encoding_le
#print axioms oracleCoordinateInterval_encoding_le
#print axioms rationalAllocationCost_encoding_le
#print axioms oracleObjectiveInterval_encoding_le
#print axioms oracleBudgetInterval_encoding_le

#eval let I := coordinateInterval (1 / 2) 1 32
      (rationalEncodingLength I.1, rationalEncodingLength I.2,
        rationalEncodingLength (coordinateQuery (1 / 2) 1 32))
#eval let I := oracleBudgetInterval ![(1 : ℚ) / 2, 1 / 2] 1 1 (1 / 128) 16
      (rationalEncodingLength I.1, rationalEncodingLength I.2)

#print allocationOracleInputLength
#check allocationOracle_eq_boundedPrecision
#check allocationOracle_output_encoding_le
#check allocationOracleWithTrace_result
#check allocationOracleWithTrace_length
#check allocationOracleWithTrace_encoding_le
#check allocationOracleBudget_encoding_le
#check allocationOracle_coordinate_polynomial_encoding_le
#print axioms allocationOracle_eq_boundedPrecision
#print axioms allocationOracle_output_encoding_le
#print axioms allocationOracleWithTrace_result
#print axioms allocationOracleWithTrace_length
#print axioms allocationOracleWithTrace_encoding_le
#print axioms allocationOracleBudget_encoding_le
#print axioms allocationOracle_coordinate_polynomial_encoding_le

#check IdentityTesting.overlapMoment_summand_abs_sub_le
#check IdentityTesting.overlapMoment_sum_abs_sub_le
#check IdentityTesting.overlapMoment_sum_tendsto_l1_targets
#check IdentityTesting.overlapMoment_tendsto_l1_targets
#check IdentityTesting.countable_relabeling_functionals
#print axioms IdentityTesting.overlapMoment_summand_abs_sub_le
#print axioms IdentityTesting.overlapMoment_sum_abs_sub_le
#print axioms IdentityTesting.overlapMoment_sum_tendsto_l1_targets
#print axioms IdentityTesting.overlapMoment_tendsto_l1_targets
#print axioms IdentityTesting.countable_relabeling_functionals

#eval let a : Fin 1 → ℚ := fun _ => 1
      let r := allocationOracleWithTrace a 1 (1 / 2)
      (allocationOracleInputLength a 1 (1 / 2), r.2.length,
        (r.2.map rationalEncodingLength).foldl max 0,
        r.1 == allocationOracle a 1 (1 / 2))
