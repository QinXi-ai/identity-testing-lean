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

#print IdentityTesting.minimumSampleComplexity
#check IdentityTesting.allocationD_mass_scale
#print axioms IdentityTesting.allocationD_mass_scale
#check IdentityTesting.equal_block_budget_isGreatest
#print axioms IdentityTesting.equal_block_budget_isGreatest
#check IdentityTesting.allocation_maximizer_equal_block_contribution
#print axioms IdentityTesting.allocation_maximizer_equal_block_contribution
#check IdentityTesting.uniform_allocationD
#print axioms IdentityTesting.uniform_allocationD
#check IdentityTesting.uniform_allocationRoot
#print axioms IdentityTesting.uniform_allocationRoot
#check IdentityTesting.uniform_overlapMoment_eq_one
#print axioms IdentityTesting.uniform_overlapMoment_eq_one
#check IdentityTesting.uniform_allocationRoot_near_endpoint
#print axioms IdentityTesting.uniform_allocationRoot_near_endpoint
#check IdentityTesting.uniform_allocationRoot_factorization
#print axioms IdentityTesting.uniform_allocationRoot_factorization
#check IdentityTesting.uniform_allocationRoot_away_endpoint
#print axioms IdentityTesting.uniform_allocationRoot_away_endpoint
#check IdentityTesting.uniform_testing_characterization
#print axioms IdentityTesting.uniform_testing_characterization
#check IdentityTesting.uniform_testing_characterization_near_endpoint
#print axioms IdentityTesting.uniform_testing_characterization_near_endpoint
#check IdentityTesting.flatTail_allocationD
#print axioms IdentityTesting.flatTail_allocationD
#check IdentityTesting.flatTail_boundary_root_equation
#print axioms IdentityTesting.flatTail_boundary_root_equation
#check IdentityTesting.quarter_power_deficit_bounds
#print axioms IdentityTesting.quarter_power_deficit_bounds
#check IdentityTesting.flat_tail_scalar_root_bounds
#print axioms IdentityTesting.flat_tail_scalar_root_bounds
#check IdentityTesting.flatTail_boundary_heavyRoot_bounds
#print axioms IdentityTesting.flatTail_boundary_heavyRoot_bounds
#check IdentityTesting.flatTail_exterior_scale_bounds
#print axioms IdentityTesting.flatTail_exterior_scale_bounds
#check IdentityTesting.flatTail_testing_characterization_boundary
#print axioms IdentityTesting.flatTail_testing_characterization_boundary
#check IdentityTesting.flatTail_testing_characterization_exterior
#print axioms IdentityTesting.flatTail_testing_characterization_exterior
#check IdentityTesting.minimumSampleComplexity_isLeast
#print axioms IdentityTesting.minimumSampleComplexity_isLeast
#check IdentityTesting.minimumSampleComplexity_at_one
#print axioms IdentityTesting.minimumSampleComplexity_at_one
#check IdentityTesting.minimumSampleComplexity_point_reference
#print axioms IdentityTesting.minimumSampleComplexity_point_reference
#check IdentityTesting.minimumSampleComplexity_pos
#print axioms IdentityTesting.minimumSampleComplexity_pos
#check IdentityTesting.minimumSampleComplexity_characterization
#print axioms IdentityTesting.minimumSampleComplexity_characterization

#check IdentityTesting.summable_allocation_positive_roots
#print axioms IdentityTesting.summable_allocation_positive_roots
#check IdentityTesting.generalAllocationRoot_tendsto_on_compacts
#print axioms IdentityTesting.generalAllocationRoot_tendsto_on_compacts
#check IdentityTesting.generalHeavyRoot_tendsto_on_compacts
#print axioms IdentityTesting.generalHeavyRoot_tendsto_on_compacts
#check IdentityTesting.sqrt_countTerm_tendstoUniformlyOn_Icc
#print axioms IdentityTesting.sqrt_countTerm_tendstoUniformlyOn_Icc
#check IdentityTesting.GeneralSignedMatrix.signed_likelihood_matrix_totalVariation
#print axioms IdentityTesting.GeneralSignedMatrix.signed_likelihood_matrix_totalVariation
#check IdentityTesting.GeneralSignedMatrix.likelihoodMatrix_frobenius_head_tail
#print axioms IdentityTesting.GeneralSignedMatrix.likelihoodMatrix_frobenius_head_tail
#check IdentityTesting.GeneralSignedMatrix.allocation_likelihoodMatrix_frobenius_bound
#print axioms IdentityTesting.GeneralSignedMatrix.allocation_likelihoodMatrix_frobenius_bound
#check IdentityTesting.GeneralSignedMatrix.allocation_heavy_signed_error
#print axioms IdentityTesting.GeneralSignedMatrix.allocation_heavy_signed_error
#check IdentityTesting.BinaryAdderMachine.binary_addition_machine
#print axioms IdentityTesting.BinaryAdderMachine.binary_addition_machine
#check IdentityTesting.BinaryMultiplierMachine.binary_multiplication_machine
#print axioms IdentityTesting.BinaryMultiplierMachine.binary_multiplication_machine
#check IdentityTesting.RationalComputation.rationalAllocationRoot_oracleInputLength_le
#print axioms IdentityTesting.RationalComputation.rationalAllocationRoot_oracleInputLength_le
#check IdentityTesting.RationalComputation.heavyRootOracle_oracleInputLength_le
#print axioms IdentityTesting.RationalComputation.heavyRootOracle_oracleInputLength_le
#check IdentityTesting.RationalComputation.sqrtInterval_encoding_le
#print axioms IdentityTesting.RationalComputation.sqrtInterval_encoding_le
#check IdentityTesting.RationalComputation.rationalMomentInterval_encoding_le
#print axioms IdentityTesting.RationalComputation.rationalMomentInterval_encoding_le
#check IdentityTesting.RationalComputation.rationalComplexityInterval_encoding_le
#print axioms IdentityTesting.RationalComputation.rationalComplexityInterval_encoding_le

#check IdentityTesting.allocationObjective_strictConcaveOn
#print axioms IdentityTesting.allocationObjective_strictConcaveOn
#check IdentityTesting.allocation_summand_explicit_derivatives
#print axioms IdentityTesting.allocation_summand_explicit_derivatives
