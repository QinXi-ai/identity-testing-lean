import IdentityTesting.CountableMomentApproximation
import IdentityTesting.MomentUpperBound
import IdentityTesting.PoolingTests

/-! The actual finite moment tester, pulled back to the original countable
alphabet after choosing a sufficiently long retained prefix. -/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace IdentityTesting
open FiniteTesting EventCounts MomentTesting

theorem finiteOverlapMoment_pooled_prefix (q : DiscreteLaw) (m : ℕ) (δ : ℝ) :
    finiteOverlapMoment (pooledLaw q (Finset.range m)) δ =
      overlapMoment (prefixPooledLaw q m) δ := by
  classical
  have hs : overlapMoment (prefixPooledLaw q m) δ =
      ∑ i ∈ Finset.range (m + 1), min ((prefixPooledLaw q m).mass i)
        (((prefixPooledLaw q m).mass i) ^ ((3 : ℝ) / 2) / Real.sqrt δ) := by
    unfold overlapMoment
    apply tsum_eq_sum
    intro i hi
    rw [prefixPooledLaw_mass_zero q m i
      (Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hi))]
    norm_num
  rw [hs, Finset.sum_range_succ, prefixPooledLaw_mass_residual]
  rw [finiteOverlapMoment, Fintype.sum_option]
  change min (residualMass q (Finset.range m))
      ((residualMass q (Finset.range m)) ^ ((3 : ℝ) / 2) / Real.sqrt δ) +
    (∑ i : (Finset.range m), min (q.mass i)
      ((q.mass i) ^ ((3 : ℝ) / 2) / Real.sqrt δ)) = _
  rw [← Finset.sum_subtype (Finset.range m) (fun _ => Iff.rfl)
    (fun i => min (q.mass i) ((q.mass i) ^ ((3 : ℝ) / 2) / Real.sqrt δ)), add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [prefixPooledLaw_mass_of_lt q m i (Finset.mem_range.mp hi)]

theorem hasIdentityTest_moment_countable (q : DiscreteLaw) (δ : ℝ)
    (hδ : 0 < δ) (hhead : 2 * δ < largestMass q) :
    ∃ n : ℕ, HasIdentityTest q (1 - δ) n ∧
      (n : ℝ) ≤ 200000000000000 / overlapMoment q δ := by
  classical
  have hgap : 0 < largestMass q / 2 - δ := by linarith
  have hsmall : ∀ᶠ m in atTop,
      residualMass q (Finset.range m) < largestMass q / 2 - δ :=
    (prefixResidual_tendsto_zero q).eventually (gt_mem_nhds hgap)
  have hW : 0 < 1 / overlapMoment q δ := one_div_pos.mpr (overlapMoment_pos q hδ)
  have hlim := overlapMoment_reciprocal_prefixPooled_tendsto q hδ
  have hdouble : 1 / overlapMoment q δ < 2 / overlapMoment q δ := by
    calc
      1 / overlapMoment q δ < 2 * (1 / overlapMoment q δ) := by linarith
      _ = 2 / overlapMoment q δ := by ring
  have hbound : ∀ᶠ m in atTop, 1 / overlapMoment (prefixPooledLaw q m)
      (δ + residualMass q (Finset.range m)) < 2 / overlapMoment q δ :=
    hlim.eventually (gt_mem_nhds hdouble)
  obtain ⟨m, hm, hr, hrecip⟩ :=
    (eventually_gt_atTop (largestIndex q) |>.and (hsmall.and hbound)).exists
  let s := Finset.range m
  let d := δ + residualMass q s
  have hres : 0 ≤ residualMass q s := tsum_nonneg (fun i => q.nonneg i)
  have hd : 0 < d := add_pos_of_pos_of_nonneg hδ hres
  let y : PoolLabel s := some ⟨largestIndex q, Finset.mem_range.mpr hm⟩
  have hy : (pooledLaw q s).mass y = largestMass q := (largestMass_eq_selected q).symm
  have hheadm : 2 * d ≤ largestMass q := by
    dsimp only [d, s]
    linarith
  have hyH : y ∈ heavyLabels (pooledLaw q s) d := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hy]
    linarith
  have hv : 2 * d ≤ eventMass (pooledLaw q s) (heavyLabels (pooledLaw q s) d) := by
    have h := Finset.single_le_sum (s := heavyLabels (pooledLaw q s) d)
      (f := (pooledLaw q s).mass) (fun i _ => (pooledLaw q s).nonneg i) hyH
    rw [hy] at h
    exact hheadm.trans h
  obtain ⟨n, test, hnull, halt, hn⟩ := finite_moment_identity_test (pooledLaw q s) d hd hv
  refine ⟨n, hasIdentityTest_of_pooled_test q s (1 - δ) n test hnull ?_, ?_⟩
  · intro p hp
    apply halt p
    have hrad : 1 - d = (1 - δ) - residualMass q s := by dsimp only [d]; ring
    rwa [hrad]
  · rw [show s = Finset.range m from rfl, finiteOverlapMoment_pooled_prefix] at hn
    calc
      (n : ℝ) ≤ 100000000000000 /
          overlapMoment (prefixPooledLaw q m) (δ + residualMass q (Finset.range m)) := hn
      _ = 100000000000000 * (1 /
          overlapMoment (prefixPooledLaw q m) (δ + residualMass q (Finset.range m))) := by ring
      _ ≤ 100000000000000 * (2 / overlapMoment q δ) :=
        mul_le_mul_of_nonneg_left hrecip.le (by norm_num)
      _ = 200000000000000 / overlapMoment q δ := by ring

end IdentityTesting
