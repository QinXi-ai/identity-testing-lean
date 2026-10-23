import IdentityTesting.CountableKernels
import IdentityTesting.CountablePooling
import IdentityTesting.Endpoints
import IdentityTesting.FiniteSampleMaps

/-! The reverse pooling kernel samples each fiber using the reference's actual
conditional law. A zero-mass fiber uses a fixed representative in that fiber. -/

noncomputable section
open scoped BigOperators
namespace IdentityTesting
open FiniteTesting

def prefixPoolRepresentative (m : ℕ) (y : PoolLabel (Finset.range m)) : ℕ :=
  match y with
  | none => m
  | some j => j.val

theorem poolMap_prefixPoolRepresentative (m : ℕ) (y : PoolLabel (Finset.range m)) :
    poolMap (Finset.range m) (prefixPoolRepresentative m y) = y := by
  cases y with
  | none => simp [prefixPoolRepresentative, poolMap]
  | some j => exact (poolMap_eq_some _ _ _).mpr rfl

def poolFiberMass (q : DiscreteLaw) (m : ℕ) (y : PoolLabel (Finset.range m)) (i : ℕ) : ℝ :=
  if poolMap (Finset.range m) i = y then q.mass i else 0

theorem poolFiberMass_nonneg (q : DiscreteLaw) (m : ℕ)
    (y : PoolLabel (Finset.range m)) (i : ℕ) : 0 ≤ poolFiberMass q m y i := by
  unfold poolFiberMass
  split_ifs
  · exact q.nonneg i
  · exact le_rfl

theorem poolFiberMass_hasSum (q : DiscreteLaw) (m : ℕ)
    (y : PoolLabel (Finset.range m)) :
    HasSum (poolFiberMass q m y) ((pooledLaw q (Finset.range m)).mass y) := by
  have hs : Summable (poolFiberMass q m y) :=
    Summable.of_nonneg_of_le (poolFiberMass_nonneg q m y)
      (fun i => by unfold poolFiberMass; split_ifs <;> simp [q.nonneg i]) q.summable
  have hv : (∑' i, poolFiberMass q m y i) = (pooledLaw q (Finset.range m)).mass y := by
    rw [pooledLaw_mass_fiber]
    symm
    simpa only [Set.indicator_apply, Set.mem_setOf_eq, poolFiberMass] using
      (tsum_subtype {i | poolMap (Finset.range m) i = y} q.mass)
  rw [← hv]
  exact hs.hasSum

def positivePoolConditional (q : DiscreteLaw) (m : ℕ)
    (y : PoolLabel (Finset.range m))
    (hy : 0 < (pooledLaw q (Finset.range m)).mass y) : DiscreteLaw where
  mass i := poolFiberMass q m y i / (pooledLaw q (Finset.range m)).mass y
  nonneg i := div_nonneg (poolFiberMass_nonneg q m y i) hy.le
  summable := (poolFiberMass_hasSum q m y).summable.div_const _
  total := by
    rw [tsum_div_const, (poolFiberMass_hasSum q m y).tsum_eq, div_self hy.ne']

def unpoolingKernel (q : DiscreteLaw) (m : ℕ)
    (y : PoolLabel (Finset.range m)) : DiscreteLaw :=
  if hy : 0 < (pooledLaw q (Finset.range m)).mass y then
    positivePoolConditional q m y hy
  else pointMass (prefixPoolRepresentative m y)

theorem unpoolingKernel_off_fiber (q : DiscreteLaw) (m : ℕ)
    (y : PoolLabel (Finset.range m)) (i : ℕ)
    (hi : poolMap (Finset.range m) i ≠ y) : (unpoolingKernel q m y).mass i = 0 := by
  unfold unpoolingKernel
  split_ifs with hy
  · simp [positivePoolConditional, poolFiberMass, hi]
  · have hne : i ≠ prefixPoolRepresentative m y := by
      intro h
      exact hi (by simpa only [h] using poolMap_prefixPoolRepresentative m y)
    simp [pointMass, hne]

theorem pool_reference_mass_times_conditional (q : DiscreteLaw) (m : ℕ)
    (y : PoolLabel (Finset.range m)) (i : ℕ) :
    (pooledLaw q (Finset.range m)).mass y * (unpoolingKernel q m y).mass i =
      poolFiberMass q m y i := by
  unfold unpoolingKernel
  split_ifs with hy
  · change _ * (poolFiberMass q m y i / _) = _
    exact mul_div_cancel₀ _ hy.ne'
  · have hz : (pooledLaw q (Finset.range m)).mass y = 0 :=
      le_antisymm (le_of_not_gt hy) ((pooledLaw q (Finset.range m)).nonneg y)
    have hf : poolFiberMass q m y i = 0 := by
      have hle := (poolFiberMass_hasSum q m y).summable.le_tsum i
        (fun j _ => poolFiberMass_nonneg q m y j)
      rw [(poolFiberMass_hasSum q m y).tsum_eq, hz] at hle
      exact le_antisymm hle (poolFiberMass_nonneg q m y i)
    rw [hz, zero_mul, hf]

theorem countableMixture_unpooling_reference (q : DiscreteLaw) (m : ℕ) :
    countableMixture (pooledLaw q (Finset.range m)) (unpoolingKernel q m) = q := by
  apply DiscreteLaw.ext
  intro i
  change (∑ y, (pooledLaw q (Finset.range m)).mass y *
    (unpoolingKernel q m y).mass i) = q.mass i
  simp_rw [pool_reference_mass_times_conditional, poolFiberMass]
  simp

theorem pooledLaw_countableMixture_unpooling (q : DiscreteLaw) (m : ℕ)
    (p : Probability (PoolLabel (Finset.range m))) :
    pooledLaw (countableMixture p (unpoolingKernel q m)) (Finset.range m) = p := by
  apply probability_ext
  intro y
  rw [pooledLaw_mass_fiber]
  have hrestrict :
      (∑' i : {i : ℕ // poolMap (Finset.range m) i = y}, (unpoolingKernel q m y).mass i) = 1 := by
    have heq : (Set.indicator {i | poolMap (Finset.range m) i = y}
        (unpoolingKernel q m y).mass) = (unpoolingKernel q m y).mass := by
      funext i
      by_cases hi : poolMap (Finset.range m) i = y
      · simp [hi]
      · simp [hi, unpoolingKernel_off_fiber q m y i hi]
    calc
      _ = ∑' i, (Set.indicator {i | poolMap (Finset.range m) i = y}
          (unpoolingKernel q m y).mass) i :=
        tsum_subtype {i | poolMap (Finset.range m) i = y} (unpoolingKernel q m y).mass
      _ = 1 := by rw [heq, DiscreteLaw.total]
  have heq : (fun i : {i : ℕ // poolMap (Finset.range m) i = y} =>
      (countableMixture p (unpoolingKernel q m)).mass i) =
      (fun i : {i : ℕ // poolMap (Finset.range m) i = y} =>
        p.mass y * (unpoolingKernel q m y).mass i) := by
    funext i
    change (∑ z, p.mass z * (unpoolingKernel q m z).mass i) = _
    rw [Finset.sum_eq_single y]
    · intro z _ hzy
      rw [unpoolingKernel_off_fiber q m z i (by simpa only [i.property] using Ne.symm hzy), mul_zero]
    · simp
  rw [heq, tsum_mul_left, hrestrict, mul_one]

end IdentityTesting
