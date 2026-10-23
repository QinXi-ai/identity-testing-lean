import IdentityTesting.SubprobabilityCells
import IdentityTesting.FiniteEmbedding
import IdentityTesting.DegenerateBranches

/-! Add an actual zero-reference label while preserving the original countable law. -/

noncomputable section
namespace IdentityTesting
open scoped BigOperators
open Classical
open FiniteTesting

def padFiniteLaw {k : ℕ} (p : Probability (Fin k)) : Probability (Fin (k + 1)) :=
  mapLaw p Fin.castSucc

@[simp] theorem padFiniteLaw_mass_castSucc {k : ℕ} (p : Probability (Fin k)) (i : Fin k) :
    (padFiniteLaw p).mass i.castSucc = p.mass i :=
  EmpiricalSeeds.mapLaw_mass_injective p Fin.castSucc (Fin.castSucc_injective k) i

@[simp] theorem padFiniteLaw_mass_last {k : ℕ} (p : Probability (Fin k)) :
    (padFiniteLaw p).mass (Fin.last k) = 0 := by
  apply EmpiricalSeeds.mapLaw_mass_eq_zero_of_not_mem p Fin.castSucc
  intro i hi
  have hv := congrArg Fin.val hi
  change i.val = k at hv
  exact (Nat.ne_of_lt i.isLt) hv

theorem padFiniteLaw_totalVariation {k : ℕ} (p q : Probability (Fin k)) :
    FiniteTesting.totalVariation (padFiniteLaw p) (padFiniteLaw q) =
      FiniteTesting.totalVariation p q := by
  unfold FiniteTesting.totalVariation
  rw [Fin.sum_univ_castSucc]
  simp

theorem extendFiniteLaw_padFiniteLaw {k : ℕ} (p : Probability (Fin k)) :
    extendFiniteLaw (padFiniteLaw p) = extendFiniteLaw p := by
  apply DiscreteLaw.eq_of_mass_eq
  funext i
  by_cases hi : i < k
  · have heq : i = (Fin.castSucc (⟨i, hi⟩ : Fin k)).val := rfl
    conv_lhs => rw [heq]
    rw [extendFiniteLaw_mass_val, padFiniteLaw_mass_castSucc]
    exact (extendFiniteLaw_mass_val p ⟨i, hi⟩).symm
  · rw [extendFiniteLaw_mass_of_not_lt p i hi]
    by_cases hik : i = k
    · subst i
      change (extendFiniteLaw (padFiniteLaw p)).mass (Fin.last k).val = 0
      rw [extendFiniteLaw_mass_val, padFiniteLaw_mass_last]
    · exact extendFiniteLaw_mass_of_not_lt (padFiniteLaw p) i (by omega)

theorem padded_sample_mixture_tv_le {k : ℕ} {I : Type*} [Fintype I]
    (w : Probability I) (p : I → Probability (Fin k)) (q : Probability (Fin k)) (n : ℕ) :
    FiniteTesting.totalVariation (mixture w (fun i => productLaw (padFiniteLaw (p i)) n))
      (productLaw (padFiniteLaw q) n) ≤
      FiniteTesting.totalVariation (mixture w (fun i => productLaw (p i) n)) (productLaw q n) := by
  let f := fun sample : Fin n → Fin k => Fin.castSucc ∘ sample
  have hmap (r : Probability (Fin k)) : mapLaw (productLaw r n) f = productLaw (padFiniteLaw r) n :=
    mapLaw_productLaw r Fin.castSucc n
  have hmix : mapLaw (mixture w (fun i => productLaw (p i) n)) f =
      mixture w (fun i => productLaw (padFiniteLaw (p i)) n) := by
    apply probability_ext
    intro y
    change (mixture (mixture w (fun i => productLaw (p i) n)) (fun x => pointLaw (f x))).mass y = _
    rw [mixture_kernel_mass]
    change (mixture w (fun i => mapLaw (productLaw (p i) n) f)).mass y = _
    simp only [hmap]
  rw [← hmix, ← hmap q]
  exact totalVariation_mapLaw_le _ _ f

/-- A prior using the new zero-reference label obstructs tests for the original
reference on N, not a modified testing problem. -/
theorem no_identityTest_of_padded_prior {k : ℕ} {I : Type*} [Fintype I]
    (w : Probability I) (p : I → Probability (Fin (k + 1))) (q : Probability (Fin k))
    (ε : ℝ) (n : ℕ)
    (hsep : ∀ i, 0 < w.mass i → ε < FiniteTesting.totalVariation (p i) (padFiniteLaw q))
    (htv : FiniteTesting.totalVariation (mixture w (fun i => productLaw (p i) n))
      (productLaw (padFiniteLaw q) n) < (1 : ℝ) / 3) :
    ¬ HasIdentityTest (extendFiniteLaw q) ε n := by
  rw [← extendFiniteLaw_padFiniteLaw q]
  exact no_identityTest_extendFiniteLaw_of_finite_prior w p (padFiniteLaw q) ε n hsep htv

end IdentityTesting
