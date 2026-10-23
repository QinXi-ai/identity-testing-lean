import IdentityTesting.MultiBinExterior

/-!
# A common actual whole-sample seed regeneration kernel
The same sample kernel applies to every exterior law. Each input bin label is
regenerated from its empirical seed law, while every exterior input is mapped
through the specified deterministic deletion map.
-/

noncomputable section
namespace IdentityTesting.SeedSampleKernel
open scoped BigOperators
open Classical
open FiniteTesting EmpiricalSeeds IndependentSeeds MultiBinSeeds SeedExterior MultiBinExterior

universe u v w z
variable {Ω : Type u} {B : Type v} [Fintype Ω] [Fintype B] [DecidableEq B]

private theorem mixture_comm {A : Type w} {C : Type z} [Fintype A] [Fintype C]
    (a : Probability A) (c : Probability C) (K : A → C → Probability Ω) :
    mixture a (fun x => mixture c (K x)) =
      mixture c (fun y => mixture a (fun x => K x y)) := by
  apply probability_ext
  intro x
  simp only [mixture_mass, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- A single observation is regenerated within its bin or deterministically
mapped in the exterior. -/
def singleSeedKernel (classify : Ω → Option B) (delete : Ω → Ω)
    (m : B → ℕ) (hm : ∀ i, 0 < m i) (seed : SeedIndex m → Ω) (x : Ω) :
    Probability Ω :=
  match classify x with
  | none => pointLaw (delete x)
  | some i => empiricalLaw (hm i) (fun j => seed ⟨i, j⟩)

/-- Actual common sample kernel, including the shared seed randomness. -/
def wholeSampleSeedKernel (p : B → Probability Ω) (classify : Ω → Option B)
    (delete : Ω → Ω) (m : B → ℕ) (hm : ∀ i, 0 < m i) (n : ℕ)
    (input : Fin n → Ω) : Probability (Fin n → Ω) :=
  mixture (multiBinSeedPrior p m)
    (fun seed => independentLaw (fun t => singleSeedKernel classify delete m hm seed (input t)))

/-- Acting on an IID input gives the actual prior predictive law of the
single-observation transformed laws. -/
theorem wholeSampleSeedKernel_productLaw (q : Probability Ω) (p : B → Probability Ω)
    (classify : Ω → Option B) (delete : Ω → Ω) (m : B → ℕ)
    (hm : ∀ i, 0 < m i) (n : ℕ) :
    mixture (productLaw q n) (wholeSampleSeedKernel p classify delete m hm n) =
      mixture (multiBinSeedPrior p m)
        (fun seed => productLaw (mixture q (singleSeedKernel classify delete m hm seed)) n) := by
  unfold wholeSampleSeedKernel
  rw [mixture_comm]
  apply congrArg (mixture (multiBinSeedPrior p m))
  funext seed
  exact mixture_independentLaw q (singleSeedKernel classify delete m hm seed) n

theorem wholeSampleSeedKernel_contraction (p : B → Probability Ω)
    (classify : Ω → Option B) (delete : Ω → Ω) (m : B → ℕ)
    (hm : ∀ i, 0 < m i) (n : ℕ) (P Q : Probability (Fin n → Ω)) :
    totalVariation
      (mixture P (wholeSampleSeedKernel p classify delete m hm n))
      (mixture Q (wholeSampleSeedKernel p classify delete m hm n)) ≤ totalVariation P Q :=
  totalVariation_kernel_le P Q (wholeSampleSeedKernel p classify delete m hm n)

omit [Fintype B] [DecidableEq B] in
theorem singleSeedKernel_exterior (exterior : Probability Ω)
    (classify : Ω → Option B) (delete : Ω → Ω) (m : B → ℕ) (hm : ∀ i, 0 < m i)
    (seed : SeedIndex m → Ω)
    (hexterior : ∀ x, 0 < exterior.mass x → classify x = none) :
    mixture exterior (singleSeedKernel classify delete m hm seed) = mapLaw exterior delete := by
  change mixture exterior (singleSeedKernel classify delete m hm seed) =
    mixture exterior (fun x => pointLaw (delete x))
  apply probability_ext
  intro y
  simp only [mixture_mass]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : exterior.mass x = 0
  · simp only [hx, zero_mul]
  · have hxpos : 0 < exterior.mass x :=
      lt_of_le_of_ne (exterior.nonneg x) (Ne.symm hx)
    simp only [singleSeedKernel, hexterior x hxpos]

omit [Fintype B] [DecidableEq B] in
theorem singleSeedKernel_cell (p : B → Probability Ω)
    (classify : Ω → Option B) (delete : Ω → Ω) (m : B → ℕ) (hm : ∀ i, 0 < m i)
    (seed : SeedIndex m → Ω)
    (hcells : ∀ i x, 0 < (p i).mass x → classify x = some i) (i : B) :
    mixture (p i) (singleSeedKernel classify delete m hm seed) =
      empiricalLaw (hm i) (fun j => seed ⟨i, j⟩) := by
  calc
    mixture (p i) (singleSeedKernel classify delete m hm seed) =
      mixture (p i) (fun _ => empiricalLaw (hm i) (fun j => seed ⟨i, j⟩)) := by
      apply probability_ext
      intro y
      simp only [mixture_mass]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : (p i).mass x = 0
      · simp only [hx, zero_mul]
      · have hxpos : 0 < (p i).mass x :=
          lt_of_le_of_ne ((p i).nonneg x) (Ne.symm hx)
        simp only [singleSeedKernel, hcells i x hxpos]
    _ = _ := mixture_constant _ _

omit [DecidableEq B] in
theorem singleSeedKernel_reference (w : Probability (Option B)) (p : B → Probability Ω)
    (exterior : Probability Ω) (classify : Ω → Option B) (delete : Ω → Ω)
    (m : B → ℕ) (hm : ∀ i, 0 < m i) (seed : SeedIndex m → Ω)
    (hcells : ∀ i x, 0 < (p i).mass x → classify x = some i)
    (hexterior : ∀ x, 0 < exterior.mass x → classify x = none) :
    mixture (mixture w (withExterior exterior p)) (singleSeedKernel classify delete m hm seed) =
      multiBinExteriorLaw w (mapLaw exterior delete) m hm seed := by
  calc
    mixture (mixture w (withExterior exterior p)) (singleSeedKernel classify delete m hm seed) =
      mixture w (fun i => mixture (withExterior exterior p i)
        (singleSeedKernel classify delete m hm seed)) := by
      apply probability_ext
      intro y
      exact mixture_kernel_mass w (withExterior exterior p)
        (singleSeedKernel classify delete m hm seed) y
    _ = _ := by
      unfold multiBinExteriorLaw
      apply congrArg (mixture w)
      funext i
      cases i with
      | none => exact singleSeedKernel_exterior exterior classify delete m hm seed hexterior
      | some i => exact singleSeedKernel_cell p classify delete m hm seed hcells i

/-- Exact caller: the common kernel sends a reference IID sample to the actual
multi-bin prior with its exterior deterministically mapped. -/
theorem wholeSampleSeedKernel_reference (w : Probability (Option B)) (p : B → Probability Ω)
    (exterior : Probability Ω) (classify : Ω → Option B) (delete : Ω → Ω)
    (m : B → ℕ) (hm : ∀ i, 0 < m i) (n : ℕ)
    (hcells : ∀ i x, 0 < (p i).mass x → classify x = some i)
    (hexterior : ∀ x, 0 < exterior.mass x → classify x = none) :
    mixture (productLaw (mixture w (withExterior exterior p)) n)
      (wholeSampleSeedKernel p classify delete m hm n) =
        multiBinExteriorSampleMixture w p (mapLaw exterior delete) m hm n := by
  rw [wholeSampleSeedKernel_productLaw]
  unfold multiBinExteriorSampleMixture
  apply congrArg (mixture (multiBinSeedPrior p m))
  funext seed
  rw [singleSeedKernel_reference w p exterior classify delete m hm seed hcells hexterior]

/-- The identical kernel acts on every member of an arbitrary exterior prior,
including a signed prior that preserves all bin masses and conditionals. -/
theorem wholeSampleSeedKernel_exteriorFamily {A : Type w} [Fintype A]
    (θ : Probability A) (w : Probability (Option B)) (p : B → Probability Ω)
    (exteriors : A → Probability Ω) (classify : Ω → Option B) (delete : Ω → Ω)
    (m : B → ℕ) (hm : ∀ i, 0 < m i) (n : ℕ)
    (hcells : ∀ i x, 0 < (p i).mass x → classify x = some i)
    (hexteriors : ∀ a x, 0 < (exteriors a).mass x → classify x = none) :
    mixture
      (mixture θ (fun a => productLaw (mixture w (withExterior (exteriors a) p)) n))
      (wholeSampleSeedKernel p classify delete m hm n) =
    mixture θ (fun a => multiBinExteriorSampleMixture w p (mapLaw (exteriors a) delete) m hm n) := by
  calc
    _ = mixture θ (fun a =>
      mixture (productLaw (mixture w (withExterior (exteriors a) p)) n)
        (wholeSampleSeedKernel p classify delete m hm n)) := by
      apply probability_ext
      intro y
      exact mixture_kernel_mass θ _ (wholeSampleSeedKernel p classify delete m hm n) y
    _ = _ := by
      apply congrArg (mixture θ)
      funext a
      exact wholeSampleSeedKernel_reference w p (exteriors a) classify delete m hm n
        hcells (hexteriors a)

/-- Full contraction caller for a common seed kernel on a signed family and the
unsigned reference. No externally supplied sample kernel is assumed. -/
theorem commonSeedKernel_tv_le {A : Type w} [Fintype A]
    (θ : Probability A) (w : Probability (Option B)) (p : B → Probability Ω)
    (exteriors : A → Probability Ω) (exterior : Probability Ω)
    (classify : Ω → Option B) (delete : Ω → Ω)
    (m : B → ℕ) (hm : ∀ i, 0 < m i) (n : ℕ)
    (hcells : ∀ i x, 0 < (p i).mass x → classify x = some i)
    (hexteriors : ∀ a x, 0 < (exteriors a).mass x → classify x = none)
    (hexterior : ∀ x, 0 < exterior.mass x → classify x = none) :
    totalVariation
      (mixture θ (fun a => multiBinExteriorSampleMixture w p (mapLaw (exteriors a) delete) m hm n))
      (multiBinExteriorSampleMixture w p (mapLaw exterior delete) m hm n) ≤
    totalVariation
      (mixture θ (fun a => productLaw (mixture w (withExterior (exteriors a) p)) n))
      (productLaw (mixture w (withExterior exterior p)) n) := by
  rw [← wholeSampleSeedKernel_exteriorFamily θ w p exteriors classify delete m hm n hcells hexteriors,
    ← wholeSampleSeedKernel_reference w p exterior classify delete m hm n hcells hexterior]
  exact wholeSampleSeedKernel_contraction p classify delete m hm n _ _

private theorem mapLaw_eq_self_of_fixed_support (p : Probability Ω) (f : Ω → Ω)
    (hf : ∀ x, 0 < p.mass x → f x = x) : mapLaw p f = p := by
  calc
    mapLaw p f = mixture p pointLaw := by
      apply probability_ext
      intro y
      simp only [mapLaw, mixture_mass]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : p.mass x = 0
      · simp only [hx, zero_mul]
      · have hxpos : 0 < p.mass x := lt_of_le_of_ne (p.nonneg x) (Ne.symm hx)
        rw [hf x hxpos]
    _ = p := probability_ext (mixture_pointLaw_mass p)

omit [DecidableEq B] in
/-- Mapping the exterior and fixing every cell-supported label is the actual
pushforward of the full reference law. -/
theorem referenceDeletionLaw (w : Probability (Option B)) (p : B → Probability Ω)
    (exterior : Probability Ω) (delete : Ω → Ω)
    (hdelete : ∀ i x, 0 < (p i).mass x → delete x = x) :
    mapLaw (mixture w (withExterior exterior p)) delete =
      mixture w (withExterior (mapLaw exterior delete) p) := by
  calc
    _ = mixture w (fun i => mapLaw (withExterior exterior p i) delete) := by
      apply probability_ext
      intro y
      exact mixture_kernel_mass w (withExterior exterior p)
        (fun x => pointLaw (delete x)) y
    _ = _ := by
      apply congrArg (mixture w)
      funext i
      cases i with
      | none => rfl
      | some i => exact mapLaw_eq_self_of_fixed_support (p i) delete (hdelete i)

/-- The actual unsigned seed mixture differs from its original IID reference
by the seed collision error plus the full-sample deletion coupling error. -/
theorem seededReference_tv_le (w : Probability (Option B)) (p : B → Probability Ω)
    (exterior : Probability Ω) (delete : Ω → Ω)
    (m : B → ℕ) (hm : ∀ i, 0 < m i) (n : ℕ)
    (hdelete : ∀ i x, 0 < (p i).mass x → delete x = x) :
    totalVariation (multiBinExteriorSampleMixture w p (mapLaw exterior delete) m hm n)
      (productLaw (mixture w (withExterior exterior p)) n) ≤
    (n.choose 2 : ℝ) * (∑ i, w.mass (some i) ^ 2 / (m i : ℝ)) +
      (n : ℝ) * (∑ x, if delete x ≠ x then
        (mixture w (withExterior exterior p)).mass x else 0) := by
  calc
    _ ≤ totalVariation (multiBinExteriorSampleMixture w p (mapLaw exterior delete) m hm n)
          (productLaw (mixture w (withExterior (mapLaw exterior delete) p)) n) +
        totalVariation (productLaw (mixture w (withExterior (mapLaw exterior delete) p)) n)
          (productLaw (mixture w (withExterior exterior p)) n) :=
      totalVariation_triangle _ _ _
    _ ≤ _ := by
      apply add_le_add (multiBinExteriorSampleMixture_tv_le w p (mapLaw exterior delete) m hm n)
      rw [← referenceDeletionLaw w p exterior delete hdelete]
      exact totalVariation_productLaw_mapLaw_le _ delete n

/-- Combined fixed-sample caller: common-kernel contraction, actual deletion,
and actual empirical-seed coupling give the three error terms. -/
theorem commonSeedKernel_final_tv_le {A : Type w} [Fintype A]
    (θ : Probability A) (w : Probability (Option B)) (p : B → Probability Ω)
    (exteriors : A → Probability Ω) (exterior : Probability Ω)
    (classify : Ω → Option B) (delete : Ω → Ω)
    (m : B → ℕ) (hm : ∀ i, 0 < m i) (n : ℕ)
    (hcells : ∀ i x, 0 < (p i).mass x → classify x = some i)
    (hexteriors : ∀ a x, 0 < (exteriors a).mass x → classify x = none)
    (hexterior : ∀ x, 0 < exterior.mass x → classify x = none)
    (hdelete : ∀ i x, 0 < (p i).mass x → delete x = x) :
    totalVariation
      (mixture θ (fun a => multiBinExteriorSampleMixture w p (mapLaw (exteriors a) delete) m hm n))
      (productLaw (mixture w (withExterior exterior p)) n) ≤
    totalVariation
      (mixture θ (fun a => productLaw (mixture w (withExterior (exteriors a) p)) n))
      (productLaw (mixture w (withExterior exterior p)) n) +
      (n : ℝ) * (∑ x, if delete x ≠ x then
        (mixture w (withExterior exterior p)).mass x else 0) +
      (n.choose 2 : ℝ) * ∑ i, w.mass (some i) ^ 2 / (m i : ℝ) := by
  calc
    _ ≤ totalVariation
        (mixture θ (fun a => multiBinExteriorSampleMixture w p (mapLaw (exteriors a) delete) m hm n))
        (multiBinExteriorSampleMixture w p (mapLaw exterior delete) m hm n) +
      totalVariation (multiBinExteriorSampleMixture w p (mapLaw exterior delete) m hm n)
        (productLaw (mixture w (withExterior exterior p)) n) := totalVariation_triangle _ _ _
    _ ≤ totalVariation
        (mixture θ (fun a => productLaw (mixture w (withExterior (exteriors a) p)) n))
        (productLaw (mixture w (withExterior exterior p)) n) +
      ((n.choose 2 : ℝ) * (∑ i, w.mass (some i) ^ 2 / (m i : ℝ)) +
        (n : ℝ) * (∑ x, if delete x ≠ x then
          (mixture w (withExterior exterior p)).mass x else 0)) :=
      add_le_add
        (commonSeedKernel_tv_le θ w p exteriors exterior classify delete m hm n
          hcells hexteriors hexterior)
        (seededReference_tv_le w p exterior delete m hm n hdelete)
    _ = _ := by ring

end IdentityTesting.SeedSampleKernel
