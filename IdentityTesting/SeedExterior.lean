import IdentityTesting.MultiBinSeeds

/-!
# Fresh fixed exterior observations with reusable empirical seeds
Only the seeded latent indices can collide. Every exterior query uses its own
fresh source coordinate, so exterior repetitions add no term to the TV bound.
-/

noncomputable section
namespace IdentityTesting.SeedExterior
open scoped BigOperators
open Classical
open FiniteTesting FiniteIID CollisionTesting IndependentSeeds

universe u v w z
variable {Ω : Type u} {I : Type v} [Fintype Ω] [Fintype I] [DecidableEq I]

private theorem mixture_comm {A : Type w} {B : Type z} [Fintype A] [Fintype B]
    (a : Probability A) (b : Probability B) (K : A → B → Probability Ω) :
    mixture a (fun x => mixture b (K x)) =
      mixture b (fun y => mixture a (fun x => K x y)) := by
  apply probability_ext
  intro x
  simp only [mixture_mass, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem mapLaw_mixture {A : Type w} {X : Type z} [Fintype A] [Fintype X]
    (a : Probability A) (K : A → Probability Ω) (f : Ω → X) :
    mapLaw (mixture a K) f = mixture a (fun i => mapLaw (K i) f) := by
  apply probability_ext
  intro y
  exact mixture_kernel_mass a K (fun x => pointLaw (f x)) y

private theorem mapLaw_pointLaw {X : Type w} [Fintype X] (x : Ω) (f : Ω → X) :
    mapLaw (pointLaw x) f = pointLaw (f x) := by
  classical
  apply probability_ext
  intro y
  simp only [mapLaw, mixture_mass, pointLaw_mass, ite_mul, one_mul, zero_mul]
  simp

private theorem mapLaw_comp {X : Type w} {Y : Type z} [Fintype X] [Fintype Y]
    (p : Probability Ω) (f : Ω → X) (g : X → Y) :
    mapLaw (mapLaw p f) g = mapLaw p (g ∘ f) := by
  change mapLaw (mixture p (fun x => pointLaw (f x))) g = _
  rw [mapLaw_mixture]
  simp only [mapLaw_pointLaw]
  rfl

private theorem mapLaw_id (p : Probability Ω) : mapLaw p id = p := by
  classical
  apply probability_ext
  intro y
  simp [mapLaw_mass]

private theorem mapLaw_const (p : Probability Ω) (x : Ω) :
    mapLaw p (fun _ => x) = pointLaw x := by
  classical
  apply probability_ext
  intro y
  rw [mapLaw_mass, pointLaw_mass]
  by_cases h : x = y
  · subst y
    simpa using p.total
  · simp [h, Ne.symm h]

/-- Splitting a finite independent source across a disjoint union is an actual
independent draw of the two source tuples. -/
private theorem independentLaw_sum {J : Type w} [Fintype J] [DecidableEq J]
    (p : I → Probability Ω) (q : J → Probability Ω) :
    independentLaw (Sum.elim p q) =
      mixture (independentLaw p)
        (fun seed => mapLaw (independentLaw q) (Sum.elim seed)) := by
  classical
  apply probability_ext
  intro y
  have hiff (a : I → Ω) (b : J → Ω) :
      Sum.elim a b = y ↔ a = y ∘ Sum.inl ∧ b = y ∘ Sum.inr := by
    constructor
    · intro h
      constructor
      · exact congrArg (fun f => f ∘ Sum.inl) h
      · exact congrArg (fun f => f ∘ Sum.inr) h
    · rintro ⟨rfl, rfl⟩
      funext x
      cases x <;> rfl
  simp only [independentLaw_mass, Fintype.prod_sum_type, mixture_mass, mapLaw_mass, hiff]
  simp [ite_and, mul_ite]

/-- Coordinatewise maps preserve independence, including constant maps. -/
private theorem mapLaw_independentLaw {X : Type w} [Fintype X]
    (p : I → Probability Ω) (f : I → Ω → X) :
    mapLaw (independentLaw p) (fun seed i => f i (seed i)) =
      independentLaw (fun i => mapLaw (p i) (f i)) := by
  classical
  apply probability_ext
  intro y
  calc
    (mapLaw (independentLaw p) (fun seed i => f i (seed i))).mass y =
        ∑ seed : I → Ω, ∏ i,
          if f i (seed i) = y i then (p i).mass (seed i) else 0 := by
      rw [mapLaw_mass]
      apply Finset.sum_congr rfl
      intro seed _
      rw [Fintype.prod_ite_zero]
      simp only [funext_iff, independentLaw_mass]
    _ = ∏ i, ∑ x, if f i x = y i then (p i).mass x else 0 :=
      (Fintype.prod_sum (fun (i : I) (x : Ω) =>
        if f i x = y i then (p i).mass x else 0)).symm
    _ = (independentLaw (fun i => mapLaw (p i) (f i))).mass y := by
      simp only [independentLaw_mass, mapLaw_mass]

/-- Extend a family of cell laws by a fixed exterior at none. -/
def withExterior (exterior : Probability Ω) (p : I → Probability Ω) :
    Option I → Probability Ω
  | none => exterior
  | some i => p i

/-- Fixed exterior law at none; point mass at the selected empirical seed at some i. -/
def conditionalLaw (exterior : Probability Ω) (seed : I → Ω) :
    Option I → Probability Ω
  | none => exterior
  | some i => pointLaw (seed i)

/-- Actual prior member: the exterior stays a fixed law. -/
def exteriorSeedLaw (r : Probability (Option I)) (exterior : Probability Ω)
    (seed : I → Ω) : Probability Ω :=
  mixture r (conditionalLaw exterior seed)

def exteriorSeedMixture (r : Probability (Option I)) (p : I → Probability Ω)
    (exterior : Probability Ω) (n : ℕ) : Probability (Fin n → Ω) :=
  mixture (independentLaw p) (fun seed => productLaw (exteriorSeedLaw r exterior seed) n)

/-- Seed coordinates are shared; exterior coordinates are fresh for each query. -/
def queryIndex {n : ℕ} (query : Fin n → Option I) (t : Fin n) : I ⊕ Fin n :=
  match query t with
  | none => Sum.inr t
  | some i => Sum.inl i

def sourceLaws (p : I → Probability Ω) (exterior : Probability Ω) (n : ℕ) :
    I ⊕ Fin n → Probability Ω :=
  Sum.elim p (fun _ => exterior)

def sharedQueryLaw (p : I → Probability Ω) (exterior : Probability Ω)
    {n : ℕ} (query : Fin n → Option I) : Probability (Fin n → Ω) :=
  mapLaw (independentLaw (sourceLaws p exterior n))
    (fun source => source ∘ queryIndex query)

theorem sharedQueryLaw_eq (p : I → Probability Ω) (exterior : Probability Ω)
    {n : ℕ} (query : Fin n → Option I) :
    sharedQueryLaw p exterior query =
      mixture (independentLaw p)
        (fun seed => independentLaw (fun t => conditionalLaw exterior seed (query t))) := by
  unfold sharedQueryLaw sourceLaws
  rw [independentLaw_sum, mapLaw_mixture]
  apply congrArg (mixture (independentLaw p))
  funext seed
  rw [mapLaw_comp]
  have hfun :
      ((fun source : I ⊕ Fin n → Ω => source ∘ queryIndex query) ∘ Sum.elim seed) =
        (fun fresh : Fin n → Ω => fun t =>
          (match query t with | none => fresh t | some i => seed i)) := by
    funext fresh t
    cases h : query t <;> simp [queryIndex, h, Function.comp_def]
  rw [hfun]
  let f : Fin n → Ω → Ω := fun t x =>
    match query t with | none => x | some i => seed i
  have hpoint :
      (fun fresh : Fin n → Ω => fun t =>
        match query t with | none => fresh t | some i => seed i) =
      (fun fresh t => f t (fresh t)) := by
    funext fresh t
    cases h : query t <;> simp [f, h]
  rw [hpoint, mapLaw_independentLaw (fun _ : Fin n => exterior) f]
  congr 1
  funext t
  cases h : query t
  · simpa only [f, h, conditionalLaw] using mapLaw_id exterior
  · simpa only [f, h, conditionalLaw] using mapLaw_const exterior (seed _)

theorem exteriorSeedMixture_latent (r : Probability (Option I)) (p : I → Probability Ω)
    (exterior : Probability Ω) (n : ℕ) :
    exteriorSeedMixture r p exterior n =
      mixture (productLaw r n) (sharedQueryLaw p exterior) := by
  unfold exteriorSeedMixture exteriorSeedLaw
  simp_rw [← mixture_independentLaw r]
  rw [mixture_comm]
  apply congrArg (mixture (productLaw r n))
  funext query
  exact (sharedQueryLaw_eq p exterior query).symm

def seededRegion : Finset (Option I) := Finset.univ.filter (fun x : Option I => x ≠ none)

theorem queryIndex_injective_of_no_repeat {n : ℕ} (query : Fin n → Option I)
    (h : ¬ HasRepeat seededRegion query) : Function.Injective (queryIndex query) := by
  intro a b hab
  by_contra hne
  cases ha : query a with
  | none =>
      cases hb : query b with
      | none => exact hne (by simpa [queryIndex, ha, hb] using hab)
      | some j => simp [queryIndex, ha, hb] at hab
  | some i =>
      cases hb : query b with
      | none => simp [queryIndex, ha, hb] at hab
      | some j =>
          have hij : i = j := by simpa [queryIndex, ha, hb] using hab
          apply h
          refine ⟨a, b, hne, ?_, ?_⟩
          · simp [ha, hb, hij]
          · simp [seededRegion, ha]

theorem sharedQueryLaw_good (p : I → Probability Ω) (exterior : Probability Ω)
    {n : ℕ} (query : Fin n → Option I) (h : ¬ HasRepeat seededRegion query) :
    sharedQueryLaw p exterior query =
      independentLaw (fun t => withExterior exterior p (query t)) := by
  unfold sharedQueryLaw
  rw [independentLaw_select_injective _ n _ (queryIndex_injective_of_no_repeat query h)]
  congr 1
  funext t
  cases hq : query t <;> simp [sourceLaws, queryIndex, withExterior, hq]

/-- Full sample coupling: exterior observations are fresh and cost no collision
term, even when exterior cells or observed labels repeat. -/
theorem exteriorSeedMixture_tv_le (r : Probability (Option I)) (p : I → Probability Ω)
    (exterior : Probability Ω) (n : ℕ) :
    totalVariation (exteriorSeedMixture r p exterior n)
      (productLaw (mixture r (withExterior exterior p)) n) ≤
      (n.choose 2 : ℝ) * ∑ i, r.mass (some i) ^ 2 := by
  classical
  rw [exteriorSeedMixture_latent, ← mixture_independentLaw]
  calc
    totalVariation
        (mixture (productLaw r n) (sharedQueryLaw p exterior))
        (mixture (productLaw r n)
          (fun query => independentLaw (fun t => withExterior exterior p (query t)))) ≤
      ∑ query, if ¬ HasRepeat seededRegion query then 0 else (productLaw r n).mass query := by
      convert totalVariation_mixtures_agree_le (productLaw r n) _ _
        (fun query => ¬ HasRepeat seededRegion query)
        (fun query h => sharedQueryLaw_good p exterior query h) using 1
      apply Finset.sum_congr rfl
      intro query _
      split_ifs <;> rfl
    _ = expectation (productLaw r n) (repeatTest seededRegion n) := by
      unfold expectation
      apply Finset.sum_congr rfl
      intro query _
      by_cases h : HasRepeat seededRegion query <;> simp [h, repeatTest]
    _ ≤ (n.choose 2 : ℝ) * ∑ x ∈ seededRegion, r.mass x ^ 2 :=
      repeat_probability_le r seededRegion n
    _ = _ := by
      congr 1
      simp [seededRegion, Finset.sum_filter, Fintype.sum_option]

/-- Public source-splitting identity for two independent coordinate blocks. -/
theorem independentLaw_sum_source {J : Type w} [Fintype J] [DecidableEq J]
    (p : I → Probability Ω) (q : J → Probability Ω) :
    independentLaw (Sum.elim p q) =
      mixture (independentLaw p)
        (fun left => mapLaw (independentLaw q) (Sum.elim left)) :=
  independentLaw_sum p q

/-- Public coordinatewise pushforward identity for possibly different laws and maps. -/
theorem mapLaw_independentLaw_coordinates {X : Type w} [Fintype X]
    (p : I → Probability Ω) (f : I → Ω → X) :
    mapLaw (independentLaw p) (fun seed i => f i (seed i)) =
      independentLaw (fun i => mapLaw (p i) (f i)) :=
  mapLaw_independentLaw p f

end IdentityTesting.SeedExterior
