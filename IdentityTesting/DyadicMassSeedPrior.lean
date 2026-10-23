import IdentityTesting.DyadicExterior
import IdentityTesting.WeightedExteriorSeedSupport
import IdentityTesting.CanonicalDyadicSeedCounts

/-! Dyadic seeds for arbitrary positive masses and actual fixed exterior masses.
The zero residual case needs no probability supported outside the seeded set. -/

noncomputable section
namespace IdentityTesting.EmpiricalSeeds
open scoped BigOperators
open Classical
open FiniteTesting IndependentSeeds MultiBinSeeds MultiBinExterior SeedExterior

variable {ι Ω : Type*} [Fintype ι] [Fintype Ω]

/-- The dyadic bins and exact integer counts used by the constructed prior. -/
def DyadicSeedSpecification (a : ι → ℝ) (b B : ℝ) (n : ℕ)
    (j : ι → ℕ) (m : OccupiedCells j → ℕ) : Prop :=
  (∀ i, dyadicUpper b (j i) / 2 < a i ∧ a i ≤ dyadicUpper b (j i)) ∧
    ∀ l, m l = allocatedSeedCount (B * (n : ℝ) ^ 2) (cellMass a j)
      (fun l : OccupiedCells j => dyadicUpper b l.val) l

/-- Normalize actual exterior masses when their total is positive. When it is
zero, any point law is harmless because its cell weight is zero. -/
theorem exists_exterior_conditional (r : Ω → ℝ) (hr : ∀ x, 0 ≤ r x)
    (d : ℝ) (hd : 0 ≤ d) (ht : ∑ x, r x = d) (x₀ : Ω) :
    ∃ p : Probability Ω, ∀ x, d * p.mass x = r x := by
  by_cases hz : d = 0
  · refine ⟨pointLaw x₀, ?_⟩
    intro x
    have hx : r x ≤ d := ht ▸ Finset.single_le_sum (fun y _ => hr y) (Finset.mem_univ x)
    simp only [hz, zero_mul]
    linarith [hr x]
  · have hd0 : 0 < d := lt_of_le_of_ne hd (Ne.symm hz)
    let p : Probability Ω :=
      { mass := fun x => r x / d
        nonneg := fun x => div_nonneg (hr x) hd
        total := by rw [← Finset.sum_div, ht, div_self hz] }
    refine ⟨p, ?_⟩
    intro x
    dsimp [p]
    field_simp

theorem exists_dyadic_exterior_prior_weighted [Nonempty ι]
    (a : ι → ℝ) (ha : ∀ i, 0 < a i) (b : ℝ) (hab : ∀ i, a i ≤ b)
    (e : ι → Ω) (aΩ : Ω → ℝ) (haΩ : ∀ x, 0 ≤ aΩ x) (hea : ∀ i, aΩ (e i) = a i)
    (f : ℝ) (hf : 0 ≤ f) (ht : f * ∑ i, a i ≤ 1)
    (exterior : Probability Ω)
    (hext : ∀ x, aΩ x ≠ 0 → (1 - f * ∑ i, a i) * exterior.mass x = 0)
    (B : ℝ) (hB : 0 < B) (n : ℕ) (hn : 0 < n) :
    ∃ (j : ι → ℕ) (m : OccupiedCells j → ℕ) (hm : ∀ l, 0 < m l),
      let w := scaledCellWeights a (fun i => (ha i).le) j f hf ht
      let p := embeddedCellLaw a ha j e
      DyadicSeedSpecification a b B n j m ∧
      (∀ seed : SeedIndex m → Ω, 0 < (multiBinSeedPrior p m).mass seed →
        (∑ x, min ((multiBinExteriorLaw w exterior m hm seed).mass x) (aΩ x)) ≤
          2 * B * (n : ℝ) ^ 2 * (∑ i, (a i) ^ ((3 : ℝ) / 2)) ^ 2 + 2 * b) ∧
      FiniteTesting.totalVariation (multiBinExteriorSampleMixture w p exterior m hm n)
        (productLaw (mixture w (withExterior exterior p)) n) ≤ f ^ 2 / (2 * B) := by
  obtain ⟨j, m, hjdef, hmdef, hj, hm, hoverlap, hcollision⟩ :=
    exists_dyadic_seed_counts_with_formula a b ha hab B hB n hn
  refine ⟨j, m, hm, ?_⟩
  dsimp only
  refine ⟨⟨hj, hmdef⟩, ?_, ?_⟩
  · intro seed hs
    apply le_trans (multiBinExteriorLaw_overlap_le_weighted _ _ exterior m hm seed hs
      aΩ haΩ hext (fun l => dyadicUpper b l.val) ?_) hoverlap
    intro l x hx
    obtain ⟨i, hi, hicell⟩ := embeddedCellLaw_positive_preimage a ha j e l x hx
    have heq : j i = l.val := congrArg Subtype.val hicell
    rw [← hi, hea]
    simpa only [heq] using (hj i).2
  · apply (multiBinExteriorSampleMixture_tv_le _ _ exterior m hm n).trans
    simp only [scaledCellWeights_some]
    have hfactor : (∑ l, (f * cellMass a j l) ^ 2 / (m l : ℝ)) =
        f ^ 2 * ∑ l, (cellMass a j l) ^ 2 / (m l : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      ring
    rw [hfactor]
    calc
      _ = f ^ 2 * ((n.choose 2 : ℝ) * ∑ l, (cellMass a j l) ^ 2 / (m l : ℝ)) := by ring
      _ ≤ f ^ 2 * (1 / (2 * B)) := mul_le_mul_of_nonneg_left hcollision (sq_nonneg f)
      _ = _ := by ring

theorem embeddedCellLaw_mass_off (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    (j : ι → ℕ) (e : ι → Ω) (l : OccupiedCells j) (x : Ω)
    (hx : ∀ i, e i ≠ x) : (embeddedCellLaw a ha j e l).mass x = 0 :=
  mapLaw_mass_eq_zero_of_not_mem _ e x hx

theorem multiBinExteriorLaw_mass_off_of_prior_pos
    (a : ι → ℝ) (ha : ∀ i, 0 < a i) (j : ι → ℕ) (e : ι → Ω)
    (w : Probability (Option (OccupiedCells j))) (ext : Probability Ω)
    (m : OccupiedCells j → ℕ) (hm : ∀ l, 0 < m l)
    (seed : SeedIndex m → Ω)
    (hs : 0 < (multiBinSeedPrior (embeddedCellLaw a ha j e) m).mass seed)
    (x : Ω) (hx : ∀ i, e i ≠ x) :
    (multiBinExteriorLaw w ext m hm seed).mass x = w.mass none * ext.mass x := by
  rw [multiBinExteriorLaw_eq]
  have hseed : ∀ l, x ≠ seed l := by
    intro l h
    have hp := independentLaw_positive_coordinate _ seed hs l
    change 0 < (embeddedCellLaw a ha j e l.1).mass (seed l) at hp
    rw [← h, embeddedCellLaw_mass_off a ha j e l.1 x hx] at hp
    exact (lt_irrefl 0) hp
  simp only [exteriorSeedLaw, mixture_mass, Fintype.sum_option, conditionalLaw,
    pointLaw_mass, if_neg (hseed _), mul_zero, Finset.sum_const_zero, add_zero]
  rfl

/-- Literal nonempty-set form of lem:seed. No total-mass assumption is imposed
on a itself; f times its mass is at most one. The prescribed exterior may vanish. -/
theorem exists_dyadic_mass_seed_prior (S : Finset Ω) (hS : S.Nonempty)
    (a : Ω → ℝ) (ha : ∀ x ∈ S, 0 < a x)
    (f : ℝ) (hf : 0 < f) (ht : f * ∑ x ∈ S, a x ≤ 1)
    (r : Ω → ℝ) (hr : ∀ x, 0 ≤ r x) (hrS : ∀ x ∈ S, r x = 0)
    (hrt : ∑ x, r x = 1 - f * ∑ x ∈ S, a x)
    (B : ℝ) (hB : 0 < B) (n : ℕ) (hn : 0 < n) :
    ∃ (ext : Probability Ω) (j : S → ℕ) (m : OccupiedCells j → ℕ) (hm : ∀ l, 0 < m l),
      let w := scaledCellWeights (fun i : S => a i) (fun i => (ha i i.property).le) j f hf.le
        (by simpa only [Finset.sum_coe_sort] using ht)
      let p := embeddedCellLaw (fun i : S => a i) (fun i => ha i i.property) j Subtype.val
      let reference := mixture w (withExterior ext p)
      DyadicSeedSpecification (fun i : S => a i) (S.sup' hS a) B n j m ∧
      (∀ x ∈ S, reference.mass x = f * a x) ∧
      (∀ x ∉ S, reference.mass x = r x) ∧
      (∀ seed : SeedIndex m → Ω, 0 < (multiBinSeedPrior p m).mass seed →
        (∀ x ∉ S, (multiBinExteriorLaw w ext m hm seed).mass x = r x) ∧
        (∑ x ∈ S, min ((multiBinExteriorLaw w ext m hm seed).mass x) (a x)) ≤
          2 * B * (n : ℝ) ^ 2 * (∑ x ∈ S, (a x) ^ ((3 : ℝ) / 2)) ^ 2 +
            2 * S.sup' hS a) ∧
      FiniteTesting.totalVariation (multiBinExteriorSampleMixture w p ext m hm n)
        (productLaw reference n) ≤ f ^ 2 / (2 * B) := by
  letI : Nonempty S := ⟨⟨hS.choose, hS.choose_spec⟩⟩
  let ai : S → ℝ := fun i => a i
  have hai : ∀ i : S, 0 < ai i := fun i => ha i i.property
  have hit : f * ∑ i : S, ai i ≤ 1 := by simpa only [ai, Finset.sum_coe_sort] using ht
  obtain ⟨ext, hext⟩ := exists_exterior_conditional r hr (1 - f * ∑ x ∈ S, a x)
    (sub_nonneg.mpr ht) hrt hS.choose
  let aΩ : Ω → ℝ := fun x => if x ∈ S then a x else 0
  have haΩ : ∀ x, 0 ≤ aΩ x := by
    intro x
    dsimp [aΩ]
    split_ifs with hx
    · exact (ha x hx).le
    · exact le_rfl
  have hea : ∀ i : S, aΩ i = ai i := fun i => if_pos i.property
  have hdisj : ∀ x, aΩ x ≠ 0 → (1 - f * ∑ i : S, ai i) * ext.mass x = 0 := by
    intro x hx
    have hxs : x ∈ S := by by_contra hn; exact hx (if_neg hn)
    simpa only [ai, Finset.sum_coe_sort, hext, hrS x hxs] using hext x
  obtain ⟨j, m, hm, hspec, hover, htv⟩ := exists_dyadic_exterior_prior_weighted ai hai (S.sup' hS a)
    (fun i => Finset.le_sup' a i.property) Subtype.val aΩ haΩ hea f hf.le hit ext hdisj B hB n hn
  refine ⟨ext, j, m, hm, ?_⟩
  dsimp only
  have hw (x : Ω) : (scaledCellWeights ai (fun i => (hai i).le) j f hf.le hit).mass none *
      ext.mass x = r x := by simpa only [scaledCellWeights_none, ai, Finset.sum_coe_sort] using hext x
  refine ⟨hspec, ?_, ?_, ?_, htv⟩
  · intro x hx
    simp only [mixture_mass, Fintype.sum_option, withExterior]
    change (1 - f * ∑ i : S, ai i) * ext.mass x +
      (∑ l, (f * cellMass ai j l) * (embeddedCellLaw ai hai j Subtype.val l).mass x) = f * a x
    rw [← show (⟨x, hx⟩ : S).val = x from rfl,
      sum_scaled_embeddedCellLaw_mass ai hai j Subtype.val Subtype.val_injective f ⟨x, hx⟩]
    have hz : (1 - f * ∑ i : S, ai i) * ext.mass x = 0 := by
      change (scaledCellWeights ai (fun i => (hai i).le) j f hf.le hit).mass none * ext.mass x = 0
      rw [hw, hrS x hx]
    change (1 - f * ∑ i : S, ai i) * ext.mass x + f * a x = f * a x
    rw [hz, zero_add]
  · intro x hx
    have hoff : ∀ i : S, i.val ≠ x := fun i h => hx (h ▸ i.property)
    change (mixture (scaledCellWeights ai (fun i => (hai i).le) j f hf.le hit)
      (withExterior ext (embeddedCellLaw ai hai j Subtype.val))).mass x = r x
    have hz : ∀ l, (embeddedCellLaw ai hai j Subtype.val l).mass x = 0 :=
      fun l => embeddedCellLaw_mass_off ai hai j Subtype.val l x hoff
    simp only [mixture_mass, Fintype.sum_option, withExterior, hz, mul_zero,
      Finset.sum_const_zero, add_zero]
    exact hw x
  · intro seed hs
    constructor
    · intro x hx
      rw [multiBinExteriorLaw_mass_off_of_prior_pos ai hai j Subtype.val _ ext m hm seed hs x
        (fun i h => hx (h ▸ i.property))]
      exact hw x
    · have h := hover seed hs
      let law := multiBinExteriorLaw (scaledCellWeights ai (fun i => (hai i).le) j f hf.le hit)
        ext m hm seed
      have hsum : (∑ x, min (law.mass x) (aΩ x)) = ∑ x ∈ S, min (law.mass x) (a x) := by
        calc
          _ = ∑ x, if x ∈ S then min (law.mass x) (a x) else 0 := by
            apply Finset.sum_congr rfl
            intro x _
            by_cases hx : x ∈ S
            · simp only [aΩ, if_pos hx]
            · simp only [aΩ, if_neg hx, min_eq_right (law.nonneg x)]
          _ = _ := by simp
      change (∑ x, min (law.mass x) (aΩ x)) ≤ _ at h
      rw [hsum] at h
      have hmoment : (∑ i : S, (ai i) ^ ((3 : ℝ) / 2)) =
          ∑ x ∈ S, (a x) ^ ((3 : ℝ) / 2) :=
        Finset.sum_coe_sort S (fun x : Ω => (a x) ^ ((3 : ℝ) / 2))
      rw [hmoment] at h
      exact h

/-- Empty S: the prescribed exterior itself is the reference and every member
of a one-point prior. All seeded mass and overlap quantities vanish exactly. -/
theorem exists_empty_mass_seed_prior (r : Ω → ℝ) (hr : ∀ x, 0 ≤ r x)
    (hrt : ∑ x, r x = 1) (n : ℕ) :
    ∃ (reference : Probability Ω) (prior : Probability Unit) (law : Unit → Probability Ω),
      (∀ x, reference.mass x = r x) ∧
      (∀ seed x, (law seed).mass x = r x) ∧
      (∀ seed, (∑ x ∈ (∅ : Finset Ω), min ((law seed).mass x) (r x)) = 0) ∧
      FiniteTesting.totalVariation (mixture prior (fun seed => productLaw (law seed) n))
        (productLaw reference n) = 0 := by
  let p : Probability Ω := ⟨r, hr, hrt⟩
  refine ⟨p, pointLaw (), fun _ => p, fun _ => rfl, fun _ _ => rfl, ?_, ?_⟩
  · intro seed
    simp
  · rw [mixture_constant, totalVariation_self]

end IdentityTesting.EmpiricalSeeds
