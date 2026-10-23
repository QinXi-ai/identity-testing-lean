import IdentityTesting.HeavyUpperConcentrated

/-! Remove the designated head from tail geometry while retaining the actual
finite observation alphabet for all statistical tests. -/
noncomputable section
open scoped BigOperators
namespace IdentityTesting.HeavyUpper
open FiniteTesting FiniteAllocationUpper
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

def tailWeights (q : Probability Ω) (a : Ω) : TailWeights Ω where
  mass i := if i = a then 0 else q.mass i
  nonneg i := by
    split
    · exact le_rfl
    · exact q.nonneg i

def retainedLabels (a : Ω) (x : Ω → ℝ) (η : ℝ) : Finset Ω :=
  insert a (coarseLabels x η)

def fineLabels (a : Ω) (x : Ω → ℝ) (η : ℝ) : Finset Ω :=
  (concentratedLabels x η).erase a

theorem retained_complement (a : Ω) (x : Ω → ℝ) (η : ℝ) :
    Finset.univ \ retainedLabels a x η = fineLabels a x η := by
  ext i
  simp [retainedLabels, fineLabels, concentratedLabels, and_comm]

theorem tailWeights_sum_erase (q : Probability Ω) (a : Ω) (L : Finset Ω) (f : Ω → ℝ) :
    (∑ i ∈ L, (tailWeights q a).mass i * f i) = ∑ i ∈ L.erase a, q.mass i * f i := by
  have hs : (∑ i ∈ L.erase a, (tailWeights q a).mass i * f i) =
      ∑ i ∈ L, (tailWeights q a).mass i * f i := by
    apply Finset.sum_subset (Finset.erase_subset a L)
    intro i hi hn
    have hia : i = a := by
      by_contra h
      exact hn (Finset.mem_erase.mpr ⟨h, hi⟩)
    simp [tailWeights, hia]
  rw [← hs]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [tailWeights, if_neg (Finset.mem_erase.mp hi).1]

theorem tail_weightedMoment (q : Probability Ω) (a : Ω) (L : Finset Ω) :
    weightedMoment (tailWeights q a) L = weightedMass q q (L.erase a) := by
  unfold weightedMoment
  rw [tailWeights_sum_erase]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [tailWeights, if_neg (Finset.mem_erase.mp hi).1]

theorem tail_sum_mass (q : Probability Ω) (a : Ω) :
    (∑ i, (tailWeights q a).mass i) = 1 - q.mass a := by
  have hs := tailWeights_sum_erase q a Finset.univ (fun _ => 1)
  simp only [mul_one] at hs
  have ha := Finset.sum_erase_add (s := Finset.univ) q.mass (Finset.mem_univ a)
  rw [q.total] at ha
  linarith

theorem head_not_coarse (a : Ω) (x : Ω → ℝ) (η : ℝ) (ha : x a = 1) (hη : 0 ≤ η) :
    a ∉ coarseLabels x η := by
  intro h
  have hlt := (Finset.mem_filter.mp h).2
  rw [ha] at hlt
  linarith

theorem tail_coarseWeightSum (q : Probability Ω) (a : Ω) (x : Ω → ℝ) (η : ℝ)
    (ha : x a = 1) (hη : 0 ≤ η) :
    coarseWeightSum (tailWeights q a) x η = ∑ i ∈ coarseLabels x η, q.mass i ^ ((2 : ℝ) / 3) := by
  apply Finset.sum_congr rfl
  intro i hi
  have hia : i ≠ a := by intro h; subst i; exact head_not_coarse a x η ha hη hi
  simp only [tailWeights, if_neg hia]

theorem tail_radius_split (q : Probability Ω) (a : Ω) (x : Ω → ℝ) (η ε g : ℝ)
    (hradius : (∑ i, (tailWeights q a).mass i * x i) + g = ε) :
    ε = coarseDisplacement (tailWeights q a) x η + (∑ i ∈ fineLabels a x η, q.mass i) -
      concentratedResidual (tailWeights q a) x η + g := by
  have hs := allocation_radius_split (tailWeights q a) x η ε g hradius
  have hm := tailWeights_sum_erase q a (concentratedLabels x η) (fun _ => 1)
  simp only [mul_one] at hm
  simpa only [hm, fineLabels] using hs

theorem fine_mass_le_tail (q : Probability Ω) (a : Ω) (x : Ω → ℝ) (η : ℝ) :
    (∑ i ∈ fineLabels a x η, q.mass i) ≤ 1 - q.mass a := by
  have hs : (∑ i ∈ fineLabels a x η, q.mass i) ≤ ∑ i ∈ Finset.univ.erase a, q.mass i := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro i hi
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hi).1, Finset.mem_univ i⟩
    · intro i _ _
      exact q.nonneg i
  have ha := Finset.sum_erase_add (s := Finset.univ) q.mass (Finset.mem_univ a)
  rw [q.total] at ha
  linarith

end IdentityTesting.HeavyUpper
