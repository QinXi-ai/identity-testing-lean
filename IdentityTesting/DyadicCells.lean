import IdentityTesting.DyadicGeometry
import IdentityTesting.FiniteSampleMaps
import IdentityTesting.SeedAllocation

/-! Actual occupied cells, their positive masses and normalized conditional laws. -/

noncomputable section
namespace IdentityTesting.EmpiricalSeeds
open scoped BigOperators
open Classical
open FiniteTesting

variable {ι : Type*} [Fintype ι]

def OccupiedCells (j : ι → ℕ) := {l : ℕ // l ∈ Finset.univ.image j}

instance occupiedCellsFintype (j : ι → ℕ) : Fintype (OccupiedCells j) :=
  inferInstanceAs (Fintype {l : ℕ // l ∈ Finset.univ.image j})

def cellOf (j : ι → ℕ) (i : ι) : OccupiedCells j :=
  ⟨j i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩

theorem cellOf_surjective (j : ι → ℕ) : Function.Surjective (cellOf j) := by
  intro l
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp l.property
  exact ⟨i, Subtype.ext hi⟩

instance occupiedCellsNonempty [Nonempty ι] (j : ι → ℕ) : Nonempty (OccupiedCells j) :=
  ⟨cellOf j (Classical.arbitrary ι)⟩

def cellMass (a : ι → ℝ) (j : ι → ℕ) (l : OccupiedCells j) : ℝ :=
  ∑ i, if cellOf j i = l then a i else 0

theorem cellMass_nonneg {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i)
    (j : ι → ℕ) (l : OccupiedCells j) : 0 ≤ cellMass a j l := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs <;> first | exact ha i | exact le_rfl

theorem cellMass_pos {a : ι → ℝ} (ha : ∀ i, 0 < a i)
    (j : ι → ℕ) (l : OccupiedCells j) : 0 < cellMass a j l := by
  obtain ⟨i, hi⟩ := cellOf_surjective j l
  apply (ha i).trans_le
  calc
    a i = (if cellOf j i = l then a i else 0) := (if_pos hi).symm
    _ ≤ cellMass a j l := by
      apply Finset.single_le_sum (f := fun i => if cellOf j i = l then a i else 0)
        (s := Finset.univ) ?_ (Finset.mem_univ i)
      intro x _
      dsimp only
      split_ifs <;> first | exact (ha x).le | exact le_rfl

theorem sum_cellMass (a : ι → ℝ) (j : ι → ℕ) :
    (∑ l, cellMass a j l) = ∑ i, a i := by
  unfold cellMass
  rw [Finset.sum_comm]
  simp

def cellLaw (a : ι → ℝ) (ha : ∀ i, 0 < a i) (j : ι → ℕ)
    (l : OccupiedCells j) : Probability ι where
  mass i := if cellOf j i = l then a i / cellMass a j l else 0
  nonneg i := by
    split_ifs
    · exact div_nonneg (ha i).le (cellMass_pos ha j l).le
    · exact le_rfl
  total := by
    calc
      (∑ i, if cellOf j i = l then a i / cellMass a j l else 0) =
          ∑ i, (if cellOf j i = l then a i else 0) / cellMass a j l := by
        apply Finset.sum_congr rfl
        intro i _
        split_ifs <;> simp
      _ = 1 := by
        rw [← Finset.sum_div]
        exact div_self (cellMass_pos ha j l).ne'

theorem cellLaw_positive_iff (a : ι → ℝ) (ha : ∀ i, 0 < a i) (j : ι → ℕ)
    (l : OccupiedCells j) (i : ι) :
    0 < (cellLaw a ha j l).mass i ↔ cellOf j i = l := by
  dsimp only [cellLaw]
  by_cases h : cellOf j i = l
  · simp only [h, ite_true, iff_true]
    exact div_pos (ha i) (cellMass_pos ha j l)
  · simp [h]

def cellWeights (q : Probability ι) (j : ι → ℕ) : Probability (OccupiedCells j) where
  mass := cellMass q.mass j
  nonneg := cellMass_nonneg q.nonneg j
  total := (sum_cellMass q.mass j).trans q.total

/-- The actual mixture of the normalized cell conditionals is the original law. -/
theorem mixture_cellLaw (q : Probability ι) (hq : ∀ i, 0 < q.mass i) (j : ι → ℕ) :
    mixture (cellWeights q j) (cellLaw q.mass hq j) = q := by
  apply probability_ext
  intro i
  change (∑ l, cellMass q.mass j l *
    (if cellOf j i = l then q.mass i / cellMass q.mass j l else 0)) = q.mass i
  calc
    (∑ l, cellMass q.mass j l *
        (if cellOf j i = l then q.mass i / cellMass q.mass j l else 0)) =
        ∑ l, if cellOf j i = l then q.mass i else 0 := by
      apply Finset.sum_congr rfl
      intro l _
      by_cases h : cellOf j i = l
      · simp only [h, ite_true]
        field_simp [(cellMass_pos hq j l).ne']
      · simp [h]
    _ = q.mass i := by simp

theorem cell_seedMoment_eq (a : ι → ℝ) (j : ι → ℕ) (b : ℝ) :
    seedMoment (cellMass a j) (fun l => dyadicUpper b l.val) =
      ∑ i, a i * Real.sqrt (dyadicUpper b (j i)) := by
  simp only [seedMoment, cellMass, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp [cellOf]

theorem sum_cellUpper_le (j : ι → ℕ) {b : ℝ} (hb : 0 ≤ b) :
    (∑ l : OccupiedCells j, dyadicUpper b l.val) ≤ 2 * b := by
  change (∑ l : {l : ℕ // l ∈ Finset.univ.image j}, dyadicUpper b l.val) ≤ 2 * b
  rw [Finset.sum_coe_sort]
  exact sum_dyadicUpper_le hb _

end IdentityTesting.EmpiricalSeeds
