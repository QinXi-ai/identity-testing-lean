import IdentityTesting.PairedRootLowerBound
import IdentityTesting.AllocationGeometry
import Mathlib.Data.List.Sort
import Mathlib.Data.List.NodupEquivFin

/-!
# Actual adjacent pairing of a mass-sorted finite set

Mass ties are allowed. Merge sort constructs the ordering; adjacent labels are
then separated into left and right lists, with at most one leftover label.
-/

noncomputable section
open scoped BigOperators

namespace IdentityTesting.SortedPairing

variable {α : Type*}

def leftLabels : List α → List α
  | a :: _ :: l => a :: leftLabels l
  | _ => []

def rightLabels : List α → List α
  | _ :: b :: l => b :: rightLabels l
  | _ => []

def leftoverLabels : List α → List α
  | [] => []
  | [a] => [a]
  | _ :: _ :: l => leftoverLabels l

def headValue (f : α → ℝ) : List α → ℝ
  | [] => 0
  | a :: _ => f a

theorem pairing_lengths (l : List α) : (leftLabels l).length = (rightLabels l).length := by
  cases l with
  | nil => rfl
  | cons a l =>
    cases l with
    | nil => rfl
    | cons b l => simpa only [leftLabels, rightLabels, List.length_cons] using congrArg Nat.succ (pairing_lengths l)
termination_by l.length

theorem pairing_perm (l : List α) :
    (leftLabels l ++ rightLabels l ++ leftoverLabels l).Perm l := by
  cases l with
  | nil => simp [leftLabels, rightLabels, leftoverLabels]
  | cons a l =>
    cases l with
    | nil => simp [leftLabels, rightLabels, leftoverLabels]
    | cons b l =>
      simp only [leftLabels, rightLabels, leftoverLabels, List.cons_append]
      apply List.Perm.cons a
      have hm : (leftLabels l ++ b :: (rightLabels l ++ leftoverLabels l)).Perm
          (b :: (leftLabels l ++ (rightLabels l ++ leftoverLabels l))) := List.perm_middle
      have ih : (b :: (leftLabels l ++ (rightLabels l ++ leftoverLabels l))).Perm (b :: l) := by
        simpa only [List.append_assoc] using (pairing_perm l).cons b
      simpa only [List.append_assoc] using hm.trans ih
termination_by l.length

theorem pairing_order (q : α → ℝ) (l : List α)
    (hl : l.Pairwise (fun a b => q b ≤ q a)) :
    List.Forall₂ (fun a b => q b ≤ q a) (leftLabels l) (rightLabels l) := by
  cases l with
  | nil => exact .nil
  | cons a l =>
    cases l with
    | nil => exact .nil
    | cons b l =>
      obtain ⟨ha, htail⟩ := List.pairwise_cons.mp hl
      exact .cons (ha b (by simp))
        (pairing_order q l (List.pairwise_cons.mp htail).2)
termination_by l.length

/-- Every term after the first is charged to a paired right endpoint at most
twice. The final unpaired term is covered by its preceding right endpoint. -/
theorem sorted_tail_sum_le (f : α → ℝ) (l : List α)
    (hf : ∀ a ∈ l, 0 ≤ f a) (hl : l.Pairwise (fun a b => f b ≤ f a)) :
    (l.map f).sum - headValue f l ≤ 2 * ((rightLabels l).map f).sum := by
  cases l with
  | nil => simp [headValue, rightLabels]
  | cons a l =>
    cases l with
    | nil => simp [headValue, rightLabels]
    | cons b l =>
      have htail := (List.pairwise_cons.mp (List.pairwise_cons.mp hl).2).2
      have ih := sorted_tail_sum_le f l
        (fun c hc => hf c (by simp [hc])) htail
      have hhead : headValue f l ≤ f b := by
        cases l with
        | nil => exact hf b (by simp)
        | cons c l =>
          exact (List.pairwise_cons.mp (List.pairwise_cons.mp hl).2).1 c (by simp)
      simp only [List.map_cons, List.sum_cons, headValue, rightLabels] at ih hhead ⊢
      linarith only [ih, hhead]
termination_by l.length

theorem sorted_amplitude_sum_ge (f : α → ℝ) (l : List α)
    (hf : ∀ a ∈ l, 0 ≤ f a) (hl : l.Pairwise (fun a b => f b ≤ f a))
    (hhead : headValue f l ≤ (l.map f).sum / 2) :
    2 * (l.map f).sum ≤ ((rightLabels l).map (fun a => 8 * f a)).sum := by
  have h := sorted_tail_sum_le f l hf hl
  have heq : ((rightLabels l).map (fun a => 8 * f a)).sum =
      8 * ((rightLabels l).map f).sum := by
    simp only [← List.sum_map_mul_left]
  rw [heq]
  linarith only [h, hhead]

def sortedLabels (q : α → ℝ) (s : Finset α) : List α :=
  s.toList.mergeSort (fun a b => q b ≤ q a)

theorem sortedLabels_perm (q : α → ℝ) (s : Finset α) :
    (sortedLabels q s).Perm s.toList := List.mergeSort_perm _ _

theorem sortedLabels_sorted (q : α → ℝ) (s : Finset α) :
    (sortedLabels q s).Pairwise (fun a b => q b ≤ q a) := by
  letI : IsTrans α (fun a b => q b ≤ q a) := ⟨fun a b c hab hbc => hbc.trans hab⟩
  letI : IsTotal α (fun a b => q b ≤ q a) := ⟨fun a b => le_total _ _⟩
  exact List.sorted_mergeSort' (fun a b => q b ≤ q a) s.toList

theorem sortedLabels_nodup (q : α → ℝ) (s : Finset α) :
    (sortedLabels q s).Nodup := (sortedLabels_perm q s).nodup_iff.mpr s.nodup_toList

theorem mem_sortedLabels (q : α → ℝ) (s : Finset α) (a : α) :
    a ∈ sortedLabels q s ↔ a ∈ s := by
  rw [(sortedLabels_perm q s).mem_iff, Finset.mem_toList]

theorem sum_sortedLabels (q f : α → ℝ) (s : Finset α) :
    ((sortedLabels q s).map f).sum = ∑ a ∈ s, f a := by
  rw [((sortedLabels_perm q s).map f).sum_eq]
  exact Finset.sum_map_toList s f

variable {k : ℕ}

def pairCount (q : Fin k → ℝ) (s : Finset (Fin k)) : ℕ :=
  (leftLabels (sortedLabels q s)).length

def untouchedCount (q : Fin k → ℝ) (s : Finset (Fin k)) : ℕ :=
  (leftoverLabels (sortedLabels q s) ++ sᶜ.toList).length

def blockList (q : Fin k → ℝ) (s : Finset (Fin k)) : List (Fin k) :=
  leftLabels (sortedLabels q s) ++
    (rightLabels (sortedLabels q s) ++ (leftoverLabels (sortedLabels q s) ++ sᶜ.toList))

theorem blockList_perm (q : Fin k → ℝ) (s : Finset (Fin k)) :
    (blockList q s).Perm (sortedLabels q s ++ sᶜ.toList) := by
  simpa only [blockList, List.append_assoc] using (pairing_perm (sortedLabels q s)).append_right sᶜ.toList

theorem blockList_nodup (q : Fin k → ℝ) (s : Finset (Fin k)) : (blockList q s).Nodup := by
  apply (blockList_perm q s).nodup_iff.mpr
  apply (sortedLabels_nodup q s).append sᶜ.nodup_toList
  apply List.disjoint_left.mpr
  intro a ha hb
  exact (Finset.mem_compl.mp (Finset.mem_toList.mp hb)) ((mem_sortedLabels q s a).mp ha)

theorem blockList_allmem (q : Fin k → ℝ) (s : Finset (Fin k)) (a : Fin k) : a ∈ blockList q s := by
  apply (blockList_perm q s).mem_iff.mpr
  by_cases ha : a ∈ s
  · exact List.mem_append_left _ ((mem_sortedLabels q s a).mpr ha)
  · exact List.mem_append_right _ (Finset.mem_toList.mpr (Finset.mem_compl.mpr ha))

theorem blockList_length (q : Fin k → ℝ) (s : Finset (Fin k)) :
    pairCount q s + (pairCount q s + untouchedCount q s) = (blockList q s).length := by
  simp only [blockList, pairCount, untouchedCount, List.length_append, pairing_lengths]

/-- A constructed finite equivalence realizes the actual sorted adjacent pairs
and leaves the odd final selected label and every unselected label untouched. -/
def blockEquiv (q : Fin k → ℝ) (s : Finset (Fin k)) :
    Fin (pairCount q s + (pairCount q s + untouchedCount q s)) ≃ Fin k :=
  (finCongr (blockList_length q s)).trans
    ((blockList_nodup q s).getEquivOfForallMemList (blockList q s) (blockList_allmem q s))

theorem blockEquiv_left (q : Fin k → ℝ) (s : Finset (Fin k)) (j : Fin (pairCount q s)) :
    blockEquiv q s (PairedPerturbation.leftIndex j) =
      (leftLabels (sortedLabels q s)).get j := by
  simp [blockEquiv, blockList, PairedPerturbation.leftIndex, List.get_eq_getElem, pairCount]

theorem blockEquiv_right (q : Fin k → ℝ) (s : Finset (Fin k)) (j : Fin (pairCount q s)) :
    blockEquiv q s (PairedPerturbation.rightIndex j) =
      (rightLabels (sortedLabels q s)).get (Fin.cast (pairing_lengths _) j) := by
  have hj : j.val < (rightLabels (sortedLabels q s)).length := by
    rw [← pairing_lengths]
    exact j.isLt
  simp [blockEquiv, blockList, PairedPerturbation.rightIndex, List.get_eq_getElem,
    pairCount, hj]

theorem blockEquiv_right_mem (q : Fin k → ℝ) (s : Finset (Fin k)) (j : Fin (pairCount q s)) :
    blockEquiv q s (PairedPerturbation.rightIndex j) ∈ s := by
  rw [blockEquiv_right]
  apply (mem_sortedLabels q s _).mp
  apply (pairing_perm (sortedLabels q s)).mem_iff.mp
  exact List.mem_append_left _ (List.mem_append_right _ (List.get_mem _ _))

theorem blockEquiv_left_mem (q : Fin k → ℝ) (s : Finset (Fin k)) (j : Fin (pairCount q s)) :
    blockEquiv q s (PairedPerturbation.leftIndex j) ∈ s := by
  rw [blockEquiv_left]
  apply (mem_sortedLabels q s _).mp
  apply (pairing_perm (sortedLabels q s)).mem_iff.mp
  exact List.mem_append_left _ (List.mem_append_left _ (List.get_mem _ _))

theorem blockEquiv_mass_order (q : Fin k → ℝ) (s : Finset (Fin k)) (j : Fin (pairCount q s)) :
    q (blockEquiv q s (PairedPerturbation.rightIndex j)) ≤
      q (blockEquiv q s (PairedPerturbation.leftIndex j)) := by
  rw [blockEquiv_right, blockEquiv_left]
  exact (pairing_order q (sortedLabels q s) (sortedLabels_sorted q s)).get j.isLt _

theorem sum_blockEquiv_right (q f : Fin k → ℝ) (s : Finset (Fin k)) :
    (∑ j : Fin (pairCount q s), f (blockEquiv q s (PairedPerturbation.rightIndex j))) =
      ((rightLabels (sortedLabels q s)).map f).sum := by
  simp only [blockEquiv_right]
  calc
    _ = ∑ j : Fin ((rightLabels (sortedLabels q s)).length),
        f ((rightLabels (sortedLabels q s)).get j) :=
      (finCongr (pairing_lengths (sortedLabels q s))).sum_comp _
    _ = _ := by
      rw [← List.sum_ofFn, List.ofFn_comp', List.ofFn_get]

theorem sorted_pairing_amplitude_sum_ge (q f : Fin k → ℝ) (s : Finset (Fin k))
    (hf : ∀ i, 0 ≤ f i) (hmono : ∀ i j, q i ≤ q j → f i ≤ f j)
    (hmax : ∀ i ∈ s, f i ≤ (∑ j ∈ s, f j) / 2) :
    2 * (∑ i ∈ s, f i) ≤
      ∑ j : Fin (pairCount q s), 8 * f (blockEquiv q s (PairedPerturbation.rightIndex j)) := by
  have hhead : headValue f (sortedLabels q s) ≤ ((sortedLabels q s).map f).sum / 2 := by
    rw [sum_sortedLabels]
    cases hl : sortedLabels q s with
    | nil =>
      simp only [headValue]
      exact div_nonneg (Finset.sum_nonneg (fun i _ => hf i)) (by norm_num)
    | cons a l =>
      exact hmax a ((mem_sortedLabels q s a).mp (by rw [hl]; simp))
  have h := sorted_amplitude_sum_ge f (sortedLabels q s) (fun a _ => hf a)
    ((sortedLabels_sorted q s).imp (fun {a b} hab => hmono b a hab)) hhead
  rw [sum_blockEquiv_right q (fun i => 8 * f i) s]
  simpa only [sum_sortedLabels] using h

theorem sorted_pairing_amplitude_bounds (q x : Fin k → ℝ) (s : Finset (Fin k))
    (hq : ∀ i, 0 ≤ q i) (hx : ∀ i, 0 ≤ x i)
    (hsmall : ∀ i ∈ s, x i ≤ (1 : ℝ) / 8) (j : Fin (pairCount q s)) :
    0 ≤ 8 * q (blockEquiv q s (PairedPerturbation.rightIndex j)) *
        x (blockEquiv q s (PairedPerturbation.rightIndex j)) ∧
      8 * q (blockEquiv q s (PairedPerturbation.rightIndex j)) *
        x (blockEquiv q s (PairedPerturbation.rightIndex j)) ≤
          q (blockEquiv q s (PairedPerturbation.leftIndex j)) ∧
      8 * q (blockEquiv q s (PairedPerturbation.rightIndex j)) *
        x (blockEquiv q s (PairedPerturbation.rightIndex j)) ≤
          q (blockEquiv q s (PairedPerturbation.rightIndex j)) := by
  exact allocation_pair_amplitude_bounds (hq _) (blockEquiv_mass_order q s j) (hx _)
    (hsmall _ (blockEquiv_right_mem q s j))

/-- The actual normalized signed alternatives on the original labels, with
the mass sorting, pairing and relabeling constructed internally. -/
def sortedPairedLaw (q : FiniteTesting.Probability (Fin k)) (x : Fin k → ℝ)
    (s : Finset (Fin k)) (hx : ∀ i, 0 ≤ x i)
    (hsmall : ∀ i ∈ s, x i ≤ (1 : ℝ) / 8)
    (σ : Fin (pairCount q.mass s) → Bool) : FiniteTesting.Probability (Fin k) :=
  PairedRelabeling.relabeledPairedLaw q (blockEquiv q.mass s)
    (fun j => 8 * q.mass (blockEquiv q.mass s (PairedPerturbation.rightIndex j)) *
      x (blockEquiv q.mass s (PairedPerturbation.rightIndex j)))
    (sorted_pairing_amplitude_bounds q.mass x s q.nonneg hx hsmall) σ

theorem sortedPairedLaw_mass_outside (q : FiniteTesting.Probability (Fin k)) (x : Fin k → ℝ)
    (s : Finset (Fin k)) (hx : ∀ i, 0 ≤ x i)
    (hsmall : ∀ i ∈ s, x i ≤ (1 : ℝ) / 8)
    (σ : Fin (pairCount q.mass s) → Bool) (i : Fin k) (hi : i ∉ s) :
    (sortedPairedLaw q x s hx hsmall σ).mass i = q.mass i := by
  obtain ⟨z, rfl⟩ := (blockEquiv q.mass s).surjective i
  revert hi
  refine Fin.addCases (fun j hi => False.elim (hi (blockEquiv_left_mem q.mass s j)))
    (fun rest => ?_) z
  refine Fin.addCases (fun j hi => False.elim (hi (blockEquiv_right_mem q.mass s j)))
    (fun j _ => ?_) rest
  change (sortedPairedLaw q x s hx hsmall σ).mass
      (blockEquiv q.mass s (PairedPerturbation.untouchedIndex j)) = _
  simp only [sortedPairedLaw, PairedRelabeling.relabeledPairedLaw_mass_apply,
    PairedPerturbation.pairedLaw_mass_untouched, PairedRelabeling.pullbackReference_mass]
  rfl

theorem sortedPairedLaw_mass_selected (q : FiniteTesting.Probability (Fin k)) (x : Fin k → ℝ)
    (s : Finset (Fin k)) (hx : ∀ i, 0 ≤ x i)
    (hsmall : ∀ i ∈ s, x i ≤ (1 : ℝ) / 8)
    (σ : Fin (pairCount q.mass s) → Bool) :
    (∑ i ∈ s, (sortedPairedLaw q x s hx hsmall σ).mass i) = ∑ i ∈ s, q.mass i := by
  have hp := Finset.sum_add_sum_compl s (sortedPairedLaw q x s hx hsmall σ).mass
  have hq := Finset.sum_add_sum_compl s q.mass
  rw [(sortedPairedLaw q x s hx hsmall σ).total] at hp
  rw [q.total] at hq
  have hcomp : (∑ i ∈ sᶜ, (sortedPairedLaw q x s hx hsmall σ).mass i) =
      ∑ i ∈ sᶜ, q.mass i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact sortedPairedLaw_mass_outside q x s hx hsmall σ i (Finset.mem_compl.mp hi)
  linarith only [hp, hq, hcomp]

theorem sortedPairedLaw_totalVariation (q : FiniteTesting.Probability (Fin k)) (x : Fin k → ℝ)
    (s : Finset (Fin k)) (hx : ∀ i, 0 ≤ x i)
    (hsmall : ∀ i ∈ s, x i ≤ (1 : ℝ) / 8)
    (σ : Fin (pairCount q.mass s) → Bool) :
    FiniteTesting.totalVariation (sortedPairedLaw q x s hx hsmall σ) q =
      ∑ j : Fin (pairCount q.mass s),
        8 * q.mass (blockEquiv q.mass s (PairedPerturbation.rightIndex j)) *
          x (blockEquiv q.mass s (PairedPerturbation.rightIndex j)) := by
  exact PairedRelabeling.relabeledPairedLaw_totalVariation _ _ _ _ _

theorem sortedPairedLaw_totalVariation_ge (q : FiniteTesting.Probability (Fin k)) (x : Fin k → ℝ)
    (s : Finset (Fin k)) (hx : ∀ i, 0 ≤ x i)
    (hsmall : ∀ i ∈ s, x i ≤ (1 : ℝ) / 8)
    (hgeometry : ∀ i j, q.mass i ≤ q.mass j → q.mass i * x i ≤ q.mass j * x j)
    (hmax : ∀ i ∈ s, q.mass i * x i ≤ (∑ j ∈ s, q.mass j * x j) / 2)
    (σ : Fin (pairCount q.mass s) → Bool) :
    2 * (∑ i ∈ s, q.mass i * x i) ≤
      FiniteTesting.totalVariation (sortedPairedLaw q x s hx hsmall σ) q := by
  rw [sortedPairedLaw_totalVariation]
  have h := sorted_pairing_amplitude_sum_ge q.mass (fun i => q.mass i * x i) s
    (fun i => mul_nonneg (q.nonneg i) (hx i)) hgeometry hmax
  simpa only [mul_assoc] using h

/-- Quantitative sample-TV bound for the constructed sorted prior, ready for
composition with the manuscript's common sample kernel. -/
theorem sortedPairedLaw_sample_totalVariation_lt
    (q : FiniteTesting.Probability (Fin k)) (x : Fin k → ℝ) (s : Finset (Fin k))
    (hx : ∀ i, 0 ≤ x i) (hsmall : ∀ i ∈ s, x i ≤ (1 : ℝ) / 8)
    {T : ℝ} (hT : 0 < T) (hq : ∀ i, 0 < q.mass i) (hx1 : ∀ i, x i < 1)
    (hbudget : T ^ 2 * (∑ i, (q.mass i) ^ 2 * (x i) ^ 4 / (1 - (x i) ^ 4)) = 1)
    (n : ℕ) (hn : (n : ℝ) ≤ (1 / (10 : ℝ) ^ 12) * T) :
    FiniteTesting.totalVariation
      (FiniteTesting.mixture (SignedDiagonalMoment.uniformSigns (pairCount q.mass s))
        (fun σ => FiniteTesting.productLaw (sortedPairedLaw q x s hx hsmall σ) n))
      (FiniteTesting.productLaw q n) < 1 / (10 : ℝ) ^ 9 := by
  apply relabeled_paired_mixture_totalVariation_lt_rate q (blockEquiv q.mass s)
    (fun j => 8 * q.mass (blockEquiv q.mass s (PairedPerturbation.rightIndex j)) *
      x (blockEquiv q.mass s (PairedPerturbation.rightIndex j)))
    (sorted_pairing_amplitude_bounds q.mass x s q.nonneg hx hsmall) hT n hq _ hn
  exact relabeledCoefficient_allocation_bound q (blockEquiv q.mass s) x hT hq
    (fun i => ⟨hx i, hx1 i⟩) (blockEquiv_mass_order q.mass s) hbudget

/-- The pairing and relabeling equivalence are constructed from the input
mass vector and selected set. No ordering or coverage certificate is supplied. -/
theorem no_identityTest_of_sorted_allocation_pairing
    (q : FiniteTesting.Probability (Fin k)) (x : Fin k → ℝ) (s : Finset (Fin k))
    {T : ℝ} (hT : 0 < T) (hq : ∀ i, 0 < q.mass i)
    (hx : ∀ i, 0 ≤ x i ∧ x i < 1)
    (hsmall : ∀ i ∈ s, x i ≤ (1 : ℝ) / 8)
    (hgeometry : ∀ i j, q.mass i ≤ q.mass j → q.mass i * x i ≤ q.mass j * x j)
    (hmax : ∀ i ∈ s, q.mass i * x i ≤ (∑ j ∈ s, q.mass j * x j) / 2)
    (hbudget : T ^ 2 * (∑ i, (q.mass i) ^ 2 * (x i) ^ 4 / (1 - (x i) ^ 4)) = 1)
    (ε : ℝ) (n : ℕ) (hsep : ε < 2 * (∑ i ∈ s, q.mass i * x i))
    (hn : (n : ℝ) ≤ (1 / (10 : ℝ) ^ 12) * T) :
    ¬ HasIdentityTest (extendFiniteLaw q) ε n := by
  apply no_identityTest_of_relabeled_allocation_pairing q (blockEquiv q.mass s) x hT hq hx
    (blockEquiv_mass_order q.mass s)
    (fun j => hsmall _ (blockEquiv_right_mem q.mass s j)) hbudget ε n _ hn
  have h := sorted_pairing_amplitude_sum_ge q.mass (fun i => q.mass i * x i) s
    (fun i => mul_nonneg (hq i).le (hx i).1) hgeometry hmax
  have hsep' := hsep.trans_le h
  simpa only [mul_assoc] using hsep'

/-- At the original allocation root, KKT geometry and the actual sorted
pairing are both constructed. The largest-displacement branch and strict TV
radius condition are the remaining mathematical case hypotheses. -/
theorem exists_original_root_sorted_pairing_lower_bound
    (q : FiniteTesting.Probability (Fin k)) (hq : ∀ i, 0 < q.mass i)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    0 < allocationRoot (extendFiniteLaw q) r ∧
      ∃ x : Fin k → ℝ, (∀ i, 0 < x i ∧ x i < 1) ∧
        (∑ i, q.mass i * x i) = r ∧
        (allocationRoot (extendFiniteLaw q) r) ^ 2 *
          (∑ i, (q.mass i) ^ 2 * (x i) ^ 4 / (1 - (x i) ^ 4)) = 1 ∧
        (∀ (ε : ℝ) (n : ℕ),
          (∀ i ∈ Finset.univ.filter (fun i => x i ≤ (1 : ℝ) / 8),
            q.mass i * x i ≤
              (∑ j ∈ Finset.univ.filter (fun j => x j ≤ (1 : ℝ) / 8), q.mass j * x j) / 2) →
          ε < 2 * (∑ i ∈ Finset.univ.filter (fun i => x i ≤ (1 : ℝ) / 8), q.mass i * x i) →
          (n : ℝ) ≤ (1 / (10 : ℝ) ^ 12) * allocationRoot (extendFiniteLaw q) r →
          ¬ HasIdentityTest (extendFiniteLaw q) ε n) := by
  obtain ⟨hT, x, β, hx, hsum, hbudget, hβ, hstationary, hfinal⟩ :=
    exists_finite_allocation_coordinates_at_root q hq hr0 hr1
  refine ⟨hT, x, hx, hsum, hbudget, ?_⟩
  intro ε n hmax hsep hn
  apply no_identityTest_of_sorted_allocation_pairing q x
    (Finset.univ.filter (fun i => x i ≤ (1 : ℝ) / 8)) hT hq
    (fun i => ⟨(hx i).1.le, (hx i).2⟩)
    (fun i hi => (Finset.mem_filter.mp hi).2) _ hmax hbudget ε n hsep hn
  intro i j hij
  exact (allocation_stationary_geometry (hq j) hβ (hx i).1 (hx i).2
    (hx j).1 (hx j).2 hij (hstationary i) (hstationary j)).2

end IdentityTesting.SortedPairing
