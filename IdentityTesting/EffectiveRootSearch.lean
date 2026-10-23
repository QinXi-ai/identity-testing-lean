import IdentityTesting.EffectiveAllocationOracle
import IdentityTesting.GeneralAllocationRoots
import Mathlib.Data.Rat.Encodable

/-! A computable search for strict rational root brackets. The search enumerates
rational endpoints and precision together; strict monotonicity proves termination.
All decisions made by the executable search are comparisons of rational numbers. -/
open scoped BigOperators
open Filter Topology Set
namespace IdentityTesting.RationalComputation

abbrev RootCandidate := ℚ × ℚ × ℕ

def rootCandidate (n : ℕ) : RootCandidate :=
  (Encodable.decode (α := RootCandidate) n).getD (0, 0, 0)

theorem rootCandidate_encode (c : RootCandidate) : rootCandidate (Encodable.encode c) = c := by
  simp [rootCandidate, Encodable.encodek]

def RootCertificate {f : ℝ → ℝ} {e : ℝ} (V : EffectiveFunctionAccess f)
    (E : EffectiveRealAccess e) (ε : ℚ) (c : RootCandidate) : Prop :=
  0 < c.1 ∧ c.1 < c.2.1 ∧ c.2.1 - c.1 ≤ ε ∧
    E.approx c.2.2 + accessError c.2.2 < (V.interval c.1 c.2.2).1 ∧
    (V.interval c.2.1 c.2.2).2 < E.approx c.2.2 - accessError c.2.2

instance {f : ℝ → ℝ} {e : ℝ} (V : EffectiveFunctionAccess f)
    (E : EffectiveRealAccess e) (ε : ℚ) (c : RootCandidate) :
    Decidable (RootCertificate V E ε c) := by
  unfold RootCertificate
  infer_instance

theorem exists_rootCertificate {f : ℝ → ℝ} {e T : ℝ}
    (V : EffectiveFunctionAccess f) (E : EffectiveRealAccess e) (ε : ℚ) (hε : 0 < ε)
    (hT : 0 < T) (hroot : f T = e) (hmono : StrictAntiOn f (Ioi 0)) :
    ∃ n : ℕ, RootCertificate V E ε (rootCandidate n) := by
  have hεR : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  obtain ⟨l, hll, hlT⟩ := exists_rat_btwn
    (show max 0 (T - (ε : ℝ) / 2) < T from max_lt hT (by linarith))
  obtain ⟨u, hTu, huu⟩ := exists_rat_btwn
    (show T < T + (ε : ℝ) / 2 by linarith)
  have hl0 : (0 : ℝ) < (l : ℝ) := (le_max_left _ _).trans_lt hll
  have hu0 : (0 : ℝ) < (u : ℝ) := hT.trans hTu
  have hlg : 0 < f l - e := by linarith [hmono hl0 hT hlT]
  have hug : 0 < e - f u := by linarith [hmono hT hu0 hTu]
  obtain ⟨n, hn⟩ := (accessError_tendsto.eventually_lt_const
    (show (0 : ℝ) < min (f l - e) (e - f u) / 4 by positivity)).exists
  have hlQ : (0 : ℚ) < l := by exact_mod_cast hl0
  have huQ : (0 : ℚ) < u := by exact_mod_cast hu0
  obtain ⟨hllow, hlup, hlwidth⟩ := V.valid l n hlQ
  obtain ⟨hulow, huup, huwidth⟩ := V.valid u n huQ
  have hlw : ((V.interval l n).2 : ℝ) - ((V.interval l n).1 : ℝ) ≤
      (accessError n : ℝ) := by exact_mod_cast hlwidth
  have huw : ((V.interval u n).2 : ℝ) - ((V.interval u n).1 : ℝ) ≤
      (accessError n : ℝ) := by exact_mod_cast huwidth
  have he := abs_le.mp (E.error_le n)
  have hgapl : 4 * (accessError n : ℝ) < f l - e := by
    linarith [min_le_left (f l - e) (e - f u)]
  have hgapu : 4 * (accessError n : ℝ) < e - f u := by
    linarith [min_le_right (f l - e) (e - f u)]
  refine ⟨Encodable.encode (l, u, n), ?_⟩
  rw [rootCandidate_encode]
  refine ⟨hlQ, by exact_mod_cast hlT.trans hTu, ?_, ?_, ?_⟩
  · have h : (u : ℝ) - (l : ℝ) ≤ (ε : ℝ) := by
      linarith [le_max_right 0 (T - (ε : ℝ) / 2)]
    exact_mod_cast h
  · have h : (E.approx n : ℝ) + (accessError n : ℝ) < ((V.interval l n).1 : ℝ) := by
      linarith
    exact_mod_cast h
  · have h : ((V.interval u n).2 : ℝ) < (E.approx n : ℝ) - (accessError n : ℝ) := by
      linarith
    exact_mod_cast h

def effectiveRootInterval {f : ℝ → ℝ} {e T : ℝ}
    (V : EffectiveFunctionAccess f) (E : EffectiveRealAccess e) (ε : ℚ) (hε : 0 < ε)
    (hT : 0 < T) (hroot : f T = e) (hmono : StrictAntiOn f (Ioi 0)) : ℚ × ℚ :=
  let n := (certifiedNatSearch _ (exists_rootCertificate V E ε hε hT hroot hmono)).val
  let c := rootCandidate n
  (c.1, c.2.1)

set_option maxHeartbeats 800000 in
theorem effectiveRootInterval_spec {f : ℝ → ℝ} {e T : ℝ}
    (V : EffectiveFunctionAccess f) (E : EffectiveRealAccess e) (ε : ℚ) (hε : 0 < ε)
    (hT : 0 < T) (hroot : f T = e) (hmono : StrictAntiOn f (Ioi 0)) :
    let I := effectiveRootInterval V E ε hε hT hroot hmono
    0 < I.1 ∧ (I.1 : ℝ) < T ∧ T < (I.2 : ℝ) ∧ I.2 - I.1 ≤ ε := by
  let n := (certifiedNatSearch _ (exists_rootCertificate V E ε hε hT hroot hmono)).val
  let c := rootCandidate n
  have hc : RootCertificate V E ε c := certifiedNatSearch_spec _
    (exists_rootCertificate V E ε hε hT hroot hmono)
  obtain ⟨hl0, hlu, hw, hlcert, hucert⟩ := hc
  have hlR : (0 : ℝ) < (c.1 : ℝ) := by exact_mod_cast hl0
  have huR : (0 : ℝ) < (c.2.1 : ℝ) := by exact_mod_cast hl0.trans hlu
  have hL := V.valid c.1 c.2.2 hl0
  have hU := V.valid c.2.1 c.2.2 (hl0.trans hlu)
  have hE := abs_le.mp (E.error_le c.2.2)
  have hlc : (E.approx c.2.2 : ℝ) + (accessError c.2.2 : ℝ) <
      ((V.interval c.1 c.2.2).1 : ℝ) := by exact_mod_cast hlcert
  have huc : ((V.interval c.2.1 c.2.2).2 : ℝ) <
      (E.approx c.2.2 : ℝ) - (accessError c.2.2 : ℝ) := by exact_mod_cast hucert
  have hlv : e < f c.1 := by linarith [hL.1]
  have huv : f c.2.1 < e := by linarith [hU.2.1]
  change 0 < c.1 ∧ (c.1 : ℝ) < T ∧ T < (c.2.1 : ℝ) ∧ c.2.1 - c.1 ≤ ε
  refine ⟨hl0, ?_, ?_, hw⟩
  · by_contra hn
    have h := hmono.antitoneOn hT hlR (le_of_not_gt hn)
    linarith
  · by_contra hn
    have h := hmono.antitoneOn huR hT (le_of_not_gt hn)
    linarith

/-- Actual original-input ordinary root algorithm. The target may be any
computable real strictly between zero and the full original total mass. -/
def countableAllocationRootInterval {a : ℕ → ℝ} {e : ℝ}
    (A : EffectiveMassAccess a) (E : EffectiveRealAccess e)
    (ha : ∀ i, 0 ≤ a i) (hs : Summable a) (he : 0 < e) (her : e < ∑' i, a i)
    (ε : ℚ) (hε : 0 < ε) : ℚ × ℚ :=
  effectiveRootInterval (countableAllocationAccess A ha hs) E ε hε
    (generalAllocationRoot_spec ha hs he her).1
    (generalAllocationRoot_spec ha hs he her).2
    (allocationD_strictAntiOn ha hs (exists_positive_of_positive_tsum ha (he.trans her)))

theorem countableAllocationRootInterval_spec {a : ℕ → ℝ} {e : ℝ}
    (A : EffectiveMassAccess a) (E : EffectiveRealAccess e)
    (ha : ∀ i, 0 ≤ a i) (hs : Summable a) (he : 0 < e) (her : e < ∑' i, a i)
    (ε : ℚ) (hε : 0 < ε) :
    let I := countableAllocationRootInterval A E ha hs he her ε hε
    0 < I.1 ∧ (I.1 : ℝ) < generalAllocationRoot a e ∧
      generalAllocationRoot a e < (I.2 : ℝ) ∧ I.2 - I.1 ≤ ε :=
  effectiveRootInterval_spec _ _ _ _ _ _ _

end IdentityTesting.RationalComputation
