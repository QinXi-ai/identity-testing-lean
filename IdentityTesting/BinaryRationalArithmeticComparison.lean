import IdentityTesting.BinaryRationalArithmeticSubtractor
import IdentityTesting.BinaryRationalArithmeticCanonical

/-! Rational comparison is computed by actual subtraction followed by reading
the canonical sign and zero marker. The Boolean result is emitted as a rational
0/1 record by charged single-cell writes. -/
namespace IdentityTesting.BinaryRationalArithmeticComparison
open BinaryArithmetic RationalComputation

inductive Phase where
  | running | decideResult | denominator | halt
  deriving DecidableEq, Repr

structure State where
  phase : Phase
  core : BinaryRationalArithmeticSubtractor.State
  numerator : List Bool
  denominator : List Bool
  deriving DecidableEq, Repr

def initial (p q : BinaryRationalArithmetic.Word) : State :=
  ⟨.running,BinaryRationalArithmeticSubtractor.initial p q,[],[]⟩

def nonpositive (s : BinaryRationalArithmeticSubtractor.State) : Prop :=
  (BinaryRationalArithmeticSubtractor.output s).numerator.negative = true ∨
    (BinaryRationalArithmeticSubtractor.output s).numerator.magnitude = []

instance (s : BinaryRationalArithmeticSubtractor.State) : Decidable (nonpositive s) := by
  unfold nonpositive
  infer_instance

def step (s : State) : State :=
  match s.phase with
  | .running => if s.core.phase = .halt then { s with phase := .decideResult }
      else { s with core := BinaryRationalArithmeticSubtractor.step s.core }
  | .decideResult => { s with phase := .denominator, numerator := if nonpositive s.core then true :: s.numerator else s.numerator }
  | .denominator => { s with phase := .halt, denominator := true :: s.denominator }
  | .halt => s

def output (s : State) : BinaryRationalArithmetic.Word := ⟨⟨false,s.numerator⟩,s.denominator⟩

def advance : ℕ → State → State
  | 0,s => s
  | n+1,s => advance n (step s)

theorem advance_add (m n : ℕ) (s : State) : advance (m+n) s = advance n (advance m s) := by
  induction m generalizing s with
  | zero => simp [advance]
  | succ m ih => simpa [Nat.succ_add,advance] using ih (step s)

def transitionTrace (s : State) : List BitOp :=
  match s.phase with
  | .running => if s.core.phase = .halt then [.branch]
      else .branch :: BinaryRationalArithmeticSubtractor.transitionTrace s.core
  | .decideResult => [.readCell,.readCell,.branch,.writeCell,.moveHead]
  | .denominator => [.writeCell,.moveHead]
  | .halt => []

def bitSteps : ℕ → State → ℕ
  | 0,_ => 0
  | n+1,s => (transitionTrace s).length+bitSteps n (step s)

theorem bitSteps_add (m n : ℕ) (s : State) :
    bitSteps (m+n) s = bitSteps m s+bitSteps n (advance m s) := by
  induction m generalizing s with
  | zero => simp [advance,bitSteps]
  | succ m ih =>
      simpa [Nat.succ_add,advance,bitSteps,Nat.add_assoc] using
        congrArg ((transitionTrace s).length+·) (ih (step s))

private theorem core_halt (k : ℕ) (s : BinaryRationalArithmeticSubtractor.State) (h : s.phase = .halt) :
    BinaryRationalArithmeticSubtractor.advance k s = s := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [BinaryRationalArithmeticSubtractor.advance,BinaryRationalArithmeticSubtractor.step,h] using ih

theorem forward (s : BinaryRationalArithmeticSubtractor.State) (k : ℕ)
    (h : (BinaryRationalArithmeticSubtractor.advance k s).phase = .halt) :
    ∃ j, j ≤ k+1 ∧ advance j ⟨.running,s,[],[]⟩ =
      ⟨.decideResult,BinaryRationalArithmeticSubtractor.advance k s,[],[]⟩ ∧
      bitSteps j ⟨.running,s,[],[]⟩ ≤ 2*BinaryRationalArithmeticSubtractor.bitSteps k s+1 := by
  induction k generalizing s with
  | zero =>
      simp only [BinaryRationalArithmeticSubtractor.advance] at h
      refine ⟨1,by omega,?_,?_⟩
      · simp [advance,step,h,BinaryRationalArithmeticSubtractor.advance]
      · simp [bitSteps,transitionTrace,h,BinaryRationalArithmeticSubtractor.bitSteps]
  | succ k ih =>
      by_cases hh : s.phase = .halt
      · refine ⟨1,by omega,?_,?_⟩
        · rw [core_halt (k+1) s hh]
          simp [advance,step,hh]
        · simp [bitSteps,transitionTrace,hh]
      · obtain ⟨j,hj,he,hc⟩ := ih (BinaryRationalArithmeticSubtractor.step s) h
        refine ⟨j+1,by omega,?_,?_⟩
        · rw [advance]
          simpa [step,hh,BinaryRationalArithmeticSubtractor.advance] using he
        · have ht : 1 ≤ (BinaryRationalArithmeticSubtractor.transitionTrace s).length := by
            cases hp : s.phase <;> simp_all [BinaryRationalArithmeticSubtractor.transitionTrace]
            all_goals split <;> simp_all
          simp only [bitSteps,transitionTrace,step,if_neg hh,List.length_cons,
            BinaryRationalArithmeticSubtractor.bitSteps]
          omega

theorem binary_rational_comparison_machine (p q : ℚ) :
    ∃ steps, let s := initial (BinaryRationalArithmetic.encode p) (BinaryRationalArithmetic.encode q)
      (advance steps s).phase = .halt ∧
      output (advance steps s) = BinaryRationalArithmetic.encode (if p ≤ q then 1 else 0) ∧
      bitSteps steps s ≤ 5500000*(rationalEncodingLength p+rationalEncodingLength q+1)^3 := by
  let c := BinaryRationalArithmeticSubtractor.initial (BinaryRationalArithmetic.encode p) (BinaryRationalArithmetic.encode q)
  let s := initial (BinaryRationalArithmetic.encode p) (BinaryRationalArithmetic.encode q)
  obtain ⟨k,hh,hv,hm,hd,hz,hb⟩ := BinaryRationalArithmeticSubtractor.binary_rational_subtraction_machine p q
  let f := BinaryRationalArithmeticSubtractor.advance k c
  have he : BinaryRationalArithmeticSubtractor.output f = BinaryRationalArithmetic.encode (p-q) :=
    BinaryRationalArithmetic.canonical_word_eq_encode _ _ hv hm hd hz
  have ht : nonpositive f ↔ p ≤ q := by
    unfold nonpositive
    rw [he,BinaryRationalArithmetic.encoded_nonpositive,sub_nonpos]
  obtain ⟨j,hj,hr,hcost⟩ := forward c k hh
  change advance j s = ⟨.decideResult,f,[],[]⟩ at hr
  change bitSteps j s ≤ 2*BinaryRationalArithmeticSubtractor.bitSteps k c+1 at hcost
  have hw : advance (j+2) s = advance 2 ⟨.decideResult,f,[],[]⟩ := by rw [advance_add,hr]
  refine ⟨j+2,?_,?_,?_⟩
  · change (advance (j+2) s).phase = _
    rw [hw]
    simp [advance,step]
  · change output (advance (j+2) s) = _
    rw [hw]
    by_cases hp : p ≤ q
    · have ht' := ht.mpr hp
      norm_num [advance,step,output,ht',hp,BinaryRationalArithmetic.encode,BinarySignedWords.encode]
    · have ht' : ¬ nonpositive f := by simpa only [ht] using hp
      norm_num [advance,step,output,ht',hp,BinaryRationalArithmetic.encode,BinarySignedWords.encode]
  · change bitSteps (j+2) s ≤ _
    rw [bitSteps_add,hr]
    have ht' : bitSteps 2 ⟨.decideResult,f,[],[]⟩ = 7 := by simp [bitSteps,transitionTrace,step]
    rw [ht']
    change BinaryRationalArithmeticSubtractor.bitSteps k c ≤
      2700000*(rationalEncodingLength p+rationalEncodingLength q+1)^3 at hb
    have hone : 0 < (rationalEncodingLength p+rationalEncodingLength q+1)^3 := by positivity
    omega

end IdentityTesting.BinaryRationalArithmeticComparison
