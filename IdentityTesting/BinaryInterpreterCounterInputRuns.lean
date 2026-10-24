import IdentityTesting.BinaryInterpreterCounterInput

namespace IdentityTesting.BinaryInterpreterCounterInput
open BinaryRegisterMachine BinaryRationalRegisters RationalComputation

theorem encode_nat (n : ℕ) : BinaryRationalArithmetic.encode (n:ℚ) = ⟨⟨false,n.bits⟩,[true]⟩ := by
  simp [BinaryRationalArithmetic.encode,BinarySignedWords.encode]

/-- The rational register is genuinely read. Only natural-valued inputs are
claimed: the numerator then equals floor(value), and the denominator is one. -/
theorem binary_natural_counter_load (s : RationalRegisters) (i : ℕ) (hi : i < s.length)
    (n : ℕ) (hn : (RationalOperand.reg i).read s = (n:ℚ)) :
    ∃ k, k ≤ 3*(rationalRegisterEncoding s+s.length)+2*rationalEncodingLength (n:ℚ)+12 ∧
      advance k (initial (tape s) (List.replicate i false)) = haltState (tape s) n.bits ∧
      bitSteps k (initial (tape s) (List.replicate i false)) ≤
        45*(rationalRegisterEncoding s+s.length)+30*rationalEncodingLength (n:ℚ)+180 := by
  have hv : s[i] = (n:ℚ) := by
    simpa only [RationalOperand.read,List.getElem?_eq_getElem hi,Option.getD_some] using hn
  obtain ⟨nr,hnr,hr⟩ := BinaryInterpreterCopy.load_steps s i hi
  rw [hv,encode_nat] at hr
  rw [hv,tape_length] at hnr
  have hh : (BinaryInterpreterRead.advance nr
      (BinaryInterpreterRead.initial (tape s) (List.replicate i false))).phase = .halt := by rw [hr]; rfl
  obtain ⟨k,hk,he⟩ := forward_read _ nr hh
  rw [hr] at he
  have htotal : advance (k+2) (initial (tape s) (List.replicate i false)) = haltState (tape s) n.bits := by
    change advance (k+2) (readingState (BinaryInterpreterRead.initial (tape s) (List.replicate i false))) = _
    rw [advance_add,he]
    rfl
  refine ⟨k+2,by omega,htotal,?_⟩
  have hb := bitSteps_le (k+2) (initial (tape s) (List.replicate i false))
  omega

theorem haltState_clean (tape : List Symbol) (bits : List Bool) : Clean (haltState tape bits) :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
theorem loaded_counter (tape : List Symbol) (n : ℕ) :
    counter (rearmTest (haltState tape n.bits)) = BinaryRationalArithmeticNatCounter.initialTest n.bits ∧
    counter (rearmPred (haltState tape n.bits)) = BinaryRationalArithmeticNatCounter.initialPred n.bits := ⟨rfl,rfl⟩

theorem loaded_floor (s : RationalRegisters) (i : ℕ) (hi : i < s.length)
    (n : ℕ) (hn : (RationalOperand.reg i).read s = (n:ℚ)) :
    ∃ k,
      advance k (initial (tape s) (List.replicate i false)) =
        haltState (tape s) (Nat.floor ((RationalOperand.reg i).read s)).bits ∧
      bitSteps k (initial (tape s) (List.replicate i false)) ≤
        45*(rationalRegisterEncoding s+s.length)+30*rationalEncodingLength ((RationalOperand.reg i).read s)+180 := by
  obtain ⟨k,_,hk,hc⟩ := binary_natural_counter_load s i hi n hn
  refine ⟨k,?_,?_⟩
  · simpa only [hn,Nat.floor_natCast] using hk
  · simpa only [hn] using hc

def countLift (frame : State) (c : BinaryRationalArithmeticNatCounter.State) : State :=
  {setCounter frame c with phase := .counting}
def countAfter (frame : State) (c : BinaryRationalArithmeticNatCounter.State) : State :=
  {setCounter frame c with phase := .halt}

theorem counter_set (frame : State) (c : BinaryRationalArithmeticNatCounter.State) :
    counter (setCounter frame c) = c := rfl
theorem count_step (frame : State) (c : BinaryRationalArithmeticNatCounter.State) (h : c.phase ≠ .halt) :
    step (countLift frame c) = countLift frame (BinaryRationalArithmeticNatCounter.step c) := by
  simp [step,countLift,setCounter,counter,h]
theorem count_halt (frame : State) (c : BinaryRationalArithmeticNatCounter.State) (h : c.phase = .halt) :
    step (countLift frame c) = countAfter frame c := by simp [step,countLift,countAfter,setCounter,h]
theorem inner_halt (n : ℕ) (c : BinaryRationalArithmeticNatCounter.State) (h : c.phase = .halt) :
    BinaryRationalArithmeticNatCounter.advance n c = c := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [BinaryRationalArithmeticNatCounter.advance,BinaryRationalArithmeticNatCounter.step,h] using ih

theorem forward_count (frame : State) (c : BinaryRationalArithmeticNatCounter.State) (n : ℕ)
    (h : (BinaryRationalArithmeticNatCounter.advance n c).phase = .halt) :
    ∃ k, k ≤ n+1 ∧ advance k (countLift frame c) = countAfter frame (BinaryRationalArithmeticNatCounter.advance n c) ∧
      bitSteps k (countLift frame c) ≤ 7*n+1 := by
  induction n generalizing c with
  | zero =>
    change c.phase = .halt at h
    refine ⟨1,by omega,count_halt frame c h,?_⟩
    simp [bitSteps,transitionTrace,countLift,setCounter,h]
  | succ n ih =>
    by_cases hh : c.phase = .halt
    · rw [inner_halt (n+1) c hh]
      refine ⟨1,by omega,count_halt frame c hh,?_⟩
      simp [bitSteps,transitionTrace,countLift,setCounter,hh]
    · obtain ⟨k,hk,he,hc⟩ := ih (BinaryRationalArithmeticNatCounter.step c) h
      refine ⟨k+1,by omega,?_,?_⟩
      · rw [advance,count_step frame c hh]
        exact he
      · have ht := BinaryRationalArithmeticNatCounter.transition_length c
        rw [bitSteps,count_step frame c hh]
        change (if c.phase = .halt then [BinaryArithmetic.BitOp.branch] else
          BinaryArithmetic.BitOp.branch :: BinaryRationalArithmeticNatCounter.transitionTrace c).length +
          bitSteps k (countLift frame (BinaryRationalArithmeticNatCounter.step c)) ≤ _
        simp only [if_neg hh,List.length_cons]
        omega

theorem test_loaded_counter (tape : List Symbol) (n : ℕ) :
    ∃ k, k ≤ 2 ∧ advance k (rearmTest (haltState tape n.bits)) =
      countAfter (haltState tape n.bits) ⟨.halt,n.bits,[],decide (n=0)⟩ ∧
      bitSteps k (rearmTest (haltState tape n.bits)) ≤ 8 := by
  have h := (BinaryRationalArithmeticNatCounter.binary_nat_counter_test n).1
  have hh : (BinaryRationalArithmeticNatCounter.advance 1
      (BinaryRationalArithmeticNatCounter.initialTest n.bits)).phase = .halt := by rw [h]
  obtain ⟨k,hk,he,hc⟩ := forward_count (haltState tape n.bits) _ 1 hh
  rw [h] at he
  exact ⟨k,hk,he,hc⟩

theorem predecessor_loaded_counter (tape : List Symbol) (n : ℕ) :
    ∃ k, k ≤ 2*n.size+3 ∧ advance k (rearmPred (haltState tape n.bits)) =
      countAfter (haltState tape n.bits) ⟨.halt,(n-1).bits,[],false⟩ ∧
      bitSteps k (rearmPred (haltState tape n.bits)) ≤ 14*n.size+15 := by
  obtain ⟨m,hm,hml,_⟩ := BinaryRationalArithmeticNatCounter.binary_nat_counter_predecessor n
  have hh : (BinaryRationalArithmeticNatCounter.advance m
      (BinaryRationalArithmeticNatCounter.initialPred n.bits)).phase = .halt := by rw [hm]
  obtain ⟨k,hk,he,hc⟩ := forward_count (haltState tape n.bits) _ m hh
  rw [hm] at he
  change bitSteps k (rearmPred (haltState tape n.bits)) ≤ 7*m+1 at hc
  exact ⟨k,by omega,he,by omega⟩

end IdentityTesting.BinaryInterpreterCounterInput
