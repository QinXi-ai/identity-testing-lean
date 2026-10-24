import IdentityTesting.BinaryInterpreterProgramTags
import IdentityTesting.BinaryInterpreterProgramInstruction

namespace IdentityTesting.BinaryInterpreterProgram
open BinaryRegisterMachine RationalComputation BinaryRationalRegisters

def Straight : RationalProgram → Prop
  | .skip | .instr _ => True
  | .seq p q => Straight p ∧ Straight q
  | .branchLe _ _ _ _ | .repeat _ _ => False

def instructionBudget (i : RationalInstruction) (s : RationalRegisters) : ℕ :=
  6000*(rationalRegisterEncoding s+s.length+i.lhs.slots+i.rhs.slots+1)+
    100000000*(rationalEncodingLength (i.lhs.read s)+rationalEncodingLength (i.rhs.read s)+1)^3

/-- Cost composed on the actual intermediate source states. This is not yet
the manuscript's input-length-only polynomial bound for all branches. -/
def cost : RationalProgram → RationalRegisters → ℕ
  | .skip, _ => 35
  | .instr i, s => 2*instructionBudget i s+36
  | .seq p q, s => 80+cost p s+cost q (p.exec s)
  | _, _ => 0

def Result (p : RationalProgram) (s : RationalRegisters) (code history : List Symbol) (f : DState) : Prop :=
  f.io.tape = tape (p.exec s) ∧ BinaryInterpreterDispatch.CleanIO f.io ∧
  BinaryInterpreterPool.Clean f.pool ∧ f.io.code = code ∧
  f.io.history = (RationalProgramCode.program p).reverse ++ history

theorem run_core (p : RationalProgram) (hstraight : Straight p) (s : RationalRegisters)
    (hslots : p.slots ≤ s.length) (core : DState) (frames : List Frame)
    (hclean : BinaryInterpreterDispatch.CleanIO core.io) (hpool : BinaryInterpreterPool.Clean core.pool)
    (htape : core.io.tape = tape s) (code : List Symbol)
    (hcode : core.io.code = RationalProgramCode.program p ++ code) :
    ∃ n f, advance n ⟨.node,resetTag core,frames⟩ = ⟨.returning,f,frames⟩ ∧
      Result p s code core.io.history f ∧ bitSteps n ⟨.node,resetTag core,frames⟩ ≤ cost p s := by
  induction p generalizing s core frames code with
  | skip =>
      have he := node_tag_run core frames false false false code hcode
      have hc := node_tag_cost core frames false false false code hcode
      refine ⟨5,afterTag core false false false code,he,?_,Nat.le_of_eq hc⟩
      exact ⟨htape,afterTag_clean core false false false code hclean,hpool,rfl,rfl⟩
  | instr i =>
      have hd : i.dst < s.length := i.destination_in_bounds s hslots
      have hl : i.lhs.slots ≤ s.length := (le_max_left _ _).trans ((le_max_right _ _).trans hslots)
      have hr : i.rhs.slots ≤ s.length := (le_max_right _ _).trans ((le_max_right _ _).trans hslots)
      have htagcode : core.io.code = RationalProgramCode.tag true false false ++
          (RationalProgramCode.instruction i ++ code) := by
        simpa only [RationalProgramCode.program,List.append_assoc] using hcode
      let mid := afterTag core true false false (RationalProgramCode.instruction i ++ code)
      have htag : advance 5 ⟨.node,resetTag core,frames⟩ =
          ⟨.instruction,BinaryInterpreterDispatch.rearm mid,frames⟩ :=
        node_tag_run core frames true false false _ htagcode
      have htagcost := node_tag_cost core frames true false false _ htagcode
      obtain ⟨nd,hdone,hdcost⟩ := BinaryInterpreterDispatch.instruction_from_rearmed mid
        (afterTag_clean core true false false _ hclean) hpool s i htape code rfl hl hr hd
      let df := BinaryInterpreterDispatch.advance nd (BinaryInterpreterDispatch.rearm mid)
      change BinaryInterpreterDispatch.InstructionFinished mid.pool s i code mid.io.history df at hdone
      rcases hdone with ⟨hh,_,ht,hi,hp,hc,hhist,_⟩
      obtain ⟨k,hk,he,hcost⟩ := forward_instruction frames (BinaryInterpreterDispatch.rearm mid) nd hh
      have htotal : advance (5+k) ⟨.node,resetTag core,frames⟩ = ⟨.returning,df,frames⟩ := by
        rw [advance_add,htag,he]
      refine ⟨5+k,df,htotal,⟨ht,hi,hp,hc,?_⟩,?_⟩
      · rw [hhist]
        simp only [mid,afterTag,BinaryInterpreterDispatch.setTag,RationalProgramCode.program,
          List.reverse_append,List.append_assoc]
      · rw [bitSteps_add,htag,htagcost]
        change _ ≤ 2*instructionBudget i s+36
        change BinaryInterpreterDispatch.bitSteps nd (BinaryInterpreterDispatch.rearm mid) ≤ instructionBudget i s at hdcost
        omega
  | seq p q ihp ihq =>
      rcases hstraight with ⟨hp,hq⟩
      have hpslots : p.slots ≤ s.length := (le_max_left _ _).trans hslots
      have hqslots : q.slots ≤ (p.exec s).length := by
        rw [p.exec_length]
        exact (le_max_right _ _).trans hslots
      let tail := RationalProgramCode.program q ++ (RationalProgramCode.endTag ++ code)
      let body := RationalProgramCode.program p ++ tail
      let mid := afterTag core false true false body
      have htagcode : core.io.code = RationalProgramCode.tag false true false ++ body := by
        simpa only [RationalProgramCode.program,List.append_assoc,body,tail] using hcode
      have htag : advance 5 ⟨.node,resetTag core,frames⟩ = ⟨.node,resetTag mid,.next::frames⟩ :=
        node_tag_run core frames false true false body htagcode
      have htagcost := node_tag_cost core frames false true false body htagcode
      obtain ⟨np,fp,hep,hpresult,hpcost⟩ := ihp hp s hpslots mid (.next::frames)
        (afterTag_clean core false true false body hclean) hpool htape tail rfl
      rcases hpresult with ⟨hpt,hpi,hpp,hpc,hph⟩
      obtain ⟨nq,fq,heq,hqresult,hqcost⟩ := ihq hq (p.exec s) hqslots fp (.close::frames)
        hpi hpp hpt (RationalProgramCode.endTag ++ code) hpc
      rcases hqresult with ⟨hqt,hqi,hqp,hqc,hqh⟩
      have hnext : advance 1 ⟨.returning,fp,.next::frames⟩ = ⟨.node,resetTag fp,.close::frames⟩ := rfl
      have hnextcost : bitSteps 1 ⟨.returning,fp,.next::frames⟩ = 3 := rfl
      have hclose : advance 1 ⟨.returning,fq,.close::frames⟩ = ⟨.closing,resetTag fq,frames⟩ := rfl
      have hclosecost : bitSteps 1 ⟨.returning,fq,.close::frames⟩ = 3 := rfl
      have hend := close_tag_run fq frames code hqc
      have hendcost := close_tag_cost fq frames code hqc
      let final := afterTag fq true true true code
      have htotal : advance (5+(np+(1+(nq+(1+5))))) ⟨.node,resetTag core,frames⟩ = ⟨.returning,final,frames⟩ := by
        rw [advance_add,htag,advance_add,hep,advance_add,hnext,advance_add,heq,advance_add,hclose,hend]
      refine ⟨5+(np+(1+(nq+(1+5)))),final,htotal,⟨hqt,afterTag_clean fq true true true code hqi,hqp,rfl,?_⟩,?_⟩
      · change (RationalProgramCode.tag true true true).reverse ++ fq.io.history = _
        rw [hqh,hph]
        simp only [mid,afterTag,BinaryInterpreterDispatch.setTag,RationalProgramCode.program,
          RationalProgramCode.endTag,List.reverse_append,List.append_assoc]
      · rw [bitSteps_add,htag,bitSteps_add,hep,bitSteps_add,hnext,bitSteps_add,heq,bitSteps_add,hclose,
          htagcost,hnextcost,hclosecost,hendcost]
        change _ ≤ 80+cost p s+cost q (p.exec s)
        omega
  | branchLe a b p q ihp ihq => exact hstraight.elim
  | «repeat» n p ih => exact hstraight.elim

end IdentityTesting.BinaryInterpreterProgram
