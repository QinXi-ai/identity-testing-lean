import IdentityTesting.BinaryInterpreterBranchTags
import IdentityTesting.BinaryInterpreterBranchWiring
import IdentityTesting.BinaryInterpreterBranchSkip
import IdentityTesting.BinaryInterpreterBranchSyntax
import IdentityTesting.BinaryInterpreterProgramRuns

namespace IdentityTesting.BinaryInterpreterBranchProgram
open BinaryRegisterMachine RationalComputation BinaryRationalRegisters

abbrev instructionBudget := BinaryInterpreterProgram.instructionBudget
abbrev Result := BinaryInterpreterProgram.Result

/-- The unselected subtree is scanned as code, not executed. The bound still
uses the actual intermediate register states, rather than only input length. -/
def cost : RationalProgram → RationalRegisters → ℕ
  | .skip, _ => 35
  | .instr i, s => 2*instructionBudget i s+36
  | .seq p q, s => 80+cost p s+cost q (p.exec s)
  | .branchLe a b p q, s => 100+2*compareBudget s a b+
      (if a.read s ≤ b.read s then cost p s+80*((RationalProgramCode.program q).length+1)
        else 80*((RationalProgramCode.program p).length+1)+cost q s)
  | .repeat _ _, _ => 0

theorem run_core (p : RationalProgram) (hfree : LoopFree p) (s : RationalRegisters)
    (hslots : p.slots ≤ s.length) (core : DState) (frames : List Frame)
    (hclean : BinaryInterpreterDispatch.CleanIO core.io) (hpool : BinaryInterpreterPool.Clean core.pool)
    (htape : core.io.tape = tape s) (code : List Symbol)
    (hcode : core.io.code = RationalProgramCode.program p ++ code) :
    ∃ n f, advance n (boundary .node (resetTag core) frames) = boundary .returning f frames ∧
      Result p s code core.io.history f ∧ bitSteps n (boundary .node (resetTag core) frames) ≤ cost p s := by
  induction p generalizing s core frames code with
  | skip =>
      have he := node_tag_run core frames false false false code hcode
      have hc := node_tag_cost core frames false false false code hcode
      refine ⟨5,afterTag core false false false code,he,?_,Nat.le_of_eq hc⟩
      exact ⟨htape,BinaryInterpreterProgram.afterTag_clean core false false false code hclean,hpool,rfl,rfl⟩
  | instr i =>
      have hd : i.dst < s.length := i.destination_in_bounds s hslots
      have hl : i.lhs.slots ≤ s.length := (le_max_left _ _).trans ((le_max_right _ _).trans hslots)
      have hr : i.rhs.slots ≤ s.length := (le_max_right _ _).trans ((le_max_right _ _).trans hslots)
      have htagcode : core.io.code = RationalProgramCode.tag true false false ++
          (RationalProgramCode.instruction i ++ code) := by
        simpa only [RationalProgramCode.program,List.append_assoc] using hcode
      let mid := afterTag core true false false (RationalProgramCode.instruction i ++ code)
      have htag : advance 5 (boundary .node (resetTag core) frames) =
          boundary .instruction (BinaryInterpreterDispatch.rearm mid) frames :=
        node_tag_run core frames true false false _ htagcode
      have htagcost := node_tag_cost core frames true false false _ htagcode
      obtain ⟨nd,hdone,hdcost⟩ := BinaryInterpreterDispatch.instruction_from_rearmed mid
        (BinaryInterpreterProgram.afterTag_clean core true false false _ hclean) hpool s i htape code rfl hl hr hd
      let df := BinaryInterpreterDispatch.advance nd (BinaryInterpreterDispatch.rearm mid)
      change BinaryInterpreterDispatch.InstructionFinished mid.pool s i code mid.io.history df at hdone
      rcases hdone with ⟨hh,_,ht,hi,hp,hc,hhist,_⟩
      obtain ⟨k,_,he,hcost⟩ := forward_instruction frames (BinaryInterpreterDispatch.rearm mid) nd hh
      have htotal : advance (5+k) (boundary .node (resetTag core) frames) = boundary .returning df frames := by
        rw [advance_add,htag,he]
      refine ⟨5+k,df,htotal,⟨ht,hi,hp,hc,?_⟩,?_⟩
      · rw [hhist]
        simp only [mid,afterTag,BinaryInterpreterProgram.afterTag,BinaryInterpreterDispatch.setTag,
          RationalProgramCode.program,List.reverse_append,List.append_assoc]
      · rw [bitSteps_add,htag,htagcost]
        change _ ≤ 2*instructionBudget i s+36
        change BinaryInterpreterDispatch.bitSteps nd (BinaryInterpreterDispatch.rearm mid) ≤ instructionBudget i s at hdcost
        omega
  | seq p q ihp ihq =>
      rcases hfree with ⟨hp,hq⟩
      have hpslots : p.slots ≤ s.length := (le_max_left _ _).trans hslots
      have hqslots : q.slots ≤ (p.exec s).length := by
        rw [p.exec_length]
        exact (le_max_right _ _).trans hslots
      let tail := RationalProgramCode.program q ++ (RationalProgramCode.endTag ++ code)
      let body := RationalProgramCode.program p ++ tail
      let mid := afterTag core false true false body
      have htagcode : core.io.code = RationalProgramCode.tag false true false ++ body := by
        simpa only [RationalProgramCode.program,List.append_assoc,body,tail] using hcode
      have htag : advance 5 (boundary .node (resetTag core) frames) = boundary .node (resetTag mid) (.next::frames) :=
        node_tag_run core frames false true false body htagcode
      have htagcost := node_tag_cost core frames false true false body htagcode
      obtain ⟨np,fp,hep,hpresult,hpcost⟩ := ihp hp s hpslots mid (.next::frames)
        (BinaryInterpreterProgram.afterTag_clean core false true false body hclean) hpool htape tail rfl
      rcases hpresult with ⟨hpt,hpi,hpp,hpc,hph⟩
      obtain ⟨nq,fq,heq,hqresult,hqcost⟩ := ihq hq (p.exec s) hqslots fp (.close::frames)
        hpi hpp hpt (RationalProgramCode.endTag ++ code) hpc
      rcases hqresult with ⟨hqt,hqi,hqp,hqc,hqh⟩
      have hnext : advance 1 (boundary .returning fp (.next::frames)) = boundary .node (resetTag fp) (.close::frames) := rfl
      have hnextcost : bitSteps 1 (boundary .returning fp (.next::frames)) = 3 := rfl
      have hclose : advance 1 (boundary .returning fq (.close::frames)) = boundary .closing (resetTag fq) frames := rfl
      have hclosecost : bitSteps 1 (boundary .returning fq (.close::frames)) = 3 := rfl
      have hend := close_tag_run fq frames code hqc
      have hendcost := close_tag_cost fq frames code hqc
      let final := afterTag fq true true true code
      have htotal : advance (5+(np+(1+(nq+(1+5))))) (boundary .node (resetTag core) frames) = boundary .returning final frames := by
        rw [advance_add,htag,advance_add,hep,advance_add,hnext,advance_add,heq,advance_add,hclose,hend]
      refine ⟨5+(np+(1+(nq+(1+5)))),final,htotal,
        ⟨hqt,BinaryInterpreterProgram.afterTag_clean fq true true true code hqi,hqp,rfl,?_⟩,?_⟩
      · change (RationalProgramCode.tag true true true).reverse ++ fq.io.history = _
        rw [hqh,hph]
        simp only [mid,afterTag,BinaryInterpreterProgram.afterTag,BinaryInterpreterDispatch.setTag,
          RationalProgramCode.program,RationalProgramCode.endTag,List.reverse_append,List.append_assoc]
      · rw [bitSteps_add,htag,bitSteps_add,hep,bitSteps_add,hnext,bitSteps_add,heq,bitSteps_add,hclose,
          htagcost,hnextcost,hclosecost,hendcost]
        change _ ≤ 80+cost p s+cost q (p.exec s)
        omega
  | branchLe a b p q ihp ihq =>
      rcases hfree with ⟨hp,hq⟩
      have hab : max a.slots b.slots ≤ s.length := (le_max_left _ _).trans hslots
      have hpq : max p.slots q.slots ≤ s.length := (le_max_right _ _).trans hslots
      have ha : a.slots ≤ s.length := (le_max_left _ _).trans hab
      have hb : b.slots ≤ s.length := (le_max_right _ _).trans hab
      have hps : p.slots ≤ s.length := (le_max_left _ _).trans hpq
      have hqs : q.slots ≤ s.length := (le_max_right _ _).trans hpq
      let tail := RationalProgramCode.endTag ++ code
      let trees := RationalProgramCode.program p ++ (RationalProgramCode.program q ++ tail)
      let body := RationalProgramCode.operand a ++ RationalProgramCode.operand b ++ trees
      let mid := afterTag core true true false body
      have htagcode : core.io.code = RationalProgramCode.tag true true false ++ body := by
        simpa only [RationalProgramCode.program,List.append_assoc,body,trees,tail] using hcode
      have htag : advance 5 (boundary .node (resetTag core) frames) = boundary .comparing (compareStart mid) frames :=
        node_tag_run core frames true true false body htagcode
      have htagcost := node_tag_cost core frames true true false body htagcode
      obtain ⟨nc,fc,hec,hct,hci,hcp,hcc,hch,hccost⟩ := compare_run mid frames s a b
        (BinaryInterpreterProgram.afterTag_clean core true true false body hclean) hpool htape trees rfl ha hb
      by_cases hcond : a.read s ≤ b.read s
      · simp only [if_pos hcond] at hec
        obtain ⟨np,fp,hep,hpr,hpcost⟩ := ihp hp s hps fc (.skipElse::frames)
          hci hcp hct (RationalProgramCode.program q ++ tail) hcc
        rcases hpr with ⟨hpt,hpi,hpp,hpc,hph⟩
        have hret : advance 1 (boundary .returning fp (.skipElse::frames)) = boundary .skipToClose (resetTag fp) frames := rfl
        have hretcost : bitSteps 1 (boundary .returning fp (.skipElse::frames)) = 3 := rfl
        obtain ⟨nk,hek,hkcost⟩ := skip_program fp frames false q tail hpc
        simp only [Bool.false_eq_true,if_false] at hek hkcost
        let fk := afterCode fp (RationalProgramCode.program q) tail
        have hend := close_tag_run fk frames code (rfl : fk.io.code = RationalProgramCode.endTag ++ code)
        have hendcost := close_tag_cost fk frames code (rfl : fk.io.code = RationalProgramCode.endTag ++ code)
        let final := afterTag fk true true true code
        have htotal : advance (5+(nc+(np+(1+(nk+5))))) (boundary .node (resetTag core) frames) = boundary .returning final frames := by
          rw [advance_add,htag,advance_add,hec,advance_add,hep,advance_add,hret,advance_add,hek,hend]
        refine ⟨5+(nc+(np+(1+(nk+5)))),final,htotal,⟨?_,?_,hpp,rfl,?_⟩,?_⟩
        · simpa only [RationalProgram.exec,if_pos hcond] using hpt
        · exact hpi
        · change (RationalProgramCode.endTag).reverse ++
            ((RationalProgramCode.program q).reverse ++ fp.io.history) = _
          rw [hph,hch]
          simp only [mid,afterTag,BinaryInterpreterProgram.afterTag,BinaryInterpreterDispatch.setTag,
            RationalProgramCode.program,List.reverse_append,List.append_assoc]
        · rw [bitSteps_add,htag,bitSteps_add,hec,bitSteps_add,hep,bitSteps_add,hret,bitSteps_add,hek,
            htagcost,hretcost,hendcost]
          change _ ≤ 100+2*compareBudget s a b+(if a.read s ≤ b.read s then _ else _)
          rw [if_pos hcond]
          omega
      · simp only [if_neg hcond] at hec
        obtain ⟨nk,hek,hkcost⟩ := skip_program fc (.close::frames) true p (RationalProgramCode.program q ++ tail) hcc
        simp only [if_pos rfl,ite_true] at hek hkcost
        let fk := afterCode fc (RationalProgramCode.program p) (RationalProgramCode.program q ++ tail)
        obtain ⟨nq,fq,heq,hqr,hqcost⟩ := ihq hq s hqs fk (.close::frames) hci hcp hct tail rfl
        rcases hqr with ⟨hqt,hqi,hqp,hqc,hqh⟩
        have hret : advance 1 (boundary .returning fq (.close::frames)) = boundary .closing (resetTag fq) frames := rfl
        have hretcost : bitSteps 1 (boundary .returning fq (.close::frames)) = 3 := rfl
        have hend := close_tag_run fq frames code hqc
        have hendcost := close_tag_cost fq frames code hqc
        let final := afterTag fq true true true code
        have htotal : advance (5+(nc+(nk+(nq+(1+5))))) (boundary .node (resetTag core) frames) = boundary .returning final frames := by
          rw [advance_add,htag,advance_add,hec,advance_add,hek,advance_add,heq,advance_add,hret,hend]
        refine ⟨5+(nc+(nk+(nq+(1+5)))),final,htotal,⟨?_,hqi,hqp,rfl,?_⟩,?_⟩
        · simpa only [RationalProgram.exec,if_neg hcond] using hqt
        · change (RationalProgramCode.endTag).reverse ++ fq.io.history = _
          rw [hqh]
          change (RationalProgramCode.endTag).reverse ++
            ((RationalProgramCode.program q).reverse ++ ((RationalProgramCode.program p).reverse ++ fc.io.history)) = _
          rw [hch]
          simp only [mid,afterTag,BinaryInterpreterProgram.afterTag,BinaryInterpreterDispatch.setTag,
            RationalProgramCode.program,List.reverse_append,List.append_assoc]
        · rw [bitSteps_add,htag,bitSteps_add,hec,bitSteps_add,hek,bitSteps_add,heq,bitSteps_add,hret,
            htagcost,hretcost,hendcost]
          change _ ≤ 100+2*compareBudget s a b+(if a.read s ≤ b.read s then _ else _)
          rw [if_neg hcond]
          dsimp only [fk] at hqcost
          omega
  | «repeat» n p ih => exact hfree.elim

end IdentityTesting.BinaryInterpreterBranchProgram
