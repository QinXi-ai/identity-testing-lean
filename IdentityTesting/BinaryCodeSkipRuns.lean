import IdentityTesting.BinaryCodeSkipFields

namespace IdentityTesting.BinaryCodeSkip
open BinaryRegisterMachine RationalComputation

theorem instruction_fields (i : RationalInstruction) :
    Parses [.word,.word,.operand,.operand] (RationalProgramCode.instruction i) := by
  have h := ((word_parses (RationalProgramCode.opBits i.op)).append
    (word_parses (List.replicate i.dst false))).append
      ((operand_parses i.lhs).append (operand_parses i.rhs))
  simpa only [RationalProgramCode.instruction,RationalProgramCode.address,List.append_assoc] using h

theorem program_task (p : RationalProgram) : Parses [.node] (RationalProgramCode.program p) := by
  induction p with
  | skip =>
    simpa only [RationalProgramCode.program,List.append_nil] using
      node_payload_parses false false false [] [] rfl empty_parses
  | instr i => exact node_payload_parses true false false _ _ rfl (instruction_fields i)
  | seq p q ihp ihq =>
    have hb := (ihp.append ihq).append end_parses
    simpa only [RationalProgramCode.program,List.append_assoc] using
      node_payload_parses false true false _ _ rfl hb
  | branchLe a b p q ihp ihq =>
    have hb := (((operand_parses a).append (operand_parses b)).append (ihp.append ihq)).append end_parses
    simpa only [RationalProgramCode.program,List.append_assoc] using
      node_payload_parses true true false _ _ rfl hb
  | «repeat» n p ih =>
    have hb := ((word_parses n.bits).append ih).append end_parses
    simpa only [RationalProgramCode.program,List.append_assoc] using
      node_payload_parses false false true _ _ rfl hb

theorem control_task (p : RationalControlProgram) : Parses [.node] (RationalProgramCode.control p) := by
  induction p with
  | basic p => exact program_task p
  | seq p q ihp ihq =>
    have hb := (ihp.append ihq).append end_parses
    simpa only [RationalProgramCode.control,List.append_assoc] using
      node_payload_parses false true false _ _ rfl hb
  | branchLe a b p q ihp ihq =>
    have hb := (((operand_parses a).append (operand_parses b)).append (ihp.append ihq)).append end_parses
    simpa only [RationalProgramCode.control,List.append_assoc] using
      node_payload_parses true true false _ _ rfl hb
  | ceilSize dst src =>
    have hb := (word_parses (List.replicate dst false)).append (operand_parses src)
    simpa only [RationalProgramCode.control,RationalProgramCode.address] using
      node_payload_parses true false true _ _ rfl hb
  | repeatRegister count p ih =>
    have hb := ((word_parses (List.replicate count false)).append ih).append end_parses
    simpa only [RationalProgramCode.control,RationalProgramCode.address,List.append_assoc] using
      node_payload_parses false true true _ _ rfl hb

theorem complete (segment : List Symbol) (h : Parses [.node] segment) (code history : List Symbol) :
    ∃ n, n ≤ 2*segment.length+2 ∧
      advance n (initial (segment++code) history) = haltState code (segment.reverse++history) ∧
      bitSteps n (initial (segment++code) history) ≤ 40*(segment.length+1) := by
  obtain ⟨n,hn,he⟩ := h [] code history
  simp only [List.append_nil] at he
  have hstart : advance 1 (initial (segment++code) history) = ready [.node] (segment++code) history := rfl
  have hfinish : advance 1 (ready [] code (segment.reverse++history)) = haltState code (segment.reverse++history) := rfl
  have htotal : advance (1+(n+1)) (initial (segment++code) history) = haltState code (segment.reverse++history) := by
    rw [advance_add,hstart,advance_add,he,hfinish]
  refine ⟨1+(n+1),by omega,htotal,?_⟩
  have hb := bitSteps_le (1+(n+1)) (initial (segment++code) history)
  omega

/-- Skip exactly one encoded source-program subtree. Code suffix and reversed
history are exact; the task stack is physically emptied before halting. -/
theorem binary_skip_program (p : RationalProgram) (code history : List Symbol) :
    ∃ n,
      advance n (initial (RationalProgramCode.program p++code) history) =
        haltState code ((RationalProgramCode.program p).reverse++history) ∧
      bitSteps n (initial (RationalProgramCode.program p++code) history) ≤
        40*((RationalProgramCode.program p).length+1) := by
  obtain ⟨n,_,he,hc⟩ := complete _ (program_task p) code history
  exact ⟨n,he,hc⟩

/-- The same finite machine also skips ceilSize and repeatRegister nodes. -/
theorem binary_skip_control (p : RationalControlProgram) (code history : List Symbol) :
    ∃ n,
      advance n (initial (RationalProgramCode.control p++code) history) =
        haltState code ((RationalProgramCode.control p).reverse++history) ∧
      bitSteps n (initial (RationalProgramCode.control p++code) history) ≤
        40*((RationalProgramCode.control p).length+1) := by
  obtain ⟨n,_,he,hc⟩ := complete _ (control_task p) code history
  exact ⟨n,he,hc⟩

end IdentityTesting.BinaryCodeSkip
