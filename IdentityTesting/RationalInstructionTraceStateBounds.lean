import IdentityTesting.RationalInstructionTraceBounds

/-! Bounds for every register at every actual execution state.  The state
sequence records the chosen branches and all iterations, not untaken code. -/
namespace IdentityTesting.RationalComputation

def registerStateIterate (f : RationalRegisters → List RationalRegisters)
    (g : RationalRegisters → RationalRegisters) : ℕ → RationalRegisters → List RationalRegisters
  | 0, s => [s]
  | n + 1, s => f s ++ registerStateIterate f g n (g s)

def RationalProgram.states : RationalProgram → RationalRegisters → List RationalRegisters
  | .skip, s => [s]
  | .instr i, s => [s, i.exec s]
  | .seq a b, s => a.states s ++ b.states (a.exec s)
  | .branchLe a b yes no, s =>
    s :: (if a.read s ≤ b.read s then yes.states s else no.states s)
  | .repeat n body, s => registerStateIterate body.states body.exec n s

theorem registerStateIterate_final_mem (f : RationalRegisters → List RationalRegisters)
    (g : RationalRegisters → RationalRegisters) (n : ℕ) (s : RationalRegisters) :
    registerIterate g n s ∈ registerStateIterate f g n s := by
  induction n generalizing s with
  | zero => simp [registerIterate, registerStateIterate]
  | succ n ih =>
    exact List.mem_append_right _ (ih (g s))

theorem RationalProgram.final_mem_states (p : RationalProgram) (s : RationalRegisters) :
    p.exec s ∈ p.states s := by
  induction p generalizing s with
  | skip => simp [states, exec]
  | instr i => simp [states, exec]
  | seq a b ha hb => exact List.mem_append_right _ (hb (a.exec s))
  | branchLe a b yes no hy hn =>
    simp only [states, exec]
    split <;> simp_all
  | «repeat» n body ih => exact registerStateIterate_final_mem body.states body.exec n s

private theorem all_set {P : ℚ → Prop} (s : RationalRegisters) (i : ℕ) (v : ℚ)
    (hs : ∀ q ∈ s, P q) (hv : P v) : ∀ q ∈ s.set i v, P q := by
  induction s generalizing i with
  | nil => simp
  | cons a s ih =>
    cases i with
    | zero => simpa using And.intro hv (fun q hq => hs q (by simp [hq]))
    | succ i =>
      change ∀ q ∈ a :: s.set i v, P q
      simp only [List.mem_cons]
      intro q hq
      rcases hq with rfl | hq
      · exact hs q (by simp)
      · exact ih i (fun q hq => hs q (by simp [hq])) q hq

theorem RationalProgram.states_preserve (p : RationalProgram) (s : RationalRegisters)
    (P : ℚ → Prop) (hs : ∀ q ∈ s, P q)
    (hc : ∀ c ∈ (p.run s).2, P c.result) :
    ∀ t ∈ p.states s, ∀ q ∈ t, P q := by
  induction p generalizing s with
  | skip => simpa [states] using hs
  | instr i =>
    have hi : P (i.call s).result := hc _ (by simp [run])
    have he := all_set s i.dst (i.call s).result hs hi
    simpa [states, RationalInstruction.exec] using And.intro hs he
  | seq a b ha hb =>
    have hca : ∀ c ∈ (a.run s).2, P c.result := by
      intro c hm
      exact hc c (by simpa [run] using List.mem_append_left (b.run (a.run s).1).2 hm)
    have hcb : ∀ c ∈ (b.run (a.exec s)).2, P c.result := by
      intro c hm
      apply hc c
      simpa only [run, run_result, List.mem_append] using Or.inr hm
    have hsa := ha s hs hca
    have hsb := hb (a.exec s) (hsa _ (a.final_mem_states s)) hcb
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact hsa t ht
    · exact hsb t ht
  | branchLe a b yes no hy hn =>
    by_cases hab : a.read s ≤ b.read s
    · have hyc : ∀ c ∈ (yes.run s).2, P c.result := by
        intro c hm
        exact hc c (by simp [run, RationalCall.result, RationalOp.eval, hab, hm])
      simpa [states, hab] using And.intro hs (hy s hs hyc)
    · have hnc : ∀ c ∈ (no.run s).2, P c.result := by
        intro c hm
        exact hc c (by simp [run, RationalCall.result, RationalOp.eval, hab, hm])
      simpa [states, hab] using And.intro hs (hn s hs hnc)
  | «repeat» n body ih =>
    change ∀ t ∈ registerStateIterate body.states body.exec n s, ∀ q ∈ t, P q
    change ∀ c ∈ (traceIterate body.run n s).2, P c.result at hc
    induction n generalizing s with
    | zero => simpa [registerStateIterate] using hs
    | succ n hn =>
      have hcb : ∀ c ∈ (body.run s).2, P c.result := by
        intro c hm
        exact hc c (List.mem_append_left _ hm)
      have hsb := ih s hs hcb
      have hcr : ∀ c ∈ (traceIterate body.run n (body.exec s)).2, P c.result := by
        intro c hm
        apply hc c
        simpa only [traceIterate, run_result, List.mem_append] using Or.inr hm
      have hsr := hn (body.exec s) (hsb _ (body.final_mem_states s)) hcr
      intro t ht
      rcases List.mem_append.mp ht with ht | ht
      · exact hsb t ht
      · exact hsr t ht

theorem RationalCall.result_encoding_le (c : RationalCall) (B : ℕ)
    (hl : rationalEncodingLength c.lhs ≤ B) (hr : rationalEncodingLength c.rhs ≤ B) :
    rationalEncodingLength c.result ≤ 4 * B + 3 := by
  have hz : rationalEncodingLength 0 = 2 := by
    norm_num [rationalEncodingLength, numeratorBits, denominatorBits]
  have ho : rationalEncodingLength 1 = 3 := by
    norm_num [rationalEncodingLength, numeratorBits, denominatorBits]
  cases h : c.op <;> simp only [result, h, RationalOp.eval]
  · omega
  · have := rational_add_encoding c.lhs c.rhs; omega
  · have := rational_sub_encoding c.lhs c.rhs; omega
  · have := rational_mul_encoding c.lhs c.rhs; omega
  · have := rational_div_encoding_le c.lhs c.rhs; omega
  · split <;> omega

theorem RationalProgram.states_encoding_le (p : RationalProgram) (s : RationalRegisters)
    (M B : ℕ) (hs : ∀ q ∈ s, rationalEncodingLength q ≤ M)
    (hc : ∀ c ∈ (p.run s).2,
      rationalEncodingLength c.lhs ≤ B ∧ rationalEncodingLength c.rhs ≤ B) :
    ∀ t ∈ p.states s, ∀ q ∈ t, rationalEncodingLength q ≤ max M (4 * B + 3) := by
  apply p.states_preserve s (fun q => rationalEncodingLength q ≤ max M (4 * B + 3))
  · intro q hq; exact (hs q hq).trans (le_max_left _ _)
  · intro c hm
    exact (c.result_encoding_le B (hc c hm).1 (hc c hm).2).trans (le_max_right _ _)

theorem rationalRegisterEncoding_le (s : RationalRegisters) (M : ℕ)
    (hs : ∀ q ∈ s, rationalEncodingLength q ≤ M) :
    rationalRegisterEncoding s + s.length ≤ s.length * (M + 2) := by
  induction s with
  | nil => simp [rationalRegisterEncoding]
  | cons a s ih =>
    have ha := hs a (by simp)
    have hi := ih (fun q hq => hs q (by simp [hq]))
    simp only [rationalRegisterEncoding, List.length_cons, List.map_cons,
      List.sum_cons, Nat.succ_mul] at *
    omega

theorem RationalProgram.states_length (p : RationalProgram) (s : RationalRegisters) :
    ∀ t ∈ p.states s, t.length = s.length := by
  induction p generalizing s with
  | skip => simp [states]
  | instr i => simp [states, RationalInstruction.exec]
  | seq a b ha hb =>
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact ha s t ht
    · exact (hb (a.exec s) t ht).trans (a.exec_length s)
  | branchLe a b yes no hy hn =>
    simp only [states, List.mem_cons]
    split <;> intro t ht <;> rcases ht with rfl | ht
    · rfl
    · exact hy s t ht
    · rfl
    · exact hn s t ht
  | «repeat» n body ih =>
    change ∀ t ∈ registerStateIterate body.states body.exec n s, t.length = s.length
    induction n generalizing s with
    | zero => simp [registerStateIterate]
    | succ n hn =>
      intro t ht
      rcases List.mem_append.mp ht with ht | ht
      · exact ih s t ht
      · exact (hn (body.exec s) t ht).trans (body.exec_length s)

theorem RationalProgram.states_tape_encoding_le (p : RationalProgram)
    (s : RationalRegisters) (M B : ℕ)
    (hs : ∀ q ∈ s, rationalEncodingLength q ≤ M)
    (hc : ∀ c ∈ (p.run s).2,
      rationalEncodingLength c.lhs ≤ B ∧ rationalEncodingLength c.rhs ≤ B)
    (t : RationalRegisters) (ht : t ∈ p.states s) :
    rationalRegisterEncoding t + t.length ≤ s.length * (max M (4 * B + 3) + 2) := by
  have h := rationalRegisterEncoding_le t _ (p.states_encoding_le s M B hs hc t ht)
  simpa only [p.states_length s t ht] using h

end IdentityTesting.RationalComputation
