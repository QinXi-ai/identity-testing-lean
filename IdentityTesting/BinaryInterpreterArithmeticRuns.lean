import IdentityTesting.BinaryInterpreterArithmetic

namespace IdentityTesting.BinaryInterpreterArithmetic
open BinaryInterpreterLayout
open BinaryRegisterMachine (Symbol)

def readWord (r : BinaryInterpreterRead.State) : Word := ⟨⟨r.negative,r.num⟩,r.den⟩

def leftState (L : Layout) (r : BinaryInterpreterRead.State) (right dest : List Bool) : State L :=
  ⟨.left, L.initial (readWord r) emptyWord, r.tape, r.address, right, dest,
    r.saved, r.copyTemp, r.record, r.numWork, r.denWork, false,
    r.phase, r.readPhase, r.splitPhase, .joining, .denCollect, .seek⟩

def rightState (L : Layout) (r : BinaryInterpreterRead.State) (x : Word) (dest : List Bool) : State L :=
  ⟨.right, L.initial x (readWord r), r.tape, [], r.address, dest,
    r.saved, r.copyTemp, r.record, r.numWork, r.denWork, false,
    r.phase, r.readPhase, r.splitPhase, .joining, .denCollect, .seek⟩

def operatingState (L : Layout) (c : L.Core) (tape : List Symbol) (dest : List Bool) : State L :=
  ⟨.operating, c, tape, [], [], dest, [], [], [], [], [], false,
    .halt, .halt, .halt, .joining, .denCollect, .seek⟩

def storingState (L : Layout) (c : L.Core) (w : BinaryInterpreterWrite.State) : State L :=
  setWriter {operatingState L c w.tape w.address with phase := .storing} w

theorem reader_left (L : Layout) (r : BinaryInterpreterRead.State) (right dest : List Bool) :
    reader (leftState L r right dest) false = r := by
  simp only [reader, leftState, L.input_initial, Bool.false_eq_true, if_false, readWord]

theorem reader_right (L : Layout) (r : BinaryInterpreterRead.State) (x : Word) (dest : List Bool) :
    reader (rightState L r x dest) true = r := by
  simp only [reader, rightState, L.input_initial, if_true, readWord]

theorem forward_left (L : Layout) (r : BinaryInterpreterRead.State) (n : ℕ) (tape : List Symbol)
    (x : Word) (right dest : List Bool)
    (h : BinaryInterpreterRead.advance n r = BinaryInterpreterRead.haltState tape x) :
    ∃ k, k ≤ n+1 ∧ advance k (leftState L r right dest) =
      rightState L (BinaryInterpreterRead.initial tape right) x dest := by
  induction n generalizing r with
  | zero =>
    simp only [BinaryInterpreterRead.advance] at h
    subst r
    exact ⟨1, by omega, rfl⟩
  | succ n ih =>
    by_cases hh : r.phase = .halt
    · rw [BinaryInterpreterCopy.load_advance_halt _ r hh] at h
      subst r
      exact ⟨1, by omega, rfl⟩
    · obtain ⟨k, hk, he⟩ := ih (BinaryInterpreterRead.step r) h
      refine ⟨k+1, by omega, ?_⟩
      rw [advance]
      simpa [step, leftState, setReader, reader, hh, readWord, L.input_initial,
        L.setInput_initial] using he

theorem forward_right (L : Layout) (r : BinaryInterpreterRead.State) (n : ℕ) (tape : List Symbol)
    (x y : Word) (dest : List Bool)
    (h : BinaryInterpreterRead.advance n r = BinaryInterpreterRead.haltState tape y) :
    ∃ k, k ≤ n+1 ∧ advance k (rightState L r x dest) =
      operatingState L (L.initial x y) tape dest := by
  induction n generalizing r with
  | zero =>
    simp only [BinaryInterpreterRead.advance] at h
    subst r
    exact ⟨1, by omega, rfl⟩
  | succ n ih =>
    by_cases hh : r.phase = .halt
    · rw [BinaryInterpreterCopy.load_advance_halt _ r hh] at h
      subst r
      exact ⟨1, by omega, rfl⟩
    · obtain ⟨k, hk, he⟩ := ih (BinaryInterpreterRead.step r) h
      refine ⟨k+1, by omega, ?_⟩
      rw [advance]
      simpa [step, rightState, setReader, reader, hh, readWord, L.input_initial,
        L.setInput_initial] using he

theorem storing_initial (L : Layout) (c : L.Core) (tape : List Symbol) (dest : List Bool) :
    storingState L c (BinaryInterpreterWrite.initial tape dest (L.output c)) =
      {operatingState L c tape dest with phase := .storing, negative := (L.output c).numerator.negative} := by
  simp [storingState, setWriter, BinaryInterpreterWrite.initial, BinaryInterpreterWrite.joiningState,
    BinaryRationalRecordJoin.initial, L.setOutput_self, operatingState]

theorem forward_operate (L : Layout) (c : L.Core) (n : ℕ) (tape : List Symbol) (dest : List Bool)
    (h : L.halted (L.advance n c) = true) :
    ∃ k, k ≤ n+1 ∧ advance k (operatingState L c tape dest) =
      storingState L (L.advance n c)
        (BinaryInterpreterWrite.initial tape dest (L.output (L.advance n c))) ∧
      bitSteps k (operatingState L c tape dest) ≤ 2*L.bitSteps n c+3 := by
  induction n generalizing c with
  | zero =>
    simp only [Layout.advance] at h ⊢
    refine ⟨1, by omega, ?_, ?_⟩
    · rw [storing_initial]; simp [advance, step, operatingState, h]
    · simp [bitSteps, transitionTrace, operatingState, h, Layout.bitSteps]
  | succ n ih =>
    by_cases hh : L.halted c = true
    · rw [L.advance_halt (n+1) c hh]
      refine ⟨1, by omega, ?_, ?_⟩
      · rw [storing_initial]; simp [advance, step, operatingState, hh]
      · simp [bitSteps, transitionTrace, operatingState, hh]
    · obtain ⟨k, hk, he, hc⟩ := ih (L.step c) h
      refine ⟨k+1, by omega, ?_, ?_⟩
      · rw [advance]
        simpa [step, operatingState, hh, Layout.advance] using he
      · have ht := L.trace_active c hh
        simp only [bitSteps, transitionTrace, step, operatingState, if_neg hh, List.length_cons,
          Layout.bitSteps]
        change (L.trace c).length+1+bitSteps k (operatingState L (L.step c) tape dest) ≤ _
        omega

theorem writer_storing (L : Layout) (c : L.Core) (w : BinaryInterpreterWrite.State) :
    writer (storingState L c w) = w := by
  simp [writer, storingState, setWriter, operatingState, L.output_num_set, L.output_den_set]

theorem forward_store (L : Layout) (c : L.Core) (w : BinaryInterpreterWrite.State)
    (n : ℕ) (tape : List Symbol) (sign : Bool)
    (h : BinaryInterpreterWrite.advance n w = BinaryInterpreterWrite.haltState sign tape) :
    ∃ k, k ≤ n+1 ∧ advance k (storingState L c w) =
      {storingState L c (BinaryInterpreterWrite.haltState sign tape) with phase := .halt} := by
  induction n generalizing w with
  | zero =>
    simp only [BinaryInterpreterWrite.advance] at h
    subst w
    exact ⟨1, by omega, rfl⟩
  | succ n ih =>
    by_cases hh : w.phase = .halt
    · rw [BinaryInterpreterCopy.store_advance_halt _ w hh] at h
      subst w
      exact ⟨1, by omega, rfl⟩
    · obtain ⟨k, hk, he⟩ := ih (BinaryInterpreterWrite.step w) h
      refine ⟨k+1, by omega, ?_⟩
      rw [advance]
      simpa [step, storingState, setWriter, writer, operatingState, hh,
        L.setOutput_set, L.output_num_set, L.output_den_set] using he

end IdentityTesting.BinaryInterpreterArithmetic
