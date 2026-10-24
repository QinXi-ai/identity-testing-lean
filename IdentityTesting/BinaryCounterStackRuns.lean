import IdentityTesting.BinaryCounterStack

namespace IdentityTesting.BinaryCounterStack
open BinaryRegisterMachine

theorem saving_run (bits : List Bool) (saved : List Symbol) (temp : List Bool) :
    advance (bits.length+1) ⟨.saving,bits,saved,temp⟩ =
      ⟨.halt,[],bits.reverse.map (fun b => Symbol.cell (.bit b)) ++ saved,temp⟩ := by
  induction bits generalizing saved with
  | nil => rfl
  | cons b bs ih =>
    simpa [advance,step,List.reverse_cons,List.map_append,List.append_assoc] using ih (.cell (.bit b)::saved)

theorem saving_cost (bits : List Bool) (saved : List Symbol) (temp : List Bool) :
    bitSteps (bits.length+1) ⟨.saving,bits,saved,temp⟩ = 6*bits.length+2 := by
  induction bits generalizing saved with
  | nil => rfl
  | cons b bs ih =>
    simp [bitSteps,step,transitionTrace,ih]
    omega

theorem restoring_run (bits counter : List Bool) (saved : List Symbol) (temp : List Bool) :
    advance (bits.length+1)
      ⟨.restoring,counter,bits.map (fun b => Symbol.cell (.bit b)) ++ .boundary::saved,temp⟩ =
      ⟨.halt,bits.reverse++counter,saved,temp⟩ := by
  induction bits generalizing counter with
  | nil => rfl
  | cons b bs ih =>
    simpa [advance,step,List.reverse_cons,List.append_assoc] using ih (b::counter)

theorem restoring_cost (bits counter : List Bool) (saved : List Symbol) (temp : List Bool) :
    bitSteps (bits.length+1)
      ⟨.restoring,counter,bits.map (fun b => Symbol.cell (.bit b)) ++ .boundary::saved,temp⟩ =
      6*bits.length+4 := by
  induction bits generalizing counter with
  | nil => rfl
  | cons b bs ih =>
    simp [bitSteps,step,transitionTrace,ih]
    omega

/-- Saving empties the current counter and leaves all more-outer frames in place. -/
theorem save_run (bits : List Bool) (saved : List Symbol) :
    advance (bits.length+2) (initialSave bits saved) = haltState [] (frame bits saved) ∧
      bitSteps (bits.length+2) (initialSave bits saved) = 6*bits.length+5 := by
  constructor
  · change advance (bits.length+1+1) (initialSave bits saved) = _
    rw [advance]
    exact saving_run bits (.boundary::saved) []
  · change bitSteps (bits.length+1+1) (initialSave bits saved) = _
    rw [bitSteps]
    change 3+bitSteps (bits.length+1) ⟨.saving,bits,.boundary::saved,[]⟩ = _
    rw [saving_cost]
    omega

/-- Restoring starts with an empty current counter, consumes exactly one frame,
and returns the original word in its original order, including the empty word. -/
theorem restore_run (bits : List Bool) (saved : List Symbol) :
    advance (bits.length+1) (initialRestore (frame bits saved)) = haltState bits saved ∧
      bitSteps (bits.length+1) (initialRestore (frame bits saved)) = 6*bits.length+4 := by
  have hr := restoring_run bits.reverse [] saved []
  have hc := restoring_cost bits.reverse [] saved []
  simpa only [List.length_reverse,List.reverse_reverse,List.append_nil] using And.intro hr hc

theorem save_current (s : State) (ht : s.temp = []) :
    advance (s.counter.length+2) (rearmSave s) = haltState [] (frame s.counter s.saved) ∧
      bitSteps (s.counter.length+2) (rearmSave s) = 6*s.counter.length+5 := by
  have h : rearmSave s = initialSave s.counter s.saved := by cases s; simp_all [rearmSave,initialSave]
  rw [h]
  exact save_run s.counter s.saved

/-- The empty-counter premise is supplied when the inner countdown reaches zero.
Rearming only changes control; it does not silently erase an inner counter. -/
theorem restore_from_empty (s : State) (bits : List Bool) (suffix : List Symbol)
    (hc : s.counter = []) (hs : s.saved = frame bits suffix) (ht : s.temp = []) :
    advance (bits.length+1) (rearmRestore s) = haltState bits suffix ∧
      bitSteps (bits.length+1) (rearmRestore s) = 6*bits.length+4 := by
  have h : rearmRestore s = initialRestore (frame bits suffix) := by
    cases s
    simp_all [rearmRestore,initialRestore]
  rw [h]
  exact restore_run bits suffix

theorem save_restore (bits : List Bool) (suffix : List Symbol) :
    advance (bits.length+1) (rearmRestore (advance (bits.length+2) (initialSave bits suffix))) =
      haltState bits suffix ∧
    bitSteps (bits.length+2) (initialSave bits suffix) +
      bitSteps (bits.length+1) (rearmRestore (advance (bits.length+2) (initialSave bits suffix))) =
      12*bits.length+9 := by
  rw [(save_run bits suffix).1]
  change advance (bits.length+1) (initialRestore (frame bits suffix)) = _ ∧ _
  refine ⟨(restore_run bits suffix).1,?_⟩
  change bitSteps (bits.length+2) (initialSave bits suffix) +
    bitSteps (bits.length+1) (initialRestore (frame bits suffix)) = _
  rw [(save_run bits suffix).2,(restore_run bits suffix).2]
  omega

theorem restore_inner_preserves_outer (inner outer : List Bool) (suffix : List Symbol) :
    advance (inner.length+1) (initialRestore (frame inner (frame outer suffix))) =
      haltState inner (frame outer suffix) := (restore_run inner (frame outer suffix)).1

end IdentityTesting.BinaryCounterStack
