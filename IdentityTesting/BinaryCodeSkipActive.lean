import IdentityTesting.BinaryCodeSkip

namespace IdentityTesting.BinaryCodeSkip

theorem halt_advance (n : ℕ) (s : State) (h : s.phase = .halt) : advance n s = s := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [advance,step,h] using ih

theorem invalid_advance (n : ℕ) (s : State) (h : s.phase = .invalid) : advance n s = s := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [advance,step,h] using ih

theorem eventually_halt_not_invalid (n : ℕ) (s : State) (h : (advance n s).phase = .halt) :
    s.phase ≠ .invalid := by
  intro hi
  rw [invalid_advance n s hi,hi] at h
  contradiction

theorem trace_active (s : State) (hh : s.phase ≠ .halt) (hi : s.phase ≠ .invalid) :
    1 ≤ (transitionTrace s).length := by
  cases hp : s.phase <;> simp only [transitionTrace,hp]
  all_goals (repeat' first | split | simp_all [pushTrace,symbolTrace,schedule] | omega)

theorem trace_active_of_eventually_halt (n : ℕ) (s : State)
    (hh : s.phase ≠ .halt) (h : (advance n s).phase = .halt) :
    1 ≤ (transitionTrace s).length :=
  trace_active s hh (eventually_halt_not_invalid n s h)

end IdentityTesting.BinaryCodeSkip
