import IdentityTesting.BinaryInterpreterArithmeticStorage
import IdentityTesting.BinaryInterpreterArithmeticReuse
import IdentityTesting.BinaryInterpreterInputLocal

/-! Six fixed physical groups are retained for the six primitive operations.
Selecting a group is finite-control wiring; inactive groups remain unchanged.
Rearming updates only finite control and preserves every physical stack. -/
namespace IdentityTesting.BinaryInterpreterPool
open BinaryInterpreterLayout BinaryInterpreterArithmetic RationalComputation

abbrev Pool := (op : RationalOp) → (arithmeticLayout op).Core

def set (pool : Pool) (op : RationalOp) (c : (arithmeticLayout op).Core) : Pool :=
  Function.update pool op c

theorem get_set (pool : Pool) (op : RationalOp) (c : (arithmeticLayout op).Core) :
    set pool op c op = c := by simp [set]

theorem other_set (pool : Pool) (op other : RationalOp) (c : (arithmeticLayout op).Core) (h : other ≠ op) :
    set pool op c other = pool other := by simp [set,h]

theorem set_self (pool : Pool) (op : RationalOp) : set pool op (pool op) = pool := by simp [set]

theorem set_set (pool : Pool) (op : RationalOp) (c d : (arithmeticLayout op).Core) :
    set (set pool op c) op d = set pool op d := by simp [set]

def empty : Pool := fun op => (arithmeticLayout op).initial emptyWord emptyWord

def Clean (pool : Pool) : Prop := ∀ op i, (arithmeticStorage op).tapes (pool op) i = []

theorem empty_clean : Clean empty := by
  intro op i
  exact initial_tapes_empty (arithmeticStorage op) i

theorem physical_stack_count :
    (arithmeticStorage .copy).count+(arithmeticStorage .add).count+(arithmeticStorage .sub).count+
      (arithmeticStorage .mul).count+(arithmeticStorage .div).count+(arithmeticStorage .le).count = 427 := by
  rfl

def rearmCore (op : RationalOp) (c : (arithmeticLayout op).Core) : (arithmeticLayout op).Core :=
  (arithmeticStorage op).setTapes ((arithmeticLayout op).initial emptyWord emptyWord)
    ((arithmeticStorage op).tapes c)

theorem rearmCore_tapes (op : RationalOp) (c : (arithmeticLayout op).Core) :
    (arithmeticStorage op).tapes (rearmCore op c) = (arithmeticStorage op).tapes c :=
  (arithmeticStorage op).tapes_set _ _

def rearm (pool : Pool) (op : RationalOp) : Pool := set pool op (rearmCore op (pool op))

theorem rearm_tapes (pool : Pool) (op other : RationalOp) :
    (arithmeticStorage other).tapes (rearm pool op other) = (arithmeticStorage other).tapes (pool other) := by
  by_cases h : other = op
  · subst other
    simp only [rearm,get_set,rearmCore_tapes]
  · rw [rearm,other_set pool op other _ h]

theorem rearm_clean (pool : Pool) (op : RationalOp) (h : Clean pool) : Clean (rearm pool op) := by
  intro other i
  rw [rearm_tapes]
  exact h other i

theorem rearm_selected_initial (pool : Pool) (op : RationalOp) (h : Clean pool) :
    rearm pool op op = (arithmeticLayout op).initial emptyWord emptyWord := by
  rw [rearm,get_set]
  have ht : (arithmeticStorage op).tapes (pool op) =
      (arithmeticStorage op).tapes ((arithmeticLayout op).initial emptyWord emptyWord) := by
    funext i
    rw [h op i,initial_tapes_empty (arithmeticStorage op) i]
  simp only [rearmCore,ht,(arithmeticStorage op).set_tapes]

end IdentityTesting.BinaryInterpreterPool
