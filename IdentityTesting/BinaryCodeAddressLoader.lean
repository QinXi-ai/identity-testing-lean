import IdentityTesting.BinaryCodeWordLoader

namespace IdentityTesting.BinaryCodeWordLoader
open BinaryRegisterMachine

theorem binary_unary_address_load (a : ℕ) (code history : List Symbol) :
    let start : State := ⟨.reading,encode (List.replicate a false)++code,history,[],[]⟩
    advance (2*a+2) start =
      ⟨.halt,code,(encode (List.replicate a false)).reverse++history,[],List.replicate a false⟩ ∧
      bitSteps (2*a+2) start ≤ 18*a+18 := by
  simpa using binary_code_word_load (List.replicate a false) [] code history

theorem unary_address_cost (a registerCount : ℕ) (h : a < registerCount)
    (code history : List Symbol) :
    bitSteps (2*a+2) ⟨.reading,encode (List.replicate a false)++code,history,[],[]⟩ ≤
      18*registerCount+18 := by
  have hc := (binary_unary_address_load a code history).2
  omega

end IdentityTesting.BinaryCodeWordLoader
