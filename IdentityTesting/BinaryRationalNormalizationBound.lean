import IdentityTesting.BinaryRationalNormalizationRuns

namespace IdentityTesting.BinaryRationalNormalizationMachine
open BinaryArithmetic BinaryLongDivision BinaryWordNormalization BinaryEuclideanRounds

theorem prepare_run (sg : Bool) (xs ys : List Bool) :
    Runs (initial sg xs ys) (2 * xs.length + 2 * ys.length + 4)
      ⟨.gcd, sg, BinaryGcdMachine.ready xs ys, BinaryDivisionMachine.initial xs [],
        BinaryDivisionMachine.initial ys [], []⟩ := by
  let g0 := BinaryGcdMachine.ready [] []
  let n0 := BinaryDivisionMachine.initial xs []
  let d0 := BinaryDivisionMachine.initial ys []
  have h0 : Runs (initial sg xs ys) (xs.length + 1)
      ⟨.tmpToN, sg, g0, BinaryDivisionMachine.initial [] [], d0, xs.reverse⟩ := by
    simpa [initial, g0, n0, d0, BinaryDivisionMachine.initial] using nToTmp_run sg g0 n0 d0 xs []
  have h1 : Runs ⟨.tmpToN, sg, g0, BinaryDivisionMachine.initial [] [], d0, xs.reverse⟩ (xs.length + 1)
      ⟨.dToTmp, sg, BinaryGcdMachine.ready xs [], n0, d0, []⟩ := by
    simpa [g0, n0, BinaryGcdMachine.ready, BinaryDivisionMachine.initial] using
      tmpToN_run sg g0 (BinaryDivisionMachine.initial [] []) d0 xs.reverse
  have h2 : Runs ⟨.dToTmp, sg, BinaryGcdMachine.ready xs [], n0, d0, []⟩ (ys.length + 1)
      ⟨.tmpToD, sg, BinaryGcdMachine.ready xs [], n0, BinaryDivisionMachine.initial [] [], ys.reverse⟩ := by
    simpa [d0, BinaryDivisionMachine.initial] using dToTmp_run sg (BinaryGcdMachine.ready xs []) n0 d0 ys []
  have h3 : Runs ⟨.tmpToD, sg, BinaryGcdMachine.ready xs [], n0, BinaryDivisionMachine.initial [] [], ys.reverse⟩
      (ys.length + 1) ⟨.gcd, sg, BinaryGcdMachine.ready xs ys, n0, d0, []⟩ := by
    simpa [d0, BinaryGcdMachine.ready, BinaryDivisionMachine.initial] using
      tmpToD_run sg (BinaryGcdMachine.ready xs []) n0 (BinaryDivisionMachine.initial [] []) ys.reverse
  convert ((h0.trans h1).trans h2).trans h3 using 1 <;> omega

theorem copyG_run (sg : Bool) (gs xs ys : List Bool) :
    Runs ⟨.gToTmp, sg, BinaryGcdMachine.terminal gs, BinaryDivisionMachine.initial xs [],
      BinaryDivisionMachine.initial ys [], []⟩ (2 * gs.length + 2)
      ⟨.divN, sg, BinaryGcdMachine.terminal [], BinaryDivisionMachine.initial xs gs,
        BinaryDivisionMachine.initial ys gs, []⟩ := by
  have h0 : Runs ⟨.gToTmp, sg, BinaryGcdMachine.terminal gs, BinaryDivisionMachine.initial xs [],
      BinaryDivisionMachine.initial ys [], []⟩ (gs.length + 1)
      ⟨.tmpToG, sg, BinaryGcdMachine.terminal [], BinaryDivisionMachine.initial xs [],
        BinaryDivisionMachine.initial ys [], gs.reverse⟩ := by
    simpa [BinaryGcdMachine.terminal, BinaryDivisionMachine.initial] using
      gToTmp_run sg (BinaryGcdMachine.terminal []) (BinaryDivisionMachine.initial xs [])
        (BinaryDivisionMachine.initial ys []) gs []
  have h1 : Runs ⟨.tmpToG, sg, BinaryGcdMachine.terminal [], BinaryDivisionMachine.initial xs [],
      BinaryDivisionMachine.initial ys [], gs.reverse⟩ (gs.length + 1)
      ⟨.divN, sg, BinaryGcdMachine.terminal [], BinaryDivisionMachine.initial xs gs,
        BinaryDivisionMachine.initial ys gs, []⟩ := by
    simpa [BinaryDivisionMachine.initial] using
      tmpToG_run sg (BinaryGcdMachine.terminal []) (BinaryDivisionMachine.initial xs [])
        (BinaryDivisionMachine.initial ys []) gs.reverse
  convert h0.trans h1 using 1 <;> omega

def terminal (sg : Bool) (g num den : List Bool)
    (rn rd : BinarySubtractorMachine.Registers) : State :=
  ⟨.halt, if num = [] then false else sg, BinaryGcdMachine.terminal [],
    BinaryDivisionMachine.terminal g num [] rn, BinaryDivisionMachine.terminal g den [] rd, []⟩

theorem normalization_run (sg : Bool) (m d : ℕ) (hd : 0 < d) :
    ∃ steps rn rd, steps ≤ 1000 * (m.size + d.size + 1) ^ 3 ∧
      Runs (initial sg m.bits d.bits) steps
        (terminal sg (Nat.gcd m d).bits (m / Nat.gcd m d).bits (d / Nat.gcd m d).bits rn rd) := by
  let g := Nat.gcd m d
  have hg : 0 < g := Nat.gcd_pos_of_pos_right m hd
  let ni := BinaryDivisionMachine.initial m.bits []
  let di := BinaryDivisionMachine.initial d.bits []
  obtain ⟨kg, hkg, heg⟩ := BinaryGcdMachine.gcd_run m d
  have hgh : (BinaryGcdMachine.advance kg (BinaryGcdMachine.ready m.bits d.bits)).phase = .halt := by
    rw [show BinaryGcdMachine.advance kg _ = _ from heg]
    rfl
  obtain ⟨jg, hjg, hfg⟩ := forward_gcd sg (BinaryGcdMachine.ready m.bits d.bits) ni di kg hgh
  have hfg' : Runs ⟨.gcd, sg, BinaryGcdMachine.ready m.bits d.bits, ni, di, []⟩ jg
      ⟨.gToTmp, sg, BinaryGcdMachine.terminal g.bits, ni, di, []⟩ := by
    simpa only [show BinaryGcdMachine.advance kg _ = _ from heg] using hfg
  obtain ⟨kn, rn, hkn, hen⟩ := BinaryDivisionMachine.division_run m.bits g.bits
  have hne : BinaryDivisionMachine.advance kn (BinaryDivisionMachine.initial m.bits g.bits) =
      BinaryDivisionMachine.terminal g.bits (m / g).bits [] rn := by
    simpa only [BinaryDivisionMachine.Runs, BinaryGcdMachine.divide_binary_eq m g hg,
      (show m % g = 0 from Nat.mod_eq_zero_of_dvd (Nat.gcd_dvd_left m d)), Nat.zero_bits] using hen
  have hnh : (BinaryDivisionMachine.advance kn (BinaryDivisionMachine.initial m.bits g.bits)).phase = .halt := by
    rw [hne]
    rfl
  obtain ⟨jn, hjn, hfn⟩ := forward_divN sg (BinaryGcdMachine.terminal [])
    (BinaryDivisionMachine.initial m.bits g.bits) (BinaryDivisionMachine.initial d.bits g.bits) kn hnh
  have hfn' : Runs ⟨.divN, sg, BinaryGcdMachine.terminal [], BinaryDivisionMachine.initial m.bits g.bits,
      BinaryDivisionMachine.initial d.bits g.bits, []⟩ jn
      ⟨.divD, sg, BinaryGcdMachine.terminal [], BinaryDivisionMachine.terminal g.bits (m / g).bits [] rn,
        BinaryDivisionMachine.initial d.bits g.bits, []⟩ := by simpa only [hne] using hfn
  obtain ⟨kd, rd, hkd, hed⟩ := BinaryDivisionMachine.division_run d.bits g.bits
  have hde : BinaryDivisionMachine.advance kd (BinaryDivisionMachine.initial d.bits g.bits) =
      BinaryDivisionMachine.terminal g.bits (d / g).bits [] rd := by
    simpa only [BinaryDivisionMachine.Runs, BinaryGcdMachine.divide_binary_eq d g hg,
      (show d % g = 0 from Nat.mod_eq_zero_of_dvd (Nat.gcd_dvd_right m d)), Nat.zero_bits] using hed
  have hdh : (BinaryDivisionMachine.advance kd (BinaryDivisionMachine.initial d.bits g.bits)).phase = .halt := by
    rw [hde]
    rfl
  obtain ⟨jd, hjd, hfd⟩ := forward_divD sg (BinaryGcdMachine.terminal [])
    (BinaryDivisionMachine.terminal g.bits (m / g).bits [] rn) (BinaryDivisionMachine.initial d.bits g.bits) kd hdh
  have hfd' : Runs ⟨.divD, sg, BinaryGcdMachine.terminal [], BinaryDivisionMachine.terminal g.bits (m / g).bits [] rn,
      BinaryDivisionMachine.initial d.bits g.bits, []⟩ jd
      ⟨.sign, sg, BinaryGcdMachine.terminal [], BinaryDivisionMachine.terminal g.bits (m / g).bits [] rn,
        BinaryDivisionMachine.terminal g.bits (d / g).bits [] rd, []⟩ := by simpa only [hde] using hfd
  have hlast : Runs ⟨.sign, sg, BinaryGcdMachine.terminal [], BinaryDivisionMachine.terminal g.bits (m / g).bits [] rn,
      BinaryDivisionMachine.terminal g.bits (d / g).bits [] rd, []⟩ 1
      (terminal sg g.bits (m / g).bits (d / g).bits rn rd) := rfl
  have hw := (((((prepare_run sg m.bits d.bits).trans hfg').trans
    (copyG_run sg g.bits m.bits d.bits)).trans hfn').trans hfd').trans hlast
  refine ⟨_, rn, rd, ?_, hw⟩
  have hgs := Nat.size_le_size (Nat.gcd_le_right m hd)
  have hrs := rounds_bound m d
  simp only [Nat.size_eq_bits_len] at hkn hkd ⊢
  set S := m.size + d.size + 1
  have hS : 1 ≤ S := by dsimp [S]; omega
  have hnS : m.size + g.size + 1 ≤ 2 * S := by dsimp [S, g] at *; omega
  have hdS : d.size + g.size + 1 ≤ 2 * S := by dsimp [S, g] at *; omega
  have hnSq := Nat.pow_le_pow_left hnS 2
  have hdSq := Nat.pow_le_pow_left hdS 2
  have hround := Nat.mul_le_mul_right (S ^ 2) (Nat.mul_le_mul_left 40 hrs)
  have hSS : S ^ 2 ≤ S ^ 3 := Nat.pow_le_pow_right (by omega) (by decide)
  have hS2 : S ≤ S ^ 2 := by nlinarith
  have hS3 : 1 ≤ S ^ 3 := Nat.one_le_pow 3 S (by omega)
  change kg ≤ 40 * rounds m d * S ^ 2 + 1 at hkg
  change 40 * rounds m d * S ^ 2 ≤ 40 * S * S ^ 2 at hround
  nlinarith

theorem binary_rational_normalization_machine (sg : Bool) (m d : ℕ) (hd : 0 < d) :
    ∃ steps, (advance steps (initial sg m.bits d.bits)).phase = .halt ∧
      (advance steps (initial sg m.bits d.bits)).num.quot.out = (m / Nat.gcd m d).bits ∧
      (advance steps (initial sg m.bits d.bits)).den.quot.out = (d / Nat.gcd m d).bits ∧
      bitSteps steps (initial sg m.bits d.bits) ≤ 9000 * (m.size + d.size + 1) ^ 3 := by
  obtain ⟨steps, rn, rd, hs, he⟩ := normalization_run sg m d hd
  refine ⟨steps, ?_, ?_, ?_, ?_⟩
  · rw [show advance steps _ = _ from he]; rfl
  · rw [show advance steps _ = _ from he]; rfl
  · rw [show advance steps _ = _ from he]; rfl
  · have hc := bitSteps_le steps (initial sg m.bits d.bits)
    nlinarith

end IdentityTesting.BinaryRationalNormalizationMachine
