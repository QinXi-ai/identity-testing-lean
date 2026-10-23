# Identity testing in Lean

Lean 4 formalization of the core results of *Instance-Optimal Identity Testing
at the Original Total-Variation Radius: Resolving Canonne's 2024 Open Question 1*,
by Xi Qin (Wuhan University).

## Verified results

- **Statistical characterization.** For every probability distribution on the
  natural numbers and every radius `0 < ε ≤ 1`, the sample complexity is bounded
  above and below by universal constant multiples of the characterization scale.
  The model uses independent samples, randomized tests with both errors at most
  `1/3`, and strict alternatives `ε < totalVariation p q`. Alternative distributions
  may assign mass outside the reference support.
- **Certified rational evaluation.** For any nonempty finite list of positive
  rational probabilities summing to one and a rational radius `0 < ε ≤ 1`, an
  executable algorithm returns rational endpoints satisfying
  `0 ≤ L ≤ complexityScale(q, ε) ≤ U ≤ 2L`. The endpoints are positive when
  `ε < 1` and both zero when `ε = 1`.
- **Rational representation sizes.** Explicit bounds for reduced numerators and
  denominators, the coordinate-bisection endpoints and actual queries, and the
  allocation oracle's parameters, search queries, and returned intervals, all in
  terms of the original rational input length.
- **Continuity and relabeling.** Joint continuity of the overlap moment under
  arbitrary ℓ¹ convergence and positive limiting overlap targets; invariance of
  allocation, moment, roots, and characterization scales under countable
  permutations, including tied largest atoms.
- **Explicit examples.** Exact uniform allocation and root formulas, the
  near-endpoint scale `max(1, √(k(1−ε)))`, and the flat-tail boundary scale
  `k^(2/5)/R`, including its exterior minimum transition.
- **Minimum sample counts.** A natural-number minimum in the original test
  model, its universal scale comparison, and the exact point-mass formula.
- **General roots and signed mixtures.** Existence and continuity of roots for
  arbitrary nonnegative summable mass vectors; the general signed-likelihood
  matrix total-variation bound and its explicit heavy-atom Frobenius constant.
- **Binary arithmetic machines.** Fixed finite-control stack machines for
  addition and multiplication, with proved termination, correct binary outputs,
  and explicit polynomial bounds on primitive bit actions.

The statistical proof constructs tests for the point-mass, allocation, moment,
and heavy-atom interior/exterior regimes, then transfers finite results to
countable references. The evaluation algorithm includes rational allocation
oracles, certified root searches, maximum-atom selection, and moment intervals.

**Scope:** polynomial bit-operation complexity is not formalized here. Executable
definitions and proved termination do not establish a polynomial-time bound.
Some auxiliary manuscript claims and the complete arithmetic/algorithm cost
composition remain unfinished.

### Representation-size bounds

Write `L(q) = 1 + bits(|q.num|) + bits(q.den)` and
`V(a) = k + ∑ᵢ L(aᵢ)`. The checked results include:

- After `n` coordinate-bisection steps, each endpoint has length at most `2n+3`.
- The actual query after `i` completed steps has length at most `2i+5`; its sign-polynomial
  value has length at most `2(L(a)+L(β))+76i+255`.
- For `B = 2n+2L(ρ)+7`, each pole-safe coordinate endpoint has length at most `B`.
  Each objective-interval endpoint has length at most `2V(a)+2kB+3`, and each
  budget-interval endpoint at most `4V(a)+2k(2L(t)+12B+22)+3`.
- The computed precision `n = oracleDyadicPrecision C δ` satisfies
  `n ≤ L(C)+L(δ)+1` whenever `δ > 0`.

For the actual allocation oracle, let `S = V(a)+L(t)+L(σ)`. Its chosen inner
precision is at most `33S+158`, and its outer fuel is at most `30S+126`.
An instrumented search returns the same interval and records at most `30S+128`
source-level budget/objective calls; every recorded parameter has length at most `180S+737`.
Each returned endpoint has length at most `368S²+1778S+25`.

For the full interval algorithm, put `T = V(q)+L(ε)`. Each returned endpoint has
length at most `288T²+2536T+5355`. Both root searches have linear bounds on
their source-level oracle-call counts, query lengths, and tolerances in their
own input lengths. Square-root and moment interval representations are bounded
as well.

These statements refer to the executable Lean definitions. The coordinate
routine bisects `[0,1]` and clips the upper endpoint to `1−ρ`; its correctness
is proved for this implementation. Rational normalization and composition of
the remaining arithmetic operations through the full algorithm must still be
proved before a polynomial bit-operation complexity theorem can be claimed.

The separate bit-stack machines add binary inputs `m,n` in at most
`50 max(bits(m),bits(n))+20` primitive actions and multiply them in at most
`140 bits(m)(bits(m)+bits(n)+1)+7`. Their transitions operate on individual
Boolean stack cells and finite registers. These bounds concern that explicit
machine model, not Lean's native integer runtime.

## Build and verify

Install [elan](https://github.com/leanprover/elan), then run:

```sh
git clone https://github.com/QinXi-ai/identity-testing-lean.git
cd identity-testing-lean
lake exe cache get
lake build +IdentityTesting:olean
lake env lean Verification.lean
```

Lean is pinned to **4.24.0** in `lean-toolchain`. Mathlib is pinned to commit
`f897ebcf72cd16f89ab4577d0c826cd14afaafc7`; transitive dependencies are recorded
in `lake-manifest.json`. No local machine paths or external proof certificates
are required.

`Verification.lean` imports the public entry point, prints the main theorem
types and definitions, audits their transitive axioms, and evaluates examples
covering all branches and a reordered reference. The audited proofs use only
`propext`, `Classical.choice`, and `Quot.sound`.

## Entry points

| File | Result |
|---|---|
| [IdentityTesting.lean](IdentityTesting.lean) | Public import |
| [CountableCharacterization.lean](IdentityTesting/CountableCharacterization.lean) | Full countable statistical theorem |
| [CountableCharacterizationRealScale.lean](IdentityTesting/CountableCharacterizationRealScale.lean) | Bounds directly in the real characterization scale |
| [RationalComplexityScale.lean](IdentityTesting/RationalComplexityScale.lean) | Executable interval algorithm and its specification |
| [RationalEncodingBounds.lean](IdentityTesting/RationalEncodingBounds.lean) | Reduced rational arithmetic and precision encoding bounds |
| [RationalBisectionEncoding.lean](IdentityTesting/RationalBisectionEncoding.lean) | Dyadic grid invariant and actual query encoding bounds |
| [RationalOracleEvaluationEncoding.lean](IdentityTesting/RationalOracleEvaluationEncoding.lean) | Pole-safe coordinate, budget, and objective encoding bounds |
| [RationalOracleResourceBounds.lean](IdentityTesting/RationalOracleResourceBounds.lean) | Actual oracle parameters, trace, and output sizes |
| [OverlapMomentJointContinuity.lean](IdentityTesting/OverlapMomentJointContinuity.lean) | General ℓ¹ and target joint continuity |
| [CountableRelabeling.lean](IdentityTesting/CountableRelabeling.lean) | Countable permutation invariance of the actual functionals |
| [AllocationScaling.lean](IdentityTesting/AllocationScaling.lean) | Exact mass scaling of the countable allocation functional |
| [EqualBlockAllocation.lean](IdentityTesting/EqualBlockAllocation.lean) | Exact equal-mass block optimization |
| [UniformExamples.lean](IdentityTesting/UniformExamples.lean) | Uniform root formulas and statistical scales |
| [FlatTailExamples.lean](IdentityTesting/FlatTailExamples.lean) | Flat-tail roots, quantitative bounds, and statistical scales |
| [MinimumSampleComplexity.lean](IdentityTesting/MinimumSampleComplexity.lean) | Literal minimum-sample characterization |
| [GeneralRootContinuity.lean](IdentityTesting/GeneralRootContinuity.lean) | General summable-vector roots and convergence |
| [GeneralSignedMatrixHeavy.lean](IdentityTesting/GeneralSignedMatrixHeavy.lean) | General signed-mixture TV theorem and heavy-atom constants |
| [RationalComplexityEncoding.lean](IdentityTesting/RationalComplexityEncoding.lean) | Full algorithm output-size bound |
| [BinaryAdderMachine.lean](IdentityTesting/BinaryAdderMachine.lean) | Fixed-stack addition machine |
| [BinaryMultiplierBound.lean](IdentityTesting/BinaryMultiplierBound.lean) | Fixed-stack multiplication machine and cost bound |
| [AllocationExplicitDerivatives.lean](IdentityTesting/AllocationExplicitDerivatives.lean) | Explicit first and second derivatives, with strict concavity on the simplex |
| [Target.lean](IdentityTesting/Target.lean) | Allocation, moment, root, and scale definitions |
| [CountableModel.lean](IdentityTesting/CountableModel.lean) | Statistical model |
| [Verification.lean](Verification.lean) | Type, axiom, and execution audit |

The main exports are:

```lean
IdentityTesting.countable_characterization
IdentityTesting.countable_characterization_realScale
IdentityTesting.RationalComputation.rationalComplexityInterval
IdentityTesting.RationalComputation.rationalComplexityInterval_spec
```

Additional verified results include exact point-mass and small-overlap endpoint
sample counts, allocation-root rounding bounds, finite Hölder bounds, and the
explicit moment upper bound `(5 * 10^13 + 1) / W`.
