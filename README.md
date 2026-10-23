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

The statistical proof constructs tests for the point-mass, allocation, moment,
and heavy-atom interior/exterior regimes, then transfers finite results to
countable references. The evaluation algorithm includes rational allocation
oracles, certified root searches, maximum-atom selection, and moment intervals.

**Scope:** polynomial bit-operation complexity is not formalized here. Executable
definitions and proved termination do not establish a polynomial-time bound.
This repository formalizes the core results, not every auxiliary claim or example
in the manuscript.

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
