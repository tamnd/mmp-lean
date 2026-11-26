# Changelog

All changes that a user can see are in this file. The format follows Keep a Changelog, and the versions follow Semantic Versioning.

## Unreleased

### Added

- `MinimalModel/Statements/Basic.lean`: the vocabulary of the program on Mathlib, with no `sorry`.
- The S0 statements S04, S10, S11, S12, S20, S22, S28, S30, S32, S33, S40, S41, S49 and S50.
- `MinimalModel/Fidelity/Basic.lean`: the first checks F3.
- `MinimalModel/Fidelity/Point.lean`: the first check F2. The point `Spec k` is a pair model, so the type `PairModel k` is not empty.
- `MinimalModel/Toric/Fan.lean`: rational polyhedral cones and fans on `PointedCone`.
- The fan API of route R3, steps 1 and 2. `MinimalModel/Toric/Fan.lean` now has the faces of cones, the trivial fan, the fan of one cone and the fan of `𝔸ⁿ`. `MinimalModel/Toric/Divisor.lean` has the rays, the torus-invariant divisors and the toric canonical divisor `K = -Σ D_ρ`. `MinimalModel/Toric/Examples.lean` has the fan of `ℙ¹`, which is complete and simplicial.
- The workflows `build`, `check`, `trust` and `scorecard`.
