# Changelog

All changes that a user can see are in this file. The format follows Keep a Changelog, and the versions follow Semantic Versioning.

## Unreleased

## v0.0.2 - 2026-11-26

### Fixed

- The docstring of `MinimalModel.MinimalModelConj` (S33) says that the statement is known for `n ≤ 4` and open for `n ≥ 5`, as spec 01.1 says. The docstrings of `MinimalModel/Fidelity/PointPairs.lean` no longer call the point an F2 instance of S22, because S22 is about dimension 4.

### Added

- `MinimalModel/Fidelity/AffineLine.lean`: the affine line as a normal variety, the Cartier divisor `[0]`, and the canonical divisor `div(dX) = 0`. The checks F3 show that `(𝔸¹, 2[0])` is not lc and that `(𝔸¹, [0])` is not klt.
- The toric files of route R3, steps 3 and 4. `MinimalModel/Toric/Fan.lean` has the primitive lattice points. `MinimalModel/Toric/Divisor.lean` has the primitive generator of a ray with its uniqueness, the Cartier and Q-Cartier conditions on the fan and the support functions. `MinimalModel/Toric/Examples.lean` has the fan of `ℙ²`, which is complete and simplicial, with a Cartier canonical divisor and the wall relation.
- The toric files of route R3, the rays and the wall. Each cone of a fan is spanned by the generators of its rays, an R-Cartier divisor has a unique support function (CLS11 Theorem 4.2.12), and `MinimalModel/Toric/Wall.lean` has the wall relation for adjacent smooth cones with unique integer coefficients.

## v0.0.1 - 2026-11-26

### Added

- `MinimalModel/Statements/Basic.lean`: the vocabulary of the program on Mathlib, with no `sorry`.
- The S0 statements S04, S10, S11, S12, S20, S22, S28, S30, S32, S33, S40, S41, S49 and S50.
- The S1 statements S05, S07, S08, S13, S15, S16, S18, S19, S21, S23, S24, S25, S26, S35, S42, S44, S48, S51 and S56, with the new files `Boundedness.lean` and `Effective.lean` and the new vocabulary for thresholds, scaling, the reduced boundary and complete programs.
- `MinimalModel/Fidelity/Basic.lean`: the first checks F3.
- `MinimalModel/Fidelity/Point.lean`: the first check F2. The point `Spec k` is a pair model, so the type `PairModel k` is not empty.
- `MinimalModel/Fidelity/PointPairs.lean`: more of check F2. The pair `(Spec k, 0)` is klt, lc, terminal, canonical and dlt, and the conclusions of S04, S20 and S22 hold for it.
- `MinimalModel/Toric/Fan.lean`: rational polyhedral cones and fans on `PointedCone`.
- The fan API of route R3, steps 1 and 2. `MinimalModel/Toric/Fan.lean` now has the faces of cones, the trivial fan, the fan of one cone and the fan of `𝔸ⁿ`. `MinimalModel/Toric/Divisor.lean` has the rays, the torus-invariant divisors and the toric canonical divisor `K = -Σ D_ρ`. `MinimalModel/Toric/Examples.lean` has the fan of `ℙ¹`, which is complete and simplicial.
- The workflows `build`, `check`, `trust` and `scorecard`.
