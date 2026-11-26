# Changelog

All changes that a user can see are in this file. The format follows Keep a Changelog, and the versions follow Semantic Versioning.

## Unreleased

## v0.0.4 - 2026-11-26

### Added

- The statements S01 (Kleiman's criterion), S02 (Kawamata-Viehweg vanishing), S06 (the contraction theorem), S09 (the length of extremal rays), S52 (the Han-Liu conjecture on enc pairs in dimension 4) and S57 (the failure of effective non-vanishing in dimension 4). The new files `Curves.lean`, `Cohomology.lean` and `Enc.lean` give their vocabulary: extremal faces, rational curves, relative positivity, the higher direct images of `𝒪_X(D)` and the enc pairs. `MinimalModel/Fidelity/PointStatements.lean` gives the checks F2 and F3 on the point and the affine line.
- `MinimalModel/Statements/BasicRelative.lean`, `MinimalModel/Toric/Program.lean` and `MinimalModel/Statements/ToricMMP.lean`, with additions to `LowDim.lean`, `Termination.lean`, `Models.lean`, `Abundance.lean` and `Boundedness.lean`: the statements S14 `SurfaceAbundance`, S17 `ThreefoldAbundance`, S29 `HanLiuReduction`, S31 `BCHM`, S39 `ToricMMP`, S43 `AbundanceNuZero`, S45 `GeneralizedAbundance`, S46 `IitakaConj` and S54 `IndexConj`. The new vocabulary is numerical equivalence, the Kodaira dimension, the relative notions and models of BCHM, and the toric program on fans. `MinimalModel/Fidelity/Relative.lean` checks that the relative notions over `Spec k` are the absolute ones.
- The workflow `trust` has a last job, `record`, that writes `replay.json` from the results of leanchecker, lean4lean, nanoda and the comparator, and uploads it as the artifact `replay-record`. mmp reads it for the rows Q3 and Q4 of the trust report.
- `MinimalModel/Statements/Toric.lean`: the pinned statement `ToricConeTheorem` of the toric cone theorem in combinatorial form, and the theorem `toricConeTheorem` that proves it from `Fan.coneTheorem`. `comparator.json` and `Comparator/Challenge.lean` list it, so the job `comparator` of the workflow `trust` checks it (row Q4).
- `MinimalModel/Statements/LinearSystems.lean` and the statement S34 `FinitenessOfModels` (BCHM Theorem E) in `Models.lean`. The new vocabulary is `H⁰(X, 𝒪_X(D))` as a submodule (`RRSpace`), the members of a linear system, very general points of a module, very ample divisors over a base, the rational affine spaces of divisors and the set `L_A(V)` of BCHM Definition 1.1.4. `BasicRelative.lean` adds the weak log canonical models over a base. `MinimalModel/Fidelity/LinearSystems.lean` checks that `0` and `1` are sections, that the members of a linear system are effective, and that the whole space is very general.

### Fixed

- The sources of S43 and S45, checked against the arXiv copies. S43 cites Gongyo, arXiv:1101.1394, Theorem 6.1 and Lemma 6.2 (Theorem 1.2 there is about minimal models), and Nakayama, Corollary V.4.9. S45 `GeneralizedAbundance` now takes the boundary with rational coefficients, `L` a nef Cartier divisor and the semiample divisor `M` a `ℚ`-divisor, as Lazić and Peternell do. The arXiv copy does not number the conjecture, so the docstring names it and no longer says Conjecture 1.1.

## v0.0.3 - 2026-11-26

### Added

- `MinimalModel/Fidelity/Centre.lean` and `MinimalModel/Fidelity/AffineLinePairs.lean`: a valuation has at most one centre on a variety, and the log discrepancy of a prime divisor is `1 - Δ Q` for every pair, so plt, canonical and terminal give klt and plt gives lc with no hypothesis. On a curve each centre of a divisorial valuation is a prime divisor, so `(𝔸¹, 0)` is klt, lc, plt, dlt, terminal and canonical, `(𝔸¹, c[0])` is klt for `c < 1` and `(𝔸¹, c[0])` is lc for `c ≤ 1`.
- `MinimalModel/Statements/Classes.lean`: the class `IsPlt` of purely log terminal pairs (KM98 Definition 2.34) and the implications among the classes of pairs. Klt gives plt and dlt, dlt gives lc, and terminal and canonical give plt when the coefficients are at most one. The implications to klt and lc, and plt to dlt, take the missing facts as hypotheses. The checks show that `(Spec k, 0)` is plt and that `(𝔸¹, 2[0])` is not plt, not klt and not dlt.
- `MinimalModel/Toric/Cone.lean`: the data of a wall, the degree of a divisor on a wall (CLS11 Proposition 6.4.4), and the fact that the degree is nonnegative exactly when the wall inequality holds. On `ℙ²` each prime divisor has degree 1 on each wall, and `-K` is nef.
- `MinimalModel/Toric/ConeTheorem.lean`: the toric cone theorem in combinatorial form, `Fan.coneTheorem`. On a complete simplicial fan, an R-Cartier divisor is nef exactly when its degree on each wall curve is nonnegative. The main step is that a support function on a complete fan is convex exactly when it satisfies the wall inequality at each wall.

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
