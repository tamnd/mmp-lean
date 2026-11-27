# MinimalModelBridge

The bridge package compares the statements of `MinimalModel` with the statements of [AxiomMath/MMP](https://github.com/AxiomMath/MMP) at commit `1f9ade3670`. AxiomMath/MMP uses [AxiomMath/Stacks](https://github.com/AxiomMath/Stacks) at commit `c496df0d9b`. Both pin the Mathlib commit `56a00585`, which is the tag `v4.35.0` that `MinimalModel` uses, so the three share one Mathlib. The bridge is a separate Lake package because the build of AxiomMath/MMP is large.

## Build

```sh
cd bridge
lake exe cache get
lake build
```

The workflow `.github/workflows/bridge.yml` runs these steps on each pull request that touches `bridge/` or `MinimalModel/Statements/`, checks that the pins agree with the manifest of `MinimalModel`, and prints the axioms of the bridge declarations.

## What is bridged

| File | Content | Imports of AxiomMath |
| --- | --- | --- |
| `Vocabulary/Variety.lean` | `MinimalModel.IsVariety` is `AlgebraicGeometry.IsVariety`; `IsNormalScheme` is `IsNormal` on an integral scheme; a `NormalVariety` is a normal variety of AxiomMath/MMP and back | 111 modules of AxiomMath/Stacks |
| `Vocabulary/PrimeDivisor.lean` | the prime divisors (points of coheight one) are the prime divisors of AxiomMath/Stacks (integral closed subschemes of codimension one); the divisors with coefficients in `R` agree, with their coefficients and their order | 61 modules of AxiomMath/Stacks |
| `Vanishing.lean` | the Kawamata-Viehweg theorem of AxiomMath/MMP (KM98 2.64), stated in the vocabulary of `MinimalModel` as `KawamataViehwegSNC`, with the dictionary of its hypotheses | none |

The names `MMP.Mori.PrimeDivisor`, `MMP.Mori.DivisorWithCoeffs`, `MMP.Mori.Divisor`, `MMP.Mori.QDivisor`, `MMP.Mori.RDivisor`, `MMP.Mori.IsVariety` and `MMP.Mori.IsNormalVariety` are abbreviations of the names of AxiomMath/Stacks that the two vocabulary files use, so the comparison holds for them by unfolding.

## What is not bridged, and why

The size of the imports. The number of modules of AxiomMath/Stacks and AxiomMath/MMP, outside Mathlib, that a file must build:

| Import | Modules | Lines |
| --- | --- | --- |
| `StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.GenericPoint` | 61 | 21k |
| `StacksFrontier.AlgebraicGeometry.Properties.Normal` | 108 | 51k |
| `MMP.AlgebraicGeometry.Divisor.Basic` | 1,395 | 463k |
| `MMP.AlgebraicGeometry.Singularities.LogDiscrepancy` | 4,364 | 1.43M |
| `MMP.Fourfold.Singularities` | 6,101 | 1.93M |
| `MMP.AlgebraicGeometry.Vanishing.KawamataViehweg` | 25,405 | 8.0M |
| all of `MMP` | 27,236 | 9.7M |

There is no compiled cache of AxiomMath/Stacks or AxiomMath/MMP. A hosted runner of GitHub has 4 cores, 16 GB of memory, a limit of 6 hours on a job and 10 GB of cache, so it cannot build the theorems of AxiomMath/MMP. They need the bridge runner of spec 09.4.

The pair classes. `MinimalModel.IsKlt` and `MinimalModel.IsLc` quantify over the divisorial valuations of the function field. `MMP.Intersection.IsLogCanonicalPair`, `MMP.Fourfold.IsKltPair`, `MMP.Mori.IsKltPair` and `MMP.Mori.IsLcPair` quantify over the prime divisors on proper birational models. The comparison needs Zariski's lemma (KM98 2.45, a divisorial valuation is the valuation of a prime divisor on a model), the comparison of the canonical divisors (the top forms of `MinimalModel` against the rational pluriforms of AxiomMath/MMP) and the comparison of `ℝ`-Cartier divisors. Besides, `MMP.Fourfold.IsKltPair` has no condition on the coefficients of the boundary, so it agrees with `MinimalModel.IsKlt` only for an effective boundary. The coefficient conditions `Δ < 1` and `Δ ≤ 1` are compared, by `MinimalModelBridge.forall_divisorEquiv_iff`.

The statements S10 to S19. AxiomMath/MMP does not prove them in the form of `MinimalModel`:

| Statement | Theorem of AxiomMath/MMP | The gap |
| --- | --- | --- |
| S10 Castelnuovo contraction | none found | no source |
| S11 cone theorem for surfaces | `IsKltPair.exists_relativeClosedConeOfCurves_eq_add_hull` (klt, relative) | the dictionary of the cones of curves and of the pair classes |
| S12, S13 surface MMP | `rationalBirationalProgramProperty_two`: over `ℂ`, a relative dlt program for a smooth surface with an snc boundary over a projective birational base | different scope: over `ℂ` only, relative and birational, from a smooth source; spec 06.4 lists it for S12 and S13, which is too wide |
| S14 abundance for surfaces | none | abundance is outside the scope of AxiomMath/MMP |
| S15, S16, S18 3-fold MMP | `projectiveLowerLogMMP_three`: over `ℂ`, the program for `ℚ`-factorial dlt pairs | over `ℂ` only and dlt; S16 and S18 are lc over each algebraically closed field of characteristic zero. S15 over `ℂ` follows only after the dictionary of the programs and of the extremal contractions |
| S17 abundance for 3-folds | none | outside the scope of AxiomMath/MMP |
| S19 special termination | the special termination of the fourfold files | the dictionary of the programs; not checked in detail |

Each of these needs the pair classes above and the dictionary of the programs (`MinimalModel.Program` against the programs of AxiomMath/MMP), and the build of 6,000 to 27,000 modules.

## Rules

1. A bridge lemma is an equivalence or an implication between a statement of this project and a statement of AxiomMath/MMP. It never proves an open statement.
2. The bridge moves to a new commit of AxiomMath/MMP only after the delta audit of that commit (Q-02).
3. The universe of the statements of this project is specialized to `0` when a statement of AxiomMath/MMP needs it (Q-07). The vocabulary files hold in each universe.
