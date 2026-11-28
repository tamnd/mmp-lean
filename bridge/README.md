# MinimalModelBridge

The bridge package compares the statements of `MinimalModel` with the statements of [AxiomMath/MMP](https://github.com/AxiomMath/MMP) at commit `1f9ade3670`. AxiomMath/MMP uses [AxiomMath/Stacks](https://github.com/AxiomMath/Stacks) at commit `c496df0d9b`. Both pin the Mathlib commit `56a00585`, which is the tag `v4.35.0` that `MinimalModel` uses, so the three share one Mathlib. The bridge is a separate Lake package because the build of AxiomMath/MMP is large.

## Build

```sh
cd bridge
lake exe cache get
lake build
```

The workflow `.github/workflows/bridge.yml` runs these steps on each pull request that touches `bridge/` or `MinimalModel/Statements/`, checks that the pins agree with the manifest of `MinimalModel`, and prints the axioms of the bridge declarations. The theorems of AxiomMath/MMP are built by the workflow `.github/workflows/bridge-full.yml`, in segments (see [The full build](#the-full-build)).

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

There is no compiled cache of AxiomMath/Stacks or AxiomMath/MMP. A hosted runner of GitHub has 4 cores, 16 GB of memory, a limit of 6 hours on a job and 10 GB of cache, so one job cannot build the theorems of AxiomMath/MMP. The segmented workflow `bridge-full.yml` (below) builds them over several runs.

The pair classes. `MinimalModel.IsKlt` and `MinimalModel.IsLc` quantify over the divisorial valuations of the function field. `MMP.Intersection.IsLogCanonicalPair`, `MMP.Fourfold.IsKltPair`, `MMP.Mori.IsKltPair` and `MMP.Mori.IsLcPair` quantify over the prime divisors on proper birational models. The comparison needs Zariski's lemma (KM98 2.45, a divisorial valuation is the valuation of a prime divisor on a model), the comparison of the canonical divisors (the top forms of `MinimalModel` against the rational pluriforms of AxiomMath/MMP) and the comparison of `ℝ`-Cartier divisors. Besides, `MMP.Fourfold.IsKltPair` has no condition on the coefficients of the boundary, so it agrees with `MinimalModel.IsKlt` only for an effective boundary. The coefficient conditions `Δ < 1` and `Δ ≤ 1` are compared, by `MinimalModelBridge.forall_divisorEquiv_iff`.

The statements S10 to S19. AxiomMath/MMP does not prove them in the form of `MinimalModel`. The map below gives, for each statement, the theorems of AxiomMath/MMP at commit `1f9ade3670` that come closest, with their modules, and the gap that a bridge theorem must close. All the theorems of AxiomMath/MMP in the map are in universe `0`, except the one of S10, which holds in each universe. The theorems of S10, S11 and the first theorem of S19 hold over each algebraically closed field (of characteristic zero for S11 and S19), and the others are over `ℂ`. The statements of `MinimalModel` are over each algebraically closed field `k` of characteristic zero, so each bridge over `ℂ` gives the statement for `k = ℂ` only, unless a Lefschetz principle is added. The map was read from the source, not checked by a build; the full build below checks that each declaration exists, with its axioms.

| Statement | Name in `MinimalModel` | Theorem of AxiomMath/MMP (module under `MMP.AlgebraicGeometry`) | The gap |
| --- | --- | --- | --- |
| S10 Castelnuovo contraction | `MinimalModel.Castelnuovo` (`Statements/LowDim.lean`) | `MMP.Resolution.Bridges.exists_contraction_of_isMinusOneCurve` (`Resolution.Surface.CastelnuovoContraction`): the relative contraction of a smooth rational curve `C ≅ ℙ¹` with `C² = -1` on a smooth surface over an algebraically closed field of each characteristic, in each universe; take `Z = Spec k` | the intersection numbers (`PairModel.I.dot` against `MMP.Mori.IsIntersectionNumber`); the hypothesis `C ≅ ℙ¹` of `MMP.Mori.IsMinusOneCurve` from `E² = -1` and `K · E = -1` (adjunction); smoothness (`NormalVariety.IsSmooth`, which is `Smooth X.str`, against `MMP.Mori.IsSmoothScheme`); the target `Y'` is proper, and `MinimalModel` asks that it be projective (a smooth proper surface is projective); the isomorphism off `C` is stated with the open set `{q}ᶜ` on both sides |
| S11 cone theorem for surfaces | `MinimalModel.SurfaceConeTheorem` | `MMP.Mori.IsKltPair.exists_relativeClosedConeOfCurves_eq_add_hull` (`MMP.ConeTheorem.RelativeConeTheorem`): klt, relative, with rational curves of length at most `2n`; take `Y = Spec k` | a smooth surface with `Δ = 0` is klt (the pair classes, below); the cone of curves and the curve classes of `PairModel.I` against `relativeClosedConeOfCurves` and `RelativeNumericalCurveClasses`; the extremality and the local finiteness of the rays, which `MinimalModel.ConeDecomposition` asks and the theorem gives only through the countable family |
| S12 MMP for smooth surfaces | `MinimalModel.SurfaceMMP` | `MMP.Fourfold.projectiveLowerLogMMP_three` (`MMP.Threefold.LogMMP`), which covers `dim X ≤ 3`, with `S = Spec ℂ` and `B = 0`; `MMP.Fourfold.rationalBirationalProgramProperty_two` (`MMP.Surface.RationalBirationalProgram`) is relative and birational, over a base of dimension 2, so it does not give S12 | over `ℂ` only; the programs (`MMP.Fourfold.RelativeDltProgram` against `MinimalModel.Program`); the endpoint is a model with `K` nef or a Mori fibre space, but `SurfaceMMP` asks that it be smooth, which needs that each step of a smooth surface is the contraction of a `(-1)`-curve (S10); the Mori fibre spaces (`MMP.Fourfold.IsMoriFibreSpace` against `MinimalModel.IsMoriFibreSpace`) |
| S13 MMP for lc surfaces | `MinimalModel.LcSurfaceMMP` | `MMP.Fourfold.projectiveLowerLogMMP_three`, for `ℚ`-factorial dlt pairs with rational boundary | over `ℂ` only; dlt and `ℚ`-factorial against lc, and rational against real boundaries: no theorem of AxiomMath/MMP covers lc surface pairs that are not dlt; the programs |
| S14 abundance for lc surfaces | `MinimalModel.SurfaceAbundance` | none; two special cases: `MMP.Fourfold.QDivisor.isRelativelySemiample_of_isLcPair_of_isRelativelyNef_of_isRelativelyBig` (`MMP.Surface.LcNefBigSemiample`, `K + B` nef and big) and `MMP.Threefold.exists_isRelativelyFreeDivisor_of_isLogCanonicalPair_of_add_qLinearlyEquivalent` (`MMP.Surface.ComplementedLcSemiample`, a complemented form) | no source: abundance is outside the scope of AxiomMath/MMP |
| S15 3-fold klt flips | `MinimalModel.ThreefoldFlips` | `MMP.Fourfold.exists_isFlip_of_isKltPair` (`MMP.Threefold.Flip.KltFlipExistence`): `ℚ`-factorial klt, dimension 3; also `MMP.Fourfold.IsContractionOfRay.exists_isFlip` (`MMP.Threefold.DltFlipExistence`, dlt) | over `ℂ` only, rational boundary; the pair classes; the extremal contractions (`IsNegativeExtremalRayOf`, `IsContractionOfRay`, `IsFlippingContraction` against `IsContraction`, `IsSmallHom`, `IsExtremalContraction`, `IsRAmpleOver`); the flip (`MMP.Fourfold.IsFlip` against the strict transform and the ampleness of `K + Δ` over `Z`) |
| S16 3-fold termination | `MinimalModel.ThreefoldTermination` | `MMP.Fourfold.SequenceOfFlips.terminates_of_isDltPair` (`MMP.Threefold.DltFlipTermination`, `ℚ`-factorial dlt) and `MMP.Fourfold.forall_projectiveKltTerminationLevel_and_terminates` (`MMP.Threefold.KltFlipTermination`, `ℚ`-factorial klt); also `projectiveLowerLogMMP_three` | over `ℂ` only; `ℚ`-factorial dlt against lc: an lc 3-fold needs a dlt modification first; the sequences of flips (`MMP.Mori.SequenceOfFlips` against `MinimalModel.HasInfiniteFlips`) |
| S17 abundance for lc 3-folds | `MinimalModel.ThreefoldAbundance` | none; one special case: `MMP.Fourfold.isRelativelySemiample_of_isLogCanonicalPair_add_of_qLinearlyEquivalent` (`MMP.Abundance.ComplementedLcThreefold`, a complemented form) | no source: abundance is outside the scope of AxiomMath/MMP |
| S18 MMP for lc 3-folds | `MinimalModel.ThreefoldLcMMP` | `MMP.Fourfold.projectiveLowerLogMMP_three`; for real klt pairs, `MMP.Fourfold.IsRealKltPair.exists_program_isRelativelyNef_or_isFibreType` (`MMP.Threefold.Termination.RealKltProgram`) | over `ℂ` only; `ℚ`-factorial dlt against lc, as for S16; the programs: `ProjectiveLowerLogMMP` says that each projective program terminates and that one maximal program exists, and `MinimalModel.EveryProgramEnds` says that each finite program extends to one that ends |
| S19 special termination | `MinimalModel.SpecialTermination` (`Statements/Termination.lean`) | `MMP.Fourfold.exists_forall_ge_disjoint_exceptionalSet_of_isFlipOf` (`MMP.Threefold.Termination.SpecialTermination`: `n = 3`, `ℚ`-factorial dlt, over each algebraically closed field of characteristic zero) and `MMP.Fourfold.SequenceOfFlips.eventually_disjoint_exceptionalSet_supp_roundDown` (`MMP.Fourfold.Termination.SpecialTermination`: `n = 4`, over `ℂ`) | only `n = 3` and `n = 4`, and the hypothesis `T(m)` for `m < n` is not used; sequences of flips against the steps of `MinimalModel.IsMMPStep`, which may be divisorial contractions (finitely many, by the Picard number); the conclusion: the exceptional sets of the flips miss the components of `⌊B⌋`, against `MMPStepData.IsIsoNear` of `⌊Δ⌋` |

Each bridge needs the pair classes above and the dictionary of the programs (`MinimalModel.Program` against the programs of AxiomMath/MMP), and the build of 6,000 to 27,000 modules.

No bridge theorem of S10 to S19 is written yet. The vocabulary files compare only the varieties and the divisors; each row above needs at least one more comparison (the intersection numbers, the pair classes, the cones, the programs or the flips), so a file `Programs.lean` with a bridge theorem would rest on comparisons that are not stated. The first candidate is S10: its theorem of AxiomMath/MMP holds in each universe and each characteristic, and its gap is the intersection numbers, adjunction and projectivity, with no pair class and no program.

## The full build

The workflow `.github/workflows/bridge-full.yml` builds the bridge package together with the modules of AxiomMath/MMP of the map above and of the Kawamata-Viehweg theorem, listed with their declarations in `full.txt`. A person starts it by hand (`workflow_dispatch`, segment 1). Each run builds for 120 minutes with `scripts/bridge-full.sh`, saves the partial build of `.lake/build`, `bridge/.lake/build` and the builds of AxiomMath/MMP and AxiomMath/Stacks in the cache under a key tied to the hash of `lake-manifest.json`, deletes the older caches of the chain, and starts the next run on the same ref. The modules of `heavy.txt`, which ran out of memory in a parallel build of the audit of tamnd/mmp, are built first, each alone in a memory-limited scope. The run that finishes prints the axioms of each declaration of `full.txt`, fails on an axiom outside `propext`, `Classical.choice` and `Quot.sound`, and uploads the artifact `bridge-full-records`. The model is the workflow `audit-build.yml` of tamnd/mmp, which builds all of AxiomMath/MMP at the same commit.

## Rules

1. A bridge lemma is an equivalence or an implication between a statement of this project and a statement of AxiomMath/MMP. It never proves an open statement.
2. The bridge moves to a new commit of AxiomMath/MMP only after the delta audit of that commit (Q-02).
3. The universe of the statements of this project is specialized to `0` when a statement of AxiomMath/MMP needs it (Q-07). The vocabulary files hold in each universe.
