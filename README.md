# mmp-lean

The Lean 4 code of the mmp project. The project states the minimal model program of birational geometry in Lean, proves the known parts, from the toric program and the surface program to the reductions of the open conjectures, audits the 4-fold termination claim of AxiomMath/MMP, and works on the open parts as research bets.

**The open conjectures of the program are not proved.** This package states them, and it proves only the results that have a proof in the literature or a proof in this package. A statement of an open conjecture is a `def ... : Prop`. It is never a theorem and never an axiom.

The map of the project, the milestones and the site are in [tamnd/mmp](https://github.com/tamnd/mmp). The site is [mmp.tamnd.com](https://mmp.tamnd.com). The `mmp` command that reads the records of this package is in [tamnd/mmp-agent](https://github.com/tamnd/mmp-agent). The handbook is in [tamnd/mmp-handbook](https://github.com/tamnd/mmp-handbook).

## Layout

| Directory | Content |
|---|---|
| `MinimalModel/Statements/` | the statements of the program, one file for each family of spec 06.2.2, pinned in `manifests/statements.sha256` |
| `MinimalModel/Statements/Basic.lean` | the vocabulary: normal varieties, divisors, canonical divisors, pairs, log discrepancies, the pair classes, ampleness, curves, the cone of curves, contractions, flips and programs |
| `MinimalModel/Fidelity/` | checks F1 to F3 of the fidelity battery: special cases, known examples and known non-examples |
| `MinimalModel/Toric/` | route R3: cones, fans and the toric program |
| `MinimalModel/WIP/` | unfinished work, not imported by `MinimalModel.lean` |
| `bridge/` | the package `MinimalModelBridge`, which compares the statements with AxiomMath/MMP |

## The vocabulary

The definitions use Mathlib only. The main choices are these (spec 06.2.3, Q-04):

1. The log discrepancy is defined for each divisorial valuation of the function field, through the lattices of top forms. The definition does not need a resolution, so it also has a meaning in characteristic p.
2. An ample divisor is defined through the affine loci of its sections (EGA II 4.5.2).
3. The intersection numbers are a structure `IntersectionData` with the axioms that fix them on Cartier divisors. A model of the program carries one.
4. A step of the program is a contraction of an extremal ray followed by a small map. A divisorial contraction is the case where the small map is the identity.
5. The termination statements say that no infinite sequence of steps exists. So they are about every program, not about some program.

## Build

You need [elan](https://github.com/leanprover/elan). The toolchain is in `lean-toolchain`.

```sh
lake exe cache get
lake build
sh scripts/scan.sh
```

The workflow `build` also writes `records/lean.json` with `scripts/Export.lean`. That record has the kind, the file, the type and the axioms of each declaration. `mmp index` in tamnd/mmp reads it.

## Trust

Each proof in the main tree uses only the axioms `propext`, `Classical.choice` and `Quot.sound`. The workflow `build` checks this on each push. The workflow `trust` replays the package each week in the Lean kernel with `leanchecker`, checks it again with lean4lean and nanoda, and runs `lake comparator --paranoid` on the proved top theorems.

## Pins

| Item | Pin |
|---|---|
| Lean | v4.35.0 |
| Mathlib | v4.35.0 |
| AxiomMath/MMP (audit and bridge) | 1f9ade3670 |

## Licence

Apache-2.0. See [LICENSE](LICENSE).
