# MinimalModelBridge

The bridge package compares the statements of `MinimalModel` with the statements of [AxiomMath/MMP](https://github.com/AxiomMath/MMP) at commit `1f9ade3670`. It is a separate Lake package, because AxiomMath/MMP pins a Mathlib commit (`56a00585`) that is not the Mathlib release of `MinimalModel`.

## Build

The build of AxiomMath/MMP is large. Use the bridge runner (spec 09.4), not a laptop.

```sh
cd bridge
lake exe cache get
lake build
```

## Rules

1. A bridge lemma is an equivalence or an implication between a statement of this project and a statement of AxiomMath/MMP. It never proves an open statement.
2. The bridge moves to a new commit of AxiomMath/MMP only after the delta audit of that commit (Q-02).
3. The universe of the statements of this project is specialized to `0` when a statement of AxiomMath/MMP needs it (Q-07).
