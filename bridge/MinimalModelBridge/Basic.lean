/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/

/-!
# The bridge to AxiomMath/MMP

This package compares the statements of `MinimalModel` with the statements of AxiomMath/MMP where both apply (spec 06.4 and spec 04, the bridges O-R2-2 and O-R2-3).

## The files

* `MinimalModelBridge/Vocabulary/Variety.lean`: the varieties and the normal schemes of `MinimalModel` are those of AxiomMath/Stacks, which AxiomMath/MMP uses.
* `MinimalModelBridge/Vocabulary/PrimeDivisor.lean`: the prime divisors and the divisors with coefficients in `R` of `MinimalModel` are those of AxiomMath/Stacks and AxiomMath/MMP.
* `MinimalModelBridge/Vanishing.lean`: the Kawamata-Viehweg vanishing theorem of AxiomMath/MMP, stated in the vocabulary of `MinimalModel`, with the dictionary of its hypotheses.

## The tiers

The files import only the parts of AxiomMath/Stacks that they need, a few hundred modules, so that the hosted runners build them. The theorems of AxiomMath/MMP that the bridges of S10 to S19 and of the Kawamata-Viehweg theorem use import about 25,000 modules of AxiomMath/Stacks and AxiomMath/MMP. Their build is for the bridge runner of spec 09.4; `bridge/README.md` gives the measurements.
-/
