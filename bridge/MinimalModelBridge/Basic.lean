/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import MinimalModel

/-!
# The bridge to AxiomMath/MMP

This package will prove that the statements of `MinimalModel` agree with the statements of AxiomMath/MMP where both apply (spec 06.4 and spec 04, the bridges O-R2-2 and O-R2-3). The first bridge lemmas compare the pair classes klt and lc, and then the statement S22 with the 4-fold termination theorem of AxiomMath/MMP.

At S0 this file has no lemma. The bridge runner builds AxiomMath/MMP from S1 on, because a cold build takes about 6 hours (spec 15.2). The import of `MMP` comes with the first lemma.
-/
