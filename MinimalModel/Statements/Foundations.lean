/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import MinimalModel.Statements.Basic

/-!
# Family A: foundations

The statements of family A of spec 06.2.2 that are planned at S0. The other statements of the family (S01 to S03 and S05 to S09) come at S1 and S2.
-/

universe u

namespace MinimalModel

variable (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]

/-- S04, the cone theorem for projective klt pairs (KM98 Theorem 3.7, parts 1 and 2, without the rationality and the length of the curves). For each projective klt pair `(X, Δ)` over `k`, the closed cone of curves is `NE(X)_{K+Δ ≥ 0}` plus countably many extremal rays spanned by `(K + Δ)`-negative curves, and these rays are discrete away from `K + Δ = 0`. -/
def ConeTheoremKlt : Prop :=
  ∀ A : PairModel k, IsKlt A.P → ConeDecomposition A

end MinimalModel
