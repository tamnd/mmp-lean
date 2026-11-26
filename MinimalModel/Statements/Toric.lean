/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import MinimalModel.Toric.Fan
import MinimalModel.Toric.Divisor
import MinimalModel.Toric.Cone

/-!
# The toric cone theorem

The pinned statement of the toric cone theorem of route R3 (spec 04.4), the first top theorem of milestone S2. Row Q4 of spec 14 compares the proved theorem `MinimalModel.Toric.toricConeTheorem` with this statement.

The file uses the toric definitions of `MinimalModel/Toric/Fan.lean`, `MinimalModel/Toric/Divisor.lean` and `MinimalModel/Toric/Cone.lean`. It does not import the proof.
-/

namespace MinimalModel.Toric

/-- The toric cone theorem, combinatorial form (Cox, Little and Schenck, Theorem 6.3.12 and Proposition 6.4.4; Reid 1983, Decomposition of toric morphisms). Let `F` be a complete simplicial fan in `ℝⁿ` and `D` an R-Cartier torus-invariant divisor. Then `D` is nef, in the sense that its support function is convex (`Fan.IsNef`), exactly when its degree on the curve of each wall `σ ∩ σ'` of two maximal cones is nonnegative. The degree is read off the fan with the data of the wall (`Fan.WallData.degree`).

This is the combinatorial form of the theorem. The geometric form says that the cone of curves of the toric variety is spanned by the classes of the wall curves `V(τ)`. It needs the toric variety as a scheme, with its curves and intersection numbers. -/
def ToricConeTheorem : Prop :=
  ∀ (n : ℕ) (F : Fan n), F.IsComplete → F.IsSimplicialFan → ∀ D : F.TDivisor ℝ, F.IsRCartier D →
    (F.IsNef D ↔ ∀ σ σ' : PointedCone ℝ (NR n), F.IsWallPair σ σ' →
      ∀ W : F.WallData σ σ', 0 ≤ W.degree D)

end MinimalModel.Toric
