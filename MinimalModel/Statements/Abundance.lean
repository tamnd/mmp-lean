/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import MinimalModel.Statements.Basic

/-!
# Family E: abundance and non-vanishing

The statements of family E of spec 06.2.2 that are planned at S0.
-/

universe u

namespace MinimalModel

variable (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]

/-- S40, the abundance conjecture in dimension `n` (KM98 3.12 in spec 03). For each projective lc pair of dimension `n`, if `K + Δ` is nef, then it is semiample. This is open for `n ≥ 4`. -/
def Abundance (n : ℕ) : Prop :=
  ∀ A : PairModel k, A.X.dim = n → IsLc A.P → IsNef A.I A.P.KΔ → IsSemiample A.P.KΔ

/-- S41, the non-vanishing conjecture in dimension `n` (spec 03). For each projective lc pair of dimension `n`, if `K + Δ` is pseudo-effective, then it is `ℝ`-linearly equivalent to an effective divisor. This is open for `n ≥ 4`. -/
def NonVanishing (n : ℕ) : Prop :=
  ∀ A : PairModel k, A.X.dim = n → IsLc A.P → IsPseudoEffective A.P.KΔ → IsREffective A.P.KΔ

end MinimalModel
