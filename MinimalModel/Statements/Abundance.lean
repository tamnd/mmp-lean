/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import MinimalModel.Statements.Basic

/-!
# Family E: abundance and non-vanishing

The statements of family E of spec 06.2.2 that are planned at S0 and S1.
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

/-- S42, abundance for a big log canonical divisor (the base point free theorem with `D = K + Δ`, KM98 Theorem 3.3; for a boundary with real coefficients, BCHM). For each projective klt pair such that `K + Δ` is nef and big, `K + Δ` is semiample. -/
def AbundanceBig : Prop :=
  ∀ A : PairModel k, IsKlt A.P → IsNef A.I A.P.KΔ → IsBig A.P.KΔ → IsSemiample A.P.KΔ

/-- S44, the reduction of Liu and Xu (arXiv:2505.05250). Fix `d`. Non-vanishing in dimension `d` (S41) gives abundance for the projective lc pairs of dimension `d` whose numerical dimension is at most one: if `K + Δ` is nef and `ν(K + Δ) ≤ 1`, then `K + Δ` is semiample. The numerical dimension is Nakayama's `κ_σ` (spec 06.5, risk 4). For a nef divisor it is the usual numerical dimension. The class is reduction. -/
def LiuXuReduction (d : ℕ) : Prop :=
  NonVanishing k d → ∀ A : PairModel k, A.X.dim = d → IsLc A.P → IsNef A.I A.P.KΔ →
    numericalDim A.P.KΔ ≤ 1 → IsSemiample A.P.KΔ

end MinimalModel
