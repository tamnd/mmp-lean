/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import MinimalModel.Statements.Basic

/-!
# Family A: foundations

The statements of family A of spec 06.2.2 that are planned at S0 and S1: S04, S05, S07 and S08. The other statements of the family (S01 to S03, S06 and S09) need vocabulary that is not in `Basic.lean` yet.
-/

universe u

namespace MinimalModel

variable (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]

/-- S04, the cone theorem for projective klt pairs (KM98 Theorem 3.7, parts 1 and 2, without the rationality and the length of the curves). For each projective klt pair `(X, Δ)` over `k`, the closed cone of curves is `NE(X)_{K+Δ ≥ 0}` plus countably many extremal rays spanned by `(K + Δ)`-negative curves, and these rays are discrete away from `K + Δ = 0`. -/
def ConeTheoremKlt : Prop :=
  ∀ A : PairModel k, IsKlt A.P → ConeDecomposition A

/-- S05, the cone theorem for projective lc pairs (Fujino 2011, the cone theorem for lc pairs). This is the conclusion of S04 for each projective lc pair `(X, Δ)` over `k`: the closed cone of curves is `NE(X)_{K+Δ ≥ 0}` plus countably many extremal rays spanned by `(K + Δ)`-negative curves, and these rays are discrete away from `K + Δ = 0`. -/
def ConeTheoremLc : Prop :=
  ∀ A : PairModel k, IsLc A.P → ConeDecomposition A

/-- S07, the rationality theorem (KM98 Theorem 3.5). Let `(X, Δ)` be a projective klt pair such that `K + Δ` is not nef. Let `a > 0` be an integer such that `a (K + Δ)` is Cartier, and let `H` be an ample Cartier divisor. Let `r` be the nef threshold, the largest `t` such that `H + t (K + Δ)` is nef. Then `r / a = u / v` for natural numbers `u` and `v` with `0 < v ≤ a (dim X + 1)`. This statement takes `H` ample, as the node of the map does. The `reader` role compares the hypothesis on `H` with KM98 before F5. -/
def RationalityTheorem : Prop :=
  ∀ A : PairModel k, IsKlt A.P → ¬ IsNef A.I A.P.KΔ → ∀ a : ℕ, 0 < a →
    (∃ E : Divisor ℤ A.X, IsCartier E ∧ (a : ℝ) • A.P.KΔ = E.toReal) →
    ∀ H : Divisor ℤ A.X, IsRelAmple H A.X.str →
      ∃ u v : ℕ, 0 < v ∧ v ≤ a * (A.X.dim + 1) ∧
        nefThreshold A.I H.toReal A.P.KΔ / a = (u : ℝ) / v

/-- S08, the base point free theorem (KM98 Theorem 3.3). Let `(X, Δ)` be a projective klt pair, and let `D` be a nef Cartier divisor such that `a D - (K + Δ)` is nef and big for some real `a > 0`. Then the linear system `|b D|` is free for each large `b`. So `D` is semiample. KM98 takes a boundary with rational coefficients. The case of real coefficients follows from it by a small change of `Δ`. -/
def BasepointFree : Prop :=
  ∀ A : PairModel k, IsKlt A.P → ∀ D : Divisor ℤ A.X, IsCartier D → IsNef A.I D.toReal →
    ∀ a : ℝ, 0 < a → IsNef A.I (a • D.toReal - A.P.KΔ) → IsBig (a • D.toReal - A.P.KΔ) →
      ∃ b₀ : ℕ, ∀ b : ℕ, b₀ ≤ b → IsFree ((b : ℤ) • D)

end MinimalModel
