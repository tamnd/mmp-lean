/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import MinimalModel.Statements.Basic

/-!
# Family F: invariants and boundedness

The statements of family F of spec 06.2.2 that are planned at S1: the ACC for log canonical thresholds and the mld bound. The statements S49 and S50 of this family are in `Termination.lean`, because S28 uses them. S52 needs the definition of an enc germ, which is not in `Basic.lean` yet.
-/

universe u

namespace MinimalModel

variable (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]

/-- S48, the ACC for log canonical thresholds (Hacon, McKernan and Xu; Theorem 3.15 of spec 03). Fix `n`, a set `I ⊆ [0, 1]` and a set `J ⊆ [0, ∞)` that satisfy the DCC. Take the thresholds `lct(X, Δ; M)`, where `(X, Δ)` is an lc pair of dimension `n` with coefficients in `I`, and `M` is an effective `ℝ`-Cartier divisor with coefficients in `J`. The set of these thresholds satisfies the ACC. The coefficient of a prime divisor outside the support is `0`, so here `I` and `J` contain `0`. A set that satisfies the DCC still does when `0` is added, so this is no loss. -/
def ACCLct : Prop :=
  ∀ n : ℕ, ∀ I J : Set ℝ, I ⊆ Set.Icc 0 1 → J ⊆ Set.Ici 0 → I.IsWF → J.IsWF →
    ∀ a : ℕ → ℝ, (∀ i, ∃ (X : NormalVariety k) (P : Pair X) (M : Divisor ℝ X), X.dim = n ∧
      IsLc P ∧ P.Δ.CoeffsIn I ∧ 0 ≤ M ∧ IsRCartier M ∧ M.CoeffsIn J ∧ lct P M = a i) →
    ¬ StrictMono a

/-- S51, the mld bound (Shokurov; Conjecture 3.18 of spec 03). Let `(X, Δ)` be a pair and `x` a closed point of `X`. Then `mld(x; X, Δ) ≤ dim X`. Equality holds only if `X` is smooth at `x` and `x` is not in the support of `Δ`. This is open in general. -/
def MldBound : Prop :=
  ∀ (X : NormalVariety k) (P : Pair X) (x : X.toScheme), IsClosed ({x} : Set X.toScheme) →
    mld P x ≤ ((X.dim : ℝ) : WithBot ℝ) ∧
      (mld P x = ((X.dim : ℝ) : WithBot ℝ) → X.IsSmoothAt x ∧ x ∉ P.Δ.supp)

end MinimalModel
