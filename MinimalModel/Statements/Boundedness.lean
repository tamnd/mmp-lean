/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import MinimalModel.Statements.Basic
import MinimalModel.Statements.Enc

/-!
# Family F: invariants and boundedness

The statements of family F of spec 06.2.2 that are planned at S1 and S2: the ACC for log canonical thresholds, the mld bound and the index conjecture. The statements S49 and S50 of this family are in `Termination.lean`, because S28 uses them. The statement S52 uses the enc pairs of `Enc.lean`, and S29 in `Termination.lean` uses `EncMldACC`.
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

/-- The ACC for the minimal log discrepancies of enc pairs of dimension `d` with coefficients in a finite set (Han-Liu, Conjecture 1.9(2')). Fix a finite set `Γ ⊆ [0, 1]`. The set `eMLD_d(Γ)` of the values `mld(X, Δ)`, where `(X, Δ)` is an enc pair of dimension `d` with the coefficients of `Δ` in `Γ`, satisfies the ACC: no sequence in it is strictly increasing. The mld is the global one, `globalMld`, as in Han-Liu Definition 3.8. The coefficient of a prime divisor outside the support is `0`, so the condition on the coefficients is with `0` added to `Γ`. -/
def EncMldACC (d : ℕ) : Prop :=
  ∀ Γ : Set ℝ, Γ ⊆ Set.Icc 0 1 → Γ.Finite → ∀ a : ℕ → ℝ,
    (∀ i, ∃ (X : NormalVariety k) (P : Pair X), X.dim = d ∧ IsEnc P ∧
      P.Δ.CoeffsIn (insert 0 Γ) ∧ globalMld P = (a i : WithBot ℝ)) →
    ¬ StrictMono a

/-- S52, the Han-Liu conjecture on enc pairs in dimension 4 (J. Han and J. Liu, "On termination of flips and exceptionally non-canonical singularities", Geom. Topol. 29 (2025), arXiv:2209.13122, Conjecture 1.9(2') with `d = 4`). For each finite set `Γ ⊆ [0, 1]`, the mlds of the enc pairs of dimension 4 with coefficients in `Γ` satisfy the ACC. By Han-Liu Theorem 1.2, this conjecture gives the termination of lc flips in dimension 4. The source states the conjecture for enc pairs and the global mld, so this statement does too. An enc germ `(X ∋ x, B)` of Definition 3.8(2) is an enc pair near `x` with `mld(X ∋ x, B) = mld(X, B)`, so its mld is in the same set. -/
def HanLiuEncACC : Prop :=
  EncMldACC k 4

/-- S54, the index conjecture for klt log Calabi-Yau pairs in dimension `n` (Shokurov; the form of spec 03.9). Fix a finite set `I ⊆ [0, 1]` of rational numbers. There is a positive integer `N` with the following property. Let `(X, Δ)` be a projective klt pair of dimension `n` with the coefficients of `Δ` in `I`, such that `K + Δ ∼_ℝ 0`. Then `N (K + Δ)` is the divisor of a rational function, that is `N (K + Δ) ∼ 0`. So the index of `K + Δ` is at most `N`, and divides `N`. The coefficient of a prime divisor outside the support is `0`, so the statement adds `0` to `I`. It is known in low dimensions and open in general. -/
def IndexConj (n : ℕ) : Prop :=
  ∀ I : Set ℝ, I.Finite → I ⊆ Set.Icc 0 1 ∩ Set.range ((↑) : ℚ → ℝ) →
    ∃ N : ℕ, 0 < N ∧ ∀ (X : NormalVariety k) (P : Pair X), IsProjective X → X.dim = n →
      IsKlt P → P.Δ.CoeffsIn (insert 0 I) → RLinEquiv P.KΔ 0 →
        ∃ E : Divisor ℤ X, IsPrincipal E ∧ (N : ℝ) • P.KΔ = E.toReal

end MinimalModel
