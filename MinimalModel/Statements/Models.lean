/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import MinimalModel.Statements.BasicRelative

/-!
# Family D: BCHM, models and the Sarkisov program

The statements of family D of spec 06.2.2 that are planned at S0, S1 and S2. The statement S31 uses the relative notions of `BasicRelative.lean`.
-/

universe u

namespace MinimalModel

open AlgebraicGeometry CategoryTheory Order

variable (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]

/-- S30, the existence of klt flips (BCHM Corollary 1.4.1). Let `(X, Δ)` be a projective klt pair, and let `f : X → Z` be a flipping contraction: a small contraction of relative Picard number one with `-(K + Δ)` ample over `Z`. Then the flip `g : X⁺ → Z` exists. -/
def KltFlips : Prop :=
  ∀ A : PairModel k, IsKlt A.P → ∀ (Z : NormalVariety k) (f : A.X.toScheme ⟶ Z.toScheme),
    f ≫ Z.str = A.X.str → IsContraction f → IsSmallHom f → IsExtremalContraction A.I f →
    IsRAmpleOver (-A.P.KΔ) f →
    ∃ (B : PairModel k) (g : B.X.toScheme ⟶ Z.toScheme), g ≫ Z.str = B.X.str ∧
      IsContraction g ∧ IsSmallHom g ∧ IsRAmpleOver B.P.KΔ g ∧ IsStrictTransform A B f g

/-- The canonical ring `R(X, K) = ⊕ₘ H⁰(X, m K)`, as the `k`-subalgebra of `k(X)[t]` that the elements `φ tᵐ` with `φ ∈ H⁰(X, m K)` generate. -/
noncomputable def canonicalRing {k : Type u} [Field k] {X : NormalVariety k} (K : CanonicalDivisor X) :
    Subalgebra k (Polynomial (FF X)) :=
  Algebra.adjoin k {p | ∃ (m : ℕ) (φ : FF X), φ ∈ sections ((m : ℤ) • K.K) ∧ p = Polynomial.monomial m φ}

/-- S32, the finite generation of the canonical ring (BCHM Corollary 1.1.2). For each smooth projective variety `X`, the canonical ring is a finitely generated `k`-algebra. -/
def FiniteGenerationCanonical : Prop :=
  ∀ X : NormalVariety k, X.IsSmooth → IsProjective X → ∀ K : CanonicalDivisor X, (canonicalRing K).FG

/-- S33, the existence of minimal models (spec 03). Each projective lc pair of dimension `n` with `K + Δ` pseudo-effective has a minimal model in the sense of KM98 Definition 3.50. This is known for `n ≤ 4` and open for `n ≥ 5` (spec 01.1). -/
def MinimalModelConj (n : ℕ) : Prop :=
  ∀ A : PairModel k, A.X.dim = n → IsLc A.P → IsPseudoEffective A.P.KΔ → ∃ B, IsMinimalModel A B

/-- S35, the Mori fibre space output (BCHM Corollary 1.3.2, the absolute case). Let `(X, Δ)` be a projective `ℚ`-factorial klt pair such that `K + Δ` is not pseudo-effective. Then some program from `(X, Δ)` is finite and ends with a Mori fibre space. BCHM run the program with scaling of an ample divisor. The statement is about some program, as the source is. The row of spec 06.2.2 also asks that `Δ` is big; the source does not, and this statement does not. -/
def MoriFibreSpaceOutput : Prop :=
  ∀ A : PairModel k, IsQFactorial A.X → IsKlt A.P → ¬ IsPseudoEffective A.P.KΔ →
    ∃ p : Program A, ∃ n : ℕ, p.len = n ∧ IsMoriFibreSpace (p.model n)

/-- S31, the main theorem of BCHM (Birkar, Cascini, Hacon and McKernan, Existence of minimal models for varieties of log general type, J. Amer. Math. Soc. 23 (2010), Theorem 1.2; Theorem 3.10 of spec 03). Let `π : X → U` be a projective morphism to a quasi-projective variety, and let `(X, Δ)` be a klt pair (the pair asks that `K + Δ` is `ℝ`-Cartier). Assume that `Δ` is big over `U` and `K + Δ` is pseudo-effective over `U`, or that `K + Δ` is big over `U`. Then:
1. `(X, Δ)` has a log terminal model over `U`;
2. if `K + Δ` is big over `U`, then `(X, Δ)` has a log canonical model over `U`;
3. if `K + Δ` is `ℚ`-Cartier, then `R(π, K + Δ) = ⊕ₘ π_* 𝒪_X(⌊m (K + Δ)⌋)` is a finitely generated `𝒪_U`-algebra.

The models are those of BCHM Definition 3.6.6 (`HasLogTerminalModelOver`, `HasLcModelOver`). The base `U` is a normal variety here. This is no loss: `X` is normal, so `π` factors through the normalization of its image, which is finite over `U`, and each notion of the statement is the same over the normalization.

The row of spec 06.2.2 also names the six statements `A_n` to `F_n` of the induction of BCHM (Theorems A to F of the source). They are the steps of the proof, not part of Theorem 1.2, and they are not stated here. -/
def BCHM : Prop :=
  ∀ (X U : NormalVariety k) (π : X.toScheme ⟶ U.toScheme), π ≫ U.str = X.str →
    IsProjectiveHom π → IsQuasiProjective U → ∀ P : Pair X, IsKlt P →
    ((IsBigRel P.Δ π ∧ IsPseudoEffectiveOver P.KΔ π) ∨ IsBigRel P.KΔ π) →
      HasLogTerminalModelOver P π ∧ (IsBigRel P.KΔ π → HasLcModelOver P π) ∧
        (IsQCartierReal P.KΔ → IsRelFG P.KΔ π)

end MinimalModel
