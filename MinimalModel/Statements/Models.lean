/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import MinimalModel.Statements.Basic

/-!
# Family D: BCHM, models and the Sarkisov program

The statements of family D of spec 06.2.2 that are planned at S0 and S1.
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

/-- S33, the existence of minimal models (spec 03). Each projective lc pair of dimension `n` with `K + Δ` pseudo-effective has a minimal model in the sense of KM98 Definition 3.50. This is open for `n ≥ 4`. -/
def MinimalModelConj (n : ℕ) : Prop :=
  ∀ A : PairModel k, A.X.dim = n → IsLc A.P → IsPseudoEffective A.P.KΔ → ∃ B, IsMinimalModel A B

/-- S35, the Mori fibre space output (BCHM Corollary 1.3.2, the absolute case). Let `(X, Δ)` be a projective `ℚ`-factorial klt pair such that `K + Δ` is not pseudo-effective. Then some program from `(X, Δ)` is finite and ends with a Mori fibre space. BCHM run the program with scaling of an ample divisor. The statement is about some program, as the source is. The row of spec 06.2.2 also asks that `Δ` is big; the source does not, and this statement does not. -/
def MoriFibreSpaceOutput : Prop :=
  ∀ A : PairModel k, IsQFactorial A.X → IsKlt A.P → ¬ IsPseudoEffective A.P.KΔ →
    ∃ p : Program A, ∃ n : ℕ, p.len = n ∧ IsMoriFibreSpace (p.model n)

end MinimalModel
