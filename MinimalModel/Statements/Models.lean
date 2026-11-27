/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import MinimalModel.Statements.BasicRelative
import MinimalModel.Statements.LinearSystems
import MinimalModel.Statements.Cones

/-!
# Family D: BCHM, models and the Sarkisov program

The statements of family D of spec 06.2.2 that are planned at S0, S1, S2 and S3. The statements S31 and S34 use the relative notions of `BasicRelative.lean`, S34 uses the linear systems of `LinearSystems.lean`, and S37 uses the Mori dream spaces of `Cones.lean`. The statement S36 (`Sarkisov`) is not stated yet: it needs the Sarkisov links, which are not in the tree.
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


/-- S34, the finiteness of models (BCHM, arXiv:math/0610203v2, Theorem E, that is `E_n`; the general ample divisors are those of the paragraph after Definition 1.1.4). Let `π : X → U` be a projective morphism to a quasi-projective variety, with `X` of dimension `n`. Assume that `X` has a klt pair `(X, Δ₀)`. Let `V` be a finite dimensional affine subspace of the real Weil divisors, defined over the rationals. Let `A ≥ 0` be a general ample `ℚ`-divisor over `U`. Then there are finitely many birational maps `ψⱼ : X ⇢ Zⱼ` over `U` such that each weak log canonical model `ψ : X ⇢ Z` over `U` of `K + Δ`, for some `Δ ∈ L_A(V)`, is `ξ ∘ ψⱼ` for some `j` and some isomorphism `ξ : Zⱼ → Z`.

A general ample divisor is written out as in BCHM. Let `D` be a divisor that is very ample over `U` (BCHM's `k A`), and let `m > 0` (BCHM's `k`). For a very general nonzero `φ` in `H⁰(X, 𝒪_X(D))`, set `A' = D + div φ` and `A = A' / m`. The conclusion holds for this `A`. The set of good `φ` may depend on `X`, `U`, `π`, `V` and `D`, which come first. BCHM fix `A` before `V` in Theorem E, but the proof (Lemma 7.2, through 3.7.3 and 3.7.4) and Corollary 1.1.5 take `A` general with respect to `V`.

What the Lean form changes:
* The base `U` is a normal variety, as in S31. The reason is the same: `π` factors through the normalization of its image.
* `k` is uncountable. Over a countable field, countably many hypersurfaces cover `H⁰(X, 𝒪_X(D))`, and the statement says nothing. BCHM work over `ℂ`.
* BCHM take `A' ∼_U k A`, a linear equivalence over `U`. Here `A' ∼ D` on `X`, but `D` ranges over all divisors that are very ample over `U`, and `D + π^* L` is very ample over `U` when `D` is. So each member of the linear system over `U` is covered.
* "Very ample over `U`" is checked on each affine open set of `U` (`IsVeryAmpleOver`).
* The maps `ψⱼ` and `ψ` are identifications of function fields, as in S31, and `ψ = ξ ∘ ψⱼ` is `IsCompOfIso`.

The theorem of BCHM is `∀ n, FinitenessOfModels k n`. The row of spec 06.2.2 speaks of log terminal models over a rational polytope. Theorem E speaks of weak log canonical models over all of `L_A(V)`, which is a rational polytope (BCHM Lemma 3.7.2). Each log terminal model is a weak log canonical model, so this form implies the form of the row. -/
def FinitenessOfModels [Uncountable k] (n : ℕ) : Prop :=
  ∀ (X U : NormalVariety k) (π : X.toScheme ⟶ U.toScheme), π ≫ U.str = X.str →
    IsProjectiveHom π → IsQuasiProjective U → X.dim = n → (∃ P₀ : Pair X, IsKlt P₀) →
    ∀ V : AffineSubspace ℝ (Divisor ℝ X), IsRationalAffineSubspace V →
    ∀ D : Divisor ℤ X, IsVeryAmpleOver D π → ∀ m : ℕ, 0 < m →
    IsVeryGeneral k {φ : RRSpace D | ∀ A' : Divisor ℤ X, IsDivOn (A' - D) (φ : FF X) Set.univ →
      ∃ (l : ℕ) (Z : Fin l → NormalVariety k) (g : ∀ j, (Z j).toScheme ⟶ U.toScheme)
        (σ : ∀ j, FF (Z j) ≃ₐ[k] FF X),
        (∀ j, g j ≫ U.str = (Z j).str ∧ IsBirMapOver π (g j) (σ j)) ∧
        ∀ P : Pair X, P.InLA ((m : ℝ)⁻¹ • A'.toReal) V →
          ∀ (Y : NormalVariety k) (Q : Pair Y) (h : Y.toScheme ⟶ U.toScheme)
            (τ : FF Y ≃ₐ[k] FF X), IsWeakLcModelOver P Q π h τ →
            ∃ j, ∃ ξ : (Z j).toScheme ≅ Y.toScheme, IsCompOfIso (σ j) τ ξ}

/-- S37, Fano type varieties are Mori dream spaces (BCHM, arXiv:math/0610203v2, Corollary 1.3.1, the absolute case). Let `X` be a projective `ℚ`-factorial variety with a dlt pair `(X, Δ)` such that `-(K + Δ)` is ample. Then `X` is a Mori dream space in the sense of Hu and Keel, Definition 1.10 (`IsMoriDreamSpace`).

What the Lean form changes:
* BCHM state the corollary for a projective morphism `π : X → U` to an affine variety `U`. This statement takes `U = Spec k`, as S35 does. Hu and Keel define a Mori dream space for a projective variety, so the absolute case is the one their definition covers.
* The pair `(X, Δ)` of the tree asks that `K + Δ` is `ℝ`-Cartier, as BCHM do. Since `X` is `ℚ`-factorial, this is no condition.
* The intersection numbers `A.I` are part of the model; by `dot_cartier` they are the intersection numbers of `X`. -/
def FanoTypeMDS : Prop :=
  ∀ A : PairModel k, IsQFactorial A.X → IsDlt A.P → IsAmple (-A.P.KΔ) → IsMoriDreamSpace A.X A.I

end MinimalModel
