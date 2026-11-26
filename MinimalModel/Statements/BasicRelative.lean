/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import MinimalModel.Statements.Basic
import MinimalModel.Statements.Curves

/-!
# More vocabulary for the statements of milestone S2

This file adds the definitions that the statements S31, S45 and S46 use and that `Basic.lean` does not have:

* numerical equivalence of `ℝ`-Cartier divisors and the Kodaira dimension;
* the relative notions of BCHM Definition 3.1.1 and the models over a base of BCHM Definition 3.6.6.

Bigness over a base is `IsBigRel` of `Curves.lean`, which is BCHM 3.1.1(7) in the second form. BCHM use `ℝ`-linear equivalence over `Z`, which also allows the pullback of an `ℝ`-Cartier divisor of `Z`. The sum of an ample divisor over `Z` and such a pullback is ample over `Z`, so the two forms agree. Nefness over a base is `IsNefRel` of `Curves.lean`, with the condition that the divisor is `ℝ`-Cartier (BCHM 3.1.1(6)).

Each definition has a body, and the file uses none of the escape hatches of spec 09.2.
-/

universe u

open AlgebraicGeometry CategoryTheory Order TopologicalSpace Filter

namespace MinimalModel

variable {k : Type u} [Field k] {X : NormalVariety k}

/-! ## Numerical equivalence and the Kodaira dimension -/

/-- Two `ℝ`-Cartier divisors are numerically equivalent: they have the same intersection number with each curve. -/
def NumEquiv (I : IntersectionData X) (D D' : Divisor ℝ X) : Prop :=
  IsRCartier D ∧ IsRCartier D' ∧ ∀ C, I.dot D C = I.dot D' C

/-- The Kodaira dimension `κ(X)`: the Iitaka dimension of a canonical divisor. It is `⊥` (that is `-∞`) when no multiple of `K` has a section. -/
noncomputable def kodairaDim (K : CanonicalDivisor X) : WithBot ℕ := iitakaDim K.K.toReal

/-! ## Relative notions (BCHM Definition 3.1.1) -/

/-- A quasi-projective variety: it has an ample Cartier divisor. -/
def IsQuasiProjective (U : NormalVariety k) : Prop := ∃ D : Divisor ℤ U, IsRelAmple D U.str

/-- An `ℝ`-divisor that is pseudo-effective over `Z`: for one divisor `A` that is ample over `Z`, each sum `D + ε A` with `ε > 0` is big over `Z`. BCHM 3.1.1(10) ask that the restriction of `D` to the generic fibre is pseudo-effective. Bigness over `Z` is bigness on the generic fibre (3.1.1(7)), so the two agree. Over `Spec k` this is `IsPseudoEffective`. -/
def IsPseudoEffectiveOver {Z : Scheme.{u}} (D : Divisor ℝ X) (π : X.toScheme ⟶ Z) : Prop :=
  ∃ A : Divisor ℝ X, IsRAmpleOver A π ∧ ∀ ε : ℝ, 0 < ε → IsBigRel (D + ε • A) π

/-- A `ℚ`-Cartier `ℝ`-divisor: a positive multiple is a Cartier divisor. Then its coefficients are rational. -/
def IsQCartierReal (D : Divisor ℝ X) : Prop :=
  ∃ m : ℕ, 0 < m ∧ ∃ E : Divisor ℤ X, IsCartier E ∧ (m : ℝ) • D = E.toReal

/-! ## Birational maps over a base and the models of BCHM 3.6.6 -/

/-- The identification `σ : k(Y) ≅ k(X)` is a birational map `X ⇢ Y` over `U`, for `π : X → U` and `g : Y → U`. The generic points of `X` and `Y` have the same image in `U`, and `σ` matches the pullbacks of the functions on the open sets of `U` that contain this image. -/
def IsBirMapOver {Y : NormalVariety k} {U : Scheme.{u}} (π : X.toScheme ⟶ U) (g : Y.toScheme ⟶ U)
    (σ : FF Y ≃ₐ[k] FF X) : Prop :=
  π.base (genericPoint X.toScheme) = g.base (genericPoint Y.toScheme) ∧
    ∀ (V : U.Opens) (hX : genericPoint X.toScheme ∈ π ⁻¹ᵁ V)
      (hY : genericPoint Y.toScheme ∈ g ⁻¹ᵁ V) (s : Γ(U, V)),
      σ ((g.app V ≫ Y.toScheme.presheaf.germ (g ⁻¹ᵁ V) _ hY).hom s) =
        (π.app V ≫ X.toScheme.presheaf.germ (π ⁻¹ᵁ V) _ hX).hom s

/-- The map `σ` is a birational contraction `φ : X ⇢ Y` over `U` and `Q` carries the strict transform `φ_* Δ` of the boundary of `P`: each prime divisor of `Y` is a prime divisor of `X`, with the same coefficient. -/
def IsBirContractionOver (P : Pair X) {Y : NormalVariety k} (Q : Pair Y) {U : Scheme.{u}}
    (π : X.toScheme ⟶ U) (g : Y.toScheme ⟶ U) (σ : FF Y ≃ₐ[k] FF X) : Prop :=
  IsBirMapOver π g σ ∧
    ∀ Q' : PrimeDivisor Y, ∃ P' : PrimeDivisor X, SameDivisor σ P' Q' ∧ Q.Δ Q' = P.Δ P'

/-- The comparison `rel` of log discrepancies on the divisors that `σ` contracts: for each prime divisor of `X` that is not a divisor of `Y`, its log discrepancy `a` on `X` and `b` on `Y` satisfy `rel a b`. With `≤` this is `(K + Δ)`-non-positive, and with `<` it is `(K + Δ)`-negative, by BCHM Lemma 3.6.3, since `K_Y + Γ` is nef over the base in each use. -/
def DiscrepancyCompare (P : Pair X) {Y : NormalVariety k} (Q : Pair Y) (σ : FF Y ≃ₐ[k] FF X)
    (rel : ℝ → ℝ → Prop) : Prop :=
  ∀ P' : PrimeDivisor X, (∀ Q', ¬ SameDivisor σ P' Q') →
    ∀ v : Valuation (FF X) VZ, IsDivisorial v → IsCentre v P'.1 →
      ∀ a b, LogDiscrepancyIs P v a → LogDiscrepancyIs Q (v.comap σ.toRingHom) b → rel a b

/-- `(X, Δ)` has a log terminal model over `U` (BCHM Definition 3.6.6): a birational contraction `φ : X ⇢ Y` over `U` to a `ℚ`-factorial variety `Y`, projective over `U`, such that `(Y, φ_* Δ)` is dlt, `K_Y + φ_* Δ` is nef over `U`, and `φ` is `(K + Δ)`-negative. -/
def HasLogTerminalModelOver (P : Pair X) {U : NormalVariety k} (π : X.toScheme ⟶ U.toScheme) :
    Prop :=
  ∃ (Y : NormalVariety k) (Q : Pair Y) (g : Y.toScheme ⟶ U.toScheme), g ≫ U.str = Y.str ∧
    IsProjectiveHom g ∧ IsQFactorial Y ∧ IsDlt Q ∧ IsRCartier Q.KΔ ∧ IsNefRel Q.KΔ g ∧
    ∃ σ : FF Y ≃ₐ[k] FF X, IsBirContractionOver P Q π g σ ∧ DiscrepancyCompare P Q σ (· < ·)

/-- `(X, Δ)` has a log canonical model over `U`: a birational contraction `φ : X ⇢ Y` over `U`, with `Y` projective over `U`, that is `(K + Δ)`-non-positive and such that `K_Y + φ_* Δ` is ample over `U`. This is a weak log canonical model (BCHM 3.6.6) with `K_Y + φ_* Δ` ample over `U`. By BCHM Lemma 3.6.5 it is then the ample model of `K + Δ` over `U`, that is the log canonical model of 3.6.6. -/
def HasLcModelOver (P : Pair X) {U : NormalVariety k} (π : X.toScheme ⟶ U.toScheme) : Prop :=
  ∃ (Y : NormalVariety k) (Q : Pair Y) (g : Y.toScheme ⟶ U.toScheme), g ≫ U.str = Y.str ∧
    IsProjectiveHom g ∧ IsRAmpleOver Q.KΔ g ∧
    ∃ σ : FF Y ≃ₐ[k] FF X, IsBirContractionOver P Q π g σ ∧ DiscrepancyCompare P Q σ (· ≤ ·)

/-! ## The relative log canonical ring -/

/-- The sections of `𝒪_X(D)` on the set `W`: the rational functions `φ` with `D + div φ ≥ 0` at the prime divisors whose generic point is in `W`, and `0`. -/
def sectionsOn (D : Divisor ℤ X) (W : Set X.toScheme) : Set (FF X) :=
  {φ | φ = 0 ∨ ∀ P : PrimeDivisor X, P.1 ∈ W → 0 ≤ D P + ordAt φ P}

/-- The ring `⊕ₘ H⁰(W, 𝒪_X(⌊m D⌋))`, as the subring of `k(X)[t]` that the elements `φ tᵐ` with `φ ∈ H⁰(W, 𝒪_X(⌊m D⌋))` generate. -/
noncomputable def relativeRing (D : Divisor ℝ X) (W : Set X.toScheme) : Subring (Polynomial (FF X)) :=
  Subring.closure {p | ∃ (m : ℕ) (φ : FF X), φ ∈ sectionsOn (D.roundDown m) W ∧
    p = Polynomial.monomial m φ}

/-- The ring `R(π, D) = ⊕ₘ π_* 𝒪_X(⌊m D⌋)` is a finitely generated `𝒪_U`-algebra: over each affine open set `V` of `U` that meets the image of `π`, the ring `⊕ₘ H⁰(π⁻¹ V, 𝒪_X(⌊m D⌋))` is generated by the functions of `V` and finitely many elements. -/
def IsRelFG (D : Divisor ℝ X) {U : Scheme.{u}} (π : X.toScheme ⟶ U) : Prop :=
  ∀ V : U.Opens, IsAffineOpen V → ∀ hX : genericPoint X.toScheme ∈ π ⁻¹ᵁ V,
    ∃ S : Finset (Polynomial (FF X)), relativeRing D (π ⁻¹ᵁ V : Set X.toScheme) =
      Subring.closure (Set.range (fun s : Γ(U, V) =>
        Polynomial.C ((π.app V ≫ X.toScheme.presheaf.germ (π ⁻¹ᵁ V) _ hX).hom s)) ∪ (S : Set _))

end MinimalModel
