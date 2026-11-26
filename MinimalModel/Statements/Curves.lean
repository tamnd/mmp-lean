/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import MinimalModel.Statements.Basic

/-!
# Curves: extremal faces, rational curves and relative positivity

This file adds to `MinimalModel/Statements/Basic.lean` the vocabulary that the statements S01, S02, S06 and S09 of spec 06.2.2 use.

## The choices

* An extremal face of the cone of curves is a pointed subcone `F` of `NE(X)` such that `a + b ∈ F` with `a` and `b` in `NE(X)` gives `a ∈ F` and `b ∈ F` (KM98, Chapter 1; the `reader` role checks the number of the definition). It is `(K + Δ)`-negative when `K + Δ` is negative on each nonzero class of `F`, that is `F ∩ NE(X)_{K+Δ ≥ 0} = 0`.
* A curve is rational when its function field is `k(t)` for a transcendental `t`. By Lüroth's theorem this is the same as a normalization isomorphic to `ℙ¹`, because `k` is algebraically closed.
* The relative notions over a morphism `f : X → U` do not use `IntersectionData`. A structure `IntersectionData X` asks for the degree on every curve of `X`, and a curve that is not complete has no degree. So when `X` is not proper over `k`, there is no such structure. The relative notions use only the curves that `f` contracts. When `U` is of finite type over `k`, such a curve maps to a closed point and is complete. The intersection number of an `ℝ`-Cartier divisor with such a curve is read from a decomposition into Cartier divisors (`IsRIntersectionNumber`).
-/

universe u

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace MinimalModel

variable {k : Type u} [Field k] {X : NormalVariety k}

/-! ## Extremal faces -/

/-- An extremal face of the closed cone of curves `NE(X)` (KM98, Chapter 1): a pointed subcone `F ⊆ NE(X)` such that `a + b ∈ F`, with `a` and `b` in `NE(X)`, gives `a ∈ F` and `b ∈ F`. -/
structure ExtremalFace (I : IntersectionData X) where
  /-- The face, as a pointed cone. -/
  carrier : PointedCone ℝ (CurveSpace X)
  le : carrier ≤ I.coneOfCurves
  isFace : ∀ a b, a ∈ I.coneOfCurves → b ∈ I.coneOfCurves → a + b ∈ carrier →
    a ∈ carrier ∧ b ∈ carrier

/-- The face `F` is `D`-negative: `D · z < 0` for each nonzero class `z` of `F`. For `D = K + Δ` this is the condition `F ∩ NE(X)_{K+Δ ≥ 0} = 0` of KM98 Theorem 3.7. -/
def ExtremalFace.IsNegative {I : IntersectionData X} (F : ExtremalFace I) (D : RCartier X) : Prop :=
  ∀ z ∈ F.carrier, z ≠ 0 → z D < 0

/-- The morphism `f : X → Z` is the contraction of the face `F` of the model `A`: `Z` is a projective normal variety over `k`, `f` is a morphism over `k` with `f_* 𝒪_X = 𝒪_Z`, and `f` contracts a curve `C` exactly when the class of `C` is in `F`. -/
def IsContractionOfFace (A : PairModel k) (F : ExtremalFace A.I) (Z : NormalVariety k)
    (f : A.X.toScheme ⟶ Z.toScheme) : Prop :=
  f ≫ Z.str = A.X.str ∧ IsProjective Z ∧ IsContraction f ∧
    ∀ C : Curve A.X, IsContracted f C ↔ A.I.curveClass C ∈ F.carrier

/-! ## Rational curves -/

/-- The curve `C` is rational: its function field, the residue field at its generic point, is `k(t)` for an element `t` that is transcendental over `k`. -/
def Curve.IsRational (C : Curve X) : Prop :=
  letI : Algebra k (X.toScheme.residueField C.1) := (X.toResidueField C.1).toAlgebra
  ∃ t : X.toScheme.residueField C.1, Transcendental k t ∧ IntermediateField.adjoin k {t} = ⊤

/-! ## Relative positivity -/

/-- `x` is the intersection number `D · C` of an `ℝ`-divisor `D` with a curve `C`: `D = Σ rᵢ Eᵢ` with Cartier divisors `Eᵢ`, and `x = Σ rᵢ (Eᵢ · C)`. The degree `Eᵢ · C` is the one of `IsIntersectionNumber`. It exists when `C` is complete. -/
def IsRIntersectionNumber (D : Divisor ℝ X) (C : Curve X) (x : ℝ) : Prop :=
  ∃ (N : ℕ) (r : Fin N → ℝ) (E : Fin N → Divisor ℤ X) (d : Fin N → ℤ),
    (∀ i, IsCartier (E i)) ∧ (∀ i, IsIntersectionNumber (E i) C (d i)) ∧
    D = ∑ i, r i • (E i).toReal ∧ x = ∑ i, r i * (d i : ℝ)

/-- `D` is numerically trivial over `f`, written `D ≡_f 0`: `D · C = 0` for each curve `C` that `f` contracts. -/
def IsNumTrivialRel {Z : Scheme.{u}} (D : Divisor ℝ X) (f : X.toScheme ⟶ Z) : Prop :=
  ∀ C, IsContracted f C → ∀ x, IsRIntersectionNumber D C x → x = 0

/-- `D` is nef over `f`: `D · C ≥ 0` for each curve `C` that `f` contracts. This is `IsNefOver` without a structure `IntersectionData`, so that `X` need not be proper over `k`. -/
def IsNefRel {Z : Scheme.{u}} (D : Divisor ℝ X) (f : X.toScheme ⟶ Z) : Prop :=
  ∀ C, IsContracted f C → ∀ x, IsRIntersectionNumber D C x → 0 ≤ x

/-- `D` is big over `f`: `D` is `ℝ`-linearly equivalent to the sum of an `f`-ample divisor and an effective divisor. For a projective `f` this is the relative Kodaira lemma, up to the pullback of a divisor of the base. Such a pullback is numerically trivial over `f`. The statement S02 uses this notion only up to numerical equivalence over `f`, so the pullback makes no difference there. -/
def IsBigRel {Z : Scheme.{u}} (D : Divisor ℝ X) (f : X.toScheme ⟶ Z) : Prop :=
  ∃ A E : Divisor ℝ X, IsRAmpleOver A f ∧ 0 ≤ E ∧ RLinEquiv D (A + E)

end MinimalModel

end
