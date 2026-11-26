/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import MinimalModel.Statements.Basic

/-!
# Family B: surfaces and 3-folds

The statements of family B of spec 06.2.2 that are planned at S0: Castelnuovo's contraction theorem, the cone theorem for smooth surfaces and the minimal model program for smooth surfaces. A surface here is a smooth projective variety of dimension 2 with the boundary 0.
-/

universe u

namespace MinimalModel

open AlgebraicGeometry CategoryTheory Order

variable (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]

/-- A smooth projective surface with the boundary 0. -/
def PairModel.IsSmoothSurface {k : Type u} [Field k] (A : PairModel k) : Prop :=
  A.X.IsSmooth ∧ A.X.dim = 2 ∧ A.P.Δ = 0

/-- S10, Castelnuovo's contraction theorem (Hartshorne V.5.7). Let `E` be a curve on a smooth projective surface `X` with `E² = -1` and `K · E = -1`. By adjunction, `E` is a smooth rational curve. Then there is a morphism `f : X → Y` to a smooth projective surface that maps `E` to a closed point `p` and is an isomorphism over `Y \ {p}`. -/
def Castelnuovo : Prop :=
  ∀ A : PairModel k, A.IsSmoothSurface →
    ∀ (E : PrimeDivisor A.X) (hE : height E.1 = 1),
      A.I.dot (Divisor.toReal (Finsupp.single E 1)) ⟨E.1, hE⟩ = -1 →
      A.I.dot A.P.KΔ ⟨E.1, hE⟩ = -1 →
      ∃ (Y : NormalVariety k) (f : A.X.toScheme ⟶ Y.toScheme), Y.IsSmooth ∧ Y.dim = 2 ∧
        IsProjective Y ∧ f ≫ Y.str = A.X.str ∧ IsProper f ∧
        ∃ (p : Y.toScheme) (hp : IsClosed ({p} : Set Y.toScheme)), f.base E.1 = p ∧
          IsIso (f ∣_ ⟨{p}ᶜ, hp.isOpen_compl⟩)

/-- S11, the cone theorem for smooth projective surfaces (Mori; KM98 Theorem 1.24 in dimension 2). This is the conclusion of S04 for a smooth projective surface with the boundary 0. -/
def SurfaceConeTheorem : Prop :=
  ∀ A : PairModel k, A.IsSmoothSurface → ConeDecomposition A

/-- S12, the minimal model program for smooth projective surfaces. Each smooth projective surface `X` has a birational morphism to a smooth projective surface `Y` such that `K_Y` is nef, or `Y` has a Mori fibre space structure (a ruled surface over a curve, or `ℙ²`). -/
def SurfaceMMP : Prop :=
  ∀ A : PairModel k, A.IsSmoothSurface →
    ∃ B : PairModel k, B.IsSmoothSurface ∧
      ∃ f : A.X.toScheme ⟶ B.X.toScheme, f ≫ B.X.str = A.X.str ∧ IsProper f ∧
        IsBirationalHom f ∧ (IsMinimal B ∨ IsMoriFibreSpace B)

end MinimalModel
