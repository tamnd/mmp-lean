/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import MinimalModel.Statements.Basic

/-!
# Family B: surfaces and 3-folds

The statements of family B of spec 06.2.2 that are planned at S0 and S1. At S0: Castelnuovo's contraction theorem, the cone theorem for smooth surfaces and the minimal model program for smooth surfaces. A smooth surface there is a smooth projective variety of dimension 2 with the boundary 0. At S1: the program for lc surface pairs, and the flips, the termination and the program for 3-folds. At S2: abundance for lc surfaces and for lc 3-folds.
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

/-- S13, the minimal model program for lc surface pairs (Fujino 2012, minimal model theory for log surfaces). Let `(X, Δ)` be a projective lc pair of dimension 2. Then each program from `(X, Δ)` runs and ends: each sequence of steps is finite, and each finite program extends to a program that ends with a minimal model or a Mori fibre space. A surface has no small contraction, so each step is a divisorial contraction. -/
def LcSurfaceMMP : Prop :=
  ∀ A : PairModel k, A.X.dim = 2 → IsLc A.P → EveryProgramEnds A

/-- S14, abundance for lc surface pairs (Fujino, Minimal model theory for log surfaces, Publ. RIMS 48 (2012), Theorem 8.1). Let `(X, Δ)` be a projective lc pair of dimension 2 with a boundary `Δ` with real coefficients. If `K + Δ` is nef, then it is semiample. This is `Abundance 2` of family E, written out so that this file does not depend on family E. -/
def SurfaceAbundance : Prop :=
  ∀ A : PairModel k, A.X.dim = 2 → IsLc A.P → IsNef A.I A.P.KΔ → IsSemiample A.P.KΔ

/-- S15, the existence of 3-fold klt flips (Mori 1988; Shokurov; KM98 Chapter 6). Let `(X, Δ)` be a projective `ℚ`-factorial klt pair of dimension 3, and let `f : X → Z` be a flipping contraction: a small contraction of relative Picard number one with `-(K + Δ)` ample over `Z`. Then the flip `g : X⁺ → Z` exists. This is S30 in dimension 3, with the hypothesis of `ℚ`-factoriality of the source. -/
def ThreefoldFlips : Prop :=
  ∀ A : PairModel k, A.X.dim = 3 → IsQFactorial A.X → IsKlt A.P →
    ∀ (Z : NormalVariety k) (f : A.X.toScheme ⟶ Z.toScheme),
    f ≫ Z.str = A.X.str → IsContraction f → IsSmallHom f → IsExtremalContraction A.I f →
    IsRAmpleOver (-A.P.KΔ) f →
    ∃ (B : PairModel k) (g : B.X.toScheme ⟶ Z.toScheme), g ≫ Z.str = B.X.str ∧
      IsContraction g ∧ IsSmallHom g ∧ IsRAmpleOver B.P.KΔ g ∧ IsStrictTransform A B f g

/-- S16, the termination of 3-fold lc flips, `T(3)` (Shokurov; Kawamata 1992). For each projective lc pair of dimension 3, each sequence of `(K + Δ)`-flips is finite. This is the statement `Termination 3` of family C, written out so that this file does not depend on family C. -/
def ThreefoldTermination : Prop :=
  ∀ A : PairModel k, A.X.dim = 3 → IsLc A.P → ¬ HasInfiniteFlips A

/-- S17, abundance for lc 3-folds (Miyaoka 1988 and Kawamata 1992 for terminal 3-folds; Keel, Matsuki and McKernan, Log abundance theorem for threefolds, Duke Math. J. 75 (1994), Theorem 1.1, for lc pairs). Let `(X, Δ)` be a projective lc pair of dimension 3 with a boundary `Δ` with rational coefficients. If `K + Δ` is nef, then it is semiample. The source states the theorem for `ℚ`-divisors, so the statement asks that the coefficients are rational. The case of real coefficients follows by the usual reduction to rational boundaries (Shokurov polytopes), which is not part of the source. -/
def ThreefoldAbundance : Prop :=
  ∀ A : PairModel k, A.X.dim = 3 → IsLc A.P → A.P.IsRationalBoundary → IsNef A.I A.P.KΔ →
    IsSemiample A.P.KΔ

/-- S18, the minimal model program for lc 3-folds (AxiomMath/MMP `projectiveLowerLogMMP_three`). Let `(X, Δ)` be a projective lc pair of dimension 3. Then each program from `(X, Δ)` runs and ends: each sequence of steps is finite, and each finite program extends to a program that ends with a minimal model or a Mori fibre space. The proof in the literature uses the existence of lc flips in dimension 3, the termination `T(3)` (S16), and the cone and contraction theorems for lc pairs (Fujino). -/
def ThreefoldLcMMP : Prop :=
  ∀ A : PairModel k, A.X.dim = 3 → IsLc A.P → EveryProgramEnds A

end MinimalModel
