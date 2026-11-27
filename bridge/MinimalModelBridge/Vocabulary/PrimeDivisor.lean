/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import MinimalModel.Statements.Basic
import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.GenericPoint

/-!
# Prime divisors and divisors

A prime divisor of `MinimalModel` is a point of coheight one. A prime divisor of AxiomMath/Stacks (`AlgebraicGeometry.PrimeDivisor`) is an integral closed subscheme of codimension one, given by its ideal sheaf. AxiomMath/MMP uses the second one: `MMP.Mori.PrimeDivisor X` is an abbreviation of `AlgebraicGeometry.PrimeDivisor X`, and `MMP.Mori.DivisorWithCoeffs R X` is an abbreviation of `MMP.Mori.PrimeDivisor X →₀ R`. So `MMP.Mori.Divisor`, `MMP.Mori.QDivisor` and `MMP.Mori.RDivisor` are the types `AlgebraicGeometry.PrimeDivisor X →₀ R` for `R = ℤ, ℚ, ℝ`.

The generic point is a bijection from the second kind to the first (Stacks, Tag 02RO), so the two kinds of divisors agree.

## Main definitions

* `MinimalModelBridge.primeDivisorEquiv`: the bijection between the prime divisors of `MinimalModel` and those of AxiomMath/Stacks. Its inverse is the generic point.
* `MinimalModelBridge.divisorEquiv`: the induced isomorphism of the groups of divisors with coefficients in `R`.

## Main results

* `MinimalModelBridge.divisorEquiv_apply`: the coefficient of the image of `D` at `Z` is the coefficient of `D` at the generic point of `Z`.
* `MinimalModelBridge.forall_divisorEquiv_iff`, `MinimalModelBridge.divisorEquiv_nonneg_iff`, `MinimalModelBridge.divisorEquiv_le_iff`: the conditions on the coefficients, such as the effectivity, or the bounds `Δ < 1` and `Δ ≤ 1` of the klt and lc pairs, are the same on both sides.

All the results hold in each universe.
-/

universe u

open Order

noncomputable section

namespace MinimalModelBridge

variable {k : Type u} [Field k] (X : MinimalModel.NormalVariety k)

/-- The prime divisors of `MinimalModel` are the prime divisors of AxiomMath/Stacks: a point of coheight one is the generic point of exactly one integral closed subscheme of codimension one. -/
def primeDivisorEquiv :
    MinimalModel.PrimeDivisor X ≃ AlgebraicGeometry.PrimeDivisor X.toScheme where
  toFun P := AlgebraicGeometry.PrimeDivisor.ofCoheightOne P.1 P.2
  invFun Z := (⟨Z.genericPoint, Z.coheight_genericPoint⟩ : {x : X.toScheme // coheight x = 1})
  left_inv P := Subtype.ext (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne P.1 P.2)
  right_inv Z := AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne Z.genericPoint
      Z.coheight_genericPoint)

/-- The prime divisor of AxiomMath/Stacks attached to `P` has the point `P` as its generic point. -/
@[simp]
theorem genericPoint_primeDivisorEquiv (P : MinimalModel.PrimeDivisor X) :
    (primeDivisorEquiv X P).genericPoint = P.1 :=
  AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne P.1 P.2

/-- The inverse of `primeDivisorEquiv` is the generic point. -/
@[simp]
theorem primeDivisorEquiv_symm_apply_val (Z : AlgebraicGeometry.PrimeDivisor X.toScheme) :
    ((primeDivisorEquiv X).symm Z).1 = Z.genericPoint :=
  rfl

variable (R : Type*) [AddCommMonoid R]

/-- The divisors with coefficients in `R` of `MinimalModel` are those of AxiomMath/Stacks and AxiomMath/MMP. For `R = ℤ, ℚ, ℝ` the target is `MMP.Mori.Divisor X.toScheme`, `MMP.Mori.QDivisor X.toScheme` and `MMP.Mori.RDivisor X.toScheme`. -/
def divisorEquiv :
    MinimalModel.Divisor R X ≃+ (AlgebraicGeometry.PrimeDivisor X.toScheme →₀ R) :=
  Finsupp.domCongr (primeDivisorEquiv X)

variable {X R}

/-- The coefficient of the image of `D` at `Z` is the coefficient of `D` at the generic point of `Z`. -/
theorem divisorEquiv_apply (D : MinimalModel.Divisor R X)
    (Z : AlgebraicGeometry.PrimeDivisor X.toScheme) :
    divisorEquiv X R D Z = D ((primeDivisorEquiv X).symm Z) :=
  rfl

/-- The coefficient of the image of `D` at the prime divisor attached to `P` is the coefficient of `D` at `P`. -/
@[simp]
theorem divisorEquiv_apply_primeDivisorEquiv (D : MinimalModel.Divisor R X)
    (P : MinimalModel.PrimeDivisor X) : divisorEquiv X R D (primeDivisorEquiv X P) = D P := by
  rw [divisorEquiv_apply, Equiv.symm_apply_apply]

/-- A condition on each coefficient holds for `D` exactly when it holds for its image. -/
theorem forall_divisorEquiv_iff (p : R → Prop) (D : MinimalModel.Divisor R X) :
    (∀ Z, p (divisorEquiv X R D Z)) ↔ ∀ P, p (D P) := by
  constructor
  · intro h P
    have hP := h (primeDivisorEquiv X P)
    rwa [divisorEquiv_apply_primeDivisorEquiv] at hP
  · intro h Z
    rw [divisorEquiv_apply]
    exact h _

/-- `D` is effective exactly when its image is effective. -/
theorem divisorEquiv_nonneg_iff [Preorder R] (D : MinimalModel.Divisor R X) :
    0 ≤ divisorEquiv X R D ↔ 0 ≤ D := by
  simp only [Finsupp.le_def, Finsupp.coe_zero, Pi.zero_apply]
  exact forall_divisorEquiv_iff (fun r => 0 ≤ r) D

/-- The order of the divisors is the same on both sides. -/
theorem divisorEquiv_le_iff [Preorder R] (D E : MinimalModel.Divisor R X) :
    divisorEquiv X R D ≤ divisorEquiv X R E ↔ D ≤ E := by
  simp only [Finsupp.le_def]
  constructor
  · intro h P
    have hP := h (primeDivisorEquiv X P)
    rwa [divisorEquiv_apply_primeDivisorEquiv, divisorEquiv_apply_primeDivisorEquiv] at hP
  · intro h Z
    rw [divisorEquiv_apply, divisorEquiv_apply]
    exact h _

end MinimalModelBridge
