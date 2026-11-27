/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import MinimalModel.Fidelity.PointPairs
import MinimalModel.Fidelity.Surfaces
import MinimalModel.Statements.GeneralizedPairs

/-!
# Fidelity checks F2 and F3 for the generalized pairs

Checks F2 and F3 of spec 06.3 for `GeneralizedPairs.lean`, used by S27.

* With the boundary `Δ` of a pair, the log discrepancy `LogDiscrepancyOfIs` is the log discrepancy `LogDiscrepancyIs` of the pair. So the generalized log discrepancy extends the one of `Basic.lean`.
* A generalized pair with `M_X = 0` gives a pair with the same canonical divisor and boundary.
* The pullback of the zero divisor is the zero divisor.
* F2: the point `Spec k` carries a generalized pair, with the nef part `0` on the model `Spec k`. It is lc, and its nef part is the same b-divisor as itself. So the types `NefPart X` and `GenPair X` are not empty, and the hypotheses `IsGenLc` and the conclusion `SameBDivisor` of S27 can hold.

The point has no flipping contraction, as it has no curves. These checks do not test the definitions in positive dimension.
-/

universe u

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace MinimalModel

section General

variable {k : Type u} [Field k] {X : NormalVariety k}

/-- With the boundary of a pair, `LogDiscrepancyOfIs` is the log discrepancy of the pair. -/
theorem logDiscrepancyOfIs_iff (P : Pair X) (v : Valuation (FF X) VZ) (A : ℝ) :
    LogDiscrepancyOfIs P.K P.Δ v A ↔ LogDiscrepancyIs P v A :=
  Iff.rfl

/-- A generalized pair with `M_X = 0` gives a pair, with the same canonical divisor and boundary. -/
def GenPair.toPair (G : GenPair X) (h : G.MX = 0) : Pair X where
  K := G.K
  Δ := G.B
  nonneg := G.nonneg
  rCartier := by
    have := G.rCartier
    rwa [h, add_zero] at this

/-- The pair of a generalized pair with `M_X = 0` has the log canonical divisor `K + B + M_X`. -/
theorem GenPair.toPair_KΔ (G : GenPair X) (h : G.MX = 0) : (G.toPair h).KΔ = G.KBM := by
  simp [Pair.KΔ, GenPair.KBM, GenPair.toPair, h]

/-- The pullback of the zero divisor is the zero divisor. -/
theorem isRPullback_zero {Y : NormalVariety k} (f : Y.toScheme ⟶ X.toScheme) (σ : FF X ≃ₐ[k] FF Y) :
    IsRPullback f σ 0 0 :=
  ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun i => i.elim0, by simp, by simp⟩

/-- A lc generalized pair has coefficients at most one. -/
theorem IsGenLc.coeff_le {G : GenPair X} (h : IsGenLc G) (Q : PrimeDivisor X) : G.B Q ≤ 1 :=
  h.1 Q

end General

section Point

variable (k : Type u) [Field k]

/-- The identity of `Spec k` is a birational model of `Spec k`. -/
theorem pointVariety_isBirModel_id :
    IsBirModel (X := pointVariety k) (Y := pointVariety k) (𝟙 _) (AlgEquiv.refl) :=
  ⟨Category.id_comp _, pointVariety_isProjective k, isBirationalHom_id _, rfl,
    fun _ _ _ _ => rfl⟩

/-- The nef part `0` on the model `Spec k` of `Spec k`. -/
def pointNefPart : NefPart (pointVariety k) where
  Y := pointVariety k
  f := 𝟙 _
  σ := AlgEquiv.refl
  isModel := pointVariety_isBirModel_id k
  M := 0
  rCartier := isRCartier_of_isEmpty _
  I := IntersectionData.ofIsEmpty
  nef := fun C => isEmptyElim C

/-- The generalized pair `(Spec k, 0, 0)`. -/
def pointGenPair : GenPair (pointVariety k) where
  K := pointCanonical k
  B := 0
  nonneg := le_rfl
  N := pointNefPart k
  MX := 0
  trace := fun Q => isEmptyElim Q
  rCartier := isRCartier_of_isEmpty _

/-- F2: the generalized pair `(Spec k, 0, 0)` is lc. -/
theorem pointGenPair_isGenLc : IsGenLc (pointGenPair k) :=
  ⟨fun Q => isEmptyElim Q, fun v hv => absurd hv (pointVariety_not_isDivisorial k v)⟩

/-- F2: the nef part of `(Spec k, 0, 0)` is the same b-divisor as itself, through the identity. -/
theorem pointNefPart_sameBDivisor :
    SameBDivisor (pointNefPart k) (pointNefPart k) AlgEquiv.refl :=
  ⟨pointVariety k, 𝟙 _, 𝟙 _, AlgEquiv.refl, AlgEquiv.refl, 0, pointVariety_isBirModel_id k,
    pointVariety_isBirModel_id k, AlgEquiv.ext fun _ => rfl, isRPullback_zero _ _,
    isRPullback_zero _ _⟩

/-- F2: the type of generalized pairs on `Spec k` is not empty. -/
theorem nonempty_genPair : Nonempty (GenPair (pointVariety k)) := ⟨pointGenPair k⟩

end Point

end MinimalModel
