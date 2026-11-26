/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import MinimalModel.Statements.Basic

/-!
# Fidelity check F2: a model on a point

Check F2 of spec 06.3 asks for one instance of each hypothesis structure, so that no statement is true only because its hypotheses can never hold. This file gives the first instance: the point `Spec k` as a projective normal variety, with a pair and with intersection data. So the types `NormalVariety k`, `Pair X`, `IntersectionData X` and `PairModel k` are not empty.

The point has no prime divisors and no curves. Thus each divisor is zero, each divisor is Cartier, and the intersection data is empty. The canonical divisor is the divisor of a nonzero element of `⋀^0`, because the dimension is zero.

This instance does not test the meaning of the definitions in positive dimension. The instances on the projective line and on toric varieties come in later milestones.
-/

universe u

open AlgebraicGeometry CategoryTheory Order

noncomputable section

namespace MinimalModel

section General

variable {k : Type u} [Field k] {X : NormalVariety k}

/-- On a space with one point, no point has coheight one. -/
theorem isEmpty_primeDivisor_of_subsingleton [Subsingleton X.toScheme] : IsEmpty (PrimeDivisor X) :=
  ⟨fun P => by
    have h0 : coheight P.1 = 0 := Order.coheight_eq_zero.mpr fun b _ => (Subsingleton.elim b P.1).le
    have h1 := P.2
    rw [h0] at h1
    exact zero_ne_one h1⟩

/-- On a space with one point, no point has height one. -/
theorem isEmpty_curve_of_subsingleton [Subsingleton X.toScheme] : IsEmpty (Curve X) :=
  ⟨fun C => by
    have h0 : height C.1 = 0 := Order.height_eq_zero.mpr fun b _ => (Subsingleton.elim C.1 b).le
    have h1 := C.2
    rw [h0] at h1
    exact zero_ne_one h1⟩

/-- When there are no prime divisors, each divisor is Cartier. -/
theorem isCartier_of_isEmpty [IsEmpty (PrimeDivisor X)] (D : Divisor ℤ X) : IsCartier D :=
  fun _ => ⟨⊤, by simp, 1, ⟨one_ne_zero, fun P => isEmptyElim P⟩⟩

/-- When there are no prime divisors, each `ℝ`-divisor is `ℝ`-Cartier. -/
theorem isRCartier_of_isEmpty [IsEmpty (PrimeDivisor X)] (D : Divisor ℝ X) : IsRCartier D := by
  rw [Subsingleton.elim D 0]
  exact Submodule.zero_mem _

/-- When there are no prime divisors, the zero divisor is ample on each affine open set. -/
theorem isAmpleOn_zero_of_isEmpty [IsEmpty (PrimeDivisor X)] (W : X.toScheme.Opens)
    (hW : IsAffineOpen W) : IsAmpleOn (0 : Divisor ℤ X) W :=
  ⟨isCartier_of_isEmpty 0, fun _x hx => ⟨1, one_pos, 1, 0, ⟨one_ne_zero, fun P => isEmptyElim P⟩,
    fun P => isEmptyElim P, ⟨hx, fun P => isEmptyElim P⟩, W, hW,
    Set.ext fun _ => ⟨fun h => ⟨h, fun P => isEmptyElim P⟩, fun h => h.1⟩⟩⟩

/-- When there are no curves, the intersection data is empty. -/
def IntersectionData.ofIsEmpty [IsEmpty (Curve X)] : IntersectionData X where
  dot _ _ := 0
  dot_cartier _ _ C := isEmptyElim C
  dot_add _ _ _ _ C := isEmptyElim C
  dot_smul _ _ _ C := isEmptyElim C
  finiteDim := by
    rw [Set.range_eq_empty, Submodule.span_empty]
    infer_instance

end General

section Point

variable (k : Type u) [Field k]

/-- The stalks of `Spec k` are integrally closed: each stalk is isomorphic to `k`. -/
theorem isNormalScheme_spec : IsNormalScheme (Spec (CommRingCat.of k)) := by
  refine ⟨fun x => ?_⟩
  have : x.asIdeal.IsPrime := x.isPrime
  have hu : x.asIdeal.primeCompl ≤ IsUnit.submonoid k := fun y hy =>
    (IsUnit.mem_submonoid_iff y).mpr <| isUnit_iff_ne_zero.mpr fun h => hy (by rw [h]; exact x.asIdeal.zero_mem)
  let e₁ : k ≃+* Localization.AtPrime x.asIdeal :=
    (IsLocalization.atUnits k x.asIdeal.primeCompl hu).toRingEquiv
  let e₂ : Localization.AtPrime x.asIdeal ≃+* (Spec (CommRingCat.of k)).presheaf.stalk x :=
    (Spec.stalkIso (CommRingCat.of k) x).symm.commRingCatIsoToRingEquiv
  exact IsIntegrallyClosed.of_equiv (e₁.trans e₂)

/-- The point `Spec k` as a normal variety over `k`. -/
def pointVariety : NormalVariety k where
  toScheme := Spec (CommRingCat.of k)
  str := 𝟙 _
  isNormal := isNormalScheme_spec k

instance : Subsingleton (pointVariety k).toScheme :=
  (inferInstance : Subsingleton (Spec (CommRingCat.of k)))

instance : IsEmpty (PrimeDivisor (pointVariety k)) := isEmpty_primeDivisor_of_subsingleton

instance : IsEmpty (Curve (pointVariety k)) := isEmpty_curve_of_subsingleton

/-- The point has dimension zero. -/
theorem pointVariety_dim : (pointVariety k).dim = 0 := by
  have h : topologicalKrullDim (PrimeSpectrum k) = 0 :=
    (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim k).trans (ringKrullDim_eq_zero_of_field k)
  unfold NormalVariety.dim
  change ENat.toNat (WithBot.unbotD 0 (topologicalKrullDim (PrimeSpectrum k))) = 0
  rw [h]
  rfl

instance : Nontrivial (TopForm (pointVariety k)) := by
  unfold TopForm
  rw [pointVariety_dim]
  exact (exteriorPower.zeroEquiv _ _).symm.injective.nontrivial

/-- A nonzero top form on the point. -/
def pointForm : TopForm (pointVariety k) := Classical.choose (exists_ne (0 : TopForm (pointVariety k)))

theorem pointForm_ne_zero : pointForm k ≠ 0 := Classical.choose_spec (exists_ne _)

/-- The canonical divisor of the point: the zero divisor, as the divisor of a nonzero top form. -/
def pointCanonical : CanonicalDivisor (pointVariety k) :=
  ⟨0, pointForm k, ⟨pointForm_ne_zero k, fun P => isEmptyElim P⟩⟩

/-- The pair `(Spec k, 0)`. -/
def pointPair : Pair (pointVariety k) where
  K := pointCanonical k
  Δ := 0
  nonneg := le_rfl
  rCartier := isRCartier_of_isEmpty _

/-- The point is projective over `k`: the identity is proper, and the zero divisor is ample. -/
theorem pointVariety_isProjective : IsProjective (pointVariety k) := by
  refine ⟨?_, 0, isCartier_of_isEmpty 0, fun V hV => isAmpleOn_zero_of_isEmpty _ hV⟩
  change IsProper (𝟙 (Spec (CommRingCat.of k)))
  infer_instance

/-- The model `(Spec k, 0)` with its empty intersection data. -/
def pointModel : PairModel k where
  X := pointVariety k
  P := pointPair k
  I := IntersectionData.ofIsEmpty
  projective := pointVariety_isProjective k

/-- F2: the type of pair models is not empty. -/
theorem nonempty_pairModel : Nonempty (PairModel k) := ⟨pointModel k⟩

end Point

end MinimalModel
