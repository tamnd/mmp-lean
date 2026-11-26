/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import MinimalModel.Fidelity.PointPairs
import MinimalModel.Fidelity.AffineLinePairs
import MinimalModel.Statements.Foundations
import MinimalModel.Statements.Effective
import MinimalModel.Statements.Boundedness

/-!
# Fidelity: the point and the affine line for S01, S09, S52 and S57

Checks F2 and F3 of spec 06.3 for some statements of milestone S2.

* F2 for S01: the point `Spec k` is projective, and the two sides of Kleiman's criterion hold on it.
* F3 for S09: a variety with no curves has no extremal ray, so S09 says nothing on the point.
* F3 for the enc pairs of S52: no pair on the point or on a variety of dimension one is enc. The global mld of `(Spec k, 0)` is `0`, the value of `sInf ∅` in `ℝ`.
* F3 for S57: the conclusion of effective non-vanishing holds for each divisor on the point, so the point is no counterexample.

There is no F2 for S02 and S06 here. Their hypotheses need a curve or a morphism with a cohomology computation, which are not cheap.
-/

universe u

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace MinimalModel

section General

variable {k : Type u} [Field k] {X : NormalVariety k}

/-- When there are no prime divisors, any two `ℝ`-divisors are `ℝ`-linearly equivalent. -/
theorem rLinEquiv_of_isEmpty [IsEmpty (PrimeDivisor X)] (D D' : Divisor ℝ X) : RLinEquiv D D' := by
  rw [RLinEquiv, Subsingleton.elim (D - D') 0]
  exact Submodule.zero_mem _

/-- On a projective variety with no prime divisors, each `ℝ`-divisor is ample. -/
theorem isAmple_of_isEmpty [IsEmpty (PrimeDivisor X)] (hX : IsProjective X) (D : Divisor ℝ X) :
    IsAmple D := by
  obtain ⟨-, A, hA⟩ := hX
  exact ⟨1, fun _ => 1, fun _ => A, one_pos, fun _ => one_pos, fun _ => hA, rLinEquiv_of_isEmpty _ _⟩

/-- When there are no curves, the cone of curves is zero. -/
theorem IntersectionData.eq_zero_of_mem_coneOfCurves_of_isEmpty [IsEmpty (Curve X)]
    (I : IntersectionData X) {z : CurveSpace X} (hz : z ∈ I.coneOfCurves) : z = 0 := by
  have hr : Set.range I.curveClass = ∅ := Set.range_eq_empty _
  have hs : (Submodule.span (Nonneg ℝ) (Set.range I.curveClass) : Set (CurveSpace X)) = {0} := by
    rw [hr, Submodule.span_empty]
    rfl
  have hz' : z ∈ closure (Submodule.span (Nonneg ℝ) (Set.range I.curveClass) : Set (CurveSpace X)) :=
    hz
  rw [hs, closure_singleton] at hz'
  exact hz'

/-- F3 for S09: when there are no curves, there is no extremal ray. -/
theorem isEmpty_extremalRay [IsEmpty (Curve X)] (I : IntersectionData X) : IsEmpty (ExtremalRay I) :=
  ⟨fun R => R.ne_zero (I.eq_zero_of_mem_coneOfCurves_of_isEmpty R.mem)⟩

/-- F3 for S52: no pair on a variety of dimension one is enc, because no divisorial valuation with a log discrepancy is exceptional. -/
theorem not_isEnc_of_dim_eq_one (hX : X.dim = 1) (P : Pair X) : ¬ IsEnc P := by
  rintro ⟨-, v, ⟨hv, he, A, hA, -⟩, -⟩
  exact hA.not_isExceptional_of_dim_eq_one hX hv he

end General

variable (k : Type u) [Field k]

/-- F2 for S01: the point is projective, and for each `ℝ`-divisor on it both sides of Kleiman's criterion hold. -/
theorem pointVariety_kleiman (I : IntersectionData (pointVariety k)) (D : Divisor ℝ (pointVariety k))
    (hD : IsRCartier D) :
    IsProjective (pointVariety k) ∧ IsAmple D ∧ ∀ z ∈ I.coneOfCurves, z ≠ 0 → 0 < z ⟨D, hD⟩ :=
  ⟨pointVariety_isProjective k, isAmple_of_isEmpty (pointVariety_isProjective k) D,
    fun _z hz h0 => absurd (I.eq_zero_of_mem_coneOfCurves_of_isEmpty hz) h0⟩

/-- F3 for S52: the pair `(Spec k, 0)` is not enc, because the point has no divisorial valuation. -/
theorem pointPair_not_isEnc : ¬ IsEnc (pointPair k) := by
  rintro ⟨-, v, ⟨hv, -⟩, -⟩
  exact pointVariety_not_isDivisorial k v hv

/-- The global mld of `(Spec k, 0)` is `0`: there is no exceptional divisor, and `sInf ∅ = 0` in `ℝ`. -/
theorem pointPair_globalMld : globalMld (pointPair k) = 0 := by
  have h : ∀ v, ¬ IsDivisorial v := pointVariety_not_isDivisorial k
  simp [globalMld, h]

/-- F3 for S52: the pairs `(𝔸¹, c [0])` are not enc. -/
theorem affineLinePair_not_isEnc {c : ℝ} (hc : 0 ≤ c) : ¬ IsEnc (affineLinePair k c hc) :=
  not_isEnc_of_dim_eq_one (affineLine_dim k) _

/-- F3 for S57: each divisor on the point has a nonzero section, the constant `1`. So the point is no counterexample to effective non-vanishing. -/
theorem pointVariety_sections_ne_bot (D : Divisor ℤ (pointVariety k)) : sections D ≠ ⊥ := by
  intro h
  have h1 : (1 : FF (pointVariety k)) ∈ sections D :=
    Submodule.subset_span ⟨one_ne_zero, fun P => isEmptyElim P⟩
  rw [h, Submodule.mem_bot] at h1
  exact one_ne_zero h1

end MinimalModel

end
