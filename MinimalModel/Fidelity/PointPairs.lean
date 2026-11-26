/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import MinimalModel.Fidelity.Basic
import MinimalModel.Fidelity.Point

/-!
# Fidelity check F2: the classes of pairs and the programs on a point

This file continues `MinimalModel/Fidelity/Point.lean`. It shows that the model `(Spec k, 0)` is in each class of pairs of spec 06.1: klt, lc, terminal, canonical and dlt. It also shows that the conclusions of S04, S20 and S22 hold for this model, and that the model is minimal.

The function field of `Spec k` is `k`. A divisorial valuation must take the value `exp (-1)` on some element, and it is trivial on `k`, so `Spec k` has no divisorial valuation. Thus each condition on the log discrepancies holds with no valuation to check. A model with no curves has no extremal contraction, so it has no step of a program.

These instances show that the hypotheses of S04, S20 and S22 can hold together. They do not test the definitions in positive dimension.
-/

universe u

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace MinimalModel

section General

variable {k : Type u} [Field k]

/-- A model with no curves has no step of a program, because a step contracts a curve. -/
theorem not_isMMPStep_of_isEmpty {A B : PairModel k} (h : IsEmpty (Curve A.X)) : ¬ IsMMPStep A B :=
  fun ⟨s⟩ => let ⟨C, _⟩ := s.extremal; h.elim C

/-- A model with no curves has no infinite program. -/
theorem not_hasInfiniteProgram_of_isEmpty {A : PairModel k} (h : IsEmpty (Curve A.X)) :
    ¬ HasInfiniteProgram A := by
  rintro ⟨m, h0, hs⟩
  have h1 := hs 0
  rw [h0] at h1
  exact not_isMMPStep_of_isEmpty h h1

/-- A model with no curves has no infinite sequence of flips. -/
theorem not_hasInfiniteFlips_of_isEmpty {A : PairModel k} (h : IsEmpty (Curve A.X)) :
    ¬ HasInfiniteFlips A :=
  fun hf => not_hasInfiniteProgram_of_isEmpty h hf.hasInfiniteProgram

/-- On a model with no curves, `K + Δ` is nef, so the model is minimal. -/
theorem isMinimal_of_isEmpty {A : PairModel k} (h : IsEmpty (Curve A.X)) : IsMinimal A :=
  fun C => h.elim C

/-- On a model with no curves, the cone of curves is zero. -/
theorem eq_zero_of_mem_coneOfCurves {A : PairModel k} (h : IsEmpty (Curve A.X)) {z : CurveSpace A.X}
    (hz : z ∈ A.I.coneOfCurves) : z = 0 := by
  have hr : Set.range A.I.curveClass = ∅ := Set.range_eq_empty _
  have hs : (Submodule.span (Nonneg ℝ) (Set.range A.I.curveClass) : Set (CurveSpace A.X)) = {0} := by
    rw [hr, Submodule.span_empty]
    rfl
  have hz' : z ∈ closure (Submodule.span (Nonneg ℝ) (Set.range A.I.curveClass) : Set (CurveSpace A.X)) :=
    hz
  rw [hs, closure_singleton] at hz'
  exact hz'

/-- On a model with no curves, the cone theorem holds with no rays. -/
theorem coneDecomposition_of_isEmpty {A : PairModel k} (h : IsEmpty (Curve A.X)) : ConeDecomposition A := by
  refine ⟨PEmpty, inferInstance, fun i => i.elim, fun i => i.elim, fun z => ⟨fun hz => ?_, ?_⟩,
    fun i => i.elim, fun _ _ _ _ => ?_⟩
  · refine ⟨z, hz, ?_, ∅, fun _ => 0, fun _ => le_rfl, by simp⟩
    rw [eq_zero_of_mem_coneOfCurves h hz]
    exact le_rfl
  · rintro ⟨y, hy, -, s, t, -, rfl⟩
    have hs : s = ∅ := Finset.eq_empty_of_isEmpty s
    simpa [hs] using hy
  · exact Set.toFinite _

end General

section Point

variable (k : Type u) [Field k]

/-- The map from `k` to the function field of `Spec k` is onto. -/
theorem pointVariety_algebraMap_surjective :
    Function.Surjective (algebraMap k (FF (pointVariety k))) := by
  intro y
  let x : PrimeSpectrum k := genericPoint (pointVariety k).toScheme
  have : x.asIdeal.IsPrime := x.isPrime
  have hu : x.asIdeal.primeCompl ≤ IsUnit.submonoid k := fun c hc =>
    (IsUnit.mem_submonoid_iff c).mpr <| isUnit_iff_ne_zero.mpr fun h => hc (by rw [h]; exact x.asIdeal.zero_mem)
  let e := IsLocalization.atUnits k x.asIdeal.primeCompl (S := Localization.AtPrime x.asIdeal) hu
  obtain ⟨c, hc⟩ := e.surjective ((Spec.stalkIso (CommRingCat.of k) x).hom y)
  refine ⟨c, ?_⟩
  have h1 : (Spec.stalkIso (CommRingCat.of k) x).inv (algebraMap k _ c) =
      (Spec (CommRingCat.of k)).presheaf.germ ⊤ x trivial ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c) :=
    congrArg (fun f => f.hom c) (Spec.algebraMap_stalkIso_inv x)
  have h2 : algebraMap k (Localization.AtPrime x.asIdeal) c = e c := (e.commutes c).symm
  have h3 : algebraMap k (FF (pointVariety k)) c =
      (Spec (CommRingCat.of k)).presheaf.germ ⊤ x trivial ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c) := by
    change ((Spec (CommRingCat.of k)).presheaf.germ ⊤ x trivial).hom
      (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ Scheme.Hom.appTop (𝟙 _)).hom c) = _
    simp
  rw [h3, ← h1, h2, hc]
  exact (Spec.stalkIso (CommRingCat.of k) x).hom_inv_id_apply y

/-- `Spec k` has no divisorial valuation: each element of `k(X) = k` has the value `0` or `1`. -/
theorem pointVariety_not_isDivisorial (v : Valuation (FF (pointVariety k)) VZ) : ¬ IsDivisorial v := by
  rintro ⟨h1, ⟨π, hπ⟩, -⟩
  obtain ⟨c, rfl⟩ := pointVariety_algebraMap_surjective k π
  by_cases hc : c = 0
  · rw [hc, map_zero, map_zero] at hπ
    exact WithZero.zero_ne_coe hπ
  · rw [h1 c hc] at hπ
    have := WithZero.exp_eq_one.mp hπ.symm
    omega

/-- The pair `(Spec k, 0)` is klt. -/
theorem pointPair_isKlt : IsKlt (pointPair k) :=
  ⟨fun Q => isEmptyElim Q, fun v hv => absurd hv (pointVariety_not_isDivisorial k v)⟩

/-- The pair `(Spec k, 0)` is lc. -/
theorem pointPair_isLc : IsLc (pointPair k) := (pointPair_isKlt k).isLc

/-- The pair `(Spec k, 0)` is terminal. -/
theorem pointPair_isTerminal : IsTerminal (pointPair k) :=
  fun v hv => absurd hv (pointVariety_not_isDivisorial k v)

/-- The pair `(Spec k, 0)` is canonical. -/
theorem pointPair_isCanonical : IsCanonical (pointPair k) := (pointPair_isTerminal k).isCanonical

/-- The pair `(Spec k, 0)` is dlt, with the closed set `Z = Spec k`. -/
theorem pointPair_isDlt : IsDlt (pointPair k) :=
  ⟨pointPair_isLc k, Set.univ, isClosed_univ, fun x hx => absurd (Set.mem_univ x) hx,
    fun v hv => absurd hv (pointVariety_not_isDivisorial k v)⟩

/-- The boundary of `(Spec k, 0)` is rational. -/
theorem pointPair_isRationalBoundary : (pointPair k).IsRationalBoundary := fun Q => isEmptyElim Q

/-- F2 for S04: the model `(Spec k, 0)` is a projective klt pair, and the conclusion of the cone theorem holds for it. -/
theorem pointModel_coneDecomposition : IsKlt (pointModel k).P ∧ ConeDecomposition (pointModel k) :=
  ⟨pointPair_isKlt k, coneDecomposition_of_isEmpty (isEmpty_curve_of_subsingleton (X := pointVariety k))⟩

/-- F2 for S20 and S22: the model `(Spec k, 0)` is an lc pair with a rational boundary, and it has no infinite program and no infinite sequence of flips. -/
theorem pointModel_terminates :
    IsLc (pointModel k).P ∧ (pointModel k).P.IsRationalBoundary ∧
      ¬ HasInfiniteProgram (pointModel k) ∧ ¬ HasInfiniteFlips (pointModel k) :=
  ⟨pointPair_isLc k, pointPair_isRationalBoundary k,
    not_hasInfiniteProgram_of_isEmpty (isEmpty_curve_of_subsingleton (X := pointVariety k)),
    not_hasInfiniteFlips_of_isEmpty (isEmpty_curve_of_subsingleton (X := pointVariety k))⟩

/-- The model `(Spec k, 0)` is minimal: `K + Δ` is nef. -/
theorem pointModel_isMinimal : IsMinimal (pointModel k) :=
  isMinimal_of_isEmpty (isEmpty_curve_of_subsingleton (X := pointVariety k))

end Point

end MinimalModel
