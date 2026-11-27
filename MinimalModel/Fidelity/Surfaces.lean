/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import MinimalModel.Fidelity.PointStatements
import MinimalModel.Statements.LowDim

/-!
# Fidelity: wrong variants of S10, S11, S12 and S33, and the point for S33

Checks F2 and F3 of spec 06.3 for the statements of milestone S0 on surfaces and on minimal models.

* F3 for S10: without the condition that `f` maps `E` to the point `p`, Castelnuovo's theorem is trivial. The identity of `X` and any closed point of `X` satisfy the conclusion.
* F3 for S11 and S04: without the condition `(K + Δ) · y ≥ 0` on the first summand, the conclusion of the cone theorem holds on each model, with no rays. So that condition carries the content of the theorem.
* F3 for S12: without the condition that the output is minimal or a Mori fibre space, the program for surfaces is trivial, with the identity of `X`. Without the map from `X`, it is trivial too, with the point as the output.
* F3 for S33: without the condition that `K_Y + Δ_Y` is nef, each lc pair is a minimal model of itself, so the existence of minimal models is trivial in each dimension.
* F2 for S33 in dimension 0: the model `(Spec k, 0)` satisfies the hypotheses of S33 with `n = 0`, and it is a minimal model of itself.

These checks show that each of the conditions named above carries weight in the statement. There is no F2 for S10, S11 and S12 here: an instance needs a smooth projective surface with its intersection numbers, which is not cheap. S11 is the conclusion of S04 on a smooth surface, and S04 has F2 on the point.
-/

universe u

open AlgebraicGeometry CategoryTheory Order

noncomputable section

namespace MinimalModel

variable (k : Type u) [Field k]

section General

variable {k}

/-- The identity of a scheme is birational. -/
theorem isBirationalHom_id (X : Scheme.{u}) [Nonempty X] : IsBirationalHom (𝟙 X) :=
  ⟨⊤, ⟨Classical.arbitrary X, trivial⟩, inferInstance⟩

/-- A normal variety has a closed point. -/
theorem NormalVariety.exists_isClosed_singleton (X : NormalVariety k) :
    ∃ p : X.toScheme, IsClosed ({p} : Set X.toScheme) := by
  obtain ⟨p, -, hp⟩ := IsClosed.exists_closed_singleton (X := X.toScheme) isClosed_univ Set.univ_nonempty
  exact ⟨p, hp⟩

end General

/-- S10 without the condition `f.base E.1 = p`: the morphism need not contract `E`. -/
def CastelnuovoNoPoint : Prop :=
  ∀ A : PairModel k, A.IsSmoothSurface →
    ∀ (E : PrimeDivisor A.X) (hE : height E.1 = 1),
      A.I.dot (Divisor.toReal (Finsupp.single E 1)) ⟨E.1, hE⟩ = -1 →
      A.I.dot A.P.KΔ ⟨E.1, hE⟩ = -1 →
      ∃ (Y : NormalVariety k) (f : A.X.toScheme ⟶ Y.toScheme), Y.IsSmooth ∧ Y.dim = 2 ∧
        IsProjective Y ∧ f ≫ Y.str = A.X.str ∧ IsProper f ∧
        ∃ (p : Y.toScheme) (hp : IsClosed ({p} : Set Y.toScheme)),
          IsIso (f ∣_ ⟨{p}ᶜ, hp.isOpen_compl⟩)

/-- F3 for S10: the variant without `f.base E.1 = p` holds, with the identity of `X`. -/
theorem castelnuovoNoPoint : CastelnuovoNoPoint k := by
  intro A hA _ _ _ _
  obtain ⟨p, hp⟩ := A.X.exists_isClosed_singleton
  exact ⟨A.X, 𝟙 _, hA.1, hA.2.1, A.projective, Category.id_comp _, inferInstance, p, hp, inferInstance⟩

variable {k} in
/-- The conclusion of the cone theorem without the condition `0 ≤ y · (K + Δ)` on the first summand. -/
def ConeDecompositionNoNonneg (A : PairModel k) : Prop :=
  ∃ (ι : Type u) (_ : Countable ι) (C : ι → Curve A.X),
    (∀ i, A.I.dot A.P.KΔ (C i) < 0) ∧
    (∀ z, z ∈ A.I.coneOfCurves ↔ ∃ y ∈ A.I.coneOfCurves,
      ∃ (s : Finset ι) (t : ι → ℝ), (∀ i, 0 ≤ t i) ∧ z = y + ∑ i ∈ s, t i • A.I.curveClass (C i)) ∧
    (∀ i, ∃ R : ExtremalRay A.I, ray R.generator = ray (A.I.curveClass (C i))) ∧
    ∀ H : Divisor ℝ A.X, IsAmple H → ∀ ε : ℝ, 0 < ε →
      ((fun i => ray (A.I.curveClass (C i))) '' {i | A.I.dot (A.P.KΔ + ε • H) (C i) < 0}).Finite

variable {k} in
/-- The variant without the condition on the first summand holds on each model, with no rays. -/
theorem coneDecompositionNoNonneg (A : PairModel k) : ConeDecompositionNoNonneg A := by
  refine ⟨PEmpty, inferInstance, fun i => i.elim, fun i => i.elim, fun z => ⟨fun hz => ?_, ?_⟩,
    fun i => i.elim, fun _ _ _ _ => Set.toFinite _⟩
  · exact ⟨z, hz, ∅, fun _ => 0, fun _ => le_rfl, by simp⟩
  · rintro ⟨y, hy, s, t, -, rfl⟩
    have hs : s = ∅ := Finset.eq_empty_of_isEmpty s
    simpa [hs] using hy

/-- S11 with the conclusion `ConeDecompositionNoNonneg`. -/
def SurfaceConeTheoremNoNonneg : Prop :=
  ∀ A : PairModel k, A.IsSmoothSurface → ConeDecompositionNoNonneg A

/-- F3 for S11: the variant without the condition on the first summand holds, with no rays. -/
theorem surfaceConeTheoremNoNonneg : SurfaceConeTheoremNoNonneg k := fun A _ => coneDecompositionNoNonneg A

/-- S12 without the condition `IsMinimal B ∨ IsMoriFibreSpace B` on the output. -/
def SurfaceMMPNoOutput : Prop :=
  ∀ A : PairModel k, A.IsSmoothSurface →
    ∃ B : PairModel k, B.IsSmoothSurface ∧
      ∃ f : A.X.toScheme ⟶ B.X.toScheme, f ≫ B.X.str = A.X.str ∧ IsProper f ∧ IsBirationalHom f

/-- F3 for S12: the variant without the condition on the output holds, with `B = A` and the identity. -/
theorem surfaceMMPNoOutput : SurfaceMMPNoOutput k := fun A hA =>
  ⟨A, hA, 𝟙 _, Category.id_comp _, inferInstance, isBirationalHom_id _⟩

/-- S12 without the map from `X` and without the condition that the output is a surface. -/
def SurfaceMMPNoMap : Prop :=
  ∀ A : PairModel k, A.IsSmoothSurface → ∃ B : PairModel k, IsMinimal B ∨ IsMoriFibreSpace B

/-- F3 for S12: the variant without the map holds, with the point as the output. -/
theorem surfaceMMPNoMap : SurfaceMMPNoMap k := fun _ _ => ⟨pointModel k, Or.inl (pointModel_isMinimal k)⟩

/-- A minimal model in the sense of `IsMinimalModel`, without the condition that `K_Y + Δ_Y` is nef. -/
def IsMinimalModelNoNef (A B : PairModel k) : Prop :=
  IsLc B.P ∧ ∃ σ : FF B.X ≃ₐ[k] FF A.X,
    (∀ Q : PrimeDivisor B.X, ∃ P : PrimeDivisor A.X, SameDivisor σ P Q ∧ B.P.Δ Q = A.P.Δ P) ∧
    ∀ P : PrimeDivisor A.X, (∀ Q, ¬ SameDivisor σ P Q) →
      ∀ v : Valuation (FF A.X) VZ, IsDivisorial v → IsCentre v P.1 →
        ∀ a b, LogDiscrepancyIs A.P v a → LogDiscrepancyIs B.P (v.comap σ.toRingHom) b → a < b

/-- S33 without the condition that `K_Y + Δ_Y` is nef. -/
def MinimalModelConjNoNef (n : ℕ) : Prop :=
  ∀ A : PairModel k, A.X.dim = n → IsLc A.P → IsPseudoEffective A.P.KΔ → ∃ B, IsMinimalModelNoNef k A B

/-- Each prime divisor is the same divisor as itself under the identity of the function field. -/
theorem sameDivisor_refl {X : NormalVariety k} (P : PrimeDivisor X) :
    SameDivisor (AlgEquiv.refl : FF X ≃ₐ[k] FF X) P P :=
  fun _ _ => rfl

/-- F3 for S33: the variant without the nef condition holds in each dimension, with `B = A`. -/
theorem minimalModelConjNoNef (n : ℕ) : MinimalModelConjNoNef k n := fun A _ hA _ =>
  ⟨A, hA, AlgEquiv.refl, fun Q => ⟨Q, sameDivisor_refl k Q, rfl⟩,
    fun P h => absurd (sameDivisor_refl k P) (h P)⟩

/-- `K` of the point is pseudo-effective: each divisor on the point is ample and big. -/
theorem pointPair_isPseudoEffective : IsPseudoEffective (pointPair k).KΔ :=
  ⟨0, isAmple_of_isEmpty (pointVariety_isProjective k) 0, fun _ _ =>
    ⟨0, 0, isAmple_of_isEmpty (pointVariety_isProjective k) 0, le_rfl, rLinEquiv_of_isEmpty _ _⟩⟩

/-- The model `(Spec k, 0)` is a minimal model of itself. -/
theorem pointModel_isMinimalModel : IsMinimalModel (pointModel k) (pointModel k) :=
  ⟨pointPair_isLc k, pointModel_isMinimal k, AlgEquiv.refl,
    fun Q => (IsEmpty.false (α := PrimeDivisor (pointVariety k)) Q).elim,
    fun P => (IsEmpty.false (α := PrimeDivisor (pointVariety k)) P).elim⟩

/-- F2 for S33 in dimension 0: `(Spec k, 0)` satisfies the hypotheses of S33 with `n = 0`, and it has a minimal model, itself. -/
theorem pointModel_minimalModelConj :
    (pointModel k).X.dim = 0 ∧ IsLc (pointModel k).P ∧ IsPseudoEffective (pointModel k).P.KΔ ∧
      ∃ B, IsMinimalModel (pointModel k) B :=
  ⟨pointVariety_dim k, pointPair_isLc k, pointPair_isPseudoEffective k,
    pointModel k, pointModel_isMinimalModel k⟩

end MinimalModel

end
