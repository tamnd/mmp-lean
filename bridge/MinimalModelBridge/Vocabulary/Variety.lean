/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import MinimalModel.Statements.Basic
import StacksFrontier.AlgebraicGeometry.Properties.Normal
import StacksFrontier.AlgebraicGeometry.Variety.Defs.Basic

/-!
# Varieties and normal schemes

This file compares the varieties of `MinimalModel` with the varieties of AxiomMath/Stacks, which AxiomMath/MMP uses (`MMP.Mori.IsVariety` is an abbreviation of `AlgebraicGeometry.IsVariety`, and `MMP.Mori.IsNormalVariety k f` is `IsVariety k f ∧ IsNormal X`).

## Main results

* `MinimalModelBridge.isVariety_iff`: the class `MinimalModel.IsVariety` is the class `AlgebraicGeometry.IsVariety` of AxiomMath/Stacks. The two differ only in the form of the compactness: `MinimalModel` asks that the space be quasi-compact, AxiomMath/Stacks that the structure morphism be quasi-compact. Over `Spec k` the two agree.
* `MinimalModelBridge.isNormalScheme_iff_isNormal`: on an integral scheme, `MinimalModel.IsNormalScheme` is the class `AlgebraicGeometry.IsNormal` of AxiomMath/Stacks. The class of AxiomMath/Stacks also asks that each stalk be a domain, which holds on an integral scheme.
* `MinimalModelBridge.NormalVariety.isVariety` and `MinimalModelBridge.NormalVariety.isNormal`: a `MinimalModel.NormalVariety` is a normal variety in the sense of AxiomMath/MMP.
* `MinimalModelBridge.NormalVariety.ofIsVariety`: conversely, a normal variety in the sense of AxiomMath/MMP is a `MinimalModel.NormalVariety`. The field `isLocallyNoetherian` holds because a scheme of finite type over a field is locally Noetherian.

All the results hold in each universe.
-/

universe u

open AlgebraicGeometry

namespace MinimalModelBridge

variable {k : Type u} [Field k]

/-- Over `Spec k`, a morphism is quasi-compact exactly when its source is quasi-compact. -/
theorem quasiCompact_iff_compactSpace_of_field {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) :
    QuasiCompact f ↔ CompactSpace X :=
  quasiCompact_iff_compactSpace f

/-- The varieties of `MinimalModel` are the varieties of AxiomMath/Stacks. -/
theorem isVariety_iff {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) :
    MinimalModel.IsVariety X f ↔ AlgebraicGeometry.IsVariety k f := by
  constructor
  · intro h
    have := h.integral
    have := h.separated
    have := h.finiteType
    have := h.compact
    have : QuasiCompact f := (quasiCompact_iff_compactSpace_of_field f).mpr h.compact
    exact ⟨⟩
  · intro h
    exact ⟨h.toIsIntegral, h.toIsSeparated, h.toLocallyOfFiniteType,
      (quasiCompact_iff_compactSpace_of_field f).mp h.toQuasiCompact⟩

/-- A normal scheme of AxiomMath/Stacks is normal in the sense of `MinimalModel`. -/
theorem isNormalScheme_of_isNormal (X : Scheme.{u}) [h : IsNormal X] :
    MinimalModel.IsNormalScheme X :=
  ⟨h.stalk_normal⟩

/-- An integral scheme that is normal in the sense of `MinimalModel` is normal in the sense of AxiomMath/Stacks. -/
theorem isNormal_of_isNormalScheme (X : Scheme.{u}) [IsIntegral X]
    [h : MinimalModel.IsNormalScheme X] : IsNormal X where
  stalk_isDomain _ := inferInstance
  stalk_normal := h.isIntegrallyClosed_stalk

/-- On an integral scheme the two classes of normal schemes agree. -/
theorem isNormalScheme_iff_isNormal (X : Scheme.{u}) [IsIntegral X] :
    MinimalModel.IsNormalScheme X ↔ IsNormal X :=
  ⟨fun _ => isNormal_of_isNormalScheme X, fun _ => isNormalScheme_of_isNormal X⟩

namespace NormalVariety

variable (X : MinimalModel.NormalVariety k)

/-- The structure morphism of a normal variety of `MinimalModel` makes it a variety in the sense of AxiomMath/Stacks. -/
instance isVariety : AlgebraicGeometry.IsVariety k X.str :=
  (isVariety_iff X.str).mp ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- A normal variety of `MinimalModel` is a normal scheme in the sense of AxiomMath/Stacks. -/
instance isNormal : IsNormal X.toScheme :=
  isNormal_of_isNormalScheme X.toScheme

/-- A normal variety of `MinimalModel` is a normal variety in the sense of AxiomMath/MMP: this is the body of `MMP.Mori.IsNormalVariety k X.str`. -/
theorem isVariety_and_isNormal : AlgebraicGeometry.IsVariety k X.str ∧ IsNormal X.toScheme :=
  ⟨inferInstance, inferInstance⟩

/-- A normal variety in the sense of AxiomMath/MMP, as a normal variety of `MinimalModel`. -/
noncomputable def ofIsVariety {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of k))
    (hf : AlgebraicGeometry.IsVariety k f) (hY : IsNormal Y) : MinimalModel.NormalVariety k :=
  haveI := hf.toIsIntegral
  haveI := hf.toIsSeparated
  haveI := hf.toLocallyOfFiniteType
  haveI := hf.toQuasiCompact
  { toScheme := Y
    str := f
    isIntegral := inferInstance
    isSeparated := inferInstance
    locallyOfFiniteType := inferInstance
    compactSpace := QuasiCompact.compactSpace_of_compactSpace f
    isLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian f
    isNormal := isNormalScheme_of_isNormal Y }

@[simp]
theorem ofIsVariety_toScheme {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of k))
    (hf : AlgebraicGeometry.IsVariety k f) (hY : IsNormal Y) :
    (ofIsVariety f hf hY).toScheme = Y :=
  rfl

theorem ofIsVariety_str {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of k))
    (hf : AlgebraicGeometry.IsVariety k f) (hY : IsNormal Y) :
    (ofIsVariety f hf hY).str = f :=
  rfl

end NormalVariety

end MinimalModelBridge
