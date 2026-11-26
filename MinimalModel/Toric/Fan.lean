/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib

/-!
# Cones and fans

The first file of route R3 (spec 04.4): rational polyhedral cones and fans in `ℝⁿ`, on the `PointedCone` of Mathlib. The lattice is `ℤⁿ`, and `ℝⁿ` is `N ⊗ ℝ`. The definitions follow Cox, Little and Schenck, Chapter 1 and Section 3.1.

A face of a cone is a face in the sense of Mathlib, `PointedCone.IsFaceOf`: a subcone `τ` of `σ` such that, when a positive combination of two points of `σ` is in `τ`, the two points are in `τ`. For a polyhedral cone, these faces are the same as the faces cut out by a supporting hyperplane, `IsFace` below. We prove one direction here, `IsFace.isFaceOf`.

## Main results

* `eq_hull_inter_of_isFaceOf`: a face of the conic hull of a set `s` is the conic hull of the points of `s` in the face.
* `finite_setOf_isFaceOf_hull`: a finitely generated cone has finitely many faces.
* `IsRationalPolyhedral.of_isFaceOf`, `IsSimplicial.of_isFaceOf`: a face of a rational polyhedral cone is rational polyhedral, and a face of a simplicial cone is simplicial.
* `bot_isFaceOf`: the zero cone is a face of each strongly convex cone.
* `Fan.bot_mem`, `Fan.inf_mem`: a fan with a cone contains the zero cone, and it contains the intersection of two of its cones.
* `Fan.trivial`, `Fan.ofCone`, `Fan.affine`: the trivial fan, the fan of the faces of one cone, and the fan of the affine space `𝔸ⁿ`.
* `isSimplicial_orthant`, `Fan.isSimplicialFan_affine`: the positive orthant is simplicial, so the fan of `𝔸ⁿ` is simplicial.
-/

namespace MinimalModel.Toric

variable {n : ℕ}

/-- The space `N_ℝ = ℝⁿ`. -/
abbrev NR (n : ℕ) := Fin n → ℝ

/-- A lattice point as a vector of `N_ℝ`. -/
def toNR (v : Fin n → ℤ) : NR n := fun i => (v i : ℝ)

@[simp]
theorem toNR_apply (v : Fin n → ℤ) (i : Fin n) : toNR v i = (v i : ℝ) := rfl

/-- The zero lattice point is the zero vector. -/
@[simp]
theorem toNR_zero : toNR (0 : Fin n → ℤ) = 0 := by
  funext i
  simp

/-- Two lattice points with the same vector are equal. -/
theorem toNR_injective : Function.Injective (toNR : (Fin n → ℤ) → NR n) := by
  intro v w h
  funext i
  have hi := congrFun h i
  simp only [toNR_apply, Int.cast_inj] at hi
  exact hi

/-- The vector of a nonzero lattice point is not zero. -/
theorem toNR_ne_zero {v : Fin n → ℤ} (hv : v ≠ 0) : toNR v ≠ 0 := fun h =>
  hv (toNR_injective (h.trans toNR_zero.symm))

/-- The cone spanned by a finite set of lattice points. -/
noncomputable def latticeCone (S : Finset (Fin n → ℤ)) : PointedCone ℝ (NR n) :=
  Submodule.span (Nonneg ℝ) (toNR '' (S : Set (Fin n → ℤ)))

/-- The cone of `S` is the conic hull, in the sense of Mathlib, of the vectors of `S`. -/
theorem latticeCone_eq_hull (S : Finset (Fin n → ℤ)) :
    latticeCone S = PointedCone.hull ℝ (toNR '' (S : Set (Fin n → ℤ))) := rfl

/-- The cone of `S` contains the vector of each point of `S`. -/
theorem toNR_mem_latticeCone {S : Finset (Fin n → ℤ)} {v : Fin n → ℤ} (hv : v ∈ S) :
    toNR v ∈ latticeCone S :=
  Submodule.subset_span ⟨v, hv, rfl⟩

/-- A vector is in the cone of one lattice point `v` when it is a nonnegative multiple of `v`. -/
theorem mem_latticeCone_singleton {v : Fin n → ℤ} {x : NR n} :
    x ∈ latticeCone {v} ↔ ∃ r : ℝ, 0 ≤ r ∧ r • toNR v = x := by
  rw [latticeCone_eq_hull, Finset.coe_singleton, Set.image_singleton]
  exact PointedCone.mem_hull_singleton

/-- A rational polyhedral cone: the span of a finite set of lattice points. -/
def IsRationalPolyhedral (σ : PointedCone ℝ (NR n)) : Prop :=
  ∃ S : Finset (Fin n → ℤ), σ = latticeCone S

/-- A strongly convex cone: it contains no line. -/
def IsStronglyConvex (σ : PointedCone ℝ (NR n)) : Prop :=
  ∀ v, v ∈ σ → -v ∈ σ → v = 0

/-- `τ` is an exposed face of `σ`: there is a linear form `u` that is nonnegative on `σ` with `τ = σ ∩ u⊥`. A fan uses the faces of Mathlib, `PointedCone.IsFaceOf`, and `IsFace.isFaceOf` shows that an exposed face is a face. -/
def IsFace (τ σ : PointedCone ℝ (NR n)) : Prop :=
  ∃ u : NR n →ₗ[ℝ] ℝ, (∀ v ∈ σ, 0 ≤ u v) ∧ ∀ v, v ∈ τ ↔ v ∈ σ ∧ u v = 0

/-- A simplicial cone: the span of linearly independent lattice points. -/
def IsSimplicial (σ : PointedCone ℝ (NR n)) : Prop :=
  ∃ S : Finset (Fin n → ℤ), σ = latticeCone S ∧
    LinearIndependent ℝ (fun v : (S : Set (Fin n → ℤ)) => toNR v.1)

/-- The cone of the empty set is the zero cone. -/
theorem latticeCone_empty : latticeCone (∅ : Finset (Fin n → ℤ)) = ⊥ := by
  simp [latticeCone]

/-- The zero cone is rational polyhedral. -/
theorem isRationalPolyhedral_bot : IsRationalPolyhedral (⊥ : PointedCone ℝ (NR n)) :=
  ⟨∅, latticeCone_empty.symm⟩

/-- The zero cone is strongly convex. -/
theorem isStronglyConvex_bot : IsStronglyConvex (⊥ : PointedCone ℝ (NR n)) := by
  intro v hv _
  simpa using hv

/-- Each cone is a face of itself, with the form `0`. -/
theorem isFace_refl (σ : PointedCone ℝ (NR n)) : IsFace σ σ :=
  ⟨0, fun _ _ => le_rfl, fun v => by simp⟩

/-- A subcone of a strongly convex cone is strongly convex. -/
theorem IsStronglyConvex.mono {σ τ : PointedCone ℝ (NR n)} (hσ : IsStronglyConvex σ)
    (h : τ ≤ σ) : IsStronglyConvex τ :=
  fun v hv hnv => hσ v (h hv) (h hnv)

/-- The zero cone is simplicial: it is the span of the empty set. -/
theorem isSimplicial_bot : IsSimplicial (⊥ : PointedCone ℝ (NR n)) := by
  refine ⟨∅, latticeCone_empty.symm, ?_⟩
  change LinearIndepOn ℝ toNR ((∅ : Finset (Fin n → ℤ)) : Set (Fin n → ℤ))
  rw [Finset.coe_empty]
  exact linearIndepOn_empty ℝ toNR

/-- The cone of one nonzero lattice point is simplicial. -/
theorem isSimplicial_latticeCone_singleton {v : Fin n → ℤ} (hv : v ≠ 0) :
    IsSimplicial (latticeCone {v}) := by
  refine ⟨{v}, rfl, ?_⟩
  change LinearIndepOn ℝ toNR (({v} : Finset (Fin n → ℤ)) : Set (Fin n → ℤ))
  rw [Finset.coe_singleton, linearIndepOn_singleton_iff]
  exact toNR_ne_zero hv

section Face

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Let `F` be a face of `C`, and let a nonnegative combination of points of `C` lie in `F`. Then each point with a positive coefficient lies in `F`. -/
theorem mem_face_of_sum_smul_mem {F C : PointedCone ℝ E} (hF : F.IsFaceOf C) {t : Finset E}
    {c : E → ℝ} (ht : ∀ x ∈ t, x ∈ C) (hc : ∀ x ∈ t, 0 ≤ c x) (hs : ∑ x ∈ t, c x • x ∈ F)
    {y : E} (hy : y ∈ t) (hcy : 0 < c y) : y ∈ F := by
  classical
  rw [← Finset.add_sum_erase t _ hy] at hs
  refine hF.mem_of_smul_add_mem (ht y hy) ?_ hcy hs
  exact Submodule.sum_mem C fun x hx =>
    C.smul_mem (hc x (Finset.mem_of_mem_erase hx)) (ht x (Finset.mem_of_mem_erase hx))

/-- A face of the conic hull of a set `s` is the conic hull of the points of `s` that lie in the face. -/
theorem eq_hull_inter_of_isFaceOf {s : Set E} {F : PointedCone ℝ E}
    (hF : F.IsFaceOf (PointedCone.hull ℝ s)) : F = PointedCone.hull ℝ (s ∩ F) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨c, hcs, hc0, rfl⟩ := PointedCone.mem_hull_set.mp (hF.le hx)
    simp only [Finsupp.sum] at hx ⊢
    refine Submodule.sum_mem _ fun y hy => ?_
    have hcy : 0 < c y := lt_of_le_of_ne (hc0 y) (Ne.symm (Finsupp.mem_support_iff.mp hy))
    have hyF : y ∈ F := mem_face_of_sum_smul_mem hF
      (fun z hz => Submodule.subset_span (hcs hz)) (fun z _ => hc0 z) hx hy hcy
    exact PointedCone.smul_mem _ (hc0 y) (Submodule.subset_span ⟨hcs hy, hyF⟩)
  · exact Submodule.span_le.mpr fun x hx => hx.2

/-- The conic hull of a finite set has finitely many faces. -/
theorem finite_setOf_isFaceOf_hull {s : Set E} (hs : s.Finite) :
    {F : PointedCone ℝ E | F.IsFaceOf (PointedCone.hull ℝ s)}.Finite := by
  refine (hs.finite_subsets.image fun t => PointedCone.hull ℝ t).subset ?_
  intro F hF
  exact ⟨s ∩ F, Set.inter_subset_left, (eq_hull_inter_of_isFaceOf hF).symm⟩

end Face

/-- A face of the cone of `S` is the cone of a subset of `S`. -/
theorem exists_subset_of_isFaceOf_latticeCone {S : Finset (Fin n → ℤ)}
    {τ : PointedCone ℝ (NR n)} (h : τ.IsFaceOf (latticeCone S)) :
    ∃ T ⊆ S, τ = latticeCone T := by
  classical
  refine ⟨S.filter fun v => toNR v ∈ τ, Finset.filter_subset _ _, ?_⟩
  refine (eq_hull_inter_of_isFaceOf h).trans ?_
  rw [latticeCone_eq_hull]
  congr 1
  ext x
  simp only [Set.mem_inter_iff, Set.mem_image, Finset.coe_filter, Set.mem_ofPred_eq,
    SetLike.mem_coe]
  constructor
  · rintro ⟨⟨v, hv, rfl⟩, hx⟩
    exact ⟨v, ⟨hv, hx⟩, rfl⟩
  · rintro ⟨v, ⟨hv, hx⟩, rfl⟩
    exact ⟨⟨v, hv, rfl⟩, hx⟩

/-- A face of a rational polyhedral cone is rational polyhedral. -/
theorem IsRationalPolyhedral.of_isFaceOf {σ τ : PointedCone ℝ (NR n)}
    (hσ : IsRationalPolyhedral σ) (h : τ.IsFaceOf σ) : IsRationalPolyhedral τ := by
  obtain ⟨S, rfl⟩ := hσ
  obtain ⟨T, -, rfl⟩ := exists_subset_of_isFaceOf_latticeCone h
  exact ⟨T, rfl⟩

/-- A face of a simplicial cone is simplicial. -/
theorem IsSimplicial.of_isFaceOf {σ τ : PointedCone ℝ (NR n)} (hσ : IsSimplicial σ)
    (h : τ.IsFaceOf σ) : IsSimplicial τ := by
  obtain ⟨S, rfl, hS⟩ := hσ
  obtain ⟨T, hT, rfl⟩ := exists_subset_of_isFaceOf_latticeCone h
  exact ⟨T, rfl, LinearIndepOn.mono (v := toNR) (s := (S : Set (Fin n → ℤ))) hS
    (Finset.coe_subset.mpr hT)⟩

/-- The cone of one lattice point `v` has two faces: the zero cone and itself. -/
theorem eq_bot_or_eq_of_isFaceOf_latticeCone_singleton {v : Fin n → ℤ}
    {τ : PointedCone ℝ (NR n)} (h : τ.IsFaceOf (latticeCone {v})) :
    τ = ⊥ ∨ τ = latticeCone {v} := by
  obtain ⟨T, hT, rfl⟩ := exists_subset_of_isFaceOf_latticeCone h
  rcases Finset.subset_singleton_iff.mp hT with rfl | rfl
  · exact Or.inl latticeCone_empty
  · exact Or.inr rfl

/-- The zero cone is a face of each strongly convex cone. -/
theorem bot_isFaceOf {σ : PointedCone ℝ (NR n)} (hσ : IsStronglyConvex σ) :
    (⊥ : PointedCone ℝ (NR n)).IsFaceOf σ := by
  refine ⟨bot_le, fun {x y a} hx hy ha hxy => ?_⟩
  rw [Submodule.mem_bot] at hxy ⊢
  have hy' : y = -(a • x) := eq_neg_of_add_eq_zero_right hxy
  have h0 : a • x = 0 := hσ _ (σ.smul_mem ha.le hx) (by rw [← hy']; exact hy)
  exact (smul_eq_zero.mp h0).resolve_left ha.ne'

/-- An exposed face is a face in the sense of Mathlib. -/
theorem IsFace.isFaceOf {τ σ : PointedCone ℝ (NR n)} (h : IsFace τ σ) : τ.IsFaceOf σ := by
  obtain ⟨u, hu, hτ⟩ := h
  refine ⟨fun v hv => ((hτ v).mp hv).1, fun {x y a} hx hy ha hxy => ?_⟩
  obtain ⟨-, h0⟩ := (hτ _).mp hxy
  rw [map_add, map_smul, smul_eq_mul] at h0
  have h1 : a * u x = 0 := by linarith [mul_nonneg ha.le (hu x hx), hu y hy]
  exact (hτ x).mpr ⟨hx, (mul_eq_zero.mp h1).resolve_left ha.ne'⟩

/-- A fan: a finite set of strongly convex rational polyhedral cones that is closed under faces, and in which two cones meet in a face of each. A face is a face in the sense of Mathlib, `PointedCone.IsFaceOf`. -/
structure Fan (n : ℕ) where
  /-- The cones of the fan. -/
  cones : Set (PointedCone ℝ (NR n))
  finite : cones.Finite
  rational : ∀ σ ∈ cones, IsRationalPolyhedral σ
  stronglyConvex : ∀ σ ∈ cones, IsStronglyConvex σ
  face_mem : ∀ σ ∈ cones, ∀ τ : PointedCone ℝ (NR n), τ.IsFaceOf σ → τ ∈ cones
  inter_face : ∀ σ ∈ cones, ∀ τ ∈ cones, PointedCone.IsFaceOf (σ ⊓ τ) σ

namespace Fan

variable (F : Fan n)

/-- The support `|Σ|` of a fan, the union of its cones. -/
def support : Set (NR n) := ⋃ σ ∈ F.cones, (σ : Set (NR n))

/-- A complete fan: its support is all of `N_ℝ`. -/
def IsComplete : Prop := F.support = Set.univ

/-- A simplicial fan: each cone is simplicial. -/
def IsSimplicialFan : Prop := ∀ σ ∈ F.cones, IsSimplicial σ

/-- A vector is in the support when it is in a cone of the fan. -/
theorem mem_support {x : NR n} : x ∈ F.support ↔ ∃ σ ∈ F.cones, x ∈ σ := by
  simp [support]

/-- Two cones of a fan meet in a face of the second cone. -/
theorem inter_face_right {σ τ : PointedCone ℝ (NR n)} (hσ : σ ∈ F.cones) (hτ : τ ∈ F.cones) :
    (σ ⊓ τ).IsFaceOf τ := by
  rw [inf_comm]
  exact F.inter_face τ hτ σ hσ

/-- The intersection of two cones of a fan is a cone of the fan. -/
theorem inf_mem {σ τ : PointedCone ℝ (NR n)} (hσ : σ ∈ F.cones) (hτ : τ ∈ F.cones) :
    σ ⊓ τ ∈ F.cones :=
  F.face_mem σ hσ _ (F.inter_face σ hσ τ hτ)

/-- A face of a face of a cone of a fan is a cone of the fan. -/
theorem mem_of_isFaceOf_of_isFaceOf {σ τ ρ : PointedCone ℝ (NR n)} (hσ : σ ∈ F.cones)
    (hτ : τ.IsFaceOf σ) (hρ : ρ.IsFaceOf τ) : ρ ∈ F.cones :=
  F.face_mem σ hσ ρ (hρ.trans hτ)

/-- A fan with a cone contains the zero cone. -/
theorem bot_mem {σ : PointedCone ℝ (NR n)} (hσ : σ ∈ F.cones) :
    (⊥ : PointedCone ℝ (NR n)) ∈ F.cones :=
  F.face_mem σ hσ ⊥ (bot_isFaceOf (F.stronglyConvex σ hσ))

/-- The trivial fan: its only cone is the zero cone. It is the fan of the torus. -/
def trivial (n : ℕ) : Fan n where
  cones := {⊥}
  finite := Set.finite_singleton _
  rational σ hσ := by
    rw [Set.mem_singleton_iff.mp hσ]
    exact isRationalPolyhedral_bot
  stronglyConvex σ hσ := by
    rw [Set.mem_singleton_iff.mp hσ]
    exact isStronglyConvex_bot
  face_mem σ hσ τ hτ := by
    rw [Set.mem_singleton_iff.mp hσ] at hτ
    exact Set.mem_singleton_iff.mpr (le_bot_iff.mp hτ.le)
  inter_face σ hσ τ hτ := by
    rw [Set.mem_singleton_iff.mp hσ, Set.mem_singleton_iff.mp hτ, inf_idem]

/-- The support of the trivial fan is the origin. -/
theorem support_trivial : (trivial n).support = {0} := by
  ext x
  simp [mem_support, trivial]

/-- The trivial fan is simplicial. -/
theorem isSimplicialFan_trivial : (trivial n).IsSimplicialFan := by
  intro σ hσ
  rw [show σ = ⊥ from hσ]
  exact isSimplicial_bot

/-- The fan of the faces of one strongly convex rational polyhedral cone `σ`. It is the fan of the affine toric variety `U_σ`. -/
noncomputable def ofCone (σ : PointedCone ℝ (NR n)) (hr : IsRationalPolyhedral σ)
    (hs : IsStronglyConvex σ) : Fan n where
  cones := {τ | PointedCone.IsFaceOf τ σ}
  finite := by
    obtain ⟨S, rfl⟩ := hr
    exact finite_setOf_isFaceOf_hull (S.finite_toSet.image _)
  rational τ hτ := hr.of_isFaceOf hτ
  stronglyConvex τ hτ := hs.mono (PointedCone.IsFaceOf.le hτ)
  face_mem τ hτ ρ hρ := PointedCone.IsFaceOf.trans hρ hτ
  inter_face τ₁ h₁ τ₂ h₂ :=
    (PointedCone.IsFaceOf.isFaceOf_iff_le (PointedCone.IsFaceOf.inf_left h₁ h₂) h₁).mpr
      inf_le_left

/-- A cone is a cone of its own fan. -/
theorem mem_ofCone_self (σ : PointedCone ℝ (NR n)) (hr : IsRationalPolyhedral σ)
    (hs : IsStronglyConvex σ) : σ ∈ (ofCone σ hr hs).cones :=
  PointedCone.IsFaceOf.refl σ

/-- The support of the fan of `σ` is `σ`. -/
theorem support_ofCone (σ : PointedCone ℝ (NR n)) (hr : IsRationalPolyhedral σ)
    (hs : IsStronglyConvex σ) : (ofCone σ hr hs).support = (σ : Set (NR n)) := by
  ext x
  rw [mem_support]
  constructor
  · rintro ⟨τ, hτ, hx⟩
    exact PointedCone.IsFaceOf.le hτ hx
  · intro hx
    exact ⟨σ, mem_ofCone_self σ hr hs, hx⟩

/-- The fan of a simplicial cone is simplicial. -/
theorem isSimplicialFan_ofCone {σ : PointedCone ℝ (NR n)} (hr : IsRationalPolyhedral σ)
    (hs : IsStronglyConvex σ) (h : IsSimplicial σ) : (ofCone σ hr hs).IsSimplicialFan :=
  fun _ hτ => h.of_isFaceOf hτ

end Fan

section Affine

/-- The lattice points `e₁, ..., eₙ` of the standard basis. -/
def stdBasis (n : ℕ) : Finset (Fin n → ℤ) := Finset.univ.image fun i => Pi.single i 1

/-- The positive orthant of `N_ℝ`: the cone spanned by `e₁, ..., eₙ`. -/
noncomputable def orthant (n : ℕ) : PointedCone ℝ (NR n) := latticeCone (stdBasis n)

/-- The cone of points with nonnegative coordinates is strongly convex. -/
theorem isStronglyConvex_positive : IsStronglyConvex (PointedCone.positive ℝ (NR n)) := by
  intro v hv hnv
  rw [PointedCone.mem_positive] at hv hnv
  exact le_antisymm (neg_nonneg.mp hnv) hv

/-- A cone spanned by lattice points with nonnegative coordinates lies in the cone of points with nonnegative coordinates. -/
theorem latticeCone_le_positive {S : Finset (Fin n → ℤ)} (hS : ∀ v ∈ S, 0 ≤ v) :
    latticeCone S ≤ PointedCone.positive ℝ (NR n) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨v, hv, rfl⟩
  rw [SetLike.mem_coe, PointedCone.mem_positive]
  intro i
  simpa using hS v hv i

/-- The positive orthant is strongly convex. -/
theorem isStronglyConvex_orthant : IsStronglyConvex (orthant n) := by
  refine isStronglyConvex_positive.mono (latticeCone_le_positive ?_)
  intro v hv
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hv
  exact Pi.single_nonneg.mpr zero_le_one

/-- The fan of the affine space `𝔸ⁿ`: the faces of the positive orthant. -/
noncomputable def Fan.affine (n : ℕ) : Fan n :=
  Fan.ofCone (orthant n) ⟨stdBasis n, rfl⟩ isStronglyConvex_orthant

/-- The support of the fan of `𝔸ⁿ` is the positive orthant. -/
theorem Fan.support_affine : (Fan.affine n).support = (orthant n : Set (NR n)) :=
  Fan.support_ofCone _ _ _

/-- The positive orthant is simplicial: `e₁, ..., eₙ` are linearly independent. -/
theorem isSimplicial_orthant : IsSimplicial (orthant n) := by
  refine ⟨stdBasis n, rfl, ?_⟩
  change LinearIndepOn ℝ toNR ((stdBasis n : Finset (Fin n → ℤ)) : Set (Fin n → ℤ))
  have hcomp : (toNR ∘ fun i : Fin n => (Pi.single i 1 : Fin n → ℤ)) = Pi.basisFun ℝ (Fin n) := by
    funext i j
    simp [Pi.single_apply]
  have hli : LinearIndependent ℝ (toNR ∘ fun i : Fin n => (Pi.single i 1 : Fin n → ℤ)) := by
    rw [hcomp]
    exact (Pi.basisFun ℝ (Fin n)).linearIndependent
  rw [show ((stdBasis n : Finset (Fin n → ℤ)) : Set (Fin n → ℤ)) =
    Set.range (fun i : Fin n => (Pi.single i 1 : Fin n → ℤ)) by simp [stdBasis]]
  exact (linearIndepOn_range_iff hli.injective.of_comp toNR).mpr hli

/-- The fan of `𝔸ⁿ` is simplicial. -/
theorem Fan.isSimplicialFan_affine : (Fan.affine n).IsSimplicialFan :=
  Fan.isSimplicialFan_ofCone _ _ isSimplicial_orthant

end Affine

end MinimalModel.Toric
