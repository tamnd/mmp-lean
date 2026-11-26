/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib

/-!
# Cones and fans

The first file of route R3 (spec 04.4): rational polyhedral cones and fans in `ℝⁿ`, on the `PointedCone` of Mathlib. The lattice is `ℤⁿ`, and `ℝⁿ` is `N ⊗ ℝ`. The definitions follow Cox, Little and Schenck, Chapter 1 and Section 3.1.
-/

namespace MinimalModel.Toric

variable {n : ℕ}

/-- The space `N_ℝ = ℝⁿ`. -/
abbrev NR (n : ℕ) := Fin n → ℝ

/-- A lattice point as a vector of `N_ℝ`. -/
def toNR (v : Fin n → ℤ) : NR n := fun i => (v i : ℝ)

/-- The cone spanned by a finite set of lattice points. -/
noncomputable def latticeCone (S : Finset (Fin n → ℤ)) : PointedCone ℝ (NR n) :=
  Submodule.span (Nonneg ℝ) (toNR '' (S : Set (Fin n → ℤ)))

/-- A rational polyhedral cone: the span of a finite set of lattice points. -/
def IsRationalPolyhedral (σ : PointedCone ℝ (NR n)) : Prop :=
  ∃ S : Finset (Fin n → ℤ), σ = latticeCone S

/-- A strongly convex cone: it contains no line. -/
def IsStronglyConvex (σ : PointedCone ℝ (NR n)) : Prop :=
  ∀ v, v ∈ σ → -v ∈ σ → v = 0

/-- `τ` is a face of `σ`: there is a linear form `u` that is nonnegative on `σ` with `τ = σ ∩ u⊥`. -/
def IsFace (τ σ : PointedCone ℝ (NR n)) : Prop :=
  ∃ u : NR n →ₗ[ℝ] ℝ, (∀ v ∈ σ, 0 ≤ u v) ∧ ∀ v, v ∈ τ ↔ v ∈ σ ∧ u v = 0

/-- A simplicial cone: the span of linearly independent lattice points. -/
def IsSimplicial (σ : PointedCone ℝ (NR n)) : Prop :=
  ∃ S : Finset (Fin n → ℤ), σ = latticeCone S ∧
    LinearIndependent ℝ (fun v : (S : Set (Fin n → ℤ)) => toNR v.1)

/-- A fan: a finite set of strongly convex rational polyhedral cones that is closed under faces, and in which two cones meet in a face of each. -/
structure Fan (n : ℕ) where
  /-- The cones of the fan. -/
  cones : Set (PointedCone ℝ (NR n))
  finite : cones.Finite
  rational : ∀ σ ∈ cones, IsRationalPolyhedral σ
  stronglyConvex : ∀ σ ∈ cones, IsStronglyConvex σ
  face_mem : ∀ σ ∈ cones, ∀ τ, IsFace τ σ → τ ∈ cones
  inter_face : ∀ σ ∈ cones, ∀ τ ∈ cones, IsFace (σ ⊓ τ) σ

namespace Fan

/-- The support `|Σ|` of a fan, the union of its cones. -/
def support (F : Fan n) : Set (NR n) := ⋃ σ ∈ F.cones, (σ : Set (NR n))

/-- A complete fan: its support is all of `N_ℝ`. -/
def IsComplete (F : Fan n) : Prop := F.support = Set.univ

/-- A simplicial fan: each cone is simplicial. -/
def IsSimplicialFan (F : Fan n) : Prop := ∀ σ ∈ F.cones, IsSimplicial σ

end Fan

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

end MinimalModel.Toric
