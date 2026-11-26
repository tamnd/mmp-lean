/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import MinimalModel.Toric.Cone

/-!
# The toric minimal model program on fans

This file gives the combinatorial vocabulary of the toric minimal model program (Reid 1983; Fujino and Sato 2004; Matsuki 2002, Chapter 14; Cox, Little and Schenck, Chapter 15). A toric variety is given by its fan, and a torus-invariant divisor by its coefficients on the rays. A toric morphism that is the identity on the lattice is given by a coarser set of cones. When the coarser cones contain lines, the morphism goes to a toric variety of smaller dimension, the quotient by the line space. So the base of a contraction is a quasi-fan: a fan whose cones need not be strongly convex.

## Main definitions

* `IsQuasiFan`: a finite set of rational polyhedral cones, closed under faces, in which two cones meet in a face of each.
* `Fan.Refines`: the fan refines a set of cones; this is the toric morphism to the coarser variety.
* `Fan.IsAmpleOver`: a divisor whose support function is strictly convex on each coarser cone; this is ampleness relative to the morphism (Cox, Little and Schenck, Theorem 6.1.14 for the absolute case, and Section 15.4).
* `Fan.IsProjectiveFan`: a complete fan with an ample divisor.
* `Fan.IsPullback`, `Fan.HasRelPicardOne`: the pullbacks from the coarser variety, and relative Picard number one.
* `ToricModel`, `IsToricStep`, `IsToricMoriFibreSpace`: the models, the steps and the Mori fibre spaces of a toric `D`-program.

The convention of signs is that of `Fan.IsNef`: the support function `φ` of `D = Σ a_ρ D_ρ` has `φ(u_ρ) = -a_ρ`, and `D` is nef when `φ` is concave in the sense of Mathlib.
-/

namespace MinimalModel.Toric

variable {n : ℕ}

/-- A quasi-fan: a finite set of rational polyhedral cones that is closed under faces, and in which two cones meet in a face of each. The cones need not be strongly convex. -/
def IsQuasiFan (T : Set (PointedCone ℝ (NR n))) : Prop :=
  T.Finite ∧ (∀ σ ∈ T, IsRationalPolyhedral σ) ∧
    (∀ σ ∈ T, ∀ τ : PointedCone ℝ (NR n), τ.IsFaceOf σ → τ ∈ T) ∧
    ∀ σ ∈ T, ∀ τ ∈ T, PointedCone.IsFaceOf (σ ⊓ τ) σ

/-- The support function `φ` is strictly convex at the cone `σ` on the set `S`: the linear form `m` of `φ` on `σ` satisfies `φ < m` at each point of `S` outside `σ`. -/
def IsStrictAt (φ : NR n → ℝ) (σ : PointedCone ℝ (NR n)) (S : Set (NR n)) : Prop :=
  ∃ m : NR n →ₗ[ℝ] ℝ, (∀ x ∈ σ, φ x = m x) ∧ ∀ x ∈ S, x ∉ σ → φ x < m x

namespace Fan

variable (F : Fan n)

/-- The fan `F` refines the set of cones `T`: each cone of `F` is in a cone of `T`, and each cone of `T` is the union of the cones of `F` that it contains. This is the toric morphism from the variety of `F` to the variety of `T`. It is proper, and it has connected fibres. -/
def Refines (T : Set (PointedCone ℝ (NR n))) : Prop :=
  (∀ σ ∈ F.cones, ∃ τ ∈ T, σ ≤ τ) ∧
    ∀ τ ∈ T, (τ : Set (NR n)) = ⋃ σ ∈ {σ | σ ∈ F.cones ∧ σ ≤ τ}, (σ : Set (NR n))

/-- The divisor `D` is ample over the variety of `T`: it has a support function `φ` that is strictly convex on each cone `τ` of `T`, at each maximal cone of `F` in `τ`. -/
def IsAmpleOver (T : Set (PointedCone ℝ (NR n))) (D : F.TDivisor ℝ) : Prop :=
  ∃ φ : NR n → ℝ, F.IsSupportFunctionOf D φ ∧
    ∀ τ ∈ T, ∀ σ, F.IsMaximalCone σ → σ ≤ τ → IsStrictAt φ σ τ

/-- An ample divisor: ample over a point, the variety of the cone `N_ℝ`. -/
def IsAmple (D : F.TDivisor ℝ) : Prop := F.IsAmpleOver {⊤} D

/-- A projective fan: a complete fan with an ample `ℝ`-Cartier divisor. -/
def IsProjectiveFan : Prop := F.IsComplete ∧ ∃ D : F.TDivisor ℝ, F.IsRCartier D ∧ F.IsAmple D

/-- The divisor `D` is a pullback from the variety of `T`: it has a support function that is linear on each cone of `T`. -/
def IsPullback (T : Set (PointedCone ℝ (NR n))) (D : F.TDivisor ℝ) : Prop :=
  ∃ φ : NR n → ℝ, F.IsSupportFunctionOf D φ ∧ ∀ τ ∈ T, ∃ m : NR n →ₗ[ℝ] ℝ, ∀ x ∈ τ, φ x = m x

/-- The relative Picard number of the morphism to the variety of `T` is one: there is an `ℝ`-Cartier divisor `D₀` that is not a pullback, and each `ℝ`-Cartier divisor is a multiple of `D₀` up to a pullback. -/
def HasRelPicardOne (T : Set (PointedCone ℝ (NR n))) : Prop :=
  ∃ D₀ : F.TDivisor ℝ, F.IsRCartier D₀ ∧ ¬ F.IsPullback T D₀ ∧
    ∀ D : F.TDivisor ℝ, F.IsRCartier D → ∃ t : ℝ, F.IsPullback T (D - t • D₀)

end Fan

/-- A model of a toric program: a fan and a torus-invariant divisor with real coefficients. -/
structure ToricModel (n : ℕ) where
  /-- The fan. -/
  F : Fan n
  /-- The divisor. -/
  D : F.TDivisor ℝ

/-- One step of the toric `D`-program from `A` to `B` (Cox, Little and Schenck, Section 15.4; Matsuki, Chapter 14). There is a fan `G`, the base of the step, such that:
* `A.F` refines `G` with relative Picard number one, and `-D` is ample over `G`: the morphism to the variety of `G` is the contraction of a `D`-negative extremal ray, and it is birational because the cones of `G` are strongly convex;
* `B.F` is a simplicial fan that refines `G`, with the same rays as `G`, and `B.D` is ample over `G`;
* `B.D` is the strict transform of `A.D`: each ray of `B.F` is a ray of `A.F` with the same coefficient.
For a divisorial contraction `B.F = G`. For a flip `G` has the rays of `A.F`, and `B.F` is the flip. -/
def IsToricStep (A B : ToricModel n) : Prop :=
  ∃ G : Fan n, A.F.Refines G.cones ∧ A.F.HasRelPicardOne G.cones ∧ A.F.IsAmpleOver G.cones (-A.D) ∧
    B.F.IsSimplicialFan ∧ B.F.Refines G.cones ∧ B.F.rays = G.rays ∧
    B.F.IsAmpleOver G.cones B.D ∧
    ∀ (ρ' : B.F.Ray) (ρ : A.F.Ray), ρ'.1 = ρ.1 → B.D ρ' = A.D ρ

/-- A toric Mori fibre space for the divisor: the contraction of a `D`-negative extremal ray to a variety of smaller dimension. The fan refines a quasi-fan `T` with relative Picard number one, a cone of `T` contains a line, and `-D` is ample over `T`. -/
def IsToricMoriFibreSpace (A : ToricModel n) : Prop :=
  ∃ T : Set (PointedCone ℝ (NR n)), IsQuasiFan T ∧ (∃ τ ∈ T, ¬ IsStronglyConvex τ) ∧
    A.F.Refines T ∧ A.F.HasRelPicardOne T ∧ A.F.IsAmpleOver T (-A.D)

end MinimalModel.Toric
