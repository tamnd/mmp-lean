/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import MinimalModel.Toric.Wall

/-!
# Nef divisors and wall curves

This file is the combinatorial side of the toric cone theorem (route R3, spec 04.4). Let `σ` and `σ'` be two maximal cones of a complete fan that meet in a wall `τ = σ ∩ σ'`, a cone of dimension `n - 1`. The wall gives a torus-invariant curve `V(τ)` of the toric variety. The degree `D · V(τ)` of a divisor on this curve can be read off the fan (Cox, Little and Schenck, Proposition 6.4.4).

We describe a wall by a `Fan.WallData`: a ray `ρ'` of `σ'` that is not in `σ`, such that each other ray of `σ'` is in `σ`, and an expression `u_ρ' = Σ c_ρ u_ρ` of its generator in terms of the generators of the rays of `σ`. The degree of `D = Σ a_ρ D_ρ` on the wall is `a_ρ' - Σ c_ρ a_ρ`. When `σ` and `σ'` are smooth, with the wall relation `v + v' = Σ bᵢ uᵢ` of `Fan.exists_unique_wall_relation`, the generator `v'` is `-v + Σ bᵢ uᵢ`, and the degree is `a_v + a_v' - Σ bᵢ a_uᵢ`. This is `D · V(τ)` in Proposition 6.4.4 of Cox, Little and Schenck. When `σ` and `σ'` are simplicial, the degree is a positive multiple of `D · V(τ)`.

The support function `φ` of `D` is convex in the sense of Cox, Little and Schenck when `φ(u + v) ≥ φ(u) + φ(v)`. In the convention of Mathlib this is `ConcaveOn ℝ Set.univ φ`. Across a wall, convexity says that `φ ≤ m_σ` on `σ'`, where `m_σ` is the linear form of `φ` on `σ`. This is the wall inequality.

## Main definitions

* `coneDim`: the dimension of a cone.
* `Fan.IsMaximalCone`, `Fan.IsWallPair`: maximal cones, and pairs of maximal cones that meet in a wall.
* `IsConvexAcross`: the wall inequality.
* `Fan.IsNef`: a divisor whose support function is convex.
* `Fan.WallData`, `Fan.WallData.degree`: the data of a wall and the degree of a divisor on it.

## Main results

* `Fan.WallData.degree_eq`: the degree is `a_ρ' + m_σ(u_ρ')`.
* `Fan.WallData.degree_nonneg_iff`: the degree is nonnegative exactly when the wall inequality holds.
-/

namespace MinimalModel.Toric

variable {n : ℕ}

/-- The dimension of a cone: the dimension of its linear span. -/
noncomputable def coneDim (σ : PointedCone ℝ (NR n)) : ℕ :=
  Module.finrank ℝ (Submodule.span ℝ (σ : Set (NR n)))

section Hull

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- If a linear form is at most another one on a set, then it is at most the other one on the cone spanned by the set. -/
theorem le_of_mem_hull {m m' : E →ₗ[ℝ] ℝ} {s : Set E} (h : ∀ x ∈ s, m x ≤ m' x) {x : E}
    (hx : x ∈ PointedCone.hull ℝ s) : m x ≤ m' x := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact h y hy
  | zero => rw [map_zero, map_zero]
  | add y z _ _ hy hz =>
    rw [map_add, map_add]
    exact add_le_add hy hz
  | smul a y _ hy =>
    rw [← Nonneg.coe_smul, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left hy a.2

end Hull

/-- The wall inequality for a function `φ` and two cones `σ` and `σ'`: each linear form `m` that agrees with `φ` on `σ` satisfies `φ ≤ m` on `σ'`. For a support function this says that `φ` bends down across `σ ∩ σ'`. -/
def IsConvexAcross (φ : NR n → ℝ) (σ σ' : PointedCone ℝ (NR n)) : Prop :=
  ∀ m : NR n →ₗ[ℝ] ℝ, (∀ x ∈ σ, φ x = m x) → ∀ x ∈ σ', φ x ≤ m x

namespace Fan

variable (F : Fan n)

/-- A maximal cone of the fan: a cone of the fan that is not contained in a larger one. -/
def IsMaximalCone (σ : PointedCone ℝ (NR n)) : Prop :=
  Maximal (· ∈ F.cones) σ

/-- Two different maximal cones `σ` and `σ'` of the fan that meet in a wall: the cone `σ ∩ σ'` has dimension `n - 1`. -/
def IsWallPair (σ σ' : PointedCone ℝ (NR n)) : Prop :=
  F.IsMaximalCone σ ∧ F.IsMaximalCone σ' ∧ σ ≠ σ' ∧ coneDim (σ ⊓ σ') + 1 = n

/-- A divisor `D` with real coefficients is nef: it has a support function `φ` that is convex in the sense of Cox, Little and Schenck, `φ(t u + (1 - t) v) ≥ t φ(u) + (1 - t) φ(v)`. This is `ConcaveOn` in Mathlib. On a complete fan the support function is unique (`IsSupportFunctionOf.eqOn_support`), and the condition says that it is convex. By Cox, Little and Schenck, Theorems 6.1.7 and 6.3.12, this is the same as the nefness of the divisor on the toric variety. We take it as the definition, since this file works with the fan only. -/
def IsNef (D : F.TDivisor ℝ) : Prop :=
  ∃ φ : NR n → ℝ, F.IsSupportFunctionOf D φ ∧ ConcaveOn ℝ Set.univ φ

/-- The data of a wall between two cones `σ` and `σ'` of the fan. There is a ray `ρ'` of `σ'` that is not in `σ`, and each other ray of `σ'` is in `σ`. The generator `u_ρ'` is a real combination `Σ c_ρ u_ρ` of the generators of rays `ρ` of `σ`. For two simplicial maximal cones that meet in a wall, such data exist, and the relation is the wall relation of Cox, Little and Schenck, Section 6.4, solved for `u_ρ'`. -/
structure WallData (σ σ' : PointedCone ℝ (NR n)) where
  /-- The ray `ρ'` of `σ'` that is not in `σ`. -/
  ray : F.Ray
  /-- The ray `ρ'` is in `σ'`. -/
  ray_le : ray.1 ≤ σ'
  /-- The ray `ρ'` is not in `σ`. -/
  ray_not_le : ¬ ray.1 ≤ σ
  /-- Each ray of `σ'` other than `ρ'` is in `σ`. -/
  eq_or_le : ∀ ρ : F.Ray, ρ.1 ≤ σ' → ρ = ray ∨ ρ.1 ≤ σ
  /-- The rays of `σ` used in the relation. -/
  base : Finset F.Ray
  /-- The rays of the relation are in `σ`. -/
  base_le : ∀ ρ ∈ base, ρ.1 ≤ σ
  /-- The coefficients `c_ρ` of the relation. -/
  coeff : F.Ray → ℝ
  /-- The relation `u_ρ' = Σ c_ρ u_ρ`. -/
  relation : toNR (F.generator ray) = ∑ ρ ∈ base, coeff ρ • toNR (F.generator ρ)

namespace WallData

variable {F} {σ σ' : PointedCone ℝ (NR n)} (W : F.WallData σ σ')

/-- The degree of a divisor `D = Σ a_ρ D_ρ` on the curve of the wall: `a_ρ' - Σ c_ρ a_ρ`. For smooth cones it is the intersection number `D · V(τ)` of Cox, Little and Schenck, Proposition 6.4.4, and for simplicial cones it is a positive multiple of it (see the module docstring). -/
noncomputable def degree (D : F.TDivisor ℝ) : ℝ :=
  D W.ray - ∑ ρ ∈ W.base, W.coeff ρ * D ρ

/-- The degree of `D` on the wall is `a_ρ' + m_σ(u_ρ')`, for each linear form `m_σ` with `m_σ(u_ρ) = -a_ρ` on the rays of `σ`. -/
theorem degree_eq {D : F.TDivisor ℝ} {m : NR n →ₗ[ℝ] ℝ}
    (hm : ∀ ρ : F.Ray, ρ.1 ≤ σ → m (toNR (F.generator ρ)) = -D ρ) :
    W.degree D = D W.ray + m (toNR (F.generator W.ray)) := by
  have h : m (toNR (F.generator W.ray)) = -∑ ρ ∈ W.base, W.coeff ρ * D ρ := by
    rw [W.relation, map_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    rw [map_smul, smul_eq_mul, hm ρ (W.base_le ρ hρ), mul_neg]
  rw [h, WallData.degree]
  ring

/-- The degree of `D` on the wall is `m_σ(u_ρ') - φ(u_ρ')`, where `φ` is a support function of `D` and `m_σ` is a linear form that agrees with `φ` on `σ`. -/
theorem degree_eq_sub {D : F.TDivisor ℝ} {φ : NR n → ℝ} (hφ : F.IsSupportFunctionOf D φ)
    {m : NR n →ₗ[ℝ] ℝ} (hm : ∀ x ∈ σ, φ x = m x) :
    W.degree D = m (toNR (F.generator W.ray)) - φ (toNR (F.generator W.ray)) := by
  rw [W.degree_eq (m := m) fun ρ hρ => by rw [← hm _ (hρ (F.toNR_generator_mem ρ)), hφ.2 ρ],
    hφ.2 W.ray]
  ring

/-- The degree of a divisor on a wall is nonnegative exactly when its support function satisfies the wall inequality across the wall (Cox, Little and Schenck, Sections 6.3 and 6.4). -/
theorem degree_nonneg_iff (hσ : σ ∈ F.cones) (hσ' : σ' ∈ F.cones) {D : F.TDivisor ℝ}
    {φ : NR n → ℝ} (hφ : F.IsSupportFunctionOf D φ) :
    0 ≤ W.degree D ↔ IsConvexAcross φ σ σ' := by
  constructor
  · intro h m' hm' x hx
    obtain ⟨m'', hm''⟩ := hφ.1 σ' hσ'
    rw [hm'' x hx]
    refine le_of_mem_hull ?_ ((F.eq_hull_generator hσ').le hx)
    rintro _ ⟨ρ, hρ, rfl⟩
    have hu := hρ (F.toNR_generator_mem ρ)
    rcases W.eq_or_le ρ hρ with rfl | hle
    · rw [← hm'' _ hu]
      have := W.degree_eq_sub hφ hm'
      linarith
    · rw [← hm'' _ hu, hm' _ (hle (F.toNR_generator_mem ρ))]
  · intro h
    obtain ⟨m, hm⟩ := hφ.1 σ hσ
    rw [W.degree_eq_sub hφ hm, sub_nonneg]
    exact h m hm _ (W.ray_le (F.toNR_generator_mem W.ray))

end WallData

end Fan

end MinimalModel.Toric
