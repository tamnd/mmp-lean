/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import MinimalModel.Toric.Fan

/-!
# Torus-invariant divisors

The second step of route R3 (spec 04.4) starts here. Each ray `ρ` of a fan gives a torus-invariant prime divisor `D_ρ` of the toric variety. A torus-invariant divisor is a finite sum `Σ a_ρ D_ρ`. So we model it as a function from the rays to the coefficients. The toric canonical divisor is `K = -Σ D_ρ`. The definitions follow Cox, Little and Schenck, Sections 4.1 and 8.2.

This file works with the fan only. The comparison with the divisors of the scheme `X_Σ` is step 9 of the route.
-/

namespace MinimalModel.Toric

variable {n : ℕ}

/-- A ray: the cone spanned by one nonzero lattice point. -/
def IsRay (ρ : PointedCone ℝ (NR n)) : Prop :=
  ∃ v : Fin n → ℤ, v ≠ 0 ∧ ρ = latticeCone {v}

/-- A ray is not the zero cone. -/
theorem IsRay.ne_bot {ρ : PointedCone ℝ (NR n)} (h : IsRay ρ) : ρ ≠ ⊥ := by
  obtain ⟨v, hv, rfl⟩ := h
  intro h0
  have hmem : toNR v ∈ latticeCone {v} := toNR_mem_latticeCone (Finset.mem_singleton_self v)
  rw [h0, Submodule.mem_bot] at hmem
  exact toNR_ne_zero hv hmem

namespace Fan

variable (F : Fan n)

/-- The rays of a fan: its cones of dimension one. This is the set `Σ(1)` of Cox, Little and Schenck. -/
def rays : Set (PointedCone ℝ (NR n)) := {ρ | ρ ∈ F.cones ∧ IsRay ρ}

/-- The type of the rays of a fan. -/
abbrev Ray := ↥F.rays

/-- Each ray of a fan is a cone of the fan. -/
theorem rays_subset : F.rays ⊆ F.cones := fun _ h => h.1

/-- A fan has finitely many rays. -/
theorem rays_finite : F.rays.Finite := F.finite.subset F.rays_subset

instance : Finite F.Ray := F.rays_finite.to_subtype

noncomputable instance : Fintype F.Ray := Fintype.ofFinite _

/-- A torus-invariant divisor with coefficients in `R`: a formal sum `Σ a_ρ D_ρ` over the rays `ρ` of the fan. -/
abbrev TDivisor (R : Type*) [Zero R] := F.Ray →₀ R

/-- The torus-invariant prime divisor `D_ρ` of a ray `ρ`. -/
noncomputable def primeDivisor (ρ : F.Ray) : F.TDivisor ℤ := Finsupp.single ρ 1

/-- The coefficient of `D_ρ` at the ray `ρ'` is `1` when `ρ' = ρ`, and `0` otherwise. -/
theorem primeDivisor_apply [DecidableEq F.Ray] (ρ ρ' : F.Ray) :
    F.primeDivisor ρ ρ' = if ρ = ρ' then 1 else 0 := by
  rw [primeDivisor, Finsupp.single_apply]

/-- A torus-invariant divisor with integer coefficients as a divisor with real coefficients. -/
noncomputable def TDivisor.toReal : F.TDivisor ℤ →+ F.TDivisor ℝ :=
  Finsupp.mapRange.addMonoidHom (Int.castAddHom ℝ)

/-- The coefficients of the real divisor are the integer coefficients. -/
@[simp]
theorem TDivisor.toReal_apply (D : F.TDivisor ℤ) (ρ : F.Ray) :
    TDivisor.toReal F D ρ = (D ρ : ℝ) := by
  simp [TDivisor.toReal]

/-- The toric canonical divisor `K = -Σ D_ρ`, the sum over all the rays of the fan. -/
noncomputable def canonical : F.TDivisor ℤ := -∑ ρ : F.Ray, F.primeDivisor ρ

/-- Each coefficient of the toric canonical divisor is `-1`. -/
@[simp]
theorem canonical_apply (ρ : F.Ray) : F.canonical ρ = -1 := by
  classical
  simp [canonical, Finsupp.finsetSum_apply, primeDivisor_apply]

/-- The toric canonical divisor as a divisor with real coefficients. -/
noncomputable def canonicalReal : F.TDivisor ℝ := TDivisor.toReal F F.canonical

/-- Each coefficient of the real toric canonical divisor is `-1`. -/
@[simp]
theorem canonicalReal_apply (ρ : F.Ray) : F.canonicalReal ρ = -1 := by
  simp [canonicalReal]

/-- The sum of the coefficients of a torus-invariant divisor. -/
noncomputable def coeffSum (D : F.TDivisor ℤ) : ℤ := ∑ ρ : F.Ray, D ρ

/-- The sum of the coefficients of `K` is minus the number of rays. -/
theorem coeffSum_canonical : F.coeffSum F.canonical = -(Nat.card F.Ray : ℤ) := by
  simp [coeffSum, Nat.card_eq_fintype_card]

/-- The trivial fan has no rays. -/
theorem rays_trivial : (trivial n).rays = ∅ := by
  ext ρ
  simp only [rays, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro hρ hr
  exact hr.ne_bot hρ

end Fan

end MinimalModel.Toric
