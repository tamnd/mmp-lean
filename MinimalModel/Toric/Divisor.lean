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

/-- The primitive generator `u_ρ` of a ray `ρ`: the primitive lattice point of `ρ`. It spans `ρ`, and the lattice points of `ρ` are the multiples `k • u_ρ` with `k : ℕ` (`IsRay.toNR_mem_iff`), so `u_ρ` generates the semigroup `ρ ∩ N` as in Cox, Little and Schenck, Section 3.1. For a cone that is not a ray, the value is `0`. -/
noncomputable def rayGenerator (ρ : PointedCone ℝ (NR n)) : Fin n → ℤ :=
  open Classical in
  if h : IsRay ρ then primitivePart (Classical.choose h) else 0

/-- The primitive generator of a ray is primitive, and it spans the ray. -/
theorem IsRay.rayGenerator_spec {ρ : PointedCone ℝ (NR n)} (h : IsRay ρ) :
    IsPrimitive (rayGenerator ρ) ∧ latticeCone {rayGenerator ρ} = ρ := by
  obtain ⟨hv, hρ⟩ := Classical.choose_spec h
  have he : rayGenerator ρ = primitivePart (Classical.choose h) := by
    rw [rayGenerator, dite_eq_left h]
  rw [he]
  exact ⟨isPrimitive_primitivePart hv, (latticeCone_primitivePart hv).trans hρ.symm⟩

/-- The primitive generator of a ray is primitive. -/
theorem IsRay.isPrimitive_rayGenerator {ρ : PointedCone ℝ (NR n)} (h : IsRay ρ) :
    IsPrimitive (rayGenerator ρ) :=
  h.rayGenerator_spec.1

/-- The primitive generator of a ray spans the ray. -/
theorem IsRay.latticeCone_rayGenerator {ρ : PointedCone ℝ (NR n)} (h : IsRay ρ) :
    latticeCone {rayGenerator ρ} = ρ :=
  h.rayGenerator_spec.2

/-- The primitive generator of a ray is not zero. -/
theorem IsRay.rayGenerator_ne_zero {ρ : PointedCone ℝ (NR n)} (h : IsRay ρ) :
    rayGenerator ρ ≠ 0 :=
  h.isPrimitive_rayGenerator.ne_zero

/-- The primitive generator of a ray lies in the ray. -/
theorem IsRay.toNR_rayGenerator_mem {ρ : PointedCone ℝ (NR n)} (h : IsRay ρ) :
    toNR (rayGenerator ρ) ∈ ρ := by
  have hmem := toNR_mem_latticeCone (Finset.mem_singleton_self (rayGenerator ρ))
  rwa [h.latticeCone_rayGenerator] at hmem

/-- The lattice points of a ray `ρ` are the multiples `k • u_ρ` of its primitive generator, with `k : ℕ`. -/
theorem IsRay.toNR_mem_iff {ρ : PointedCone ℝ (NR n)} (h : IsRay ρ) {w : Fin n → ℤ} :
    toNR w ∈ ρ ↔ ∃ k : ℕ, w = k • rayGenerator ρ := by
  have hiff := h.isPrimitive_rayGenerator.toNR_mem_latticeCone_iff (w := w)
  rwa [h.latticeCone_rayGenerator] at hiff

/-- Uniqueness of the primitive generator: a primitive lattice point of a ray `ρ` is `u_ρ`. -/
theorem IsRay.eq_rayGenerator {ρ : PointedCone ℝ (NR n)} (h : IsRay ρ) {u : Fin n → ℤ}
    (hu : IsPrimitive u) (hρ : toNR u ∈ ρ) : u = rayGenerator ρ := by
  obtain ⟨k, hk⟩ := h.toNR_mem_iff.mp hρ
  exact hu.eq_of_eq_nsmul hk

/-- The cone of a primitive point `u` is a ray, and its primitive generator is `u`. -/
theorem rayGenerator_latticeCone {u : Fin n → ℤ} (hu : IsPrimitive u) :
    rayGenerator (latticeCone {u}) = u :=
  (IsRay.eq_rayGenerator ⟨u, hu.ne_zero, rfl⟩ hu
    (toNR_mem_latticeCone (Finset.mem_singleton_self u))).symm

/-- The linear form `x ↦ Σ cᵢ xᵢ` on `N_ℝ`, for a vector `c` of `M_ℝ = ℝⁿ`. -/
noncomputable def linearForm (c : Fin n → ℝ) : NR n →ₗ[ℝ] ℝ where
  toFun x := ∑ i, c i * x i
  map_add' x y := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' r x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

@[simp]
theorem linearForm_apply (c : Fin n → ℝ) (x : NR n) : linearForm c x = ∑ i, c i * x i := rfl

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

/-- A cone is a ray of the fan when it is a cone of the fan and a ray. -/
theorem mem_rays {ρ : PointedCone ℝ (NR n)} : ρ ∈ F.rays ↔ ρ ∈ F.cones ∧ IsRay ρ := Iff.rfl

/-- Each ray of the fan is a ray. -/
theorem isRay (ρ : F.Ray) : IsRay ρ.1 := ρ.2.2

/-- The primitive generator `u_ρ` of a ray `ρ` of the fan. -/
noncomputable def generator (ρ : F.Ray) : Fin n → ℤ := rayGenerator ρ.1

/-- The primitive generator of a ray of the fan is primitive. -/
theorem isPrimitive_generator (ρ : F.Ray) : IsPrimitive (F.generator ρ) :=
  (F.isRay ρ).isPrimitive_rayGenerator

/-- The primitive generator of a ray of the fan spans the ray. -/
theorem latticeCone_generator (ρ : F.Ray) : latticeCone {F.generator ρ} = ρ.1 :=
  (F.isRay ρ).latticeCone_rayGenerator

/-- The primitive generator of a ray of the fan lies in the ray. -/
theorem toNR_generator_mem (ρ : F.Ray) : toNR (F.generator ρ) ∈ ρ.1 :=
  (F.isRay ρ).toNR_rayGenerator_mem

/-- The primitive generator of a ray of the fan is the only primitive lattice point of the ray. -/
theorem eq_generator (ρ : F.Ray) {u : Fin n → ℤ} (hu : IsPrimitive u) (hρ : toNR u ∈ ρ.1) :
    u = F.generator ρ :=
  (F.isRay ρ).eq_rayGenerator hu hρ

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
  simp [canonical, primeDivisor_apply]

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

/-! ### The Cartier and Q-Cartier conditions

The pairing of `M = ℤⁿ` and `N = ℤⁿ` is `⟨m, u⟩ = Σ mᵢ uᵢ`. The conditions below are stated on the fan, with the primitive generators of the rays. -/

/-- A torus-invariant divisor `D = Σ a_ρ D_ρ` is Cartier: for each cone `σ` of the fan there is `m_σ ∈ M` with `⟨m_σ, u_ρ⟩ = -a_ρ` for each ray `ρ` of `σ`. This is the criterion of Cox, Little and Schenck, Theorem 4.2.8. We take it as the definition, since this file works with the fan only. -/
def IsCartier (D : F.TDivisor ℤ) : Prop :=
  ∀ σ ∈ F.cones, ∃ m : Fin n → ℤ, ∀ ρ : F.Ray, ρ.1 ≤ σ → ∑ i, m i * F.generator ρ i = -D ρ

/-- A torus-invariant divisor is Q-Cartier when a positive multiple of it is Cartier (Cox, Little and Schenck, Section 4.2). -/
def IsQCartier (D : F.TDivisor ℤ) : Prop :=
  ∃ k : ℕ, 0 < k ∧ F.IsCartier (k • D)

/-- A torus-invariant divisor with real coefficients `D = Σ a_ρ D_ρ` satisfies the criterion of Theorem 4.2.8 over `ℝ`: for each cone `σ` there is a linear form `m_σ` on `N_ℝ` with `m_σ(u_ρ) = -a_ρ` for each ray `ρ` of `σ`. -/
def IsRCartier (D : F.TDivisor ℝ) : Prop :=
  ∀ σ ∈ F.cones, ∃ m : NR n →ₗ[ℝ] ℝ, ∀ ρ : F.Ray, ρ.1 ≤ σ → m (toNR (F.generator ρ)) = -D ρ

/-- A support function of the fan: a function on `N_ℝ` that is linear on each cone of the fan (Cox, Little and Schenck, Definition 4.2.11, with real values). Only its values on the support `|Σ|` matter. -/
def IsSupportFunction (φ : NR n → ℝ) : Prop :=
  ∀ σ ∈ F.cones, ∃ m : NR n →ₗ[ℝ] ℝ, ∀ x ∈ σ, φ x = m x

/-- `φ` is a support function of `D = Σ a_ρ D_ρ`: it is a support function of the fan, and `φ(u_ρ) = -a_ρ` for each ray `ρ` (Cox, Little and Schenck, Theorem 4.2.12). -/
def IsSupportFunctionOf (D : F.TDivisor ℝ) (φ : NR n → ℝ) : Prop :=
  F.IsSupportFunction φ ∧ ∀ ρ : F.Ray, φ (toNR (F.generator ρ)) = -D ρ

variable {F}

/-- A Cartier divisor is Q-Cartier. -/
theorem IsCartier.isQCartier {D : F.TDivisor ℤ} (h : F.IsCartier D) : F.IsQCartier D :=
  ⟨1, one_pos, by rwa [one_smul]⟩

/-- A torus-invariant divisor is Q-Cartier when, for each cone `σ`, there is `m_σ ∈ M_ℚ` with `⟨m_σ, u_ρ⟩ = -a_ρ` for each ray `ρ` of `σ`. -/
theorem isQCartier_iff {D : F.TDivisor ℤ} : F.IsQCartier D ↔
    ∀ σ ∈ F.cones, ∃ m : Fin n → ℚ, ∀ ρ : F.Ray, ρ.1 ≤ σ →
      ∑ i, m i * (F.generator ρ i : ℚ) = -(D ρ : ℚ) := by
  constructor
  · rintro ⟨k, hk, h⟩ σ hσ
    obtain ⟨m, hm⟩ := h σ hσ
    have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
    refine ⟨fun i => (m i : ℚ) / k, fun ρ hρ => ?_⟩
    have h1 := congrArg (Int.cast : ℤ → ℚ) (hm ρ hρ)
    rw [Finsupp.smul_apply, nsmul_eq_mul] at h1
    push_cast at h1
    calc ∑ i, (m i : ℚ) / k * (F.generator ρ i : ℚ)
        = (∑ i, (m i : ℚ) * (F.generator ρ i : ℚ)) / k := by
          rw [Finset.sum_div]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = -(D ρ : ℚ) := by rw [h1, neg_div, mul_div_cancel_left₀ _ hk']
  · intro h
    choose! m hm using h
    obtain ⟨k, hk, hdvd⟩ : ∃ k : ℕ, 0 < k ∧ ∀ σ ∈ F.cones, ∀ i, (m σ i).den ∣ k :=
      ⟨∏ σ ∈ F.finite.toFinset, ∏ i, (m σ i).den,
        Finset.prod_pos fun σ _ => Finset.prod_pos fun i _ => (m σ i).den_pos,
        fun σ hσ i => (Finset.dvd_prod_of_mem (fun i => (m σ i).den) (Finset.mem_univ i)).trans
          (Finset.dvd_prod_of_mem (fun σ => ∏ i, (m σ i).den) (F.finite.mem_toFinset.mpr hσ))⟩
    have hint : ∀ σ ∈ F.cones, ∀ i, ∃ z : ℤ, (z : ℚ) = k * m σ i := by
      intro σ hσ i
      obtain ⟨c, hc⟩ := hdvd σ hσ i
      refine ⟨(c : ℤ) * (m σ i).num, ?_⟩
      rw [hc]
      push_cast
      linear_combination (-(c : ℚ)) * Rat.den_mul_eq_num (m σ i)
    refine ⟨k, hk, fun σ hσ => ?_⟩
    choose z hz using hint σ hσ
    refine ⟨z, fun ρ hρ => ?_⟩
    rw [Finsupp.smul_apply, nsmul_eq_mul]
    have h1 := hm σ hσ ρ hρ
    have h2 : ((∑ i, z i * F.generator ρ i : ℤ) : ℚ) = ((-((k : ℤ) * D ρ) : ℤ) : ℚ) := by
      push_cast
      simp_rw [hz]
      rw [← mul_neg, ← h1, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    exact_mod_cast h2

/-- A Q-Cartier divisor satisfies the criterion over `ℝ`. -/
theorem IsQCartier.isRCartier {D : F.TDivisor ℤ} (h : F.IsQCartier D) :
    F.IsRCartier (TDivisor.toReal F D) := by
  intro σ hσ
  obtain ⟨m, hm⟩ := isQCartier_iff.mp h σ hσ
  refine ⟨linearForm fun i => (m i : ℝ), fun ρ hρ => ?_⟩
  have h1 := congrArg (Rat.cast : ℚ → ℝ) (hm ρ hρ)
  push_cast at h1
  simpa using h1

/-- A divisor with a support function satisfies the criterion over `ℝ`: on each cone `σ`, the linear form of the support function takes the value `-a_ρ` at `u_ρ` for each ray `ρ` of `σ`. -/
theorem IsSupportFunctionOf.isRCartier {D : F.TDivisor ℝ} {φ : NR n → ℝ}
    (h : F.IsSupportFunctionOf D φ) : F.IsRCartier D := by
  intro σ hσ
  obtain ⟨m, hm⟩ := h.1 σ hσ
  exact ⟨m, fun ρ hρ => by rw [← hm _ (hρ (F.toNR_generator_mem ρ)), h.2 ρ]⟩

variable (F)

/-- The trivial fan has no rays. -/
theorem rays_trivial : (trivial n).rays = ∅ := by
  ext ρ
  simp only [rays, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro hρ hr
  exact hr.ne_bot hρ

end Fan

end MinimalModel.Toric
