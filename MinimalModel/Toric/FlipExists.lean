/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import MinimalModel.Toric.FlipStep

/-!
# Toric flips, part 10: the side of `F` and the existence of flips

This file finishes step 5 of the route to `flipExists` in `MinimalModel/Toric/Flip.lean` (route R3, spec 04.4): the side of the fan `F` in the step `IsToricStep`, and the existence of the flip (Reid 1983, Sections 2 and 3, Theorem 3.4; Matsuki, Proposition 14-2-5; Cox, Little and Schenck, Theorems 15.3.13 and 15.4.3).

Let `F` be a complete simplicial fan, `R` an extremal ray of its cone of curves, `c` the class of a wall curve in `R`, and `G` the contraction fan, with `J₋` not empty. Let `ν` be a maximal cone of `F` in the star of `cone(u_{J₋})`, and `K_ν = cone(u_S)` its cone of `G`, with `S` the rays of `ν` and of the circuit.

## The maximal cones of `F` over a cone of the contraction

For `k ∈ J₊` the cone `Fan.flipCone c ν k = cone(u_{S ∖ {k}})` is a maximal cone of `F`: it is `ν` for the ray of `J₊` outside `ν`, and the neighbour of `ν` across the facet opposite `k` for another ray (`Fan.IsExtremalRay.isMaximalCone_flipCone_of_pos`). These cones cover `K_ν` (`Fan.exists_mem_flipCone_of_pos`, the same computation as for `J₋` with the signs exchanged). Conversely, let `σ` be a maximal cone of `F` in `K_ν`. The supporting divisor of `R` is linear on `K_ν`, so it is linear on `σ` and at the generators of the rays of `J₋`; so `σ` contains `cone(u_{J₋})` (`Fan.IsRaySupport.negCone_le_of_eq`), it misses one ray `k ∈ J₊` of the circuit, and it is `Fan.flipCone c ν k` by maximality (`Fan.IsExtremalRay.exists_eq_flipCone_of_pos`).

## Ampleness and relative Picard number one

The computation of part 9 with the relation `-c` gives that `-D` is ample over `G` when `D · c < 0` (`Fan.IsExtremalRay.isAmpleOver_contractionFan`). A divisor `D` with `D · c = 0` is a pullback from `G`: the linear form `m` of its support function on `ν` satisfies `c_j (m(u_j) + D_j) = D · c = 0` for the ray `j ∈ J₊` outside `ν`, so `m(u_ρ) = -D_ρ` on all of `S`, and the linear forms of the cones `cone(u_{S ∖ {k}})` agree with `m` on `K_ν` (`Fan.IsExtremalRay.isPullback_of_degree_eq_zero`). A divisor with `D · c ≠ 0` is not a pullback, since a linear form `m` with `m(u_ρ) = -D_ρ` on the circuit gives `D · c = -Σ c_ρ m(u_ρ) = 0` (`Fan.IsExtremalRay.not_isPullback`). So `F` has relative Picard number one over `G` (`Fan.IsExtremalRay.hasRelPicardOne_contractionFan`): `D - (D · c / D₀ · c) D₀` is a pullback.

## Main results

* `Fan.IsExtremalRay.exists_eq_flipCone_of_pos`: the maximal cones of `F` in a cone `K_ν` of the star are the cones `Fan.flipCone c ν k` with `k ∈ J₊`.
* `Fan.IsExtremalRay.isAmpleOver_contractionFan`: `-D` is ample over the contraction fan when `D · c < 0`.
* `Fan.IsExtremalRay.hasRelPicardOne_contractionFan`: `F` has relative Picard number one over the contraction fan.
* `Fan.IsExtremalRay.flipExists`: **the existence of toric flips.** When `D · c < 0` and `J₋` has two rays, the flipped fan with the strict transform of `D` is a toric step from `(F, D)`.
-/

namespace MinimalModel.Toric

variable {n : ℕ}

namespace Fan

variable {F : Fan n}

/-! ### The maximal cones of `F` over a cone of the contraction -/

/-- **The cones `cone(u_{S ∖ {k}})`, `k ∈ J₊`, cover the cones of the contraction.** A nonnegative combination `x = Σ b_ρ u_ρ` of the generators of the rays of `K_ν`, for `ν` in the star, is in `Fan.flipCone c ν k` for the ray `k ∈ J₊` that minimizes `b_ρ / c_ρ`: the coefficients `b - t c`, with `t = b_k / c_k`, are nonnegative and vanish at `k`. -/
theorem exists_mem_flipCone_of_pos (hs : F.IsSimplicialFan) {σ₀ σ₀' : PointedCone ℝ (NR n)}
    (hw₀ : F.IsWallPair σ₀ σ₀') (W₀ : F.WallData σ₀ σ₀') {ν : PointedCone ℝ (NR n)}
    (hneg : F.negCone W₀.curveClass ≤ ν) {k : F.Ray} (hk : 0 < W₀.curveClass k) {x : NR n}
    (hx : x ∈ F.contractCone W₀.curveClass ν) :
    ∃ j, 0 < W₀.curveClass j ∧ x ∈ F.flipCone W₀.curveClass ν j := by
  classical
  obtain ⟨b, hb0, hbP, rfl⟩ := (mem_hull_generator_iff (fun ρ : F.Ray => ρ.1 ≤ ν ∨
    (F.negCone W₀.curveClass ≤ ν ∧ W₀.curveClass ρ ≠ 0))).mp hx
  obtain ⟨j, hjS, hjmin⟩ := (Finset.univ.filter fun ρ => 0 < W₀.curveClass ρ).exists_min_image
    (fun ρ => b ρ / W₀.curveClass ρ) ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩⟩
  have hj : 0 < W₀.curveClass j := (Finset.mem_filter.mp hjS).2
  obtain ⟨t, htdef⟩ : ∃ t, t = b j / W₀.curveClass j := ⟨_, rfl⟩
  have ht0 : 0 ≤ t := by
    rw [htdef]
    exact div_nonneg (hb0 j) hj.le
  have htj : t * W₀.curveClass j = b j := by
    rw [htdef, div_mul_cancel₀ _ hj.ne']
  have hmin : ∀ ρ, 0 < W₀.curveClass ρ → t * W₀.curveClass ρ ≤ b ρ := fun ρ hρ => by
    have h1 : b j / W₀.curveClass j ≤ b ρ / W₀.curveClass ρ :=
      hjmin ρ (Finset.mem_filter.mpr ⟨Finset.mem_univ ρ, hρ⟩)
    rw [← htdef, le_div_iff₀ hρ] at h1
    exact h1
  refine ⟨j, hj, mem_indexCone.mpr
    ⟨fun ρ => b ρ - t * W₀.curveClass ρ, fun ρ => ?_, fun ρ hρ => ?_, ?_⟩⟩
  · show 0 ≤ b ρ - t * W₀.curveClass ρ
    by_cases hρ : 0 < W₀.curveClass ρ
    · linarith [hmin ρ hρ]
    · have h1 := mul_nonneg ht0 (neg_nonneg.mpr (not_lt.mp hρ))
      have h2 : t * -W₀.curveClass ρ = -(t * W₀.curveClass ρ) := by ring
      linarith [hb0 ρ]
  · show b ρ - t * W₀.curveClass ρ = 0
    by_contra h0
    apply hρ
    refine ⟨?_, fun _ hρj => ?_⟩
    · by_cases hcρ : W₀.curveClass ρ = 0
      · have hbρ : b ρ ≠ 0 := fun hb => h0 (by rw [hb, hcρ, mul_zero, sub_zero])
        exact not_not.mp fun hn => hbρ (hbP ρ hn)
      · exact Or.inr ⟨hneg, hcρ⟩
    · rw [hρj, htj, sub_self] at h0
      exact h0 rfl
  · have hrel := W₀.sum_curveClass_smul_generator hw₀.1.mem (hs σ₀ hw₀.1.mem)
    have hterm : ∀ ρ, (b ρ - t * W₀.curveClass ρ) • toNR (F.generator ρ) =
        b ρ • toNR (F.generator ρ) - t • (W₀.curveClass ρ • toNR (F.generator ρ)) :=
      fun ρ => by rw [sub_smul, mul_smul]
    show ∑ ρ, (b ρ - t * W₀.curveClass ρ) • toNR (F.generator ρ) = _
    simp only [hterm]
    rw [Finset.sum_sub_distrib, ← Finset.smul_sum, hrel, smul_zero, sub_zero]

variable {R : PointedCone ℝ (F.Ray → ℝ)}

/-- **The cones `cone(u_{S ∖ {k}})`, `k ∈ J₊`, are maximal cones of `F`.** For `ν` in the star and `k ∈ J₊`, the cone `Fan.flipCone c ν k` is `ν` when `k` is the ray of the circuit outside `ν`, and the neighbour of `ν` across the facet opposite `k` otherwise. -/
theorem IsExtremalRay.isMaximalCone_flipCone_of_pos (hc : F.IsComplete)
    (hs : F.IsSimplicialFan) (hR : F.IsExtremalRay R) {σ₀ σ₀' : PointedCone ℝ (NR n)}
    (hw₀ : F.IsWallPair σ₀ σ₀') (W₀ : F.WallData σ₀ σ₀') (hW₀ : W₀.curveClass ∈ R)
    {ν : PointedCone ℝ (NR n)} (hν : F.IsMaximalCone ν) (hneg : F.negCone W₀.curveClass ≤ ν)
    {k : F.Ray} (hk : 0 < W₀.curveClass k) :
    F.IsMaximalCone (F.flipCone W₀.curveClass ν k) := by
  obtain ⟨j, hj, hjν, hjr⟩ := hR.exists_ray_not_le hc hs hw₀ W₀ hW₀ hν hneg
  rw [flipCone_of_le hneg hk.ne']
  by_cases hkj : k = j
  · rw [hkj, ← eq_circuitCone_sup_linkCone hν.mem hjν hjr]
    exact hν
  · obtain ⟨σ'', hw, -, heq, -⟩ :=
      hR.exists_eq_circuitCone_sup_linkCone hc hs hw₀ W₀ hW₀ hν hneg hj hjν hjr hk hkj
    rw [← heq]
    exact hw.2.1

/-- **The maximal cones of `F` over a cone of the contraction.** A maximal cone `σ` of `F` in the cone `K_ν` of the contraction, for `ν` in the star, is a cone `Fan.flipCone c ν k` with `k ∈ J₊`. The supporting divisor of `R` is linear on `K_ν`, so `σ` contains `cone(u_{J₋})`; it misses a ray `k ∈ J₊` of the circuit, so it is in `Fan.flipCone c ν k`, and it is equal to it by maximality. -/
theorem IsExtremalRay.exists_eq_flipCone_of_pos (hc : F.IsComplete) (hs : F.IsSimplicialFan)
    (hR : F.IsExtremalRay R) {σ₀ σ₀' : PointedCone ℝ (NR n)} (hw₀ : F.IsWallPair σ₀ σ₀')
    (W₀ : F.WallData σ₀ σ₀') (hW₀ : W₀.curveClass ∈ R) {σ ν : PointedCone ℝ (NR n)}
    (hσ : F.IsMaximalCone σ) (hν : F.IsMaximalCone ν) (hneg : F.negCone W₀.curveClass ≤ ν)
    (hσν : σ ≤ F.contractCone W₀.curveClass ν) :
    ∃ k, 0 < W₀.curveClass k ∧ σ = F.flipCone W₀.curveClass ν k := by
  obtain ⟨D, φ, h⟩ := hR.exists_isRaySupport hc hs
  obtain ⟨m, hm⟩ := h.isSupportFunctionOf.1 ν hν.mem
  have hK : ∀ x ∈ F.contractCone W₀.curveClass ν, φ x = m x := fun x hx =>
    h.apply_eq_of_mem_contractCone hc hs hw₀ W₀ hW₀ hν hm hx
  have hnegσ : F.negCone W₀.curveClass ≤ σ := by
    by_contra hn
    obtain ⟨j, hj, hjσ⟩ : ∃ j : F.Ray, W₀.curveClass j < 0 ∧ ¬ j.1 ≤ σ := by
      by_contra hno
      push Not at hno
      exact hn (negCone_le_iff.mpr hno)
    exact hn (h.negCone_le_of_eq hc hs hR hw₀ W₀ hW₀ hσ (fun x hx => hK x (hσν hx))
      (hK _ (Submodule.subset_span ⟨j, Or.inr ⟨hneg, hj.ne⟩, rfl⟩)) hjσ).1
  obtain ⟨k, hk, hkσ, -⟩ := hR.exists_ray_not_le hc hs hw₀ W₀ hW₀ hσ hnegσ
  have hle : σ ≤ F.flipCone W₀.curveClass ν k := by
    refine (F.eq_hull_generator hσ.mem).trans_le (Submodule.span_le.mpr ?_)
    rintro _ ⟨ρ, hρ, rfl⟩
    have hρS : ρ ∈ F.flipRays W₀.curveClass ν k :=
      ⟨(hR.generator_mem_contractCone_iff hc hs hw₀ W₀ hW₀ hν).mp
        (hσν (hρ (F.toNR_generator_mem ρ))), fun _ hρk => hkσ (by rw [← hρk]; exact hρ)⟩
    exact mem_indexCone_of_mem (fun ρ : F.Ray => toNR (F.generator ρ)) hρS
  exact ⟨k, hk, le_antisymm hle
    (hσ.le_of_le (hR.isMaximalCone_flipCone_of_pos hc hs hw₀ W₀ hW₀ hν hneg hk).mem hle)⟩

/-- The support function of a divisor `D` is given on the cone `Fan.flipCone c ν k`, for `ν` in the star and `k ∈ J₊`, by a linear form `m` with `m(u_ρ) = -D_ρ` on the rays of the cone. -/
theorem IsExtremalRay.exists_linearMap_flipCone_of_pos (hc : F.IsComplete)
    (hs : F.IsSimplicialFan) (hR : F.IsExtremalRay R) {σ₀ σ₀' : PointedCone ℝ (NR n)}
    (hw₀ : F.IsWallPair σ₀ σ₀') (W₀ : F.WallData σ₀ σ₀') (hW₀ : W₀.curveClass ∈ R)
    {D : F.TDivisor ℝ} {φ : NR n → ℝ} (hφ : F.IsSupportFunctionOf D φ)
    {ν : PointedCone ℝ (NR n)} (hν : F.IsMaximalCone ν) (hneg : F.negCone W₀.curveClass ≤ ν)
    {k : F.Ray} (hk : 0 < W₀.curveClass k) :
    ∃ m : NR n →ₗ[ℝ] ℝ, (∀ x ∈ F.flipCone W₀.curveClass ν k, φ x = m x) ∧
      ∀ ρ ∈ F.flipRays W₀.curveClass ν k, m (toNR (F.generator ρ)) = -D ρ := by
  obtain ⟨m, hm⟩ := hφ.1 _ (hR.isMaximalCone_flipCone_of_pos hc hs hw₀ W₀ hW₀ hν hneg hk).mem
  refine ⟨m, hm, fun ρ hρ => ?_⟩
  rw [← hm _ (mem_indexCone_of_mem (fun ρ : F.Ray => toNR (F.generator ρ)) hρ)]
  exact hφ.2 ρ

/-! ### The side of `F` in the step -/

/-- **`-D` is ample over the contraction** (Reid 1983, Section 2). Let `D` be a divisor with `D · c < 0`, where `c` is the class of a wall curve in `R`. Then `-D` has a support function that is strictly convex on each cone of the contraction fan `G`, at each maximal cone of `F` in it. -/
theorem IsExtremalRay.isAmpleOver_contractionFan (hc : F.IsComplete) (hs : F.IsSimplicialFan)
    (hR : F.IsExtremalRay R) {σ₀ σ₀' : PointedCone ℝ (NR n)} (hw₀ : F.IsWallPair σ₀ σ₀')
    (W₀ : F.WallData σ₀ σ₀') (hW₀ : W₀.curveClass ∈ R) (hJ : ∃ k, W₀.curveClass k < 0)
    {D : F.TDivisor ℝ} (hD : W₀.degree D < 0) :
    F.IsAmpleOver (hR.contractionFan hc hs hw₀ W₀ hW₀ hJ).cones (-D) := by
  obtain ⟨φ, hφ⟩ := (hs.isRCartier (-D)).exists_isSupportFunctionOf
  refine ⟨φ, hφ, ?_⟩
  rintro τ ⟨ν, hν, hτ⟩ σ hσ hστ
  by_cases hneg : F.negCone W₀.curveClass ≤ ν
  · obtain ⟨k, hk, rfl⟩ :=
      hR.exists_eq_flipCone_of_pos hc hs hw₀ W₀ hW₀ hσ hν hneg (hστ.trans hτ.le)
    obtain ⟨m, hm, hmD⟩ := hR.exists_linearMap_flipCone_of_pos hc hs hw₀ W₀ hW₀ hφ hν hneg hk
    refine ⟨m, hm, fun x hx hxσ => ?_⟩
    obtain ⟨k', hk', hxk'⟩ := exists_mem_flipCone_of_pos hs hw₀ W₀ hneg hk (hτ.le hx)
    obtain ⟨m', hm', hm'D⟩ :=
      hR.exists_linearMap_flipCone_of_pos hc hs hw₀ W₀ hW₀ hφ hν hneg hk'
    rw [hm' x hxk']
    have hrel : ∑ ρ, (-W₀.curveClass ρ) • toNR (F.generator ρ) = 0 := by
      simp only [neg_smul, Finset.sum_neg_distrib,
        W₀.sum_curveClass_smul_generator hw₀.1.mem (hs σ₀ hw₀.1.mem), neg_zero]
    have hd : ∑ ρ, -W₀.curveClass ρ * (-D) ρ < 0 := by
      rw [W₀.degree_eq_sum_curveClass] at hD
      simpa only [Finsupp.coe_neg, Pi.neg_apply, neg_mul_neg] using hD
    exact (apply_le_of_relation (v := fun ρ : F.Ray => toNR (F.generator ρ))
      (c := fun ρ => -W₀.curveClass ρ) (D := fun ρ => (-D) ρ) hrel hd (neg_lt_zero.mpr hk)
      (S := F.flipRays W₀.curveClass ν k) (T := F.flipRays W₀.curveClass ν k')
      (fun ρ h0 hρk => ⟨Or.inr ⟨hneg, neg_ne_zero.mp h0⟩, fun _ => hρk⟩)
      (fun ρ hρ hρk => ⟨hρ.1, fun _ => hρk⟩) hmD hm'D hxk').2 hxσ
  · have hσν : σ ≤ ν := by
      rw [← contractCone_of_not_le hν.mem hneg]
      exact hστ.trans hτ.le
    have hνσ : ν ≤ σ := hσ.le_of_le hν.mem hσν
    obtain ⟨m, hm⟩ := hφ.1 σ hσ.mem
    refine ⟨m, hm, fun x hx hxσ => absurd (hνσ ?_) hxσ⟩
    have hxν := hτ.le hx
    rwa [contractCone_of_not_le hν.mem hneg] at hxν

/-- **A divisor of degree zero on `R` is a pullback from the contraction.** Let `D` be a divisor with `D · c = 0`. Its support function is linear on each cone `K_ν` of the contraction: the linear form `m` of `ν` satisfies `m(u_ρ) = -D_ρ` at each ray of `K_ν`, by the relation, and so does the linear form of each cone `Fan.flipCone c ν k` with `k ∈ J₊`, and these cones cover `K_ν`. -/
theorem IsExtremalRay.isPullback_of_degree_eq_zero (hc : F.IsComplete)
    (hs : F.IsSimplicialFan) (hR : F.IsExtremalRay R) {σ₀ σ₀' : PointedCone ℝ (NR n)}
    (hw₀ : F.IsWallPair σ₀ σ₀') (W₀ : F.WallData σ₀ σ₀') (hW₀ : W₀.curveClass ∈ R)
    (hJ : ∃ k, W₀.curveClass k < 0) {D : F.TDivisor ℝ} (hD : W₀.degree D = 0) :
    F.IsPullback (hR.contractionFan hc hs hw₀ W₀ hW₀ hJ).cones D := by
  obtain ⟨φ, hφ⟩ := (hs.isRCartier D).exists_isSupportFunctionOf
  refine ⟨φ, hφ, ?_⟩
  rintro τ ⟨ν, hν, hτ⟩
  obtain ⟨m, hm⟩ := hφ.1 ν hν.mem
  refine ⟨m, fun x hx => ?_⟩
  have hxK := hτ.le hx
  by_cases hneg : F.negCone W₀.curveClass ≤ ν
  · obtain ⟨j, hj, -, hjr⟩ := hR.exists_ray_not_le hc hs hw₀ W₀ hW₀ hν hneg
    have hmν : ∀ ρ ∈ {ρ : F.Ray | ρ.1 ≤ ν}, m (toNR (F.generator ρ)) = -D ρ := fun ρ hρ => by
      rw [← hm _ (hρ (F.toNR_generator_mem ρ))]
      exact hφ.2 ρ
    have hmj : m (toNR (F.generator j)) = -D j := by
      have hrel := W₀.sum_curveClass_smul_generator hw₀.1.mem (hs σ₀ hw₀.1.mem)
      have h := mul_apply_add_eq_of_relation hrel (S := {ρ : F.Ray | ρ.1 ≤ ν}) (j := j)
        (fun ρ h0 hρj => hjr ρ h0 hρj) hmν
      rw [← W₀.degree_eq_sum_curveClass, hD] at h
      have h' := (mul_eq_zero.mp h).resolve_left hj.ne'
      linarith
    have hmS : ∀ ρ : F.Ray, (ρ.1 ≤ ν ∨ (F.negCone W₀.curveClass ≤ ν ∧ W₀.curveClass ρ ≠ 0)) →
        m (toNR (F.generator ρ)) = -D ρ := by
      rintro ρ (hρ | ⟨-, h0⟩)
      · exact hmν ρ hρ
      · by_cases hρj : ρ = j
        · rw [hρj]
          exact hmj
        · exact hmν ρ (hjr ρ h0 hρj)
    obtain ⟨k, hk, hxk⟩ := exists_mem_flipCone_of_pos hs hw₀ W₀ hneg hj hxK
    obtain ⟨m', hm', hm'D⟩ := hR.exists_linearMap_flipCone_of_pos hc hs hw₀ W₀ hW₀ hφ hν hneg hk
    rw [hm' x hxk]
    obtain ⟨b, -, hbT, rfl⟩ := mem_indexCone.mp hxk
    simp only [map_sum, map_smul, smul_eq_mul]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    by_cases hρ : ρ ∈ F.flipRays W₀.curveClass ν k
    · rw [hm'D ρ hρ, hmS ρ hρ.1]
    · rw [hbT ρ hρ, zero_mul, zero_mul]
  · rw [contractCone_of_not_le hν.mem hneg] at hxK
    exact hm x hxK

/-- **A divisor of nonzero degree on `R` is not a pullback from the contraction.** A linear form `m` with `m(u_ρ) = -D_ρ` at the rays of the circuit, the rays of the cone `K_{σ₀}` of the contraction, gives `D · c = -Σ c_ρ m(u_ρ) = 0` by the relation of the circuit. -/
theorem IsExtremalRay.not_isPullback (hc : F.IsComplete) (hs : F.IsSimplicialFan)
    (hR : F.IsExtremalRay R) {σ₀ σ₀' : PointedCone ℝ (NR n)} (hw₀ : F.IsWallPair σ₀ σ₀')
    (W₀ : F.WallData σ₀ σ₀') (hW₀ : W₀.curveClass ∈ R) (hJ : ∃ k, W₀.curveClass k < 0)
    {D : F.TDivisor ℝ} (hD : W₀.degree D ≠ 0) :
    ¬ F.IsPullback (hR.contractionFan hc hs hw₀ W₀ hW₀ hJ).cones D := by
  rintro ⟨φ, hφ, hlin⟩
  have hneg : F.negCone W₀.curveClass ≤ σ₀ :=
    (W₀.negCone_curveClass_le_inf (hs σ₀ hw₀.1.mem) hw₀).trans inf_le_left
  obtain ⟨m, hm⟩ := hlin (F.contractCone W₀.curveClass σ₀) (by
    rw [hR.cones_contractionFan]
    exact ⟨σ₀, hw₀.1, PointedCone.IsFaceOf.refl _⟩)
  have hval : ∀ ρ : F.Ray, W₀.curveClass ρ ≠ 0 → m (toNR (F.generator ρ)) = -D ρ := by
    intro ρ hρ
    rw [← hm _ (Submodule.subset_span ⟨ρ, Or.inr ⟨hneg, hρ⟩, rfl⟩)]
    exact hφ.2 ρ
  have h2 : ∑ ρ, W₀.curveClass ρ * m (toNR (F.generator ρ)) = 0 := by
    have h := congrArg m (W₀.sum_curveClass_smul_generator hw₀.1.mem (hs σ₀ hw₀.1.mem))
    simpa only [map_sum, map_smul, smul_eq_mul, map_zero] using h
  have h3 : ∑ ρ, W₀.curveClass ρ * m (toNR (F.generator ρ)) =
      -∑ ρ, W₀.curveClass ρ * D ρ := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    by_cases h0 : W₀.curveClass ρ = 0
    · rw [h0, zero_mul, zero_mul, neg_zero]
    · rw [hval ρ h0]
      ring
  apply hD
  rw [W₀.degree_eq_sum_curveClass]
  linarith

/-- **Relative Picard number one** (Reid 1983, Section 2; Cox, Little and Schenck, Theorem 15.4.3). `F` has relative Picard number one over the contraction fan: a divisor `D₀` with `D₀ · c ≠ 0` is not a pullback, and for each divisor `D` the divisor `D - (D · c / D₀ · c) D₀` has degree zero on `R`, so it is a pullback. Each divisor is `ℝ`-Cartier, since `F` is simplicial. -/
theorem IsExtremalRay.hasRelPicardOne_contractionFan (hc : F.IsComplete)
    (hs : F.IsSimplicialFan) (hR : F.IsExtremalRay R) {σ₀ σ₀' : PointedCone ℝ (NR n)}
    (hw₀ : F.IsWallPair σ₀ σ₀') (W₀ : F.WallData σ₀ σ₀') (hW₀ : W₀.curveClass ∈ R)
    (hJ : ∃ k, W₀.curveClass k < 0) {D₀ : F.TDivisor ℝ} (hD₀ : W₀.degree D₀ ≠ 0) :
    F.HasRelPicardOne (hR.contractionFan hc hs hw₀ W₀ hW₀ hJ).cones := by
  refine ⟨D₀, hs.isRCartier D₀, hR.not_isPullback hc hs hw₀ W₀ hW₀ hJ hD₀, fun D _ =>
    ⟨W₀.degree D / W₀.degree D₀, hR.isPullback_of_degree_eq_zero hc hs hw₀ W₀ hW₀ hJ ?_⟩⟩
  have h1 : ∀ t : ℝ, W₀.degree (D - t • D₀) = W₀.degree D - t * W₀.degree D₀ := fun t => by
    rw [W₀.degree_eq_sum_curveClass, W₀.degree_eq_sum_curveClass, W₀.degree_eq_sum_curveClass,
      Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul]
    ring
  rw [h1, div_mul_cancel₀ _ hD₀, sub_self]

/-! ### The existence of flips -/

/-- **The existence of toric flips** (Reid 1983, Theorem 3.4; Matsuki, Proposition 14-2-5; Cox, Little and Schenck, Theorem 15.3.13). Let `F` be a complete simplicial fan, `R` an extremal ray of its cone of curves, `c` the class of a wall curve in `R`, and `D` a divisor with `D · c < 0`. Let `J₋` have two rays, so that the contraction of `R` is small. Then the flipped fan `F⁺` with the strict transform of `D` is a toric step from `(F, D)` over the contraction fan: `F` has relative Picard number one over it and `-D` is ample over it, and `F⁺` is simplicial, has the same rays, and the strict transform is ample over it. -/
theorem IsExtremalRay.flipExists (hc : F.IsComplete) (hs : F.IsSimplicialFan)
    (hR : F.IsExtremalRay R) {σ₀ σ₀' : PointedCone ℝ (NR n)} (hw₀ : F.IsWallPair σ₀ σ₀')
    (W₀ : F.WallData σ₀ σ₀') (hW₀ : W₀.curveClass ∈ R) {k k' : F.Ray}
    (hk : W₀.curveClass k < 0) (hk' : W₀.curveClass k' < 0) (hkk' : k ≠ k')
    {D : F.TDivisor ℝ} (hD : W₀.degree D < 0) :
    IsToricStep ⟨F, D⟩ ⟨hR.flippedFan hc hs hw₀ W₀ hW₀,
      strictTransform D _ (hR.rays_flippedFan hc hs hw₀ W₀ hW₀ hk hk' hkk').subset⟩ :=
  hR.isToricStep_flippedFan hc hs hw₀ W₀ hW₀ hk hk' hkk' hD
    (hR.hasRelPicardOne_contractionFan hc hs hw₀ W₀ hW₀ ⟨k, hk⟩ hD.ne)
    (hR.isAmpleOver_contractionFan hc hs hw₀ W₀ hW₀ ⟨k, hk⟩ hD)

/-- **The existence of toric flips**, as an existence statement: for a `D`-negative extremal ray of a complete simplicial fan whose `J₋` has two rays, there is a toric step from `(F, D)` to a model whose fan has the same rays as `F`. -/
theorem IsExtremalRay.exists_isToricStep (hc : F.IsComplete) (hs : F.IsSimplicialFan)
    (hR : F.IsExtremalRay R) {σ₀ σ₀' : PointedCone ℝ (NR n)} (hw₀ : F.IsWallPair σ₀ σ₀')
    (W₀ : F.WallData σ₀ σ₀') (hW₀ : W₀.curveClass ∈ R) {k k' : F.Ray}
    (hk : W₀.curveClass k < 0) (hk' : W₀.curveClass k' < 0) (hkk' : k ≠ k')
    {D : F.TDivisor ℝ} (hD : W₀.degree D < 0) :
    ∃ B : ToricModel n, IsToricStep ⟨F, D⟩ B ∧ B.F.rays = F.rays :=
  ⟨_, hR.flipExists hc hs hw₀ W₀ hW₀ hk hk' hkk' hD,
    hR.rays_flippedFan hc hs hw₀ W₀ hW₀ hk hk' hkk'⟩

end Fan

end MinimalModel.Toric
