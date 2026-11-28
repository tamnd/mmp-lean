/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import MinimalModel.Toric.FlipFlipped

/-!
# Toric flips, part 9: the strict transform is ample over the base

This file starts step 5 of the route to `flipExists` in `MinimalModel/Toric/Flip.lean` (route R3, spec 04.4): the side of the flipped fan `F⁺` in the step `IsToricStep` (Reid 1983, Theorem 3.4; Matsuki, Proposition 14-2-5; Cox, Little and Schenck, Theorem 15.3.13).

Let `F` be a complete simplicial fan, `R` an extremal ray of its cone of curves, `c` the class of a wall curve in `R`, and `D` a divisor with `D · c < 0`. Let `G` be the contraction fan and `F⁺` the flipped fan. The strict transform `Fan.strictTransform D F⁺ h` has the coefficients of `D` on the same rays.

## The sign of the degree changes

Let `ν` be a maximal cone of `F` in the star of `cone(u_{J₋})`, and `K_ν` its cone of `G`, spanned by the generators of a set `S` of rays with `Σ_{ρ ∈ S} c_ρ u_ρ = 0`. The maximal cones of `F⁺` in `K_ν` are the cones `cone(u_{S ∖ {j}})` with `j ∈ J₋`. Let `m_j` be the linear form of the support function of the strict transform on it: `m_j(u_ρ) = -D_ρ` for `ρ ≠ j`. Applying `m_j` to the relation gives `c_j (m_j(u_j) + D_j) = Σ c_ρ D_ρ = D · c` (`mul_apply_add_eq_of_relation`). So `m_j(u_j) + D_j > 0`: the degree of `D` on the flipped wall, `-(m_j(u_j) + D_j)` up to the positive factor `1 / |c_j|`, has the sign opposite to `D · c`. This is the circuit relation with the signs of `J₊` and `J₋` exchanged.

For `x = Σ b_ρ u_ρ` in another cone `cone(u_{S ∖ {j'}})`, with `b ≥ 0`, the two forms differ only at `j`: `m_j(x) - m_{j'}(x) = b_j (m_j(u_j) + D_j) ≥ 0`, and the difference is positive unless `b_j = 0`, that is unless `x ∈ cone(u_{S ∖ {j}})` (`apply_le_of_relation`). Since these cones cover `K_ν` (`Fan.exists_mem_flipCone`), the support function of the strict transform is strictly below `m_j` on `K_ν` outside `cone(u_{S ∖ {j}})`. Off the star, `K_ν = ν` is a cone of `F⁺` and there is nothing to prove. So the strict transform is ample over `G` (`Fan.IsExtremalRay.isAmpleOver_flippedFan`).

## Main results

* `Fan.strictTransform`: the strict transform of a divisor to a fan whose rays are rays of `F`.
* `Fan.IsExtremalRay.exists_eq_flipCone`: a maximal cone of `F⁺` in a cone `K_ν` of `G` is a cone `Fan.flipCone c ν j` with `j ∈ J₋`.
* `Fan.IsExtremalRay.isAmpleOver_flippedFan`: the strict transform of a divisor `D` with `D · c < 0` is ample over the contraction fan.
* `Fan.IsExtremalRay.isToricStep_flippedFan`: when `J₋` has two rays, `(F⁺, D⁺)` is a toric step from `(F, D)`, given the two conditions on the side of `F`: relative Picard number one over `G`, and `-D` ample over `G`.
-/

namespace MinimalModel.Toric

variable {n : ℕ}

section IndexCone

variable {ι E : Type*} [Fintype ι] [AddCommGroup E] [Module ℝ E]

/-- Let `Σ cᵢ vᵢ = 0`, and let `m` be a linear form with `m(vᵢ) = -Dᵢ` for each `i ∈ S`, where `S` contains each `i ≠ j` with `cᵢ ≠ 0`. Then `c_j (m(v_j) + D_j) = Σ cᵢ Dᵢ`. For the circuit of a wall and `j ∈ J₋`, the left side is the degree of `D` on the flipped wall up to a factor `-c_j`, and the right side is the degree on the wall. -/
theorem mul_apply_add_eq_of_relation {v : ι → E} {c D : ι → ℝ} (hrel : ∑ i, c i • v i = 0)
    {S : Set ι} {j : ι} (hS : ∀ i, c i ≠ 0 → i ≠ j → i ∈ S) {m : E →ₗ[ℝ] ℝ}
    (hm : ∀ i ∈ S, m (v i) = -D i) :
    c j * (m (v j) + D j) = ∑ i, c i * D i := by
  classical
  have h2 : ∑ i, c i * m (v i) = 0 := by
    have h := congrArg m hrel
    simpa only [map_sum, map_smul, smul_eq_mul, map_zero] using h
  have h3 : ∑ i, (c i * m (v i) + c i * D i) = c j * (m (v j) + D j) := by
    rw [Finset.sum_eq_single j (fun i _ hij => ?_) (fun h => absurd (Finset.mem_univ j) h)]
    · ring
    · by_cases hc : c i = 0
      · rw [hc]
        ring
      · rw [hm i (hS i hc hij)]
        ring
  rw [Finset.sum_add_distrib, h2, zero_add] at h3
  exact h3.symm

/-- **The sign of the degree changes.** Let `Σ cᵢ vᵢ = 0` with `Σ cᵢ Dᵢ < 0` and `c_j < 0`. Let `m` be a linear form with `m(vᵢ) = -Dᵢ` on a set `S` that contains each `i ≠ j` with `cᵢ ≠ 0`, and `m'` one with `m'(vᵢ) = -Dᵢ` on a set `T` with `T ∖ {j} ⊆ S`. Then `m' ≤ m` on the cone of `T`, with strict inequality outside the cone of `S`. -/
theorem apply_le_of_relation {v : ι → E} {c D : ι → ℝ} (hrel : ∑ i, c i • v i = 0)
    (hd : ∑ i, c i * D i < 0) {S T : Set ι} {j : ι} (hj : c j < 0)
    (hS : ∀ i, c i ≠ 0 → i ≠ j → i ∈ S) (hTS : ∀ i ∈ T, i ≠ j → i ∈ S)
    {m m' : E →ₗ[ℝ] ℝ} (hm : ∀ i ∈ S, m (v i) = -D i) (hm' : ∀ i ∈ T, m' (v i) = -D i)
    {x : E} (hx : x ∈ indexCone v T) :
    m' x ≤ m x ∧ (x ∉ indexCone v S → m' x < m x) := by
  classical
  obtain ⟨b, hb0, hbT, rfl⟩ := mem_indexCone.mp hx
  have he : 0 < m (v j) + D j := by
    have h := mul_apply_add_eq_of_relation hrel hS hm
    by_contra hle
    push_neg at hle
    nlinarith [mul_nonneg (neg_nonneg.mpr hj.le) (neg_nonneg.mpr hle)]
  have hdiff : m (∑ i, b i • v i) - m' (∑ i, b i • v i) = b j * (m (v j) + D j) := by
    simp only [map_sum, map_smul, smul_eq_mul]
    rw [← Finset.sum_sub_distrib,
      Finset.sum_eq_single j (fun i _ hij => ?_) (fun h => absurd (Finset.mem_univ j) h)]
    · by_cases hjT : j ∈ T
      · rw [hm' j hjT]
        ring
      · rw [hbT j hjT]
        ring
    · by_cases hiT : i ∈ T
      · rw [hm' i hiT, hm i (hTS i hiT hij)]
        ring
      · rw [hbT i hiT]
        ring
  refine ⟨?_, fun hxS => ?_⟩
  · nlinarith [mul_nonneg (hb0 j) he.le]
  · have hbj : 0 < b j := by
      refine lt_of_le_of_ne (hb0 j) fun h0 => hxS (mem_indexCone.mpr ⟨b, hb0, fun i hi => ?_, rfl⟩)
      by_contra hbi
      have hiT : i ∈ T := by
        by_contra hT
        exact hbi (hbT i hT)
      have hij : i ≠ j := by
        rintro rfl
        exact hbi h0.symm
      exact hi (hTS i hiT hij)
    nlinarith [mul_pos hbj he]

end IndexCone

namespace Fan

variable {F : Fan n}

/-! ### The strict transform of a divisor -/

/-- The strict transform of a divisor `D` of `F` to a fan `F'` whose rays are rays of `F`: the divisor of `F'` with the coefficient of `D` on each ray. -/
noncomputable def strictTransform (D : F.TDivisor ℝ) (F' : Fan n) (h : F'.rays ⊆ F.rays) :
    F'.TDivisor ℝ :=
  Finsupp.equivFunOnFinite.symm fun ρ => D ⟨ρ.1, h ρ.2⟩

/-- The coefficient of the strict transform on a ray is the coefficient of the divisor. -/
theorem strictTransform_apply (D : F.TDivisor ℝ) {F' : Fan n} (h : F'.rays ⊆ F.rays)
    (ρ : F'.Ray) : strictTransform D F' h ρ = D ⟨ρ.1, h ρ.2⟩ :=
  rfl

/-- The strict transform has the coefficient of the divisor on each ray that is the same cone. -/
theorem strictTransform_apply_of_eq (D : F.TDivisor ℝ) {F' : Fan n} (h : F'.rays ⊆ F.rays)
    {ρ' : F'.Ray} {ρ : F.Ray} (hρ : ρ'.1 = ρ.1) : strictTransform D F' h ρ' = D ρ := by
  rw [strictTransform_apply]
  exact congrArg D (Subtype.ext hρ)

/-! ### The linear forms on the cones of the flipped fan -/

variable {R : PointedCone ℝ (F.Ray → ℝ)}

/-- The rays of a cone `Fan.flipCone c ν j` are rays of the flipped fan. -/
theorem IsExtremalRay.mem_rays_flippedFan (hc : F.IsComplete) (hs : F.IsSimplicialFan)
    (hR : F.IsExtremalRay R) {σ₀ σ₀' : PointedCone ℝ (NR n)} (hw₀ : F.IsWallPair σ₀ σ₀')
    (W₀ : F.WallData σ₀ σ₀') (hW₀ : W₀.curveClass ∈ R) {ν : PointedCone ℝ (NR n)}
    (hν : F.IsMaximalCone ν) {j : F.Ray} (hj : W₀.curveClass j < 0) {ρ : F.Ray}
    (hρ : ρ ∈ F.flipRays W₀.curveClass ν j) : ρ.1 ∈ (hR.flippedFan hc hs hw₀ W₀ hW₀).rays := by
  refine ⟨⟨ν, j, hν, hj, ?_⟩, F.isRay ρ⟩
  have h := hR.isFaceOf_flipCone hc hs hw₀ W₀ hW₀ hν hj (Set.singleton_subset_iff.mpr hρ)
  rwa [indexCone_singleton_generator] at h

/-- The support function of the strict transform is given on the cone `Fan.flipCone c ν j` by a linear form `m` with `m(u_ρ) = -D_ρ` on the rays of the cone. -/
theorem IsExtremalRay.exists_linearMap_flipCone (hc : F.IsComplete) (hs : F.IsSimplicialFan)
    (hR : F.IsExtremalRay R) {σ₀ σ₀' : PointedCone ℝ (NR n)} (hw₀ : F.IsWallPair σ₀ σ₀')
    (W₀ : F.WallData σ₀ σ₀') (hW₀ : W₀.curveClass ∈ R) {D : F.TDivisor ℝ}
    (h : (hR.flippedFan hc hs hw₀ W₀ hW₀).rays ⊆ F.rays) {φ : NR n → ℝ}
    (hφ : (hR.flippedFan hc hs hw₀ W₀ hW₀).IsSupportFunctionOf (strictTransform D _ h) φ)
    {ν : PointedCone ℝ (NR n)} (hν : F.IsMaximalCone ν) {j : F.Ray} (hj : W₀.curveClass j < 0) :
    ∃ m : NR n →ₗ[ℝ] ℝ, (∀ x ∈ F.flipCone W₀.curveClass ν j, φ x = m x) ∧
      ∀ ρ ∈ F.flipRays W₀.curveClass ν j, m (toNR (F.generator ρ)) = -D ρ := by
  obtain ⟨m, hm⟩ := hφ.1 _ (⟨ν, j, hν, hj, PointedCone.IsFaceOf.refl _⟩ :
    F.flipCone W₀.curveClass ν j ∈ (hR.flippedFan hc hs hw₀ W₀ hW₀).cones)
  refine ⟨m, hm, fun ρ hρ => ?_⟩
  have hu : toNR (F.generator ρ) ∈ F.flipCone W₀.curveClass ν j :=
    mem_indexCone_of_mem (fun ρ : F.Ray => toNR (F.generator ρ)) hρ
  have h1 := hφ.2 ⟨ρ.1, hR.mem_rays_flippedFan hc hs hw₀ W₀ hW₀ hν hj hρ⟩
  rw [strictTransform_apply] at h1
  rw [← hm _ hu]
  exact h1

/-- **The maximal cones of the flipped fan over a cone of the contraction.** A maximal cone of `F⁺` in the cone `K_ν` of the contraction is a cone `Fan.flipCone c ν j` with `j ∈ J₋`. It is a cone `Fan.flipCone c ν' j'` that misses a ray `j` of `J₋`: `j'` itself when `ν'` is in the star, a ray of `J₋` outside `ν'` when it is not. Its rays are rays of `K_ν` other than `j`, so it is in `Fan.flipCone c ν j`, and it is equal to it by maximality. -/
theorem IsExtremalRay.exists_eq_flipCone (hc : F.IsComplete) (hs : F.IsSimplicialFan)
    (hR : F.IsExtremalRay R) {σ₀ σ₀' : PointedCone ℝ (NR n)} (hw₀ : F.IsWallPair σ₀ σ₀')
    (W₀ : F.WallData σ₀ σ₀') (hW₀ : W₀.curveClass ∈ R) {σ ν : PointedCone ℝ (NR n)}
    (hσ : (hR.flippedFan hc hs hw₀ W₀ hW₀).IsMaximalCone σ) (hν : F.IsMaximalCone ν)
    (hσν : σ ≤ F.contractCone W₀.curveClass ν) :
    ∃ j, W₀.curveClass j < 0 ∧ σ = F.flipCone W₀.curveClass ν j := by
  obtain ⟨ν', j', hν', hj', hσ'⟩ := hσ.mem
  have heq : σ = F.flipCone W₀.curveClass ν' j' :=
    le_antisymm hσ'.le (hσ.le_of_le ⟨ν', j', hν', hj', PointedCone.IsFaceOf.refl _⟩ hσ'.le)
  subst heq
  -- a ray of `J₋` that is not a ray of the cone
  obtain ⟨j, hj, hjS⟩ : ∃ j, W₀.curveClass j < 0 ∧ j ∉ F.flipRays W₀.curveClass ν' j' := by
    by_cases hneg' : F.negCone W₀.curveClass ≤ ν'
    · exact ⟨j', hj', fun hj'S => hj'S.2 hneg' rfl⟩
    · obtain ⟨j, hj, hjν⟩ : ∃ j : F.Ray, W₀.curveClass j < 0 ∧ ¬ j.1 ≤ ν' := by
        by_contra hno
        push_neg at hno
        exact hneg' (negCone_le_iff.mpr hno)
      exact ⟨j, hj, fun hjS => hjS.1.elim hjν fun h' => hneg' h'.1⟩
  have hle : F.flipCone W₀.curveClass ν' j' ≤ F.flipCone W₀.curveClass ν j := by
    refine indexCone_mono (fun ρ : F.Ray => toNR (F.generator ρ))
      (S := F.flipRays W₀.curveClass ν' j') (T := F.flipRays W₀.curveClass ν j)
      fun ρ hρ => ⟨?_, fun _ hρj => hjS (by rw [← hρj]; exact hρ)⟩
    exact (hR.generator_mem_contractCone_iff hc hs hw₀ W₀ hW₀ hν).mp
      (hσν (mem_indexCone_of_mem (fun ρ : F.Ray => toNR (F.generator ρ)) hρ))
  exact ⟨j, hj, le_antisymm hle (hσ.le_of_le ⟨ν, j, hν, hj, PointedCone.IsFaceOf.refl _⟩ hle)⟩

/-! ### Ampleness over the contraction and the step -/

/-- **The strict transform is ample over the contraction** (Reid 1983, Theorem 3.4). Let `D` be a divisor with `D · c < 0`, where `c` is the class of a wall curve in `R`. Its strict transform to the flipped fan `F⁺` has a support function that is strictly convex on each cone of the contraction fan `G`, at each maximal cone of `F⁺` in it. -/
theorem IsExtremalRay.isAmpleOver_flippedFan (hc : F.IsComplete) (hs : F.IsSimplicialFan)
    (hR : F.IsExtremalRay R) {σ₀ σ₀' : PointedCone ℝ (NR n)} (hw₀ : F.IsWallPair σ₀ σ₀')
    (W₀ : F.WallData σ₀ σ₀') (hW₀ : W₀.curveClass ∈ R) (hJ : ∃ k, W₀.curveClass k < 0)
    (h : (hR.flippedFan hc hs hw₀ W₀ hW₀).rays ⊆ F.rays) {D : F.TDivisor ℝ}
    (hD : W₀.degree D < 0) :
    (hR.flippedFan hc hs hw₀ W₀ hW₀).IsAmpleOver (hR.contractionFan hc hs hw₀ W₀ hW₀ hJ).cones
      (strictTransform D _ h) := by
  obtain ⟨k, hk⟩ := hJ
  obtain ⟨φ, hφ⟩ := ((hR.isSimplicialFan_flippedFan hc hs hw₀ W₀ hW₀).isRCartier
    (strictTransform D _ h)).exists_isSupportFunctionOf
  refine ⟨φ, hφ, ?_⟩
  rintro τ ⟨ν, hν, hτ⟩ σ hσ hστ
  obtain ⟨j, hj, rfl⟩ := hR.exists_eq_flipCone hc hs hw₀ W₀ hW₀ hσ hν (hστ.trans hτ.le)
  obtain ⟨m, hm, hmD⟩ := hR.exists_linearMap_flipCone hc hs hw₀ W₀ hW₀ h hφ hν hj
  refine ⟨m, hm, fun x hx hxσ => ?_⟩
  by_cases hneg : F.negCone W₀.curveClass ≤ ν
  · obtain ⟨j', hj', hxj'⟩ := exists_mem_flipCone hs hw₀ W₀ hk (hτ.le hx)
    obtain ⟨m', hm', hm'D⟩ := hR.exists_linearMap_flipCone hc hs hw₀ W₀ hW₀ h hφ hν hj'
    rw [hm' x hxj']
    have hrel := W₀.sum_curveClass_smul_generator hw₀.1.mem (hs σ₀ hw₀.1.mem)
    have hd : ∑ ρ, W₀.curveClass ρ * D ρ < 0 := by
      rwa [← W₀.degree_eq_sum_curveClass]
    exact (apply_le_of_relation hrel hd hj (S := F.flipRays W₀.curveClass ν j)
      (T := F.flipRays W₀.curveClass ν j') (fun ρ h0 hρj => ⟨Or.inr ⟨hneg, h0⟩, fun _ => hρj⟩)
      (fun ρ hρ hρj => ⟨hρ.1, fun _ => hρj⟩) hmD hm'D hxj').2 hxσ
  · rw [flipCone_of_not_le hν.mem hneg] at hxσ
    have hxν := hτ.le hx
    rw [contractCone_of_not_le hν.mem hneg] at hxν
    exact absurd hxν hxσ

/-- **The flip as a toric step, on the side of `F⁺`.** Let `D` be a divisor with `D · c < 0`, and let `J₋` have two rays. Then the flipped fan with the strict transform of `D` is a toric step from `(F, D)` over the contraction fan `G`, as soon as `F` has relative Picard number one over `G` and `-D` is ample over `G`. The conditions on the side of `F⁺` are proved: `F⁺` is simplicial, refines `G`, has the rays of `G`, and the strict transform is ample over `G`. -/
theorem IsExtremalRay.isToricStep_flippedFan (hc : F.IsComplete) (hs : F.IsSimplicialFan)
    (hR : F.IsExtremalRay R) {σ₀ σ₀' : PointedCone ℝ (NR n)} (hw₀ : F.IsWallPair σ₀ σ₀')
    (W₀ : F.WallData σ₀ σ₀') (hW₀ : W₀.curveClass ∈ R) {k k' : F.Ray}
    (hk : W₀.curveClass k < 0) (hk' : W₀.curveClass k' < 0) (hkk' : k ≠ k')
    {D : F.TDivisor ℝ} (hD : W₀.degree D < 0)
    (hpic : F.HasRelPicardOne (hR.contractionFan hc hs hw₀ W₀ hW₀ ⟨k, hk⟩).cones)
    (hamp : F.IsAmpleOver (hR.contractionFan hc hs hw₀ W₀ hW₀ ⟨k, hk⟩).cones (-D)) :
    IsToricStep ⟨F, D⟩ ⟨hR.flippedFan hc hs hw₀ W₀ hW₀,
      strictTransform D _ (hR.rays_flippedFan hc hs hw₀ W₀ hW₀ hk hk' hkk').subset⟩ :=
  ⟨hR.contractionFan hc hs hw₀ W₀ hW₀ ⟨k, hk⟩, hR.refines_contraction hc hs hw₀ W₀ hW₀, hpic,
    hamp, hR.isSimplicialFan_flippedFan hc hs hw₀ W₀ hW₀,
    hR.refines_flippedFan hc hs hw₀ W₀ hW₀ ⟨k, hk⟩,
    (hR.rays_flippedFan hc hs hw₀ W₀ hW₀ hk hk' hkk').trans
      (hR.rays_contractionFan hc hs hw₀ W₀ hW₀ hk hk' hkk').symm,
    hR.isAmpleOver_flippedFan hc hs hw₀ W₀ hW₀ ⟨k, hk⟩ _ hD,
    fun _ _ hρ => strictTransform_apply_of_eq D _ hρ⟩

end Fan

end MinimalModel.Toric
