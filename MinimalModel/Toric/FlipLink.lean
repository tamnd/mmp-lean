/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import MinimalModel.Toric.FlipSupport

/-!
# Toric flips, part 6: the star of `cone(u_{J₋})` is the join of the circuit with a link

This file finishes step 3 of the route to `flipExists` in `MinimalModel/Toric/Flip.lean` (route R3, spec 04.4), the star of the exceptional locus (Reid 1983, Corollary 2.5 and Section 2; Matsuki, Proposition 14-2-1; Cox, Little and Schenck, Proposition 15.4.5).

Let `F` be a complete simplicial fan, `R` an extremal ray of its cone of curves, and `c` the class of a wall curve in `R`. The rays `ρ` with `c ρ > 0` form `J₊`, those with `c ρ < 0` form `J₋`. The star of `cone(u_{J₋})` is the set of maximal cones of `F` that contain `cone(u_{J₋})` (`Fan.negCone`). For a ray `k` of `J₊`, let `Fan.circuitCone c k` be the cone of the generators of the rays of `J₊ ∪ J₋` other than `k`, and for a cone `σ` let `Fan.linkCone c σ` be the cone of the generators of the rays of `σ` outside `J₊ ∪ J₋`. The link `Fan.link c` is the set of the cones `Fan.linkCone c σ` for `σ` in the star. The main result is

  `σ` is in the star `↔` `σ = cone(u_{J₊ ∪ J₋ ∖ {k}}) + λ` for a ray `k` of `J₊` and a cone `λ` of the link

(`Fan.IsExtremalRay.star_iff`, `Fan.IsExtremalRay.star`).

## The supporting divisor is linear on the star

Let `D` be the divisor of Reid that supports `R` (`Fan.IsExtremalRay.exists_tDivisor`), and `φ` a support function of `D`. Every divisor of a simplicial fan is R-Cartier (`Fan.IsSimplicialFan.isRCartier`), and the maximal cones of a complete fan have dimension `n` (`Fan.IsMaximalCone.coneDim_eq`). So `φ ≤ m_σ` everywhere for each maximal cone `σ`, where `m_σ` is the linear form of `φ` on `σ` (`le_of_span_eq_top`). These are the properties that we use (`Fan.IsRaySupport`, `Fan.IsExtremalRay.exists_isRaySupport`).

Let `σ` be a maximal cone in the star. The numbers `g_ρ = m_σ(u_ρ) - φ(u_ρ)` are nonnegative and vanish on the rays of `σ`, and `Σ c_ρ g_ρ = m_σ(Σ c_ρ u_ρ) + D · C = 0`. The rays with `c_ρ < 0` are in `σ`, so each term is nonnegative, and `g_ρ = 0` for each ray of the circuit (`Fan.IsRaySupport.eq_of_curveClass_ne_zero`): `φ` agrees with `m_σ` on `cone(u_{J₊ ∪ J₋})`.

## The walls met by the circuit are walls of `R`

Let `σ, σ''` be a wall pair, `l` the ray of `σ` that is not in `σ''`, and let `y = Σ β_ρ u_ρ` be a vector with `β_l < 0` and `φ(y) = m_σ(y)`. Write `ℓ = m_σ'' - m_σ`. It vanishes on the rays of `σ` other than `l`, and `φ(y) ≤ m_σ''(y)` gives `β_l ℓ(u_l) ≥ 0`, so `ℓ(u_l) ≤ 0`. The new ray `ρ''` of `σ''` is `u_ρ'' = Σ c''_ρ u_ρ` with `c''_l < 0`, so `ℓ(u_ρ'') ≥ 0`, and `φ(u_ρ'') ≤ m_σ(u_ρ'')` gives `ℓ(u_ρ'') ≤ 0`. So the degree of `D` on the wall, `-ℓ(u_ρ'')`, is zero, and the curve of the wall is in `R` (`Fan.IsRaySupport.degree_eq_zero`).

## The shape of a cone of the star

Let `σ` be in the star. A ray `j` of the circuit is not in `σ`, since the generators of `σ` are linearly independent; it is in `J₊`. Write `u_j = Σ β_ρ u_ρ` in the basis of the generators of `σ`. Some `β_l` is negative, as `u_j ∉ σ`, and `φ(u_j) = m_σ(u_j)`, so the wall opposite `l` is a wall of `R`. Its class is proportional to `c`, and it vanishes outside `σ` and the new ray, so `j` is the only ray of the circuit outside `σ` (`Fan.IsExtremalRay.exists_ray_not_le`). So `σ = cone(u_{J₊ ∪ J₋ ∖ {j}}) + λ` with `λ = Fan.linkCone c σ` (`Fan.eq_circuitCone_sup_linkCone`).

For another ray `k` of `J₊`, the relation `c` gives `u_j = -Σ_{ρ ≠ j} (c_ρ / c_j) u_ρ`, with a negative coefficient at `k`. So the wall of `σ` opposite `k` is a wall of `R`, and the new ray across it is `j` (`Fan.WallData.IsProportional.ray_eq`). The neighbour is `cone(u_{J₊ ∪ J₋ ∖ {k}}) + λ` with the same `λ` (`Fan.IsExtremalRay.exists_exchange`, `Fan.IsExtremalRay.exists_eq_circuitCone_sup_linkCone`). This gives the star.

## Main results

* `Fan.IsSimplicialFan.isRCartier`: each divisor of a simplicial fan is R-Cartier.
* `Fan.IsMaximalCone.coneDim_eq`: the maximal cones of a complete fan have dimension `n`.
* `Fan.IsExtremalRay.exists_isRaySupport`: a support function of a divisor that supports an extremal ray, below the linear form of each maximal cone.
* `Fan.IsRaySupport.degree_eq_zero`: the walls met by a vector on which the support function is linear are walls of the ray.
* `Fan.IsExtremalRay.exists_ray_not_le`: a cone of the star contains all the rays of the circuit but one ray `j` of `J₊`.
* `Fan.IsExtremalRay.exists_exchange`, `Fan.IsExtremalRay.exists_eq_circuitCone_sup_linkCone`: crossing the wall opposite another ray `k` of `J₊` exchanges `k` and `j`, with the same link.
* `Fan.linkCone_mem`: the cones of the link are cones of the fan.
* `Fan.IsExtremalRay.star_iff`, `Fan.IsExtremalRay.star`: the star of `cone(u_{J₋})` is the set of the cones `cone(u_{J₊ ∪ J₋ ∖ {k}}) + λ`, with `k` in `J₊` and `λ` in the link.
-/

open Set

namespace MinimalModel.Toric

variable {n : ℕ}

namespace Fan

variable {F : Fan n}

/-! ### Divisors of a simplicial fan and maximal cones of a complete fan -/

/-- Each divisor of a simplicial fan is R-Cartier: on a simplicial cone the generators of the rays are linearly independent, so a linear form takes any prescribed values on them. -/
theorem IsSimplicialFan.isRCartier (hs : F.IsSimplicialFan) (D : F.TDivisor ℝ) :
    F.IsRCartier D := by
  intro σ hσ
  have hli := linearIndependent_generator hσ (hs σ hσ)
  obtain ⟨m, hm⟩ := LinearMap.exists_extend
    ((Finsupp.linearCombination ℝ fun ρ : {ρ : F.Ray // ρ.1 ≤ σ} => -D ρ.1).comp hli.repr)
  refine ⟨m, fun ρ hρ => ?_⟩
  let x : Submodule.span ℝ (Set.range fun ρ : {ρ : F.Ray // ρ.1 ≤ σ} => toNR (F.generator ρ.1)) :=
    ⟨toNR (F.generator ρ), Submodule.subset_span ⟨⟨ρ, hρ⟩, rfl⟩⟩
  have h := LinearMap.congr_fun hm x
  rw [LinearMap.comp_apply, LinearMap.comp_apply, hli.repr_eq_single ⟨ρ, hρ⟩ x rfl,
    Finsupp.linearCombination_single, smul_eq_mul, one_mul] at h
  exact h

/-- A maximal cone of a complete fan has dimension `n`. Let `p` be the sum of the generators of the rays of `σ`. The cones that do not contain `p` form a closed set, so near `p` there is a point `x` outside the span of `σ` and outside these cones. A cone `C` that contains `x` contains `p`, so `σ ∩ C` is a face of `σ` that contains `p`, and it is `σ`. By maximality `C = σ`, and `x ∈ σ`, a contradiction. -/
theorem IsMaximalCone.coneDim_eq (hc : F.IsComplete) {σ : PointedCone ℝ (NR n)}
    (h : F.IsMaximalCone σ) : coneDim σ = n := by
  classical
  by_contra hne
  have htop : Submodule.span ℝ (σ : Set (NR n)) ≠ ⊤ := fun htop => hne (by
    change Module.finrank ℝ (Submodule.span ℝ (σ : Set (NR n))) = n
    rw [htop, finrank_top, Module.finrank_fin_fun ℝ])
  have hpσ : ∑ ρ : {ρ : F.Ray // ρ.1 ≤ σ}, toNR (F.generator ρ.1) ∈ σ :=
    Submodule.sum_mem _ fun ρ _ => ρ.2 (F.toNR_generator_mem ρ.1)
  have hK : IsClosed (⋃ C ∈ {C ∈ F.cones |
      ∑ ρ : {ρ : F.Ray // ρ.1 ≤ σ}, toNR (F.generator ρ.1) ∉ C}, (C : Set (NR n))) :=
    (F.finite.subset (Set.sep_subset _ _)).isClosed_biUnion fun C hC => F.isClosed_of_mem hC.1
  have hpK : ∑ ρ : {ρ : F.Ray // ρ.1 ≤ σ}, toNR (F.generator ρ.1) ∉ ⋃ C ∈ {C ∈ F.cones |
      ∑ ρ : {ρ : F.Ray // ρ.1 ≤ σ}, toNR (F.generator ρ.1) ∉ C}, (C : Set (NR n)) := by
    intro hmem
    obtain ⟨C, hC, hpC⟩ := Set.mem_iUnion₂.mp hmem
    exact hC.2 hpC
  obtain ⟨x, hxK, hx⟩ := exists_forall_notMem
    (fun C : PointedCone ℝ (NR n) => Submodule.span ℝ (C : Set (NR n))) {σ} _ hK.isOpen_compl
    ⟨_, hpK⟩ fun C hC => by
      rw [Finset.mem_singleton.mp hC]
      exact htop
  obtain ⟨C, hC, hxC⟩ := exists_mem_of_isComplete hc x
  have hpC : ∑ ρ : {ρ : F.Ray // ρ.1 ≤ σ}, toNR (F.generator ρ.1) ∈ C := by
    by_contra hpC
    exact hxK (Set.mem_iUnion₂.mpr ⟨C, ⟨hC, hpC⟩, hxC⟩)
  have hle : σ ≤ σ ⊓ C := le_of_isFaceOf_of_sum_mem h.mem (F.inter_face σ h.mem C hC) le_rfl
    (Submodule.mem_inf.mpr ⟨hpσ, hpC⟩)
  have hCσ : C ≤ σ := h.le_of_le hC (hle.trans inf_le_right)
  exact hx σ (Finset.mem_singleton_self σ) (Submodule.subset_span (hCσ hxC))

/-- The cone of the negative rays of a class is in a cone of the fan exactly when the negative rays are. -/
theorem negCone_le_iff {c : F.Ray → ℝ} {σ : PointedCone ℝ (NR n)} :
    F.negCone c ≤ σ ↔ ∀ ρ : F.Ray, c ρ < 0 → ρ.1 ≤ σ := by
  constructor
  · intro h ρ hρ
    rw [← F.latticeCone_generator ρ]
    exact latticeCone_singleton_le.mpr (h (Submodule.subset_span ⟨ρ, hρ, rfl⟩))
  · intro h
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨ρ, hρ, rfl⟩
    exact h ρ hρ (F.toNR_generator_mem ρ)

/-- A sum over the rays of a cone `σ` is a sum over a finite set of rays that contains the rays of `σ`, when the terms outside `σ` vanish. -/
theorem sum_subtype_eq_sum {σ : PointedCone ℝ (NR n)} {M : Type*} [AddCommMonoid M]
    (s : Finset F.Ray) (f : F.Ray → M) (hs : ∀ ρ : F.Ray, ρ.1 ≤ σ → ρ ∈ s)
    (hf : ∀ ρ ∈ s, f ρ ≠ 0 → ρ.1 ≤ σ) :
    ∑ ρ : {ρ : F.Ray // ρ.1 ≤ σ}, f ρ.1 = ∑ ρ ∈ s, f ρ := by
  classical
  refine (Finset.sum_subtype (p := fun ρ : F.Ray => ρ.1 ≤ σ)
    (Finset.univ.filter fun ρ : F.Ray => ρ.1 ≤ σ) (fun ρ => by simp) f).symm.trans ?_
  refine Finset.sum_subset (fun ρ hρ => hs ρ (Finset.mem_filter.mp hρ).2) fun ρ hρ hρ' => ?_
  by_contra h
  exact hρ' (Finset.mem_filter.mpr ⟨Finset.mem_univ ρ, hf ρ hρ h⟩)

/-! ### The support function of a divisor that supports an extremal ray -/

variable (F) in
/-- The properties of a support function `φ` of a divisor `D` that supports the extremal ray `R` (Reid 1983, Section 2) that the description of the star uses. -/
structure IsRaySupport (R : PointedCone ℝ (F.Ray → ℝ)) (D : F.TDivisor ℝ) (φ : NR n → ℝ) :
    Prop where
  /-- `φ` is a support function of `D`. -/
  isSupportFunctionOf : F.IsSupportFunctionOf D φ
  /-- `φ` is below the linear form of `φ` on each maximal cone. -/
  le_linear : ∀ τ, F.IsMaximalCone τ → ∀ m : NR n →ₗ[ℝ] ℝ, (∀ x ∈ τ, φ x = m x) →
    ∀ x, φ x ≤ m x
  /-- The degree of `D` on a wall is zero exactly when the curve of the wall is in `R`. -/
  degree_eq_zero_iff : ∀ σ σ' : PointedCone ℝ (NR n), F.IsWallPair σ σ' →
    ∀ W : F.WallData σ σ', W.degree D = 0 ↔ W.curveClass ∈ R

/-- **The supporting divisor** of an extremal ray of a complete simplicial fan, with a support function below the linear form of each maximal cone. -/
theorem IsExtremalRay.exists_isRaySupport (hc : F.IsComplete) (hs : F.IsSimplicialFan)
    {R : PointedCone ℝ (F.Ray → ℝ)} (hR : F.IsExtremalRay R) :
    ∃ (D : F.TDivisor ℝ) (φ : NR n → ℝ), F.IsRaySupport R D φ := by
  obtain ⟨D, -, hD0, hconv⟩ := hR.exists_tDivisor hs
  obtain ⟨φ, hφ⟩ := (hs.isRCartier D).exists_isSupportFunctionOf
  refine ⟨D, φ, hφ, fun τ hτ m hm x => ?_, hD0⟩
  exact le_of_span_eq_top hc (fun C hC => F.isClosed_of_mem hC) hφ.1
    (fun σ σ' hw => hconv φ hφ σ σ' hw (hw.nonempty_wallData hs).some)
    (span_eq_top_of_coneDim_eq (hτ.coneDim_eq hc)) hm x

namespace IsRaySupport

variable {R : PointedCone ℝ (F.Ray → ℝ)} {D : F.TDivisor ℝ} {φ : NR n → ℝ}

/-- **A wall of the ray.** Let `σ, σ''` be a wall pair, `l` the ray of `σ` that is not in `σ''`, and `y = Σ β_ρ u_ρ` a vector with `β_l < 0` on which `φ` agrees with the linear form `m` of `φ` on `σ`. Then the degree of `D` on the wall is zero. The proof is in the module docstring. -/
theorem degree_eq_zero (h : F.IsRaySupport R D φ) (hs : F.IsSimplicialFan)
    {σ σ'' : PointedCone ℝ (NR n)} (hw : F.IsWallPair σ σ'') (W : F.WallData σ σ'')
    {m : NR n →ₗ[ℝ] ℝ} (hm : ∀ x ∈ σ, φ x = m x) {l : F.Ray} (hl : l.1 ≤ σ)
    (hl' : ¬ l.1 ≤ σ'') (β : {ρ : F.Ray // ρ.1 ≤ σ} → ℝ) (hβ : β ⟨l, hl⟩ < 0)
    (hy : φ (∑ ρ, β ρ • toNR (F.generator ρ.1)) = m (∑ ρ, β ρ • toNR (F.generator ρ.1))) :
    W.degree D = 0 := by
  classical
  have hσ := hw.1.mem
  obtain ⟨m'', hm''⟩ := h.isSupportFunctionOf.1 σ'' hw.2.1.mem
  have hzero : ∀ ρ : {ρ : F.Ray // ρ.1 ≤ σ}, ρ ≠ ⟨l, hl⟩ →
      m'' (toNR (F.generator ρ.1)) - m (toNR (F.generator ρ.1)) = 0 := by
    intro ρ hρ
    have hρ'' : ρ.1.1 ≤ σ'' := by
      by_contra h'
      exact hρ (Subtype.ext (IsWallPair.eq_of_not_le (hs σ hσ) hw ρ.2 h' hl hl'))
    rw [← hm'' _ (hρ'' (F.toNR_generator_mem _)), ← hm _ (ρ.2 (F.toNR_generator_mem _)), sub_self]
  have hsum : ∀ a : {ρ : F.Ray // ρ.1 ≤ σ} → ℝ,
      m'' (∑ ρ, a ρ • toNR (F.generator ρ.1)) - m (∑ ρ, a ρ • toNR (F.generator ρ.1)) =
        a ⟨l, hl⟩ * (m'' (toNR (F.generator l)) - m (toNR (F.generator l))) := by
    intro a
    rw [map_sum, map_sum, ← Finset.sum_sub_distrib, Finset.sum_eq_single ⟨l, hl⟩]
    · rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul, ← mul_sub]
    · intro ρ _ hρ
      rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul, ← mul_sub, hzero ρ hρ, mul_zero]
    · intro h'
      exact absurd (Finset.mem_univ _) h'
  -- the form `ℓ = m'' - m` is nonpositive at `u_l`
  have hl0 : m'' (toNR (F.generator l)) - m (toNR (F.generator l)) ≤ 0 := by
    have h1 := h.le_linear σ'' hw.2.1 m'' hm'' (∑ ρ, β ρ • toNR (F.generator ρ.1))
    have h2 := hsum β
    rw [hy] at h1
    by_contra h3
    have := mul_neg_of_neg_of_pos hβ (not_le.mp h3)
    linarith
  -- the coefficient of `u_l` in the new ray is negative
  obtain ⟨ρ0, hρ0, hneg⟩ := W.exists_coeffIn_neg hσ hw.2.1.mem
  have hρ0l : ρ0 = ⟨l, hl⟩ :=
    Subtype.ext (IsWallPair.eq_of_not_le (hs σ hσ) hw ρ0.2 hρ0 hl hl')
  rw [hρ0l] at hneg
  have hray := hsum W.coeffIn
  rw [W.sum_coeffIn_smul_generator] at hray
  have hr1 : 0 ≤ m'' (toNR (F.generator W.ray)) - m (toNR (F.generator W.ray)) := by
    rw [hray]
    nlinarith
  have hr : φ (toNR (F.generator W.ray)) = m'' (toNR (F.generator W.ray)) :=
    hm'' _ (W.ray_le (F.toNR_generator_mem _))
  have hr2 := h.le_linear σ hw.1 m hm (toNR (F.generator W.ray))
  rw [W.degree_eq_sub h.isSupportFunctionOf hm]
  linarith

/-- **The support function is linear on the circuit.** Let `σ` be a maximal cone that contains the negative rays of the class of a wall curve of `R`. Then `φ` agrees with its linear form on `σ` at each ray of the circuit. The proof is in the module docstring. -/
theorem eq_of_curveClass_ne_zero (h : F.IsRaySupport R D φ) (hs : F.IsSimplicialFan)
    {σ₀ σ₀' : PointedCone ℝ (NR n)} (hw₀ : F.IsWallPair σ₀ σ₀') (W₀ : F.WallData σ₀ σ₀')
    (hW₀ : W₀.curveClass ∈ R) {σ : PointedCone ℝ (NR n)} (hσ : F.IsMaximalCone σ)
    (hneg : ∀ ρ : F.Ray, W₀.curveClass ρ < 0 → ρ.1 ≤ σ) {m : NR n →ₗ[ℝ] ℝ}
    (hm : ∀ x ∈ σ, φ x = m x) (ρ : F.Ray) (hρ : W₀.curveClass ρ ≠ 0) :
    φ (toNR (F.generator ρ)) = m (toNR (F.generator ρ)) := by
  have hσ₀ := hw₀.1.mem
  have hdeg : W₀.degree D = 0 := (h.degree_eq_zero_iff σ₀ σ₀' hw₀ W₀).mpr hW₀
  have hterm : ∀ ρ ∈ (Finset.univ : Finset F.Ray),
      0 ≤ W₀.curveClass ρ * (m (toNR (F.generator ρ)) - φ (toNR (F.generator ρ))) := by
    intro ρ _
    by_cases hlt : W₀.curveClass ρ < 0
    · exact le_of_eq (by rw [hm _ (hneg ρ hlt (F.toNR_generator_mem ρ)), sub_self, mul_zero])
    · exact mul_nonneg (not_lt.mp hlt) (sub_nonneg.mpr (h.le_linear σ hσ m hm _))
  have h1 : ∑ ρ, W₀.curveClass ρ * m (toNR (F.generator ρ)) = 0 := by
    have h2 := congrArg m (W₀.sum_curveClass_smul_generator hσ₀ (hs σ₀ hσ₀))
    rw [map_sum, map_zero] at h2
    simpa only [map_smul, smul_eq_mul] using h2
  have h2 : ∑ ρ, W₀.curveClass ρ * φ (toNR (F.generator ρ)) = -W₀.degree D := by
    rw [W₀.degree_eq_sum_curveClass, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [h.isSupportFunctionOf.2 ρ, mul_neg]
  have htot : ∑ ρ, W₀.curveClass ρ * (m (toNR (F.generator ρ)) - φ (toNR (F.generator ρ))) =
      0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, h1, h2, hdeg, neg_zero, sub_zero]
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp htot ρ (Finset.mem_univ ρ)
  rcases mul_eq_zero.mp h0 with h3 | h3
  · exact absurd h3 hρ
  · linarith

/-- A cone of the star contains all the rays of the circuit but one ray of `J₊`. -/
theorem exists_ray_not_le (h : F.IsRaySupport R D φ) (hc : F.IsComplete)
    (hs : F.IsSimplicialFan) (hR : F.IsExtremalRay R) {σ₀ σ₀' : PointedCone ℝ (NR n)}
    (hw₀ : F.IsWallPair σ₀ σ₀') (W₀ : F.WallData σ₀ σ₀') (hW₀ : W₀.curveClass ∈ R)
    {σ : PointedCone ℝ (NR n)} (hσ : F.IsMaximalCone σ)
    (hneg : ∀ ρ : F.Ray, W₀.curveClass ρ < 0 → ρ.1 ≤ σ) :
    ∃ j : F.Ray, 0 < W₀.curveClass j ∧ ¬ j.1 ≤ σ ∧
      ∀ ρ : F.Ray, W₀.curveClass ρ ≠ 0 → ρ ≠ j → ρ.1 ≤ σ := by
  classical
  have hσ₀ := hw₀.1.mem
  obtain ⟨m, hm⟩ := h.isSupportFunctionOf.1 σ hσ.mem
  -- a ray of the circuit is not in `σ`
  obtain ⟨j, hj0, hjσ⟩ : ∃ j : F.Ray, W₀.curveClass j ≠ 0 ∧ ¬ j.1 ≤ σ := by
    by_contra hno
    have hno' : ∀ ρ : F.Ray, W₀.curveClass ρ ≠ 0 → ρ.1 ≤ σ := fun ρ hρ => by
      by_contra hρσ
      exact hno ⟨ρ, hρ, hρσ⟩
    have hsum : ∑ ρ : {ρ : F.Ray // ρ.1 ≤ σ}, W₀.curveClass ρ.1 • toNR (F.generator ρ.1) = 0 :=
      (sum_subtype_eq_sum Finset.univ (fun ρ => W₀.curveClass ρ • toNR (F.generator ρ))
        (fun ρ _ => Finset.mem_univ ρ)
        (fun ρ _ hρ => hno' ρ fun h0 => hρ (by simp [h0]))).trans
        (W₀.sum_curveClass_smul_generator hσ₀ (hs σ₀ hσ₀))
    have hzero := Fintype.linearIndependent_iff.mp
      (linearIndependent_generator hσ.mem (hs σ hσ.mem)) (fun ρ => W₀.curveClass ρ.1) hsum
    apply W₀.curveClass_ne_zero
    funext ρ
    by_cases hρ : W₀.curveClass ρ = 0
    · exact hρ
    · exact hzero ⟨ρ, hno' ρ hρ⟩
  have hj : 0 < W₀.curveClass j :=
    lt_of_le_of_ne (not_lt.mp fun hlt => hjσ (hneg j hlt)) (Ne.symm hj0)
  -- write `u_j` in the basis of the generators of `σ`
  have hspan : Submodule.span ℝ
      (Set.range fun ρ : {ρ : F.Ray // ρ.1 ≤ σ} => toNR (F.generator ρ.1)) = ⊤ := by
    rw [← Set.image_univ, ← span_indexCone, ← eq_indexCone_generator hσ.mem]
    exact span_eq_top_of_coneDim_eq (hσ.coneDim_eq hc)
  have hmem : toNR (F.generator j) ∈ Submodule.span ℝ
      (Set.range fun ρ : {ρ : F.Ray // ρ.1 ≤ σ} => toNR (F.generator ρ.1)) := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨β, hβ⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hmem
  obtain ⟨l, hl⟩ : ∃ l, β l < 0 := by
    by_contra hno
    apply hjσ
    have hx : toNR (F.generator j) ∈
        indexCone (fun ρ : {ρ : F.Ray // ρ.1 ≤ σ} => toNR (F.generator ρ.1)) Set.univ :=
      mem_indexCone.mpr ⟨β, fun l => not_lt.mp fun hlt => hno ⟨l, hlt⟩,
        fun i hi => absurd (Set.mem_univ i) hi, hβ⟩
    rw [← eq_indexCone_generator hσ.mem] at hx
    rw [← F.latticeCone_generator j]
    exact latticeCone_singleton_le.mpr hx
  -- the wall opposite `l` is a wall of `R`
  obtain ⟨σ'', hw, hl'', -⟩ := exists_isWallPair_of_ray hc hs hσ.mem (hσ.coneDim_eq hc) l.1 l.2
  obtain ⟨W⟩ := hw.nonempty_wallData hs
  have hW0 : W.degree D = 0 := h.degree_eq_zero hs hw W hm l.2 hl'' β hl (by
    rw [hβ]
    exact h.eq_of_curveClass_ne_zero hs hw₀ W₀ hW₀ hσ hneg hm j hj0)
  have hWR := (h.degree_eq_zero_iff σ σ'' hw W).mp hW0
  obtain ⟨t, ht, hct⟩ := WallData.isProportional_iff.mp (hR.isProportional hW₀ hWR)
  -- so each ray of the circuit outside `σ` is the new ray of the wall
  have hray : ∀ ρ : F.Ray, W₀.curveClass ρ ≠ 0 → ¬ ρ.1 ≤ σ → ρ = W.ray := by
    intro ρ hρ hρσ
    by_contra hne
    have h1 := W.curveClass_eq_zero_of_not_le hne hρσ
    rw [hct, Pi.smul_apply, smul_eq_mul] at h1
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact ht.ne' h2
    · exact hρ h2
  refine ⟨j, hj, hjσ, fun ρ hρ hρj => ?_⟩
  by_contra hρσ
  exact hρj ((hray ρ hρ hρσ).trans (hray j hj0 hjσ).symm)

/-- **The exchange.** Let `σ` be a cone of the star, `j` the ray of the circuit that is not in `σ`, and `k ≠ j` another ray of `J₊`. The neighbour of `σ` across the facet opposite `k` has the rays of `σ` and `j`, but not `k`. -/
theorem exists_exchange (h : F.IsRaySupport R D φ) (hc : F.IsComplete)
    (hs : F.IsSimplicialFan) (hR : F.IsExtremalRay R) {σ₀ σ₀' : PointedCone ℝ (NR n)}
    (hw₀ : F.IsWallPair σ₀ σ₀') (W₀ : F.WallData σ₀ σ₀') (hW₀ : W₀.curveClass ∈ R)
    {σ : PointedCone ℝ (NR n)} (hσ : F.IsMaximalCone σ)
    (hneg : ∀ ρ : F.Ray, W₀.curveClass ρ < 0 → ρ.1 ≤ σ) {j : F.Ray}
    (hcj : 0 < W₀.curveClass j) (hjσ : ¬ j.1 ≤ σ)
    (hj : ∀ ρ : F.Ray, W₀.curveClass ρ ≠ 0 → ρ ≠ j → ρ.1 ≤ σ) {k : F.Ray}
    (hk : 0 < W₀.curveClass k) (hkj : k ≠ j) :
    ∃ σ'', F.IsWallPair σ σ'' ∧ ∀ ρ : F.Ray, ρ.1 ≤ σ'' ↔ ρ = j ∨ (ρ.1 ≤ σ ∧ ρ ≠ k) := by
  classical
  have hσ₀ := hw₀.1.mem
  have hkσ : k.1 ≤ σ := hj k hk.ne' hkj
  obtain ⟨m, hm⟩ := h.isSupportFunctionOf.1 σ hσ.mem
  obtain ⟨σ'', hw, hk'', hother⟩ := exists_isWallPair_of_ray hc hs hσ.mem (hσ.coneDim_eq hc) k hkσ
  obtain ⟨W⟩ := hw.nonempty_wallData hs
  -- the relation of the circuit: `c_j u_j + Σ_{ρ ≤ σ} c_ρ u_ρ = 0`
  have hrel : W₀.curveClass j • toNR (F.generator j) +
      ∑ ρ : {ρ : F.Ray // ρ.1 ≤ σ}, W₀.curveClass ρ.1 • toNR (F.generator ρ.1) = 0 := by
    rw [show ∑ ρ : {ρ : F.Ray // ρ.1 ≤ σ}, W₀.curveClass ρ.1 • toNR (F.generator ρ.1) =
        ∑ ρ ∈ Finset.univ.erase j, W₀.curveClass ρ • toNR (F.generator ρ) from
      sum_subtype_eq_sum _ (fun ρ => W₀.curveClass ρ • toNR (F.generator ρ))
        (fun ρ hρ => Finset.mem_erase.mpr ⟨fun hρj => hjσ (by rw [← hρj]; exact hρ),
          Finset.mem_univ ρ⟩)
        (fun ρ hρ h0 => hj ρ (fun h0' => h0 (by simp [h0'])) (Finset.mem_erase.mp hρ).1)]
    exact (Finset.add_sum_erase _ (fun ρ => W₀.curveClass ρ • toNR (F.generator ρ))
      (Finset.mem_univ j)).trans (W₀.sum_curveClass_smul_generator hσ₀ (hs σ₀ hσ₀))
  have hy : ∑ ρ : {ρ : F.Ray // ρ.1 ≤ σ},
      (-(W₀.curveClass j)⁻¹ * W₀.curveClass ρ.1) • toNR (F.generator ρ.1) =
        toNR (F.generator j) := by
    simp_rw [mul_smul]
    rw [← Finset.smul_sum, eq_neg_iff_add_eq_zero.mpr ((add_comm _ _).trans hrel), smul_neg,
      neg_smul, neg_neg, smul_smul, inv_mul_cancel₀ hcj.ne', one_smul]
  -- the wall opposite `k` is a wall of `R`, and its new ray is `j`
  have hW0 : W.degree D = 0 := h.degree_eq_zero hs hw W hm hkσ hk''
    (fun ρ => -(W₀.curveClass j)⁻¹ * W₀.curveClass ρ.1)
    (mul_neg_of_neg_of_pos (neg_lt_zero.mpr (inv_pos.mpr hcj)) hk)
    ((congrArg φ hy).trans ((h.eq_of_curveClass_ne_zero hs hw₀ W₀ hW₀ hσ hneg hm j
      hcj.ne').trans (congrArg m hy).symm))
  have hprop := hR.isProportional hW₀ ((h.degree_eq_zero_iff σ σ'' hw W).mp hW0)
  have hray : W.ray = j := hprop.ray_eq fun ρ hρ hρj => hj ρ hρ.ne' hρj
  refine ⟨σ'', hw, fun ρ => ⟨fun hρ => ?_, fun hρ => ?_⟩⟩
  · rcases W.eq_or_le ρ hρ with hρr | hρσ
    · exact Or.inl (hρr.trans hray)
    · exact Or.inr ⟨hρσ, fun hρk => hk'' (by rw [← hρk]; exact hρ)⟩
  · rcases hρ with hρj | ⟨hρσ, hρk⟩
    · rw [hρj, ← hray]
      exact W.ray_le
    · exact hother ρ hρσ hρk

end IsRaySupport

/-! ### The circuit cones and the link -/

variable (F) in
/-- The cone `cone(u_{J₊ ∪ J₋ ∖ {k}})` of the generators of the rays `ρ ≠ k` with `c ρ ≠ 0`. For the class `c` of a wall curve and `k` in `J₊`, these are the maximal cones of the circuit fan `Circuit.fan`. -/
noncomputable def circuitCone (c : F.Ray → ℝ) (k : F.Ray) : PointedCone ℝ (NR n) :=
  PointedCone.hull ℝ {x | ∃ ρ : F.Ray, (c ρ ≠ 0 ∧ ρ ≠ k) ∧ toNR (F.generator ρ) = x}

variable (F) in
/-- The cone of the generators of the rays of `σ` outside the circuit of `c`, the rays `ρ` with `c ρ = 0`. -/
noncomputable def linkCone (c : F.Ray → ℝ) (σ : PointedCone ℝ (NR n)) : PointedCone ℝ (NR n) :=
  PointedCone.hull ℝ {x | ∃ ρ : F.Ray, (ρ.1 ≤ σ ∧ c ρ = 0) ∧ toNR (F.generator ρ) = x}

variable (F) in
/-- The link of the star of `cone(u_{J₋})`: the cones `Fan.linkCone c σ` for the maximal cones `σ` that contain `cone(u_{J₋})`. -/
def link (c : F.Ray → ℝ) : Set (PointedCone ℝ (NR n)) :=
  {L | ∃ τ, F.IsMaximalCone τ ∧ F.negCone c ≤ τ ∧ F.linkCone c τ = L}

/-- A cone of the fan is the cone of the generators of its rays, described by a property of the rays. -/
theorem eq_hull_of_forall_le_iff {σ : PointedCone ℝ (NR n)} (hσ : σ ∈ F.cones)
    {P : F.Ray → Prop} (h : ∀ ρ : F.Ray, ρ.1 ≤ σ ↔ P ρ) :
    σ = PointedCone.hull ℝ {x | ∃ ρ : F.Ray, P ρ ∧ toNR (F.generator ρ) = x} := by
  refine (F.eq_hull_generator hσ).trans ?_
  simp only [h]

/-- The cone of the generators of the rays with one of two properties is the sum of the two cones. -/
theorem hull_or (A B : F.Ray → Prop) :
    PointedCone.hull ℝ {x | ∃ ρ : F.Ray, (A ρ ∨ B ρ) ∧ toNR (F.generator ρ) = x} =
      PointedCone.hull ℝ {x | ∃ ρ : F.Ray, A ρ ∧ toNR (F.generator ρ) = x} ⊔
        PointedCone.hull ℝ {x | ∃ ρ : F.Ray, B ρ ∧ toNR (F.generator ρ) = x} := by
  have hset : {x | ∃ ρ : F.Ray, (A ρ ∨ B ρ) ∧ toNR (F.generator ρ) = x} =
      {x | ∃ ρ : F.Ray, A ρ ∧ toNR (F.generator ρ) = x} ∪
        {x | ∃ ρ : F.Ray, B ρ ∧ toNR (F.generator ρ) = x} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_union, or_and_right, exists_or]
  rw [hset]
  exact Submodule.span_union _ _

/-- Two cones with the same rays outside the circuit have the same link cone. -/
theorem linkCone_congr {c : F.Ray → ℝ} {σ τ : PointedCone ℝ (NR n)}
    (h : ∀ ρ : F.Ray, c ρ = 0 → (ρ.1 ≤ σ ↔ ρ.1 ≤ τ)) : F.linkCone c σ = F.linkCone c τ := by
  unfold linkCone
  congr 1
  ext x
  exact exists_congr fun ρ =>
    and_congr ⟨fun hρ => ⟨(h ρ hρ.2).mp hρ.1, hρ.2⟩, fun hρ => ⟨(h ρ hρ.2).mpr hρ.1, hρ.2⟩⟩
      Iff.rfl

/-- The link cone of a cone of a simplicial fan is a face of it, so a cone of the fan. -/
theorem linkCone_mem (hs : F.IsSimplicialFan) {σ : PointedCone ℝ (NR n)} (hσ : σ ∈ F.cones)
    (c : F.Ray → ℝ) : F.linkCone c σ ∈ F.cones := by
  have hli := linearIndependent_generator hσ (hs σ hσ)
  have hface := LinearIndependent.indexCone_isFaceOf hli
    {ρ : {ρ : F.Ray // ρ.1 ≤ σ} | c ρ.1 = 0}
  rw [← eq_indexCone_generator hσ] at hface
  have heq : F.linkCone c σ = indexCone (fun ρ : {ρ : F.Ray // ρ.1 ≤ σ} => toNR (F.generator ρ.1))
      {ρ : {ρ : F.Ray // ρ.1 ≤ σ} | c ρ.1 = 0} := by
    unfold linkCone indexCone
    congr 1
    ext x
    constructor
    · rintro ⟨ρ, ⟨hρ, h0⟩, rfl⟩
      exact ⟨⟨ρ, hρ⟩, h0, rfl⟩
    · rintro ⟨ρ, h0, rfl⟩
      exact ⟨ρ.1, ⟨ρ.2, h0⟩, rfl⟩
  rw [heq]
  exact F.face_mem σ hσ _ hface

/-- A cone of the fan that contains all the rays `ρ ≠ j` with `c ρ ≠ 0`, but not `j`, is `cone(u_{J₊ ∪ J₋ ∖ {j}}) + λ`, with `λ` its link cone. -/
theorem eq_circuitCone_sup_linkCone {σ : PointedCone ℝ (NR n)} (hσ : σ ∈ F.cones)
    {c : F.Ray → ℝ} {j : F.Ray} (hjσ : ¬ j.1 ≤ σ) (hj : ∀ ρ : F.Ray, c ρ ≠ 0 → ρ ≠ j → ρ.1 ≤ σ) :
    σ = F.circuitCone c j ⊔ F.linkCone c σ := by
  refine (eq_hull_of_forall_le_iff hσ
    (P := fun ρ => (c ρ ≠ 0 ∧ ρ ≠ j) ∨ (ρ.1 ≤ σ ∧ c ρ = 0)) fun ρ =>
      ⟨fun hρ => ?_, fun hρ => ?_⟩).trans
    (hull_or (fun ρ : F.Ray => c ρ ≠ 0 ∧ ρ ≠ j) fun ρ : F.Ray => ρ.1 ≤ σ ∧ c ρ = 0)
  · by_cases h0 : c ρ = 0
    · exact Or.inr ⟨hρ, h0⟩
    · exact Or.inl ⟨h0, fun hρj => hjσ (by rw [← hρj]; exact hρ)⟩
  · rcases hρ with ⟨h0, hρj⟩ | ⟨hρ, -⟩
    · exact hj ρ h0 hρj
    · exact hρ

/-! ### The star -/

variable {R : PointedCone ℝ (F.Ray → ℝ)}

/-- **A cone of the star** contains all the rays of the circuit of `R` but one ray `j` of `J₊`. So it is `cone(u_{J₊ ∪ J₋ ∖ {j}}) + λ`, with `λ` its link cone (`Fan.eq_circuitCone_sup_linkCone`). -/
theorem IsExtremalRay.exists_ray_not_le (hc : F.IsComplete) (hs : F.IsSimplicialFan)
    (hR : F.IsExtremalRay R) {σ₀ σ₀' : PointedCone ℝ (NR n)} (hw₀ : F.IsWallPair σ₀ σ₀')
    (W₀ : F.WallData σ₀ σ₀') (hW₀ : W₀.curveClass ∈ R) {σ : PointedCone ℝ (NR n)}
    (hσ : F.IsMaximalCone σ) (hneg : F.negCone W₀.curveClass ≤ σ) :
    ∃ j : F.Ray, 0 < W₀.curveClass j ∧ ¬ j.1 ≤ σ ∧
      ∀ ρ : F.Ray, W₀.curveClass ρ ≠ 0 → ρ ≠ j → ρ.1 ≤ σ := by
  obtain ⟨D, φ, h⟩ := hR.exists_isRaySupport hc hs
  exact h.exists_ray_not_le hc hs hR hw₀ W₀ hW₀ hσ (negCone_le_iff.mp hneg)

/-- **Crossing a wall of the star.** Let `σ` be a cone of the star, `j` the ray of the circuit of `R` that is not in `σ`, and `k ≠ j` another ray of `J₊`. The neighbour of `σ` across the facet opposite `k` has the rays of `σ` and `j`, but not `k`. -/
theorem IsExtremalRay.exists_exchange (hc : F.IsComplete) (hs : F.IsSimplicialFan)
    (hR : F.IsExtremalRay R) {σ₀ σ₀' : PointedCone ℝ (NR n)} (hw₀ : F.IsWallPair σ₀ σ₀')
    (W₀ : F.WallData σ₀ σ₀') (hW₀ : W₀.curveClass ∈ R) {σ : PointedCone ℝ (NR n)}
    (hσ : F.IsMaximalCone σ) (hneg : F.negCone W₀.curveClass ≤ σ) {j : F.Ray}
    (hcj : 0 < W₀.curveClass j) (hjσ : ¬ j.1 ≤ σ)
    (hj : ∀ ρ : F.Ray, W₀.curveClass ρ ≠ 0 → ρ ≠ j → ρ.1 ≤ σ) {k : F.Ray}
    (hk : 0 < W₀.curveClass k) (hkj : k ≠ j) :
    ∃ σ'', F.IsWallPair σ σ'' ∧ ∀ ρ : F.Ray, ρ.1 ≤ σ'' ↔ ρ = j ∨ (ρ.1 ≤ σ ∧ ρ ≠ k) := by
  obtain ⟨D, φ, h⟩ := hR.exists_isRaySupport hc hs
  exact h.exists_exchange hc hs hR hw₀ W₀ hW₀ hσ (negCone_le_iff.mp hneg) hcj hjσ hj hk hkj

/-- **The neighbour in the star.** In the situation of `Fan.IsExtremalRay.exists_exchange`, the neighbour `σ''` of `σ` is in the star, it is `cone(u_{J₊ ∪ J₋ ∖ {k}}) + λ` with `λ` the link cone of `σ`, and it has the same link cone as `σ`. -/
theorem IsExtremalRay.exists_eq_circuitCone_sup_linkCone (hc : F.IsComplete)
    (hs : F.IsSimplicialFan) (hR : F.IsExtremalRay R) {σ₀ σ₀' : PointedCone ℝ (NR n)}
    (hw₀ : F.IsWallPair σ₀ σ₀') (W₀ : F.WallData σ₀ σ₀') (hW₀ : W₀.curveClass ∈ R)
    {σ : PointedCone ℝ (NR n)} (hσ : F.IsMaximalCone σ) (hneg : F.negCone W₀.curveClass ≤ σ)
    {j : F.Ray} (hcj : 0 < W₀.curveClass j) (hjσ : ¬ j.1 ≤ σ)
    (hj : ∀ ρ : F.Ray, W₀.curveClass ρ ≠ 0 → ρ ≠ j → ρ.1 ≤ σ) {k : F.Ray}
    (hk : 0 < W₀.curveClass k) (hkj : k ≠ j) :
    ∃ σ'', F.IsWallPair σ σ'' ∧ F.negCone W₀.curveClass ≤ σ'' ∧
      σ'' = F.circuitCone W₀.curveClass k ⊔ F.linkCone W₀.curveClass σ ∧
      F.linkCone W₀.curveClass σ'' = F.linkCone W₀.curveClass σ := by
  obtain ⟨σ'', hw, hchar⟩ := hR.exists_exchange hc hs hw₀ W₀ hW₀ hσ hneg hcj hjσ hj hk hkj
  have hneg' := negCone_le_iff.mp hneg
  refine ⟨σ'', hw, negCone_le_iff.mpr fun ρ hρ => (hchar ρ).mpr (Or.inr ⟨hneg' ρ hρ, ?_⟩), ?_,
    linkCone_congr fun ρ h0 => ?_⟩
  · rintro rfl
    exact absurd hk (not_lt.mpr hρ.le)
  · refine (eq_hull_of_forall_le_iff hw.2.1.mem
      (P := fun ρ => (W₀.curveClass ρ ≠ 0 ∧ ρ ≠ k) ∨ (ρ.1 ≤ σ ∧ W₀.curveClass ρ = 0))
        fun ρ => ⟨fun hρ => ?_, fun hρ => ?_⟩).trans
      (hull_or (fun ρ : F.Ray => W₀.curveClass ρ ≠ 0 ∧ ρ ≠ k)
        fun ρ : F.Ray => ρ.1 ≤ σ ∧ W₀.curveClass ρ = 0)
    · rcases (hchar ρ).mp hρ with hρj | ⟨hρσ, hρk⟩
      · rw [hρj]
        exact Or.inl ⟨hcj.ne', hkj.symm⟩
      · by_cases h0 : W₀.curveClass ρ = 0
        · exact Or.inr ⟨hρσ, h0⟩
        · exact Or.inl ⟨h0, hρk⟩
    · refine (hchar ρ).mpr ?_
      rcases hρ with ⟨h0, hρk⟩ | ⟨hρσ, h0⟩
      · by_cases hρj : ρ = j
        · exact Or.inl hρj
        · exact Or.inr ⟨hj ρ h0 hρj, hρk⟩
      · refine Or.inr ⟨hρσ, ?_⟩
        rintro rfl
        exact hk.ne' h0
  · constructor
    · intro hρ
      rcases (hchar ρ).mp hρ with hρj | ⟨hρσ, -⟩
      · rw [hρj] at h0
        exact absurd h0 hcj.ne'
      · exact hρσ
    · intro hρ
      refine (hchar ρ).mpr (Or.inr ⟨hρ, ?_⟩)
      rintro rfl
      exact hk.ne' h0

/-- **The star of `cone(u_{J₋})`** (Reid 1983, Corollary 2.5; Matsuki, Proposition 14-2-1; Cox, Little and Schenck, Proposition 15.4.5). Let `F` be a complete simplicial fan, `R` an extremal ray, and `c` the class of a wall curve in `R`. A maximal cone of `F` contains `cone(u_{J₋})` exactly when it is `cone(u_{J₊ ∪ J₋ ∖ {k}}) + λ` for a ray `k` of `J₊` and a cone `λ` of the link. -/
theorem IsExtremalRay.star_iff (hc : F.IsComplete) (hs : F.IsSimplicialFan)
    (hR : F.IsExtremalRay R) {σ₀ σ₀' : PointedCone ℝ (NR n)} (hw₀ : F.IsWallPair σ₀ σ₀')
    (W₀ : F.WallData σ₀ σ₀') (hW₀ : W₀.curveClass ∈ R) (σ : PointedCone ℝ (NR n)) :
    F.IsMaximalCone σ ∧ F.negCone W₀.curveClass ≤ σ ↔
      ∃ k : F.Ray, 0 < W₀.curveClass k ∧
        ∃ L ∈ F.link W₀.curveClass, σ = F.circuitCone W₀.curveClass k ⊔ L := by
  constructor
  · rintro ⟨hσ, hneg⟩
    obtain ⟨j, hj, hjσ, hjr⟩ := hR.exists_ray_not_le hc hs hw₀ W₀ hW₀ hσ hneg
    exact ⟨j, hj, F.linkCone W₀.curveClass σ, ⟨σ, hσ, hneg, rfl⟩,
      eq_circuitCone_sup_linkCone hσ.mem hjσ hjr⟩
  · rintro ⟨k, hk, L, ⟨τ, hτ, hneg, rfl⟩, rfl⟩
    obtain ⟨j, hj, hjτ, hjr⟩ := hR.exists_ray_not_le hc hs hw₀ W₀ hW₀ hτ hneg
    by_cases hkj : k = j
    · rw [hkj, ← eq_circuitCone_sup_linkCone hτ.mem hjτ hjr]
      exact ⟨hτ, hneg⟩
    · obtain ⟨σ'', hw, hneg'', heq, -⟩ :=
        hR.exists_eq_circuitCone_sup_linkCone hc hs hw₀ W₀ hW₀ hτ hneg hj hjτ hjr hk hkj
      rw [← heq]
      exact ⟨hw.2.1, hneg''⟩

/-- **The star of `cone(u_{J₋})`** as a set: the maximal cones of `F` that contain `cone(u_{J₋})` are the cones `cone(u_{J₊ ∪ J₋ ∖ {k}}) + λ`, with `k` a ray of `J₊` and `λ` a cone of the link. -/
theorem IsExtremalRay.star (hc : F.IsComplete) (hs : F.IsSimplicialFan)
    (hR : F.IsExtremalRay R) {σ₀ σ₀' : PointedCone ℝ (NR n)} (hw₀ : F.IsWallPair σ₀ σ₀')
    (W₀ : F.WallData σ₀ σ₀') (hW₀ : W₀.curveClass ∈ R) :
    {σ | F.IsMaximalCone σ ∧ F.negCone W₀.curveClass ≤ σ} =
      {σ | ∃ k : F.Ray, 0 < W₀.curveClass k ∧
        ∃ L ∈ F.link W₀.curveClass, σ = F.circuitCone W₀.curveClass k ⊔ L} :=
  Set.ext fun σ => hR.star_iff hc hs hw₀ W₀ hW₀ σ

/-- The cones of the link are cones of the fan. -/
theorem link_subset (hs : F.IsSimplicialFan) (c : F.Ray → ℝ) : F.link c ⊆ F.cones := by
  rintro _ ⟨τ, hτ, -, rfl⟩
  exact linkCone_mem hs hτ.mem c

end Fan

end MinimalModel.Toric
