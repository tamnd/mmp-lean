/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import MinimalModel.Toric.FlipStar

/-!
# Toric flips, part 5: finitely generated cones are closed, Farkas' lemma, exposed faces

This file gives three facts of convex geometry that step 3 of the route to `flipExists` in `MinimalModel/Toric/Flip.lean` needs (route R3, spec 04.4), and that Mathlib at our pin does not have for `PointedCone`. Mathlib has Farkas' lemma for closed cones, `ProperCone.hyperplane_separation_point`, and the closedness of simplicial cones of the form of `IsSimplicial.isClosed`, but not the closedness of a finitely generated cone, nor Minkowski–Weyl (`Mathlib/Geometry/Convex/Cone/DualFinite.lean` states the definitions only).

## Carathéodory's theorem for cones

A point of the cone of a finite family `v` is in the cone of a linearly independent subfamily (`exists_linearIndepOn_mem_indexCone`). The proof is the usual one. Write `x = Σ cᵢ vᵢ` with `cᵢ ≥ 0` supported on `T`. When the `vᵢ` with `i ∈ T` are dependent, there is a relation `Σ gᵢ vᵢ = 0` supported on `T` with some `gᵢ > 0`. Let `j` be an index with `gⱼ > 0` where `cᵢ / gᵢ` is least. Then `c - (cⱼ / gⱼ) g` is a nonnegative combination for `x` supported on `T \ {j}`, and we conclude by induction on `T`.

## Closedness

The cone of a linearly independent finite family is the image of the closed orthant under an injective linear map with a finite-dimensional domain, a closed embedding, so it is closed. By Carathéodory's theorem, the cone of a finite family is the union of the cones of its linearly independent subfamilies, a finite union of closed sets (`isClosed_indexCone`). This holds in each Hausdorff topological vector space over `ℝ`, without finite dimension. So finitely generated pointed cones are closed (`isClosed_hull_of_finite`, `isClosed_of_fg`), and so are the cones of a fan (`Fan.isClosed_of_mem`).

## Farkas' lemma and exposed faces

A finitely generated cone is closed, so it is a `ProperCone`, and Farkas' lemma of Mathlib applies: a point outside the cone of a finite family is separated from it by a continuous linear form that is nonnegative on the family (`exists_dual_of_notMem_indexCone`). As a consequence, each face `G` of a finitely generated cone `C` is exposed: there is a linear form that is nonnegative on `C` and vanishes on `C` exactly on `G` (`exists_linearMap_of_isFaceOf`). For a generator `vᵢ` outside `G`, the point `-vᵢ` is not in `C - G`, since `G` is a face, and Farkas' lemma for the finitely generated cone `C - G` gives a form `fᵢ` that is nonnegative on `C`, zero on `G` and positive at `vᵢ`. The sum of the `fᵢ` is the form.

## Main results

* `exists_linearIndepOn_mem_indexCone`: Carathéodory's theorem for cones.
* `isClosed_indexCone`, `isClosed_hull_of_finite`, `isClosed_of_fg`: finitely generated cones are closed.
* `Fan.isClosed_of_mem`: the cones of a fan are closed.
* `exists_dual_of_notMem_indexCone`, `exists_dual_of_notMem_hull`, `exists_linearMap_of_notMem_hull`: Farkas' lemma for finitely generated cones.
* `exists_linearMap_of_isFaceOf`: each face of a finitely generated cone is exposed.
-/

open Set Pointwise

namespace MinimalModel.Toric

variable {n : ℕ}

section Caratheodory

variable {ι E : Type*} [Fintype ι] [AddCommGroup E] [Module ℝ E]

/-- **Carathéodory's theorem for cones**, the form with coefficients. Let `c` be nonnegative coefficients supported on a finite set `T` of indices. Then the combination `Σ cᵢ vᵢ` is in the cone of a subset `S` of `T` on which the family `v` is linearly independent. -/
theorem exists_linearIndepOn_of_sum (v : ι → E) (T : Finset ι) :
    ∀ c : ι → ℝ, (∀ i, 0 ≤ c i) → (∀ i, i ∉ T → c i = 0) →
      ∃ S ⊆ T, LinearIndepOn ℝ v (S : Set ι) ∧ ∑ i, c i • v i ∈ indexCone v (S : Set ι) := by
  classical
  refine Finset.strongInduction (p := fun T : Finset ι => ∀ c : ι → ℝ, (∀ i, 0 ≤ c i) →
    (∀ i, i ∉ T → c i = 0) →
      ∃ S ⊆ T, LinearIndepOn ℝ v (S : Set ι) ∧ ∑ i, c i • v i ∈ indexCone v (S : Set ι))
    (fun T ih => ?_) T
  intro c hc hcT
  by_cases hT : LinearIndepOn ℝ v (T : Set ι)
  · exact ⟨T, subset_rfl, hT, mem_indexCone.mpr ⟨c, hc, fun i hi => hcT i hi, rfl⟩⟩
  -- a relation supported on `T` with a positive coefficient
  obtain ⟨g, hgT, hg, i₀, hi₀⟩ : ∃ g : ι → ℝ, (∀ i, i ∉ T → g i = 0) ∧ ∑ i, g i • v i = 0 ∧
      ∃ i₀, 0 < g i₀ := by
    rw [linearIndepOn_iff'] at hT
    push Not at hT
    obtain ⟨t, g, hts, hg, i₀, hi₀t, hi₀⟩ := hT
    have hg' : ∑ i, (if i ∈ t then g i else 0) • v i = 0 := by
      simp [ite_smul, Finset.sum_ite_mem, hg]
    have ht' : ∀ i, i ∉ T → (if i ∈ t then g i else 0) = 0 := fun i hi => by
      have hit : i ∉ t := fun h => hi (hts h)
      simp [hit]
    rcases lt_or_gt_of_ne hi₀ with hneg | hpos
    · refine ⟨fun i => -(if i ∈ t then g i else 0), fun i hi => by simp only [ht' i hi, neg_zero],
        ?_, i₀, ?_⟩
      · simp only [neg_smul, Finset.sum_neg_distrib, hg', neg_zero]
      · show 0 < -(if i₀ ∈ t then g i₀ else 0)
        simp only [hi₀t, ↓reduceIte]
        linarith
    · refine ⟨fun i => if i ∈ t then g i else 0, ht', hg', i₀, ?_⟩
      show 0 < (if i₀ ∈ t then g i₀ else 0)
      simpa only [hi₀t, ↓reduceIte] using hpos
  have hi₀T : i₀ ∈ T := by
    by_contra h
    have := hgT i₀ h
    linarith
  -- the index `j` where `cᵢ / gᵢ` is least among the indices with `gᵢ > 0`
  obtain ⟨j, hjP, hjmin⟩ := Finset.exists_min_image (T.filter fun i => 0 < g i)
    (fun i => c i / g i) ⟨i₀, Finset.mem_filter.mpr ⟨hi₀T, hi₀⟩⟩
  obtain ⟨hjT, hgj⟩ := Finset.mem_filter.mp hjP
  have hl0 : 0 ≤ c j / g j := div_nonneg (hc j) hgj.le
  have hc' : ∀ i, 0 ≤ c i - c j / g j * g i := by
    intro i
    by_cases hgi : 0 < g i
    · by_cases hiT : i ∈ T
      · have h1 : c j / g j ≤ c i / g i := hjmin i (Finset.mem_filter.mpr ⟨hiT, hgi⟩)
        rw [le_div_iff₀ hgi] at h1
        linarith
      · simp [hcT i hiT, hgT i hiT]
    · have := mul_nonpos_of_nonneg_of_nonpos hl0 (not_lt.mp hgi)
      linarith [hc i]
  have hc'T : ∀ i, i ∉ T.erase j → c i - c j / g j * g i = 0 := by
    intro i hi
    by_cases hij : i = j
    · rw [hij, div_mul_cancel₀ (c j) hgj.ne', sub_self]
    · have hiT : i ∉ T := fun h => hi (Finset.mem_erase.mpr ⟨hij, h⟩)
      rw [hcT i hiT, hgT i hiT, mul_zero, sub_zero]
  have hsum : ∑ i, (c i - c j / g j * g i) • v i = ∑ i, c i • v i := by
    simp only [sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, hg, smul_zero,
      sub_zero]
  obtain ⟨S, hS, hli, hmem⟩ := ih (T.erase j) (Finset.erase_ssubset hjT)
    (fun i => c i - c j / g j * g i) hc' hc'T
  refine ⟨S, hS.trans (Finset.erase_subset j T), hli, ?_⟩
  rw [← hsum]
  exact hmem

/-- **Carathéodory's theorem for cones.** A point of the cone of the vectors `v i` with `i ∈ T` is in the cone of a subset `S` of `T` on which the family `v` is linearly independent. -/
theorem exists_linearIndepOn_mem_indexCone {v : ι → E} {T : Set ι} {x : E}
    (hx : x ∈ indexCone v T) : ∃ S ⊆ T, LinearIndepOn ℝ v S ∧ x ∈ indexCone v S := by
  classical
  obtain ⟨c, hc, hcT, rfl⟩ := mem_indexCone.mp hx
  obtain ⟨S, hS, hli, hmem⟩ := exists_linearIndepOn_of_sum v T.toFinset c hc
    (fun i hi => hcT i (by simpa using hi))
  exact ⟨S, fun i hi => by simpa using hS hi, hli, hmem⟩

/-- The cone of a family indexed by the points of a set is the conic hull of the set. -/
theorem hull_eq_indexCone_val (s : Set E) [Fintype s] :
    PointedCone.hull ℝ s = indexCone (Subtype.val : s → E) univ := by
  unfold indexCone
  rw [Set.image_univ, Subtype.range_coe]

end Caratheodory

section Closed

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [T2Space E]

/-- The cone of a linearly independent finite family is closed: it is the image of the closed orthant under an injective linear map with a finite-dimensional domain. -/
theorem LinearIndependent.isClosed_indexCone_univ {ι : Type*} [Fintype ι] {v : ι → E}
    (hv : LinearIndependent ℝ v) : IsClosed (indexCone v univ : Set E) := by
  have hf : Topology.IsClosedEmbedding (Fintype.linearCombination ℝ v) :=
    LinearMap.isClosedEmbedding_of_injective
      (LinearMap.ker_eq_bot.mpr hv.fintypeLinearCombination_injective)
  have heq : (indexCone v univ : Set E) =
      Fintype.linearCombination ℝ v '' {c | ∀ i, 0 ≤ c i} := by
    ext x
    rw [SetLike.mem_coe, mem_indexCone]
    constructor
    · rintro ⟨c, hc, -, rfl⟩
      exact ⟨c, hc, by rw [Fintype.linearCombination_apply]⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c, hc, fun i hi => absurd (mem_univ i) hi, by rw [Fintype.linearCombination_apply]⟩
  have hcl : IsClosed {c : ι → ℝ | ∀ i, 0 ≤ c i} := by
    rw [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  rw [heq]
  exact hf.isClosedMap _ hcl

/-- The cone of the vectors `v i` with `i ∈ S` is closed when the family is linearly independent on `S`. -/
theorem isClosed_indexCone_of_linearIndepOn {ι : Type*} [Fintype ι] {v : ι → E} {S : Set ι}
    (hS : LinearIndepOn ℝ v S) : IsClosed (indexCone v S : Set E) := by
  classical
  have h : indexCone v S = indexCone (fun i : S => v i) univ := by
    unfold indexCone
    rw [Set.image_univ, ← Set.image_eq_range]
  rw [h]
  exact LinearIndependent.isClosed_indexCone_univ (show LinearIndependent ℝ (fun i : S => v i) from hS)

/-- **A finitely generated cone is closed.** The cone of the vectors `v i` with `i ∈ T`, for a finite family `v`, is closed. By Carathéodory's theorem it is the union of the cones of the linearly independent subfamilies, a finite union of closed sets. -/
theorem isClosed_indexCone {ι : Type*} [Fintype ι] (v : ι → E) (T : Set ι) :
    IsClosed (indexCone v T : Set E) := by
  classical
  have h : (indexCone v T : Set E) =
      ⋃ S ∈ {S : Set ι | S ⊆ T ∧ LinearIndepOn ℝ v S}, (indexCone v S : Set E) := by
    ext x
    rw [Set.mem_iUnion₂]
    constructor
    · intro hx
      obtain ⟨S, hST, hS, hxS⟩ := exists_linearIndepOn_mem_indexCone hx
      exact ⟨S, ⟨hST, hS⟩, hxS⟩
    · rintro ⟨S, ⟨hST, -⟩, hxS⟩
      exact indexCone_mono v hST hxS
  rw [h]
  exact (Set.toFinite _).isClosed_biUnion fun S hS => isClosed_indexCone_of_linearIndepOn hS.2

/-- **The conic hull of a finite set is closed.** -/
theorem isClosed_hull_of_finite {s : Set E} (hs : s.Finite) :
    IsClosed (PointedCone.hull ℝ s : Set E) := by
  have : Fintype s := hs.fintype
  rw [hull_eq_indexCone_val s]
  exact isClosed_indexCone _ _

/-- **A finitely generated pointed cone is closed.** -/
theorem isClosed_of_fg {C : PointedCone ℝ E} (hC : C.FG) : IsClosed (C : Set E) := by
  obtain ⟨S, rfl⟩ := hC
  exact isClosed_hull_of_finite S.finite_toSet

end Closed

/-- A rational polyhedral cone is closed. -/
theorem IsRationalPolyhedral.isClosed {σ : PointedCone ℝ (NR n)} (h : IsRationalPolyhedral σ) :
    IsClosed (σ : Set (NR n)) := by
  obtain ⟨S, rfl⟩ := h
  rw [latticeCone_eq_hull]
  exact isClosed_hull_of_finite (S.finite_toSet.image toNR)

/-- **The cones of a fan are closed.** So the hypothesis that the cones are closed in `Fan.exists_isWallPair_of_le` and in the toric cone theorem holds for each fan. -/
theorem Fan.isClosed_of_mem (F : Fan n) {σ : PointedCone ℝ (NR n)} (hσ : σ ∈ F.cones) :
    IsClosed (σ : Set (NR n)) :=
  (F.rational σ hσ).isClosed

section Farkas

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [T2Space E] [LocallyConvexSpace ℝ E]

/-- **Farkas' lemma for finitely generated cones.** A point `x` outside the cone of the vectors `v i` with `i ∈ T` is separated from the cone by a continuous linear form: the form is nonnegative at each `v i` with `i ∈ T` and negative at `x`. -/
theorem exists_dual_of_notMem_indexCone {ι : Type*} [Fintype ι] {v : ι → E} {T : Set ι} {x : E}
    (hx : x ∉ indexCone v T) : ∃ f : StrongDual ℝ E, (∀ i ∈ T, 0 ≤ f (v i)) ∧ f x < 0 := by
  let C : ProperCone ℝ E := { toSubmodule := indexCone v T, isClosed' := isClosed_indexCone v T }
  obtain ⟨f, hf, hfx⟩ := C.hyperplane_separation_point (x₀ := x) hx
  exact ⟨f, fun i hi => hf (v i) (mem_indexCone_of_mem v hi), hfx⟩

/-- **Farkas' lemma for the conic hull of a finite set.** A point outside the conic hull of a finite set `s` is separated from it by a continuous linear form that is nonnegative on `s`. -/
theorem exists_dual_of_notMem_hull {s : Set E} (hs : s.Finite) {x : E}
    (hx : x ∉ PointedCone.hull ℝ s) : ∃ f : StrongDual ℝ E, (∀ y ∈ s, 0 ≤ f y) ∧ f x < 0 := by
  have : Fintype s := hs.fintype
  rw [hull_eq_indexCone_val s] at hx
  obtain ⟨f, hf, hfx⟩ := exists_dual_of_notMem_indexCone hx
  exact ⟨f, fun y hy => hf ⟨y, hy⟩ (mem_univ _), hfx⟩

/-- **Farkas' lemma**, with a linear form: a point outside the conic hull of a finite set `s` is separated from it by a linear form that is nonnegative on `s`. -/
theorem exists_linearMap_of_notMem_hull {s : Set E} (hs : s.Finite) {x : E}
    (hx : x ∉ PointedCone.hull ℝ s) : ∃ m : E →ₗ[ℝ] ℝ, (∀ y ∈ s, 0 ≤ m y) ∧ m x < 0 := by
  obtain ⟨f, hf, hfx⟩ := exists_dual_of_notMem_hull hs hx
  exact ⟨f.toLinearMap, hf, hfx⟩

/-- Let `G` be a face of the cone of a finite family `v`, and `vᵢ` a vector of the family outside `G`. Then there is a linear form that is nonnegative at each `vⱼ`, zero at each `vⱼ` in `G`, and positive at `vᵢ`. -/
theorem exists_linearMap_pos_of_isFaceOf {ι : Type*} [Fintype ι] {v : ι → E}
    {G : PointedCone ℝ E} (hG : G.IsFaceOf (indexCone v univ)) {i : ι} (hi : v i ∉ G) :
    ∃ m : E →ₗ[ℝ] ℝ, (∀ j, 0 ≤ m (v j)) ∧ (∀ j, v j ∈ G → m (v j) = 0) ∧ 0 < m (v i) := by
  classical
  -- the cone `C - G`, spanned by the `vⱼ` and the `-vⱼ` with `vⱼ ∈ G`
  have hfin : (range v ∪ (fun j => -v j) '' {j | v j ∈ G}).Finite :=
    (finite_range v).union ((Set.toFinite _).image _)
  have hnot : -v i ∉ PointedCone.hull ℝ (range v ∪ (fun j => -v j) '' {j | v j ∈ G}) := by
    intro h
    rw [PointedCone.hull, Submodule.span_union] at h
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp h
    have hzG : z ∈ -G := by
      refine (Submodule.span_le.mpr ?_) hz
      rintro _ ⟨j, hj, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_neg, neg_neg]
      exact hj
    have hy' : y ∈ indexCone v univ := by
      unfold indexCone
      rw [Set.image_univ]
      exact hy
    have hsum : v i + y = -z := by
      rw [eq_neg_iff_add_eq_zero, add_assoc, hyz, add_neg_cancel]
    have hmem : v i + y ∈ G := by
      rw [hsum]
      exact Submodule.mem_neg.mp hzG
    exact hi (hG.mem_of_add_mem_left (mem_indexCone_of_mem v (mem_univ i)) hy' hmem)
  obtain ⟨m, hm, hmi⟩ := exists_linearMap_of_notMem_hull hfin hnot
  refine ⟨m, fun j => hm _ (Or.inl (mem_range_self j)), fun j hj => ?_, ?_⟩
  · have h1 := hm _ (Or.inl (mem_range_self j))
    have h2 := hm _ (Or.inr ⟨j, hj, rfl⟩)
    rw [map_neg] at h2
    linarith
  · rw [map_neg] at hmi
    linarith

/-- **Each face of a finitely generated cone is exposed.** Let `G` be a face of the cone `C` of a finite family `v`. Then there is a linear form `m` that is nonnegative on `C` and vanishes on `C` exactly on `G`. -/
theorem exists_linearMap_of_isFaceOf {ι : Type*} [Fintype ι] {v : ι → E}
    {G : PointedCone ℝ E} (hG : G.IsFaceOf (indexCone v univ)) :
    ∃ m : E →ₗ[ℝ] ℝ, (∀ x ∈ indexCone v univ, 0 ≤ m x) ∧
      ∀ x ∈ indexCone v univ, m x = 0 ↔ x ∈ G := by
  classical
  have H : ∀ i, ∃ m : E →ₗ[ℝ] ℝ, (∀ j, 0 ≤ m (v j)) ∧ (∀ j, v j ∈ G → m (v j) = 0) ∧
      (v i ∉ G → 0 < m (v i)) := by
    intro i
    by_cases hi : v i ∈ G
    · exact ⟨0, fun _ => le_rfl, fun _ _ => rfl, fun h => absurd hi h⟩
    · obtain ⟨m, h1, h2, h3⟩ := exists_linearMap_pos_of_isFaceOf hG hi
      exact ⟨m, h1, h2, fun _ => h3⟩
  choose g hg0 hgG hgpos using H
  -- the sum of the forms
  have hsum : ∀ x, (∑ i, g i) x = ∑ i, g i x := fun x => by simp
  have hm0 : ∀ j, 0 ≤ (∑ i, g i) (v j) := fun j => by
    rw [hsum]
    exact Finset.sum_nonneg fun i _ => hg0 i j
  have hmG : ∀ j, (∑ i, g i) (v j) = 0 ↔ v j ∈ G := by
    intro j
    rw [hsum]
    constructor
    · intro h
      by_contra hj
      have hpos : 0 < ∑ i, g i (v j) :=
        lt_of_lt_of_le (hgpos j hj) (Finset.single_le_sum (fun i _ => hg0 i j) (Finset.mem_univ j))
      linarith
    · intro hj
      exact Finset.sum_eq_zero fun i _ => hgG i j hj
  refine ⟨∑ i, g i, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨c, hc, -, rfl⟩ := mem_indexCone.mp hx
    rw [map_sum]
    exact Finset.sum_nonneg fun j _ => by
      rw [map_smul, smul_eq_mul]
      exact mul_nonneg (hc j) (hm0 j)
  · obtain ⟨c, hc, -, rfl⟩ := mem_indexCone.mp hx
    have hterm : ∀ j ∈ (Finset.univ : Finset ι), 0 ≤ (∑ i, g i) (c j • v j) := fun j _ => by
      rw [map_smul, smul_eq_mul]
      exact mul_nonneg (hc j) (hm0 j)
    rw [map_sum, Finset.sum_eq_zero_iff_of_nonneg hterm]
    constructor
    · intro h
      refine Submodule.sum_mem _ fun j _ => ?_
      have hj := h j (Finset.mem_univ j)
      rw [map_smul, smul_eq_mul] at hj
      rcases mul_eq_zero.mp hj with h0 | h0
      · rw [h0, zero_smul]
        exact zero_mem _
      · exact PointedCone.smul_mem _ (hc j) ((hmG j).mp h0)
    · intro hx' j _
      by_cases h0 : c j = 0
      · rw [h0, zero_smul, map_zero]
      have h1 : c j • v j ∈ indexCone v univ :=
        PointedCone.smul_mem _ (hc j) (mem_indexCone_of_mem v (mem_univ j))
      have h2 : ∑ k ∈ Finset.univ.erase j, c k • v k ∈ indexCone v univ :=
        Submodule.sum_mem _ fun k _ =>
          PointedCone.smul_mem _ (hc k) (mem_indexCone_of_mem v (mem_univ k))
      have h3 : c j • v j + ∑ k ∈ Finset.univ.erase j, c k • v k ∈ G := by
        rw [Finset.add_sum_erase _ (fun k => c k • v k) (Finset.mem_univ j)]
        exact hx'
      have h5 : (c j)⁻¹ • (c j • v j) ∈ G :=
        PointedCone.smul_mem _ (inv_nonneg.mpr (hc j)) (hG.mem_of_add_mem_left h1 h2 h3)
      rw [inv_smul_smul₀ h0] at h5
      rw [map_smul, smul_eq_mul, (hmG j).mpr h5, mul_zero]

end Farkas

end MinimalModel.Toric
