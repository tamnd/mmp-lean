/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import MinimalModel.Toric.FlipRay

/-!
# Toric flips, part 4: crossing a facet, and the neighbours across the walls of a ray

This file continues step 3 of the route to `flipExists` in `MinimalModel/Toric/Flip.lean` (route R3, spec 04.4), the star of the exceptional locus (Reid 1983, Section 2; Matsuki, Section 14-2).

## Crossing a facet

Let `F` be a complete fan with closed cones, for instance a complete simplicial fan, let `σ` be a cone of `F` of dimension `n`, and let `τ` be a cone of `F` in `σ` of dimension `n - 1`, a facet of `σ`. Then there is a maximal cone `σ'` of `F` on the other side of `τ`: the cones `σ` and `σ'` meet in a wall, and `σ ∩ σ' = τ` (`Fan.exists_isWallPair_of_le`). The proof is the usual one. Let `p` be the sum of the generators of the rays of `τ`, a point of the relative interior of `τ`: a face of `σ` that contains `p` contains `τ`. Let `u` be a point of `σ` outside the span of `τ`. The points `p - t u` with `t > 0` are not in `σ`, since `τ` is a face of `σ`. The cones of `F` that do not contain `p` form a closed set, so for small `t` the point `p - t u` lies in a cone `C` of `F` that contains `p`. Then `C ∩ σ` is a face of `σ` that contains `p`, so it contains `τ`. A maximal cone `σ'` that contains `C` is different from `σ`, and `σ ∩ σ'` is a face of `σ` that contains `τ` and has dimension less than `n`, so it is `τ`.

For a simplicial cone `σ` of dimension `n` and a ray `ρ` of `σ`, the generators of the other rays span a facet of `σ` (`LinearIndependent.indexCone_isFaceOf`). So there is a maximal cone `σ'` that meets `σ` in a wall, with `ρ` not in `σ'` and each other ray of `σ` in `σ'` (`Fan.exists_isWallPair_of_ray`).

## The neighbours across the walls of a ray

Let `W` be a wall whose curve spans an extremal ray `R`, and let `W'` be the data of another wall `τ ∩ τ'` of `R`, so that `W` and `W'` have proportional classes. The ray `ρ'` of `τ'` that is not in `τ` has a positive coefficient in the class of `W'`, so it has a positive coefficient in the class of `W` (`Fan.WallData.IsProportional.curveClass_ray_pos`): it is a ray of `J₊`. So when `τ` contains all the rays of `J₊` but one, `ρ`, the new ray is `ρ` (`Fan.WallData.IsProportional.ray_eq`), and the neighbour is `τ' = (τ ∩ τ') + ρ` (`Fan.WallData.IsProportional.eq_inf_sup`). This is how the star of `cone(u_{J₋})` is the join of the circuit fan with a link: crossing a wall of `R` from a cone `cone(u_{≠ j}) + λ` of the join leads to the cone `cone(u_{≠ k}) + λ` with the same `λ`.

## Main results

* `coneDim_mono`: a smaller cone has a smaller dimension.
* `Fan.isMaximalCone_of_coneDim_eq`: a cone of dimension `n` is maximal.
* `Fan.le_of_isFaceOf_of_sum_mem`: a face that contains the sum of the generators of the rays of a cone `τ` contains `τ`.
* `Fan.exists_isWallPair_of_le`, `Fan.exists_isWallPair_of_le_of_isSimplicialFan`: a facet of a cone of dimension `n` of a complete fan is the wall of a wall pair.
* `LinearIndependent.indexCone_isFaceOf`: the cones of the subsets of a linearly independent family are faces of the cone of the family.
* `Fan.exists_isWallPair_of_ray`: in a complete simplicial fan, each cone of dimension `n` has a neighbour across the facet opposite each of its rays.
* `Fan.WallData.IsProportional.curveClass_ray_pos`, `Fan.WallData.IsProportional.ray_eq`, `Fan.WallData.IsProportional.eq_inf_sup`: the neighbour across a wall of a ray.
-/

open Topology Filter

namespace MinimalModel.Toric

variable {n : ℕ}

/-- A smaller cone has a smaller dimension. -/
theorem coneDim_mono {τ σ : PointedCone ℝ (NR n)} (h : τ ≤ σ) : coneDim τ ≤ coneDim σ :=
  Submodule.finrank_mono (Submodule.span_mono (SetLike.coe_subset_coe.mpr h))

section IndexCone

variable {ι E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The linear span of the cone of a set of indices is the span of the vectors of the set. -/
theorem span_indexCone (v : ι → E) (T : Set ι) :
    Submodule.span ℝ (indexCone v T : Set E) = Submodule.span ℝ (v '' T) := by
  unfold indexCone
  exact Submodule.span_span_of_tower ..

/-- The cone of a set of indices contains the vectors of the set. -/
theorem mem_indexCone_of_mem (v : ι → E) {T : Set ι} {i : ι} (hi : i ∈ T) :
    v i ∈ indexCone v T := by
  unfold indexCone
  exact Submodule.subset_span ⟨i, hi, rfl⟩

/-- The cone of a set of indices of a linearly independent family is a face of the cone of the family. So the faces of a simplicial cone are the cones of the subsets of its generators. -/
theorem LinearIndependent.indexCone_isFaceOf [Fintype ι] {v : ι → E}
    (hv : LinearIndependent ℝ v) (T : Set ι) :
    (indexCone v T).IsFaceOf (indexCone v Set.univ) := by
  refine ⟨indexCone_mono v (Set.subset_univ T), fun {x y r} hx hy hr hxy => ?_⟩
  obtain ⟨c, hc, -, rfl⟩ := mem_indexCone.mp hx
  obtain ⟨d, hd, -, rfl⟩ := mem_indexCone.mp hy
  obtain ⟨e, -, heT, hexy⟩ := mem_indexCone.mp hxy
  have h1 : ∑ i, (r * c i + d i) • v i = ∑ i, e i • v i := by
    rw [hexy]
    simp only [add_smul, Finset.sum_add_distrib, mul_smul, Finset.smul_sum]
  have h0 := Fintype.linearIndependent_iff.mp hv (fun i => r * c i + d i - e i)
    (by simp only [sub_smul, Finset.sum_sub_distrib, h1, sub_self])
  refine mem_indexCone.mpr ⟨c, hc, fun i hi => ?_, rfl⟩
  have h2 : r * c i + d i - e i = 0 := h0 i
  rw [heT i hi] at h2
  have h3 := mul_nonneg hr.le (hc i)
  have h4 := hd i
  have h5 : r * c i = 0 := by linarith
  rcases mul_eq_zero.mp h5 with h6 | h6
  · exact absurd h6 hr.ne'
  · exact h6

end IndexCone

namespace Fan

variable {F : Fan n} {σ τ : PointedCone ℝ (NR n)}

/-! ### Crossing a facet -/

/-- A cone of the fan of dimension `n` is a maximal cone: a cone of the fan that contains it meets it in a face with the same span. -/
theorem isMaximalCone_of_coneDim_eq (hσ : σ ∈ F.cones) (hdim : coneDim σ = n) :
    F.IsMaximalCone σ := by
  refine ⟨hσ, ?_⟩
  intro C hC hle
  have hface : (σ ⊓ C).IsFaceOf C := F.inter_face_right hσ hC
  rw [inf_eq_left.mpr hle] at hface
  refine le_of_isFaceOf_of_span_le hface ?_
  rw [span_eq_top_of_coneDim_eq hdim]
  exact le_top

/-- A face `G` of a cone that contains the sum of the generators of the rays of a cone `τ` of the fan contains `τ`. The sum is a point of the relative interior of `τ`. -/
theorem le_of_isFaceOf_of_sum_mem (hτ : τ ∈ F.cones) {G C : PointedCone ℝ (NR n)}
    (hG : G.IsFaceOf C) (hτC : τ ≤ C)
    (hp : ∑ ρ : {ρ : F.Ray // ρ.1 ≤ τ}, toNR (F.generator ρ.1) ∈ G) : τ ≤ G := by
  refine (F.eq_hull_generator hτ).le.trans (Submodule.span_le.mpr ?_)
  rintro _ ⟨ρ, hρ, rfl⟩
  exact hG.mem_of_sum_mem (f := fun ρ : {ρ : F.Ray // ρ.1 ≤ τ} => toNR (F.generator ρ.1))
    (fun ρ => hτC (ρ.2 (F.toNR_generator_mem ρ.1))) hp ⟨ρ, hρ⟩

/-- **Crossing a facet.** Let `F` be a complete fan with closed cones, `σ` a cone of `F` of dimension `n`, and `τ` a cone of `F` in `σ` of dimension `n - 1`. Then there is a maximal cone `σ'` of `F` such that `σ` and `σ'` meet in a wall, and the wall is `τ`. The proof is in the module docstring. -/
theorem exists_isWallPair_of_le (hc : F.IsComplete)
    (hcl : ∀ C ∈ F.cones, IsClosed (C : Set (NR n))) (hσ : σ ∈ F.cones) (hdim : coneDim σ = n)
    (hτ : τ ∈ F.cones) (hτσ : τ ≤ σ) (hτdim : coneDim τ + 1 = n) :
    ∃ σ', F.IsWallPair σ σ' ∧ σ ⊓ σ' = τ := by
  classical
  have hmax := isMaximalCone_of_coneDim_eq hσ hdim
  have hτface : τ.IsFaceOf σ := by
    have h := F.inter_face σ hσ τ hτ
    rwa [inf_eq_right.mpr hτσ] at h
  -- a point of the relative interior of `τ`
  have hpτ : ∑ ρ : {ρ : F.Ray // ρ.1 ≤ τ}, toNR (F.generator ρ.1) ∈ τ :=
    Submodule.sum_mem _ fun ρ _ => ρ.2 (F.toNR_generator_mem ρ.1)
  -- a vector of `σ` outside the span of `τ`
  obtain ⟨u, huσ, huτ⟩ : ∃ u ∈ σ, u ∉ Submodule.span ℝ (τ : Set (NR n)) := by
    by_contra h
    push Not at h
    have hle : Submodule.span ℝ (σ : Set (NR n)) ≤ Submodule.span ℝ (τ : Set (NR n)) :=
      Submodule.span_le.mpr fun x hx => h x hx
    rw [span_eq_top_of_coneDim_eq hdim] at hle
    have h2 : coneDim τ = n := by
      unfold coneDim
      rw [eq_top_iff.mpr hle, finrank_top, Module.finrank_fin_fun]
    omega
  -- the points `p - t • u` with `t > 0` are not in `σ`
  have hnot : ∀ t : ℝ, 0 < t →
      ∑ ρ : {ρ : F.Ray // ρ.1 ≤ τ}, toNR (F.generator ρ.1) - t • u ∉ σ := by
    intro t ht hq
    have h1 : ∑ ρ : {ρ : F.Ray // ρ.1 ≤ τ}, toNR (F.generator ρ.1) - t • u + t • u ∈ τ := by
      rw [sub_add_cancel]
      exact hpτ
    have h2 : t • u ∈ τ :=
      hτface.mem_of_add_mem_right hq (PointedCone.smul_mem σ ht.le huσ) h1
    apply huτ
    have h3 : t⁻¹ • (t • u) ∈ Submodule.span ℝ (τ : Set (NR n)) :=
      Submodule.smul_mem _ _ (Submodule.subset_span h2)
    rwa [inv_smul_smul₀ ht.ne'] at h3
  -- for small `t`, the point `p - t • u` is in a cone of the fan that contains `p`
  have hK : IsClosed (⋃ C ∈ {C ∈ F.cones |
      ∑ ρ : {ρ : F.Ray // ρ.1 ≤ τ}, toNR (F.generator ρ.1) ∉ C}, (C : Set (NR n))) :=
    (F.finite.subset (Set.sep_subset _ _)).isClosed_biUnion fun C hC => hcl C hC.1
  have hpK : ∑ ρ : {ρ : F.Ray // ρ.1 ≤ τ}, toNR (F.generator ρ.1) ∉ ⋃ C ∈ {C ∈ F.cones |
      ∑ ρ : {ρ : F.Ray // ρ.1 ≤ τ}, toNR (F.generator ρ.1) ∉ C}, (C : Set (NR n)) := by
    intro h
    obtain ⟨C, hC, hpC⟩ := Set.mem_iUnion₂.mp h
    exact hC.2 hpC
  have hγ : Tendsto (fun t : ℝ => ∑ ρ : {ρ : F.Ray // ρ.1 ≤ τ}, toNR (F.generator ρ.1) - t • u)
      (𝓝 0) (𝓝 (∑ ρ : {ρ : F.Ray // ρ.1 ≤ τ}, toNR (F.generator ρ.1))) :=
    (by fun_prop : Continuous fun t : ℝ =>
      ∑ ρ : {ρ : F.Ray // ρ.1 ≤ τ}, toNR (F.generator ρ.1) - t • u).tendsto' 0 _ (by simp)
  obtain ⟨t, ht0, htK⟩ := ((eventually_mem_nhdsWithin (s := Set.Ioi (0 : ℝ)) (a := 0)).and
    ((hγ.eventually (hK.isOpen_compl.mem_nhds hpK)).filter_mono nhdsWithin_le_nhds)).exists
  have ht0' : (0 : ℝ) < t := ht0
  obtain ⟨C, hC, hqC⟩ := exists_mem_of_isComplete hc
    (∑ ρ : {ρ : F.Ray // ρ.1 ≤ τ}, toNR (F.generator ρ.1) - t • u)
  have hpC : ∑ ρ : {ρ : F.Ray // ρ.1 ≤ τ}, toNR (F.generator ρ.1) ∈ C := by
    by_contra hpC
    exact htK (Set.mem_iUnion₂.mpr ⟨C, ⟨hC, hpC⟩, hqC⟩)
  -- the cone `C` contains `τ`
  have hτC : τ ≤ C :=
    (le_of_isFaceOf_of_sum_mem hτ (F.inter_face σ hσ C hC) hτσ
      (Submodule.mem_inf.mpr ⟨hτσ hpτ, hpC⟩)).trans inf_le_right
  obtain ⟨σ', hCσ', hmax'⟩ := F.exists_le_isMaximalCone hC
  have hne : σ ≠ σ' := by
    rintro rfl
    exact hnot t ht0' (hCσ' hqC)
  have hτle : τ ≤ σ ⊓ σ' := le_inf hτσ (hτC.trans hCσ')
  have hlt := hmax.coneDim_inf_lt hmax' hne
  have hge := coneDim_mono hτle
  rw [hdim] at hlt
  have hdim' : coneDim (σ ⊓ σ') + 1 = n := by omega
  refine ⟨σ', ⟨hmax, hmax', hne, hdim'⟩, le_antisymm ?_ hτle⟩
  -- the face `σ ⊓ σ'` of `σ` has the span of `τ`, so it is `τ`
  have hτface' : τ.IsFaceOf (σ ⊓ σ') :=
    (hτface.isFaceOf_iff_le (F.inter_face σ hσ σ' hmax'.mem)).mpr hτle
  refine le_of_isFaceOf_of_span_le hτface' ?_
  have hspan : Submodule.span ℝ (τ : Set (NR n)) ≤
      Submodule.span ℝ ((σ ⊓ σ' : PointedCone ℝ (NR n)) : Set (NR n)) :=
    Submodule.span_mono (SetLike.coe_subset_coe.mpr hτle)
  refine (Submodule.eq_of_le_of_finrank_eq hspan ?_).ge
  show coneDim τ = coneDim (σ ⊓ σ')
  omega

/-- **Crossing a facet** in a complete simplicial fan: a cone `τ` of the fan of dimension `n - 1` in a cone `σ` of dimension `n` is the wall `σ ∩ σ'` of a wall pair. -/
theorem exists_isWallPair_of_le_of_isSimplicialFan (hc : F.IsComplete) (hs : F.IsSimplicialFan)
    (hσ : σ ∈ F.cones) (hdim : coneDim σ = n) (hτ : τ ∈ F.cones) (hτσ : τ ≤ σ)
    (hτdim : coneDim τ + 1 = n) : ∃ σ', F.IsWallPair σ σ' ∧ σ ⊓ σ' = τ :=
  exists_isWallPair_of_le hc (fun C hC => (hs C hC).isClosed) hσ hdim hτ hτσ hτdim

/-- A cone of the fan is the cone of the generators of its rays, as an `indexCone`. -/
theorem eq_indexCone_generator (hσ : σ ∈ F.cones) :
    σ = indexCone (fun ρ : {ρ : F.Ray // ρ.1 ≤ σ} => toNR (F.generator ρ.1)) Set.univ := by
  refine (F.eq_hull_generator hσ).trans ?_
  unfold indexCone
  congr 1
  ext x
  constructor
  · rintro ⟨ρ, hρ, rfl⟩
    exact ⟨⟨ρ, hρ⟩, Set.mem_univ _, rfl⟩
  · rintro ⟨ρ, -, rfl⟩
    exact ⟨ρ.1, ρ.2, rfl⟩

/-- **The neighbour across the facet opposite a ray.** Let `F` be a complete simplicial fan, `σ` a cone of `F` of dimension `n`, and `ρ` a ray of `σ`. Then there is a maximal cone `σ'` such that `σ` and `σ'` meet in a wall, `ρ` is not in `σ'`, and each other ray of `σ` is in `σ'`. The wall is the facet of `σ` spanned by the generators of the rays other than `ρ`. -/
theorem exists_isWallPair_of_ray (hc : F.IsComplete) (hs : F.IsSimplicialFan) (hσ : σ ∈ F.cones)
    (hdim : coneDim σ = n) (ρ : F.Ray) (hρ : ρ.1 ≤ σ) :
    ∃ σ', F.IsWallPair σ σ' ∧ ¬ ρ.1 ≤ σ' ∧ ∀ ρ' : F.Ray, ρ'.1 ≤ σ → ρ' ≠ ρ → ρ'.1 ≤ σ' := by
  classical
  have hli : LinearIndependent ℝ fun ρ : {ρ : F.Ray // ρ.1 ≤ σ} => toNR (F.generator ρ.1) :=
    linearIndependent_generator hσ (hs σ hσ)
  have hσv := eq_indexCone_generator hσ
  have hface := LinearIndependent.indexCone_isFaceOf hli ({⟨ρ, hρ⟩}ᶜ : Set {ρ : F.Ray // ρ.1 ≤ σ})
  rw [← hσv] at hface
  have hτ := F.face_mem σ hσ _ hface
  -- the generator of `ρ` is not in the span of the facet
  have hρτ : toNR (F.generator ρ) ∉ Submodule.span ℝ
      (indexCone (fun ρ : {ρ : F.Ray // ρ.1 ≤ σ} => toNR (F.generator ρ.1))
        ({⟨ρ, hρ⟩}ᶜ : Set {ρ : F.Ray // ρ.1 ≤ σ}) : Set (NR n)) := by
    rw [span_indexCone]
    exact hli.notMem_span_image (x := ⟨ρ, hρ⟩) (by simp)
  -- the facet has dimension `n - 1`
  have hlt : coneDim (indexCone (fun ρ : {ρ : F.Ray // ρ.1 ≤ σ} => toNR (F.generator ρ.1))
      ({⟨ρ, hρ⟩}ᶜ : Set {ρ : F.Ray // ρ.1 ≤ σ})) < n := by
    by_contra hge
    have heq := le_antisymm (coneDim_le _) (not_lt.mp hge)
    apply hρτ
    rw [span_eq_top_of_coneDim_eq heq]
    exact Submodule.mem_top
  have hge : n ≤ coneDim (indexCone (fun ρ : {ρ : F.Ray // ρ.1 ≤ σ} => toNR (F.generator ρ.1))
      ({⟨ρ, hρ⟩}ᶜ : Set {ρ : F.Ray // ρ.1 ≤ σ})) + 1 := by
    have hspan : Submodule.span ℝ (σ : Set (NR n)) ≤
        Submodule.span ℝ (indexCone (fun ρ : {ρ : F.Ray // ρ.1 ≤ σ} => toNR (F.generator ρ.1))
          ({⟨ρ, hρ⟩}ᶜ : Set {ρ : F.Ray // ρ.1 ≤ σ}) : Set (NR n)) ⊔
        Submodule.span ℝ {toNR (F.generator ρ)} := by
      have e : Submodule.span ℝ (σ : Set (NR n)) = Submodule.span ℝ
          (indexCone (fun ρ : {ρ : F.Ray // ρ.1 ≤ σ} => toNR (F.generator ρ.1)) Set.univ :
            Set (NR n)) := by
        rw [← hσv]
      rw [e, span_indexCone, Submodule.span_le]
      rintro _ ⟨ρ', -, rfl⟩
      by_cases h' : ρ' = ⟨ρ, hρ⟩
      · rw [h']
        exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
      · exact Submodule.mem_sup_left (Submodule.subset_span
          (mem_indexCone_of_mem _ (Set.mem_compl_singleton_iff.mpr h')))
    rw [span_eq_top_of_coneDim_eq hdim] at hspan
    have h1 := Submodule.finrank_mono hspan
    have h2 := Submodule.finrank_add_le_finrank_add_finrank
      (Submodule.span ℝ (indexCone (fun ρ : {ρ : F.Ray // ρ.1 ≤ σ} => toNR (F.generator ρ.1))
        ({⟨ρ, hρ⟩}ᶜ : Set {ρ : F.Ray // ρ.1 ≤ σ}) : Set (NR n)))
      (Submodule.span ℝ {toNR (F.generator ρ)})
    have h3 : Module.finrank ℝ (Submodule.span ℝ ({toNR (F.generator ρ)} : Set (NR n))) ≤ 1 :=
      (finrank_span_le_card ({toNR (F.generator ρ)} : Set (NR n))).trans (by simp)
    rw [finrank_top, Module.finrank_fin_fun] at h1
    change _ ≤ coneDim (indexCone (fun ρ : {ρ : F.Ray // ρ.1 ≤ σ} => toNR (F.generator ρ.1))
      ({⟨ρ, hρ⟩}ᶜ : Set {ρ : F.Ray // ρ.1 ≤ σ})) + _ at h2
    omega
  obtain ⟨σ', hw, hinf⟩ := exists_isWallPair_of_le_of_isSimplicialFan hc hs hσ hdim hτ hface.le
    (by omega)
  refine ⟨σ', hw, fun hρσ' => ?_, fun ρ' hρ' hne => ?_⟩
  · apply hρτ
    have h : toNR (F.generator ρ) ∈ σ ⊓ σ' :=
      Submodule.mem_inf.mpr ⟨hρ (F.toNR_generator_mem ρ), hρσ' (F.toNR_generator_mem ρ)⟩
    rw [hinf] at h
    exact Submodule.subset_span h
  · have h : toNR (F.generator ρ') ∈
        indexCone (fun ρ : {ρ : F.Ray // ρ.1 ≤ σ} => toNR (F.generator ρ.1))
          ({⟨ρ, hρ⟩}ᶜ : Set {ρ : F.Ray // ρ.1 ≤ σ}) :=
      mem_indexCone_of_mem (fun ρ : {ρ : F.Ray // ρ.1 ≤ σ} => toNR (F.generator ρ.1))
        (i := ⟨ρ', hρ'⟩)
        (Set.mem_compl_singleton_iff.mpr fun h => hne (congrArg Subtype.val h))
    rw [← hinf] at h
    rw [← F.latticeCone_generator ρ']
    exact latticeCone_singleton_le.mpr (Submodule.mem_inf.mp h).2

/-! ### The neighbours across the walls of a ray -/

namespace WallData

variable {σ' τ' : PointedCone ℝ (NR n)} {W : F.WallData σ σ'} {W' : F.WallData τ τ'}

/-- Let `W` and `W'` be walls with proportional classes. The ray `ρ'` of the second cone of `W'` that is not in the first one has a positive coefficient in the class of `W`: it is a ray of `J₊`. -/
theorem IsProportional.curveClass_ray_pos (h : W.IsProportional W') :
    0 < W.curveClass W'.ray := by
  obtain ⟨t, ht, hc⟩ := isProportional_iff.mp h
  have h1 : W'.curveClass W'.ray = t * W.curveClass W'.ray := by
    rw [hc, Pi.smul_apply, smul_eq_mul]
  rw [W'.curveClass_ray] at h1
  by_contra h2
  have := mul_nonpos_of_nonneg_of_nonpos ht.le (not_lt.mp h2)
  linarith

/-- **The new ray across a wall of a ray.** Let `W'` be a wall `τ ∩ τ'` whose class is proportional to the class of `W`, and let `τ` contain each ray of `J₊` of `W` other than `ρ`. Then the ray of `τ'` that is not in `τ` is `ρ`. -/
theorem IsProportional.ray_eq (h : W.IsProportional W') {ρ : F.Ray}
    (hρ : ∀ ρ' : F.Ray, 0 < W.curveClass ρ' → ρ' ≠ ρ → ρ'.1 ≤ τ) : W'.ray = ρ := by
  by_contra hne
  exact W'.ray_not_le (hρ W'.ray h.curveClass_ray_pos hne)

/-- **The neighbour across a wall of a ray.** In the situation of `IsProportional.ray_eq`, the cone `τ'` is the sum of the wall `τ ∩ τ'` and the ray `ρ`. So crossing a wall of the ray from a cone `cone(u_{≠ j}) + λ` of the star leads to the cone `cone(u_{≠ k}) + λ`, with the same cone `λ` of the link. -/
theorem IsProportional.eq_inf_sup (hτ' : τ' ∈ F.cones) (h : W.IsProportional W') {ρ : F.Ray}
    (hρ : ∀ ρ' : F.Ray, 0 < W.curveClass ρ' → ρ' ≠ ρ → ρ'.1 ≤ τ) : τ' = (τ ⊓ τ') ⊔ ρ.1 := by
  apply le_antisymm
  · refine (F.eq_hull_generator hτ').le.trans (Submodule.span_le.mpr ?_)
    rintro _ ⟨ρ', hρ', rfl⟩
    rcases W'.eq_or_le ρ' hρ' with rfl | hle
    · rw [h.ray_eq hρ]
      exact Submodule.mem_sup_right (F.toNR_generator_mem ρ)
    · exact Submodule.mem_sup_left
        (Submodule.mem_inf.mpr ⟨hle (F.toNR_generator_mem ρ'), hρ' (F.toNR_generator_mem ρ')⟩)
  · refine sup_le inf_le_right ?_
    rw [← h.ray_eq hρ]
    exact W'.ray_le

end WallData

end Fan

end MinimalModel.Toric
