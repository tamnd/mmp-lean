/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import MinimalModel.Toric.ConeClosed

/-!
# Toric flips, part 5: a nef divisor that supports an extremal ray

This file continues step 3 of the route to `flipExists` in `MinimalModel/Toric/Flip.lean` (route R3, spec 04.4). It gives the divisor of Reid 1983, Section 2, that supports an extremal ray `R` of the cone of curves: a divisor `D` with `D · C ≥ 0` on each wall curve `C`, and `D · C = 0` exactly on the wall curves of `R`. Its support function bends across each wall, so it is nef, and it is linear across exactly the walls of `R`.

## The class of a wall is determined by the wall

Let `F` be a simplicial fan and `σ, σ'` two maximal cones that meet in a wall. Two data `W, W'` of the wall have the same class (`Fan.WallData.curveClass_eq`). The ray of `σ'` that is not in `σ` is unique (`Fan.IsWallPair.eq_of_not_le`), so `W` and `W'` have the same ray `ρ'`, where both classes are `1`. Outside `σ` and `ρ'` both classes vanish. So the difference of the classes is a linear relation among the generators of the rays of `σ`, which are linearly independent, and it is zero. As `F` has finitely many cones, there are finitely many classes of wall curves (`Fan.finite_curveClasses`), and the cone of curves is finitely generated.

## The supporting divisor

The extremal ray `R` is a face of the finitely generated cone of curves, so it is exposed (`exists_linearMap_of_isFaceOf`): there is a linear form `m` on `ℝ^{Σ(1)}` that is nonnegative on the cone of curves and vanishes on it exactly on `R` (`Fan.IsExtremalRay.exists_linearMap`). The divisor `D = Σ m(e_ρ) D_ρ` pairs with the class of a wall curve as `m` does, so its degree on a wall is nonnegative, and it is zero exactly on the walls of `R` (`Fan.IsExtremalRay.exists_tDivisor`). By `Fan.WallData.degree_nonneg_iff`, each support function of `D` satisfies the wall inequality across each wall.

## Main results

* `Fan.WallData.curveClass_eq`: in a simplicial fan, the class of a wall curve depends only on the wall.
* `Fan.finite_curveClasses`, `Fan.curveCone_fg`: there are finitely many classes of wall curves, and the cone of curves is finitely generated.
* `Fan.isClosed_curveCone`: the cone of curves is closed.
* `Fan.IsExtremalRay.exists_linearMap`: an extremal ray is cut out of the cone of curves by a nonnegative linear form.
* `Fan.IsExtremalRay.exists_tDivisor`: a divisor whose degree is nonnegative on each wall, and zero exactly on the walls of the ray, and whose support functions bend across each wall.
* `Fan.exists_isWallPair_of_le_of_isComplete`: crossing a facet in a complete fan, with no hypothesis on the cones, since the cones of a fan are closed.
-/

open Set

namespace MinimalModel.Toric

variable {n : ℕ}

namespace Fan

variable {F : Fan n}

/-- **Crossing a facet** in a complete fan. The cones of a fan are closed (`Fan.isClosed_of_mem`), so `Fan.exists_isWallPair_of_le` holds with no hypothesis on the cones: a cone `τ` of dimension `n - 1` in a cone `σ` of dimension `n` is the wall `σ ∩ σ'` of a wall pair. -/
theorem exists_isWallPair_of_le_of_isComplete {σ τ : PointedCone ℝ (NR n)} (hc : F.IsComplete)
    (hσ : σ ∈ F.cones) (hdim : coneDim σ = n) (hτ : τ ∈ F.cones) (hτσ : τ ≤ σ)
    (hτdim : coneDim τ + 1 = n) : ∃ σ', F.IsWallPair σ σ' ∧ σ ⊓ σ' = τ :=
  exists_isWallPair_of_le hc (fun _ hC => F.isClosed_of_mem hC) hσ hdim hτ hτσ hτdim

/-- Two maximal cones that meet in a wall, in the other order. -/
theorem IsWallPair.symm {σ σ' : PointedCone ℝ (NR n)} (hw : F.IsWallPair σ σ') :
    F.IsWallPair σ' σ :=
  ⟨hw.2.1, hw.1, hw.2.2.1.symm, by rw [inf_comm]; exact hw.2.2.2⟩

namespace WallData

variable {σ σ' : PointedCone ℝ (NR n)}

/-- The class of a wall curve vanishes at a ray that is not in `σ` and is not the ray `ρ'`. -/
theorem curveClass_eq_zero_of_not_le (W : F.WallData σ σ') {ρ : F.Ray} (h₁ : ρ ≠ W.ray)
    (h₂ : ¬ ρ.1 ≤ σ) : W.curveClass ρ = 0 :=
  W.curveClass_eq_zero fun i hi => by
    cases i with
    | none => exact h₁ hi.symm
    | some ρ' =>
      rw [circuitRay_some] at hi
      subst hi
      exact h₂ ρ'.2

/-- **The class of a wall curve depends only on the wall.** In a simplicial fan, two data of the same wall `σ ∩ σ'` have the same class. -/
theorem curveClass_eq (hs : F.IsSimplicialFan) (hw : F.IsWallPair σ σ') (W W' : F.WallData σ σ') :
    W.curveClass = W'.curveClass := by
  classical
  have hσ := hw.1.mem
  have hray : W.ray = W'.ray :=
    IsWallPair.eq_of_not_le (hs σ' hw.2.1.mem) hw.symm W.ray_le W.ray_not_le W'.ray_le
      W'.ray_not_le
  -- the difference of the classes vanishes outside `σ`
  have hzero : ∀ ρ : F.Ray, ¬ ρ.1 ≤ σ → W.curveClass ρ - W'.curveClass ρ = 0 := by
    intro ρ hρ
    by_cases hr : ρ = W.ray
    · rw [hr, W.curveClass_ray, hray, W'.curveClass_ray, sub_self]
    · rw [W.curveClass_eq_zero_of_not_le hr hρ,
        W'.curveClass_eq_zero_of_not_le (by rw [← hray]; exact hr) hρ, sub_self]
  -- the difference is a relation among the generators of the rays of `σ`
  have hall : ∑ ρ, (W.curveClass ρ - W'.curveClass ρ) • toNR (F.generator ρ) = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, W.sum_curveClass_smul_generator hσ (hs σ hσ),
      W'.sum_curveClass_smul_generator hσ (hs σ hσ), sub_self]
  have hsub : ∑ ρ : {ρ : F.Ray // ρ.1 ≤ σ},
      (W.curveClass ρ.1 - W'.curveClass ρ.1) • toNR (F.generator ρ.1) = 0 := by
    have h1 : ∑ ρ ∈ Finset.univ.filter (fun ρ : F.Ray => ρ.1 ≤ σ),
        (W.curveClass ρ - W'.curveClass ρ) • toNR (F.generator ρ) =
        ∑ ρ : {ρ : F.Ray // ρ.1 ≤ σ},
          (W.curveClass ρ.1 - W'.curveClass ρ.1) • toNR (F.generator ρ.1) :=
      Finset.sum_subtype _ (fun ρ => by simp) _
    have h2 : ∑ ρ ∈ Finset.univ.filter (fun ρ : F.Ray => ρ.1 ≤ σ),
        (W.curveClass ρ - W'.curveClass ρ) • toNR (F.generator ρ) =
        ∑ ρ, (W.curveClass ρ - W'.curveClass ρ) • toNR (F.generator ρ) :=
      Finset.sum_subset (Finset.subset_univ _) fun ρ _ hρ => by
        rw [hzero ρ (by simpa using hρ), zero_smul]
    rw [← h1, h2, hall]
  funext ρ
  by_cases hρ : ρ.1 ≤ σ
  · have h : W.curveClass ρ - W'.curveClass ρ = 0 :=
      Fintype.linearIndependent_iff.mp (linearIndependent_generator hσ (hs σ hσ))
        (fun ρ => W.curveClass ρ.1 - W'.curveClass ρ.1) hsub ⟨ρ, hρ⟩
    exact sub_eq_zero.mp h
  · exact sub_eq_zero.mp (hzero ρ hρ)

end WallData

variable (F) in
/-- The classes of the curves of the walls of the fan, the generators of the cone of curves. -/
def curveClasses : Set (F.Ray → ℝ) :=
  {c | ∃ σ σ' : PointedCone ℝ (NR n), F.IsWallPair σ σ' ∧ ∃ W : F.WallData σ σ', W.curveClass = c}

/-- The cone of curves is the conic hull of the classes of the wall curves. -/
theorem curveCone_eq_hull : F.curveCone = PointedCone.hull ℝ F.curveClasses := rfl

/-- In a simplicial fan, the classes of the curve of one wall form a subsingleton. -/
theorem subsingleton_curveClasses_wall (hs : F.IsSimplicialFan) (σ σ' : PointedCone ℝ (NR n)) :
    {c : F.Ray → ℝ | F.IsWallPair σ σ' ∧ ∃ W : F.WallData σ σ', W.curveClass = c}.Subsingleton := by
  rintro c ⟨hw, W, rfl⟩ c' ⟨-, W', rfl⟩
  exact WallData.curveClass_eq hs hw W W'

/-- **There are finitely many classes of wall curves** in a simplicial fan: a fan has finitely many cones, and the class of a wall curve depends only on the wall. -/
theorem finite_curveClasses (hs : F.IsSimplicialFan) : F.curveClasses.Finite := by
  refine (F.finite.biUnion fun σ _ => F.finite.biUnion fun σ' _ =>
    (subsingleton_curveClasses_wall hs σ σ').finite).subset ?_
  rintro c ⟨σ, σ', hw, W, rfl⟩
  exact Set.mem_biUnion hw.1.mem (Set.mem_biUnion hw.2.1.mem ⟨hw, W, rfl⟩)

/-- **The cone of curves of a simplicial fan is finitely generated.** -/
theorem curveCone_fg (hs : F.IsSimplicialFan) : F.curveCone.FG := by
  obtain ⟨S, hS⟩ := (finite_curveClasses hs).exists_finset_coe
  exact ⟨S, by rw [hS]; rfl⟩

/-- **The cone of curves of a simplicial fan is closed.** -/
theorem isClosed_curveCone (hs : F.IsSimplicialFan) : IsClosed (F.curveCone : Set (F.Ray → ℝ)) :=
  isClosed_hull_of_finite (finite_curveClasses hs)

/-- **An extremal ray is exposed.** In a simplicial fan, there is a linear form `m` on `ℝ^{Σ(1)}` that is nonnegative on the cone of curves and vanishes on it exactly on the extremal ray `R`. -/
theorem IsExtremalRay.exists_linearMap (hs : F.IsSimplicialFan)
    {R : PointedCone ℝ (F.Ray → ℝ)} (hR : F.IsExtremalRay R) :
    ∃ m : (F.Ray → ℝ) →ₗ[ℝ] ℝ, (∀ c ∈ F.curveCone, 0 ≤ m c) ∧
      ∀ c ∈ F.curveCone, m c = 0 ↔ c ∈ R := by
  have := (finite_curveClasses hs).fintype
  have heq : F.curveCone = indexCone (Subtype.val : F.curveClasses → F.Ray → ℝ) univ :=
    hull_eq_indexCone_val _
  have hface := hR.1
  rw [heq] at hface ⊢
  exact exists_linearMap_of_isFaceOf hface

/-- **A nef divisor that supports an extremal ray** (Reid 1983, Section 2). Let `F` be a simplicial fan and `R` an extremal ray of its cone of curves. There is a divisor `D` whose degree on each wall is nonnegative, and zero exactly on the walls whose curves lie in `R`. Each support function of `D` satisfies the wall inequality across each wall (`Fan.WallData.degree_nonneg_iff`): it bends across the walls, and it is linear across exactly the walls of `R`. -/
theorem IsExtremalRay.exists_tDivisor (hs : F.IsSimplicialFan) {R : PointedCone ℝ (F.Ray → ℝ)}
    (hR : F.IsExtremalRay R) :
    ∃ D : F.TDivisor ℝ,
      (∀ σ σ' : PointedCone ℝ (NR n), F.IsWallPair σ σ' → ∀ W : F.WallData σ σ',
        0 ≤ W.degree D) ∧
      (∀ σ σ' : PointedCone ℝ (NR n), F.IsWallPair σ σ' → ∀ W : F.WallData σ σ',
        (W.degree D = 0 ↔ W.curveClass ∈ R)) ∧
      ∀ φ : NR n → ℝ, F.IsSupportFunctionOf D φ → ∀ σ σ' : PointedCone ℝ (NR n),
        F.IsWallPair σ σ' → F.WallData σ σ' → IsConvexAcross φ σ σ' := by
  classical
  obtain ⟨m, hm0, hmR⟩ := hR.exists_linearMap hs
  let D : F.TDivisor ℝ :=
    Finsupp.equivFunOnFinite.symm fun ρ => m fun ρ' => if ρ = ρ' then 1 else 0
  have hdeg : ∀ (σ σ' : PointedCone ℝ (NR n)) (W : F.WallData σ σ'),
      W.degree D = m W.curveClass := by
    intro σ σ' W
    rw [W.degree_eq_sum_curveClass, LinearMap.pi_apply_eq_sum_univ m W.curveClass]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    simp [D]
  have hnonneg : ∀ σ σ' : PointedCone ℝ (NR n), F.IsWallPair σ σ' → ∀ W : F.WallData σ σ',
      0 ≤ W.degree D := fun σ σ' hw W => by
    rw [hdeg]
    exact hm0 _ (W.curveClass_mem_curveCone hw)
  refine ⟨D, hnonneg, fun σ σ' hw W => ?_, fun φ hφ σ σ' hw W => ?_⟩
  · rw [hdeg]
    exact hmR _ (W.curveClass_mem_curveCone hw)
  · exact (W.degree_nonneg_iff hw.1.mem hw.2.1.mem hφ).mp (hnonneg σ σ' hw W)

end Fan

end MinimalModel.Toric
