/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import MinimalModel.Toric.FlipContract

/-!
# Toric flips, part 8: the flipped fan

This file does step 4 of the route to `flipExists` in `MinimalModel/Toric/Flip.lean` (route R3, spec 04.4), the flipped fan `F⁺` (Reid 1983, Section 2 and Theorem 3.4; Matsuki, Section 14-2; Cox, Little and Schenck, Theorem 15.3.13 and Proposition 15.4.5).

Let `F` be a complete simplicial fan, `R` an extremal ray of its cone of curves, and `c` the class of a wall curve in `R`, with `J₊` and `J₋` the rays where `c` is positive and negative. For a maximal cone `ν` of `F` and a ray `j` of `J₋`, the cone `Fan.flipCone c ν j` is the cone of the generators of the rays `Fan.flipRays c ν j`. It is `ν` when `ν` is not in the star of `cone(u_{J₋})` (`Fan.flipCone_of_not_le`), and `cone(u_{J₊ ∪ J₋ ∖ {j}}) + λ` with `λ = Fan.linkCone c ν` when it is (`Fan.flipCone_of_le`). The flipped fan `Fan.flipped c` is the set of the faces of these cones. So it keeps the cones of `F` outside the star, and it replaces the star by the cones `cone(u_{J₊ ∪ J₋ ∖ {j}}) + λ` with `j ∈ J₋` and `λ` in the link (`Fan.mem_flipped_of_not_le`, `Fan.circuitCone_sup_mem_flipped`).

## The cones of the flipped fan are simplicial

The cone `Fan.flipCone c ν j` is in the cone `Fan.contractCone c ν` of the contraction (`Fan.flipCone_le_contractCone`). On the star, a linear relation among the generators of the rays of `K_ν` is a multiple `s c` of `c` (`Fan.IsExtremalRay.exists_eq_mul_of_sum_eq_zero`, from `Fan.eq_smul_of_sum_eq_zero`). A relation among the rays of `Fan.flipRays c ν j` vanishes at `j`, where `c` does not, so `s = 0`. Off the star, the rays are those of the simplicial cone `ν`. So the generators of `Fan.flipRays c ν j` are linearly independent (`Fan.IsExtremalRay.eq_zero_of_sum_eq_zero_flipRays`), the cone is simplicial (`Fan.IsExtremalRay.isSimplicial_flipCone`), and the cones of its subsets of rays are its faces (`Fan.IsExtremalRay.isFaceOf_flipCone`, from `indexCone_isFaceOf_of_forall`).

## Two cones meet in a face of each

The generator of a ray is in `K_ν` exactly when the ray is a ray of `K_ν` (`Fan.IsExtremalRay.generator_mem_contractCone_iff`), and `K_ν ∩ K_ν'` is a face of `K_ν` (`Fan.IsRaySupport.inf_isFaceOf`). So a nonnegative combination of generators of rays of `K_ν` that lies in `K_ν'` only uses rays of `K_ν'` (`Fan.IsExtremalRay.generator_mem_of_sum_mem`). Let `x = Σ b_ρ u_ρ = Σ b'_ρ u_ρ` be in `Fan.flipCone c ν j ∩ Fan.flipCone c ν' j'`, with `b` on the rays of the first cone and `b'` on those of the second. If `ν'` is off the star, `b` is on the rays of `K_ν' = ν'`, which are the rays of the second cone. If `ν` is off the star, `b'` works in the same way. If both are in the star, `b - b'` is a relation among the rays of `K_ν`, so `b - b' = s c`. At `j` it is `-b'_j ≤ 0` and at `j'` it is `b_{j'} ≥ 0`, while `c_j, c_{j'} < 0`, so `s = 0` and `b = b'`. In all cases `x` is in the cone of the common rays (`Fan.IsExtremalRay.flipCone_inf`), which is a face of each cone. So the flipped fan is a fan, `Fan.IsExtremalRay.flippedFan`, and it is simplicial (`Fan.IsExtremalRay.isSimplicialFan_flippedFan`).

## The flipped fan refines the contraction

Let `x = Σ b_ρ u_ρ` be in `K_ν`, with `b ≥ 0` on the rays of `K_ν`. When `ν` is in the star, let `j ∈ J₋` minimize `b_ρ / (-c_ρ)` over `J₋`, and `t = b_j / (-c_j)`. Then `b + t c` is nonnegative, vanishes at `j`, and still gives `x`, so `x ∈ Fan.flipCone c ν j` (`Fan.exists_mem_flipCone`). This is the argument of `IsCircuit.exists_mem_indexCone_compl` with `J₋` in place of `J₊`. So the cones `Fan.flipCone c ν j` cover `K_ν`, and the flipped fan has the same support as `F` (`Fan.IsExtremalRay.support_flippedFan`). The rays of `x` in a face `τ` of `K_ν` are in `τ`, so the face of `Fan.flipCone c ν j` that they span is a cone of `F⁺` in `τ` that contains `x`. So `F⁺` refines the contraction fan `G` (`Fan.IsExtremalRay.refines_flippedFan`). When `J₋` has two rays, each ray of `F` is a ray of `Fan.flipCone c ν j` for a maximal cone `ν` that contains it and a ray `j ∈ J₋` other than it, and each ray of `F⁺` is spanned by a generator of a ray of `F`. So the flipped fan has the same rays as `F` (`Fan.IsExtremalRay.rays_flippedFan`).

## Main results

* `Fan.flipped`, `Fan.flipCone`: the flipped fan of an extremal ray.
* `Fan.IsExtremalRay.flippedFan`, `Fan.IsExtremalRay.isSimplicialFan_flippedFan`: the flipped fan is a simplicial fan.
* `Fan.IsExtremalRay.support_flippedFan`, `Fan.IsExtremalRay.isComplete_flippedFan`: when `J₋` is not empty, it has the same support as `F`, so it is complete.
* `Fan.IsExtremalRay.refines_flippedFan`: it refines the contraction fan.
* `Fan.IsExtremalRay.rays_flippedFan`: when `J₋` has two rays, it has the same rays as `F`.
-/

open Set

namespace MinimalModel.Toric

variable {n : ℕ}

section IndexCone

variable {ι E : Type*} [Fintype ι] [AddCommGroup E] [Module ℝ E]

/-- The cones of the subsets of a set `S` of indices are faces of the cone of `S`, when the vectors `v i` with `i ∈ S` are linearly independent: a linear relation among them is zero. -/
theorem indexCone_isFaceOf_of_forall {v : ι → E} {S T : Set ι}
    (hS : ∀ d : ι → ℝ, (∀ i, i ∉ S → d i = 0) → ∑ i, d i • v i = 0 → ∀ i, d i = 0)
    (hTS : T ⊆ S) : (indexCone v T).IsFaceOf (indexCone v S) := by
  refine ⟨indexCone_mono v hTS, fun {x y r} hx hy hr hxy => ?_⟩
  obtain ⟨c, hc, hcS, rfl⟩ := mem_indexCone.mp hx
  obtain ⟨d, hd, hdS, rfl⟩ := mem_indexCone.mp hy
  obtain ⟨e, -, heT, hexy⟩ := mem_indexCone.mp hxy
  have h1 : ∑ i, (r * c i + d i) • v i = ∑ i, e i • v i := by
    rw [hexy]
    simp only [add_smul, Finset.sum_add_distrib, mul_smul, Finset.smul_sum]
  have h0 := hS (fun i => r * c i + d i - e i) (fun i hi => by
      show r * c i + d i - e i = 0
      rw [hcS i hi, hdS i hi, heT i fun h => hi (hTS h)]
      simp)
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

variable {F : Fan n}

/-- The cone of the generator of one ray is the ray. -/
theorem indexCone_singleton_generator (ρ : F.Ray) :
    indexCone (fun ρ : F.Ray => toNR (F.generator ρ)) {ρ} = ρ.1 := by
  rw [← F.latticeCone_generator ρ, latticeCone_eq_hull, Finset.coe_singleton, Set.image_singleton]
  unfold indexCone
  rw [Set.image_singleton]

/-! ### The flipped fan -/

variable (F) in
/-- The rays of the cone of the flipped fan for a maximal cone `ν` and a ray `j`: the rays of the cone `Fan.contractCone c ν` of the contraction, without `j` when `ν` contains `cone(u_{J₋})`. -/
def flipRays (c : F.Ray → ℝ) (ν : PointedCone ℝ (NR n)) (j : F.Ray) : Set F.Ray :=
  {ρ | (ρ.1 ≤ ν ∨ (F.negCone c ≤ ν ∧ c ρ ≠ 0)) ∧ (F.negCone c ≤ ν → ρ ≠ j)}

variable (F) in
/-- The cone of the flipped fan for a maximal cone `ν` and a ray `j` of `J₋`. It is `ν` when `ν` is not in the star of `cone(u_{J₋})` (`Fan.flipCone_of_not_le`), and `cone(u_{J₊ ∪ J₋ ∖ {j}}) + λ` with `λ` the link cone of `ν` when it is (`Fan.flipCone_of_le`). -/
noncomputable def flipCone (c : F.Ray → ℝ) (ν : PointedCone ℝ (NR n)) (j : F.Ray) :
    PointedCone ℝ (NR n) :=
  indexCone (fun ρ : F.Ray => toNR (F.generator ρ)) (F.flipRays c ν j)

variable (F) in
/-- **The flipped fan** of the extremal ray of the class `c`: the faces of the cones `Fan.flipCone c ν j` for the maximal cones `ν` of `F` and the rays `j` of `J₋`. It replaces the star of `cone(u_{J₋})` by the cones `cone(u_{J₊ ∪ J₋ ∖ {j}}) + λ` with `j ∈ J₋` and `λ` in the link, and it keeps the other cones. -/
def flipped (c : F.Ray → ℝ) : Set (PointedCone ℝ (NR n)) :=
  {τ | ∃ ν j, F.IsMaximalCone ν ∧ c j < 0 ∧ τ.IsFaceOf (F.flipCone c ν j)}

/-- Outside the star of `cone(u_{J₋})`, the cone of the flipped fan is the cone of the fan. -/
theorem flipCone_of_not_le {c : F.Ray → ℝ} {ν : PointedCone ℝ (NR n)} (hν : ν ∈ F.cones)
    (h : ¬ F.negCone c ≤ ν) (j : F.Ray) : F.flipCone c ν j = ν :=
  (eq_hull_of_forall_le_iff hν (P := fun ρ => ρ ∈ F.flipRays c ν j) fun _ =>
    ⟨fun hρ => ⟨Or.inl hρ, fun h' => absurd h' h⟩,
      fun hρ => hρ.1.resolve_right fun h' => h h'.1⟩).symm

/-- On the star of `cone(u_{J₋})`, the cone of the flipped fan is `cone(u_{J₊ ∪ J₋ ∖ {j}}) + λ`, with `λ` the link cone. -/
theorem flipCone_of_le {c : F.Ray → ℝ} {ν : PointedCone ℝ (NR n)} (h : F.negCone c ≤ ν)
    {j : F.Ray} (hj : c j ≠ 0) :
    F.flipCone c ν j = F.circuitCone c j ⊔ F.linkCone c ν := by
  refine Eq.trans ?_ (hull_or (fun ρ : F.Ray => c ρ ≠ 0 ∧ ρ ≠ j) fun ρ : F.Ray => ρ.1 ≤ ν ∧ c ρ = 0)
  unfold flipCone indexCone
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  refine exists_congr fun ρ => and_congr ⟨fun hρ => ?_, fun hρ => ?_⟩ Iff.rfl
  · by_cases h0 : c ρ = 0
    · exact Or.inr ⟨hρ.1.resolve_right fun h' => h'.2 h0, h0⟩
    · exact Or.inl ⟨h0, hρ.2 h⟩
  · rcases hρ with ⟨h0, hρj⟩ | ⟨hρ, h0⟩
    · exact ⟨Or.inr ⟨h, h0⟩, fun _ => hρj⟩
    · exact ⟨Or.inl hρ, fun _ hρj => hj (by rw [← hρj]; exact h0)⟩

/-- The cone of the flipped fan is in the cone of the contraction. -/
theorem flipCone_le_contractCone (c : F.Ray → ℝ) (ν : PointedCone ℝ (NR n)) (j : F.Ray) :
    F.flipCone c ν j ≤ F.contractCone c ν :=
  indexCone_mono (fun ρ : F.Ray => toNR (F.generator ρ)) (S := F.flipRays c ν j)
    (T := {ρ | ρ.1 ≤ ν ∨ (F.negCone c ≤ ν ∧ c ρ ≠ 0)}) fun _ hρ => hρ.1

/-- The cones of the flipped fan are rational polyhedral. -/
theorem isRationalPolyhedral_flipCone (c : F.Ray → ℝ) (ν : PointedCone ℝ (NR n)) (j : F.Ray) :
    IsRationalPolyhedral (F.flipCone c ν j) :=
  isRationalPolyhedral_hull_generator fun ρ => ρ ∈ F.flipRays c ν j

/-- A cone of the flipped fan has finitely many faces. -/
theorem finite_setOf_isFaceOf_flipCone (c : F.Ray → ℝ) (ν : PointedCone ℝ (NR n)) (j : F.Ray) :
    {τ : PointedCone ℝ (NR n) | τ.IsFaceOf (F.flipCone c ν j)}.Finite := by
  unfold flipCone indexCone
  exact finite_setOf_isFaceOf_hull ((Set.toFinite _).image _)

/-- The cones `cone(u_{J₊ ∪ J₋ ∖ {j}}) + λ`, with `j ∈ J₋` and `λ` in the link, are cones of the flipped fan. -/
theorem circuitCone_sup_mem_flipped {c : F.Ray → ℝ} {L : PointedCone ℝ (NR n)}
    (hL : L ∈ F.link c) {j : F.Ray} (hj : c j < 0) : F.circuitCone c j ⊔ L ∈ F.flipped c := by
  obtain ⟨τ, hτ, hneg, rfl⟩ := hL
  refine ⟨τ, j, hτ, hj, ?_⟩
  rw [flipCone_of_le hneg hj.ne]

/-- The flipped fan keeps the cones of the fan in a maximal cone outside the star of `cone(u_{J₋})`, when `J₋` is not empty. -/
theorem mem_flipped_of_not_le {c : F.Ray → ℝ} {σ ν : PointedCone ℝ (NR n)}
    (hσ : σ ∈ F.cones) (hν : F.IsMaximalCone ν) (hσν : σ ≤ ν) (hneg : ¬ F.negCone c ≤ ν)
    {j : F.Ray} (hj : c j < 0) : σ ∈ F.flipped c := by
  refine ⟨ν, j, hν, hj, ?_⟩
  rw [flipCone_of_not_le hν.mem hneg]
  have h := F.inter_face ν hν.mem σ hσ
  rwa [inf_eq_right.mpr hσν] at h

/-- **The cones of the flipped fan cover the cones of the contraction.** A nonnegative combination `x = Σ b_ρ u_ρ` of the generators of the rays of `K_ν` is in `Fan.flipCone c ν j` for the ray `j ∈ J₋` that minimizes `b_ρ / (-c_ρ)`: the coefficients `b + t c`, with `t = b_j / (-c_j)`, are nonnegative and vanish at `j`. -/
theorem exists_mem_flipCone (hs : F.IsSimplicialFan) {σ₀ σ₀' : PointedCone ℝ (NR n)}
    (hw₀ : F.IsWallPair σ₀ σ₀') (W₀ : F.WallData σ₀ σ₀') {ν : PointedCone ℝ (NR n)}
    {k : F.Ray} (hk : W₀.curveClass k < 0) {x : NR n}
    (hx : x ∈ F.contractCone W₀.curveClass ν) :
    ∃ j, W₀.curveClass j < 0 ∧ x ∈ F.flipCone W₀.curveClass ν j := by
  classical
  obtain ⟨b, hb0, hbP, rfl⟩ := (mem_hull_generator_iff (fun ρ : F.Ray => ρ.1 ≤ ν ∨
    (F.negCone W₀.curveClass ≤ ν ∧ W₀.curveClass ρ ≠ 0))).mp hx
  by_cases hneg : F.negCone W₀.curveClass ≤ ν
  · obtain ⟨j, hjS, hjmin⟩ := (Finset.univ.filter fun ρ => W₀.curveClass ρ < 0).exists_min_image
      (fun ρ => b ρ / -W₀.curveClass ρ) ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩⟩
    have hj : W₀.curveClass j < 0 := (Finset.mem_filter.mp hjS).2
    obtain ⟨t, htdef⟩ : ∃ t, t = b j / -W₀.curveClass j := ⟨_, rfl⟩
    have ht0 : 0 ≤ t := by
      rw [htdef]
      exact div_nonneg (hb0 j) (neg_nonneg.mpr hj.le)
    have htj : t * W₀.curveClass j = -b j := by
      rw [htdef, div_mul_eq_mul_div, div_eq_iff (neg_ne_zero.mpr hj.ne)]
      ring
    have hmin : ∀ ρ, W₀.curveClass ρ < 0 → t * -W₀.curveClass ρ ≤ b ρ := fun ρ hρ => by
      have h1 : b j / -W₀.curveClass j ≤ b ρ / -W₀.curveClass ρ :=
        hjmin ρ (Finset.mem_filter.mpr ⟨Finset.mem_univ ρ, hρ⟩)
      rw [← htdef, le_div_iff₀ (neg_pos.mpr hρ)] at h1
      exact h1
    refine ⟨j, hj, mem_indexCone.mpr
      ⟨fun ρ => b ρ + t * W₀.curveClass ρ, fun ρ => ?_, fun ρ hρ => ?_, ?_⟩⟩
    · show 0 ≤ b ρ + t * W₀.curveClass ρ
      by_cases hρ : W₀.curveClass ρ < 0
      · have h1 := hmin ρ hρ
        have h2 : t * -W₀.curveClass ρ = -(t * W₀.curveClass ρ) := by ring
        linarith
      · have h1 := mul_nonneg ht0 (not_lt.mp hρ)
        linarith [hb0 ρ]
    · show b ρ + t * W₀.curveClass ρ = 0
      by_contra h0
      apply hρ
      refine ⟨?_, fun _ hρj => ?_⟩
      · by_cases hcρ : W₀.curveClass ρ = 0
        · have hbρ : b ρ ≠ 0 := fun hb => h0 (by rw [hb, hcρ, mul_zero, add_zero])
          exact not_not.mp fun hn => hbρ (hbP ρ hn)
        · exact Or.inr ⟨hneg, hcρ⟩
      · rw [hρj, htj, add_neg_cancel] at h0
        exact h0 rfl
    · have hrel := W₀.sum_curveClass_smul_generator hw₀.1.mem (hs σ₀ hw₀.1.mem)
      have hterm : ∀ ρ, (b ρ + t * W₀.curveClass ρ) • toNR (F.generator ρ) =
          b ρ • toNR (F.generator ρ) + t • (W₀.curveClass ρ • toNR (F.generator ρ)) :=
        fun ρ => by rw [add_smul, mul_smul]
      show ∑ ρ, (b ρ + t * W₀.curveClass ρ) • toNR (F.generator ρ) = _
      simp only [hterm]
      rw [Finset.sum_add_distrib, ← Finset.smul_sum, hrel, smul_zero, add_zero]
  · refine ⟨k, hk, mem_indexCone.mpr ⟨b, hb0, fun ρ hρ => ?_, rfl⟩⟩
    by_contra h0
    exact hρ ⟨not_not.mp fun hn => h0 (hbP ρ hn), fun h => absurd h hneg⟩

/-! ### The cones of the flipped fan are simplicial -/

variable {R : PointedCone ℝ (F.Ray → ℝ)}

/-- The generator of a ray is in the cone `K_ν` of the contraction exactly when the ray is one of the rays that span `K_ν`. -/
theorem IsExtremalRay.generator_mem_contractCone_iff (hc : F.IsComplete)
    (hs : F.IsSimplicialFan) (hR : F.IsExtremalRay R) {σ₀ σ₀' : PointedCone ℝ (NR n)}
    (hw₀ : F.IsWallPair σ₀ σ₀') (W₀ : F.WallData σ₀ σ₀') (hW₀ : W₀.curveClass ∈ R)
    {ν : PointedCone ℝ (NR n)} (hν : F.IsMaximalCone ν) {ρ : F.Ray} :
    toNR (F.generator ρ) ∈ F.contractCone W₀.curveClass ν ↔
      ρ.1 ≤ ν ∨ (F.negCone W₀.curveClass ≤ ν ∧ W₀.curveClass ρ ≠ 0) := by
  refine ⟨fun hρ => ?_, fun hρ => Submodule.subset_span ⟨ρ, hρ, rfl⟩⟩
  obtain ⟨D, φ, h⟩ := hR.exists_isRaySupport hc hs
  obtain ⟨m, hm⟩ := h.isSupportFunctionOf.1 ν hν.mem
  by_cases hρν : ρ.1 ≤ ν
  · exact Or.inl hρν
  · exact Or.inr (h.negCone_le_of_eq hc hs hR hw₀ W₀ hW₀ hν hm
      ((h.mem_contractCone_iff hc hs hR hw₀ W₀ hW₀ hν hm).mp hρ) hρν)

/-- **A combination in two cones of the contraction.** A nonnegative combination of generators in the cone `K_ν` of the contraction that lies in another cone `K_ν'` only uses generators in `K_ν'`, since `K_ν ∩ K_ν'` is a face of `K_ν`. -/
theorem IsExtremalRay.generator_mem_of_sum_mem (hc : F.IsComplete) (hs : F.IsSimplicialFan)
    (hR : F.IsExtremalRay R) {σ₀ σ₀' : PointedCone ℝ (NR n)} (hw₀ : F.IsWallPair σ₀ σ₀')
    (W₀ : F.WallData σ₀ σ₀') (hW₀ : W₀.curveClass ∈ R) {ν ν' : PointedCone ℝ (NR n)}
    (hν : F.IsMaximalCone ν) (hν' : F.IsMaximalCone ν') {b : F.Ray → ℝ} (hb0 : ∀ ρ, 0 ≤ b ρ)
    (hbν : ∀ ρ, b ρ ≠ 0 → toNR (F.generator ρ) ∈ F.contractCone W₀.curveClass ν)
    (hx : ∑ ρ, b ρ • toNR (F.generator ρ) ∈ F.contractCone W₀.curveClass ν') {ρ : F.Ray}
    (hρ : b ρ ≠ 0) : toNR (F.generator ρ) ∈ F.contractCone W₀.curveClass ν' := by
  obtain ⟨D, φ, h⟩ := hR.exists_isRaySupport hc hs
  have hface := h.inf_isFaceOf hc hs hR hw₀ W₀ hW₀ hν hν'
  have hterm : ∀ ρ, b ρ • toNR (F.generator ρ) ∈ F.contractCone W₀.curveClass ν := by
    intro ρ
    by_cases h0 : b ρ = 0
    · rw [h0, zero_smul]
      exact Submodule.zero_mem _
    · exact PointedCone.smul_mem _ (hb0 ρ) (hbν ρ h0)
  have hsum : ∑ ρ, b ρ • toNR (F.generator ρ) ∈
      F.contractCone W₀.curveClass ν ⊓ F.contractCone W₀.curveClass ν' :=
    Submodule.mem_inf.mpr ⟨Submodule.sum_mem _ fun ρ _ => hterm ρ, hx⟩
  have h1 := hface.mem_of_sum_mem (f := fun ρ => b ρ • toNR (F.generator ρ)) hterm hsum ρ
  have h2 := PointedCone.smul_mem _ (inv_nonneg.mpr (hb0 ρ)) (Submodule.mem_inf.mp h1).2
  rwa [smul_smul, inv_mul_cancel₀ hρ, one_smul] at h2

/-- **The relations on the star.** Let `ν` be a maximal cone that contains `cone(u_{J₋})`. A linear relation among the generators of the rays of `ν` and of the circuit is a multiple of `c`. -/
theorem IsExtremalRay.exists_eq_mul_of_sum_eq_zero (hc : F.IsComplete) (hs : F.IsSimplicialFan)
    (hR : F.IsExtremalRay R) {σ₀ σ₀' : PointedCone ℝ (NR n)} (hw₀ : F.IsWallPair σ₀ σ₀')
    (W₀ : F.WallData σ₀ σ₀') (hW₀ : W₀.curveClass ∈ R) {ν : PointedCone ℝ (NR n)}
    (hν : F.IsMaximalCone ν) (hneg : F.negCone W₀.curveClass ≤ ν) {d : F.Ray → ℝ}
    (hd : ∀ ρ, d ρ ≠ 0 → ρ.1 ≤ ν ∨ W₀.curveClass ρ ≠ 0)
    (hsum : ∑ ρ, d ρ • toNR (F.generator ρ) = 0) :
    ∃ s : ℝ, ∀ ρ, d ρ = s * W₀.curveClass ρ := by
  obtain ⟨j, hcj, -, hj⟩ := hR.exists_ray_not_le hc hs hw₀ W₀ hW₀ hν hneg
  refine ⟨d j / W₀.curveClass j,
    eq_smul_of_sum_eq_zero hs hw₀ W₀ hν.mem hcj.ne' hj (d := d) (fun ρ h0 hρj => ?_) hsum⟩
  rcases hd ρ h0 with hρ | hρ
  · exact hρ
  · exact hj ρ hρ hρj

/-- **The generators of the rays of a cone of the flipped fan are linearly independent.** On the star, a relation is a multiple of `c` and vanishes at `j ∈ J₋`; off the star, the rays are those of the simplicial cone `ν`. -/
theorem IsExtremalRay.eq_zero_of_sum_eq_zero_flipRays (hc : F.IsComplete)
    (hs : F.IsSimplicialFan) (hR : F.IsExtremalRay R) {σ₀ σ₀' : PointedCone ℝ (NR n)}
    (hw₀ : F.IsWallPair σ₀ σ₀') (W₀ : F.WallData σ₀ σ₀') (hW₀ : W₀.curveClass ∈ R)
    {ν : PointedCone ℝ (NR n)} (hν : F.IsMaximalCone ν) {j : F.Ray}
    (hj : W₀.curveClass j < 0) {d : F.Ray → ℝ}
    (hd : ∀ ρ, ρ ∉ F.flipRays W₀.curveClass ν j → d ρ = 0)
    (hsum : ∑ ρ, d ρ • toNR (F.generator ρ) = 0) (ρ : F.Ray) : d ρ = 0 := by
  have hd' : ∀ ρ, d ρ ≠ 0 → ρ ∈ F.flipRays W₀.curveClass ν j :=
    fun ρ h0 => not_not.mp fun hn => h0 (hd ρ hn)
  by_cases hneg : F.negCone W₀.curveClass ≤ ν
  · obtain ⟨s, hsd⟩ := hR.exists_eq_mul_of_sum_eq_zero hc hs hw₀ W₀ hW₀ hν hneg
      (fun ρ h0 => (hd' ρ h0).1.imp_right And.right) hsum
    have hdj : d j = 0 := hd j fun h => h.2 hneg rfl
    have hs0 : s = 0 := by
      have h1 := hsd j
      rw [hdj] at h1
      rcases mul_eq_zero.mp h1.symm with h2 | h2
      · exact h2
      · exact absurd h2 hj.ne
    rw [hsd ρ, hs0, zero_mul]
  · have hdν : ∀ ρ, d ρ ≠ 0 → ρ.1 ≤ ν :=
      fun ρ h0 => (hd' ρ h0).1.resolve_right fun h => hneg h.1
    have hsub : ∑ ρ : {ρ : F.Ray // ρ.1 ≤ ν}, d ρ.1 • toNR (F.generator ρ.1) = 0 :=
      (sum_subtype_eq_sum Finset.univ (fun ρ => d ρ • toNR (F.generator ρ))
        (fun ρ _ => Finset.mem_univ ρ)
        (fun ρ _ h0 => hdν ρ fun h0' => h0 (by simp [h0']))).trans hsum
    have hzero := Fintype.linearIndependent_iff.mp
      (linearIndependent_generator hν.mem (hs ν hν.mem)) (fun ρ => d ρ.1) hsub
    by_cases h0 : d ρ = 0
    · exact h0
    · exact hzero ⟨ρ, hdν ρ h0⟩

/-- The cones of the subsets of the rays of a cone of the flipped fan are faces of it. -/
theorem IsExtremalRay.isFaceOf_flipCone (hc : F.IsComplete) (hs : F.IsSimplicialFan)
    (hR : F.IsExtremalRay R) {σ₀ σ₀' : PointedCone ℝ (NR n)} (hw₀ : F.IsWallPair σ₀ σ₀')
    (W₀ : F.WallData σ₀ σ₀') (hW₀ : W₀.curveClass ∈ R) {ν : PointedCone ℝ (NR n)}
    (hν : F.IsMaximalCone ν) {j : F.Ray} (hj : W₀.curveClass j < 0) {T : Set F.Ray}
    (hT : T ⊆ F.flipRays W₀.curveClass ν j) :
    (indexCone (fun ρ : F.Ray => toNR (F.generator ρ)) T).IsFaceOf
      (F.flipCone W₀.curveClass ν j) :=
  indexCone_isFaceOf_of_forall (fun _ hd hsum =>
    hR.eq_zero_of_sum_eq_zero_flipRays hc hs hw₀ W₀ hW₀ hν hj hd hsum) hT

/-- **The cones of the flipped fan are simplicial.** -/
theorem IsExtremalRay.isSimplicial_flipCone (hc : F.IsComplete) (hs : F.IsSimplicialFan)
    (hR : F.IsExtremalRay R) {σ₀ σ₀' : PointedCone ℝ (NR n)} (hw₀ : F.IsWallPair σ₀ σ₀')
    (W₀ : F.WallData σ₀ σ₀') (hW₀ : W₀.curveClass ∈ R) {ν : PointedCone ℝ (NR n)}
    (hν : F.IsMaximalCone ν) {j : F.Ray} (hj : W₀.curveClass j < 0) :
    IsSimplicial (F.flipCone W₀.curveClass ν j) := by
  classical
  refine ⟨(Set.toFinite (F.flipRays W₀.curveClass ν j)).toFinset.image F.generator, ?_, ?_⟩
  · rw [latticeCone_eq_hull, Finset.coe_image, Set.Finite.coe_toFinset, Set.image_image]
    rfl
  · have hli : LinearIndepOn ℝ (toNR ∘ F.generator) (F.flipRays W₀.curveClass ν j) := by
      refine linearIndepOn_iff''.mpr fun t d ht htd hsum ρ _ => ?_
      have h1 : ∑ ρ ∈ t, d ρ • toNR (F.generator ρ) = ∑ ρ, d ρ • toNR (F.generator ρ) :=
        Finset.sum_subset (Finset.subset_univ t) fun ρ _ hρ => by simp [htd ρ hρ]
      exact hR.eq_zero_of_sum_eq_zero_flipRays hc hs hw₀ W₀ hW₀ hν hj
        (fun ρ hρ => htd ρ fun hρt => hρ (ht hρt)) (h1.symm.trans hsum) ρ
    show LinearIndepOn ℝ toNR
      (((Set.toFinite (F.flipRays W₀.curveClass ν j)).toFinset.image F.generator :
        Finset (Fin n → ℤ)) : Set (Fin n → ℤ))
    rw [Finset.coe_image, Set.Finite.coe_toFinset]
    exact hli.image_of_comp F.generator toNR

/-! ### The flipped fan is a fan -/

/-- **Two cones of the flipped fan meet in the cone of their common rays.** The proof is in the module docstring. -/
theorem IsExtremalRay.flipCone_inf (hc : F.IsComplete) (hs : F.IsSimplicialFan)
    (hR : F.IsExtremalRay R) {σ₀ σ₀' : PointedCone ℝ (NR n)} (hw₀ : F.IsWallPair σ₀ σ₀')
    (W₀ : F.WallData σ₀ σ₀') (hW₀ : W₀.curveClass ∈ R) {ν₁ ν₂ : PointedCone ℝ (NR n)}
    (hν₁ : F.IsMaximalCone ν₁) (hν₂ : F.IsMaximalCone ν₂) {j₁ j₂ : F.Ray}
    (hj₁ : W₀.curveClass j₁ < 0) (hj₂ : W₀.curveClass j₂ < 0) :
    F.flipCone W₀.curveClass ν₁ j₁ ⊓ F.flipCone W₀.curveClass ν₂ j₂ =
      indexCone (fun ρ : F.Ray => toNR (F.generator ρ))
        (F.flipRays W₀.curveClass ν₁ j₁ ∩ F.flipRays W₀.curveClass ν₂ j₂) := by
  refine le_antisymm (fun x hx => ?_) (le_inf
    (indexCone_mono _ Set.inter_subset_left) (indexCone_mono _ Set.inter_subset_right))
  obtain ⟨b, hb0, hb1, rfl⟩ := mem_indexCone.mp (Submodule.mem_inf.mp hx).1
  obtain ⟨b', hb'0, hb2, hb'⟩ := mem_indexCone.mp (Submodule.mem_inf.mp hx).2
  have hb1' : ∀ ρ, b ρ ≠ 0 → ρ ∈ F.flipRays W₀.curveClass ν₁ j₁ :=
    fun ρ h0 => not_not.mp fun hn => h0 (hb1 ρ hn)
  have hb2' : ∀ ρ, b' ρ ≠ 0 → ρ ∈ F.flipRays W₀.curveClass ν₂ j₂ :=
    fun ρ h0 => not_not.mp fun hn => h0 (hb2 ρ hn)
  -- `b` uses only rays of `K_ν₂`, and `b'` only rays of `K_ν₁`
  have hP2 : ∀ ρ, b ρ ≠ 0 →
      ρ.1 ≤ ν₂ ∨ (F.negCone W₀.curveClass ≤ ν₂ ∧ W₀.curveClass ρ ≠ 0) := fun ρ h0 =>
    (hR.generator_mem_contractCone_iff hc hs hw₀ W₀ hW₀ hν₂).mp
      (hR.generator_mem_of_sum_mem hc hs hw₀ W₀ hW₀ hν₁ hν₂ hb0
        (fun ρ h0 => (hR.generator_mem_contractCone_iff hc hs hw₀ W₀ hW₀ hν₁).mpr (hb1' ρ h0).1)
        (flipCone_le_contractCone W₀.curveClass ν₂ j₂ (Submodule.mem_inf.mp hx).2) h0)
  have hx₁ : ∑ ρ, b' ρ • toNR (F.generator ρ) ∈ F.contractCone W₀.curveClass ν₁ := by
    rw [hb']
    exact flipCone_le_contractCone W₀.curveClass ν₁ j₁ (Submodule.mem_inf.mp hx).1
  have hP1 : ∀ ρ, b' ρ ≠ 0 →
      ρ.1 ≤ ν₁ ∨ (F.negCone W₀.curveClass ≤ ν₁ ∧ W₀.curveClass ρ ≠ 0) := fun ρ h0 =>
    (hR.generator_mem_contractCone_iff hc hs hw₀ W₀ hW₀ hν₁).mp
      (hR.generator_mem_of_sum_mem hc hs hw₀ W₀ hW₀ hν₂ hν₁ hb'0
        (fun ρ h0 => (hR.generator_mem_contractCone_iff hc hs hw₀ W₀ hW₀ hν₂).mpr (hb2' ρ h0).1)
        hx₁ h0)
  by_cases hneg₂ : F.negCone W₀.curveClass ≤ ν₂
  · by_cases hneg₁ : F.negCone W₀.curveClass ≤ ν₁
    · -- both cones are in the star: `b - b' = s c` with `s = 0`
      obtain ⟨s, hsd⟩ := hR.exists_eq_mul_of_sum_eq_zero hc hs hw₀ W₀ hW₀ hν₁ hneg₁
        (d := fun ρ => b ρ - b' ρ) (fun ρ h0 => by
          by_cases hb : b ρ = 0
          · exact (hP1 ρ fun hb'' => h0 (by simp [hb, hb''])).imp_right And.right
          · exact (hb1' ρ hb).1.imp_right And.right)
        (by simp only [sub_smul, Finset.sum_sub_distrib, hb', sub_self])
      have h1 : b j₁ - b' j₁ = s * W₀.curveClass j₁ := hsd j₁
      have h2 : b j₂ - b' j₂ = s * W₀.curveClass j₂ := hsd j₂
      have hbj₁ : b j₁ = 0 := hb1 j₁ fun h => h.2 hneg₁ rfl
      have hbj₂ : b' j₂ = 0 := hb2 j₂ fun h => h.2 hneg₂ rfl
      have hs0 : s = 0 := by
        rcases lt_trichotomy s 0 with hlt | heq | hgt
        · have h3 := mul_pos_of_neg_of_neg hlt hj₁
          linarith [hb'0 j₁]
        · exact heq
        · have h3 := mul_neg_of_pos_of_neg hgt hj₂
          linarith [hb0 j₂]
      refine mem_indexCone.mpr ⟨b, hb0, fun ρ hρ => ?_, rfl⟩
      by_contra h0
      have hbb : b' ρ = b ρ := by
        have h3 : b ρ - b' ρ = s * W₀.curveClass ρ := hsd ρ
        rw [hs0, zero_mul] at h3
        linarith
      exact hρ ⟨hb1' ρ h0, hb2' ρ (by rw [hbb]; exact h0)⟩
    · -- `ν₁` is not in the star: use `b'`
      refine mem_indexCone.mpr ⟨b', hb'0, fun ρ hρ => ?_, hb'⟩
      by_contra h0
      exact hρ ⟨⟨hP1 ρ h0, fun h => absurd h hneg₁⟩, hb2' ρ h0⟩
  · -- `ν₂` is not in the star: use `b`
    refine mem_indexCone.mpr ⟨b, hb0, fun ρ hρ => ?_, rfl⟩
    by_contra h0
    exact hρ ⟨hb1' ρ h0, ⟨hP2 ρ h0, fun h => absurd h hneg₂⟩⟩

/-- **The flipped fan** of an extremal ray `R`, with `c` the class of a wall curve in `R`: the faces of the cones `cone(u_{J₊ ∪ J₋ ∖ {j}}) + λ` for `j ∈ J₋` and `λ` in the link, and of the cones of `F` outside the star of `cone(u_{J₋})`. -/
noncomputable def IsExtremalRay.flippedFan (hc : F.IsComplete) (hs : F.IsSimplicialFan)
    (hR : F.IsExtremalRay R) {σ₀ σ₀' : PointedCone ℝ (NR n)} (hw₀ : F.IsWallPair σ₀ σ₀')
    (W₀ : F.WallData σ₀ σ₀') (hW₀ : W₀.curveClass ∈ R) : Fan n where
  cones := F.flipped W₀.curveClass
  finite := by
    have hmax : {ν | F.IsMaximalCone ν}.Finite :=
      F.finite.subset fun ν hν => IsMaximalCone.mem hν
    refine (hmax.biUnion fun ν _ => Set.finite_iUnion fun j =>
      finite_setOf_isFaceOf_flipCone W₀.curveClass ν j).subset ?_
    rintro τ ⟨ν, j, hν, -, hτ⟩
    exact Set.mem_biUnion hν (Set.mem_iUnion.mpr ⟨j, hτ⟩)
  rational σ hσ := by
    obtain ⟨ν, j, -, -, hσ⟩ := hσ
    exact (isRationalPolyhedral_flipCone _ ν j).of_isFaceOf hσ
  stronglyConvex σ hσ := by
    obtain ⟨ν, j, hν, hj, hσ⟩ := hσ
    exact (hR.isStronglyConvex_contractCone hc hs hw₀ W₀ hW₀ hν hj).mono
      (hσ.le.trans (flipCone_le_contractCone _ ν j))
  face_mem σ hσ τ hτ := by
    obtain ⟨ν, j, hν, hj, hσ⟩ := hσ
    exact ⟨ν, j, hν, hj, hτ.trans hσ⟩
  inter_face σ hσ τ hτ := by
    obtain ⟨ν, j, hν, hj, hσ⟩ := hσ
    obtain ⟨ν', j', hν', hj', hτ⟩ := hτ
    refine isFaceOf_inf_of_isFaceOf hσ hτ ?_ ?_
    · rw [hR.flipCone_inf hc hs hw₀ W₀ hW₀ hν hν' hj hj']
      exact hR.isFaceOf_flipCone hc hs hw₀ W₀ hW₀ hν hj Set.inter_subset_left
    · rw [hR.flipCone_inf hc hs hw₀ W₀ hW₀ hν hν' hj hj']
      exact hR.isFaceOf_flipCone hc hs hw₀ W₀ hW₀ hν' hj' Set.inter_subset_right

/-- The cones of the flipped fan. -/
theorem IsExtremalRay.cones_flippedFan (hc : F.IsComplete) (hs : F.IsSimplicialFan)
    (hR : F.IsExtremalRay R) {σ₀ σ₀' : PointedCone ℝ (NR n)} (hw₀ : F.IsWallPair σ₀ σ₀')
    (W₀ : F.WallData σ₀ σ₀') (hW₀ : W₀.curveClass ∈ R) :
    (hR.flippedFan hc hs hw₀ W₀ hW₀).cones = F.flipped W₀.curveClass :=
  rfl

/-- **The flipped fan is simplicial.** -/
theorem IsExtremalRay.isSimplicialFan_flippedFan (hc : F.IsComplete) (hs : F.IsSimplicialFan)
    (hR : F.IsExtremalRay R) {σ₀ σ₀' : PointedCone ℝ (NR n)} (hw₀ : F.IsWallPair σ₀ σ₀')
    (W₀ : F.WallData σ₀ σ₀') (hW₀ : W₀.curveClass ∈ R) :
    (hR.flippedFan hc hs hw₀ W₀ hW₀).IsSimplicialFan := by
  rintro σ ⟨ν, j, hν, hj, hσ⟩
  exact (hR.isSimplicial_flipCone hc hs hw₀ W₀ hW₀ hν hj).of_isFaceOf hσ

/-! ### Support, refinement and rays -/

/-- **The flipped fan has the same support** as `F` when `J₋` is not empty. -/
theorem IsExtremalRay.support_flippedFan (hc : F.IsComplete) (hs : F.IsSimplicialFan)
    (hR : F.IsExtremalRay R) {σ₀ σ₀' : PointedCone ℝ (NR n)} (hw₀ : F.IsWallPair σ₀ σ₀')
    (W₀ : F.WallData σ₀ σ₀') (hW₀ : W₀.curveClass ∈ R) (hJ : ∃ k, W₀.curveClass k < 0) :
    (hR.flippedFan hc hs hw₀ W₀ hW₀).support = F.support := by
  obtain ⟨k, hk⟩ := hJ
  ext x
  refine ⟨fun _ => by rw [show F.support = Set.univ from hc]; exact Set.mem_univ x, fun _ => ?_⟩
  obtain ⟨σ, hσ, hxσ⟩ := exists_mem_of_isComplete hc x
  obtain ⟨ν, hσν, hν⟩ := F.exists_le_isMaximalCone hσ
  obtain ⟨j, hj, hxj⟩ := exists_mem_flipCone hs hw₀ W₀ hk
    (le_contractCone hν.mem W₀.curveClass (hσν hxσ))
  exact (hR.flippedFan hc hs hw₀ W₀ hW₀).mem_support.mpr
    ⟨_, ⟨ν, j, hν, hj, PointedCone.IsFaceOf.refl _⟩, hxj⟩

/-- The flipped fan is complete when `J₋` is not empty. -/
theorem IsExtremalRay.isComplete_flippedFan (hc : F.IsComplete) (hs : F.IsSimplicialFan)
    (hR : F.IsExtremalRay R) {σ₀ σ₀' : PointedCone ℝ (NR n)} (hw₀ : F.IsWallPair σ₀ σ₀')
    (W₀ : F.WallData σ₀ σ₀') (hW₀ : W₀.curveClass ∈ R) (hJ : ∃ k, W₀.curveClass k < 0) :
    (hR.flippedFan hc hs hw₀ W₀ hW₀).IsComplete := by
  unfold IsComplete
  rw [hR.support_flippedFan hc hs hw₀ W₀ hW₀ hJ]
  exact hc

/-- **The flipped fan refines the contraction.** Each cone of `F⁺` is in a cone of the contraction fan `G`, and each cone of `G` is the union of the cones of `F⁺` that it contains. -/
theorem IsExtremalRay.refines_flippedFan (hc : F.IsComplete) (hs : F.IsSimplicialFan)
    (hR : F.IsExtremalRay R) {σ₀ σ₀' : PointedCone ℝ (NR n)} (hw₀ : F.IsWallPair σ₀ σ₀')
    (W₀ : F.WallData σ₀ σ₀') (hW₀ : W₀.curveClass ∈ R) (hJ : ∃ k, W₀.curveClass k < 0) :
    (hR.flippedFan hc hs hw₀ W₀ hW₀).Refines (hR.contractionFan hc hs hw₀ W₀ hW₀ hJ).cones := by
  obtain ⟨k, hk⟩ := hJ
  refine ⟨?_, ?_⟩
  · rintro σ ⟨ν, j, hν, -, hσ⟩
    exact ⟨F.contractCone W₀.curveClass ν, ⟨ν, hν, PointedCone.IsFaceOf.refl _⟩,
      hσ.le.trans (flipCone_le_contractCone _ ν j)⟩
  · rintro τ ⟨ν, hν, hτ⟩
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨j, hj, hxj⟩ := exists_mem_flipCone hs hw₀ W₀ hk (hτ.le hx)
      obtain ⟨b, hb0, hbS, rfl⟩ := mem_indexCone.mp hxj
      have hbS' : ∀ ρ, b ρ ≠ 0 → ρ ∈ F.flipRays W₀.curveClass ν j :=
        fun ρ h0 => not_not.mp fun hn => h0 (hbS ρ hn)
      have hterm : ∀ ρ, b ρ • toNR (F.generator ρ) ∈ F.contractCone W₀.curveClass ν := by
        intro ρ
        by_cases h0 : b ρ = 0
        · rw [h0, zero_smul]
          exact Submodule.zero_mem _
        · exact PointedCone.smul_mem _ (hb0 ρ) (flipCone_le_contractCone W₀.curveClass ν j
            (mem_indexCone_of_mem (fun ρ : F.Ray => toNR (F.generator ρ)) (hbS' ρ h0)))
      have hτgen : ∀ ρ, b ρ ≠ 0 → toNR (F.generator ρ) ∈ τ := by
        intro ρ h0
        have h1 : b ρ • toNR (F.generator ρ) ∈ τ :=
          hτ.mem_of_sum_mem (f := fun ρ => b ρ • toNR (F.generator ρ)) hterm hx ρ
        have h2 := PointedCone.smul_mem τ (inv_nonneg.mpr (hb0 ρ)) h1
        rwa [smul_smul, inv_mul_cancel₀ h0, one_smul] at h2
      refine Set.mem_biUnion
        (x := indexCone (fun ρ : F.Ray => toNR (F.generator ρ)) {ρ | b ρ ≠ 0})
        ⟨⟨ν, j, hν, hj, hR.isFaceOf_flipCone hc hs hw₀ W₀ hW₀ hν hj fun ρ h0 => hbS' ρ h0⟩,
          Submodule.span_le.mpr ?_⟩ ?_
      · rintro _ ⟨ρ, h0, rfl⟩
        exact hτgen ρ h0
      · exact mem_indexCone.mpr ⟨b, hb0, fun ρ h0 => not_not.mp h0, rfl⟩
    · intro x hx
      obtain ⟨σ, ⟨-, hστ⟩, hxσ⟩ := Set.mem_iUnion₂.mp hx
      exact hστ hxσ

/-- **The flipped fan has the same rays** as `F` when `J₋` has two rays. -/
theorem IsExtremalRay.rays_flippedFan (hc : F.IsComplete) (hs : F.IsSimplicialFan)
    (hR : F.IsExtremalRay R) {σ₀ σ₀' : PointedCone ℝ (NR n)} (hw₀ : F.IsWallPair σ₀ σ₀')
    (W₀ : F.WallData σ₀ σ₀') (hW₀ : W₀.curveClass ∈ R) {k k' : F.Ray}
    (hk : W₀.curveClass k < 0) (hk' : W₀.curveClass k' < 0) (hkk' : k ≠ k') :
    (hR.flippedFan hc hs hw₀ W₀ hW₀).rays = F.rays := by
  ext τ
  constructor
  · rintro ⟨⟨ν, j, hν, hj, hτ⟩, hray⟩
    -- a generator of a ray of the cone lies in the face `τ`
    have heq := eq_hull_inter_of_isFaceOf
      (s := (fun ρ : F.Ray => toNR (F.generator ρ)) '' F.flipRays W₀.curveClass ν j) hτ
    obtain ⟨ρ, hρ, hgτ⟩ : ∃ ρ ∈ F.flipRays W₀.curveClass ν j, toNR (F.generator ρ) ∈ τ := by
      by_contra hno
      apply hray.ne_bot
      rw [heq]
      refine le_bot_iff.mp (Submodule.span_le.mpr ?_)
      rintro _ ⟨⟨ρ, hρ, rfl⟩, hgτ⟩
      exact (hno ⟨ρ, hρ, hgτ⟩).elim
    -- the ray `ρ` is a face of the cone in `τ`, so a face of `τ`
    have hρface : ρ.1.IsFaceOf (F.flipCone W₀.curveClass ν j) := by
      rw [← indexCone_singleton_generator ρ]
      exact hR.isFaceOf_flipCone hc hs hw₀ W₀ hW₀ hν hj (Set.singleton_subset_iff.mpr hρ)
    have hρτ : ρ.1.IsFaceOf τ :=
      (PointedCone.IsFaceOf.isFaceOf_iff_le hρface hτ).mpr (le_of_generator_mem hgτ)
    refine ⟨?_, hray⟩
    obtain ⟨v, -, hv⟩ := hray
    rw [hv] at hρτ
    rcases eq_bot_or_eq_of_isFaceOf_latticeCone_singleton hρτ with h0 | h0
    · exact absurd h0 (F.isRay ρ).ne_bot
    · rw [hv, ← h0]
      exact ρ.2.1
  · rintro ⟨hτ, hray⟩
    obtain ⟨ν, hτν, hν⟩ := F.exists_le_isMaximalCone hτ
    obtain ⟨j, hj, hjρ⟩ : ∃ j, W₀.curveClass j < 0 ∧ (⟨τ, hτ, hray⟩ : F.Ray) ≠ j := by
      by_cases hkρ : (⟨τ, hτ, hray⟩ : F.Ray) = k
      · exact ⟨k', hk', fun h => hkk' (hkρ.symm.trans h)⟩
      · exact ⟨k, hk, hkρ⟩
    refine ⟨⟨ν, j, hν, hj, ?_⟩, hray⟩
    have h := hR.isFaceOf_flipCone hc hs hw₀ W₀ hW₀ hν hj (T := {⟨τ, hτ, hray⟩})
      (Set.singleton_subset_iff.mpr ⟨Or.inl hτν, fun _ => hjρ⟩)
    rwa [indexCone_singleton_generator] at h

end Fan

end MinimalModel.Toric
