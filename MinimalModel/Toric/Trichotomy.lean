/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import MinimalModel.Toric.FlipExists

/-!
# Toric flips, part 12: divisorial contractions, Mori fibre spaces and the trichotomy

This file proves the trichotomy of the toric `D`-program at a model, the second conjunct of `MinimalModel.ToricMMP` (Reid 1983, Sections 2 and 3; Matsuki, Chapter 14; Cox, Little and Schenck, Section 15.4). Let `F` be a complete simplicial fan with an ample divisor and `D` a divisor. Then `D` is nef, or `(F, D)` is a toric Mori fibre space, or one more toric step starts at `(F, D)`.

## A `D`-negative extremal ray

Let `D` be a divisor that is not nef. By the cone theorem it has negative degree on a wall curve. An ample divisor `H` has positive degree on each wall curve (`Fan.WallData.degree_pos_of_isAmple`): the support function of `H` is strictly convex at the maximal cone `σ` of the wall, at the generator of the ray of `σ'` outside `σ`. The faces of the cone of curves are cut out as follows. For a linear form `g`, let `μ` be the least value of `g / H` at the classes of the wall curves. Then `g - μ H` is nonnegative at these classes, and the classes where it vanishes span a face (`indexCone_isFaceOf_of_nonneg`, `exists_isFaceOf_indexCone_min`). Take first `g = D`, so that `μ < 0`, and then the coordinates `g = c ↦ c_ρ` one by one. In the last face all the classes are positive multiples of one vector `w` (`exists_isFaceOf_indexCone_eq_hull`), so the face is the extremal ray `cone(w)`, and its wall curves have negative degree on `D` (`Fan.exists_isExtremalRay_degree_neg`).

## The three cases

Let `R` be a `D`-negative extremal ray, `c` the class of a wall curve in `R`, and `J₋` the rays with `c_ρ < 0`.
* `J₋` has two rays: the flip is a toric step (`Fan.IsExtremalRay.flipExists`).
* `J₋` is one ray `k`: the contraction is divisorial. On the star of `cone(u_k)` the relation gives `u_k = Σ_{ρ ≠ k} (c_ρ / -c_k) u_ρ`, a nonnegative combination, so the cone `Fan.flipCone c ν k` without `u_k` is the cone `Fan.contractCone c ν` of the contraction (`Fan.flipCone_eq_contractCone_of_unique`). So the flipped fan is the contraction fan `G` (`Fan.flipped_eq_contraction_of_unique`), its rays are the rays of `G`, and the flipped fan with the strict transform of `D` is a toric step with `B.F = G` (`Fan.IsExtremalRay.divisorialStep`).
* `J₋` is empty: the cone `Fan.contractCone c σ₀` of the contraction contains `u_j` and `-u_j = Σ_{ρ ≠ j} c_ρ u_ρ` for the ray `j` of `σ₀'` outside `σ₀`, so it is not strongly convex (`Fan.not_isStronglyConvex_contractCone`). The contraction is a quasi-fan with relative Picard number one over which `-D` is ample, so `(F, D)` is a toric Mori fibre space (`Fan.IsExtremalRay.isToricMoriFibreSpace`).

## Steps preserve the hypotheses

A toric step `A → B` keeps completeness (`IsToricStep.isComplete`: `A`, `G` and `B` have the same support), simpliciality (part of the step), the inclusion of the rays (`IsToricStep.rays_subset`) and the rationality of the coefficients (`IsToricStep.rational`). The abstract step does not keep projectivity in an evident way: an ample divisor of `B` would come from an ample divisor of the base `G`, and the definition of the step does not ask `G` to be projective. So the trichotomy at the last model of a sequence of steps is proved when that model has an ample divisor (`toricMMP_trichotomy`).

## Main results

* `Fan.exists_isExtremalRay_degree_neg`: a divisor of negative degree on a wall curve of a simplicial fan with an ample divisor has a `D`-negative extremal ray.
* `Fan.IsExtremalRay.divisorialStep`: the divisorial contraction is a toric step.
* `Fan.IsExtremalRay.isToricMoriFibreSpace`: when `J₋` is empty, the contraction is a toric Mori fibre space.
* `Fan.trichotomy`: the trichotomy for a complete simplicial fan with an ample divisor.
* `toricMMP_trichotomy`: the trichotomy at the last model of a sequence of steps, when it has an ample divisor.
-/

namespace MinimalModel.Toric

variable {n : ℕ}

section IndexCone

variable {ι E : Type*} [Fintype ι] [AddCommGroup E] [Module ℝ E]

/-- **The face cut out by a linear form.** Let `f` be a linear form that is nonnegative at the vectors `v i` with `i ∈ S`. The cone of those where it vanishes is a face of the cone of `S`. -/
theorem indexCone_isFaceOf_of_nonneg {v : ι → E} {S : Set ι} {f : E →ₗ[ℝ] ℝ}
    (hf : ∀ i ∈ S, 0 ≤ f (v i)) :
    (indexCone v {i | i ∈ S ∧ f (v i) = 0}).IsFaceOf (indexCone v S) := by
  have hsum : ∀ c : ι → ℝ, f (∑ i, c i • v i) = ∑ i, c i * f (v i) := fun c => by
    simp only [map_sum, map_smul, smul_eq_mul]
  have hnn : ∀ c : ι → ℝ, (∀ i, 0 ≤ c i) → (∀ i, i ∉ S → c i = 0) →
      ∀ i, 0 ≤ c i * f (v i) := by
    intro c hc hcS i
    by_cases hi : i ∈ S
    · exact mul_nonneg (hc i) (hf i hi)
    · rw [hcS i hi, zero_mul]
  refine ⟨indexCone_mono v fun i hi => hi.1, fun {x y r} hx hy hr hxy => ?_⟩
  obtain ⟨c, hc, hcS, rfl⟩ := mem_indexCone.mp hx
  obtain ⟨d, hd, hdS, rfl⟩ := mem_indexCone.mp hy
  obtain ⟨e, -, heT, hexy⟩ := mem_indexCone.mp hxy
  have hfe : f (r • ∑ i, c i • v i + ∑ i, d i • v i) = 0 := by
    rw [← hexy, hsum]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hi : i ∈ S ∧ f (v i) = 0
    · rw [hi.2, mul_zero]
    · rw [heT i hi, zero_mul]
  rw [map_add, map_smul, hsum, hsum, smul_eq_mul] at hfe
  have h1 := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => hnn c hc hcS i
  have h2 := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => hnn d hd hdS i
  have h3 : ∑ i, c i * f (v i) = 0 := by
    have h4 := mul_nonneg hr.le h1
    have h5 : r * ∑ i, c i * f (v i) = 0 := by linarith
    exact (mul_eq_zero.mp h5).resolve_left hr.ne'
  have h6 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hnn c hc hcS i).mp h3
  refine mem_indexCone.mpr ⟨c, hc, fun i hi => ?_, rfl⟩
  by_cases hiS : i ∈ S
  · rcases mul_eq_zero.mp (h6 i (Finset.mem_univ i)) with h7 | h7
    · exact h7
    · exact absurd ⟨hiS, h7⟩ hi
  · exact hcS i hiS

/-- **The face where a ratio is least.** Let `h` be positive at the vectors `v i` with `i ∈ S`, and let `μ` be the least value of `g / h` at them. Then `μ h ≤ g` on `S`, and the indices where `g = μ h` form a nonempty set whose cone is a face of the cone of `S`. -/
theorem exists_isFaceOf_indexCone_min {v : ι → E} {S : Set ι} {h g : E →ₗ[ℝ] ℝ}
    (hpos : ∀ i ∈ S, 0 < h (v i)) {i₀ : ι} (hi₀ : i₀ ∈ S) :
    ∃ μ : ℝ, ∃ T ⊆ S, T.Nonempty ∧ (indexCone v T).IsFaceOf (indexCone v S) ∧
      (∀ i ∈ T, g (v i) = μ * h (v i)) ∧ ∀ i ∈ S, μ * h (v i) ≤ g (v i) := by
  classical
  obtain ⟨j, hjS, hjmin⟩ := (Finset.univ.filter fun i => i ∈ S).exists_min_image
    (fun i => g (v i) / h (v i)) ⟨i₀, by simpa using hi₀⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hjS hjmin
  have hle : ∀ i ∈ S, g (v j) / h (v j) * h (v i) ≤ g (v i) := fun i hi =>
    (le_div_iff₀ (hpos i hi)).mp (hjmin i hi)
  have hf : ∀ i ∈ S, 0 ≤ (g - (g (v j) / h (v j)) • h) (v i) := fun i hi => by
    rw [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, sub_nonneg]
    exact hle i hi
  refine ⟨g (v j) / h (v j), {i | i ∈ S ∧ (g - (g (v j) / h (v j)) • h) (v i) = 0},
    fun i hi => hi.1, ⟨j, hjS, ?_⟩,
    indexCone_isFaceOf_of_nonneg hf, fun i hi => ?_, hle⟩
  · rw [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
      div_mul_cancel₀ _ (hpos j hjS).ne', sub_self]
  · have h0 := hi.2
    rw [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, sub_eq_zero] at h0
    exact h0

omit [Fintype ι] in
/-- The cone of vectors that are positive multiples of one vector `w` is the cone of `w`, when there is one. -/
theorem indexCone_eq_hull_singleton {v : ι → E} {T : Set ι} {w : E} {a : ι → ℝ}
    (ha : ∀ i ∈ T, 0 < a i) (hv : ∀ i ∈ T, v i = a i • w) {i₀ : ι} (hi₀ : i₀ ∈ T) :
    indexCone v T = PointedCone.hull ℝ {w} := by
  unfold indexCone
  refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_le.mpr fun x hx => ?_)
  · rintro _ ⟨i, hi, rfl⟩
    rw [hv i hi]
    exact PointedCone.smul_mem _ (ha i hi).le (Submodule.subset_span (Set.mem_singleton w))
  · rw [Set.mem_singleton_iff.mp hx]
    have hw : w = (a i₀)⁻¹ • v i₀ := by
      rw [hv i₀ hi₀, smul_smul, inv_mul_cancel₀ (ha i₀ hi₀).ne', one_smul]
    rw [hw]
    exact PointedCone.smul_mem _ (inv_nonneg.mpr (ha i₀ hi₀).le) (mem_indexCone_of_mem v hi₀)

/-- **A face spanned by one vector.** Let `h` be positive at the vectors `v i` with `i` in a nonempty set `S`. Then there is a nonempty subset `T` of `S` whose cone is a face of the cone of `S`, and whose vectors are positive multiples `h (v i) • w` of one vector `w`. Each coordinate `c ↦ c_k` is cut down to a multiple of `h` by `exists_isFaceOf_indexCone_min`, one after the other. -/
theorem exists_isFaceOf_indexCone_eq_hull {κ : Type*} [Fintype κ] {v : ι → κ → ℝ} {S : Set ι}
    {h : (κ → ℝ) →ₗ[ℝ] ℝ} (hpos : ∀ i ∈ S, 0 < h (v i)) (hS : S.Nonempty) :
    ∃ T ⊆ S, T.Nonempty ∧ (indexCone v T).IsFaceOf (indexCone v S) ∧
      ∃ w : κ → ℝ, ∀ i ∈ T, v i = h (v i) • w := by
  classical
  have key : ∀ I : Finset κ, ∃ T ⊆ S, T.Nonempty ∧ (indexCone v T).IsFaceOf (indexCone v S) ∧
      ∀ k ∈ I, ∃ μ : ℝ, ∀ i ∈ T, v i k = μ * h (v i) := by
    intro I
    induction I using Finset.induction_on with
    | empty => exact ⟨S, subset_rfl, hS, PointedCone.IsFaceOf.refl _, fun k hk => by simp at hk⟩
    | insert k I _ ih =>
      obtain ⟨T, hTS, ⟨i₀, hi₀⟩, hT, hI⟩ := ih
      obtain ⟨μ, T', hT'T, hT'ne, hT', hμ, -⟩ :=
        exists_isFaceOf_indexCone_min (g := LinearMap.proj k) (fun i hi => hpos i (hTS hi)) hi₀
      refine ⟨T', hT'T.trans hTS, hT'ne, hT'.trans hT, fun k' hk' => ?_⟩
      rcases Finset.mem_insert.mp hk' with rfl | hk'
      · exact ⟨μ, fun i hi => hμ i hi⟩
      · obtain ⟨μ', hμ'⟩ := hI k' hk'
        exact ⟨μ', fun i hi => hμ' i (hT'T hi)⟩
  obtain ⟨T, hTS, hTne, hT, hI⟩ := key Finset.univ
  choose w hw using fun k => hI k (Finset.mem_univ k)
  refine ⟨T, hTS, hTne, hT, w, fun i hi => funext fun k => ?_⟩
  rw [Pi.smul_apply, smul_eq_mul, hw k i hi, mul_comm]

end IndexCone

namespace Fan

variable {F : Fan n}

/-! ### A `D`-negative extremal ray -/

variable (F) in
/-- The pairing of a class `c` in `ℝ^{Σ(1)}` with a divisor `D`: `Σ c_ρ D_ρ`. On the class of a wall curve it is the degree of `D` on the curve (`Fan.WallData.curvePairing_curveClass`). -/
noncomputable def curvePairing (D : F.TDivisor ℝ) : (F.Ray → ℝ) →ₗ[ℝ] ℝ where
  toFun c := ∑ ρ, c ρ * D ρ
  map_add' c c' := by
    show ∑ ρ, (c + c') ρ * D ρ = ∑ ρ, c ρ * D ρ + ∑ ρ, c' ρ * D ρ
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' t c := by
    show ∑ ρ, (t • c) ρ * D ρ = t • ∑ ρ, c ρ * D ρ
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]

/-- The pairing of a class with a divisor. -/
theorem curvePairing_apply (D : F.TDivisor ℝ) (c : F.Ray → ℝ) :
    F.curvePairing D c = ∑ ρ, c ρ * D ρ :=
  rfl

/-- The pairing of the class of a wall curve with a divisor is the degree of the divisor. -/
theorem WallData.curvePairing_curveClass {σ σ' : PointedCone ℝ (NR n)} (W : F.WallData σ σ')
    (D : F.TDivisor ℝ) : F.curvePairing D W.curveClass = W.degree D :=
  (W.degree_eq_sum_curveClass D).symm

/-- **An ample divisor has positive degree on each wall curve.** Its support function `φ` is strictly convex at the maximal cone `σ`, so `φ(u) < m_σ(u)` at the generator `u` of the ray of `σ'` outside `σ`, and the degree is `m_σ(u) - φ(u)`. -/
theorem WallData.degree_pos_of_isAmple {σ σ' : PointedCone ℝ (NR n)} (hw : F.IsWallPair σ σ')
    (W : F.WallData σ σ') {H : F.TDivisor ℝ} (hH : F.IsAmple H) : 0 < W.degree H := by
  obtain ⟨φ, hφ, hstrict⟩ := hH
  obtain ⟨m, hm, hlt⟩ := hstrict ⊤ (Set.mem_singleton _) σ hw.1 le_top
  rw [W.degree_eq_sub hφ hm, sub_pos]
  exact hlt _ Submodule.mem_top fun h => W.ray_not_le (le_of_generator_mem h)

/-- **A `D`-negative extremal ray** (Reid 1983, Theorem 1.5; Cox, Little and Schenck, Theorem 6.3.20). Let `F` be a simplicial fan with an ample divisor `H`, and let `D` have negative degree on a wall curve. Then the cone of curves has an extremal ray `R` that contains the class of a wall curve of negative degree on `D`. -/
theorem exists_isExtremalRay_degree_neg (hs : F.IsSimplicialFan) {H : F.TDivisor ℝ}
    (hH : F.IsAmple H) {D : F.TDivisor ℝ}
    (hD : ∃ σ σ' : PointedCone ℝ (NR n), F.IsWallPair σ σ' ∧
      ∃ W : F.WallData σ σ', W.degree D < 0) :
    ∃ R, F.IsExtremalRay R ∧ ∃ σ₀ σ₀' : PointedCone ℝ (NR n), F.IsWallPair σ₀ σ₀' ∧
      ∃ W₀ : F.WallData σ₀ σ₀', W₀.curveClass ∈ R ∧ W₀.degree D < 0 := by
  classical
  have : Finite F.curveClasses := (finite_curveClasses hs).to_subtype
  let : Fintype F.curveClasses := Fintype.ofFinite _
  have hpos : ∀ i ∈ (Set.univ : Set F.curveClasses), 0 < F.curvePairing H i.1 := by
    rintro ⟨c, σ, σ', hw, W, rfl⟩ -
    show 0 < F.curvePairing H W.curveClass
    rw [W.curvePairing_curveClass]
    exact W.degree_pos_of_isAmple hw hH
  have hcc : F.curveCone = indexCone (Subtype.val : F.curveClasses → F.Ray → ℝ) Set.univ := by
    rw [curveCone_eq_hull]
    unfold indexCone
    rw [Set.image_univ, Subtype.range_coe]
  obtain ⟨σ, σ', hw, W, hW⟩ := hD
  obtain ⟨μ, T, -, hTne, hT, hμ, hle⟩ := exists_isFaceOf_indexCone_min
    (v := (Subtype.val : F.curveClasses → F.Ray → ℝ)) (g := F.curvePairing D) hpos
    (Set.mem_univ ⟨W.curveClass, σ, σ', hw, W, rfl⟩)
  have hμ0 : μ < 0 := by
    have h1 : μ * F.curvePairing H W.curveClass ≤ F.curvePairing D W.curveClass :=
      hle ⟨W.curveClass, σ, σ', hw, W, rfl⟩ (Set.mem_univ _)
    have h2 : 0 < F.curvePairing H W.curveClass :=
      hpos ⟨W.curveClass, σ, σ', hw, W, rfl⟩ (Set.mem_univ _)
    rw [W.curvePairing_curveClass, W.curvePairing_curveClass] at h1
    rw [W.curvePairing_curveClass] at h2
    by_contra h3
    have h4 := mul_nonneg (not_lt.mp h3) h2.le
    linarith
  obtain ⟨T', hT'T, ⟨i₁, hi₁⟩, hT', w, hw'⟩ :=
    exists_isFaceOf_indexCone_eq_hull (fun i _ => hpos i (Set.mem_univ i)) hTne
  have heq := indexCone_eq_hull_singleton (fun i _ => hpos i (Set.mem_univ i)) hw' hi₁
  obtain ⟨σ₁, σ₁', hw₁, W₁, hW₁⟩ := i₁.2
  refine ⟨PointedCone.hull ℝ {w}, ⟨?_, w, fun hw0 => ?_, rfl⟩, σ₁, σ₁', hw₁, W₁, ?_, ?_⟩
  · rw [hcc, ← heq]
    exact hT'.trans hT
  · have h1 := hw' i₁ hi₁
    have h2 := hpos i₁ (Set.mem_univ _)
    rw [hw0, smul_zero] at h1
    rw [h1, map_zero] at h2
    exact lt_irrefl 0 h2
  · rw [hW₁, ← heq]
    exact mem_indexCone_of_mem _ hi₁
  · rw [← W₁.curvePairing_curveClass, hW₁, hμ i₁ (hT'T hi₁)]
    exact mul_neg_of_neg_of_pos hμ0 (hpos i₁ (Set.mem_univ _))

/-! ### The divisorial contraction -/

/-- When `J₋` is the one ray `k`, the generator `u_k` is in the cone `Fan.flipCone c ν k` of the star: the relation gives `u_k = Σ_{ρ ≠ k} (c_ρ / -c_k) u_ρ`, with nonnegative coefficients. -/
theorem generator_mem_flipCone_of_unique {c : F.Ray → ℝ}
    (hrel : ∑ ρ, c ρ • toNR (F.generator ρ) = 0) {k : F.Ray} (hk : c k < 0)
    (huniq : ∀ ρ, c ρ < 0 → ρ = k) {ν : PointedCone ℝ (NR n)} (hneg : F.negCone c ≤ ν) :
    toNR (F.generator k) ∈ F.flipCone c ν k := by
  classical
  refine mem_indexCone.mpr ⟨fun ρ => c ρ / -c k + if ρ = k then 1 else 0, fun ρ => ?_,
    fun ρ hρ => ?_, ?_⟩
  · show 0 ≤ c ρ / -c k + if ρ = k then 1 else 0
    by_cases hρk : ρ = k
    · rw [ite_eq_left hρk, hρk, div_neg, div_self hk.ne]
      norm_num
    · rw [ite_eq_right hρk, add_zero]
      exact div_nonneg (not_lt.mp fun h => hρk (huniq ρ h)) (by linarith)
  · show c ρ / -c k + (if ρ = k then 1 else 0) = 0
    by_cases hρk : ρ = k
    · rw [ite_eq_left hρk, hρk, div_neg, div_self hk.ne, neg_add_cancel]
    · have h0 : c ρ = 0 := by
        by_contra h0
        exact hρ ⟨Or.inr ⟨hneg, h0⟩, fun _ => hρk⟩
      rw [ite_eq_right hρk, h0, zero_div, add_zero]
  · have h1 : ∑ ρ, (c ρ / -c k) • toNR (F.generator ρ) = 0 := by
      have h2 : ∀ ρ, (c ρ / -c k) • toNR (F.generator ρ) =
          (-c k)⁻¹ • (c ρ • toNR (F.generator ρ)) := fun ρ => by
        rw [smul_smul, div_eq_inv_mul]
      simp only [h2]
      rw [← Finset.smul_sum, hrel, smul_zero]
    simp only [add_smul, Finset.sum_add_distrib, h1, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, zero_add]

/-- **When `J₋` is one ray `k`, the cones of the flipped fan are the cones of the contraction.** On the star of `cone(u_k)` the generator `u_k` is in `Fan.flipCone c ν k` (`Fan.generator_mem_flipCone_of_unique`), and off the star both cones are `ν`. -/
theorem flipCone_eq_contractCone_of_unique {c : F.Ray → ℝ}
    (hrel : ∑ ρ, c ρ • toNR (F.generator ρ) = 0) {k : F.Ray} (hk : c k < 0)
    (huniq : ∀ ρ, c ρ < 0 → ρ = k) {ν : PointedCone ℝ (NR n)} (hν : ν ∈ F.cones) :
    F.flipCone c ν k = F.contractCone c ν := by
  refine le_antisymm (flipCone_le_contractCone c ν k) ?_
  by_cases hneg : F.negCone c ≤ ν
  · unfold contractCone
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨ρ, hρ, rfl⟩
    by_cases hρk : ρ = k
    · rw [hρk]
      exact generator_mem_flipCone_of_unique hrel hk huniq hneg
    · exact mem_indexCone_of_mem (fun ρ : F.Ray => toNR (F.generator ρ))
        (show ρ ∈ F.flipRays c ν k from ⟨hρ, fun _ => hρk⟩)
  · rw [flipCone_of_not_le hν hneg, contractCone_of_not_le hν hneg]

/-- **When `J₋` is one ray, the flipped fan is the contraction.** -/
theorem flipped_eq_contraction_of_unique {c : F.Ray → ℝ}
    (hrel : ∑ ρ, c ρ • toNR (F.generator ρ) = 0) {k : F.Ray} (hk : c k < 0)
    (huniq : ∀ ρ, c ρ < 0 → ρ = k) : F.flipped c = F.contraction c := by
  ext τ
  constructor
  · rintro ⟨ν, j, hν, hj, hτ⟩
    rw [huniq j hj, flipCone_eq_contractCone_of_unique hrel hk huniq hν.mem] at hτ
    exact ⟨ν, hν, hτ⟩
  · rintro ⟨ν, hν, hτ⟩
    refine ⟨ν, k, hν, hk, ?_⟩
    rwa [flipCone_eq_contractCone_of_unique hrel hk huniq hν.mem]

variable {R : PointedCone ℝ (F.Ray → ℝ)}

/-- The rays of the contraction fan are rays of `F`, since `F` refines it. -/
theorem IsExtremalRay.rays_contractionFan_subset (hc : F.IsComplete) (hs : F.IsSimplicialFan)
    (hR : F.IsExtremalRay R) {σ₀ σ₀' : PointedCone ℝ (NR n)} (hw₀ : F.IsWallPair σ₀ σ₀')
    (W₀ : F.WallData σ₀ σ₀') (hW₀ : W₀.curveClass ∈ R) (hJ : ∃ k, W₀.curveClass k < 0) :
    (hR.contractionFan hc hs hw₀ W₀ hW₀ hJ).rays ⊆ F.rays := by
  rintro τ ⟨hτ, hray⟩
  exact ⟨mem_cones_of_refines (hR.refines_contraction hc hs hw₀ W₀ hW₀) hτ hray, hray⟩

/-- **When `J₋` is one ray, the flipped fan has the cones of the contraction fan.** -/
theorem IsExtremalRay.cones_flippedFan_of_unique (hc : F.IsComplete) (hs : F.IsSimplicialFan)
    (hR : F.IsExtremalRay R) {σ₀ σ₀' : PointedCone ℝ (NR n)} (hw₀ : F.IsWallPair σ₀ σ₀')
    (W₀ : F.WallData σ₀ σ₀') (hW₀ : W₀.curveClass ∈ R) {k : F.Ray}
    (hk : W₀.curveClass k < 0) (huniq : ∀ ρ, W₀.curveClass ρ < 0 → ρ = k) :
    (hR.flippedFan hc hs hw₀ W₀ hW₀).cones = (hR.contractionFan hc hs hw₀ W₀ hW₀ ⟨k, hk⟩).cones :=
  flipped_eq_contraction_of_unique
    (W₀.sum_curveClass_smul_generator hw₀.1.mem (hs σ₀ hw₀.1.mem)) hk huniq

/-- When `J₋` is one ray, the flipped fan has the rays of the contraction fan. -/
theorem IsExtremalRay.rays_flippedFan_of_unique (hc : F.IsComplete) (hs : F.IsSimplicialFan)
    (hR : F.IsExtremalRay R) {σ₀ σ₀' : PointedCone ℝ (NR n)} (hw₀ : F.IsWallPair σ₀ σ₀')
    (W₀ : F.WallData σ₀ σ₀') (hW₀ : W₀.curveClass ∈ R) {k : F.Ray}
    (hk : W₀.curveClass k < 0) (huniq : ∀ ρ, W₀.curveClass ρ < 0 → ρ = k) :
    (hR.flippedFan hc hs hw₀ W₀ hW₀).rays = (hR.contractionFan hc hs hw₀ W₀ hW₀ ⟨k, hk⟩).rays := by
  unfold Fan.rays
  rw [hR.cones_flippedFan_of_unique hc hs hw₀ W₀ hW₀ hk huniq]

/-- When `J₋` is one ray, the rays of the flipped fan are rays of `F`. -/
theorem IsExtremalRay.rays_flippedFan_subset_of_unique (hc : F.IsComplete)
    (hs : F.IsSimplicialFan) (hR : F.IsExtremalRay R) {σ₀ σ₀' : PointedCone ℝ (NR n)}
    (hw₀ : F.IsWallPair σ₀ σ₀') (W₀ : F.WallData σ₀ σ₀') (hW₀ : W₀.curveClass ∈ R)
    {k : F.Ray} (hk : W₀.curveClass k < 0) (huniq : ∀ ρ, W₀.curveClass ρ < 0 → ρ = k) :
    (hR.flippedFan hc hs hw₀ W₀ hW₀).rays ⊆ F.rays :=
  (hR.rays_flippedFan_of_unique hc hs hw₀ W₀ hW₀ hk huniq).trans_subset
    (hR.rays_contractionFan_subset hc hs hw₀ W₀ hW₀ ⟨k, hk⟩)

/-- **The divisorial contraction is a toric step** (Reid 1983, Corollary 2.5 and Section 3; Matsuki, Proposition 14-2-5). Let `F` be a complete simplicial fan, `R` an extremal ray of its cone of curves, `c` the class of a wall curve in `R`, and `D` a divisor with `D · c < 0`. Let `J₋` be one ray `k`. Then the flipped fan, which is the contraction fan `G` with the ray `k` removed from the cones of the star, with the strict transform of `D`, is a toric step from `(F, D)` over `G`. -/
theorem IsExtremalRay.divisorialStep (hc : F.IsComplete) (hs : F.IsSimplicialFan)
    (hR : F.IsExtremalRay R) {σ₀ σ₀' : PointedCone ℝ (NR n)} (hw₀ : F.IsWallPair σ₀ σ₀')
    (W₀ : F.WallData σ₀ σ₀') (hW₀ : W₀.curveClass ∈ R) {k : F.Ray}
    (hk : W₀.curveClass k < 0) (huniq : ∀ ρ, W₀.curveClass ρ < 0 → ρ = k)
    {D : F.TDivisor ℝ} (hD : W₀.degree D < 0) :
    IsToricStep ⟨F, D⟩ ⟨hR.flippedFan hc hs hw₀ W₀ hW₀,
      strictTransform D _ (hR.rays_flippedFan_subset_of_unique hc hs hw₀ W₀ hW₀ hk huniq)⟩ :=
  ⟨hR.contractionFan hc hs hw₀ W₀ hW₀ ⟨k, hk⟩, hR.refines_contraction hc hs hw₀ W₀ hW₀,
    hR.hasRelPicardOne_contraction hc hs hw₀ W₀ hW₀ hD.ne,
    hR.isAmpleOver_contraction hc hs hw₀ W₀ hW₀ hD,
    hR.isSimplicialFan_flippedFan hc hs hw₀ W₀ hW₀,
    hR.refines_flippedFan hc hs hw₀ W₀ hW₀ ⟨k, hk⟩,
    hR.rays_flippedFan_of_unique hc hs hw₀ W₀ hW₀ hk huniq,
    hR.isAmpleOver_flippedFan hc hs hw₀ W₀ hW₀ ⟨k, hk⟩
      (hR.rays_flippedFan_subset_of_unique hc hs hw₀ W₀ hW₀ hk huniq) hD,
    fun _ _ hρ => strictTransform_apply_of_eq D
      (hR.rays_flippedFan_subset_of_unique hc hs hw₀ W₀ hW₀ hk huniq) hρ⟩

/-! ### The Mori fibre space -/

/-- **When `J₋` is empty, the cone of the contraction at `σ₀` contains a line.** It contains the generator `u` of the ray of `σ₀'` outside `σ₀`, which has coefficient `1` in the class, and `-u`, the sum of the other terms of the relation. -/
theorem not_isStronglyConvex_contractCone (hs : F.IsSimplicialFan)
    {σ₀ σ₀' : PointedCone ℝ (NR n)} (hw₀ : F.IsWallPair σ₀ σ₀') (W₀ : F.WallData σ₀ σ₀')
    (hJ : ∀ ρ, 0 ≤ W₀.curveClass ρ) :
    ¬ IsStronglyConvex (F.contractCone W₀.curveClass σ₀) := by
  classical
  have hrel := W₀.sum_curveClass_smul_generator hw₀.1.mem (hs σ₀ hw₀.1.mem)
  have hneg : F.negCone W₀.curveClass ≤ σ₀ := Submodule.span_le.mpr (by
    rintro _ ⟨ρ, hρ, -⟩
    exact absurd hρ (not_lt.mpr (hJ ρ)))
  have hP : ∀ ρ : F.Ray, W₀.curveClass ρ ≠ 0 →
      ρ.1 ≤ σ₀ ∨ (F.negCone W₀.curveClass ≤ σ₀ ∧ W₀.curveClass ρ ≠ 0) :=
    fun ρ h => Or.inr ⟨hneg, h⟩
  have hray : W₀.curveClass W₀.ray ≠ 0 := by
    rw [W₀.curveClass_ray]
    exact one_ne_zero
  intro hsc
  have hu : toNR (F.generator W₀.ray) ∈ F.contractCone W₀.curveClass σ₀ :=
    Submodule.subset_span ⟨W₀.ray, hP _ hray, rfl⟩
  have hnu : -toNR (F.generator W₀.ray) ∈ F.contractCone W₀.curveClass σ₀ := by
    refine (mem_hull_generator_iff (fun ρ : F.Ray => ρ.1 ≤ σ₀ ∨
      (F.negCone W₀.curveClass ≤ σ₀ ∧ W₀.curveClass ρ ≠ 0))).mpr
      ⟨fun ρ => W₀.curveClass ρ - if ρ = W₀.ray then 1 else 0, fun ρ => ?_, fun ρ hρ => ?_, ?_⟩
    · show 0 ≤ W₀.curveClass ρ - if ρ = W₀.ray then 1 else 0
      by_cases h : ρ = W₀.ray
      · rw [ite_eq_left h, h, W₀.curveClass_ray]
        norm_num
      · rw [ite_eq_right h, sub_zero]
        exact hJ ρ
    · show W₀.curveClass ρ - (if ρ = W₀.ray then 1 else 0) = 0
      have h0 : W₀.curveClass ρ = 0 := by
        by_contra h0
        exact hρ (hP ρ h0)
      have h1 : ρ ≠ W₀.ray := fun h => hray (by rw [← h]; exact h0)
      rw [h0, ite_eq_right h1, sub_zero]
    · simp only [sub_smul, Finset.sum_sub_distrib, hrel, ite_smul, one_smul, zero_smul,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true, zero_sub]
  have h0 := hsc _ hu hnu
  exact W₀.ray_not_le (le_of_generator_mem (by rw [h0]; exact Submodule.zero_mem _))

/-- **The contraction of fibre type is a toric Mori fibre space** (Reid 1983, Section 2; Matsuki, Proposition 14-2-5). When `J₋` is empty and `D · c < 0`, the contraction is a quasi-fan with a cone that contains a line, `F` has relative Picard number one over it, and `-D` is ample over it. -/
theorem IsExtremalRay.isToricMoriFibreSpace (hc : F.IsComplete) (hs : F.IsSimplicialFan)
    (hR : F.IsExtremalRay R) {σ₀ σ₀' : PointedCone ℝ (NR n)} (hw₀ : F.IsWallPair σ₀ σ₀')
    (W₀ : F.WallData σ₀ σ₀') (hW₀ : W₀.curveClass ∈ R) (hJ : ∀ ρ, 0 ≤ W₀.curveClass ρ)
    {D : F.TDivisor ℝ} (hD : W₀.degree D < 0) : IsToricMoriFibreSpace ⟨F, D⟩ :=
  ⟨F.contraction W₀.curveClass, hR.isQuasiFan_contraction hc hs hw₀ W₀ hW₀,
    ⟨F.contractCone W₀.curveClass σ₀, ⟨σ₀, hw₀.1, PointedCone.IsFaceOf.refl _⟩,
      not_isStronglyConvex_contractCone hs hw₀ W₀ hJ⟩,
    hR.refines_contraction hc hs hw₀ W₀ hW₀, hR.hasRelPicardOne_contraction hc hs hw₀ W₀ hW₀ hD.ne,
    hR.isAmpleOver_contraction hc hs hw₀ W₀ hW₀ hD⟩

/-! ### The trichotomy -/

/-- **The contraction of a `D`-negative extremal ray** is a toric Mori fibre space when `J₋` is empty, a divisorial step when `J₋` is one ray, and a flip when `J₋` has two rays. -/
theorem IsExtremalRay.isToricMoriFibreSpace_or_isToricStep (hc : F.IsComplete)
    (hs : F.IsSimplicialFan) (hR : F.IsExtremalRay R) {σ₀ σ₀' : PointedCone ℝ (NR n)}
    (hw₀ : F.IsWallPair σ₀ σ₀') (W₀ : F.WallData σ₀ σ₀') (hW₀ : W₀.curveClass ∈ R)
    {D : F.TDivisor ℝ} (hD : W₀.degree D < 0) :
    IsToricMoriFibreSpace ⟨F, D⟩ ∨ ∃ B, IsToricStep ⟨F, D⟩ B := by
  by_cases hJ : ∃ k, W₀.curveClass k < 0
  · right
    obtain ⟨k, hk⟩ := hJ
    by_cases h2 : ∃ k', W₀.curveClass k' < 0 ∧ k' ≠ k
    · obtain ⟨k', hk', hne⟩ := h2
      exact ⟨_, hR.flipExists hc hs hw₀ W₀ hW₀ hk hk' (Ne.symm hne) hD⟩
    · have huniq : ∀ ρ, W₀.curveClass ρ < 0 → ρ = k := fun ρ hρ => by
        by_contra hne
        exact h2 ⟨ρ, hρ, hne⟩
      exact ⟨_, hR.divisorialStep hc hs hw₀ W₀ hW₀ hk huniq hD⟩
  · left
    exact hR.isToricMoriFibreSpace hc hs hw₀ W₀ hW₀ (fun ρ => not_lt.mp fun h => hJ ⟨ρ, h⟩) hD

/-- **The trichotomy of the toric `D`-program** (Reid 1983, Sections 2 and 3; Cox, Little and Schenck, Section 15.4). Let `F` be a complete simplicial fan with an ample divisor, and `D` a divisor. Then `D` is nef, or `(F, D)` is a toric Mori fibre space, or there is a toric step from `(F, D)`. -/
theorem trichotomy (hc : F.IsComplete) (hs : F.IsSimplicialFan)
    (hp : ∃ H : F.TDivisor ℝ, F.IsAmple H) (D : F.TDivisor ℝ) :
    F.IsNef D ∨ IsToricMoriFibreSpace ⟨F, D⟩ ∨ ∃ B, IsToricStep ⟨F, D⟩ B := by
  by_cases hnef : F.IsNef D
  · exact Or.inl hnef
  right
  rw [coneTheorem hc hs (hs.isRCartier D)] at hnef
  push Not at hnef
  obtain ⟨H, hH⟩ := hp
  obtain ⟨R, hR, σ₀, σ₀', hw₀, W₀, hW₀, hD⟩ := exists_isExtremalRay_degree_neg hs hH hnef
  exact hR.isToricMoriFibreSpace_or_isToricStep hc hs hw₀ W₀ hW₀ hD

/-- **The trichotomy on a projective simplicial fan.** -/
theorem IsProjectiveFan.trichotomy (hp : F.IsProjectiveFan) (hs : F.IsSimplicialFan)
    (D : F.TDivisor ℝ) :
    F.IsNef D ∨ IsToricMoriFibreSpace ⟨F, D⟩ ∨ ∃ B, IsToricStep ⟨F, D⟩ B :=
  Fan.trichotomy hp.1 hs (hp.2.imp fun _ h => h.2) D

end Fan

/-! ### Steps preserve the hypotheses -/

namespace IsToricStep

variable {A B : ToricModel n}

/-- **A toric step keeps completeness**: `A.F`, the base `G` and `B.F` have the same support. -/
theorem isComplete (h : IsToricStep A B) (hA : A.F.IsComplete) : B.F.IsComplete := by
  obtain ⟨G, hAG, -, -, -, hBG, -⟩ := h
  unfold Fan.IsComplete
  rw [← Fan.support_eq_of_refines hBG, Fan.support_eq_of_refines hAG]
  exact hA

/-- A toric step gives a simplicial fan. -/
theorem isSimplicialFan (h : IsToricStep A B) : B.F.IsSimplicialFan := by
  obtain ⟨G, -, -, -, hB, -⟩ := h
  exact hB

/-- **A toric step does not add rays**: the rays of `B.F` are the rays of the base, which are rays of `A.F`. -/
theorem rays_subset (h : IsToricStep A B) : B.F.rays ⊆ A.F.rays := by
  obtain ⟨G, hAG, -, -, -, -, hrays, -⟩ := h
  rw [hrays]
  rintro τ ⟨hτ, hray⟩
  exact ⟨Fan.mem_cones_of_refines hAG hτ hray, hray⟩

/-- **A toric step keeps rational coefficients**: the divisor of `B` is the strict transform. -/
theorem rational (h : IsToricStep A B) (hA : ∀ ρ, A.D ρ ∈ Set.range ((↑) : ℚ → ℝ)) :
    ∀ ρ, B.D ρ ∈ Set.range ((↑) : ℚ → ℝ) := by
  intro ρ
  have hsub := h.rays_subset
  obtain ⟨G, -, -, -, -, -, -, -, hD⟩ := h
  rw [hD ρ ⟨ρ.1, hsub ρ.2⟩ rfl]
  exact hA _

end IsToricStep

/-- **A sequence of toric steps keeps completeness and simpliciality.** -/
theorem isComplete_isSimplicialFan_of_steps {model : ℕ → ToricModel n} {m : ℕ}
    (hc : (model 0).F.IsComplete) (hs : (model 0).F.IsSimplicialFan)
    (hsteps : ∀ i < m, IsToricStep (model i) (model (i + 1))) :
    ∀ i ≤ m, (model i).F.IsComplete ∧ (model i).F.IsSimplicialFan := by
  intro i
  induction i with
  | zero => exact fun _ => ⟨hc, hs⟩
  | succ i ih =>
    intro hi
    have hstep := hsteps i (Nat.lt_of_succ_le hi)
    exact ⟨hstep.isComplete (ih (Nat.le_of_succ_le hi)).1, hstep.isSimplicialFan⟩

/-- **A sequence of toric steps keeps rational coefficients.** -/
theorem rational_of_steps {model : ℕ → ToricModel n} {m : ℕ}
    (hD : ∀ ρ, (model 0).D ρ ∈ Set.range ((↑) : ℚ → ℝ))
    (hsteps : ∀ i < m, IsToricStep (model i) (model (i + 1))) :
    ∀ i ≤ m, ∀ ρ, (model i).D ρ ∈ Set.range ((↑) : ℚ → ℝ) := by
  intro i
  induction i with
  | zero => exact fun _ => hD
  | succ i ih =>
    intro hi
    exact (hsteps i (Nat.lt_of_succ_le hi)).rational (ih (Nat.le_of_succ_le hi))

/-- **The trichotomy at the last model of a sequence of toric steps** (conjunct 2 of `MinimalModel.ToricMMP`, when the last model has an ample divisor). Let `F` be a complete simplicial fan, and let `model 0 = (F, D)`, ..., `model m` be a sequence of toric steps. When the fan of `model m` has an ample divisor, the divisor is nef on it, or it is a toric Mori fibre space, or one more toric step starts at it. -/
theorem toricMMP_trichotomy {F : Fan n} (hc : F.IsComplete) (hs : F.IsSimplicialFan)
    {D : F.TDivisor ℝ} (m : ℕ) (model : ℕ → ToricModel n) (h0 : model 0 = ⟨F, D⟩)
    (hsteps : ∀ i < m, IsToricStep (model i) (model (i + 1)))
    (hp : ∃ H : (model m).F.TDivisor ℝ, (model m).F.IsAmple H) :
    (model m).F.IsNef (model m).D ∨ IsToricMoriFibreSpace (model m) ∨
      ∃ B, IsToricStep (model m) B := by
  have hc0 : (model 0).F.IsComplete := by
    rw [h0]
    exact hc
  have hs0 : (model 0).F.IsSimplicialFan := by
    rw [h0]
    exact hs
  obtain ⟨hcm, hsm⟩ := isComplete_isSimplicialFan_of_steps hc0 hs0 hsteps m le_rfl
  exact Fan.trichotomy hcm hsm hp (model m).D

end MinimalModel.Toric
