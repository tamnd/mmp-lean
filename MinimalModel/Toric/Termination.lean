/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import MinimalModel.Toric.Program
import MinimalModel.Toric.ConeTheorem
import MinimalModel.Toric.ConeClosed

/-!
# Toric flips, part 11: termination of the toric program

This file proves the first part of the statement `ToricMMP` (S39): no infinite sequence of toric steps `IsToricStep` starts at a complete fan (Fujino and Sato, Introduction to the toric Mori theory, Michigan Math. J. 52 (2004); Matsuki, Introduction to the Mori program, 14-2-7; Cox, Little and Schenck, Section 15.4). The step `IsToricStep` is an abstract predicate on pairs of models, so the proof works with each sequence of steps, not only with the flips and the divisorial contractions that `MinimalModel/Toric/FlipExists.lean` constructs.

## The rays and the cones

Let `A → B` be a step with base `G`. Each ray of `G` is a union of cones of `A.F`, so it is a ray of `A.F`, and the rays of `B.F` are the rays of `G` (`Fan.Refines.rays_subset`). So along a sequence of steps the rays of each fan are rays of the first fan `F`, and the coefficient of the divisor at a ray does not change. The fans `A.F`, `G` and `B.F` have the same support (`Fan.Refines.support_eq`), so each fan of the sequence is complete. Each cone of a fan is spanned by the generators of its rays, so the sets of cones of the fans of the sequence lie in a finite set (`finite_cones_of_rays_subset`).

## The support function goes up

Let `φ_A` and `φ_B` be the support functions of the divisors of the step. Let `x` be a vector, `σ` a maximal cone of `A.F` that contains `x`, `τ` the cone of `G` that contains `σ`, and `σ'` a cone of `B.F` in `τ` that contains `x`. Write `x` as a nonnegative combination of generators `u_ρ` of rays of `σ'`. The function `-φ_A` lies below its linear form `m` of `σ` on `τ`, and it agrees with `-φ_B` at the generators `u_ρ`; so `φ_A(x) = -m(x) ≤ φ_B(x)` (`IsToricStep.supportFunction_le`).

If `φ_A = φ_B`, then for each maximal cone `τ` of `G` there are a maximal cone `σ` of `A.F` and a maximal cone `σ'` of `B.F` in `τ` such that `σ ∩ σ'` has interior points (Baire). The linear forms of `-φ_A` on `σ` and of `φ_B` on `σ'` agree on these interior points, so they are opposite, and the strict convexity of `-φ_A` on `τ` at `σ` gives `τ = σ`. So each cone of `G` is in a cone of `A.F`, each divisor on `A.F` is a pullback from `G`, and this contradicts the relative Picard number one (`IsToricStep.supportFunction_ne`).

So the support functions of a sequence of steps strictly increase, and no two fans of the sequence have the same cones, since the support function only depends on the cones and the coefficients at the rays. There are finitely many sets of cones, so the sequence is finite. The proof needs neither the simpliciality of `F` nor the rationality of the divisor.

## Main results

* `IsToricStep.supportFunction_le`, `IsToricStep.supportFunction_ne`: in a toric step the support function goes up, and it changes.
* `not_exists_infinite_toricStep`: **termination.** No infinite sequence of toric steps starts at a complete fan.
* `toricMMP_not_exists_infinite`: the first part of `ToricMMP`, in its exact form.
-/

namespace MinimalModel.Toric

variable {n : ℕ}

/-! ### Interiors of cones -/

/-- A finite union of closed sets with an interior point has a member with an interior point. This is the Baire category theorem, for the space `N_ℝ`. -/
theorem exists_nonempty_interior_of_biUnion {ι : Type*} {S : Set ι} (hS : S.Finite)
    {f : ι → Set (NR n)} (hc : ∀ i ∈ S, IsClosed (f i))
    (h : (interior (⋃ i ∈ S, f i)).Nonempty) : ∃ i ∈ S, (interior (f i)).Nonempty := by
  by_contra hne
  have hnd : ∀ i ∈ S, IsNowhereDense (f i) := fun i hi =>
    (hc i hi).isNowhereDense_iff.mpr
      (Set.not_nonempty_iff_eq_empty.mp fun h' => hne ⟨i, hi, h'⟩)
  rw [interior_biUnion_of_isClosed hc hS.countable hnd] at h
  exact Set.not_nonempty_empty h

/-- A face of a cone `C` that contains an interior point of `C` is `C`. -/
theorem eq_of_isFaceOf_of_mem_interior {F C : PointedCone ℝ (NR n)} (hF : F.IsFaceOf C)
    {x : NR n} (hxF : x ∈ F) (hx : x ∈ interior (C : Set (NR n))) : F = C := by
  refine le_antisymm hF.le fun y hy => ?_
  have hC : (C : Set (NR n)) ∈ nhds (x - (0 : ℝ) • y) := by
    rw [zero_smul, sub_zero]
    exact mem_interior_iff_mem_nhds.mp hx
  have hev : ∀ᶠ t in nhds (0 : ℝ), x - t • y ∈ (C : Set (NR n)) :=
    (by fun_prop : Continuous fun t : ℝ => x - t • y).continuousAt.preimage_mem_nhds hC
  obtain ⟨t, ht, htC⟩ := ((eventually_mem_nhdsWithin (a := (0 : ℝ)) (s := Set.Ioi 0)).and
    (eventually_nhdsWithin_of_eventually_nhds hev)).exists
  refine hF.mem_of_smul_add_mem hy htC (Set.mem_Ioi.mp ht) ?_
  simpa using hxF

/-- Two linear forms that agree on a nonempty open set are equal. -/
theorem linearMap_eq_of_eqOn_isOpen {m m' : NR n →ₗ[ℝ] ℝ} {W : Set (NR n)} (hW : IsOpen W)
    {x : NR n} (hx : x ∈ W) (h : ∀ y ∈ W, m y = m' y) : m = m' := by
  refine LinearMap.ext fun v => ?_
  have hW' : W ∈ nhds (x + (0 : ℝ) • v) := by
    rw [zero_smul, add_zero]
    exact hW.mem_nhds hx
  have hev : ∀ᶠ t in nhds (0 : ℝ), x + t • v ∈ W :=
    (by fun_prop : Continuous fun t : ℝ => x + t • v).continuousAt.preimage_mem_nhds hW'
  obtain ⟨t, ht, htW⟩ := ((eventually_mem_nhdsWithin (a := (0 : ℝ)) (s := Set.Ioi 0)).and
    (eventually_nhdsWithin_of_eventually_nhds hev)).exists
  have h1 := h _ htW
  rw [map_add, map_add, map_smul, map_smul, h x hx, smul_eq_mul, smul_eq_mul] at h1
  exact mul_left_cancel₀ (Set.mem_Ioi.mp ht).ne' (add_left_cancel h1)

namespace Fan

/-- A cone of a fan with an interior point is a maximal cone. -/
theorem isMaximalCone_of_nonempty_interior {F : Fan n} {σ : PointedCone ℝ (NR n)}
    (hσ : σ ∈ F.cones) (hint : (interior (σ : Set (NR n))).Nonempty) : F.IsMaximalCone σ := by
  refine ⟨hσ, fun σ' hσ' hle => ?_⟩
  obtain ⟨x, hx⟩ := hint
  have hface := F.inter_face σ' hσ' σ hσ
  rw [inf_eq_right.mpr hle] at hface
  exact (eq_of_isFaceOf_of_mem_interior hface (interior_subset hx)
    (interior_mono (SetLike.coe_subset_coe.mpr hle) hx)).ge

/-- A maximal cone `τ` of a complete fan has an interior point: the sum `x₀` of the generators of the rays of `τ`. A cone of the fan that contains `x₀` meets `τ` in a face that contains each generator, so it contains `τ`, and it is `τ`. The cones that do not contain `x₀` form a closed set, and its complement is a neighbourhood of `x₀` in `τ`. -/
theorem nonempty_interior_of_isComplete {G : Fan n} (hG : G.IsComplete)
    {τ : PointedCone ℝ (NR n)} (hτ : G.IsMaximalCone τ) :
    (interior (τ : Set (NR n))).Nonempty := by
  classical
  have hτG : τ ∈ G.cones := hτ.mem
  have hsfin : {x | ∃ ρ : G.Ray, ρ.1 ≤ τ ∧ toNR (G.generator ρ) = x}.Finite :=
    (Set.finite_range fun ρ : G.Ray => toNR (G.generator ρ)).subset
      (by rintro _ ⟨ρ, -, rfl⟩; exact ⟨ρ, rfl⟩)
  have htτ : ∀ x ∈ hsfin.toFinset, x ∈ τ := by
    intro x hx
    obtain ⟨ρ, hρ, rfl⟩ := hsfin.mem_toFinset.mp hx
    exact hρ (G.toNR_generator_mem ρ)
  have hx₀ : ∑ x ∈ hsfin.toFinset, (1 : ℝ) • x ∈ τ :=
    Submodule.sum_mem _ fun x hx => τ.smul_mem zero_le_one (htτ x hx)
  have hkey : ∀ τ' ∈ G.cones, ∑ x ∈ hsfin.toFinset, (1 : ℝ) • x ∈ τ' →
      τ' ≤ τ := by
    intro τ' hτ' hx
    have hface := G.inter_face τ hτG τ' hτ'
    have hle : τ ≤ τ ⊓ τ' := (G.eq_hull_generator hτG).le.trans
      (Submodule.span_le.mpr fun y hy =>
        mem_face_of_sum_smul_mem (c := fun _ => 1) hface htτ (fun _ _ => zero_le_one)
          (Submodule.mem_inf.mpr ⟨hx₀, hx⟩) (hsfin.mem_toFinset.mpr hy) one_pos)
    exact hτ.le_of_le hτ' (hle.trans inf_le_right)
  have hK : IsClosed (⋃ τ' ∈ {τ' | τ' ∈ G.cones ∧
      ∑ x ∈ hsfin.toFinset, (1 : ℝ) • x ∉ τ'}, (τ' : Set (NR n))) :=
    Set.Finite.isClosed_biUnion (G.finite.subset fun τ' h => h.1) fun τ' h =>
      G.isClosed_of_mem h.1
  refine ⟨∑ x ∈ hsfin.toFinset, (1 : ℝ) • x,
    mem_interior.mpr ⟨_, ?_, hK.isOpen_compl, ?_⟩⟩
  · intro y hy
    obtain ⟨τ', hτ', hyτ'⟩ := exists_mem_of_isComplete hG y
    by_cases hx : ∑ x ∈ hsfin.toFinset, (1 : ℝ) • x ∈ τ'
    · exact hkey τ' hτ' hx hyτ'
    · exact (hy (Set.mem_biUnion (x := τ') ⟨hτ', hx⟩ hyτ')).elim
  · intro hK'
    obtain ⟨τ', hτ', hx⟩ := Set.mem_iUnion₂.mp hK'
    exact hτ'.2 hx

/-! ### Refinements -/

/-- A fan that refines a set of cones `T` has the support `⋃ τ ∈ T, τ`. -/
theorem Refines.support_eq {F : Fan n} {T : Set (PointedCone ℝ (NR n))} (h : F.Refines T) :
    F.support = ⋃ τ ∈ T, (τ : Set (NR n)) := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨σ, hσ, hxσ⟩ := F.mem_support.mp hx
    obtain ⟨τ, hτ, hστ⟩ := h.1 σ hσ
    exact Set.mem_biUnion hτ (hστ hxσ)
  · intro x hx
    obtain ⟨τ, hτ, hxτ⟩ := Set.mem_iUnion₂.mp hx
    rw [h.2 τ hτ] at hxτ
    obtain ⟨σ, hσ, hxσ⟩ := Set.mem_iUnion₂.mp hxτ
    exact F.mem_support.mpr ⟨σ, hσ.1, hxσ⟩

/-- If a complete fan refines a fan `G`, then `G` is complete. -/
theorem Refines.isComplete_base {F G : Fan n} (h : F.Refines G.cones) (hF : F.IsComplete) :
    G.IsComplete := by
  have he : F.support = G.support := h.support_eq
  show G.support = Set.univ
  rw [← he]
  exact hF

/-- A fan that refines a complete fan is complete. -/
theorem Refines.isComplete_of_base {F G : Fan n} (h : F.Refines G.cones) (hG : G.IsComplete) :
    F.IsComplete := by
  have he : F.support = G.support := h.support_eq
  show F.support = Set.univ
  rw [he]
  exact hG

/-- If a fan `F` refines a fan `G`, then each ray of `G` is a ray of `F`: the ray is a union of cones of `F` in it, and the cone that contains its generator is the ray. -/
theorem Refines.rays_subset {F G : Fan n} (h : F.Refines G.cones) : G.rays ⊆ F.rays := by
  intro ρ hρ
  have hu : toNR (rayGenerator ρ) ∈ (ρ : Set (NR n)) := hρ.2.toNR_rayGenerator_mem
  rw [h.2 ρ hρ.1] at hu
  obtain ⟨σ, hσ, huσ⟩ := Set.mem_iUnion₂.mp hu
  have hle : ρ ≤ σ := by
    rw [← hρ.2.latticeCone_rayGenerator]
    exact latticeCone_singleton_le.mpr huσ
  have hσρ : σ = ρ := le_antisymm hσ.2 hle
  rw [Fan.mem_rays, ← hσρ]
  exact ⟨hσ.1, hσρ ▸ hρ.2⟩

/-- If `φ` is a support function of `-D`, then `-φ` is a support function of `D`. -/
theorem IsSupportFunctionOf.of_neg {F : Fan n} {D : F.TDivisor ℝ} {φ : NR n → ℝ}
    (h : F.IsSupportFunctionOf (-D) φ) : F.IsSupportFunctionOf D (-φ) := by
  refine ⟨fun σ hσ => ?_, fun ρ => ?_⟩
  · obtain ⟨m, hm⟩ := h.1 σ hσ
    exact ⟨-m, fun x hx => by rw [Pi.neg_apply, hm x hx, LinearMap.neg_apply]⟩
  · rw [Pi.neg_apply, h.2 ρ, Finsupp.neg_apply, neg_neg]

end Fan

/-! ### The support function in a step -/

/-- **The support function goes up in a toric step** (Fujino and Sato, 2004; Matsuki, 14-2-7). Let `A → B` be a toric step from a complete fan, and `φ_A`, `φ_B` support functions of the divisors. Then `φ_A ≤ φ_B`. For a vector `x` in a maximal cone `σ` of `A.F`, in a cone `τ` of the base, and in a cone `σ'` of `B.F` in `τ`, the linear form `m` of `-φ_A` on `σ` is at least `-φ_A = -φ_B` at the generators of the rays of `σ'`, so `-φ_B(x) ≤ m(x) = -φ_A(x)`. -/
theorem IsToricStep.supportFunction_le {A B : ToricModel n} (h : IsToricStep A B)
    (hA : A.F.IsComplete) {φA φB : NR n → ℝ} (hφA : A.F.IsSupportFunctionOf A.D φA)
    (hφB : B.F.IsSupportFunctionOf B.D φB) : φA ≤ φB := by
  obtain ⟨G, hAG, -, ⟨ψ, hψ, hstrA⟩, -, hBG, hrays, -, hD⟩ := h
  intro x
  obtain ⟨σ₀, hσ₀, hxσ₀⟩ := Fan.exists_mem_of_isComplete hA x
  obtain ⟨σ, hσ₀σ, hσ⟩ := A.F.exists_le_isMaximalCone hσ₀
  obtain ⟨τ, hτ, hστ⟩ := hAG.1 σ hσ.mem
  have hxσ : x ∈ σ := hσ₀σ hxσ₀
  have hxτ : x ∈ (τ : Set (NR n)) := hστ hxσ
  rw [hBG.2 τ hτ] at hxτ
  obtain ⟨σ', ⟨hσ'B, hσ'τ⟩, hxσ'⟩ := Set.mem_iUnion₂.mp hxτ
  obtain ⟨m, hmσ, hmlt⟩ := hstrA τ hτ σ hσ hστ
  obtain ⟨mB, hmB⟩ := hφB.1 σ' hσ'B
  have hle : (-mB) x ≤ m x := by
    refine le_of_mem_hull ?_ ((B.F.eq_hull_generator hσ'B).le hxσ')
    rintro _ ⟨ρ', hρ', rfl⟩
    have hρG : ρ'.1 ∈ G.rays := hrays ▸ ρ'.2
    have hρA : ρ'.1 ∈ A.F.rays := hAG.rays_subset hρG
    have hu : toNR (B.F.generator ρ') ∈ σ' := hρ' (B.F.toNR_generator_mem ρ')
    have e1 : ψ (toNR (B.F.generator ρ')) = A.D ⟨ρ'.1, hρA⟩ := by
      have e := hψ.2 ⟨ρ'.1, hρA⟩
      rw [Finsupp.neg_apply, neg_neg] at e
      exact e
    have e2 : mB (toNR (B.F.generator ρ')) = -B.D ρ' := by
      rw [← hmB _ hu, hφB.2 ρ']
    have e3 : B.D ρ' = A.D ⟨ρ'.1, hρA⟩ := hD ρ' _ rfl
    have hψm : ψ (toNR (B.F.generator ρ')) ≤ m (toNR (B.F.generator ρ')) := by
      by_cases hus : toNR (B.F.generator ρ') ∈ σ
      · exact (hmσ _ hus).le
      · exact (hmlt _ (hσ'τ hu) hus).le
    rw [LinearMap.neg_apply, e2, e3, neg_neg, ← e1]
    exact hψm
  have e4 : φA x = -ψ x :=
    (hψ.of_neg.eqOn_support hφA (A.F.mem_support.mpr ⟨σ, hσ.mem, hxσ⟩)).symm
  rw [e4, hmσ x hxσ, hmB x hxσ']
  rw [LinearMap.neg_apply] at hle
  linarith

/-- **The support function changes in a toric step.** Let `A → B` be a toric step from a complete fan, with base `G`. If the support functions of the divisors were equal, then each maximal cone `τ` of `G` would be a cone of `A.F`: there are maximal cones `σ` of `A.F` and `σ'` of `B.F` in `τ` whose intersection has interior points, the linear forms of the support function on `σ` and `σ'` agree there, and the strict convexity of `-φ_A` on `τ` at `σ` gives `τ ≤ σ`. Then each divisor on `A.F` would be a pullback from `G`, against the relative Picard number one. -/
theorem IsToricStep.supportFunction_ne {A B : ToricModel n} (h : IsToricStep A B)
    (hA : A.F.IsComplete) {φA φB : NR n → ℝ} (hφA : A.F.IsSupportFunctionOf A.D φA)
    (hφB : B.F.IsSupportFunctionOf B.D φB) : φA ≠ φB := by
  intro heq
  obtain ⟨G, hAG, ⟨D₀, hD₀, hnot, -⟩, ⟨ψ, hψ, hstrA⟩, -, hBG, -,
    ⟨ψB, hψB, hstrB⟩, -⟩ := h
  have hG : G.IsComplete := hAG.isComplete_base hA
  have hB : B.F.IsComplete := hBG.isComplete_of_base hG
  have hψφ : ∀ x, ψ x = -φA x := by
    intro x
    have e := hψ.of_neg.eqOn_support hφA
      (A.F.mem_support.mpr (Fan.exists_mem_of_isComplete hA x))
    rw [← e, Pi.neg_apply, neg_neg]
  have hψBφ : ∀ x, ψB x = φB x := fun x =>
    hψB.eqOn_support hφB (B.F.mem_support.mpr (Fan.exists_mem_of_isComplete hB x))
  have hmaxA : ∀ τ, G.IsMaximalCone τ → τ ∈ A.F.cones := by
    intro τ hτ
    have hτG : τ ∈ G.cones := hτ.mem
    have hτint := Fan.nonempty_interior_of_isComplete hG hτ
    rw [hAG.2 τ hτG] at hτint
    obtain ⟨σ, ⟨hσA, hστ⟩, hσint⟩ := exists_nonempty_interior_of_biUnion
      (S := {σ | σ ∈ A.F.cones ∧ σ ≤ τ}) (f := fun σ => (σ : Set (NR n)))
      (A.F.finite.subset fun σ hσ => hσ.1) (fun σ hσ => A.F.isClosed_of_mem hσ.1) hτint
    have hσmax : A.F.IsMaximalCone σ := Fan.isMaximalCone_of_nonempty_interior hσA hσint
    have hcov : (σ : Set (NR n)) ⊆
        ⋃ σ' ∈ {σ' | σ' ∈ B.F.cones ∧ σ' ≤ τ}, (σ : Set (NR n)) ∩ σ' := by
      intro x hx
      have hxτ : x ∈ (τ : Set (NR n)) := hστ hx
      rw [hBG.2 τ hτG] at hxτ
      obtain ⟨σ', hσ', hxσ'⟩ := Set.mem_iUnion₂.mp hxτ
      exact Set.mem_iUnion₂.mpr ⟨σ', hσ', hx, hxσ'⟩
    obtain ⟨σ', ⟨hσ'B, hσ'τ⟩, hint⟩ := exists_nonempty_interior_of_biUnion
      (S := {σ' | σ' ∈ B.F.cones ∧ σ' ≤ τ}) (f := fun σ' => (σ : Set (NR n)) ∩ σ')
      (B.F.finite.subset fun σ' hσ' => hσ'.1)
      (fun σ' hσ' => (A.F.isClosed_of_mem hσA).inter (B.F.isClosed_of_mem hσ'.1))
      (hσint.mono (interior_mono hcov))
    have hσ'max : B.F.IsMaximalCone σ' := Fan.isMaximalCone_of_nonempty_interior hσ'B
      (hint.mono (interior_mono Set.inter_subset_right))
    obtain ⟨m, hmσ, hmlt⟩ := hstrA τ hτG σ hσmax hστ
    obtain ⟨m', hm'σ', hm'lt⟩ := hstrB τ hτG σ' hσ'max hσ'τ
    obtain ⟨x₀, hx₀⟩ := hint
    have hmm : m = -m' := linearMap_eq_of_eqOn_isOpen isOpen_interior hx₀ fun y hy => by
      have hy' : y ∈ (σ : Set (NR n)) ∩ σ' := interior_subset hy
      rw [← hmσ y hy'.1, LinearMap.neg_apply, ← hm'σ' y hy'.2, hψφ y, hψBφ y, heq]
    have hτσ : τ ≤ σ := by
      intro u hu
      by_contra hnu
      have h1 := hmlt u hu hnu
      have h2 : ψB u ≤ m' u := by
        by_cases hu' : u ∈ σ'
        · exact (hm'σ' u hu').le
        · exact (hm'lt u hu hu').le
      rw [hmm, LinearMap.neg_apply, hψφ u, heq] at h1
      rw [hψBφ u] at h2
      linarith
    exact (le_antisymm hστ hτσ) ▸ hσA
  apply hnot
  obtain ⟨φ₀, hφ₀⟩ := hD₀.exists_isSupportFunctionOf
  refine ⟨φ₀, hφ₀, fun τ hτ => ?_⟩
  obtain ⟨τ₁, hττ₁, hτ₁⟩ := G.exists_le_isMaximalCone hτ
  obtain ⟨m, hm⟩ := hφ₀.1 τ₁ (hmaxA τ₁ hτ₁)
  exact ⟨m, fun x hx => hm x (hττ₁ hx)⟩

/-! ### Termination -/

/-- The sets of cones of the fans whose rays are in a finite set `R` form a finite set: each cone of such a fan is spanned by the generators of the rays of `R` in it. -/
theorem finite_cones_of_rays_subset (R : Set (PointedCone ℝ (NR n))) (hR : R.Finite) :
    {T : Set (PointedCone ℝ (NR n)) | ∃ F : Fan n, F.rays ⊆ R ∧ F.cones = T}.Finite := by
  refine ((hR.finite_subsets.image fun S =>
    PointedCone.hull ℝ ((fun ρ => toNR (rayGenerator ρ)) '' S)).finite_subsets).subset ?_
  rintro _ ⟨F, hF, rfl⟩
  show F.cones ⊆ _
  intro σ hσ
  refine ⟨{ρ | ρ ∈ F.rays ∧ ρ ≤ σ}, fun ρ hρ => hF hρ.1, ?_⟩
  show PointedCone.hull ℝ _ = σ
  conv_rhs => rw [F.eq_hull_generator hσ]
  congr 1
  ext x
  constructor
  · rintro ⟨ρ, ⟨hρ, hρσ⟩, rfl⟩
    exact ⟨⟨ρ, hρ⟩, hρσ, rfl⟩
  · rintro ⟨ρ, hρσ, rfl⟩
    exact ⟨ρ.1, ⟨ρ.2, hρσ⟩, rfl⟩

/-- **Termination of the toric program** (Fujino and Sato, 2004; Matsuki, 14-2-7; Cox, Little and Schenck, Section 15.4). No infinite sequence of toric steps starts at a complete fan `F` with a divisor `D`. Along a sequence of steps, each fan is complete, its rays are rays of `F`, and the coefficient of the divisor at a ray is that of `D`. So the support functions strictly increase (`IsToricStep.supportFunction_le`, `IsToricStep.supportFunction_ne`), and two fans of the sequence with the same cones have the same support function. There are finitely many sets of cones (`finite_cones_of_rays_subset`), so two fans of the sequence have the same cones, a contradiction. -/
theorem not_exists_infinite_toricStep {F : Fan n} (hF : F.IsComplete) (D : F.TDivisor ℝ) :
    ¬ ∃ model : ℕ → ToricModel n, model 0 = ⟨F, D⟩ ∧
      ∀ i, IsToricStep (model i) (model (i + 1)) := by
  rintro ⟨model, h0, hstep⟩
  have hcomp : ∀ i, (model i).F.IsComplete := by
    intro i
    induction i with
    | zero => rw [h0]; exact hF
    | succ i ih =>
      obtain ⟨G, hAG, -, -, -, hBG, -, -, -⟩ := hstep i
      exact hBG.isComplete_of_base (hAG.isComplete_base ih)
  have hray : ∀ i, ∀ ρ : (model i).F.Ray,
      ∃ ρ₀ : F.Ray, ρ₀.1 = ρ.1 ∧ (model i).D ρ = D ρ₀ := by
    intro i
    induction i with
    | zero =>
      have key : ∀ M : ToricModel n, M = ⟨F, D⟩ →
          ∀ ρ : M.F.Ray, ∃ ρ₀ : F.Ray, ρ₀.1 = ρ.1 ∧ M.D ρ = D ρ₀ := by
        rintro M rfl ρ
        exact ⟨ρ, rfl, rfl⟩
      exact key _ h0
    | succ i ih =>
      intro ρ'
      obtain ⟨G, hAG, -, -, -, -, hrays, -, hD⟩ := hstep i
      have hρG : ρ'.1 ∈ G.rays := hrays ▸ ρ'.2
      obtain ⟨ρ₀, h1, h2⟩ := ih ⟨ρ'.1, hAG.rays_subset hρG⟩
      exact ⟨ρ₀, h1, (hD ρ' ⟨ρ'.1, hAG.rays_subset hρG⟩ rfl).trans h2⟩
  have hsub : ∀ i, (model i).F.rays ⊆ F.rays := by
    intro i ρ hρ
    obtain ⟨ρ₀, h1, -⟩ := hray i ⟨ρ, hρ⟩
    have h1' : ρ₀.1 = ρ := h1
    rw [← h1']
    exact ρ₀.2
  have hex : ∀ i, ∃ φ : NR n → ℝ, (model i).F.IsSupportFunctionOf (model i).D φ := by
    intro i
    obtain ⟨G, -, -, ⟨ψ, hψ, -⟩, -⟩ := hstep i
    exact ⟨-ψ, hψ.of_neg⟩
  choose Φ hΦ using hex
  have hmono : StrictMono Φ := strictMono_nat_of_lt_succ fun i =>
    lt_of_le_of_ne ((hstep i).supportFunction_le (hcomp i) (hΦ i) (hΦ (i + 1)))
      ((hstep i).supportFunction_ne (hcomp i) (hΦ i) (hΦ (i + 1)))
  have hmem : ∀ i, (model i).F.cones ∈
      {T : Set (PointedCone ℝ (NR n)) | ∃ F' : Fan n, F'.rays ⊆ F.rays ∧ F'.cones = T} :=
    fun i => ⟨(model i).F, hsub i, rfl⟩
  obtain ⟨i, j, hij, hcones⟩ := Set.Finite.exists_lt_map_eq_of_forall_mem
    (f := fun i : ℕ => (model i).F.cones) hmem (finite_cones_of_rays_subset F.rays F.rays_finite)
  have hc : (model i).F.cones = (model j).F.cones := hcones
  have heq : Φ i = Φ j := by
    funext x
    obtain ⟨σ, hσ, hxσ⟩ := Fan.exists_mem_of_isComplete (hcomp i) x
    have hσj : σ ∈ (model j).F.cones := hc ▸ hσ
    obtain ⟨m, hm⟩ := (hΦ i).1 σ hσ
    obtain ⟨m', hm'⟩ := (hΦ j).1 σ hσj
    rw [hm x hxσ, hm' x hxσ]
    refine (model i).F.eq_of_eq_generator hσ (fun ρ hρ => ?_) hxσ
    have hu := hρ ((model i).F.toNR_generator_mem ρ)
    have hρj : ρ.1 ∈ (model j).F.rays := by
      rw [Fan.mem_rays, ← hc]
      exact ρ.2
    obtain ⟨ρ₀, h1, h2⟩ := hray i ρ
    obtain ⟨ρ₀', h1', h2'⟩ := hray j ⟨ρ.1, hρj⟩
    have hρ₀ : ρ₀ = ρ₀' := Subtype.ext (h1.trans h1'.symm)
    rw [← hm _ hu, ← hm' _ hu]
    calc Φ i (toNR ((model i).F.generator ρ)) = -(model i).D ρ := (hΦ i).2 ρ
      _ = -(model j).D ⟨ρ.1, hρj⟩ := by rw [h2, h2', hρ₀]
      _ = Φ j (toNR ((model i).F.generator ρ)) := ((hΦ j).2 ⟨ρ.1, hρj⟩).symm
  exact absurd (hmono.injective heq) hij.ne

/-- **The first part of `ToricMMP` (S39)**, in its exact form: no infinite sequence of toric steps starts at `(F, D)`. It follows from `not_exists_infinite_toricStep`, since a projective fan is complete; the simpliciality of `F` and the rationality of `D` are not used. -/
theorem toricMMP_not_exists_infinite :
    ∀ (n : ℕ) (F : Fan n), F.IsSimplicialFan → F.IsProjectiveFan →
      ∀ D : F.TDivisor ℝ, (∀ ρ, D ρ ∈ Set.range ((↑) : ℚ → ℝ)) →
        ¬ ∃ model : ℕ → ToricModel n, model 0 = ⟨F, D⟩ ∧
          ∀ i, IsToricStep (model i) (model (i + 1)) :=
  fun _ _ _ hP D _ => not_exists_infinite_toricStep hP.1 D

end MinimalModel.Toric
