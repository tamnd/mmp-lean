/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import MinimalModel.Toric.Divisor

/-!
# The fan of the projective line

Check F2 of spec 06.3 asks for instances of the definitions, so that no statement is true only because its hypotheses can never hold. This file gives the fan of the projective line `ℙ¹`. It lives in `N_ℝ = ℝ`, and its cones are `0`, `ℝ≥0 · e` and `ℝ≥0 · (-e)`. We prove that it is a fan, that it is complete and simplicial, that it has two rays, and that the sum of the coefficients of its canonical divisor is `-2`. This is the degree of the canonical divisor of `ℙ¹`.

The fan of the affine space `𝔸ⁿ` is `Fan.affine` in `MinimalModel/Toric/Fan.lean`.
-/

namespace MinimalModel.Toric.P1

/-- Two vectors of `ℝ¹` are equal when their coordinates are equal. -/
theorem ext {x y : NR 1} (h : x 0 = y 0) : x = y :=
  funext fun i => by rw [Subsingleton.elim i 0]; exact h

/-- The cone `ℝ≥0 · e` of the vectors with a nonnegative coordinate. -/
noncomputable def pos : PointedCone ℝ (NR 1) := latticeCone {1}

/-- The cone `ℝ≥0 · (-e)` of the vectors with a nonpositive coordinate. -/
noncomputable def neg : PointedCone ℝ (NR 1) := latticeCone {-1}

/-- A vector is in `pos` when its coordinate is nonnegative. -/
theorem mem_pos {x : NR 1} : x ∈ pos ↔ 0 ≤ x 0 := by
  rw [pos, mem_latticeCone_singleton]
  constructor
  · rintro ⟨r, hr, rfl⟩
    simpa using hr
  · intro hx
    exact ⟨x 0, hx, ext (by simp)⟩

/-- A vector is in `neg` when its coordinate is nonpositive. -/
theorem mem_neg {x : NR 1} : x ∈ neg ↔ x 0 ≤ 0 := by
  rw [neg, mem_latticeCone_singleton]
  constructor
  · rintro ⟨r, hr, rfl⟩
    simpa using hr
  · intro hx
    exact ⟨-x 0, by linarith, ext (by simp)⟩

/-- The cones `pos` and `neg` meet in the zero cone. -/
theorem pos_inf_neg : pos ⊓ neg = ⊥ := by
  ext x
  rw [Submodule.mem_inf, mem_pos, mem_neg, Submodule.mem_bot]
  constructor
  · rintro ⟨h1, h2⟩
    exact ext (by rw [Pi.zero_apply]; linarith)
  · rintro rfl
    simp

/-- The cones `neg` and `pos` meet in the zero cone. -/
theorem neg_inf_pos : neg ⊓ pos = ⊥ := by
  rw [inf_comm, pos_inf_neg]

/-- The cone `pos` is strongly convex. -/
theorem isStronglyConvex_pos : IsStronglyConvex pos := by
  intro v hv hnv
  rw [mem_pos] at hv hnv
  rw [Pi.neg_apply] at hnv
  exact ext (by rw [Pi.zero_apply]; linarith)

/-- The cone `neg` is strongly convex. -/
theorem isStronglyConvex_neg : IsStronglyConvex neg := by
  intro v hv hnv
  rw [mem_neg] at hv hnv
  rw [Pi.neg_apply] at hnv
  exact ext (by rw [Pi.zero_apply]; linarith)

/-- The cones `pos` and `neg` are different. -/
theorem pos_ne_neg : pos ≠ neg := by
  intro h
  have h1 : (1 : NR 1) ∈ pos := mem_pos.mpr (by simp)
  rw [h, mem_neg] at h1
  simp at h1

/-- The fan of `ℙ¹`: the cones `0`, `pos` and `neg`. -/
noncomputable def fan : Fan 1 where
  cones := {⊥, pos, neg}
  finite := ((Set.finite_singleton _).insert _).insert _
  rational σ hσ := by
    rcases hσ with rfl | rfl | rfl
    · exact isRationalPolyhedral_bot
    · exact ⟨{1}, rfl⟩
    · exact ⟨{-1}, rfl⟩
  stronglyConvex σ hσ := by
    rcases hσ with rfl | rfl | rfl
    · exact isStronglyConvex_bot
    · exact isStronglyConvex_pos
    · exact isStronglyConvex_neg
  face_mem σ hσ τ hτ := by
    rcases hσ with rfl | rfl | rfl
    · exact Or.inl (le_bot_iff.mp hτ.le)
    · rcases eq_bot_or_eq_of_isFaceOf_latticeCone_singleton hτ with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    · rcases eq_bot_or_eq_of_isFaceOf_latticeCone_singleton hτ with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inr rfl)
  inter_face σ hσ τ hτ := by
    rcases hσ with rfl | rfl | rfl <;> rcases hτ with rfl | rfl | rfl <;>
      simp only [inf_idem, bot_inf_eq, inf_bot_eq, pos_inf_neg, neg_inf_pos] <;>
      first
      | exact PointedCone.IsFaceOf.refl _
      | exact bot_isFaceOf isStronglyConvex_pos
      | exact bot_isFaceOf isStronglyConvex_neg

/-- The cones of the fan of `ℙ¹`. -/
theorem mem_cones {σ : PointedCone ℝ (NR 1)} : σ ∈ fan.cones ↔ σ = ⊥ ∨ σ = pos ∨ σ = neg :=
  Iff.rfl

/-- The fan of `ℙ¹` is complete: each vector of `ℝ` is in `pos` or in `neg`. -/
theorem isComplete : fan.IsComplete := by
  refine Set.eq_univ_of_forall fun x => (fan.mem_support).mpr ?_
  rcases le_total 0 (x 0) with h | h
  · exact ⟨pos, mem_cones.mpr (Or.inr (Or.inl rfl)), mem_pos.mpr h⟩
  · exact ⟨neg, mem_cones.mpr (Or.inr (Or.inr rfl)), mem_neg.mpr h⟩

/-- The fan of `ℙ¹` is simplicial. -/
theorem isSimplicialFan : fan.IsSimplicialFan := by
  intro σ hσ
  rcases mem_cones.mp hσ with rfl | rfl | rfl
  · exact isSimplicial_bot
  · exact isSimplicial_latticeCone_singleton one_ne_zero
  · exact isSimplicial_latticeCone_singleton (neg_ne_zero.mpr one_ne_zero)

/-- The rays of the fan of `ℙ¹` are `pos` and `neg`. -/
theorem rays_fan : fan.rays = {pos, neg} := by
  ext ρ
  simp only [Fan.rays, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hρ, hr⟩
    rcases mem_cones.mp hρ with rfl | rfl | rfl
    · exact absurd rfl hr.ne_bot
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨mem_cones.mpr (Or.inr (Or.inl rfl)), 1, one_ne_zero, rfl⟩
    · exact ⟨mem_cones.mpr (Or.inr (Or.inr rfl)), -1, neg_ne_zero.mpr one_ne_zero, rfl⟩

/-- The fan of `ℙ¹` has two rays. -/
theorem card_ray : Nat.card fan.Ray = 2 := by
  show Nat.card ↥fan.rays = 2
  rw [rays_fan, Nat.card_coe_set_eq, Set.ncard_pair pos_ne_neg]

/-- The sum of the coefficients of the canonical divisor of `ℙ¹` is `-2`. -/
theorem coeffSum_canonical : fan.coeffSum fan.canonical = -2 := by
  rw [Fan.coeffSum_canonical, card_ray]
  norm_num

end MinimalModel.Toric.P1
