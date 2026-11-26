/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import MinimalModel.Toric.Wall

/-!
# The fans of the projective line and the projective plane

Check F2 of spec 06.3 asks for instances of the definitions, so that no statement is true only because its hypotheses can never hold. This file gives the fan of the projective line `ℙ¹` and the fan of the projective plane `ℙ²`. It lives in `N_ℝ = ℝ`, and its cones are `0`, `ℝ≥0 · e` and `ℝ≥0 · (-e)`. We prove that it is a fan, that it is complete and simplicial, that it has two rays, and that the sum of the coefficients of its canonical divisor is `-2`. This is the degree of the canonical divisor of `ℙ¹`.

The fan of `ℙ²` lives in `N_ℝ = ℝ²`. Its rays are spanned by `e₁`, `e₂` and `e₀ = -e₁ - e₂`, and its three 2-cones are spanned by two of them (Cox, Little and Schenck, Example 3.1.10). We prove that it is a fan, that it is complete and simplicial, that it has three rays with the primitive generators `e₁`, `e₂` and `e₀`, that the sum of the coefficients of its canonical divisor is `-3`, and that its canonical divisor is Cartier. The wall relation of each pair of adjacent 2-cones is `e₁ + e₂ + e₀ = 0`.

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
  have h2 : (1 : NR 1) 0 ≤ 0 := mem_neg.mp (h ▸ h1)
  have h3 : (1 : NR 1) 0 = (1 : ℝ) := rfl
  linarith

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

namespace MinimalModel.Toric.P2

/-- Two vectors of `ℝ²` are equal when their coordinates are equal. -/
theorem ext {x y : NR 2} (h0 : x 0 = y 0) (h1 : x 1 = y 1) : x = y := by
  funext i
  fin_cases i
  exacts [h0, h1]

/-- The lattice point `e₁ = (1, 0)`. -/
def e1 : Fin 2 → ℤ := ![1, 0]

/-- The lattice point `e₂ = (0, 1)`. -/
def e2 : Fin 2 → ℤ := ![0, 1]

/-- The lattice point `e₀ = -e₁ - e₂ = (-1, -1)`. -/
def e0 : Fin 2 → ℤ := ![-1, -1]

/-- A coordinate of `e1`. -/
@[simp]
theorem e1_zero : e1 0 = 1 := rfl
/-- A coordinate of `e1`. -/
@[simp]
theorem e1_one : e1 1 = 0 := rfl
/-- A coordinate of `e2`. -/
@[simp]
theorem e2_zero : e2 0 = 0 := rfl
/-- A coordinate of `e2`. -/
@[simp]
theorem e2_one : e2 1 = 1 := rfl
/-- A coordinate of `e0`. -/
@[simp]
theorem e0_zero : e0 0 = -1 := rfl
/-- A coordinate of `e0`. -/
@[simp]
theorem e0_one : e0 1 = -1 := rfl

/-- The point `e₁` is not zero. -/
theorem e1_ne_zero : e1 ≠ 0 := fun h => by simpa using congrFun h 0

/-- The point `e₂` is not zero. -/
theorem e2_ne_zero : e2 ≠ 0 := fun h => by simpa using congrFun h 1

/-- The point `e₀` is not zero. -/
theorem e0_ne_zero : e0 ≠ 0 := fun h => by simpa using congrFun h 0

/-- The point `e₁` is primitive. -/
theorem isPrimitive_e1 : IsPrimitive e1 := isPrimitive_of_isUnit (i := 0) (by simp)

/-- The point `e₂` is primitive. -/
theorem isPrimitive_e2 : IsPrimitive e2 := isPrimitive_of_isUnit (i := 1) (by simp)

/-- The point `e₀` is primitive. -/
theorem isPrimitive_e0 : IsPrimitive e0 :=
  isPrimitive_of_isUnit (i := 0) (by rw [e0_zero]; exact isUnit_one.neg)

/-- The ray `ℝ≥0 · e₁`. -/
noncomputable def r1 : PointedCone ℝ (NR 2) := latticeCone {e1}

/-- The ray `ℝ≥0 · e₂`. -/
noncomputable def r2 : PointedCone ℝ (NR 2) := latticeCone {e2}

/-- The ray `ℝ≥0 · e₀`. -/
noncomputable def r0 : PointedCone ℝ (NR 2) := latticeCone {e0}

/-- The 2-cone spanned by `e₁` and `e₂`. -/
noncomputable def c12 : PointedCone ℝ (NR 2) := latticeCone {e1, e2}

/-- The 2-cone spanned by `e₂` and `e₀`. -/
noncomputable def c20 : PointedCone ℝ (NR 2) := latticeCone {e2, e0}

/-- The 2-cone spanned by `e₀` and `e₁`. -/
noncomputable def c01 : PointedCone ℝ (NR 2) := latticeCone {e0, e1}

/-- The vectors of `r1` in coordinates. -/
theorem mem_r1 {x : NR 2} : x ∈ r1 ↔ 0 ≤ x 0 ∧ x 1 = 0 := by
  rw [r1, mem_latticeCone_singleton]
  constructor
  · rintro ⟨r, hr, rfl⟩
    simpa using hr
  · rintro ⟨h0, h1⟩
    exact ⟨x 0, h0, ext (by simp) (by simp [h1])⟩

/-- The vectors of `r2` in coordinates. -/
theorem mem_r2 {x : NR 2} : x ∈ r2 ↔ x 0 = 0 ∧ 0 ≤ x 1 := by
  rw [r2, mem_latticeCone_singleton]
  constructor
  · rintro ⟨r, hr, rfl⟩
    simpa using hr
  · rintro ⟨h0, h1⟩
    exact ⟨x 1, h1, ext (by simp [h0]) (by simp)⟩

/-- The vectors of `r0` in coordinates. -/
theorem mem_r0 {x : NR 2} : x ∈ r0 ↔ x 0 ≤ 0 ∧ x 1 = x 0 := by
  rw [r0, mem_latticeCone_singleton]
  constructor
  · rintro ⟨r, hr, rfl⟩
    simpa using hr
  · rintro ⟨h0, h1⟩
    exact ⟨-x 0, by linarith, ext (by simp) (by simp [h1])⟩

/-- The vectors of `c12` in coordinates. -/
theorem mem_c12 {x : NR 2} : x ∈ c12 ↔ 0 ≤ x 0 ∧ 0 ≤ x 1 := by
  rw [c12, mem_latticeCone_pair]
  constructor
  · rintro ⟨r, s, hr, hs, rfl⟩
    exact ⟨by simpa using hr, by simpa using hs⟩
  · rintro ⟨h0, h1⟩
    exact ⟨x 0, x 1, h0, h1, ext (by simp) (by simp)⟩

/-- The vectors of `c20` in coordinates. -/
theorem mem_c20 {x : NR 2} : x ∈ c20 ↔ x 0 ≤ 0 ∧ x 0 ≤ x 1 := by
  rw [c20, mem_latticeCone_pair]
  constructor
  · rintro ⟨r, s, hr, hs, rfl⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, toNR_apply, e2_zero, e2_one, e0_zero,
      e0_one, Int.cast_zero, Int.cast_one, Int.cast_neg]
    constructor <;> linarith
  · rintro ⟨h0, h1⟩
    refine ⟨x 1 - x 0, -x 0, by linarith, by linarith, ext ?_ ?_⟩ <;>
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, toNR_apply, e2_zero, e2_one, e0_zero,
        e0_one, Int.cast_zero, Int.cast_one, Int.cast_neg] <;> ring

/-- The vectors of `c01` in coordinates. -/
theorem mem_c01 {x : NR 2} : x ∈ c01 ↔ x 1 ≤ 0 ∧ x 1 ≤ x 0 := by
  rw [c01, mem_latticeCone_pair]
  constructor
  · rintro ⟨r, s, hr, hs, rfl⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, toNR_apply, e1_zero, e1_one, e0_zero,
      e0_one, Int.cast_zero, Int.cast_one, Int.cast_neg]
    constructor <;> linarith
  · rintro ⟨h0, h1⟩
    refine ⟨-x 1, x 0 - x 1, by linarith, by linarith, ext ?_ ?_⟩ <;>
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, toNR_apply, e1_zero, e1_one, e0_zero,
        e0_one, Int.cast_zero, Int.cast_one, Int.cast_neg] <;> ring

/-- The cone `c12` is strongly convex. -/
theorem isStronglyConvex_c12 : IsStronglyConvex c12 := by
  intro v hv hnv
  rw [mem_c12] at hv hnv
  simp only [Pi.neg_apply] at hnv
  obtain ⟨h0, h1⟩ := hv
  obtain ⟨h2, h3⟩ := hnv
  exact ext (by rw [Pi.zero_apply]; linarith) (by rw [Pi.zero_apply]; linarith)

/-- The cone `c20` is strongly convex. -/
theorem isStronglyConvex_c20 : IsStronglyConvex c20 := by
  intro v hv hnv
  rw [mem_c20] at hv hnv
  simp only [Pi.neg_apply] at hnv
  obtain ⟨h0, h1⟩ := hv
  obtain ⟨h2, h3⟩ := hnv
  exact ext (by rw [Pi.zero_apply]; linarith) (by rw [Pi.zero_apply]; linarith)

/-- The cone `c01` is strongly convex. -/
theorem isStronglyConvex_c01 : IsStronglyConvex c01 := by
  intro v hv hnv
  rw [mem_c01] at hv hnv
  simp only [Pi.neg_apply] at hnv
  obtain ⟨h0, h1⟩ := hv
  obtain ⟨h2, h3⟩ := hnv
  exact ext (by rw [Pi.zero_apply]; linarith) (by rw [Pi.zero_apply]; linarith)

/-- The ray `r1` lies in the cone `c12`. -/
theorem r1_le_c12 : r1 ≤ c12 := fun x hx => by
  rw [mem_r1] at hx; rw [mem_c12]; constructor <;> linarith [hx.1, hx.2]
/-- The ray `r2` lies in the cone `c12`. -/
theorem r2_le_c12 : r2 ≤ c12 := fun x hx => by
  rw [mem_r2] at hx; rw [mem_c12]; constructor <;> linarith [hx.1, hx.2]
/-- The ray `r2` lies in the cone `c20`. -/
theorem r2_le_c20 : r2 ≤ c20 := fun x hx => by
  rw [mem_r2] at hx; rw [mem_c20]; constructor <;> linarith [hx.1, hx.2]
/-- The ray `r0` lies in the cone `c20`. -/
theorem r0_le_c20 : r0 ≤ c20 := fun x hx => by
  rw [mem_r0] at hx; rw [mem_c20]; constructor <;> linarith [hx.1, hx.2]
/-- The ray `r0` lies in the cone `c01`. -/
theorem r0_le_c01 : r0 ≤ c01 := fun x hx => by
  rw [mem_r0] at hx; rw [mem_c01]; constructor <;> linarith [hx.1, hx.2]
/-- The ray `r1` lies in the cone `c01`. -/
theorem r1_le_c01 : r1 ≤ c01 := fun x hx => by
  rw [mem_r1] at hx; rw [mem_c01]; constructor <;> linarith [hx.1, hx.2]

/-- The ray `r1` is strongly convex. -/
theorem isStronglyConvex_r1 : IsStronglyConvex r1 := isStronglyConvex_c12.mono r1_le_c12
/-- The ray `r2` is strongly convex. -/
theorem isStronglyConvex_r2 : IsStronglyConvex r2 := isStronglyConvex_c12.mono r2_le_c12
/-- The ray `r0` is strongly convex. -/
theorem isStronglyConvex_r0 : IsStronglyConvex r0 := isStronglyConvex_c20.mono r0_le_c20

/-- The linear form `x ↦ a x₀ + b x₁` on `ℝ²`. -/
noncomputable def form (a b : ℝ) : NR 2 →ₗ[ℝ] ℝ := linearForm ![a, b]

/-- The value of the form `x ↦ a x₀ + b x₁`. -/
theorem form_apply (a b : ℝ) (x : NR 2) : form a b x = a * x 0 + b * x 1 := by
  simp [form, Fin.sum_univ_two]

/-- A face cut out by the form `x ↦ a x₀ + b x₁`. -/
theorem isFaceOf_of_form {τ σ : PointedCone ℝ (NR 2)} (a b : ℝ)
    (hσ : ∀ x ∈ σ, 0 ≤ a * x 0 + b * x 1)
    (hτ : ∀ x, x ∈ τ ↔ x ∈ σ ∧ a * x 0 + b * x 1 = 0) : τ.IsFaceOf σ :=
  IsFace.isFaceOf ⟨form a b, fun x hx => by rw [form_apply]; exact hσ x hx,
    fun x => by rw [form_apply]; exact hτ x⟩

/-- The ray `r1` is a face of the cone `c12`. -/
theorem r1_face_c12 : r1.IsFaceOf c12 := isFaceOf_of_form 0 1
  (fun x hx => by rw [mem_c12] at hx; linarith [hx.1, hx.2])
  fun x => by
    rw [mem_r1, mem_c12]
    constructor
    · rintro ⟨h0, h1⟩
      exact ⟨⟨by linarith, by linarith⟩, by linarith⟩
    · rintro ⟨⟨h0, h1⟩, h2⟩
      exact ⟨by linarith, by linarith⟩

/-- The ray `r2` is a face of the cone `c12`. -/
theorem r2_face_c12 : r2.IsFaceOf c12 := isFaceOf_of_form 1 0
  (fun x hx => by rw [mem_c12] at hx; linarith [hx.1, hx.2])
  fun x => by
    rw [mem_r2, mem_c12]
    constructor
    · rintro ⟨h0, h1⟩
      exact ⟨⟨by linarith, by linarith⟩, by linarith⟩
    · rintro ⟨⟨h0, h1⟩, h2⟩
      exact ⟨by linarith, by linarith⟩

/-- The ray `r2` is a face of the cone `c20`. -/
theorem r2_face_c20 : r2.IsFaceOf c20 := isFaceOf_of_form (-1) 0
  (fun x hx => by rw [mem_c20] at hx; linarith [hx.1, hx.2])
  fun x => by
    rw [mem_r2, mem_c20]
    constructor
    · rintro ⟨h0, h1⟩
      exact ⟨⟨by linarith, by linarith⟩, by linarith⟩
    · rintro ⟨⟨h0, h1⟩, h2⟩
      exact ⟨by linarith, by linarith⟩

/-- The ray `r0` is a face of the cone `c20`. -/
theorem r0_face_c20 : r0.IsFaceOf c20 := isFaceOf_of_form (-1) 1
  (fun x hx => by rw [mem_c20] at hx; linarith [hx.1, hx.2])
  fun x => by
    rw [mem_r0, mem_c20]
    constructor
    · rintro ⟨h0, h1⟩
      exact ⟨⟨by linarith, by linarith⟩, by linarith⟩
    · rintro ⟨⟨h0, h1⟩, h2⟩
      exact ⟨by linarith, by linarith⟩

/-- The ray `r0` is a face of the cone `c01`. -/
theorem r0_face_c01 : r0.IsFaceOf c01 := isFaceOf_of_form 1 (-1)
  (fun x hx => by rw [mem_c01] at hx; linarith [hx.1, hx.2])
  fun x => by
    rw [mem_r0, mem_c01]
    constructor
    · rintro ⟨h0, h1⟩
      exact ⟨⟨by linarith, by linarith⟩, by linarith⟩
    · rintro ⟨⟨h0, h1⟩, h2⟩
      exact ⟨by linarith, by linarith⟩

/-- The ray `r1` is a face of the cone `c01`. -/
theorem r1_face_c01 : r1.IsFaceOf c01 := isFaceOf_of_form 0 (-1)
  (fun x hx => by rw [mem_c01] at hx; linarith [hx.1, hx.2])
  fun x => by
    rw [mem_r1, mem_c01]
    constructor
    · rintro ⟨h0, h1⟩
      exact ⟨⟨by linarith, by linarith⟩, by linarith⟩
    · rintro ⟨⟨h0, h1⟩, h2⟩
      exact ⟨by linarith, by linarith⟩

/-- Two vectors with zero coordinates are zero. -/
theorem eq_zero {x : NR 2} (h0 : x 0 = 0) (h1 : x 1 = 0) : x = 0 :=
  ext (by rw [h0, Pi.zero_apply]) (by rw [h1, Pi.zero_apply])

/-- The intersection of `r1` and `r2`. -/
theorem r1_inf_r2 : r1 ⊓ r2 = ⊥ := by
  ext x
  rw [Submodule.mem_inf, mem_r1, mem_r2, Submodule.mem_bot]
  constructor
  · rintro ⟨⟨h2, h1⟩, h0, h3⟩
    exact eq_zero h0 h1
  · rintro rfl
    simp

/-- The intersection of `r1` and `r0`. -/
theorem r1_inf_r0 : r1 ⊓ r0 = ⊥ := by
  ext x
  rw [Submodule.mem_inf, mem_r1, mem_r0, Submodule.mem_bot]
  constructor
  · rintro ⟨⟨h0, h1⟩, h2, h3⟩
    exact eq_zero (by linarith) h1
  · rintro rfl
    simp

/-- The intersection of `r2` and `r0`. -/
theorem r2_inf_r0 : r2 ⊓ r0 = ⊥ := by
  ext x
  rw [Submodule.mem_inf, mem_r2, mem_r0, Submodule.mem_bot]
  constructor
  · rintro ⟨⟨h0, h1⟩, h2, h3⟩
    exact eq_zero h0 (by linarith)
  · rintro rfl
    simp

/-- The intersection of `r1` and `c20`. -/
theorem r1_inf_c20 : r1 ⊓ c20 = ⊥ := by
  ext x
  rw [Submodule.mem_inf, mem_r1, mem_c20, Submodule.mem_bot]
  constructor
  · rintro ⟨⟨h0, h1⟩, h2, h3⟩
    exact eq_zero (by linarith) h1
  · rintro rfl
    simp

/-- The intersection of `r2` and `c01`. -/
theorem r2_inf_c01 : r2 ⊓ c01 = ⊥ := by
  ext x
  rw [Submodule.mem_inf, mem_r2, mem_c01, Submodule.mem_bot]
  constructor
  · rintro ⟨⟨h0, h1⟩, h2, h3⟩
    exact eq_zero h0 (by linarith)
  · rintro rfl
    simp

/-- The intersection of `r0` and `c12`. -/
theorem r0_inf_c12 : r0 ⊓ c12 = ⊥ := by
  ext x
  rw [Submodule.mem_inf, mem_r0, mem_c12, Submodule.mem_bot]
  constructor
  · rintro ⟨⟨h0, h1⟩, h2, h3⟩
    exact eq_zero (by linarith) (by linarith)
  · rintro rfl
    simp

/-- The intersection of `c12` and `c20`. -/
theorem c12_inf_c20 : c12 ⊓ c20 = r2 := by
  ext x
  rw [Submodule.mem_inf, mem_c12, mem_c20, mem_r2]
  constructor
  · rintro ⟨⟨h0, h1⟩, h2, h3⟩
    exact ⟨by linarith, h1⟩
  · rintro ⟨h0, h1⟩
    exact ⟨⟨by linarith, h1⟩, by linarith, by linarith⟩

/-- The intersection of `c20` and `c01`. -/
theorem c20_inf_c01 : c20 ⊓ c01 = r0 := by
  ext x
  rw [Submodule.mem_inf, mem_c20, mem_c01, mem_r0]
  constructor
  · rintro ⟨⟨h0, h1⟩, h2, h3⟩
    exact ⟨h0, by linarith⟩
  · rintro ⟨h0, h1⟩
    exact ⟨⟨h0, by linarith⟩, by linarith, by linarith⟩

/-- The intersection of `c01` and `c12`. -/
theorem c01_inf_c12 : c01 ⊓ c12 = r1 := by
  ext x
  rw [Submodule.mem_inf, mem_c01, mem_c12, mem_r1]
  constructor
  · rintro ⟨⟨h0, h1⟩, h2, h3⟩
    exact ⟨h2, by linarith⟩
  · rintro ⟨h0, h1⟩
    exact ⟨⟨by linarith, by linarith⟩, h0, by linarith⟩

/-- The intersection of `r2` and `r1`. -/
theorem r2_inf_r1 : r2 ⊓ r1 = ⊥ := by rw [inf_comm, r1_inf_r2]
/-- The intersection of `r0` and `r1`. -/
theorem r0_inf_r1 : r0 ⊓ r1 = ⊥ := by rw [inf_comm, r1_inf_r0]
/-- The intersection of `r0` and `r2`. -/
theorem r0_inf_r2 : r0 ⊓ r2 = ⊥ := by rw [inf_comm, r2_inf_r0]
/-- The intersection of `c20` and `r1`. -/
theorem c20_inf_r1 : c20 ⊓ r1 = ⊥ := by rw [inf_comm, r1_inf_c20]
/-- The intersection of `c01` and `r2`. -/
theorem c01_inf_r2 : c01 ⊓ r2 = ⊥ := by rw [inf_comm, r2_inf_c01]
/-- The intersection of `c12` and `r0`. -/
theorem c12_inf_r0 : c12 ⊓ r0 = ⊥ := by rw [inf_comm, r0_inf_c12]
/-- The intersection of `c20` and `c12`. -/
theorem c20_inf_c12 : c20 ⊓ c12 = r2 := by rw [inf_comm, c12_inf_c20]
/-- The intersection of `c01` and `c20`. -/
theorem c01_inf_c20 : c01 ⊓ c20 = r0 := by rw [inf_comm, c20_inf_c01]
/-- The intersection of `c12` and `c01`. -/
theorem c12_inf_c01 : c12 ⊓ c01 = r1 := by rw [inf_comm, c01_inf_c12]

/-- The cones of the fan of `ℙ²`: the zero cone, three rays and three 2-cones. -/
def cones : Set (PointedCone ℝ (NR 2)) := {⊥, r1, r2, r0, c12, c20, c01}

/-- The cones of the fan of `ℙ²`. -/
theorem mem_cones {σ : PointedCone ℝ (NR 2)} :
    σ ∈ cones ↔ σ = ⊥ ∨ σ = r1 ∨ σ = r2 ∨ σ = r0 ∨ σ = c12 ∨ σ = c20 ∨ σ = c01 :=
  Iff.rfl

/-- The fan of `ℙ²`. -/
noncomputable def fan : Fan 2 where
  cones := cones
  finite := (((((((Set.finite_singleton _).insert _).insert _).insert _).insert _).insert _).insert _)
  rational σ hσ := by
    rcases mem_cones.mp hσ with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact isRationalPolyhedral_bot
    · exact ⟨{e1}, rfl⟩
    · exact ⟨{e2}, rfl⟩
    · exact ⟨{e0}, rfl⟩
    · exact ⟨{e1, e2}, rfl⟩
    · exact ⟨{e2, e0}, rfl⟩
    · exact ⟨{e0, e1}, rfl⟩
  stronglyConvex σ hσ := by
    rcases mem_cones.mp hσ with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact isStronglyConvex_bot
    · exact isStronglyConvex_r1
    · exact isStronglyConvex_r2
    · exact isStronglyConvex_r0
    · exact isStronglyConvex_c12
    · exact isStronglyConvex_c20
    · exact isStronglyConvex_c01
  face_mem σ hσ τ hτ := by
    rw [mem_cones]
    rcases mem_cones.mp hσ with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (le_bot_iff.mp hτ.le)
    · rcases eq_bot_or_eq_of_isFaceOf_latticeCone_singleton hτ with rfl | rfl <;> simp [r1]
    · rcases eq_bot_or_eq_of_isFaceOf_latticeCone_singleton hτ with rfl | rfl <;> simp [r2]
    · rcases eq_bot_or_eq_of_isFaceOf_latticeCone_singleton hτ with rfl | rfl <;> simp [r0]
    · rcases eq_of_isFaceOf_latticeCone_pair hτ with rfl | rfl | rfl | rfl <;>
        simp [r1, r2, c12]
    · rcases eq_of_isFaceOf_latticeCone_pair hτ with rfl | rfl | rfl | rfl <;>
        simp [r2, r0, c20]
    · rcases eq_of_isFaceOf_latticeCone_pair hτ with rfl | rfl | rfl | rfl <;>
        simp [r0, r1, c01]
  inter_face σ hσ τ hτ := by
    rcases mem_cones.mp hσ with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases mem_cones.mp hτ with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [inf_idem, bot_inf_eq, inf_bot_eq, r1_inf_r2, r1_inf_r0, r2_inf_r0, r2_inf_r1,
        r0_inf_r1, r0_inf_r2, r1_inf_c20, r2_inf_c01, r0_inf_c12, c20_inf_r1, c01_inf_r2,
        c12_inf_r0, c12_inf_c20, c20_inf_c01, c01_inf_c12, c20_inf_c12, c01_inf_c20, c12_inf_c01,
        inf_of_le_left r1_le_c12, inf_of_le_right r1_le_c12, inf_of_le_left r2_le_c12,
        inf_of_le_right r2_le_c12, inf_of_le_left r2_le_c20, inf_of_le_right r2_le_c20,
        inf_of_le_left r0_le_c20, inf_of_le_right r0_le_c20, inf_of_le_left r0_le_c01,
        inf_of_le_right r0_le_c01, inf_of_le_left r1_le_c01, inf_of_le_right r1_le_c01] <;>
      first
      | exact PointedCone.IsFaceOf.refl _
      | exact bot_isFaceOf isStronglyConvex_r1
      | exact bot_isFaceOf isStronglyConvex_r2
      | exact bot_isFaceOf isStronglyConvex_r0
      | exact bot_isFaceOf isStronglyConvex_c12
      | exact bot_isFaceOf isStronglyConvex_c20
      | exact bot_isFaceOf isStronglyConvex_c01
      | exact r1_face_c12
      | exact r2_face_c12
      | exact r2_face_c20
      | exact r0_face_c20
      | exact r0_face_c01
      | exact r1_face_c01

/-- The cone `⊥` is a cone of the fan of `ℙ²`. -/
theorem bot_mem : (⊥ : PointedCone ℝ (NR 2)) ∈ fan.cones := Or.inl rfl
/-- The cone `r1` is a cone of the fan of `ℙ²`. -/
theorem r1_mem : r1 ∈ fan.cones := Or.inr (Or.inl rfl)
/-- The cone `r2` is a cone of the fan of `ℙ²`. -/
theorem r2_mem : r2 ∈ fan.cones := Or.inr (Or.inr (Or.inl rfl))
/-- The cone `r0` is a cone of the fan of `ℙ²`. -/
theorem r0_mem : r0 ∈ fan.cones := Or.inr (Or.inr (Or.inr (Or.inl rfl)))
/-- The cone `c12` is a cone of the fan of `ℙ²`. -/
theorem c12_mem : c12 ∈ fan.cones := Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
/-- The cone `c20` is a cone of the fan of `ℙ²`. -/
theorem c20_mem : c20 ∈ fan.cones := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
/-- The cone `c01` is a cone of the fan of `ℙ²`. -/
theorem c01_mem : c01 ∈ fan.cones := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))

/-- The fan of `ℙ²` is complete: each vector of `ℝ²` is in one of the three 2-cones. -/
theorem isComplete : fan.IsComplete := by
  refine Set.eq_univ_of_forall fun x => (fan.mem_support).mpr ?_
  rcases le_total 0 (x 0) with h0 | h0 <;> rcases le_total 0 (x 1) with h1 | h1
  · exact ⟨c12, c12_mem, mem_c12.mpr ⟨h0, h1⟩⟩
  · rcases le_total (x 1) (x 0) with h | h
    · exact ⟨c01, c01_mem, mem_c01.mpr ⟨h1, h⟩⟩
    · exact ⟨c12, c12_mem, mem_c12.mpr ⟨h0, by linarith⟩⟩
  · exact ⟨c20, c20_mem, mem_c20.mpr ⟨h0, by linarith⟩⟩
  · rcases le_total (x 0) (x 1) with h | h
    · exact ⟨c20, c20_mem, mem_c20.mpr ⟨h0, h⟩⟩
    · exact ⟨c01, c01_mem, mem_c01.mpr ⟨h1, h⟩⟩

/-- The cone of two lattice points with independent vectors is simplicial. -/
theorem isSimplicial_pair {a b : Fin 2 → ℤ} (hab : a ≠ b)
    (h : ∀ c d : ℝ, c • toNR a + d • toNR b = 0 → c = 0 ∧ d = 0) :
    IsSimplicial (latticeCone {a, b}) := by
  refine ⟨{a, b}, rfl, ?_⟩
  change LinearIndepOn ℝ toNR (({a, b} : Finset (Fin 2 → ℤ)) : Set (Fin 2 → ℤ))
  rw [Finset.coe_insert, Finset.coe_singleton, LinearIndepOn.pair_iff _ hab]
  exact h

/-- The fan of `ℙ²` is simplicial. -/
theorem isSimplicialFan : fan.IsSimplicialFan := by
  intro σ hσ
  rcases mem_cones.mp hσ with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact isSimplicial_bot
  · exact isSimplicial_latticeCone_singleton e1_ne_zero
  · exact isSimplicial_latticeCone_singleton e2_ne_zero
  · exact isSimplicial_latticeCone_singleton e0_ne_zero
  · refine isSimplicial_pair (fun h => by simpa using congrFun h 0) fun c d h => ?_
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp at h0 h1
    constructor <;> linarith
  · refine isSimplicial_pair (fun h => by simpa using congrFun h 1) fun c d h => ?_
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp at h0 h1
    constructor <;> linarith
  · refine isSimplicial_pair (fun h => by simpa using congrFun h 1) fun c d h => ?_
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp at h0 h1
    constructor <;> linarith

/-- A cone that contains two vectors that are not proportional is not a ray. -/
theorem not_isRay_of_mem {σ : PointedCone ℝ (NR 2)} {x y : NR 2} (hx : x ∈ σ) (hy : y ∈ σ)
    (hx0 : x ≠ 0) (hxy : ∀ a b : ℝ, a • x = b • y → a = 0 ∧ b = 0) : ¬ IsRay σ := by
  rintro ⟨v, -, rfl⟩
  obtain ⟨r, -, rfl⟩ := mem_latticeCone_singleton.mp hx
  obtain ⟨s, -, rfl⟩ := mem_latticeCone_singleton.mp hy
  obtain ⟨-, hr⟩ := hxy s r (by rw [smul_smul, smul_smul, mul_comm])
  exact hx0 (by rw [hr, zero_smul])

/-- The vector of `e1` lies in `c12`. -/
theorem toNR_e1_mem_c12 : toNR e1 ∈ c12 := toNR_mem_latticeCone (by simp)
/-- The vector of `e2` lies in `c12`. -/
theorem toNR_e2_mem_c12 : toNR e2 ∈ c12 := toNR_mem_latticeCone (by simp)
/-- The vector of `e2` lies in `c20`. -/
theorem toNR_e2_mem_c20 : toNR e2 ∈ c20 := toNR_mem_latticeCone (by simp)
/-- The vector of `e0` lies in `c20`. -/
theorem toNR_e0_mem_c20 : toNR e0 ∈ c20 := toNR_mem_latticeCone (by simp)
/-- The vector of `e0` lies in `c01`. -/
theorem toNR_e0_mem_c01 : toNR e0 ∈ c01 := toNR_mem_latticeCone (by simp)
/-- The vector of `e1` lies in `c01`. -/
theorem toNR_e1_mem_c01 : toNR e1 ∈ c01 := toNR_mem_latticeCone (by simp)

/-- The 2-cone `c12` is not a ray. -/
theorem not_isRay_c12 : ¬ IsRay c12 :=
  not_isRay_of_mem toNR_e1_mem_c12 toNR_e2_mem_c12 (toNR_ne_zero e1_ne_zero) fun a b h => by
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp at h0 h1
    constructor <;> linarith

/-- The 2-cone `c20` is not a ray. -/
theorem not_isRay_c20 : ¬ IsRay c20 :=
  not_isRay_of_mem toNR_e2_mem_c20 toNR_e0_mem_c20 (toNR_ne_zero e2_ne_zero) fun a b h => by
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp at h0 h1
    constructor <;> linarith

/-- The 2-cone `c01` is not a ray. -/
theorem not_isRay_c01 : ¬ IsRay c01 :=
  not_isRay_of_mem toNR_e0_mem_c01 toNR_e1_mem_c01 (toNR_ne_zero e0_ne_zero) fun a b h => by
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp at h0 h1
    constructor <;> linarith

/-- The cone `r1` is a ray. -/
theorem isRay_r1 : IsRay r1 := ⟨e1, e1_ne_zero, rfl⟩
/-- The cone `r2` is a ray. -/
theorem isRay_r2 : IsRay r2 := ⟨e2, e2_ne_zero, rfl⟩
/-- The cone `r0` is a ray. -/
theorem isRay_r0 : IsRay r0 := ⟨e0, e0_ne_zero, rfl⟩

/-- The rays of the fan of `ℙ²` are `r1`, `r2` and `r0`. -/
theorem rays_fan : fan.rays = {r1, r2, r0} := by
  ext ρ
  rw [Fan.mem_rays]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hρ, hr⟩
    rcases mem_cones.mp hρ with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hr.ne_bot
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
    · exact absurd hr not_isRay_c12
    · exact absurd hr not_isRay_c20
    · exact absurd hr not_isRay_c01
  · rintro (rfl | rfl | rfl)
    · exact ⟨r1_mem, isRay_r1⟩
    · exact ⟨r2_mem, isRay_r2⟩
    · exact ⟨r0_mem, isRay_r0⟩

/-- The vector of `e1` lies in `r1`. -/
theorem toNR_e1_mem_r1 : toNR e1 ∈ r1 := toNR_mem_latticeCone (Finset.mem_singleton_self _)
/-- The vector of `e2` lies in `r2`. -/
theorem toNR_e2_mem_r2 : toNR e2 ∈ r2 := toNR_mem_latticeCone (Finset.mem_singleton_self _)
/-- The vector of `e0` lies in `r0`. -/
theorem toNR_e0_mem_r0 : toNR e0 ∈ r0 := toNR_mem_latticeCone (Finset.mem_singleton_self _)

/-- The rays `r1` and `r2` are different. -/
theorem r1_ne_r2 : r1 ≠ r2 := fun h => by
  have h' : toNR e1 ∈ r2 := h ▸ toNR_e1_mem_r1
  have := mem_r2.mp h'
  simp at this
/-- The rays `r1` and `r0` are different. -/
theorem r1_ne_r0 : r1 ≠ r0 := fun h => by
  have h' : toNR e1 ∈ r0 := h ▸ toNR_e1_mem_r1
  have := mem_r0.mp h'
  simp at this
/-- The rays `r2` and `r0` are different. -/
theorem r2_ne_r0 : r2 ≠ r0 := fun h => by
  have h' : toNR e2 ∈ r0 := h ▸ toNR_e2_mem_r2
  have := mem_r0.mp h'
  simp at this

/-- The fan of `ℙ²` has three rays. -/
theorem card_ray : Nat.card fan.Ray = 3 := by
  show Nat.card ↥fan.rays = 3
  rw [rays_fan, Nat.card_coe_set_eq]
  exact Set.ncard_eq_three.mpr ⟨r1, r2, r0, r1_ne_r2, r1_ne_r0, r2_ne_r0, rfl⟩

/-- The sum of the coefficients of the canonical divisor of `ℙ²` is `-3`. -/
theorem coeffSum_canonical : fan.coeffSum fan.canonical = -3 := by
  rw [Fan.coeffSum_canonical, card_ray]
  norm_num

/-- The primitive generator of `r1` is `e₁`. -/
theorem rayGenerator_r1 : rayGenerator r1 = e1 := rayGenerator_latticeCone isPrimitive_e1

/-- The primitive generator of `r2` is `e₂`. -/
theorem rayGenerator_r2 : rayGenerator r2 = e2 := rayGenerator_latticeCone isPrimitive_e2

/-- The primitive generator of `r0` is `e₀`. -/
theorem rayGenerator_r0 : rayGenerator r0 = e0 := rayGenerator_latticeCone isPrimitive_e0

/-- The wall relation of the fan of `ℙ²`: `u₁ + u₂ + u₀ = 0` for the primitive generators. Each pair of adjacent 2-cones, for example `c12` and `c20` with the wall `r2 = c12 ⊓ c20`, has this relation, with the coefficient `1` at the generator of the wall (Cox, Little and Schenck, Section 6.4). -/
theorem wall_relation : rayGenerator r1 + rayGenerator r2 + rayGenerator r0 = 0 := by
  rw [rayGenerator_r1, rayGenerator_r2, rayGenerator_r0]
  funext i
  fin_cases i <;> rfl

/-- Each ray of the fan of `ℙ²` is `r1`, `r2` or `r0`. -/
theorem ray_cases (ρ : fan.Ray) : ρ.1 = r1 ∨ ρ.1 = r2 ∨ ρ.1 = r0 := by
  have h : ρ.1 ∈ ({r1, r2, r0} : Set (PointedCone ℝ (NR 2))) :=
    (Set.ext_iff.mp rays_fan ρ.1).mp ρ.2
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h

/-- The ray `r0` is not in the cone `c12`. -/
theorem not_r0_le_c12 : ¬ r0 ≤ c12 := fun h => by
  have := mem_c12.mp (h toNR_e0_mem_r0)
  norm_num at this
/-- The ray `r1` is not in the cone `c20`. -/
theorem not_r1_le_c20 : ¬ r1 ≤ c20 := fun h => by
  have := mem_c20.mp (h toNR_e1_mem_r1)
  norm_num at this
/-- The ray `r2` is not in the cone `c01`. -/
theorem not_r2_le_c01 : ¬ r2 ≤ c01 := fun h => by
  have := mem_c01.mp (h toNR_e2_mem_r2)
  norm_num at this

/-- The data `m_σ` of the canonical divisor on a cone `σ ≤ σ'`. -/
theorem cartier_aux {σ σ' : PointedCone ℝ (NR 2)} (h : σ ≤ σ') (m : Fin 2 → ℤ)
    (hm : ∀ ρ : fan.Ray, ρ.1 ≤ σ' → ∑ i, m i * fan.generator ρ i = 1) :
    ∃ m : Fin 2 → ℤ, ∀ ρ : fan.Ray, ρ.1 ≤ σ → ∑ i, m i * fan.generator ρ i = -fan.canonical ρ :=
  ⟨m, fun ρ hρ => by rw [Fan.canonical_apply, neg_neg]; exact hm ρ (hρ.trans h)⟩

/-- The data `m_σ` of the canonical divisor on the cone `c12`. -/
theorem cartier_c12 (ρ : fan.Ray) (hρ : ρ.1 ≤ c12) :
    ∑ i, (![1, 1] : Fin 2 → ℤ) i * fan.generator ρ i = 1 := by
  rcases ray_cases ρ with h | h | h <;> rw [h] at hρ
  · rw [Fan.generator, h, rayGenerator_r1]; simp [Fin.sum_univ_two]
  · rw [Fan.generator, h, rayGenerator_r2]; simp [Fin.sum_univ_two]
  · exact absurd hρ not_r0_le_c12

/-- The data `m_σ` of the canonical divisor on the cone `c20`. -/
theorem cartier_c20 (ρ : fan.Ray) (hρ : ρ.1 ≤ c20) :
    ∑ i, (![-2, 1] : Fin 2 → ℤ) i * fan.generator ρ i = 1 := by
  rcases ray_cases ρ with h | h | h <;> rw [h] at hρ
  · exact absurd hρ not_r1_le_c20
  · rw [Fan.generator, h, rayGenerator_r2]; simp [Fin.sum_univ_two]
  · rw [Fan.generator, h, rayGenerator_r0]; simp [Fin.sum_univ_two]

/-- The data `m_σ` of the canonical divisor on the cone `c01`. -/
theorem cartier_c01 (ρ : fan.Ray) (hρ : ρ.1 ≤ c01) :
    ∑ i, (![1, -2] : Fin 2 → ℤ) i * fan.generator ρ i = 1 := by
  rcases ray_cases ρ with h | h | h <;> rw [h] at hρ
  · rw [Fan.generator, h, rayGenerator_r1]; simp [Fin.sum_univ_two]
  · exact absurd hρ not_r2_le_c01
  · rw [Fan.generator, h, rayGenerator_r0]; simp [Fin.sum_univ_two]

/-- The canonical divisor of `ℙ²` is Cartier, with `m_σ = (1, 1)`, `(-2, 1)` and `(1, -2)` on the three 2-cones. -/
theorem isCartier_canonical : fan.IsCartier fan.canonical := by
  intro σ hσ
  rcases mem_cones.mp hσ with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact cartier_aux bot_le _ cartier_c12
  · exact cartier_aux r1_le_c12 _ cartier_c12
  · exact cartier_aux r2_le_c12 _ cartier_c12
  · exact cartier_aux r0_le_c20 _ cartier_c20
  · exact cartier_aux le_rfl _ cartier_c12
  · exact cartier_aux le_rfl _ cartier_c20
  · exact cartier_aux le_rfl _ cartier_c01

/-- The canonical divisor of `ℙ²` is Q-Cartier. -/
theorem isQCartier_canonical : fan.IsQCartier fan.canonical :=
  isCartier_canonical.isQCartier

/-- The canonical divisor of `ℙ²` has a support function (Cox, Little and Schenck, Theorem 4.2.12). -/
theorem exists_isSupportFunctionOf_canonical :
    ∃ φ : NR 2 → ℝ, fan.IsSupportFunctionOf (Fan.TDivisor.toReal fan fan.canonical) φ :=
  isQCartier_canonical.isRCartier.exists_isSupportFunctionOf

/-- The image of the family `a, b` indexed by `Option Unit` is the set `{a, b}`. -/
theorem range_elim' (a b : Fin 2 → ℤ) :
    (Set.range fun o : Option Unit => toNR (Option.elim' a (fun _ => b) o)) =
      toNR '' ((({a, b} : Finset (Fin 2 → ℤ))) : Set (Fin 2 → ℤ)) := by
  ext x
  constructor
  · rintro ⟨o, rfl⟩
    cases o with
    | none => exact ⟨a, by simp, rfl⟩
    | some _ => exact ⟨b, by simp, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    rw [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact ⟨none, rfl⟩
    · exact ⟨some (), rfl⟩

/-- The cone `c12` is the cone of the family `e₁, e₂`. -/
theorem familyCone_e1_e2 : familyCone (Option.elim' e1 fun _ : Unit => e2) = c12 := by
  rw [familyCone, c12, latticeCone, range_elim']

/-- The cone `c20` is the cone of the family `e₀, e₂`. -/
theorem familyCone_e0_e2 : familyCone (Option.elim' e0 fun _ : Unit => e2) = c20 := by
  rw [familyCone, c20, latticeCone, range_elim', Finset.pair_comm]

/-- The points `e₁, e₂` are a basis of the lattice `ℤ²`. -/
theorem isLatticeBasis_e1_e2 : IsLatticeBasis (Option.elim' e1 fun _ : Unit => e2) := by
  constructor
  · rw [Fintype.linearIndependent_iff]
    intro g hg o
    rw [Fintype.sum_option] at hg
    have h0 := congrFun hg 0
    have h1 := congrFun hg 1
    simp [e1, e2] at h0 h1
    rcases o with _ | ⟨⟩
    · exact h0
    · exact h1
  · rw [Submodule.top_le_span_range_iff_forall_exists_fun]
    intro x
    refine ⟨Option.elim' (x 0) fun _ => x 1, ?_⟩
    rw [Fintype.sum_option]
    funext j
    fin_cases j <;> simp [e1, e2]

/-- The points `e₀, e₂` are a basis of the lattice `ℤ²`. -/
theorem isLatticeBasis_e0_e2 : IsLatticeBasis (Option.elim' e0 fun _ : Unit => e2) := by
  constructor
  · rw [Fintype.linearIndependent_iff]
    intro g hg o
    rw [Fintype.sum_option] at hg
    have h0 := congrFun hg 0
    have h1 := congrFun hg 1
    simp [e0, e2] at h0 h1
    rcases o with _ | ⟨⟩
    · exact h0
    · simpa [h0] using h1
  · rw [Submodule.top_le_span_range_iff_forall_exists_fun]
    intro x
    refine ⟨Option.elim' (-x 0) fun _ => x 1 - x 0, ?_⟩
    rw [Fintype.sum_option]
    funext j
    fin_cases j <;> simp [e0, e2]

/-- The points `e₁` and `e₀` are different. -/
theorem e1_ne_e0 : e1 ≠ e0 := fun h => by simpa using congrFun h 0

/-- The wall relation of `Fan.exists_unique_wall_relation` for the adjacent cones `c12` and `c20` of the fan of `ℙ²`, with the wall `r2`. There is a unique `b` with `e₁ + e₀ = b • e₂`, and it is `-1`. This shows that the hypotheses of the wall relation can hold. -/
theorem existsUnique_wall_c12_c20 : ∃! b : Unit → ℤ, e1 + e0 = ∑ i, b i • e2 :=
  fan.exists_unique_wall_relation isLatticeBasis_e1_e2 isLatticeBasis_e0_e2
    (by rw [familyCone_e1_e2]; exact c12_mem) (by rw [familyCone_e0_e2]; exact c20_mem) e1_ne_e0

/-- The coefficient of the wall relation of `c12` and `c20` is `-1`: `e₁ + e₀ = -e₂`. -/
theorem wall_c12_c20 : e1 + e0 = ∑ _i : Unit, (-1 : ℤ) • e2 := by
  funext j
  fin_cases j <;> simp [e1, e2, e0]

end MinimalModel.Toric.P2
