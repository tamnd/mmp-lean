/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import MinimalModel.Toric.ConeTheorem
import MinimalModel.Toric.Examples

/-!
# Fidelity checks F2 and F3 for the toric cone theorem

This file gives checks F2 and F3 of spec 06.3 for the pinned statement `ToricConeTheorem` of `MinimalModel/Statements/Toric.lean`. It uses the fan of `ℙ²` of `MinimalModel/Toric/Examples.lean`.

The file shows that the cones `c12` and `c20` of `ℙ²` are a wall pair. They are maximal, they are different, and they meet in the ray `r2`, a cone of dimension one.

* F2: the statement, applied to `ℙ²`, gives that the anticanonical divisor `-K` has degree `0` or more on the wall between `c12` and `c20`. The degree is `3` (`degree_neg_canonical`).
* F3: the statement shows that the canonical divisor `K` of `ℙ²` is not nef. Its degree on the wall is `-3`. So the statement does not make every divisor nef.
* F3: two wrong variants of the statement are false. In the first, the degree is `0` or less on each wall. The divisor `-K` of `ℙ²` is a counterexample. In the second, the degree is more than `0` on each wall. The zero divisor of `ℙ²` is a counterexample.
-/

namespace MinimalModel.Toric

/-- A wrong variant of `ToricConeTheorem`: the degree is `0` or less on each wall. -/
def ToricConeTheoremNonpos : Prop :=
  ∀ (n : ℕ) (F : Fan n), F.IsComplete → F.IsSimplicialFan → ∀ D : F.TDivisor ℝ, F.IsRCartier D →
    (F.IsNef D ↔ ∀ σ σ' : PointedCone ℝ (NR n), F.IsWallPair σ σ' →
      ∀ W : F.WallData σ σ', W.degree D ≤ 0)

/-- A wrong variant of `ToricConeTheorem`: the degree is more than `0` on each wall. -/
def ToricConeTheoremPos : Prop :=
  ∀ (n : ℕ) (F : Fan n), F.IsComplete → F.IsSimplicialFan → ∀ D : F.TDivisor ℝ, F.IsRCartier D →
    (F.IsNef D ↔ ∀ σ σ' : PointedCone ℝ (NR n), F.IsWallPair σ σ' →
      ∀ W : F.WallData σ σ', 0 < W.degree D)

namespace P2

/-! ### The wall pair `c12`, `c20` of `ℙ²` -/

/-- The cone `c12` is a cone of the fan of `ℙ²`. -/
theorem c12_mem_cones : c12 ∈ fan.cones :=
  mem_cones.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))

/-- The cone `c20` is a cone of the fan of `ℙ²`. -/
theorem c20_mem_cones : c20 ∈ fan.cones :=
  mem_cones.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))

/-- The point `(1, 1)` is in `c12`. -/
theorem one_one_mem_c12 : (![1, 1] : NR 2) ∈ c12 :=
  mem_c12.mpr (by simp)

/-- The point `(-1, 1)` is in `c20`. -/
theorem neg_one_one_mem_c20 : (![-1, 1] : NR 2) ∈ c20 :=
  mem_c20.mpr (by norm_num)

/-- The only cone of `ℙ²` that has the point `(1, 1)` is `c12`. -/
theorem eq_c12_of_mem {σ : PointedCone ℝ (NR 2)} (hσ : σ ∈ fan.cones)
    (h : (![1, 1] : NR 2) ∈ σ) : σ = c12 := by
  rcases mem_cones.mp hσ with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have h0 := congrFun ((Submodule.mem_bot _).mp h) 0
    simp at h0
  · have := (mem_r1.mp h).2
    simp at this
  · have := (mem_r2.mp h).1
    simp at this
  · have := (mem_r0.mp h).1
    norm_num at this
  · rfl
  · have := (mem_c20.mp h).1
    norm_num at this
  · have := (mem_c01.mp h).1
    norm_num at this

/-- The only cone of `ℙ²` that has the point `(-1, 1)` is `c20`. -/
theorem eq_c20_of_mem {σ : PointedCone ℝ (NR 2)} (hσ : σ ∈ fan.cones)
    (h : (![-1, 1] : NR 2) ∈ σ) : σ = c20 := by
  rcases mem_cones.mp hσ with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have h0 := congrFun ((Submodule.mem_bot _).mp h) 0
    simp at h0
  · have := (mem_r1.mp h).2
    simp at this
  · have := (mem_r2.mp h).1
    simp at this
  · have := (mem_r0.mp h).2
    norm_num at this
  · have := (mem_c12.mp h).1
    norm_num at this
  · rfl
  · have := (mem_c01.mp h).1
    norm_num at this

/-- The cone `c12` is a maximal cone of `ℙ²`. -/
theorem isMaximalCone_c12 : fan.IsMaximalCone c12 :=
  ⟨c12_mem_cones, fun _ hσ hle => (eq_c12_of_mem hσ (hle one_one_mem_c12)).le⟩

/-- The cone `c20` is a maximal cone of `ℙ²`. -/
theorem isMaximalCone_c20 : fan.IsMaximalCone c20 :=
  ⟨c20_mem_cones, fun _ hσ hle => (eq_c20_of_mem hσ (hle neg_one_one_mem_c20)).le⟩

/-- The cones `c12` and `c20` are different: the point `(1, 1)` is in `c12` and not in `c20`. -/
theorem c12_ne_c20 : c12 ≠ c20 := fun h => by
  have := (mem_c20.mp (h ▸ one_one_mem_c12)).1
  norm_num at this

/-- The cones `c12` and `c20` meet in the ray `r2`. -/
theorem c12_inf_c20 : c12 ⊓ c20 = r2 := by
  ext x
  rw [Submodule.mem_inf, mem_c12, mem_c20, mem_r2]
  constructor
  · rintro ⟨⟨h0, h1⟩, h2, -⟩
    exact ⟨le_antisymm h2 h0, h1⟩
  · rintro ⟨h0, h1⟩
    exact ⟨⟨h0.ge, h1⟩, h0.le, by linarith⟩

/-- The vector `e₂` is not zero in `ℝ²`. -/
theorem toNR_e2_ne_zero : toNR e2 ≠ 0 := fun h => by
  have := congrFun h 1
  simp [toNR_apply, e2_one] at this

/-- The real span of the ray `r2` is the line of `e₂`. -/
theorem span_r2 : Submodule.span ℝ (r2 : Set (NR 2)) = ℝ ∙ toNR e2 := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx
    obtain ⟨h0, -⟩ := mem_r2.mp hx
    rw [SetLike.mem_coe, Submodule.mem_span_singleton]
    exact ⟨x 1, ext (by simp [toNR_apply, e2_zero, h0]) (by simp [toNR_apply, e2_one])⟩
  · rw [Submodule.span_singleton_le_iff_mem]
    exact Submodule.subset_span (mem_r2.mpr (by simp [toNR_apply, e2_zero, e2_one]))

/-- The ray `r2` has dimension one. -/
theorem coneDim_r2 : coneDim r2 = 1 := by
  rw [coneDim, span_r2, finrank_span_singleton toNR_e2_ne_zero]

/-- The cones `c12` and `c20` of `ℙ²` are a wall pair. -/
theorem isWallPair_c12_c20 : fan.IsWallPair c12 c20 :=
  ⟨isMaximalCone_c12, isMaximalCone_c20, c12_ne_c20, by rw [c12_inf_c20, coneDim_r2]⟩

/-! ### The checks -/

/-- The anticanonical divisor `-K` of `ℙ²` is R-Cartier. -/
theorem isRCartier_neg_canonical : fan.IsRCartier (-fan.canonicalReal) :=
  let ⟨_, hφ, _⟩ := isNef_neg_canonical
  hφ.isRCartier

/-- The canonical divisor `K` of `ℙ²` is R-Cartier. -/
theorem isRCartier_canonical : fan.IsRCartier fan.canonicalReal :=
  isQCartier_canonical.isRCartier

/-- The zero divisor of `ℙ²` is nef, with the support function `0`. -/
theorem isNef_zero : fan.IsNef 0 :=
  ⟨0, ⟨fun _ _ => ⟨0, fun _ _ => rfl⟩, fun _ => by simp⟩, concaveOn_const 0 convex_univ⟩

/-- The zero divisor of `ℙ²` is R-Cartier. -/
theorem isRCartier_zero : fan.IsRCartier 0 :=
  let ⟨_, hφ, _⟩ := isNef_zero
  hφ.isRCartier

/-- F2: by `ToricConeTheorem`, the nef divisor `-K` of `ℙ²` has degree `0` or more on the wall between `c12` and `c20`. -/
theorem degree_neg_canonical_nonneg_of_toricConeTheorem (h : ToricConeTheorem) :
    0 ≤ wallData_c12_c20.degree (-fan.canonicalReal) :=
  (h 2 fan isComplete isSimplicialFan _ isRCartier_neg_canonical).mp isNef_neg_canonical
    c12 c20 isWallPair_c12_c20 wallData_c12_c20

/-- F3: by `ToricConeTheorem`, the canonical divisor `K` of `ℙ²` is not nef. Its degree on the wall between `c12` and `c20` is `-3`. -/
theorem not_isNef_canonical_of_toricConeTheorem (h : ToricConeTheorem) :
    ¬ fan.IsNef fan.canonicalReal := fun hK => by
  have := (h 2 fan isComplete isSimplicialFan _ isRCartier_canonical).mp hK
    c12 c20 isWallPair_c12_c20 wallData_c12_c20
  rw [degree_c12_c20] at this
  simp only [Fan.canonicalReal_apply] at this
  norm_num at this

/-- F3: the canonical divisor `K` of `ℙ²` is not nef. -/
theorem not_isNef_canonical : ¬ fan.IsNef fan.canonicalReal :=
  not_isNef_canonical_of_toricConeTheorem toricConeTheorem

/-- F3: the variant `ToricConeTheoremNonpos` is false. The divisor `-K` of `ℙ²` is nef and has degree `3` on a wall. -/
theorem not_toricConeTheoremNonpos : ¬ ToricConeTheoremNonpos := fun h => by
  have := (h 2 fan isComplete isSimplicialFan _ isRCartier_neg_canonical).mp isNef_neg_canonical
    c12 c20 isWallPair_c12_c20 wallData_c12_c20
  rw [degree_neg_canonical.1] at this
  norm_num at this

/-- F3: the variant `ToricConeTheoremPos` is false. The zero divisor of `ℙ²` is nef and has degree `0` on each wall. -/
theorem not_toricConeTheoremPos : ¬ ToricConeTheoremPos := fun h => by
  have := (h 2 fan isComplete isSimplicialFan _ isRCartier_zero).mp isNef_zero
    c12 c20 isWallPair_c12_c20 wallData_c12_c20
  rw [degree_c12_c20] at this
  simp at this

end P2

end MinimalModel.Toric
