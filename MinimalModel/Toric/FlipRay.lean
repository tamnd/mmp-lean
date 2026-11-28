/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import MinimalModel.Toric.FlipFan

/-!
# Toric flips, part 3: the walls of an extremal ray

This file starts step 3 of the route to `flipExists` in `MinimalModel/Toric/Flip.lean` (route R3, spec 04.4): the walls whose curves span an extremal ray of the cone of curves (Reid 1983, Section 2 and Corollary 2.5; Matsuki, Section 14-1; Cox, Little and Schenck, Section 6.4 and Proposition 15.4.3).

## The class of a wall curve

Let `F` be a complete simplicial fan. Each divisor of `F` is `ℝ`-Cartier, so the numerical class of a curve is the linear form `D ↦ D · C` on the space `F.TDivisor ℝ = ℝ^{Σ(1)}` of all torus-invariant divisors. This form vanishes on the principal divisors, so it is a linear relation among the generators `u_ρ` of the rays (Cox, Little and Schenck, Proposition 6.4.1). For the curve `V(τ)` of a wall `τ = σ ∩ σ'`, the relation is the wall relation `Σ aᵢ uᵢ = 0` of the circuit of the wall (`Fan.WallData.circuit`), read as a vector of `ℝ^{Σ(1)}`. This is `Fan.WallData.curveClass`: the coefficient `aᵢ` at the ray of the index `i` of the circuit, and zero at the other rays. It is a relation among all the generators (`Fan.WallData.sum_curveClass_smul_generator`), and the degree of `D` on the wall is `Σ_ρ [V(τ)]_ρ D(ρ)` (`Fan.WallData.degree_eq_sum_curveClass`). The class is read off the degrees: its value at a ray `ρ` is the degree of the prime divisor `D_ρ` (`Fan.WallData.degree_single`).

The cone of curves `Fan.curveCone` is the cone in `ℝ^{Σ(1)}` spanned by the classes of the wall curves; by the toric cone theorem it is the cone of curves `NE(X)` of the toric variety (Cox, Little and Schenck, Theorem 6.3.20). An extremal ray (`Fan.IsExtremalRay`) is a face of this cone spanned by one nonzero vector.

## The walls of a ray

Two walls whose curves lie in the same ray `R` have proportional classes, with a positive factor (`Fan.IsExtremalRay.isProportional`, `Fan.WallData.isProportional_of_mem_hull`). So the wall relations agree up to a positive scalar: the rays of `J₊` are the same for the two circuits, and so are the rays of `J₋` (`Fan.WallData.IsProportional.image_jPlus`, `Fan.WallData.IsProportional.image_jMinus`). An index of one circuit whose ray is not a ray of the other circuit is in `J₀` (`Fan.WallData.IsProportional.circuitCoeff_eq_zero`), and the other coefficients are proportional (`Fan.WallData.IsProportional.circuitCoeff_eq`). This is the first half of Reid, Corollary 2.5: the sets `J₊` and `J₋`, and the relation on `J₊ ∪ J₋`, depend only on the ray `R`, not on the wall; the walls differ in their indices of `J₀`.

The cone `cone(u_{J₋})` of the rays with a negative coefficient (`Fan.negCone`) lies in both maximal cones of each wall of the ray (`Fan.WallData.negCone_curveClass_le_inf`, `Fan.WallData.IsProportional.negCone_le_inf`). The reason is that a ray of `σ` with a coefficient `c_ρ ≥ 0` in the relation `u_ρ' = Σ c_ρ u_ρ` is in `σ'`: only one ray of `σ` is not in `σ'` (`Fan.IsWallPair.eq_of_not_le`), and it has `c_ρ < 0` (`Fan.WallData.exists_coeffIn_neg`). So the closed subvariety `V(cone(u_{J₋}))` contains each curve of `R`: it is the exceptional locus of the contraction of `R`.

## Main definitions

* `Fan.WallData.curveClass`: the class of the curve of a wall, the wall relation as a vector of `ℝ^{Σ(1)}`.
* `Fan.curveCone`: the cone spanned by the classes of the wall curves.
* `Fan.IsExtremalRay`: a face of the cone of curves spanned by one nonzero vector.
* `Fan.WallData.IsProportional`: the degrees of the divisors on two walls are proportional, with a positive factor.
* `Fan.negCone`: the cone of the generators of the rays with a negative coefficient in a class.

## Main results

* `Fan.IsWallPair.eq_of_not_le`: at most one ray of a simplicial maximal cone of a wall pair is not in the other cone.
* `Fan.WallData.degree_eq_sum_curveClass`, `Fan.WallData.degree_single`: the degree on a wall is the pairing with its class, and the class is the degree on the prime divisors.
* `Fan.WallData.isProportional_iff`: the degrees on two walls are proportional exactly when the classes are.
* `Fan.IsExtremalRay.isProportional`: two walls of an extremal ray have proportional classes.
* `Fan.WallData.IsProportional.image_jPlus`, `Fan.WallData.IsProportional.image_jMinus`, `Fan.WallData.IsProportional.circuitCoeff_eq`: the circuits of two walls of a ray have the same rays in `J₊` and in `J₋`, with proportional coefficients.
* `Fan.WallData.IsProportional.negCone_le_inf`: the cone of `J₋` lies in the two maximal cones of each wall of the ray.
-/

namespace MinimalModel.Toric

variable {n : ℕ}

namespace Fan

variable {F : Fan n}

/-- Let `σ` and `σ'` be two maximal cones of a fan that meet in a wall, with `σ` simplicial. Then at most one ray of the fan in `σ` is not in `σ'`. The cone `σ` is spanned by at most `n` independent lattice points, and the face `σ ∩ σ'` of dimension `n - 1` is spanned by a subset of them, so at most one of the points is not in `σ'`. -/
theorem IsWallPair.eq_of_not_le {σ σ' : PointedCone ℝ (NR n)} (hs : IsSimplicial σ)
    (hw : F.IsWallPair σ σ') {ρ₁ ρ₂ : F.Ray} (h₁ : ρ₁.1 ≤ σ) (h₁' : ¬ ρ₁.1 ≤ σ')
    (h₂ : ρ₂.1 ≤ σ) (h₂' : ¬ ρ₂.1 ≤ σ') : ρ₁ = ρ₂ := by
  classical
  obtain ⟨hmax, hmax', -, hdim⟩ := hw
  have hσ := hmax.mem
  have hσ' := hmax'.mem
  obtain ⟨S, rfl, hS⟩ := hs
  obtain ⟨T, hTS, hT⟩ := exists_subset_of_isFaceOf_latticeCone (F.inter_face _ hσ _ hσ')
  have hTcard : n ≤ T.card + 1 := by
    have := coneDim_latticeCone_le T
    rw [← hT] at this
    omega
  have hScard : S.card ≤ n := by
    have := hS.fintype_card_le_finrank
    simpa [Module.finrank_fin_fun] using this
  have hwit : ∀ ρ : F.Ray, ρ.1 ≤ latticeCone S → ¬ ρ.1 ≤ σ' →
      ∃ w ∈ S, w ∉ T ∧ toNR w ∈ ρ.1 := by
    intro ρ hρ hρσ
    obtain ⟨Tρ, hTρ, hρeq⟩ :=
      exists_subset_of_isFaceOf_latticeCone (F.isFaceOf_of_le hσ ρ hρ)
    by_contra hno
    push Not at hno
    apply hρσ
    have hsub : Tρ ⊆ T := fun w hw => by
      by_contra hwT
      exact hno w (hTρ hw) hwT (by rw [hρeq]; exact toNR_mem_latticeCone hw)
    calc ρ.1 = latticeCone Tρ := hρeq
      _ ≤ latticeCone T := Submodule.span_mono (Set.image_mono (Finset.coe_subset.mpr hsub))
      _ = latticeCone S ⊓ σ' := hT.symm
      _ ≤ σ' := inf_le_right
  obtain ⟨w₁, hw₁, hw₁T, hw₁ρ⟩ := hwit ρ₁ h₁ h₁'
  obtain ⟨w₂, hw₂, hw₂T, hw₂ρ⟩ := hwit ρ₂ h₂ h₂'
  by_cases h12 : w₁ = w₂
  · subst h12
    exact ray_eq_of_mem hw₁ρ hw₂ρ (hS.ne_zero ⟨w₁, Finset.mem_coe.mpr hw₁⟩)
  · exfalso
    have hsub : insert w₁ (insert w₂ T) ⊆ S :=
      Finset.insert_subset hw₁ (Finset.insert_subset hw₂ hTS)
    have := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem (by simp [h12, hw₁T]),
      Finset.card_insert_of_notMem hw₂T] at this
    omega

/-- The cone spanned by the generators of the rays `ρ` with `c ρ < 0`. For the class `c` of a wall curve this is the cone `cone(u_{J₋})` of the circuit of the wall, and `V(cone(u_{J₋}))` is the locus of the curves of the ray of `c`. -/
noncomputable def negCone (F : Fan n) (c : F.Ray → ℝ) : PointedCone ℝ (NR n) :=
  PointedCone.hull ℝ {x | ∃ ρ : F.Ray, c ρ < 0 ∧ toNR (F.generator ρ) = x}

/-- The cone of the negative rays of a class does not change when the class is multiplied by a positive scalar. -/
theorem negCone_smul (c : F.Ray → ℝ) {t : ℝ} (ht : 0 < t) : F.negCone (t • c) = F.negCone c := by
  have h : ∀ ρ : F.Ray, (t • c) ρ < 0 ↔ c ρ < 0 := fun ρ => by
    rw [Pi.smul_apply, smul_eq_mul]
    constructor
    · intro h
      by_contra h'
      have := mul_nonneg ht.le (not_lt.mp h')
      linarith
    · exact mul_neg_of_pos_of_neg ht
  unfold negCone
  simp only [h]

namespace WallData

variable {σ σ' : PointedCone ℝ (NR n)} (W : F.WallData σ σ')

/-! ### The class of the curve of a wall -/

/-- The rays of the circuit of a wall are different from each other: the ray `ρ'` is not in `σ`, and the other indices are rays of `σ`. -/
theorem circuitRay_injective : Function.Injective W.circuitRay := by
  rintro (_ | ρ₁) (_ | ρ₂) h
  · rfl
  · simp only [circuitRay_none, circuitRay_some] at h
    exfalso
    apply W.ray_not_le
    rw [h]
    exact ρ₂.2
  · simp only [circuitRay_none, circuitRay_some] at h
    exfalso
    apply W.ray_not_le
    rw [← h]
    exact ρ₁.2
  · simp only [circuitRay_some] at h
    exact congrArg some (Subtype.ext h)

/-- The class of the curve of the wall, as a vector of `ℝ^{Σ(1)}`: the coefficient `aᵢ` of the wall relation `Σ aᵢ uᵢ = 0` at the ray of the index `i` of the circuit, and zero at the other rays of the fan. It is a linear relation among the generators of all the rays (`sum_curveClass_smul_generator`), and its pairing with a divisor is the degree of the divisor on the wall (`degree_eq_sum_curveClass`). -/
noncomputable def curveClass : F.Ray → ℝ :=
  Function.extend W.circuitRay W.circuitCoeff 0

/-- The class at the ray of an index of the circuit is the coefficient of the index. -/
theorem curveClass_circuitRay (i : Option {ρ : F.Ray // ρ.1 ≤ σ}) :
    W.curveClass (W.circuitRay i) = W.circuitCoeff i :=
  W.circuitRay_injective.extend_apply _ _ _

/-- The class vanishes at a ray that is not a ray of the circuit. -/
theorem curveClass_eq_zero {ρ : F.Ray} (h : ∀ i, W.circuitRay i ≠ ρ) : W.curveClass ρ = 0 := by
  rw [curveClass, Function.extend_apply' _ _ _ fun ⟨i, hi⟩ => h i hi]
  rfl

/-- The class at the ray `ρ'` of `σ'` that is not in `σ` is `1`. -/
theorem curveClass_ray : W.curveClass W.ray = 1 :=
  W.curveClass_circuitRay none

/-- The class of the curve of a wall is not zero. -/
theorem curveClass_ne_zero : W.curveClass ≠ 0 := fun h => by
  have h1 := congrFun h W.ray
  rw [curveClass_ray, Pi.zero_apply] at h1
  exact one_ne_zero h1

/-- The pairing of the class with a family of vectors indexed by the rays is the sum over the circuit. -/
theorem sum_curveClass_smul {M : Type*} [AddCommMonoid M] [Module ℝ M] (g : F.Ray → M) :
    ∑ ρ, W.curveClass ρ • g ρ = ∑ i, W.circuitCoeff i • g (W.circuitRay i) := by
  classical
  have hz : ∀ ρ ∈ (Finset.univ : Finset F.Ray), ρ ∉ Finset.univ.image W.circuitRay →
      W.curveClass ρ • g ρ = 0 := by
    intro ρ _ hρ
    have hρ' : ∀ i, W.circuitRay i ≠ ρ := fun i hi => hρ (by
      rw [← hi]
      exact Finset.mem_image_of_mem _ (Finset.mem_univ i))
    rw [W.curveClass_eq_zero hρ', zero_smul]
  rw [← Finset.sum_subset (Finset.subset_univ _) hz,
    Finset.sum_image W.circuitRay_injective.injOn]
  exact Finset.sum_congr rfl fun i _ => by simp only [W.curveClass_circuitRay]

/-- The class of the curve of a wall is a linear relation among the generators of the rays of the fan. -/
theorem sum_curveClass_smul_generator (hσ : σ ∈ F.cones) (hs : IsSimplicial σ) :
    ∑ ρ, W.curveClass ρ • toNR (F.generator ρ) = 0 := by
  rw [W.sum_curveClass_smul]
  exact (W.isCircuit hσ hs).1

/-- The degree of a divisor on the wall is the pairing of the divisor with the class of the curve of the wall. -/
theorem degree_eq_sum_curveClass (D : F.TDivisor ℝ) :
    W.degree D = ∑ ρ, W.curveClass ρ * D ρ := by
  have h := W.sum_curveClass_smul fun ρ => D ρ
  simp only [smul_eq_mul] at h
  rw [h, W.degree_eq_sum]

/-- The degree of the prime divisor `D_ρ` on the wall is the class of the curve of the wall at `ρ`. So the class is determined by the degrees of the divisors. -/
theorem degree_single (ρ : F.Ray) : W.degree (Finsupp.single ρ 1) = W.curveClass ρ := by
  rw [degree_eq_sum_curveClass, Finset.sum_eq_single ρ
    (fun b _ hb => by rw [Finsupp.single_eq_of_ne hb, mul_zero])
    (fun h => absurd (Finset.mem_univ ρ) h), Finsupp.single_eq_same, mul_one]

/-- The rays of the indices of `J₊` of the circuit of a wall are the rays with a positive class. -/
theorem image_jPlus (hσ : σ ∈ F.cones) (hs : IsSimplicial σ) :
    W.circuitRay '' (W.circuit hσ hs).jPlus = {ρ | 0 < W.curveClass ρ} := by
  ext ρ
  constructor
  · rintro ⟨i, hi, rfl⟩
    show 0 < W.curveClass (W.circuitRay i)
    rw [curveClass_circuitRay]
    exact hi
  · intro hρ
    rw [Set.mem_ofPred_eq] at hρ
    by_cases hr : ∃ i, W.circuitRay i = ρ
    · obtain ⟨i, rfl⟩ := hr
      rw [curveClass_circuitRay] at hρ
      exact ⟨i, hρ, rfl⟩
    · push Not at hr
      rw [W.curveClass_eq_zero hr] at hρ
      exact absurd hρ (lt_irrefl 0)

/-- The rays of the indices of `J₋` of the circuit of a wall are the rays with a negative class. -/
theorem image_jMinus (hσ : σ ∈ F.cones) (hs : IsSimplicial σ) :
    W.circuitRay '' (W.circuit hσ hs).jMinus = {ρ | W.curveClass ρ < 0} := by
  ext ρ
  constructor
  · rintro ⟨i, hi, rfl⟩
    show W.curveClass (W.circuitRay i) < 0
    rw [curveClass_circuitRay]
    exact hi
  · intro hρ
    rw [Set.mem_ofPred_eq] at hρ
    by_cases hr : ∃ i, W.circuitRay i = ρ
    · obtain ⟨i, rfl⟩ := hr
      rw [curveClass_circuitRay] at hρ
      exact ⟨i, hρ, rfl⟩
    · push Not at hr
      rw [W.curveClass_eq_zero hr] at hρ
      exact absurd hρ (lt_irrefl 0)

/-! ### The cone of `J₋` is in each wall of the ray -/

/-- A ray of `σ` with a coefficient `c_ρ ≥ 0` in the relation `u_ρ' = Σ c_ρ u_ρ` is in `σ'`. Only one ray of `σ` is not in `σ'` (`IsWallPair.eq_of_not_le`), and it has a negative coefficient (`exists_coeffIn_neg`). -/
theorem le_right_of_coeffIn_nonneg (hs : IsSimplicial σ)
    (hw : F.IsWallPair σ σ') (ρ : {ρ : F.Ray // ρ.1 ≤ σ}) (hρ : 0 ≤ W.coeffIn ρ) :
    ρ.1.1 ≤ σ' := by
  by_contra h
  obtain ⟨ρ₁, hρ₁, hneg⟩ := W.exists_coeffIn_neg hw.isMaximalCone_left.mem
    hw.isMaximalCone_right.mem
  have hρρ₁ : ρ = ρ₁ := Subtype.ext (hw.eq_of_not_le hs ρ.2 h ρ₁.2 hρ₁)
  rw [hρρ₁] at hρ
  linarith

/-- The rays of the indices of `J₋ ∪ J₀` of the circuit of a wall are rays of the wall `σ ∩ σ'`. -/
theorem circuitRay_le_inf (hs : IsSimplicial σ) (hw : F.IsWallPair σ σ')
    {i : Option {ρ : F.Ray // ρ.1 ≤ σ}} (hi : W.circuitCoeff i ≤ 0) :
    (W.circuitRay i).1 ≤ σ ⊓ σ' := by
  cases i with
  | none =>
    rw [circuitCoeff_none] at hi
    exact absurd hi (by norm_num)
  | some ρ =>
    rw [circuitCoeff_some] at hi
    rw [circuitRay_some]
    exact le_inf ρ.2 (W.le_right_of_coeffIn_nonneg hs hw ρ (by linarith))

/-- The cone `cone(u_{J₋})` of the rays with a negative class lies in the wall `σ ∩ σ'`, so in both maximal cones of the wall. -/
theorem negCone_curveClass_le_inf (hs : IsSimplicial σ)
    (hw : F.IsWallPair σ σ') : F.negCone W.curveClass ≤ σ ⊓ σ' := by
  unfold negCone
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨ρ, hρ, rfl⟩
  by_cases hr : ∃ i, W.circuitRay i = ρ
  · obtain ⟨i, rfl⟩ := hr
    rw [curveClass_circuitRay] at hρ
    exact W.circuitRay_le_inf hs hw hρ.le (F.toNR_generator_mem _)
  · push Not at hr
    rw [W.curveClass_eq_zero hr] at hρ
    exact absurd hρ (lt_irrefl 0)

/-! ### Walls with proportional classes -/

/-- The curves of the walls `W` and `W'` span the same ray of the cone of curves: there is `t > 0` with `D · V(τ') = t (D · V(τ))` for each divisor `D`. Each divisor of a complete simplicial fan is `ℝ`-Cartier, so this says that the numerical classes are proportional. -/
def IsProportional {τ τ' : PointedCone ℝ (NR n)} (W' : F.WallData τ τ') : Prop :=
  ∃ t : ℝ, 0 < t ∧ ∀ D : F.TDivisor ℝ, W'.degree D = t * W.degree D

variable {W} {τ τ' : PointedCone ℝ (NR n)} {W' : F.WallData τ τ'}

/-- The degrees on two walls are proportional exactly when their classes are. -/
theorem isProportional_iff :
    W.IsProportional W' ↔ ∃ t : ℝ, 0 < t ∧ W'.curveClass = t • W.curveClass := by
  constructor
  · rintro ⟨t, ht, h⟩
    refine ⟨t, ht, funext fun ρ => ?_⟩
    rw [Pi.smul_apply, smul_eq_mul, ← W'.degree_single, h, W.degree_single]
  · rintro ⟨t, ht, h⟩
    refine ⟨t, ht, fun D => ?_⟩
    rw [degree_eq_sum_curveClass, degree_eq_sum_curveClass, h, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, mul_assoc]

/-- Two walls whose classes are in the ray spanned by a vector `c` have proportional classes. -/
theorem isProportional_of_mem_hull {c : F.Ray → ℝ}
    (hW : W.curveClass ∈ PointedCone.hull ℝ {c}) (hW' : W'.curveClass ∈ PointedCone.hull ℝ {c}) :
    W.IsProportional W' := by
  obtain ⟨r, hr0, hr⟩ := PointedCone.mem_hull_singleton.mp hW
  obtain ⟨r', hr0', hr'⟩ := PointedCone.mem_hull_singleton.mp hW'
  have hpos : ∀ {s : ℝ} {d : F.Ray → ℝ}, 0 ≤ s → s • c = d → d ≠ 0 → 0 < s := by
    intro s d hs hd hd0
    refine lt_of_le_of_ne hs fun h => hd0 ?_
    rw [← hd, ← h, zero_smul]
  have hrpos := hpos hr0 hr W.curveClass_ne_zero
  have hrpos' := hpos hr0' hr' W'.curveClass_ne_zero
  refine isProportional_iff.mpr ⟨r' / r, div_pos hrpos' hrpos, ?_⟩
  rw [← hr, ← hr', smul_smul, div_mul_cancel₀ _ hrpos.ne']

/-- The degree of a divisor on the second wall is negative exactly when it is negative on the first one. So a ray is `D`-negative when one of its walls is. -/
theorem IsProportional.degree_neg_iff (h : W.IsProportional W') (D : F.TDivisor ℝ) :
    W'.degree D < 0 ↔ W.degree D < 0 := by
  obtain ⟨t, ht, h⟩ := h
  rw [h D]
  constructor
  · intro h1
    by_contra h2
    have := mul_nonneg ht.le (not_lt.mp h2)
    linarith
  · exact mul_neg_of_pos_of_neg ht

/-- Let the classes of two walls be proportional, with the factor `t`. An index `i'` of the circuit of the second wall whose ray is the ray of an index `i` of the circuit of the first wall has the coefficient `t aᵢ`. -/
theorem IsProportional.circuitCoeff_eq {t : ℝ} (h : W'.curveClass = t • W.curveClass)
    {i : Option {ρ : F.Ray // ρ.1 ≤ σ}} {i' : Option {ρ : F.Ray // ρ.1 ≤ τ}}
    (hi : W'.circuitRay i' = W.circuitRay i) : W'.circuitCoeff i' = t * W.circuitCoeff i := by
  rw [← W'.curveClass_circuitRay, hi, h, Pi.smul_apply, curveClass_circuitRay, smul_eq_mul]

/-- Let the classes of two walls be proportional. An index of the circuit of the second wall whose ray is not a ray of the circuit of the first wall has the coefficient zero: it is in `J₀`. -/
theorem IsProportional.circuitCoeff_eq_zero {t : ℝ} (h : W'.curveClass = t • W.curveClass)
    {i' : Option {ρ : F.Ray // ρ.1 ≤ τ}} (hi : ∀ i, W.circuitRay i ≠ W'.circuitRay i') :
    W'.circuitCoeff i' = 0 := by
  rw [← W'.curveClass_circuitRay, h, Pi.smul_apply, W.curveClass_eq_zero hi, smul_zero]

/-- **The walls of a ray have the same `J₊`** (Reid 1983, Corollary 2.5). When two walls have proportional classes, the rays of the indices of `J₊` of their circuits are the same. -/
theorem IsProportional.image_jPlus (h : W.IsProportional W') (hσ : σ ∈ F.cones)
    (hs : IsSimplicial σ) (hτ : τ ∈ F.cones) (hs' : IsSimplicial τ) :
    W'.circuitRay '' (W'.circuit hτ hs').jPlus = W.circuitRay '' (W.circuit hσ hs).jPlus := by
  obtain ⟨t, ht, hc⟩ := isProportional_iff.mp h
  rw [W.image_jPlus hσ hs, W'.image_jPlus hτ hs', hc]
  ext ρ
  simp only [Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul]
  exact mul_pos_iff_of_pos_left ht

/-- **The walls of a ray have the same `J₋`** (Reid 1983, Corollary 2.5). When two walls have proportional classes, the rays of the indices of `J₋` of their circuits are the same. -/
theorem IsProportional.image_jMinus (h : W.IsProportional W') (hσ : σ ∈ F.cones)
    (hs : IsSimplicial σ) (hτ : τ ∈ F.cones) (hs' : IsSimplicial τ) :
    W'.circuitRay '' (W'.circuit hτ hs').jMinus = W.circuitRay '' (W.circuit hσ hs).jMinus := by
  obtain ⟨t, ht, hc⟩ := isProportional_iff.mp h
  rw [W.image_jMinus hσ hs, W'.image_jMinus hτ hs', hc]
  ext ρ
  simp only [Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul]
  constructor
  · intro h1
    by_contra h2
    have := mul_nonneg ht.le (not_lt.mp h2)
    linarith
  · exact mul_neg_of_pos_of_neg ht

/-- **The cone of `J₋` is in each wall of the ray.** When two walls have proportional classes, the cone `cone(u_{J₋})` of the first lies in the wall of the second, so in both of its maximal cones. So `V(cone(u_{J₋}))` contains the curve of each wall of the ray. -/
theorem IsProportional.negCone_le_inf (h : W.IsProportional W') (hs' : IsSimplicial τ)
    (hw' : F.IsWallPair τ τ') : F.negCone W.curveClass ≤ τ ⊓ τ' := by
  obtain ⟨t, ht, hc⟩ := isProportional_iff.mp h
  rw [← F.negCone_smul W.curveClass ht, ← hc]
  exact W'.negCone_curveClass_le_inf hs' hw'

end WallData

/-! ### The cone of curves and its extremal rays -/

variable (F) in
/-- The cone of curves of the fan, in the space `ℝ^{Σ(1)}`: the cone spanned by the classes of the curves of the walls of the fan. By the toric cone theorem, the classes of the wall curves span the cone of curves `NE(X)` of the toric variety (Cox, Little and Schenck, Theorem 6.3.20). -/
noncomputable def curveCone : PointedCone ℝ (F.Ray → ℝ) :=
  PointedCone.hull ℝ
    {c | ∃ σ σ' : PointedCone ℝ (NR n), F.IsWallPair σ σ' ∧ ∃ W : F.WallData σ σ', W.curveClass = c}

/-- The class of the curve of a wall is in the cone of curves. -/
theorem WallData.curveClass_mem_curveCone {σ σ' : PointedCone ℝ (NR n)} (W : F.WallData σ σ')
    (hw : F.IsWallPair σ σ') : W.curveClass ∈ F.curveCone := by
  unfold curveCone
  exact PointedCone.subset_hull ⟨σ, σ', hw, W, rfl⟩

variable (F) in
/-- An extremal ray of the cone of curves: a face of the cone of curves that is spanned by one nonzero vector. -/
def IsExtremalRay (R : PointedCone ℝ (F.Ray → ℝ)) : Prop :=
  R.IsFaceOf F.curveCone ∧ ∃ c : F.Ray → ℝ, c ≠ 0 ∧ R = PointedCone.hull ℝ {c}

/-- **The walls of an extremal ray** (Reid 1983, Corollary 2.5). Two walls whose curves lie in an extremal ray `R` have proportional classes. So their circuits have the same rays in `J₊` and in `J₋` (`WallData.IsProportional.image_jPlus`, `WallData.IsProportional.image_jMinus`), with proportional coefficients (`WallData.IsProportional.circuitCoeff_eq`), and the cone of `J₋` lies in each wall of `R` (`WallData.IsProportional.negCone_le_inf`). -/
theorem IsExtremalRay.isProportional {R : PointedCone ℝ (F.Ray → ℝ)} (hR : F.IsExtremalRay R)
    {σ σ' τ τ' : PointedCone ℝ (NR n)} {W : F.WallData σ σ'} {W' : F.WallData τ τ'}
    (hW : W.curveClass ∈ R) (hW' : W'.curveClass ∈ R) : W.IsProportional W' := by
  obtain ⟨-, c, -, rfl⟩ := hR
  exact WallData.isProportional_of_mem_hull hW hW'

end Fan

end MinimalModel.Toric
