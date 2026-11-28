/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import MinimalModel.Toric.Flip
import MinimalModel.Toric.ConeTheorem

/-!
# Toric flips, part 2: the circuit of a wall and the join with a simplex

This file is step 2 of the route to `flipExists` in `MinimalModel/Toric/Flip.lean` (route R3, spec 04.4). Let `σ` and `σ'` be two maximal cones of a simplicial fan `F` that meet in a wall. The generators of the rays of `σ` and `σ'` form a circuit (Reid 1983, Section 2; Matsuki, Chapter 14; Cox, Little and Schenck, Section 15.3).

We read the circuit off the data of the wall, `Fan.WallData`. Let `ρ'` be the ray of `σ'` that is not in `σ`, with the relation `u_ρ' = Σ c_ρ u_ρ` over the rays `ρ` of `σ`. The index set of the circuit is `Option {ρ // ρ ≤ σ}`: the index `none` is the ray `ρ'`, and `some ρ` is a ray `ρ` of `σ`. Each ray of `σ'` is `ρ'` or a ray of `σ`, so these are all the rays of `σ` and `σ'`. The relation is `a = (1, -c)`, that is `u_ρ' - Σ c_ρ u_ρ = 0`. Each linear relation is a multiple of `a`, since the generators of the rays of a simplicial cone are linearly independent (`Fan.linearIndependent_generator`).

The signs are fixed as follows. The index `none` of `ρ'` is in `J₊`, and so is the index of a ray of `σ` that is not in `σ'`, since its coefficient `c_ρ` is negative (`Fan.WallData.exists_coeffIn_neg`). So `σ` and `σ'` are both cones of the fan `Circuit.fan` of the circuit: the original fan `F` contains the triangulation `Circuit.fan`, and the flip is `Circuit.neg.fan`. The degree of a divisor `D` on the wall is `Σ aᵢ D(ρᵢ)` (`Fan.WallData.degree_eq_sum`), so it changes sign when the circuit is replaced by the opposite circuit.

The last section starts step 4, the flipped fan. The star of the flipping locus is the join of `Circuit.fan` with a link `L`. For one cone `λ` of the link, spanned by lattice points `w` that are linearly independent modulo the span of the circuit, the join is again a circuit, `Circuit.join`: the relation is extended by zero, so the points `w` are in `J₀`. Its fan has the cones `cone(u_T) + cone(w_K)` with `T` missing an index of `J₊` (`Circuit.mem_join_fan_cones`), and its flip has the cones with `T` missing an index of `J₋` (`Circuit.mem_join_neg_fan_cones`). The results of `MinimalModel/Toric/Flip.lean` then give that both are simplicial fans with the same support (`Circuit.support_join_neg_fan`).

## Main definitions

* `Fan.WallData.circuitRay`, `Fan.WallData.circuitCoeff`: the rays of the circuit of a wall and the coefficients of the wall relation.
* `Fan.WallData.circuit`: the circuit of a wall of two cones `σ`, `σ'` with `σ` simplicial.
* `Circuit.join`: the join of a circuit with lattice points that are linearly independent modulo its span.

## Main results

* `Fan.linearIndependent_generator`: the generators of the rays of a fan in a simplicial cone of the fan are linearly independent.
* `Fan.WallData.isCircuit`: the wall relation `(1, -c)` is a circuit relation.
* `Fan.WallData.exists_coeffIn_neg`: a ray of `σ` that is not in `σ'` has a negative coefficient.
* `Fan.WallData.cone_setOf_le`: a cone of the fan spanned by rays of the circuit is the cone of the circuit of these rays.
* `Fan.WallData.mem_circuit_fan_left`, `Fan.WallData.mem_circuit_fan_right`: the cones `σ` and `σ'` are cones of the fan of the circuit.
* `Fan.WallData.degree_eq_sum`: the degree of a divisor on the wall is `Σ aᵢ D(ρᵢ)`.
* `Fan.IsWallPair.exists_circuit`: a wall pair of a simplicial fan gives a circuit whose fan contains the two cones.
* `IsCircuit.sumElim`: a circuit relation extended by zero to a family that is independent modulo the span is a circuit relation.
* `Circuit.mem_join_fan_cones`, `Circuit.mem_join_neg_fan_cones`: the cones of the fan of the join and of its flip.
* `Circuit.support_join_fan`, `Circuit.support_join_neg_fan`: the fan of the join and its flip have the same support.
-/

namespace MinimalModel.Toric

variable {n : ℕ}

namespace Fan

variable {F : Fan n}

/-- The rays of a fan in a cone form a finite type. -/
noncomputable instance (F : Fan n) (σ : PointedCone ℝ (NR n)) :
    Fintype {ρ : F.Ray // ρ.1 ≤ σ} :=
  Fintype.ofFinite _

/-- The primitive generators of the rays of a fan in a simplicial cone `σ` of the fan are linearly independent. Each such ray is a face of `σ`, so it is spanned by one of the linearly independent lattice points that span `σ`. -/
theorem linearIndependent_generator {σ : PointedCone ℝ (NR n)} (hσ : σ ∈ F.cones)
    (hs : IsSimplicial σ) :
    LinearIndependent ℝ fun ρ : {ρ : F.Ray // ρ.1 ≤ σ} => toNR (F.generator ρ.1) := by
  obtain ⟨S, rfl, hS⟩ := hs
  have hpt : ∀ ρ : {ρ : F.Ray // ρ.1 ≤ latticeCone S}, ∃ s : (S : Set (Fin n → ℤ)),
      toNR s.1 ∈ ρ.1.1 ∧ ∃ r : ℝ, 0 < r ∧ toNR (F.generator ρ.1) = r • toNR s.1 := by
    intro ρ
    obtain ⟨T, hTS, hT⟩ := exists_subset_of_isFaceOf_latticeCone (F.isFaceOf_of_le hσ ρ.1 ρ.2)
    obtain ⟨s, hsT⟩ : T.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      rintro rfl
      exact (F.isRay ρ.1).ne_bot (hT.trans latticeCone_empty)
    have hsS : s ∈ (S : Set (Fin n → ℤ)) := Finset.mem_coe.mpr (hTS hsT)
    have hs0 : toNR s ≠ 0 := hS.ne_zero ⟨s, hsS⟩
    have hsρ : toNR s ∈ ρ.1.1 := by
      rw [hT]
      exact toNR_mem_latticeCone hsT
    refine ⟨⟨s, hsS⟩, hsρ, ?_⟩
    have hsρ' := hsρ
    rw [← F.latticeCone_generator ρ.1, mem_latticeCone_singleton] at hsρ'
    obtain ⟨r, hr, hrs⟩ := hsρ'
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hrs
      exact hs0 hrs.symm
    refine ⟨r⁻¹, inv_pos.mpr (lt_of_le_of_ne hr (Ne.symm hr0)), ?_⟩
    rw [← hrs, smul_smul, inv_mul_cancel₀ hr0, one_smul]
  choose s hsmem r hr hgen using hpt
  have hinj : Function.Injective s := by
    intro ρ₁ ρ₂ h
    have h2 : toNR (s ρ₁).1 ∈ ρ₂.1.1 := by
      rw [h]
      exact hsmem ρ₂
    exact Subtype.ext (ray_eq_of_mem (hsmem ρ₁) h2 (hS.ne_zero (s ρ₁)))
  have hli : LinearIndependent ℝ fun ρ => toNR (s ρ).1 := hS.comp s hinj
  convert hli.units_smul fun ρ => Units.mk0 (r ρ) (hr ρ).ne' using 1
  funext ρ
  simp only [Pi.smul_apply', Units.smul_def, Units.val_mk0, hgen ρ]

namespace WallData

variable {σ σ' : PointedCone ℝ (NR n)} (W : F.WallData σ σ')

/-- The rays of the circuit of a wall: the index `none` is the ray `ρ'` of `σ'` that is not in `σ`, and the index `some ρ` is a ray `ρ` of the fan in `σ`. -/
def circuitRay (i : Option {ρ : F.Ray // ρ.1 ≤ σ}) : F.Ray :=
  Option.elim i W.ray Subtype.val

/-- The ray of the index `none` is the ray `ρ'` of `σ'` that is not in `σ`. -/
@[simp]
theorem circuitRay_none : W.circuitRay none = W.ray := rfl

/-- The ray of the index `some ρ` is `ρ`. -/
@[simp]
theorem circuitRay_some (ρ : {ρ : F.Ray // ρ.1 ≤ σ}) : W.circuitRay (some ρ) = ρ.1 := rfl

open Classical in
/-- The coefficient `c_ρ` of the wall relation `u_ρ' = Σ c_ρ u_ρ` at a ray `ρ` of `σ`. It is zero when `ρ` is not in the base of the relation. -/
noncomputable def coeffIn (ρ : {ρ : F.Ray // ρ.1 ≤ σ}) : ℝ :=
  if ρ.1 ∈ W.base then W.coeff ρ.1 else 0

/-- The coefficients `a = (1, -c)` of the wall relation `u_ρ' - Σ c_ρ u_ρ = 0`. -/
noncomputable def circuitCoeff (i : Option {ρ : F.Ray // ρ.1 ≤ σ}) : ℝ :=
  Option.elim i 1 fun ρ => -W.coeffIn ρ

/-- The coefficient of the index `none` is `1`. -/
@[simp]
theorem circuitCoeff_none : W.circuitCoeff none = 1 := rfl

/-- The coefficient of the index `some ρ` is `-c_ρ`. -/
@[simp]
theorem circuitCoeff_some (ρ : {ρ : F.Ray // ρ.1 ≤ σ}) :
    W.circuitCoeff (some ρ) = -W.coeffIn ρ := rfl

/-- The sum of the relation over all the rays of `σ` is the sum over the base of the relation. -/
theorem sum_coeffIn_smul {M : Type*} [AddCommMonoid M] [Module ℝ M] (g : F.Ray → M) :
    ∑ ρ : {ρ : F.Ray // ρ.1 ≤ σ}, W.coeffIn ρ • g ρ.1 = ∑ ρ ∈ W.base, W.coeff ρ • g ρ := by
  classical
  have h1 : ∑ ρ ∈ W.base, W.coeff ρ • g ρ =
      ∑ ρ ∈ Finset.univ.filter fun ρ : F.Ray => ρ.1 ≤ σ,
        if ρ ∈ W.base then W.coeff ρ • g ρ else 0 := by
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext ρ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => ⟨W.base_le ρ h, h⟩, fun h => h.2⟩
  have h2 : ∑ ρ ∈ Finset.univ.filter fun ρ : F.Ray => ρ.1 ≤ σ,
        (if ρ ∈ W.base then W.coeff ρ • g ρ else 0) =
      ∑ ρ : {ρ : F.Ray // ρ.1 ≤ σ}, if ρ.1 ∈ W.base then W.coeff ρ.1 • g ρ.1 else 0 :=
    Finset.sum_subtype _ (fun ρ => by simp) _
  rw [h1, h2]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  by_cases h : ρ.1 ∈ W.base
  · simp [coeffIn, h]
  · simp [coeffIn, h]

/-- The wall relation over all the rays of `σ`: `u_ρ' = Σ c_ρ u_ρ`. -/
theorem sum_coeffIn_smul_generator :
    ∑ ρ : {ρ : F.Ray // ρ.1 ≤ σ}, W.coeffIn ρ • toNR (F.generator ρ.1) =
      toNR (F.generator W.ray) := by
  rw [W.sum_coeffIn_smul fun ρ => toNR (F.generator ρ), W.relation]

/-- The wall relation `(1, -c)` is a circuit relation of the generators of the rays of `σ` and `σ'`, when `σ` is a simplicial cone of the fan: each linear relation of these generators is a multiple of it. -/
theorem isCircuit (hσ : σ ∈ F.cones)
    (hs : IsSimplicial σ) :
    IsCircuit (fun i => toNR (F.generator (W.circuitRay i))) W.circuitCoeff := by
  have hrel := W.sum_coeffIn_smul_generator
  refine ⟨?_, fun b hb => ⟨b none, ?_⟩⟩
  · rw [Fintype.sum_option]
    simp only [circuitCoeff_none, circuitRay_none, circuitCoeff_some, circuitRay_some, one_smul,
      neg_smul, Finset.sum_neg_distrib, hrel]
    exact add_neg_cancel _
  · rw [Fintype.sum_option] at hb
    simp only [circuitRay_none, circuitRay_some] at hb
    rw [← hrel, Finset.smul_sum, ← Finset.sum_add_distrib] at hb
    have h0 := Fintype.linearIndependent_iff.mp (linearIndependent_generator hσ hs)
      (fun ρ => b none * W.coeffIn ρ + b (some ρ)) (by
        refine Eq.trans ?_ hb
        refine Finset.sum_congr rfl fun ρ _ => ?_
        simp only [add_smul, mul_smul])
    funext i
    cases i with
    | none =>
      rw [Pi.smul_apply, smul_eq_mul, circuitCoeff_none, mul_one]
    | some ρ =>
      have h1 : b none * W.coeffIn ρ + b (some ρ) = 0 := h0 ρ
      rw [Pi.smul_apply, smul_eq_mul, circuitCoeff_some, mul_neg]
      linarith

/-- The circuit of a wall (Reid 1983, Section 2). Let `σ` be a simplicial cone of the fan. The lattice points are the generators of the ray `ρ'` of `σ'` that is not in `σ` (the index `none`) and of the rays of `σ` (the indices `some ρ`). The relation is the wall relation `u_ρ' - Σ c_ρ u_ρ = 0`. -/
noncomputable def circuit (hσ : σ ∈ F.cones)
    (hs : IsSimplicial σ) : Circuit (Option {ρ : F.Ray // ρ.1 ≤ σ}) n where
  u i := F.generator (W.circuitRay i)
  a := W.circuitCoeff
  isCircuit := W.isCircuit hσ hs

/-- The coefficient of the ray `ρ'` in the circuit of the wall is positive: the index `none` is in `J₊`. -/
theorem none_mem_jPlus (hσ : σ ∈ F.cones)
    (hs : IsSimplicial σ) : none ∈ (W.circuit hσ hs).jPlus := by
  show (0 : ℝ) < W.circuitCoeff none
  rw [circuitCoeff_none]
  exact one_pos

/-- A ray of `σ` that is not in `σ'` has a negative coefficient in the wall relation. Otherwise the generator `u_ρ'` would be in the face `σ ∩ σ'` of `σ'`, and so in `σ`: write `u_ρ' + Σ (-min(c_ρ, 0)) u_ρ = Σ max(c_ρ, 0) u_ρ`, where the left side is in `σ'` and the right side is in `σ`. -/
theorem exists_coeffIn_neg (hσ : σ ∈ F.cones) (hσ' : σ' ∈ F.cones) :
    ∃ ρ : {ρ : F.Ray // ρ.1 ≤ σ}, ¬ ρ.1.1 ≤ σ' ∧ W.coeffIn ρ < 0 := by
  by_contra hno
  have key : ∀ ρ : {ρ : F.Ray // ρ.1 ≤ σ}, W.coeffIn ρ < 0 → ρ.1.1 ≤ σ' := fun ρ hρ => by
    by_contra h
    exact hno ⟨ρ, h, hρ⟩
  have hg' : toNR (F.generator W.ray) ∈ σ' := W.ray_le (F.toNR_generator_mem W.ray)
  have hy : ∑ ρ : {ρ : F.Ray // ρ.1 ≤ σ}, (-min (W.coeffIn ρ) 0) • toNR (F.generator ρ.1) ∈
      σ' := by
    refine Submodule.sum_mem _ fun ρ _ => ?_
    by_cases h : W.coeffIn ρ < 0
    · exact PointedCone.smul_mem _ (neg_nonneg.mpr (min_le_right _ _))
        (key ρ h (F.toNR_generator_mem ρ.1))
    · rw [min_eq_right (not_lt.mp h), neg_zero, zero_smul]
      exact zero_mem _
  have hz : ∑ ρ : {ρ : F.Ray // ρ.1 ≤ σ}, max (W.coeffIn ρ) 0 • toNR (F.generator ρ.1) ∈ σ :=
    Submodule.sum_mem _ fun ρ _ =>
      PointedCone.smul_mem _ (le_max_right _ _) (ρ.2 (F.toNR_generator_mem ρ.1))
  have hsum : toNR (F.generator W.ray) +
      ∑ ρ : {ρ : F.Ray // ρ.1 ≤ σ}, (-min (W.coeffIn ρ) 0) • toNR (F.generator ρ.1) =
      ∑ ρ : {ρ : F.Ray // ρ.1 ≤ σ}, max (W.coeffIn ρ) 0 • toNR (F.generator ρ.1) := by
    rw [← W.sum_coeffIn_smul_generator, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [← add_smul]
    congr 1
    have := max_add_min (W.coeffIn ρ) 0
    linarith
  have hinf : (1 : ℝ) • toNR (F.generator W.ray) +
      ∑ ρ : {ρ : F.Ray // ρ.1 ≤ σ}, (-min (W.coeffIn ρ) 0) • toNR (F.generator ρ.1) ∈
      σ ⊓ σ' := by
    rw [one_smul]
    exact Submodule.mem_inf.mpr ⟨by rw [hsum]; exact hz, add_mem hg' hy⟩
  have hmem := (F.inter_face_right hσ hσ').mem_of_smul_add_mem hg' hy one_pos hinf
  apply W.ray_not_le
  rw [← F.latticeCone_generator W.ray]
  exact latticeCone_singleton_le.mpr (Submodule.mem_inf.mp hmem).1

/-- A cone `τ` of the fan whose rays are rays of the circuit is the cone of the circuit of the indices of the rays in `τ`. -/
theorem cone_setOf_le (hσ : σ ∈ F.cones)
    (hs : IsSimplicial σ) {τ : PointedCone ℝ (NR n)} (hτ : τ ∈ F.cones)
    (h : ∀ ρ : F.Ray, ρ.1 ≤ τ → ∃ i, W.circuitRay i = ρ) :
    (W.circuit hσ hs).cone {i | (W.circuitRay i).1 ≤ τ} = τ := by
  refine Eq.trans ?_ (F.eq_hull_generator hτ).symm
  show PointedCone.hull ℝ _ = PointedCone.hull ℝ _
  congr 1
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨W.circuitRay i, hi, rfl⟩
  · rintro ⟨ρ, hρ, rfl⟩
    obtain ⟨i, rfl⟩ := h ρ hρ
    exact ⟨i, hρ, rfl⟩

/-- The cone `σ` is a cone of the fan of the circuit of the wall: it is the cone of the indices `some ρ`, and it misses the index `none` of `J₊`. -/
theorem mem_circuit_fan_left (hσ : σ ∈ F.cones) (hs : IsSimplicial σ) :
    σ ∈ (W.circuit hσ hs).fan.cones :=
  (W.circuit hσ hs).mem_fan_cones.mpr ⟨{i | (W.circuitRay i).1 ≤ σ}, none,
    W.none_mem_jPlus hσ hs, W.ray_not_le,
    (W.cone_setOf_le hσ hs hσ fun ρ hρ => ⟨some ⟨ρ, hρ⟩, rfl⟩).symm⟩

/-- The cone `σ'` is a cone of the fan of the circuit of the wall: it is the cone of the index `none` and of the rays of `σ` in `σ'`, and it misses the index of a ray of `σ` with a negative coefficient (`exists_coeffIn_neg`), which is in `J₊`. -/
theorem mem_circuit_fan_right (hσ : σ ∈ F.cones) (hs : IsSimplicial σ) (hσ' : σ' ∈ F.cones) :
    σ' ∈ (W.circuit hσ hs).fan.cones := by
  obtain ⟨ρ, hρσ', hρneg⟩ := W.exists_coeffIn_neg hσ hσ'
  refine (W.circuit hσ hs).mem_fan_cones.mpr ⟨{i | (W.circuitRay i).1 ≤ σ'}, some ρ, ?_, hρσ',
    (W.cone_setOf_le hσ hs hσ' fun ρ' hρ' => ?_).symm⟩
  · show (0 : ℝ) < W.circuitCoeff (some ρ)
    rw [circuitCoeff_some]
    linarith
  · rcases W.eq_or_le ρ' hρ' with rfl | h
    · exact ⟨none, rfl⟩
    · exact ⟨some ⟨ρ', h⟩, rfl⟩

/-- The degree of a divisor `D` on the wall is `Σ aᵢ D(ρᵢ)`, the sum of the coefficients of the wall relation times the coefficients of `D` on the rays of the circuit. So it changes sign when the circuit is replaced by the opposite circuit. -/
theorem degree_eq_sum (D : F.TDivisor ℝ) :
    W.degree D = ∑ i, W.circuitCoeff i * D (W.circuitRay i) := by
  have h := W.sum_coeffIn_smul fun ρ => D ρ
  simp only [smul_eq_mul] at h
  rw [WallData.degree, ← h, Fintype.sum_option]
  simp only [circuitCoeff_none, circuitRay_none, circuitCoeff_some, circuitRay_some, one_mul,
    neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg]

end WallData

/-- **The circuit of a wall.** Two maximal cones `σ` and `σ'` of a simplicial fan that meet in a wall give a circuit: the generators of their rays, with the wall relation of `Fan.IsWallPair.nonempty_wallData`. The two cones are cones of the fan of the circuit, so the fan `F` contains this triangulation of the circuit near the wall, and the flip replaces it by the fan of the opposite circuit. -/
theorem IsWallPair.exists_circuit {σ σ' : PointedCone ℝ (NR n)} (hs : F.IsSimplicialFan)
    (hw : F.IsWallPair σ σ') :
    ∃ (ι : Type) (_ : Fintype ι) (C : Circuit ι n), σ ∈ C.fan.cones ∧ σ' ∈ C.fan.cones := by
  obtain ⟨W⟩ := hw.nonempty_wallData hs
  have hσ := hw.isMaximalCone_left.mem
  exact ⟨Option {ρ : F.Ray // ρ.1 ≤ σ}, inferInstance, W.circuit hσ (hs σ hσ), W.mem_circuit_fan_left hσ (hs σ hσ),
    W.mem_circuit_fan_right hσ (hs σ hσ) hw.isMaximalCone_right.mem⟩

end Fan

/-! ### The join of a circuit with a simplex -/

section Join

variable {ι κ E : Type*} [Fintype ι] [Fintype κ] [AddCommGroup E] [Module ℝ E]

/-- The cone of the indices `inl '' T ∪ inr '' K` of a sum of two families is the sum of the cone of `T` in the first family and the cone of `K` in the second one. -/
omit [Fintype ι] [Fintype κ] in
theorem indexCone_sumElim (v : ι → E) (w : κ → E) (T : Set ι) (K : Set κ) :
    indexCone (Sum.elim v w) (Sum.inl '' T ∪ Sum.inr '' K) = indexCone v T ⊔ indexCone w K := by
  unfold indexCone
  simp only [Set.image_union, Set.image_image, Sum.elim_inl, Sum.elim_inr]
  exact Submodule.span_union _ _

/-- Let `a` be a circuit relation of `v`, and let `w` be a family that is linearly independent modulo the span of `v`. Then `a`, extended by zero, is a circuit relation of the family `v, w`. -/
theorem IsCircuit.sumElim {v : ι → E} {a : ι → ℝ} (h : IsCircuit v a) {w : κ → E}
    (hw : ∀ (b : ι → ℝ) (c : κ → ℝ), ∑ i, b i • v i + ∑ k, c k • w k = 0 → c = 0) :
    IsCircuit (Sum.elim v w) (Sum.elim a 0) := by
  refine ⟨by simp [Fintype.sum_sum_type, h.1], fun b hb => ?_⟩
  rw [Fintype.sum_sum_type] at hb
  simp only [Sum.elim_inl, Sum.elim_inr] at hb
  have hc : ∀ k, b (Sum.inr k) = 0 := fun k => congrFun (hw _ _ hb) k
  have hb' : ∑ i, b (Sum.inl i) • v i = 0 := by simpa [hc] using hb
  obtain ⟨s, hs⟩ := h.2 _ hb'
  refine ⟨s, funext fun x => ?_⟩
  cases x with
  | inl i => simpa using congrFun hs i
  | inr k => simp [hc k]

end Join

namespace Circuit

variable {ι κ : Type*} [Fintype ι] [Fintype κ] (C : Circuit ι n) (w : κ → Fin n → ℤ)
  (hw : ∀ (b : ι → ℝ) (c : κ → ℝ),
    ∑ i, b i • toNR (C.u i) + ∑ k, c k • toNR (w k) = 0 → c = 0)

/-- The join of a circuit with lattice points `w` that are linearly independent modulo the span of the `uᵢ`. The relation is extended by zero, so the points `w` are in `J₀`. The fan of the join is the join of the fan of the circuit with the faces of the simplicial cone of `w` (`mem_join_fan_cones`). This is the local model of the star of a flipping locus with one cone in its link (Reid 1983, Section 2). -/
noncomputable def join : Circuit (ι ⊕ κ) n where
  u := Sum.elim C.u w
  a := Sum.elim C.a 0
  isCircuit := by
    have he : (fun i => toNR (Sum.elim C.u w i)) =
        Sum.elim (fun i => toNR (C.u i)) fun k => toNR (w k) := by
      funext x
      cases x <;> rfl
    show IsCircuit (fun i => toNR (Sum.elim C.u w i)) (Sum.elim C.a 0)
    rw [he]
    exact C.isCircuit.sumElim hw

/-- The set `J₊` of the join is the set `J₊` of the circuit. -/
theorem jPlus_join : (C.join w hw).jPlus = Sum.inl '' C.jPlus := by
  ext x
  cases x with
  | inl i => simp [jPlus, join]
  | inr k => simp [jPlus, join]

/-- The set `J₋` of the join is the set `J₋` of the circuit. -/
theorem jMinus_join : (C.join w hw).jMinus = Sum.inl '' C.jMinus := by
  ext x
  cases x with
  | inl i => simp [jMinus, join]
  | inr k => simp [jMinus, join]

/-- The opposite of the join is the join of the opposite circuit. -/
theorem neg_join : (C.join w hw).neg = C.neg.join w hw := by
  simp only [neg, join, Circuit.mk.injEq, true_and]
  funext x
  cases x <;> simp

/-- The cone of the join of the indices `inl '' T ∪ inr '' K` is the sum of the cone `cone(u_T)` of the circuit and the cone of the points `w_k` with `k ∈ K`. -/
theorem join_cone (T : Set ι) (K : Set κ) :
    (C.join w hw).cone (Sum.inl '' T ∪ Sum.inr '' K) =
      C.cone T ⊔ indexCone (fun k => toNR (w k)) K := by
  have he : (fun i => toNR ((C.join w hw).u i)) =
      Sum.elim (fun i => toNR (C.u i)) fun k => toNR (w k) := by
    funext x
    cases x <;> rfl
  show indexCone (fun i => toNR ((C.join w hw).u i)) _ = _
  rw [he, indexCone_sumElim]
  rfl

/-- The cones of the fan of the join are the sums `cone(u_T) + cone(w_K)`, where `T` misses an index of `J₊` and `K` is any set of indices of `w`. So the fan of the join is the join of `C.fan` with the faces of the cone of `w`. -/
theorem mem_join_fan_cones {σ : PointedCone ℝ (NR n)} :
    σ ∈ (C.join w hw).fan.cones ↔ ∃ T : Set ι, ∃ j ∈ C.jPlus, j ∉ T ∧
      ∃ K : Set κ, σ = C.cone T ⊔ indexCone (fun k => toNR (w k)) K := by
  rw [mem_fan_cones, jPlus_join]
  constructor
  · rintro ⟨S, _, ⟨j, hj, rfl⟩, hjS, rfl⟩
    refine ⟨Sum.inl ⁻¹' S, j, hj, hjS, Sum.inr ⁻¹' S, ?_⟩
    rw [← C.join_cone w hw]
    congr 1
    ext x
    cases x <;> simp
  · rintro ⟨T, j, hj, hjT, K, rfl⟩
    exact ⟨_, _, ⟨j, hj, rfl⟩, by simpa using hjT, (C.join_cone w hw T K).symm⟩

/-- The cones of the flip of the join are the sums `cone(u_T) + cone(w_K)`, where `T` misses an index of `J₋`. So the flip of the join is the join of the flip `C.neg.fan` with the faces of the cone of `w`. -/
theorem mem_join_neg_fan_cones {σ : PointedCone ℝ (NR n)} :
    σ ∈ (C.join w hw).neg.fan.cones ↔ ∃ T : Set ι, ∃ j ∈ C.jMinus, j ∉ T ∧
      ∃ K : Set κ, σ = C.cone T ⊔ indexCone (fun k => toNR (w k)) K := by
  rw [C.neg_join w hw, C.neg.mem_join_fan_cones w hw, C.jPlus_neg]
  exact Iff.rfl

/-- When `J₊` and `J₋` are not empty, the fan of the join and its flip have the same support, the sum of the cone of the circuit and the cone of `w`. -/
theorem support_join_neg_fan {j₀ k₀ : ι} (hj₀ : j₀ ∈ C.jPlus) (hk₀ : k₀ ∈ C.jMinus) :
    (C.join w hw).neg.fan.support = (C.join w hw).fan.support :=
  (C.join w hw).support_neg_fan (j₀ := Sum.inl j₀) (k₀ := Sum.inl k₀)
    (by rw [jPlus_join]; exact ⟨j₀, hj₀, rfl⟩) (by rw [jMinus_join]; exact ⟨k₀, hk₀, rfl⟩)

/-- The support of the fan of the join is the sum of the cone of the circuit and the cone of `w`, when `J₊` is not empty. -/
theorem support_join_fan {j₀ : ι} (hj₀ : j₀ ∈ C.jPlus) :
    (C.join w hw).fan.support =
      ((C.cone Set.univ ⊔ indexCone (fun k => toNR (w k)) Set.univ : PointedCone ℝ (NR n)) :
        Set (NR n)) := by
  rw [(C.join w hw).support_fan (j₀ := Sum.inl j₀) (by rw [jPlus_join]; exact ⟨j₀, hj₀, rfl⟩),
    ← C.join_cone w hw, Set.image_univ, Set.image_univ, Set.range_inl_union_range_inr]

end Circuit

end MinimalModel.Toric
