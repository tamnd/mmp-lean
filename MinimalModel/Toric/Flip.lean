/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import MinimalModel.Toric.Program

/-!
# Toric flips, part 1: the two triangulations of a circuit

This file starts step 5 of route R3 (spec 04.4), the toric flip. It gives the local model of a flip (Reid 1983, Section 2; Matsuki, Chapter 14; Cox, Little and Schenck, Section 15.3).

## The route to `flipExists`

Let `F` be a complete simplicial fan in `N_ℝ = ℝⁿ`, and let `R` be an extremal ray of its cone of curves, spanned by the class of the curve `V(τ)` of a wall `τ = σ ∩ σ'`. The `n + 1` generators `u_i` of the rays of `σ` and `σ'` satisfy one linear relation `∑ aᵢ uᵢ = 0`, unique up to a scalar, the wall relation. It splits the indices into `J₊ = {i | 0 < aᵢ}`, `J₋ = {i | aᵢ < 0}` and `J₀ = {i | aᵢ = 0}`. The plan is the following.

1. (This file.) The combinatorics of a circuit: a finite family `u` of lattice points and a relation `a` such that each linear relation of the `uᵢ` is a multiple of `a`. The cones `cone(u_T)` with `T` missing an index of `J₊` form a simplicial fan `Circuit.fan`. The cones with `T` missing an index of `J₋` form the fan `C.neg.fan` of the opposite relation `-a`. When `J₊` and `J₋` are not empty, the two fans have the same support, the cone of all the `uᵢ`. These are the two triangulations of the circuit; the flip replaces the first by the second.
2. (Next.) The circuit of a wall: for a wall pair `σ, σ'` of a complete simplicial fan, the generators of `σ` and `σ'` form a circuit, with the relation of `Fan.IsWallPair.nonempty_wallData`. The relation is unique up to a scalar because the generators of `σ` are a basis of `N_ℝ`.
3. (Next.) The star of the exceptional locus (Reid, Corollary 2.5; Matsuki, Proposition 14-2-1). For a `D`-negative extremal ray `R`, all the walls of `R` have proportional relations, up to the indices of `J₀`. The cones of `F` that contain `cone(u_{J₋})` are the sums of the cones of `Circuit.fan` with the cones of a link `L`. The contraction `G` replaces these cones by the sums `cone(u_{J₊ ∪ J₋}) + λ` with `λ ∈ L`; it is birational when `J₋` is not empty, a flip when `J₋` has at least two indices.
4. (Next.) The flipped fan: `F⁺` replaces the cones of `Circuit.fan + L` by the cones of `C.neg.fan + L`. The results of this file give that `F⁺` is a simplicial fan with the support and the rays of `F`, and that it refines `G`.
5. (Next.) The step: `F⁺` and the strict transform of `D` satisfy `IsToricStep`. The divisor is ample over `G` on `F⁺` since its degree on the flipped walls changes sign (Reid, Theorem 3.4). This gives `flipExists`.
6. (Later.) Termination: a flip keeps the rays, so the fans of a sequence of flips are among finitely many simplicial fans with the same rays. The support function of `D` increases strictly at each flip (Fujino and Sato 2004, Matsuki 14-2-7), so no fan comes back. A divisorial contraction removes a ray. This gives `terminationOfFlips` and, with the toric cone theorem, `mmp` (S39).

## Main definitions

* `indexCone v T`: the cone of the vectors `v i` with `i ∈ T`.
* `IsCircuit v a`: `a` is a linear relation of the family `v`, and each relation is a multiple of `a`.
* `Circuit`, `Circuit.jPlus`, `Circuit.jMinus`, `Circuit.jZero`: a circuit of lattice points and the sets `J₊`, `J₋`, `J₀`.
* `Circuit.neg`: the circuit with the opposite relation, so `J₊` and `J₋` change places.
* `Circuit.fan`: the fan of the cones `cone(u_T)` with `T` missing an index of `J₊`.

## Main results

* `mem_indexCone`: the points of `indexCone v T` are the nonnegative combinations of the `v i` with `i ∈ T`.
* `IsCircuit.exists_mem_indexCone_compl`: the cones `cone(u_{≠ j})` with `j ∈ J₊` cover the cone of all the `uᵢ`.
* `IsCircuit.indexCone_inf`: two cones that each miss an index of `J₊` meet in the cone of the common indices.
* `IsCircuit.indexCone_isFaceOf`, `IsCircuit.linearIndepOn`: a cone that misses an index of `J₊ ∪ J₋` is simplicial, and the cones of its subsets are faces.
* `Circuit.isSimplicialFan_fan`: the fan of a circuit is simplicial.
* `Circuit.support_fan`, `Circuit.support_neg_fan`: the fan of a circuit with `J₊` not empty has the support `cone(u)`, and the flipped fan has the same support.
-/

namespace MinimalModel.Toric

variable {n : ℕ}

section IndexCone

variable {ι E : Type*} [Fintype ι] [AddCommGroup E] [Module ℝ E]

/-- The cone spanned by the vectors `v i` with `i ∈ T`. -/
noncomputable def indexCone (v : ι → E) (T : Set ι) : PointedCone ℝ E :=
  PointedCone.hull ℝ (v '' T)

/-- A vector is in `indexCone v T` when it is a nonnegative combination of the `v i`, with the coefficients zero outside `T`. -/
theorem mem_indexCone {v : ι → E} {T : Set ι} {x : E} :
    x ∈ indexCone v T ↔
      ∃ c : ι → ℝ, (∀ i, 0 ≤ c i) ∧ (∀ i, i ∉ T → c i = 0) ∧ ∑ i, c i • v i = x := by
  classical
  unfold indexCone
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, hi, rfl⟩ := hy
      refine ⟨fun k => if k = i then 1 else 0, fun k => ?_, fun k hk => ?_, ?_⟩
      · dsimp only
        split_ifs <;> norm_num
      · have hki : k ≠ i := fun h => hk (h ▸ hi)
        simp [hki]
      · simp [ite_smul]
    | zero => exact ⟨0, fun _ => le_rfl, fun _ _ => rfl, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨c, hc, hcT, rfl⟩ := hy
      obtain ⟨d, hd, hdT, rfl⟩ := hz
      refine ⟨c + d, fun i => add_nonneg (hc i) (hd i), fun i hi => ?_, ?_⟩
      · simp [hcT i hi, hdT i hi]
      · simp [add_smul, Finset.sum_add_distrib]
    | smul r y _ hy =>
      obtain ⟨c, hc, hcT, rfl⟩ := hy
      refine ⟨fun i => (r : ℝ) * c i, fun i => mul_nonneg r.2 (hc i), fun i hi => ?_, ?_⟩
      · simp [hcT i hi]
      · rw [← Nonneg.coe_smul, Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ => mul_smul _ _ _
  · rintro ⟨c, hc, hcT, rfl⟩
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hi : i ∈ T
    · exact PointedCone.smul_mem _ (hc i) (Submodule.subset_span ⟨i, hi, rfl⟩)
    · rw [hcT i hi, zero_smul]
      exact zero_mem _

omit [Fintype ι] in
/-- The cone of a smaller set of indices is smaller. -/
theorem indexCone_mono (v : ι → E) {S T : Set ι} (h : S ⊆ T) : indexCone v S ≤ indexCone v T :=
  Submodule.span_mono (Set.image_mono h)

/-- A circuit relation of a family `v`: `∑ aᵢ vᵢ = 0`, and each linear relation of the `vᵢ` is a multiple of `a`. For the `n + 1` generators of two simplicial cones of dimension `n` that meet in a wall, this is the wall relation (Cox, Little and Schenck, Section 6.4; Reid 1983, Section 2). -/
def IsCircuit (v : ι → E) (a : ι → ℝ) : Prop :=
  ∑ i, a i • v i = 0 ∧ ∀ b : ι → ℝ, ∑ i, b i • v i = 0 → ∃ s : ℝ, b = s • a

namespace IsCircuit

variable {v : ι → E} {a : ι → ℝ}

/-- The opposite relation `-a` is a circuit relation. -/
theorem neg (h : IsCircuit v a) : IsCircuit v (-a) := by
  refine ⟨by simp [neg_smul, Finset.sum_neg_distrib, h.1], fun b hb => ?_⟩
  obtain ⟨s, hs⟩ := h.2 b hb
  exact ⟨-s, by rw [hs, neg_smul_neg]⟩

/-- Let `j` be an index with `aⱼ ≠ 0`, and let `S` be a set of indices without `j`. Two combinations of the `vᵢ` with `i ∈ S` that have the same value have the same coefficients. -/
theorem eq_of_sum_eq (h : IsCircuit v a) {S : Set ι} {j : ι} (hj : a j ≠ 0) (hjS : j ∉ S)
    {c d : ι → ℝ} (hc : ∀ i, i ∉ S → c i = 0) (hd : ∀ i, i ∉ S → d i = 0)
    (hcd : ∑ i, c i • v i = ∑ i, d i • v i) : c = d := by
  obtain ⟨s, hs⟩ := h.2 (c - d) (by simp [sub_smul, Finset.sum_sub_distrib, hcd])
  have hj' : c j - d j = s * a j := by simpa using congrFun hs j
  rw [hc j hjS, hd j hjS, sub_zero] at hj'
  have hs0 : s = 0 := by
    rcases mul_eq_zero.mp hj'.symm with h0 | h0
    · exact h0
    · exact absurd h0 hj
  funext i
  have hi : c i - d i = s * a i := by simpa using congrFun hs i
  rw [hs0, zero_mul] at hi
  exact sub_eq_zero.mp hi

/-- The vectors `vᵢ` with `i ∈ S` are linearly independent when `S` misses an index `j` with `aⱼ ≠ 0`. So the cone of a set of indices that misses an index of `J₊ ∪ J₋` is simplicial. -/
theorem linearIndepOn (h : IsCircuit v a) {S : Set ι} {j : ι} (hj : a j ≠ 0) (hjS : j ∉ S) :
    LinearIndepOn ℝ v S := by
  classical
  rw [linearIndepOn_iff']
  intro t g hts hg i hi
  have hb := h.eq_of_sum_eq (c := fun k => if k ∈ t then g k else 0) (d := 0) hj hjS
    (fun k hk => by simp [show k ∉ t from fun h => hk (hts h)]) (fun _ _ => rfl)
    (by simp [ite_smul, Finset.sum_ite_mem, hg])
  simpa [hi] using congrFun hb i

/-- The cone of a set of indices that misses an index `j` with `aⱼ ≠ 0` is strongly convex. -/
theorem eq_zero_of_mem_indexCone (h : IsCircuit v a) {S : Set ι} {j : ι} (hj : a j ≠ 0)
    (hjS : j ∉ S) {x : E} (hx : x ∈ indexCone v S) (hnx : -x ∈ indexCone v S) : x = 0 := by
  obtain ⟨c, hc, hcS, rfl⟩ := mem_indexCone.mp hx
  obtain ⟨d, hd, hdS, hdx⟩ := mem_indexCone.mp hnx
  have hcd : (fun i => c i + d i) = fun _ => (0 : ℝ) :=
    h.eq_of_sum_eq hj hjS (fun i hi => by simp [hcS i hi, hdS i hi]) (fun _ _ => rfl)
      (by simp [add_smul, Finset.sum_add_distrib, hdx])
  have hc0 : ∀ i, c i = 0 := fun i => by
    have h1 : c i + d i = 0 := congrFun hcd i
    linarith [hc i, hd i]
  simp [hc0]

/-- Let `S` miss an index `j` with `aⱼ ≠ 0`. For `T ⊆ S`, the cone of `T` is a face of the cone of `S`. -/
theorem indexCone_isFaceOf (h : IsCircuit v a) {S T : Set ι} {j : ι} (hj : a j ≠ 0)
    (hjS : j ∉ S) (hTS : T ⊆ S) : (indexCone v T).IsFaceOf (indexCone v S) := by
  refine ⟨indexCone_mono v hTS, fun {x y r} hx hy hr hxy => ?_⟩
  obtain ⟨c, hc, hcS, rfl⟩ := mem_indexCone.mp hx
  obtain ⟨d, hd, hdS, rfl⟩ := mem_indexCone.mp hy
  obtain ⟨e, -, heT, hexy⟩ := mem_indexCone.mp hxy
  have hce : (fun i => r * c i + d i) = e :=
    h.eq_of_sum_eq hj hjS (fun i hi => by simp [hcS i hi, hdS i hi])
      (fun i hi => heT i fun hiT => hi (hTS hiT))
      (by
        rw [hexy]
        simp only [add_smul, Finset.sum_add_distrib, mul_smul, Finset.smul_sum])
  refine mem_indexCone.mpr ⟨c, hc, fun i hi => ?_, rfl⟩
  have h1 : r * c i + d i = e i := congrFun hce i
  rw [heT i hi] at h1
  have h2 := mul_nonneg hr.le (hc i)
  have h3 := hd i
  have h4 : r * c i = 0 := by linarith
  rcases mul_eq_zero.mp h4 with h5 | h5
  · exact absurd h5 hr.ne'
  · exact h5

/-- Let `S` miss an index `j` of `J₊` and `T` miss an index `k` of `J₊`. Then the cones of `S` and `T` meet in the cone of `S ∩ T`. This is the intersection property of the triangulation of the circuit by the cones `cone(v_{≠ j})`, `j ∈ J₊`. -/
theorem indexCone_inf (h : IsCircuit v a) {S T : Set ι} {j k : ι} (hj : 0 < a j) (hjS : j ∉ S)
    (hk : 0 < a k) (hkT : k ∉ T) : indexCone v S ⊓ indexCone v T = indexCone v (S ∩ T) := by
  refine le_antisymm (fun x hx => ?_)
    (le_inf (indexCone_mono v Set.inter_subset_left) (indexCone_mono v Set.inter_subset_right))
  obtain ⟨c, hc, hcS, hcx⟩ := mem_indexCone.mp (Submodule.mem_inf.mp hx).1
  obtain ⟨d, hd, hdT, hdx⟩ := mem_indexCone.mp (Submodule.mem_inf.mp hx).2
  obtain ⟨s, hs⟩ := h.2 (c - d) (by simp [sub_smul, Finset.sum_sub_distrib, hcx, hdx])
  have hsj : c j - d j = s * a j := by simpa using congrFun hs j
  have hsk : c k - d k = s * a k := by simpa using congrFun hs k
  rw [hcS j hjS] at hsj
  rw [hdT k hkT] at hsk
  have h3 : s ≤ 0 := by
    by_contra hpos
    have := mul_pos (not_le.mp hpos) hj
    linarith [hd j]
  have h4 : 0 ≤ s := by
    by_contra hneg
    have := mul_neg_of_neg_of_pos (not_le.mp hneg) hk
    linarith [hc k]
  have hs0 : s = 0 := le_antisymm h3 h4
  have hcd : c = d := by
    funext i
    have hi : c i - d i = s * a i := by simpa using congrFun hs i
    rw [hs0, zero_mul] at hi
    exact sub_eq_zero.mp hi
  refine mem_indexCone.mpr ⟨c, hc, fun i hi => ?_, hcx⟩
  rw [Set.mem_inter_iff, not_and_or] at hi
  rcases hi with hiS | hiT
  · exact hcS i hiS
  · rw [hcd]
    exact hdT i hiT

/-- Let `J₊` be nonempty. Each point of the cone of all the `vᵢ` is in a cone `cone(v_{≠ j})` with `j ∈ J₊`. The index `j` is one where `cᵢ / aᵢ` is least on `J₊`, for the coefficients `c` of the point (the argument of Carathéodory's theorem). -/
theorem exists_mem_indexCone_compl (h : IsCircuit v a) {j₀ : ι} (hj₀ : 0 < a j₀) {x : E}
    (hx : x ∈ indexCone v Set.univ) : ∃ j, 0 < a j ∧ x ∈ indexCone v {j}ᶜ := by
  obtain ⟨c, hc, -, rfl⟩ := mem_indexCone.mp hx
  obtain ⟨j, hj, hmin⟩ := Set.exists_min_image {i | 0 < a i} (fun i => c i / a i)
    (Set.toFinite _) ⟨j₀, hj₀⟩
  have hja : 0 < a j := hj
  have ht0 : 0 ≤ c j / a j := div_nonneg (hc j) hja.le
  refine ⟨j, hja, mem_indexCone.mpr ⟨fun i => c i - c j / a j * a i, fun i => ?_, fun i hi => ?_, ?_⟩⟩
  · show 0 ≤ c i - c j / a j * a i
    by_cases hai : 0 < a i
    · have h1 : c j / a j ≤ c i / a i := hmin i hai
      have h2 := (le_div_iff₀ hai).mp h1
      linarith
    · have h1 : c j / a j * a i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht0 (not_lt.mp hai)
      linarith [hc i]
  · have hij : i = j := by simpa using hi
    show c i - c j / a j * a i = 0
    rw [hij, div_mul_cancel₀ _ hja.ne', sub_self]
  · simp only [sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, h.1, smul_zero,
      sub_zero]

end IsCircuit

end IndexCone

/-- A circuit of lattice points: a finite family `u` of lattice points with a relation `∑ aᵢ uᵢ = 0` such that each linear relation of the `uᵢ` is a multiple of `a`. The wall relation of two simplicial maximal cones that meet in a wall is a circuit (step 2 of the module docstring). -/
structure Circuit (ι : Type*) [Fintype ι] (n : ℕ) where
  /-- The lattice points. -/
  u : ι → Fin n → ℤ
  /-- The coefficients of the relation. -/
  a : ι → ℝ
  /-- The relation is a circuit relation. -/
  isCircuit : IsCircuit (fun i => toNR (u i)) a

namespace Circuit

variable {ι : Type*} [Fintype ι] (C : Circuit ι n)

/-- The set `J₊` of the indices with a positive coefficient. -/
def jPlus : Set ι := {i | 0 < C.a i}

/-- The set `J₋` of the indices with a negative coefficient. -/
def jMinus : Set ι := {i | C.a i < 0}

/-- The set `J₀` of the indices with the coefficient zero. -/
def jZero : Set ι := {i | C.a i = 0}

/-- Each index is in `J₊`, `J₋` or `J₀`. -/
theorem jPlus_union_jMinus_union_jZero : C.jPlus ∪ C.jMinus ∪ C.jZero = Set.univ := by
  ext i
  simp only [jPlus, jMinus, jZero, Set.mem_union, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  rcases lt_trichotomy (C.a i) 0 with h | h | h
  · exact Or.inl (Or.inr h)
  · exact Or.inr h
  · exact Or.inl (Or.inl h)

/-- The circuit with the opposite relation `-a`. -/
def neg : Circuit ι n where
  u := C.u
  a := -C.a
  isCircuit := C.isCircuit.neg

/-- The set `J₊` of the opposite circuit is `J₋`. -/
theorem jPlus_neg : C.neg.jPlus = C.jMinus := by
  ext i
  simp [jPlus, jMinus, neg]

/-- The set `J₋` of the opposite circuit is `J₊`. -/
theorem jMinus_neg : C.neg.jMinus = C.jPlus := by
  ext i
  simp [jPlus, jMinus, neg]

/-- The cone `cone(u_T)` of the points `uᵢ` with `i ∈ T`. -/
noncomputable def cone (T : Set ι) : PointedCone ℝ (NR n) :=
  indexCone (fun i => toNR (C.u i)) T

/-- The opposite circuit has the same cones. -/
@[simp]
theorem neg_cone (T : Set ι) : C.neg.cone T = C.cone T := rfl

/-- The cone of a set of indices is the cone of a finite set of lattice points, so it is rational polyhedral. -/
theorem cone_eq_latticeCone (T : Set ι) :
    C.cone T = latticeCone ((Set.toFinite T).toFinset.image C.u) := by
  rw [latticeCone_eq_hull, Finset.coe_image, Set.Finite.coe_toFinset, Set.image_image]
  rfl

/-- The cones of the circuit fan: the cones `cone(u_T)` such that `T` misses an index of `J₊`. -/
def cones : Set (PointedCone ℝ (NR n)) :=
  {σ | ∃ T : Set ι, ∃ j ∈ C.jPlus, j ∉ T ∧ σ = C.cone T}

/-- The fan of the circuit: the cones `cone(u_T)` such that `T` misses an index of `J₊`. Its maximal cones are the cones `cone(u_{≠ j})` with `j ∈ J₊`. The fan of the opposite circuit, `C.neg.fan`, has the maximal cones `cone(u_{≠ j})` with `j ∈ J₋`; it is the flip of `C.fan` (Reid 1983, Section 2). -/
noncomputable def fan : Fan n where
  cones := C.cones
  finite := (Set.finite_range C.cone).subset (by
    rintro _ ⟨T, -, -, -, rfl⟩
    exact ⟨T, rfl⟩)
  rational := by
    rintro _ ⟨T, -, -, -, rfl⟩
    exact ⟨_, C.cone_eq_latticeCone T⟩
  stronglyConvex := by
    rintro _ ⟨T, j, hj, hjT, rfl⟩ x hx hnx
    exact C.isCircuit.eq_zero_of_mem_indexCone (show 0 < C.a j from hj).ne' hjT hx hnx
  face_mem := by
    rintro _ ⟨T, j, hj, hjT, rfl⟩ τ hτ
    refine ⟨T ∩ (fun i => toNR (C.u i)) ⁻¹' (τ : Set (NR n)), j, hj, fun h => hjT h.1, ?_⟩
    refine (eq_hull_inter_of_isFaceOf (s := (fun i => toNR (C.u i)) '' T) hτ).trans ?_
    unfold Circuit.cone indexCone
    rw [Set.image_inter_preimage]
  inter_face := by
    rintro _ ⟨S, j, hj, hjS, rfl⟩ _ ⟨T, k, hk, hkT, rfl⟩
    have he : C.cone S ⊓ C.cone T = C.cone (S ∩ T) :=
      C.isCircuit.indexCone_inf (show 0 < C.a j from hj) hjS (show 0 < C.a k from hk) hkT
    rw [he]
    exact C.isCircuit.indexCone_isFaceOf (show 0 < C.a j from hj).ne' hjS Set.inter_subset_left

/-- A cone is in the circuit fan when it is a cone `cone(u_T)` with `T` missing an index of `J₊`. -/
theorem mem_fan_cones {σ : PointedCone ℝ (NR n)} :
    σ ∈ C.fan.cones ↔ ∃ T : Set ι, ∃ j ∈ C.jPlus, j ∉ T ∧ σ = C.cone T :=
  Iff.rfl

/-- The fan of a circuit is simplicial. -/
theorem isSimplicialFan_fan : C.fan.IsSimplicialFan := by
  rintro _ ⟨T, j, hj, hjT, rfl⟩
  refine ⟨_, C.cone_eq_latticeCone T, ?_⟩
  show LinearIndepOn ℝ toNR
    (((Set.toFinite T).toFinset.image C.u : Finset (Fin n → ℤ)) : Set (Fin n → ℤ))
  rw [Finset.coe_image, Set.Finite.coe_toFinset]
  exact (C.isCircuit.linearIndepOn (show 0 < C.a j from hj).ne' hjT).image_of_comp C.u toNR

/-- When `J₊` is not empty, the support of the fan of the circuit is the cone of all the `uᵢ`. -/
theorem support_fan {j₀ : ι} (hj₀ : j₀ ∈ C.jPlus) :
    C.fan.support = (C.cone Set.univ : Set (NR n)) := by
  ext x
  rw [Fan.mem_support]
  constructor
  · rintro ⟨_, ⟨T, -, -, -, rfl⟩, hx⟩
    exact indexCone_mono (fun i => toNR (C.u i)) (Set.subset_univ T) hx
  · intro hx
    obtain ⟨j, hj, hxj⟩ := C.isCircuit.exists_mem_indexCone_compl hj₀ hx
    exact ⟨C.cone {j}ᶜ, ⟨{j}ᶜ, j, hj, fun h => h (Set.mem_singleton j), rfl⟩, hxj⟩

/-- The flip of the fan of a circuit has the same support: when `J₊` and `J₋` are not empty, the fans `C.fan` and `C.neg.fan` both have the support `cone(u)`. -/
theorem support_neg_fan {j₀ k₀ : ι} (hj₀ : j₀ ∈ C.jPlus) (hk₀ : k₀ ∈ C.jMinus) :
    C.neg.fan.support = C.fan.support := by
  rw [C.support_fan hj₀, C.neg.support_fan (j₀ := k₀) (by rw [C.jPlus_neg]; exact hk₀), neg_cone]

/-- The flip of the fan of a circuit is simplicial. -/
theorem isSimplicialFan_neg_fan : C.neg.fan.IsSimplicialFan :=
  C.neg.isSimplicialFan_fan

end Circuit

end MinimalModel.Toric
