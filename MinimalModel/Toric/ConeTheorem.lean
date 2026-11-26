/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import MinimalModel.Toric.Cone

/-!
# The toric cone theorem

This file proves the toric cone theorem in combinatorial form (route R3, spec 04.4). On a complete simplicial fan, an R-Cartier divisor is nef exactly when its degree on each wall curve is nonnegative (Cox, Little and Schenck, Theorem 6.3.12 and Proposition 6.4.4).

The main step is that a support function on a complete fan is convex in the sense of Cox, Little and Schenck (`ConcaveOn` in Mathlib) exactly when it satisfies the wall inequality at each wall. The proof is the generic segment argument. Let `σ` be a cone of full dimension with linear form `m_σ`. To see `φ(x) ≤ m_σ(x)`, take a point `p` in the interior of `σ` that is generic: the segment from `p` to `x` meets no cone of dimension at most `n - 2`, except maybe at `x`. Along the segment, each point other than `x` lies only in cones of dimension at least `n - 1`. Near such a point, the wall inequality says that `φ` is at most a linear form that agrees with `φ` at the point. So `φ - m_σ` is locally concave on the segment, and hence concave. It vanishes near `p`, so it is at most zero at `x`.

## Main results

* `Fan.concaveOn_iff_forall_isConvexAcross`: on a complete fan with closed cones, a support function is convex exactly when it satisfies the wall inequality at each wall.
* `Fan.concaveOn_iff_forall_isConvexAcross_of_isSimplicialFan`: the same for a complete simplicial fan.
* `Fan.IsWallPair.nonempty_wallData`: two simplicial maximal cones that meet in a wall carry the data of a wall.
* `Fan.coneTheorem`: the toric cone theorem in combinatorial form.
-/

open Topology Filter

namespace MinimalModel.Toric

variable {n : ℕ}

/-! ### Dimension of cones -/

/-- The dimension of a cone is at most `n`. -/
theorem coneDim_le (σ : PointedCone ℝ (NR n)) : coneDim σ ≤ n := by
  unfold coneDim
  exact (Submodule.finrank_le _).trans_eq (Module.finrank_fin_fun ℝ)

/-- A cone of dimension `n` spans `N_ℝ`. -/
theorem span_eq_top_of_coneDim_eq {σ : PointedCone ℝ (NR n)} (h : coneDim σ = n) :
    Submodule.span ℝ (σ : Set (NR n)) = ⊤ :=
  Submodule.eq_top_of_finrank_eq (h.trans (Module.finrank_fin_fun ℝ).symm)

/-- The cone of a finite set `T` of lattice points has dimension at most the size of `T`. -/
theorem coneDim_latticeCone_le (T : Finset (Fin n → ℤ)) : coneDim (latticeCone T) ≤ T.card := by
  classical
  unfold coneDim latticeCone
  rw [Submodule.span_span_of_tower, ← Finset.coe_image]
  exact (finrank_span_finset_le_card _).trans Finset.card_image_le

/-- A face `τ` of a cone `σ` with the same linear span is `σ`. -/
theorem le_of_isFaceOf_of_span_le {τ σ : PointedCone ℝ (NR n)} (h : τ.IsFaceOf σ)
    (hs : Submodule.span ℝ (σ : Set (NR n)) ≤ Submodule.span ℝ (τ : Set (NR n))) : σ ≤ τ := by
  intro x hx
  obtain ⟨p, hp, q, hq, hxpq⟩ := PointedCone.mem_span.mp (hs (Submodule.subset_span hx))
  refine h.mem_of_smul_add_mem hx (h.le hq) one_pos ?_
  rw [one_smul, hxpq, sub_add_cancel]
  exact hp

/-- A simplicial cone is closed. It is the image of the nonnegative orthant under an injective linear map. -/
theorem IsSimplicial.isClosed {σ : PointedCone ℝ (NR n)} (h : IsSimplicial σ) :
    IsClosed (σ : Set (NR n)) := by
  obtain ⟨S, rfl, hS⟩ := h
  have hf : Topology.IsClosedEmbedding
      (Fintype.linearCombination ℝ (fun v : (S : Set (Fin n → ℤ)) => toNR v.1)) :=
    LinearMap.isClosedEmbedding_of_injective
      (LinearMap.ker_eq_bot.mpr hS.fintypeLinearCombination_injective)
  have h1 : latticeCone S = familyCone (fun v : (S : Set (Fin n → ℤ)) => v.1) := by
    unfold latticeCone familyCone
    rw [Set.image_eq_range]
  have heq : (latticeCone S : Set (NR n)) =
      Fintype.linearCombination ℝ (fun v : (S : Set (Fin n → ℤ)) => toNR v.1) ''
        {c | ∀ i, 0 ≤ c i} := by
    ext x
    rw [SetLike.mem_coe, h1, mem_familyCone]
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c, hc, by rw [Fintype.linearCombination_apply]⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c, hc, by rw [Fintype.linearCombination_apply]⟩
  have hcl : IsClosed {c : ↥(S : Set (Fin n → ℤ)) → ℝ | ∀ i, 0 ≤ c i} := by
    rw [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  rw [heq]
  exact hf.isClosedMap _ hcl

/-! ### Generic points -/

/-- In `N_ℝ`, a nonempty open set contains a point outside finitely many proper subspaces. -/
theorem exists_forall_notMem {ι : Type*} (W : ι → Submodule ℝ (NR n)) (s : Finset ι) :
    ∀ U : Set (NR n), IsOpen U → U.Nonempty → (∀ i ∈ s, W i ≠ ⊤) →
      ∃ p ∈ U, ∀ i ∈ s, p ∉ W i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro U _ hU _
    obtain ⟨p, hp⟩ := hU
    exact ⟨p, hp, fun i hi => absurd hi (Finset.notMem_empty i)⟩
  | insert i s _ ih =>
    intro U hU1 hU2 hW
    have hne : (U ∩ (W i : Set (NR n))ᶜ).Nonempty := by
      by_contra hne
      apply hW i (Finset.mem_insert_self i s)
      refine Submodule.eq_top_of_nonempty_interior' _ (hU2.mono (interior_maximal ?_ hU1))
      intro y hy
      by_contra hy'
      exact hne ⟨y, hy, hy'⟩
    obtain ⟨p, ⟨hpU, hpW⟩, hp⟩ := ih (U ∩ (W i : Set (NR n))ᶜ)
      (hU1.inter (Submodule.closed_of_finiteDimensional (W i)).isOpen_compl) hne
      (fun j hj => hW j (Finset.mem_insert_of_mem hj))
    refine ⟨p, hpU, fun j hj => ?_⟩
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hpW
    · exact hp j hj

/-! ### A local criterion for concavity on a segment -/

/-- A function on `[0, 1]` that is continuous and locally concave at each interior point lies above its chord. -/
theorem chord_le_of_local {g : ℝ → ℝ} (hg : ContinuousOn g (Set.Icc 0 1))
    (hloc : ∀ s ∈ Set.Ioo (0 : ℝ) 1, ∀ᶠ ε in 𝓝 (0 : ℝ), g (s - ε) + g (s + ε) ≤ 2 * g s)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : (1 - t) * g 0 + t * g 1 ≤ g t := by
  obtain ⟨d, hd⟩ : ∃ d : ℝ → ℝ, ∀ s, d s = g s - ((1 - s) * g 0 + s * g 1) :=
    ⟨_, fun _ => rfl⟩
  have hdc : ContinuousOn d (Set.Icc 0 1) := by
    rw [show d = fun s => g s - ((1 - s) * g 0 + s * g 1) from funext hd]
    exact hg.sub (by fun_prop : Continuous fun s : ℝ => (1 - s) * g 0 + s * g 1).continuousOn
  have hd0 : d 0 = 0 := by rw [hd]; ring
  have hd1 : d 1 = 0 := by rw [hd]; ring
  obtain ⟨s0, hs0, hmin⟩ :=
    isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.mpr zero_le_one) hdc
  have hmin' : ∀ y ∈ Set.Icc (0 : ℝ) 1, d s0 ≤ d y := isMinOn_iff.mp hmin
  by_contra hlt
  push Not at hlt
  have hμ : d s0 < 0 := by
    have := hmin' t ht
    rw [hd t] at this
    linarith
  have hS : IsClosed (Set.Icc (0 : ℝ) 1 ∩ d ⁻¹' {d s0}) :=
    hdc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  obtain ⟨s1, hS1, hleast⟩ :=
    (isCompact_Icc.of_isClosed_subset hS Set.inter_subset_left).exists_isLeast
      ⟨s0, hs0, Set.mem_singleton _⟩
  obtain ⟨⟨hs1a, hs1b⟩, hs1d⟩ := hS1
  have hs1d' : d s1 = d s0 := hs1d
  have hs1 : s1 ∈ Set.Ioo (0 : ℝ) 1 := by
    refine ⟨lt_of_le_of_ne hs1a fun h => ?_, lt_of_le_of_ne hs1b fun h => ?_⟩
    · rw [← h] at hs1d'
      linarith
    · rw [h] at hs1d'
      linarith
  obtain ⟨ε, hε, h1, h2, h3⟩ := ((eventually_mem_nhdsWithin (s := Set.Ioi (0 : ℝ)) (a := 0)).and
    (((hloc s1 hs1).and ((eventually_lt_nhds hs1.1).and
      (eventually_lt_nhds (sub_pos.mpr hs1.2)))).filter_mono nhdsWithin_le_nhds)).exists
  have hε' : 0 < ε := hε
  have hm1 : s1 - ε ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hm2 : s1 + ε ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hlt1 : d s0 < d (s1 - ε) := by
    refine lt_of_le_of_ne (hmin' _ hm1) fun h => ?_
    have := hleast ⟨hm1, h.symm⟩
    linarith
  have hle2 := hmin' _ hm2
  have key : d (s1 - ε) + d (s1 + ε) - 2 * d s1 = g (s1 - ε) + g (s1 + ε) - 2 * g s1 := by
    rw [hd, hd, hd]
    ring
  linarith

namespace Fan

variable {F : Fan n} {σ σ' : PointedCone ℝ (NR n)} {φ : NR n → ℝ}

/-! ### Maximal cones and walls -/

/-- A maximal cone is a cone of the fan. -/
theorem IsMaximalCone.mem (h : F.IsMaximalCone σ) : σ ∈ F.cones :=
  Maximal.prop h

/-- A cone of the fan that contains a maximal cone is the maximal cone. -/
theorem IsMaximalCone.le_of_le (h : F.IsMaximalCone σ) {τ : PointedCone ℝ (NR n)}
    (hτ : τ ∈ F.cones) (hle : σ ≤ τ) : τ ≤ σ :=
  Maximal.le_of_ge h hτ hle

variable (F) in
/-- Each cone of the fan lies in a maximal cone. -/
theorem exists_le_isMaximalCone (hσ : σ ∈ F.cones) : ∃ τ, σ ≤ τ ∧ F.IsMaximalCone τ :=
  F.finite.exists_le_maximal hσ

/-- On a complete fan, each vector lies in a cone of the fan. -/
theorem exists_mem_of_isComplete (hc : F.IsComplete) (x : NR n) : ∃ σ ∈ F.cones, x ∈ σ :=
  F.mem_support.mp (by rw [show F.support = Set.univ from hc]; exact Set.mem_univ x)

/-- Two different maximal cones meet in a cone of smaller dimension. -/
theorem IsMaximalCone.coneDim_inf_lt (h : F.IsMaximalCone σ) (h' : F.IsMaximalCone σ')
    (hne : σ ≠ σ') : coneDim (σ ⊓ σ') < coneDim σ := by
  unfold coneDim
  apply Submodule.finrank_lt_finrank_of_lt
  refine lt_of_le_of_ne (Submodule.span_mono (SetLike.coe_subset_coe.mpr inf_le_left))
    fun heq => hne ?_
  have hle := le_of_isFaceOf_of_span_le (F.inter_face σ h.mem σ' h'.mem) heq.ge
  have hle' : σ ≤ σ' := hle.trans inf_le_right
  exact le_antisymm hle' (h.le_of_le h'.mem hle')

/-- The first cone of a wall pair has dimension `n`. -/
theorem IsWallPair.coneDim_eq (hw : F.IsWallPair σ σ') : coneDim σ = n := by
  obtain ⟨h, h', hne, hdim⟩ := hw
  have h1 := h.coneDim_inf_lt h' hne
  have h2 := coneDim_le σ
  omega

/-- The first cone of a wall pair spans `N_ℝ`. -/
theorem IsWallPair.span_eq_top (hw : F.IsWallPair σ σ') :
    Submodule.span ℝ (σ : Set (NR n)) = ⊤ :=
  span_eq_top_of_coneDim_eq hw.coneDim_eq

/-- The first cone of a wall pair is maximal. -/
theorem IsWallPair.isMaximalCone_left (hw : F.IsWallPair σ σ') : F.IsMaximalCone σ := by
  obtain ⟨h, -, -, -⟩ := hw
  exact h

/-- The second cone of a wall pair is maximal. -/
theorem IsWallPair.isMaximalCone_right (hw : F.IsWallPair σ σ') : F.IsMaximalCone σ' := by
  obtain ⟨-, h, -, -⟩ := hw
  exact h

/-! ### Support functions -/

/-- On a complete fan, a support function is positively homogeneous. -/
theorem IsSupportFunction.apply_smul (hc : F.IsComplete) (hφ : F.IsSupportFunction φ)
    (x : NR n) {t : ℝ} (ht : 0 ≤ t) : φ (t • x) = t * φ x := by
  obtain ⟨C, hC, hx⟩ := exists_mem_of_isComplete hc x
  obtain ⟨m, hm⟩ := hφ C hC
  rw [hm _ (PointedCone.smul_mem C ht hx), hm x hx, map_smul, smul_eq_mul]

/-- On a complete fan, a convex support function is superadditive. -/
theorem IsSupportFunction.add_le (hc : F.IsComplete) (hφ : F.IsSupportFunction φ)
    (hcc : ConcaveOn ℝ Set.univ φ) (x y : NR n) : φ x + φ y ≤ φ (x + y) := by
  have h := hcc.2 (Set.mem_univ ((2 : ℝ) • x)) (Set.mem_univ ((2 : ℝ) • y))
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  rw [show (1 / 2 : ℝ) • ((2 : ℝ) • x) + (1 / 2 : ℝ) • ((2 : ℝ) • y) = x + y by module,
    hφ.apply_smul hc x (t := 2) (by norm_num), hφ.apply_smul hc y (t := 2) (by norm_num),
    smul_eq_mul, smul_eq_mul] at h
  linarith

/-- On a complete fan with closed cones, a support function is continuous. -/
theorem IsSupportFunction.continuous (hc : F.IsComplete)
    (hcl : ∀ σ ∈ F.cones, IsClosed (σ : Set (NR n))) (hφ : F.IsSupportFunction φ) :
    Continuous φ := by
  have := F.finite.to_subtype
  refine LocallyFinite.continuous (f := fun C : F.cones => (C.1 : Set (NR n)))
    (locallyFinite_of_finite _) ?_ (fun C => hcl C.1 C.2) fun C => ?_
  · refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨C, hC, hx⟩ := exists_mem_of_isComplete hc x
    exact Set.mem_iUnion.mpr ⟨⟨C, hC⟩, hx⟩
  · obtain ⟨m, hm⟩ := hφ C.1 C.2
    exact (LinearMap.continuous_of_finiteDimensional m).continuousOn.congr fun x hx => hm x hx

/-! ### Part 1: convexity and the wall inequality -/

/-- On a complete fan, a convex support function satisfies the wall inequality at each wall. -/
theorem isConvexAcross_of_concaveOn (hc : F.IsComplete) (hφ : F.IsSupportFunction φ)
    (hcc : ConcaveOn ℝ Set.univ φ) (hw : F.IsWallPair σ σ') : IsConvexAcross φ σ σ' := by
  intro m hm x _
  have hx : x ∈ Submodule.span ℝ (σ : Set (NR n)) := by
    rw [hw.span_eq_top]
    exact Submodule.mem_top
  obtain ⟨p, hp, q, hq, rfl⟩ := PointedCone.mem_span.mp hx
  have h := hφ.add_le hc hcc (p - q) q
  rw [sub_add_cancel] at h
  rw [map_sub, ← hm p hp, ← hm q hq]
  linarith

/-- Near a generic point `q`, one that lies only in cones of dimension at least `n - 1`, the wall inequality gives a linear form that agrees with `φ` at `q` and is at least `φ` near `q`. -/
theorem exists_local (hc : F.IsComplete) (hcl : ∀ σ ∈ F.cones, IsClosed (σ : Set (NR n)))
    (hφ : F.IsSupportFunction φ)
    (hwall : ∀ σ σ', F.IsWallPair σ σ' → IsConvexAcross φ σ σ') {q : NR n}
    (hq : ∀ C ∈ F.cones, q ∈ C → n ≤ coneDim C + 1) :
    ∃ m' : NR n →ₗ[ℝ] ℝ, φ q = m' q ∧ ∀ᶠ w in 𝓝 q, φ w ≤ m' w := by
  obtain ⟨C0, hC0, hqC0⟩ := exists_mem_of_isComplete hc q
  obtain ⟨σ0, hle0, hmax0⟩ := F.exists_le_isMaximalCone hC0
  obtain ⟨m', hm'⟩ := hφ σ0 hmax0.mem
  refine ⟨m', hm' q (hle0 hqC0), ?_⟩
  have hK : IsClosed (⋃ C ∈ {C ∈ F.cones | q ∉ C}, (C : Set (NR n))) :=
    (F.finite.subset (Set.sep_subset _ _)).isClosed_biUnion fun C hC => hcl C hC.1
  have hqK : q ∉ ⋃ C ∈ {C ∈ F.cones | q ∉ C}, (C : Set (NR n)) := by
    intro h
    obtain ⟨C, hC, hqC⟩ := Set.mem_iUnion₂.mp h
    exact hC.2 hqC
  filter_upwards [hK.isOpen_compl.mem_nhds hqK] with w hw
  obtain ⟨C, hC, hwC⟩ := exists_mem_of_isComplete hc w
  have hqC : q ∈ C := by
    by_contra hqC
    exact hw (Set.mem_iUnion₂.mpr ⟨C, ⟨hC, hqC⟩, hwC⟩)
  obtain ⟨σ1, hle1, hmax1⟩ := F.exists_le_isMaximalCone hC
  by_cases h01 : σ0 = σ1
  · subst h01
    exact (hm' w (hle1 hwC)).le
  · have hlow := hq (σ0 ⊓ σ1) (F.inf_mem hmax0.mem hmax1.mem)
      (Submodule.mem_inf.mpr ⟨hle0 hqC0, hle1 hqC⟩)
    have hlt := hmax0.coneDim_inf_lt hmax1 h01
    have hn := coneDim_le σ0
    have hwp : F.IsWallPair σ0 σ1 := ⟨hmax0, hmax1, h01, by omega⟩
    exact hwall σ0 σ1 hwp m' hm' w (hle1 hwC)

/-- If `φ` satisfies the wall inequality at each wall, then `φ ≤ m_σ` everywhere, for each cone `σ` of full dimension and the linear form `m_σ` of `φ` on `σ`. This is the generic segment argument. -/
theorem le_of_span_eq_top (hc : F.IsComplete) (hcl : ∀ σ ∈ F.cones, IsClosed (σ : Set (NR n)))
    (hφ : F.IsSupportFunction φ)
    (hwall : ∀ σ σ', F.IsWallPair σ σ' → IsConvexAcross φ σ σ')
    (hspan : Submodule.span ℝ (σ : Set (NR n)) = ⊤)
    {m : NR n →ₗ[ℝ] ℝ} (hm : ∀ x ∈ σ, φ x = m x) (x : NR n) : φ x ≤ m x := by
  classical
  obtain ⟨L, hL⟩ : ∃ L : Finset (PointedCone ℝ (NR n)),
      ∀ C, C ∈ L ↔ C ∈ F.cones ∧ coneDim C + 2 ≤ n :=
    ⟨F.finite.toFinset.filter fun C => coneDim C + 2 ≤ n, fun C => by
      rw [Finset.mem_filter, Set.Finite.mem_toFinset]⟩
  let W : PointedCone ℝ (NR n) → Submodule ℝ (NR n) := fun C =>
    Submodule.span ℝ (C : Set (NR n)) ⊔ Submodule.span ℝ {x}
  have hW : ∀ C ∈ L, W C ≠ ⊤ := by
    intro C hC htop
    have h1 := Submodule.finrank_add_le_finrank_add_finrank
      (Submodule.span ℝ (C : Set (NR n))) (Submodule.span ℝ {x})
    have h2 : Module.finrank ℝ (Submodule.span ℝ ({x} : Set (NR n))) ≤ 1 :=
      (finrank_span_le_card ({x} : Set (NR n))).trans (by simp)
    have h3 : Module.finrank ℝ (W C) = n := by
      rw [htop, finrank_top, Module.finrank_fin_fun ℝ]
    have h4 := ((hL C).mp hC).2
    change Module.finrank ℝ (W C) ≤ coneDim C + _ at h1
    omega
  have hint : (interior (σ : Set (NR n))).Nonempty := by
    rw [(PointedCone.convex σ).interior_nonempty_iff_affineSpan_eq_top,
      AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty (k := ℝ) (V := NR n) (P := NR n)
        ⟨0, σ.zero_mem⟩, vectorSpan_eq_span_vsub_set_right ℝ (SetLike.mem_coe.mpr σ.zero_mem)]
    simpa using hspan
  obtain ⟨p, hp, hpW⟩ := exists_forall_notMem W L _ isOpen_interior hint hW
  have hpσ : p ∈ σ := interior_subset hp
  -- the points of the segment other than `x` are generic
  have hgen : ∀ t : ℝ, t < 1 → ∀ C ∈ F.cones, p + t • (x - p) ∈ C → n ≤ coneDim C + 1 := by
    intro t ht C hC hqC
    by_contra hlow
    have hCL : C ∈ L := (hL C).mpr ⟨hC, by omega⟩
    apply hpW C hCL
    have hmem : p + t • (x - p) - t • x ∈ W C :=
      sub_mem (Submodule.mem_sup_left (Submodule.subset_span hqC))
        (Submodule.smul_mem _ _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)))
    have heq : p = (1 - t)⁻¹ • (p + t • (x - p) - t • x) := by
      rw [show p + t • (x - p) - t • x = (1 - t) • p by module,
        inv_smul_smul₀ (sub_ne_zero.mpr ht.ne')]
    rw [heq]
    exact Submodule.smul_mem _ _ hmem
  have hγ : Continuous fun s : ℝ => p + s • (x - p) := by fun_prop
  have hmc : Continuous m := LinearMap.continuous_of_finiteDimensional m
  have hφc := hφ.continuous hc hcl
  have hloc : ∀ s ∈ Set.Ioo (0 : ℝ) 1, ∀ᶠ ε in 𝓝 (0 : ℝ),
      (φ (p + (s - ε) • (x - p)) - m (p + (s - ε) • (x - p))) +
        (φ (p + (s + ε) • (x - p)) - m (p + (s + ε) • (x - p))) ≤
      2 * (φ (p + s • (x - p)) - m (p + s • (x - p))) := by
    intro s hs
    obtain ⟨m', hm'q, hm'⟩ := exists_local hc hcl hφ hwall (hgen s hs.2)
    have t1 : Tendsto (fun ε : ℝ => p + (s - ε) • (x - p)) (𝓝 0) (𝓝 (p + s • (x - p))) :=
      (by fun_prop : Continuous fun ε : ℝ => p + (s - ε) • (x - p)).tendsto' 0 _ (by simp)
    have t2 : Tendsto (fun ε : ℝ => p + (s + ε) • (x - p)) (𝓝 0) (𝓝 (p + s • (x - p))) :=
      (by fun_prop : Continuous fun ε : ℝ => p + (s + ε) • (x - p)).tendsto' 0 _ (by simp)
    filter_upwards [t1.eventually hm', t2.eventually hm'] with ε h1 h2
    have hab : (p + (s - ε) • (x - p)) + (p + (s + ε) • (x - p)) =
        (2 : ℝ) • (p + s • (x - p)) := by module
    have e1 := congrArg m' hab
    have e2 := congrArg m hab
    rw [map_add, map_smul, smul_eq_mul] at e1 e2
    linarith
  have hchord := fun t (ht : t ∈ Set.Icc (0 : ℝ) 1) =>
    chord_le_of_local (g := fun s => φ (p + s • (x - p)) - m (p + s • (x - p)))
      ((hφc.comp hγ).sub (hmc.comp hγ)).continuousOn hloc ht
  -- near `0`, the segment is in `σ`
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), p + t • (x - p) ∈ interior (σ : Set (NR n)) :=
    (hγ.tendsto' 0 p (by simp)).eventually (isOpen_interior.mem_nhds hp)
  obtain ⟨t, ht0, ht1, htσ⟩ := ((eventually_mem_nhdsWithin (s := Set.Ioi (0 : ℝ)) (a := 0)).and
    (((eventually_lt_nhds (zero_lt_one' ℝ)).and hnear).filter_mono nhdsWithin_le_nhds)).exists
  have ht0' : (0 : ℝ) < t := ht0
  have h := hchord t ⟨ht0'.le, ht1.le⟩
  have e0 : p + (0 : ℝ) • (x - p) = p := by simp
  have e1 : p + (1 : ℝ) • (x - p) = x := by simp
  simp only [e0, e1] at h
  rw [hm p hpσ, hm _ (interior_subset htσ)] at h
  simp only [sub_self, mul_zero, zero_add] at h
  by_contra hpos
  push Not at hpos
  have := mul_pos ht0' (sub_pos.mpr hpos)
  linarith

/-- On a complete fan with closed cones, each vector lies in a cone of dimension `n`. -/
theorem exists_mem_coneDim_eq (hc : F.IsComplete)
    (hcl : ∀ σ ∈ F.cones, IsClosed (σ : Set (NR n))) (x : NR n) :
    ∃ C ∈ F.cones, coneDim C = n ∧ x ∈ C := by
  classical
  by_contra hno
  push Not at hno
  have hK : IsClosed (⋃ C ∈ {C ∈ F.cones | coneDim C = n}, (C : Set (NR n))) :=
    (F.finite.subset (Set.sep_subset _ _)).isClosed_biUnion fun C hC => hcl C hC.1
  have hxK : x ∉ ⋃ C ∈ {C ∈ F.cones | coneDim C = n}, (C : Set (NR n)) := by
    intro h
    obtain ⟨C, hC, hxC⟩ := Set.mem_iUnion₂.mp h
    exact hno C hC.1 hC.2 hxC
  obtain ⟨L, hL⟩ : ∃ L : Finset (PointedCone ℝ (NR n)), ∀ C, C ∈ L ↔ C ∈ F.cones ∧ coneDim C ≠ n :=
    ⟨F.finite.toFinset.filter fun C => coneDim C ≠ n, fun C => by
      rw [Finset.mem_filter, Set.Finite.mem_toFinset]⟩
  have hW : ∀ C ∈ L, Submodule.span ℝ (C : Set (NR n)) ≠ ⊤ := by
    intro C hC htop
    apply ((hL C).mp hC).2
    change Module.finrank ℝ (Submodule.span ℝ (C : Set (NR n))) = n
    rw [htop, finrank_top, Module.finrank_fin_fun ℝ]
  obtain ⟨p, hpK, hp⟩ := exists_forall_notMem (fun C : PointedCone ℝ (NR n) => Submodule.span ℝ (C : Set (NR n))) L
    _ hK.isOpen_compl ⟨x, hxK⟩ hW
  obtain ⟨C, hC, hpC⟩ := exists_mem_of_isComplete hc p
  by_cases hdim : coneDim C = n
  · exact hpK (Set.mem_iUnion₂.mpr ⟨C, ⟨hC, hdim⟩, hpC⟩)
  · exact hp C ((hL C).mpr ⟨hC, hdim⟩) (Submodule.subset_span hpC)

/-- **Part 1.** On a complete fan whose cones are closed, a support function `φ` is convex in the sense of Cox, Little and Schenck (`ConcaveOn` in Mathlib) exactly when it satisfies the wall inequality at each wall (Cox, Little and Schenck, Sections 6.1 and 6.4). The proof is the generic segment argument of the module docstring. -/
theorem concaveOn_iff_forall_isConvexAcross (hc : F.IsComplete)
    (hcl : ∀ σ ∈ F.cones, IsClosed (σ : Set (NR n))) (hφ : F.IsSupportFunction φ) :
    ConcaveOn ℝ Set.univ φ ↔ ∀ σ σ', F.IsWallPair σ σ' → IsConvexAcross φ σ σ' := by
  refine ⟨fun hcc σ σ' hw => isConvexAcross_of_concaveOn hc hφ hcc hw, fun hwall => ?_⟩
  refine ⟨convex_univ, fun x _ y _ a b ha hb _ => ?_⟩
  obtain ⟨C, hC, hdim, hz⟩ := exists_mem_coneDim_eq hc hcl (a • x + b • y)
  obtain ⟨m, hm⟩ := hφ C hC
  have hle := le_of_span_eq_top hc hcl hφ hwall (span_eq_top_of_coneDim_eq hdim) hm
  rw [hm _ hz, map_add, map_smul, map_smul]
  exact add_le_add (smul_le_smul_of_nonneg_left (hle x) ha)
    (smul_le_smul_of_nonneg_left (hle y) hb)

/-- **Part 1** for a complete simplicial fan: a support function is convex exactly when it satisfies the wall inequality at each wall. -/
theorem concaveOn_iff_forall_isConvexAcross_of_isSimplicialFan (hc : F.IsComplete)
    (hs : F.IsSimplicialFan) (hφ : F.IsSupportFunction φ) :
    ConcaveOn ℝ Set.univ φ ↔ ∀ σ σ', F.IsWallPair σ σ' → IsConvexAcross φ σ σ' :=
  concaveOn_iff_forall_isConvexAcross hc (fun σ hσ => (hs σ hσ).isClosed) hφ

/-! ### The data of a wall -/

/-- A ray of the fan that shares a nonzero vector with a second ray is contained in it. -/
theorem ray_le_of_mem {ρ₁ ρ₂ : F.Ray} {y : NR n} (h₁ : y ∈ ρ₁.1) (h₂ : y ∈ ρ₂.1) (hy : y ≠ 0) :
    ρ₁.1 ≤ ρ₂.1 := by
  have hface : (ρ₁.1 ⊓ ρ₂.1).IsFaceOf (latticeCone {F.generator ρ₁}) := by
    rw [F.latticeCone_generator]
    exact F.inter_face _ ρ₁.2.1 _ ρ₂.2.1
  rcases eq_bot_or_eq_of_isFaceOf_latticeCone_singleton hface with h | h
  · have hy' : y ∈ ρ₁.1 ⊓ ρ₂.1 := Submodule.mem_inf.mpr ⟨h₁, h₂⟩
    rw [h] at hy'
    exact absurd ((Submodule.mem_bot _).mp hy') hy
  · rw [F.latticeCone_generator] at h
    exact inf_eq_left.mp h

/-- Two rays of the fan that share a nonzero vector are equal. -/
theorem ray_eq_of_mem {ρ₁ ρ₂ : F.Ray} {y : NR n} (h₁ : y ∈ ρ₁.1) (h₂ : y ∈ ρ₂.1) (hy : y ≠ 0) :
    ρ₁ = ρ₂ :=
  Subtype.ext (le_antisymm (ray_le_of_mem h₁ h₂ hy) (ray_le_of_mem h₂ h₁ hy))

/-- Two simplicial maximal cones `σ` and `σ'` that meet in a wall carry the data of a wall: one ray of `σ'` is not in `σ`, and its generator is a combination of the generators of the rays of `σ`, since `σ` spans `N_ℝ`. -/
theorem IsWallPair.nonempty_wallData (hs : F.IsSimplicialFan) (hw : F.IsWallPair σ σ') :
    Nonempty (F.WallData σ σ') := by
  classical
  have hspan := hw.span_eq_top
  obtain ⟨hmax, hmax', hne, hdim⟩ := hw
  obtain ⟨ρ0, hρ0, hρ0'⟩ : ∃ ρ : F.Ray, ρ.1 ≤ σ' ∧ ¬ ρ.1 ≤ σ := by
    by_contra h
    push Not at h
    apply hne
    have hle : σ' ≤ σ := by
      refine (F.eq_hull_generator hmax'.mem).le.trans (Submodule.span_le.mpr ?_)
      rintro _ ⟨ρ, hρ, rfl⟩
      exact h ρ hρ (F.toNR_generator_mem ρ)
    exact le_antisymm (hmax'.le_of_le hmax.mem hle) hle
  -- the coefficients
  let v : {ρ : F.Ray // ρ.1 ≤ σ} → NR n := fun ρ => toNR (F.generator ρ.1)
  have hrange : Set.range v = {x | ∃ ρ : F.Ray, ρ.1 ≤ σ ∧ toNR (F.generator ρ) = x} := by
    ext x
    constructor
    · rintro ⟨ρ, rfl⟩
      exact ⟨ρ.1, ρ.2, rfl⟩
    · rintro ⟨ρ, hρ, rfl⟩
      exact ⟨⟨ρ, hρ⟩, rfl⟩
  have htop : Submodule.span ℝ (Set.range v) = ⊤ := by
    rw [hrange, ← hspan]
    conv_rhs => rw [F.eq_hull_generator hmax.mem]
    exact (Submodule.span_span_of_tower _ ℝ _).symm
  have hmem : toNR (F.generator ρ0) ∈ Submodule.span ℝ (Set.range v) := by
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨c, hcv⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hmem
  -- the other rays of `σ'` are in `σ`
  obtain ⟨S', rfl, hS'⟩ := hs σ' hmax'.mem
  obtain ⟨T, hTS, hT⟩ := exists_subset_of_isFaceOf_latticeCone (F.inter_face_right hmax.mem hmax'.mem)
  have hTcard : n ≤ T.card + 1 := by
    have := coneDim_latticeCone_le T
    rw [← hT] at this
    omega
  have hS'card : S'.card ≤ n := by
    have := hS'.fintype_card_le_finrank
    simpa [Module.finrank_fin_fun] using this
  have huniq : ∀ w₁ ∈ S', w₁ ∉ T → ∀ w₂ ∈ S', w₂ ∉ T → w₁ = w₂ := by
    intro w₁ h₁ h₁' w₂ h₂ h₂'
    by_contra h12
    have hsub : insert w₁ (insert w₂ T) ⊆ S' := Finset.insert_subset h₁ (Finset.insert_subset h₂ hTS)
    have := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem (by simp [h12, h₁']), Finset.card_insert_of_notMem h₂'] at this
    omega
  have hwit : ∀ ρ : F.Ray, ρ.1 ≤ latticeCone S' → ¬ ρ.1 ≤ σ →
      ∃ w ∈ S', w ∉ T ∧ toNR w ∈ ρ.1 := by
    intro ρ hρ hρσ
    obtain ⟨Tρ, hTρ, hρeq⟩ :=
      exists_subset_of_isFaceOf_latticeCone (F.isFaceOf_of_le hmax'.mem ρ hρ)
    by_contra hno
    push Not at hno
    apply hρσ
    have hsub : Tρ ⊆ T := fun w hw => by
      by_contra hwT
      exact hno w (hTρ hw) hwT (by rw [hρeq]; exact toNR_mem_latticeCone hw)
    calc ρ.1 = latticeCone Tρ := hρeq
      _ ≤ latticeCone T := Submodule.span_mono (Set.image_mono (Finset.coe_subset.mpr hsub))
      _ = σ ⊓ latticeCone S' := hT.symm
      _ ≤ σ := inf_le_left
  refine ⟨{
    ray := ρ0
    ray_le := hρ0
    ray_not_le := hρ0'
    eq_or_le := fun ρ hρ => ?_
    base := Finset.univ.map (Function.Embedding.subtype fun ρ : F.Ray => ρ.1 ≤ σ)
    base_le := fun ρ hρ => by
      obtain ⟨a, -, rfl⟩ := Finset.mem_map.mp hρ
      exact a.2
    coeff := fun ρ => if h : ρ.1 ≤ σ then c ⟨ρ, h⟩ else 0
    relation := ?_ }⟩
  · by_cases hρσ : ρ.1 ≤ σ
    · exact Or.inr hρσ
    · left
      obtain ⟨w, hw, hwT, hwρ⟩ := hwit ρ hρ hρσ
      obtain ⟨w0, hw0, hw0T, hw0ρ⟩ := hwit ρ0 hρ0 hρ0'
      obtain rfl := huniq w hw hwT w0 hw0 hw0T
      exact ray_eq_of_mem hwρ hw0ρ (hS'.ne_zero ⟨w, Finset.mem_coe.mpr hw⟩)
  · rw [Finset.sum_map, ← hcv]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    show c ρ • v ρ = (if h : ρ.1.1 ≤ σ then c ⟨ρ.1, h⟩ else 0) • toNR (F.generator ρ.1)
    rw [dite_cond_eq_true (eq_true ρ.2)]

/-! ### Part 3: the toric cone theorem -/

/-- **The toric cone theorem, combinatorial form.** Let `D` be an R-Cartier divisor on a complete simplicial fan. Then `D` is nef, in the sense that its support function is convex (`Fan.IsNef`), exactly when its degree `D · V(τ)` on each wall curve is nonnegative (Cox, Little and Schenck, Theorem 6.3.12 and Proposition 6.4.4). Each wall `σ ∩ σ'` carries the data of a wall (`Fan.IsWallPair.nonempty_wallData`), so the condition is not empty.

This is the combinatorial form of the theorem. The geometric form says that the cone of curves of the toric variety is spanned by the classes of the curves `V(τ)`, and that a divisor is nef when it has nonnegative degree on each of them. It needs the toric variety as a scheme, with its curves and intersection numbers, and this is not in the repository yet. -/
theorem coneTheorem (hc : F.IsComplete) (hs : F.IsSimplicialFan) {D : F.TDivisor ℝ}
    (hD : F.IsRCartier D) :
    F.IsNef D ↔ ∀ σ σ' : PointedCone ℝ (NR n), F.IsWallPair σ σ' →
      ∀ W : F.WallData σ σ', 0 ≤ W.degree D := by
  constructor
  · rintro ⟨ψ, hψ, hcc⟩ σ σ' hw W
    exact (W.degree_nonneg_iff hw.isMaximalCone_left.mem hw.isMaximalCone_right.mem hψ).mpr
      (isConvexAcross_of_concaveOn hc hψ.1 hcc hw)
  · intro h
    obtain ⟨φ, hφ⟩ := hD.exists_isSupportFunctionOf
    refine ⟨φ, hφ, (concaveOn_iff_forall_isConvexAcross_of_isSimplicialFan hc hs hφ.1).mpr
      fun σ σ' hw => ?_⟩
    obtain ⟨W⟩ := hw.nonempty_wallData hs
    exact (W.degree_nonneg_iff hw.isMaximalCone_left.mem hw.isMaximalCone_right.mem hφ).mp
      (h σ σ' hw W)

end Fan

end MinimalModel.Toric
