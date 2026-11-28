/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import MinimalModel.Toric.FlipLink

/-!
# Toric flips, part 7: the contraction of an extremal ray

This file does step 3 of the route to `flipExists` in `MinimalModel/Toric/Flip.lean` (route R3, spec 04.4), the contraction of an extremal ray (Reid 1983, Section 2 and Corollary 2.5; Matsuki, Section 14-2; Cox, Little and Schenck, Theorem 15.4.3 and Proposition 15.4.5).

Let `F` be a complete simplicial fan, `R` an extremal ray of its cone of curves, and `c` the class of a wall curve in `R`, with `J₊` and `J₋` the rays where `c` is positive and negative. For a maximal cone `ν` of `F`, the cone `Fan.contractCone c ν` is `ν` when `ν` is not in the star of `cone(u_{J₋})`, and `cone(u_{J₊ ∪ J₋}) + λ` with `λ = Fan.linkCone c ν` when it is (`Fan.contractCone_of_not_le`, `Fan.contractCone_of_le`). The contraction `Fan.contraction c` is the set of the faces of these cones. So it replaces the star by the cones `cone(u_{J₊ ∪ J₋}) + λ` for `λ` in the link, and it keeps the other cones (`Fan.fullCircuitCone_sup_mem_contraction`, `Fan.mem_contraction_of_not_le`).

## The cones of the contraction are the linearity domains of the supporting divisor

Let `φ` be the support function of the divisor that supports `R` (`Fan.IsRaySupport`), and `m_ν` its linear form on `ν`. Then `φ ≤ m_ν` everywhere. The main point is

  `x ∈ Fan.contractCone c ν ↔ φ(x) = m_ν(x)`

(`Fan.IsRaySupport.mem_contractCone_iff`). The set on the right is a convex cone: if `φ = m_ν` at `x` and `y`, let `m'` be the linear form of `φ` on a maximal cone that contains `x + y`. Then `φ(x + y) = m'(x) + m'(y) ≥ φ(x) + φ(y) = m_ν(x + y) ≥ φ(x + y)`. It contains the generators of `ν`, and those of the circuit when `ν` is in the star (`Fan.IsRaySupport.eq_of_curveClass_ne_zero`). This gives `→`.

For `←`, write `x` in a maximal cone `μ` that contains it, `x = Σ b_ρ u_ρ` with `b ≥ 0`. Then `Σ b_ρ (m_ν - m_μ)(u_ρ) = 0` with nonnegative terms, so `φ(u_ρ) = m_ν(u_ρ)` when `b_ρ > 0`. So it suffices that `φ(u_ρ) = m_ν(u_ρ)` with `ρ ⊄ ν` forces `ν` to be in the star and `ρ` to be in the circuit (`Fan.IsRaySupport.negCone_le_of_eq`). Write `u_ρ = Σ β_l u_l` in the basis of `ν`. Some `β_l` is negative, as `u_ρ ∉ ν`, so the wall of `ν` opposite `l` is a wall of `R` (`Fan.IsRaySupport.degree_eq_zero`). Its class is a positive multiple of `c`, so `c_l > 0` and `ν` contains `cone(u_{J₋})` (`Fan.IsRaySupport.pos_of_coeff_neg`). Let `j` be the ray of the circuit outside `ν`. If `c_ρ = 0`, shift the coefficients by `t c`, with `t = max(-β_l / c_l)` over `J₊`, attained at `l₀`. The new coefficients `γ` vanish at `l₀` and live on the neighbour `ν''` of `ν` across the facet opposite `l₀`, which has the rays of `ν` and `j` but not `l₀` (`Fan.IsRaySupport.exists_exchange`). A negative `γ_l` would give `c_l > 0` in the same way, which the choice of `t` excludes. So `u_ρ ∈ ν''`, and `ρ = j`, a contradiction.

## The contraction is a quasi-fan refined by `F`

For two maximal cones `ν, ν'`, the intersection `K_ν ∩ K_ν'` is the face of `K_ν` cut out by `m_ν' - m_ν`, which is nonnegative on `K_ν` (`Fan.IsRaySupport.inf_isFaceOf`). So two faces of `K_ν` and `K_ν'` meet in a face of each (`Fan.isFaceOf_inf_of_isFaceOf`), and the contraction is a quasi-fan (`Fan.IsExtremalRay.isQuasiFan_contraction`). A point `x` of a face `τ` of `K_ν` is `Σ b_ρ u_ρ` in a maximal cone `μ` with each `u_ρ` with `b_ρ > 0` in `K_ν`, so in `τ`, and the face of `μ` spanned by these rays is a cone of `F` in `τ` that contains `x`. So `F` refines the contraction (`Fan.IsExtremalRay.refines_contraction`).

## Birational and small contractions

The relation `c` is the only linear relation among the generators of the rays of `ν` and `j` (`Fan.eq_smul_of_sum_eq_zero`). When `J₋` is not empty, `c` has a negative coefficient, and so the cones `K_ν` are strongly convex (`Fan.IsExtremalRay.isStronglyConvex_contractCone`). Then the contraction is a fan, `Fan.IsExtremalRay.contractionFan`, with the same support as `F` (`Fan.IsExtremalRay.support_contractionFan`): the contraction is birational. When `J₋` has two rays, the rays of `ν` are faces of `K_ν` (`Fan.IsExtremalRay.isFaceOf_contractCone`): a decomposition `a x + y = r u_ρ` gives a relation `a α + α' - r δ_ρ = s c`, and `s` is zero since `c` is negative at a ray of `J₋` other than `ρ` and positive at `j`. So the contraction has the same rays as `F` (`Fan.IsExtremalRay.rays_contractionFan`): it is small, a flipping contraction.

## Main results

* `Fan.contraction`, `Fan.contractCone`: the contraction of an extremal ray.
* `Fan.IsRaySupport.mem_contractCone_iff`: the maximal cones of the contraction are the linearity domains of the support function of the divisor that supports the ray.
* `Fan.IsExtremalRay.isQuasiFan_contraction`, `Fan.IsExtremalRay.refines_contraction`: the contraction is a quasi-fan, and `F` refines it.
* `Fan.IsExtremalRay.contractionFan`, `Fan.IsExtremalRay.support_contractionFan`: when `J₋` is not empty, the contraction is a fan with the same support as `F`.
* `Fan.IsExtremalRay.rays_contractionFan`: when `J₋` has two rays, the contraction has the same rays as `F`.
-/

open Set

namespace MinimalModel.Toric

variable {n : ℕ}

namespace Fan

variable {F : Fan n}

/-! ### Cones of generators of rays -/

/-- A vector is in the cone of the generators of the rays with a property `P` when it is a nonnegative combination of these generators. -/
theorem mem_hull_generator_iff (P : F.Ray → Prop) {x : NR n} :
    x ∈ PointedCone.hull ℝ {x | ∃ ρ : F.Ray, P ρ ∧ toNR (F.generator ρ) = x} ↔
      ∃ b : F.Ray → ℝ, (∀ ρ, 0 ≤ b ρ) ∧ (∀ ρ, ¬ P ρ → b ρ = 0) ∧
        ∑ ρ, b ρ • toNR (F.generator ρ) = x := by
  show x ∈ indexCone (fun ρ : F.Ray => toNR (F.generator ρ)) {ρ | P ρ} ↔ _
  exact mem_indexCone

/-- The cone of the generators of the rays with a property is rational polyhedral. -/
theorem isRationalPolyhedral_hull_generator (P : F.Ray → Prop) :
    IsRationalPolyhedral
      (PointedCone.hull ℝ {x | ∃ ρ : F.Ray, P ρ ∧ toNR (F.generator ρ) = x}) := by
  classical
  refine ⟨(Finset.univ.filter P).image F.generator, ?_⟩
  rw [latticeCone_eq_hull]
  congr 1
  ext x
  constructor
  · rintro ⟨ρ, hρ, rfl⟩
    exact ⟨F.generator ρ, Finset.mem_coe.mpr (Finset.mem_image_of_mem _
      (Finset.mem_filter.mpr ⟨Finset.mem_univ ρ, hρ⟩)), rfl⟩
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hv)
    exact ⟨ρ, (Finset.mem_filter.mp hρ).2, rfl⟩

/-- The set of the generators of the rays with a property is finite. -/
theorem finite_setOf_generator (P : F.Ray → Prop) :
    {x | ∃ ρ : F.Ray, P ρ ∧ toNR (F.generator ρ) = x}.Finite :=
  (Set.finite_range fun ρ : F.Ray => toNR (F.generator ρ)).subset
    fun _ ⟨ρ, _, hρ⟩ => ⟨ρ, hρ⟩

/-- A ray of the fan is in a cone when its generator is. -/
theorem le_of_generator_mem {τ : PointedCone ℝ (NR n)} {ρ : F.Ray} (h : toNR (F.generator ρ) ∈ τ) :
    ρ.1 ≤ τ := by
  rw [← F.latticeCone_generator ρ]
  exact latticeCone_singleton_le.mpr h

/-- The cone of the generators of some rays of a cone `μ` of a simplicial fan is a face of `μ`, so a cone of the fan. -/
theorem hull_generator_mem (hs : F.IsSimplicialFan) {μ : PointedCone ℝ (NR n)}
    (hμ : μ ∈ F.cones) (P : F.Ray → Prop) (hP : ∀ ρ : F.Ray, P ρ → ρ.1 ≤ μ) :
    PointedCone.hull ℝ {x | ∃ ρ : F.Ray, P ρ ∧ toNR (F.generator ρ) = x} ∈ F.cones := by
  have hli := linearIndependent_generator hμ (hs μ hμ)
  have hface := LinearIndependent.indexCone_isFaceOf hli
    {ρ : {ρ : F.Ray // ρ.1 ≤ μ} | P ρ.1}
  rw [← eq_indexCone_generator hμ] at hface
  have heq : PointedCone.hull ℝ {x | ∃ ρ : F.Ray, P ρ ∧ toNR (F.generator ρ) = x} =
      indexCone (fun ρ : {ρ : F.Ray // ρ.1 ≤ μ} => toNR (F.generator ρ.1))
        {ρ : {ρ : F.Ray // ρ.1 ≤ μ} | P ρ.1} := by
    unfold indexCone
    congr 1
    ext x
    constructor
    · rintro ⟨ρ, hρ, rfl⟩
      exact ⟨⟨ρ, hP ρ hρ⟩, hρ, rfl⟩
    · rintro ⟨ρ, hρ, rfl⟩
      exact ⟨ρ.1, hρ, rfl⟩
  rw [heq]
  exact F.face_mem μ hμ _ hface

/-- A vector is a real combination of the generators of the rays of a maximal cone of a complete fan. -/
theorem exists_sum_eq_of_isMaximalCone (hc : F.IsComplete) {ν : PointedCone ℝ (NR n)}
    (hν : F.IsMaximalCone ν) (x : NR n) :
    ∃ β : F.Ray → ℝ, (∀ ρ, β ρ ≠ 0 → ρ.1 ≤ ν) ∧ ∑ ρ, β ρ • toNR (F.generator ρ) = x := by
  classical
  have hspan : Submodule.span ℝ
      (Set.range fun ρ : {ρ : F.Ray // ρ.1 ≤ ν} => toNR (F.generator ρ.1)) = ⊤ := by
    rw [← Set.image_univ, ← span_indexCone, ← eq_indexCone_generator hν.mem]
    exact span_eq_top_of_coneDim_eq (hν.coneDim_eq hc)
  have hmem : x ∈ Submodule.span ℝ
      (Set.range fun ρ : {ρ : F.Ray // ρ.1 ≤ ν} => toNR (F.generator ρ.1)) := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨β', hβ'⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hmem
  refine ⟨fun ρ => if h : ρ.1 ≤ ν then β' ⟨ρ, h⟩ else 0, fun ρ h0 => ?_, ?_⟩
  · by_contra h
    exact h0 (by simp [h])
  · rw [← hβ']
    refine (sum_subtype_eq_sum (σ := ν) Finset.univ
      (fun ρ => (if h : ρ.1 ≤ ν then β' ⟨ρ, h⟩ else 0) • toNR (F.generator ρ))
      (fun ρ _ => Finset.mem_univ ρ) fun ρ _ h0 => ?_).symm.trans ?_
    · by_contra h
      exact h0 (by simp [h])
    · refine Finset.sum_congr rfl fun ρ _ => ?_
      show (if h : ρ.1.1 ≤ ν then β' ⟨ρ.1, h⟩ else 0) • toNR (F.generator ρ.1) = _
      rw [dite_eq_left ρ.2]

/-! ### The contraction -/

variable (F) in
/-- The cone `cone(u_{J₊ ∪ J₋})` of the generators of the rays `ρ` with `c ρ ≠ 0`. -/
noncomputable def fullCircuitCone (c : F.Ray → ℝ) : PointedCone ℝ (NR n) :=
  PointedCone.hull ℝ {x | ∃ ρ : F.Ray, c ρ ≠ 0 ∧ toNR (F.generator ρ) = x}

variable (F) in
/-- The cone of the contraction that contains the maximal cone `ν`: the cone of the generators of the rays of `ν`, and of the rays `ρ` with `c ρ ≠ 0` when `ν` contains `cone(u_{J₋})`. It is `ν` when `ν` is not in the star (`Fan.contractCone_of_not_le`), and `cone(u_{J₊ ∪ J₋}) + λ` with `λ` the link cone of `ν` when it is (`Fan.contractCone_of_le`). -/
noncomputable def contractCone (c : F.Ray → ℝ) (ν : PointedCone ℝ (NR n)) :
    PointedCone ℝ (NR n) :=
  PointedCone.hull ℝ
    {x | ∃ ρ : F.Ray, (ρ.1 ≤ ν ∨ (F.negCone c ≤ ν ∧ c ρ ≠ 0)) ∧ toNR (F.generator ρ) = x}

variable (F) in
/-- **The contraction** of the extremal ray of the class `c`: the faces of the cones `Fan.contractCone c ν` for the maximal cones `ν` of `F`. It replaces the star of `cone(u_{J₋})` by the cones `cone(u_{J₊ ∪ J₋}) + λ` with `λ` in the link, and it keeps the other cones. -/
def contraction (c : F.Ray → ℝ) : Set (PointedCone ℝ (NR n)) :=
  {τ | ∃ ν, F.IsMaximalCone ν ∧ τ.IsFaceOf (F.contractCone c ν)}

/-- Outside the star of `cone(u_{J₋})`, the cone of the contraction is the cone of the fan. -/
theorem contractCone_of_not_le {c : F.Ray → ℝ} {ν : PointedCone ℝ (NR n)} (hν : ν ∈ F.cones)
    (h : ¬ F.negCone c ≤ ν) : F.contractCone c ν = ν :=
  (eq_hull_of_forall_le_iff hν (P := fun ρ => ρ.1 ≤ ν ∨ (F.negCone c ≤ ν ∧ c ρ ≠ 0))
    fun _ => ⟨Or.inl, fun hρ => hρ.resolve_right fun h' => h h'.1⟩).symm

/-- On the star of `cone(u_{J₋})`, the cone of the contraction is `cone(u_{J₊ ∪ J₋}) + λ`, with `λ` the link cone. -/
theorem contractCone_of_le {c : F.Ray → ℝ} {ν : PointedCone ℝ (NR n)}
    (h : F.negCone c ≤ ν) :
    F.contractCone c ν = F.fullCircuitCone c ⊔ F.linkCone c ν := by
  refine Eq.trans ?_ (hull_or (fun ρ : F.Ray => c ρ ≠ 0) fun ρ : F.Ray => ρ.1 ≤ ν ∧ c ρ = 0)
  unfold contractCone
  congr 1
  ext x
  refine exists_congr fun ρ => and_congr ⟨fun hρ => ?_, fun hρ => ?_⟩ Iff.rfl
  · by_cases h0 : c ρ = 0
    · exact Or.inr ⟨hρ.resolve_right fun h' => h'.2 h0, h0⟩
    · exact Or.inl h0
  · rcases hρ with h0 | ⟨hρ, -⟩
    · exact Or.inr ⟨h, h0⟩
    · exact Or.inl hρ

/-- A cone of the fan is in its cone of the contraction. -/
theorem le_contractCone {ν : PointedCone ℝ (NR n)} (hν : ν ∈ F.cones) (c : F.Ray → ℝ) :
    ν ≤ F.contractCone c ν :=
  (F.eq_hull_generator hν).trans_le
    (Submodule.span_mono fun _ ⟨ρ, hρ, hx⟩ => ⟨ρ, Or.inl hρ, hx⟩)

/-- The cones of the contraction are rational polyhedral. -/
theorem isRationalPolyhedral_contractCone (c : F.Ray → ℝ) (ν : PointedCone ℝ (NR n)) :
    IsRationalPolyhedral (F.contractCone c ν) :=
  isRationalPolyhedral_hull_generator fun ρ => ρ.1 ≤ ν ∨ (F.negCone c ≤ ν ∧ c ρ ≠ 0)

/-- A cone of the contraction has finitely many faces. -/
theorem finite_setOf_isFaceOf_contractCone (c : F.Ray → ℝ) (ν : PointedCone ℝ (NR n)) :
    {τ : PointedCone ℝ (NR n) | τ.IsFaceOf (F.contractCone c ν)}.Finite :=
  finite_setOf_isFaceOf_hull
    (finite_setOf_generator fun ρ => ρ.1 ≤ ν ∨ (F.negCone c ≤ ν ∧ c ρ ≠ 0))

/-- The contraction has finitely many cones. -/
theorem finite_contraction (c : F.Ray → ℝ) : (F.contraction c).Finite := by
  have hmax : {ν | F.IsMaximalCone ν}.Finite :=
    F.finite.subset fun ν hν => IsMaximalCone.mem hν
  refine (hmax.biUnion fun ν _ => finite_setOf_isFaceOf_contractCone c ν).subset ?_
  rintro τ ⟨ν, hν, hτ⟩
  exact Set.mem_biUnion hν hτ

/-- The cones `cone(u_{J₊ ∪ J₋}) + λ`, with `λ` in the link, are cones of the contraction. -/
theorem fullCircuitCone_sup_mem_contraction {c : F.Ray → ℝ} {L : PointedCone ℝ (NR n)}
    (hL : L ∈ F.link c) : F.fullCircuitCone c ⊔ L ∈ F.contraction c := by
  obtain ⟨τ, hτ, hneg, rfl⟩ := hL
  refine ⟨τ, hτ, ?_⟩
  simp only [contractCone_of_le hneg, PointedCone.IsFaceOf.refl]

/-- The contraction keeps the cones of the fan in a maximal cone outside the star of `cone(u_{J₋})`. -/
theorem mem_contraction_of_not_le {c : F.Ray → ℝ} {σ ν : PointedCone ℝ (NR n)}
    (hσ : σ ∈ F.cones) (hν : F.IsMaximalCone ν) (hσν : σ ≤ ν) (hneg : ¬ F.negCone c ≤ ν) :
    σ ∈ F.contraction c := by
  refine ⟨ν, hν, ?_⟩
  rw [contractCone_of_not_le hν.mem hneg]
  have h := F.inter_face ν hν.mem σ hσ
  rwa [inf_eq_right.mpr hσν] at h

/-- Two faces of two cones meet in a face of the first, when the two cones meet in a face of each. -/
theorem isFaceOf_inf_of_isFaceOf {A B K K' : PointedCone ℝ (NR n)} (hA : A.IsFaceOf K)
    (hB : B.IsFaceOf K') (h : (K ⊓ K').IsFaceOf K) (h' : (K ⊓ K').IsFaceOf K') :
    (A ⊓ B).IsFaceOf A := by
  have hA' : (A ⊓ (K ⊓ K')).IsFaceOf (K ⊓ K') :=
    (PointedCone.IsFaceOf.isFaceOf_iff_le (hA.inf_left h) h).mpr inf_le_right
  have hB' : (B ⊓ (K ⊓ K')).IsFaceOf (K ⊓ K') :=
    (PointedCone.IsFaceOf.isFaceOf_iff_le (hB.inf_left h') h').mpr inf_le_right
  have heq : A ⊓ (K ⊓ K') ⊓ (B ⊓ (K ⊓ K')) = A ⊓ B := by
    apply le_antisymm
    · exact le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
    · exact le_inf
        (le_inf inf_le_left (le_inf (inf_le_left.trans hA.le) (inf_le_right.trans hB.le)))
        (le_inf inf_le_right (le_inf (inf_le_left.trans hA.le) (inf_le_right.trans hB.le)))
  have hface : (A ⊓ B).IsFaceOf K := by
    rw [← heq]
    exact (hA'.inf_left hB').trans h
  exact (PointedCone.IsFaceOf.isFaceOf_iff_le hface hA).mpr inf_le_left

/-! ### The linearity domains of the supporting divisor -/

namespace IsRaySupport

variable {R : PointedCone ℝ (F.Ray → ℝ)} {D : F.TDivisor ℝ} {φ : NR n → ℝ}

/-- On a complete fan, each vector lies in a maximal cone, on which `φ` is linear. -/
theorem exists_eq_linear (h : F.IsRaySupport R D φ) (hc : F.IsComplete) (x : NR n) :
    ∃ (μ : PointedCone ℝ (NR n)) (m' : NR n →ₗ[ℝ] ℝ), F.IsMaximalCone μ ∧
      (∀ y ∈ μ, φ y = m' y) ∧ x ∈ μ := by
  obtain ⟨C, hC, hx⟩ := exists_mem_of_isComplete hc x
  obtain ⟨μ, hCμ, hμ⟩ := F.exists_le_isMaximalCone hC
  obtain ⟨m', hm'⟩ := h.isSupportFunctionOf.1 μ hμ.mem
  exact ⟨μ, m', hμ, hm', hCμ hx⟩

/-- **The linearity domain is a cone.** If `φ` agrees with the linear form `m` of a maximal cone on a set, it agrees with `m` on the cone of the set. -/
theorem apply_eq_of_mem_hull (h : F.IsRaySupport R D φ) (hc : F.IsComplete)
    {ν : PointedCone ℝ (NR n)} (hν : F.IsMaximalCone ν) {m : NR n →ₗ[ℝ] ℝ}
    (hm : ∀ x ∈ ν, φ x = m x) {s : Set (NR n)} (hs : ∀ x ∈ s, φ x = m x) {x : NR n}
    (hx : x ∈ PointedCone.hull ℝ s) : φ x = m x := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact hs y hy
  | zero => exact hm 0 (Submodule.zero_mem ν)
  | add y z _ _ hy hz =>
    obtain ⟨μ, m', hμ, hm', hyz⟩ := h.exists_eq_linear hc (y + z)
    have h1 := h.le_linear μ hμ m' hm' y
    have h2 := h.le_linear μ hμ m' hm' z
    have h3 := h.le_linear ν hν m hm (y + z)
    have h4 := hm' _ hyz
    rw [map_add] at h3 h4 ⊢
    linarith
  | smul a y _ hy =>
    show φ ((a : ℝ) • y) = m ((a : ℝ) • y)
    rw [IsSupportFunction.apply_smul hc h.isSupportFunctionOf.1 y (t := (a : ℝ)) a.2, map_smul,
      smul_eq_mul, hy]

/-- `φ` agrees with the linear form of `ν` on the cone of the contraction of `ν`. -/
theorem apply_eq_of_mem_contractCone (h : F.IsRaySupport R D φ) (hc : F.IsComplete)
    (hs : F.IsSimplicialFan) {σ₀ σ₀' : PointedCone ℝ (NR n)} (hw₀ : F.IsWallPair σ₀ σ₀')
    (W₀ : F.WallData σ₀ σ₀') (hW₀ : W₀.curveClass ∈ R) {ν : PointedCone ℝ (NR n)}
    (hν : F.IsMaximalCone ν) {m : NR n →ₗ[ℝ] ℝ} (hm : ∀ x ∈ ν, φ x = m x) {x : NR n}
    (hx : x ∈ F.contractCone W₀.curveClass ν) : φ x = m x := by
  refine h.apply_eq_of_mem_hull hc hν hm (s := {x | ∃ ρ : F.Ray, (ρ.1 ≤ ν ∨
    (F.negCone W₀.curveClass ≤ ν ∧ W₀.curveClass ρ ≠ 0)) ∧ toNR (F.generator ρ) = x}) ?_ hx
  rintro _ ⟨ρ, hρ | ⟨hneg, hρ⟩, rfl⟩
  · exact hm _ (hρ (F.toNR_generator_mem ρ))
  · exact h.eq_of_curveClass_ne_zero hs hw₀ W₀ hW₀ hν (negCone_le_iff.mp hneg) hm ρ hρ

/-- A vector on which `φ` agrees with the linear form `m` of a maximal cone `ν` is a nonnegative combination of generators of the rays of a maximal cone `μ`, and `φ` agrees with `m` at each generator of the combination. -/
theorem exists_coeff (h : F.IsRaySupport R D φ) (hc : F.IsComplete)
    {ν : PointedCone ℝ (NR n)} (hν : F.IsMaximalCone ν) {m : NR n →ₗ[ℝ] ℝ}
    (hm : ∀ x ∈ ν, φ x = m x) {x : NR n} (hx : φ x = m x) :
    ∃ μ, F.IsMaximalCone μ ∧ ∃ b : F.Ray → ℝ, (∀ ρ, 0 ≤ b ρ) ∧ (∀ ρ, b ρ ≠ 0 → ρ.1 ≤ μ) ∧
      (∀ ρ, b ρ ≠ 0 → φ (toNR (F.generator ρ)) = m (toNR (F.generator ρ))) ∧
        ∑ ρ, b ρ • toNR (F.generator ρ) = x := by
  obtain ⟨μ, m', hμ, hm', hxμ⟩ := h.exists_eq_linear hc x
  have hx' := hxμ
  rw [F.eq_hull_generator hμ.mem] at hx'
  obtain ⟨b, hb0, hbμ, hbx⟩ := (mem_hull_generator_iff (fun ρ : F.Ray => ρ.1 ≤ μ)).mp hx'
  have hμρ : ∀ ρ, b ρ ≠ 0 → ρ.1 ≤ μ := fun ρ hρ => by
    by_contra h'
    exact hρ (hbμ ρ h')
  have hterm : ∀ ρ ∈ (Finset.univ : Finset F.Ray),
      0 ≤ b ρ * (m (toNR (F.generator ρ)) - m' (toNR (F.generator ρ))) := by
    intro ρ _
    by_cases h0 : b ρ = 0
    · simp [h0]
    · refine mul_nonneg (hb0 ρ) (sub_nonneg.mpr ?_)
      rw [← hm' _ (hμρ ρ h0 (F.toNR_generator_mem ρ))]
      exact h.le_linear ν hν m hm _
  have htot : ∑ ρ, b ρ * (m (toNR (F.generator ρ)) - m' (toNR (F.generator ρ))) = 0 := by
    have h1 := congrArg (fun y => m y - m' y) hbx
    simp only [map_sum, map_smul, smul_eq_mul] at h1
    simp only [mul_sub, Finset.sum_sub_distrib]
    linarith [hm' x hxμ]
  refine ⟨μ, hμ, b, hb0, hμρ, fun ρ hρ => ?_, hbx⟩
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp htot ρ (Finset.mem_univ ρ)
  rcases mul_eq_zero.mp h0 with h3 | h3
  · exact absurd h3 hρ
  · rw [hm' _ (hμρ ρ hρ (F.toNR_generator_mem ρ))]
    linarith

/-- **A negative coefficient.** Let `y = Σ β_ρ u_ρ` be a combination of the generators of a maximal cone `ν` on which `φ` agrees with its linear form on `ν`. If `β_l < 0`, then `c_l > 0`, and `ν` contains `cone(u_{J₋})`: the wall of `ν` opposite `l` is a wall of `R`. -/
theorem pos_of_coeff_neg (h : F.IsRaySupport R D φ) (hc : F.IsComplete)
    (hs : F.IsSimplicialFan) (hR : F.IsExtremalRay R) {σ₀ σ₀' : PointedCone ℝ (NR n)}
    (W₀ : F.WallData σ₀ σ₀') (hW₀ : W₀.curveClass ∈ R)
    {ν : PointedCone ℝ (NR n)} (hν : F.IsMaximalCone ν) {m : NR n →ₗ[ℝ] ℝ}
    (hm : ∀ x ∈ ν, φ x = m x) (β : F.Ray → ℝ) (hβν : ∀ ρ, β ρ ≠ 0 → ρ.1 ≤ ν)
    (hy : φ (∑ ρ, β ρ • toNR (F.generator ρ)) = m (∑ ρ, β ρ • toNR (F.generator ρ)))
    {l : F.Ray} (hl : β l < 0) :
    0 < W₀.curveClass l ∧ F.negCone W₀.curveClass ≤ ν := by
  have hlν : l.1 ≤ ν := hβν l hl.ne
  obtain ⟨ν'', hw, hl'', -⟩ := exists_isWallPair_of_ray hc hs hν.mem (hν.coneDim_eq hc) l hlν
  obtain ⟨W⟩ := hw.nonempty_wallData hs
  have hsum : ∑ ρ : {ρ : F.Ray // ρ.1 ≤ ν}, β ρ.1 • toNR (F.generator ρ.1) =
      ∑ ρ, β ρ • toNR (F.generator ρ) :=
    sum_subtype_eq_sum Finset.univ (fun ρ => β ρ • toNR (F.generator ρ))
      (fun ρ _ => Finset.mem_univ ρ) (fun ρ _ hρ => hβν ρ fun h0 => hρ (by simp [h0]))
  have hW0 : W.degree D = 0 := h.degree_eq_zero hs hw W hm hlν hl'' (fun ρ => β ρ.1) hl (by
    have hy' := hy
    rw [← hsum] at hy'
    exact hy')
  have hprop := hR.isProportional hW₀ ((h.degree_eq_zero_iff ν ν'' hw W).mp hW0)
  obtain ⟨t, ht, hct⟩ := WallData.isProportional_iff.mp hprop
  refine ⟨?_, (hprop.negCone_le_inf (hs ν hν.mem) hw).trans inf_le_left⟩
  obtain ⟨ρ0, hρ0, hneg⟩ := W.exists_coeffIn_neg hν.mem hw.2.1.mem
  have hρ0l : ρ0 = ⟨l, hlν⟩ :=
    Subtype.ext (IsWallPair.eq_of_not_le (hs ν hν.mem) hw ρ0.2 hρ0 hlν hl'')
  rw [hρ0l] at hneg
  have h1 : W.curveClass l = -W.coeffIn ⟨l, hlν⟩ := W.curveClass_circuitRay (some ⟨l, hlν⟩)
  rw [hct, Pi.smul_apply, smul_eq_mul] at h1
  by_contra h2
  push Not at h2
  nlinarith

/-- **The rays of the linearity domain.** If `φ` agrees with the linear form of a maximal cone `ν` at the generator of a ray `ρ` that is not in `ν`, then `ν` contains `cone(u_{J₋})` and `ρ` is a ray of the circuit. The proof is in the module docstring. -/
theorem negCone_le_of_eq (h : F.IsRaySupport R D φ) (hc : F.IsComplete)
    (hs : F.IsSimplicialFan) (hR : F.IsExtremalRay R) {σ₀ σ₀' : PointedCone ℝ (NR n)}
    (hw₀ : F.IsWallPair σ₀ σ₀') (W₀ : F.WallData σ₀ σ₀') (hW₀ : W₀.curveClass ∈ R)
    {ν : PointedCone ℝ (NR n)} (hν : F.IsMaximalCone ν) {m : NR n →ₗ[ℝ] ℝ}
    (hm : ∀ x ∈ ν, φ x = m x) {ρ : F.Ray}
    (hρ : φ (toNR (F.generator ρ)) = m (toNR (F.generator ρ))) (hρν : ¬ ρ.1 ≤ ν) :
    F.negCone W₀.curveClass ≤ ν ∧ W₀.curveClass ρ ≠ 0 := by
  classical
  -- write `u_ρ` in the basis of `ν`
  obtain ⟨β, hβν, hβsum⟩ := exists_sum_eq_of_isMaximalCone hc hν (toNR (F.generator ρ))
  obtain ⟨l, hl⟩ : ∃ l, β l < 0 := by
    by_contra hno
    have hno' : ∀ l, 0 ≤ β l := fun l => not_lt.mp fun hlt => hno ⟨l, hlt⟩
    apply hρν
    apply le_of_generator_mem
    rw [F.eq_hull_generator hν.mem]
    exact (mem_hull_generator_iff (fun ρ' : F.Ray => ρ'.1 ≤ ν)).mpr
      ⟨β, hno', fun ρ' h' => by
        by_contra h0
        exact h' (hβν ρ' h0), hβsum⟩
  have hy : φ (∑ ρ', β ρ' • toNR (F.generator ρ')) = m (∑ ρ', β ρ' • toNR (F.generator ρ')) := by
    rw [hβsum]
    exact hρ
  obtain ⟨hcl, hneg⟩ := h.pos_of_coeff_neg hc hs hR W₀ hW₀ hν hm β hβν hy hl
  have hneg' := negCone_le_iff.mp hneg
  refine ⟨hneg, fun hc0 => ?_⟩
  obtain ⟨j, hcj, hjν, hj⟩ := h.exists_ray_not_le hc hs hR hw₀ W₀ hW₀ hν hneg'
  -- the shift `t = max (-β_l / c_l)` over `J₊`, attained at `l₀`
  obtain ⟨l₀, hl₀S, hl₀max⟩ := (Finset.univ.filter fun l => 0 < W₀.curveClass l).exists_max_image
    (fun l => -β l / W₀.curveClass l) ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ l, hcl⟩⟩
  have hcl₀ : 0 < W₀.curveClass l₀ := (Finset.mem_filter.mp hl₀S).2
  obtain ⟨t, htdef⟩ : ∃ t, t = -β l₀ / W₀.curveClass l₀ := ⟨_, rfl⟩
  have hmax : ∀ l', 0 < W₀.curveClass l' → -β l' / W₀.curveClass l' ≤ t := fun l' hl' => by
    rw [htdef]
    exact hl₀max l' (Finset.mem_filter.mpr ⟨Finset.mem_univ l', hl'⟩)
  have ht : 0 < t := lt_of_lt_of_le (div_pos (neg_pos.mpr hl) hcl) (hmax l hcl)
  have htl₀ : t * W₀.curveClass l₀ = -β l₀ := by
    rw [htdef, div_mul_cancel₀ _ hcl₀.ne']
  have hβl₀ : β l₀ < 0 := by
    have := mul_pos ht hcl₀
    linarith
  have hl₀ν : l₀.1 ≤ ν := hβν l₀ hβl₀.ne
  have hl₀j : l₀ ≠ j := fun h' => hjν (by rw [← h']; exact hl₀ν)
  -- the neighbour of `ν` across the facet opposite `l₀`
  obtain ⟨ν'', hw, hchar⟩ := h.exists_exchange hc hs hR hw₀ W₀ hW₀ hν hneg' hcj hjν hj hcl₀ hl₀j
  have hm'' : ∀ x ∈ ν'', φ x = m x := by
    intro x hx
    rw [F.eq_hull_generator hw.2.1.mem] at hx
    refine h.apply_eq_of_mem_hull hc hν hm ?_ hx
    rintro _ ⟨ρ', hρ', rfl⟩
    rcases (hchar ρ').mp hρ' with hρ'j | ⟨hρ'ν, -⟩
    · rw [hρ'j]
      exact h.eq_of_curveClass_ne_zero hs hw₀ W₀ hW₀ hν hneg' hm j hcj.ne'
    · exact hm _ (hρ'ν (F.toNR_generator_mem ρ'))
  -- the shifted coefficients `γ = β + t c`
  obtain ⟨γ, hγ⟩ : ∃ γ : F.Ray → ℝ, ∀ ρ', γ ρ' = β ρ' + t * W₀.curveClass ρ' :=
    ⟨_, fun _ => rfl⟩
  have hγl₀ : γ l₀ = 0 := by
    rw [hγ, htl₀, add_neg_cancel]
  have hrel := W₀.sum_curveClass_smul_generator hw₀.1.mem (hs σ₀ hw₀.1.mem)
  have hγsum : ∑ ρ', γ ρ' • toNR (F.generator ρ') = toNR (F.generator ρ) := by
    have hterm : ∀ ρ', γ ρ' • toNR (F.generator ρ') = β ρ' • toNR (F.generator ρ') +
        t • (W₀.curveClass ρ' • toNR (F.generator ρ')) := fun ρ' => by
      rw [hγ, add_smul, mul_smul]
    simp only [hterm]
    rw [Finset.sum_add_distrib, ← Finset.smul_sum, hrel, smul_zero, add_zero, hβsum]
  have hγν'' : ∀ ρ', γ ρ' ≠ 0 → ρ'.1 ≤ ν'' := by
    intro ρ' h0
    refine (hchar ρ').mpr ?_
    by_cases hρ'j : ρ' = j
    · exact Or.inl hρ'j
    · refine Or.inr ⟨?_, fun hρ'l => h0 (by rw [hρ'l]; exact hγl₀)⟩
      by_cases hb : β ρ' = 0
      · refine hj ρ' (fun hc' => h0 ?_) hρ'j
        rw [hγ, hb, hc', mul_zero, add_zero]
      · exact hβν ρ' hb
  have hy'' : φ (∑ ρ', γ ρ' • toNR (F.generator ρ')) =
      m (∑ ρ', γ ρ' • toNR (F.generator ρ')) := by
    rw [hγsum]
    exact hρ
  -- the shifted coefficients are nonnegative
  have hγ0 : ∀ ρ', 0 ≤ γ ρ' := by
    intro ρ'
    by_contra hlt
    have hlt' : γ ρ' < 0 := not_le.mp hlt
    obtain ⟨hcρ', -⟩ := h.pos_of_coeff_neg hc hs hR W₀ hW₀ hw.2.1 hm'' γ hγν'' hy'' hlt'
    have h1 := hmax ρ' hcρ'
    rw [div_le_iff₀ hcρ'] at h1
    rw [hγ] at hlt'
    linarith
  -- so `u_ρ` is in `ν''`, and `ρ = j`
  have hρν'' : ρ.1 ≤ ν'' := by
    apply le_of_generator_mem
    rw [← hγsum]
    refine Submodule.sum_mem _ fun ρ' _ => ?_
    by_cases h0 : γ ρ' = 0
    · rw [h0, zero_smul]
      exact Submodule.zero_mem _
    · exact PointedCone.smul_mem _ (hγ0 ρ') (hγν'' ρ' h0 (F.toNR_generator_mem ρ'))
  rcases (hchar ρ).mp hρν'' with hρj | ⟨hρν', -⟩
  · rw [hρj] at hc0
    exact hcj.ne' hc0
  · exact hρν hρν'

/-- The generator of a ray at which `φ` agrees with the linear form of `ν` is in the cone of the contraction of `ν`. -/
theorem mem_contractCone_of_eq (h : F.IsRaySupport R D φ) (hc : F.IsComplete)
    (hs : F.IsSimplicialFan) (hR : F.IsExtremalRay R) {σ₀ σ₀' : PointedCone ℝ (NR n)}
    (hw₀ : F.IsWallPair σ₀ σ₀') (W₀ : F.WallData σ₀ σ₀') (hW₀ : W₀.curveClass ∈ R)
    {ν : PointedCone ℝ (NR n)} (hν : F.IsMaximalCone ν) {m : NR n →ₗ[ℝ] ℝ}
    (hm : ∀ x ∈ ν, φ x = m x) {ρ : F.Ray}
    (hρ : φ (toNR (F.generator ρ)) = m (toNR (F.generator ρ))) :
    toNR (F.generator ρ) ∈ F.contractCone W₀.curveClass ν := by
  refine Submodule.subset_span ⟨ρ, ?_, rfl⟩
  by_cases hρν : ρ.1 ≤ ν
  · exact Or.inl hρν
  · exact Or.inr (h.negCone_le_of_eq hc hs hR hw₀ W₀ hW₀ hν hm hρ hρν)

/-- **The cone of the contraction is the linearity domain** of the supporting divisor: `x ∈ Fan.contractCone c ν ↔ φ x = m_ν x`. -/
theorem mem_contractCone_iff (h : F.IsRaySupport R D φ) (hc : F.IsComplete)
    (hs : F.IsSimplicialFan) (hR : F.IsExtremalRay R) {σ₀ σ₀' : PointedCone ℝ (NR n)}
    (hw₀ : F.IsWallPair σ₀ σ₀') (W₀ : F.WallData σ₀ σ₀') (hW₀ : W₀.curveClass ∈ R)
    {ν : PointedCone ℝ (NR n)} (hν : F.IsMaximalCone ν) {m : NR n →ₗ[ℝ] ℝ}
    (hm : ∀ x ∈ ν, φ x = m x) {x : NR n} :
    x ∈ F.contractCone W₀.curveClass ν ↔ φ x = m x := by
  refine ⟨h.apply_eq_of_mem_contractCone hc hs hw₀ W₀ hW₀ hν hm, fun hx => ?_⟩
  obtain ⟨-, -, b, hb0, -, hbeq, rfl⟩ := h.exists_coeff hc hν hm hx
  refine Submodule.sum_mem _ fun ρ _ => ?_
  by_cases h0 : b ρ = 0
  · rw [h0, zero_smul]
    exact Submodule.zero_mem _
  · exact PointedCone.smul_mem _ (hb0 ρ)
      (h.mem_contractCone_of_eq hc hs hR hw₀ W₀ hW₀ hν hm (hbeq ρ h0))

/-- **Two cones of the contraction meet in a face of each.** The intersection of the cones of the contraction of two maximal cones `ν, ν'` is the face of the first cut out by `m_ν' - m_ν`. -/
theorem inf_isFaceOf (h : F.IsRaySupport R D φ) (hc : F.IsComplete)
    (hs : F.IsSimplicialFan) (hR : F.IsExtremalRay R) {σ₀ σ₀' : PointedCone ℝ (NR n)}
    (hw₀ : F.IsWallPair σ₀ σ₀') (W₀ : F.WallData σ₀ σ₀') (hW₀ : W₀.curveClass ∈ R)
    {ν ν' : PointedCone ℝ (NR n)} (hν : F.IsMaximalCone ν) (hν' : F.IsMaximalCone ν') :
    (F.contractCone W₀.curveClass ν ⊓ F.contractCone W₀.curveClass ν').IsFaceOf
      (F.contractCone W₀.curveClass ν) := by
  obtain ⟨m, hm⟩ := h.isSupportFunctionOf.1 ν hν.mem
  obtain ⟨m', hm'⟩ := h.isSupportFunctionOf.1 ν' hν'.mem
  refine IsFace.isFaceOf ⟨m' - m, fun v hv => ?_, fun v => ?_⟩
  · have h1 := (h.mem_contractCone_iff hc hs hR hw₀ W₀ hW₀ hν hm).mp hv
    have h2 := h.le_linear ν' hν' m' hm' v
    rw [LinearMap.sub_apply]
    linarith
  · rw [Submodule.mem_inf, h.mem_contractCone_iff hc hs hR hw₀ W₀ hW₀ hν hm,
      h.mem_contractCone_iff hc hs hR hw₀ W₀ hW₀ hν' hm', LinearMap.sub_apply]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by linarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by linarith⟩

end IsRaySupport

/-! ### The contraction is a quasi-fan refined by the fan -/

variable {R : PointedCone ℝ (F.Ray → ℝ)}

/-- **The contraction is a quasi-fan** (Reid 1983, Corollary 2.5). -/
theorem IsExtremalRay.isQuasiFan_contraction (hc : F.IsComplete) (hs : F.IsSimplicialFan)
    (hR : F.IsExtremalRay R) {σ₀ σ₀' : PointedCone ℝ (NR n)} (hw₀ : F.IsWallPair σ₀ σ₀')
    (W₀ : F.WallData σ₀ σ₀') (hW₀ : W₀.curveClass ∈ R) :
    IsQuasiFan (F.contraction W₀.curveClass) := by
  obtain ⟨D, φ, h⟩ := hR.exists_isRaySupport hc hs
  refine ⟨finite_contraction _, ?_, ?_, ?_⟩
  · rintro σ ⟨ν, -, hσ⟩
    exact (isRationalPolyhedral_contractCone _ ν).of_isFaceOf hσ
  · rintro σ ⟨ν, hν, hσ⟩ τ hτ
    exact ⟨ν, hν, hτ.trans hσ⟩
  · rintro σ ⟨ν, hν, hσ⟩ τ ⟨ν', hν', hτ⟩
    refine isFaceOf_inf_of_isFaceOf hσ hτ (h.inf_isFaceOf hc hs hR hw₀ W₀ hW₀ hν hν') ?_
    rw [inf_comm]
    exact h.inf_isFaceOf hc hs hR hw₀ W₀ hW₀ hν' hν

/-- **The fan refines the contraction.** Each cone of `F` is in a cone of the contraction, and each cone of the contraction is the union of the cones of `F` that it contains. -/
theorem IsExtremalRay.refines_contraction (hc : F.IsComplete) (hs : F.IsSimplicialFan)
    (hR : F.IsExtremalRay R) {σ₀ σ₀' : PointedCone ℝ (NR n)} (hw₀ : F.IsWallPair σ₀ σ₀')
    (W₀ : F.WallData σ₀ σ₀') (hW₀ : W₀.curveClass ∈ R) :
    F.Refines (F.contraction W₀.curveClass) := by
  obtain ⟨D, φ, h⟩ := hR.exists_isRaySupport hc hs
  refine ⟨fun σ hσ => ?_, ?_⟩
  · obtain ⟨ν, hσν, hν⟩ := F.exists_le_isMaximalCone hσ
    exact ⟨F.contractCone W₀.curveClass ν, ⟨ν, hν, PointedCone.IsFaceOf.refl _⟩,
      hσν.trans (le_contractCone hν.mem _)⟩
  · rintro τ ⟨ν, hν, hτ⟩
    obtain ⟨m, hm⟩ := h.isSupportFunctionOf.1 ν hν.mem
    apply Set.Subset.antisymm
    · intro x hx
      have hxK : φ x = m x :=
        (h.mem_contractCone_iff hc hs hR hw₀ W₀ hW₀ hν hm).mp (hτ.le hx)
      obtain ⟨μ, hμ, b, hb0, hbμ, hbeq, rfl⟩ := h.exists_coeff hc hν hm hxK
      have hterm : ∀ ρ, b ρ • toNR (F.generator ρ) ∈ F.contractCone W₀.curveClass ν := by
        intro ρ
        by_cases h0 : b ρ = 0
        · rw [h0, zero_smul]
          exact Submodule.zero_mem _
        · exact PointedCone.smul_mem _ (hb0 ρ)
            (h.mem_contractCone_of_eq hc hs hR hw₀ W₀ hW₀ hν hm (hbeq ρ h0))
      have hτgen : ∀ ρ, b ρ ≠ 0 → toNR (F.generator ρ) ∈ τ := by
        intro ρ h0
        have h1 : b ρ • toNR (F.generator ρ) ∈ τ :=
          hτ.mem_of_sum_mem (f := fun ρ => b ρ • toNR (F.generator ρ)) hterm hx ρ
        have h2 := PointedCone.smul_mem τ (inv_nonneg.mpr (hb0 ρ)) h1
        rwa [smul_smul, inv_mul_cancel₀ h0, one_smul] at h2
      refine Set.mem_biUnion
        (x := PointedCone.hull ℝ {y | ∃ ρ : F.Ray, b ρ ≠ 0 ∧ toNR (F.generator ρ) = y})
        ⟨hull_generator_mem hs hμ.mem (fun ρ : F.Ray => b ρ ≠ 0) hbμ, Submodule.span_le.mpr ?_⟩ ?_
      · rintro _ ⟨ρ, h0, rfl⟩
        exact hτgen ρ h0
      · exact (mem_hull_generator_iff (fun ρ : F.Ray => b ρ ≠ 0)).mpr
          ⟨b, hb0, fun ρ h0 => not_not.mp h0, rfl⟩
    · intro x hx
      obtain ⟨σ, ⟨-, hστ⟩, hxσ⟩ := Set.mem_iUnion₂.mp hx
      exact hστ hxσ

/-! ### Birational and small contractions -/

/-- **The relation of the circuit is unique.** Let `ν` be a cone of a simplicial fan that contains all the rays of the circuit of `c` but `j`. A linear relation among the generators of the rays of `ν` and `j` is a multiple of `c`. -/
theorem eq_smul_of_sum_eq_zero (hs : F.IsSimplicialFan) {σ₀ σ₀' : PointedCone ℝ (NR n)}
    (hw₀ : F.IsWallPair σ₀ σ₀') (W₀ : F.WallData σ₀ σ₀') {ν : PointedCone ℝ (NR n)}
    (hν : ν ∈ F.cones) {j : F.Ray} (hcj : W₀.curveClass j ≠ 0)
    (hj : ∀ ρ : F.Ray, W₀.curveClass ρ ≠ 0 → ρ ≠ j → ρ.1 ≤ ν) {d : F.Ray → ℝ}
    (hd : ∀ ρ : F.Ray, d ρ ≠ 0 → ρ ≠ j → ρ.1 ≤ ν)
    (hsum : ∑ ρ, d ρ • toNR (F.generator ρ) = 0) (ρ : F.Ray) :
    d ρ = d j / W₀.curveClass j * W₀.curveClass ρ := by
  obtain ⟨e, he⟩ : ∃ e : F.Ray → ℝ, ∀ ρ, e ρ = d ρ - d j / W₀.curveClass j * W₀.curveClass ρ :=
    ⟨_, fun _ => rfl⟩
  have hej : e j = 0 := by rw [he, div_mul_cancel₀ _ hcj, sub_self]
  have heν : ∀ ρ, e ρ ≠ 0 → ρ.1 ≤ ν := by
    intro ρ h0
    have hρj : ρ ≠ j := fun hρj => h0 (by rw [hρj]; exact hej)
    by_cases hd0 : d ρ = 0
    · refine hj ρ (fun hc0 => h0 ?_) hρj
      rw [he, hd0, hc0, mul_zero, sub_zero]
    · exact hd ρ hd0 hρj
  have hrel := W₀.sum_curveClass_smul_generator hw₀.1.mem (hs σ₀ hw₀.1.mem)
  have hesum : ∑ ρ, e ρ • toNR (F.generator ρ) = 0 := by
    have hterm : ∀ ρ, e ρ • toNR (F.generator ρ) = d ρ • toNR (F.generator ρ) -
        (d j / W₀.curveClass j) • (W₀.curveClass ρ • toNR (F.generator ρ)) := fun ρ => by
      rw [he, sub_smul, mul_smul]
    simp only [hterm]
    rw [Finset.sum_sub_distrib, ← Finset.smul_sum, hrel, hsum, smul_zero, sub_zero]
  have hesub : ∑ ρ : {ρ : F.Ray // ρ.1 ≤ ν}, e ρ.1 • toNR (F.generator ρ.1) = 0 :=
    (sum_subtype_eq_sum Finset.univ (fun ρ => e ρ • toNR (F.generator ρ))
      (fun ρ _ => Finset.mem_univ ρ) (fun ρ _ h0 => heν ρ fun h0' => h0 (by simp [h0']))).trans
      hesum
  have hzero := Fintype.linearIndependent_iff.mp (linearIndependent_generator hν (hs ν hν))
    (fun ρ => e ρ.1) hesub
  have he0 : e ρ = 0 := by
    by_cases h0 : e ρ = 0
    · exact h0
    · exact hzero ⟨ρ, heν ρ h0⟩
  rw [he] at he0
  linarith

/-- **The cones of the contraction are strongly convex** when `J₋` is not empty. A line in `cone(u_{J₊ ∪ J₋}) + λ` would give a nonnegative relation among the generators of the rays of `ν` and `j`, which is a multiple of `c`, and `c` has a negative coefficient. -/
theorem IsExtremalRay.isStronglyConvex_contractCone (hc : F.IsComplete)
    (hs : F.IsSimplicialFan) (hR : F.IsExtremalRay R) {σ₀ σ₀' : PointedCone ℝ (NR n)}
    (hw₀ : F.IsWallPair σ₀ σ₀') (W₀ : F.WallData σ₀ σ₀') (hW₀ : W₀.curveClass ∈ R)
    {ν : PointedCone ℝ (NR n)} (hν : F.IsMaximalCone ν) {k : F.Ray}
    (hk : W₀.curveClass k < 0) : IsStronglyConvex (F.contractCone W₀.curveClass ν) := by
  by_cases hneg : F.negCone W₀.curveClass ≤ ν
  · obtain ⟨j, hcj, hjν, hj⟩ := hR.exists_ray_not_le hc hs hw₀ W₀ hW₀ hν hneg
    intro v hv hnv
    obtain ⟨a, ha0, haP, rfl⟩ := (mem_hull_generator_iff (fun ρ : F.Ray => ρ.1 ≤ ν ∨
      (F.negCone W₀.curveClass ≤ ν ∧ W₀.curveClass ρ ≠ 0))).mp hv
    obtain ⟨a', ha'0, ha'P, ha'⟩ := (mem_hull_generator_iff (fun ρ : F.Ray => ρ.1 ≤ ν ∨
      (F.negCone W₀.curveClass ≤ ν ∧ W₀.curveClass ρ ≠ 0))).mp hnv
    have hP : ∀ ρ : F.Ray, (ρ.1 ≤ ν ∨ (F.negCone W₀.curveClass ≤ ν ∧ W₀.curveClass ρ ≠ 0)) →
        ρ ≠ j → ρ.1 ≤ ν := by
      rintro ρ (hρ | ⟨-, hρ⟩) hρj
      · exact hρ
      · exact hj ρ hρ hρj
    have hd : ∀ ρ : F.Ray, a ρ + a' ρ ≠ 0 → ρ ≠ j → ρ.1 ≤ ν := by
      intro ρ h0 hρj
      refine hP ρ ?_ hρj
      by_contra hn
      exact h0 (by rw [haP ρ hn, ha'P ρ hn, add_zero])
    have hsum : ∑ ρ, (a ρ + a' ρ) • toNR (F.generator ρ) = 0 := by
      simp only [add_smul, Finset.sum_add_distrib, ha', add_neg_cancel]
    have hR' := eq_smul_of_sum_eq_zero hs hw₀ W₀ hν.mem hcj.ne' hj
      (d := fun ρ => a ρ + a' ρ) hd hsum
    have hlam0 : 0 ≤ (a j + a' j) / W₀.curveClass j :=
      div_nonneg (add_nonneg (ha0 j) (ha'0 j)) hcj.le
    have hlam : (a j + a' j) / W₀.curveClass j = 0 := by
      have h1 : a k + a' k = (a j + a' j) / W₀.curveClass j * W₀.curveClass k := hR' k
      have h2 : 0 ≤ a k + a' k := add_nonneg (ha0 k) (ha'0 k)
      by_contra hne
      have h3 : 0 < (a j + a' j) / W₀.curveClass j := lt_of_le_of_ne hlam0 (Ne.symm hne)
      have h4 := mul_neg_of_pos_of_neg h3 hk
      linarith
    have ha : ∀ ρ, a ρ = 0 := by
      intro ρ
      have h1 : a ρ + a' ρ = (a j + a' j) / W₀.curveClass j * W₀.curveClass ρ := hR' ρ
      rw [hlam, zero_mul] at h1
      linarith [ha0 ρ, ha'0 ρ]
    simp only [ha, zero_smul, Finset.sum_const_zero]
  · rw [contractCone_of_not_le hν.mem hneg]
    exact F.stronglyConvex ν hν.mem

/-- **The contraction as a fan.** When `J₋` is not empty, the cones of the contraction are strongly convex, and the contraction is a fan. -/
noncomputable def IsExtremalRay.contractionFan (hc : F.IsComplete) (hs : F.IsSimplicialFan)
    (hR : F.IsExtremalRay R) {σ₀ σ₀' : PointedCone ℝ (NR n)} (hw₀ : F.IsWallPair σ₀ σ₀')
    (W₀ : F.WallData σ₀ σ₀') (hW₀ : W₀.curveClass ∈ R) (hJ : ∃ k, W₀.curveClass k < 0) :
    Fan n where
  cones := F.contraction W₀.curveClass
  finite := (hR.isQuasiFan_contraction hc hs hw₀ W₀ hW₀).1
  rational := (hR.isQuasiFan_contraction hc hs hw₀ W₀ hW₀).2.1
  stronglyConvex σ hσ := by
    obtain ⟨ν, hν, hσν⟩ := hσ
    obtain ⟨k, hk⟩ := hJ
    exact (hR.isStronglyConvex_contractCone hc hs hw₀ W₀ hW₀ hν hk).mono hσν.le
  face_mem := (hR.isQuasiFan_contraction hc hs hw₀ W₀ hW₀).2.2.1
  inter_face := (hR.isQuasiFan_contraction hc hs hw₀ W₀ hW₀).2.2.2

/-- The cones of the contraction fan are the cones of the contraction. -/
theorem IsExtremalRay.cones_contractionFan (hc : F.IsComplete) (hs : F.IsSimplicialFan)
    (hR : F.IsExtremalRay R) {σ₀ σ₀' : PointedCone ℝ (NR n)} (hw₀ : F.IsWallPair σ₀ σ₀')
    (W₀ : F.WallData σ₀ σ₀') (hW₀ : W₀.curveClass ∈ R) (hJ : ∃ k, W₀.curveClass k < 0) :
    (hR.contractionFan hc hs hw₀ W₀ hW₀ hJ).cones = F.contraction W₀.curveClass :=
  rfl

/-- A fan that refines the cones of another fan has the same support. -/
theorem support_eq_of_refines {G : Fan n} (h : F.Refines G.cones) : G.support = F.support := by
  ext x
  rw [G.mem_support, F.mem_support]
  constructor
  · rintro ⟨τ, hτ, hx⟩
    have hx' : x ∈ (τ : Set (NR n)) := hx
    rw [h.2 τ hτ] at hx'
    obtain ⟨σ, ⟨hσ, -⟩, hxσ⟩ := Set.mem_iUnion₂.mp hx'
    exact ⟨σ, hσ, hxσ⟩
  · rintro ⟨σ, hσ, hx⟩
    obtain ⟨τ, hτ, hστ⟩ := h.1 σ hσ
    exact ⟨τ, hτ, hστ hx⟩

/-- A ray of a set of cones refined by the fan is a cone of the fan. -/
theorem mem_cones_of_refines {T : Set (PointedCone ℝ (NR n))} (h : F.Refines T)
    {τ : PointedCone ℝ (NR n)} (hτ : τ ∈ T) (hray : IsRay τ) : τ ∈ F.cones := by
  obtain ⟨v, -, rfl⟩ := hray
  have hx : toNR v ∈ ((latticeCone {v} : PointedCone ℝ (NR n)) : Set (NR n)) :=
    toNR_mem_latticeCone (Finset.mem_singleton_self v)
  rw [h.2 _ hτ] at hx
  obtain ⟨σ, ⟨hσ, hστ⟩, hxσ⟩ := Set.mem_iUnion₂.mp hx
  rw [← le_antisymm hστ (latticeCone_singleton_le.mpr hxσ)]
  exact hσ

/-- **The contraction is birational** when `J₋` is not empty: the contraction fan has the same support as `F`. So it is not of fibre type. -/
theorem IsExtremalRay.support_contractionFan (hc : F.IsComplete) (hs : F.IsSimplicialFan)
    (hR : F.IsExtremalRay R) {σ₀ σ₀' : PointedCone ℝ (NR n)} (hw₀ : F.IsWallPair σ₀ σ₀')
    (W₀ : F.WallData σ₀ σ₀') (hW₀ : W₀.curveClass ∈ R) (hJ : ∃ k, W₀.curveClass k < 0) :
    (hR.contractionFan hc hs hw₀ W₀ hW₀ hJ).support = F.support :=
  support_eq_of_refines (hR.refines_contraction hc hs hw₀ W₀ hW₀)

/-- The contraction fan is complete. -/
theorem IsExtremalRay.isComplete_contractionFan (hc : F.IsComplete) (hs : F.IsSimplicialFan)
    (hR : F.IsExtremalRay R) {σ₀ σ₀' : PointedCone ℝ (NR n)} (hw₀ : F.IsWallPair σ₀ σ₀')
    (W₀ : F.WallData σ₀ σ₀') (hW₀ : W₀.curveClass ∈ R) (hJ : ∃ k, W₀.curveClass k < 0) :
    (hR.contractionFan hc hs hw₀ W₀ hW₀ hJ).IsComplete := by
  unfold IsComplete
  rw [hR.support_contractionFan hc hs hw₀ W₀ hW₀ hJ]
  exact hc

/-- **The rays of a cone of the star are faces of its cone of the contraction** when `J₋` has two rays. A decomposition `a x + y = r u_ρ` in the cone gives a linear relation `a α + α' - r δ_ρ` among the generators of the rays of `ν` and `j`, a multiple `s c` of `c`. It is nonnegative at `j` and at a ray of `J₋` other than `ρ`, so `s = 0`, and `x` is a multiple of `u_ρ`. -/
theorem IsExtremalRay.isFaceOf_contractCone (hc : F.IsComplete) (hs : F.IsSimplicialFan)
    (hR : F.IsExtremalRay R) {σ₀ σ₀' : PointedCone ℝ (NR n)} (hw₀ : F.IsWallPair σ₀ σ₀')
    (W₀ : F.WallData σ₀ σ₀') (hW₀ : W₀.curveClass ∈ R) {ν : PointedCone ℝ (NR n)}
    (hν : F.IsMaximalCone ν) (hneg : F.negCone W₀.curveClass ≤ ν) {k k' : F.Ray}
    (hk : W₀.curveClass k < 0) (hk' : W₀.curveClass k' < 0) (hkk' : k ≠ k') {ρ : F.Ray}
    (hρ : ρ.1 ≤ ν) : ρ.1.IsFaceOf (F.contractCone W₀.curveClass ν) := by
  classical
  obtain ⟨j, hcj, hjν, hj⟩ := hR.exists_ray_not_le hc hs hw₀ W₀ hW₀ hν hneg
  have hρj : ρ ≠ j := fun h' => hjν (by rw [← h']; exact hρ)
  have hP : ∀ ρ' : F.Ray, (ρ'.1 ≤ ν ∨ (F.negCone W₀.curveClass ≤ ν ∧ W₀.curveClass ρ' ≠ 0)) →
      ρ' ≠ j → ρ'.1 ≤ ν := by
    rintro ρ' (hρ' | ⟨-, hρ'⟩) hρ'j
    · exact hρ'
    · exact hj ρ' hρ' hρ'j
  refine ⟨hρ.trans (le_contractCone hν.mem _), fun {x y a} hx hy ha hxy => ?_⟩
  obtain ⟨α, hα0, hαP, rfl⟩ := (mem_hull_generator_iff (fun ρ' : F.Ray => ρ'.1 ≤ ν ∨
    (F.negCone W₀.curveClass ≤ ν ∧ W₀.curveClass ρ' ≠ 0))).mp hx
  obtain ⟨α', hα'0, hα'P, rfl⟩ := (mem_hull_generator_iff (fun ρ' : F.Ray => ρ'.1 ≤ ν ∨
    (F.negCone W₀.curveClass ≤ ν ∧ W₀.curveClass ρ' ≠ 0))).mp hy
  rw [← F.latticeCone_generator ρ] at hxy ⊢
  obtain ⟨r, -, hr⟩ := mem_latticeCone_singleton.mp hxy
  -- the relation `d = a α + α' - r δ_ρ`
  obtain ⟨d, hd⟩ : ∃ d : F.Ray → ℝ,
      ∀ ρ', d ρ' = a * α ρ' + α' ρ' - if ρ' = ρ then r else 0 := ⟨_, fun _ => rfl⟩
  have hdsum : ∑ ρ', d ρ' • toNR (F.generator ρ') = 0 := by
    have hterm : ∀ ρ', d ρ' • toNR (F.generator ρ') =
        a • (α ρ' • toNR (F.generator ρ')) + α' ρ' • toNR (F.generator ρ') -
          if ρ' = ρ then r • toNR (F.generator ρ') else 0 := fun ρ' => by
      rw [hd, sub_smul, add_smul, mul_smul, ite_smul, zero_smul]
    simp only [hterm]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.smul_sum,
      Finset.sum_ite_eq' Finset.univ ρ, ite_eq_left (Finset.mem_univ ρ), hr, sub_self]
  have hdν : ∀ ρ', d ρ' ≠ 0 → ρ' ≠ j → ρ'.1 ≤ ν := by
    intro ρ' h0 hρ'j
    by_cases hρ'ρ : ρ' = ρ
    · rw [hρ'ρ]
      exact hρ
    · refine hP ρ' ?_ hρ'j
      by_contra hn
      apply h0
      rw [hd, ite_eq_right hρ'ρ, hαP ρ' hn, hα'P ρ' hn, mul_zero, add_zero, sub_zero]
  have hR' := eq_smul_of_sum_eq_zero hs hw₀ W₀ hν.mem hcj.ne' hj hdν hdsum
  have hdj : d j = a * α j + α' j := by rw [hd, ite_eq_right (Ne.symm hρj), sub_zero]
  have hlam0 : 0 ≤ d j / W₀.curveClass j :=
    div_nonneg (by rw [hdj]; exact add_nonneg (mul_nonneg ha.le (hα0 j)) (hα'0 j)) hcj.le
  -- a ray of `J₋` other than `ρ`
  obtain ⟨k'', hk'', hk''ρ⟩ : ∃ k'', W₀.curveClass k'' < 0 ∧ k'' ≠ ρ := by
    by_cases hkρ : k = ρ
    · exact ⟨k', hk', fun h' => hkk' (hkρ.trans h'.symm)⟩
    · exact ⟨k, hk, hkρ⟩
  have hlam : d j / W₀.curveClass j = 0 := by
    have h1 : d k'' = d j / W₀.curveClass j * W₀.curveClass k'' := hR' k''
    have h2 : d k'' = a * α k'' + α' k'' := by rw [hd, ite_eq_right hk''ρ, sub_zero]
    by_contra hne
    have h3 : 0 < d j / W₀.curveClass j := lt_of_le_of_ne hlam0 (Ne.symm hne)
    have h4 := mul_neg_of_pos_of_neg h3 hk''
    have h5 : 0 ≤ a * α k'' + α' k'' := add_nonneg (mul_nonneg ha.le (hα0 k'')) (hα'0 k'')
    linarith
  -- so `α` vanishes outside `ρ`
  have hα : ∀ ρ', ρ' ≠ ρ → α ρ' = 0 := by
    intro ρ' hρ'
    have h1 : d ρ' = d j / W₀.curveClass j * W₀.curveClass ρ' := hR' ρ'
    rw [hlam, zero_mul, hd, ite_eq_right hρ', sub_zero] at h1
    have h5 := mul_nonneg ha.le (hα0 ρ')
    have h6 := hα'0 ρ'
    have h7 : a * α ρ' = 0 := by linarith
    rcases mul_eq_zero.mp h7 with h8 | h8
    · exact absurd h8 ha.ne'
    · exact h8
  rw [Finset.sum_eq_single ρ]
  · exact mem_latticeCone_singleton.mpr ⟨α ρ, hα0 ρ, rfl⟩
  · intro ρ' _ hρ'
    rw [hα ρ' hρ', zero_smul]
  · intro h'
    exact absurd (Finset.mem_univ ρ) h'

/-- **The contraction is small** when `J₋` has two rays: the contraction fan has the same rays as `F`. So no divisor is contracted, and the contraction is a flipping contraction. -/
theorem IsExtremalRay.rays_contractionFan (hc : F.IsComplete) (hs : F.IsSimplicialFan)
    (hR : F.IsExtremalRay R) {σ₀ σ₀' : PointedCone ℝ (NR n)} (hw₀ : F.IsWallPair σ₀ σ₀')
    (W₀ : F.WallData σ₀ σ₀') (hW₀ : W₀.curveClass ∈ R) {k k' : F.Ray}
    (hk : W₀.curveClass k < 0) (hk' : W₀.curveClass k' < 0) (hkk' : k ≠ k') :
    (hR.contractionFan hc hs hw₀ W₀ hW₀ ⟨k, hk⟩).rays = F.rays := by
  ext τ
  constructor
  · rintro ⟨hτ, hray⟩
    exact ⟨mem_cones_of_refines (hR.refines_contraction hc hs hw₀ W₀ hW₀) hτ hray, hray⟩
  · rintro ⟨hτ, hray⟩
    obtain ⟨ν, hτν, hν⟩ := F.exists_le_isMaximalCone hτ
    refine ⟨⟨ν, hν, ?_⟩, hray⟩
    by_cases hneg : F.negCone W₀.curveClass ≤ ν
    · exact hR.isFaceOf_contractCone hc hs hw₀ W₀ hW₀ hν hneg hk hk' hkk'
        (ρ := ⟨τ, hτ, hray⟩) hτν
    · rw [contractCone_of_not_le hν.mem hneg]
      exact F.isFaceOf_of_le hν.mem ⟨τ, hτ, hray⟩ hτν

end Fan

end MinimalModel.Toric
