/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import MinimalModel.Toric.Divisor

/-!
# The wall relation

Let `σ` and `σ'` be two smooth cones of full dimension of a fan that share all generators but one. So `σ` is spanned by a basis `v, u₁, ..., uₖ` of the lattice `N` and `σ'` is spanned by a basis `v', u₁, ..., uₖ`, with `v ≠ v'`. The two cones meet in the wall spanned by `u₁, ..., uₖ`, and there are unique integers `bᵢ` with `v + v' = Σ bᵢ uᵢ`. This is the wall relation of Cox, Little and Schenck, Section 6.4. In a smooth complete fan, each wall is the intersection of two maximal cones of this form, and the numbers `bᵢ` give the intersection numbers of the curve of the wall.

The proof works with the coordinates in the two bases. The coordinate of `v'` at `v` is a unit, so it is `1` or `-1`. If it were `1`, then a point of `σ ∩ σ'` would have a positive coordinate at `v'` in `σ'` and at `v` in `σ`. Since `σ ∩ σ'` is a face of each cone, `v'` would lie in `σ` and `v` in `σ'`, and this forces `v = v'`.

## Main results

* `realForm_toNR`: an integer linear form on `N` extends to a real linear form on `N_ℝ`.
* `IsLatticeBasis.repr_nonneg`: a lattice point in the cone of a lattice basis has nonnegative coordinates.
* `Fan.exists_unique_wall_relation`: the wall relation.
-/

namespace MinimalModel.Toric

variable {n : ℕ}

/-- The vector of a sum of lattice points is the sum of their vectors. -/
theorem toNR_add (v w : Fin n → ℤ) : toNR (v + w) = toNR v + toNR w := by
  funext i
  simp

/-- The vector of an integer combination of lattice points. -/
theorem toNR_sum_smul {ι : Type*} (s : Finset ι) (a : ι → ℤ) (w : ι → Fin n → ℤ) :
    toNR (∑ i ∈ s, a i • w i) = ∑ i ∈ s, (a i : ℝ) • toNR (w i) := by
  funext k
  simp [Finset.sum_apply]

/-- The extension to `N_ℝ` of an integer linear form `f` on `N`: the real linear form with the same values on the standard basis. -/
noncomputable def realForm (f : (Fin n → ℤ) →ₗ[ℤ] ℤ) : NR n →ₗ[ℝ] ℝ :=
  linearForm fun j => ((f fun k => if j = k then 1 else 0 : ℤ) : ℝ)

/-- The real extension of `f` takes the value `f v` at the vector of a lattice point `v`. -/
theorem realForm_toNR (f : (Fin n → ℤ) →ₗ[ℤ] ℤ) (v : Fin n → ℤ) :
    realForm f (toNR v) = (f v : ℝ) := by
  rw [LinearMap.pi_apply_eq_sum_univ f v]
  simp only [realForm, linearForm_apply, toNR_apply, smul_eq_mul, Int.cast_sum, Int.cast_mul]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

section Basis

variable {ι : Type*}

/-- A family of lattice points is a basis of the lattice `N = ℤⁿ`. The cone spanned by such a family is a smooth cone of full dimension (Cox, Little and Schenck, Definition 1.2.16). -/
def IsLatticeBasis (u : ι → Fin n → ℤ) : Prop :=
  LinearIndependent ℤ u ∧ ⊤ ≤ Submodule.span ℤ (Set.range u)

/-- The basis of `N` given by a lattice basis. -/
noncomputable def IsLatticeBasis.basis {u : ι → Fin n → ℤ} (h : IsLatticeBasis u) :
    Module.Basis ι ℤ (Fin n → ℤ) :=
  Module.Basis.mk h.1 h.2

/-- The vectors of the basis are the points of the family. -/
@[simp]
theorem IsLatticeBasis.coe_basis {u : ι → Fin n → ℤ} (h : IsLatticeBasis u) :
    ⇑h.basis = u :=
  Module.Basis.coe_mk _ _

/-- The coordinates of a point of a lattice basis. -/
theorem IsLatticeBasis.repr_self [DecidableEq ι] {u : ι → Fin n → ℤ} (h : IsLatticeBasis u)
    (i j : ι) : h.basis.repr (u i) j = if i = j then 1 else 0 := by
  rw [(congrFun h.coe_basis i).symm, Module.Basis.repr_self, Finsupp.single_apply]

/-- The cone spanned by a family of lattice points. -/
noncomputable def familyCone (u : ι → Fin n → ℤ) : PointedCone ℝ (NR n) :=
  PointedCone.hull ℝ (Set.range fun i => toNR (u i))

/-- The cone of a family contains the vector of each point of the family. -/
theorem toNR_mem_familyCone (u : ι → Fin n → ℤ) (i : ι) : toNR (u i) ∈ familyCone u :=
  Submodule.subset_span ⟨i, rfl⟩

/-- A vector is in the cone of a finite family when it is a nonnegative combination of the family. -/
theorem mem_familyCone [Fintype ι] {u : ι → Fin n → ℤ} {x : NR n} :
    x ∈ familyCone u ↔ ∃ c : ι → ℝ, (∀ i, 0 ≤ c i) ∧ ∑ i, c i • toNR (u i) = x := by
  unfold familyCone
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨fun i => c i, fun i => (c i).2, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨fun i => ⟨c i, hc i⟩, rfl⟩

/-- If the vector of a lattice point `x` is in the cone of a lattice basis, then the coordinates of `x` in the basis are nonnegative. -/
theorem IsLatticeBasis.repr_nonneg [Fintype ι] {u : ι → Fin n → ℤ} (h : IsLatticeBasis u)
    {x : Fin n → ℤ} (hx : toNR x ∈ familyCone u) (i : ι) : 0 ≤ h.basis.repr x i := by
  classical
  obtain ⟨c, hc, hsum⟩ := mem_familyCone.mp hx
  have h2 : (h.basis.repr x i : ℝ) = c i := by
    calc (h.basis.repr x i : ℝ) = realForm (h.basis.coord i) (toNR x) := by
          rw [realForm_toNR, Module.Basis.coord_apply]
      _ = realForm (h.basis.coord i) (∑ j, c j • toNR (u j)) := by rw [hsum]
      _ = ∑ j, c j * ((h.basis.coord i (u j) : ℤ) : ℝ) := by
          simp only [map_sum, map_smul, realForm_toNR, smul_eq_mul]
      _ = c i := by
          simp only [Module.Basis.coord_apply, h.repr_self]
          simp
  have h3 := hc i
  rw [← h2] at h3
  exact_mod_cast h3

end Basis

section Wall

variable {κ : Type*} [Fintype κ]

/-- The coordinates of `a₀ • v + Σ aᵢ uᵢ` in a lattice basis `v, u₁, ..., uₖ` are `a₀, a₁, ..., aₖ`. -/
theorem IsLatticeBasis.repr_elim' {v : Fin n → ℤ} {u : κ → Fin n → ℤ}
    (h : IsLatticeBasis (Option.elim' v u)) (a₀ : ℤ) (a : κ → ℤ) :
    ⇑(h.basis.repr (a₀ • v + ∑ i, a i • u i)) = Option.elim' a₀ a := by
  have he : a₀ • v + ∑ i, a i • u i = ∑ o, Option.elim' a₀ a o • h.basis o := by
    rw [Fintype.sum_option, h.coe_basis]
    rfl
  rw [he, Module.Basis.repr_sum_self]

/-- Two combinations of a lattice basis `v, u₁, ..., uₖ` with the same value have the same coefficients. -/
theorem IsLatticeBasis.eq_of_elim' {v : Fin n → ℤ} {u : κ → Fin n → ℤ}
    (h : IsLatticeBasis (Option.elim' v u)) {a₀ b₀ : ℤ} {a b : κ → ℤ}
    (hab : a₀ • v + ∑ i, a i • u i = b₀ • v + ∑ i, b i • u i) : a₀ = b₀ ∧ a = b := by
  have he : Option.elim' a₀ a = Option.elim' b₀ b := by
    rw [← h.repr_elim' a₀ a, ← h.repr_elim' b₀ b, hab]
  exact ⟨congrFun he none, funext fun i => congrFun he (some i)⟩

/-- The wall relation (Cox, Little and Schenck, Section 6.4). Let `σ` be a cone of a fan spanned by a lattice basis `v, u₁, ..., uₖ`, and let `σ'` be a cone of the fan spanned by a lattice basis `v', u₁, ..., uₖ`, with `v ≠ v'`. Then there are unique integers `bᵢ` with `v + v' = Σ bᵢ uᵢ`. -/
theorem Fan.exists_unique_wall_relation (F : Fan n) {u : κ → Fin n → ℤ} {v v' : Fin n → ℤ}
    (hB : IsLatticeBasis (Option.elim' v u)) (hB' : IsLatticeBasis (Option.elim' v' u))
    (hσ : familyCone (Option.elim' v u) ∈ F.cones)
    (hσ' : familyCone (Option.elim' v' u) ∈ F.cones) (hne : v ≠ v') :
    ∃! b : κ → ℤ, v + v' = ∑ i, b i • u i := by
  classical
  obtain ⟨c₀, c, hv'⟩ : ∃ (c₀ : ℤ) (c : κ → ℤ), v' = c₀ • v + ∑ i, c i • u i := by
    have h := hB.basis.sum_repr v'
    rw [Fintype.sum_option, hB.coe_basis] at h
    exact ⟨hB.basis.repr v' none, fun i => hB.basis.repr v' (some i), h.symm⟩
  obtain ⟨d₀, d, hv⟩ : ∃ (d₀ : ℤ) (d : κ → ℤ), v = d₀ • v' + ∑ i, d i • u i := by
    have h := hB'.basis.sum_repr v
    rw [Fintype.sum_option, hB'.coe_basis] at h
    exact ⟨hB'.basis.repr v none, fun i => hB'.basis.repr v (some i), h.symm⟩
  have hsub : v = (d₀ * c₀) • v + ∑ i, (d₀ * c i + d i) • u i := by
    calc v = d₀ • v' + ∑ i, d i • u i := hv
      _ = d₀ • (c₀ • v + ∑ i, c i • u i) + ∑ i, d i • u i := by rw [hv']
      _ = (d₀ * c₀) • v + ∑ i, (d₀ * c i + d i) • u i := by
        simp only [smul_add, Finset.smul_sum, smul_smul, add_smul, Finset.sum_add_distrib,
          add_assoc]
  have hone : (1 : ℤ) • v + ∑ i, (0 : ℤ) • u i =
      (d₀ * c₀) • v + ∑ i, (d₀ * c i + d i) • u i := by
    simp only [one_smul, zero_smul, Finset.sum_const_zero, add_zero]
    exact hsub
  obtain ⟨h₀, hcoef⟩ := hB.eq_of_elim' hone
  rcases Int.eq_one_or_neg_one_of_mul_eq_one (show c₀ * d₀ = 1 by rw [mul_comm]; exact h₀.symm)
    with hc₀ | hc₀
  · exfalso
    have hv'R : toNR v' = toNR v + ∑ i, (c i : ℝ) • toNR (u i) := by
      rw [hv', hc₀, one_smul, toNR_add, toNR_sum_smul]
    have hgen : ∀ i, toNR (u i) ∈ familyCone (Option.elim' v u) :=
      fun i => toNR_mem_familyCone _ (some i)
    have hgen' : ∀ i, toNR (u i) ∈ familyCone (Option.elim' v' u) :=
      fun i => toNR_mem_familyCone _ (some i)
    have hv0 : toNR v ∈ familyCone (Option.elim' v u) := toNR_mem_familyCone _ none
    have hv0' : toNR v' ∈ familyCone (Option.elim' v' u) := toNR_mem_familyCone _ none
    have hy' : ∑ i, |(c i : ℝ)| • toNR (u i) ∈ familyCone (Option.elim' v' u) :=
      Submodule.sum_mem _ fun i _ => PointedCone.smul_mem _ (abs_nonneg _) (hgen' i)
    have hy : ∑ i, ((c i : ℝ) + |(c i : ℝ)|) • toNR (u i) ∈ familyCone (Option.elim' v u) :=
      Submodule.sum_mem _ fun i _ =>
        PointedCone.smul_mem _ (by linarith [neg_abs_le (c i : ℝ)]) (hgen i)
    have hp : toNR v' + ∑ i, |(c i : ℝ)| • toNR (u i) =
        toNR v + ∑ i, ((c i : ℝ) + |(c i : ℝ)|) • toNR (u i) := by
      rw [hv'R, add_assoc, ← Finset.sum_add_distrib]
      simp only [add_smul]
    have hpinf : toNR v' + ∑ i, |(c i : ℝ)| • toNR (u i) ∈
        familyCone (Option.elim' v u) ⊓ familyCone (Option.elim' v' u) :=
      Submodule.mem_inf.mpr ⟨by rw [hp]; exact add_mem hv0 hy, add_mem hv0' hy'⟩
    have hv'σ : toNR v' ∈ familyCone (Option.elim' v u) := by
      have h1 := (F.inter_face_right hσ hσ').mem_of_smul_add_mem hv0' hy' one_pos
        (by rw [one_smul]; exact hpinf)
      exact (Submodule.mem_inf.mp h1).1
    have hvσ' : toNR v ∈ familyCone (Option.elim' v' u) := by
      have h1 := (F.inter_face _ hσ _ hσ').mem_of_smul_add_mem hv0 hy one_pos
        (by rw [one_smul, ← hp]; exact hpinf)
      exact (Submodule.mem_inf.mp h1).2
    have hcnn : ∀ i, 0 ≤ c i := by
      intro i
      have h1 := hB.repr_nonneg hv'σ (some i)
      rw [hv', congrFun (hB.repr_elim' c₀ c) (some i)] at h1
      exact h1
    have hdnn : ∀ i, 0 ≤ d i := by
      intro i
      have h1 := hB'.repr_nonneg hvσ' (some i)
      rw [hv, congrFun (hB'.repr_elim' d₀ d) (some i)] at h1
      exact h1
    have hd₀ : d₀ = 1 := by
      rw [hc₀, mul_one] at h₀
      exact h₀.symm
    have hc0 : ∀ i, c i = 0 := by
      intro i
      have h2 := congrFun hcoef i
      simp only [hd₀, one_mul] at h2
      have := hcnn i
      have := hdnn i
      omega
    apply hne
    rw [hv', hc₀, one_smul]
    simp only [hc0, zero_smul, Finset.sum_const_zero, add_zero]
  · have hcase : v + v' = ∑ i, c i • u i := by
      rw [hv', hc₀, neg_smul, one_smul, ← add_assoc, add_neg_cancel, zero_add]
    refine ⟨c, hcase, fun b hb => ?_⟩
    have h3 : (0 : ℤ) • v + ∑ i, b i • u i = (0 : ℤ) • v + ∑ i, c i • u i := by
      rw [← hb, ← hcase]
    exact (hB.eq_of_elim' h3).2

end Wall

end MinimalModel.Toric
