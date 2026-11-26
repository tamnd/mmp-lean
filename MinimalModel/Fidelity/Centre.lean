/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import MinimalModel.Fidelity.AffineLine

/-!
# The centre of a valuation and the log discrepancy of a prime divisor

This file proves the hypothesis `Pair.HasDivisorLogDiscrepancy` of `MinimalModel/Statements/Classes.lean` for every pair. So the implications plt to klt, canonical to klt, terminal to klt and plt to lc hold with no extra hypothesis.

## The steps

* A valuation of `k(X)` has at most one centre on `X` (`IsCentre.eq`). A centre `x` gives a morphism from the spectrum of the valuation ring to `X`, through the stalk at `x`. Two centres give two lifts of the same square, and the valuative criterion for the separated morphism `X → Spec k` makes them equal. The closed point goes to the centre, so the two centres are equal.
* Let `Q` be a prime divisor that is a centre of `v`, and let `v` take the value `exp (-1)`. The stalk at `Q` is a discrete valuation ring, and each nonzero `g` is a unit times a power of a uniformizer. The units have valuation one, so `v g = exp (-ord_Q g)` (`IsCentre.valuation_eq_exp`). Thus the valuation ring of `v` is the stalk at `Q`, and the order of a top form along `v` is the coefficient of the canonical divisor at `Q`.
* With these, the log discrepancy of `v` is `1 + K Q - (K Q + Δ Q) = 1 - Δ Q` (`Pair.hasDivisorLogDiscrepancy`).

On a variety of dimension one, a centre of a divisorial valuation is not the generic point, so it has coheight one. Thus each divisorial valuation with a log discrepancy is not exceptional, and its log discrepancy is `1 - Δ Q` for a prime divisor `Q`. This gives the classes of the pairs on a curve from the coefficients of the boundary.
-/

universe u

open AlgebraicGeometry CategoryTheory Order

noncomputable section

namespace MinimalModel

variable {k : Type u} [Field k] {X : NormalVariety k}

/-! ## The uniqueness of the centre -/

/-- The map from the stalk at a centre of `v` to the valuation ring of `v`. -/
def centreStalkHom {v : Valuation (FF X) VZ} {x : X.toScheme} (hx : IsCentre v x) :
    X.toScheme.presheaf.stalk x ⟶ CommRingCat.of v.valuationSubring :=
  CommRingCat.ofHom ((algebraMap (X.toScheme.presheaf.stalk x) (FF X)).codRestrict
    v.valuationSubring fun s => (v.mem_valuationSubring_iff _).mpr (hx.1 s))

/-- The map from the stalk at a centre to the valuation ring is local. -/
theorem isLocalHom_centreStalkHom {v : Valuation (FF X) VZ} {x : X.toScheme} (hx : IsCentre v x) :
    IsLocalHom (centreStalkHom hx).hom := by
  refine ⟨fun s hs => ?_⟩
  by_contra hns
  have h1 := hx.2 s ((IsLocalRing.mem_maximalIdeal s).mpr hns)
  obtain ⟨b, hb⟩ := hs.exists_right_inv
  have hb' : algebraMap _ (FF X) s * (b : FF X) = 1 := congrArg Subtype.val hb
  have hvb : v (b : FF X) ≤ 1 := (v.mem_valuationSubring_iff _).mp b.2
  have h2 := congrArg v hb'
  rw [map_mul, map_one] at h2
  exact absurd h2 ((mul_le_of_le_one_right' hvb).trans_lt h1).ne

/-- The morphism from the spectrum of the valuation ring of `v` to `X` given by a centre of `v`. -/
def centreMorphism {v : Valuation (FF X) VZ} {x : X.toScheme} (hx : IsCentre v x) :
    Spec (CommRingCat.of v.valuationSubring) ⟶ X.toScheme :=
  Spec.map (centreStalkHom hx) ≫ X.toScheme.fromSpecStalk x

/-- The morphism of a centre `x` sends the closed point to `x`. -/
theorem centreMorphism_closedPoint {v : Valuation (FF X) VZ} {x : X.toScheme} (hx : IsCentre v x) :
    centreMorphism hx (IsLocalRing.closedPoint v.valuationSubring) = x := by
  have := isLocalHom_centreStalkHom hx
  have h1 : Spec.map (centreStalkHom hx) (IsLocalRing.closedPoint v.valuationSubring) =
      IsLocalRing.closedPoint (X.toScheme.presheaf.stalk x) :=
    IsLocalRing.comap_closedPoint (centreStalkHom hx).hom
  show X.toScheme.fromSpecStalk x
    (Spec.map (centreStalkHom hx) (IsLocalRing.closedPoint v.valuationSubring)) = x
  rw [h1, Scheme.fromSpecStalk_closedPoint]

/-- On the generic point, the morphism of a centre is the morphism of the function field. -/
theorem specMap_comp_centreMorphism {v : Valuation (FF X) VZ} {x : X.toScheme} (hx : IsCentre v x) :
    Spec.map (CommRingCat.ofHom (algebraMap v.valuationSubring (FF X))) ≫ centreMorphism hx =
      X.toScheme.fromSpecStalk (genericPoint X.toScheme) := by
  have e : centreStalkHom hx ≫ CommRingCat.ofHom (algebraMap v.valuationSubring (FF X)) =
      X.toScheme.presheaf.stalkSpecializes
        ((genericPoint_spec X.toScheme).specializes trivial) :=
    CommRingCat.hom_ext (RingHom.ext fun _ => rfl)
  rw [centreMorphism, ← Category.assoc, ← Spec.map_comp, e,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk]

/-- A valuation of `k(X)` has at most one centre on `X`. This is the valuative criterion for the separated morphism `X → Spec k`. -/
theorem IsCentre.eq {v : Valuation (FF X) VZ} {x y : X.toScheme} (hx : IsCentre v x)
    (hy : IsCentre v y) : x = y := by
  have h1 : Spec.map (CommRingCat.ofHom (algebraMap v.valuationSubring (FF X))) ≫ centreMorphism hx =
      Spec.map (CommRingCat.ofHom (algebraMap v.valuationSubring (FF X))) ≫ centreMorphism hy := by
    rw [specMap_comp_centreMorphism, specMap_comp_centreMorphism]
  have h2 : centreMorphism hx ≫ X.str = centreMorphism hy ≫ X.str := by
    obtain ⟨a, ha⟩ := Spec.map_surjective (centreMorphism hx ≫ X.str)
    obtain ⟨b, hb⟩ := Spec.map_surjective (centreMorphism hy ≫ X.str)
    have hab : Spec.map (a ≫ CommRingCat.ofHom (algebraMap v.valuationSubring (FF X))) =
        Spec.map (b ≫ CommRingCat.ofHom (algebraMap v.valuationSubring (FF X))) := by
      rw [Spec.map_comp, Spec.map_comp, ha, hb, ← Category.assoc, ← Category.assoc, h1]
    have hab' := Spec.map_injective hab
    have hab'' : a = b :=
      CommRingCat.hom_ext (RingHom.ext fun s => Subtype.ext (congrArg (fun f => f.hom s) hab'))
    rw [← ha, ← hb, hab'']
  let S : ValuativeCommSq X.str :=
    { R := v.valuationSubring
      K := FF X
      i₁ := Spec.map (CommRingCat.ofHom (algebraMap v.valuationSubring (FF X))) ≫ centreMorphism hy
      i₂ := centreMorphism hy ≫ X.str
      commSq := ⟨Category.assoc _ _ _⟩ }
  have hu : Subsingleton S.commSq.LiftStruct := IsSeparated.valuativeCriterion X.str S
  have hl : (⟨centreMorphism hx, h1, h2⟩ : S.commSq.LiftStruct) = ⟨centreMorphism hy, rfl, rfl⟩ :=
    Subsingleton.elim _ _
  have hl' : centreMorphism hx = centreMorphism hy := congrArg CommSq.LiftStruct.l hl
  calc x = centreMorphism hx (IsLocalRing.closedPoint v.valuationSubring) :=
        (centreMorphism_closedPoint hx).symm
    _ = centreMorphism hy (IsLocalRing.closedPoint v.valuationSubring) := by rw [hl']
    _ = y := centreMorphism_closedPoint hy

/-! ## The valuation of a prime divisor -/

/-- A unit of the stalk at a centre has valuation one. -/
theorem IsCentre.valuation_unit {v : Valuation (FF X) VZ} {x : X.toScheme} (hx : IsCentre v x)
    (u : (X.toScheme.presheaf.stalk x)ˣ) :
    v (algebraMap _ (FF X) (u : X.toScheme.presheaf.stalk x)) = 1 := by
  have h1 := hx.1 (u : X.toScheme.presheaf.stalk x)
  have h2 := hx.1 ((u⁻¹ : (X.toScheme.presheaf.stalk x)ˣ) : X.toScheme.presheaf.stalk x)
  have h3 : v (algebraMap _ (FF X) (u : X.toScheme.presheaf.stalk x)) *
      v (algebraMap _ (FF X) ((u⁻¹ : (X.toScheme.presheaf.stalk x)ˣ) :
        X.toScheme.presheaf.stalk x)) = 1 := by
    rw [← Valuation.map_mul, ← RingHom.map_mul, Units.mul_inv, map_one, map_one]
  refine le_antisymm h1 ?_
  calc (1 : VZ) = _ := h3.symm
    _ ≤ _ := mul_le_of_le_one_right' h2

/-- Let the prime divisor `Q` be a centre of `v`, and let `v` take the value `exp (-1)`. Then `v` is the order along `Q`: `v g = exp (-ord_Q g)` for each nonzero `g`. -/
theorem IsCentre.valuation_eq_exp {v : Valuation (FF X) VZ} (hπ : ∃ π, v π = WithZero.exp (-1 : ℤ))
    {Q : PrimeDivisor X} (hQ : IsCentre v Q.1) {g : FF X} (hg : g ≠ 0) :
    v g = WithZero.exp (-ordAt g Q) := by
  have := isDiscreteValuationRing_stalk Q
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (X.toScheme.presheaf.stalk Q.1)
  obtain ⟨t, ht⟩ : ∃ t : FF X, algebraMap (X.toScheme.presheaf.stalk Q.1) (FF X) ϖ = t := ⟨_, rfl⟩
  have ht0 : t ≠ 0 := by
    rw [← ht]
    exact (map_ne_zero_iff _ (IsFractionRing.injective _ (FF X))).mpr hϖ.ne_zero
  have ht1 : Ring.ordFrac (X.toScheme.presheaf.stalk Q.1) t = WithZero.exp 1 := by
    rw [← ht]
    exact Ring.ordFrac_irreducible hϖ
  have hvt : v t < 1 := by
    rw [← ht]
    exact hQ.2 ϖ ((IsLocalRing.mem_maximalIdeal ϖ).mpr hϖ.not_isUnit)
  have hpow : ∀ f : FF X, f ≠ 0 → v f = v t ^ ordAt f Q := by
    intro f hf
    have h1 : Ring.ordFrac (X.toScheme.presheaf.stalk Q.1) (t ^ ordAt f Q) =
        Ring.ordFrac (X.toScheme.presheaf.stalk Q.1) f := by
      rw [map_zpow₀, ht1, ← WithZero.exp_zsmul, smul_eq_mul, mul_one]
      exact ((Scheme.ord_eq_iff Q.2 hf).mp rfl).symm
    obtain ⟨u, hu⟩ := Ring.associated_of_ordFrac_eq _ _ h1
    have h2 : v f = v (u • t ^ ordAt f Q) := by rw [hu]
    rw [h2, Units.smul_def, Algebra.smul_def, map_mul, hQ.valuation_unit u, one_mul, map_zpow₀]
  obtain ⟨π, hπ⟩ := hπ
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have hvt0 : v t ≠ 0 := (Valuation.ne_zero_iff v).mpr ht0
  obtain ⟨a, ha⟩ : ∃ a : ℤ, v t = WithZero.exp a := ⟨_, (WithZero.exp_log hvt0).symm⟩
  rw [ha, WithZero.exp_lt_one_iff] at hvt
  have h2 := hpow π hπ0
  rw [hπ, ha, ← WithZero.exp_zsmul, WithZero.exp_inj, smul_eq_mul] at h2
  have ha1 : a = -1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_neg_one
      (show a * ordAt π Q = -1 by rw [mul_comm]; exact h2.symm) with h | h <;> omega
  rw [hpow g hg, ha, ha1, ← WithZero.exp_zsmul, smul_eq_mul, mul_neg_one]

/-- The valuation ring of `v` is the stalk at a prime divisor `Q` that is a centre of `v`. -/
theorem IsCentre.integer_eq {v : Valuation (FF X) VZ} (hπ : ∃ π, v π = WithZero.exp (-1 : ℤ))
    {Q : PrimeDivisor X} (hQ : IsCentre v Q.1) : v.integer = stalkSubring Q.1 := by
  ext g
  by_cases hg : g = 0
  · subst hg
    exact ⟨fun _ => Subring.zero_mem _, fun _ => Subring.zero_mem _⟩
  · rw [Valuation.mem_integer_iff, hQ.valuation_eq_exp hπ hg, mem_stalkSubring_iff Q hg,
      WithZero.exp_le_one_iff, neg_nonpos]

/-- The order along `v` of the form of a divisor `D` is the coefficient of `D` at a prime divisor `Q` that is a centre of `v`. -/
theorem IsCentre.formOrd_eq {v : Valuation (FF X) VZ} (hπ : ∃ π, v π = WithZero.exp (-1 : ℤ))
    {Q : PrimeDivisor X} (hQ : IsCentre v Q.1) {D : Divisor ℤ X} {ω : TopForm X}
    (hD : IsDivOfForm D ω) {m : ℤ} (hm : FormOrd v ω m) : m = D Q := by
  obtain ⟨π, hπ'⟩ := hπ
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ'
    exact WithZero.exp_ne_zero hπ'.symm
  have key : ∀ n : ℤ, (-D Q ≤ n ↔ -n ≤ m) := by
    intro n
    have hg : π ^ n ≠ 0 := zpow_ne_zero n hπ0
    have hord : ordAt (π ^ n) Q = n := by
      have h1 := hQ.valuation_eq_exp ⟨π, hπ'⟩ hg
      rw [map_zpow₀, hπ', ← WithZero.exp_zsmul, WithZero.exp_inj, smul_eq_mul, mul_neg_one,
        neg_inj] at h1
      exact h1.symm
    have h2 := hm (π ^ n) hg
    rw [hQ.integer_eq ⟨π, hπ'⟩, hD.2 Q _ hg, hQ.valuation_eq_exp ⟨π, hπ'⟩ hg, hord,
      WithZero.exp_le_exp] at h2
    exact h2
  have h1 := (key (-m)).mpr (by omega)
  have h2 := (key (-D Q)).mp le_rfl
  omega

/-! ## The log discrepancy of a prime divisor -/

/-- Each divisorial valuation that is not exceptional has the log discrepancy `1 - Δ Q` for a prime divisor `Q`. Its centre is a prime divisor `Q`, the valuation is the order along `Q`, and the log discrepancy is `1 + K Q - (K Q + Δ Q)`. -/
theorem Pair.hasDivisorLogDiscrepancy (P : Pair X) : P.HasDivisorLogDiscrepancy := by
  intro v hv hne A hA
  have hne' : ∃ q, IsCentre v q ∧ coheight q = 1 := by
    by_contra h
    push_neg at h
    exact hne h
  obtain ⟨q, hq, hq1⟩ := hne'
  obtain ⟨x, hx, U, hxU, N, r, h, e, m, hhe, hm, hKΔ, rfl⟩ := hA
  have hqU : q ∈ U := by
    rw [← hx.eq hq]
    exact hxU
  let Q : PrimeDivisor X := ⟨q, hq1⟩
  have hπ := hv.2.1
  have he : ∀ i, e i = ordAt (h i) Q := fun i => by
    have h0 : h i ≠ 0 := by
      intro h0
      have h3 := hhe i
      rw [h0, map_zero] at h3
      exact WithZero.exp_ne_zero h3.symm
    have h3 := (hhe i).symm.trans (hq.valuation_eq_exp (Q := Q) hπ h0)
    rw [WithZero.exp_inj, neg_inj] at h3
    exact h3
  have hmK : m = P.K.K Q := hq.formOrd_eq (Q := Q) hπ P.K.isDiv hm
  refine ⟨Q, ?_⟩
  have hs : ∑ i, r i * (e i : ℝ) = P.KΔ Q := by
    rw [hKΔ Q hqU]
    exact Finset.sum_congr rfl fun i _ => by rw [he i]
  rw [hs, hmK]
  simp only [Pair.KΔ, Finsupp.add_apply, Divisor.toReal, Finsupp.mapRange_apply]
  ring

/-- A plt pair whose coefficients are less than one is klt. -/
theorem IsPlt.isKlt' {P : Pair X} (h : IsPlt P) (hΔ : ∀ Q, P.Δ Q < 1) : IsKlt P :=
  h.isKlt hΔ P.hasDivisorLogDiscrepancy

/-- A canonical pair whose coefficients are less than one is klt. -/
theorem IsCanonical.isKlt' {P : Pair X} (h : IsCanonical P) (hΔ : ∀ Q, P.Δ Q < 1) : IsKlt P :=
  h.isKlt hΔ P.hasDivisorLogDiscrepancy

/-- A terminal pair whose coefficients are less than one is klt. -/
theorem IsTerminal.isKlt' {P : Pair X} (h : IsTerminal P) (hΔ : ∀ Q, P.Δ Q < 1) : IsKlt P :=
  h.isKlt hΔ P.hasDivisorLogDiscrepancy

/-- A plt pair is lc. -/
theorem IsPlt.isLc' {P : Pair X} (h : IsPlt P) : IsLc P :=
  h.isLc P.hasDivisorLogDiscrepancy

/-! ## Curves -/

/-- The coheight of a point is at most the dimension of the space. -/
theorem coheight_le_topologicalKrullDim (x : X.toScheme) :
    (coheight x : WithBot ℕ∞) ≤ topologicalKrullDim X.toScheme := by
  have h := Order.coheight_le_krullDim ((irreducibleSetEquivPoints (α := X.toScheme)).symm x)
  rw [coheight_orderIso] at h
  exact h

/-- On a variety of dimension one, each point has coheight at most one. -/
theorem coheight_le_one_of_dim_eq_one (hX : X.dim = 1) (x : X.toScheme) : coheight x ≤ 1 := by
  have h := coheight_le_topologicalKrullDim x
  unfold NormalVariety.dim at hX
  generalize topologicalKrullDim X.toScheme = d at h hX
  induction d using WithBot.recBotCoe with
  | bot => simp at hX
  | coe n =>
    rw [WithBot.unbotD_coe] at hX
    have hn : n = 1 := by
      induction n using ENat.recTopCoe with
      | top => simp at hX
      | coe j =>
        simp only [ENat.toNat_coe] at hX
        simp [hX]
    rw [hn] at h
    exact_mod_cast h

/-- A centre of a valuation that takes the value `exp (-1)` is not the generic point, so its coheight is not zero. -/
theorem IsCentre.coheight_ne_zero {v : Valuation (FF X) VZ} (hπ : ∃ π, v π = WithZero.exp (-1 : ℤ))
    {x : X.toScheme} (hx : IsCentre v x) : coheight x ≠ 0 := by
  intro h0
  rw [Order.coheight_eq_zero] at h0
  have hη : genericPoint X.toScheme ⤳ x := (genericPoint_spec X.toScheme).specializes trivial
  have hle : x ≤ genericPoint X.toScheme := hη
  have h1 : x ⤳ genericPoint X.toScheme := h0 hle
  have hxη : x = genericPoint X.toScheme := (h1.antisymm hη).eq
  subst hxη
  have hfield : IsField (X.toScheme.presheaf.stalk (genericPoint X.toScheme)) :=
    isField_stalk_of_closure_mem_irreducibleComponents X.toScheme (genericPoint X.toScheme)
      (by simp [irreducibleComponents_eq_singleton])
  have hsurj : Function.Surjective
      (algebraMap (X.toScheme.presheaf.stalk (genericPoint X.toScheme)) (FF X)) :=
    IsFractionRing.surjective_iff_isField.mpr hfield
  obtain ⟨π, hπ⟩ := hπ
  obtain ⟨s, hs⟩ := hsurj π⁻¹
  have h3 : v π⁻¹ ≤ 1 := by
    rw [← hs]
    exact hx.1 s
  rw [map_inv₀, hπ, ← WithZero.exp_neg, neg_neg, WithZero.exp_le_one_iff] at h3
  omega

/-- On a variety of dimension one, a centre of a divisorial valuation has coheight one. -/
theorem IsCentre.coheight_eq_one_of_dim_eq_one (hX : X.dim = 1) {v : Valuation (FF X) VZ}
    (hv : IsDivisorial v) {x : X.toScheme} (hx : IsCentre v x) : coheight x = 1 :=
  le_antisymm (coheight_le_one_of_dim_eq_one hX x)
    (Order.one_le_iff_ne_zero.mpr (hx.coheight_ne_zero hv.2.1))

/-- On a variety of dimension one, a divisorial valuation with a log discrepancy is not exceptional. A divisorial valuation with no centre, as the order at infinity on the affine line, is exceptional by the definition, but it has no log discrepancy. -/
theorem LogDiscrepancyIs.not_isExceptional_of_dim_eq_one (hX : X.dim = 1) {P : Pair X}
    {v : Valuation (FF X) VZ} (hv : IsDivisorial v) {A : ℝ} (hA : LogDiscrepancyIs P v A) :
    ¬ IsExceptional v := by
  obtain ⟨x, hx, -⟩ := hA
  exact fun he => he x hx (hx.coheight_eq_one_of_dim_eq_one hX hv)

/-- On a variety of dimension one, each log discrepancy of a divisorial valuation is `1 - Δ Q` for a prime divisor `Q`. -/
theorem LogDiscrepancyIs.exists_eq_of_dim_eq_one (hX : X.dim = 1) {P : Pair X}
    {v : Valuation (FF X) VZ} (hv : IsDivisorial v) {A : ℝ} (hA : LogDiscrepancyIs P v A) :
    ∃ Q : PrimeDivisor X, A = 1 - P.Δ Q :=
  P.hasDivisorLogDiscrepancy v hv (hA.not_isExceptional_of_dim_eq_one hX hv) A hA

/-- On a variety of dimension one, a pair whose coefficients are less than one is klt. -/
theorem isKlt_of_dim_eq_one (hX : X.dim = 1) {P : Pair X} (hΔ : ∀ Q, P.Δ Q < 1) : IsKlt P :=
  ⟨hΔ, fun v hv A hA => by
    obtain ⟨Q, rfl⟩ := hA.exists_eq_of_dim_eq_one hX hv
    exact sub_pos.mpr (hΔ Q)⟩

/-- On a variety of dimension one, a pair whose coefficients are at most one is lc. -/
theorem isLc_of_dim_eq_one (hX : X.dim = 1) {P : Pair X} (hΔ : ∀ Q, P.Δ Q ≤ 1) : IsLc P :=
  ⟨hΔ, fun v hv A hA => by
    obtain ⟨Q, rfl⟩ := hA.exists_eq_of_dim_eq_one hX hv
    exact sub_nonneg.mpr (hΔ Q)⟩

/-- On a variety of dimension one, a pair whose coefficients are at most one is plt. -/
theorem isPlt_of_dim_eq_one (hX : X.dim = 1) {P : Pair X} (hΔ : ∀ Q, P.Δ Q ≤ 1) : IsPlt P :=
  ⟨hΔ, fun _ hv he _ hA => absurd he (hA.not_isExceptional_of_dim_eq_one hX hv)⟩

/-- On a variety of dimension one, each pair is terminal: there is no exceptional valuation with a log discrepancy. -/
theorem isTerminal_of_dim_eq_one (hX : X.dim = 1) (P : Pair X) : IsTerminal P :=
  fun _ hv he _ hA => absurd he (hA.not_isExceptional_of_dim_eq_one hX hv)

/-- On a variety of dimension one, each pair is canonical. -/
theorem isCanonical_of_dim_eq_one (hX : X.dim = 1) (P : Pair X) : IsCanonical P :=
  (isTerminal_of_dim_eq_one hX P).isCanonical

/-- On a variety of dimension one, a pair whose coefficients are less than one is dlt. -/
theorem isDlt_of_dim_eq_one (hX : X.dim = 1) {P : Pair X} (hΔ : ∀ Q, P.Δ Q < 1) : IsDlt P :=
  (isKlt_of_dim_eq_one hX hΔ).isDlt

end MinimalModel
