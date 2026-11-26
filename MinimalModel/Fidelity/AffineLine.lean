/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import MinimalModel.Fidelity.Basic

/-!
# Fidelity checks on the affine line

DRAFT
-/

universe u

open AlgebraicGeometry CategoryTheory Order Polynomial

noncomputable section

#check @one_le_inv₀
#check @Ring.ordFrac_eq_valuation_inv
#check @StructureSheaf.toStalk_stalkSpecializes
#check @AlternatingMap.ofSubsingleton_apply_apply

namespace MinimalModel

section General

variable {k : Type u} [Field k] {X : NormalVariety k}

/-- The stalk of a normal variety at a prime divisor is a discrete valuation ring. -/
theorem isDiscreteValuationRing_stalk (P : PrimeDivisor X) :
    IsDiscreteValuationRing (X.toScheme.presheaf.stalk P.1) := by
  have h1 : Ring.KrullDimLE 1 (X.toScheme.presheaf.stalk P.1) := krullDimLE_of_coheight_le P.2.le
  have hnf : ¬ IsField (X.toScheme.presheaf.stalk P.1) := by
    intro h
    have h2 := ringKrullDim_stalk_eq_coheight P.1
    rw [P.2, ringKrullDim_eq_zero_of_isField h] at h2
    exact absurd h2 (by decide)
  have hm : IsLocalRing.maximalIdeal (X.toScheme.presheaf.stalk P.1) ≠ ⊥ :=
    fun h => hnf ((IsLocalRing.isField_iff_maximalIdeal_eq).mpr h)
  refine ((IsDiscreteValuationRing.TFAE _ hnf).out 0 3).mpr
    ⟨X.isNormal.isIntegrallyClosed_stalk P.1, IsLocalRing.maximalIdeal _, ⟨hm, inferInstance⟩,
      fun Q hQ => ?_⟩
  have := (Ring.krullDimLE_one_iff_of_isPrime_bot.mp h1) Q hQ.1 hQ.2
  exact IsLocalRing.eq_maximalIdeal this

/-- On a normal variety, a nonzero rational function is regular at a prime divisor if and only if its order there is not negative. -/
theorem mem_stalkSubring_iff (P : PrimeDivisor X) {g : FF X} (hg : g ≠ 0) :
    g ∈ stalkSubring P.1 ↔ 0 ≤ ordAt g P := by
  have := isDiscreteValuationRing_stalk P
  unfold ordAt
  rw [Scheme.le_ord_iff P.2 hg]
  change _ ↔ Multiplicative.ofAdd 0 ≤ Ring.ordFrac (X.toScheme.presheaf.stalk P.1) g
  rw [Ring.ordFrac_eq_valuation_inv]
  have hv : (IsDiscreteValuationRing.maximalIdeal (X.toScheme.presheaf.stalk P.1)).valuation (FF X) g ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr hg
  have h1 : ((Multiplicative.ofAdd (0 : ℤ) : Multiplicative ℤ) : ℤᵐ⁰) = 1 := rfl
  rw [h1, one_le_inv₀ (zero_lt_iff.mpr hv)]
  constructor
  · rintro ⟨s, rfl⟩
    exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ s
  · intro h
    obtain ⟨a, ha⟩ := IsDiscreteValuationRing.exists_lift_of_le_one h
    exact ⟨a, ha⟩

end General

section AffineLine

variable (k : Type u) [Field k]

/-- The stalks of `Spec k[X]` are integrally closed: each stalk is a localization of the principal ideal domain `k[X]`. -/
theorem isNormalScheme_affineLine : IsNormalScheme (Spec (CommRingCat.of k[X])) := by
  refine ⟨fun x => ?_⟩
  have : x.asIdeal.IsPrime := x.isPrime
  have : IsIntegrallyClosed (Localization.AtPrime x.asIdeal) :=
    isIntegrallyClosed_of_isLocalization k[X] (Localization.AtPrime x.asIdeal) x.asIdeal.primeCompl
      (Ideal.primeCompl_le_nonZeroDivisors _)
  exact IsIntegrallyClosed.of_equiv
    (Spec.stalkIso (CommRingCat.of k[X]) x).symm.commRingCatIsoToRingEquiv

instance : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k k[X]))) := by
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  change Algebra.FiniteType k k[X]
  infer_instance

/-- The affine line `𝔸¹ = Spec k[X]` as a normal variety over `k`. -/
def affineLine : NormalVariety k where
  toScheme := Spec (CommRingCat.of k[X])
  str := Spec.map (CommRingCat.ofHom (algebraMap k k[X]))
  isNormal := isNormalScheme_affineLine k

/-- The affine line has dimension one. -/
theorem affineLine_dim : (affineLine k).dim = 1 := by
  have h : topologicalKrullDim (PrimeSpectrum k[X]) = 1 :=
    (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim k[X]).trans
      (IsPrincipalIdealRing.ringKrullDim_eq_one _ Polynomial.not_isField)
  unfold NormalVariety.dim
  change ENat.toNat (WithBot.unbotD 0 (topologicalKrullDim (PrimeSpectrum k[X]))) = 1
  rw [h]
  rfl

instance : Algebra k[X] (FF (affineLine k)) :=
  inferInstanceAs (Algebra (CommRingCat.of k[X]) (Spec (CommRingCat.of k[X])).functionField)

instance : IsFractionRing k[X] (FF (affineLine k)) :=
  inferInstanceAs (IsFractionRing (CommRingCat.of k[X]) (Spec (CommRingCat.of k[X])).functionField)

instance : IsScalarTower k k[X] (FF (affineLine k)) := by
  refine IsScalarTower.of_algebraMap_eq fun c => ?_
  have h : (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (affineLine k).str.appTop =
      CommRingCat.ofHom (algebraMap k k[X]) ≫ (Scheme.ΓSpecIso (CommRingCat.of k[X])).inv :=
    (Scheme.ΓSpecIso_inv_naturality _).symm
  change ((Spec (CommRingCat.of k[X])).presheaf.germ ⊤ _ trivial).hom
    (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (affineLine k).str.appTop).hom c) = _
  rw [h]
  rfl

/-- The coordinate `X` as a rational function on the affine line. -/
def coord : FF (affineLine k) := algebraMap k[X] (FF (affineLine k)) X

theorem coord_ne_zero : coord k ≠ 0 := by
  rw [coord, ne_eq, map_eq_zero_iff _ (IsFractionRing.injective k[X] _)]
  exact X_ne_zero

/-- The map from `k[X]` to the stalk at a point `Q` of the affine line. -/
instance (Q : (affineLine k).toScheme) : Algebra k[X] ((affineLine k).toScheme.presheaf.stalk Q) :=
  inferInstanceAs (Algebra k[X] ((Spec.structureSheaf k[X]).presheaf.stalk (Q : PrimeSpectrum k[X])))

instance (Q : (affineLine k).toScheme) :
    IsLocalization.AtPrime ((affineLine k).toScheme.presheaf.stalk Q) (Q : PrimeSpectrum k[X]).asIdeal :=
  inferInstanceAs (IsLocalization.AtPrime
    ((Spec.structureSheaf k[X]).presheaf.stalk (Q : PrimeSpectrum k[X])) (Q : PrimeSpectrum k[X]).asIdeal)

instance (Q : (affineLine k).toScheme) :
    IsScalarTower k[X] ((affineLine k).toScheme.presheaf.stalk Q) (FF (affineLine k)) := by
  refine IsScalarTower.of_algebraMap_eq fun r => ?_
  exact (congrArg (fun f => f.hom r) (StructureSheaf.toStalk_stalkSpecializes (R := k[X])
    ((genericPoint_spec (affineLine k).toScheme).specializes trivial))).symm

variable {k}

theorem algebraMap_mem_stalkSubring (Q : (affineLine k).toScheme) (r : k[X]) :
    algebraMap k[X] (FF (affineLine k)) r ∈ stalkSubring Q :=
  ⟨algebraMap k[X] _ r, (IsScalarTower.algebraMap_apply _ _ _ r).symm⟩

theorem inv_algebraMap_mem_stalkSubring (Q : (affineLine k).toScheme) {b : k[X]}
    (hb : b ∉ (Q : PrimeSpectrum k[X]).asIdeal) :
    (algebraMap k[X] (FF (affineLine k)) b)⁻¹ ∈ stalkSubring Q := by
  obtain ⟨u, hu⟩ := IsLocalization.map_units ((affineLine k).toScheme.presheaf.stalk Q)
    (⟨b, hb⟩ : (Q : PrimeSpectrum k[X]).asIdeal.primeCompl)
  refine ⟨(u⁻¹ : _ˣ), ?_⟩
  rw [IsScalarTower.algebraMap_apply k[X] ((affineLine k).toScheme.presheaf.stalk Q), ← hu,
    eq_inv_iff_mul_eq_one, ← map_mul, Units.inv_mul, map_one]

theorem exists_of_mem_stalkSubring {Q : (affineLine k).toScheme} {y : FF (affineLine k)}
    (hy : y ∈ stalkSubring Q) : ∃ a b : k[X], b ∉ (Q : PrimeSpectrum k[X]).asIdeal ∧
      y * algebraMap k[X] _ b = algebraMap k[X] _ a := by
  obtain ⟨s, rfl⟩ := hy
  obtain ⟨a, b, rfl⟩ := IsLocalization.mk'_surjective (Q : PrimeSpectrum k[X]).asIdeal.primeCompl s
  refine ⟨a, b, b.2, ?_⟩
  rw [IsScalarTower.algebraMap_apply k[X] ((affineLine k).toScheme.presheaf.stalk Q) (FF _) b,
    IsScalarTower.algebraMap_apply k[X] ((affineLine k).toScheme.presheaf.stalk Q) (FF _) a,
    ← map_mul, IsLocalization.mk'_spec]

variable (k)

instance : Algebra.FormallyEtale k[X] (FF (affineLine k)) :=
  Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors k[X])

/-- The linear map `Ω[k(X)/k] → k(X)` that sends `dX` to `1`. -/
def derivL : KaehlerDifferential k (FF (affineLine k)) →ₗ[FF (affineLine k)] FF (affineLine k) :=
  (TensorProduct.AlgebraTensorModule.rid k[X] (FF (affineLine k)) (FF (affineLine k))).toLinearMap ∘ₗ
    (LinearMap.baseChange (FF (affineLine k)) (KaehlerDifferential.polynomialEquiv k).toLinearMap) ∘ₗ
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k k[X] (FF (affineLine k))).symm.toLinearMap

variable {k}

theorem derivL_D_algebraMap (p : k[X]) :
    derivL k (KaehlerDifferential.D k (FF (affineLine k)) (algebraMap k[X] _ p)) =
      algebraMap k[X] _ (derivative p) := by
  simp [derivL, KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
    KaehlerDifferential.polynomialEquiv_D, Algebra.smul_def]

theorem derivL_D_coord : derivL k (KaehlerDifferential.D k (FF (affineLine k)) (coord k)) = 1 := by
  rw [coord, derivL_D_algebraMap, derivative_X, map_one]

/-- The derivation `d/dX` keeps each stalk of the affine line. -/
theorem derivL_D_mem {Q : (affineLine k).toScheme} {y : FF (affineLine k)} (hy : y ∈ stalkSubring Q) :
    derivL k (KaehlerDifferential.D k (FF (affineLine k)) y) ∈ stalkSubring Q := by
  obtain ⟨a, b, hb, h⟩ := exists_of_mem_stalkSubring hy
  set δ := (derivL k).compDer (KaehlerDifferential.D k (FF (affineLine k)))
  have hδ : ∀ z, derivL k (KaehlerDifferential.D k (FF (affineLine k)) z) = δ z := fun _ => rfl
  have hB : algebraMap k[X] (FF (affineLine k)) b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective k[X] _)).mpr fun h0 => hb (h0 ▸ Ideal.zero_mem _)
  have hl := congrArg δ h
  rw [Derivation.leibniz, ← hδ, ← hδ, derivL_D_algebraMap, derivL_D_algebraMap, smul_eq_mul,
    smul_eq_mul] at hl
  have hy' : δ y = (algebraMap k[X] _ b)⁻¹ *
      (algebraMap k[X] _ (derivative a) - y * algebraMap k[X] _ (derivative b)) := by
    rw [← hl]
    field_simp
    ring
  rw [hδ, hy']
  exact Subring.mul_mem _ (inv_algebraMap_mem_stalkSubring Q hb)
    (Subring.sub_mem _ (algebraMap_mem_stalkSubring Q _)
      (Subring.mul_mem _ hy (algebraMap_mem_stalkSubring Q _)))

instance : Subsingleton (Fin (affineLine k).dim) := by
  rw [affineLine_dim]
  infer_instance

/-- The index of the only coordinate of a top form on the affine line. -/
def index0 : Fin (affineLine k).dim := ⟨0, by rw [affineLine_dim]; exact Nat.one_pos⟩

variable (k)

/-- The linear map from the top forms to `k(X)` that sends `g dX` to `g`. -/
def formCoeff : TopForm (affineLine k) →ₗ[FF (affineLine k)] FF (affineLine k) :=
  exteriorPower.alternatingMapLinearEquiv
    (AlternatingMap.ofSubsingleton (FF (affineLine k)) _ _ index0 (derivL k))

/-- The form `dX`. -/
def dX : TopForm (affineLine k) :=
  exteriorPower.ιMulti (FF (affineLine k)) (affineLine k).dim
    (fun _ => KaehlerDifferential.D k (FF (affineLine k)) (coord k))

variable {k}

theorem formCoeff_ιMulti (a : Fin (affineLine k).dim → FF (affineLine k)) :
    formCoeff k (exteriorPower.ιMulti (FF (affineLine k)) (affineLine k).dim
      (fun i => KaehlerDifferential.D k (FF (affineLine k)) (a i))) =
      derivL k (KaehlerDifferential.D k (FF (affineLine k)) (a index0)) := by
  rw [formCoeff, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

theorem formCoeff_smul_dX (g : FF (affineLine k)) : formCoeff k (g • dX k) = g := by
  rw [map_smul, dX, formCoeff_ιMulti, derivL_D_coord, smul_eq_mul, mul_one]

theorem dX_ne_zero : dX k ≠ 0 := fun h => by
  have := formCoeff_smul_dX (k := k) 1
  rw [one_smul, h, map_zero] at this
  exact zero_ne_one this

theorem coord_mem_stalkSubring (Q : (affineLine k).toScheme) : coord k ∈ stalkSubring Q :=
  algebraMap_mem_stalkSubring Q X

/-- On the affine line, `g dX` is regular at a point if and only if `g` is regular there. -/
theorem smul_dX_mem_formLattice_iff (Q : (affineLine k).toScheme) (g : FF (affineLine k)) :
    g • dX k ∈ formLattice (stalkSubring Q) ↔ g ∈ stalkSubring Q := by
  constructor
  · intro h
    have hle : formLattice (stalkSubring Q) ≤
        (stalkSubring Q).toAddSubgroup.comap (formCoeff k).toAddMonoidHom := by
      refine (AddSubgroup.closure_le _).mpr ?_
      rintro ω ⟨c, hc, a, ha, rfl⟩
      change formCoeff k (c • _) ∈ stalkSubring Q
      rw [map_smul, formCoeff_ιMulti, smul_eq_mul]
      exact Subring.mul_mem _ hc (derivL_D_mem (ha index0))
    have := hle h
    change formCoeff k (g • dX k) ∈ stalkSubring Q at this
    rwa [formCoeff_smul_dX] at this
  · intro h
    exact AddSubgroup.subset_closure ⟨g, h, fun _ => coord k, fun _ => coord_mem_stalkSubring Q, rfl⟩

variable (k)

/-- The canonical divisor of the affine line: the zero divisor, as the divisor of `dX`. -/
def affineLineCanonical : CanonicalDivisor (affineLine k) :=
  ⟨0, dX k, ⟨dX_ne_zero, fun P g hg => by
    rw [smul_dX_mem_formLattice_iff, mem_stalkSubring_iff P hg]
    simp⟩⟩

/-- The point `0` of the affine line: the prime ideal `(X)`. -/
def zeroPoint : (affineLine k).toScheme :=
  (⟨Ideal.span {X}, (Ideal.span_singleton_prime X_ne_zero).mpr prime_X⟩ : PrimeSpectrum k[X])

/-- The point `0` has coheight one, because the ideal `(X)` has height one. -/
theorem coheight_zeroPoint : coheight (zeroPoint k) = 1 := by
  rw [← idealHeight_eq_coheight (CommRingCat.of k[X]) (zeroPoint k)]
  exact Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero X_ne_zero) not_isUnit_X

/-- The prime divisor `[0]` of the affine line. -/
def zeroDivisor : PrimeDivisor (affineLine k) := ⟨zeroPoint k, coheight_zeroPoint k⟩

variable {k}

/-- A prime divisor of the affine line other than `[0]` does not contain `X`. -/
theorem X_notMem_of_ne {Q : PrimeDivisor (affineLine k)} (hQ : Q ≠ zeroDivisor k) :
    X ∉ (Q.1 : PrimeSpectrum k[X]).asIdeal := by
  intro hX
  have hne : (Q.1 : PrimeSpectrum k[X]).asIdeal ≠ ⊤ := (Q.1 : PrimeSpectrum k[X]).isPrime.ne_top
  have hmax : (Ideal.span {X} : Ideal k[X]).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible irreducible_X
  have heq := hmax.eq_of_le hne ((Ideal.span_singleton_le_iff_mem _).mpr hX)
  exact hQ (Subtype.ext (PrimeSpectrum.ext heq.symm))

/-- The order of `X` along a prime divisor `Q` other than `[0]` is zero. -/
theorem ordAt_coord_of_ne {Q : PrimeDivisor (affineLine k)} (hQ : Q ≠ zeroDivisor k) :
    ordAt (coord k) Q = 0 := by
  have hu : IsUnit (algebraMap k[X] ((affineLine k).toScheme.presheaf.stalk Q.1) X) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff _ _ X).mpr (X_notMem_of_ne hQ)
  unfold ordAt
  rw [Scheme.ord_eq_iff Q.2 coord_ne_zero]
  have := isDiscreteValuationRing_stalk Q
  change Ring.ordFrac ((affineLine k).toScheme.presheaf.stalk Q.1) (coord k) = _
  rw [coord, IsScalarTower.algebraMap_apply k[X] ((affineLine k).toScheme.presheaf.stalk Q.1),
    Ring.ordFrac_of_isUnit hu]
  rfl

/-- The order of `X` along `[0]` is one. -/
theorem ordAt_coord_zeroDivisor : ordAt (coord k) (zeroDivisor k) = 1 := by
  have := isDiscreteValuationRing_stalk (zeroDivisor k)
  have hirr : Irreducible (algebraMap k[X] ((affineLine k).toScheme.presheaf.stalk (zeroPoint k)) X) := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer,
      ← IsLocalization.AtPrime.map_eq_maximalIdeal (zeroPoint k : PrimeSpectrum k[X]).asIdeal,
      ← Set.image_singleton, ← Ideal.map_span]
    rfl
  unfold ordAt
  rw [Scheme.ord_eq_iff (zeroDivisor k).2 coord_ne_zero]
  change Ring.ordFrac ((affineLine k).toScheme.presheaf.stalk (zeroPoint k)) (coord k) = _
  rw [coord, IsScalarTower.algebraMap_apply k[X] ((affineLine k).toScheme.presheaf.stalk (zeroPoint k)),
    Ring.ordFrac_irreducible hirr]
  rfl

/-- The divisor `[0]` is Cartier: it is the divisor of `X` on all of the affine line. -/
theorem isCartier_zeroDivisor : IsCartier (Finsupp.single (zeroDivisor k) (1 : ℤ)) := by
  classical
  refine fun _ => ⟨⊤, trivial, coord k, coord_ne_zero, fun Q _ => ?_⟩
  rw [Finsupp.single_apply]
  split_ifs with h
  · rw [← h, ordAt_coord_zeroDivisor]
  · rw [ordAt_coord_of_ne (Ne.symm h)]

/-- `K + c [0]` is `ℝ`-Cartier for each real number `c`. -/
theorem isRCartier_smul_zeroDivisor (c : ℝ) :
    IsRCartier ((affineLineCanonical k).K.toReal + Finsupp.single (zeroDivisor k) c) := by
  have h : (affineLineCanonical k).K.toReal + Finsupp.single (zeroDivisor k) c =
      c • (Finsupp.single (zeroDivisor k) (1 : ℤ)).toReal := by
    simp [affineLineCanonical, Divisor.toReal]
  rw [h]
  exact Submodule.smul_mem _ c (Submodule.subset_span ⟨_, isCartier_zeroDivisor, rfl⟩)

variable (k)

/-- The pair `(𝔸¹, c [0])` for a real number `c ≥ 0`. -/
def affineLinePair (c : ℝ) (hc : 0 ≤ c) : Pair (affineLine k) where
  K := affineLineCanonical k
  Δ := Finsupp.single (zeroDivisor k) c
  nonneg := Finsupp.single_nonneg.mpr hc
  rCartier := isRCartier_smul_zeroDivisor c

/-- F3: the pair `(𝔸¹, 2 [0])` is not lc. -/
theorem affineLinePair_two_not_isLc : ¬ IsLc (affineLinePair k 2 zero_le_two) :=
  not_isLc_of_one_lt (Q := zeroDivisor k) (by simp [affineLinePair])

/-- F3: the pair `(𝔸¹, [0])` is not klt. -/
theorem affineLinePair_one_not_isKlt : ¬ IsKlt (affineLinePair k 1 zero_le_one) :=
  not_isKlt_of_one_le (Q := zeroDivisor k) (by simp [affineLinePair])

/-- F2: the pair `(𝔸¹, 0)`. Its boundary is zero. -/
theorem affineLinePair_zero_Δ : (affineLinePair k 0 le_rfl).Δ = 0 := by
  simp [affineLinePair]

end AffineLine

end MinimalModel
