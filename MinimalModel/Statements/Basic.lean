/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib

/-!
# The vocabulary of the minimal model program

This file gives the definitions that the statements of `MinimalModel/Statements/` use (spec 06.1). Each definition has a body, and the file uses none of the escape hatches of spec 09.2.

## The choices

* A variety is bundled as `NormalVariety k`: an integral, separated, quasi-compact scheme of finite type over a field `k`, with integrally closed stalks.
* A divisor is a finitely supported function on the points of coheight one (`Divisor R X`). The order of vanishing is the Mathlib function `Scheme.ord`.
* A canonical divisor is the divisor of a nonzero rational top form. The order of a top form along a prime divisor, or along a divisorial valuation, is read from the lattice of the forms that are regular on the valuation ring.
* The log discrepancy is defined for every divisorial valuation of the function field, not on one log resolution (spec 06.2.3). A divisorial valuation is a discrete valuation of rank one that is trivial on `k` and whose residue field has transcendence degree `dim X - 1` over `k`. By a theorem of Zariski (KM98 Lemma 2.45) these are the valuations of the prime divisors on the birational models of `X`.
* Ampleness of a Cartier divisor uses the affine loci of its sections (EGA II 4.5.2). A projective variety is a proper variety with an ample Cartier divisor.
* The intersection numbers of divisors and curves are a structure `IntersectionData`. Its field `dot_cartier` fixes each value by the degree of the restriction to the normalization of the curve, so the structure has at most one value on each `ℝ`-Cartier divisor. Its field `finiteDim` is the theorem of the base, which is a hypothesis (spec 03.14).
* The steps of a program (`IsMMPStep`) are the divisorial contractions and the flips of the lc minimal model program in the sense of Fujino. A step is a flip when the contraction is small.

The definitions of intersection numbers assume that `k` is algebraically closed, because they count each place of a curve with degree one. The statements of families A to G assume `[IsAlgClosed k] [CharZero k]`.
-/

universe u

open AlgebraicGeometry CategoryTheory Order TopologicalSpace Filter

noncomputable section

namespace MinimalModel

/-! ## Varieties -/

/-- A variety over `k`: an integral scheme, separated and of finite type over `k`, and quasi-compact. This is the unbundled form, for the bridge to AxiomMath/MMP (spec 06.4). -/
class IsVariety {k : Type u} [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k)) : Prop where
  integral : IsIntegral X
  separated : IsSeparated f
  finiteType : LocallyOfFiniteType f
  compact : CompactSpace X

/-- A scheme is normal when each stalk is an integrally closed domain. -/
class IsNormalScheme (X : Scheme.{u}) : Prop where
  isIntegrallyClosed_stalk : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)

/-- A normal variety over `k`, bundled with its structure morphism. The field `isLocallyNoetherian` follows from the other fields; it is a field so that the order of vanishing is available at once. -/
structure NormalVariety (k : Type u) [Field k] where
  /-- The underlying scheme. -/
  toScheme : Scheme.{u}
  /-- The structure morphism to `Spec k`. -/
  str : toScheme ⟶ Spec (CommRingCat.of k)
  [isIntegral : IsIntegral toScheme]
  [isSeparated : IsSeparated str]
  [locallyOfFiniteType : LocallyOfFiniteType str]
  [compactSpace : CompactSpace toScheme]
  [isLocallyNoetherian : IsLocallyNoetherian toScheme]
  [isNormal : IsNormalScheme toScheme]

attribute [instance] NormalVariety.isIntegral NormalVariety.isSeparated
  NormalVariety.locallyOfFiniteType NormalVariety.compactSpace
  NormalVariety.isLocallyNoetherian NormalVariety.isNormal

variable {k : Type u} [Field k]

namespace NormalVariety

variable (X : NormalVariety k)

/-- The map from `k` to the global sections. -/
noncomputable def toΓ : k →+* Γ(X.toScheme, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ X.str.appTop).hom

/-- The function field `k(X)` is a `k`-algebra. -/
noncomputable instance algebraFunctionField : Algebra k X.toScheme.functionField :=
  ((X.toScheme.presheaf.germ ⊤ (genericPoint X.toScheme) trivial).hom.comp X.toΓ).toAlgebra

/-- The map from `k` to the residue field of a point. -/
noncomputable def toResidueField (x : X.toScheme) : k →+* X.toScheme.residueField x :=
  ((X.toScheme.presheaf.germ ⊤ x trivial ≫ X.toScheme.residue x).hom.comp X.toΓ)

/-- The dimension of `X`: its Krull dimension as a topological space. -/
noncomputable def dim : ℕ := ENat.toNat (WithBot.unbotD 0 (topologicalKrullDim X.toScheme))

/-- `X` is smooth over `k`. -/
def IsSmooth : Prop := Smooth X.str

/-- `X` is smooth over `k` at the point `x`. -/
def IsSmoothAt (x : X.toScheme) : Prop :=
  ∃ U : X.toScheme.Opens, x ∈ U ∧ Smooth (U.ι ≫ X.str)

end NormalVariety

/-- The function field of a normal variety. -/
abbrev FF (X : NormalVariety k) : Type u := X.toScheme.functionField

/-! ## Divisors -/

/-- The prime divisors of `X` are the points of coheight one, that is the generic points of the closed integral subschemes of codimension one. -/
def PrimeDivisor (X : NormalVariety k) : Type u := {x : X.toScheme // coheight x = 1}

/-- Divisors with coefficients in `R`. The cases `ℤ`, `ℚ` and `ℝ` are the Weil divisors, the `ℚ`-divisors and the `ℝ`-divisors. -/
abbrev Divisor (R : Type*) [Zero R] (X : NormalVariety k) := PrimeDivisor X →₀ R

variable {X : NormalVariety k}

/-- The order of vanishing of a rational function along a prime divisor. -/
noncomputable def ordAt (φ : FF X) (P : PrimeDivisor X) : ℤ := Scheme.ord φ P.1

/-- An integral divisor as an `ℝ`-divisor. -/
noncomputable def Divisor.toReal (D : Divisor ℤ X) : Divisor ℝ X :=
  Finsupp.mapRange (fun n : ℤ => (n : ℝ)) (by simp) D

/-- An integral divisor as a `ℚ`-divisor. -/
noncomputable def Divisor.toRat (D : Divisor ℤ X) : Divisor ℚ X :=
  Finsupp.mapRange (fun n : ℤ => (n : ℚ)) (by simp) D

/-- A `ℚ`-divisor as an `ℝ`-divisor. -/
noncomputable def Divisor.ratToReal (D : Divisor ℚ X) : Divisor ℝ X :=
  Finsupp.mapRange (fun q : ℚ => (q : ℝ)) (by simp) D

/-- The round down `⌊m D⌋` of `m` times an `ℝ`-divisor. -/
noncomputable def Divisor.roundDown (m : ℕ) (D : Divisor ℝ X) : Divisor ℤ X :=
  Finsupp.mapRange (fun r : ℝ => ⌊(m : ℝ) * r⌋) (by simp) D

/-- `D` is the divisor of the rational function `φ` on the set `U`: the two have the same coefficient at each prime divisor whose generic point is in `U`. -/
def IsDivOn (D : Divisor ℤ X) (φ : FF X) (U : Set X.toScheme) : Prop :=
  φ ≠ 0 ∧ ∀ P : PrimeDivisor X, P.1 ∈ U → D P = ordAt φ P

/-- A principal divisor: the divisor of a nonzero rational function. -/
def IsPrincipal (D : Divisor ℤ X) : Prop := ∃ φ, IsDivOn D φ Set.univ

/-- `D ∼_ℝ D'`: the difference is an `ℝ`-linear combination of principal divisors. -/
def RLinEquiv (D D' : Divisor ℝ X) : Prop :=
  D - D' ∈ Submodule.span ℝ (Divisor.toReal '' {E : Divisor ℤ X | IsPrincipal E})

/-- `D ∼_ℚ D'` for `ℚ`-divisors. -/
def QLinEquiv (D D' : Divisor ℚ X) : Prop :=
  D - D' ∈ Submodule.span ℚ (Divisor.toRat '' {E : Divisor ℤ X | IsPrincipal E})

/-- A Cartier divisor: locally principal. -/
def IsCartier (D : Divisor ℤ X) : Prop :=
  ∀ x : X.toScheme, ∃ U : X.toScheme.Opens, x ∈ U ∧ ∃ φ, IsDivOn D φ U

/-- A `ℚ`-Cartier divisor: a positive multiple is Cartier. -/
def IsQCartier (D : Divisor ℚ X) : Prop :=
  ∃ m : ℕ, 0 < m ∧ ∃ E : Divisor ℤ X, IsCartier E ∧ (m : ℚ) • D = E.toRat

/-- An `ℝ`-Cartier divisor: an `ℝ`-linear combination of Cartier divisors. -/
def IsRCartier (D : Divisor ℝ X) : Prop :=
  D ∈ Submodule.span ℝ (Divisor.toReal '' {E : Divisor ℤ X | IsCartier E})

/-- `X` is `ℚ`-factorial: each Weil divisor is `ℚ`-Cartier. -/
def IsQFactorial (X : NormalVariety k) : Prop :=
  ∀ D : Divisor ℤ X, ∃ m : ℕ, 0 < m ∧ IsCartier ((m : ℤ) • D)

/-- The coefficients of an `ℝ`-divisor are in the set `S`. -/
def Divisor.CoeffsIn (D : Divisor ℝ X) (S : Set ℝ) : Prop := ∀ P, D P ∈ S

/-- The points of the support of `D`: the points in the closure of a prime divisor with a nonzero coefficient. -/
def Divisor.supp {R : Type*} [Zero R] (D : Divisor R X) : Set X.toScheme :=
  {y | ∃ P : PrimeDivisor X, D P ≠ 0 ∧ P.1 ⤳ y}

/-! ## Top forms and the canonical divisor -/

/-- The rational top forms: the top exterior power of the Kähler differentials of `k(X)` over `k`. -/
abbrev TopForm (X : NormalVariety k) : Type u :=
  ↥(⋀[FF X]^X.dim (KaehlerDifferential k (FF X)))

/-- The lattice of the top forms that are regular on a subring `O` of `k(X)`: the additive group generated by the forms `g • da₁ ∧ ... ∧ daₙ` with `g` and the `aᵢ` in `O`. When `O` is a discrete valuation ring of a smooth point of a model, this is `O • ω₀` for a generator `ω₀`. -/
def formLattice (O : Subring (FF X)) : AddSubgroup (TopForm X) :=
  AddSubgroup.closure {ω | ∃ g ∈ O, ∃ a : Fin X.dim → FF X, (∀ i, a i ∈ O) ∧
    ω = g • exteriorPower.ιMulti (FF X) X.dim (fun i => KaehlerDifferential.D k (FF X) (a i))}

/-- The image of the stalk at `x` in the function field. -/
noncomputable def stalkSubring (x : X.toScheme) : Subring (FF X) :=
  (algebraMap (X.toScheme.presheaf.stalk x) (FF X)).range

/-- `D` is the divisor of the nonzero top form `ω`: for each prime divisor `P` and each nonzero `g`, the form `g • ω` is regular at `P` if and only if `ord_P g ≥ -D P`. -/
def IsDivOfForm (D : Divisor ℤ X) (ω : TopForm X) : Prop :=
  ω ≠ 0 ∧ ∀ P : PrimeDivisor X, ∀ g : FF X, g ≠ 0 →
    (g • ω ∈ formLattice (stalkSubring P.1) ↔ -D P ≤ ordAt g P)

/-- A canonical divisor: the divisor of a nonzero rational top form. -/
structure CanonicalDivisor (X : NormalVariety k) where
  /-- The divisor. -/
  K : Divisor ℤ X
  /-- The form. -/
  ω : TopForm X
  isDiv : IsDivOfForm K ω

/-- A pair `(X, Δ)`: a canonical divisor `K`, an effective `ℝ`-divisor `Δ`, and `K + Δ` is `ℝ`-Cartier. -/
structure Pair (X : NormalVariety k) where
  /-- The canonical divisor. -/
  K : CanonicalDivisor X
  /-- The boundary. -/
  Δ : Divisor ℝ X
  nonneg : 0 ≤ Δ
  rCartier : IsRCartier (K.K.toReal + Δ)

/-- The log canonical divisor `K + Δ`. -/
noncomputable def Pair.KΔ (P : Pair X) : Divisor ℝ X := P.K.K.toReal + P.Δ

/-- The boundary has rational coefficients. -/
def Pair.IsRationalBoundary (P : Pair X) : Prop := P.Δ.CoeffsIn (Set.range ((↑) : ℚ → ℝ))

/-- The support of the reduced boundary `⌊Δ⌋`: the points in the closure of a prime divisor whose coefficient in `Δ` is at least one. For an lc pair, these prime divisors are the ones with coefficient one. -/
def Pair.reducedSupp (P : Pair X) : Set X.toScheme := (P.Δ.roundDown 1).supp

/-! ## Valuations and discrepancies -/

/-- The value group of the valuations: `ℤ` with a zero, written multiplicatively. -/
abbrev VZ : Type := WithZero (Multiplicative ℤ)

/-- A divisorial valuation of `k(X)` over `k`, normalized: the value group is all of `ℤ`, the valuation is trivial on `k`, and the residue field has `dim X - 1` algebraically independent elements over `k`. -/
def IsDivisorial (v : Valuation (FF X) VZ) : Prop :=
  (∀ c : k, c ≠ 0 → v (algebraMap k (FF X) c) = 1) ∧
  (∃ π, v π = WithZero.exp (-1 : ℤ)) ∧
  ∃ a : Fin (X.dim - 1) → FF X, (∀ i, v (a i) ≤ 1) ∧
    ∀ p : MvPolynomial (Fin (X.dim - 1)) k, p ≠ 0 → v (MvPolynomial.aeval a p) = 1

/-- The point `x` is the centre of `v` on `X`: the stalk at `x` is in the valuation ring, and its maximal ideal is in the maximal ideal of the valuation. -/
def IsCentre (v : Valuation (FF X) VZ) (x : X.toScheme) : Prop :=
  (∀ s : X.toScheme.presheaf.stalk x, v (algebraMap _ (FF X) s) ≤ 1) ∧
  ∀ s ∈ IsLocalRing.maximalIdeal (X.toScheme.presheaf.stalk x), v (algebraMap _ (FF X) s) < 1

/-- A valuation is exceptional over `X` when its centre is not a prime divisor of `X`. -/
def IsExceptional (v : Valuation (FF X) VZ) : Prop :=
  ∀ x, IsCentre v x → coheight x ≠ 1

/-- The order of a top form along a valuation is `m`: for each nonzero `g`, the form `g • ω` is regular on the valuation ring if and only if `v g ≤ exp m`, that is `ord_v g ≥ -m`. -/
def FormOrd (v : Valuation (FF X) VZ) (ω : TopForm X) (m : ℤ) : Prop :=
  ∀ g : FF X, g ≠ 0 → (g • ω ∈ formLattice v.integer ↔ v g ≤ WithZero.exp m)

/-- `A` is the log discrepancy `A_{X,Δ}(v)` of the valuation `v`. Near the centre `x` of `v`, write `K + Δ = Σ rᵢ div(hᵢ)`. Then `A = 1 + ord_v(ω) - Σ rᵢ ord_v(hᵢ)`, where `ω` is the form of the canonical divisor. On a model `Y` where `v` is a prime divisor `E`, this is `1 + coeff_E (K_Y - f^*(K + Δ))`. For the prime divisor `P` of `X` it is `1 - Δ P`. -/
def LogDiscrepancyIs (P : Pair X) (v : Valuation (FF X) VZ) (A : ℝ) : Prop :=
  ∃ x, IsCentre v x ∧ ∃ U : X.toScheme.Opens, x ∈ U ∧
  ∃ (N : ℕ) (r : Fin N → ℝ) (h : Fin N → FF X) (e : Fin N → ℤ) (m : ℤ),
    (∀ i, v (h i) = WithZero.exp (-(e i))) ∧ FormOrd v P.K.ω m ∧
    (∀ Q : PrimeDivisor X, Q.1 ∈ U → P.KΔ Q = ∑ i, r i * (ordAt (h i) Q : ℝ)) ∧
    A = 1 + m - ∑ i, r i * (e i : ℝ)

/-- Kawamata log terminal: the coefficients of `Δ` are less than one, and each log discrepancy is positive. -/
def IsKlt (P : Pair X) : Prop :=
  (∀ Q, P.Δ Q < 1) ∧ ∀ v, IsDivisorial v → ∀ A, LogDiscrepancyIs P v A → 0 < A

/-- Log canonical: the coefficients of `Δ` are at most one, and each log discrepancy is nonnegative. -/
def IsLc (P : Pair X) : Prop :=
  (∀ Q, P.Δ Q ≤ 1) ∧ ∀ v, IsDivisorial v → ∀ A, LogDiscrepancyIs P v A → 0 ≤ A

/-- Terminal: each exceptional log discrepancy is more than one. -/
def IsTerminal (P : Pair X) : Prop :=
  ∀ v, IsDivisorial v → IsExceptional v → ∀ A, LogDiscrepancyIs P v A → 1 < A

/-- Canonical: each exceptional log discrepancy is at least one. -/
def IsCanonical (P : Pair X) : Prop :=
  ∀ v, IsDivisorial v → IsExceptional v → ∀ A, LogDiscrepancyIs P v A → 1 ≤ A

open Classical in
/-- The prime divisors in the set `S` have simple normal crossings at `x`, and `X` is smooth at `x`: the divisors of `S` through `x` have local equations that are part of a regular system of parameters of the stalk. -/
def IsSncAt (S : Set (PrimeDivisor X)) (x : X.toScheme) : Prop :=
  X.IsSmoothAt x ∧
  ∃ t : {P : PrimeDivisor X // P ∈ S ∧ P.1 ⤳ x} →
      IsLocalRing.maximalIdeal (X.toScheme.presheaf.stalk x),
    (∀ P Q, Q.1 ⤳ x → ordAt (algebraMap _ (FF X) (t P).1) Q = if Q = P.1 then 1 else 0) ∧
    LinearIndependent (IsLocalRing.ResidueField (X.toScheme.presheaf.stalk x))
      (fun P => (IsLocalRing.maximalIdeal _).toCotangent (t P))

/-- Divisorial log terminal (Szabó): `(X, Δ)` is lc, and there is a closed set `Z` such that the pair is snc outside `Z` and each valuation with centre in `Z` has a positive log discrepancy. -/
def IsDlt (P : Pair X) : Prop :=
  IsLc P ∧ ∃ Z : Set X.toScheme, IsClosed Z ∧
    (∀ x ∉ Z, IsSncAt {Q | P.Δ Q ≠ 0} x) ∧
    ∀ v, IsDivisorial v → ∀ x, IsCentre v x → x ∈ Z → ∀ A, LogDiscrepancyIs P v A → 0 < A

open Classical in
/-- The minimal log discrepancy at a point `x`: the infimum of the log discrepancies of the valuations with centre `x`. It is `⊥` when one of them is negative, because then they are not bounded below (KM98 Corollary 2.31). -/
noncomputable def mld (P : Pair X) (x : X.toScheme) : WithBot ℝ :=
  if ∃ v A, IsDivisorial v ∧ IsCentre v x ∧ LogDiscrepancyIs P v A ∧ A < 0 then ⊥
  else ((sInf {A | ∃ v, IsDivisorial v ∧ IsCentre v x ∧ LogDiscrepancyIs P v A} : ℝ) : WithBot ℝ)

/-- The log canonical threshold of an effective `ℝ`-divisor `D` with respect to `(X, Δ)`. -/
noncomputable def lct (P : Pair X) (D : Divisor ℝ X) : ℝ :=
  sSup {t : ℝ | 0 ≤ t ∧ ∃ P' : Pair X, P'.K = P.K ∧ P'.Δ = P.Δ + t • D ∧ IsLc P'}

/-! ## Morphisms -/

/-- A morphism of schemes is birational when it is an isomorphism over a nonempty open set of the target. The target is integral, so the open set is dense. -/
def IsBirationalHom {Y Z : Scheme.{u}} (f : Y ⟶ Z) : Prop :=
  ∃ U : Z.Opens, (U : Set Z).Nonempty ∧ IsIso (f ∣_ U)

/-- A small birational morphism: it is birational, and an isomorphism near the generic point of each prime divisor of the source. -/
def IsSmallHom {Y Z : NormalVariety k} (f : Y.toScheme ⟶ Z.toScheme) : Prop :=
  IsBirationalHom f ∧ ∀ P : PrimeDivisor Y, ∃ V : Z.toScheme.Opens, f.base P.1 ∈ V ∧ IsIso (f ∣_ V)

/-! ## Ampleness and positivity -/

/-- The locus of `W` where the effective divisor `E` vanishes nowhere. -/
def nonvanishing (E : Divisor ℤ X) (W : Set X.toScheme) : Set X.toScheme :=
  {y | y ∈ W ∧ ∀ P : PrimeDivisor X, P.1 ⤳ y → E P = 0}

/-- A Cartier divisor `D` is ample on the open set `W`: the sections of the multiples of `D` on `W` whose nonvanishing loci are affine cover `W` (EGA II 4.5.2). A section of `m D` is a rational function `φ` with `m D + div φ ≥ 0` on `W`. -/
def IsAmpleOn (D : Divisor ℤ X) (W : X.toScheme.Opens) : Prop :=
  IsCartier D ∧ ∀ x ∈ W, ∃ m : ℕ, 0 < m ∧ ∃ φ : FF X, ∃ E : Divisor ℤ X,
    IsDivOn (E - (m : ℤ) • D) φ W ∧ (∀ P : PrimeDivisor X, P.1 ∈ W → 0 ≤ E P) ∧
    x ∈ nonvanishing E W ∧ ∃ U : X.toScheme.Opens, IsAffineOpen U ∧ (U : Set X.toScheme) = nonvanishing E W

/-- A Cartier divisor is ample relative to a morphism `f : X → Z` when it is ample on the inverse image of each affine open set of `Z`. -/
def IsRelAmple {Z : Scheme.{u}} (D : Divisor ℤ X) (f : X.toScheme ⟶ Z) : Prop :=
  IsCartier D ∧ ∀ V : Z.Opens, IsAffineOpen V → IsAmpleOn D (f ⁻¹ᵁ V)

/-- An `ℝ`-divisor is ample relative to `f`: it is `ℝ`-linearly equivalent to a positive combination of `f`-ample Cartier divisors. -/
def IsRAmpleOver {Z : Scheme.{u}} (D : Divisor ℝ X) (f : X.toScheme ⟶ Z) : Prop :=
  ∃ (N : ℕ) (r : Fin N → ℝ) (A : Fin N → Divisor ℤ X), 0 < N ∧ (∀ i, 0 < r i) ∧
    (∀ i, IsRelAmple (A i) f) ∧ RLinEquiv D (∑ i, r i • (A i).toReal)

/-- An ample `ℝ`-divisor. -/
def IsAmple (D : Divisor ℝ X) : Prop := IsRAmpleOver D X.str

/-- A projective morphism: proper, with a relatively ample Cartier divisor. -/
def IsProjectiveHom {Z : Scheme.{u}} (f : X.toScheme ⟶ Z) : Prop :=
  IsProper f ∧ ∃ D : Divisor ℤ X, IsRelAmple D f

/-- `X` is projective over `k`. -/
def IsProjective (X : NormalVariety k) : Prop := IsProjectiveHom (X := X) X.str

/-- A big `ℝ`-divisor: `ℝ`-linearly equivalent to an ample divisor plus an effective divisor. -/
def IsBig (D : Divisor ℝ X) : Prop :=
  ∃ A E : Divisor ℝ X, IsAmple A ∧ 0 ≤ E ∧ RLinEquiv D (A + E)

/-- A pseudo-effective `ℝ`-divisor: its sum with each small positive multiple of an ample divisor is big. -/
def IsPseudoEffective (D : Divisor ℝ X) : Prop :=
  ∃ A : Divisor ℝ X, IsAmple A ∧ ∀ ε : ℝ, 0 < ε → IsBig (D + ε • A)

/-- `D` is `ℝ`-linearly equivalent to an effective divisor. -/
def IsREffective (D : Divisor ℝ X) : Prop := ∃ E : Divisor ℝ X, 0 ≤ E ∧ RLinEquiv D E

/-- A Cartier divisor is free (base point free): at each point, some section of it does not vanish. -/
def IsFree (D : Divisor ℤ X) : Prop :=
  IsCartier D ∧ ∀ x : X.toScheme, ∃ φ : FF X, ∃ E : Divisor ℤ X,
    IsDivOn (E - D) φ Set.univ ∧ 0 ≤ E ∧ x ∈ nonvanishing E Set.univ

/-- A semiample `ℝ`-divisor: `ℝ`-linearly equivalent to a nonnegative combination of Cartier divisors that have a free multiple. -/
def IsSemiample (D : Divisor ℝ X) : Prop :=
  ∃ (N : ℕ) (r : Fin N → ℝ) (A : Fin N → Divisor ℤ X), (∀ i, 0 ≤ r i) ∧
    (∀ i, ∃ m : ℕ, 0 < m ∧ IsFree ((m : ℤ) • A i)) ∧ RLinEquiv D (∑ i, r i • (A i).toReal)

/-- The space of global sections `H⁰(X, 𝒪(D))`, as the `k`-span of the rational functions `φ` with `D + div φ ≥ 0`. -/
noncomputable def sections (D : Divisor ℤ X) : Submodule k (FF X) :=
  Submodule.span k {φ | φ ≠ 0 ∧ ∀ P, 0 ≤ D P + ordAt φ P}

/-- `h⁰(X, 𝒪(D))`. -/
noncomputable def h0 (D : Divisor ℤ X) : ℕ := Module.finrank k (sections D)

open Classical in
/-- The Iitaka dimension of an `ℝ`-divisor: `⊥` when no multiple `⌊m D⌋` has a section, and otherwise the largest `κ` such that `h⁰(⌊m D⌋) ≥ c m^κ` for infinitely many `m`. -/
noncomputable def iitakaDim (D : Divisor ℝ X) : WithBot ℕ :=
  if ∀ m : ℕ, 0 < m → h0 (D.roundDown m) = 0 then ⊥
  else ((sSup {κ : ℕ | ∃ c : ℝ, 0 < c ∧ ∃ᶠ m : ℕ in atTop, c * (m : ℝ) ^ κ ≤ h0 (D.roundDown m)} : ℕ) : WithBot ℕ)

open Classical in
/-- The numerical dimension `κ_σ` of Nakayama (risk 4 of spec 06.5): `⊥` when `D` is not pseudo-effective, and otherwise the largest `κ` such that, for some ample Cartier divisor `A`, `h⁰(⌊m D⌋ + A) ≥ c m^κ` for infinitely many `m`. -/
noncomputable def numericalDim (D : Divisor ℝ X) : WithBot ℕ :=
  if ¬ IsPseudoEffective D then ⊥
  else ((sSup {κ : ℕ | ∃ A : Divisor ℤ X, IsRelAmple A X.str ∧ ∃ c : ℝ, 0 < c ∧
      ∃ᶠ m : ℕ in atTop, c * (m : ℝ) ^ κ ≤ h0 (D.roundDown m + A)} : ℕ) : WithBot ℕ)

/-! ## Curves and intersection numbers -/

/-- The curves of `X`: the points of height one, that is the generic points of the closed integral subschemes of dimension one. -/
def Curve (X : NormalVariety k) : Type u := {c : X.toScheme // height c = 1}

/-- The places of a curve `C`: the normalized discrete valuations of its function field `κ(C)` that are trivial on `k`. -/
def Place (C : Curve X) : Type u :=
  {w : Valuation (X.toScheme.residueField C.1) VZ //
    (∀ a : k, a ≠ 0 → w (X.toResidueField C.1 a) = 1) ∧ ∃ π, w π = WithZero.exp (-1 : ℤ)}

/-- The point `p` of the closure of `C` is the centre of the place `w`. -/
def IsPlaceCentre {C : Curve X} (w : Place C) (p : X.toScheme) (h : C.1 ⤳ p) : Prop :=
  (∀ s : X.toScheme.presheaf.stalk p,
    w.1 ((X.toScheme.presheaf.stalkSpecializes h ≫ X.toScheme.residue C.1).hom s) ≤ 1) ∧
  ∀ s ∈ IsLocalRing.maximalIdeal (X.toScheme.presheaf.stalk p),
    w.1 ((X.toScheme.presheaf.stalkSpecializes h ≫ X.toScheme.residue C.1).hom s) < 1

/-- `d` is the intersection number `D · C` of a Cartier divisor and a curve: the degree of `𝒪(D)` on the normalization of `C`. Move `D` by the divisor of `g` so that `C` is not in its support. At each place `w` of `C`, take a local equation `s` of `D + div g` near the centre of `w`; it is a unit at `C`, and `w` gives the order of its restriction. The sum of these orders is `d`. Each place has degree one, because `k` is algebraically closed. -/
def IsIntersectionNumber (D : Divisor ℤ X) (C : Curve X) (d : ℤ) : Prop :=
  ∃ g : FF X, g ≠ 0 ∧ ∃ e : Place C → ℤ, (Function.support e).Finite ∧ d = ∑ᶠ w, e w ∧
    ∀ w : Place C, ∃ p : X.toScheme, ∃ h : C.1 ⤳ p, IsPlaceCentre w p h ∧
      ∃ U : X.toScheme.Opens, p ∈ U ∧ ∃ s : X.toScheme.presheaf.stalk C.1, IsUnit s ∧
        (∀ Q : PrimeDivisor X, Q.1 ∈ U → D Q + ordAt g Q = ordAt (algebraMap _ (FF X) s) Q) ∧
        w.1 (X.toScheme.residue C.1 |>.hom s) = WithZero.exp (-(e w))

/-- The `ℝ`-Cartier divisors. -/
def RCartier (X : NormalVariety k) : Type u := {D : Divisor ℝ X // IsRCartier D}

/-- The ambient space of the curve classes: the real functions on the `ℝ`-Cartier divisors. -/
abbrev CurveSpace (X : NormalVariety k) : Type u := RCartier X → ℝ

/-- The intersection numbers of `ℝ`-Cartier divisors with the curves of `X`. The values on Cartier divisors are fixed by `IsIntersectionNumber`, and the values on `ℝ`-Cartier divisors by linearity. So there is at most one structure, up to the values on divisors that are not `ℝ`-Cartier. The field `finiteDim` is the theorem of the base (spec 03.14). F2 asks for one instance of this structure (spec 06.3). -/
structure IntersectionData (X : NormalVariety k) where
  /-- The intersection number `D · C`. -/
  dot : Divisor ℝ X → Curve X → ℝ
  dot_cartier : ∀ D : Divisor ℤ X, IsCartier D → ∀ C, ∃ d : ℤ,
    IsIntersectionNumber D C d ∧ dot D.toReal C = d
  dot_add : ∀ D D', IsRCartier D → IsRCartier D' → ∀ C, dot (D + D') C = dot D C + dot D' C
  dot_smul : ∀ (r : ℝ) D, IsRCartier D → ∀ C, dot (r • D) C = r * dot D C
  finiteDim : FiniteDimensional ℝ
    (Submodule.span ℝ (Set.range (fun C : Curve X => fun D : RCartier X => dot D.1 C)))

namespace IntersectionData

variable (I : IntersectionData X)

/-- The class of a curve in `N₁(X)`. -/
def curveClass (C : Curve X) : CurveSpace X := fun D => I.dot D.1 C

/-- `N₁(X)`: the span of the curve classes. -/
def N₁ : Submodule ℝ (CurveSpace X) := Submodule.span ℝ (Set.range I.curveClass)

/-- The closed cone of curves `NE(X)`, the closure of the cone of the curve classes. -/
noncomputable def coneOfCurves : PointedCone ℝ (CurveSpace X) :=
  (Submodule.span (Nonneg ℝ) (Set.range I.curveClass)).closure

/-- The value of an `ℝ`-Cartier divisor on a class. -/
def eval (z : CurveSpace X) (D : RCartier X) : ℝ := z D

end IntersectionData

/-- A nef `ℝ`-divisor. -/
def IsNef (I : IntersectionData X) (D : Divisor ℝ X) : Prop := ∀ C, 0 ≤ I.dot D C

/-- The nef threshold of KM98 Theorem 3.5: the largest `t ≥ 0` such that `H + t D` is nef. Let `H` and `D` be `ℝ`-Cartier, `H` nef and `D` not nef. Then the set of these `t` is a closed bounded interval that contains `0`, so the supremum is a maximum. When `D` is nef, the set has no upper bound and the value is `0`. The statements use the threshold only when `D` is not nef. -/
noncomputable def nefThreshold (I : IntersectionData X) (H D : Divisor ℝ X) : ℝ :=
  sSup {t : ℝ | 0 ≤ t ∧ IsNef I (H + t • D)}

/-- The scaling threshold of BCHM 3.10: the least `t ≥ 0` such that `D + t C` is nef. In a program with scaling of `C`, the divisor `D` is `K + Δ`. When no `t` makes `D + t C` nef, the set is empty and the value is `0`. Then no step with scaling exists, because a step with scaling asks that `D + λ C` is nef. -/
noncomputable def scalingThreshold (I : IntersectionData X) (D C : Divisor ℝ X) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ IsNef I (D + t • C)}

/-- The morphism `f` contracts the curve `C`: the image of `C` is a closed point. -/
def IsContracted {Z : Scheme.{u}} (f : X.toScheme ⟶ Z) (C : Curve X) : Prop :=
  IsClosed ({f.base C.1} : Set Z)

/-- A nef `ℝ`-divisor relative to `f`: nonnegative on the curves that `f` contracts. -/
def IsNefOver (I : IntersectionData X) {Z : Scheme.{u}} (D : Divisor ℝ X) (f : X.toScheme ⟶ Z) :
    Prop :=
  ∀ C, IsContracted f C → 0 ≤ I.dot D C

/-- The ray `ℝ≥0 • z`. -/
def ray (z : CurveSpace X) : Set (CurveSpace X) := {y | ∃ t : ℝ, 0 ≤ t ∧ y = t • z}

/-- An extremal ray of the cone of curves. -/
structure ExtremalRay (I : IntersectionData X) where
  /-- A generator of the ray. -/
  generator : CurveSpace X
  mem : generator ∈ I.coneOfCurves
  ne_zero : generator ≠ 0
  isExtremal : ∀ a b, a ∈ I.coneOfCurves → b ∈ I.coneOfCurves → a + b ∈ ray generator →
    a ∈ ray generator ∧ b ∈ ray generator

/-! ## Contractions, flips and programs -/

/-- A contraction: a projective morphism `f` with `f_* 𝒪_X = 𝒪_Z`. -/
def IsContraction {Z : NormalVariety k} (f : X.toScheme ⟶ Z.toScheme) : Prop :=
  IsProjectiveHom f ∧ ∀ U : Z.toScheme.Opens, IsIso (f.app U)

/-- The contraction `f` has relative Picard number one: it contracts a curve, and the classes of the curves that it contracts are positive multiples of each other. -/
def IsExtremalContraction (I : IntersectionData X) {Z : Scheme.{u}} (f : X.toScheme ⟶ Z) : Prop :=
  ∃ C₀, IsContracted f C₀ ∧ ∀ C, IsContracted f C →
    ∃ t : ℝ, 0 < t ∧ I.curveClass C = t • I.curveClass C₀

/-- A pair on a projective normal variety, with the intersection numbers of the variety. These are the models that a program runs through. -/
structure PairModel (k : Type u) [Field k] where
  /-- The variety. -/
  X : NormalVariety k
  /-- The pair. -/
  P : Pair X
  /-- The intersection numbers. -/
  I : IntersectionData X
  projective : IsProjective X

/-- `Δ_B` is the strict transform of `Δ_A` along `A ⟶ Z ⟵ B`: each prime divisor of `B` maps to the image of a prime divisor of `A`, with the same coefficient. -/
def IsStrictTransform (A B : PairModel k) {Z : NormalVariety k}
    (f : A.X.toScheme ⟶ Z.toScheme) (g : B.X.toScheme ⟶ Z.toScheme) : Prop :=
  ∀ Q : PrimeDivisor B.X, ∃ P : PrimeDivisor A.X, f.base P.1 = g.base Q.1 ∧ B.P.Δ Q = A.P.Δ P

/-- The step data of a program from `A` to `B` over a variety `Z`: `f` is the birational contraction of a `(K + Δ)`-negative extremal ray, `g` is small, `K_B + Δ_B` is ample over `Z`, and `Δ_B` is the strict transform of `Δ_A`. When `K_Z + Δ_Z` is `ℝ`-Cartier, `B = Z` and `g` is the identity: a divisorial contraction. Otherwise `B` is the flip. -/
structure MMPStepData (A B : PairModel k) where
  /-- The base of the step. -/
  Z : NormalVariety k
  /-- The contraction of the ray. -/
  f : A.X.toScheme ⟶ Z.toScheme
  /-- The small map from the next model. -/
  g : B.X.toScheme ⟶ Z.toScheme
  over_f : f ≫ Z.str = A.X.str
  over_g : g ≫ Z.str = B.X.str
  contraction_f : IsContraction f
  birational_f : IsBirationalHom f
  extremal : IsExtremalContraction A.I f
  negative : IsRAmpleOver (-A.P.KΔ) f
  contraction_g : IsContraction g
  small_g : IsSmallHom g
  positive : IsRAmpleOver B.P.KΔ g
  strict : IsStrictTransform A B f g

/-- `B` is the result of one step of a `(K + Δ)`-minimal model program on `A`. -/
def IsMMPStep (A B : PairModel k) : Prop := Nonempty (MMPStepData A B)

/-- `B` is a `(K + Δ)`-flip of `A`: a step whose contraction is small. -/
def IsFlip (A B : PairModel k) : Prop := ∃ s : MMPStepData A B, IsSmallHom s.f

/-- A Mori fibre space structure on `A`: a contraction of a `(K + Δ)`-negative extremal ray to a variety of smaller dimension. -/
def IsMoriFibreSpace (A : PairModel k) : Prop :=
  ∃ (Z : NormalVariety k) (f : A.X.toScheme ⟶ Z.toScheme), f ≫ Z.str = A.X.str ∧
    IsContraction f ∧ Z.dim < A.X.dim ∧ IsExtremalContraction A.I f ∧ IsRAmpleOver (-A.P.KΔ) f

/-- `K + Δ` as an `ℝ`-Cartier divisor. -/
def Pair.KΔR (P : Pair X) : RCartier X := ⟨P.KΔ, P.rCartier⟩

/-- The conclusion of the cone theorem for a model `A` (KM98 Theorem 3.7). There are countably many curves `Cᵢ` with `(K + Δ) · Cᵢ < 0`, such that:
1. `NE(X) = NE(X)_{K+Δ ≥ 0} + Σ ℝ≥0 [Cᵢ]`;
2. each ray `ℝ≥0 [Cᵢ]` is extremal;
3. for each ample `H` and each `ε > 0`, only finitely many of these rays have `(K + Δ + ε H) · Cᵢ < 0`.

The theorem also says that the `Cᵢ` are rational curves with `-(K + Δ) · Cᵢ ≤ 2 dim X`. That part is statement S09, because it needs the vocabulary of rational curves. -/
def ConeDecomposition (A : PairModel k) : Prop :=
  ∃ (ι : Type u) (_ : Countable ι) (C : ι → Curve A.X),
    (∀ i, A.I.dot A.P.KΔ (C i) < 0) ∧
    (∀ z, z ∈ A.I.coneOfCurves ↔ ∃ y ∈ A.I.coneOfCurves, 0 ≤ y A.P.KΔR ∧
      ∃ (s : Finset ι) (t : ι → ℝ), (∀ i, 0 ≤ t i) ∧ z = y + ∑ i ∈ s, t i • A.I.curveClass (C i)) ∧
    (∀ i, ∃ R : ExtremalRay A.I, ray R.generator = ray (A.I.curveClass (C i))) ∧
    ∀ H : Divisor ℝ A.X, IsAmple H → ∀ ε : ℝ, 0 < ε →
      ((fun i => ray (A.I.curveClass (C i))) '' {i | A.I.dot (A.P.KΔ + ε • H) (C i) < 0}).Finite

/-- `K + Δ` is nef on the model. -/
def IsMinimal (A : PairModel k) : Prop := IsNef A.I A.P.KΔ

/-- A program: a sequence of steps of length `len` (finite or infinite). It is complete when it is finite and ends at a minimal model or a Mori fibre space. -/
structure Program (A : PairModel k) where
  /-- The number of steps, or `⊤`. -/
  len : ℕ∞
  /-- The models. -/
  model : ℕ → PairModel k
  start : model 0 = A
  step : ∀ i : ℕ, (i : ℕ∞) < len → IsMMPStep (model i) (model (i + 1))

/-- A program is complete when it is finite and its last model is minimal or a Mori fibre space. -/
def Program.IsComplete {A : PairModel k} (p : Program A) : Prop :=
  ∃ n : ℕ, p.len = n ∧ (IsMinimal (p.model n) ∨ IsMoriFibreSpace (p.model n))

/-- An infinite sequence of steps from `A`. -/
def HasInfiniteProgram (A : PairModel k) : Prop :=
  ∃ model : ℕ → PairModel k, model 0 = A ∧ ∀ i, IsMMPStep (model i) (model (i + 1))

/-- An infinite sequence of flips from `A`. -/
def HasInfiniteFlips (A : PairModel k) : Prop :=
  ∃ model : ℕ → PairModel k, model 0 = A ∧ ∀ i, IsFlip (model i) (model (i + 1))

/-- The step data `s` from `A` to `B` sends the divisor `D` of `A` to the divisor `D'` of `B`: each prime divisor of `B` has the coefficient in `D'` of the prime divisor of `A` with the same image in the base. So `D'` is the strict transform of `D`. -/
def MMPStepData.IsStrictTransformOf {A B : PairModel k} (s : MMPStepData A B) (D : Divisor ℝ A.X)
    (D' : Divisor ℝ B.X) : Prop :=
  ∀ Q : PrimeDivisor B.X, ∃ P : PrimeDivisor A.X, s.f.base P.1 = s.g.base Q.1 ∧ D' Q = D P

/-- The step data `s` is an isomorphism near the set `S` of the first model: the contraction and the small map are isomorphisms over an open set of the base that contains the image of `S`. -/
def MMPStepData.IsIsoNear {A B : PairModel k} (s : MMPStepData A B) (S : Set A.X.toScheme) : Prop :=
  ∃ V : s.Z.toScheme.Opens, s.f.base '' S ⊆ (V : Set s.Z.toScheme) ∧ IsIso (s.f ∣_ V) ∧ IsIso (s.g ∣_ V)

/-- `B` is the result of one step of the `(K + Δ)`-program with scaling of `C` on `A` (BCHM 3.10), and `C'` is the strict transform of `C` on `B`. Let `λ` be the scaling threshold of `C`. Then `K + Δ + λ C` is nef, and it is zero on each curve that the contraction contracts. The step is `(K + Δ)`-negative, as each step of a program is. -/
def IsScalingStep (A B : PairModel k) (C : Divisor ℝ A.X) (C' : Divisor ℝ B.X) : Prop :=
  ∃ s : MMPStepData A B, s.IsStrictTransformOf C C' ∧
    IsNef A.I (A.P.KΔ + scalingThreshold A.I A.P.KΔ C • C) ∧
    ∀ C₀, IsContracted s.f C₀ → A.I.dot (A.P.KΔ + scalingThreshold A.I A.P.KΔ C • C) C₀ = 0

/-- Each program from `A` runs and ends. No sequence of steps from `A` is infinite. At the last model of each finite program, `K + Δ` is nef, or the model is a Mori fibre space, or one more step exists. So each program extends to a complete program. -/
def EveryProgramEnds (A : PairModel k) : Prop :=
  ¬ HasInfiniteProgram A ∧ ∀ (p : Program A) (n : ℕ), p.len = n →
    IsMinimal (p.model n) ∨ IsMoriFibreSpace (p.model n) ∨ ∃ B, IsMMPStep (p.model n) B

/-! ## Birational maps and minimal models -/

/-- The prime divisor `P` of `X` and the prime divisor `Q` of `Y` are the same divisor through the identification `σ` of the function fields: the valuation of `Q`, moved to `k(X)`, has its centre at `P`. -/
def SameDivisor {Y : NormalVariety k} (σ : FF Y ≃ₐ[k] FF X) (P : PrimeDivisor X) (Q : PrimeDivisor Y) :
    Prop :=
  ∀ φ : FF X, φ ≠ 0 → ordAt (σ.symm φ) Q = ordAt φ P

/-- A minimal model of `(X, Δ)` in the sense of KM98 Definition 3.50: a projective lc pair `(Y, Δ_Y)` and a birational contraction `X ⇢ Y`, given by `σ : k(Y) ≅ k(X)`, such that each prime divisor of `Y` comes from a prime divisor of `X` with the same coefficient, `K_Y + Δ_Y` is nef, and each prime divisor of `X` that `Y` contracts has a smaller log discrepancy on `X` than on `Y`. -/
def IsMinimalModel (A B : PairModel k) : Prop :=
  IsLc B.P ∧ IsMinimal B ∧ ∃ σ : FF B.X ≃ₐ[k] FF A.X,
    (∀ Q : PrimeDivisor B.X, ∃ P : PrimeDivisor A.X, SameDivisor σ P Q ∧ B.P.Δ Q = A.P.Δ P) ∧
    ∀ P : PrimeDivisor A.X, (∀ Q, ¬ SameDivisor σ P Q) →
      ∀ v : Valuation (FF A.X) VZ, IsDivisorial v → IsCentre v P.1 →
        ∀ a b, LogDiscrepancyIs A.P v a → LogDiscrepancyIs B.P (v.comap σ.toRingHom) b → a < b

/-! ## Resolutions -/

/-- `(X, Δ)` has a log resolution: a proper birational morphism `f : Y → X` from a smooth variety such that the exceptional divisors and the strict transforms of the components of `Δ` have simple normal crossings at each point of `Y`, and `f` is an isomorphism outside the images of the exceptional divisors. This is the hypothesis that spec 2161 shares (Q-09). -/
def HasLogResolution (P : Pair X) : Prop :=
  ∃ (Y : NormalVariety k) (f : Y.toScheme ⟶ X.toScheme), f ≫ X.str = Y.str ∧ IsProper f ∧
    IsBirationalHom f ∧ Y.IsSmooth ∧
    (∀ y, IsSncAt {E : PrimeDivisor Y | coheight (f.base E.1) ≠ 1 ∨
      ∃ Q : PrimeDivisor X, f.base E.1 = Q.1 ∧ P.Δ Q ≠ 0} y) ∧
    ∀ x : X.toScheme, (∀ E : PrimeDivisor Y, coheight (f.base E.1) ≠ 1 → ¬ f.base E.1 ⤳ x) →
      ∃ V : X.toScheme.Opens, x ∈ V ∧ IsIso (f ∣_ V)

end MinimalModel

end
