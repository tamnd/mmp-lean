/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import MinimalModel.Statements.BasicRelative

/-!
# Generalized pairs

The vocabulary of the statement S27 (`GeneralizedLcFlips`, in `Termination.lean`). It follows Hu and Liu, arXiv:2603.03817, Definitions 2.5, 2.7 and 2.9, with the base `U` a point.

## The choices

* A birational model of `X` is a projective birational morphism `f : Y → X` over `k`, with the identification `σ = f^* : k(X) ≅ k(Y)` (`IsBirModel`).
* The pullback of a Cartier divisor `D` along `f` is the divisor that has the local equation `f^* φ` on `f⁻¹ U` wherever `D` has the local equation `φ` on `U` (`IsCartierPullback`). The pullback of an `ℝ`-Cartier divisor is the same combination of the pullbacks of Cartier divisors (`IsRPullback`).
* The nef part of a generalized pair is a b-divisor `M` that descends to a model `Y` with `M_Y` nef (Hu-Liu 2.5). It is given by its data on one such model (`NefPart`): `M_Y` on `Y`, `ℝ`-Cartier and nef. On each higher model `X'` the trace `M_{X'}` is the pullback of `M_Y`, so the coefficient of `M` along a divisorial valuation `v` is the order of `M_Y` along `v` (`NefPart.OrdIs`). The trace `M_X` on `X` is the pushforward of `M_Y` (`NefPart.IsTrace`).
* Two nef parts are the same b-divisor when they descend to a common model with the same trace there (`SameBDivisor`).
* The log discrepancy of a generalized pair along `v` is `1 + ord_v(K_{X'}) - ord_v(h^*(K + B + M_X)) + ord_v(M_{X'})`, which is `1 - mult_E B'` in the notation of Hu-Liu 2.9 (`GenLogDiscrepancyIs`). The first three terms are the log discrepancy of the divisor `B + M_X`, which may not be effective (`LogDiscrepancyOfIs`).

Each definition has a body, and the file uses none of the escape hatches of spec 09.2.
-/

universe u

open AlgebraicGeometry CategoryTheory

namespace MinimalModel

variable {k : Type u} [Field k] {X : NormalVariety k}

/-! ## Birational models and pullbacks -/

/-- `f : Y → X` is a birational model of `X`: a projective birational morphism over `k`, and `σ : k(X) ≅ k(Y)` is its pullback on the function fields. -/
def IsBirModel {Y : NormalVariety k} (f : Y.toScheme ⟶ X.toScheme) (σ : FF X ≃ₐ[k] FF Y) : Prop :=
  f ≫ X.str = Y.str ∧ IsProjectiveHom (X := Y) f ∧ IsBirationalHom f ∧
    IsBirMapOver (X := Y) (Y := X) f (𝟙 X.toScheme) σ

/-- `D'` on `Y` is the pullback `f^* D` of the Cartier divisor `D` on `X`, where `σ` is the pullback of the functions: on each open set `U` where `D` is the divisor of `φ`, `D'` is the divisor of `σ φ` on `f⁻¹ U`. The divisor `D` is Cartier, so these open sets cover `X` and they fix `D'`. -/
def IsCartierPullback {Y : NormalVariety k} (f : Y.toScheme ⟶ X.toScheme) (σ : FF X ≃ₐ[k] FF Y)
    (D : Divisor ℤ X) (D' : Divisor ℤ Y) : Prop :=
  IsCartier D ∧ ∀ (U : X.toScheme.Opens) (φ : FF X), IsDivOn D φ U →
    IsDivOn D' (σ φ) ((f ⁻¹ᵁ U : Y.toScheme.Opens) : Set Y.toScheme)

/-- `D'` on `Y` is the pullback `f^* D` of the `ℝ`-Cartier divisor `D`: `D = Σ rᵢ Eᵢ` with `Eᵢ` Cartier, and `D' = Σ rᵢ f^* Eᵢ`. -/
def IsRPullback {Y : NormalVariety k} (f : Y.toScheme ⟶ X.toScheme) (σ : FF X ≃ₐ[k] FF Y)
    (D : Divisor ℝ X) (D' : Divisor ℝ Y) : Prop :=
  ∃ (N : ℕ) (r : Fin N → ℝ) (E : Fin N → Divisor ℤ X) (E' : Fin N → Divisor ℤ Y),
    (∀ i, IsCartierPullback f σ (E i) (E' i)) ∧ D = ∑ i, r i • (E i).toReal ∧
      D' = ∑ i, r i • (E' i).toReal

/-! ## The nef part -/

/-- The nef part of a generalized pair on `X` (Hu-Liu Definition 2.5, with `U` a point): a b-divisor that descends to a birational model `f : Y → X`, given by its trace `M_Y` on `Y`. The divisor `M_Y` is `ℝ`-Cartier and nef. -/
structure NefPart (X : NormalVariety k) where
  /-- The model where the b-divisor descends. -/
  Y : NormalVariety k
  /-- The morphism to `X`. -/
  f : Y.toScheme ⟶ X.toScheme
  /-- The pullback of the functions. -/
  σ : FF X ≃ₐ[k] FF Y
  isModel : IsBirModel f σ
  /-- The trace on `Y`. -/
  M : Divisor ℝ Y
  rCartier : IsRCartier M
  /-- The intersection numbers of `Y`. -/
  I : IntersectionData Y
  nef : IsNef I M

/-- `M_X` is the trace of the nef part on `X`: the pushforward `f_* M_Y`. Each prime divisor of `X` has the coefficient of its strict transform on `Y`. -/
def NefPart.IsTrace (N : NefPart X) (MX : Divisor ℝ X) : Prop :=
  ∀ Q : PrimeDivisor X, ∃ P : PrimeDivisor N.Y, SameDivisor N.σ P Q ∧ MX Q = N.M P

/-- `m` is the coefficient of the b-divisor along the valuation `v` of `k(X)`. Move `v` to `k(Y)` and take its centre `y` on `Y`. Near `y`, write `M_Y = Σ rᵢ div(hᵢ)`. Then `m = Σ rᵢ ord_v(hᵢ)`. On a model `X'` over `Y` where `v` is a prime divisor `E`, this is the coefficient of `E` in the pullback of `M_Y`, that is in `M_{X'}`. -/
def NefPart.OrdIs (N : NefPart X) (v : Valuation (FF X) VZ) (m : ℝ) : Prop :=
  ∃ y : N.Y.toScheme, IsCentre (X := N.Y) (v.comap N.σ.symm.toRingHom) y ∧
    ∃ U : N.Y.toScheme.Opens, y ∈ U ∧
    ∃ (n : ℕ) (r : Fin n → ℝ) (h : Fin n → FF N.Y) (e : Fin n → ℤ),
      (∀ i, v (N.σ.symm (h i)) = WithZero.exp (-(e i))) ∧
      (∀ Q : PrimeDivisor N.Y, Q.1 ∈ U → N.M Q = ∑ i, r i * (ordAt (h i) Q : ℝ)) ∧
      m = ∑ i, r i * (e i : ℝ)

/-- The nef parts `N` on `X` and `N'` on `X'` are the same b-divisor through `σ : k(X') ≅ k(X)`: they descend to a common model `W`, over the models of both, with the same trace `M_W`. The two identifications of `k(X)` with `k(W)` agree. -/
def SameBDivisor {X' : NormalVariety k} (N : NefPart X) (N' : NefPart X') (σ : FF X' ≃ₐ[k] FF X) :
    Prop :=
  ∃ (W : NormalVariety k) (p : W.toScheme ⟶ N.Y.toScheme) (p' : W.toScheme ⟶ N'.Y.toScheme)
    (τ : FF N.Y ≃ₐ[k] FF W) (τ' : FF N'.Y ≃ₐ[k] FF W) (MW : Divisor ℝ W),
    IsBirModel (X := N.Y) (Y := W) p τ ∧ IsBirModel (X := N'.Y) (Y := W) p' τ' ∧
    N.σ.trans τ = σ.symm.trans (N'.σ.trans τ') ∧
    IsRPullback (X := N.Y) (Y := W) p τ N.M MW ∧ IsRPullback (X := N'.Y) (Y := W) p' τ' N'.M MW

/-! ## Generalized pairs and their singularities -/

/-- A generalized pair `(X, B, M)` (Hu-Liu Definition 2.7, with `U` a point): a canonical divisor `K`, an effective `ℝ`-divisor `B`, a nef part `M` with trace `M_X` on `X`, and `K + B + M_X` is `ℝ`-Cartier. -/
structure GenPair (X : NormalVariety k) where
  /-- The canonical divisor. -/
  K : CanonicalDivisor X
  /-- The boundary. -/
  B : Divisor ℝ X
  nonneg : 0 ≤ B
  /-- The nef part. -/
  N : NefPart X
  /-- The trace of the nef part on `X`. -/
  MX : Divisor ℝ X
  trace : N.IsTrace MX
  rCartier : IsRCartier (K.K.toReal + B + MX)

/-- The divisor `K + B + M_X`. -/
noncomputable def GenPair.KBM (G : GenPair X) : Divisor ℝ X := G.K.K.toReal + G.B + G.MX

/-- `A` is the log discrepancy of `v` with respect to the canonical divisor `K` and the `ℝ`-divisor `Δ`, which may not be effective. The body is the one of `LogDiscrepancyIs`, with `K + Δ` for the log canonical divisor of the pair. -/
def LogDiscrepancyOfIs (K : CanonicalDivisor X) (Δ : Divisor ℝ X) (v : Valuation (FF X) VZ) (A : ℝ) :
    Prop :=
  ∃ x, IsCentre v x ∧ ∃ U : X.toScheme.Opens, x ∈ U ∧
  ∃ (N : ℕ) (r : Fin N → ℝ) (h : Fin N → FF X) (e : Fin N → ℤ) (m : ℤ),
    (∀ i, v (h i) = WithZero.exp (-(e i))) ∧ FormOrd v K.ω m ∧
    (∀ Q : PrimeDivisor X, Q.1 ∈ U → (K.K.toReal + Δ) Q = ∑ i, r i * (ordAt (h i) Q : ℝ)) ∧
    A = 1 + m - ∑ i, r i * (e i : ℝ)

/-- `A` is the log discrepancy of `v` with respect to the generalized pair (Hu-Liu Definition 2.9). On a model `h : X' → X` where `v` is a prime divisor `E`, write `K_{X'} + B' + M_{X'} = h^*(K + B + M_X)`. Then `A = 1 - mult_E B'`, which is the log discrepancy `a` of `v` with respect to `K + B + M_X` plus the coefficient `m` of the b-divisor along `v`. -/
def GenLogDiscrepancyIs (G : GenPair X) (v : Valuation (FF X) VZ) (A : ℝ) : Prop :=
  ∃ a m : ℝ, LogDiscrepancyOfIs G.K (G.B + G.MX) v a ∧ G.N.OrdIs v m ∧ A = a + m

/-- A log canonical generalized pair (Hu-Liu Definition 2.9): the coefficients of `B` are at most one, and each log discrepancy is nonnegative. -/
def IsGenLc (G : GenPair X) : Prop :=
  (∀ Q, G.B Q ≤ 1) ∧ ∀ v, IsDivisorial v → ∀ A, GenLogDiscrepancyIs G v A → 0 ≤ A

end MinimalModel
