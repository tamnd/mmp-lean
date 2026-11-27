/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import MinimalModel.Statements.BasicRelative
import MinimalModel.Statements.Cones

/-!
# Mori fibre spaces, flops and Sarkisov links

The vocabulary of the statement S36 (`Sarkisov`, in `Models.lean`). It follows Hacon and McKernan, The Sarkisov program, J. Algebraic Geom. 22 (2013), arXiv:0905.0946, Section 1.

## The choices

* A Mori fibre space (`MoriFibreSpace`) is a projective `ℚ`-factorial klt pair `(X, Δ)` with a contraction `φ : X → S` of relative Picard number one, such that `dim S < dim X` and `-(K + Δ)` is ample over `S` (Hacon-McKernan, Conjecture 1.2(2)).
* The intersection numbers of the other varieties of a diagram are not part of the data. A contraction is extremal when it is extremal for some intersection data (`IsExtremalContr`). The intersection data has at most one value on each `ℝ`-Cartier divisor, so this does not depend on the choice.
* A `(K + Ξ)`-flop over a base `V` (`IsFlopOver`) is a diagram `X → W ← X⁺` over `V`: a small extremal contraction `f` with `K + Ξ` trivial on the curves that it contracts, a small contraction `g`, and an `ℝ`-divisor `D` with `-D` ample over `W` and its strict transform `D⁺` ample over `W` (KM98 Definition 6.10). The target is `ℚ`-factorial, and `Ξ⁺` is the strict transform of `Ξ`. A composition of flops is `FlopChain`.
* A Sarkisov link (`IsSarkisovLink`) is one of the diagrams of types I, II, III, IVm and IVs of Hacon-McKernan, Section 1. The equality `S = T` of type II is an isomorphism over `k`. A sequence of links (`SarkisovChain`) ends with an isomorphism of Mori fibre spaces.
* A run of the minimal model program (`IsMMPRun`) is a finite sequence of steps (`MMPStepData`), with the birational map that it induces.

Each birational map `X ⇢ Y` is an isomorphism `k(Y) ≅ k(X)` of function fields over `k`, as in `BasicRelative.lean`. Each definition has a body, and the file uses none of the escape hatches of spec 09.2.
-/

universe u

open AlgebraicGeometry CategoryTheory

namespace MinimalModel

variable {k : Type u} [Field k] {X : NormalVariety k}

/-! ## Mori fibre spaces -/

/-- A Mori fibre space `φ : X → S` (Hacon-McKernan, Conjecture 1.2(2)): a projective `ℚ`-factorial klt pair `(X, Δ)` with a contraction `φ` of a `(K + Δ)`-negative extremal ray to a variety of smaller dimension. -/
structure MoriFibreSpace (k : Type u) [Field k] where
  /-- The pair `(X, Δ)`, with the intersection numbers of `X`. -/
  A : PairModel k
  /-- The base. -/
  S : NormalVariety k
  /-- The fibration. -/
  φ : A.X.toScheme ⟶ S.toScheme
  over : φ ≫ S.str = A.X.str
  contraction : IsContraction φ
  dim_lt : S.dim < A.X.dim
  extremal : IsExtremalContraction A.I φ
  negative : IsRAmpleOver (-A.P.KΔ) φ
  qFactorial : IsQFactorial A.X
  klt : IsKlt A.P

/-! ## Contractions and flops -/

/-- `f : X → Z` is an extremal contraction over `k`: a contraction of relative Picard number one, for some intersection data of `X`. -/
def IsExtremalContr {Z : NormalVariety k} (f : X.toScheme ⟶ Z.toScheme) : Prop :=
  f ≫ Z.str = X.str ∧ IsContraction f ∧ ∃ I : IntersectionData X, IsExtremalContraction I f

/-- `p : X → Z` is a divisorial contraction: a birational extremal contraction that maps a prime divisor of `X` to a point that is not a prime divisor of `Z`. -/
def IsDivisorialContr {Z : NormalVariety k} (p : X.toScheme ⟶ Z.toScheme) : Prop :=
  IsExtremalContr p ∧ IsBirationalHom p ∧ ∃ E : PrimeDivisor X, Order.coheight (p.base E.1) ≠ 1

/-- `τ : k(Z) ≅ k(X)` is the pullback of the functions along the birational morphism `p : X → Z`. -/
def IsFieldPullback {Z : NormalVariety k} (p : X.toScheme ⟶ Z.toScheme) (τ : FF Z ≃ₐ[k] FF X) : Prop :=
  IsBirMapOver (X := X) (Y := Z) p (𝟙 Z.toScheme) τ

/-- `K + Δ` is numerically trivial over `π`: it is zero on each curve that `π` contracts. -/
def IsNumTrivialOver (P : Pair X) {V : Scheme.{u}} (π : X.toScheme ⟶ V) : Prop :=
  ∃ I : IntersectionData X, ∀ C, IsContracted π C → I.dot P.KΔ C = 0

/-- The map `X ⇢ X⁺`, given by `σ : k(X⁺) ≅ k(X)`, is a `(K + Ξ)`-flop over `V` (KM98 Definition 6.10), where `(X, Ξ)` is the pair `P` and `(X⁺, Ξ⁺)` is the pair `P'`. There is a diagram `X → W ← X⁺` over `V` with:
* `f : X → W` a small contraction of relative Picard number one, with `K + Ξ` zero on each curve that `f` contracts;
* `g : X⁺ → W` a small contraction;
* `σ` the birational map over `W`, and `Ξ⁺` the strict transform of `Ξ`;
* an `ℝ`-divisor `D` with `-D` ample over `W` and its strict transform `D⁺` ample over `W`.

The variety `X⁺` is `ℚ`-factorial, as each variety of a link is. -/
def IsFlopOver {V X' : NormalVariety k} (P : Pair X) (P' : Pair X') (π : X.toScheme ⟶ V.toScheme)
    (π' : X'.toScheme ⟶ V.toScheme) (σ : FF X' ≃ₐ[k] FF X) : Prop :=
  IsQFactorial X' ∧
  ∃ (W : NormalVariety k) (f : X.toScheme ⟶ W.toScheme) (g : X'.toScheme ⟶ W.toScheme)
    (w : W.toScheme ⟶ V.toScheme), f ≫ W.str = X.str ∧ g ≫ W.str = X'.str ∧ f ≫ w = π ∧
    g ≫ w = π' ∧ IsContraction f ∧ IsSmallHom f ∧ IsContraction g ∧ IsSmallHom g ∧
    (∃ I : IntersectionData X, IsExtremalContraction I f ∧ ∀ C, IsContracted f C → I.dot P.KΔ C = 0) ∧
    IsBirMapOver (X := X) (Y := X') f g σ ∧ IsStrictPullback σ P'.Δ P.Δ ∧
    ∃ (D : Divisor ℝ X) (D' : Divisor ℝ X'), IsRAmpleOver (-D) f ∧ IsRAmpleOver D' g ∧
      IsStrictPullback σ D' D

/-- A composition of `(K + Ξ)`-flops over `V`, from `(X, Ξ)` with `π : X → V` to `Y` with `π_Y : Y → V`, which induces `σ : k(Y) ≅ k(X)`. The boundary moves by strict transform at each flop. With no flop, `Y = X`, `π_Y = π` and `σ` is the identity. -/
inductive FlopChain (V : NormalVariety k) : (X : NormalVariety k) → Pair X → (X.toScheme ⟶ V.toScheme) →
    (Y : NormalVariety k) → (Y.toScheme ⟶ V.toScheme) → (FF Y ≃ₐ[k] FF X) → Prop
  | refl (X : NormalVariety k) (P : Pair X) (π : X.toScheme ⟶ V.toScheme) :
      FlopChain V X P π X π AlgEquiv.refl
  | step {X X' Y : NormalVariety k} {P : Pair X} {P' : Pair X'} {π : X.toScheme ⟶ V.toScheme}
      {π' : X'.toScheme ⟶ V.toScheme} {πY : Y.toScheme ⟶ V.toScheme} {σ₁ : FF X' ≃ₐ[k] FF X}
      {σ₂ : FF Y ≃ₐ[k] FF X'} :
      IsFlopOver P P' π π' σ₁ → FlopChain V X' P' π' Y πY σ₂ → FlopChain V X P π Y πY (σ₂.trans σ₁)

/-! ## Sarkisov links

In each type, `φ : X → S` and `ψ : Y → T` are the Mori fibre spaces `M` and `N`, and `σ : k(Y) ≅ k(X)` is the birational map `X ⇢ Y`. There is a pair `(L, Ξ)` on the variety `L` on the top left of the diagram, klt and numerically trivial over the base of the diagram, and the top row is a composition of `(K + Ξ)`-flops over the base. -/

/-- A link of type I: `X' → X` is a divisorial contraction, `X' ⇢ Y` is a composition of flops over `S`, and `T → S` is an extremal contraction.
```
X' ⇢ Y
↓    ↓ ψ
X    T
φ ↘ ↙
   S
``` -/
def IsLinkI (M N : MoriFibreSpace k) (σ : FF N.A.X ≃ₐ[k] FF M.A.X) : Prop :=
  ∃ (X' : NormalVariety k) (Ξ : Pair X') (p : X'.toScheme ⟶ M.A.X.toScheme) (τ : FF M.A.X ≃ₐ[k] FF X')
    (t : N.S.toScheme ⟶ M.S.toScheme) (σ' : FF N.A.X ≃ₐ[k] FF X'),
    IsQFactorial X' ∧ IsQFactorial M.S ∧ IsQFactorial N.S ∧ IsDivisorialContr p ∧
    IsFieldPullback p τ ∧ IsExtremalContr t ∧ IsKlt Ξ ∧ IsNumTrivialOver Ξ (p ≫ M.φ) ∧
    FlopChain M.S X' Ξ (p ≫ M.φ) N.A.X (N.φ ≫ t) σ' ∧ σ = σ'.trans τ.symm

/-- A link of type II: `X' → X` and `Y' → Y` are divisorial contractions, `X' ⇢ Y'` is a composition of flops over `S`, and `S = T`, through an isomorphism `ι` over `k`.
```
X' ⇢ Y'
↓     ↓
X     Y
φ ↓   ↓ ψ
S  =  T
``` -/
def IsLinkII (M N : MoriFibreSpace k) (σ : FF N.A.X ≃ₐ[k] FF M.A.X) : Prop :=
  ∃ (X' : NormalVariety k) (Ξ : Pair X') (p : X'.toScheme ⟶ M.A.X.toScheme) (τ : FF M.A.X ≃ₐ[k] FF X')
    (Y' : NormalVariety k) (q : Y'.toScheme ⟶ N.A.X.toScheme) (τ' : FF N.A.X ≃ₐ[k] FF Y')
    (ι : M.S.toScheme ≅ N.S.toScheme) (σ' : FF Y' ≃ₐ[k] FF X'),
    IsQFactorial X' ∧ IsQFactorial Y' ∧ IsQFactorial M.S ∧ ι.hom ≫ N.S.str = M.S.str ∧
    IsDivisorialContr p ∧ IsFieldPullback p τ ∧ IsDivisorialContr q ∧ IsFieldPullback q τ' ∧
    IsKlt Ξ ∧ IsNumTrivialOver Ξ (p ≫ M.φ) ∧
    FlopChain M.S X' Ξ (p ≫ M.φ) Y' (q ≫ N.φ ≫ ι.inv) σ' ∧ σ = τ'.trans (σ'.trans τ.symm)

/-- A link of type III: `X ⇢ Y'` is a composition of flops over `T`, `Y' → Y` is a divisorial contraction, and `S → T` is an extremal contraction.
```
X ⇢ Y'
φ ↓   ↓
S     Y
 ↘    ↓ ψ
      T
``` -/
def IsLinkIII (M N : MoriFibreSpace k) (σ : FF N.A.X ≃ₐ[k] FF M.A.X) : Prop :=
  ∃ (Ξ : Pair M.A.X) (s : M.S.toScheme ⟶ N.S.toScheme) (Y' : NormalVariety k)
    (q : Y'.toScheme ⟶ N.A.X.toScheme) (τ' : FF N.A.X ≃ₐ[k] FF Y') (σ' : FF Y' ≃ₐ[k] FF M.A.X),
    IsQFactorial Y' ∧ IsQFactorial M.S ∧ IsQFactorial N.S ∧ IsExtremalContr s ∧
    IsDivisorialContr q ∧ IsFieldPullback q τ' ∧ IsKlt Ξ ∧ IsNumTrivialOver Ξ (M.φ ≫ s) ∧
    FlopChain N.S M.A.X Ξ (M.φ ≫ s) Y' (q ≫ N.φ) σ' ∧ σ = τ'.trans σ'

/-- A link of type IVm: `X ⇢ Y` is a composition of flops over `R`, and `s : S → R` and `t : T → R` are extremal contractions of fibre type, so they are Mori fibre spaces in the sense of the diagram. The variety `R` is `ℚ`-factorial.
```
X ⇢ Y
φ ↓   ↓ ψ
S     T
 ↘   ↙
   R
``` -/
def IsLinkIVm (M N : MoriFibreSpace k) (σ : FF N.A.X ≃ₐ[k] FF M.A.X) : Prop :=
  ∃ (R : NormalVariety k) (Ξ : Pair M.A.X) (s : M.S.toScheme ⟶ R.toScheme) (t : N.S.toScheme ⟶ R.toScheme),
    IsQFactorial M.S ∧ IsQFactorial N.S ∧ IsQFactorial R ∧ IsExtremalContr s ∧ IsExtremalContr t ∧
    R.dim < M.S.dim ∧ R.dim < N.S.dim ∧ IsKlt Ξ ∧ IsNumTrivialOver Ξ (M.φ ≫ s) ∧
    FlopChain R M.A.X Ξ (M.φ ≫ s) N.A.X (N.φ ≫ t) σ

/-- A link of type IVs: the diagram of type IVm, where `s : S → R` and `t : T → R` are small birational extremal contractions, and `R` is not `ℚ`-factorial. -/
def IsLinkIVs (M N : MoriFibreSpace k) (σ : FF N.A.X ≃ₐ[k] FF M.A.X) : Prop :=
  ∃ (R : NormalVariety k) (Ξ : Pair M.A.X) (s : M.S.toScheme ⟶ R.toScheme) (t : N.S.toScheme ⟶ R.toScheme),
    IsQFactorial M.S ∧ IsQFactorial N.S ∧ ¬ IsQFactorial R ∧ IsExtremalContr s ∧ IsExtremalContr t ∧
    IsSmallHom s ∧ IsSmallHom t ∧ IsKlt Ξ ∧ IsNumTrivialOver Ξ (M.φ ≫ s) ∧
    FlopChain R M.A.X Ξ (M.φ ≫ s) N.A.X (N.φ ≫ t) σ

/-- `σ : k(Y) ≅ k(X)` is a Sarkisov link from the Mori fibre space `M` to `N`, of one of the types I, II, III, IVm and IVs (Hacon-McKernan, Section 1). -/
def IsSarkisovLink (M N : MoriFibreSpace k) (σ : FF N.A.X ≃ₐ[k] FF M.A.X) : Prop :=
  IsLinkI M N σ ∨ IsLinkII M N σ ∨ IsLinkIII M N σ ∨ IsLinkIVm M N σ ∨ IsLinkIVs M N σ

/-- `σ : k(Y) ≅ k(X)` is a composition of Sarkisov links from `M` to `N`. The last Mori fibre space of the sequence is isomorphic to `N`: there are isomorphisms `ξ : X ≅ Y` and `η : S ≅ T` over `k` with `ψ ∘ ξ = η ∘ φ`, and `σ` is the pullback along `ξ`. With no link, the sequence is this isomorphism. -/
inductive SarkisovChain : (M N : MoriFibreSpace k) → (FF N.A.X ≃ₐ[k] FF M.A.X) → Prop
  | iso (M N : MoriFibreSpace k) (ξ : M.A.X.toScheme ≅ N.A.X.toScheme) (η : M.S.toScheme ≅ N.S.toScheme)
      (σ : FF N.A.X ≃ₐ[k] FF M.A.X) :
      ξ.hom ≫ N.A.X.str = M.A.X.str → η.hom ≫ N.S.str = M.S.str → M.φ ≫ η.hom = ξ.hom ≫ N.φ →
      IsFieldPullback ξ.hom σ → SarkisovChain M N σ
  | link {M N O : MoriFibreSpace k} {σ : FF N.A.X ≃ₐ[k] FF M.A.X} {τ : FF O.A.X ≃ₐ[k] FF N.A.X} :
      IsSarkisovLink M N σ → SarkisovChain N O τ → SarkisovChain M O (τ.trans σ)

/-! ## Runs of the minimal model program -/

/-- A finite sequence of steps of the minimal model program from `A` to `B`, with the birational map `A ⇢ B` that it induces, given by `σ : k(B) ≅ k(A)`. At each step, the map is the birational map over the base of the step. -/
inductive IsMMPRun : (A B : PairModel k) → (FF B.X ≃ₐ[k] FF A.X) → Prop
  | refl (A : PairModel k) : IsMMPRun A A AlgEquiv.refl
  | step {A B C : PairModel k} (s : MMPStepData A B) {σ₁ : FF B.X ≃ₐ[k] FF A.X}
      {σ₂ : FF C.X ≃ₐ[k] FF B.X} :
      IsBirMapOver (X := A.X) (Y := B.X) s.f s.g σ₁ → IsMMPRun B C σ₂ → IsMMPRun A C (σ₂.trans σ₁)

end MinimalModel
