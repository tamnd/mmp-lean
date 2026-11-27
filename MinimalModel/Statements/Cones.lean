/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import MinimalModel.Statements.Basic

/-!
# Cones of divisors, Mori dream spaces and automorphisms

The vocabulary of the statements S37 (`FanoTypeMDS`, in `Models.lean`) and S55 (`ConeConj`, in `Boundedness.lean`).

## The choices

* The numerical class of an `ℝ`-divisor `D` is the function `C ↦ D · C` on the curves of `X` (`numClass`). It is the class in `N¹(X)` when `D` is `ℝ`-Cartier. The space `N¹(X)` is the span of the classes of the Cartier divisors (`N1`). It sits in `Curve X → ℝ`, with the product topology.
* A Mori dream space follows Hu and Keel, Mori dream spaces and GIT, Michigan Math. J. 48 (2000), arXiv:math/0004017, Definition 1.10 (`IsMoriDreamSpace`). The moving cone is the cone of the classes of the divisors with no stable base component (Hu-Keel, after Definition 1.2).
* A small `ℚ`-factorial modification `X ⇢ Y` is an identification `σ : k(Y) ≅ k(X)` that is an isomorphism in codimension one: each prime divisor of `X` is a prime divisor of `Y`, and the other way round (`IsIsoInCodimOne`). Along such a map, the pullback of a divisor of `Y` is its strict transform (`IsStrictPullback`).
* The cones of the cone conjecture follow Totaro, The cone conjecture for Calabi-Yau pairs in dimension two, Duke Math. J. 154 (2010), arXiv:0901.3361, Section 1, with the base `S` a point.
-/

universe u

namespace MinimalModel

open AlgebraicGeometry CategoryTheory

variable {k : Type u} [Field k] {X : NormalVariety k}

/-! ## Numerical classes -/

/-- The numerical class of an `ℝ`-divisor: its intersection numbers with the curves. -/
def numClass (I : IntersectionData X) (D : Divisor ℝ X) : Curve X → ℝ := fun C => I.dot D C

/-- `N¹(X)`: the real span of the numerical classes of the Cartier divisors. -/
def N1 (I : IntersectionData X) : Submodule ℝ (Curve X → ℝ) :=
  Submodule.span ℝ ((fun D : Divisor ℤ X => numClass I D.toReal) '' {D | IsCartier D})

/-- A rational polyhedral cone in `N¹(X)`: the convex cone spanned by the classes of finitely many Cartier divisors (Totaro, Section 1). -/
def IsRatPolyCone (I : IntersectionData X) (F : Set (Curve X → ℝ)) : Prop :=
  ∃ (N : ℕ) (D : Fin N → Divisor ℤ X), (∀ j, IsCartier (D j)) ∧
    F = {z | ∃ r : Fin N → ℝ, (∀ j, 0 ≤ r j) ∧ z = ∑ j, r j • numClass I (D j).toReal}

/-- The interior of a set of classes, relative to `N¹(X)`. -/
def interiorN1 (I : IntersectionData X) (F : Set (Curve X → ℝ)) : Set (Curve X → ℝ) :=
  {z | z ∈ N1 I ∧ ∃ U : Set (Curve X → ℝ), IsOpen U ∧ z ∈ U ∧ U ∩ (N1 I : Set (Curve X → ℝ)) ⊆ F}

/-! ## Mori dream spaces -/

/-- A Weil divisor with no stable base component: for each prime divisor `P`, some positive multiple `m D` is linearly equivalent to an effective divisor that does not contain `P`. -/
def NoStableBaseComponent (D : Divisor ℤ X) : Prop :=
  ∀ P : PrimeDivisor X, ∃ m : ℕ, 0 < m ∧ ∃ (φ : FF X) (E : Divisor ℤ X), 0 ≤ E ∧
    IsDivOn (E - (m : ℤ) • D) φ Set.univ ∧ E P = 0

/-- The moving cone `Mov(X)` of Hu and Keel: the convex cone spanned by the classes of the Weil divisors with no stable base component. -/
def movingCone (I : IntersectionData X) : Set (Curve X → ℝ) :=
  {z | ∃ (N : ℕ) (r : Fin N → ℝ) (D : Fin N → Divisor ℤ X),
    (∀ j, 0 ≤ r j ∧ NoStableBaseComponent (D j)) ∧ z = ∑ j, r j • numClass I (D j).toReal}

/-- Hu-Keel Definition 1.10(2): the nef cone is the convex cone spanned by the classes of finitely many semiample Cartier divisors. -/
def NefConeFinGen (I : IntersectionData X) : Prop :=
  ∃ (N : ℕ) (S : Fin N → Divisor ℤ X), (∀ j, IsCartier (S j) ∧ IsSemiample (S j).toReal) ∧
    ∀ D : Divisor ℝ X, IsRCartier D →
      (IsNef I D ↔ ∃ r : Fin N → ℝ, (∀ j, 0 ≤ r j) ∧ numClass I D = ∑ j, r j • numClass I (S j).toReal)

/-- The birational map `X ⇢ Y` given by `σ : k(Y) ≅ k(X)` is an isomorphism in codimension one: each prime divisor of `X` is a prime divisor of `Y`, and each prime divisor of `Y` is one of `X`. -/
def IsIsoInCodimOne {Y : NormalVariety k} (σ : FF Y ≃ₐ[k] FF X) : Prop :=
  (∀ P : PrimeDivisor X, ∃ Q, SameDivisor σ P Q) ∧ ∀ Q : PrimeDivisor Y, ∃ P, SameDivisor σ P Q

/-- `D` on `X` is the pullback of `D'` on `Y` along a map `X ⇢ Y` that is an isomorphism in codimension one: the two divisors have the same coefficient at each prime divisor. -/
def IsStrictPullback {Y : NormalVariety k} (σ : FF Y ≃ₐ[k] FF X) (D' : Divisor ℝ Y) (D : Divisor ℝ X) :
    Prop :=
  ∀ P Q, SameDivisor σ P Q → D P = D' Q

/-- A Mori dream space (Hu-Keel Definition 1.10). The projective variety `X`, with its intersection numbers `I`, is a Mori dream space if
1. `X` is `ℚ`-factorial and `Pic(X)_ℚ = N¹(X)`: a numerically trivial Cartier divisor has a multiple that is principal;
2. the nef cone is spanned by the classes of finitely many semiample Cartier divisors (`NefConeFinGen`);
3. there are finitely many small `ℚ`-factorial modifications `fᵢ : X ⇢ Yᵢ`, with `Yᵢ` projective, such that each `Yᵢ` satisfies 2 and `Mov(X)` is the union of the cones `fᵢ^* Nef(Yᵢ)`.

Hu and Keel write `fᵢ_*`; on classes of divisors it is the pullback along `fᵢ`, which this definition uses, because the map is an isomorphism in codimension one. -/
def IsMoriDreamSpace (X : NormalVariety k) (I : IntersectionData X) : Prop :=
  IsQFactorial X ∧
  (∀ D : Divisor ℤ X, IsCartier D → (∀ C, I.dot D.toReal C = 0) →
    ∃ m : ℕ, 0 < m ∧ IsPrincipal ((m : ℤ) • D)) ∧
  NefConeFinGen I ∧
  ∃ (N : ℕ) (Y : Fin N → NormalVariety k) (J : ∀ i, IntersectionData (Y i))
    (σ : ∀ i, FF (Y i) ≃ₐ[k] FF X),
    (∀ i, IsProjective (Y i) ∧ IsQFactorial (Y i) ∧ IsIsoInCodimOne (σ i) ∧ NefConeFinGen (J i)) ∧
    ∀ z, z ∈ movingCone I ↔ ∃ i, ∃ (D' : Divisor ℝ (Y i)) (D : Divisor ℝ X),
      IsRCartier D' ∧ IsNef (J i) D' ∧ IsStrictPullback (σ i) D' D ∧ z = numClass I D

/-! ## The cones of the cone conjecture -/

/-- A Cartier divisor that is effective in the sense of Totaro: it has a nonzero section, that is it is linearly equivalent to an effective divisor. -/
def HasSection (D : Divisor ℤ X) : Prop :=
  ∃ (φ : FF X) (E : Divisor ℤ X), 0 ≤ E ∧ IsDivOn (E - D) φ Set.univ

/-- A movable Cartier divisor in the sense of Totaro: the base locus of `|D|` has codimension at least two, that is for each prime divisor `P` some member of `|D|` does not contain `P`. -/
def IsMovable (D : Divisor ℤ X) : Prop :=
  IsCartier D ∧ ∀ P : PrimeDivisor X, ∃ (φ : FF X) (E : Divisor ℤ X), 0 ≤ E ∧
    IsDivOn (E - D) φ Set.univ ∧ E P = 0

/-- The effective cone `Bᵉ(X)`: the convex cone, not closed, spanned by the classes of the Cartier divisors with a nonzero section. -/
def effCone (I : IntersectionData X) : Set (Curve X → ℝ) :=
  {z | ∃ (N : ℕ) (r : Fin N → ℝ) (D : Fin N → Divisor ℤ X),
    (∀ j, 0 ≤ r j ∧ IsCartier (D j) ∧ HasSection (D j)) ∧ z = ∑ j, r j • numClass I (D j).toReal}

/-- The nef cone `A(X)`: the classes of the nef `ℝ`-Cartier divisors. This is the closed convex cone that the nef Cartier divisors span, as in Totaro, because the ample classes are dense in it. -/
def nefCone (I : IntersectionData X) : Set (Curve X → ℝ) :=
  {z | ∃ D : Divisor ℝ X, IsRCartier D ∧ IsNef I D ∧ z = numClass I D}

/-- The closed movable cone `M(X)`: the closure of the convex cone spanned by the classes of the movable Cartier divisors. -/
def closedMovCone (I : IntersectionData X) : Set (Curve X → ℝ) :=
  closure {z | ∃ (N : ℕ) (r : Fin N → ℝ) (D : Fin N → Divisor ℤ X),
    (∀ j, 0 ≤ r j ∧ IsMovable (D j)) ∧ z = ∑ j, r j • numClass I (D j).toReal}

/-- `Aᵉ(X) = A(X) ∩ Bᵉ(X)`, the effective nef cone. -/
def effNefCone (I : IntersectionData X) : Set (Curve X → ℝ) := nefCone I ∩ effCone I

/-- `Mᵉ(X) = M(X) ∩ Bᵉ(X)`, the effective movable cone. -/
def effMovCone (I : IntersectionData X) : Set (Curve X → ℝ) := closedMovCone I ∩ effCone I

/-- `D'` is the pullback `g^* D` along an automorphism `g` of `X`: the coefficient of `D'` at `P` is the coefficient of `D` at `g(P)`. -/
def IsAutPullback (g : X.toScheme ≅ X.toScheme) (D D' : Divisor ℝ X) : Prop :=
  ∀ P Q : PrimeDivisor X, g.hom.base P.1 = Q.1 → D' P = D Q

/-- An element of `Aut(X, Δ)`: an automorphism of `X` over `k` that maps `Δ` to itself. -/
def IsAutOf (P : Pair X) (g : X.toScheme ≅ X.toScheme) : Prop :=
  g.hom ≫ X.str = X.str ∧ IsAutPullback g P.Δ P.Δ

/-- The cone `g^* F`: the classes `g^* D` for the `ℝ`-Cartier divisors `D` with class in `F`. -/
def autPull (I : IntersectionData X) (g : X.toScheme ≅ X.toScheme) (F : Set (Curve X → ℝ)) :
    Set (Curve X → ℝ) :=
  {z | ∃ D D' : Divisor ℝ X, IsRCartier D ∧ numClass I D ∈ F ∧ IsAutPullback g D D' ∧
    z = numClass I D'}

/-- `g^* = 1` on `N¹(X)`. -/
def AutActsTrivially (I : IntersectionData X) (g : X.toScheme ≅ X.toScheme) : Prop :=
  ∀ D D' : Divisor ℝ X, IsRCartier D → IsAutPullback g D D' → numClass I D' = numClass I D

/-- An element of `PsAut(X, Δ)`: a pseudo-automorphism of `X`, that is a birational map `X ⇢ X` that is an isomorphism in codimension one, which maps `Δ` to itself. -/
def IsPsAutOf (P : Pair X) (σ : FF X ≃ₐ[k] FF X) : Prop :=
  IsIsoInCodimOne σ ∧ IsStrictPullback σ P.Δ P.Δ

/-- The cone `σ^* F` for a pseudo-automorphism `σ`. -/
def psAutPull (I : IntersectionData X) (σ : FF X ≃ₐ[k] FF X) (F : Set (Curve X → ℝ)) :
    Set (Curve X → ℝ) :=
  {z | ∃ D D' : Divisor ℝ X, IsRCartier D ∧ numClass I D ∈ F ∧ IsStrictPullback σ D D' ∧
    z = numClass I D'}

/-- `σ^* = 1` on `N¹(X)`. -/
def PsAutActsTrivially (I : IntersectionData X) (σ : FF X ≃ₐ[k] FF X) : Prop :=
  ∀ D D' : Divisor ℝ X, IsRCartier D → IsStrictPullback σ D D' → numClass I D' = numClass I D

end MinimalModel
