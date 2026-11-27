/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import MinimalModel.Statements.Basic
import MinimalModel.Statements.Curves
import MinimalModel.Statements.Cohomology

/-!
# Family A: foundations

The statements of family A of spec 06.2.2: S01 to S09. The statements S01, S02, S03, S06 and S09 use the vocabulary of `Curves.lean` and `Cohomology.lean`.
-/

universe u

open AlgebraicGeometry CategoryTheory

namespace MinimalModel

section Kleiman

variable (k : Type u) [Field k] [IsAlgClosed k]

/-- S01, Kleiman's criterion (KM98, Chapter 1, Theorem 1.18). Let `X` be a projective variety and `D` an `ℝ`-Cartier divisor on `X`. Then `D` is ample if and only if `D · z > 0` for each nonzero class `z` of the closed cone of curves `NE(X)`. The criterion holds in each characteristic, so the statement does not assume `CharZero k`. The intersection numbers are a structure `IntersectionData X`, which has at most one value on each `ℝ`-Cartier divisor. So the statement quantifies over it. -/
def KleimanCriterion : Prop :=
  ∀ X : NormalVariety k, IsProjective X → ∀ (I : IntersectionData X) (D : Divisor ℝ X)
    (hD : IsRCartier D), IsAmple D ↔ ∀ z ∈ I.coneOfCurves, z ≠ 0 → 0 < z ⟨D, hD⟩

end Kleiman

variable (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]

/-- S04, the cone theorem for projective klt pairs (KM98 Theorem 3.7, parts 1 and 2, without the rationality and the length of the curves). For each projective klt pair `(X, Δ)` over `k`, the closed cone of curves is `NE(X)_{K+Δ ≥ 0}` plus countably many extremal rays spanned by `(K + Δ)`-negative curves, and these rays are discrete away from `K + Δ = 0`. -/
def ConeTheoremKlt : Prop :=
  ∀ A : PairModel k, IsKlt A.P → ConeDecomposition A

/-- S05, the cone theorem for projective lc pairs (Fujino 2011, the cone theorem for lc pairs). This is the conclusion of S04 for each projective lc pair `(X, Δ)` over `k`: the closed cone of curves is `NE(X)_{K+Δ ≥ 0}` plus countably many extremal rays spanned by `(K + Δ)`-negative curves, and these rays are discrete away from `K + Δ = 0`. -/
def ConeTheoremLc : Prop :=
  ∀ A : PairModel k, IsLc A.P → ConeDecomposition A

/-- S07, the rationality theorem (KM98 Theorem 3.5). Let `(X, Δ)` be a projective klt pair such that `K + Δ` is not nef. Let `a > 0` be an integer such that `a (K + Δ)` is Cartier, and let `H` be an ample Cartier divisor. Let `r` be the nef threshold, the largest `t` such that `H + t (K + Δ)` is nef. Then `r / a = u / v` for natural numbers `u` and `v` with `0 < v ≤ a (dim X + 1)`. This statement takes `H` ample, as the node of the map does. The `reader` role compares the hypothesis on `H` with KM98 before F5. -/
def RationalityTheorem : Prop :=
  ∀ A : PairModel k, IsKlt A.P → ¬ IsNef A.I A.P.KΔ → ∀ a : ℕ, 0 < a →
    (∃ E : Divisor ℤ A.X, IsCartier E ∧ (a : ℝ) • A.P.KΔ = E.toReal) →
    ∀ H : Divisor ℤ A.X, IsRelAmple H A.X.str →
      ∃ u v : ℕ, 0 < v ∧ v ≤ a * (A.X.dim + 1) ∧
        nefThreshold A.I H.toReal A.P.KΔ / a = (u : ℝ) / v

/-- S08, the base point free theorem (KM98 Theorem 3.3). Let `(X, Δ)` be a projective klt pair, and let `D` be a nef Cartier divisor such that `a D - (K + Δ)` is nef and big for some real `a > 0`. Then the linear system `|b D|` is free for each large `b`. So `D` is semiample. KM98 takes a boundary with rational coefficients. The case of real coefficients follows from it by a small change of `Δ`. -/
def BasepointFree : Prop :=
  ∀ A : PairModel k, IsKlt A.P → ∀ D : Divisor ℤ A.X, IsCartier D → IsNef A.I D.toReal →
    ∀ a : ℝ, 0 < a → IsNef A.I (a • D.toReal - A.P.KΔ) → IsBig (a • D.toReal - A.P.KΔ) →
      ∃ b₀ : ℕ, ∀ b : ℕ, b₀ ≤ b → IsFree ((b : ℤ) • D)

/-- S02, Kawamata-Viehweg vanishing (KM98 Theorem 2.70). Let `(X, Δ)` be a klt pair with `Δ` a `ℚ`-divisor, and `π : X → U` a projective morphism to a scheme `U` of finite type over `k`. Let `N` be a `ℚ`-Cartier Weil divisor and `M` a `ℚ`-Cartier `ℚ`-divisor that is `π`-nef and `π`-big, with `N ≡_π K + Δ + M`. Then `R^i π_* 𝒪_X(N) = 0` for each `i > 0`. The relative notions are the ones of `Curves.lean`: they use the curves that `π` contracts, which are complete. The higher direct images are the ones of `Cohomology.lean`. A `π`-big divisor here is an `f`-ample divisor plus an effective one, which needs `π` projective. -/
def KawamataViehweg : Prop :=
  ∀ (X : NormalVariety k) (P : Pair X), IsKlt P → P.IsRationalBoundary →
    ∀ (U : Scheme.{u}) (g : U ⟶ Spec (CommRingCat.of k)) (π : X.toScheme ⟶ U),
      LocallyOfFiniteType g → π ≫ g = X.str → IsProjectiveHom (X := X) π →
      ∀ N : Divisor ℤ X, IsQCartier N.toRat → ∀ M : Divisor ℚ X, IsQCartier M →
        IsNefRel M.ratToReal π → IsBigRel M.ratToReal π →
        IsNumTrivialRel (N.toReal - P.KΔ - M.ratToReal) π → HigherDirectImagesVanish N π

/-- S06, the contraction theorem (KM98 Theorem 3.7, parts 3 and 4). Let `(X, Δ)` be a projective klt pair and `F` a `(K + Δ)`-negative extremal face of `NE(X)`. Then there is a morphism `cont_F : X → Z` over `k` onto a projective normal variety `Z` with `(cont_F)_* 𝒪_X = 𝒪_Z` that contracts a curve exactly when its class is in `F`. It is unique up to a unique isomorphism of `Z`. Each Cartier divisor `L` with `L · C = 0` for the curves `C` with class in `F` is trivial on the inverse image of an open neighbourhood of each point of `Z`. Because `(cont_F)_* 𝒪_X = 𝒪_Z`, this is the same as `𝒪_X(L) ≅ cont_F^* L_Z` for a line bundle `L_Z` on `Z`. -/
def ContractionTheorem : Prop :=
  ∀ A : PairModel k, IsKlt A.P → ∀ F : ExtremalFace A.I, F.IsNegative A.P.KΔR →
    ∃ (Z : NormalVariety k) (f : A.X.toScheme ⟶ Z.toScheme), IsContractionOfFace A F Z f ∧
      (∀ (Z' : NormalVariety k) (f' : A.X.toScheme ⟶ Z'.toScheme), IsContractionOfFace A F Z' f' →
        ∃ e : Z.toScheme ≅ Z'.toScheme, f ≫ e.hom = f') ∧
      ∀ L : Divisor ℤ A.X, IsCartier L →
        (∀ C : Curve A.X, A.I.curveClass C ∈ F.carrier → A.I.dot L.toReal C = 0) →
        ∀ z : Z.toScheme, ∃ V : Z.toScheme.Opens, z ∈ V ∧
          ∃ φ : FF A.X, IsDivOn L φ (f ⁻¹ᵁ V : Set A.X.toScheme)

/-- S09, the length of extremal rays (KM98 Theorem 3.7(1), after Kawamata 1991). Let `(X, Δ)` be a projective klt pair. Each `(K + Δ)`-negative extremal ray `R` of `NE(X)` is spanned by the class of a rational curve `C` with `0 < -(K + Δ) · C ≤ 2 dim X`. -/
def LengthOfExtremalRays : Prop :=
  ∀ A : PairModel k, IsKlt A.P → ∀ R : ExtremalRay A.I, R.generator A.P.KΔR < 0 →
    ∃ C : Curve A.X, C.IsRational ∧ ray R.generator = ray (A.I.curveClass C) ∧
      0 < -A.I.dot A.P.KΔ C ∧ -A.I.dot A.P.KΔ C ≤ 2 * (A.X.dim : ℝ)

/-- Kollár's injectivity theorem (J. Kollár, Higher direct images of dualizing sheaves I, Ann. of Math. 123 (1986), Theorem 2.2, in the form of O. Fujino, A transcendental approach to Kollár's injectivity theorem, arXiv:0704.0073, Theorem 1.1). Let `X` be a smooth projective variety and `L` a semiample Cartier divisor on `X`. Let `s` be a nonzero section of `𝒪_X(n L)` for some `n > 0`. Then for each `q ≥ 0` and each `m ≥ 1` the map `× s : H^q(X, 𝒪_X(K + m L)) → H^q(X, 𝒪_X(K + (m + n) L))` is injective.

The section `s` is a rational function `φ ≠ 0` with `n L + div φ ≥ 0`, and `× s` is multiplication by `φ` (`mulSheafHom`). The target is written `𝒪_X((K + m L) + n L)`. A line bundle on `X` is `𝒪_X(L)` for a Cartier divisor `L`, because `X` is integral, and `L` is semiample when some multiple is free. -/
def KollarInjectivity : Prop :=
  ∀ X : NormalVariety k, X.IsSmooth → IsProjective X → ∀ (K : CanonicalDivisor X) (L : Divisor ℤ X),
    IsCartier L → (∃ a : ℕ, 0 < a ∧ IsFree ((a : ℤ) • L)) → ∀ n : ℕ, 0 < n →
    ∀ (φ : FF X) (hφ : φ ≠ 0)
      (hs : ∀ P : PrimeDivisor X, P.1 ∈ (⊤ : X.toScheme.Opens) → 0 ≤ ((n : ℤ) • L) P + ordAt φ P),
    ∀ m : ℕ, 0 < m → ∀ q : ℕ,
      Function.Injective (cohomMap (mulSheafHom (D := K.K + (m : ℤ) • L) hφ hs) q)

/-- Kollár's torsion-freeness theorem (J. Kollár, Higher direct images of dualizing sheaves I, Ann. of Math. 123 (1986), Theorem 2.1(i); in the form of O. Fujino, Fundamental theorems for the log minimal model program, Publ. RIMS 47 (2011), arXiv:0909.4445, 3.4(i), which cites Kollár, Shafarevich maps and automorphic forms, 10.15; here with `M = 0`). Let `X` be a smooth projective variety, `Δ` an effective `ℚ`-divisor on `X` with simple normal crossing support and `⌊Δ⌋ = 0`, and `f : X → Y` a surjective morphism onto a projective variety. Let `D` be a Cartier divisor with `D ∼_ℚ K + Δ`. Then `R^i f_* 𝒪_X(D)` is torsion-free for each `i ≥ 0`. The case `Δ = 0`, `D = K` is Kollár's theorem that `R^i f_* ω_X` is torsion-free.

Torsion-free is read on the affine open sets `W` of `Y`, where `R^i f_* 𝒪_X(D)` is `H^i(f⁻¹ W, 𝒪_X(D))`, as in `HigherDirectImagesVanish`: multiplication by each nonzero `a ∈ Γ(W, 𝒪_Y)` is injective on it. Multiplication by `a` is multiplication by its pullback `f^* a`, a rational function with `div (f^* a) ≥ 0` on `f⁻¹ W`, so the map goes to `𝒪_X(D + 0)`. The statement takes as hypotheses that `f^* a ≠ 0` and `div (f^* a) ≥ 0` on `f⁻¹ W`. Both always hold, because `f` is dominant and `f^* a` is regular on `f⁻¹ W`.

What the Lean form changes:
* The variety `Y` is normal. This is no loss: `f` factors through the normalization `ν : Yⁿ → Y`, which is finite, so `R^i f_* = ν_* R^i g_*`, and `ν_*` keeps a sheaf torsion-free.
* Fujino's 3.4(i) allows `D - (K + Δ) ∼_ℚ f^* M` for a `ℚ`-Cartier divisor `M` on `Y`. This statement takes `M = 0`, because the tree has no pullback of divisors along a morphism that is not birational. -/
def KollarTorsionFreeness : Prop :=
  ∀ (X Y : NormalVariety k) (f : X.toScheme ⟶ Y.toScheme), f ≫ Y.str = X.str →
    X.IsSmooth → IsProjective X → IsProjective Y → Function.Surjective f.base →
    ∀ (K : CanonicalDivisor X) (Δ : Divisor ℚ X) (D : Divisor ℤ X), 0 ≤ Δ → (∀ Q, Δ Q < 1) →
      (∀ x : X.toScheme, IsSncAt {Q | Δ Q ≠ 0} x) → IsCartier D →
      QLinEquiv D.toRat (K.K.toRat + Δ) →
    ∀ W : Y.toScheme.Opens, IsAffineOpen W → ∀ hX : genericPoint X.toScheme ∈ f ⁻¹ᵁ W,
    ∀ a : Γ(Y.toScheme, W), a ≠ 0 →
      ∀ (ha : (f.app W ≫ X.toScheme.presheaf.germ (f ⁻¹ᵁ W) _ hX).hom a ≠ 0)
        (hreg : ∀ P : PrimeDivisor X, P.1 ∈ f ⁻¹ᵁ W →
          0 ≤ (0 : Divisor ℤ X) P + ordAt ((f.app W ≫ X.toScheme.presheaf.germ (f ⁻¹ᵁ W) _ hX).hom a) P),
      ∀ i : ℕ, Function.Injective (cohomMap (mulSheafHom (D := D) ha hreg) i)

/-- S03, Kollár's injectivity and torsion-freeness theorems (Kollár 1986, Theorems 2.1 and 2.2): the conjunction of `KollarInjectivity` and `KollarTorsionFreeness`. The torsion-freeness is the form of Fujino 3.4(i) with `M = 0`, which the lc program uses. -/
def KollarTorsionFree : Prop :=
  KollarInjectivity k ∧ KollarTorsionFreeness k

end MinimalModel
