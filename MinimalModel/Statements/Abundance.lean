/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import MinimalModel.Statements.BasicRelative

/-!
# Family E: abundance and non-vanishing

The statements of family E of spec 06.2.2 that are planned at S0, S1 and S2. The statements S45 and S46 use numerical equivalence and the Kodaira dimension of `BasicRelative.lean`.
-/

universe u

namespace MinimalModel

open AlgebraicGeometry CategoryTheory

variable (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]

/-- S40, the abundance conjecture in dimension `n` (KM98 3.12 in spec 03). For each projective lc pair of dimension `n`, if `K + Δ` is nef, then it is semiample. This is open for `n ≥ 4`. -/
def Abundance (n : ℕ) : Prop :=
  ∀ A : PairModel k, A.X.dim = n → IsLc A.P → IsNef A.I A.P.KΔ → IsSemiample A.P.KΔ

/-- S41, the non-vanishing conjecture in dimension `n` (spec 03). For each projective lc pair of dimension `n`, if `K + Δ` is pseudo-effective, then it is `ℝ`-linearly equivalent to an effective divisor. This is open for `n ≥ 4`. -/
def NonVanishing (n : ℕ) : Prop :=
  ∀ A : PairModel k, A.X.dim = n → IsLc A.P → IsPseudoEffective A.P.KΔ → IsREffective A.P.KΔ

/-- S42, abundance for a big log canonical divisor (the base point free theorem with `D = K + Δ`, KM98 Theorem 3.3; for a boundary with real coefficients, BCHM). For each projective klt pair such that `K + Δ` is nef and big, `K + Δ` is semiample. -/
def AbundanceBig : Prop :=
  ∀ A : PairModel k, IsKlt A.P → IsNef A.I A.P.KΔ → IsBig A.P.KΔ → IsSemiample A.P.KΔ

/-- S44, the reduction of Liu and Xu (arXiv:2505.05250). Fix `d`. Non-vanishing in dimension `d` (S41) gives abundance for the projective lc pairs of dimension `d` whose numerical dimension is at most one: if `K + Δ` is nef and `ν(K + Δ) ≤ 1`, then `K + Δ` is semiample. The numerical dimension is Nakayama's `κ_σ` (spec 06.5, risk 4). For a nef divisor it is the usual numerical dimension. The class is reduction. -/
def LiuXuReduction (d : ℕ) : Prop :=
  NonVanishing k d → ∀ A : PairModel k, A.X.dim = d → IsLc A.P → IsNef A.I A.P.KΔ →
    numericalDim A.P.KΔ ≤ 1 → IsSemiample A.P.KΔ

/-- S43, abundance for numerical dimension zero (Nakayama, Zariski-decomposition and abundance, MSJ Memoirs 14 (2004), Theorem V.4.9, for klt pairs with rational coefficients; Gongyo, On the minimal model theory for dlt pairs of numerical log Kodaira dimension zero, Math. Res. Lett. 18 (2011), Theorem 1.2, for lc pairs with real coefficients). For each projective lc pair, if `K + Δ` is nef and its numerical dimension is `0`, then `K + Δ` is semiample. For a nef divisor, numerical dimension `0` says that the divisor is numerically trivial, and the conclusion of the sources is `K + Δ ∼_ℝ 0`, which is semiample. The numerical dimension is Nakayama's `κ_σ` (spec 06.5, risk 4). -/
def AbundanceNuZero : Prop :=
  ∀ A : PairModel k, IsLc A.P → IsNef A.I A.P.KΔ → numericalDim A.P.KΔ = 0 → IsSemiample A.P.KΔ

/-- S45, the generalised abundance conjecture in dimension `n` (Lazić and Peternell, On generalised abundance, I, Publ. RIMS 56 (2020), Conjecture 1.1). Let `(X, Δ)` be a projective klt pair of dimension `n` with `K + Δ` pseudo-effective, and let `L` be a nef `ℝ`-Cartier divisor such that `K + Δ + L` is nef. Then `K + Δ + L` is numerically equivalent to a semiample `ℝ`-divisor. With `L = 0` this is the abundance conjecture for klt pairs, up to numerical equivalence. It is open for `n ≥ 3`. -/
def GeneralizedAbundance (n : ℕ) : Prop :=
  ∀ A : PairModel k, A.X.dim = n → IsKlt A.P → IsPseudoEffective A.P.KΔ →
    ∀ L : Divisor ℝ A.X, IsRCartier L → IsNef A.I L → IsNef A.I (A.P.KΔ + L) →
      ∃ S : Divisor ℝ A.X, IsSemiample S ∧ NumEquiv A.I (A.P.KΔ + L) S

/-- S46, the Iitaka conjecture `C_{n,m}` (Iitaka, Genera and classification of algebraic varieties, 1972; the form of spec 03.8). Let `f : X → Y` be an algebraic fibre space of smooth projective varieties, with `dim X = n` and `dim Y = m`: a projective morphism over `k` with `f_* 𝒪_X = 𝒪_Y`. Let `F` be a general fibre. Then `κ(X) ≥ κ(F) + κ(Y)`.

"General fibre" is written with an open set: there is a nonempty open set `V` of `Y` such that the inequality holds for the fibre over each closed point of `V`. The fibre `f⁻¹(y)` is the scheme `f.fiber y` of Mathlib. Over a general closed point it is a smooth projective variety, and the statement takes each `F : NormalVariety k` with an isomorphism to the fibre over `k`. The Kodaira dimensions are those of canonical divisors, and `⊥` is `-∞`, so the inequality holds when `κ(F) = -∞`. It is known for `n ≤ 6` (Birkar 2009) and in other cases, and open in general. -/
def IitakaConj (n m : ℕ) : Prop :=
  ∀ (X Y : NormalVariety k) (f : X.toScheme ⟶ Y.toScheme), X.IsSmooth → Y.IsSmooth →
    IsProjective X → IsProjective Y → X.dim = n → Y.dim = m → f ≫ Y.str = X.str →
    IsContraction f →
    ∃ V : Y.toScheme.Opens, (V : Set Y.toScheme).Nonempty ∧
      ∀ y ∈ V, IsClosed ({y} : Set Y.toScheme) →
        ∀ (F : NormalVariety k) (e : F.toScheme ≅ f.fiber y), e.hom ≫ f.fiberι y ≫ X.str = F.str →
          ∀ (KX : CanonicalDivisor X) (KY : CanonicalDivisor Y) (KF : CanonicalDivisor F),
            kodairaDim KF + kodairaDim KY ≤ kodairaDim KX

end MinimalModel
