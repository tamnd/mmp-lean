/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import MinimalModel.Statements.Curves
import MinimalModel.Statements.Cohomology

/-!
# The Kawamata-Viehweg vanishing theorem of AxiomMath/MMP, in the vocabulary of `MinimalModel`

AxiomMath/MMP proves the Kawamata-Viehweg vanishing theorem in the form of KM98 Theorem 2.64 (`MMP.Mori.subsingleton_derivedCohomologyOverField_divisorialSheaf_neg`, in `MMP/AlgebraicGeometry/Vanishing/KawamataViehweg.lean` at commit `1f9ade3670`):

```
theorem MMP.Mori.subsingleton_derivedCohomologyOverField_divisorialSheaf_neg {k : Type}
    [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} (f : X ⟶ Spec (.of k))
    [IsProjectiveVariety k f] (hsm : IsSmoothScheme f) [IsLocallyNoetherian X] [IsNormal X]
    {n : ℕ} (hn : topologicalKrullDim X = n) (B : Divisor X) (M Δ : QDivisor X)
    (hMnef : M.IsNef k f) (hMbig : M.IsBig k f) (hΔ : Δ.IsSNC f)
    (hΔ0 : ∀ E, 0 ≤ Δ E) (hΔ1 : ∀ E, Δ E < 1)
    (hB : (Divisor.toQDivisor B).NumericallyEquivalent k f (M + Δ)) (i : ℤ) (hi : i < n) :
    Subsingleton (Stacks.Duality.derivedCohomologyOverField f
      ((DerivedCategory.singleFunctor X.Modules 0).obj (-B).divisorialSheaf) i)
```

This file states the same theorem with the definitions of `MinimalModel` (O-R2-3 of spec 04). It is the statement `MinimalModelBridge.KawamataViehwegSNC`. It is a `Prop`, not a theorem: the proof from the theorem of AxiomMath/MMP needs the dictionary below, and the build of the theorem of AxiomMath/MMP needs about 25,000 modules of AxiomMath/Stacks and AxiomMath/MMP, which the hosted runners of GitHub cannot build (see `bridge/README.md`).

## The dictionary

Each hypothesis of AxiomMath/MMP is matched with a hypothesis of `MinimalModelBridge.KawamataViehwegSNC`.

* `IsProjectiveVariety k f`, `IsSmoothScheme f`, `IsLocallyNoetherian X`, `IsNormal X`: `X` is a `MinimalModel.NormalVariety k` with `IsProjective X` and `X.IsSmooth`. The variety and the normality are compared in `MinimalModelBridge/Vocabulary/Variety.lean`. The projectivity of AxiomMath/Stacks (a closed immersion into a projective space) and the one of `MinimalModel` (proper with an ample Cartier divisor) are not compared yet.
* `topologicalKrullDim X = n`: `n = X.dim`, which is the same number, because the Krull dimension of a variety is finite.
* `B : Divisor X`, `M Δ : QDivisor X`: divisors of `MinimalModel` with coefficients in `ℤ` and `ℚ`. They are compared in `MinimalModelBridge/Vocabulary/PrimeDivisor.lean`.
* `M.IsNef k f`: `MinimalModel.IsNefRel M.ratToReal X.str`, that is `M · C ≥ 0` for each complete curve `C`. Not compared yet.
* `M.IsBig k f`: `MinimalModel.IsBig M.ratToReal`, ample plus effective up to `ℝ`-linear equivalence (Kodaira's lemma). Not compared yet.
* `Δ.IsSNC f`: the components of `Δ` have simple normal crossings at each point, `MinimalModel.IsSncAt`. Not compared yet.
* `0 ≤ Δ E` and `Δ E < 1`: the same conditions on the coefficients (`MinimalModelBridge.forall_divisorEquiv_iff`).
* `B ≡ M + Δ`: `MinimalModel.IsNumTrivialRel (B - (M + Δ)) X.str`. Not compared yet.
* The cohomology: AxiomMath/MMP takes the derived cohomology of the sheaf of `𝒪_X`-modules `𝒪_X(-B)` over `k`, and `MinimalModel` takes `CategoryTheory.Sheaf.H` of the abelian sheaf `MinimalModel.divisorialSheaf (-B) ⊤`. For `i < 0` the statement of AxiomMath/MMP is empty. For `i ≥ 0` the comparison needs that the two sheaves agree as abelian sheaves and that the cohomology of a sheaf of modules is the cohomology of the underlying abelian sheaf (Hartshorne III.2.6). Not compared yet.

The universe of AxiomMath/MMP is `0`, so the theorem of AxiomMath/MMP gives `KawamataViehwegSNC.{0}` only.
-/

universe u

open CategoryTheory

noncomputable section

namespace MinimalModelBridge

open MinimalModel

variable (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]

/-- Kawamata-Viehweg vanishing in the form of KM98 Theorem 2.64, the form that AxiomMath/MMP proves. Let `X` be a smooth projective variety of dimension `n` over `k`, and `B` a Weil divisor numerically equivalent to `M + Δ`, where `M` is a nef and big `ℚ`-divisor and `Δ` is a `ℚ`-divisor with simple normal crossing support and coefficients in `[0, 1)`. Then `H^i(X, 𝒪_X(-B)) = 0` for each `i < n`. -/
def KawamataViehwegSNC : Prop :=
  ∀ X : NormalVariety k, X.IsSmooth → IsProjective X →
    ∀ (B : Divisor ℤ X) (M Δ : Divisor ℚ X),
      IsNefRel M.ratToReal X.str → IsBig M.ratToReal →
      (∀ x : X.toScheme, IsSncAt {P : PrimeDivisor X | Δ P ≠ 0} x) →
      (∀ P, 0 ≤ Δ P) → (∀ P, Δ P < 1) →
      IsNumTrivialRel (B.toReal - Divisor.ratToReal (M + Δ)) X.str →
      ∀ i : ℕ, i < X.dim → Subsingleton (Sheaf.H (divisorialSheaf (-B) ⊤) i : Type u)

end MinimalModelBridge
