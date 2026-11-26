/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import MinimalModel.Statements.Basic

/-!
# Family G: effective results

The statements of family G of spec 06.2.2 that are planned at S1: Fujita's freeness conjecture (S56) and the failure of effective non-vanishing in dimension 4 (S57). The statement S57 is the negation of a conjecture, so it needs no abelian varieties: the witness of the source is in the docstring, not in the statement.
-/

universe u

namespace MinimalModel

variable (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]

/-- S56, Fujita's freeness conjecture. Let `X` be a smooth projective variety, `K` a canonical divisor of `X` and `L` an ample Cartier divisor. Then `K + m L` is free for each `m ≥ dim X + 1`. It is known in dimension at most 5. OpenAI 038 claims the full conjecture (claim C8 of spec 01.3). The class stays `open` until experts accept a proof. -/
def FujitaFreeness : Prop :=
  ∀ X : NormalVariety k, X.IsSmooth → IsProjective X → ∀ (K : CanonicalDivisor X) (L : Divisor ℤ X),
    IsRelAmple L X.str → ∀ m : ℕ, X.dim + 1 ≤ m → IsFree (K.K + (m : ℤ) • L)

/-- The Ambro-Kawamata effective non-vanishing conjecture in dimension `n` (Kawamata, "On effective non-vanishing and base-point-freeness", Asian J. Math. 4 (2000), Conjecture 2.1; the `reader` role checks the number). Let `(X, Δ)` be a klt pair of dimension `n` and `D` a nef Cartier divisor such that `D - (K + Δ)` is nef and big. Then `H⁰(X, 𝒪_X(D)) ≠ 0`. The source takes `X` complete. This form takes `X` projective, so its negation is stronger than the negation of the source. -/
def EffectiveNonVanishing (n : ℕ) : Prop :=
  ∀ A : PairModel k, A.X.dim = n → IsKlt A.P → ∀ D : Divisor ℤ A.X, IsCartier D →
    IsNef A.I D.toReal → IsNef A.I (D.toReal - A.P.KΔ) → IsBig (D.toReal - A.P.KΔ) →
      sections D ≠ ⊥

/-- S57, effective non-vanishing fails in dimension 4 (Ajit, arXiv:2610.09270 v2, the counterexamples in dimension 4; claim C14 of spec 01.3). The statement is the negation of `EffectiveNonVanishing k 4`. The witness of the source is `X = E⁴/⟨ρ⟩`, with `E` the Fermat cubic curve and `ρ` an automorphism of order 3: `X` is terminal with `3 K_X ∼ 0`, and an ample Cartier divisor `D` on `X` has `D⁴ = 72` and `H⁰(X, D) = 0`. With `Δ = 0`, the divisor `D - K_X` is ample, so nef and big. The class of the statement is claimed until a referee accepts the source (spec 06.2.1). No statement of the tree takes it as a hypothesis. -/
def NotEffectiveNonVanishing4 : Prop :=
  ¬ EffectiveNonVanishing k 4

end MinimalModel
