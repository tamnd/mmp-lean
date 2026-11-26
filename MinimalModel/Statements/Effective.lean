/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import MinimalModel.Statements.Basic

/-!
# Family G: effective results

The statements of family G of spec 06.2.2 that are planned at S1 and need no new vocabulary: Fujita's freeness conjecture. S57 needs abelian varieties, which are not in `Basic.lean` yet.
-/

universe u

namespace MinimalModel

variable (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]

/-- S56, Fujita's freeness conjecture. Let `X` be a smooth projective variety, `K` a canonical divisor of `X` and `L` an ample Cartier divisor. Then `K + m L` is free for each `m ≥ dim X + 1`. It is known in dimension at most 5. OpenAI 038 claims the full conjecture (claim C8 of spec 01.3). The class stays `open` until experts accept a proof. -/
def FujitaFreeness : Prop :=
  ∀ X : NormalVariety k, X.IsSmooth → IsProjective X → ∀ (K : CanonicalDivisor X) (L : Divisor ℤ X),
    IsRelAmple L X.str → ∀ m : ℕ, X.dim + 1 ≤ m → IsFree (K.K + (m : ℤ) • L)

end MinimalModel
