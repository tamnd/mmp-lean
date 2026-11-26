/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import MinimalModel.Statements.Basic

/-!
# Pairs with an exceptionally non-canonical singularity

This file adds to `MinimalModel/Statements/Basic.lean` the global minimal log discrepancy and the enc pairs of Han and Liu. The statement S52 of spec 06.2.2 uses them.

## The source

J. Han and J. Liu, "On termination of flips and exceptionally non-canonical singularities", Geom. Topol. 29 (2025), arXiv:2209.13122, Definition 3.8(1): "(X, B) is enc if mld(X, B) < 1, and the set {E | E is exceptional over X, a(E, X, B) ≤ 1} contains a unique element." Here `mld(X, B)` is the global minimal log discrepancy, the infimum of `a(E, X, B)` over the prime divisors `E` exceptional over `X`. The remark of the source after Theorem 1.3 fixes this reading: the global mld of each normal variety is at most 2, because of the blow-up of a smooth point of codimension 2.

## The choices

* A prime divisor over `X` is a divisorial valuation of `k(X)` with a centre on `X`. It is exceptional when the centre is not the generic point of a prime divisor of `X`. The log discrepancy `a(E, X, B)` is the one of `LogDiscrepancyIs`, which also gives the centre.
* `globalMld P` is `⊥` when some exceptional log discrepancy is negative. Otherwise it is the infimum of the exceptional log discrepancies, as for `mld`. When `X` is a curve, no divisorial valuation is exceptional, the set is empty, and the infimum is `sInf ∅ = 0` in `ℝ`. No enc pair is a curve all the same, because the unique element of the definition does not exist.
-/

universe u

open AlgebraicGeometry Classical

noncomputable section

namespace MinimalModel

variable {k : Type u} [Field k] {X : NormalVariety k}

/-- The minimal log discrepancy of the pair `(X, Δ)` over all of `X`: the infimum of `a(E, X, Δ)` over the divisorial valuations `E` that are exceptional over `X`. It is `⊥` when one of them is negative (Han-Liu, Definition 3.8). -/
def globalMld (P : Pair X) : WithBot ℝ :=
  if ∃ v A, IsDivisorial v ∧ IsExceptional v ∧ LogDiscrepancyIs P v A ∧ A < 0 then ⊥
  else ((sInf {A | ∃ v, IsDivisorial v ∧ IsExceptional v ∧ LogDiscrepancyIs P v A} : ℝ) :
    WithBot ℝ)

/-- The pair `(X, Δ)` is enc, exceptionally non-canonical (Han-Liu, Definition 3.8(1)): `mld(X, Δ) < 1`, and exactly one divisorial valuation `E` exceptional over `X` has `a(E, X, Δ) ≤ 1`. -/
def IsEnc (P : Pair X) : Prop :=
  globalMld P < ((1 : ℝ) : WithBot ℝ) ∧
    ∃! v : Valuation (FF X) VZ, IsDivisorial v ∧ IsExceptional v ∧
      ∃ A, LogDiscrepancyIs P v A ∧ A ≤ 1

end MinimalModel

end
