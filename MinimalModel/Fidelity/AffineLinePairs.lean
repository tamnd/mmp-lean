/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import MinimalModel.Fidelity.Centre

/-!
# Fidelity checks F2 and F3: the classes of the pairs on the affine line

This file continues `MinimalModel/Fidelity/AffineLine.lean`. It gives the positive instances on the affine line `𝔸¹`. The pair `(𝔸¹, 0)` is klt, lc, plt, dlt, terminal and canonical. The pair `(𝔸¹, c [0])` is klt and dlt for `c < 1`, and it is lc and plt for `c ≤ 1`.

The proofs use `MinimalModel/Fidelity/Centre.lean`. The affine line has dimension one, so a centre of a divisorial valuation is a prime divisor `Q`, and the log discrepancy of the valuation is `1 - Δ Q`. The coefficients of the boundary `c [0]` are at most `c`.

The file does not show that `(𝔸¹, [0])` is dlt. The class `IsDlt` asks for a closed set outside which the pair is snc, and for `[0]` this needs the snc condition at the point `0`, which is not done here.
-/

universe u

open AlgebraicGeometry

noncomputable section

namespace MinimalModel

variable (k : Type u) [Field k]

/-- Each coefficient of the boundary of `(𝔸¹, c [0])` is at most `c`. -/
theorem affineLinePair_coeff_le {c : ℝ} (hc : 0 ≤ c) (Q : PrimeDivisor (affineLine k)) :
    (affineLinePair k c hc).Δ Q ≤ c := by
  classical
  simp only [affineLinePair, Finsupp.single_apply]
  split_ifs <;> linarith

/-- F3: the pair `(𝔸¹, c [0])` is klt for `c < 1`. -/
theorem affineLinePair_isKlt {c : ℝ} (hc : 0 ≤ c) (hc1 : c < 1) : IsKlt (affineLinePair k c hc) :=
  isKlt_of_dim_eq_one (affineLine_dim k) fun Q => (affineLinePair_coeff_le k hc Q).trans_lt hc1

/-- F3: the pair `(𝔸¹, c [0])` is lc for `c ≤ 1`. -/
theorem affineLinePair_isLc {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1) : IsLc (affineLinePair k c hc) :=
  isLc_of_dim_eq_one (affineLine_dim k) fun Q => (affineLinePair_coeff_le k hc Q).trans hc1

/-- F3: the pair `(𝔸¹, c [0])` is plt for `c ≤ 1`. -/
theorem affineLinePair_isPlt {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1) : IsPlt (affineLinePair k c hc) :=
  isPlt_of_dim_eq_one (affineLine_dim k) fun Q => (affineLinePair_coeff_le k hc Q).trans hc1

/-- F3: the pair `(𝔸¹, c [0])` is dlt for `c < 1`. -/
theorem affineLinePair_isDlt {c : ℝ} (hc : 0 ≤ c) (hc1 : c < 1) : IsDlt (affineLinePair k c hc) :=
  (affineLinePair_isKlt k hc hc1).isDlt

/-- The pair `(𝔸¹, c [0])` is terminal for each `c`: there is no exceptional divisorial valuation with a log discrepancy. -/
theorem affineLinePair_isTerminal {c : ℝ} (hc : 0 ≤ c) : IsTerminal (affineLinePair k c hc) :=
  isTerminal_of_dim_eq_one (affineLine_dim k) _

/-- The pair `(𝔸¹, c [0])` is canonical for each `c`. -/
theorem affineLinePair_isCanonical {c : ℝ} (hc : 0 ≤ c) : IsCanonical (affineLinePair k c hc) :=
  isCanonical_of_dim_eq_one (affineLine_dim k) _

/-- F2: the pair `(𝔸¹, 0)` is klt. -/
theorem affineLinePair_zero_isKlt : IsKlt (affineLinePair k 0 le_rfl) :=
  affineLinePair_isKlt k le_rfl zero_lt_one

/-- F2: the pair `(𝔸¹, 0)` is lc. -/
theorem affineLinePair_zero_isLc : IsLc (affineLinePair k 0 le_rfl) :=
  affineLinePair_isLc k le_rfl zero_le_one

/-- F2: the pair `(𝔸¹, 0)` is plt. -/
theorem affineLinePair_zero_isPlt : IsPlt (affineLinePair k 0 le_rfl) :=
  affineLinePair_isPlt k le_rfl zero_le_one

/-- F2: the pair `(𝔸¹, 0)` is dlt. -/
theorem affineLinePair_zero_isDlt : IsDlt (affineLinePair k 0 le_rfl) :=
  affineLinePair_isDlt k le_rfl zero_lt_one

/-- F2: the pair `(𝔸¹, 0)` is terminal. -/
theorem affineLinePair_zero_isTerminal : IsTerminal (affineLinePair k 0 le_rfl) :=
  affineLinePair_isTerminal k le_rfl

/-- F2: the pair `(𝔸¹, 0)` is canonical. -/
theorem affineLinePair_zero_isCanonical : IsCanonical (affineLinePair k 0 le_rfl) :=
  affineLinePair_isCanonical k le_rfl

/-- F3: the pair `(𝔸¹, [0])` is lc. -/
theorem affineLinePair_one_isLc : IsLc (affineLinePair k 1 zero_le_one) :=
  affineLinePair_isLc k zero_le_one le_rfl

/-- F3: the pair `(𝔸¹, [0])` is plt. -/
theorem affineLinePair_one_isPlt : IsPlt (affineLinePair k 1 zero_le_one) :=
  affineLinePair_isPlt k zero_le_one le_rfl

end MinimalModel
