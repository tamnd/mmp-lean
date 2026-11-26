/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import MinimalModel.Statements.Basic

/-!
# Family C: termination and flips

The statements of family C of spec 06.2.2 that are planned at S0. "Every program" is the form of each statement (spec 06.2.3): the statements say that no infinite sequence of steps exists, so they cover each choice of the extremal rays.
-/

universe u

namespace MinimalModel

variable (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]

/-- S20, the termination conjecture `T(n)`. For each projective lc pair of dimension `n`, each sequence of `(K + Δ)`-flips is finite. This is open for `n ≥ 4`. -/
def Termination (n : ℕ) : Prop :=
  ∀ A : PairModel k, A.X.dim = n → IsLc A.P → ¬ HasInfiniteFlips A

/-- S22, a fresh claim (OpenAI 056, AxiomMath/MMP; spec 01.3). For each projective lc pair of dimension 4 with a rational boundary, each sequence of steps of the minimal model program is finite. The class is `claimed`: this statement is never a hypothesis of another proof (spec 06.6). -/
def TerminationLc4Rational : Prop :=
  ∀ A : PairModel k, A.X.dim = 4 → IsLc A.P → A.P.IsRationalBoundary → ¬ HasInfiniteProgram A

/-- S49, the ACC conjecture for minimal log discrepancies in dimension `n` (Shokurov; KM98 3.16 in spec 03). For each set `I ⊆ [0, 1]` that satisfies the DCC, the set of the mlds at the closed points of the lc pairs of dimension `n` with coefficients in `I` satisfies the ACC. -/
def ACCMld (n : ℕ) : Prop :=
  ∀ I : Set ℝ, I ⊆ Set.Icc 0 1 → I.IsWF →
    ∀ a : ℕ → ℝ, (∀ i, ∃ (X : NormalVariety k) (P : Pair X) (x : X.toScheme), X.dim = n ∧
      IsLc P ∧ P.Δ.CoeffsIn I ∧ IsClosed ({x} : Set X.toScheme) ∧ mld P x = (a i : WithBot ℝ)) →
    ¬ StrictMono a

/-- S50, the lower semicontinuity conjecture for minimal log discrepancies in dimension `n` (Ambro). For each lc pair of dimension `n` and each real `t`, the closed points `x` with `mld(x) > t` are the closed points of an open set. -/
def LSCMld (n : ℕ) : Prop :=
  ∀ (X : NormalVariety k) (P : Pair X), X.dim = n → IsLc P → ∀ t : ℝ,
    ∃ U : Set X.toScheme, IsOpen U ∧ ∀ x : X.toScheme, IsClosed ({x} : Set X.toScheme) →
      (x ∈ U ↔ (t : WithBot ℝ) < mld P x)

/-- S28, Shokurov's reduction (Shokurov 2004). The ACC and the lower semicontinuity of the minimal log discrepancies in dimension `n` give the termination of flips in dimension `n`. The `reader` role checks the class of pairs of the source (klt or lc) before F5. -/
def ShokurovReduction (n : ℕ) : Prop :=
  ACCMld k n → LSCMld k n → Termination k n

end MinimalModel
