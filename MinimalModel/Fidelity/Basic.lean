/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import MinimalModel.Statements.Termination

/-!
# Fidelity checks F3 for the vocabulary

Check F3 of spec 06.3: small facts that a faithful definition must satisfy, and facts that show which forms of a statement are trivial. A failure of one of these lemmas shows a wrong definition before any proof uses it.
-/

universe u

namespace MinimalModel

variable {k : Type u} [Field k] {X : NormalVariety k}

/-- A klt pair is lc. -/
theorem IsKlt.isLc {P : Pair X} (h : IsKlt P) : IsLc P :=
  ⟨fun Q => (h.1 Q).le, fun v hv A hA => (h.2 v hv A hA).le⟩

/-- A terminal pair is canonical. -/
theorem IsTerminal.isCanonical {P : Pair X} (h : IsTerminal P) : IsCanonical P :=
  fun v hv he A hA => (h v hv he A hA).le

/-- A pair with a coefficient more than one is not lc. -/
theorem not_isLc_of_one_lt {P : Pair X} {Q : PrimeDivisor X} (hQ : 1 < P.Δ Q) : ¬ IsLc P :=
  fun h => absurd (h.1 Q) (not_le.2 hQ)

/-- A pair with a coefficient at least one is not klt. -/
theorem not_isKlt_of_one_le {P : Pair X} {Q : PrimeDivisor X} (hQ : 1 ≤ P.Δ Q) : ¬ IsKlt P :=
  fun h => absurd (h.1 Q) (not_lt.2 hQ)

/-- The mld of an lc pair is never `⊥`. -/
theorem mld_ne_bot_of_isLc {P : Pair X} (h : IsLc P) (x : X.toScheme) : mld P x ≠ ⊥ := by
  unfold mld
  split_ifs with h'
  · obtain ⟨v, A, hv, -, hA, hneg⟩ := h'
    exact absurd (h.2 v hv A hA) (not_le.2 hneg)
  · exact WithBot.coe_ne_bot

/-- The program of length zero. It shows that "some program is finite" is trivial, so the termination statements must be about every program (spec 06.5, risk 1). -/
def Program.trivial (A : PairModel k) : Program A where
  len := 0
  model := fun _ => A
  start := rfl
  step := fun i hi => absurd hi (by simp)

/-- Each model has a finite program. This is the trivial form of termination that the statements avoid. -/
theorem exists_finite_program (A : PairModel k) : ∃ p : Program A, p.len ≠ ⊤ :=
  ⟨Program.trivial A, by simp [Program.trivial]⟩

/-- A flip is a step of the program. -/
theorem IsFlip.isMMPStep {A B : PairModel k} (h : IsFlip A B) : IsMMPStep A B :=
  let ⟨s, _⟩ := h; ⟨s⟩

/-- An infinite sequence of flips is an infinite program. -/
theorem HasInfiniteFlips.hasInfiniteProgram {A : PairModel k} (h : HasInfiniteFlips A) :
    HasInfiniteProgram A :=
  let ⟨m, h0, hs⟩ := h; ⟨m, h0, fun i => (hs i).isMMPStep⟩

/-- S22 gives the termination of flips for the 4-folds of its class. -/
theorem TerminationLc4Rational.noInfiniteFlips {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    (h : TerminationLc4Rational k) (A : PairModel k) (hn : A.X.dim = 4) (hlc : IsLc A.P)
    (hq : A.P.IsRationalBoundary) : ¬ HasInfiniteFlips A :=
  fun hf => h A hn hlc hq hf.hasInfiniteProgram

end MinimalModel
