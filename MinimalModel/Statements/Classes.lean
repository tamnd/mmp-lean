/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import MinimalModel.Statements.Basic

/-!
# Purely log terminal pairs and the implications among the classes of pairs

This file adds the class `IsPlt` of purely log terminal pairs (KM98 Definition 2.34) to the classes of `MinimalModel/Statements/Basic.lean`. It proves the implications among the six classes that the definitions allow.

## The implications

The direct ones are klt to plt, klt to dlt, dlt to lc and plt to klt when the coefficients are less than one and the divisors of `X` have their usual log discrepancy. The classes `IsTerminal` and `IsCanonical` only ask for a condition on the exceptional valuations. So terminal and canonical give plt when the coefficients of `Δ` are at most one.

The classes `IsKlt` and `IsLc` ask for a condition on every divisorial valuation, also on the valuations of the prime divisors of `X`. The log discrepancy of the valuation of a prime divisor `D` of `X` is `1 - coeff_D Δ`. With the definition `LogDiscrepancyIs`, this needs the uniqueness of the centre of a valuation on a separated scheme. So the implications canonical to klt and plt to lc in this file take this fact as the hypothesis `Pair.HasDivisorLogDiscrepancy`. The file `MinimalModel/Fidelity/Centre.lean` proves the hypothesis for every pair (`Pair.hasDivisorLogDiscrepancy`), and gives the implications with no hypothesis.

The class `IsDlt` asks for a closed set `Z` outside which the pair is snc, and for a positive log discrepancy at each valuation with centre in `Z`. The implication plt to dlt takes the lc condition, the set `Z` and the fact that each valuation with centre in `Z` is exceptional as hypotheses.
-/

universe u

namespace MinimalModel

variable {k : Type u} [Field k] {X : NormalVariety k}

/-- Purely log terminal (KM98 Definition 2.34): the coefficients of `Δ` are at most one, and the log discrepancy of each exceptional divisorial valuation over `X` is positive. In the discrepancy of KM98 this is `a(E, X, Δ) > -1` for each exceptional divisor `E`, because the log discrepancy is `1 + a(E, X, Δ)`. KM98 states no condition on the coefficients. In dimension at least two it follows from the condition on the exceptional divisors (KM98 Corollary 2.31). In dimension one there is no exceptional divisor, so the definition states it, as `IsLc` does. -/
def IsPlt (P : Pair X) : Prop :=
  (∀ Q, P.Δ Q ≤ 1) ∧
    ∀ v : Valuation (FF X) VZ, IsDivisorial v → IsExceptional v → ∀ A, LogDiscrepancyIs P v A → 0 < A

/-- The log discrepancy of each divisorial valuation that is not exceptional over `X` is `1 - Δ Q` for a prime divisor `Q` of `X`. This holds for every pair: such a valuation is the order along a prime divisor `Q` of `X`, and its log discrepancy is `1 - coeff_Q Δ`. The proof needs the uniqueness of the centre of a valuation on a separated scheme. The implications of this file take this fact as a hypothesis, and `Pair.hasDivisorLogDiscrepancy` in `MinimalModel/Fidelity/Centre.lean` proves it for every pair. -/
def Pair.HasDivisorLogDiscrepancy (P : Pair X) : Prop :=
  ∀ v : Valuation (FF X) VZ, IsDivisorial v → ¬ IsExceptional v → ∀ A, LogDiscrepancyIs P v A →
    ∃ Q : PrimeDivisor X, A = 1 - P.Δ Q

/-- A klt pair is plt. -/
theorem IsKlt.isPlt {P : Pair X} (h : IsKlt P) : IsPlt P :=
  ⟨fun Q => (h.1 Q).le, fun v hv _ A hA => h.2 v hv A hA⟩

/-- A klt pair is dlt, with the closed set `Z = X`. -/
theorem IsKlt.isDlt {P : Pair X} (h : IsKlt P) : IsDlt P :=
  ⟨⟨fun Q => (h.1 Q).le, fun v hv A hA => (h.2 v hv A hA).le⟩, Set.univ, isClosed_univ,
    fun x hx => absurd (Set.mem_univ x) hx, fun v hv _ _ _ A hA => h.2 v hv A hA⟩

/-- A dlt pair is lc. -/
theorem IsDlt.isLc {P : Pair X} (h : IsDlt P) : IsLc P := h.1

/-- A canonical pair whose coefficients are at most one is plt. -/
theorem IsCanonical.isPlt {P : Pair X} (h : IsCanonical P) (hΔ : ∀ Q, P.Δ Q ≤ 1) : IsPlt P :=
  ⟨hΔ, fun v hv he A hA => zero_lt_one.trans_le (h v hv he A hA)⟩

/-- A terminal pair whose coefficients are at most one is plt. -/
theorem IsTerminal.isPlt {P : Pair X} (h : IsTerminal P) (hΔ : ∀ Q, P.Δ Q ≤ 1) : IsPlt P :=
  ⟨hΔ, fun v hv he A hA => zero_lt_one.trans (h v hv he A hA)⟩

/-- A plt pair whose coefficients are less than one is klt, when the divisors of `X` have the log discrepancy `1 - Δ Q`. -/
theorem IsPlt.isKlt {P : Pair X} (h : IsPlt P) (hΔ : ∀ Q, P.Δ Q < 1)
    (hd : P.HasDivisorLogDiscrepancy) : IsKlt P := by
  refine ⟨hΔ, fun v hv A hA => ?_⟩
  by_cases he : IsExceptional v
  · exact h.2 v hv he A hA
  · obtain ⟨Q, rfl⟩ := hd v hv he A hA
    exact sub_pos.mpr (hΔ Q)

/-- A canonical pair whose coefficients are less than one is klt, when the divisors of `X` have the log discrepancy `1 - Δ Q`. With `Δ = 0` the condition on the coefficients holds. KM98 Definition 2.34 asks `⌊Δ⌋ ≤ 0` for klt, which is the condition `Δ Q < 1` here. -/
theorem IsCanonical.isKlt {P : Pair X} (h : IsCanonical P) (hΔ : ∀ Q, P.Δ Q < 1)
    (hd : P.HasDivisorLogDiscrepancy) : IsKlt P :=
  (h.isPlt fun Q => (hΔ Q).le).isKlt hΔ hd

/-- A terminal pair whose coefficients are less than one is klt, when the divisors of `X` have the log discrepancy `1 - Δ Q`. -/
theorem IsTerminal.isKlt {P : Pair X} (h : IsTerminal P) (hΔ : ∀ Q, P.Δ Q < 1)
    (hd : P.HasDivisorLogDiscrepancy) : IsKlt P :=
  (h.isPlt fun Q => (hΔ Q).le).isKlt hΔ hd

/-- A plt pair is lc, when the divisors of `X` have the log discrepancy `1 - Δ Q`. -/
theorem IsPlt.isLc {P : Pair X} (h : IsPlt P) (hd : P.HasDivisorLogDiscrepancy) : IsLc P := by
  refine ⟨h.1, fun v hv A hA => ?_⟩
  by_cases he : IsExceptional v
  · exact (h.2 v hv he A hA).le
  · obtain ⟨Q, rfl⟩ := hd v hv he A hA
    exact sub_nonneg.mpr (h.1 Q)

/-- A plt pair is dlt, when it is lc and there is a closed set `Z` such that the pair is snc outside `Z` and each divisorial valuation with centre in `Z` is exceptional. For a normal variety in characteristic zero, the set of the points where the pair is not snc has codimension at least two, so it is such a set. These facts are not formalized here. -/
theorem IsPlt.isDlt {P : Pair X} (h : IsPlt P) (hlc : IsLc P) {Z : Set X.toScheme} (hZ : IsClosed Z)
    (hsnc : ∀ x ∉ Z, IsSncAt {Q | P.Δ Q ≠ 0} x)
    (hexc : ∀ v : Valuation (FF X) VZ, IsDivisorial v → ∀ x, IsCentre v x → x ∈ Z → IsExceptional v) :
    IsDlt P :=
  ⟨hlc, Z, hZ, hsnc, fun v hv x hx hxZ A hA => h.2 v hv (hexc v hv x hx hxZ) A hA⟩

/-- A pair with a coefficient more than one is not plt. -/
theorem not_isPlt_of_one_lt {P : Pair X} {Q : PrimeDivisor X} (hQ : 1 < P.Δ Q) : ¬ IsPlt P :=
  fun h => absurd (h.1 Q) (not_le.2 hQ)

end MinimalModel
