/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import MinimalModel.Statements.BasicRelative

/-!
# Fidelity checks F3 for the relative vocabulary

Check F3 of spec 06.3 for `BasicRelative.lean`. Over `Spec k` the relative notions of bigness and pseudo-effectivity are the absolute notions of `Basic.lean`, and numerical equivalence is reflexive and symmetric on the `ℝ`-Cartier divisors.
-/

universe u

namespace MinimalModel

variable {k : Type u} [Field k] {X : NormalVariety k}

/-- Over `Spec k`, bigness over the base is bigness. -/
theorem isBigRel_str_iff (D : Divisor ℝ X) : IsBigRel D X.str ↔ IsBig D := Iff.rfl

/-- Over `Spec k`, pseudo-effectivity over the base is pseudo-effectivity. -/
theorem isPseudoEffectiveOver_str_iff (D : Divisor ℝ X) :
    IsPseudoEffectiveOver D X.str ↔ IsPseudoEffective D := Iff.rfl

/-- An `ℝ`-Cartier divisor is numerically equivalent to itself. -/
theorem NumEquiv.refl (I : IntersectionData X) {D : Divisor ℝ X} (h : IsRCartier D) :
    NumEquiv I D D :=
  ⟨h, h, fun _ => rfl⟩

/-- Numerical equivalence is symmetric. -/
theorem NumEquiv.symm {I : IntersectionData X} {D D' : Divisor ℝ X} (h : NumEquiv I D D') :
    NumEquiv I D' D :=
  ⟨h.2.1, h.1, fun C => (h.2.2 C).symm⟩

/-- A divisor that is not `ℝ`-Cartier is numerically equivalent to no divisor. This is why `GeneralizedAbundance` asks that `L` is Cartier: then `K + Δ + L` is `ℝ`-Cartier, and the conclusion can hold. -/
theorem not_numEquiv_of_not_isRCartier {I : IntersectionData X} {D : Divisor ℝ X}
    (h : ¬ IsRCartier D) (D' : Divisor ℝ X) : ¬ NumEquiv I D D' :=
  fun h' => h h'.1

end MinimalModel
