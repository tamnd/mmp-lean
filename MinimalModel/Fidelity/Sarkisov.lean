/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import MinimalModel.Statements.Models

/-!
# Fidelity checks F3 for the Sarkisov links

Check F3 of spec 06.3 for `Sarkisov.lean`, used by S36.

* A Mori fibre space of `Sarkisov.lean` is a Mori fibre space in the sense of `IsMoriFibreSpace` of `Basic.lean`, and its total space has positive dimension.
* Each Mori fibre space is related to itself by the empty sequence of links, through the identity. So the conclusion of S36 holds for the run with no step, from a Mori fibre space to itself.
* A sequence of links gives a birational map, so the relation of S36 is only between birational Mori fibre spaces.
* A flop and a divisorial contraction are not isomorphisms: the contraction of a flop contracts a curve, and a divisorial contraction maps a prime divisor to a point that is not a prime divisor.

There is no F2 here: an instance needs a Mori fibre space, that is a variety of positive dimension with its intersection numbers.
-/

universe u

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace MinimalModel

variable {k : Type u} [Field k]

/-- A Mori fibre space of `Sarkisov.lean` is a Mori fibre space in the sense of `Basic.lean`. -/
theorem MoriFibreSpace.isMoriFibreSpace (M : MoriFibreSpace k) : IsMoriFibreSpace M.A :=
  ⟨M.S, M.φ, M.over_φ, M.contraction, M.dim_lt, M.extremal, M.negative⟩

/-- The total space of a Mori fibre space has positive dimension. -/
theorem MoriFibreSpace.dim_pos (M : MoriFibreSpace k) : 0 < M.A.X.dim :=
  lt_of_le_of_lt (Nat.zero_le _) M.dim_lt

/-- The identity of a normal variety is the pullback of the functions along the identity. -/
theorem isFieldPullback_id (X : NormalVariety k) :
    IsFieldPullback (X := X) (Z := X) (𝟙 X.toScheme) AlgEquiv.refl :=
  ⟨rfl, fun _ _ _ _ => rfl⟩

/-- Each Mori fibre space is related to itself by the empty sequence of links. -/
theorem SarkisovChain.self (M : MoriFibreSpace k) : SarkisovChain M M AlgEquiv.refl :=
  SarkisovChain.iso M M (Iso.refl _) (Iso.refl _) AlgEquiv.refl (by simp)
    (by simp) (by simp) (isFieldPullback_id M.A.X)

/-- The conclusion of S36 for the run with no step, from a Mori fibre space to itself. -/
theorem sarkisov_refl (M : MoriFibreSpace k) :
    SarkisovChain M M ((AlgEquiv.refl : FF M.A.X ≃ₐ[k] FF M.A.X).trans AlgEquiv.refl.symm) := by
  have h : (AlgEquiv.refl : FF M.A.X ≃ₐ[k] FF M.A.X).trans AlgEquiv.refl.symm = AlgEquiv.refl :=
    AlgEquiv.ext fun _ => rfl
  rw [h]
  exact SarkisovChain.self M

/-- The run with no step is a run of the minimal model program. -/
theorem isMMPRun_refl (A : PairModel k) : IsMMPRun A A AlgEquiv.refl := IsMMPRun.refl A

/-- A sequence of links gives a birational map. -/
theorem SarkisovChain.nonempty_algEquiv {M N : MoriFibreSpace k} {σ : FF N.A.X ≃ₐ[k] FF M.A.X}
    (_h : SarkisovChain M N σ) : Nonempty (FF N.A.X ≃ₐ[k] FF M.A.X) :=
  ⟨σ⟩

/-- The contraction of a flop contracts a curve. -/
theorem IsFlopOver.exists_contracted {X V X' : NormalVariety k} {P : Pair X} {P' : Pair X'}
    {π : X.toScheme ⟶ V.toScheme} {π' : X'.toScheme ⟶ V.toScheme} {σ : FF X' ≃ₐ[k] FF X}
    (h : IsFlopOver P P' π π' σ) :
    ∃ (W : NormalVariety k) (f : X.toScheme ⟶ W.toScheme) (C : Curve X), IsContracted f C := by
  obtain ⟨-, W, f, _, _, -, -, -, -, -, -, -, -, ⟨_, ⟨C, hC, -⟩, -⟩, -⟩ := h
  exact ⟨W, f, C, hC⟩

/-- A divisorial contraction maps a prime divisor to a point that is not a prime divisor. -/
theorem IsDivisorialContr.exists_exceptional {X Z : NormalVariety k} {p : X.toScheme ⟶ Z.toScheme}
    (h : IsDivisorialContr p) : ∃ E : PrimeDivisor X, Order.coheight (p.base E.1) ≠ 1 :=
  h.2.2

end MinimalModel
