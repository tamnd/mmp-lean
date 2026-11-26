/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import MinimalModel.Toric.Program

/-!
# The toric minimal model program

The statement S39 of family D of spec 06.2.2, planned at S2. It uses the fans of `MinimalModel/Toric/Fan.lean` and the program on fans of `MinimalModel/Toric/Program.lean`. It is in its own file so that the pinned statement `ToricConeTheorem` of `Toric.lean` does not change.
-/

namespace MinimalModel

open Toric

/-- S39, the toric minimal model program (Reid, Decomposition of toric morphisms, 1983; Fujino and Sato, Introduction to the toric Mori theory, Michigan Math. J. 52 (2004); Matsuki, Introduction to the Mori program, Chapter 14; Cox, Little and Schenck, Toric varieties, Chapter 15). Let `F` be a complete simplicial projective fan and `D` a torus-invariant divisor with rational coefficients. Then each toric `D`-program from `(F, D)` runs and ends:
1. no infinite sequence of toric steps starts at `(F, D)`;
2. at the last model of each finite sequence of steps, `D` is nef, or the model is a toric Mori fibre space for `D`, or one more step exists.
So each toric `D`-program ends with a minimal model (`D` nef) or a Mori fibre space. The divisor is arbitrary, as in the toric program of the sources; with `D = K` this is the `K`-program.

The row of spec 06.2.2 also names the toric formula for the mld at a torus-fixed point (the minimum of a linear function on the lattice points of the cone, Ambro). That part needs the toric variety as a scheme, to compare with `mld` of `Basic.lean`, and it is not stated here. -/
def ToricMMP : Prop :=
  ∀ (n : ℕ) (F : Fan n), F.IsSimplicialFan → F.IsProjectiveFan →
    ∀ D : F.TDivisor ℝ, (∀ ρ, D ρ ∈ Set.range ((↑) : ℚ → ℝ)) →
      (¬ ∃ model : ℕ → ToricModel n, model 0 = ⟨F, D⟩ ∧
          ∀ i, IsToricStep (model i) (model (i + 1))) ∧
      ∀ (m : ℕ) (model : ℕ → ToricModel n), model 0 = ⟨F, D⟩ →
        (∀ i < m, IsToricStep (model i) (model (i + 1))) →
        (model m).F.IsNef (model m).D ∨ IsToricMoriFibreSpace (model m) ∨
          ∃ B, IsToricStep (model m) B

end MinimalModel
