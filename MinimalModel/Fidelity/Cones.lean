/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import MinimalModel.Statements.Boundedness
import MinimalModel.Statements.Models

/-!
# Fidelity checks F3 for the cones and the `ε`-lc pairs

Check F3 of spec 06.3 for `Cones.lean` and for `IsEpsLc`, used by S37, S53 and S55.
* A `0`-lc pair is an lc pair, the condition `ε`-lc gets weaker as `ε` gets smaller, and an `ε`-lc pair with `ε > 0` is klt. So BAB is about klt pairs, as Birkar says.
* The class of the zero divisor is zero, and the zero class is in the moving cone and in the effective cone.
* A Mori dream space is `ℚ`-factorial, and the effective nef cone is in the nef cone.
-/

universe u

namespace MinimalModel

variable {k : Type u} [Field k] {X : NormalVariety k}

/-- A `0`-lc pair is an lc pair. -/
theorem isEpsLc_zero_iff (P : Pair X) : IsEpsLc 0 P ↔ IsLc P := by
  simp only [IsEpsLc, IsLc, sub_zero]

/-- An `ε'`-lc pair is `ε`-lc for each `ε ≤ ε'`. -/
theorem IsEpsLc.mono {ε ε' : ℝ} (h : ε ≤ ε') {P : Pair X} (hP : IsEpsLc ε' P) : IsEpsLc ε P :=
  ⟨fun Q => (hP.1 Q).trans (by linarith), fun v hv a ha => h.trans (hP.2 v hv a ha)⟩

/-- An `ε`-lc pair with `ε > 0` is klt. -/
theorem IsEpsLc.isKlt {ε : ℝ} (hε : 0 < ε) {P : Pair X} (hP : IsEpsLc ε P) : IsKlt P :=
  ⟨fun Q => (hP.1 Q).trans_lt (by linarith), fun v hv a ha => hε.trans_le (hP.2 v hv a ha)⟩

/-- The class of the zero divisor is zero. -/
theorem numClass_zero (I : IntersectionData X) : numClass I 0 = 0 := by
  funext C
  have h := I.dot_smul 0 0 (by unfold IsRCartier; exact Submodule.zero_mem _) C
  simpa [numClass] using h

/-- The zero class is in the moving cone. -/
theorem zero_mem_movingCone (I : IntersectionData X) : (0 : Curve X → ℝ) ∈ movingCone I :=
  ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩

/-- The zero class is in the effective cone. -/
theorem zero_mem_effCone (I : IntersectionData X) : (0 : Curve X → ℝ) ∈ effCone I :=
  ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩

/-- A Mori dream space is `ℚ`-factorial. -/
theorem IsMoriDreamSpace.isQFactorial {I : IntersectionData X} (h : IsMoriDreamSpace X I) :
    IsQFactorial X :=
  h.1

/-- The effective nef cone is in the nef cone. -/
theorem effNefCone_subset_nefCone (I : IntersectionData X) : effNefCone I ⊆ nefCone I :=
  Set.inter_subset_left

end MinimalModel
