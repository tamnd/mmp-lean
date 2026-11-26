/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import MinimalModel.Statements.Toric

/-!
# The challenge for `lake comparator`

This file states each proved top theorem of the package with its pinned statement from `MinimalModel/Statements/`, and with `sorry` in place of the proof. `lake comparator` checks that each theorem of the same name in `Comparator/Solution.lean` has exactly this type and uses only the permitted axioms. This is row Q4 of spec 14. The file is not in the main tree, so `scripts/scan.sh` does not scan it.

The first entry came at S2: `MinimalModel.Toric.toricConeTheorem`, the toric cone theorem in combinatorial form, with the pinned statement `MinimalModel.Toric.ToricConeTheorem` of `MinimalModel/Statements/Toric.lean`. Each entry is also in `theorem_names` of `comparator.json`.
-/

/-- The toric cone theorem in combinatorial form, with the pinned statement of `MinimalModel/Statements/Toric.lean`. -/
theorem MinimalModel.Toric.toricConeTheorem : MinimalModel.Toric.ToricConeTheorem := by
  sorry
