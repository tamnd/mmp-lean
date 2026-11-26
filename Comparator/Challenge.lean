/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import MinimalModel.Statements.Basic

/-!
# The challenge for `lake comparator`

This file states each proved top theorem of the package with its pinned statement from `MinimalModel/Statements/`, and with `sorry` in place of the proof. `lake comparator` checks that each theorem of the same name in `Comparator/Solution.lean` has exactly this type and uses only the permitted axioms. This is row Q4 of spec 14. The file is not in the main tree, so `scripts/scan.sh` does not scan it.

At S0 no top theorem is proved, so this file states no theorem, and `theorem_names` in `comparator.json` is empty. The job `comparator` of the workflow `trust` skips the comparison until the first top theorem is proved. The first entries are planned at S2: `MinimalModel.Toric.coneTheorem`.
-/
