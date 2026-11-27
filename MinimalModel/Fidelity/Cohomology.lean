/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import MinimalModel.Statements.Cohomology

/-!
# Fidelity checks F3 for the maps of divisorial sheaves

Check F3 of spec 06.3 for the maps of `Cohomology.lean` that S03 uses.
* On sections, `mulSectionsHom` is multiplication by `φ`.
* The identity of `𝒪_V(D)` gives the identity on cohomology, so `cohomMap` is the map of Mathlib's sheaf cohomology and the injectivity in S03 is about the expected maps.
-/

universe u

open AlgebraicGeometry CategoryTheory

namespace MinimalModel

variable {k : Type u} [Field k] {X : NormalVariety k}

/-- On sections, `mulSectionsHom` is multiplication by `φ`. -/
theorem mulSectionsHom_apply {D E : Divisor ℤ X} {S : Set X.toScheme} {φ : FF X} (hφ : φ ≠ 0)
    (hE : ∀ P : PrimeDivisor X, P.1 ∈ S → 0 ≤ E P + ordAt φ P) (ψ : divisorialSections D S) :
    (mulSectionsHom hφ hE ψ : FF X) = φ * ψ :=
  rfl

/-- The identity of `𝒪_V(D)` gives the identity on `H^i(V, 𝒪_X(D))`. -/
theorem cohomMap_id (D : Divisor ℤ X) (V : X.toScheme.Opens) (i : ℕ) :
    cohomMap (𝟙 (divisorialSheaf D V)) i = id := by
  funext x
  exact Sheaf.H.map_id_apply x

/-- The identity of `𝒪_V(D)` gives an injective map on cohomology. -/
theorem cohomMap_id_injective (D : Divisor ℤ X) (V : X.toScheme.Opens) (i : ℕ) :
    Function.Injective (cohomMap (𝟙 (divisorialSheaf D V)) i) := by
  rw [cohomMap_id]
  exact Function.injective_id

end MinimalModel
