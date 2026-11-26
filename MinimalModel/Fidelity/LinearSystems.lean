/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import MinimalModel.Statements.LinearSystems

/-!
# Fidelity checks F3 for the linear systems

Check F3 of spec 06.3 for `LinearSystems.lean`, used by S34.
* `0` is in `H⁰(X, 𝒪_X(D))`, and so is `1` when `D ≥ 0`.
* Each member `D + div φ` of `|D|` is effective.
* The whole space is very general, with the empty family of hypersurfaces. The very general sets are closed under supersets and under finite intersections.
-/

universe u

namespace MinimalModel

variable {k : Type u} [Field k] {X : NormalVariety k}

/-- `0` is a section of each divisor. -/
theorem zero_mem_RRSpace (D : Divisor ℤ X) : (0 : FF X) ∈ RRSpace D := (RRSpace D).zero_mem

/-- The constant `1` is a section of each effective divisor. -/
theorem one_mem_RRSpace {D : Divisor ℤ X} (hD : 0 ≤ D) : (1 : FF X) ∈ RRSpace D := by
  rw [mem_RRSpace_iff]
  refine Or.inr fun P => ?_
  have h1 : ordAt (1 : FF X) P = 0 := by simpa using ordAt_algebraMap (X := X) (1 : k) P
  have h2 : (0 : Divisor ℤ X) P ≤ D P := hD P
  rw [h1, zero_add]
  simpa using h2

/-- Each member of a linear system is effective: if `E = D + div φ` with `φ ∈ H⁰(X, 𝒪_X(D))`, then `E ≥ 0`. -/
theorem IsLinSysMember.nonneg {D E : Divisor ℤ X} {φ : FF X} (h : IsLinSysMember D φ E) : 0 ≤ E := by
  intro P
  have h1 : (E - D) P = ordAt φ P := h.2.2 P (Set.mem_univ _)
  have h2 : 0 ≤ ordAt φ P + D P := (mem_RRSpace_iff.mp h.1).resolve_left h.2.1 P
  rw [Finsupp.sub_apply] at h1
  exact (by linarith : (0 : ℤ) ≤ E P)

section VeryGeneral

variable {V : Type*} [AddCommGroup V] [Module k V]

/-- The whole space is very general: take no hypersurface. -/
theorem isVeryGeneral_univ : IsVeryGeneral k (Set.univ : Set V) :=
  ⟨∅, Set.countable_empty, fun _ h => by simp at h, fun _ _ => trivial⟩

/-- A set that contains a very general set is very general. -/
theorem IsVeryGeneral.mono {S T : Set V} (h : IsVeryGeneral k S) (hST : S ⊆ T) :
    IsVeryGeneral k T := by
  obtain ⟨F, hF, hF', hS⟩ := h
  exact ⟨F, hF, hF', fun v hv => hST (hS v hv)⟩

/-- The intersection of two very general sets is very general: take both families of hypersurfaces. -/
theorem IsVeryGeneral.inter {S T : Set V} (hS : IsVeryGeneral k S) (hT : IsVeryGeneral k T) :
    IsVeryGeneral k (S ∩ T) := by
  obtain ⟨F, hF, hF', hS⟩ := hS
  obtain ⟨G, hG, hG', hT⟩ := hT
  refine ⟨F ∪ G, hF.union hG, fun f hf => ((Set.mem_union f F G).mp hf).elim (hF' f) (hG' f), fun v hv => ⟨?_, ?_⟩⟩
  · exact hS v fun f hf => hv f (Set.mem_union_left G hf)
  · exact hT v fun f hf => hv f (Set.mem_union_right F hf)

end VeryGeneral

end MinimalModel
