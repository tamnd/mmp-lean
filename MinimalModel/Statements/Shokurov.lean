/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.Order.WellFoundedSet
import Mathlib.Topology.Semicontinuity.Basic

/-!
# The abstract Shokurov lemma

The pinned statement of the abstract Shokurov lemma, route item O-R4-1 of spec 04.5, a top theorem of milestone S3 (spec 14.2). Row Q4 of spec 14 compares the proved theorem `MinimalModel.shokurovLemma` with this statement.

The file uses Mathlib only: the ascending chain condition `Set.WellFoundedOn`, compact sets and lower semicontinuity. It does not import the proof.
-/

namespace MinimalModel

/-- **The abstract Shokurov lemma** (Shokurov 2004, Letters of a bi-rationalist V; route item O-R4-1). Let `step` be a relation on a type `α` of states, the steps of an axiomatic flip sequence. Each state `x` has a topological space of points `P x`, a compact nonempty locus `L x` in it, and a local invariant `a x` that is lower semicontinuous on `L x`. The values of the local invariants on the loci lie in a set `S` of a linear order with the ascending chain condition, `S.WellFoundedOn (· > ·)`. The invariant strictly improves at each step: for each point `q` of the locus of the next state there is a point `p` of the locus of the current state with `a x p < a y q`. Then there is no infinite sequence of steps.

The statement has no geometry. In the application to S28 (`MinimalModel.ShokurovReduction`) the states are the models of a sequence of flips, the local invariant is the minimal log discrepancy and the ACC set is that of S49. -/
def ShokurovLemma.{u, v, w} : Prop :=
  ∀ {α : Type u} {β : Type v} [LinearOrder β] {S : Set β}, S.WellFoundedOn (· > ·) →
    ∀ {P : α → Type w} [∀ x, TopologicalSpace (P x)] (L : ∀ x, Set (P x)) (a : ∀ x, P x → β),
      (∀ x, IsCompact (L x)) → (∀ x, (L x).Nonempty) →
      (∀ x, LowerSemicontinuousOn (a x) (L x)) → (∀ x, ∀ p ∈ L x, a x p ∈ S) →
      ∀ {step : α → α → Prop}, (∀ x y, step x y → ∀ q ∈ L y, ∃ p ∈ L x, a x p < a y q) →
        ¬ ∃ f : ℕ → α, ∀ i, step (f i) (f (i + 1))

end MinimalModel
