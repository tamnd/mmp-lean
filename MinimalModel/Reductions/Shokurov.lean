/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.Order.WellFoundedSet
import Mathlib.Topology.Semicontinuity.Basic

/-!
# The abstract Shokurov lemma

This file proves the abstract form of the termination argument of Shokurov (Letters of a bi-rationalist V, 2004), route item O-R4-1 of spec 04.5 and target 27 of report D. The idea of the reduction S28 (`MinimalModel.ShokurovReduction`) is that along a sequence of flips the minimal log discrepancies form a sequence in a set with the ascending chain condition, and that such a sequence cannot increase for ever.

The file has no geometry. A flip sequence is axiomatic: a relation `step` on a type `α` of states, and a sequence `f : ℕ → α` with `step (f i) (f (i + 1))` for each `i`. The ascending chain condition (ACC) on a set `S` is `S.WellFoundedOn (· > ·)`: each nonempty subset of `S` has a maximal element, so `S` has no strictly increasing sequence. Each result says that no infinite flip sequence exists.

## Main results

* `MinimalModel.not_exists_chain_of_acc`: an invariant with values in an ACC set that strictly increases at each step gives termination.
* `MinimalModel.partiallyWellOrderedOn_ge_of_acc`: in a linear order, an ACC set is partially well ordered by `≥`.
* `MinimalModel.shokurovLemma_pi`: the same as `not_exists_chain_of_acc` for a finite tuple of invariants, each in its own ACC set, that strictly increases in the product order. The proof is Dickson's lemma, `Set.PartiallyWellOrderedOn.pi`.
* `MinimalModel.shokurovLemma`: the abstract Shokurov lemma. Each state has a compact nonempty locus of points and a lower semicontinuous local invariant on it, with values in an ACC set. When each point of the next locus has a larger value than some point of the current locus, the sequence is finite. Lower semicontinuity is used where Shokurov uses it: the minimum of the local invariant on the locus is attained, so it is a value of the invariant and lies in the ACC set.

In the application the states are the models of a sequence of flips of pairs of dimension `n` with coefficients in a fixed DCC set, the local invariant is the minimal log discrepancy, and the ACC set is the set of minimal log discrepancies of S49 (`MinimalModel.ACCMld`). The lower semicontinuity is S50 (`MinimalModel.LSCMld`). The geometric input, that the minimal log discrepancies do not decrease under a flip and increase over the flipped locus, is not in this file. The `reader` role checks the form of the improvement hypothesis against the source before S28 is proved from this lemma.
-/

namespace MinimalModel

/-- **Termination from an ACC invariant.** Let `step` be a relation on states, and `v` an invariant with values in a set `S` of a preorder that satisfies the ascending chain condition. When `v` strictly increases at each step, there is no infinite sequence of steps. -/
theorem not_exists_chain_of_acc {α β : Type*} [Preorder β] {S : Set β}
    (hS : S.WellFoundedOn (· > ·)) {step : α → α → Prop} (v : α → β) (hv : ∀ x, v x ∈ S)
    (himp : ∀ x y, step x y → v x < v y) : ¬ ∃ f : ℕ → α, ∀ i, step (f i) (f (i + 1)) := by
  rintro ⟨f, hf⟩
  rw [Set.wellFoundedOn_iff] at hS
  obtain ⟨_, ⟨n, rfl⟩, hmin⟩ := hS.has_min (Set.range fun n => v (f n)) ⟨_, 0, rfl⟩
  exact hmin _ ⟨n + 1, rfl⟩ ⟨himp _ _ (hf n), hv _, hv _⟩

/-- In a linear order, a set with the ascending chain condition is partially well ordered by `≥`: each sequence in the set has two terms `m < n` with `g n ≤ g m`. -/
theorem partiallyWellOrderedOn_ge_of_acc {β : Type*} [LinearOrder β] {S : Set β}
    (hS : S.WellFoundedOn (· > ·)) : S.PartiallyWellOrderedOn fun a b => b ≤ a := by
  rw [Set.partiallyWellOrderedOn_iff_exists_lt]
  intro g hg
  by_contra hcon
  refine not_exists_chain_of_acc hS g hg (step := fun m n : ℕ => m < n) ?_
    ⟨id, fun n => Nat.lt_add_one n⟩
  intro m n hmn
  exact not_le.1 fun hle => hcon ⟨m, n, hmn, hle⟩

/-- **The abstract Shokurov lemma for a finite tuple of invariants.** Let `step` be a relation on states, and `v` a tuple of invariants indexed by a finite type `ι`, such that the coordinate `i` takes values in a set `S i` of a linear order with the ascending chain condition. When `v` strictly increases in the product order at each step (each coordinate does not decrease and one coordinate increases), there is no infinite sequence of steps. -/
theorem shokurovLemma_pi {α ι β : Type*} [Finite ι] [LinearOrder β] {S : ι → Set β}
    (hS : ∀ i, (S i).WellFoundedOn (· > ·)) {step : α → α → Prop} (v : α → ι → β)
    (hv : ∀ x i, v x i ∈ S i) (himp : ∀ x y, step x y → v x < v y) :
    ¬ ∃ f : ℕ → α, ∀ n, step (f n) (f (n + 1)) := by
  rintro ⟨f, hf⟩
  haveI : IsPreorder β fun a b : β => b ≤ a :=
    { refl := fun a => le_refl a
      trans := fun _ _ _ h₁ h₂ => le_trans h₂ h₁ }
  have hP : (Set.univ.pi S).PartiallyWellOrderedOn fun a b : ι → β => ∀ i, b i ≤ a i :=
    Set.PartiallyWellOrderedOn.pi (α := fun _ => β) (r := fun _ a b => b ≤ a) (s := S)
      fun i => partiallyWellOrderedOn_ge_of_acc (hS i)
  have hmono : StrictMono fun n => v (f n) := strictMono_nat_of_lt_succ fun n => himp _ _ (hf n)
  obtain ⟨m, n, hmn, hle⟩ := hP.exists_lt fun n => Set.mem_univ_pi.2 (hv (f n))
  exact (lt_iff_le_not_ge.1 (hmono hmn)).2 (Pi.le_def.2 hle)

/-- **The abstract Shokurov lemma** (Shokurov 2004; route item O-R4-1). Let `step` be a relation on states, the steps of an axiomatic flip sequence. Each state `x` has a topological space of points `P x`, a compact nonempty locus `L x` in it, and a local invariant `a x` that is lower semicontinuous on `L x`. The values of the local invariants on the loci lie in a set `S` of a linear order with the ascending chain condition. The invariant strictly improves at each step: for each point `q` of the locus of the next state there is a point `p` of the locus of the current state with `a x p < a y q`. Then there is no infinite sequence of steps.

The proof takes the minimum of `a x` on `L x`. It exists by lower semicontinuity and compactness (`LowerSemicontinuousOn.exists_isMinOn`), so it is a value of the local invariant and lies in `S`. It strictly increases at each step, and `not_exists_chain_of_acc` applies. Without the lower semicontinuity the infimum need not be in `S`. -/
theorem shokurovLemma {α β : Type*} [LinearOrder β] {S : Set β} (hS : S.WellFoundedOn (· > ·))
    {P : α → Type*} [∀ x, TopologicalSpace (P x)] (L : ∀ x, Set (P x)) (a : ∀ x, P x → β)
    (hL : ∀ x, IsCompact (L x)) (hne : ∀ x, (L x).Nonempty)
    (hlsc : ∀ x, LowerSemicontinuousOn (a x) (L x)) (ha : ∀ x, ∀ p ∈ L x, a x p ∈ S)
    {step : α → α → Prop} (himp : ∀ x y, step x y → ∀ q ∈ L y, ∃ p ∈ L x, a x p < a y q) :
    ¬ ∃ f : ℕ → α, ∀ i, step (f i) (f (i + 1)) := by
  choose m hm hmin using fun x => (hlsc x).exists_isMinOn (hne x) (hL x)
  refine not_exists_chain_of_acc hS (fun x => a x (m x)) (fun x => ha x _ (hm x)) ?_
  intro x y hxy
  obtain ⟨p, hp, hlt⟩ := himp x y hxy (m y) (hm y)
  exact lt_of_le_of_lt (isMinOn_iff.1 (hmin x) p hp) hlt

end MinimalModel
