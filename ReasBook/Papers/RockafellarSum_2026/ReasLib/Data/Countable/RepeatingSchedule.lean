/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import Mathlib.Data.Countable.Defs
public import Mathlib.Data.Nat.Pairing
public import Mathlib.Data.Set.Finite.Basic

/-!
# Repeating schedules

This module defines countable schedules with strictly increasing occurrence
indices and their canonical construction.
-/

public section

universe u

/-- A sequence together with a strictly increasing sequence of indices at which each value
occurs. -/
structure RepeatingSchedule (α : Type u) where
  /-- The underlying sequence. -/
  toFun : ℕ → α
  /-- The sequence of occurrence indices for each value. -/
  occurrence : α → ℕ → ℕ
  /-- The occurrence indices for each value are strictly increasing. -/
  strictMono_occurrence : ∀ a, StrictMono (occurrence a)
  /-- Every designated occurrence index has the requested value. -/
  apply_occurrence : ∀ a k, toFun (occurrence a k) = a

namespace RepeatingSchedule

/-- Pairing a fixed natural number with a varying second coordinate is strictly increasing. -/
private theorem strictMono_occurrenceOfSurjective {α : Type u} (f : ℕ → α)
    (hf : Function.Surjective f) (a : α) :
    StrictMono (fun k ↦ Nat.pair (Function.surjInv hf a) k) := by
  -- With the chosen preimage fixed, pairing preserves strict order in the counter.
  intro k l hkl
  exact Nat.pair_lt_pair_right _ hkl

/-- The pairing-based occurrence indices recover the requested value under the repeated
schedule. -/
private theorem apply_occurrenceOfSurjective {α : Type u} (f : ℕ → α)
    (hf : Function.Surjective f) (a : α) (k : ℕ) :
    f (Nat.unpair (Nat.pair (Function.surjInv hf a) k)).1 = a := by
  -- Unpair the designated index, then apply the defining property of the section.
  rw [Nat.unpair_pair]
  exact Function.surjInv_eq hf a

/-- Construct a repeating schedule from an explicitly selected surjection from `ℕ`. -/
noncomputable def ofSurjective {α : Type u} (f : ℕ → α)
    (hf : Function.Surjective f) : RepeatingSchedule α where
  toFun n := f (Nat.unpair n).1
  occurrence a k := Nat.pair (Function.surjInv hf a) k
  strictMono_occurrence := strictMono_occurrenceOfSurjective f hf
  apply_occurrence := apply_occurrenceOfSurjective f hf

/-- Every value in a repeating schedule has an infinite fiber. -/
theorem infinite_fiber {α : Type u} (r : RepeatingSchedule α) (a : α) :
    Set.Infinite {n | r.toFun n = a} := by
  -- The strictly increasing occurrence map has an infinite range.
  refine (Set.infinite_range_of_injective (r.strictMono_occurrence a).injective).mono ?_
  -- Every point of that range lies in the requested fiber.
  rintro n ⟨k, rfl⟩
  exact r.apply_occurrence a k

/-- Construct a repeating schedule on any nonempty countable type. -/
noncomputable def ofCountable (α : Type u) [Countable α] [Nonempty α] : RepeatingSchedule α :=
  ofSurjective (exists_surjective_nat α).choose (exists_surjective_nat α).choose_spec

end RepeatingSchedule
