/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Topology.Order.LocalExtr

public section

open scoped Topology

universe u v

variable {α : Type u} {β : Type v} [TopologicalSpace α] [Preorder β]

/-- A function `f` has a strict local minimum at `a` if `a` is a local minimizer and
`f a < f x` eventually holds on the punctured neighborhood `𝓝[≠] a`. -/
def IsStrictLocalMin (f : α → β) (a : α) : Prop :=
  IsLocalMin f a ∧ ∀ᶠ x in 𝓝[≠] a, f a < f x

namespace IsStrictLocalMin

/-- A strict local minimizer is, in particular, a local minimizer. -/
theorem isLocalMin {f : α → β} {a : α} (h : IsStrictLocalMin f a) :
    IsLocalMin f a := by
  -- Unpack the first component of the defining conjunction.
  exact h.1

/-- A strict local minimizer satisfies a strict inequality on a punctured neighborhood. -/
theorem eventually_lt {f : α → β} {a : α} (h : IsStrictLocalMin f a) :
    ∀ᶠ x in 𝓝[≠] a, f a < f x := by
  -- Unpack the punctured-neighborhood part of the definition.
  exact h.2

end IsStrictLocalMin

/-- The defining specification of `IsStrictLocalMin`. -/
theorem isStrictLocalMin_iff (f : α → β) (a : α) :
    IsStrictLocalMin f a ↔ IsLocalMin f a ∧ ∀ᶠ x in 𝓝[≠] a, f a < f x := by
  -- This is exactly the definition unfolded once.
  rfl
