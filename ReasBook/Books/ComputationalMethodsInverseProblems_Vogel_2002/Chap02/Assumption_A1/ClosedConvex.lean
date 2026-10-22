/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Topology.Basic

public section

universe u

namespace Set

variable {E : Type u} [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]

/-- A subset of a real topological vector space is closed and convex. -/
def ClosedConvex (C : Set E) : Prop :=
  IsClosed C ∧ Convex ℝ C

/-- Specification lemma for `Set.ClosedConvex`. -/
theorem closedConvex_iff {C : Set E} :
    ClosedConvex C ↔ IsClosed C ∧ Convex ℝ C :=
  Iff.rfl

namespace ClosedConvex

/-- A closed convex set is closed. -/
theorem isClosed {C : Set E} (hC : ClosedConvex C) : IsClosed C :=
  hC.1

/-- A closed convex set is convex. -/
theorem convex {C : Set E} (hC : ClosedConvex C) : Convex ℝ C :=
  hC.2

end ClosedConvex

end Set
