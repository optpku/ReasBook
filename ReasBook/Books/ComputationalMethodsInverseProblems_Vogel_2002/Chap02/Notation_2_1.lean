/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Defs

public section

/-!
Notation 2.1-extra-1. This file owns the source-facing `C¹(Ω)` function-space
surface used in Chapter 2, implemented as the set of scalar-valued functions
that are `ContDiffOn ℝ 1` on `Ω`.
-/

namespace Set

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Notation 2.1. The source notation `C¹(Ω)` is represented by the set of
real-valued functions on `E` that are `ContDiffOn ℝ 1` on `Ω`. The Chapter 2
uses of this notation are scalar-valued, so this owner keeps the codomain
explicitly fixed to `ℝ` instead of introducing a broader overloaded surface. -/
def contDiffOne (Ω : Set E) : Set (E → ℝ) := {f | ContDiffOn ℝ 1 f Ω}

notation "C¹(" s ")" => Set.contDiffOne s

/-- Membership in `C¹(Ω)` is exactly the `ContDiffOn ℝ 1` condition on `Ω`. -/
@[simp] theorem mem_contDiffOne_iff {Ω : Set E} {f : E → ℝ} :
    f ∈ C¹(Ω) ↔ ContDiffOn ℝ 1 f Ω :=
  Iff.rfl

end Set
