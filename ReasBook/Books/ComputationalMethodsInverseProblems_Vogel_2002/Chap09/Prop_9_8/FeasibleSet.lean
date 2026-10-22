/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.Calculus.Gradient.Basic

public section

noncomputable section

namespace NonnegativeOrthant

variable {n : ℕ}

/-- The feasible set for problem `(9.16)` is the nonnegative orthant in
`EuclideanSpace ℝ (Fin n)`. -/
def feasibleSet (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  { f | ∀ i : Fin n, 0 ≤ f i }

@[simp] theorem mem_feasibleSet
    {f : EuclideanSpace ℝ (Fin n)} :
    f ∈ feasibleSet n ↔ ∀ i : Fin n, 0 ≤ f i :=
  Iff.rfl

end NonnegativeOrthant
