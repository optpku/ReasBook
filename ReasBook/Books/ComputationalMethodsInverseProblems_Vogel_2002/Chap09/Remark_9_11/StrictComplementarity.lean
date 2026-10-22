/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Definition_9_5.StrictComplementarity
public import Mathlib.Analysis.Calculus.Gradient.Basic

public section

noncomputable section

namespace NonnegativeOrthant

variable {n : ℕ}

/-- The strict complementarity condition `(9.20)` for the nonnegative-orthant
problem requires every zero coordinate of `f` to have strictly positive
gradient. -/
abbrev StrictComplementarity
    (J : EuclideanSpace ℝ (Fin n) → ℝ)
    (f : EuclideanSpace ℝ (Fin n)) : Prop :=
  KKT.StrictComplementarity (fun i x ↦ x i) f (fun i ↦ gradient J f i)

/-- `StrictComplementarity J f` is equivalent to the coordinatewise source form
`f i = 0 → 0 < gradient J f i`. -/
theorem strictComplementarity_iff
    (J : EuclideanSpace ℝ (Fin n) → ℝ)
    (f : EuclideanSpace ℝ (Fin n)) :
    StrictComplementarity J f ↔
      ∀ i : Fin n, f i = 0 → 0 < gradient J f i := by
  -- Specialize the generic KKT equivalence to the orthant constraints `x ↦ x i`.
  simpa [StrictComplementarity] using
    (KKT.strictComplementarity_iff
      (fun i x ↦ x i) f (fun i ↦ gradient J f i))

/-- Under strict complementarity, any zero coordinate of `f` has strictly
positive gradient. -/
theorem pos_of_eq_zero
    {J : EuclideanSpace ℝ (Fin n) → ℝ}
    {f : EuclideanSpace ℝ (Fin n)}
    (hsc : StrictComplementarity J f)
    {i : Fin n}
    (hi : f i = 0) :
    0 < gradient J f i := by
  -- Convert strict complementarity to its coordinatewise form and apply it at `i`.
  exact ((strictComplementarity_iff J f).mp hsc) i hi

end NonnegativeOrthant
