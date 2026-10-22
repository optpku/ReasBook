/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap10.Definition_10_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Definition 10.11: for a proper convex `]-∞,+∞]`-valued function, the exact modulus of
convexity assigns to each radius `t ≥ 0` the infimum of the normalized Jensen gaps over all
effective-domain pairs at distance `t` and all coefficients `α ∈ ]0,1[`. -/
noncomputable def exactModulusOfConvexity
    (f : H → Set.Ioi (⊥ : EReal))
    : NNReal → EReal :=
  fun t ↦ sInf
    {δ : EReal |
      ∃ x ∈ effectiveDomain f, ∃ y ∈ effectiveDomain f,
        ‖x - y‖₊ = t ∧
        ∃ α : ℝ, α ∈ Set.Ioo (0 : ℝ) 1 ∧
          δ = jensenGap f α x y / (α * (1 - α) : ℝ)}

/-- The exact modulus of convexity is bounded above by every normalized Jensen gap realized at the
given radius. -/
-- Proof sketch: unfold `exactModulusOfConvexity` and apply `sInf_le` to the witness
-- corresponding to the chosen points `x`, `y`, and coefficient `α`.
theorem exactModulusOfConvexity_le_normalizedGap
    (f : H → Set.Ioi (⊥ : EReal)) {t : NNReal} {x y : H}
    (hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f) (ht : ‖x - y‖₊ = t)
    {α : ℝ} (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    exactModulusOfConvexity f t ≤ jensenGap f α x y / (α * (1 - α) : ℝ) := sorry

end ERealFunction
