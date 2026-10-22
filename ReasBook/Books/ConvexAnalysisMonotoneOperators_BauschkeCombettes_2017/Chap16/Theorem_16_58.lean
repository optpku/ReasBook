/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Corollary_13_38
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Definition_16_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

section SubdifferentialCalculus

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/- Source/core/bridge triage:
- `source-facing`: Theorem 16.58 is the Brøndsted--Rockafellar approximation statement.
- `core/canonical`: the owner abstractions are the subdifferential `∂ f` and the packaged
  `Γ₀(H)` Fenchel conjugate `f∗[hf]`.
- `bridge/view`: graph language for `∂ f` is derived from the primitive data `z`, `w`, and
  `w ∈ (∂ f) z`, so the public surface keeps the latter and avoids pair-projection bookkeeping.
-/

-- Proof sketch: apply Ekeland's variational principle to the shifted function
-- `x ↦ (f x : EReal) - ⟪x, v⟫`. The gap hypothesis makes `y` an approximate minimizer with error
-- `λ * μ`. Ekeland yields `z` with `‖z - y‖ ≤ λ` such that `z` minimizes the perturbation by
-- `μ ‖· - z‖`. Fermat's rule puts `0` in the subdifferential of that perturbation at `z`, the
-- sum rule splits the subdifferential, and the norm subdifferential formula produces
-- `w ∈ (∂ f) z` with `‖w - v‖ ≤ μ`.
/-- Theorem 16.58: the Brondsted--Rockafellar approximation theorem. For `f ∈ Γ₀(H)`, if the
Fenchel--Young gap at `(y, v)` is at most `λμ`, then there exist `z` and `w ∈ (∂ f) z` with
`z` within distance `λ` of `y` and `w` within distance `μ` of `v`. -/
theorem exists_subgradient_point_close_of_fenchelYoung_gap_le
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (y v : H) (lam μ : NNReal)
    (hgap :
      (f y : EReal) + (f∗[hf] v : EReal) ≤
        ((⟪y, v⟫_ℝ + ((lam * μ : NNReal) : ℝ) : ℝ) : EReal)) :
    ∃ z w, w ∈ (∂ f) z ∧ ‖z - y‖ ≤ (lam : ℝ) ∧ ‖w - v‖ ≤ (μ : ℝ) := sorry

end SubdifferentialCalculus

end ERealFunction
