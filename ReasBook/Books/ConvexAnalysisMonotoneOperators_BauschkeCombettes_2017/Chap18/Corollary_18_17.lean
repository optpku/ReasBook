/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Remark_4_34

open SubtypeFirmness

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient InnerProductSpace

universe u

namespace ERealFunction

section StrongerDifferentiabilityNotions

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: apply Theorem 18.15 to identify clause `(i)` with clause `(v)` for the TFAE list
-- attached to a continuous convex function. The hypothesis `Differentiable ℝ f` supplies the
-- differentiability component already built into both clauses, so the equivalence reduces to the
-- raw gradient statements.
/-- Corollary 18.17: for a Fréchet differentiable convex function on a real Hilbert space, the
gradient is `β`-Lipschitz if and only if it is `1 / β`-cocoercive. -/
theorem gradient_lipschitz_iff_cocoercive_of_differentiable_convex
    (f : H → ℝ) (hdiff : Differentiable ℝ f) (hconv : _root_.ConvexOn ℝ Set.univ f)
    (β : Set.Ioi (0 : ℝ)) :
    LipschitzWith (Real.toNNReal (β : ℝ)) (∇ f) ↔
      CocoerciveOn (1 / (β : ℝ)) (Set.univ : Set H) (fun x : Set.univ ↦ ∇ f x) := sorry

-- Proof sketch: specialize the previous theorem to `β = 1`. Then `1 / β = 1`, and
-- Remark 4.34(3) identifies `1`-cocoercivity on the whole space with firm nonexpansiveness.
/-- For a Fréchet differentiable convex function on a real Hilbert space, a nonexpansive gradient
is exactly a firmly nonexpansive gradient. -/
theorem gradient_nonexpansive_iff_firmlyNonexpansive_of_differentiable_convex
    (f : H → ℝ) (hdiff : Differentiable ℝ f) (hconv : _root_.ConvexOn ℝ Set.univ f) :
    LipschitzWith 1 (∇ f) ↔ FirmlyNonexpansive (∇ f) := sorry

end StrongerDifferentiabilityNotions

end ERealFunction
