/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Definition_8_7
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Definition_12_20_Core
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Definition_13_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Corollary_13_38

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

section Conjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: `conjugate f u` is already strictly above `-∞`, and subtracting a finite real
-- quadratic term preserves that lower bound in `EReal`.
/-- Subtracting the finite quadratic term `γ⁻¹ ‖u‖² / 2` from the conjugate of a real-valued
function still yields an `]-∞,+∞]`-valued function. -/
theorem conjugate_sub_invHalfSquaredNorm_gt_bot
    (f : H → ℝ) (γ : Set.Ioi (0 : ℝ)) (u : H) :
    ⊥ < f.toEReal.asEReal∗ u - moreauQuadraticKernel γ u := by
  refine bot_lt_iff_ne_bot.mpr ?_
  have hconj : f.toEReal.asEReal∗ u ≠ ⊥ := by
    exact conjugate_ne_bot_of_effectiveDomain_nonempty (by simp) u
  have hkernel : (moreauQuadraticKernel γ u : EReal) ≠ ⊤ := by
    simpa using
      (EReal.coe_ne_top (((1 / (2 * (γ : ℝ))) * ‖u‖ ^ (2 : ℕ) : ℝ)))
  change f.toEReal.asEReal∗ u + -↑(moreauQuadraticKernel γ u) ≠ ⊥
  rw [EReal.add_ne_bot_iff]
  constructor
  · exact hconj
  · intro hneg
    exact hkernel ((EReal.neg_eq_bot_iff.mp hneg))

/-- The shifted conjugate `f* - γ⁻¹ q`, packaged through the canonical Moreau quadratic kernel
as an `]-∞,+∞]`-valued function. -/
noncomputable def conjugateSubInvHalfSquaredNorm
    (f : H → ℝ) (γ : Set.Ioi (0 : ℝ)) : H → Set.Ioi (⊥ : EReal) :=
  fun u ↦
    ⟨f.toEReal.asEReal∗ u - moreauQuadraticKernel γ u,
      conjugate_sub_invHalfSquaredNorm_gt_bot f γ u⟩

/-- Coercing `conjugateSubInvHalfSquaredNorm f γ` to `EReal` recovers the canonical expression
`f.toEReal.asEReal∗ - moreauQuadraticKernel γ`. -/
@[simp] theorem conjugateSubInvHalfSquaredNorm_apply
    (f : H → ℝ) (γ : Set.Ioi (0 : ℝ)) (u : H) :
    (conjugateSubInvHalfSquaredNorm f γ u : EReal) =
      f.toEReal.asEReal∗ u - moreauQuadraticKernel γ u :=
  rfl

end Conjugation

section ConjugationComplete

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: for `(i) → (ii)`, apply the Fenchel--Moreau identities from Chapter 13 to the
-- convex function `f* - γ⁻¹ q` and identify `γ q - f` with a Moreau-envelope expression, whose
-- convexity follows from Proposition 12.15. For `(ii) → (i)`, write `f = γ q - g` with `g`
-- convex, use Proposition 13.29 to rewrite `f* - γ⁻¹ q` as a positive multiple of a conjugate,
-- and conclude by convexity of Fenchel conjugates.
/-- Proposition 14.2: for a continuous convex real-valued function `f` on a real Hilbert space and
`γ ∈ ℝ_{++}`, the shifted conjugate `f* - γ⁻¹ q` with `q(x) = ‖x‖² / 2` is convex if and only if
`γ q - f` is convex. -/
theorem conjugateSubInvHalfSquaredNorm_convex_iff_halfSquaredNorm_sub_convex
    (f : H → ℝ) (hcont : Continuous f) (hconv : _root_.ConvexOn ℝ Set.univ f)
    (γ : Set.Ioi (0 : ℝ)) :
    ConvexOn (conjugateSubInvHalfSquaredNorm f γ)
      (effectiveDomain (conjugateSubInvHalfSquaredNorm f γ)) ↔
      _root_.ConvexOn ℝ Set.univ (fun x : H ↦ ((γ : ℝ) / 2) * ‖x‖ ^ (2 : ℕ) - f x) := sorry

end ConjugationComplete

end ERealFunction
