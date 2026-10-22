/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap15.Example_15_29

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped InnerProductSpace Pointwise

namespace ERealFunction

/- 
Source/core/bridge triage:
- `source-facing`: Corollary 15.30 is the attained bilinear minimax statement
  `min_x max_v ⟪Lx, v⟫ = max_v min_x ⟪Lx, v⟫`.
- `core/canonical`: `IsSaddlePointOn` for the payoff `(x, v) ↦ ⟪L x, v⟫` on `C × D`.
- `bridge/view`: the chapter-owner reformulation through `σ[D] (L x)` and
  `innerInfimumOn C (L.adjoint v)`, obtained from the image rewrites in Example 15.29.
-/

section FenchelRockafellarDuality

variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

variable {C : Set E} {D : Set F}

variable (L : E →L[ℝ] F)

-- Proof sketch: pass from `C` and `D` to their closed convex hulls, which preserve the direct
-- bilinear slice-value functions via the support-function and inner-infimum invariance results
-- from Chapters 7 and 11 together with the image rewrites from Example 15.29. Then use the
-- attained owner equality on the closed convex hulls and weak compactness of bounded closed convex
-- sets to recover a primal minimizer and a dual maximizer for the original bilinear payoff.
/-- Corollary 15.30: the bilinear minimax equality
`min_{x ∈ C} max_{v ∈ D} ⟪Lx, v⟫ = max_{v ∈ D} min_{x ∈ C} ⟪Lx, v⟫`
is attained by some `x ∈ C` and `v ∈ D` when `C` and `D` are nonempty bounded closed subsets of
real Hilbert spaces. -/
theorem vonNeumann_minimax_inner_eq
    (hC_nonempty : C.Nonempty) (hC_bounded : Bornology.IsBounded C) (hC_closed : IsClosed C)
    (hD_nonempty : D.Nonempty) (hD_bounded : Bornology.IsBounded D) (hD_closed : IsClosed D) :
    ∃ x ∈ C, ∃ v ∈ D,
      IsMinOn
          (fun y : E ↦ sSup ((fun w : F ↦ (⟪L y, w⟫_ℝ : EReal)) '' D))
          C x ∧
        IsMaxOn
          (fun w : F ↦ sInf ((fun y : E ↦ (⟪L y, w⟫_ℝ : EReal)) '' C))
          D v ∧
        sInf
            ((fun y : E ↦ sSup ((fun w : F ↦ (⟪L y, w⟫_ℝ : EReal)) '' D)) '' C) =
          sSup
            ((fun w : F ↦ sInf ((fun y : E ↦ (⟪L y, w⟫_ℝ : EReal)) '' C)) '' D) ∧
        sSup ((fun w : F ↦ (⟪L x, w⟫_ℝ : EReal)) '' D) =
          sInf ((fun y : E ↦ (⟪L y, v⟫_ℝ : EReal)) '' C) := by
  sorry

-- Proof sketch: use the attained bilinear minimax statement to choose `x ∈ C` and `v ∈ D`
-- realizing the primal and dual slice values, then apply `isSaddlePointOn_iff` to package those
-- two equalities as the canonical saddle-point owner condition.
/-- Companion consequence: Corollary 15.30 also yields a saddle point of the bilinear payoff on
`C × D`. This is the core/canonical owner consequence, not the main source-facing entry. -/
theorem vonNeumann_minimax_isSaddlePointOn_inner
    (hC_nonempty : C.Nonempty) (hC_bounded : Bornology.IsBounded C) (hC_closed : IsClosed C)
    (hD_nonempty : D.Nonempty) (hD_bounded : Bornology.IsBounded D) (hD_closed : IsClosed D) :
    ∃ x ∈ C, ∃ v ∈ D,
      IsSaddlePointOn C D (fun y w ↦ (⟪L y, w⟫_ℝ : EReal)) x v := by
  sorry

-- Proof sketch: pass from `C` and `D` to their closed convex hulls, which preserve the owner
-- slice-value functions by `supportFunction_closure_convexHull_eq` and
-- `innerInfimumOn_closure_convexHull_eq`. Then apply Example 15.29 to those closed convex hulls
-- and rewrite the resulting saddle-value equality back on the original `σ[D]`/`innerInfimumOn C`
-- surface.
/-- Companion bridge: the owner equality
`inf_{x ∈ C} σ[D](Lx) = sup_{v ∈ D} innerInfimumOn C (L.adjoint v)` only needs the Chapter 15
regularity assumption on the closed convex hulls of `C` and `D`. This is the canonical
`bridge/view` reformulation used by Example 15.29, not the main source-facing entry. -/
theorem vonNeumann_minimax_supportFunction_eq_innerInfimumOn
    (hsri :
      (0 : F) ∈
        Set.strongRelativeInterior
          (closure (convexHull ℝ D) -
            L '' closure (convexHull ℝ C))) :
    sInf ((fun x : E ↦ σ[D] (L x)) '' C) =
      sSup ((fun v : F ↦ innerInfimumOn C (L.adjoint v)) '' D) := by
  sorry

end FenchelRockafellarDuality

end ERealFunction
