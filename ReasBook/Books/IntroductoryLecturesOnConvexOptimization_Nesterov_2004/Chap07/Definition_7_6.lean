/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_4_4

-- Declarations for this item will be appended below by the statement pipeline.

open Metric

universe u

/- Domain review for this item: it lies in the real continuous-dual / operator-norm domain.

Sampled owner-style declarations:
- mathlib `StrongDual`
- mathlib `ContinuousLinearMap.sSup_unitClosedBall_eq_norm`
- mathlib `IsCompact.exists_sSup_image_eq`
- project `dual_norm_eq_sSup_closedUnitBall` in `Chap04/Definition_4_4_4`

Best owner abstraction:
- source-facing: the textbook dual norm of a real continuous linear functional;
- core/canonical: the existing norm `‖·‖ : StrongDual ℝ E → ℝ`;
- bridge/view: the Chapter 4 support-function formula `dual_norm_eq_sSup_closedUnitBall`.

Primitive data:
- a real normed space `E`;
- a continuous linear functional `g : StrongDual ℝ E`.

Derived API:
- the canonical norm owner `‖g‖`;
- the closed-unit-ball support formula, reused directly from Chapter 4;
- in finite dimensions, existence of a maximizer on the primal closed unit ball.

Source/core/bridge triage:
- source-facing: the dual norm and its finite-dimensional attainment formula;
- core/canonical: the norm on `StrongDual ℝ E`;
- bridge/view: `dual_norm_eq_sSup_closedUnitBall`.

The previous local theorem `dual_norm_eq_sSup_pairing_closedUnitBall` duplicated the exact
Chapter 4 bridge `dual_norm_eq_sSup_closedUnitBall`. This file is therefore recall-first: it
reuses the canonical owner and the existing bridge, and keeps only the new finite-dimensional
attainment statement. -/

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Definition 7.6: the dual norm is the canonical norm on the continuous dual `StrongDual ℝ E`.
-/
#check (‖·‖ : StrongDual ℝ E → ℝ)

/- The textbook closed-unit-ball formula is exactly the existing Chapter 4 bridge theorem. -/
recall dual_norm_eq_sSup_closedUnitBall

section

variable [FiniteDimensional ℝ E]

/-- The dual norm of a continuous linear functional is attained on the primal closed unit ball. -/
-- Proof sketch: use compactness of the closed unit ball in finite dimensions and continuity of
-- `x ↦ g x` to obtain a maximizer, then identify the attained supremum with `‖g‖` via
-- `dual_norm_eq_sSup_closedUnitBall`.
theorem dual_norm_exists_maximizer_closedUnitBall (g : StrongDual ℝ E) :
    ∃ x ∈ closedBall (0 : E) 1, ‖g‖ = g x := by
  -- Finite dimensionality makes the primal closed unit ball compact.
  have hcompact : IsCompact (closedBall (0 : E) 1) := by
    simpa using isCompact_closedBall (0 : E) 1
  -- The closed unit ball is nonempty, with witness `0`.
  have hzero_mem : (0 : E) ∈ closedBall (0 : E) 1 := by
    simp
  have hnonempty : Set.Nonempty (closedBall (0 : E) 1) := ⟨0, hzero_mem⟩
  -- The evaluation map of a continuous linear functional is continuous on the compact domain.
  have hcont : ContinuousOn (fun x : E ↦ g x) (closedBall (0 : E) 1) := by
    simpa using g.continuous.continuousOn
  -- A continuous real-valued function on a compact nonempty set attains its supremum.
  obtain ⟨x, hx, hsSup⟩ := hcompact.exists_sSup_image_eq hnonempty hcont
  refine ⟨x, hx, ?_⟩
  -- Rewrite the attained supremum using the Chapter 4 dual-norm formula.
  calc
    ‖g‖ = sSup (g '' closedBall (0 : E) 1) := dual_norm_eq_sSup_closedUnitBall g
    _ = g x := by simpa using hsSup

end

end
