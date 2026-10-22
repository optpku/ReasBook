/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_3_6_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

/- Definition 5.3.5.2 is a source-facing specialization in the chapter's central-path /
barrier-penalty domain.

Primary domain:
* central paths for barrier-penalized minimization in a real inner-product space.

Sampled owner-style declarations:
* `centralPathPenaltyObjective` in `Definition_5_3_6_1`, the Chapter 5 owner for the penalty
  objective `z ↦ t ⟪c, z⟫ + F z`;
* `centralPathPenaltyObjective_apply` in `Definition_5_3_6_1`, the companion evaluation theorem
  for that owner;
* `IsCentralPath` in `Definition_5_3_6_1`, the owner predicate asserting pointwise minimizers of
  the penalty objective;
* `isCentralPath_iff` in `Definition_5_3_6_1`, the canonical pointwise minimizer bridge.

Best owner abstraction:
* source-facing: the auxiliary central path based at `y₀`;
* core/canonical: `IsCentralPath dom (-∇ F (y0 : E)) F yStar`;
* bridge/view: the specialization of `centralPathPenaltyObjective` to `c = -∇ F (y0 : E)`.

Primitive data:
* a domain `dom : Set E`;
* a barrier `F : E → ℝ`;
* a base point `y0 : dom`;
* a trajectory `yStar : Set.Ici (0 : ℝ) → dom`.

Derived API:
* the specialized penalty formula
  `centralPathPenaltyObjective (-∇ F (y0 : E)) F t z =
    F z - (t : ℝ) * inner ℝ (∇ F (y0 : E)) z`;
* the pointwise minimizer expansion of `IsCentralPath dom (-∇ F (y0 : E)) F yStar`.

Source/core/bridge triage:
* source-facing: the auxiliary central path obtained by choosing the linear objective
  `c = -∇ F(y₀)`;
* core/canonical: `centralPathPenaltyObjective` and `IsCentralPath`;
* bridge/view: the specialization to `c = -∇ F(y₀)`.

The previous version restated the specialized `IsMinOn` condition directly. This file now reuses
the Chapter 5 owner `IsCentralPath` and keeps the textbook formula only as a thin specialization
bridge. -/

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {dom : Set E} (F : E → ℝ) (y0 : dom)
variable (yStar : Set.Ici (0 : ℝ) → dom)

/- Definition 5.3.5.2 specializes the central-path owner to the choice
`c = -∇ F(y₀)`. -/
#check IsCentralPath dom (-∇ F (y0 : E)) F yStar

/- The specialized penalty objective is exactly the textbook auxiliary-central-path formula. -/
#check
  (show
      ∀ t : Set.Ici (0 : ℝ), ∀ z : E,
        centralPathPenaltyObjective (-∇ F (y0 : E)) F t z =
          F z - (t : ℝ) * inner ℝ (∇ F (y0 : E)) z
    from fun t z ↦ by
      rw [centralPathPenaltyObjective_apply]
      simp [sub_eq_add_neg, add_comm])

/- Expanding the specialized owner recovers the source-facing pointwise minimizer statement. -/
#check
  (show
      IsCentralPath dom (-∇ F (y0 : E)) F yStar ↔
        ∀ t : Set.Ici (0 : ℝ),
          IsMinOn
            (fun z ↦ F z - (t : ℝ) * inner ℝ (∇ F (y0 : E)) z)
            dom
            (yStar t : E)
    from by
      have hobjective :
          ∀ t : Set.Ici (0 : ℝ),
            centralPathPenaltyObjective (-∇ F (y0 : E)) F t =
              fun z ↦ F z - (t : ℝ) * inner ℝ (∇ F (y0 : E)) z := by
        intro t
        funext z
        rw [centralPathPenaltyObjective_apply]
        simp [sub_eq_add_neg, add_comm]
      constructor
      · intro h t
        rw [← hobjective t]
        exact h t
      · intro h t
        rw [hobjective t]
        exact h t)

end
