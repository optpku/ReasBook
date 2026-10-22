/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_10

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/-
Definition 3.2.2 lies in the positive-parameter strong-convexity domain for real-valued
functions on a feasible set.

Sampled owner-style declarations:
- mathlib `StrongConvexOn`
- mathlib `strongConvexOn_iff_convex`
- project `strongConvexOn_iff_quadratic_jensen_bound` in `Chap02/Theorem_2_10`

Best owner abstraction:
- source-facing: positive strong convexity on `Q`, expressed as `∃ μ > 0, StrongConvexOn Q μ f`
- core/canonical: `StrongConvexOn Q μ f`
- bridge/view: `strongConvexOn_iff_quadratic_jensen_bound`

Primitive data:
- the feasible set `Q`
- the objective `f`

Derived API:
- existence of a positive strong-convexity modulus `μ`
- convexity of `Q`
- the textbook quadratic segment inequality for that modulus

Source/core/bridge triage:
- source-facing main entry: `∃ μ > 0, StrongConvexOn Q μ f`
- core/canonical companion: `StrongConvexOn Q μ f`
- bridge/view companion: the fixed-modulus quadratic Jensen equivalence

Definition 3.2.2 adds only the positive-existential layer on top of the fixed-modulus owner.
This file therefore keeps that existential surface as the main statement and reuses the canonical
bridge `strongConvexOn_iff_quadratic_jensen_bound`, rather than introducing a parallel local
strong-convexity definition.
-/

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Q : Set E} {μ : ℝ} {f : E → ℝ}

/- Definition 3.2.2: a real-valued function is strongly convex on the feasible set `Q` exactly
when there exists a positive modulus `μ` such that `StrongConvexOn Q μ f`. The textbook segment
inequality is recorded below as the canonical bridge for this positive-existential owner. -/
#check (∃ μ > 0, StrongConvexOn Q μ f)

/-- The positive-modulus strong-convexity condition is equivalent to the textbook quadratic
segment upper bound on a convex feasible set. -/
-- Proof sketch: apply `strongConvexOn_iff_quadratic_jensen_bound` for each fixed modulus `μ`,
-- move the positive witness through that fixed-parameter equivalence, and keep `Convex ℝ Q` as
-- the explicit source-side hypothesis because the textbook states the segment inequality only on
-- convex feasible sets.
theorem exists_pos_strongConvexOn_iff_forall_segment_upper_bound :
    (∃ μ > 0, StrongConvexOn Q μ f) ↔
      Convex ℝ Q ∧
        ∃ μ > 0,
          ∀ x ∈ Q, ∀ y ∈ Q, ∀ α ∈ Set.Icc (0 : ℝ) 1,
            f (α • x + (1 - α) • y) ≤
              α * f x + (1 - α) * f y -
                (μ / 2) * α * (1 - α) * ‖x - y‖ ^ (2 : ℕ) := by
  constructor
  · rintro ⟨μ, hμ, hf⟩
    refine ⟨hf.1, μ, hμ, ?_⟩
    intro x hx y hy α hα
    simpa [le_sub_iff_add_le, mul_assoc, mul_left_comm, mul_comm] using
      (strongConvexOn_iff_quadratic_jensen_bound hf.1).mp hf hx hy hα
  · rintro ⟨hQ, μ, hμ, hbound⟩
    refine ⟨μ, hμ, ?_⟩
    refine (strongConvexOn_iff_quadratic_jensen_bound hQ).mpr ?_
    intro x y hx hy α hα
    simpa [le_sub_iff_add_le, mul_assoc, mul_left_comm, mul_comm] using
      hbound x hx y hy α hα

end
