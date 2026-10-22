/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {α : Type u}

/-
Lemma 3.3.6 lies in the chapter's set-constrained scalar parametric max-value-function domain.

Sampled owner declarations:
- `SetConstrainedMinimizationProblem.optimalValue` in `Chap01/Definition_1_3_7`, the project
  owner for constrained extended-real optimal values;
- `SetConstrainedMinimizationProblem.optimalValue_eq_sInf_image`, the canonical expansion of that
  owner as an infimum over the feasible-set image;
- `SetConstrainedMinimizationProblem.optimalValue_le_optimalValue_of_forall_le` and
  `SetConstrainedMinimizationProblem.optimalValue_sub_le_optimalValue_of_forall_sub_le`, the
  comparison owners that transport pointwise objective bounds to optimal-value bounds.

Best owner abstraction:
- source-facing: `setConstrainedParametricObjective f barf t` and
  `parametricValueFunction Q f barf t`;
- core/canonical: `(.mk Q (setConstrainedParametricObjective f barf t) :
  SetConstrainedMinimizationProblem α).optimalValue`;
- bridge/view: the source-facing `sInf` expansions and the shift bounds obtained from the Chapter
  1 comparison lemmas.

Primitive data:
- feasible set `Q`;
- objective `f`;
- constraint surrogate `barf`;
- scalar parameter `t`.

Derived API:
- the pointwise evaluation formula for `setConstrainedParametricObjective`;
- the value-function `sInf` expansions;
- the monotonicity and shift inequalities in the parameter.

This file therefore keeps the two-term max objective as the source-facing owner and routes the
value-level API through the canonical `SetConstrainedMinimizationProblem` comparison theorems
instead of reproving feasible-set infimum facts directly.
-/

/-- The pointwise max-type objective attached to `f`, `barf`, and the scalar parameter `t`,
namely `x ↦ max (f x - t) (barf x)`. This is the primitive owner object underlying the chapter's
parametric value function. -/
def setConstrainedParametricObjective
    (f barf : α → ℝ) (t : ℝ) : α → ℝ :=
  fun x ↦ max (f x - t) (barf x)

/-- Evaluating `setConstrainedParametricObjective f barf t` at `x` gives the defining pointwise
maximum `max (f x - t) (barf x)`. -/
@[simp] theorem setConstrainedParametricObjective_apply
    {f barf : α → ℝ} {t : ℝ} {x : α} :
    setConstrainedParametricObjective f barf t x = max (f x - t) (barf x) :=
  rfl

/-- The parametric value attached to the max-type model `x ↦ max (f x - t) (barf x)` is the
extended-real optimal value of the corresponding constrained problem on `Q`. -/
def parametricValueFunction
    (Q : Set α) (f barf : α → ℝ) (t : ℝ) : EReal :=
  SetConstrainedMinimizationProblem.optimalValue
    (.mk Q (setConstrainedParametricObjective f barf t) : SetConstrainedMinimizationProblem α)

/-- Unfolding `parametricValueFunction` gives the feasible-set image formula over `Q`. -/
theorem parametricValueFunction_eq_sInf_image
    (Q : Set α) (f barf : α → ℝ) (t : ℝ) :
    parametricValueFunction Q f barf t =
      sInf ((fun x ↦ (setConstrainedParametricObjective f barf t x : EReal)) '' Q) := by
  simpa [parametricValueFunction] using
    (SetConstrainedMinimizationProblem.optimalValue_eq_sInf_image
      (.mk Q (setConstrainedParametricObjective f barf t) :
        SetConstrainedMinimizationProblem α))

/-- Unfolding `parametricValueFunction` gives the displayed `sInf` formula over `Q`. -/
theorem parametricValueFunction_def
    (Q : Set α) (f barf : α → ℝ) (t : ℝ) :
    parametricValueFunction Q f barf t =
      sInf (Set.range fun x : Q ↦ (setConstrainedParametricObjective f barf t x : EReal)) := by
  rw [parametricValueFunction_eq_sInf_image]
  refine congrArg sInf ?_
  ext y
  constructor
  · rintro ⟨x, hxQ, rfl⟩
    exact ⟨⟨x, hxQ⟩, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, x.2, rfl⟩

/-- Increasing the parameter by a nonnegative amount can only decrease the pointwise max-type
objective. -/
theorem setConstrainedParametricObjective_shift_le
    (f barf : α → ℝ) (Δ t : ℝ) (hΔ : 0 ≤ Δ) (x : α) :
    setConstrainedParametricObjective f barf (t + Δ) x ≤
      setConstrainedParametricObjective f barf t x := by
  rw [setConstrainedParametricObjective_apply, setConstrainedParametricObjective_apply]
  refine max_le_max ?_ le_rfl
  linarith

/-- Increasing the parameter by `Δ ≥ 0` lowers the pointwise max-type objective by at most `Δ`.
-/
theorem setConstrainedParametricObjective_sub_le_shift
    (f barf : α → ℝ) (Δ t : ℝ) (hΔ : 0 ≤ Δ) (x : α) :
    setConstrainedParametricObjective f barf t x - Δ ≤
      setConstrainedParametricObjective f barf (t + Δ) x := by
  rw [setConstrainedParametricObjective_apply, setConstrainedParametricObjective_apply]
  by_cases h : barf x ≤ f x - t
  · rw [max_eq_left h]
    have hrewrite : f x - t - Δ = f x - (t + Δ) := by ring
    rw [hrewrite]
    exact le_max_left _ _
  · have h' : f x - t ≤ barf x := le_of_not_ge h
    rw [max_eq_right h']
    exact (sub_le_self _ hΔ).trans (le_max_right _ _)

/-- Lemma 3.3.6: for any model `f` and any `Δ ≥ 0`, shifting the parameter from `t` to `t + Δ`
decreases the chapter parametric value by at most `Δ`. The textbook exact value `f^*(t)` and the
approximate value `\hat f_k^*(X; t)` are the corresponding specializations of this owner theorem.
-/
theorem parametricValueFunction_sub_le_shift
    (Q : Set α) (f barf : α → ℝ) (Δ t : ℝ) (hΔ : 0 ≤ Δ) :
    parametricValueFunction Q f barf t - Δ ≤
      parametricValueFunction Q f barf (t + Δ) := by
  simpa [parametricValueFunction] using
    (SetConstrainedMinimizationProblem.optimalValue_sub_le_optimalValue_of_forall_sub_le
      (.mk Q (setConstrainedParametricObjective f barf t) :
        SetConstrainedMinimizationProblem α)
      (.mk Q (setConstrainedParametricObjective f barf (t + Δ)) :
        SetConstrainedMinimizationProblem α)
      rfl
      (fun x _ ↦ setConstrainedParametricObjective_sub_le_shift f barf Δ t hΔ x))

/-- For any model `f` and any `Δ ≥ 0`, shifting the parameter from `t` to `t + Δ` never
increases the parametric value. -/
theorem parametricValueFunction_shift_le
    (Q : Set α) (f barf : α → ℝ) (Δ t : ℝ) (hΔ : 0 ≤ Δ) :
    parametricValueFunction Q f barf (t + Δ) ≤
      parametricValueFunction Q f barf t := by
  simpa [parametricValueFunction] using
    (SetConstrainedMinimizationProblem.optimalValue_le_optimalValue_of_forall_le
      (.mk Q (setConstrainedParametricObjective f barf (t + Δ)) :
        SetConstrainedMinimizationProblem α)
      (.mk Q (setConstrainedParametricObjective f barf t) :
        SetConstrainedMinimizationProblem α)
      rfl
      (fun x _ ↦ setConstrainedParametricObjective_shift_le f barf Δ t hΔ x))

/-- The parametric value function is antitone in the scalar parameter. This is derived owner API:
increasing `t` lowers the pointwise model `x ↦ max (f x - t) (barf x)`, so the infimum over the
fixed feasible set `Q` cannot increase. -/
theorem parametricValueFunction_antitone
    (Q : Set α) (f barf : α → ℝ) :
    Antitone (parametricValueFunction Q f barf) := by
  intro t₁ t₂ ht
  have hΔ : 0 ≤ t₂ - t₁ := sub_nonneg.mpr ht
  have hshift :
      parametricValueFunction Q f barf (t₁ + (t₂ - t₁)) ≤
        parametricValueFunction Q f barf t₁ := by
    exact parametricValueFunction_shift_le Q f barf (t₂ - t₁) t₁ hΔ
  simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
    hshift
