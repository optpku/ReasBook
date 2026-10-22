/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_13
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_94

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped ConstrainedArgmin

variable {E : Type u} [SeminormedAddCommGroup E]

/- Theorem 7.20 lies in the localized strictly-positive-objective / constrained minimization
domain.

Sampled owner-style declarations:
- `boundedFeasibleSet` in `Chap07/Definition_7_13`, the chapter owner for the localized feasible
  set `Q ∩ closedBall x₀ R`;
- `argmin[Q] f` in `Chap01/Definition_1_3_3`, the project owner for a constrained minimizer,
  packaging feasibility together with `IsMinOn`;
- `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the project owner for a
  real-valued objective on a feasible set;
- `SetConstrainedMinimizationProblem.optimalValue` and
  `SetConstrainedMinimizationProblem.optimalValue_eq_sInf_image` in `Chap01/Definition_1_3_7`,
  the canonical constrained optimal-value owner and its bridge back to the feasible-value infimum;
- mathlib `LipschitzOnWith`, the canonical owner for a set-restricted Lipschitz bound;
- mathlib `IsMinOn`, the underlying setwise minimality predicate used inside `argmin[Q] f`.

Best owner abstraction:
- source-facing: the localized max objective
  `x ↦ max (shiftedObjective φ x₀ L R x) (L * ‖x - x₀‖)`;
- core/canonical: `boundedFeasibleSet Q x₀ R`,
  `x ∈ argmin[boundedFeasibleSet Q x₀ R] f`,
  `(.mk (boundedFeasibleSet Q x₀ R) (localStrictlyPositiveObjective φ x₀ L R))`,
  `LipschitzOnWith (Real.toNNReal L) φ Q`, and `IsMinOn`;
- bridge/view: the evaluation lemma for the max formula, the in-ball branch equality with
  `shiftedObjective`, and
  `optimalValue_eq_sInf_image`.

Primitive data:
- the feasible set `Q`, objective `φ`, base point `x₀`, and radii constants `L`, `R`;
- the canonical Lipschitz owner `LipschitzOnWith (Real.toNNReal L) φ Q`;
- the constrained problem data `Q` together with the local objective
  `localStrictlyPositiveObjective φ x₀ L R`.

Derived API:
- pointwise lower and positivity bounds for the localized max objective;
- the in-ball identification with the shifted branch `shiftedObjective φ x₀ L R`;
- optimization consequences organized on the localized feasible slice `boundedFeasibleSet Q x₀ R`
  and its Chapter 1 owner optimal value.
-/

/-- The max-type objective obtained from the local minimization model around `x₀`. -/
def localStrictlyPositiveObjective
    (φ : E → ℝ) (x₀ : E) (L R : ℝ) : E → ℝ :=
  fun x ↦ max (shiftedObjective φ x₀ L R x) (L * ‖x - x₀‖)

/-- Evaluating `localStrictlyPositiveObjective φ x₀ L R` at `x` recovers the textbook formula
`max {φ(x) - φ(x₀) + 2LR, L ‖x - x₀‖}`. -/
@[simp]
theorem localStrictlyPositiveObjective_apply
    (φ : E → ℝ) (x₀ x : E) (L R : ℝ) :
    localStrictlyPositiveObjective φ x₀ L R x =
      max (shiftedObjective φ x₀ L R x) (L * ‖x - x₀‖) := by
  simp [localStrictlyPositiveObjective]

/-- If `L * R ≥ 0`, then the value of the local strictly positive objective at the base point `x₀`
is `2LR`. -/
-- Proof sketch: unfold the definition at `x₀`; the norm term vanishes and the remaining maximum is
-- `max (shiftedObjective φ x₀ L R x₀) 0 = 2 * L * R`, using
-- `shiftedObjective_basePoint` and `0 ≤ L * R`.
theorem localStrictlyPositiveObjective_at_basePoint
    (φ : E → ℝ) (x₀ : E) {L R : ℝ} (hLR : 0 ≤ L * R) :
    localStrictlyPositiveObjective φ x₀ L R x₀ = 2 * L * R := by
  -- At the base point, the norm branch vanishes and the shifted branch is exactly `2 * L * R`.
  have h2LR : 0 ≤ 2 * L * R := by
    nlinarith
  rw [localStrictlyPositiveObjective_apply, shiftedObjective_basePoint]
  simp [h2LR]

section LocalStrictlyPositiveObjective

variable {Q : Set E} {φ : E → ℝ} {x₀ : E} {L R : ℝ}

/-- A uniform Lipschitz bound on `φ` over `Q` forces the local objective to be bounded below by
`LR` at every feasible point. -/
-- Proof sketch: use the Lipschitz inequality with `y = x₀` to get
-- `shiftedObjective φ x₀ L R x ≥ 2 * L * R - L * ‖x - x₀‖`, then compare the two arguments of the
-- maximum against the midpoint value `L * R`.
theorem localStrictlyPositiveObjective_lower_bound
    (hx₀ : x₀ ∈ Q) (hL_nonneg : 0 ≤ L)
    (hφ_lipschitz : LipschitzOnWith (Real.toNNReal L) φ Q)
    {x : E} (hx : x ∈ Q) :
    L * R ≤ localStrictlyPositiveObjective φ x₀ L R x := by
  -- First rewrite the Lipschitz control at `(x₀, x)` as a norm inequality.
  have hφ_bound : φ x₀ ≤ φ x + L * ‖x - x₀‖ := by
    simpa [Real.toNNReal_of_nonneg hL_nonneg, dist_eq_norm, norm_sub_rev] using
      hφ_lipschitz.le_add_mul hx₀ hx
  -- This is the lower estimate for the shifted branch that drives the max split.
  have hshift_lower :
      2 * L * R - L * ‖x - x₀‖ ≤ shiftedObjective φ x₀ L R x := by
    rw [shiftedObjective_apply]
    linarith
  -- Split according to which branch of the max is large enough to dominate `L * R`.
  by_cases hRle : R ≤ ‖x - x₀‖
  · have hnorm_lower : L * R ≤ L * ‖x - x₀‖ :=
      mul_le_mul_of_nonneg_left hRle hL_nonneg
    calc
      L * R ≤ L * ‖x - x₀‖ := hnorm_lower
      _ ≤ localStrictlyPositiveObjective φ x₀ L R x := by
        rw [localStrictlyPositiveObjective_apply]
        exact le_max_right _ _
  · have hnorm_le_R : ‖x - x₀‖ ≤ R := le_of_not_ge hRle
    have hnorm_mul_le : L * ‖x - x₀‖ ≤ L * R :=
      mul_le_mul_of_nonneg_left hnorm_le_R hL_nonneg
    have hshift_dominates : L * R ≤ shiftedObjective φ x₀ L R x := by
      linarith
    calc
      L * R ≤ shiftedObjective φ x₀ L R x := hshift_dominates
      _ ≤ localStrictlyPositiveObjective φ x₀ L R x := by
        rw [localStrictlyPositiveObjective_apply]
        exact le_max_left _ _

/-- On the radius-`R` ball around `x₀`, the first branch of the max formula for the local strictly
positive objective dominates the norm branch. -/
-- Proof sketch: use the same Lipschitz lower estimate with `y = x₀`; when `‖x - x₀‖ ≤ R`, the
-- shifted value `shiftedObjective φ x₀ L R x` is at least `L * R`, hence at least
-- `L * ‖x - x₀‖`.
theorem localStrictlyPositiveObjective_eq_shift_of_norm_le
    (hx₀ : x₀ ∈ Q) (hL_nonneg : 0 ≤ L)
    (hφ_lipschitz : LipschitzOnWith (Real.toNNReal L) φ Q)
    {x : E} (hx : x ∈ Q) (hxR : ‖x - x₀‖ ≤ R) :
    localStrictlyPositiveObjective φ x₀ L R x = shiftedObjective φ x₀ L R x := by
  -- Reuse the Lipschitz estimate to show the shifted branch dominates the norm branch on the ball.
  have hφ_bound : φ x₀ ≤ φ x + L * ‖x - x₀‖ := by
    simpa [Real.toNNReal_of_nonneg hL_nonneg, dist_eq_norm, norm_sub_rev] using
      hφ_lipschitz.le_add_mul hx₀ hx
  have hshift_lower :
      2 * L * R - L * ‖x - x₀‖ ≤ shiftedObjective φ x₀ L R x := by
    rw [shiftedObjective_apply]
    linarith
  have hnorm_mul_le : L * ‖x - x₀‖ ≤ L * R :=
    mul_le_mul_of_nonneg_left hxR hL_nonneg
  have hnorm_branch_le : L * ‖x - x₀‖ ≤ shiftedObjective φ x₀ L R x := by
    linarith
  -- Once the second branch is dominated, the max collapses to the shifted branch.
  rw [localStrictlyPositiveObjective_apply, max_eq_left hnorm_branch_le]

-- Proof sketch: apply `localStrictlyPositiveObjective_lower_bound` to the feasible point `x`,
-- then combine `0 < L` and `0 < R` to deduce `0 < L * R`.
/-- Theorem 7.20: if `φ` satisfies the uniform Lipschitz bound
`|φ x - φ y| ≤ L ‖x - y‖` on `Q`, with `x₀ ∈ Q` and `L, R > 0`, then the local objective
`x ↦ max {φ(x) - φ(x₀) + 2LR, L ‖x - x₀‖}` is strictly positive at every feasible point of `Q`. -/
theorem localStrictlyPositiveObjective_strictlyPositive
    (hx₀ : x₀ ∈ Q) (hL : 0 < L) (hR : 0 < R)
    (hφ_lipschitz : LipschitzOnWith (Real.toNNReal L) φ Q)
    {x : E} (hx : x ∈ Q) :
    0 < localStrictlyPositiveObjective φ x₀ L R x := by
  -- The uniform lower bound `L * R ≤ f(x)` becomes strict because both factors are positive.
  have hLR : 0 < L * R := mul_pos hL hR
  exact lt_of_lt_of_le hLR
    (localStrictlyPositiveObjective_lower_bound hx₀ hL.le hφ_lipschitz hx)

/-- A constrained minimizer of `φ` on the bounded feasible set
`Q₁(R) = Q ∩ closedBall x₀ R` is also a constrained minimizer of the local strictly positive
objective on the same bounded feasible set. -/
-- Proof sketch: on `boundedFeasibleSet Q x₀ R`, replace the local objective by
-- `shiftedObjective φ x₀ L R x` using `localStrictlyPositiveObjective_eq_shift_of_norm_le`, so
-- the local minimizer of `φ` also minimizes the shifted objective there.
theorem mem_argmin_localStrictlyPositiveObjective_of_mem_argmin_boundedFeasibleSet
    (hx₀ : x₀ ∈ Q) (hL_nonneg : 0 ≤ L)
    (hφ_lipschitz : LipschitzOnWith (Real.toNNReal L) φ Q)
    {xStar : E} (hxStar : xStar ∈ argmin[boundedFeasibleSet Q x₀ R] φ) :
    xStar ∈ argmin[boundedFeasibleSet Q x₀ R] (localStrictlyPositiveObjective φ x₀ L R) := by
  rcases mem_constrainedArgmin_iff.mp hxStar with ⟨hxStar_mem, hxStar_min⟩
  rcases mem_boundedFeasibleSet_iff.mp hxStar_mem with ⟨hxStar_Q, hxStar_R⟩
  -- The minimizer remains feasible, so it is enough to transfer the pointwise minimizing property.
  refine mem_constrainedArgmin_iff.mpr ⟨hxStar_mem, ?_⟩
  refine isMinOn_iff.mpr ?_
  intro y hy
  rcases mem_boundedFeasibleSet_iff.mp hy with ⟨hy_Q, hy_R⟩
  have hxStar_local :
      localStrictlyPositiveObjective φ x₀ L R xStar = shiftedObjective φ x₀ L R xStar :=
    localStrictlyPositiveObjective_eq_shift_of_norm_le hx₀ hL_nonneg hφ_lipschitz hxStar_Q hxStar_R
  have hy_local :
      localStrictlyPositiveObjective φ x₀ L R y = shiftedObjective φ x₀ L R y :=
    localStrictlyPositiveObjective_eq_shift_of_norm_le hx₀ hL_nonneg hφ_lipschitz hy_Q hy_R
  have hφ_min : φ xStar ≤ φ y := (isMinOn_iff.mp hxStar_min) y hy
  -- On the bounded slice, both objectives differ from `φ` by the same constant shift.
  rw [hxStar_local, hy_local, shiftedObjective_apply, shiftedObjective_apply]
  linarith

/-- The Chapter 1 optimal value of the localized constrained local-objective problem on
`Q₁(R) = boundedFeasibleSet Q x₀ R` is bounded below by `LR`. -/
-- Proof sketch: package `boundedFeasibleSet Q x₀ R` together with the local objective as a
-- `SetConstrainedMinimizationProblem`; then use `optimalValue_eq_sInf_image` to rewrite the owner
-- value as the infimum of the feasible objective image, where
-- `localStrictlyPositiveObjective_lower_bound` gives the needed pointwise lower bound.
theorem localStrictlyPositiveObjective_boundedFeasibleSet_optimalValue_lower_bound
    (hx₀ : x₀ ∈ Q) (hL_nonneg : 0 ≤ L)
    (hφ_lipschitz : LipschitzOnWith (Real.toNNReal L) φ Q) :
    (L * R : EReal) ≤
      (SetConstrainedMinimizationProblem.mk (boundedFeasibleSet Q x₀ R)
        (localStrictlyPositiveObjective φ x₀ L R)).optimalValue := by
  let problem : SetConstrainedMinimizationProblem E :=
    SetConstrainedMinimizationProblem.mk (boundedFeasibleSet Q x₀ R)
      (localStrictlyPositiveObjective φ x₀ L R)
  change (L * R : EReal) ≤ problem.optimalValue
  rw [problem.optimalValue_eq_sInf_image]
  -- Compare the owner infimum with the pointwise lower bound at every feasible image value.
  refine le_sInf ?_
  rintro _ ⟨x, hx, rfl⟩
  rcases mem_boundedFeasibleSet_iff.mp hx with ⟨hxQ, _⟩
  change ((L * R : ℝ) : EReal) ≤
    ((localStrictlyPositiveObjective φ x₀ L R x : ℝ) : EReal)
  exact_mod_cast
    (localStrictlyPositiveObjective_lower_bound (Q := Q) (φ := φ) (x₀ := x₀)
      (L := L) (R := R) hx₀ hL_nonneg hφ_lipschitz hxQ)

/-- If `R ≥ 0` and `L * R ≥ 0`, the Chapter 1 optimal value of the localized constrained
local-objective problem on `Q₁(R) = boundedFeasibleSet Q x₀ R` is bounded above by `2LR`. -/
-- Proof sketch: `x₀ ∈ boundedFeasibleSet Q x₀ R` follows from `x₀ ∈ Q` and `0 ≤ R`, so the owner
-- theorem `optimalValue_le_of_mem_feasibleSet` bounds the optimal value by the objective at `x₀`;
-- then
-- `localStrictlyPositiveObjective_at_basePoint` identifies that value with `2 * L * R`.
theorem localStrictlyPositiveObjective_boundedFeasibleSet_optimalValue_upper_bound
    (hx₀ : x₀ ∈ Q) (hR : 0 ≤ R) (hLR : 0 ≤ L * R) :
    ((SetConstrainedMinimizationProblem.mk (boundedFeasibleSet Q x₀ R)
        (localStrictlyPositiveObjective φ x₀ L R)).optimalValue) ≤
      (2 * L * R : EReal) := by
  let problem : SetConstrainedMinimizationProblem E :=
    SetConstrainedMinimizationProblem.mk (boundedFeasibleSet Q x₀ R)
      (localStrictlyPositiveObjective φ x₀ L R)
  change problem.optimalValue ≤ (2 * L * R : EReal)
  -- The base point is feasible for the localized problem because it lies at distance zero
  -- from itself.
  have hx₀_feasible : x₀ ∈ problem.feasibleSet := by
    change x₀ ∈ boundedFeasibleSet Q x₀ R
    rw [mem_boundedFeasibleSet_iff]
    constructor
    · exact hx₀
    · simpa using hR
  -- Evaluating the objective at the feasible base point gives the owner upper bound.
  have hpoint :
      problem.optimalValue ≤
        ((localStrictlyPositiveObjective φ x₀ L R x₀ : ℝ) : EReal) := by
    simpa [problem] using problem.optimalValue_le_of_mem_feasibleSet hx₀_feasible
  have hbase :
      ((localStrictlyPositiveObjective φ x₀ L R x₀ : ℝ) : EReal) =
        (2 * L * R : EReal) := by
    simpa [mul_assoc] using congrArg (fun t : ℝ ↦ (t : EReal))
      (localStrictlyPositiveObjective_at_basePoint (φ := φ) (x₀ := x₀)
        (L := L) (R := R) hLR)
  calc
    problem.optimalValue ≤ ((localStrictlyPositiveObjective φ x₀ L R x₀ : ℝ) : EReal) := hpoint
    _ = (2 * L * R : EReal) := hbase

end LocalStrictlyPositiveObjective
