/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_7_11

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
open scoped Gradient

noncomputable section

/- Proposition 6.23 lies in Chapter 6's finite-family log-sum-exp / stable max-shift domain.

Sampled owner-style declarations:
- `logSumExp` and `logSumExp_apply` in `Chap05/Definition_5_4_7_11`, the project owner for the
  unscaled finite log-sum-exp potential on `EuclideanSpace ℝ (Fin n)`;
- `convexOn_log_sum_exp_of_convexOn` in `Chap03/Proposition_3_21`, the project owner theorem for
  finite-family log-sum-exp on a common domain;
- `smoothMaxInnerApproximation` in `Chap07/Definition_7_42`, the later project smoothing owner
  using the canonical positive-parameter surface `{μ : ℝ // 0 < μ}`;
- `logSumExpMaxEigenvalueSmoothing` in `Chap06/Definition_6_47`, the analogous Chapter 6
  positive-parameter log-sum-exp owner for spectral smoothing;
- `entropyRegularizedSimplexObjective_softmax_eq_value` in `Chap06/Lemma_6_4`, a direct
  downstream use of the scaled log-sum-exp owner.

Best owner abstraction:
- source-facing: `coordinateMaximum`, `centeredByCoordinateMaximum`, `η`, and the stable
  shift/gradient identities of Proposition 6.23;
- core/canonical: the finite-family positive-parameter owner `η`;
- bridge/view: `eta_apply`.

Primitive data:
- a finite index type `ι`;
- the positive smoothing parameter `μ : {μ : ℝ // 0 < μ}`;
- the score vector `u : EuclideanSpace ℝ ι`.

Derived API:
- the finite-maximum expansion `coordinateMaximum_def`;
- the coordinate formula `centeredByCoordinateMaximum_apply`;
- the evaluation formula `eta_apply`;
- the shift and gradient invariance theorems.

This file stays at the source-facing Chapter 6 layer. The positive-parameter log-sum-exp owner
`η` is stated at the intrinsic finite-family level, while the stable max-shift specialization
continues to use the coordinate-owner `coordinateMaximum` on the same finite score vectors.
-/

universe v

variable {ι : Type v} [Fintype ι]

/-- The log-sum-exp smoothing potential
`η_μ(u) = μ log (∑ⱼ exp (uⱼ / μ))` on a finite score family for a positive smoothing parameter
`μ`. -/
def η (μ : {μ : ℝ // 0 < μ}) (u : EuclideanSpace ℝ ι) : ℝ :=
  (μ : ℝ) * Real.log (∑ j : ι, Real.exp (u j / (μ : ℝ)))

/-- Evaluating `η μ` at `u` gives the defining log-sum-exp formula
`μ log (∑ⱼ exp (uⱼ / μ))`. -/
theorem eta_apply (μ : {μ : ℝ // 0 < μ}) (u : EuclideanSpace ℝ ι) :
    η μ u = (μ : ℝ) * Real.log (∑ j : ι, Real.exp (u j / (μ : ℝ))) :=
  rfl

section

variable {m : ℕ} [NeZero m]

local notation "U" => EuclideanSpace ℝ (Fin m)

/-- The maximal coordinate of `u ∈ ℝᵐ`. -/
def coordinateMaximum (u : U) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun j : Fin m ↦ u j)

/-- Expanding `coordinateMaximum u` gives the finite maximum of the coordinates of `u`. -/
-- Proof sketch: unfold `coordinateMaximum`; the right-hand side is the defining `Finset.sup'`.
theorem coordinateMaximum_def (u : U) :
    coordinateMaximum u =
      Finset.univ.sup' Finset.univ_nonempty (fun j : Fin m ↦ u j) := rfl

/-- The vector obtained from `u` by subtracting its maximal coordinate from every component. -/
def centeredByCoordinateMaximum (u : U) : U :=
  WithLp.toLp 2 (fun j : Fin m ↦ u j - coordinateMaximum u)

/-- Each coordinate of `centeredByCoordinateMaximum u` is obtained by subtracting
`coordinateMaximum u` from the corresponding coordinate of `u`. -/
-- Proof sketch: unfold `centeredByCoordinateMaximum`; `WithLp.toLp` preserves the displayed
-- coordinate formula.
theorem centeredByCoordinateMaximum_apply (u : U) (j : Fin m) :
    centeredByCoordinateMaximum u j = u j - coordinateMaximum u := rfl

/-- Helper for Proposition 6.23: the constant vector whose coordinates are all equal to `c`. -/
def constantVector (c : ℝ) : U :=
  WithLp.toLp 2 (fun _ : Fin m ↦ c)

/-- Helper for Proposition 6.23: every coordinate of `constantVector c` equals `c`. -/
theorem constantVector_apply (c : ℝ) (j : Fin m) :
    constantVector c j = c := rfl

/-- Helper for Proposition 6.23: the finite exponential denominator in `η μ x` is strictly
positive. -/
theorem eta_sum_exp_pos
    (μ : {μ : ℝ // 0 < μ}) (x : U) :
    0 < ∑ j : Fin m, Real.exp (x j / (μ : ℝ)) := by
  let j0 : Fin m := ⟨0, Nat.pos_of_neZero m⟩
  -- A single strictly positive exponential term keeps the whole finite sum positive.
  refine Finset.sum_pos' ?_ ?_
  · intro j hj
    exact Real.exp_nonneg (x j / (μ : ℝ))
  · exact ⟨j0, Finset.mem_univ j0, Real.exp_pos (x j0 / (μ : ℝ))⟩

/-- Helper for Proposition 6.23: uniformly shifting every coordinate by `c` adds exactly `c` to
`η μ`. -/
theorem eta_add_constant
    (μ : {μ : ℝ // 0 < μ}) (x : U) (c : ℝ) :
    η μ (x + constantVector c) = c + η μ x := by
  have hμ_ne : (μ : ℝ) ≠ 0 := ne_of_gt μ.property
  have hsum_pos : 0 < ∑ j : Fin m, Real.exp (x j / (μ : ℝ)) :=
    eta_sum_exp_pos μ x
  have hshifted_sum :
      ∑ j : Fin m, Real.exp ((x + constantVector c).ofLp j / (μ : ℝ)) =
        Real.exp (c / (μ : ℝ)) * ∑ j : Fin m, Real.exp (x j / (μ : ℝ)) := by
    -- Rewrite each shifted coordinate as `x j + c`, then factor the common exponential term.
    calc
      ∑ j : Fin m, Real.exp ((x + constantVector c).ofLp j / (μ : ℝ))
          = ∑ j : Fin m, Real.exp (c / (μ : ℝ)) * Real.exp (x j / (μ : ℝ)) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              rw [PiLp.add_apply, constantVector_apply, add_div, Real.exp_add, mul_comm]
      _ = Real.exp (c / (μ : ℝ)) * ∑ j : Fin m, Real.exp (x j / (μ : ℝ)) := by
            rw [Finset.mul_sum]
  have hexp_ne : Real.exp (c / (μ : ℝ)) ≠ 0 := (Real.exp_pos _).ne'
  have hmul : (μ : ℝ) * (c / (μ : ℝ)) = c := by
    field_simp [hμ_ne]
  -- Pull the multiplicative exponential factor out of `log`, then simplify `μ * (c / μ)`.
  calc
    η μ (x + constantVector c)
        = (μ : ℝ) *
            Real.log
              (Real.exp (c / (μ : ℝ)) *
                ∑ j : Fin m, Real.exp (x j / (μ : ℝ))) := by
            rw [eta_apply, hshifted_sum]
    _ = (μ : ℝ) *
          (Real.log (Real.exp (c / (μ : ℝ))) +
            Real.log (∑ j : Fin m, Real.exp (x j / (μ : ℝ)))) := by
          rw [Real.log_mul hexp_ne hsum_pos.ne']
    _ = (μ : ℝ) * (c / (μ : ℝ) + Real.log (∑ j : Fin m, Real.exp (x j / (μ : ℝ)))) := by
          rw [Real.log_exp]
    _ = (μ : ℝ) * (c / (μ : ℝ)) +
          (μ : ℝ) * Real.log (∑ j : Fin m, Real.exp (x j / (μ : ℝ))) := by
          ring
    _ = c + (μ : ℝ) * Real.log (∑ j : Fin m, Real.exp (x j / (μ : ℝ))) := by
          rw [hmul]
    _ = c + η μ x := by
          rw [eta_apply]

/-- Helper for Proposition 6.23: the max-centered vector recovers `u` after adding back the
constant vector with value `coordinateMaximum u`. -/
theorem centeredByCoordinateMaximum_add_coordinateMaximum
    (u : U) :
    centeredByCoordinateMaximum u + constantVector (coordinateMaximum u) = u := by
  -- Coordinatewise, subtracting and then re-adding the same maximum restores the original value.
  ext j
  rw [PiLp.add_apply, centeredByCoordinateMaximum_apply, constantVector_apply]
  ring

/-- Helper for Proposition 6.23: the finite log-sum-exp potential `η μ` is differentiable at
every point. -/
theorem eta_differentiableAt
    (μ : {μ : ℝ // 0 < μ}) (x : U) :
    DifferentiableAt ℝ (η μ) x := by
  have hsum_diff :
      DifferentiableAt ℝ
        (fun y : U ↦ ∑ j : Fin m, Real.exp (y j / (μ : ℝ))) x := by
    -- Each summand is an exponential of a linear coordinate functional.
    refine DifferentiableAt.fun_sum ?_
    intro j hj
    have hproj_diff : DifferentiableAt ℝ (fun y : U ↦ y j) x := by
      simpa using ((EuclideanSpace.proj j : U →L[ℝ] ℝ).differentiableAt (x := x))
    have hscaled_diff :
        DifferentiableAt ℝ (fun y : U ↦ (μ : ℝ)⁻¹ * y j) x := by
      simpa using (hproj_diff.const_mul ((μ : ℝ)⁻¹))
    simpa [div_eq_mul_inv, mul_comm] using hscaled_diff.exp
  have hlog_diff :
      DifferentiableAt ℝ
        (fun y : U ↦ Real.log (∑ j : Fin m, Real.exp (y j / (μ : ℝ)))) x := by
    -- The positive exponential sum keeps `Real.log` on its differentiable branch.
    exact hsum_diff.log (eta_sum_exp_pos μ x).ne'
  -- Multiplying by the fixed positive parameter `μ` preserves differentiability.
  simpa [η] using hlog_diff.const_mul (μ : ℝ)

/-- Helper for Proposition 6.23: uniformly shifting every coordinate by `c` leaves the gradient of
`η μ` unchanged. -/
theorem gradient_eta_add_constant
    (μ : {μ : ℝ // 0 < μ}) (x : U) (c : ℝ) :
    ∇ (η μ) (x + constantVector c) = ∇ (η μ) x := by
  have hgrad_shifted :
      HasGradientAt (η μ) (∇ (η μ) (x + constantVector c)) (x + constantVector c) :=
    (eta_differentiableAt μ (x + constantVector c)).hasGradientAt
  have hgrad_base :
      HasGradientAt (η μ) (∇ (η μ) x) x :=
    (eta_differentiableAt μ x).hasGradientAt
  have htranslated :
      HasGradientAt
        (fun y : U ↦ η μ (y + constantVector c))
        (∇ (η μ) (x + constantVector c))
        x := by
    -- Translating the input by a fixed vector does not change the derivative map.
    simpa using
      (show
        HasFDerivAt
          (fun y : U ↦ η μ (y + constantVector c))
          ((InnerProductSpace.toDual ℝ U) (∇ (η μ) (x + constantVector c)))
          x from
        (hasFDerivAt_comp_add_right (f := η μ) (x := x) (a := constantVector c)).2
          hgrad_shifted.hasFDerivAt).hasGradientAt
  have htranslated_from_value :
      HasGradientAt
        (fun y : U ↦ η μ (y + constantVector c))
        (∇ (η μ) x)
        x := by
    -- Replace the translated function by the equal function `y ↦ c + η μ y`.
    have hvalue :
        (fun y : U ↦ η μ (y + constantVector c)) = fun y : U ↦ c + η μ y := by
      funext y
      simpa using eta_add_constant μ y c
    rw [hvalue]
    simpa using (hgrad_base.hasFDerivAt.const_add c).hasGradientAt
  exact HasGradientAt.unique htranslated htranslated_from_value

/-- Proposition 6.23 (1): if `v` is obtained from `u` by subtracting the maximal coordinate
`coordinateMaximum u` from every component, then the log-sum-exp potential satisfies
`η(u) = coordinateMaximum u + η(v)`. -/
-- Proof sketch: factor `exp (coordinateMaximum u / μ)` out of the finite sum
-- `∑ⱼ exp (uⱼ / μ)`, rewrite the remaining summand using
-- `centeredByCoordinateMaximum_apply`, and then apply `Real.log_mul` to pull out the additive
-- term `coordinateMaximum u`.
theorem eta_eq_coordinateMaximum_add_eta_centered
    (μ : {μ : ℝ // 0 < μ}) (u : U) :
    η μ u = coordinateMaximum u + η μ (centeredByCoordinateMaximum u) := by
  -- Rewrite `u` as its centered part plus the uniform maximum shift.
  calc
    η μ u = η μ (centeredByCoordinateMaximum u + constantVector (coordinateMaximum u)) := by
      rw [centeredByCoordinateMaximum_add_coordinateMaximum u]
    _ = coordinateMaximum u + η μ (centeredByCoordinateMaximum u) := by
      simpa using
        eta_add_constant μ (centeredByCoordinateMaximum u) (coordinateMaximum u)

/-- Proposition 6.23 (2): subtracting the same maximal coordinate from every component leaves the
gradient of the log-sum-exp potential unchanged. -/
-- Proof sketch: differentiate the explicit softmax formula for `η`, or differentiate the identity
-- from `eta_eq_coordinateMaximum_add_eta_centered` on regions where the maximizing index is fixed
-- and then use the explicit coordinate formula to remove the local partition.
theorem gradient_eta_eq_gradient_eta_centered
    (μ : {μ : ℝ // 0 < μ}) (u : U) :
    ∇ (η μ) u = ∇ (η μ) (centeredByCoordinateMaximum u) := by
  -- Rewrite `u` as the centered vector plus its maximal-coordinate shift.
  calc
    ∇ (η μ) u = ∇ (η μ) (centeredByCoordinateMaximum u + constantVector (coordinateMaximum u)) := by
      rw [centeredByCoordinateMaximum_add_coordinateMaximum u]
    _ = ∇ (η μ) (centeredByCoordinateMaximum u) := by
      simpa using
        gradient_eta_add_constant μ (centeredByCoordinateMaximum u) (coordinateMaximum u)

end

end
