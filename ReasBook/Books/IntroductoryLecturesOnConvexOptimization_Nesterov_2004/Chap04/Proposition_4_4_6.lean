/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.ModifiedGaussNewtonValueFunction
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.ModifiedGaussNewtonSecantBounds

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Set
open scoped ConvexAnalysis
open scoped ModifiedGaussNewtonStep.ModifiedGaussNewtonStepWholeSpaceNotation

universe u

variable {E₁ : Type u} [NormedAddCommGroup E₁]

/-- Concavity statement from Proposition 4.4.6: if for each positive `M` a whole-space
modified Gauss--Newton minimizer is
chosen, then the canonical interval owner for `f_M(x)` is concave in the regularization
parameter `M` on `(0, ∞)`. The step-based textbook value remains available via
`modifiedGaussNewtonOptimalValue_eq_modelValueAtUniv`. -/
-- Proof sketch: first show the canonical owner value is finite on `(0, ∞)` using the chosen
-- minimizers `step M`; then apply
-- `modifiedGaussNewtonOptimalValueAt_concaveInRegularization` and restrict the resulting
-- concavity statement to the canonical interval owner.
theorem modifiedGaussNewtonOptimalValue_concaveInRegularization
    {ψ : E₁ → E₁ → ℝ} {x : E₁}
    (step : (M : Ioi (0 : ℝ)) → ModifiedGaussNewtonStep ψ Set.univ M.1) :
    ConcaveOn ℝ (Ioi (0 : ℝ))
      (extendedRealRealPart (modifiedGaussNewtonOptimalValueAt ψ x)) := by
  apply modifiedGaussNewtonOptimalValueAt_concaveInRegularization
  intro M hM
  exact modifiedGaussNewtonOptimalValueAt_mem_dom_of_step (step ⟨M, hM⟩) x

/-- Helper for Proposition 4.4.6: if two affine secant bounds share the same base value and
positive slope gap, then the slope coefficients inherit the corresponding order. -/
lemma le_of_add_mul_le_add_mul_of_pos
    {A B₁ B₂ Δ : ℝ}
    (hΔ : 0 < Δ)
    (hbound : A + Δ * B₁ ≤ A + Δ * B₂) :
    B₁ ≤ B₂ := by
  -- Cancel the shared affine offset, then cancel the positive scalar gap.
  have hmul : Δ * B₁ ≤ Δ * B₂ := (add_le_add_iff_left A).mp hbound
  exact le_of_mul_le_mul_left hmul hΔ

/-- Helper for Proposition 4.4.6: if `step₁` and `step₂` minimize the modified Gauss--Newton
models at parameters `M₁ < M₂`, then the residual-square term `(1 / 2) r_M(x)^2` decreases from
`M₁` to `M₂`. -/
lemma residualSqHalf_antitone_of_steps
    {ψ : E₁ → E₁ → ℝ} {x : E₁} {M₁ M₂ : ℝ}
    (step₁ : ModifiedGaussNewtonStep ψ Set.univ M₁)
    (step₂ : ModifiedGaussNewtonStep ψ Set.univ M₂)
    (hLt : M₁ < M₂) :
    (1 / 2 : ℝ) * (r[step₂](x)) ^ (2 : ℕ) ≤
      (1 / 2 : ℝ) * (r[step₁](x)) ^ (2 : ℕ) := by
  -- Reuse the imported secant bounds directly instead of re-expanding the quadratic objective.
  rcases modifiedGaussNewton_secant_bounds_of_steps (step₁ := step₁) (step₂ := step₂)
    with ⟨hlower, hupper⟩
  -- Strictly increasing regularization makes the secant coefficient positive.
  have hcoeff_pos : 0 < ((M₂ - M₁) / 2 : ℝ) := by
    exact div_pos (sub_pos.mpr hLt) (by norm_num)
  -- The two secant bounds differ only in the residual-square coefficient, so the positive gap
  -- can be cancelled.
  have hsq :
      (r[step₂](x)) ^ (2 : ℕ) ≤ (r[step₁](x)) ^ (2 : ℕ) := by
    exact le_of_add_mul_le_add_mul_of_pos hcoeff_pos (hlower.trans hupper)
  have hhalf : 0 ≤ (1 / 2 : ℝ) := by
    norm_num
  -- Multiply the residual-square comparison by the nonnegative factor `1 / 2`.
  exact mul_le_mul_of_nonneg_left hsq hhalf

-- Proof sketch: compare the canonical owner values at `M₁` and `M₂` against the opposite
-- endpoint minimizers. The same affine slice in `M` then gives two bounds on the secant slope of
-- `f_M(x)`, and cancelling the positive factor `M₂ - M₁` yields the monotonicity of
-- `(1 / 2) r_M(x)^2`.
/-- Proposition 4.4.6: if a whole-space modified Gauss--Newton minimizer is
chosen for each positive regularization parameter, then the source-facing residual quantity
`(1 / 2) r_M(x)^2` is decreasing in `M` on `(0, ∞)`. The proof uses the source-faithful
minimum-of-affine comparison at two parameters rather than exposing any extra derivative bridge as
public API. -/
theorem antitone_modifiedGaussNewtonResidualSqHalf
    {ψ : E₁ → E₁ → ℝ} {x : E₁}
    (step : (M : Ioi (0 : ℝ)) → ModifiedGaussNewtonStep ψ Set.univ M.1) :
    Antitone
      (fun M : Ioi (0 : ℝ) ↦
        (1 / 2 : ℝ) * (r[(step M)](x)) ^ (2 : ℕ)) :=
by
  intro M₁ M₂ hM
  rcases lt_or_eq_of_le hM with hLt | hEq
  · exact residualSqHalf_antitone_of_steps (step M₁) (step M₂) hLt
  · subst hEq
    exact le_rfl

end
