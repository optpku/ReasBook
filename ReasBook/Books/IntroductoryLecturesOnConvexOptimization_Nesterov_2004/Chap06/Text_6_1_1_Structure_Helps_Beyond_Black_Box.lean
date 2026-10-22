/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_34
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Text_6_1_1_Complexity_Insight

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u}

/- Text 6.1.1 lies in the chapter's surrogate-smoothing / oracle-complexity bridge domain.

Sampled owner-style declarations:
* `IsApproximateSolution` in `Chap03/Definition_3_34`, the chapter's source-facing owner for an
  `ε`-accurate unconstrained solution relative to a chosen minimizer `xStar`;
* `isApproximateSolution_iff_isApproximateMinimizer` in `Chap03/Definition_3_34`, the canonical
  bridge from that source-facing owner to the Chapter 1 approximate-minimizer API on
  `SetConstrainedMinimizationProblem.unconstrained f`;
* mathlib `IsMinOn`, the canonical owner of exact minimizers on `Set.univ`;
* `fastGradient_oracleComplexity_le_const_div_epsilon_of_smoothApproximation` in
  `Text_6_1_1_Complexity_Insight`, the Chapter 6 owner for the scalar `ε⁻¹` oracle bound.

Best owner abstraction:
* source-facing: the statement that a structured smoothing scheme yields a genuine Chapter 3
  `IsApproximateSolution f xStar ε x` once `xStar` is fixed as an exact minimizer of `f`, together
  with an explicit oracle bound;
* core/canonical: `IsApproximateSolution`, the surrogate minimizer owner
  `IsMinOn fμ Set.univ xμStar`, and the imported scalar oracle-complexity theorem;
* bridge/view: the transfer from surrogate suboptimality to the raw objective-gap inequality
  `f x - f xStar ≤ ε`, and then from that inequality to the Chapter 3 approximate-solution owner
  via an exact minimizer of `f`.

Primitive data:
* the surrogate minimizer witness `hxμStar : IsMinOn fμ Set.univ xμStar`;
* the lower and upper approximation inequalities relating `f` and `fμ`;
* the surrogate suboptimality estimate at `x`;
* the scale choice `cμ * ε ≤ μ`, the Lipschitz-growth bound `Lμ ≤ CL / μ`, and the input oracle
  estimate.

Derived API:
* the raw suboptimality estimate `f x - f xStar ≤ ε` against an arbitrary comparison point;
* `IsApproximateSolution f xStar ε x` once `xStar` is also assumed to be an exact minimizer of
  `f`;
* the explicit inverse-`ε` oracle bound from the imported scalar owner theorem.

The file therefore stays at the bridge layer: it does not introduce a parallel smoothing package,
and it keeps only the primitive assumptions actually needed to derive the raw suboptimality,
approximate-solution, and complexity conclusions.
-/

-- Proof sketch: compare the original objective and the smoothed surrogate at `x` and at a
-- comparison point `xStar`. The lower approximation bound gives
-- `f x ≤ fμ x + ε / 2`, the surrogate suboptimality gives
-- `fμ x ≤ fμ xμStar + ε / 2`, the minimizer property of `xμStar` and the upper approximation bound
-- give `fμ xμStar ≤ fμ xStar ≤ f xStar`, and rearranging yields the raw objective-gap estimate
-- `f x - f xStar ≤ ε`.
/-- If the smoothed surrogate approximates the original objective within `ε / 2` from below and
never exceeds it, then an `ε / 2`-accurate point for the surrogate relative to an exact smoothed
minimizer has original objective value at most `ε` above any chosen comparison point `xStar`. -/
theorem sub_le_epsilon_of_smoothedObjective_suboptimality
    {f fμ : E → ℝ} {x xStar xμStar : E} {ε : ℝ}
    (hxμStar : IsMinOn fμ Set.univ xμStar)
    (happrox_lower : ∀ z : E, f z ≤ fμ z + ε / 2)
    (happrox_upper : ∀ z : E, fμ z ≤ f z)
    (hstructured_step : fμ x ≤ fμ xμStar + ε / 2) :
    f x - f xStar ≤ ε := by
  have hxμStar_le : fμ xμStar ≤ fμ xStar := (isMinOn_univ_iff.mp hxμStar) xStar
  linarith [happrox_lower x, hstructured_step, hxμStar_le, happrox_upper xStar]

-- Proof sketch: first derive the raw objective-gap estimate from
-- `sub_le_epsilon_of_smoothedObjective_suboptimality`, then use the exact minimizer hypothesis on
-- `xStar` to convert that inequality to the genuine Chapter 3 approximate-solution owner.
/-- If `xStar` is an exact minimizer of `f`, the smoothed-surrogate suboptimality estimate above
upgrades to the genuine Chapter 3 statement that `x` is an `ε`-approximate solution of `f`
relative to `xStar`. -/
theorem isApproximateSolution_of_smoothedObjective_suboptimality
    {f fμ : E → ℝ} {x xStar xμStar : E} {ε : ℝ}
    (hxStar : IsMinOn f Set.univ xStar)
    (hxμStar : IsMinOn fμ Set.univ xμStar)
    (happrox_lower : ∀ z : E, f z ≤ fμ z + ε / 2)
    (happrox_upper : ∀ z : E, fμ z ≤ f z)
    (hstructured_step : fμ x ≤ fμ xμStar + ε / 2) :
    IsApproximateSolution f xStar ε x := by
  rw [isApproximateSolution_iff_isApproximateMinimizer hxStar]
  exact
    (SetConstrainedMinimizationProblem.unconstrained_isApproximateMinimizer_iff_sub_le
      f hxStar ε).2
      (sub_le_epsilon_of_smoothedObjective_suboptimality
        hxμStar happrox_lower happrox_upper hstructured_step)

-- Proof sketch: the approximation assumptions transfer `ε / 2` surrogate accuracy to the Chapter
-- 6 raw objective-gap estimate by `sub_le_epsilon_of_smoothedObjective_suboptimality`. For
-- the oracle bound, combine
-- `Lμ ≤ CL / μ` with the scale choice `μ ≥ cμ * ε` and positivity of `ε` to get
-- `Lμ / (ε / 2) ≤ (2 * CL / cμ) / ε^2`; taking square roots and multiplying by `CF` yields the
-- displayed `1 / ε` estimate.
/-- Text 6.1.1-Structure Helps Beyond Black-Box: once an objective admits a structured smoothing
scheme whose surrogate `f_μ` lies between `f` and `f + ε / 2`, whose gradient Lipschitz constant
satisfies `L_μ ≤ C_L / μ`, and whose smoothing parameter is chosen on the scale `μ ≳ ε`, any
fast-gradient method that solves the surrogate to accuracy `ε / 2` produces a point whose
original objective value is at most `ε` above any chosen comparison point `xStar`, with oracle
complexity bounded by a constant multiple of `ε⁻¹`. -/
theorem structured_smoothing_yields_suboptimality_with_inv_epsilon_oracle_bound
    {f fμ : E → ℝ} {x xStar xμStar : E}
    {ε μ Lμ CL CF cμ : ℝ} {N : ℕ}
    (hε : 0 < ε)
    (hcμ : 0 < cμ)
    (hCF : 0 ≤ CF)
    (hxμStar : IsMinOn fμ Set.univ xμStar)
    (happrox_lower : ∀ z : E, f z ≤ fμ z + ε / 2)
    (happrox_upper : ∀ z : E, fμ z ≤ f z)
    (hμ : cμ * ε ≤ μ)
    (hLμ : Lμ ≤ CL / μ)
    (hstructured_step : fμ x ≤ fμ xμStar + ε / 2)
    (horacle : (N : ℝ) ≤ CF * Real.sqrt (Lμ / (ε / 2))) :
    f x - f xStar ≤ ε ∧
      (N : ℝ) ≤ (CF * Real.sqrt (2 * CL / cμ)) / ε := by
  refine ⟨?_, ?_⟩
  · exact
      sub_le_epsilon_of_smoothedObjective_suboptimality hxμStar
        happrox_lower happrox_upper hstructured_step
  · have horacle' : (N : ℝ) ≤ CF * Real.sqrt ((2 * Lμ) / ε) := by
      have hε_ne : ε ≠ 0 := ne_of_gt hε
      have hrewrite : Lμ / (ε / 2) = (2 * Lμ) / ε := by
        field_simp [hε_ne]
      simpa [hrewrite] using horacle
    have hLμ' : 2 * Lμ ≤ (2 * CL) / μ := by
      have hscaled := mul_le_mul_of_nonneg_left hLμ (show 0 ≤ (2 : ℝ) by positivity)
      simpa [two_mul, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hscaled
    simpa [two_mul, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      fastGradient_oracleComplexity_le_const_div_epsilon_of_smoothApproximation
        hε hcμ hCF hμ hLμ' horacle'

-- Proof sketch: combine the raw objective-gap theorem
-- `structured_smoothing_yields_suboptimality_with_inv_epsilon_oracle_bound` with the exact
-- minimizer bridge for `IsApproximateSolution`.
/-- Text 6.1.1-Structure Helps Beyond Black-Box: if `xStar` is an exact minimizer of `f`, then
structured smoothing turns the surrogate `ε / 2`-accuracy guarantee into the genuine Chapter 3
statement `IsApproximateSolution f xStar ε x`, while keeping the oracle complexity bounded by a
constant multiple of `ε⁻¹`. -/
theorem structured_smoothing_yields_approximateSolution_with_inv_epsilon_oracle_bound
    {f fμ : E → ℝ} {x xStar xμStar : E}
    {ε μ Lμ CL CF cμ : ℝ} {N : ℕ}
    (hxStar : IsMinOn f Set.univ xStar)
    (hε : 0 < ε)
    (hcμ : 0 < cμ)
    (hCF : 0 ≤ CF)
    (hxμStar : IsMinOn fμ Set.univ xμStar)
    (happrox_lower : ∀ z : E, f z ≤ fμ z + ε / 2)
    (happrox_upper : ∀ z : E, fμ z ≤ f z)
    (hμ : cμ * ε ≤ μ)
    (hLμ : Lμ ≤ CL / μ)
    (hstructured_step : fμ x ≤ fμ xμStar + ε / 2)
    (horacle : (N : ℝ) ≤ CF * Real.sqrt (Lμ / (ε / 2))) :
    IsApproximateSolution f xStar ε x ∧
      (N : ℝ) ≤ (CF * Real.sqrt (2 * CL / cμ)) / ε := by
  rcases structured_smoothing_yields_suboptimality_with_inv_epsilon_oracle_bound
      hε hcμ hCF hxμStar happrox_lower happrox_upper hμ hLμ hstructured_step horacle with
    ⟨hsub, horacle_bound⟩
  refine ⟨?_, horacle_bound⟩
  rw [isApproximateSolution_iff_isApproximateMinimizer hxStar]
  exact
    (SetConstrainedMinimizationProblem.unconstrained_isApproximateMinimizer_iff_sub_le
      f hxStar ε).2 hsub

end
