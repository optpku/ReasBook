/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Algorithm_2_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Algorithm_2_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_17
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Lemma_2_10
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_20

-- Declarations for this item will be appended below by the statement pipeline.

open scoped StrongConvexSmooth

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Primary domain: strongly convex type-II accelerated optimal-method rates on a real Hilbert
space.

Owner declarations sampled before refining this file:
* `GeneralOptimalMethodScheme` in `Algorithm_2_2` owns the optimal-method trajectory and its
  canonical scalar sequences;
* `optimal_method_alpha0_initial_curvature`,
  `optimal_method_alpha0_initial_curvature_mem_Ioc` in `Algorithm_2_4` own the intrinsic map
  `α₀ ↦ γ₀` and the source-to-owner interval bridge;
* `optimal_method_hyperbolic_suboptimality_le_of_mem_Ioc` in `Theorem_2_20` owns the
  hyperbolic objective-gap estimate for the owner method once
  `γ₀ ∈ (μ, 3L + μ]`;
* `optimal_method_quadratic_suboptimality_le_of_mem_Ioc` in `Theorem_2_20` owns the quadratic
  objective-gap estimate for the same owner method under the same interval hypothesis on `γ₀`.

Best owner abstraction: the public object here is the owner method
`method : GeneralOptimalMethodScheme ... γ₀` with
`γ₀ = optimal_method_alpha0_initial_curvature μ L α₀`. The admissible interval for `α₀` is the
source-facing hypothesis, while the interval condition on `γ₀` and the resulting rate bounds are
derived owner API.

Primitive data:
* the source-facing objective hypothesis `f ∈ 𝓢[μ, L]¹¹`;
* the admissible parameter `α₀`;
* a minimizer `xStar`;
* the owner method started from the induced curvature `γ₀`.

Derived API:
* the internal bridge from the admissible `α₀` range to the owner interval
  `γ₀ ∈ (μ, 3L + μ]`;
* the owner hyperbolic objective-gap estimate;
* the owner quadratic objective-gap estimate. -/

variable {μ L : ℝ}

local notation "qf" => q[μ, L]
local notation "αRange" =>
  Set.Ioc (Real.sqrt qf) (constantStepSchemeIIAlphaUpper qf)

section OptimalMethodAlpha0Rates

variable {f : E → ℝ}
variable (α0 : ℝ)
local notation "γ0" => optimal_method_alpha0_initial_curvature μ L α0
variable (xStar : E)
variable {x0 : E}

/-- Helper for Theorem 2.21: the admissible `α₀` range induces the owner interval
condition `γ₀ ∈ (μ, 3L + μ]`. -/
private theorem gamma0_mem_Ioc
    (hf : f ∈ 𝓢[μ, L]¹¹)
    (hα0 : α0 ∈ αRange)
    (method : GeneralOptimalMethodScheme f L μ x0 γ0) :
    γ0 ∈ Set.Ioc μ (3 * L + μ) :=
  -- This is the source-to-owner bridge: convert the textbook `α₀` hypothesis into the exact
  -- curvature interval required by the owner theorems from Theorem 2.20.
  optimal_method_alpha0_initial_curvature_mem_Ioc
    (IsStrongConvexSmoothObjective.mu_pos (mem_S11_iff.mp hf))
    method.L_pos hα0

/-- Theorem 2.21: for a smooth `μ`-strongly convex objective on a real Hilbert space, the
optimal-method trajectory started from the parameter `α₀` in the stated admissible range
satisfies the displayed hyperbolic upper bound on the objective gap. -/
-- Proof sketch: use the owner bridge
-- `optimal_method_alpha0_initial_curvature_mem_Ioc
--   (IsStrongConvexSmoothObjective.mu_pos hf') method.L_pos hα0` to place
-- `γ₀` in `(μ, 3L + μ]`, then apply the owner rate theorem
-- `optimal_method_hyperbolic_suboptimality_le_of_mem_Ioc`.
theorem optimal_method_alpha0_hyperbolic_objective_gap_le
    (hf : f ∈ 𝓢[μ, L]¹¹)
    (hα0 : α0 ∈ αRange)
    (hxStar : IsMinOn f Set.univ xStar)
    (method : GeneralOptimalMethodScheme f L μ x0 γ0)
    (k : ℕ) :
    f (method k) - f xStar ≤
      (4 * μ *
        (f x0 - f xStar + (γ0 / 2) * ‖x0 - xStar‖ ^ (2 : ℕ))) /
        ((γ0 - μ) *
          (Real.exp (((k + 1 : ℝ) / 2) * Real.sqrt qf) -
            Real.exp (-(((k + 1 : ℝ) / 2) * Real.sqrt qf))) ^
            (2 : ℕ)) := by
  -- First place the induced curvature `γ₀` in the owner interval from Theorem 2.20.
  have hγ0 : γ0 ∈ Set.Ioc μ (3 * L + μ) := gamma0_mem_Ioc α0 hf hα0 method
  -- Then the owner hyperbolic estimate applies directly; `method.x_zero` identifies the initial
  -- point with the source-facing `x0`.
  simpa [method.x_zero] using
    optimal_method_hyperbolic_suboptimality_le_of_mem_Ioc
      method hf hxStar hγ0 k

/-- Under the same admissible choice of `α₀`, the hyperbolic estimate yields the simpler
quadratic `O((k + 1)⁻²)` upper bound on the objective gap. -/
-- Proof sketch: use the same bridge `α₀ ↦ γ₀ ∈ (μ, 3L + μ]` and apply the owner quadratic rate
-- theorem `optimal_method_quadratic_suboptimality_le_of_mem_Ioc`.
theorem optimal_method_alpha0_quadratic_objective_gap_le
    (hf : f ∈ 𝓢[μ, L]¹¹)
    (hα0 : α0 ∈ αRange)
    (hxStar : IsMinOn f Set.univ xStar)
    (method : GeneralOptimalMethodScheme f L μ x0 γ0)
    (k : ℕ) :
    f (method k) - f xStar ≤
      (4 * L / ((γ0 - μ) * (k + 1 : ℝ) ^ (2 : ℕ))) *
        (f x0 - f xStar + (γ0 / 2) * ‖x0 - xStar‖ ^ (2 : ℕ)) := by
  -- Reuse the same bridge from the admissible `α₀` hypothesis to the owner curvature interval.
  have hγ0 : γ0 ∈ Set.Ioc μ (3 * L + μ) := gamma0_mem_Ioc α0 hf hα0 method
  -- The quadratic owner estimate is now immediate, with the same normalization at time zero.
  simpa [method.x_zero] using
    optimal_method_quadratic_suboptimality_le_of_mem_Ioc
      method hf hxStar hγ0 k

end OptimalMethodAlpha0Rates

end
