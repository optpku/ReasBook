/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Proposition_1_10_12
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Theorem_1_10_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open EuclideanSpace Filter
open scoped ConstrainedArgmin EuclideanOrthant

local notation "Λ" => EuclideanSpace ℝ (Fin 1)
local notation "λ⋆" => lagrangianRelaxationExampleLambdaStar
local notation "Λ⋆" => single 0 λ⋆

/-
Primary domain: primal optimality certificates in Lagrangian duality.

Relevant owner declarations sampled before refining this file:
* `lagrangianRelaxationExample : LagrangianProblem _ 1` in `Definition_1_10_3`;
* `lagrangianRelaxationExampleMinimizerTrajectory` in `Proposition_1_10_5`;
* `lagrangianRelaxationExampleLambdaStar_mem_dualFeasibleSet` and
  `lagrangianRelaxationExampleLambdaStar_isMaxOn_dualFeasibleSet` in `Proposition_1_10_12`;
* `LagrangianProblem.globalOptimality_of_dualCertificate` in `Theorem_1_10_4`;
* `lagrangianRelaxationExampleTrajectory_atLambdaStar` in `Proposition_1_10_12`.

Best owner abstraction: the primitive owner remains
`lagrangianRelaxationExample : LagrangianProblem (EuclideanSpace ℝ (Fin 2)) 1`.

Primitive data used here:
* the dual maximizer `lagrangianRelaxationExampleLambdaStar`;
* the owner trajectory `lagrangianRelaxationExampleMinimizerTrajectory`.

Derived API used here:
* `argmin[lagrangianRelaxationExample.feasibleSet] lagrangianRelaxationExample`;
* `lagrangianRelaxationExample.lagrangianMinimizers`;
* `lagrangianRelaxationExampleLambdaStar_mem_dualFeasibleSet`;
* `lagrangianRelaxationExampleLambdaStar_isMaxOn_dualFeasibleSet`;
* `LagrangianProblem.globalOptimality_of_dualCertificate`;
* the coordinate rewrite `lagrangianRelaxationExampleTrajectory_atLambdaStar`.

Source/core/bridge triage:
* source-facing: the textbook point `(2^(-1 / 3), 2^(1 / 3))`;
* core/canonical: `lagrangianRelaxationExample` together with
  `LagrangianProblem.globalOptimality_of_dualCertificate`;
* bridge/view: `lagrangianRelaxationExampleTrajectory_atLambdaStar`, which identifies the owner
  trajectory value with the textbook coordinates.
-/

/-- Helper for Example 1.10.6: a multiplier in `ℝ^1` is determined by its single coordinate. -/
lemma one_dim_multiplier_eq_single (lam : Λ) :
    lam = EuclideanSpace.single 0 (lam 0) := by
  -- Collapse the one-dimensional multiplier to its only coordinate.
  ext i
  fin_cases i
  rfl

/-- Helper for Example 1.10.6: every multiplier in the certificate ball still has coordinate
strictly below the domain boundary `1`. -/
lemma multiplier_coord_lt_one_of_mem_certificate_ball {lam : Λ}
    (hmem : lam ∈ Metric.closedBall Λ⋆ ((1 - λ⋆) / 2) ∩ ℝ₊^1) :
    lam 0 < 1 := by
  rcases hmem with ⟨hball, _⟩
  rw [Metric.mem_closedBall, dist_eq_norm] at hball
  -- Rewrite the one-dimensional distance to a scalar absolute value.
  have habs : |lam 0 - λ⋆| ≤ (1 - λ⋆) / 2 := by
    simpa [show lam - Λ⋆ = EuclideanSpace.single 0 (lam 0 - λ⋆) by
      ext i
      fin_cases i
      rfl, PiLp.norm_single, Real.norm_eq_abs] using hball
  have hupper : lam 0 - λ⋆ ≤ (1 - λ⋆) / 2 := (abs_le.mp habs).2
  linarith [lagrangianRelaxationExampleLambdaStar_lt_one]

/-- Helper for Example 1.10.6: the explicit minimizer trajectory varies continuously at the
dual maximizer. -/
lemma lagrangianRelaxationExampleTrajectory_continuousAt_dualMaximizer :
    ContinuousAt (fun lam : Λ ↦ lagrangianRelaxationExampleMinimizerTrajectory (lam 0)) Λ⋆ := by
  -- Read the unique coordinate of `Λ` through `WithLp.ofLp` so coordinate continuity is explicit.
  have hlam0 : ContinuousAt (fun lam : Λ ↦ lam 0) Λ⋆ := by
    have hofLp : ContinuousAt (fun lam : Λ ↦ WithLp.ofLp lam) Λ⋆ := by
      simpa [Function.comp] using
        (PiLp.continuous_ofLp 2 (fun _ : Fin 1 ↦ ℝ)).continuousAt
    simpa [Function.comp] using ((continuous_apply 0).continuousAt.comp hofLp)
  have hcoord0 : ContinuousAt (fun lam : Λ ↦ (1 : ℝ) - lam 0) Λ⋆ :=
    continuousAt_const.sub hlam0
  have hdenom : 1 - λ⋆ ≠ 0 := by
    linarith [lagrangianRelaxationExampleLambdaStar_lt_one]
  have hcoord1 : ContinuousAt (fun lam : Λ ↦ (1 : ℝ) / (1 - lam 0)) Λ⋆ := by
    -- The second coordinate is continuous because the denominator stays nonzero at `λ⋆`.
    exact ContinuousAt.div continuousAt_const hcoord0 hdenom
  -- Package the continuous scalar coordinates back into the trajectory vector.
  change ContinuousAt
    (fun lam : Λ ↦ WithLp.toLp 2 ![(1 : ℝ) - lam 0, (1 : ℝ) / (1 - lam 0)])
    Λ⋆
  refine (PiLp.continuous_toLp 2 (fun _ : Fin 2 ↦ ℝ)).continuousAt.comp ?_
  rw [continuousAt_pi]
  intro i
  fin_cases i
  · simpa using hcoord0
  · simpa using hcoord1

/-- Helper for Example 1.10.6: the example constraint vector is continuous at the trajectory
point corresponding to the dual maximizer. -/
lemma lagrangianRelaxationExample_constraintVector_continuousAt_trajectory_dualMaximizer :
    ContinuousAt lagrangianRelaxationExample.constraintVector
      (lagrangianRelaxationExampleMinimizerTrajectory λ⋆) := by
  let xStar := lagrangianRelaxationExampleMinimizerTrajectory λ⋆
  -- Expose the two primal coordinates through `WithLp.ofLp`.
  have hx0 : ContinuousAt (fun x : EuclideanSpace ℝ (Fin 2) ↦ x 0) xStar := by
    have hofLp :
        ContinuousAt (fun x : EuclideanSpace ℝ (Fin 2) ↦ WithLp.ofLp x) xStar := by
      simpa [Function.comp] using
        (PiLp.continuous_ofLp 2 (fun _ : Fin 2 ↦ ℝ)).continuousAt
    simpa [Function.comp] using ((continuous_apply 0).continuousAt.comp hofLp)
  have hx1 : ContinuousAt (fun x : EuclideanSpace ℝ (Fin 2) ↦ x 1) xStar := by
    have hofLp :
        ContinuousAt (fun x : EuclideanSpace ℝ (Fin 2) ↦ WithLp.ofLp x) xStar := by
      simpa [Function.comp] using
        (PiLp.continuous_ofLp 2 (fun _ : Fin 2 ↦ ℝ)).continuousAt
    simpa [Function.comp] using ((continuous_apply 1).continuousAt.comp hofLp)
  have hscalar :
      ContinuousAt
        (fun x : EuclideanSpace ℝ (Fin 2) ↦ x 0 - (1 / 2 : ℝ) * x 1 ^ (2 : ℕ))
        xStar := by
    -- The single scalar constraint is a polynomial in the two coordinates.
    exact hx0.sub (continuousAt_const.mul (hx1.pow 2))
  -- Rewrite the packaged constraint vector into its one-dimensional coordinate form.
  rw [show lagrangianRelaxationExample.constraintVector =
      fun x : EuclideanSpace ℝ (Fin 2) ↦
        WithLp.toLp 2 (fun _ : Fin 1 ↦ x 0 - (1 / 2 : ℝ) * x 1 ^ (2 : ℕ)) by
      funext x
      ext i
      fin_cases i
      rfl]
  refine (PiLp.continuous_toLp 2 (fun _ : Fin 1 ↦ ℝ)).continuousAt.comp ?_
  rw [continuousAt_pi]
  intro i
  fin_cases i
  simpa using hscalar

/-- Example 1.10.6: the point `x(λ_*) = (2^(-1 / 3), 2^(1 / 3))` obtained from the explicit
dual maximizer `λ_* = 1 - (1 / 2)^(1 / 3)` is a global optimal solution of the example
constrained problem. -/
theorem lagrangianRelaxationExampleOptimalPoint_isGlobalOptimal :
    WithLp.toLp 2
        ![Real.rpow (2 : ℝ) (-(1 / 3 : ℝ)),
          Real.rpow (2 : ℝ) (1 / 3 : ℝ)] ∈
      argmin[lagrangianRelaxationExample.feasibleSet] lagrangianRelaxationExample := by
  let ε : ℝ := (1 - λ⋆) / 2
  let xPath : Λ → EuclideanSpace ℝ (Fin 2) :=
    fun lam ↦ lagrangianRelaxationExampleMinimizerTrajectory (lam 0)
  have hlamStar : Λ⋆ ∈ lagrangianRelaxationExample.dualFeasibleSet := by
    simpa using lagrangianRelaxationExampleLambdaStar_mem_dualFeasibleSet
  have hmax :
      IsMaxOn lagrangianRelaxationExample.dualFunction
        lagrangianRelaxationExample.dualFeasibleSet Λ⋆ := by
    simpa using lagrangianRelaxationExampleLambdaStar_isMaxOn_dualFeasibleSet
  have hε : 0 < ε := by
    dsimp [ε]
    linarith [lagrangianRelaxationExampleLambdaStar_lt_one]
  have hxPath :
      ∀ ⦃lam : Λ⦄,
        lam ∈ Metric.closedBall Λ⋆ ε ∩ ℝ₊^1 →
          lam ≠ Λ⋆ →
          xPath lam ∈ lagrangianRelaxationExample.lagrangianMinimizers lam := by
    intro lam hmem _
    -- Inside the certificate ball, the scalar multiplier stays in the dual-domain interval.
    have hlam_lt_one : lam 0 < 1 := by
      simpa [ε] using multiplier_coord_lt_one_of_mem_certificate_ball hmem
    -- Rewrite the one-dimensional multiplier into the scalar form expected by Proposition 1.10.5.
    rw [one_dim_multiplier_eq_single lam]
    simpa [xPath] using
      lagrangianRelaxationExampleMinimizerTrajectory_mem_lagrangianMinimizers
        (lam 0) hlam_lt_one
  have hlim :
      Tendsto xPath
        (nhdsWithin Λ⋆
          ((Metric.closedBall Λ⋆ ε ∩ ℝ₊^1) \ {Λ⋆}))
        (nhds (lagrangianRelaxationExampleMinimizerTrajectory λ⋆)) := by
    -- The punctured-neighborhood limit follows from ordinary continuity at `Λ⋆`.
    have hcontPath : ContinuousAt xPath Λ⋆ := by
      simpa [xPath] using lagrangianRelaxationExampleTrajectory_continuousAt_dualMaximizer
    simpa [xPath] using hcontPath.tendsto.mono_left
      (show nhdsWithin Λ⋆ ((Metric.closedBall Λ⋆ ε ∩ ℝ₊^1) \ {Λ⋆}) ≤ nhds Λ⋆ from
        nhdsWithin_le_nhds)
  have hcont :
      ContinuousAt lagrangianRelaxationExample.constraintVector
        (lagrangianRelaxationExampleMinimizerTrajectory λ⋆) := by
    -- The packaged constraint map is continuous because its single coordinate is polynomial.
    simpa using
      lagrangianRelaxationExample_constraintVector_continuousAt_trajectory_dualMaximizer
  have hxStar :
      lagrangianRelaxationExampleMinimizerTrajectory λ⋆ ∈
        lagrangianRelaxationExample.lagrangianMinimizers Λ⋆ := by
    have hsingleton :
        lagrangianRelaxationExample.lagrangianMinimizers Λ⋆ =
          ({lagrangianRelaxationExampleMinimizerTrajectory λ⋆} :
            Set (EuclideanSpace ℝ (Fin 2))) := by
      change
        lagrangianRelaxationExample.lagrangianMinimizers (single 0 λ⋆) =
          ({lagrangianRelaxationExampleMinimizerTrajectory λ⋆} :
            Set (EuclideanSpace ℝ (Fin 2)))
      simpa using
        lagrangianRelaxationExample_lagrangianMinimizers_eq_singleton λ⋆
          lagrangianRelaxationExampleLambdaStar_lt_one
    rw [hsingleton]
    simp
  have hoptimal :
      lagrangianRelaxationExampleMinimizerTrajectory λ⋆ ∈
        argmin[lagrangianRelaxationExample.feasibleSet] lagrangianRelaxationExample := by
    simpa [ε, xPath] using
      lagrangianRelaxationExample.globalOptimality_of_dualCertificate
        xPath
        (lagrangianRelaxationExampleMinimizerTrajectory λ⋆)
        hlamStar hmax hε hxPath hlim hcont hxStar
  simpa [lagrangianRelaxationExampleTrajectory_atLambdaStar] using hoptimal
