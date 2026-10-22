/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_1_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_1_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_1_10
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Algorithm_4_1_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Lemma_4_1_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Theorem_4_1_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient LevelSetNotation CubicRegularizationModelNotation

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-
Theorem 4.1.8 lies in the nonlinear change-of-variables / cubic-regularization rate domain.

This item keeps the proof local because the previously extracted support modules currently do not
elaborate. The proof route remains the same source-faithful route: first derive the transported
one-step cubic comparison, then solve the resulting scalar recurrence.
-/

namespace CubicRegularizationMethod

section NonlinearTransformation

variable {problem : NonlinearConvexTransformation E} {𝓕 : Set E}
variable {stepMap : ℝ → E → E} {L0 : ℝ} {L : NNReal}
variable [HessianLipschitzOn L 𝓕 problem]

local notation "f" => problem
local notation "𝓛₀" => f ⁻¹' Set.Iic (f problem.x0)

/-- Helper for Theorem 4.1.8: one cubic-regularization step cannot increase the transformed
objective, because the current iterate is itself a feasible comparison point for the cubic
subproblem. -/
theorem objective_succ_le_objective
    (method :
      CubicRegularizationMethod
        problem
        stepMap
        L0 (L : ℝ) problem.x0)
    (k : ℕ) :
    f (method (k + 1)) ≤ f (method k) := by
  let M := method.regularization k
  have hmodel :
      EReal.toReal
          (SetConstrainedMinimizationProblem.optimalValue
            (cubicRegularizationProblem f M (method k))) ≤
        cubicRegularizationQuadraticApproximation f M (method k) (method k) := by
    have hM_pos : 0 < M := method.regularization_pos k
    -- Compare the accepted model value with the current iterate.
    simpa [M] using
      (@cubicRegularizationProblem_optimalValue_toReal_le_quadraticApproximation
        E _ _ _ f M (method k) (method k) hM_pos)
  have hstep :
      f (method (k + 1)) ≤
        EReal.toReal
          (SetConstrainedMinimizationProblem.optimalValue
            (cubicRegularizationProblem f M (method k))) := by
    -- Rewrite the accepted trial point as the next iterate.
    simpa [M, method.x_succ k] using method.objective_step_le_value k
  calc
    f (method (k + 1)) ≤
        EReal.toReal
          (SetConstrainedMinimizationProblem.optimalValue
            (cubicRegularizationProblem f M (method k))) := hstep
    _ ≤ cubicRegularizationQuadraticApproximation f M (method k) (method k) := hmodel
    _ = f (method k) := by
      simp [M, cubicRegularizationQuadraticApproximation_apply]

/-- Helper for Theorem 4.1.8: every iterate stays in the initial transformed sublevel set
`𝓛₀`. -/
theorem mem_initial_sublevel
    (method :
      CubicRegularizationMethod
        problem
        stepMap
        L0 (L : ℝ) problem.x0)
    (k : ℕ) :
    method k ∈ 𝓛₀ := by
  induction k with
  | zero =>
      -- The initial iterate is exactly `x₀`.
      change f (method 0) ≤ f problem.x0
      simp [method.x_zero]
  | succ k hk =>
      -- Monotonicity propagates the initial sublevel bound along the trajectory.
      change f (method (k + 1)) ≤ f problem.x0
      exact (method.objective_succ_le_objective k).trans hk

/-- Helper for Theorem 4.1.8: every accepted cubic step satisfies the feasible comparison
estimate against any point of the controlling set `𝓕`. -/
theorem objective_succ_le_feasibleComparison
    (method :
      CubicRegularizationMethod
        problem
        stepMap
        L0 (L : ℝ) problem.x0)
    (hlevel_subset : 𝓛₀ ⊆ 𝓕)
    (k : ℕ) {y : E} (hy : y ∈ 𝓕) :
    f (method (k + 1)) ≤
      f y + ((L : ℝ) / 2) * ‖(y - method k : E)‖ ^ (3 : ℕ) := by
  let M := method.regularization k
  have hxF : method k ∈ 𝓕 := hlevel_subset (method.mem_initial_sublevel k)
  have hcomparison :
      EReal.toReal
          (SetConstrainedMinimizationProblem.optimalValue
            (cubicRegularizationProblem f M (method k))) ≤
        f y + (((L : ℝ) + M) / 6 : ℝ) * ‖(y - method k : E)‖ ^ (3 : ℕ) := by
    -- Compare the minimizing model value with the feasible point `y`.
    simpa [M] using
      cubicRegularizationValue_le_feasibleComparison_of_mem
        (hf := inferInstance)
        (hstep := method.step_isMinOn k)
        (x := method k)
        (y := y)
        hxF
        hy
  have hstep :
      f (method (k + 1)) ≤
        f y + (((L : ℝ) + M) / 6 : ℝ) * ‖(y - method k : E)‖ ^ (3 : ℕ) := by
    have haccept :
        f (method (k + 1)) ≤
          EReal.toReal
            (SetConstrainedMinimizationProblem.optimalValue
              (cubicRegularizationProblem f M (method k))) := by
      -- The accepted trial point realizes the displayed optimal value.
      simpa [M, method.x_succ k] using method.objective_step_le_value k
    exact haccept.trans hcomparison
  have hcoef :
      (((L : ℝ) + M) / 6 : ℝ) ≤ (L : ℝ) / 2 := by
    have hM : M ≤ 2 * (L : ℝ) := by
      simpa [M] using method.regularization_le_two_mul_L k
    nlinarith
  have hpow_nonneg : 0 ≤ ‖(y - method k : E)‖ ^ (3 : ℕ) := by
    positivity
  have hterm :
      (((L : ℝ) + M) / 6 : ℝ) * ‖(y - method k : E)‖ ^ (3 : ℕ) ≤
        ((L : ℝ) / 2) * ‖(y - method k : E)‖ ^ (3 : ℕ) := by
    exact mul_le_mul_of_nonneg_right hcoef hpow_nonneg
  calc
    f (method (k + 1))
        ≤ f y + (((L : ℝ) + M) / 6 : ℝ) * ‖(y - method k : E)‖ ^ (3 : ℕ) := hstep
    _ ≤ f y + ((L : ℝ) / 2) * ‖(y - method k : E)‖ ^ (3 : ℕ) := by
      -- Replace the cubic coefficient by the simpler upper bound `L / 2`.
      simpa [add_assoc, add_left_comm, add_comm] using add_le_add_left hterm (f y)

end NonlinearTransformation

end CubicRegularizationMethod

/-- Helper for Theorem 4.1.8: a nonnegative scalar sequence satisfying the normalized cubic
one-step recurrence has the standard inverse-square decay. -/
lemma inverse_square_rate_of_normalized_cubic_recurrence
    {Δ : ℕ → ℝ} {c : ℝ}
    (hc : 0 < c)
    (hΔ_nonneg : ∀ k : ℕ, 0 ≤ Δ k)
    (hgap0 : Δ 0 ≤ c)
    (hstep_gap :
      ∀ k : ℕ, ∀ α : ℝ, α ∈ Set.Icc (0 : ℝ) 1 →
        Δ (k + 1) ≤ (1 - α) * Δ k + c * ((1 / 3 : ℝ) * α ^ (3 : ℕ))) :
    ∀ k : ℕ,
      Δ k ≤ c / (1 + (k : ℝ) / 3) ^ (2 : ℕ) := by
  let α : ℕ → ℝ := fun k ↦ Real.sqrt (Δ k / c)
  have hΔ_le_c : ∀ k : ℕ, Δ k ≤ c := by
    intro k
    induction k with
    | zero =>
        simpa using hgap0
    | succ k hk =>
        have hα_one : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
          simp
        have hstep_one :
            Δ (k + 1) ≤ c * ((1 / 3 : ℝ) * (1 : ℝ) ^ (3 : ℕ)) := by
          simpa using hstep_gap k 1 hα_one
        have hthird_le_c : c * ((1 / 3 : ℝ) * (1 : ℝ) ^ (3 : ℕ)) ≤ c := by
          nlinarith [hc]
        exact hstep_one.trans hthird_le_c
  have hα_mem : ∀ k : ℕ, α k ∈ Set.Icc (0 : ℝ) 1 := by
    intro k
    refine ⟨?_, ?_⟩
    · simp [α]
    · have hquot_le_one : Δ k / c ≤ 1 := by
        have hscaled : Δ k ≤ 1 * c := by
          simpa using hΔ_le_c k
        exact (div_le_iff₀ hc).2 hscaled
      have hsqrt_le_one : Real.sqrt (Δ k / c) ≤ 1 := by
        apply (Real.sqrt_le_iff).2
        constructor
        · norm_num
        · simpa using hquot_le_one
      simpa [α] using hsqrt_le_one
  have hΔ_eq : ∀ k : ℕ, Δ k = c * α k ^ (2 : ℕ) := by
    intro k
    have hsq : α k ^ (2 : ℕ) = Δ k / c := by
      simp [α, Real.sq_sqrt, div_nonneg (hΔ_nonneg k) hc.le]
    have hmul := congrArg (fun t : ℝ ↦ c * t) hsq
    field_simp [hc.ne'] at hmul
    nlinarith [hmul]
  have hrecurrence :
      ∀ k : ℕ,
        Δ (k + 1) ≤ c * (α k ^ (2 : ℕ) - (2 / 3 : ℝ) * α k ^ (3 : ℕ)) := by
    intro k
    have hstepk := hstep_gap k (α k) (hα_mem k)
    rw [hΔ_eq k] at hstepk
    nlinarith
  have hreciprocal_or_zero :
      ∀ k : ℕ, Δ k = 0 ∨ 1 / α k ≥ 1 + (k : ℝ) / 3 := by
    intro k
    induction k with
    | zero =>
        by_cases hΔ0 : Δ 0 = 0
        · exact Or.inl hΔ0
        · have hα0_nonneg : 0 ≤ α 0 := (hα_mem 0).1
          have hα0_ne : α 0 ≠ 0 := by
            intro hα0_zero
            have hzero : Δ 0 = 0 := by
              rw [hΔ_eq 0, hα0_zero]
              ring
            exact hΔ0 hzero
          have hα0_pos : 0 < α 0 := lt_of_le_of_ne hα0_nonneg (Ne.symm hα0_ne)
          have hone : 1 ≤ 1 / α 0 := by
            simpa using one_div_le_one_div_of_le hα0_pos (hα_mem 0).2
          have hbase : 1 / α 0 ≥ 1 + ((0 : ℕ) : ℝ) / 3 := by
            nlinarith
          exact Or.inr hbase
    | succ k hk =>
        rcases hk with hΔk_zero | hk_recip
        · have hαk_zero : α k = 0 := by
            rw [hΔ_eq k] at hΔk_zero
            have hsq_zero : α k ^ (2 : ℕ) = 0 := by
              nlinarith [hΔk_zero, hc]
            nlinarith [sq_nonneg (α k), hsq_zero]
          have hnext_le_zero : Δ (k + 1) ≤ 0 := by
            have hrec := hrecurrence k
            rw [hαk_zero] at hrec
            simpa using hrec
          exact Or.inl (le_antisymm hnext_le_zero (hΔ_nonneg (k + 1)))
        · have hgrowth :
              α (k + 1) ∈ Set.Icc (0 : ℝ) (α k) ∧
                (Δ (k + 1) = 0 ∨ 1 / α (k + 1) ≥ 1 / α k + 1 / 3) := by
            simpa [α] using
              reciprocal_alpha_growth_of_cubic_step hc (hα_mem k)
                (hΔ_nonneg (k + 1)) (hrecurrence k)
          rcases hgrowth with ⟨_, hgrowth'⟩
          rcases hgrowth' with hΔnext_zero | hnext_recip
          · exact Or.inl hΔnext_zero
          · have hcast :
                (1 + (k : ℝ) / 3) + 1 / 3 = 1 + ((k + 1 : ℕ) : ℝ) / 3 := by
              rw [Nat.cast_add]
              ring
            have hsum :
                1 / α (k + 1) ≥ 1 + ((k + 1 : ℕ) : ℝ) / 3 := by
              nlinarith [hk_recip, hnext_recip, hcast]
            exact Or.inr hsum
  intro k
  rcases hreciprocal_or_zero k with hΔk_zero | hk_recip
  · have hbound_nonneg : 0 ≤ c / (1 + (k : ℝ) / 3) ^ (2 : ℕ) := by
      positivity
    simpa [hΔk_zero] using hbound_nonneg
  · have hαk_nonneg : 0 ≤ α k := (hα_mem k).1
    have hαk_ne : α k ≠ 0 := by
      intro hαk_zero
      have hpositive : (0 : ℝ) < 1 + (k : ℝ) / 3 := by
        positivity
      have hcontr : (0 : ℝ) ≥ 1 + (k : ℝ) / 3 := by
        simpa [hαk_zero] using hk_recip
      linarith
    have hαk_pos : 0 < α k := lt_of_le_of_ne hαk_nonneg (Ne.symm hαk_ne)
    have hs_pos : 0 < 1 + (k : ℝ) / 3 := by
      positivity
    have hsα : (1 + (k : ℝ) / 3) * α k ≤ 1 := by
      have hk_recip' : 1 + (k : ℝ) / 3 ≤ 1 / α k := by
        simpa using hk_recip
      exact (le_div_iff₀ hαk_pos).1 hk_recip'
    have hαk_le : α k ≤ 1 / (1 + (k : ℝ) / 3) := by
      have hsα_comm : α k * (1 + (k : ℝ) / 3) ≤ 1 := by
        simpa [mul_comm] using hsα
      exact (le_div_iff₀ hs_pos).2 hsα_comm
    calc
      Δ k = c * α k ^ (2 : ℕ) := hΔ_eq k
      _ ≤ c * (1 / (1 + (k : ℝ) / 3)) ^ (2 : ℕ) := by
        gcongr
      _ = c / (1 + (k : ℝ) / 3) ^ (2 : ℕ) := by
        have hs_ne : (1 + (k : ℝ) / 3) ≠ 0 := by
          positivity
        field_simp [hs_ne]

section NonlinearTransformationCubicRate

variable (problem : NonlinearConvexTransformation E)
variable (𝓕 : Set E) {stepMap : ℝ → E → E} {L0 : ℝ} {L : NNReal}
variable
  (method :
    CubicRegularizationMethod
      problem
      stepMap
      L0 (L : ℝ) problem.x0)

local notation "f" => problem
local notation "𝓛₀" => f ⁻¹' Set.Iic (f problem.x0)
local notation "Δ" => fun k : ℕ ↦ f (method k) - f problem.xStar
local notation "σD" => problem.sigma * problem.D

variable
  (hlevel_subset : 𝓛₀ ⊆ 𝓕)
  [HessianLipschitzOn L 𝓕 problem]

/-- Helper for Theorem 4.1.8: transporting the cubic comparison point through the nonlinear
change of variables yields the same one-step scalar recurrence as in Theorem 4.1.4, with `D`
replaced by `σ D`. -/
lemma nonlinear_transformation_cubic_gap_succ_le_alpha_step
    (hlevel_subset : 𝓛₀ ⊆ 𝓕)
    (k : ℕ) {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    Δ (k + 1) ≤
      (1 - α) * Δ k + ((L : ℝ) / 2) * α ^ (3 : ℕ) * σD ^ (3 : ℕ) := by
  let uk : E := problem.u (method k)
  let zα : E := AffineMap.lineMap uk problem.uStar α
  let yα : E := problem.u.symm zα
  let S : Set E := (𝓛[problem.φ]((problem.φ (problem.u problem.x0))) : Set E)
  have hσ_nonneg : 0 ≤ problem.sigma := by
    rcases problem.sigma_isGreatest.1 with ⟨w, -, hw⟩
    rw [← hw]
    exact norm_nonneg _
  have hD_nonneg : 0 ≤ problem.D := by
    rcases problem.D_isGreatest.1 with ⟨w, -, hw⟩
    rw [← hw]
    exact norm_nonneg _
  have hσD_nonneg : 0 ≤ σD := mul_nonneg hσ_nonneg hD_nonneg
  have hk_sublevel : method k ∈ 𝓛₀ := method.mem_initial_sublevel k
  have hk_level : f (method k) ≤ f problem.x0 := hk_sublevel
  have huk : uk ∈ S := by
    -- Rewrite the current iterate into image coordinates.
    change problem.φ (problem.u (method k)) ≤ problem.φ (problem.u problem.x0)
    simpa [uk] using hk_level
  have huStar_level :
      problem.φ problem.uStar ≤ problem.φ (problem.u problem.x0) := by
    -- The chosen minimizer of `φ` is below the initial image value.
    have hu0_mem : problem.u problem.x0 ∈ (Set.univ : Set E) := by
      simp
    exact (isMinOn_iff.mp problem.isMinOn_uStar) (problem.u problem.x0) hu0_mem
  have huk_univ : uk ∈ (Set.univ : Set E) := by
    simp
  have huStar_univ : problem.uStar ∈ (Set.univ : Set E) := by
    simp
  have hα_nonneg : 0 ≤ α := hα.1
  have hone_sub_nonneg : 0 ≤ 1 - α := sub_nonneg.mpr hα.2
  have hweights : (1 - α) + α = 1 := by
    ring
  have hconv :
      problem.φ zα ≤
        (1 - α) * problem.φ uk + α * problem.φ problem.uStar := by
    -- Convexity controls `φ` along the image-space segment from `u x_k` to `u*`.
    simpa [uk, zα, AffineMap.lineMap_apply_module, mul_comm, mul_left_comm, mul_assoc] using
      problem.φ_convex.2 huk_univ huStar_univ hone_sub_nonneg hα_nonneg hweights
  have hkφ_level : problem.φ uk ≤ problem.φ (problem.u problem.x0) := by
    simpa [uk] using hk_level
  have hzα_level :
      problem.φ zα ≤ problem.φ (problem.u problem.x0) := by
    have hleft :
        (1 - α) * problem.φ uk ≤ (1 - α) * problem.φ (problem.u problem.x0) := by
      exact mul_le_mul_of_nonneg_left hkφ_level hone_sub_nonneg
    have hright :
        α * problem.φ problem.uStar ≤ α * problem.φ (problem.u problem.x0) := by
      exact mul_le_mul_of_nonneg_left huStar_level hα_nonneg
    calc
      problem.φ zα ≤ (1 - α) * problem.φ uk + α * problem.φ problem.uStar := hconv
      _ ≤ (1 - α) * problem.φ (problem.u problem.x0) + α * problem.φ (problem.u problem.x0) := by
        exact add_le_add hleft hright
      _ = problem.φ (problem.u problem.x0) := by
        ring
  have hyα_sublevel : yα ∈ 𝓛₀ := by
    -- Pull the segment point back through `u⁻¹`.
    change problem yα ≤ problem problem.x0
    simpa [yα, zα] using hzα_level
  have hyαF : yα ∈ 𝓕 := hlevel_subset hyα_sublevel
  have hcomparison :
      f (method (k + 1)) ≤
        f yα + ((L : ℝ) / 2) * ‖(yα - method k : E)‖ ^ (3 : ℕ) := by
    -- Route correction: use the owner-level feasible comparison theorem from this file.
    simpa [yα] using
      method.objective_succ_le_feasibleComparison hlevel_subset k hyαF
  have hyα_eq : f yα = problem.φ zα := by
    simp [yα, zα]
  have hxStar_eq : f problem.xStar = problem.φ problem.uStar := by
    simp [NonlinearConvexTransformation.xStar]
  have hk_eq : f (method k) = problem.φ uk := by
    simp [uk]
  have hobjective :
      f yα - f problem.xStar ≤ (1 - α) * Δ k := by
    -- Convexity bounds the objective part of the transported comparison point.
    calc
      f yα - f problem.xStar = problem.φ zα - problem.φ problem.uStar := by
        rw [hyα_eq, hxStar_eq]
      _ ≤ (1 - α) * (problem.φ uk - problem.φ problem.uStar) := by
        linarith [hconv]
      _ = (1 - α) * (f (method k) - f problem.xStar) := by
        rw [hk_eq, hxStar_eq]
      _ = (1 - α) * Δ k := by
        rfl
  have hs : Convex ℝ S := by
    change Convex ℝ (𝓛[problem.φ]((problem.φ (problem.u problem.x0))) : Set E)
    simpa [Function.comp, Set.preimage, Set.mem_Iic, Set.sep_univ] using
      problem.φ_convex.convex_le (problem.φ (problem.u problem.x0))
  have hzα_mem : zα ∈ S := by
    change problem.φ zα ≤ problem.φ (problem.u problem.x0)
    exact hzα_level
  have hdist :
      ‖(yα - method k : E)‖ ≤ problem.sigma * ‖(zα - uk : E)‖ := by
    -- The derivative bound for `u⁻¹` controls the transported displacement.
    simpa [uk, yα] using
      hs.norm_image_sub_le_of_norm_fderiv_le
        (fun z hz ↦ problem.u_symm_differentiableAt_controllingLevelSet hz)
        (fun z hz ↦ problem.norm_fderiv_u_symm_le_sigma hz)
        huk
        hzα_mem
  have hzα_eq :
      zα = α • (problem.uStar - uk) + uk := by
    -- `lineMap` exposes the displacement from `u x_k` toward `u*`.
    simpa [uk, zα] using AffineMap.lineMap_apply uk problem.uStar α
  have hzα_norm_eq :
      ‖(zα - uk : E)‖ = α * ‖(problem.uStar - uk : E)‖ := by
    rw [hzα_eq]
    simp [norm_smul_of_nonneg, hα_nonneg]
  have huk_radius :
      ‖(problem.uStar - uk : E)‖ ≤ problem.D := by
    -- The current image iterate stays inside the controlling level set.
    simpa [uk, norm_sub_rev] using problem.norm_sub_uStar_le_D huk
  have hzα_norm_le :
      ‖(zα - uk : E)‖ ≤ α * problem.D := by
    rw [hzα_norm_eq]
    exact mul_le_mul_of_nonneg_left huk_radius hα_nonneg
  have hnorm_le :
      ‖(yα - method k : E)‖ ≤ α * σD := by
    calc
      ‖(yα - method k : E)‖ ≤ problem.sigma * ‖(zα - uk : E)‖ := hdist
      _ ≤ problem.sigma * (α * problem.D) := by
        exact mul_le_mul_of_nonneg_left hzα_norm_le hσ_nonneg
      _ = α * σD := by
        ring
  have hcube :
      ((L : ℝ) / 2) * ‖(yα - method k : E)‖ ^ (3 : ℕ) ≤
        ((L : ℝ) / 2) * α ^ (3 : ℕ) * σD ^ (3 : ℕ) := by
    -- Cubing the transported distance bound yields the cubic penalty estimate.
    have hpow :
        ‖(yα - method k : E)‖ ^ (3 : ℕ) ≤ (α * σD) ^ (3 : ℕ) := by
      exact pow_le_pow_left₀ (norm_nonneg _) hnorm_le 3
    have hcoef_nonneg : 0 ≤ (L : ℝ) / 2 := by
      positivity
    have hscaled :
        ((L : ℝ) / 2) * ‖(yα - method k : E)‖ ^ (3 : ℕ) ≤
          ((L : ℝ) / 2) * (α * σD) ^ (3 : ℕ) := by
      exact mul_le_mul_of_nonneg_left hpow hcoef_nonneg
    simpa [mul_pow, mul_assoc, mul_left_comm, mul_comm] using hscaled
  have hstep_gap :
      Δ (k + 1) ≤
        (f yα - f problem.xStar) + ((L : ℝ) / 2) * ‖(yα - method k : E)‖ ^ (3 : ℕ) := by
    -- Subtract the optimal value from the feasible comparison estimate.
    have hsub := sub_le_sub_right hcomparison (f problem.xStar)
    change
      f (method (k + 1)) - f problem.xStar ≤
        (f yα - f problem.xStar) + ((L : ℝ) / 2) * ‖(yα - method k : E)‖ ^ (3 : ℕ)
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsub
  have hsum :
      (f yα - f problem.xStar) + ((L : ℝ) / 2) * ‖(yα - method k : E)‖ ^ (3 : ℕ) ≤
        (1 - α) * Δ k + ((L : ℝ) / 2) * α ^ (3 : ℕ) * σD ^ (3 : ℕ) := by
    exact add_le_add hobjective hcube
  exact hstep_gap.trans hsum

/-- Helper for Theorem 4.1.8: every transformed objective gap above the transported minimizer
`x*` is nonnegative. -/
lemma nonlinear_transformation_objective_gap_nonneg
    (k : ℕ) :
    0 ≤ Δ k := by
  -- The transported minimizer `x*` globally minimizes the transformed objective.
  have hmin : f problem.xStar ≤ f (method k) := by
    have hmethod_mem : method k ∈ (Set.univ : Set E) := by
      simp
    exact (isMinOn_iff.mp problem.isMinOn_xStar) (method k) hmethod_mem
  change 0 ≤ f (method k) - f problem.xStar
  exact sub_nonneg.mpr hmin

/-- Helper for Theorem 4.1.8: the endpoint comparison `α = 1` bounds every next-step gap by the
pure cubic scale `(L / 2) (σ D)^3`. -/
lemma nonlinear_transformation_gap_succ_le_half_sigmaD_cube
    (hlevel_subset : 𝓛₀ ⊆ 𝓕)
    (k : ℕ) :
    Δ (k + 1) ≤ ((L : ℝ) / 2) * σD ^ (3 : ℕ) := by
  have hα_one : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    simp
  -- Specialize the transported recurrence to the endpoint competitor `u*`.
  have hstep :=
    nonlinear_transformation_cubic_gap_succ_le_alpha_step
      (problem := problem)
      (𝓕 := 𝓕)
      (stepMap := stepMap)
      (L0 := L0)
      (L := L)
      (method := method)
      hlevel_subset
      k
      hα_one
  simpa using hstep

-- Proof sketch: use
-- `method.objective_succ_le_feasibleComparison hlevel_subset`
-- for the accepted cubic step, then combine it with the convexity of `φ` along the segment
-- joining `u (method 0)` to `uStar`. Use the distortion bound and the radius bound already
-- encoded by `problem.sigma` and `problem.D` to obtain the same scalar recursion as in
-- Theorem 4.1.4 with `D` replaced by `σ * D`, and then specialize that recursion at `k = 0`.
/-- Theorem 4.1.8 (1): for a nonlinear transformation of a convex objective, if the Hessian of
`problem = problem.φ ∘ problem.u` satisfies the canonical owner
`HessianLipschitzOn L 𝓕 problem` on a comparison set `𝓕` containing the sublevel set
`f ⁻¹' Set.Iic (f x₀)`, and the iterates are generated by the chapter
cubic-regularization method owner, then an initial gap of at least `(3 / 2) L (σ D)^3` implies
that the first-step gap is at most `(1 / 2) L (σ D)^3`. -/
theorem nonlinearTransformation_cubicRegularization_first_gap_le_half_sigmaD_cube
    (hlevel_subset : 𝓛₀ ⊆ 𝓕)
    (hgap0 : Δ 0 ≥ (3 / 2 : ℝ) * (L : ℝ) * σD ^ (3 : ℕ)) :
    Δ 1 ≤ (1 / 2 : ℝ) * (L : ℝ) * σD ^ (3 : ℕ) := by
  have _ := hgap0
  have hcoef :
      ((L : ℝ) / 2) * σD ^ (3 : ℕ) =
        (1 / 2 : ℝ) * (L : ℝ) * σD ^ (3 : ℕ) := by
    ring
  -- The endpoint comparison `α = 1` already gives the textbook first-step bound directly.
  have hstep :=
    nonlinear_transformation_gap_succ_le_half_sigmaD_cube
      (problem := problem)
      (𝓕 := 𝓕)
      (stepMap := stepMap)
      (L0 := L0)
      (L := L)
      (method := method)
      hlevel_subset
      0
  rwa [hcoef] at hstep

-- Proof sketch: use the same derived one-step comparison estimate as in part (1) to obtain, for
-- every `k`, the scalar recurrence from Theorem 4.1.4 with `D` replaced by
-- `problem.sigma * problem.D`. Under the small-gap hypothesis at `k = 0`, solve that recurrence
-- to obtain the inverse-square upper bound for all later iterates.
/-- Theorem 4.1.8 (2): under the same nonlinear-transformation and cubic-regularization
hypotheses, if the initial gap is at most `(3 / 2) L (σ D)^3`, then every iterate satisfies the
inverse-square decay bound
`f(x_k) - f* ≤ 3 L (σ D)^3 / (2 (1 + k / 3)^2)`. -/
theorem nonlinearTransformation_cubicRegularization_gap_le_inverse_square_rate
    (hlevel_subset : 𝓛₀ ⊆ 𝓕)
    (hgap0 : Δ 0 ≤ (3 / 2 : ℝ) * (L : ℝ) * σD ^ (3 : ℕ)) :
    ∀ k : ℕ,
      Δ k ≤
        (3 * (L : ℝ) * σD ^ (3 : ℕ)) /
          (2 * (1 + (k : ℝ) / 3) ^ (2 : ℕ)) := by
  have hσ_nonneg : 0 ≤ problem.sigma := by
    rcases problem.sigma_isGreatest.1 with ⟨w, -, hw⟩
    rw [← hw]
    exact norm_nonneg _
  have hD_nonneg : 0 ≤ problem.D := by
    rcases problem.D_isGreatest.1 with ⟨w, -, hw⟩
    rw [← hw]
    exact norm_nonneg _
  have hσD_nonneg : 0 ≤ σD := mul_nonneg hσ_nonneg hD_nonneg
  set c : ℝ := (3 / 2 : ℝ) * (L : ℝ) * σD ^ (3 : ℕ) with hcdef
  have hc_nonneg : 0 ≤ c := by
    rw [hcdef]
    positivity
  have hnumerator_eq : 3 * (L : ℝ) * σD ^ (3 : ℕ) = 2 * c := by
    rw [hcdef]
    ring
  by_cases hc_zero : c = 0
  · intro k
    have hΔ0_nonneg : 0 ≤ Δ 0 :=
      nonlinear_transformation_objective_gap_nonneg
        (problem := problem)
        (method := method)
        0
    have hΔ0_le_zero : Δ 0 ≤ 0 := by
      have hgap0' : Δ 0 ≤ c := by
        simpa [hcdef] using hgap0
      simpa [hc_zero] using hgap0'
    have hΔ0_zero : Δ 0 = 0 := le_antisymm hΔ0_le_zero hΔ0_nonneg
    have hgap_le_initial : ∀ j : ℕ, Δ j ≤ Δ 0 := by
      intro j
      induction j with
      | zero =>
          exact le_rfl
      | succ j hj =>
          -- Monotonicity of the objective values propagates directly to the gaps.
          calc
            Δ (j + 1) ≤ Δ j := by
              change
                f (method (j + 1)) - f problem.xStar ≤
                  f (method j) - f problem.xStar
              exact sub_le_sub_right (method.objective_succ_le_objective j) (f problem.xStar)
            _ ≤ Δ 0 := hj
    have hΔk_zero : Δ k = 0 := by
      have hk_le_zero : Δ k ≤ 0 := by
        calc
          Δ k ≤ Δ 0 := hgap_le_initial k
          _ = 0 := hΔ0_zero
      exact le_antisymm hk_le_zero
        (nonlinear_transformation_objective_gap_nonneg
          (problem := problem)
          (method := method)
          k)
    have hbound_zero :
        (3 * (L : ℝ) * σD ^ (3 : ℕ)) /
            (2 * (1 + (k : ℝ) / 3) ^ (2 : ℕ)) = 0 := by
      rw [hnumerator_eq, hc_zero]
      simp
    rw [hΔk_zero, hbound_zero]
  · have hc : 0 < c := lt_of_le_of_ne hc_nonneg (Ne.symm hc_zero)
    have hΔ_nonneg : ∀ k : ℕ, 0 ≤ Δ k := by
      intro k
      exact nonlinear_transformation_objective_gap_nonneg
        (problem := problem)
        (method := method)
        k
    intro k
    have hstep_gap :
        ∀ j : ℕ, ∀ α : ℝ, α ∈ Set.Icc (0 : ℝ) 1 →
          Δ (j + 1) ≤ (1 - α) * Δ j + c * ((1 / 3 : ℝ) * α ^ (3 : ℕ)) := by
      intro j α hα
      have hstep :=
        nonlinear_transformation_cubic_gap_succ_le_alpha_step
          (problem := problem)
          (𝓕 := 𝓕)
          (stepMap := stepMap)
          (L0 := L0)
          (L := L)
          (method := method)
          hlevel_subset
          j
          hα
      have hcubic :
          ((L : ℝ) / 2) * α ^ (3 : ℕ) * σD ^ (3 : ℕ) =
            c * ((1 / 3 : ℝ) * α ^ (3 : ℕ)) := by
        rw [hcdef]
        ring
      rw [hcubic] at hstep
      exact hstep
    have hgap0c : Δ 0 ≤ c := by
      simpa [hcdef] using hgap0
    have hmain :=
      inverse_square_rate_of_normalized_cubic_recurrence
        hc
        hΔ_nonneg
        hgap0c
        hstep_gap
    have hmaink : Δ k ≤ c / (1 + (k : ℝ) / 3) ^ (2 : ℕ) := hmain k
    have hrew :
        c / (1 + (k : ℝ) / 3) ^ (2 : ℕ) =
          (3 * (L : ℝ) * σD ^ (3 : ℕ)) /
            (2 * (1 + (k : ℝ) / 3) ^ (2 : ℕ)) := by
      rw [hcdef]
      have hs_ne : (1 + (k : ℝ) / 3) ≠ 0 := by
        positivity
      field_simp [hs_ne]
    rwa [hrew] at hmaink

end NonlinearTransformationCubicRate
