/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_1_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_1_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_1_10
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Algorithm_4_1_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Lemma_4_1_6
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Theorem_4_1_8
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_30

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient LevelSetNotation

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Theorem 4.1.9 lies in the nonlinear-transformation / strong-convex cubic-regularization rate
domain.

Sampled owner declarations:
* `NonlinearConvexTransformation` in `Definition_4_1_10`, the source-facing owner for the
  transformed objective, transported minimizer, and level-set constants `σ` and `D`;
* `CubicRegularizationMethod` in `Algorithm_4_1_5`, the chapter owner for the iterate sequence
  and regularization schedule;
* `HessianLipschitzOn` in `Definition_4_1_2`, the canonical chapter owner for local convex
  Hessian-Lipschitz control on a comparison set;
* `CubicRegularizationMethod.objective_succ_le_feasibleComparison` in `Theorem_4_1_8`, the
  owner-level one-step feasible comparison estimate used by the transformed cubic-rate bounds.

Source/core/bridge triage:
* source-facing: the first-phase decay, termination, and second-phase superlinear estimates for a
  strongly convex transformed objective;
* core/canonical: `NonlinearConvexTransformation`, `CubicRegularizationMethod`, and
  `StrongConvexOn Set.univ μ problem.φ`;
* bridge/view: the scalar threshold `\tilde ω`.

Primitive data:
* the transformed problem `problem`;
* the comparison set `𝓕` together with the sublevel containment hypothesis from Theorem 4.1.8;
* the canonical smoothness owner `HessianLipschitzOn L 𝓕 problem.objective`;
* the cubic-regularization method `method`;
* the strong-convexity parameter `μ > 0`.

Derived API:
* the threshold `\tilde ω = μ^3 / (8 σ^6 L^2)`;
* the objective gaps `f(x_k) - f(x*)`;
* the owner-level one-step feasible comparison estimate from
  `CubicRegularizationMethod.objective_succ_le_feasibleComparison`;
* the phase-wise gap estimates below.

The monotonicity needed to keep the trajectory inside the initial sublevel set is already derived
from the chapter owner `CubicRegularizationMethod`, and Theorem 4.1.8 already upgrades the
one-step feasible comparison estimate to the owner theorem
`CubicRegularizationMethod.objective_succ_le_feasibleComparison`. This refinement therefore keeps
the Theorem 4.1.8 comparison-set hypotheses explicit, preserves the source-facing theorem family
semantics, and derives the one-step feasible comparison bound from the method owner rather than
keeping it as parallel public data. -/

/-- The threshold `\tilde ω = μ^3 / (8 σ^6 L^2)` governing the two-phase convergence estimate
for cubic regularization after a nonlinear transformation of a strongly convex function. -/
abbrev nonlinearTransformationStrongConvexCubicThreshold
    (L σ μ : ℝ) : ℝ :=
  μ ^ (3 : ℕ) / (8 * σ ^ (6 : ℕ) * L ^ (2 : ℕ))

/-- Expanding `nonlinearTransformationStrongConvexCubicThreshold L σ μ` recovers the textbook
formula `\tilde ω = μ^3 / (8 σ^6 L^2)`. -/
@[simp]
theorem nonlinearTransformationStrongConvexCubicThreshold_def
    (L σ μ : ℝ) :
    nonlinearTransformationStrongConvexCubicThreshold L σ μ =
      μ ^ (3 : ℕ) / (8 * σ ^ (6 : ℕ) * L ^ (2 : ℕ)) :=
  rfl

section NonlinearTransformationStrongConvexCubicRate

variable (problem : NonlinearConvexTransformation E)
variable (𝓕 : Set E) (μ : ℝ) {stepMap : ℝ → E → E} {L0 : ℝ} {L : NNReal}
variable
  (method :
    CubicRegularizationMethod
      problem
      stepMap
      L0 (L : ℝ) problem.x0)

local notation "f" => problem
local notation "𝓛₀" => f ⁻¹' Set.Iic (f problem.x0)
local notation "ω̃" =>
  nonlinearTransformationStrongConvexCubicThreshold (L : ℝ) problem.sigma μ
local notation "Δ" => fun k : ℕ ↦ f (method k) - f problem.xStar

variable
  (hlevel_subset : 𝓛₀ ⊆ 𝓕)
  [HessianLipschitzOn L 𝓕 problem]
  (hμ : 0 < μ)
  (hphi_strong : StrongConvexOn Set.univ μ problem.φ)

-- Semantic recall: `lean_leansearch` pointed to the `Analysis.Convex.Strong` module, while local
-- symbol search found no ready-made `quadratic_growth` bridge under the current project names.

/-- Helper for Theorem 4.1.9: the transformed objective gaps are monotone nonincreasing along the
cubic-regularization trajectory. -/
lemma nonlinear_transformation_gap_antitone
    (k : ℕ) :
    Δ (k + 1) ≤ Δ k :=
  by
  -- Subtracting the constant value `f x*` preserves the stepwise objective monotonicity.
  exact sub_le_sub_right (method.objective_succ_le_objective k) (f problem.xStar)

/-- Helper for Theorem 4.1.9: strong convexity of `φ` turns the current gap into a quadratic
control of the image-space distance to `u*`. -/
lemma nonlinear_transformation_gap_controls_u_distance_sq
    (hphi_strong : StrongConvexOn Set.univ μ problem.φ)
    (k : ℕ) :
    (μ / 2) * ‖(problem.u (method k) - problem.uStar : E)‖ ^ (2 : ℕ) ≤ Δ k :=
  by
  have hgrowth :=
    StrongConvexOn.quadratic_growth_of_isMinOn
      hphi_strong
      problem.isMinOn_uStar
      (problem.u (method k))
  have hk_eq : f (method k) = problem.φ (problem.u (method k)) := by
    simp
  have hxStar_eq : f problem.xStar = problem.φ problem.uStar := by
    simp [NonlinearConvexTransformation.xStar]
  -- Rewrite the quadratic-growth lower bound in terms of the transformed objective gap `Δ k`.
  change (μ / 2) * ‖(problem.u (method k) - problem.uStar : E)‖ ^ (2 : ℕ) ≤
      f (method k) - f problem.xStar
  rw [hk_eq, hxStar_eq]
  linarith

/-- Helper for Theorem 4.1.9: the current gap bounds the image-space distance to `u*` by the
strong-convexity radius `sqrt ((2 / μ) * Δ k)`. -/
lemma nonlinear_transformation_gap_controls_u_distance
    (hμ : 0 < μ)
    (hphi_strong : StrongConvexOn Set.univ μ problem.φ)
    (k : ℕ) :
    ‖(problem.u (method k) - problem.uStar : E)‖ ≤
      Real.sqrt ((2 / μ) * Δ k) :=
  by
  have hgap_nonneg :
      0 ≤ Δ k := by
    simpa using nonlinear_transformation_objective_gap_nonneg problem method k
  have hsq :
      ‖(problem.u (method k) - problem.uStar : E)‖ ^ (2 : ℕ) ≤ (2 / μ) * Δ k := by
    have hquad :=
      nonlinear_transformation_gap_controls_u_distance_sq problem μ method hphi_strong k
    have hμhalf_pos : 0 < μ / 2 := by
      positivity
    have hdiv :
        ‖(problem.u (method k) - problem.uStar : E)‖ ^ (2 : ℕ) ≤ Δ k / (μ / 2) := by
      exact (le_div_iff₀ hμhalf_pos).2 (by simpa [mul_comm] using hquad)
    have hrewrite : Δ k / (μ / 2) = (2 / μ) * Δ k := by
      field_simp [ne_of_gt hμ]
    rw [hrewrite] at hdiv
    exact hdiv
  have hrhs_nonneg : 0 ≤ (2 / μ) * Δ k := by
    exact mul_nonneg (by positivity) hgap_nonneg
  have hsqrt_sq :
      (Real.sqrt ((2 / μ) * Δ k)) ^ (2 : ℕ) = (2 / μ) * Δ k := by
    simpa using Real.sq_sqrt hrhs_nonneg
  have hsq' :
      ‖(problem.u (method k) - problem.uStar : E)‖ ^ (2 : ℕ) ≤
        (Real.sqrt ((2 / μ) * Δ k)) ^ (2 : ℕ) := by
    rw [hsqrt_sq]
    exact hsq
  -- Compare squared norms and then take square roots on both nonnegative sides.
  simpa [pow_two] using
    (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).1 hsq'

/-- Helper for Theorem 4.1.9: replacing the global level-set radius from Theorem 4.1.8 by the
strong-convexity radius of the current gap yields the local one-step scalar model. -/
lemma nonlinear_transformation_gap_succ_le_alpha_local_model
    (hlevel_subset : 𝓛₀ ⊆ 𝓕)
    (hμ : 0 < μ)
    (hphi_strong : StrongConvexOn Set.univ μ problem.φ)
    (k : ℕ) {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    Δ (k + 1) ≤
      (1 - α) * Δ k +
        ((L : ℝ) / 2) * α ^ (3 : ℕ) *
          (problem.sigma * Real.sqrt ((2 / μ) * Δ k)) ^ (3 : ℕ) :=
  by
  let uk : E := problem.u (method k)
  let zα : E := AffineMap.lineMap uk problem.uStar α
  let yα : E := problem.u.symm zα
  let S : Set E := 𝓛[problem.φ]((problem.φ (problem.u problem.x0)))
  have hσ_nonneg : 0 ≤ problem.sigma := by
    rcases problem.sigma_isGreatest.1 with ⟨w, -, hw⟩
    rw [← hw]
    exact norm_nonneg _
  have hk_sublevel : method k ∈ 𝓛₀ := method.mem_initial_sublevel k
  have hk_level : f (method k) ≤ f problem.x0 := hk_sublevel
  have huk : uk ∈ S := by
    -- Rewrite the current iterate into image coordinates on the controlling level set.
    change problem.φ (problem.u (method k)) ≤ problem.φ (problem.u problem.x0)
    simpa [uk] using hk_level
  have huStar_level :
      problem.φ problem.uStar ≤ problem.φ (problem.u problem.x0) := by
    have hu0_mem : problem.u problem.x0 ∈ (Set.univ : Set E) := by
      simp
    -- The chosen minimizer `u*` lies below the initial image value.
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
    -- Convexity controls the objective along the image-space segment to `u*`.
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
    -- Pull the image-space comparison point back through `u⁻¹`.
    change problem yα ≤ problem problem.x0
    simpa [yα, zα] using hzα_level
  have hyαF : yα ∈ 𝓕 := hlevel_subset hyα_sublevel
  have hcomparison :
      f (method (k + 1)) ≤
        f yα + ((L : ℝ) / 2) * ‖(yα - method k : E)‖ ^ (3 : ℕ) := by
    -- Route correction: reuse the owner-level feasible comparison theorem from Theorem 4.1.8.
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
    -- Convexity bounds the objective value of the transported comparison point.
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
      ‖(problem.uStar - uk : E)‖ ≤ Real.sqrt ((2 / μ) * Δ k) := by
    -- Strong convexity replaces the global radius `D` by the current-gap radius.
    simpa [uk, norm_sub_rev] using
      nonlinear_transformation_gap_controls_u_distance problem μ method hμ hphi_strong k
  have hzα_norm_le :
      ‖(zα - uk : E)‖ ≤ α * Real.sqrt ((2 / μ) * Δ k) := by
    rw [hzα_norm_eq]
    exact mul_le_mul_of_nonneg_left huk_radius hα_nonneg
  have hnorm_le :
      ‖(yα - method k : E)‖ ≤ α * (problem.sigma * Real.sqrt ((2 / μ) * Δ k)) := by
    calc
      ‖(yα - method k : E)‖ ≤ problem.sigma * ‖(zα - uk : E)‖ := hdist
      _ ≤ problem.sigma * (α * Real.sqrt ((2 / μ) * Δ k)) := by
        exact mul_le_mul_of_nonneg_left hzα_norm_le hσ_nonneg
      _ = α * (problem.sigma * Real.sqrt ((2 / μ) * Δ k)) := by
        ring
  have hcube :
      ((L : ℝ) / 2) * ‖(yα - method k : E)‖ ^ (3 : ℕ) ≤
        ((L : ℝ) / 2) * α ^ (3 : ℕ) *
          (problem.sigma * Real.sqrt ((2 / μ) * Δ k)) ^ (3 : ℕ) := by
    -- Cubing the local transported-distance bound yields the desired scalar penalty term.
    have hpow :
        ‖(yα - method k : E)‖ ^ (3 : ℕ) ≤
          (α * (problem.sigma * Real.sqrt ((2 / μ) * Δ k))) ^ (3 : ℕ) := by
      exact pow_le_pow_left₀ (norm_nonneg _) hnorm_le 3
    have hcoef_nonneg : 0 ≤ (L : ℝ) / 2 := by
      positivity
    have hscaled :
        ((L : ℝ) / 2) * ‖(yα - method k : E)‖ ^ (3 : ℕ) ≤
          ((L : ℝ) / 2) * (α * (problem.sigma * Real.sqrt ((2 / μ) * Δ k))) ^ (3 : ℕ) := by
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
        (1 - α) * Δ k +
          ((L : ℝ) / 2) * α ^ (3 : ℕ) *
            (problem.sigma * Real.sqrt ((2 / μ) * Δ k)) ^ (3 : ℕ) := by
    exact add_le_add hobjective hcube
  exact hstep_gap.trans hsum

/-- Helper for Theorem 4.1.9: the strong-convex local threshold `ω̃ = μ^3 / (8 σ^6 L^2)` is
nonnegative. -/
lemma nonlinear_transformation_threshold_nonneg :
    0 < μ → 0 ≤ ω̃ := by
  -- Expand the threshold and discharge nonnegativity from `μ > 0`.
  intro hμ
  rw [nonlinearTransformationStrongConvexCubicThreshold_def]
  positivity

/-- Helper for Theorem 4.1.9: every transformed objective gap is bounded above by the initial
gap. -/
lemma nonlinear_transformation_gap_le_initial
    (k : ℕ) :
    Δ k ≤ Δ 0 := by
  induction k with
  | zero =>
      exact le_rfl
  | succ k ih =>
      -- The one-step antitonicity telescopes back to the initial iterate.
      exact (nonlinear_transformation_gap_antitone problem method k).trans ih

/-- Helper for Theorem 4.1.9: raising a nonnegative quantity to the quarter power and then to the
fourth power recovers the original value. -/
lemma rpow_one_quarter_pow_four_eq
    {x : ℝ}
    (hx : 0 ≤ x) :
    (Real.rpow x (1 / 4 : ℝ)) ^ (4 : ℕ) = x := by
  -- The exponents multiply to `1`, so the `rpow`/`pow` composition collapses.
  calc
    (Real.rpow x (1 / 4 : ℝ)) ^ (4 : ℕ)
        = Real.rpow x ((1 / 4 : ℝ) * 4) := by
            symm
            simpa using Real.rpow_mul_natCast hx (1 / 4 : ℝ) 4
    _ = x := by
          norm_num [Real.rpow_one]

/-- Helper for Theorem 4.1.9: the quarter root of `4 / 9` is the large-phase constant
`sqrt (2 / 3)`. -/
lemma four_ninths_rpow_one_quarter :
    Real.rpow (4 / 9 : ℝ) (1 / 4 : ℝ) = Real.sqrt (2 / 3 : ℝ) := by
  -- Rewrite `4 / 9` as `(2 / 3)^2` and simplify the product of exponents.
  calc
    Real.rpow (4 / 9 : ℝ) (1 / 4 : ℝ)
        = Real.rpow ((2 / 3 : ℝ) ^ (2 : ℕ)) (1 / 4 : ℝ) := by
            norm_num
    _ = Real.rpow (2 / 3 : ℝ) ((2 : ℝ) * (1 / 4 : ℝ)) := by
          simpa [Real.rpow_natCast] using
            (Real.rpow_mul (by positivity : 0 ≤ (2 / 3 : ℝ)) (2 : ℝ) (1 / 4 : ℝ)).symm
    _ = Real.sqrt (2 / 3 : ℝ) := by
          rw [show (2 : ℝ) * (1 / 4 : ℝ) = (1 / 2 : ℝ) by norm_num]
          simp [Real.sqrt_eq_rpow]

/-- Helper for Theorem 4.1.9: the threshold `ω̃` converts the strong-convexity radius
`Real.sqrt ((2 / μ) * gap)` into the normalized scalar `Real.sqrt (gap / ω̃)`. -/
lemma nonlinear_transformation_sqrt_threshold_normalization
    {gap : ℝ}
    (hμ : 0 < μ)
    (hgap : 0 ≤ gap) :
    Real.sqrt (gap / ω̃) =
      ((2 * problem.sigma ^ (3 : ℕ) * (L : ℝ)) / μ) *
        Real.sqrt ((2 / μ) * gap) := by
  let s : ℝ := Real.sqrt ((2 / μ) * gap)
  have hμ_ne : μ ≠ 0 := ne_of_gt hμ
  have hσ_nonneg : 0 ≤ problem.sigma := by
    rcases problem.sigma_isGreatest.1 with ⟨w, -, hw⟩
    rw [← hw]
    exact norm_nonneg _
  have hs_sq : s ^ (2 : ℕ) = (2 / μ) * gap := by
    -- Squaring the auxiliary radius removes the square root.
    dsimp [s]
    nlinarith [Real.sq_sqrt (by positivity : 0 ≤ (2 / μ) * gap)]
  have htarget_nonneg : 0 ≤ gap / ω̃ := by
    -- Expanding `ω̃` makes the normalized gap manifestly nonnegative.
    rw [nonlinearTransformationStrongConvexCubicThreshold_def]
    positivity
  have hright_nonneg :
      0 ≤ ((2 * problem.sigma ^ (3 : ℕ) * (L : ℝ)) / μ) * s := by
    positivity
  have hsq :
      (((2 * problem.sigma ^ (3 : ℕ) * (L : ℝ)) / μ) * s) ^ (2 : ℕ) =
        gap / ω̃ := by
    -- The threshold definition is chosen so that the two squares agree exactly.
    calc
      (((2 * problem.sigma ^ (3 : ℕ) * (L : ℝ)) / μ) * s) ^ (2 : ℕ)
          = (((2 * problem.sigma ^ (3 : ℕ) * (L : ℝ)) / μ) ^ (2 : ℕ)) * s ^ (2 : ℕ) := by
              ring
      _ = (((2 * problem.sigma ^ (3 : ℕ) * (L : ℝ)) / μ) ^ (2 : ℕ)) * ((2 / μ) * gap) := by
            rw [hs_sq]
      _ = gap / ω̃ := by
            rw [nonlinearTransformationStrongConvexCubicThreshold_def]
            field_simp [hμ_ne]
            ring
  nlinarith [Real.sq_sqrt htarget_nonneg, hsq, Real.sqrt_nonneg (gap / ω̃), hright_nonneg]

/-- Helper for Theorem 4.1.9: the local comparison inequality rewrites entirely in terms of the
normalized gap `Δ k / ω̃`. -/
lemma nonlinear_transformation_gap_succ_le_normalized_local_model
    (hlevel_subset : 𝓛₀ ⊆ 𝓕)
    (hμ : 0 < μ)
    (hphi_strong : StrongConvexOn Set.univ μ problem.φ)
    (k : ℕ) {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    Δ (k + 1) ≤
      (1 - α + (1 / 2 : ℝ) * α ^ (3 : ℕ) * Real.sqrt (Δ k / ω̃)) * Δ k := by
  let gap : ℝ := Δ k
  let s : ℝ := Real.sqrt ((2 / μ) * gap)
  have hμ_ne : μ ≠ 0 := ne_of_gt hμ
  have hgap_nonneg : 0 ≤ gap := by
    simpa [gap] using nonlinear_transformation_objective_gap_nonneg problem method k
  have hs_sq : s ^ (2 : ℕ) = (2 / μ) * gap := by
    -- The cubic term becomes linear in `gap` after peeling off one factor of `s`.
    dsimp [s]
    nlinarith [Real.sq_sqrt (by positivity : 0 ≤ (2 / μ) * gap)]
  have hsqrt_target :
      Real.sqrt (gap / ω̃) =
        ((2 * problem.sigma ^ (3 : ℕ) * (L : ℝ)) / μ) * s := by
    simpa [gap, s] using
      nonlinear_transformation_sqrt_threshold_normalization
        problem μ hμ hgap_nonneg
  have hlocal :=
    nonlinear_transformation_gap_succ_le_alpha_local_model
      problem 𝓕 μ method hlevel_subset hμ hphi_strong k hα
  -- Rewrite the local cubic model into the normalized scalar recurrence in `gap / ω̃`.
  calc
    Δ (k + 1) ≤
        (1 - α) * gap +
          ((L : ℝ) / 2) * α ^ (3 : ℕ) * (problem.sigma * s) ^ (3 : ℕ) := by
      simpa [gap, s] using hlocal
    _ = (1 - α) * gap +
          ((L : ℝ) / 2) * α ^ (3 : ℕ) * (problem.sigma ^ (3 : ℕ) * (s * s ^ (2 : ℕ))) := by
      ring
    _ = (1 - α) * gap +
          ((L : ℝ) / 2) * α ^ (3 : ℕ) *
            (problem.sigma ^ (3 : ℕ) * (s * ((2 / μ) * gap))) := by
      rw [hs_sq]
    _ = (1 - α) * gap +
          (((1 / 2 : ℝ) * α ^ (3 : ℕ) *
              (((2 * problem.sigma ^ (3 : ℕ) * (L : ℝ)) / μ) * s)) * gap) := by
      field_simp [hμ_ne]
    _ = (1 - α + (1 / 2 : ℝ) * α ^ (3 : ℕ) * Real.sqrt (gap / ω̃)) * gap := by
      rw [hsqrt_target]
      ring
    _ = (1 - α + (1 / 2 : ℝ) * α ^ (3 : ℕ) * Real.sqrt (Δ k / ω̃)) * Δ k := by
      rfl

/-- Helper for Theorem 4.1.9: the endpoint choice `α = sqrt (2 / 3) / β` is feasible whenever
`β` is at least `sqrt (2 / 3)`. -/
lemma nonlinear_transformation_large_phase_alpha_mem
    {β : ℝ}
    (hβ : Real.sqrt (2 / 3 : ℝ) ≤ β) :
    Real.sqrt (2 / 3 : ℝ) / β ∈ Set.Icc (0 : ℝ) 1 := by
  have hconst_pos : 0 < Real.sqrt (2 / 3 : ℝ) := by
    positivity
  have hβ_pos : 0 < β := lt_of_lt_of_le hconst_pos hβ
  -- The large-phase threshold gives exactly the denominator needed to keep `α` in `[0,1]`.
  refine ⟨?_, ?_⟩
  · positivity
  · exact (div_le_iff₀ hβ_pos).2 (by simpa using hβ)

/-- Helper for Theorem 4.1.9: in normalized fourth-root variables, the large-phase scalar model
contracts by `sqrt (2 / 3) / 6` in one step. -/
lemma nonlinear_transformation_large_phase_scalar_polynomial_nonpos
    (β : ℝ) :
    Real.sqrt (2 / 3 : ℝ) * β / 81 - β ^ (2 : ℕ) / 9 - 1 / 2916 ≤ 0 := by
  have hsqrt_sq : (Real.sqrt (2 / 3 : ℝ)) ^ (2 : ℕ) = (2 / 3 : ℝ) := by
    -- The completed-square remainder uses only the defining square of `sqrt (2 / 3)`.
    simpa using Real.sq_sqrt (show 0 ≤ (2 / 3 : ℝ) by positivity)
  -- Complete the square in the normalized variable `β` and close the remainder by nonnegativity.
  nlinarith [sq_nonneg (((18 : ℝ) * β) - Real.sqrt (2 / 3 : ℝ)), hsqrt_sq]

/-- Helper for Theorem 4.1.9: the positive threshold cancels against its normalized quotient. -/
lemma nonlinear_transformation_threshold_mul_div_cancel
    {gap : ℝ}
    (hω_pos : 0 < ω̃) :
    ω̃ * (gap / ω̃) = gap := by
  -- Route correction: isolate the `ω̃ * (gap / ω̃)` transport once instead of repeating it.
  calc
    ω̃ * (gap / ω̃) = ω̃ * (gap * ω̃⁻¹) := by rw [div_eq_mul_inv]
    _ = gap * (ω̃ * ω̃⁻¹) := by ring
    _ = gap := by rw [mul_inv_cancel₀ hω_pos.ne', mul_one]

/-- Helper for Theorem 4.1.9: in normalized fourth-root variables, the large-phase scalar model
contracts by `sqrt (2 / 3) / 6` in one step. -/
lemma nonlinear_transformation_large_phase_scalar_step
    {β : ℝ}
    (hβ : Real.sqrt (2 / 3 : ℝ) ≤ β) :
    (1 - Real.sqrt (2 / 3 : ℝ) / β +
        (1 / 2 : ℝ) * (Real.sqrt (2 / 3 : ℝ) / β) ^ (3 : ℕ) * β ^ (2 : ℕ)) * β ^ (4 : ℕ) ≤
      (β - Real.sqrt (2 / 3 : ℝ) / 6) ^ (4 : ℕ) := by
  have hconst_pos : 0 < Real.sqrt (2 / 3 : ℝ) := by
    positivity
  have hβ_pos : 0 < β := lt_of_lt_of_le hconst_pos hβ
  have hsqrt_sq : (Real.sqrt (2 / 3 : ℝ)) ^ (2 : ℕ) = (2 / 3 : ℝ) := by
    -- Squaring `sqrt (2 / 3)` removes the only irrational-looking coefficient.
    simpa using Real.sq_sqrt (show 0 ≤ (2 / 3 : ℝ) by positivity)
  have hsqrt_cube :
      (Real.sqrt (2 / 3 : ℝ)) ^ (3 : ℕ) =
        (2 / 3 : ℝ) * Real.sqrt (2 / 3 : ℝ) := by
    -- Rewrite the cubic power through the already-known square.
    calc
      (Real.sqrt (2 / 3 : ℝ)) ^ (3 : ℕ)
          = (Real.sqrt (2 / 3 : ℝ)) ^ (2 : ℕ) * Real.sqrt (2 / 3 : ℝ) := by ring
      _ = (2 / 3 : ℝ) * Real.sqrt (2 / 3 : ℝ) := by rw [hsqrt_sq]
  have hsqrt_four :
      (Real.sqrt (2 / 3 : ℝ)) ^ (4 : ℕ) = (4 / 9 : ℝ) := by
    -- The quartic power is just the square of `2 / 3`.
    calc
      (Real.sqrt (2 / 3 : ℝ)) ^ (4 : ℕ)
          = ((Real.sqrt (2 / 3 : ℝ)) ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
      _ = ((2 / 3 : ℝ)) ^ (2 : ℕ) := by rw [hsqrt_sq]
      _ = (4 / 9 : ℝ) := by norm_num
  have hdiff :
      (1 - Real.sqrt (2 / 3 : ℝ) / β +
          (1 / 2 : ℝ) * (Real.sqrt (2 / 3 : ℝ) / β) ^ (3 : ℕ) * β ^ (2 : ℕ)) *
          β ^ (4 : ℕ) -
        (β - Real.sqrt (2 / 3 : ℝ) / 6) ^ (4 : ℕ) =
      Real.sqrt (2 / 3 : ℝ) * β / 81 - β ^ (2 : ℕ) / 9 - 1 / 2916 := by
    -- Expand the quartic difference and rewrite the square of `sqrt (2 / 3)`.
    field_simp [hβ_pos.ne']
    ring_nf
    rw [hsqrt_cube, hsqrt_sq, hsqrt_four]
    ring
  have hpoly := nonlinear_transformation_large_phase_scalar_polynomial_nonpos β
  -- The remaining scalar remainder is the unconditional square-completion inequality above.
  nlinarith [hdiff, hpoly]

/-- Helper for Theorem 4.1.9: a positive threshold factors quarter roots through the normalized
gaps `Δ k / ω̃`. -/
lemma nonlinear_transformation_gap_rpow_scale
    (hω_pos : 0 < ω̃)
    (k : ℕ) :
    Real.rpow (Δ k) (1 / 4 : ℝ) =
      Real.rpow ω̃ (1 / 4 : ℝ) * Real.rpow (Δ k / ω̃) (1 / 4 : ℝ) := by
  have hgap_nonneg : 0 ≤ Δ k := by
    simpa using nonlinear_transformation_objective_gap_nonneg problem method k
  have hnormalized_nonneg : 0 ≤ Δ k / ω̃ := by
    exact div_nonneg hgap_nonneg hω_pos.le
  have hthreshold : ω̃ * (Δ k / ω̃) = Δ k :=
    nonlinear_transformation_threshold_mul_div_cancel problem μ hω_pos
  have hrpow_threshold :
      Real.rpow (Δ k) (1 / 4 : ℝ) =
        Real.rpow (ω̃ * (Δ k / ω̃)) (1 / 4 : ℝ) := by
    simpa using congrArg (fun t : ℝ ↦ Real.rpow t (1 / 4 : ℝ)) hthreshold.symm
  -- Rewrite the gap through the positive threshold before factoring the quarter root.
  calc
    Real.rpow (Δ k) (1 / 4 : ℝ)
        = Real.rpow (ω̃ * (Δ k / ω̃)) (1 / 4 : ℝ) := hrpow_threshold
    _ = Real.rpow ω̃ (1 / 4 : ℝ) * Real.rpow (Δ k / ω̃) (1 / 4 : ℝ) := by
          simpa using
            (Real.mul_rpow hω_pos.le hnormalized_nonneg :
              Real.rpow (ω̃ * (Δ k / ω̃)) (1 / 4 : ℝ) =
                Real.rpow ω̃ (1 / 4 : ℝ) * Real.rpow (Δ k / ω̃) (1 / 4 : ℝ))

/-- Helper for Theorem 4.1.9: while `Δ k` stays above the first-phase threshold, the normalized
fourth root drops by `sqrt (2 / 3) / 6` in one step. -/
lemma nonlinear_transformation_large_phase_step_rpow_drop
    (hlevel_subset : 𝓛₀ ⊆ 𝓕)
    (hμ : 0 < μ)
    (hphi_strong : StrongConvexOn Set.univ μ problem.φ)
    (hω_pos : 0 < ω̃)
    (k : ℕ)
    (hk : Δ k ≥ (4 / 9 : ℝ) * ω̃) :
    Real.rpow (Δ (k + 1) / ω̃) (1 / 4 : ℝ) ≤
      Real.rpow (Δ k / ω̃) (1 / 4 : ℝ) - Real.sqrt (2 / 3 : ℝ) / 6 := by
  set β : ℝ := Real.rpow (Δ k / ω̃) (1 / 4 : ℝ) with hβ_def
  have hgap_nonneg : 0 ≤ Δ k := by
    simpa using nonlinear_transformation_objective_gap_nonneg problem method k
  have hgap_succ_nonneg : 0 ≤ Δ (k + 1) := by
    simpa using nonlinear_transformation_objective_gap_nonneg problem method (k + 1)
  have hnormalized_nonneg : 0 ≤ Δ k / ω̃ := by
    exact div_nonneg hgap_nonneg hω_pos.le
  have hnormalized_succ_nonneg : 0 ≤ Δ (k + 1) / ω̃ := by
    exact div_nonneg hgap_succ_nonneg hω_pos.le
  have hthreshold_div : (4 / 9 : ℝ) ≤ Δ k / ω̃ := by
    rw [le_div_iff₀ hω_pos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hk
  have hβ_large :
      Real.sqrt (2 / 3 : ℝ) ≤ β := by
    calc
      Real.sqrt (2 / 3 : ℝ) = Real.rpow (4 / 9 : ℝ) (1 / 4 : ℝ) := by
        rw [four_ninths_rpow_one_quarter]
      _ ≤ Real.rpow (Δ k / ω̃) (1 / 4 : ℝ) := by
        exact Real.rpow_le_rpow
          (by positivity : 0 ≤ (4 / 9 : ℝ))
          hthreshold_div
          (by positivity : 0 ≤ (1 / 4 : ℝ))
      _ = β := by rw [← hβ_def]
  have hα :
      Real.sqrt (2 / 3 : ℝ) / β ∈ Set.Icc (0 : ℝ) 1 :=
    nonlinear_transformation_large_phase_alpha_mem hβ_large
  have hlocal :=
    nonlinear_transformation_gap_succ_le_normalized_local_model
      problem 𝓕 μ method hlevel_subset hμ hphi_strong k hα
  have hβ_sq :
      β ^ (2 : ℕ) = Real.sqrt (Δ k / ω̃) := by
    calc
      β ^ (2 : ℕ) = (Real.rpow (Δ k / ω̃) (1 / 4 : ℝ)) ^ (2 : ℕ) := by
        rw [hβ_def]
      _ = Real.rpow (Δ k / ω̃) ((1 / 4 : ℝ) * 2) := by
            symm
            simpa using Real.rpow_mul_natCast hnormalized_nonneg (1 / 4 : ℝ) 2
      _ = Real.sqrt (Δ k / ω̃) := by
            rw [show (1 / 4 : ℝ) * 2 = (1 / 2 : ℝ) by norm_num]
            simp [Real.sqrt_eq_rpow]
  have hβ_four :
      β ^ (4 : ℕ) = Δ k / ω̃ := by
    calc
      β ^ (4 : ℕ) = (Real.rpow (Δ k / ω̃) (1 / 4 : ℝ)) ^ (4 : ℕ) := by
        rw [hβ_def]
      _ = Δ k / ω̃ := by
            exact rpow_one_quarter_pow_four_eq hnormalized_nonneg
  have hnormalized_model :
      Δ (k + 1) / ω̃ ≤
        (1 - Real.sqrt (2 / 3 : ℝ) / β +
            (1 / 2 : ℝ) * (Real.sqrt (2 / 3 : ℝ) / β) ^ (3 : ℕ) * β ^ (2 : ℕ)) *
          β ^ (4 : ℕ) := by
    have hdiv_model :
        Δ (k + 1) / ω̃ ≤
          ((1 - Real.sqrt (2 / 3 : ℝ) / β +
                (1 / 2 : ℝ) * (Real.sqrt (2 / 3 : ℝ) / β) ^ (3 : ℕ) *
                  Real.sqrt (Δ k / ω̃)) *
              Δ k) / ω̃ := by
      exact div_le_div_of_nonneg_right (by simpa using hlocal) hω_pos.le
    calc
      Δ (k + 1) / ω̃
          ≤ ((1 - Real.sqrt (2 / 3 : ℝ) / β +
                  (1 / 2 : ℝ) * (Real.sqrt (2 / 3 : ℝ) / β) ^ (3 : ℕ) *
                    Real.sqrt (Δ k / ω̃)) *
                Δ k) / ω̃ := hdiv_model
      _ =
          (1 - Real.sqrt (2 / 3 : ℝ) / β +
              (1 / 2 : ℝ) * (Real.sqrt (2 / 3 : ℝ) / β) ^ (3 : ℕ) *
                Real.sqrt (Δ k / ω̃)) *
            (Δ k / ω̃) := by
              field_simp [hω_pos.ne']
      _ =
          (1 - Real.sqrt (2 / 3 : ℝ) / β +
              (1 / 2 : ℝ) * (Real.sqrt (2 / 3 : ℝ) / β) ^ (3 : ℕ) * β ^ (2 : ℕ)) *
            β ^ (4 : ℕ) := by
              rw [← hβ_sq, ← hβ_four]
  have hscalar :
      Δ (k + 1) / ω̃ ≤ (β - Real.sqrt (2 / 3 : ℝ) / 6) ^ (4 : ℕ) := by
    exact hnormalized_model.trans (nonlinear_transformation_large_phase_scalar_step hβ_large)
  have hβ_sub_nonneg : 0 ≤ β - Real.sqrt (2 / 3 : ℝ) / 6 := by
    have hconst_nonneg : 0 ≤ Real.sqrt (2 / 3 : ℝ) := by positivity
    nlinarith
  have hquarter_fourth :
      Real.rpow ((β - Real.sqrt (2 / 3 : ℝ) / 6) ^ (4 : ℕ)) (1 / 4 : ℝ) =
        β - Real.sqrt (2 / 3 : ℝ) / 6 := by
    calc
      Real.rpow ((β - Real.sqrt (2 / 3 : ℝ) / 6) ^ (4 : ℕ)) (1 / 4 : ℝ)
          = Real.rpow (β - Real.sqrt (2 / 3 : ℝ) / 6) ((4 : ℝ) * (1 / 4 : ℝ)) := by
              simpa [Real.rpow_natCast] using
                (Real.rpow_mul hβ_sub_nonneg (4 : ℝ) (1 / 4 : ℝ)).symm
      _ = β - Real.sqrt (2 / 3 : ℝ) / 6 := by
            norm_num [Real.rpow_one]
  -- Keep the argument in normalized quarter-root variables until the last scalar rewrite.
  calc
    Real.rpow (Δ (k + 1) / ω̃) (1 / 4 : ℝ)
        ≤ Real.rpow ((β - Real.sqrt (2 / 3 : ℝ) / 6) ^ (4 : ℕ)) (1 / 4 : ℝ) := by
            exact Real.rpow_le_rpow
              hnormalized_succ_nonneg
              hscalar
              (by positivity : 0 ≤ (1 / 4 : ℝ))
    _ = β - Real.sqrt (2 / 3 : ℝ) / 6 := hquarter_fourth
    _ = Real.rpow (Δ k / ω̃) (1 / 4 : ℝ) - Real.sqrt (2 / 3 : ℝ) / 6 := by
          rw [hβ_def]

/-- Helper for Theorem 4.1.9: along the whole first phase, the normalized fourth root decreases
linearly with slope `sqrt (2 / 3) / 6`. -/
lemma nonlinear_transformation_first_phase_gap_rpow_bound
    (hlevel_subset : 𝓛₀ ⊆ 𝓕)
    (hμ : 0 < μ)
    (hphi_strong : StrongConvexOn Set.univ μ problem.φ)
    (hω_pos : 0 < ω̃)
    (hgap0 : Δ 0 ≥ (4 / 9 : ℝ) * ω̃) :
    ∀ k : ℕ,
      Δ k ≥ (4 / 9 : ℝ) * ω̃ →
        Real.rpow (Δ k / ω̃) (1 / 4 : ℝ) ≤
          Real.rpow (Δ 0 / ω̃) (1 / 4 : ℝ) -
            ((k : ℝ) / 6 : ℝ) * Real.sqrt (2 / 3 : ℝ) := by
  intro k
  induction k with
  | zero =>
      intro hk0
      -- The initial step has no accumulated decrement.
      simpa using le_rfl
  | succ k ih =>
      intro hk_succ
      have hk :
          Δ k ≥ (4 / 9 : ℝ) * ω̃ := by
        -- Monotonicity propagates the threshold from step `k + 1` back to step `k`.
        exact hk_succ.trans (nonlinear_transformation_gap_antitone problem method k)
      have hdrop :=
        nonlinear_transformation_large_phase_step_rpow_drop
          problem 𝓕 μ method hlevel_subset hμ hphi_strong hω_pos k hk
      have hih := ih hk
      calc
        Real.rpow (Δ (k + 1) / ω̃) (1 / 4 : ℝ)
            ≤ Real.rpow (Δ k / ω̃) (1 / 4 : ℝ) - Real.sqrt (2 / 3 : ℝ) / 6 := hdrop
        _ ≤
            (Real.rpow (Δ 0 / ω̃) (1 / 4 : ℝ) -
              ((k : ℝ) / 6 : ℝ) * Real.sqrt (2 / 3 : ℝ)) -
              Real.sqrt (2 / 3 : ℝ) / 6 := by
              linarith
        _ =
            Real.rpow (Δ 0 / ω̃) (1 / 4 : ℝ) -
              ((((k + 1 : ℕ) : ℝ) / 6 : ℝ) * Real.sqrt (2 / 3 : ℝ)) := by
              rw [Nat.cast_add]
              ring

/-- Helper for Theorem 4.1.9: the local model at `α = 1` is exactly the second-phase
superlinear one-step recurrence. -/
lemma nonlinear_transformation_gap_succ_le_second_phase_superlinear_pointwise
    (hlevel_subset : 𝓛₀ ⊆ 𝓕)
    (hμ : 0 < μ)
    (hphi_strong : StrongConvexOn Set.univ μ problem.φ)
    (k : ℕ) :
    Δ (k + 1) ≤
      (1 / 2 : ℝ) * Δ k * Real.sqrt (Δ k / ω̃) := by
  have hlocal :=
    nonlinear_transformation_gap_succ_le_normalized_local_model
      problem 𝓕 μ method hlevel_subset hμ hphi_strong k (by simp : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
  -- The endpoint choice `α = 1` leaves exactly the second-phase superlinear scalar factor.
  simpa [mul_assoc, mul_left_comm, mul_comm] using hlocal

-- Proof sketch: apply
-- `method.objective_succ_le_feasibleComparison hlevel_subset`
-- from Theorem 4.1.8 at the comparison point `v (α • u* + (1 - α) • u (x_k))`, then use
-- convexity of `φ` and strong convexity at `u*` to bound the objective and distance terms.
-- Rewrite the resulting scalar recursion in terms of
-- `\tilde ω = nonlinearTransformationStrongConvexCubicThreshold L σ μ`, and iterate the same
-- first-phase argument as in the star-convex model case.
/-- Theorem 4.1.9 (1): under the nonlinear-transformation assumptions from Theorem 4.1.8, if
`φ` is `μ`-strongly convex and the initial gap is at least `(4 / 9) * \tilde ω`, then every
iterate whose gap is still above that threshold satisfies the fourth-root decay bound. -/
theorem nonlinearTransformation_cubicRegularization_firstPhase_gap_bound
    (hlevel_subset : 𝓛₀ ⊆ 𝓕)
    (hμ : 0 < μ)
    (hphi_strong : StrongConvexOn Set.univ μ problem.φ)
    (hgap0 :
      Δ 0 ≥ (4 / 9 : ℝ) * ω̃)
    (k : ℕ)
    (hk : Δ k ≥ (4 / 9 : ℝ) * ω̃) :
    Δ k ≤
      (Real.rpow (Δ 0) (1 / 4 : ℝ) -
        ((k : ℝ) / 6 : ℝ) * Real.sqrt (2 / 3 : ℝ) * Real.rpow ω̃ (1 / 4 : ℝ)) ^
        (4 : ℕ) := by
  by_cases hω : ω̃ = 0
  · have hgap_nonneg0 : 0 ≤ Δ 0 := by
      simpa using nonlinear_transformation_objective_gap_nonneg problem method 0
    -- Route correction: in the degenerate-threshold branch the target reduces to monotonicity.
    calc
      Δ k ≤ Δ 0 := nonlinear_transformation_gap_le_initial problem method k
      _ = (Real.rpow (Δ 0) (1 / 4 : ℝ)) ^ (4 : ℕ) := by
            symm
            exact rpow_one_quarter_pow_four_eq hgap_nonneg0
      _ =
          (Real.rpow (Δ 0) (1 / 4 : ℝ) -
            ((k : ℝ) / 6 : ℝ) * Real.sqrt (2 / 3 : ℝ) * Real.rpow ω̃ (1 / 4 : ℝ)) ^
            (4 : ℕ) := by
              simp [hω]
  · have hω_pos : 0 < ω̃ := lt_of_le_of_ne
        (nonlinear_transformation_threshold_nonneg problem μ hμ)
        (by simpa [eq_comm] using hω)
    have hgap_nonneg : 0 ≤ Δ k := by
      simpa using nonlinear_transformation_objective_gap_nonneg problem method k
    have hroot_bound_norm :=
      nonlinear_transformation_first_phase_gap_rpow_bound
        problem 𝓕 μ method hlevel_subset hμ hphi_strong hω_pos hgap0 k hk
    have hωroot_nonneg : 0 ≤ Real.rpow ω̃ (1 / 4 : ℝ) := by
      exact Real.rpow_nonneg hω_pos.le _
    have hscale_k :
        Real.rpow (Δ k) (1 / 4 : ℝ) =
          Real.rpow ω̃ (1 / 4 : ℝ) * Real.rpow (Δ k / ω̃) (1 / 4 : ℝ) :=
      nonlinear_transformation_gap_rpow_scale problem μ method hω_pos k
    have hscale_0 :
        Real.rpow (Δ 0) (1 / 4 : ℝ) =
          Real.rpow ω̃ (1 / 4 : ℝ) * Real.rpow (Δ 0 / ω̃) (1 / 4 : ℝ) :=
      nonlinear_transformation_gap_rpow_scale problem μ method hω_pos 0
    have hroot_bound :
        Real.rpow (Δ k) (1 / 4 : ℝ) ≤
          Real.rpow (Δ 0) (1 / 4 : ℝ) -
            ((k : ℝ) / 6 : ℝ) * Real.sqrt (2 / 3 : ℝ) * Real.rpow ω̃ (1 / 4 : ℝ) := by
      calc
        Real.rpow (Δ k) (1 / 4 : ℝ)
            = Real.rpow ω̃ (1 / 4 : ℝ) * Real.rpow (Δ k / ω̃) (1 / 4 : ℝ) := hscale_k
        _ ≤
            Real.rpow ω̃ (1 / 4 : ℝ) *
              (Real.rpow (Δ 0 / ω̃) (1 / 4 : ℝ) -
                ((k : ℝ) / 6 : ℝ) * Real.sqrt (2 / 3 : ℝ)) := by
                  exact mul_le_mul_of_nonneg_left hroot_bound_norm hωroot_nonneg
        _ =
            Real.rpow ω̃ (1 / 4 : ℝ) * Real.rpow (Δ 0 / ω̃) (1 / 4 : ℝ) -
              ((k : ℝ) / 6 : ℝ) * Real.sqrt (2 / 3 : ℝ) * Real.rpow ω̃ (1 / 4 : ℝ) := by
                ring
        _ =
            Real.rpow (Δ 0) (1 / 4 : ℝ) -
              ((k : ℝ) / 6 : ℝ) * Real.sqrt (2 / 3 : ℝ) * Real.rpow ω̃ (1 / 4 : ℝ) := by
                rw [← hscale_0]
    have hpow_bound :
        (Real.rpow (Δ k) (1 / 4 : ℝ)) ^ (4 : ℕ) ≤
          (Real.rpow (Δ 0) (1 / 4 : ℝ) -
            ((k : ℝ) / 6 : ℝ) * Real.sqrt (2 / 3 : ℝ) * Real.rpow ω̃ (1 / 4 : ℝ)) ^
            (4 : ℕ) := by
      exact pow_le_pow_left₀ (Real.rpow_nonneg hgap_nonneg _) hroot_bound 4
    -- Raise the quarter-root bound back to the original gap.
    calc
      Δ k = (Real.rpow (Δ k) (1 / 4 : ℝ)) ^ (4 : ℕ) := by
        symm
        exact rpow_one_quarter_pow_four_eq hgap_nonneg
      _ ≤
          (Real.rpow (Δ 0) (1 / 4 : ℝ) -
            ((k : ℝ) / 6 : ℝ) * Real.sqrt (2 / 3 : ℝ) * Real.rpow ω̃ (1 / 4 : ℝ)) ^
            (4 : ℕ) := hpow_bound

-- Proof sketch: apply the first-phase scalar recursion from the previous theorem to the
-- normalized gaps `Δ_k = (f(x_k) - f(x*)) / \tilde ω`. The same argument as in the first phase
-- shows that this recursion cannot remain forever in the regime `Δ_k > 4 / 9`, so some iterate
-- must cross the threshold.
/-- Theorem 4.1.9 (2): under the same assumptions, the first phase ends at some index `k₀` where
`f(x_{k₀}) - f(x^*) ≤ (4 / 9) * \tilde ω`. -/
theorem nonlinearTransformation_cubicRegularization_firstPhase_terminates
    (hlevel_subset : 𝓛₀ ⊆ 𝓕)
    (hμ : 0 < μ)
    (hphi_strong : StrongConvexOn Set.univ μ problem.φ)
    (hgap0 :
      Δ 0 ≥ (4 / 9 : ℝ) * ω̃) :
    ∃ k0 : ℕ,
      Δ k0 ≤ (4 / 9 : ℝ) * ω̃ := by
  by_cases hω : ω̃ = 0
  · refine ⟨1, ?_⟩
    -- When `ω̃ = 0`, the second-phase pointwise bound at `k = 0` already forces `Δ 1 = 0`.
    simpa [hω] using
      nonlinear_transformation_gap_succ_le_second_phase_superlinear_pointwise
        problem 𝓕 μ method hlevel_subset hμ hphi_strong 0
  · have hω_pos : 0 < ω̃ := lt_of_le_of_ne
        (nonlinear_transformation_threshold_nonneg problem μ hμ)
        (by simpa [eq_comm] using hω)
    by_contra hno
    have hall :
        ∀ k : ℕ, (4 / 9 : ℝ) * ω̃ < Δ k := by
      intro k
      exact lt_of_not_ge (by
        intro hk'
        exact hno ⟨k, hk'⟩)
    set a : ℝ := Real.rpow (Δ 0 / ω̃) (1 / 4 : ℝ)
    set c : ℝ := Real.sqrt (2 / 3 : ℝ) / 6
    have hc_pos : 0 < c := by
      dsimp [c]
      positivity
    obtain ⟨N, hN⟩ := exists_nat_gt (a / c)
    have hmul : a < (N : ℝ) * c := by
      have hmul_raw : (a / c) * c < (N : ℝ) * c := by
        exact mul_lt_mul_of_pos_right hN hc_pos
      simpa [hc_pos.ne'] using hmul_raw
    have hboundN :
        Real.rpow (Δ N / ω̃) (1 / 4 : ℝ) ≤ a - (N : ℝ) * c := by
      simpa [a, c, Nat.cast_ofNat, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using
        nonlinear_transformation_first_phase_gap_rpow_bound
          problem 𝓕 μ method hlevel_subset hμ hphi_strong hω_pos hgap0 N (le_of_lt (hall N))
    have hleft_nonneg : 0 ≤ Real.rpow (Δ N / ω̃) (1 / 4 : ℝ) := by
      exact Real.rpow_nonneg
        (div_nonneg
          (by simpa using nonlinear_transformation_objective_gap_nonneg problem method N)
          hω_pos.le)
        _
    -- The linear decay estimate cannot remain compatible with nonnegativity forever.
    linarith

-- Proof sketch: once `f(x_k) - f(x*) ≤ (4 / 9) * \tilde ω`, the scalar upper bound obtained from
-- the comparison points
-- `v (α • u* + (1 - α) • u (x_k))` is minimized at `α = 1`, giving
-- `Δ_{k+1} ≤ (1 / 2) Δ_k^(3/2)` for `Δ_k = (f(x_k) - f(x*)) / \tilde ω`. Rewriting this bound
-- in terms of the original objective values yields the displayed superlinear recurrence.
/-- Theorem 4.1.9 (3): once an iterate reaches the threshold `(4 / 9) * \tilde ω`, every later
iterate satisfies the superlinear estimate
`f(x_{k+1}) - f(x^*) ≤ (1 / 2) (f(x_k) - f(x^*)) * sqrt ((f(x_k) - f(x^*)) / \tilde ω)`. -/
theorem nonlinearTransformation_cubicRegularization_secondPhase_gap_le_superlinear
    (hlevel_subset : 𝓛₀ ⊆ 𝓕)
    (hμ : 0 < μ)
    (hphi_strong : StrongConvexOn Set.univ μ problem.φ)
    (k0 : ℕ)
    (hk0 : Δ k0 ≤ (4 / 9 : ℝ) * ω̃)
    (k : ℕ)
    (hk : k0 ≤ k) :
    Δ (k + 1) ≤
      (1 / 2 : ℝ) * Δ k * Real.sqrt (Δ k / ω̃) := by
  -- The pointwise local superlinear recurrence is stronger than the tail statement.
  simpa using
    nonlinear_transformation_gap_succ_le_second_phase_superlinear_pointwise
      problem 𝓕 μ method hlevel_subset hμ hphi_strong k

end NonlinearTransformationStrongConvexCubicRate
