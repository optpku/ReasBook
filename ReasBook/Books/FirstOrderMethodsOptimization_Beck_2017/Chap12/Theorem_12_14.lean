/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap01.Definition_1_37
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_10
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_13
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_19
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Theorem_4_12
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Theorem_4_15
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Theorem_5_26
import FirstOrderMethodsOptimization_Beck_2017.Chap11.Definition_11_13
import FirstOrderMethodsOptimization_Beck_2017.Chap11.Theorem_11_11
import FirstOrderMethodsOptimization_Beck_2017.Chap12.DualBlockMinimizationView
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Definition_12_14
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Definition_12_1_1
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Definition_12_15
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Algorithm_12_13.Comparison
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Algorithm_12_14
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Algorithm_12_15
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Definition_12_17
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Lemma_12_3
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Lemma_12_7
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Lemma_12_15
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Theorem_12_4

noncomputable section

universe u v

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory ENNReal Gradient

section

variable {Ω : Type v} {E : Type u} {p : ℕ}
variable [NeZero p]
variable [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Theorem 12.14 is `source-facing`: it is the randomized-order `O(1 / k)` rate statement for
the Chapter 12 dual block proximal-gradient method.

Domain sampling against the surrounding project APIs identifies the relevant owners:
- `IsDualBlockProximalGradientProblem` for Assumption 12.14;
- `is_dual_block_proximal_gradient_primal_trajectory` from Algorithm 12.15 as the pathwise owner
  of the realized primal/dual iterates driven by a realized block-choice rule;
- `dual_block_proximal_gradient_dual_objective` and
  `dual_block_proximal_gradient_dual_optimal_set` for the canonical block dual objective `q` and
  its optimal set `Λ*`; and
- `μ[...]` from the probability API, with theorem-level `Integrable` hypotheses exactly as in the
  randomized block proximal-gradient results of Chapter 11 and the realized-process style used by
  later randomized block methods in the project.

Primitive stochastic data are therefore the sampled blocks together with the realized iterate
processes `x : ℕ → Ω → E` and `y : ℕ → Ω → Fin p → E`. History-adapted realization is kept only
through the pathwise hypothesis
`∀ ω, is_dual_block_proximal_gradient_primal_trajectory ... (fun k ↦ x k ω) (fun k ↦ y k ω)`,
which is the canonical bridge from the probabilistic layer to the Chapter 12 pathwise algorithmic
owner. No measurable structure on `E` is primitive here: the theorem integrates only the
real-valued observables `(q (y (k + 1) ω)).toReal` and `‖x (k + 1) ω - x*‖²` on the probability
space `Ω`.

The source contains two independent quantitative conclusions, so the item is split into two atomic
theorem statements: the expected dual-gap estimate and the expected primal squared-distance
estimate. -/

section

variable (σ : PosReal) (f : E → EReal) (g : Fin p → E → EReal)
variable (y0 : Fin p → E)
variable (sampled_block : ℕ → Ω → Fin p)
variable (x : ℕ → Ω → E)
variable (y : ℕ → Ω → Fin p → E)

local notation "F" => composite_model_objective f (finite_sum_objective g)

variable
  (h_problem : IsDualBlockProximalGradientProblem f g σ)
  (h_traj :
    ∀ ω,
      is_dual_block_proximal_gradient_primal_trajectory
        f g σ (fun n ↦ sampled_block n ω) y0
        (fun n ↦ x n ω)
        (fun n ↦ y n ω))
  (h_sampled_block_meas : ∀ k, Measurable (sampled_block k))
  (h_sampled_block_indep : iIndepFun sampled_block μ)
  (h_sampled_block_uniform :
    ∀ k (i : Fin p), μ ((sampled_block k) ⁻¹' {i}) = 1 / (p : ℝ≥0∞))
  (yStar : Fin p → E)
  (hyStar : yStar ∈ Λ*(f, g))
  (hy0_finite : y0 ∈ finite_domain (q(f, g)))
  (hyStar_finite : yStar ∈ finite_domain (q(f, g)))

/-- Helper for Theorem 12.14: the Chapter 11 constant-weight initial norm term rewrites to the
explicit Lyapunov coefficient on the canonical block `L²` owner `WithLp.toLp 2 (y0 - yStar)`. -/
lemma half_weighted_sqnorm_eq_initial_lyapunov
    (σ : PosReal) (y0 yStar : Fin p → E) :
    (1 / 2 : ℝ) *
        compositeWeightedL2Norm (fun i : Fin p ↦ σ⁻¹) (y0 - yStar) ^ (2 : ℕ) =
      (1 / (2 * (σ : ℝ))) * ‖WithLp.toLp 2 (y0 - yStar)‖ ^ (2 : ℕ) := by
  have hσ : (σ : ℝ) ≠ 0 := by
    exact ne_of_gt σ.2
  have hsum_nonneg :
      0 ≤ ∑ i : Fin p, (((σ⁻¹ : PosReal) : ℝ)) * ‖(y0 - yStar) i‖ ^ (2 : ℕ) := by
    refine Finset.sum_nonneg ?_
    intro i hi
    have hweight_nonneg : 0 ≤ (((σ⁻¹ : PosReal) : ℝ)) := by
      exact le_of_lt (σ⁻¹).2
    have hnormsq_nonneg : 0 ≤ ‖(y0 - yStar) i‖ ^ (2 : ℕ) := by
      simpa [pow_two] using sq_nonneg ‖(y0 - yStar) i‖
    exact mul_nonneg hweight_nonneg hnormsq_nonneg
  -- Expand the weighted norm into the explicit weighted `L²` sum.
  calc
    (1 / 2 : ℝ) *
        compositeWeightedL2Norm (fun i : Fin p ↦ σ⁻¹) (y0 - yStar) ^ (2 : ℕ)
        =
      (1 / 2 : ℝ) *
        ∑ i : Fin p, (((σ⁻¹ : PosReal) : ℝ)) * ‖(y0 - yStar) i‖ ^ (2 : ℕ) := by
          rw [compositeWeightedL2Norm_def, Real.sq_sqrt hsum_nonneg]
    _ =
      (1 / 2 : ℝ) *
        ((σ : ℝ)⁻¹ * ∑ i : Fin p, ‖(y0 - yStar) i‖ ^ (2 : ℕ)) := by
          -- The weight is constant across blocks, so it factors out of the finite sum.
          rw [show (((σ⁻¹ : PosReal) : ℝ)) = (σ : ℝ)⁻¹ by rfl, ← Finset.mul_sum]
    _ = (1 / 2 : ℝ) * ((σ : ℝ)⁻¹ * ‖WithLp.toLp 2 (y0 - yStar)‖ ^ (2 : ℕ)) := by
          -- Identify the coordinate sum with the squared norm on the `PiLp` owner.
          congr 2
          symm
          simpa using
            (PiLp.norm_sq_eq_of_L2 (fun _ : Fin p ↦ E) (WithLp.toLp 2 (y0 - yStar)))
    _ = (1 / (2 * (σ : ℝ))) * ‖WithLp.toLp 2 (y0 - yStar)‖ ^ (2 : ℕ) := by
          field_simp [hσ]

/-- Helper for Theorem 12.14: an optimal block-dual point identifies the source-facing dual
optimum after passing to `EReal.toReal`. -/
lemma dual_problem_value_toReal_eq_of_mem_optimal_set
    {yStar : Fin p → E} (hyStar : yStar ∈ Λ*(f, g)) :
    EReal.toReal (q_opt(f, g)) = (q(f, g) yStar).toReal := by
  -- Rewrite the optimum value with the canonical optimal-set owner from Definition 12.17.
  rw [← dual_block_proximal_gradient_dual_objective_eq_dual_problem_value_of_mem_optimal_set
    f g hyStar]

/-- Helper for Theorem 12.14: each realized DBPG trajectory exposes the source step-(a) primal
argmax condition at every iterate. -/
lemma realized_dbpg_primal_argmax_at
    (h_traj :
      ∀ ω,
        is_dual_block_proximal_gradient_primal_trajectory
          f g σ (fun n ↦ sampled_block n ω) y0
          (fun n ↦ x n ω)
          (fun n ↦ y n ω))
    (k : ℕ) (ω : Ω) :
    x k ω ∈ dual_proximal_gradient_primal_x_argmax f LinearMap.id (∑ j, y k ω j) := by
  -- The realized DBPG trajectory owner already packages the step-(a) argmax membership.
  exact (is_dual_block_proximal_gradient_primal_trajectory_step (h_traj ω) k).1

/-- Helper for Theorem 12.14: a source argmax point for
`x' ↦ ⟪x', v⟫ - f x'` is exactly a conjugate-side subgradient at `v`. -/
lemma eval_mem_conjugate_subdifferential_of_mem_dual_primal_x_argmax
    (h_problem : IsDualBlockProximalGradientProblem f g σ)
    {v xBar : E}
    (hx : xBar ∈ dual_proximal_gradient_primal_x_argmax f LinearMap.id v) :
    Module.Dual.eval ℝ E xBar ∈
      subdifferential (conjugate_function f)
        (InnerProductSpace.toDualMap ℝ E v) := by
  have hf_convex_toReal :
      ConvexOn ℝ (effective_domain f) (fun z : E ↦ (f z).toReal) := by
    -- Strong convexity of `f` on its effective domain implies convexity of its real-valued part.
    exact (h_problem.f_strongly_convex.strictConvexOn σ.2).convexOn
  have hf_convex : is_convex_function f := by
    -- Convert the domainwise convexity statement back to the project owner `is_convex_function`.
    rw [is_convex_function_iff_convexOn_toReal (fun z _ ↦ h_problem.toIsProperExtendedRealFunction.ne_bot z)]
    exact hf_convex_toReal
  have hmax :
      IsMaxOn
        (fun x' : E ↦
          (((InnerProductSpace.toDualMap ℝ E v) x' : EReal) - f x'))
        Set.univ xBar := by
    -- Unfold the source argmax owner and rewrite the dual pairing as the Hilbert inner product.
    simpa [mem_dual_proximal_gradient_primal_x_argmax_iff,
      InnerProductSpace.toDualMap_apply_apply, real_inner_comm] using hx
  -- The Chapter 4 conjugacy bridge turns the source argmax condition into a conjugate subgradient.
  rw [subdifferential_conjugate_eq_eval_image_argmax_affine_minus
    f
    h_problem.toIsProperExtendedRealFunction
    h_problem.f_closed
    hf_convex
    (InnerProductSpace.toDualMap ℝ E v)]
  exact ⟨xBar, hmax, rfl⟩

/-- Helper for Theorem 12.14: a conjugate-side subgradient at `v` is the canonical gradient point
`∇(f∗)(v)` on the source route. -/
lemma conjugate_subgradient_eval_eq_gradient_point
    (h_problem : IsDualBlockProximalGradientProblem f g σ)
    {v xBar : E}
    (hx :
      Module.Dual.eval ℝ E xBar ∈
        subdifferential (conjugate_function f) (InnerProductSpace.toDualMap ℝ E v)) :
    xBar = ∇ (fun z : E ↦ ((f∗) z).toReal) v := by
  let φ : E →ₗ[ℝ] Module.Dual ℝ E :=
    ((LinearMap.toContinuousLinearMap : (Module.Dual ℝ E) ≃ₗ[ℝ] StrongDual ℝ E).symm).toLinearMap.comp
      ((InnerProductSpace.toDual ℝ E).toLinearEquiv.toLinearMap)
  let xDual : Module.Dual ℝ E :=
    (LinearMap.toContinuousLinearMap : (Module.Dual ℝ E) ≃ₗ[ℝ] StrongDual ℝ E).symm
      (InnerProductSpace.toDual ℝ E xBar)
  have hconj_finite :
      ∀ z : E, (f∗) z ≠ ⊥ ∧ (f∗) z < ⊤ := by
    intro z
    -- Strong convexity of `f` makes its conjugate finite-valued everywhere.
    simpa using
      dual_based_proximal_gradient_dual_F_primal_finite_valued
        (σ := σ)
        (f := f)
        (A := (LinearMap.id : E →ₗ[ℝ] E))
        h_problem.toIsProperExtendedRealFunction
        h_problem.f_closed
        h_problem.f_strongly_convex
        z
  have hconj_convex : is_convex_function (f∗) := by
    -- The conjugate objective is convex on the primal space.
    simpa using
      dual_based_proximal_gradient_dual_F_primal_convex
        (f := f)
        (A := (LinearMap.id : E →ₗ[ℝ] E))
  have hconj_diff :
      DifferentiableAt ℝ (fun z : E ↦ ((f∗) z).toReal) v := by
    -- Lemma 12.3 gives global differentiability of the conjugate under strong convexity.
    exact
      (conjugate_function_primal_is_l_smooth_on_of_proper_closed_strongConvexOn
        (σ := σ)
        (f := f)
        h_problem.toIsProperExtendedRealFunction
        h_problem.f_closed
        h_problem.f_strongly_convex).1 v (by simp)
  have hv_interior : v ∈ interior (finite_domain (f∗)) := by
    have hfinite_domain_univ : finite_domain (f∗) = Set.univ := by
      ext z
      constructor
      · intro _
        simp
      · intro _
        rcases hconj_finite z with ⟨hz_ne_bot, hz_lt_top⟩
        exact ⟨hz_lt_top, hz_ne_bot⟩
    -- Finite-valuedness everywhere identifies the interior with `Set.univ`.
    simpa [hfinite_domain_univ]
  have hx_primal : xDual ∈ subdifferential (f∗) v := by
    have hφ_apply (z : E) : φ z = (InnerProductSpace.toDualMap ℝ E z : Module.Dual ℝ E) := by
      ext w
      simp [φ, InnerProductSpace.toDual_apply_eq_toDualMap_apply]
    have hφdual :
        φ.dualMap (Module.Dual.eval ℝ E xBar) = xDual := by
      ext z
      simp [xDual, φ, InnerProductSpace.toDual_apply_eq_toDualMap_apply, real_inner_comm]
    have hpullback :
        φ.dualMap (Module.Dual.eval ℝ E xBar) ∈
          subdifferential (fun z : E ↦ conjugate_function f (φ z)) v := by
      -- Pull the given conjugate subgradient back through the Riesz identification.
      exact
        (subdifferential_precompose_affineMap_subset
          (f := conjugate_function f)
          (φ := φ.toAffineMap)
          (x := v))
          ⟨Module.Dual.eval ℝ E xBar, hx, rfl⟩
    have hsubset :
        (fun z : E ↦ conjugate_function f (φ z)) = (f∗) := by
      funext z
      simpa [hφ_apply z] using (conjugate_function_primal_apply f z).symm
    simpa [hsubset, hφdual] using hpullback
  have hx_strong :
      InnerProductSpace.toDual ℝ E xBar ∈ strongDualSubdifferential (f∗) v := by
    have hx_image :
        InnerProductSpace.toDual ℝ E xBar ∈
          (LinearMap.toContinuousLinearMap : (Module.Dual ℝ E) ≃ₗ[ℝ] StrongDual ℝ E) ''
            subdifferential (f∗) v := by
      refine ⟨xDual, hx_primal, ?_⟩
      ext z
      simp [xDual, InnerProductSpace.toDual_apply_eq_toDualMap_apply]
    simpa [strongDualSubdifferential_eq_image_subdifferential] using hx_image
  have hsingleton :=
    subdifferential_eq_singleton_gradient_of_differentiableAt
      (f := (f∗))
      v
      hconj_convex
      ⟨hv_interior, hconj_diff⟩
  have hx_eq_dual :
      InnerProductSpace.toDual ℝ E xBar =
        InnerProductSpace.toDual ℝ E
          (∇ (fun z : E ↦ ((f∗) z).toReal) v) := by
    have :
        InnerProductSpace.toDual ℝ E xBar ∈
          ({InnerProductSpace.toDual ℝ E
              (∇ (fun z : E ↦ ((f∗) z).toReal) v)} : Set (StrongDual ℝ E)) := by
      simpa [hsingleton] using hx_strong
    simpa using this
  -- Injectivity of the Riesz map identifies the primal point with the canonical gradient point.
  exact (InnerProductSpace.toDual ℝ E).injective hx_eq_dual

/-- Helper for Theorem 12.14: every source primal argmax witness is the canonical conjugate
gradient point `∇(f∗)(v)`. -/
lemma dual_primal_argmax_eq_conjugate_gradient
    (h_problem : IsDualBlockProximalGradientProblem f g σ)
    {v xBar : E}
    (hx : xBar ∈ dual_proximal_gradient_primal_x_argmax f LinearMap.id v) :
    xBar = ∇ (fun z : E ↦ ((f∗) z).toReal) v := by
  -- Follow the source route: argmax gives a conjugate subgradient, and differentiability of `f∗`
  -- collapses that subgradient to the singleton gradient point.
  exact
    conjugate_subgradient_eval_eq_gradient_point
      (f := f)
      (g := g)
      (σ := σ)
      h_problem
      (eval_mem_conjugate_subdifferential_of_mem_dual_primal_x_argmax
        (f := f)
        (g := g)
        (σ := σ)
        h_problem
        hx)

/-- Helper for Theorem 12.14: every optimal dual point minimizes the Chapter 11 minimization view
`Hdual = -q`. This is the source-faithful bridge from the source optimal set `Λ*` to the Chapter
11 owner `unconstrained_problem_solutions`. -/
lemma optimal_dual_point_mem_unconstrained_problem_solutions_minimization_view
    (h_problem : IsDualBlockProximalGradientProblem f g σ)
    {yStar : Fin p → E}
    (hyStar : yStar ∈ Λ*(f, g)) :
    yStar ∈
      unconstrained_problem_solutions (DualBlockMinimizationView.objective f g) := by
  -- Rewrite the Chapter 11 minimization surface to `-q`, then use the global maximality of
  -- `yStar` for the source-facing dual objective.
  rw [mem_unconstrained_problem_solutions_iff_forall_le]
  intro yBar
  have hmax_all : ∀ yBar' : Fin p → E, q(f, g) yBar' ≤ q(f, g) yStar := by
    simpa [mem_dual_block_proximal_gradient_dual_optimal_set, isMaxOn_univ_iff] using hyStar
  have hmax : q(f, g) yBar ≤ q(f, g) yStar := by
    exact hmax_all yBar
  -- Replace the Chapter 11 objective by `-q` on both points and negate the source inequality.
  rw [dual_block_dual_minimization_view_apply
      f g h_problem.toIsProperExtendedRealFunction h_problem.g_proper yStar,
    dual_block_dual_minimization_view_apply
      f g h_problem.toIsProperExtendedRealFunction h_problem.g_proper yBar]
  simpa using (EReal.neg_le_neg_iff.mpr hmax)

/-- Helper for Theorem 12.14: the blockwise affine update `w + 𝒰[i] d` changes the aggregated
coordinate sum by exactly the increment `d`. This is the canonical chain-rule bridge from the
block owner to the primal-space conjugate term. -/
lemma sum_block_coordinate_update
    (w : Fin p → E) (i : Fin p) (d : E) :
    (∑ j : Fin p, block_coordinate_update w i d j) = (∑ j : Fin p, w j) + d := by
  -- Expand the one-block update as `w + Pi.single i d` and sum the coordinates termwise.
  classical
  calc
    (∑ j : Fin p, block_coordinate_update w i d j)
        = ∑ j : Fin p, (block_coordinate_update w i d) j := by
            rfl
    _ = (∑ j : Fin p, w j) + ∑ j : Fin p, Pi.single i d j := by
          simp [block_coordinate_update, Finset.sum_add_distrib]
    _ = (∑ j : Fin p, w j) + d := by
          simp

/-- Helper for Theorem 12.14: summing the dual representatives of the block coordinates agrees
with the dual representative of the aggregated block sum. -/
lemma sumDual_eq_toDualMap_sum
    (w : Fin p → E) :
    (∑ j : Fin p, (InnerProductSpace.toDualMap ℝ E (w j) : Module.Dual ℝ E)) =
      InnerProductSpace.toDualMap ℝ E (∑ j : Fin p, w j) := by
  ext z
  simp [InnerProductSpace.toDualMap_apply_apply, sum_inner]

/-- Helper for Theorem 12.14: updating one block by `d` adds exactly the dual increment
`InnerProductSpace.toDualMap ℝ E d` to the aggregated dual sum. -/
lemma sumDual_blockCoordinateUpdate
    (w : Fin p → E) (i : Fin p) (d : E) :
    (∑ j : Fin p,
        (InnerProductSpace.toDualMap ℝ E (block_coordinate_update w i d j) :
          Module.Dual ℝ E)) =
      (InnerProductSpace.toDualMap ℝ E d : Module.Dual ℝ E) +
        ∑ j : Fin p, (InnerProductSpace.toDualMap ℝ E (w j) : Module.Dual ℝ E) := by
  -- Collapse both finite sums to the Riesz functional of the aggregated block sum.
  calc
    (∑ j : Fin p,
        (InnerProductSpace.toDualMap ℝ E (block_coordinate_update w i d j) :
          Module.Dual ℝ E)) =
      InnerProductSpace.toDualMap ℝ E
        (∑ j : Fin p, block_coordinate_update w i d j) := by
          exact sumDual_eq_toDualMap_sum (w := fun j ↦ block_coordinate_update w i d j)
    _ =
      InnerProductSpace.toDualMap ℝ E ((∑ j : Fin p, w j) + d) := by
        rw [sum_block_coordinate_update]
    _ =
      (InnerProductSpace.toDualMap ℝ E d : Module.Dual ℝ E) +
        InnerProductSpace.toDualMap ℝ E (∑ j : Fin p, w j) := by
          simpa [add_comm] using
            (InnerProductSpace.toDualMap ℝ E).map_add (∑ j : Fin p, w j) d
    _ =
      (InnerProductSpace.toDualMap ℝ E d : Module.Dual ℝ E) +
        ∑ j : Fin p, (InnerProductSpace.toDualMap ℝ E (w j) : Module.Dual ℝ E) := by
          rw [sumDual_eq_toDualMap_sum]

/-- Helper for Theorem 12.14: the minimization-view optimal value `FOpt = -q_opt` is the GLB of
`Hdual = -q` once a finite initial dual point and a finite optimal witness are fixed. -/
lemma dual_block_minimization_view_optimal_value_isGLB
    (h_problem : IsDualBlockProximalGradientProblem f g σ)
    (hyStar : yStar ∈ Λ*(f, g))
    (hy0_finite : y0 ∈ finite_domain (q(f, g)))
    (hyStar_finite : yStar ∈ finite_domain (q(f, g))) :
    IsGLB
      (Set.range (DualBlockMinimizationView.objective f g))
      (((-EReal.toReal (q_opt(f, g)) : ℝ)) : EReal) := by
  have hqOpt_ne_bot : q_opt(f, g) ≠ ⊥ := by
    intro hqOpt_bot
    have hle : q(f, g) y0 ≤ q_opt(f, g) :=
      dual_objective_le_dual_problem_value (f := f) (g := g) y0
    have hy0_ne_bot : q(f, g) y0 ≠ ⊥ := (mem_finite_domain.mp hy0_finite).2
    exact hy0_ne_bot (by simpa [hqOpt_bot] using hle)
  have hqOpt_ne_top : q_opt(f, g) ≠ ⊤ := by
    rw [← dual_block_proximal_gradient_dual_objective_eq_dual_problem_value_of_mem_optimal_set
      f g hyStar]
    exact (mem_finite_domain.mp hyStar_finite).1.ne
  have hqOpt_coe :
      (((EReal.toReal (q_opt(f, g)) : ℝ)) : EReal) = q_opt(f, g) :=
    EReal.coe_toReal hqOpt_ne_top hqOpt_ne_bot
  have hneg_qOpt_coe :
      (((-EReal.toReal (q_opt(f, g)) : ℝ)) : EReal) = -q_opt(f, g) := by
    -- Coerce the finite optimal value to `ℝ`, then negate on both sides.
    simpa using congrArg Neg.neg hqOpt_coe
  constructor
  · rintro _ ⟨yBar, rfl⟩
    have hmax : q(f, g) yBar ≤ q_opt(f, g) :=
      dual_objective_le_dual_problem_value (f := f) (g := g) yBar
    -- Rewrite the minimization-view value to `-q(yBar)` and compare it against `-q_opt`.
    calc
      (((-EReal.toReal (q_opt(f, g)) : ℝ)) : EReal) = -q_opt(f, g) := hneg_qOpt_coe
      _ ≤ -q(f, g) yBar := by
        simpa using (EReal.neg_le_neg_iff.mpr hmax)
      _ = DualBlockMinimizationView.objective f g yBar := by
            rw [dual_block_dual_minimization_view_apply
              f g h_problem.toIsProperExtendedRealFunction h_problem.g_proper yBar]
  · intro b hb
    have hyStar_lb :
        b ≤ DualBlockMinimizationView.objective f g yStar :=
      hb ⟨yStar, rfl⟩
    -- Evaluate the lower bound at the chosen optimizer and rewrite the value back to `-q_opt`.
    calc
      b ≤ DualBlockMinimizationView.objective f g yStar := hyStar_lb
      _ = -q(f, g) yStar := by
            rw [dual_block_dual_minimization_view_apply
              f g h_problem.toIsProperExtendedRealFunction h_problem.g_proper yStar]
      _ = -q_opt(f, g) := by
            rw [dual_block_proximal_gradient_dual_objective_eq_dual_problem_value_of_mem_optimal_set
              f g hyStar]
      _ = (((-EReal.toReal (q_opt(f, g)) : ℝ)) : EReal) := hneg_qOpt_coe.symm

/-- Helper for Theorem 12.14: a `PiLp` block vector lies in the effective domain of the separable
block penalty exactly when each coordinate lies in the corresponding block effective domain. -/
lemma mem_effective_domain_piLp_separableSum_iff
    (hg_proper : ∀ i : Fin p, IsProperExtendedRealFunction (g i))
    {z : PiLp (2 : ENNReal) (fun _ : Fin p ↦ E)} :
    z ∈ effective_domain (PiLp.separableSum g) ↔
      ∀ i : Fin p, z i ∈ effective_domain (g i) := by
  constructor
  · intro hz i
    -- A finite separable-sum value forces every coordinate block penalty to stay finite above.
    exact
      block_mem_effective_domain_of_mem_separableSum_effective_domain
        g hg_proper
        (by simpa [mem_effective_domain] using hz)
        i
  · intro hz
    -- Coordinatewise finite-domain membership makes the finite separable sum stay below `⊤`.
    rw [mem_effective_domain]
    exact
      ereal_sum_lt_top Finset.univ
        (fun i ↦ g i (z i))
        (fun i _ ↦ mem_effective_domain.mp (hz i))

/-- Helper for Theorem 12.14: if a scalar point is feasible for every block penalty, then its
duplicated block vector is feasible for the `PiLp` separable sum. -/
lemma constant_block_mem_effective_domain_piLp_separableSum
    (hg_proper : ∀ i : Fin p, IsProperExtendedRealFunction (g i))
    {xHat : E}
    (hxHat_g : ∀ i : Fin p, xHat ∈ effective_domain (g i)) :
    (dual_block_duplication E p).toLinearMap xHat ∈ effective_domain (PiLp.separableSum g) := by
  -- The duplicated block vector has every coordinate equal to `xHat`, so the coordinatewise
  -- effective-domain criterion closes immediately.
  rw [mem_effective_domain_piLp_separableSum_iff g hg_proper]
  simpa [dual_block_duplication_apply] using hxHat_g

/-- Helper for Theorem 12.14: the coordinatewise relative-interior witness from Assumption 12.14
already implies that the duplicated block vector lies in the effective domain of the `PiLp`
separable sum. -/
lemma constant_block_mem_effective_domain_piLp_separableSum_of_intrinsicInterior
    (hg_proper : ∀ i : Fin p, IsProperExtendedRealFunction (g i))
    {xHat : E}
    (hxHat_g : ∀ i : Fin p, xHat ∈ intrinsicInterior ℝ (effective_domain (g i))) :
    (dual_block_duplication E p).toLinearMap xHat ∈ effective_domain (PiLp.separableSum g) := by
  -- Strip only the set-membership content from the coordinatewise relative-interior witnesses.
  have hxHat_dom : ∀ i : Fin p, xHat ∈ effective_domain (g i) := by
    intro i
    exact intrinsicInterior_subset (hxHat_g i)
  exact constant_block_mem_effective_domain_piLp_separableSum g hg_proper hxHat_dom

/-- Helper for Theorem 12.14: the relative interiors of two sets combine to the relative interior
of their Cartesian product. This is the finite-product bridge needed before transporting the
coordinatewise qualification witness to the duplicated block owner. -/
private theorem mem_intrinsicInterior_prod
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {S : Set E} {T : Set V} {x : E} {z : V}
    (hx : x ∈ intrinsicInterior ℝ S)
    (hz : z ∈ intrinsicInterior ℝ T) :
    (x, z) ∈ intrinsicInterior ℝ (S ×ˢ T) := by
  -- Route correction: use the closed-ball characterization from Definition 3.7, then project the
  -- product affine-span condition to each coordinate before reusing the source witnesses.
  rcases (mem_intrinsicInterior_iff_closedBall_inter_affineSpan_subset).1 hx with
    ⟨hx_span, εS, hεS, hballS⟩
  rcases (mem_intrinsicInterior_iff_closedBall_inter_affineSpan_subset).1 hz with
    ⟨hz_span, εT, hεT, hballT⟩
  refine (mem_intrinsicInterior_iff_closedBall_inter_affineSpan_subset).2 ?_
  refine ⟨subset_affineSpan ℝ (S ×ˢ T) ⟨intrinsicInterior_subset hx, intrinsicInterior_subset hz⟩,
    min εS εT, lt_min hεS hεT, ?_⟩
  intro uv huv
  rcases uv with ⟨u, v⟩
  rcases huv with ⟨huv_ball, huv_span⟩
  have huv_dist : max (dist u x) (dist v z) ≤ min εS εT := by
    simpa [Prod.dist_eq, max_comm, max_left_comm, max_assoc] using huv_ball
  have hu_ball : u ∈ Metric.closedBall x εS := by
    exact Metric.mem_closedBall.2 <|
      le_trans ((max_le_iff.1 huv_dist).1) (min_le_left εS εT)
  have hv_ball : v ∈ Metric.closedBall z εT := by
    exact Metric.mem_closedBall.2 <|
      le_trans ((max_le_iff.1 huv_dist).2) (min_le_right εS εT)
  have hu_span_prod :
      u ∈ affineSpan ℝ (((LinearMap.fst ℝ E V).toAffineMap) '' (S ×ˢ T)) := by
    have hmem_map :
        u ∈ (affineSpan ℝ (S ×ˢ T)).map ((LinearMap.fst ℝ E V).toAffineMap) := by
      simpa using
        (AffineSubspace.mem_map_of_mem ((LinearMap.fst ℝ E V).toAffineMap) huv_span)
    rw [AffineSubspace.map_span] at hmem_map
    exact hmem_map
  have hv_span_prod :
      v ∈ affineSpan ℝ (((LinearMap.snd ℝ E V).toAffineMap) '' (S ×ˢ T)) := by
    have hmem_map :
        v ∈ (affineSpan ℝ (S ×ˢ T)).map ((LinearMap.snd ℝ E V).toAffineMap) := by
      simpa using
        (AffineSubspace.mem_map_of_mem ((LinearMap.snd ℝ E V).toAffineMap) huv_span)
    rw [AffineSubspace.map_span] at hmem_map
    exact hmem_map
  have hu_span : u ∈ affineSpan ℝ S := by
    refine (affineSpan_mono ℝ ?_) hu_span_prod
    rintro _ ⟨p, hp, rfl⟩
    exact hp.1
  have hv_span : v ∈ affineSpan ℝ T := by
    refine (affineSpan_mono ℝ ?_) hv_span_prod
    rintro _ ⟨p, hp, rfl⟩
    exact hp.2
  exact ⟨hballS ⟨hu_ball, hu_span⟩, hballT ⟨hv_ball, hv_span⟩⟩

/-- Helper for Theorem 12.14: the `PiLp` separable-sum effective domain is exactly the pullback of
the coordinatewise raw product domain along the canonical coordinate equivalence. -/
lemma effective_domain_piLp_separableSum_eq_preimage_raw_product
    (hg_proper : ∀ i : Fin p, IsProperExtendedRealFunction (g i)) :
    let e := PiLp.continuousLinearEquiv (2 : ENNReal) ℝ (fun _ : Fin p ↦ E)
    effective_domain (PiLp.separableSum g) =
      e ⁻¹' Set.pi Set.univ (fun i ↦ effective_domain (g i)) := by
  let e := PiLp.continuousLinearEquiv (2 : ENNReal) ℝ (fun _ : Fin p ↦ E)
  -- Evaluate the `PiLp` separable sum coordinatewise and then read off membership in the product
  -- of the block effective domains.
  ext z
  constructor
  · intro hz
    rw [Set.mem_preimage, Set.mem_univ_pi]
    intro i
    -- Finite separable-sum value forces the `i`th block penalty to stay finite.
    exact
      block_mem_effective_domain_of_mem_separableSum_effective_domain
        g hg_proper
        (by simpa [mem_effective_domain, PiLp.separableSum_apply] using hz)
        i
  · intro hz
    rw [Set.mem_preimage, Set.mem_univ_pi] at hz
    -- Coordinatewise finiteness of the block penalties makes the finite sum stay below `⊤`.
    rw [mem_effective_domain, PiLp.separableSum_apply]
    exact
      ereal_sum_lt_top Finset.univ
        (fun i ↦ g i (z.ofLp i))
        (fun i _ ↦ mem_effective_domain.mp (hz i))

/-- Helper for Theorem 12.14: intrinsic-interior membership pulls back along a continuous linear
equivalence after rewriting the target set as a preimage. -/
lemma mem_intrinsicInterior_preimage_of_continuousLinearEquiv
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (e : V ≃L[ℝ] W) {s : Set W} {x : V}
    (hx : e x ∈ intrinsicInterior ℝ s) :
    x ∈ intrinsicInterior ℝ (e ⁻¹' s) := by
  let eA : V ≃ᵃ[ℝ] W := e.toContinuousAffineEquiv.toAffineEquiv
  rcases (mem_intrinsicInterior_iff_closedBall_inter_affineSpan_subset).1 hx with
    ⟨hx_span, ε, hε, hball⟩
  have hx_mem_preimage : x ∈ e ⁻¹' s := by
    -- Intrinsic-interior membership lies inside the target set itself.
    simpa using intrinsicInterior_subset hx
  have hx_preimage : x ∈ affineSpan ℝ (e ⁻¹' s) := by
    -- The pullback point therefore belongs to the affine span of the pullback set.
    exact subset_affineSpan ℝ (e ⁻¹' s) hx_mem_preimage
  have hnhds :
      e ⁻¹' Metric.ball (e x) ε ∈ nhds x := by
    -- Continuity of the linear equivalence gives a small neighborhood sent into the target ball.
    have hcont : ContinuousAt e x := e.continuousAt
    exact hcont.preimage_mem_nhds (Metric.ball_mem_nhds _ hε)
  rcases Metric.mem_nhds_iff.1 hnhds with ⟨δ, hδ, hδball⟩
  refine (mem_intrinsicInterior_iff_closedBall_inter_affineSpan_subset).2 ?_
  refine ⟨hx_preimage, δ / 2, by positivity, ?_⟩
  intro u hu
  rcases hu with ⟨hu_ball, hu_span⟩
  have hu_ball' : u ∈ Metric.ball x δ := by
    refine Metric.closedBall_subset_ball ?_ hu_ball
    linarith
  have heu_ball : e u ∈ Metric.ball (e x) ε := hδball hu_ball'
  have heu_span_map :
      e u ∈ (affineSpan ℝ (e ⁻¹' s)).map eA.toAffineMap := by
    simpa [eA] using
      (AffineSubspace.mem_map_of_mem eA.toAffineMap hu_span)
  have heu_span :
      e u ∈ affineSpan ℝ s := by
    rw [AffineSubspace.map_span] at heu_span_map
    exact (affineSpan_mono ℝ (Set.image_preimage_subset e s)) heu_span_map
  -- Push the affine-span witness through `e` and use the source closed-ball characterization.
  exact hball ⟨Metric.mem_closedBall.2 (le_of_lt heu_ball), heu_span⟩

/-- Helper for Theorem 12.14: coordinatewise intrinsic-interior membership on the raw block owner
places the full block vector in the intrinsic interior of the coordinate product set. -/
lemma mem_intrinsicInterior_univ_pi_of_forall
    {s : Fin p → Set E} {v : Fin p → E}
    (hv : ∀ i : Fin p, v i ∈ intrinsicInterior ℝ (s i)) :
    v ∈ intrinsicInterior ℝ (Set.pi Set.univ s) := by
  classical
  induction p with
  | zero =>
      have hpi : Set.pi Set.univ s = (Set.univ : Set (Fin 0 → E)) := by
        ext w
        constructor
        · intro _
          trivial
        · intro _
          rw [Set.mem_pi]
          intro i _
          exact Fin.elim0 i
      -- In the zero-block case, the product set is the whole singleton function space.
      simpa [hpi, intrinsicInterior] using
        (show v ∈ intrinsicInterior ℝ (Set.univ : Set (Fin 0 → E)) by
          simp [intrinsicInterior])
  | succ p ih =>
      let e : (Fin (p + 1) → E) ≃L[ℝ] E × (Fin p → E) :=
        (Fin.consLinearEquiv ℝ (fun _ : Fin (p + 1) ↦ E)).symm.toContinuousLinearEquiv
      have hhead : v 0 ∈ intrinsicInterior ℝ (s 0) := hv 0
      have htail :
          (fun i : Fin p ↦ v i.succ) ∈
            intrinsicInterior ℝ (Set.pi Set.univ (fun i : Fin p ↦ s i.succ)) :=
        ih (fun i ↦ hv i.succ)
      have hprod :
          e v ∈
            intrinsicInterior ℝ
              (s 0 ×ˢ Set.pi Set.univ (fun i : Fin p ↦ s i.succ)) := by
        -- Split the finite product into its head coordinate and tail block family.
        simpa [e, Fin.tail] using
          (mem_intrinsicInterior_prod hhead htail)
      have hpre :
          v ∈ intrinsicInterior ℝ (e ⁻¹' (s 0 ×ˢ Set.pi Set.univ (fun i : Fin p ↦ s i.succ))) :=
        mem_intrinsicInterior_preimage_of_continuousLinearEquiv e hprod
      have hset :
          e ⁻¹' (s 0 ×ˢ Set.pi Set.univ (fun i : Fin p ↦ s i.succ)) = Set.pi Set.univ s := by
        ext w
        constructor
        · intro hw
          have hw' : w 0 ∈ s 0 ∧ ∀ i : Fin p, w i.succ ∈ s i.succ := by
            simpa [e, Fin.tail] using hw
          rw [Set.mem_pi]
          intro i _
          refine Fin.cases ?_ ?_ i
          · simpa using hw'.1
          · intro j
            simpa using hw'.2 j
        · intro hw
          rw [Set.mem_pi] at hw
          have hhead' : w 0 ∈ s 0 := hw 0 (by simp)
          have htail' : ∀ i : Fin p, w i.succ ∈ s i.succ := fun i ↦ hw i.succ (by simp)
          simpa [e, Fin.tail] using And.intro hhead' htail'
      -- Rewrite the product-set pullback back to the original finite product owner.
      rwa [hset] at hpre

/-- Helper for Theorem 12.14: the duplicated block vector inherits a `PiLp` relative-interior
witness from the coordinatewise block relative interiors. -/
lemma constant_block_mem_intrinsicInterior_piLp_separableSum_of_intrinsicInterior
    (hg_proper : ∀ i : Fin p, IsProperExtendedRealFunction (g i))
    {xHat : E}
    (hxHat_g : ∀ i : Fin p, xHat ∈ intrinsicInterior ℝ (effective_domain (g i))) :
    (dual_block_duplication E p).toLinearMap xHat ∈
      intrinsicInterior ℝ (effective_domain (PiLp.separableSum g)) := by
  let e := PiLp.continuousLinearEquiv (2 : ENNReal) ℝ (fun _ : Fin p ↦ E)
  have hraw :
      e ((dual_block_duplication E p).toLinearMap xHat) ∈
        intrinsicInterior ℝ (Set.pi Set.univ (fun i ↦ effective_domain (g i))) := by
    -- First build the raw product intrinsic-interior witness from the coordinatewise data.
    simpa [e, dual_block_duplication_apply] using
      (mem_intrinsicInterior_univ_pi_of_forall hxHat_g)
  -- Then transport that raw witness back to the `PiLp` owner through the coordinate equivalence.
  rw [effective_domain_piLp_separableSum_eq_preimage_raw_product g hg_proper]
  exact mem_intrinsicInterior_preimage_of_continuousLinearEquiv e hraw

/-- Helper for Theorem 12.14: Assumption 12.14 on the block problem should induce the Chapter
12.1 owner for the duplicated block-space model. -/
lemma dual_block_problem_to_dual_based_problem :
    IsDualBlockProximalGradientProblem f g σ →
    IsDualBasedProximalGradientProblem
      f
      (PiLp.separableSum g)
      (dual_block_duplication E p).toLinearMap
      σ := by
  intro h_problem
  -- Populate the Chapter 12.1 owner directly from the block assumptions; the only nontrivial
  -- source-faithful step is transporting the qualification witness to the duplicated `PiLp`
  -- block domain.
  let e := PiLp.continuousLinearEquiv (2 : ENNReal) ℝ (fun _ : Fin p ↦ E)
  have hsum_proper :
      IsProperExtendedRealFunction (separableSum g) :=
    separableSum_proper g h_problem.g_proper
  have hsum_closed :
      LowerSemicontinuous (separableSum g) :=
    separableSum_closed g h_problem.g_closed
  have hsum_convex :
      is_convex_function (separableSum g) :=
    separableSum_convex g h_problem.g_proper h_problem.g_convex
  refine
    { toIsProperExtendedRealFunction := h_problem.toIsProperExtendedRealFunction
      f_closed := h_problem.f_closed
      f_strongly_convex := h_problem.f_strongly_convex
      g_proper := by
        refine
          { ne_bot := ?_
            effective_domain_nonempty := ?_ }
        · intro z
          simpa [PiLp.separableSum, e] using hsum_proper.ne_bot (e z)
        · rcases hsum_proper.effective_domain_nonempty with ⟨z, hz⟩
          refine ⟨e.symm z, ?_⟩
          simpa [PiLp.separableSum, e, mem_effective_domain] using hz
      g_closed := by
        -- Lower semicontinuity transports along the coordinate equivalence to the `PiLp` owner.
        simpa [Function.comp, PiLp.separableSum, e] using hsum_closed.comp e.continuous
      g_convex := by
        -- Convexity is invariant under precomposition with the coordinate linear equivalence.
        simpa [PiLp.separableSum, e] using
          is_convex_function_precompose_linearMap_add hsum_convex e.toLinearMap 0
      qualification := ?_ }
  rcases IsDualBlockProximalGradientProblem.exists_mem_intrinsicInterior h_problem with
    ⟨xHat, hxHat_f, hxHat_g⟩
  refine ⟨xHat, hxHat_f, ?_⟩
  -- TODO: the remaining source-faithful bridge is exactly that the constant block vector
  -- `WithLp.toLp 2 (fun _ ↦ xHat)` lies in
  -- `intrinsicInterior ℝ (effective_domain (PiLp.separableSum g))` whenever
  -- `xHat ∈ intrinsicInterior ℝ (effective_domain (g i))` for every block `i`.
  have hdup_mem_dom :
      (dual_block_duplication E p).toLinearMap xHat ∈
        effective_domain (PiLp.separableSum g) := by
    -- First reduce the duplicated `PiLp` witness to plain coordinatewise domain membership.
    exact
      constant_block_mem_effective_domain_piLp_separableSum_of_intrinsicInterior
        g h_problem.g_proper hxHat_g
  have hdup_mem_span :
      (dual_block_duplication E p).toLinearMap xHat ∈
        affineSpan ℝ (effective_domain (PiLp.separableSum g)) := by
    -- The domain-membership part of the witness already places the duplicated point in the affine
    -- hull of the duplicated feasible core.
    exact subset_affineSpan ℝ (effective_domain (PiLp.separableSum g)) hdup_mem_dom
  have hdup_mem_ri :
      (dual_block_duplication E p).toLinearMap xHat ∈
        intrinsicInterior ℝ (effective_domain (PiLp.separableSum g)) := by
    -- Combine the coordinatewise witnesses on the raw block owner and then transport them back to
    -- the duplicated `PiLp` owner through the canonical coordinate equivalence.
    exact
      constant_block_mem_intrinsicInterior_piLp_separableSum_of_intrinsicInterior
        g h_problem.g_proper hxHat_g
  simpa [dual_block_duplication_apply] using hdup_mem_ri

/-- Helper for Theorem 12.14: the duplicated `PiLp` dual problem value agrees with the
source-facing block dual optimum `q_opt`. -/
lemma dual_block_problem_value_eq_duplicated_dual_problem_value
    (h_problem : IsDualBlockProximalGradientProblem f g σ) :
    dual_based_proximal_gradient_lagrange_dual_problem_value
        f
        (PiLp.separableSum g)
        (dual_block_duplication E p) =
      q_opt(f, g) := by
  let Y := PiLp (2 : ENNReal) (fun _ : Fin p ↦ E)
  -- Compare the two optimal values as suprema of the same pointwise objective, viewed once on the
  -- duplicated-owner dual space and once on the source block-dual owner.
  rw [dual_based_proximal_gradient_lagrange_dual_problem_value,
    dual_block_proximal_gradient_dual_problem_value_eq_sSup]
  apply le_antisymm
  · refine sSup_le ?_
    rintro z ⟨φ, rfl⟩
    let φc : StrongDual ℝ Y := LinearMap.toContinuousLinearMap φ
    rcases (InnerProductSpace.toDual ℝ Y).surjective φc with ⟨v, hv⟩
    have hφ : φ = InnerProductSpace.toDualMap ℝ Y v := by
      ext w
      have hw := congrArg (fun ψ : StrongDual ℝ Y ↦ ψ w) hv.symm
      simpa [φc, Y, InnerProductSpace.toDual_apply_eq_toDualMap_apply] using hw
    rw [hφ]
    have hobj :
        dual_based_proximal_gradient_lagrange_dual_objective
            f
            (PiLp.separableSum g)
            (dual_block_duplication E p)
            (InnerProductSpace.toDualMap ℝ Y v) =
          q(f, g) v := by
      calc
        dual_based_proximal_gradient_lagrange_dual_objective
            f
            (PiLp.separableSum g)
            (dual_block_duplication E p)
            (InnerProductSpace.toDualMap ℝ Y v) =
          dual_based_proximal_gradient_lagrange_dual_objective_primal
            f
            (PiLp.separableSum g)
            (dual_block_duplication E p)
            v := by
              simpa [Y] using
                (primalDualObjective_eq_dualOwner
                  (f := f)
                  (g := PiLp.separableSum g)
                  (A := dual_block_duplication E p)
                  (y := v)).symm
        _ = q(f, g) v := by
              simpa [Y] using
                (dual_block_proximal_gradient_lagrange_dual_objective_primal_eq_dual_objective
                  (f := f)
                  (g := g)
                  (hg_proper := h_problem.g_proper)
                  v)
    have hs :
        q(f, g) v ≤ sSup (Set.range (q(f, g))) :=
      le_sSup ⟨v, rfl⟩
    exact hobj.le.trans hs
  · refine sSup_le ?_
    rintro z ⟨v, rfl⟩
    have hobj :
        dual_based_proximal_gradient_lagrange_dual_objective
            f
            (PiLp.separableSum g)
            (dual_block_duplication E p)
            (InnerProductSpace.toDualMap ℝ Y (WithLp.toLp 2 v)) =
          q(f, g) v := by
      calc
        dual_based_proximal_gradient_lagrange_dual_objective
            f
            (PiLp.separableSum g)
            (dual_block_duplication E p)
            (InnerProductSpace.toDualMap ℝ Y (WithLp.toLp 2 v)) =
          dual_based_proximal_gradient_lagrange_dual_objective_primal
            f
            (PiLp.separableSum g)
            (dual_block_duplication E p)
            (WithLp.toLp 2 v) := by
              simpa [Y] using
                (primalDualObjective_eq_dualOwner
                  (f := f)
                  (g := PiLp.separableSum g)
                  (A := dual_block_duplication E p)
                  (y := WithLp.toLp 2 v)).symm
        _ = q(f, g) v := by
              simpa [PiLp.toLp_apply] using
                (dual_block_proximal_gradient_lagrange_dual_objective_primal_eq_dual_objective
                  (f := f)
                  (g := g)
                  (hg_proper := h_problem.g_proper)
                  (WithLp.toLp 2 v))
    have hs :
        q(f, g) v ≤
          sSup
            (Set.range
              (dual_based_proximal_gradient_lagrange_dual_objective
                f
                (PiLp.separableSum g)
                (dual_block_duplication E p))) := by
      calc
        q(f, g) v =
            dual_based_proximal_gradient_lagrange_dual_objective
              f
              (PiLp.separableSum g)
              (dual_block_duplication E p)
              (InnerProductSpace.toDualMap ℝ Y (WithLp.toLp 2 v)) := hobj.symm
        _ ≤
            sSup
              (Set.range
                (dual_based_proximal_gradient_lagrange_dual_objective
                  f
                  (PiLp.separableSum g)
                  (dual_block_duplication E p))) := by
              exact le_sSup ⟨InnerProductSpace.toDualMap ℝ Y (WithLp.toLp 2 v), rfl⟩
    exact hs

/-- Helper for Theorem 12.14: iterating the textbook one-step factor
`(p + n) / (p + n + 1)` yields the closed-form coefficient `p / (p + k + 1)`. -/
lemma sublinear_bound_of_dbpg_step_contraction
    {V : ℕ → ℝ}
    (h_step :
      ∀ n : ℕ, V (n + 1) ≤ ((p + n : ℝ) / (p + n + 1 : ℝ)) * V n)
    (k : ℕ) :
    V (k + 1) ≤ (p : ℝ) / (p + k + 1 : ℝ) * V 0 := by
  have hp_nat : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  induction k with
  | zero =>
      -- The initial contraction is exactly the `n = 0` instance of the one-step estimate.
      simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using h_step 0
  | succ k hk =>
      have hstep : V (k + 2) ≤ ((p + (k + 1) : ℝ) / (p + (k + 1) + 1 : ℝ)) * V (k + 1) := by
        -- Reindex the one-step contraction at time `k + 1`.
        simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using h_step (k + 1)
      have hfactor_nonneg :
          0 ≤ ((p + (k + 1) : ℝ) / (p + (k + 1) + 1 : ℝ)) := by
        positivity
      have hscaled :
          ((p + (k + 1) : ℝ) / (p + (k + 1) + 1 : ℝ)) * V (k + 1) ≤
            ((p + (k + 1) : ℝ) / (p + (k + 1) + 1 : ℝ)) *
              ((p : ℝ) / (p + k + 1 : ℝ) * V 0) :=
        mul_le_mul_of_nonneg_left hk hfactor_nonneg
      have hcoeff :
          ((p + (k + 1) : ℝ) / (p + (k + 1) + 1 : ℝ)) *
              ((p : ℝ) / (p + k + 1 : ℝ) * V 0) =
            (p : ℝ) / (p + (k + 1) + 1 : ℝ) * V 0 := by
        have hp_denom : (p + k + 1 : ℝ) ≠ 0 := by
          positivity
        have hsucc_denom : (p + (k + 1) + 1 : ℝ) ≠ 0 := by
          positivity
        -- Cancel the common factor `p + k + 1` between the two consecutive step coefficients.
        field_simp [hp_denom, hsucc_denom]
        ring
      -- The inductive step is the one-step contraction followed by the coefficient telescoping.
      calc
        V (k + 2)
            ≤ ((p + (k + 1) : ℝ) / (p + (k + 1) + 1 : ℝ)) * V (k + 1) := hstep
        _ ≤ ((p + (k + 1) : ℝ) / (p + (k + 1) + 1 : ℝ)) *
              ((p : ℝ) / (p + k + 1 : ℝ) * V 0) := hscaled
        _ = (p : ℝ) / (p + (k + 1) + 1 : ℝ) * V 0 := hcoeff
        _ = (p : ℝ) / (p + (k + 1 : ℕ) + 1 : ℝ) * V 0 := by
              simp [Nat.cast_add, add_assoc, add_left_comm, add_comm]

/-- Helper for Theorem 12.14: under integrability of the sampled dual objective, the expected dual
gap can be written as the expectation of the pointwise dual-gap random variable. -/
lemma expected_dual_gap_eq_integral_pointwise_gap
    (k : ℕ)
    (h_dual_value_integrable :
      Integrable (fun ω ↦ (q(f, g) (y (k + 1) ω)).toReal) μ) :
    EReal.toReal (q_opt(f, g)) - μ[fun ω ↦ (q(f, g) (y (k + 1) ω)).toReal] =
      μ[fun ω ↦ EReal.toReal (q_opt(f, g)) - (q(f, g) (y (k + 1) ω)).toReal] := by
  -- Move the constant optimum value inside the expectation using linearity of the integral.
  rw [integral_sub (integrable_const (EReal.toReal (q_opt(f, g)))) h_dual_value_integrable,
    integral_const]
  simp

/-- Helper for Theorem 12.14: the block slice of the minimization-view smooth term
`w ↦ (f∗)(∑ i, w_i)` has derivative given by the conjugate gradient at the aggregated sum. -/
lemma dual_block_minimization_view_block_partial_gradient_spec
    (h_problem : IsDualBlockProximalGradientProblem f g σ)
    (i : Fin p) (w : Fin p → E) :
    HasFDerivAt
      (block_coordinate_slice (DualBlockMinimizationView.smoothTerm f) w i)
      (InnerProductSpace.toDualMap ℝ E
        (gradient (fun z : E ↦ (((f∗) z).toReal)) (∑ j : Fin p, w j)))
      0 := by
  let φ : E → ℝ := fun z ↦ ((f∗) z).toReal
  have hdiffAt : DifferentiableAt ℝ φ (∑ j : Fin p, w j) := by
    -- Lemma 12.3 gives differentiability of the conjugate real lift at every aggregated dual sum.
    exact
      (conjugate_function_primal_is_l_smooth_on_of_proper_closed_strongConvexOn
        (σ := σ)
        (f := f)
        h_problem.toIsProperExtendedRealFunction
        h_problem.f_closed
        h_problem.f_strongly_convex).1
        (∑ j : Fin p, w j)
        (by simp)
  have hbase :
      HasFDerivAt
        φ
        (InnerProductSpace.toDualMap ℝ E (gradient φ (∑ j : Fin p, w j)))
        (∑ j : Fin p, w j) := by
    -- Rewrite differentiability into the Fréchet derivative shape used by the chain rule.
    simpa [φ] using hdiffAt.hasGradientAt.hasFDerivAt
  have hshift :
      HasFDerivAt
        (fun d : E ↦ (∑ j : Fin p, w j) + d)
        (ContinuousLinearMap.id ℝ E)
        0 := by
    -- The affine re-centering map `d ↦ ∑ w_j + d` has derivative `id`.
    simpa using
      ((ContinuousLinearMap.id ℝ E).hasFDerivAt.const_add (∑ j : Fin p, w j) :
        HasFDerivAt
          (fun d : E ↦ (∑ j : Fin p, w j) + (ContinuousLinearMap.id ℝ E d))
          (ContinuousLinearMap.id ℝ E)
          0)
  have hbase0 :
      HasFDerivAt
        φ
        (InnerProductSpace.toDualMap ℝ E (gradient φ (∑ j : Fin p, w j)))
        ((∑ j : Fin p, w j) + 0) := by
    simpa using hbase
  have hcomp := hbase0.comp 0 hshift
  have hslice :
      block_coordinate_slice (DualBlockMinimizationView.smoothTerm f) w i =
        fun d : E ↦ φ ((∑ j : Fin p, w j) + d) := by
    funext d
    simp [block_coordinate_slice_apply, DualBlockMinimizationView.smoothTerm_apply, φ,
      sum_block_coordinate_update, add_comm, add_left_comm, add_assoc]
  -- Route correction: rewrite the block slice through the aggregated block-sum normal form before
  -- consuming the composed derivative.
  rw [hslice]
  simpa using hcomp

/-- Helper for Theorem 12.14: the block gradient of the minimization-view smooth term is
`σ⁻¹`-Lipschitz along every coordinate direction. -/
lemma dual_block_minimization_view_block_partial_gradient_lipschitz
    (h_problem : IsDualBlockProximalGradientProblem f g σ)
    (i : Fin p) (w : Fin p → E) (d : E) :
    ‖(gradient (fun z : E ↦ (((f∗) z).toReal)) (∑ j : Fin p, w j)) -
        (gradient (fun z : E ↦ (((f∗) z).toReal))
          (∑ j : Fin p, block_coordinate_update w i d j))‖ ≤
      (σ⁻¹ : ℝ) * ‖d‖ := by
  let φ : E → ℝ := fun z ↦ ((f∗) z).toReal
  have hsmooth :
      is_l_smooth_on φ Set.univ (Real.toNNReal (1 / (σ : ℝ))) := by
    -- Lemma 12.3 gives the global `1 / σ` smoothness of the conjugate term on the primal space.
    simpa [φ] using
      conjugate_function_primal_is_l_smooth_on_of_proper_closed_strongConvexOn
        σ
        f
        h_problem.toIsProperExtendedRealFunction
        h_problem.f_closed
        h_problem.f_strongly_convex
  have hgrad :=
    (is_l_smooth_on_iff_forall_norm_sub_le.mp hsmooth).2
      (∑ j : Fin p, w j)
      (by simp)
      (∑ j : Fin p, block_coordinate_update w i d j)
      (by simp)
  have hσ_nonneg : 0 ≤ 1 / (σ : ℝ) := by
    exact div_nonneg (by norm_num) (le_of_lt σ.2)
  have hgrad' :
      ‖(gradient (fun z : E ↦ (((f∗) z).toReal)) (∑ j : Fin p, w j)) -
          (gradient (fun z : E ↦ (((f∗) z).toReal))
            (∑ j : Fin p, block_coordinate_update w i d j))‖ ≤
        (1 / (σ : ℝ)) * ‖∑ j : Fin p, w j - ∑ j : Fin p, block_coordinate_update w i d j‖ := by
    calc
      ‖(gradient (fun z : E ↦ (((f∗) z).toReal)) (∑ j : Fin p, w j)) -
          (gradient (fun z : E ↦ (((f∗) z).toReal))
            (∑ j : Fin p, block_coordinate_update w i d j))‖
          ≤ ((Real.toNNReal (1 / (σ : ℝ)) : NNReal) : ℝ) *
              ‖∑ j : Fin p, w j - ∑ j : Fin p, block_coordinate_update w i d j‖ :=
        hgrad
      _ = (1 / (σ : ℝ)) * ‖∑ j : Fin p, w j - ∑ j : Fin p, block_coordinate_update w i d j‖ := by
          have hσ_cast :
              (((Real.toNNReal (1 / (σ : ℝ)) : NNReal) : ℝ)) = 1 / (σ : ℝ) := by
            exact congrArg (fun x : NNReal => (x : ℝ)) (Real.toNNReal_of_nonneg hσ_nonneg)
          rw [hσ_cast]
  -- After rewriting the updated aggregated sum as `∑ w_j + d`, the global smoothness bound
  -- collapses to the desired one-block estimate.
  calc
    ‖(gradient (fun z : E ↦ (((f∗) z).toReal)) (∑ j : Fin p, w j)) -
        (gradient (fun z : E ↦ (((f∗) z).toReal))
          (∑ j : Fin p, block_coordinate_update w i d j))‖
        ≤ (1 / (σ : ℝ)) * ‖∑ j : Fin p, w j - ∑ j : Fin p, block_coordinate_update w i d j‖ :=
      hgrad'
    _ = (σ⁻¹ : ℝ) * ‖d‖ := by
      simp [sum_block_coordinate_update, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
        norm_neg]

/-- Helper for Theorem 12.14: the minimization view `Hdual = -q` satisfies the Chapter 11
randomized block proximal-gradient assumptions with constant block weight `σ⁻¹`. -/
lemma dual_block_minimization_view_randomized_assumptions
    (h_problem : IsDualBlockProximalGradientProblem f g σ)
    (hyStar : yStar ∈ Λ*(f, g))
    (hy0_finite : y0 ∈ finite_domain (q(f, g)))
    (hyStar_finite : yStar ∈ finite_domain (q(f, g))) :
    RandomizedBlockProximalGradientAssumptions
      (DualBlockMinimizationView.smoothTerm f)
      (fun i z ↦ ((g i)∗) (-z))
      (fun _ : Fin p ↦ fun w : Fin p → E ↦
        (∇ fun z : E ↦ (((f∗) z).toReal)) (∑ j : Fin p, w j))
      (unconstrained_problem_solutions (DualBlockMinimizationView.objective f g))
      (-EReal.toReal (q_opt(f, g)))
      (fun _ : Fin p ↦ σ⁻¹) := by
  let sumLinearMap : (Fin p → E) →ₗ[ℝ] E :=
    { toFun := fun w ↦ ∑ j : Fin p, w j
      map_add' := by
        intro w z
        simp [Finset.sum_add_distrib]
      map_smul' := by
        intro a w
        simp [Finset.smul_sum] }
  let sumCLM : (Fin p → E) →L[ℝ] E :=
    { toLinearMap := sumLinearMap
      cont := sumLinearMap.continuous_of_finiteDimensional }
  have hsmooth_domain_univ :
      effective_domain (DualBlockMinimizationView.smoothTerm (p := p) f) = Set.univ := by
    ext w
    constructor
    · intro _
      simp
    · intro _
      rw [mem_effective_domain, DualBlockMinimizationView.smoothTerm_apply]
      simpa using
        (dual_based_proximal_gradient_dual_F_primal_finite_valued
          (σ := σ)
          (f := f)
          (A := (LinearMap.id : E →ₗ[ℝ] E))
          h_problem.toIsProperExtendedRealFunction
          h_problem.f_closed
          h_problem.f_strongly_convex
          (∑ j : Fin p, w j)).2
  have hsmooth_convex :
      is_convex_function (DualBlockMinimizationView.smoothTerm (p := p) f) := by
    -- Pull convexity of `f∗` back along the block-sum linear map.
    simpa [sumLinearMap, DualBlockMinimizationView.smoothTerm_apply] using
      is_convex_function_precompose_linearMap_add
        (f := (f∗))
        (conjugate_function_closed_and_convex f).2
        sumLinearMap
        0
  have hsmooth_precompose :
      is_l_smooth_on
        (fun w : Fin p → E ↦ ((f∗) (sumCLM w)).toReal)
        Set.univ
        (Real.toNNReal (1 / (σ : ℝ)) * ‖sumCLM‖₊ ^ (2 : ℕ)) := by
    -- Global smoothness of `z ↦ ((f∗) z).toReal` is stable under linear precomposition.
    exact
      Example_10_44.is_l_smooth_on_precompose_continuousLinearMap
        sumCLM
        (fun z : E ↦ ((f∗) z).toReal)
        (conjugate_function_primal_is_l_smooth_on_of_proper_closed_strongConvexOn
          (σ := σ)
          (f := f)
          h_problem.toIsProperExtendedRealFunction
          h_problem.f_closed
          h_problem.f_strongly_convex)
  have hsmooth_diff_univ :
      DifferentiableOn
        ℝ
        (fun w : Fin p → E ↦ (DualBlockMinimizationView.smoothTerm (p := p) f w).toReal)
        Set.univ := by
    have hsmooth_toReal_eq :
        (fun w : Fin p → E ↦ ((f∗) (sumCLM w)).toReal) =
          fun w : Fin p → E ↦ (DualBlockMinimizationView.smoothTerm (p := p) f w).toReal := by
      funext w
      simp [sumCLM, sumLinearMap, DualBlockMinimizationView.smoothTerm_apply]
    intro w hw
    -- Differentiate the precomposed smooth conjugate on the whole block space.
    rw [← hsmooth_toReal_eq]
    exact (hsmooth_precompose.1 w (by simp)).differentiableWithinAt
  have hsmooth_closed :
      LowerSemicontinuous (DualBlockMinimizationView.smoothTerm (p := p) f) := by
    -- Lower semicontinuity of `f∗` is stable under continuous precomposition.
    have hclosed :
        LowerSemicontinuous (fun w : Fin p → E ↦ (f∗) (sumCLM w)) :=
      (conjugate_function_closed_and_convex f).1.comp sumCLM.continuous
    simpa [sumCLM, DualBlockMinimizationView.smoothTerm_apply] using hclosed
  have hyStar_minimization :
      yStar ∈ unconstrained_problem_solutions (DualBlockMinimizationView.objective f g) := by
    -- The source dual optimizer is exactly a minimizer of the Chapter 11 minimization view.
    exact
      optimal_dual_point_mem_unconstrained_problem_solutions_minimization_view
        (σ := σ)
        (f := f)
        (g := g)
        h_problem
        hyStar
  refine
    RandomizedBlockProximalGradientAssumptions.ofIsBlockProximalGradientProblem ?_ hsmooth_convex ?_
  · refine
      { f_ne_bot := ?_
        block_g_proper := ?_
        block_g_closed := ?_
        block_g_convex := ?_
        f_closed := hsmooth_closed
        g_effective_domain_subset_interior_f_effective_domain := ?_
        optimal_set_eq := rfl
        optimal_set_nonempty := ⟨yStar, hyStar_minimization⟩
        optimal_value_isGLB :=
          dual_block_minimization_view_optimal_value_isGLB
            (σ := σ)
            (f := f)
            (g := g)
            (y0 := y0)
            (yStar := yStar)
            h_problem
            hyStar
            hy0_finite
            hyStar_finite
        block_partial_gradient_spec := ?_
        block_partial_gradient_lipschitz := ?_ }
    · intro w
      -- Properness of `f` prevents the smooth conjugate term from taking the value `⊥`.
      simpa [DualBlockMinimizationView.smoothTerm_apply, conjugate_function_primal_apply] using
        conjugate_function_ne_bot_of_proper
          f
          h_problem.toIsProperExtendedRealFunction
          (InnerProductSpace.toDualMap ℝ E (∑ j : Fin p, w j))
    · intro i
      -- Each block penalty `g_i^*(-·)` is proper by Lemma 12.3.
      exact
        dual_based_proximal_gradient_dual_G_primal_proper
          (g i)
          (h_problem.g_proper i)
          (h_problem.g_convex i)
    · intro i
      -- Closedness of `g_i^*(-·)` is the corresponding closedness half of the same Lemma 12.3
      -- companion.
      exact
        (dual_based_proximal_gradient_dual_G_primal_closed_and_convex (g i)).1
    · intro i
      -- Convexity of `g_i^*(-·)` is the convex half of the same Chapter 12 companion.
      exact
        (dual_based_proximal_gradient_dual_G_primal_closed_and_convex (g i)).2
    · intro w hw
      -- The smooth minimization-view term is finite everywhere, so its interior effective domain
      -- is all of block space.
      simpa [hsmooth_domain_univ]
    · intro i w hw
      -- The block-slice derivative is the conjugate gradient at the aggregated block sum.
      exact
        dual_block_minimization_view_block_partial_gradient_spec
          (σ := σ)
          (f := f)
          (g := g)
          h_problem
          i
          w
    · intro i w d hw hwd
      -- The global `1 / σ` smoothness of the conjugate gives the blockwise Lipschitz bound.
      exact
        dual_block_minimization_view_block_partial_gradient_lipschitz
          (σ := σ)
          (f := f)
          (g := g)
          h_problem
          i
          w
          d
  · -- Route correction: after identifying the smooth-term effective domain with `Set.univ`, the
    -- differentiability field is just the global differentiability of the precomposed conjugate.
    simpa [hsmooth_domain_univ] using hsmooth_diff_univ

/-- Helper for Theorem 12.14: the sampled block-dual iterate at time `k + 1` should stay in the
finite domain of the dual objective along every realized DBPG trajectory. -/
lemma randomized_dbpg_dual_iterate_mem_finite_domain
    (h_problem : IsDualBlockProximalGradientProblem f g σ)
    (h_traj :
      ∀ ω,
        is_dual_block_proximal_gradient_primal_trajectory
          f g σ (fun n ↦ sampled_block n ω) y0
          (fun n ↦ x n ω)
          (fun n ↦ y n ω))
    (hy0_finite : y0 ∈ finite_domain (q(f, g)))
    (k : ℕ) :
    ∀ ω, y (k + 1) ω ∈ finite_domain (q(f, g)) := by
  have hy_all : ∀ n : ℕ, ∀ ω, y n ω ∈ finite_domain (q(f, g)) := by
    intro n
    induction n with
    | zero =>
        intro ω
        -- The realized DBPG trajectory starts from the prescribed finite initial dual point.
        simpa [is_dual_block_proximal_gradient_primal_trajectory_zero (h_traj ω)] using hy0_finite
    | succ n ihn =>
        intro ω
        -- One primal-representation DBPG step preserves finiteness of the source dual value.
        exact
          dual_block_primal_y_step_mem_finite_domain
            (σ := σ)
            (f := f)
            (g := g)
            h_problem
            (ihn ω)
            (is_dual_block_proximal_gradient_primal_trajectory_step (h_traj ω) n).2
  -- Specialize the global iterate invariant to the sampled time `k + 1`.
  intro ω
  exact hy_all (k + 1) ω

/-- Helper for Theorem 12.14: each realized DBPG sample path coincides with the Chapter 11
randomized block proximal-gradient recursion on the minimization view `Hdual = -q`. -/
lemma randomized_dbpg_realized_minimization_view_method_eq
    (h_problem : IsDualBlockProximalGradientProblem f g σ)
    (h_traj :
      ∀ ω,
        is_dual_block_proximal_gradient_primal_trajectory
          f g σ (fun n ↦ sampled_block n ω) y0
          (fun n ↦ x n ω)
          (fun n ↦ y n ω))
    (hRBPG :
      RandomizedBlockProximalGradientAssumptions
        (DualBlockMinimizationView.smoothTerm f)
        (fun i z ↦ ((g i)∗) (-z))
        (fun _ : Fin p ↦ fun w : Fin p → E ↦
          (∇ fun z : E ↦ (((f∗) z).toReal)) (∑ j : Fin p, w j))
        (unconstrained_problem_solutions (DualBlockMinimizationView.objective f g))
        (-EReal.toReal (q_opt(f, g)))
        (fun _ : Fin p ↦ σ⁻¹))
    (hy0_eff :
      y0 ∈ effective_domain (DualBlockMinimizationView.regularizer g)) :
    ∀ ω n,
      y n ω =
        randomized_block_proximal_gradient_method
          hRBPG.toIsBlockProximalGradientProblem
          (hRBPG.interior_effective_domain_point ⟨y0, hy0_eff⟩)
          (fun m ↦ sampled_block m ω)
          n := by
  intro ω n
  induction n with
  | zero =>
      -- The realized DBPG path and the Chapter 11 RBPG path start from the same initial point.
      simpa [randomized_block_proximal_gradient_method_zero,
        is_dual_block_proximal_gradient_primal_trajectory_zero (h_traj ω)] using
        (hRBPG.toIsBlockProximalGradientProblem.interior_effective_domain_point_coe
          ⟨y0, hy0_eff⟩).symm
  | succ n ihn =>
      let hcore := hRBPG.toIsBlockProximalGradientProblem
      let yRBPG :=
        randomized_block_proximal_gradient_method
          hcore
          (hRBPG.interior_effective_domain_point ⟨y0, hy0_eff⟩)
          (fun m ↦ sampled_block m ω)
          n
      have hσ0 : (σ : ℝ) ≠ 0 := ne_of_gt σ.2
      have hσ : (1 / (σ⁻¹ : PosReal) : ℝ) = (σ : ℝ) := by
        change (1 : ℝ) / ((σ : ℝ)⁻¹) = (σ : ℝ)
        field_simp [hσ0]
      have hstep :
          y (n + 1) ω ∈
            dual_block_proximal_gradient_dual_step
              (fun i z ↦ ((g i)∗) (-z))
              (∇ fun z : E ↦ (((f∗) z).toReal))
              σ
              (sampled_block n ω)
              yRBPG := by
        have hx_argmax :
            x n ω ∈ dual_proximal_gradient_primal_x_argmax
              f
              LinearMap.id
              (∑ j : Fin p, y n ω j) := by
          exact (is_dual_block_proximal_gradient_primal_trajectory_step (h_traj ω) n).1
        have hx_eq :
            x n ω = ∇ (fun z : E ↦ ((f∗) z).toReal) (∑ j : Fin p, y n ω j) := by
          exact
            dual_primal_argmax_eq_conjugate_gradient
              (f := f)
              (g := g)
              (σ := σ)
              h_problem
              hx_argmax
        have hprimal_step :
            y (n + 1) ω ∈
              dual_block_proximal_gradient_primal_y_step
                g
                σ
                ((∇ fun z : E ↦ (((f∗) z).toReal)) (∑ j : Fin p, y n ω j))
                (y n ω)
                (sampled_block n ω) := by
          simpa [hx_eq] using (is_dual_block_proximal_gradient_primal_trajectory_step (h_traj ω) n).2
        -- Rewrite the realized Chapter 12 step onto the already-identified Chapter 11 current
        -- iterate.
        simpa [yRBPG, ihn] using
          (dual_block_proximal_gradient_dual_step_iff_mem_dual_block_proximal_gradient_primal_y_step
            (f := f)
            (g := g)
            (σ := σ)
            h_problem.toIsProperExtendedRealFunction
            h_problem.f_closed
            h_problem.f_strongly_convex
            h_problem.g_proper
            h_problem.g_closed
            h_problem.g_convex
            (sampled_block n ω)
            (y (n + 1) ω)
            (y n ω)).2 hprimal_step
      rw [randomized_block_proximal_gradient_method_succ]
      rw [mem_dual_block_proximal_gradient_dual_step_iff] at hstep
      rcases hstep with ⟨hactive, hrest⟩
      have hprox :
          prox[(((σ : ℝ) : EReal) • (fun z : E ↦ ((g (sampled_block n ω))∗) (-z)))]
              (yRBPG (sampled_block n ω) -
                (σ : ℝ) •
                  ((∇ fun z : E ↦ (((f∗) z).toReal)) (∑ j : Fin p, yRBPG j))) =
            {hcore.prox_point (σ⁻¹) (sampled_block n ω) yRBPG} := by
        -- The owner-level prox point is the unique active-block proximal point of the
        -- minimization-view Chapter 11 problem.
        simpa [IsBlockProximalGradientProblem.prox_point, hσ] using
          block_partial_prox_grad_point_eq_singleton
            (fun i z ↦ ((g i)∗) (-z))
            (fun _ : Fin p ↦ fun w : Fin p → E ↦
              (∇ fun z : E ↦ (((f∗) z).toReal)) (∑ j : Fin p, w j))
            hcore.block_g_proper
            hcore.block_g_closed
            hcore.block_g_convex
            (σ⁻¹)
            (sampled_block n ω)
            yRBPG
      have hactive_eq :
          y (n + 1) ω (sampled_block n ω) =
            hcore.prox_point (σ⁻¹) (sampled_block n ω) yRBPG := by
        -- The active block belongs to a singleton proximal set, so its value is the owner-level
        -- prox point.
        rw [hprox] at hactive
        simpa using hactive
      -- Compare the updated block and all untouched blocks separately.
      ext j
      by_cases hj : j = sampled_block n ω
      · subst hj
        simpa [yRBPG, block_coordinate_update] using hactive_eq
      · simpa [yRBPG, block_coordinate_update_apply_ne, hj] using hrest j hj

/-- Helper for Theorem 12.14: the sampled dual objective at time `k + 1` should be integrable
because the realized DBPG iterate depends only on finitely many uniformly sampled blocks. -/
lemma randomized_dbpg_dual_value_integrable
    (h_problem : IsDualBlockProximalGradientProblem f g σ)
    (h_traj :
      ∀ ω,
        is_dual_block_proximal_gradient_primal_trajectory
          f g σ (fun n ↦ sampled_block n ω) y0
          (fun n ↦ x n ω)
          (fun n ↦ y n ω))
    (h_sampled_block_meas : ∀ k, Measurable (sampled_block k))
    (h_sampled_block_indep : iIndepFun sampled_block μ)
    (h_sampled_block_uniform :
      ∀ k (i : Fin p), μ ((sampled_block k) ⁻¹' {i}) = 1 / (p : ℝ≥0∞))
    (hyStar : yStar ∈ Λ*(f, g))
    (hy0_finite : y0 ∈ finite_domain (q(f, g)))
    (hyStar_finite : yStar ∈ finite_domain (q(f, g)))
    (k : ℕ) :
    Integrable (fun ω ↦ (q(f, g) (y (k + 1) ω)).toReal) μ := by
  let Hsmooth : (Fin p → E) → EReal := DualBlockMinimizationView.smoothTerm f
  let G : Fin p → E → EReal := fun i z ↦ ((g i)∗) (-z)
  let Hdual : (Fin p → E) → EReal := DualBlockMinimizationView.objective f g
  have hRBPG :=
    dual_block_minimization_view_randomized_assumptions
      (σ := σ)
      (f := f)
      (g := g)
      (y0 := y0)
      (yStar := yStar)
      h_problem
      hyStar
      hy0_finite
      hyStar_finite
  have hy0_eff :
      y0 ∈ effective_domain (separableSum G) :=
    initial_dual_point_mem_effective_domain_minimization_view
      f
      g
      y0
      h_problem.toIsProperExtendedRealFunction
      h_problem.g_proper
      hy0_finite
  have hpath :
      ∀ ω n,
        y n ω =
          randomized_block_proximal_gradient_method
            hRBPG.toIsBlockProximalGradientProblem
            (hRBPG.interior_effective_domain_point ⟨y0, hy0_eff⟩)
            (fun m ↦ sampled_block m ω)
            n :=
    randomized_dbpg_realized_minimization_view_method_eq
      (σ := σ)
      (f := f)
      (g := g)
      (y0 := y0)
      (sampled_block := sampled_block)
      (x := x)
      (y := y)
      h_problem
      h_traj
      hRBPG
      hy0_eff
  have hobjective_integrable :
      Integrable
        (fun ω ↦
          (Hdual
            (randomized_block_proximal_gradient_method
              hRBPG.toIsBlockProximalGradientProblem
              (hRBPG.interior_effective_domain_point ⟨y0, hy0_eff⟩)
              (fun m ↦ sampled_block m ω)
              (k + 1))).toReal)
        μ := by
    let history : Ω → Fin k → Fin p :=
      fun ω ↦ randomized_block_history (fun m ↦ sampled_block m ω) k
    let joint : Ω → (Fin k → Fin p) × Fin p :=
      fun ω ↦ (history ω, sampled_block k ω)
    let ψ : (Fin k → Fin p) → Fin p → ℝ :=
      fun ξ i ↦
        (Hdual
          (randomized_block_proximal_gradient_method
            hRBPG.toIsBlockProximalGradientProblem
            (hRBPG.interior_effective_domain_point ⟨y0, hy0_eff⟩)
            (rbpgHistoryWithCurrent k ξ i)
            (k + 1))).toReal
    let φ : ((Fin k → Fin p) × Fin p) → ℝ := fun z ↦ ψ z.1 z.2
    have hhistory_meas : Measurable history := by
      -- The frozen history is measurable because each coordinate is one sampled block.
      refine measurable_pi_lambda _ fun t ↦ ?_
      simpa [history, randomized_block_history] using h_sampled_block_meas t
    have hjoint_meas : Measurable joint := by
      -- Pairing the frozen history with the current block preserves measurability.
      exact hhistory_meas.prodMk (h_sampled_block_meas k)
    have hrepr :
        (fun ω ↦
          (Hdual
            (randomized_block_proximal_gradient_method
              hRBPG.toIsBlockProximalGradientProblem
              (hRBPG.interior_effective_domain_point ⟨y0, hy0_eff⟩)
              (fun m ↦ sampled_block m ω)
              (k + 1))).toReal) =
          fun ω ↦ ψ (history ω) (sampled_block k ω) := by
      -- Rewrite the `(k + 1)`-st iterate through the frozen-history/current-block decomposition.
      funext ω
      have hω :=
        rbpgPathwiseIterate_succ_eq_historyCurrent
          hRBPG
          ⟨y0, hy0_eff⟩
          sampled_block
          ω
          k
      simpa [rbpg_pathwise_iterate, history, ψ] using
        congrArg (fun z ↦ (Hdual z).toReal) hω
    have hφ_int : Integrable φ (μ.map joint) := by
      -- Any real observable of the finite joint state `(ξ₀, …, ξ_{k-1}, i_k)` is integrable.
      exact Integrable.of_finite
    have hjoint_int :
        Integrable (fun ω ↦ ψ (history ω) (sampled_block k ω)) μ := by
      simpa [joint, φ] using hφ_int.comp_measurable hjoint_meas
    rw [hrepr]
    exact hjoint_int
  have hneg_integrable :
      Integrable (fun ω ↦ - (q(f, g) (y (k + 1) ω)).toReal) μ := by
    -- Rewrite the Chapter 11 observable back to the source dual objective `q` pointwise.
    refine hobjective_integrable.congr ?_
    refine Filter.Eventually.of_forall ?_
    intro ω
    have hpathω := hpath ω (k + 1)
    calc
      (Hdual
          (randomized_block_proximal_gradient_method
            hRBPG.toIsBlockProximalGradientProblem
            (hRBPG.interior_effective_domain_point ⟨y0, hy0_eff⟩)
            (fun m ↦ sampled_block m ω)
            (k + 1))).toReal
          = (Hdual (y (k + 1) ω)).toReal := by
              simpa [hpathω]
      _ = (- q(f, g) (y (k + 1) ω)).toReal := by
            simpa [Hdual] using
              congrArg EReal.toReal
                (dual_block_dual_minimization_view_apply
                  f
                  g
                  h_problem.toIsProperExtendedRealFunction
                  h_problem.g_proper
                  (y (k + 1) ω))
      _ = - (q(f, g) (y (k + 1) ω)).toReal := by
            simp
  -- Negating the observable one more time recovers the desired source-facing integrability.
  simpa using hneg_integrable.neg

/-- Helper for Theorem 12.14: after normalizing the realized primal argmax point to the canonical
gradient of `f∗`, each realized DBPG successor lies in the Chapter 12 dual-step owner written in
the minimization-view variables. -/
lemma realized_dbpg_dual_step_mem_canonical_dual_step
    (h_problem : IsDualBlockProximalGradientProblem f g σ)
    (h_traj :
      ∀ ω,
        is_dual_block_proximal_gradient_primal_trajectory
          f g σ (fun n ↦ sampled_block n ω) y0
          (fun n ↦ x n ω)
          (fun n ↦ y n ω))
    (k : ℕ) (ω : Ω) :
    y (k + 1) ω ∈
      dual_block_proximal_gradient_dual_step
        (fun j z ↦ ((g j)∗) (-z))
        (∇ fun z : E ↦ (((f∗) z).toReal))
        σ
        (sampled_block k ω)
        (y k ω) := by
  have hx_argmax :
      x k ω ∈ dual_proximal_gradient_primal_x_argmax
        f
        LinearMap.id
        (∑ j : Fin p, y k ω j) := by
    -- Extract the source argmax clause from the realized trajectory owner.
    exact (is_dual_block_proximal_gradient_primal_trajectory_step (h_traj ω) k).1
  have hx_eq :
      x k ω = ∇ (fun z : E ↦ ((f∗) z).toReal) (∑ j : Fin p, y k ω j) := by
    -- Route correction: normalize the source argmax witness before transporting the step owner.
    exact
      dual_primal_argmax_eq_conjugate_gradient
        (f := f)
        (g := g)
        (σ := σ)
        h_problem
        hx_argmax
  have hprimal_step :
      y (k + 1) ω ∈
        dual_block_proximal_gradient_primal_y_step
          g
          σ
          ((∇ fun z : E ↦ (((f∗) z).toReal)) (∑ j : Fin p, y k ω j))
          (y k ω)
          (sampled_block k ω) := by
    -- Rewrite the realized primal-representation step using the canonical gradient point.
    simpa [hx_eq] using (is_dual_block_proximal_gradient_primal_trajectory_step (h_traj ω) k).2
  -- Lemma 12.15 converts the primal-representation step into the dual-step owner exactly.
  exact
    (dual_block_proximal_gradient_dual_step_iff_mem_dual_block_proximal_gradient_primal_y_step
      (f := f)
      (g := g)
      (σ := σ)
      h_problem.toIsProperExtendedRealFunction
      h_problem.f_closed
      h_problem.f_strongly_convex
      h_problem.g_proper
      h_problem.g_closed
      h_problem.g_convex
      (sampled_block k ω)
      (y (k + 1) ω)
      (y k ω)).2 hprimal_step

/-- Helper for Theorem 12.14: at each realized iterate, the Chapter 12.7 primal-vs-dual-gap
estimate on the duplicated block model yields the scalar dual-gap bound used in part (2). -/
lemma dbpg_pointwise_primal_sqdist_le_dual_gap_at_succ
    (h_problem : IsDualBlockProximalGradientProblem f g σ)
    (h_traj :
      ∀ ω,
        is_dual_block_proximal_gradient_primal_trajectory
          f g σ (fun n ↦ sampled_block n ω) y0
          (fun n ↦ x n ω)
          (fun n ↦ y n ω))
    (hyStar : yStar ∈ Λ*(f, g))
    (hyStar_finite : yStar ∈ finite_domain (q(f, g)))
    (xStar : E)
    (hxStar : IsMinOn F Set.univ xStar)
    (k : ℕ)
    (ω : Ω)
    (hy_finite : y (k + 1) ω ∈ finite_domain (q(f, g))) :
    ‖x (k + 1) ω - xStar‖ ^ (2 : ℕ) ≤
      (2 / (σ : ℝ)) *
        (EReal.toReal (q_opt(f, g)) - (q(f, g) (y (k + 1) ω)).toReal) := by
  have h_problem_dup :
      IsDualBasedProximalGradientProblem
        f
        (PiLp.separableSum g)
        (dual_block_duplication E p).toLinearMap
        σ :=
    dual_block_problem_to_dual_based_problem
      (σ := σ)
      (f := f)
      (g := g)
      h_problem
  have hx_argmax_sum :
      x (k + 1) ω ∈ dual_proximal_gradient_primal_x_argmax
        f
        LinearMap.id
        (∑ j : Fin p, y (k + 1) ω j) :=
    realized_dbpg_primal_argmax_at
      (f := f)
      (g := g)
      (σ := σ)
      (y0 := y0)
      (sampled_block := sampled_block)
      (x := x)
      (y := y)
      h_traj
      (k + 1)
      ω
  have hx_argmax_dup :
      x (k + 1) ω ∈
        dual_proximal_gradient_primal_x_argmax
          f
          (dual_block_duplication E p).toLinearMap
          (WithLp.toLp 2 (y (k + 1) ω)) := by
    -- Transport the realized argmax condition to the duplicated `PiLp` owner used by
    -- Lemma 12.7.
    exact
      (mem_dual_primal_x_argmax_duplication_iff
        (f := f)
        (n := p)
        (x := x (k + 1) ω)
        (v := y (k + 1) ω)).2 hx_argmax_sum
  have hdup_gap :
      ((((σ : ℝ) / 2) * ‖x (k + 1) ω - xStar‖ ^ (2 : ℕ) : ℝ) : EReal) ≤
        dual_based_proximal_gradient_lagrange_dual_problem_value
            f
            (PiLp.separableSum g)
            (dual_block_duplication E p) -
          dual_based_proximal_gradient_lagrange_dual_objective_primal
            f
            (PiLp.separableSum g)
            (dual_block_duplication E p)
            (WithLp.toLp 2 (y (k + 1) ω)) := by
    -- Apply Lemma 12.7 exactly on the duplicated block-space model.
    exact
      half_sigma_sqdist_le_dual_gap_of_primal_argmax
        (σ := σ)
        (f := f)
        (g := PiLp.separableSum g)
        (A := dual_block_duplication E p)
        h_problem_dup
        (WithLp.toLp 2 (y (k + 1) ω))
        (x (k + 1) ω)
        xStar
        hx_argmax_dup
        hxStar
  have hgap_ereal :
      ((((σ : ℝ) / 2) * ‖x (k + 1) ω - xStar‖ ^ (2 : ℕ) : ℝ) : EReal) ≤
        q_opt(f, g) - q(f, g) (y (k + 1) ω) := by
    -- Rewrite the duplicated-model dual gap back to the source-facing block-dual gap.
    calc
      ((((σ : ℝ) / 2) * ‖x (k + 1) ω - xStar‖ ^ (2 : ℕ) : ℝ) : EReal) ≤
          dual_based_proximal_gradient_lagrange_dual_problem_value
              f
              (PiLp.separableSum g)
              (dual_block_duplication E p) -
            dual_based_proximal_gradient_lagrange_dual_objective_primal
              f
              (PiLp.separableSum g)
              (dual_block_duplication E p)
              (WithLp.toLp 2 (y (k + 1) ω)) :=
        hdup_gap
      _ = q_opt(f, g) - q(f, g) (y (k + 1) ω) := by
        rw [dual_block_problem_value_eq_duplicated_dual_problem_value
          (σ := σ) (f := f) (g := g) h_problem]
        simpa [PiLp.toLp_apply] using
          congrArg
            (fun t : EReal => q_opt(f, g) - t)
            (dual_block_proximal_gradient_lagrange_dual_objective_primal_eq_dual_objective
              (f := f)
              (g := g)
              (hg_proper := h_problem.g_proper)
              (WithLp.toLp 2 (y (k + 1) ω)))
  have hqOpt_ne_top : q_opt(f, g) ≠ ⊤ := by
    -- The attained optimal value is finite above because the chosen optimal witness lies in the
    -- finite domain of `q`.
    rw [← dual_block_proximal_gradient_dual_objective_eq_dual_problem_value_of_mem_optimal_set
      f g hyStar]
    exact (mem_finite_domain.mp hyStar_finite).1.ne
  have hgap_ne_top : q_opt(f, g) - q(f, g) (y (k + 1) ω) ≠ ⊤ := by
    -- Subtracting a finite-above dual value from a finite-above optimum cannot hit `⊤`.
    have hneg_ne_top : -q(f, g) (y (k + 1) ω) ≠ ⊤ := by
      simpa [EReal.neg_eq_top_iff] using (mem_finite_domain.mp hy_finite).2
    simpa [sub_eq_add_neg] using EReal.add_ne_top hqOpt_ne_top hneg_ne_top
  have hgap_real :
      ((σ : ℝ) / 2) * ‖x (k + 1) ω - xStar‖ ^ (2 : ℕ) ≤
        EReal.toReal (q_opt(f, g) - q(f, g) (y (k + 1) ω)) := by
    -- Push the finite `EReal` comparison down to `ℝ`.
    exact EReal.toReal_le_toReal hgap_ereal (EReal.coe_ne_bot _) hgap_ne_top
  have hgap_scalar :
      ((σ : ℝ) / 2) * ‖x (k + 1) ω - xStar‖ ^ (2 : ℕ) ≤
        EReal.toReal (q_opt(f, g)) - (q(f, g) (y (k + 1) ω)).toReal := by
    -- Replace the right-hand side by the already verified scalar dual-gap identity.
    simpa using
      (hgap_real.trans_eq
        (dual_gap_toReal_eq_of_mem_finite_domain
          (f := f)
          (g := g)
          (yBar := y (k + 1) ω)
          (yStar := yStar)
          hyStar
          hyStar_finite
          hy_finite))
  have hσ_pos : 0 < (σ : ℝ) := σ.2
  have hscaled :
      (σ : ℝ) * ‖x (k + 1) ω - xStar‖ ^ (2 : ℕ) ≤
        (σ : ℝ) *
          ((2 / (σ : ℝ)) *
            (EReal.toReal (q_opt(f, g)) - (q(f, g) (y (k + 1) ω)).toReal)) := by
    calc
      (σ : ℝ) * ‖x (k + 1) ω - xStar‖ ^ (2 : ℕ)
          = 2 * (((σ : ℝ) / 2) * ‖x (k + 1) ω - xStar‖ ^ (2 : ℕ)) := by ring
      _ ≤
          2 *
            (EReal.toReal (q_opt(f, g)) - (q(f, g) (y (k + 1) ω)).toReal) := by
            gcongr
      _ =
          (σ : ℝ) *
            ((2 / (σ : ℝ)) *
              (EReal.toReal (q_opt(f, g)) - (q(f, g) (y (k + 1) ω)).toReal)) := by
            field_simp [show (σ : ℝ) ≠ 0 by exact ne_of_gt hσ_pos]
  -- Cancel the positive factor `σ` from both sides to recover the displayed squared-distance
  -- estimate.
  exact le_of_mul_le_mul_left hscaled hσ_pos

-- Proof sketch: condition on the sampled-block history generated by `sampled_block`, use the
-- one-step randomized DBPG Lyapunov contraction for
-- `(1 / (2 σ)) ‖y^k - y*‖² + q_opt - q(y^k)`, average over the uniformly sampled block, and
-- iterate the recursion to obtain the factor `p / (p + k + 1)`. Finally identify the optimal
-- value by `dual_block_proximal_gradient_dual_objective_eq_dual_problem_value_of_mem_optimal_set`.
/-- Helper for Theorem 12.14: with the full DBPG assumptions made explicit, the Chapter 11
randomized objective-gap theorem on the minimization view `Hdual = -q` yields the expected
dual-gap estimate in the canonical block `L²` coordinates. -/
lemma randomized_dbpg_expected_dual_gap_le_of_assumptions_l2_view
    (k : ℕ)
    (h_problem : IsDualBlockProximalGradientProblem f g σ)
    (h_traj :
      ∀ ω,
        is_dual_block_proximal_gradient_primal_trajectory
          f g σ (fun n ↦ sampled_block n ω) y0
          (fun n ↦ x n ω)
          (fun n ↦ y n ω))
    (h_sampled_block_meas : ∀ k, Measurable (sampled_block k))
    (h_sampled_block_indep : iIndepFun sampled_block μ)
    (h_sampled_block_uniform :
      ∀ k (i : Fin p), μ ((sampled_block k) ⁻¹' {i}) = 1 / (p : ℝ≥0∞))
    (hyStar : yStar ∈ Λ*(f, g))
    (hy0_finite : y0 ∈ finite_domain (q(f, g)))
    (hyStar_finite : yStar ∈ finite_domain (q(f, g)))
    (h_dual_value_finite : ∀ ω, y (k + 1) ω ∈ finite_domain (q(f, g)))
    (h_dual_value_integrable : Integrable (fun ω ↦ (q(f, g) (y (k + 1) ω)).toReal) μ) :
    EReal.toReal (q_opt(f, g)) - μ[fun ω ↦ (q(f, g) (y (k + 1) ω)).toReal] ≤
      (p : ℝ) / (p + k + 1 : ℝ) *
        ((1 / (2 * (σ : ℝ))) * ‖WithLp.toLp 2 (y0 - yStar)‖ ^ (2 : ℕ) +
          EReal.toReal (q_opt(f, g)) - (q(f, g) y0).toReal) := by
  let Hdual : (Fin p → E) → EReal := DualBlockMinimizationView.objective f g
  let G : Fin p → E → EReal := fun i z ↦ ((g i)∗) (-z)
  have hRBPG :=
    dual_block_minimization_view_randomized_assumptions
      (σ := σ)
      (f := f)
      (g := g)
      (y0 := y0)
      (yStar := yStar)
      h_problem
      hyStar
      hy0_finite
      hyStar_finite
  have hy0_eff :
      y0 ∈ effective_domain (DualBlockMinimizationView.regularizer g) :=
    initial_dual_point_mem_effective_domain_minimization_view
      f
      g
      y0
      h_problem.toIsProperExtendedRealFunction
      h_problem.g_proper
      hy0_finite
  have hyStar_minimization :
      yStar ∈ unconstrained_problem_solutions (DualBlockMinimizationView.objective f g) := by
    -- The Chapter 12 optimal dual point is the Chapter 11 minimizer of `Hdual = -q`.
    exact
      optimal_dual_point_mem_unconstrained_problem_solutions_minimization_view
        (σ := σ)
        (f := f)
        (g := g)
        h_problem
        hyStar
  have hpath :
      ∀ ω n,
        y n ω =
          rbpg_pathwise_iterate
            hRBPG
            ⟨y0, hy0_eff⟩
            sampled_block
            ω
            n := by
    intro ω n
    -- The realized DBPG path is exactly the RBPG path on the minimization view.
    simpa [rbpg_pathwise_iterate] using
      randomized_dbpg_realized_minimization_view_method_eq
        (σ := σ)
        (f := f)
        (g := g)
        (y0 := y0)
        (sampled_block := sampled_block)
        (x := x)
        (y := y)
        h_problem
        h_traj
        hRBPG
        hy0_eff
        ω
        n
  have hobjective_integrable :
      Integrable (fun ω ↦ (Hdual (y (k + 1) ω)).toReal) μ := by
    -- Rewrite `Hdual = -q` pointwise and reuse the assumed integrability of the sampled dual
    -- value.
    refine h_dual_value_integrable.neg.congr ?_
    refine Filter.Eventually.of_forall ?_
    intro ω
    have hobj :
        Hdual (y (k + 1) ω) = -q(f, g) (y (k + 1) ω) := by
      simpa [Hdual] using
        dual_block_dual_minimization_view_apply
          f
          g
          h_problem.toIsProperExtendedRealFunction
          h_problem.g_proper
          (y (k + 1) ω)
    simpa [hobj]
  have hpointwise_gap :
      ∀ ω,
        (Hdual (y (k + 1) ω)).toReal - (-EReal.toReal (q_opt(f, g))) =
          EReal.toReal (q_opt(f, g)) - (q(f, g) (y (k + 1) ω)).toReal := by
    intro ω
    -- Rewrite first to the finite `EReal` dual gap, then use the scalar dual-gap identity.
    calc
      (Hdual (y (k + 1) ω)).toReal - (-EReal.toReal (q_opt(f, g))) =
          (q_opt(f, g) - q(f, g) (y (k + 1) ω)).toReal := by
            simpa [Hdual] using
              dual_block_minimization_view_gap_toReal_eq_dual_gap
                f
                g
                h_problem.toIsProperExtendedRealFunction
                h_problem.g_proper
                hyStar
                hyStar_finite
                (h_dual_value_finite ω)
      _ =
          EReal.toReal (q_opt(f, g)) - (q(f, g) (y (k + 1) ω)).toReal := by
            simpa using
              dual_gap_toReal_eq_of_mem_finite_domain
                (f := f)
                (g := g)
                (yBar := y (k + 1) ω)
                (yStar := yStar)
                hyStar
                hyStar_finite
                (h_dual_value_finite ω)
  have hgap_integral :
      μ[fun ω ↦ (Hdual (y (k + 1) ω)).toReal] - (-EReal.toReal (q_opt(f, g))) =
        EReal.toReal (q_opt(f, g)) -
          μ[fun ω ↦ (q(f, g) (y (k + 1) ω)).toReal] := by
    -- Separate the constant-shift rewrite from the pointwise dual-gap rewrite to keep the final
    -- normalization stable.
    calc
      μ[fun ω ↦ (Hdual (y (k + 1) ω)).toReal] - (-EReal.toReal (q_opt(f, g))) =
          μ[fun ω ↦ (Hdual (y (k + 1) ω)).toReal] -
            μ[fun _ : Ω ↦ -EReal.toReal (q_opt(f, g))] := by
              simpa [integral_const]
      _ =
          μ[fun ω ↦
            (Hdual (y (k + 1) ω)).toReal - (-EReal.toReal (q_opt(f, g)))] := by
              symm
              exact
                integral_sub
                  hobjective_integrable
                  (integrable_const (-EReal.toReal (q_opt(f, g))))
      _ =
          μ[fun ω ↦
            EReal.toReal (q_opt(f, g)) -
              (q(f, g) (y (k + 1) ω)).toReal] := by
                apply integral_congr_ae
                exact Filter.Eventually.of_forall hpointwise_gap
      _ =
          EReal.toReal (q_opt(f, g)) -
            μ[fun ω ↦ (q(f, g) (y (k + 1) ω)).toReal] := by
              symm
              exact
                expected_dual_gap_eq_integral_pointwise_gap
                  (f := f)
                  (g := g)
                  (y := y)
                  k
                  h_dual_value_integrable
  have hgap_eq :
      rbpg_expected_objective_gap
          hRBPG
          ⟨y0, hy0_eff⟩
          sampled_block
          μ
          (k + 1) =
        EReal.toReal (q_opt(f, g)) -
          μ[fun ω ↦ (q(f, g) (y (k + 1) ω)).toReal] := by
    rw [rbpg_expected_objective_gap_apply]
    have hpath_integral :
        μ[fun ω ↦
          (composite_model_objective
            (DualBlockMinimizationView.smoothTerm f)
            (separableSum G)
            (rbpg_pathwise_iterate hRBPG ⟨y0, hy0_eff⟩ sampled_block ω (k + 1))).toReal] =
          μ[fun ω ↦ (Hdual (y (k + 1) ω)).toReal] := by
      -- Rewrite the Chapter 11 pathwise iterate back to the realized DBPG iterate.
      apply integral_congr_ae
      refine Filter.Eventually.of_forall ?_
      intro ω
      simpa [Hdual, G, rbpg_pathwise_iterate] using
        congrArg
          (fun z ↦ (DualBlockMinimizationView.objective f g z).toReal)
          (hpath ω (k + 1)).symm
    rw [hpath_integral]
    exact hgap_integral
  have hinit_eq :
      rbpg_initial_lyapunov
          (fun _ : Fin p ↦ σ⁻¹)
          (-EReal.toReal (q_opt(f, g)))
          Hdual
          y0
          yStar =
        (1 / (2 * (σ : ℝ))) * ‖WithLp.toLp 2 (y0 - yStar)‖ ^ (2 : ℕ) +
          EReal.toReal (q_opt(f, g)) - (q(f, g) y0).toReal := by
    rw [rbpg_initial_lyapunov_def]
    have hobj0 :
        (Hdual y0).toReal = - (q(f, g) y0).toReal := by
      -- Evaluate `Hdual = -q` at the initial dual point and take real parts.
      simpa [Hdual] using
        congrArg EReal.toReal
          (dual_block_dual_minimization_view_apply
            f
            g
            h_problem.toIsProperExtendedRealFunction
            h_problem.g_proper
            y0)
    rw [hobj0]
    -- The Chapter 11 weighted initial norm is exactly the displayed block `L²` Lyapunov term.
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (congrArg
        (fun t : ℝ ↦ t + (- (q(f, g) y0).toReal - -EReal.toReal (q_opt(f, g))))
        (half_weighted_sqnorm_eq_initial_lyapunov σ y0 yStar))
  have hsublinear :
      rbpg_expected_objective_gap
          hRBPG
          ⟨y0, hy0_eff⟩
          sampled_block
          μ
          (k + 1) ≤
        (p : ℝ) / (p + k + 1 : ℝ) *
          rbpg_initial_lyapunov
            (fun _ : Fin p ↦ σ⁻¹)
            (-EReal.toReal (q_opt(f, g)))
            Hdual
            y0
            yStar := by
    -- This is exactly Theorem 11.11 specialized to the minimization-view Chapter 12 owner.
    simpa [Hdual, G] using
      randomized_block_proximal_gradient_expected_objective_gap_le_sublinear
        hRBPG
        ⟨y0, hy0_eff⟩
        sampled_block
        μ
        yStar
        hyStar_minimization
        h_sampled_block_meas
        h_sampled_block_indep
        (fun n i ↦ by
          simpa using h_sampled_block_uniform n i)
        k
  calc
    EReal.toReal (q_opt(f, g)) - μ[fun ω ↦ (q(f, g) (y (k + 1) ω)).toReal] =
        rbpg_expected_objective_gap
          hRBPG
          ⟨y0, hy0_eff⟩
          sampled_block
          μ
          (k + 1) := hgap_eq.symm
    _ ≤
        (p : ℝ) / (p + k + 1 : ℝ) *
          rbpg_initial_lyapunov
            (fun _ : Fin p ↦ σ⁻¹)
            (-EReal.toReal (q_opt(f, g)))
            Hdual
            y0
            yStar := hsublinear
    _ =
        (p : ℝ) / (p + k + 1 : ℝ) *
          ((1 / (2 * (σ : ℝ))) * ‖WithLp.toLp 2 (y0 - yStar)‖ ^ (2 : ℕ) +
            EReal.toReal (q_opt(f, g)) - (q(f, g) y0).toReal) := by
              rw [hinit_eq]

/-- Helper for Theorem 12.14: the rate bounds use the transported block `L²` norm on
`Fin p → E`. -/
local instance block_l2_normedAddCommGroup : NormedAddCommGroup (Fin p → E) :=
  PiLp.normedAddCommGroupToPi 2 (fun _ : Fin p ↦ E)

section

include sampled_block x h_problem h_traj h_sampled_block_meas h_sampled_block_indep
  h_sampled_block_uniform hyStar hy0_finite hyStar_finite

/-- Theorem 12.14 (1): for primal and dual sequences generated by the dual block proximal-gradient
method with randomized uniformly sampled block order, if the sampled dual objective value is
integrable and the relevant dual points lie in the finite domain of `q`, then the expected dual
objective gap satisfies the sublinear estimate
`q_opt - E[q(y^{k+1})] ≤ (p / (p + k + 1)) ((1 / (2σ)) ‖y^0 - y*‖² + q_opt - q(y^0))`. -/
theorem randomized_dual_block_proximal_gradient_expected_dual_gap_le
    (k : ℕ)
    (h_dual_value_finite : ∀ ω, y (k + 1) ω ∈ finite_domain (q(f, g)))
    (h_dual_value_integrable : Integrable (fun ω ↦ (q(f, g) (y (k + 1) ω)).toReal) μ) :
    EReal.toReal (q_opt(f, g)) - μ[fun ω ↦ (q(f, g) (y (k + 1) ω)).toReal] ≤
      (p : ℝ) / (p + k + 1 : ℝ) *
        ((1 / (2 * (σ : ℝ))) * ‖y0 - yStar‖ ^ (2 : ℕ) +
          EReal.toReal (q_opt(f, g)) - (q(f, g) y0).toReal) :=
by
  -- Instantiate the already proved explicit-assumptions wrapper from the Chapter 11 reduction.
  have h_l2 :
      EReal.toReal (q_opt(f, g)) - μ[fun ω ↦ (q(f, g) (y (k + 1) ω)).toReal] ≤
        (p : ℝ) / (p + k + 1 : ℝ) *
          ((1 / (2 * (σ : ℝ))) * ‖WithLp.toLp 2 y0 - WithLp.toLp 2 yStar‖ ^ (2 : ℕ) +
            EReal.toReal (q_opt(f, g)) - (q(f, g) y0).toReal) := by
    simpa [WithLp.toLp_sub] using
      randomized_dbpg_expected_dual_gap_le_of_assumptions_l2_view
        (μ := μ)
        (σ := σ)
        (f := f)
        (g := g)
        (y0 := y0)
        (sampled_block := sampled_block)
        (x := x)
        (y := y)
        (yStar := yStar)
        k
        h_problem
        h_traj
        h_sampled_block_meas
        h_sampled_block_indep
        h_sampled_block_uniform
        hyStar
        hy0_finite
        hyStar_finite
        h_dual_value_finite
        h_dual_value_integrable
  have hnorm :
      ‖WithLp.toLp 2 y0 - WithLp.toLp 2 yStar‖ ^ (2 : ℕ) = ‖y0 - yStar‖ ^ (2 : ℕ) := by
    rw [← WithLp.toLp_sub]
    have hnorm_eq : ‖WithLp.toLp 2 (y0 - yStar)‖ = ‖y0 - yStar‖ := by
      simpa using
        (PiLp.norm_seminormedAddCommGroupToPi
          (p := 2)
          (α := fun _ : Fin p ↦ E)
          (y0 - yStar)).symm
    rw [hnorm_eq]
  calc
    EReal.toReal (q_opt(f, g)) - μ[fun ω ↦ (q(f, g) (y (k + 1) ω)).toReal] ≤
        (p : ℝ) / (p + k + 1 : ℝ) *
          ((1 / (2 * (σ : ℝ))) * ‖WithLp.toLp 2 y0 - WithLp.toLp 2 yStar‖ ^ (2 : ℕ) +
            EReal.toReal (q_opt(f, g)) - (q(f, g) y0).toReal) :=
      h_l2
    _ =
        (p : ℝ) / (p + k + 1 : ℝ) *
          ((1 / (2 * (σ : ℝ))) * ‖y0 - yStar‖ ^ (2 : ℕ) +
            EReal.toReal (q_opt(f, g)) - (q(f, g) y0).toReal) := by
      rw [hnorm]

end

lemma expected_primal_sqdist_le_of_dual_gap_bound
    (xStar : E) (k : ℕ)
    (h_problem : IsDualBlockProximalGradientProblem f g σ)
    (h_traj :
      ∀ ω,
        is_dual_block_proximal_gradient_primal_trajectory
          f g σ (fun n ↦ sampled_block n ω) y0
          (fun n ↦ x n ω)
          (fun n ↦ y n ω))
    (h_sampled_block_meas : ∀ k, Measurable (sampled_block k))
    (h_sampled_block_indep : iIndepFun sampled_block μ)
    (h_sampled_block_uniform :
      ∀ k (i : Fin p), μ ((sampled_block k) ⁻¹' {i}) = 1 / (p : ℝ≥0∞))
    (hyStar : yStar ∈ Λ*(f, g))
    (hy0_finite : y0 ∈ finite_domain (q(f, g)))
    (hyStar_finite : yStar ∈ finite_domain (q(f, g)))
    (h_primal_sqdist_integrable :
      Integrable (fun ω ↦ ‖x (k + 1) ω - xStar‖ ^ (2 : ℕ)) μ)
    (h_dual_value_finite : ∀ ω, y (k + 1) ω ∈ finite_domain (q(f, g)))
    (h_dual_value_integrable :
      Integrable (fun ω ↦ (q(f, g) (y (k + 1) ω)).toReal) μ)
    (h_pointwise :
      ∀ ω,
        ‖x (k + 1) ω - xStar‖ ^ (2 : ℕ) ≤
          (2 / (σ : ℝ)) *
            (EReal.toReal (q_opt(f, g)) - (q(f, g) (y (k + 1) ω)).toReal)) :
    μ[fun ω ↦ ‖x (k + 1) ω - xStar‖ ^ (2 : ℕ)] ≤
      2 * (p : ℝ) / ((σ : ℝ) * (p + k + 1 : ℝ)) *
        ((1 / (2 * (σ : ℝ))) * ‖y0 - yStar‖ ^ (2 : ℕ) +
          EReal.toReal (q_opt(f, g)) - (q(f, g) y0).toReal) :=
by
  have h_gap_integrable :
      Integrable
        (fun ω ↦ EReal.toReal (q_opt(f, g)) - (q(f, g) (y (k + 1) ω)).toReal) μ := by
    -- Subtracting the constant dual optimum preserves integrability of the sampled dual gap.
    exact (integrable_const (EReal.toReal (q_opt(f, g)))).sub h_dual_value_integrable
  have h_scaled_gap_integrable :
      Integrable
        (fun ω ↦
          (2 / (σ : ℝ)) *
            (EReal.toReal (q_opt(f, g)) - (q(f, g) (y (k + 1) ω)).toReal)) μ := by
    -- The pointwise Chapter 12 bound is integrated after scaling by the deterministic factor
    -- `2 / σ`.
    exact h_gap_integrable.const_mul (2 / (σ : ℝ))
  have h_integral_le :
      μ[fun ω ↦ ‖x (k + 1) ω - xStar‖ ^ (2 : ℕ)] ≤
        μ[fun ω ↦
          (2 / (σ : ℝ)) *
            (EReal.toReal (q_opt(f, g)) - (q(f, g) (y (k + 1) ω)).toReal)] := by
    -- Integrate the pointwise primal-vs-dual-gap comparison from the source proof.
    exact
      integral_mono_ae
        h_primal_sqdist_integrable
        h_scaled_gap_integrable
        (Filter.Eventually.of_forall h_pointwise)
  have h_dual_gap_bound :
      EReal.toReal (q_opt(f, g)) - μ[fun ω ↦ (q(f, g) (y (k + 1) ω)).toReal] ≤
        (p : ℝ) / (p + k + 1 : ℝ) *
          ((1 / (2 * (σ : ℝ))) * ‖y0 - yStar‖ ^ (2 : ℕ) +
            EReal.toReal (q_opt(f, g)) - (q(f, g) y0).toReal) :=
    randomized_dual_block_proximal_gradient_expected_dual_gap_le
      (μ := μ)
      (σ := σ)
      (f := f)
      (g := g)
      (y0 := y0)
      (sampled_block := sampled_block)
      (x := x)
      (y := y)
      (h_problem := h_problem)
      (h_traj := h_traj)
      (h_sampled_block_meas := h_sampled_block_meas)
      (h_sampled_block_indep := h_sampled_block_indep)
      (h_sampled_block_uniform := h_sampled_block_uniform)
      (yStar := yStar)
      (hyStar := hyStar)
      (hy0_finite := hy0_finite)
      (hyStar_finite := hyStar_finite)
      k
      h_dual_value_finite
      h_dual_value_integrable
  have h_scaled_dual_gap_bound :
      (2 / (σ : ℝ)) *
          (EReal.toReal (q_opt(f, g)) - μ[fun ω ↦ (q(f, g) (y (k + 1) ω)).toReal]) ≤
        (2 / (σ : ℝ)) *
          ((p : ℝ) / (p + k + 1 : ℝ) *
            ((1 / (2 * (σ : ℝ))) * ‖y0 - yStar‖ ^ (2 : ℕ) +
              EReal.toReal (q_opt(f, g)) - (q(f, g) y0).toReal)) := by
    -- The scalar factor `2 / σ` is nonnegative, so it preserves the expected dual-gap bound.
    have hscale_nonneg : 0 ≤ 2 / (σ : ℝ) := by
      exact div_nonneg (by norm_num) (le_of_lt σ.2)
    exact mul_le_mul_of_nonneg_left h_dual_gap_bound hscale_nonneg
  have h_rhs_rewrite :
      (2 / (σ : ℝ)) *
          ((p : ℝ) / (p + k + 1 : ℝ) *
            ((1 / (2 * (σ : ℝ))) * ‖y0 - yStar‖ ^ (2 : ℕ) +
              EReal.toReal (q_opt(f, g)) - (q(f, g) y0).toReal)) =
        2 * (p : ℝ) / ((σ : ℝ) * (p + k + 1 : ℝ)) *
          ((1 / (2 * (σ : ℝ))) * ‖y0 - yStar‖ ^ (2 : ℕ) +
            EReal.toReal (q_opt(f, g)) - (q(f, g) y0).toReal) := by
    -- The closing constant is just a rearrangement of the deterministic prefactor.
    field_simp
  calc
    μ[fun ω ↦ ‖x (k + 1) ω - xStar‖ ^ (2 : ℕ)]
        ≤
          μ[fun ω ↦
            (2 / (σ : ℝ)) *
              (EReal.toReal (q_opt(f, g)) - (q(f, g) (y (k + 1) ω)).toReal)] :=
      h_integral_le
    _ =
        (2 / (σ : ℝ)) *
          μ[fun ω ↦
            EReal.toReal (q_opt(f, g)) - (q(f, g) (y (k + 1) ω)).toReal] := by
          rw [integral_const_mul]
    _ =
        (2 / (σ : ℝ)) *
          (EReal.toReal (q_opt(f, g)) - μ[fun ω ↦ (q(f, g) (y (k + 1) ω)).toReal]) := by
          rw [expected_dual_gap_eq_integral_pointwise_gap f g y k h_dual_value_integrable]
    _ ≤
        (2 / (σ : ℝ)) *
          ((p : ℝ) / (p + k + 1 : ℝ) *
            ((1 / (2 * (σ : ℝ))) * ‖y0 - yStar‖ ^ (2 : ℕ) +
              EReal.toReal (q_opt(f, g)) - (q(f, g) y0).toReal)) :=
      h_scaled_dual_gap_bound
    _ =
        2 * (p : ℝ) / ((σ : ℝ) * (p + k + 1 : ℝ)) *
          ((1 / (2 * (σ : ℝ))) * ‖y0 - yStar‖ ^ (2 : ℕ) +
            EReal.toReal (q_opt(f, g)) - (q(f, g) y0).toReal) :=
      h_rhs_rewrite

/-- Helper for Theorem 12.14: with the DBPG trajectory and sampling assumptions made explicit,
the expected primal squared-distance bound follows formally from the expectation wrapper and the
already established pointwise/integrability lemmas. -/
lemma randomized_dbpg_expected_primal_sqdist_le_of_assumptions
    (xStar : E) (hxStar : IsMinOn F Set.univ xStar)
    (k : ℕ)
    (h_problem : IsDualBlockProximalGradientProblem f g σ)
    (h_traj :
      ∀ ω,
        is_dual_block_proximal_gradient_primal_trajectory
          f g σ (fun n ↦ sampled_block n ω) y0
          (fun n ↦ x n ω)
          (fun n ↦ y n ω))
    (h_sampled_block_meas : ∀ k, Measurable (sampled_block k))
    (h_sampled_block_indep : iIndepFun sampled_block μ)
    (h_sampled_block_uniform :
      ∀ k (i : Fin p), μ ((sampled_block k) ⁻¹' {i}) = 1 / (p : ℝ≥0∞))
    (hyStar : yStar ∈ Λ*(f, g))
    (hy0_finite : y0 ∈ finite_domain (q(f, g)))
    (hyStar_finite : yStar ∈ finite_domain (q(f, g)))
    (h_primal_sqdist_integrable :
      Integrable (fun ω ↦ ‖x (k + 1) ω - xStar‖ ^ (2 : ℕ)) μ) :
    μ[fun ω ↦ ‖x (k + 1) ω - xStar‖ ^ (2 : ℕ)] ≤
      2 * (p : ℝ) / ((σ : ℝ) * (p + k + 1 : ℝ)) *
        ((1 / (2 * (σ : ℝ))) * ‖y0 - yStar‖ ^ (2 : ℕ) +
          EReal.toReal (q_opt(f, g)) - (q(f, g) y0).toReal) := by
  have h_dual_value_finite :
      ∀ ω, y (k + 1) ω ∈ finite_domain (q(f, g)) :=
    randomized_dbpg_dual_iterate_mem_finite_domain
      (σ := σ)
      (f := f)
      (g := g)
      (y0 := y0)
      (sampled_block := sampled_block)
      (x := x)
      (y := y)
      h_problem
      h_traj
      hy0_finite
      k
  have h_dual_value_integrable :
      Integrable (fun ω ↦ (q(f, g) (y (k + 1) ω)).toReal) μ :=
    randomized_dbpg_dual_value_integrable
      (μ := μ)
      (σ := σ)
      (f := f)
      (g := g)
      (y0 := y0)
      (yStar := yStar)
      (sampled_block := sampled_block)
      (x := x)
      (y := y)
      (h_problem := h_problem)
      (h_traj := h_traj)
      (h_sampled_block_meas := h_sampled_block_meas)
      (h_sampled_block_indep := h_sampled_block_indep)
      (h_sampled_block_uniform := h_sampled_block_uniform)
      (hyStar := hyStar)
      (hy0_finite := hy0_finite)
      (hyStar_finite := hyStar_finite)
      k
  have h_pointwise :
      ∀ ω,
        ‖x (k + 1) ω - xStar‖ ^ (2 : ℕ) ≤
          (2 / (σ : ℝ)) *
            (EReal.toReal (q_opt(f, g)) - (q(f, g) (y (k + 1) ω)).toReal) := by
    intro ω
    -- The pathwise Chapter 12 estimate is already available at the sampled successor iterate.
    exact
      dbpg_pointwise_primal_sqdist_le_dual_gap_at_succ
        (σ := σ)
        (f := f)
        (g := g)
        (y0 := y0)
        (yStar := yStar)
        (sampled_block := sampled_block)
        (x := x)
        (y := y)
        (h_problem := h_problem)
        (h_traj := h_traj)
        (hyStar := hyStar)
        (hyStar_finite := hyStar_finite)
        (xStar := xStar)
        (hxStar := hxStar)
        k
        ω
        (h_dual_value_finite ω)
  -- Once all explicit DBPG assumptions are present, the theorem is exactly the expectation
  -- wrapper instantiated with the local Chapter 12 helper lemmas.
  exact
    expected_primal_sqdist_le_of_dual_gap_bound
      (μ := μ)
      (σ := σ)
      (f := f)
      (g := g)
      (y0 := y0)
      (sampled_block := sampled_block)
      (x := x)
      (y := y)
      (yStar := yStar)
      xStar
      k
      h_problem
      h_traj
      h_sampled_block_meas
      h_sampled_block_indep
      h_sampled_block_uniform
      hyStar
      hy0_finite
      hyStar_finite
      h_primal_sqdist_integrable
      h_dual_value_finite
      h_dual_value_integrable
      h_pointwise

-- Proof sketch: combine the same history-conditioned randomized Lyapunov contraction used in
-- part (1) with the Chapter 12 primal-dual estimate that bounds `‖x^{k+1} - x*‖²` by `(2 / σ)`
-- times the dual-gap Lyapunov quantity. Taking expectations and substituting the part (1)
-- recursion gives the displayed `O(1 / k)` primal-distance estimate.
include sampled_block y h_problem h_traj h_sampled_block_meas h_sampled_block_indep
  h_sampled_block_uniform hyStar hy0_finite hyStar_finite

/-- Helper for Theorem 12.14: the public part-(2) theorem is exactly the explicit-assumptions
wrapper once the ambient randomized DBPG trajectory data are re-exposed at the theorem boundary. -/
lemma randomized_dbpg_expected_primal_sqdist_public_context_bridge
    (xStar : E) (hxStar : IsMinOn F Set.univ xStar)
    (k : ℕ)
    (h_primal_sqdist_integrable :
      Integrable (fun ω ↦ ‖x (k + 1) ω - xStar‖ ^ (2 : ℕ)) μ) :
    μ[fun ω ↦ ‖x (k + 1) ω - xStar‖ ^ (2 : ℕ)] ≤
      2 * (p : ℝ) / ((σ : ℝ) * (p + k + 1 : ℝ)) *
        ((1 / (2 * (σ : ℝ))) * ‖y0 - yStar‖ ^ (2 : ℕ) +
          EReal.toReal (q_opt(f, g)) - (q(f, g) y0).toReal) := by
  -- Restore the ambient randomized DBPG assumptions by calling the proved explicit wrapper.
  exact
    randomized_dbpg_expected_primal_sqdist_le_of_assumptions
      (μ := μ)
      (σ := σ)
      (f := f)
      (g := g)
      (y0 := y0)
      (sampled_block := sampled_block)
      (x := x)
      (y := y)
      (yStar := yStar)
      xStar
      hxStar
      k
      h_problem
      h_traj
      h_sampled_block_meas
      h_sampled_block_indep
      h_sampled_block_uniform
      hyStar
      hy0_finite
      hyStar_finite
      h_primal_sqdist_integrable

/-- Theorem 12.14 (2): for primal and dual sequences generated by the dual block proximal-gradient
method with randomized uniformly sampled block order, if the sampled primal squared distance is
integrable and the dual endpoint values on the right-hand side lie in the finite domain of `q`,
then the expected primal squared distance to a primal optimizer satisfies
`E[‖x^{k+1} - x*‖²] ≤ (2p / (σ (p + k + 1))) ((1 / (2σ)) ‖y^0 - y*‖² + q_opt - q(y^0))`. -/
theorem randomized_dual_block_proximal_gradient_expected_primal_sqdist_le
    (xStar : E) (hxStar : IsMinOn F Set.univ xStar)
    (k : ℕ)
    (h_primal_sqdist_integrable :
      Integrable (fun ω ↦ ‖x (k + 1) ω - xStar‖ ^ (2 : ℕ)) μ) :
    μ[fun ω ↦ ‖x (k + 1) ω - xStar‖ ^ (2 : ℕ)] ≤
      2 * (p : ℝ) / ((σ : ℝ) * (p + k + 1 : ℝ)) *
        ((1 / (2 * (σ : ℝ))) * ‖y0 - yStar‖ ^ (2 : ℕ) +
          EReal.toReal (q_opt(f, g)) - (q(f, g) y0).toReal) :=
by
  -- Route correction: close the public theorem from the dedicated bridge instead of repeating
  -- the explicit-assumptions instantiation at the public boundary.
  simpa using
    randomized_dbpg_expected_primal_sqdist_public_context_bridge
      (μ := μ)
      (σ := σ)
      (f := f)
      (g := g)
      (y0 := y0)
      (sampled_block := sampled_block)
      (x := x)
      (y := y)
      (h_problem := h_problem)
      (h_traj := h_traj)
      (h_sampled_block_meas := h_sampled_block_meas)
      (h_sampled_block_indep := h_sampled_block_indep)
      (h_sampled_block_uniform := h_sampled_block_uniform)
      (yStar := yStar)
      (hyStar := hyStar)
      (hy0_finite := hy0_finite)
      (hyStar_finite := hyStar_finite)
      xStar
      hxStar
      k
      h_primal_sqdist_integrable

end
