/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_2
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_16
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_2
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_14
import FirstOrderMethodsOptimization_Beck_2017.Chap11.Algorithm_11_4
import FirstOrderMethodsOptimization_Beck_2017.Chap11.Lemma_11_4
import FirstOrderMethodsOptimization_Beck_2017.Chap11.Lemma_11_5
import FirstOrderMethodsOptimization_Beck_2017.Chap11.Lemma_11_6
import FirstOrderMethodsOptimization_Beck_2017.Chap11.Lemma_11_7
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Algorithm_12_15
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Definition_12_18
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Theorem_12_14

noncomputable section

universe u

namespace DualBlockProximalGradient

/-- The explicit geometric-or-sublinear upper bound in Theorem 12.17, as a function of the
number of blocks `p`, strong-convexity modulus `σ`, superlevel radius `R`, initial dual gap, and
outer iteration `k`. -/
def cyclicGapBound
    (p : ℕ) (σ R : PosReal) (initialGap : ℝ) (k : ℕ) : ℝ :=
  max
    (((1 / 2 : ℝ) ^ (((k - 1 : ℕ) : ℝ) / 2)) * initialGap)
    ((8 * (p : ℝ) * ((p + 1 : ℝ) ^ 2) * ((R : ℝ) ^ 2)) /
      ((σ : ℝ) * ((k - 1 : ℕ) : ℝ)))

/-- Expanding `cyclicGapBound` gives the two branches of the textbook rate. -/
@[simp] theorem cyclicGapBound_apply
    (p : ℕ) (σ R : PosReal) (initialGap : ℝ) (k : ℕ) :
    cyclicGapBound p σ R initialGap k =
      max
        (((1 / 2 : ℝ) ^ (((k - 1 : ℕ) : ℝ) / 2)) * initialGap)
        ((8 * (p : ℝ) * ((p + 1 : ℝ) ^ 2) * ((R : ℝ) ^ 2)) /
          ((σ : ℝ) * ((k - 1 : ℕ) : ℝ))) := rfl

end DualBlockProximalGradient

open DualBlockProximalGradient

section

variable {E : Type u} {p : ℕ}
variable [NeZero p]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Theorem 12.17 is `source-facing`: it specializes the Chapter 11 cyclic block
proximal-gradient rate to the dual objective `q` and then applies the Chapter 12 primal-dual
distance estimate. The two source conclusions remain separate atomic theorems. The dual
initialization, trajectory, and Assumption 12.16 radius all use the Euclidean product owner
`PiLp 2 (fun _ : Fin p ↦ E)`; the raw function space appears only through `ofLp`
when applying the existing objective and trajectory APIs. -/

variable (σ : PosReal) (f : E → EReal) (g : Fin p → E → EReal)
variable [h_problem : IsDualBlockProximalGradientSuperlevelDistanceBoundedProblem f g σ]
variable (y0 : PiLp 2 (fun _ : Fin p ↦ E)) (x : ℕ → E)
variable (y : ℕ → PiLp 2 (fun _ : Fin p ↦ E))
variable (h_trajectory : is_dual_block_proximal_gradient_primal_trajectory f g σ
  (dual_block_proximal_gradient_cyclic_block_index p) y0.ofLp x (fun n ↦ (y n).ofLp))
variable (α0 : PosReal) (h_initial_level : q(f, g) y0.ofLp = (α0 : EReal))
variable (R : PosReal) (h_R : IsSuperlevelRadius f g α0 R)

include h_problem h_trajectory h_initial_level h_R

/-- Helper for Theorem 12.17 (`thm:12.17`): the prescribed initial dual level
`q(f, g) y0.ofLp = α0` is finite, so the starting dual point belongs to the finite domain of `q`.
-/
lemma initialDualPointMemFiniteDomain :
    y0.ofLp ∈ finite_domain (q(f, g)) := by
  -- Rewrite the initial dual value to the finite positive scalar level `α0`.
  refine mem_finite_domain.mpr ?_
  constructor
  · refine mem_effective_domain.mpr ?_
    rw [h_initial_level]
    simp
  · rw [h_initial_level]
    simp

/-- Helper for Theorem 12.17 (`thm:12.17`): every dual iterate of the deterministic cyclic DBPG
trajectory stays in the finite domain of the block dual objective `q`. -/
lemma cyclicDbpgDualIterateMemFiniteDomain
    (n : ℕ) :
    (y n).ofLp ∈ finite_domain (q(f, g)) := by
  -- Propagate finite dual values along the source DBPG recursion one step at a time.
  induction n with
  | zero =>
      simpa [is_dual_block_proximal_gradient_primal_trajectory_zero h_trajectory] using
        initialDualPointMemFiniteDomain
          (σ := σ)
          (f := f)
          (g := g)
          (h_problem := h_problem)
          (y0 := y0)
          (x := x)
          (y := y)
          (h_trajectory := h_trajectory)
          (α0 := α0)
          (h_initial_level := h_initial_level)
          (R := R)
          (h_R := h_R)
  | succ n ihn =>
      exact
        dual_block_primal_y_step_mem_finite_domain
          σ
          f
          g
          h_problem.toIsDualBlockProximalGradientProblem
          ihn
          (is_dual_block_proximal_gradient_primal_trajectory_step h_trajectory n).2

/-- Helper for Theorem 12.17 (`thm:12.17`): every optimal dual point has a finite block-dual
objective value. -/
lemma optimalDualPointMemFiniteDomain
    {yStar : Fin p → E}
    (hyStar : yStar ∈ Λ*(f, g)) :
    yStar ∈ finite_domain (q(f, g)) := by
  have hy0_finite :
      y0.ofLp ∈ finite_domain (q(f, g)) :=
    initialDualPointMemFiniteDomain
      (σ := σ)
      (f := f)
      (g := g)
      (h_problem := h_problem)
      (y0 := y0)
      (x := x)
      (y := y)
      (h_trajectory := h_trajectory)
      (α0 := α0)
      (h_initial_level := h_initial_level)
      (R := R)
      (h_R := h_R)
  have h_problem_dup :
      IsDualBasedProximalGradientProblem
        f
        (PiLp.separableSum g)
        (dual_block_duplication E p).toLinearMap
        σ :=
    (dual_block_problem_to_dual_based_problem
      (σ := σ)
      (f := f)
      (g := g)) h_problem.toIsDualBlockProximalGradientProblem
  have hqStar_ne_top : q(f, g) yStar ≠ ⊤ := by
    -- Compare the source-facing block dual objective with the duplicated-model Chapter 12 dual
    -- objective, which is never `⊤`.
    have hdup_ne_top :
        dual_based_proximal_gradient_lagrange_dual_objective_primal
            f
            (PiLp.separableSum g)
            (dual_block_duplication E p)
            (WithLp.toLp 2 yStar) ≠ ⊤ := by
      simpa using
        dual_objective_ne_top
          (σ := σ)
          (f := f)
          (g := PiLp.separableSum g)
          (A := (dual_block_duplication E p).toLinearMap)
          h_problem_dup
          (WithLp.toLp 2 yStar)
    have hdup_eq :
        dual_based_proximal_gradient_lagrange_dual_objective_primal
            f
            (PiLp.separableSum g)
            (dual_block_duplication E p)
            (WithLp.toLp 2 yStar) =
          q(f, g) yStar := by
      simpa using
        dual_block_proximal_gradient_lagrange_dual_objective_primal_eq_dual_objective
          (f := f)
          (g := g)
          (hg_proper := h_problem.g_proper)
          (y := WithLp.toLp 2 yStar)
    intro hqStar_top
    have hdup_top :
        dual_based_proximal_gradient_lagrange_dual_objective_primal
            f
            (PiLp.separableSum g)
            (dual_block_duplication E p)
            (WithLp.toLp 2 yStar) = ⊤ := by
      rw [hdup_eq]
      exact hqStar_top
    exact hdup_ne_top hdup_top
  have hqStar_ne_bot : q(f, g) yStar ≠ ⊥ := by
    have hy0_ne_bot : q(f, g) y0.ofLp ≠ ⊥ := (mem_finite_domain.mp hy0_finite).2
    have hle : q(f, g) y0.ofLp ≤ q(f, g) yStar := by
      calc
        q(f, g) y0.ofLp ≤ q_opt(f, g) :=
          dual_objective_le_dual_problem_value f g y0.ofLp
        _ = q(f, g) yStar := by
          symm
          exact
            dual_block_proximal_gradient_dual_objective_eq_dual_problem_value_of_mem_optimal_set
              f
              g
              hyStar
    intro hbot
    have hy0_eq_bot : q(f, g) y0.ofLp = ⊥ := by
      rw [hbot] at hle
      exact le_antisymm hle bot_le
    exact hy0_ne_bot hy0_eq_bot
  -- Finiteness is exactly the conjunction of not being `⊤` and not being `⊥`.
  exact
    mem_finite_domain.mpr
      ⟨mem_effective_domain.mpr (lt_top_iff_ne_top.mpr hqStar_ne_top), hqStar_ne_bot⟩

/-- Helper for Theorem 12.17 (`thm:12.17`): at the sampled cyclic iterate `p * k`, the Chapter
12 pointwise primal-vs-dual-gap inequality gives the source-facing squared-distance bound. -/
lemma cyclicDbpgPrimalSqdist_le_dualGap
    (xStar : E)
    (h_xStar :
      xStar ∈ unconstrained_problem_solutions
        (composite_model_objective f (finite_sum_objective g)))
    (k : ℕ)
    (hk_pos : 0 < p * k) :
    ‖x (p * k) - xStar‖ ^ 2 ≤
      (2 / (σ : ℝ)) * (q_opt(f, g) - q(f, g) (y (p * k)).ofLp).toReal := by
  rcases h_problem.dual_optimal_set_nonempty with ⟨yStar, hyStar⟩
  have hyStar_finite :
      yStar ∈ finite_domain (q(f, g)) :=
    optimalDualPointMemFiniteDomain
      (σ := σ)
      (f := f)
      (g := g)
      (y0 := y0)
      (x := x)
      (y := y)
      (h_problem := h_problem)
      (h_trajectory := h_trajectory)
      (α0 := α0)
      (h_initial_level := h_initial_level)
      (R := R)
      (h_R := h_R)
      hyStar
  have hxStar_min :
      IsMinOn
        (composite_model_objective f (finite_sum_objective g))
        Set.univ
        xStar := by
    simpa using (mem_unconstrained_problem_solutions_iff.mp h_xStar)
  let xDet : ℕ → Unit → E := fun n _ ↦ x n
  let yDet : ℕ → Unit → Fin p → E := fun n _ ↦ (y n).ofLp
  have h_trajDet :
      ∀ ω : Unit,
        is_dual_block_proximal_gradient_primal_trajectory
          f
          g
          σ
          (dual_block_proximal_gradient_cyclic_block_index p)
          y0.ofLp
          (fun n ↦ xDet n ω)
          (fun n ↦ yDet n ω) := by
    intro ω
    simpa [xDet, yDet] using h_trajectory
  have hy_iter_finite :
      (y (p * k)).ofLp ∈ finite_domain (q(f, g)) :=
    cyclicDbpgDualIterateMemFiniteDomain
      (σ := σ)
      (f := f)
      (g := g)
      (y0 := y0)
      (x := x)
      (y := y)
      (h_problem := h_problem)
      (h_trajectory := h_trajectory)
      (α0 := α0)
      (h_initial_level := h_initial_level)
      (R := R)
      (h_R := h_R)
      (p * k)
  have hk_step : p * k - 1 + 1 = p * k :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt hk_pos)
  have hy_step_finite :
      yDet (p * k - 1 + 1) () ∈ finite_domain (q(f, g)) := by
    simpa [yDet, hk_step] using hy_iter_finite
  have hpointwise :
      ‖xDet (p * k - 1 + 1) () - xStar‖ ^ (2 : ℕ) ≤
        (2 / (σ : ℝ)) *
          (EReal.toReal (q_opt(f, g)) -
            (q(f, g) (yDet (p * k - 1 + 1) ())).toReal) := by
    exact
      dbpg_pointwise_primal_sqdist_le_dual_gap_at_succ
        (Ω := Unit)
        (σ := σ)
        (f := f)
        (g := g)
        (y0 := y0.ofLp)
        (yStar := yStar)
        (sampled_block := fun n _ ↦ dual_block_proximal_gradient_cyclic_block_index p n)
        (x := xDet)
        (y := yDet)
        (h_problem := h_problem.toIsDualBlockProximalGradientProblem)
        (h_traj := h_trajDet)
        (hyStar := hyStar)
        (hyStar_finite := hyStar_finite)
        (xStar := xStar)
        (hxStar := hxStar_min)
        (k := p * k - 1)
        (ω := ())
        hy_step_finite
  calc
    ‖x (p * k) - xStar‖ ^ 2
        = ‖xDet (p * k - 1 + 1) () - xStar‖ ^ (2 : ℕ) := by
            simp [xDet, hk_step]
    _ ≤
        (2 / (σ : ℝ)) *
          (EReal.toReal (q_opt(f, g)) -
            (q(f, g) (yDet (p * k - 1 + 1) ())).toReal) := hpointwise
    _ =
        (2 / (σ : ℝ)) *
          (EReal.toReal (q_opt(f, g)) -
            (q(f, g) (y (p * k)).ofLp).toReal) := by
              simp [yDet, hk_step]
    _ =
        (2 / (σ : ℝ)) *
          (q_opt(f, g) - q(f, g) (y (p * k)).ofLp).toReal := by
            rw [← dual_gap_toReal_eq_of_mem_finite_domain
              (f := f)
              (g := g)
              (yBar := (y (p * k)).ofLp)
              (yStar := yStar)
              hyStar
              hyStar_finite
              hy_iter_finite]

/-- Helper for Theorem 12.17 (`thm:12.17`): after `p * k + m` cyclic one-block updates, the
active block is the zero-based block `m` whenever `m < p`. -/
lemma cyclicBlockIndex_mul_add
    (k m : ℕ) (hm : m < p) :
    dual_block_proximal_gradient_cyclic_block_index p (p * k + m) = ⟨m, hm⟩ := by
  -- Reduce the cyclic index to its remainder modulo `p`, then collapse the `p * k` term.
  ext
  rw [dual_block_proximal_gradient_cyclic_block_index_val]
  rw [Nat.add_mod, Nat.mul_mod_right, zero_add]
  simpa using Nat.mod_eq_of_lt hm

/-- Helper for Theorem 12.17 (`thm:12.17`): the deterministic cyclic DBPG dual path is the
special case of the Chapter 11 minimization-view RBPG recursion obtained by freezing the sample
space to `Unit` and the sampled blocks to the cyclic schedule. -/
lemma cyclicDbpg_eqRandomizedMinimizationViewMethod
    (n : ℕ) :
    ∃ hRBPG :
        RandomizedBlockProximalGradientAssumptions
          (DualBlockMinimizationView.smoothTerm f)
          (fun i z ↦ ((g i)∗) (-z))
          (fun _ : Fin p ↦ fun w : Fin p → E ↦
            gradient (fun z : E ↦ (((f∗) z).toReal)) (∑ j : Fin p, w j))
          (unconstrained_problem_solutions (DualBlockMinimizationView.objective f g))
          (-EReal.toReal (q_opt(f, g)))
          (fun _ : Fin p ↦ σ⁻¹),
      (y n).ofLp =
        randomized_block_proximal_gradient_method
          hRBPG.toIsBlockProximalGradientProblem
          (hRBPG.interior_effective_domain_point
            ⟨y0.ofLp,
              initial_dual_point_mem_effective_domain_minimization_view
                f
                g
                y0.ofLp
                h_problem.toIsProperExtendedRealFunction
                h_problem.g_proper
                (initialDualPointMemFiniteDomain
                  (σ := σ)
                  (f := f)
                  (g := g)
                  (h_problem := h_problem)
                  (y0 := y0)
                  (x := x)
                  (y := y)
                  (h_trajectory := h_trajectory)
                  (α0 := α0)
                  (h_initial_level := h_initial_level)
                  (R := R)
                  (h_R := h_R))⟩)
          (dual_block_proximal_gradient_cyclic_block_index p)
          n := by
  rcases h_problem.dual_optimal_set_nonempty with ⟨yStar, hyStar⟩
  have hy0_finite :
      y0.ofLp ∈ finite_domain (q(f, g)) :=
    initialDualPointMemFiniteDomain
      (σ := σ)
      (f := f)
      (g := g)
      (h_problem := h_problem)
      (y0 := y0)
      (x := x)
      (y := y)
      (h_trajectory := h_trajectory)
      (α0 := α0)
      (h_initial_level := h_initial_level)
      (R := R)
      (h_R := h_R)
  have hyStar_finite :
      yStar ∈ finite_domain (q(f, g)) :=
    optimalDualPointMemFiniteDomain
      (σ := σ)
      (f := f)
      (g := g)
      (y0 := y0)
      (x := x)
      (y := y)
      (h_problem := h_problem)
      (h_trajectory := h_trajectory)
      (α0 := α0)
      (h_initial_level := h_initial_level)
      (R := R)
      (h_R := h_R)
      hyStar
  let sampledBlockDet : ℕ → Unit → Fin p :=
    fun k _ ↦ dual_block_proximal_gradient_cyclic_block_index p k
  let xDet : ℕ → Unit → E := fun k _ ↦ x k
  let yDet : ℕ → Unit → Fin p → E := fun k _ ↦ (y k).ofLp
  have hTrajDet :
      ∀ ω : Unit,
        is_dual_block_proximal_gradient_primal_trajectory
          f
          g
          σ
          (fun k ↦ sampledBlockDet k ω)
          y0.ofLp
          (fun k ↦ xDet k ω)
          (fun k ↦ yDet k ω) := by
    intro ω
    -- The `Unit` specialization keeps the original cyclic trajectory unchanged.
    simpa [sampledBlockDet, xDet, yDet] using h_trajectory
  let hRBPG :
      RandomizedBlockProximalGradientAssumptions
        (DualBlockMinimizationView.smoothTerm f)
        (fun i z ↦ ((g i)∗) (-z))
        (fun _ : Fin p ↦ fun w : Fin p → E ↦
          gradient (fun z : E ↦ (((f∗) z).toReal)) (∑ j : Fin p, w j))
        (unconstrained_problem_solutions (DualBlockMinimizationView.objective f g))
        (-EReal.toReal (q_opt(f, g)))
        (fun _ : Fin p ↦ σ⁻¹) :=
    dual_block_minimization_view_randomized_assumptions
      (σ := σ)
      (f := f)
      (g := g)
      (y0 := y0.ofLp)
      (yStar := yStar)
      h_problem.toIsDualBlockProximalGradientProblem
      hyStar
      hy0_finite
      hyStar_finite
  have hy0_eff :
      y0.ofLp ∈ effective_domain (DualBlockMinimizationView.regularizer g) :=
    initial_dual_point_mem_effective_domain_minimization_view
      f
      g
      y0.ofLp
      h_problem.toIsProperExtendedRealFunction
      h_problem.g_proper
      hy0_finite
  refine ⟨hRBPG, ?_⟩
  -- Specialize the realized-path bridge from Theorem 12.14 to the deterministic `Unit` path.
  simpa [sampledBlockDet, yDet] using
    (randomized_dbpg_realized_minimization_view_method_eq
      (Ω := Unit)
      (σ := σ)
      (f := f)
      (g := g)
      (y0 := y0.ofLp)
      (sampled_block := sampledBlockDet)
      (x := xDet)
      (y := yDet)
      h_problem.toIsDualBlockProximalGradientProblem
      hTrajDet
      hRBPG
      hy0_eff
      ()
      n)

/-- Helper for Theorem 12.17 (`thm:12.17`): the minimization-view smooth term is convex because
it is the conjugate `f∗` precomposed with the block-sum linear map. -/
lemma dualBlockMinimizationViewSmoothTermConvex :
    is_convex_function (DualBlockMinimizationView.smoothTerm (p := p) f) := by
  let sumLinearMap : (Fin p → E) →ₗ[ℝ] E :=
    { toFun := fun w ↦ ∑ j : Fin p, w j
      map_add' := by
        intro w z
        simp [Finset.sum_add_distrib]
      map_smul' := by
        intro a w
        simp [Finset.smul_sum] }
  -- Pull convexity of `f∗` back along the block-sum linear map.
  simpa [sumLinearMap, DualBlockMinimizationView.smoothTerm_apply] using
    is_convex_function_precompose_linearMap_add
      (f := (f∗))
      (conjugate_function_closed_and_convex f).2
      sumLinearMap
      0

/-- Helper for Theorem 12.17 (`thm:12.17`): the Chapter 12 minimization view carries a
theorem-local Chapter 11 block-proximal-gradient owner with the raw precomposition smoothness
constant inherited from `f∗`. -/
lemma dualBlockMinimizationViewBlockAssumptionsRaw
    {yStar : Fin p → E}
    (hyStar : yStar ∈ Λ*(f, g))
    (hyStar_finite : yStar ∈ finite_domain (q(f, g))) :
    ∃ LfRaw : NNReal,
      BlockProximalGradientAssumptions
        (DualBlockMinimizationView.smoothTerm f)
        (fun i z ↦ ((g i)∗) (-z))
        (fun _ : Fin p ↦ fun w : Fin p → E ↦
          gradient (fun z : E ↦ (((f∗) z).toReal)) (∑ j : Fin p, w j))
        (unconstrained_problem_solutions (DualBlockMinimizationView.objective f g))
        (-EReal.toReal (q_opt(f, g)))
        LfRaw
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
  let LfRaw : NNReal :=
    Real.toNNReal (1 / (σ : ℝ)) * ‖sumCLM‖₊ ^ (2 : ℕ)
  have hy0_finite :
      y0.ofLp ∈ finite_domain (q(f, g)) :=
    initialDualPointMemFiniteDomain
      (σ := σ)
      (f := f)
      (g := g)
      (h_problem := h_problem)
      (y0 := y0)
      (x := x)
      (y := y)
      (h_trajectory := h_trajectory)
      (α0 := α0)
      (h_initial_level := h_initial_level)
      (R := R)
      (h_R := h_R)
  let hRBPG :
      RandomizedBlockProximalGradientAssumptions
        (DualBlockMinimizationView.smoothTerm f)
        (fun i z ↦ ((g i)∗) (-z))
        (fun _ : Fin p ↦ fun w : Fin p → E ↦
          gradient (fun z : E ↦ (((f∗) z).toReal)) (∑ j : Fin p, w j))
        (unconstrained_problem_solutions (DualBlockMinimizationView.objective f g))
        (-EReal.toReal (q_opt(f, g)))
        (fun _ : Fin p ↦ σ⁻¹) :=
    dual_block_minimization_view_randomized_assumptions
      (σ := σ)
      (f := f)
      (g := g)
      (y0 := y0.ofLp)
      (yStar := yStar)
      h_problem.toIsDualBlockProximalGradientProblem
      hyStar
      hy0_finite
      hyStar_finite
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
  have hsmooth_precompose :
      is_l_smooth_on
        (fun w : Fin p → E ↦ ((f∗) (sumCLM w)).toReal)
        Set.univ
        LfRaw := by
    -- The global `1 / σ` smoothness of `f∗` is stable under linear precomposition by the block
    -- sum map.
    simpa [LfRaw] using
      (Example_10_44.is_l_smooth_on_precompose_continuousLinearMap
        sumCLM
        (fun z : E ↦ ((f∗) z).toReal)
        (conjugate_function_primal_is_l_smooth_on_of_proper_closed_strongConvexOn
          (σ := σ)
          (f := f)
          h_problem.toIsProperExtendedRealFunction
          h_problem.f_closed
          h_problem.f_strongly_convex))
  refine ⟨LfRaw, ?_⟩
  refine
    { toIsBlockProximalGradientProblem := hRBPG.toIsBlockProximalGradientProblem
      f_effective_domain_convex := ?_
      f_toReal_smooth_on_interior_effective_domain := ?_ }
  · -- The minimization-view smooth term is finite everywhere, so its effective domain is all of
    -- block space.
    simpa [hsmooth_domain_univ] using
      (convex_univ : Convex ℝ (Set.univ : Set (Fin p → E)))
  · -- Route correction: keep the raw precomposition smoothness constant local to the Chapter 11
    -- owner instead of forcing the displayed `p / σ` coefficient into the recursion itself.
    simpa [hsmooth_domain_univ, LfRaw, sumCLM, sumLinearMap,
      DualBlockMinimizationView.smoothTerm_apply] using hsmooth_precompose

omit y0 x y h_problem h_trajectory α0 h_initial_level R h_R

/-- Helper for Theorem 12.17 (`thm:12.17`): an RBPG iterate at time `n + m` can be computed by
restarting the recursion from the state at time `n` and shifting the realized block schedule by
`n`. -/
lemma randomizedBlockProximalGradientMethod_add_eq_restart
    (hcore :
      IsBlockProximalGradientProblem
        (DualBlockMinimizationView.smoothTerm f)
        (fun i z ↦ ((g i)∗) (-z))
        (fun _ : Fin p ↦ fun w : Fin p → E ↦
          gradient (fun z : E ↦ (((f∗) z).toReal)) (∑ j : Fin p, w j))
        (unconstrained_problem_solutions (DualBlockMinimizationView.objective f g))
        (-EReal.toReal (q_opt(f, g)))
        (fun _ : Fin p ↦ σ⁻¹))
    (z : Fin p → E)
    (schedule : ℕ → Fin p)
    (n m : ℕ) :
    randomized_block_proximal_gradient_method hcore z schedule (n + m) =
      randomized_block_proximal_gradient_method
        hcore
        (randomized_block_proximal_gradient_method hcore z schedule n)
        (fun t ↦ schedule (n + t))
        m := by
  induction m with
  | zero =>
      -- Restarting for zero additional steps leaves the current iterate unchanged.
      simp
  | succ m ih =>
      -- One more shifted step after the restart matches the original `(n + m + 1)` update.
      simpa [Nat.add_assoc] using
        (by
          rw [randomized_block_proximal_gradient_method_succ, ih,
            randomized_block_proximal_gradient_method_succ] :
            randomized_block_proximal_gradient_method hcore z schedule (n + m + 1) =
              randomized_block_proximal_gradient_method
                hcore
                (randomized_block_proximal_gradient_method hcore z schedule n)
                (fun t ↦ schedule (n + t))
                (m + 1))

/-- Helper for Theorem 12.17 (`thm:12.17`): two RBPG schedules that agree on the first `n`
realized blocks generate the same iterate at time `n`. -/
lemma randomizedBlockProximalGradientMethod_eq_ofPrefixEq
    (hcore :
      IsBlockProximalGradientProblem
        (DualBlockMinimizationView.smoothTerm f)
        (fun i z ↦ ((g i)∗) (-z))
        (fun _ : Fin p ↦ fun w : Fin p → E ↦
          gradient (fun z : E ↦ (((f∗) z).toReal)) (∑ j : Fin p, w j))
        (unconstrained_problem_solutions (DualBlockMinimizationView.objective f g))
        (-EReal.toReal (q_opt(f, g)))
        (fun _ : Fin p ↦ σ⁻¹))
    (z : Fin p → E)
    {schedule₁ schedule₂ : ℕ → Fin p} {n : ℕ}
    (hprefix : ∀ t < n, schedule₁ t = schedule₂ t) :
    randomized_block_proximal_gradient_method hcore z schedule₁ n =
      randomized_block_proximal_gradient_method hcore z schedule₂ n := by
  induction n with
  | zero =>
      -- At time zero both RBPG recursions are definitionally the same initial point.
      simp
  | succ n ih =>
      -- Rewrite both successors and use the shared prefix on the first `n` steps.
      rw [randomized_block_proximal_gradient_method_succ,
        randomized_block_proximal_gradient_method_succ]
      have hprev :
          randomized_block_proximal_gradient_method hcore z schedule₁ n =
            randomized_block_proximal_gradient_method hcore z schedule₂ n := by
        refine ih ?_
        intro t ht
        exact hprefix t (Nat.lt_trans ht (Nat.lt_succ_self n))
      rw [hprefix n (Nat.lt_succ_self n), hprev]

/-- Helper for Theorem 12.17 (`thm:12.17`): starting from any point, the first `m ≤ p` cyclic
RBPG updates agree with the stage-`m` CBPG inner iterate. -/
lemma cyclicRbpgPrefix_eqCbpgInnerIterate
    {LfRaw : NNReal}
    (hblock :
      BlockProximalGradientAssumptions
        (DualBlockMinimizationView.smoothTerm f)
        (fun i z ↦ ((g i)∗) (-z))
        (fun _ : Fin p ↦ fun w : Fin p → E ↦
          gradient (fun z : E ↦ (((f∗) z).toReal)) (∑ j : Fin p, w j))
        (unconstrained_problem_solutions (DualBlockMinimizationView.objective f g))
        (-EReal.toReal (q_opt(f, g)))
        LfRaw
        (fun _ : Fin p ↦ σ⁻¹))
    (z : Fin p → E)
    (m : ℕ) (hm : m ≤ p) :
    randomized_block_proximal_gradient_method
        hblock.toIsBlockProximalGradientProblem
        z
        (dual_block_proximal_gradient_cyclic_block_index p)
        m =
      cyclic_block_proximal_gradient_inner_iterate hblock z m := by
  induction m with
  | zero =>
      -- Both owners start from the same base point at stage zero.
      simp
  | succ m ih =>
      have hm_prev : m ≤ p := Nat.le_of_succ_le hm
      have hm_lt : m < p := Nat.lt_of_succ_le hm
      -- Route correction: normalize the chosen cyclic block before comparing the one-step updates.
      rw [randomized_block_proximal_gradient_method_succ, ih hm_prev]
      have hidx :
          dual_block_proximal_gradient_cyclic_block_index p m = (⟨m, hm_lt⟩ : Fin p) := by
        ext
        rw [dual_block_proximal_gradient_cyclic_block_index_val]
        simpa using Nat.mod_eq_of_lt hm_lt
      rw [hidx]
      -- After the prefix state is identified, the next RBPG update is exactly the CBPG stage step.
      let x' := cyclic_block_proximal_gradient_inner_iterate hblock z m
      calc
        block_coordinate_update x' ⟨m, hm_lt⟩
            (hblock.prox_point (σ⁻¹) ⟨m, hm_lt⟩ x' - x' ⟨m, hm_lt⟩) =
            x' + 𝒰[(⟨m, hm_lt⟩ : Fin p)]
              (hblock.prox_point (σ⁻¹) ⟨m, hm_lt⟩ x' - x' ⟨m, hm_lt⟩) := by
              simpa [x'] using
                (block_proximal_gradient_update_eq_add_block_embedding
                  (T := fun i x ↦ hblock.prox_point (σ⁻¹) i x)
                  (x := x')
                  (i := (⟨m, hm_lt⟩ : Fin p)))
        _ = cyclic_block_proximal_gradient_inner_iterate hblock z (m + 1) := by
              symm
              simpa [x'] using
                (cyclic_block_proximal_gradient_inner_iterate_succ
                  (hproblem := hblock)
                  (xk := z)
                  hm_lt)

include y0 x y h_problem h_trajectory α0 h_initial_level R h_R

/-- Helper for Theorem 12.17 (`thm:12.17`): for the deterministic cyclic schedule, the pathwise
randomized Chapter 11 recursion agrees exactly with the cyclic inner-iterate recursion at every
time `p * k + m`. -/
lemma cyclicRandomizedMinimizationViewIterate_eqCbpgInnerIterate
    {LfRaw : NNReal}
    (hblock :
      BlockProximalGradientAssumptions
        (DualBlockMinimizationView.smoothTerm f)
        (fun i z ↦ ((g i)∗) (-z))
        (fun _ : Fin p ↦ fun w : Fin p → E ↦
          gradient (fun z : E ↦ (((f∗) z).toReal)) (∑ j : Fin p, w j))
        (unconstrained_problem_solutions (DualBlockMinimizationView.objective f g))
        (-EReal.toReal (q_opt(f, g)))
        LfRaw
        (fun _ : Fin p ↦ σ⁻¹))
    (y0_eff : effective_domain (DualBlockMinimizationView.regularizer g))
    (k m : ℕ) (hm : m ≤ p) :
    randomized_block_proximal_gradient_method
        hblock.toIsBlockProximalGradientProblem
        (hblock.interior_effective_domain_point y0_eff)
        (dual_block_proximal_gradient_cyclic_block_index p)
        (p * k + m) =
      cyclic_block_proximal_gradient_inner_iterate
        hblock
        (cyclic_block_proximal_gradient_method
          hblock
          (hblock.interior_effective_domain_point y0_eff)
          k)
        m := by
  let z0 := hblock.interior_effective_domain_point y0_eff
  revert m hm
  induction k with
  | zero =>
      intro m hm
      -- In the base outer cycle, synchronization is exactly the prefix agreement up to stage `m`.
      simpa [z0, Nat.zero_mul, Nat.zero_add] using
        (cyclicRbpgPrefix_eqCbpgInnerIterate
          (σ := σ)
          (f := f)
          (g := g)
          (hblock := hblock)
          (z := z0)
          (m := m)
          (hm := hm))
  | succ k ih =>
      intro m hm
      have houter_prev :
          randomized_block_proximal_gradient_method
              hblock.toIsBlockProximalGradientProblem
              z0
              (dual_block_proximal_gradient_cyclic_block_index p)
              (p * k) =
            cyclic_block_proximal_gradient_method hblock z0 k := by
        simpa [z0] using ih 0 (Nat.zero_le p)
      have hshifted_outer :
          randomized_block_proximal_gradient_method
              hblock.toIsBlockProximalGradientProblem
              z0
              (dual_block_proximal_gradient_cyclic_block_index p)
              (p * (k + 1)) =
            cyclic_block_proximal_gradient_method hblock z0 (k + 1) := by
        calc
          randomized_block_proximal_gradient_method
              hblock.toIsBlockProximalGradientProblem
              z0
              (dual_block_proximal_gradient_cyclic_block_index p)
              (p * (k + 1)) =
              randomized_block_proximal_gradient_method
                hblock.toIsBlockProximalGradientProblem
                (randomized_block_proximal_gradient_method
                  hblock.toIsBlockProximalGradientProblem
                  z0
                  (dual_block_proximal_gradient_cyclic_block_index p)
                  (p * k))
                (fun t ↦ dual_block_proximal_gradient_cyclic_block_index p (p * k + t))
                p := by
                  simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
                    (randomizedBlockProximalGradientMethod_add_eq_restart
                      (σ := σ)
                      (f := f)
                      (g := g)
                      (hcore := hblock.toIsBlockProximalGradientProblem)
                      (z := z0)
                      (schedule := dual_block_proximal_gradient_cyclic_block_index p)
                      (n := p * k)
                      (m := p))
          _ =
              randomized_block_proximal_gradient_method
                hblock.toIsBlockProximalGradientProblem
                (randomized_block_proximal_gradient_method
                  hblock.toIsBlockProximalGradientProblem
                  z0
                  (dual_block_proximal_gradient_cyclic_block_index p)
                  (p * k))
                (dual_block_proximal_gradient_cyclic_block_index p)
                p := by
                  apply randomizedBlockProximalGradientMethod_eq_ofPrefixEq
                    (σ := σ)
                    (f := f)
                    (g := g)
                    (hcore := hblock.toIsBlockProximalGradientProblem)
                    (z := randomized_block_proximal_gradient_method
                      hblock.toIsBlockProximalGradientProblem
                      z0
                      (dual_block_proximal_gradient_cyclic_block_index p)
                      (p * k))
                  intro t ht
                  have ht_lt : t < p := ht
                  have hshift_idx :
                      dual_block_proximal_gradient_cyclic_block_index p (p * k + t) =
                        (⟨t, ht_lt⟩ : Fin p) := by
                    ext
                    rw [dual_block_proximal_gradient_cyclic_block_index_val, Nat.add_mod,
                      Nat.mul_mod_right, zero_add]
                    simpa using Nat.mod_eq_of_lt ht_lt
                  have hbase_idx :
                      dual_block_proximal_gradient_cyclic_block_index p t =
                        (⟨t, ht_lt⟩ : Fin p) := by
                    ext
                    rw [dual_block_proximal_gradient_cyclic_block_index_val]
                    simpa using Nat.mod_eq_of_lt ht_lt
                  calc
                    dual_block_proximal_gradient_cyclic_block_index p (p * k + t) =
                        (⟨t, ht_lt⟩ : Fin p) := hshift_idx
                    _ = dual_block_proximal_gradient_cyclic_block_index p t := by
                      exact hbase_idx.symm
          _ =
              cyclic_block_proximal_gradient_inner_iterate
                hblock
                (randomized_block_proximal_gradient_method
                  hblock.toIsBlockProximalGradientProblem
                  z0
                  (dual_block_proximal_gradient_cyclic_block_index p)
                  (p * k))
                p := by
                  simpa using
                    (cyclicRbpgPrefix_eqCbpgInnerIterate
                      (σ := σ)
                      (f := f)
                      (g := g)
                      (hblock := hblock)
                      (z := randomized_block_proximal_gradient_method
                        hblock.toIsBlockProximalGradientProblem
                        z0
                        (dual_block_proximal_gradient_cyclic_block_index p)
                        (p * k))
                      (m := p)
                      (hm := (le_rfl : p ≤ p)))
          _ =
              cyclic_block_proximal_gradient_inner_iterate
                hblock
                (cyclic_block_proximal_gradient_method hblock z0 k)
                p := by
                  rw [houter_prev]
          _ = cyclic_block_proximal_gradient_method hblock z0 (k + 1) := by
                  rw [cyclic_block_proximal_gradient_method_succ]
      -- Restart at the beginning of the `(k + 1)`-st outer cycle, then compare the first `m`
      -- shifted blocks with the standard cyclic prefix `0,1,...,m-1`.
      calc
        randomized_block_proximal_gradient_method
            hblock.toIsBlockProximalGradientProblem
            z0
            (dual_block_proximal_gradient_cyclic_block_index p)
            (p * (k + 1) + m) =
            randomized_block_proximal_gradient_method
              hblock.toIsBlockProximalGradientProblem
              (randomized_block_proximal_gradient_method
                hblock.toIsBlockProximalGradientProblem
                z0
                (dual_block_proximal_gradient_cyclic_block_index p)
                (p * (k + 1)))
              (fun t ↦ dual_block_proximal_gradient_cyclic_block_index p (p * (k + 1) + t))
              m := by
                simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
                  (randomizedBlockProximalGradientMethod_add_eq_restart
                    (σ := σ)
                    (f := f)
                    (g := g)
                    (hcore := hblock.toIsBlockProximalGradientProblem)
                    (z := z0)
                    (schedule := dual_block_proximal_gradient_cyclic_block_index p)
                    (n := p * (k + 1))
                    (m := m))
        _ =
            randomized_block_proximal_gradient_method
              hblock.toIsBlockProximalGradientProblem
              (randomized_block_proximal_gradient_method
                hblock.toIsBlockProximalGradientProblem
                z0
                (dual_block_proximal_gradient_cyclic_block_index p)
                (p * (k + 1)))
              (dual_block_proximal_gradient_cyclic_block_index p)
              m := by
                apply randomizedBlockProximalGradientMethod_eq_ofPrefixEq
                  (σ := σ)
                  (f := f)
                  (g := g)
                  (hcore := hblock.toIsBlockProximalGradientProblem)
                  (z := randomized_block_proximal_gradient_method
                    hblock.toIsBlockProximalGradientProblem
                    z0
                    (dual_block_proximal_gradient_cyclic_block_index p)
                    (p * (k + 1)))
                intro t ht
                have ht_lt : t < p := lt_of_lt_of_le ht hm
                have hshift_idx :
                    dual_block_proximal_gradient_cyclic_block_index p (p * (k + 1) + t) =
                      (⟨t, ht_lt⟩ : Fin p) := by
                  ext
                  rw [dual_block_proximal_gradient_cyclic_block_index_val, Nat.add_mod,
                    Nat.mul_mod_right, zero_add]
                  simpa using Nat.mod_eq_of_lt ht_lt
                have hbase_idx :
                    dual_block_proximal_gradient_cyclic_block_index p t =
                      (⟨t, ht_lt⟩ : Fin p) := by
                  ext
                  rw [dual_block_proximal_gradient_cyclic_block_index_val]
                  simpa using Nat.mod_eq_of_lt ht_lt
                calc
                  dual_block_proximal_gradient_cyclic_block_index p (p * (k + 1) + t) =
                      (⟨t, ht_lt⟩ : Fin p) := hshift_idx
                  _ = dual_block_proximal_gradient_cyclic_block_index p t := by
                    exact hbase_idx.symm
        _ =
            randomized_block_proximal_gradient_method
              hblock.toIsBlockProximalGradientProblem
              (cyclic_block_proximal_gradient_method hblock z0 (k + 1))
              (dual_block_proximal_gradient_cyclic_block_index p)
              m := by
                rw [hshifted_outer]
        _ =
            cyclic_block_proximal_gradient_inner_iterate
              hblock
              (cyclic_block_proximal_gradient_method hblock z0 (k + 1))
              m := by
                simpa using
                  (cyclicRbpgPrefix_eqCbpgInnerIterate
                    (σ := σ)
                    (f := f)
                    (g := g)
                    (hblock := hblock)
                    (z := cyclic_block_proximal_gradient_method hblock z0 (k + 1))
                    (m := m)
                    (hm := hm))

/-- Helper for Theorem 12.17 (`thm:12.17`): the sampled cyclic DBPG outer iterate `y^(p k)`
agrees with the Chapter 11 CBPG outer iterate on the minimization view for a theorem-local raw
block owner. -/
lemma cyclicDbpgSampledOuterIterate_eqCbpgOuterIterate
    {yStar : Fin p → E}
    (hyStar : yStar ∈ Λ*(f, g))
    (hyStar_finite : yStar ∈ finite_domain (q(f, g))) :
    ∃ LfRaw : NNReal,
      ∃ hblock :
        BlockProximalGradientAssumptions
          (DualBlockMinimizationView.smoothTerm f)
          (fun i z ↦ ((g i)∗) (-z))
          (fun _ : Fin p ↦ fun w : Fin p → E ↦
            gradient (fun z : E ↦ (((f∗) z).toReal)) (∑ j : Fin p, w j))
          (unconstrained_problem_solutions (DualBlockMinimizationView.objective f g))
          (-EReal.toReal (q_opt(f, g)))
          LfRaw
          (fun _ : Fin p ↦ σ⁻¹),
        ∀ k : ℕ,
          (y (p * k)).ofLp =
            cyclic_block_proximal_gradient_method
              hblock
              (hblock.interior_effective_domain_point
                ⟨y0.ofLp,
                  initial_dual_point_mem_effective_domain_minimization_view
                    f
                    g
                    y0.ofLp
                    h_problem.toIsProperExtendedRealFunction
                    h_problem.g_proper
                    (initialDualPointMemFiniteDomain
                      (σ := σ)
                      (f := f)
                      (g := g)
                      (h_problem := h_problem)
                      (y0 := y0)
                      (x := x)
                      (y := y)
                      (h_trajectory := h_trajectory)
                      (α0 := α0)
                      (h_initial_level := h_initial_level)
                      (R := R)
                      (h_R := h_R))⟩)
              k := by
  obtain ⟨LfRaw, hblock⟩ :=
    dualBlockMinimizationViewBlockAssumptionsRaw
      (σ := σ)
      (f := f)
      (g := g)
      (y0 := y0)
      (x := x)
      (y := y)
      (h_problem := h_problem)
      (h_trajectory := h_trajectory)
      (α0 := α0)
      (h_initial_level := h_initial_level)
      (R := R)
      (h_R := h_R)
      hyStar
      hyStar_finite
  have hy0_finite :
      y0.ofLp ∈ finite_domain (q(f, g)) :=
    initialDualPointMemFiniteDomain
      (σ := σ)
      (f := f)
      (g := g)
      (h_problem := h_problem)
      (y0 := y0)
      (x := x)
      (y := y)
      (h_trajectory := h_trajectory)
      (α0 := α0)
      (h_initial_level := h_initial_level)
      (R := R)
      (h_R := h_R)
  have hy0_eff :
      y0.ofLp ∈ effective_domain (DualBlockMinimizationView.regularizer g) :=
    initial_dual_point_mem_effective_domain_minimization_view
      f
      g
      y0.ofLp
      h_problem.toIsProperExtendedRealFunction
      h_problem.g_proper
      hy0_finite
  let hRBPG :
      RandomizedBlockProximalGradientAssumptions
        (DualBlockMinimizationView.smoothTerm f)
        (fun i z ↦ ((g i)∗) (-z))
        (fun _ : Fin p ↦ fun w : Fin p → E ↦
          gradient (fun z : E ↦ (((f∗) z).toReal)) (∑ j : Fin p, w j))
        (unconstrained_problem_solutions (DualBlockMinimizationView.objective f g))
        (-EReal.toReal (q_opt(f, g)))
        (fun _ : Fin p ↦ σ⁻¹) :=
    hblock.toRandomizedBlockProximalGradientAssumptions
      (dualBlockMinimizationViewSmoothTermConvex
        (σ := σ)
        (f := f)
        (g := g)
        (y0 := y0)
        (x := x)
        (y := y)
        (h_problem := h_problem)
        (h_trajectory := h_trajectory)
        (α0 := α0)
        (h_initial_level := h_initial_level)
        (R := R)
        (h_R := h_R))
  refine ⟨LfRaw, hblock, ?_⟩
  intro k
  -- Route correction: first identify the deterministic DBPG path with the Chapter 11 RBPG path,
  -- then collapse the cyclic RBPG recursion to the CBPG outer iterate by taking `m = 0`.
  calc
    (y (p * k)).ofLp =
        randomized_block_proximal_gradient_method
          hblock.toIsBlockProximalGradientProblem
          (hblock.interior_effective_domain_point ⟨y0.ofLp, hy0_eff⟩)
          (dual_block_proximal_gradient_cyclic_block_index p)
          (p * k) := by
            simpa using
              (randomized_dbpg_realized_minimization_view_method_eq
                (Ω := Unit)
                (σ := σ)
                (f := f)
                (g := g)
                (y0 := y0.ofLp)
                (sampled_block := fun n _ ↦ dual_block_proximal_gradient_cyclic_block_index p n)
                (x := fun n _ ↦ x n)
                (y := fun n _ ↦ (y n).ofLp)
                h_problem.toIsDualBlockProximalGradientProblem
                (by
                  intro ω
                  simpa using h_trajectory)
                hRBPG
                hy0_eff
                ()
                (p * k))
    _ =
        cyclic_block_proximal_gradient_inner_iterate
          hblock
          (cyclic_block_proximal_gradient_method
            hblock
            (hblock.interior_effective_domain_point ⟨y0.ofLp, hy0_eff⟩)
            k)
          0 := by
            simpa using
              (cyclicRandomizedMinimizationViewIterate_eqCbpgInnerIterate
                (σ := σ)
                (f := f)
                (g := g)
                (y0 := y0)
                (x := x)
                (y := y)
                (h_problem := h_problem)
                (h_trajectory := h_trajectory)
                (α0 := α0)
                (h_initial_level := h_initial_level)
                (R := R)
                (h_R := h_R)
                hblock
                ⟨y0.ofLp, hy0_eff⟩
                k
                0
                (Nat.zero_le p))
    _ =
        cyclic_block_proximal_gradient_method
          hblock
          (hblock.interior_effective_domain_point ⟨y0.ofLp, hy0_eff⟩)
          k := by
            simp

/-- Helper for Theorem 12.17 (`thm:12.17`): the canonical continuous linear equivalence from raw
block tuples to the Euclidean `PiLp` owner. -/
private def blockToPiLp : (Fin p → E) ≃L[ℝ] PiLp 2 (fun _ : Fin p ↦ E) :=
  ContinuousLinearEquiv.symm (PiLp.continuousLinearEquiv (2 : ENNReal) ℝ (fun _ : Fin p ↦ E))

/-- Helper for Theorem 12.17 (`thm:12.17`): pull the Euclidean-product seminormed additive
structure back to raw block tuples. -/
local instance blockL2SeminormedAddCommGroup : SeminormedAddCommGroup (Fin p → E) := by
  exact (blockToPiLp (E := E) (p := p)).toEquiv.seminormedAddCommGroup

/-- Helper for Theorem 12.17 (`thm:12.17`): from this point on, block-vector norms on
`Fin p → E` use the transported Euclidean `PiLp` owner required by the theorem statement. -/
local instance blockL2NormedAddCommGroup : NormedAddCommGroup (Fin p → E) := by
  exact (blockToPiLp (E := E) (p := p)).toEquiv.normedAddCommGroup

/-- Helper for Theorem 12.17 (`thm:12.17`): distances on raw block tuples use the same
transported Euclidean product metric as the local `PiLp` norm. -/
local instance blockL2PseudoMetricSpace : PseudoMetricSpace (Fin p → E) := by
  exact blockL2SeminormedAddCommGroup.toPseudoMetricSpace

omit [NeZero p] [FiniteDimensional ℝ E] h_problem h_trajectory h_initial_level h_R in
omit [NeZero p] [FiniteDimensional ℝ E] h_problem h_trajectory h_initial_level h_R in
omit y0 x y α0 R in
/-- Helper for Theorem 12.17 (`thm:12.17`): the raw ambient product norm is bounded by the
transported Euclidean `PiLp` norm on the same block vector. -/
lemma rawAmbientNorm_eq_toPiLpNorm
    (v : Fin p → E) :
    ‖v‖ = ‖WithLp.toLp 2 v‖ := by
  simpa using
    (PiLp.norm_seminormedAddCommGroupToPi
      (p := 2)
      (α := fun _ : Fin p ↦ E)
      v)

omit [NeZero p] [FiniteDimensional ℝ E] h_problem h_trajectory h_initial_level h_R in
omit y0 x y α0 R in
/-- Helper for Theorem 12.17 (`thm:12.17`): the `blockToPiLp` equivalence preserves the
Euclidean product norm on raw block tuples. -/
lemma blockToPiLp_norm_eq
    (v : Fin p → E) :
    ‖blockToPiLp (E := E) (p := p) v‖ = ‖v‖ := by
  simpa [blockToPiLp] using
    (PiLp.norm_seminormedAddCommGroupToPi
      (p := 2)
      (α := fun _ : Fin p ↦ E)
      v).symm

omit [NeZero p] [FiniteDimensional ℝ E] h_problem h_trajectory h_initial_level h_R in
omit y0 x y α0 R in
/-- Helper for Theorem 12.17 (`thm:12.17`): the transported Euclidean product norm expands as the
sum of the squared coordinate norms. -/
lemma blockNorm_sq_eq_sum_sq
    (v : Fin p → E) :
    ‖v‖ ^ (2 : ℕ) = ∑ i : Fin p, ‖v i‖ ^ (2 : ℕ) := by
  simpa [blockToPiLp] using
    (PiLp.norm_sq_eq_of_L2
      (fun _ : Fin p ↦ E)
      ((blockToPiLp (E := E) (p := p)) v))

omit [NeZero p] [FiniteDimensional ℝ E] h_problem h_trajectory h_initial_level h_R in
omit y0 x y α0 R in
/-- Helper for Theorem 12.17 (`thm:12.17`): each coordinate norm is bounded by the transported
Euclidean product norm of the full block tuple. -/
lemma coordNorm_le_blockNorm
    (v : Fin p → E) (i : Fin p) :
    ‖v i‖ ≤ ‖v‖ := by
  simpa [blockToPiLp] using
    (PiLp.norm_apply_le
      ((blockToPiLp (E := E) (p := p)) v)
      i)

omit [NeZero p] [FiniteDimensional ℝ E] h_problem h_trajectory h_initial_level h_R in
omit y0 x y α0 R in
/-- Helper for Theorem 12.17 (`thm:12.17`): the transported Euclidean product norm on raw block
tuples is nonnegative. -/
lemma blockNorm_nonneg
    (v : Fin p → E) :
    0 ≤ ‖v‖ := by
  have hEq : ‖v‖ = ‖blockToPiLp (E := E) (p := p) v‖ := by
    simpa [blockToPiLp] using
      (PiLp.norm_seminormedAddCommGroupToPi
        (p := 2)
        (α := fun _ : Fin p ↦ E)
        v)
  rw [hEq]
  exact norm_nonneg ((blockToPiLp (E := E) (p := p)) v)

omit [NeZero p] [FiniteDimensional ℝ E] h_problem h_trajectory h_initial_level h_R in
omit y0 x y α0 R in
/-- Helper for Theorem 12.17 (`thm:12.17`): the transported Euclidean product norm is symmetric
under reversing a blockwise difference. -/
lemma blockNorm_sub_rev
    (u v : Fin p → E) :
    ‖u - v‖ = ‖v - u‖ := by
  simpa [blockToPiLp, sub_eq_add_neg] using
    norm_sub_rev
      ((blockToPiLp (E := E) (p := p)) u)
      ((blockToPiLp (E := E) (p := p)) v)

omit [NeZero p] [FiniteDimensional ℝ E] h_problem h_trajectory h_initial_level h_R in
omit y0 x y α0 R in
/-- Helper for Theorem 12.17 (`thm:12.17`): the raw ambient product norm is bounded by the
transported Euclidean `PiLp` norm on the same block vector. -/
lemma rawAmbientNorm_le_toPiLpNorm
    (v : Fin p → E) :
    ‖v‖ ≤ ‖WithLp.toLp 2 v‖ := by
  -- The local ambient norm is already the transported `PiLp` norm.
  exact le_of_eq <| by
    simpa using
      (PiLp.norm_seminormedAddCommGroupToPi
        (p := 2)
        (α := fun _ : Fin p ↦ E)
        v)

omit [NeZero p] [FiniteDimensional ℝ E] h_problem h_trajectory h_initial_level h_R in
omit y0 x y α0 R in
/-- Helper for Theorem 12.17 (`thm:12.17`): the norm of the aggregate block sum is bounded by
`p` times the raw ambient product norm. This is the theorem-local bridge from the smoothness of
`f∗` on the summed dual variable to the displayed coefficient `p / σ`. -/
lemma sumBlockNorm_le_p_mul_rawAmbientNorm
    (v : Fin p → E) :
    ‖∑ i : Fin p, v i‖ ≤ (p : ℝ) * ‖v‖ := by
  -- First bound the norm of the sum by the sum of the coordinate norms.
  calc
    ‖∑ i : Fin p, v i‖ ≤ ∑ i : Fin p, ‖v i‖ := by
      simpa using (norm_sum_le (s := Finset.univ) (f := fun i : Fin p ↦ v i))
    _ ≤ ∑ _i : Fin p, ‖v‖ := by
      refine Finset.sum_le_sum ?_
      intro i hi
      simpa [blockToPiLp] using
        (PiLp.norm_apply_le
          ((blockToPiLp (E := E) (p := p)) v)
          i)
    _ = (p : ℝ) * ‖v‖ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Helper for Theorem 12.17 (`thm:12.17`): the source radius `R = R(q(y⁰))` controls the
initial minimization-view sublevel set `Hdual(w) ≤ Hdual(y⁰)` after rewriting `Hdual = -q` and
comparing the raw ambient norm with the Euclidean `PiLp` norm from Assumption 12.16. -/
lemma dualBlockMinimizationViewInitialRadiusBound
    {w : Fin p → E}
    (hw :
      DualBlockMinimizationView.objective f g w ≤
        DualBlockMinimizationView.objective f g y0.ofLp) :
    Metric.infDist w (unconstrained_problem_solutions (DualBlockMinimizationView.objective f g)) ≤
      R := by
  rcases h_problem.dual_optimal_set_nonempty with ⟨yStar, hyStar⟩
  let yStarLp : PiLp 2 (fun _ : Fin p ↦ E) := WithLp.toLp 2 yStar
  have hyStar_min :
      yStar ∈ unconstrained_problem_solutions (DualBlockMinimizationView.objective f g) := by
    exact
      optimal_dual_point_mem_unconstrained_problem_solutions_minimization_view
        (σ := σ)
        (f := f)
        (g := g)
        h_problem.toIsDualBlockProximalGradientProblem
        hyStar
  have hsuperlevel :
      ((α0 : ℝ) : EReal) ≤ q(f, g) w := by
    have hw_neg :
        -q(f, g) w ≤ -q(f, g) y0.ofLp := by
      -- Rewrite the minimization-view inequality to the source dual objective `q`.
      simpa [dual_block_dual_minimization_view_apply
        (f := f)
        (g := g)
        h_problem.toIsProperExtendedRealFunction
        h_problem.g_proper] using hw
    have hq_le : q(f, g) y0.ofLp ≤ q(f, g) w := by
      exact EReal.neg_le_neg_iff.mp hw_neg
    -- The fixed initial level `q(y⁰) = α₀` is exactly the superlevel threshold from the source.
    rw [h_initial_level] at hq_le
    exact hq_le
  have hpi :
      ‖WithLp.toLp 2 w - yStarLp‖ ≤ (R : ℝ) := by
    -- Apply the source superlevel-radius hypothesis at the current point and the chosen optimizer.
    simpa [yStarLp] using h_R (WithLp.toLp 2 w) yStarLp hsuperlevel (by simpa [yStarLp] using hyStar)
  -- Any one optimal dual point gives the required `infDist` upper bound for the minimization
  -- view.
  have hdist :
      dist w yStar = ‖WithLp.toLp 2 w - yStarLp‖ := by
    rw [dist_eq_norm]
    simpa [yStarLp] using
      rawAmbientNorm_eq_toPiLpNorm (E := E) (p := p) (v := w - yStar)
  refine (Metric.infDist_le_dist_of_mem hyStar_min).trans ?_
  rw [hdist]
  exact hpi

/-- Helper for Theorem 12.17 (`thm:12.17`): the theorem-local CBPG outer sequence on the
minimization view satisfies the Chapter 11 sufficient-decrease interface `(11.11)` in the raw
ambient norm. -/
lemma dualBlockMinimizationViewOuterStepDecreaseBound
    {LfRaw : NNReal}
    (hblock :
      BlockProximalGradientAssumptions
        (DualBlockMinimizationView.smoothTerm f)
        (fun i z ↦ ((g i)∗) (-z))
        (fun _ : Fin p ↦ fun w : Fin p → E ↦
          gradient (fun z : E ↦ (((f∗) z).toReal)) (∑ j : Fin p, w j))
        (unconstrained_problem_solutions (DualBlockMinimizationView.objective f g))
        (-EReal.toReal (q_opt(f, g)))
        LfRaw
        (fun _ : Fin p ↦ σ⁻¹))
    (y0_eff : effective_domain (DualBlockMinimizationView.regularizer g))
    (k : ℕ) :
    cbpgStepDecreaseBound
      (fun _ : Fin p ↦ σ⁻¹)
      (DualBlockMinimizationView.objective f g)
      (fun m ↦
        cyclic_block_proximal_gradient_method
          hblock
          (hblock.interior_effective_domain_point y0_eff)
          m)
      k := by
  let _ : Nonempty (Fin p) :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne p)⟩⟩
  let z0 := hblock.interior_effective_domain_point y0_eff
  let zSeq :
      ℕ → Fin p → E := fun m ↦
        cyclic_block_proximal_gradient_method hblock z0 m
  let toPiLp :=
    ContinuousLinearEquiv.symm
      (PiLp.continuousLinearEquiv (2 : ENNReal) ℝ (fun _ : Fin p ↦ E))
  have hraw :
      ‖zSeq k - zSeq (k + 1)‖ ≤ ‖toPiLp (zSeq k - zSeq (k + 1))‖ := by
    -- Compare the raw ambient product norm with the canonical `PiLp` norm on the same outer
    -- step.
    simpa [zSeq, toPiLp] using
      rawAmbientNorm_le_toPiLpNorm (v := zSeq k - zSeq (k + 1))
  have hraw_sq :
      ‖zSeq k - zSeq (k + 1)‖ ^ (2 : ℕ) ≤
        ‖toPiLp (zSeq k - zSeq (k + 1))‖ ^ (2 : ℕ) := by
    have hnonneg : 0 ≤ ‖zSeq k - zSeq (k + 1)‖ := by
      have hEq :
          ‖zSeq k - zSeq (k + 1)‖ =
            ‖toPiLp (zSeq k - zSeq (k + 1))‖ := by
        simpa [toPiLp, blockToPiLp] using
          (PiLp.norm_seminormedAddCommGroupToPi
            (p := 2)
            (α := fun _ : Fin p ↦ E)
            (zSeq k - zSeq (k + 1)))
      rw [hEq]
      exact norm_nonneg _
    exact
      pow_le_pow_left₀
        hnonneg
        hraw
        2
  have hcoeff_nonneg :
      0 ≤ (((cbpg_min_block_stepsize (fun _ : Fin p ↦ σ⁻¹) : PosReal) : ℝ) / 2) := by
    exact div_nonneg
      (le_of_lt (PosReal.coe_pos (cbpg_min_block_stepsize (fun _ : Fin p ↦ σ⁻¹))))
      (by norm_num)
  have hreal :
      (((cbpg_min_block_stepsize (fun _ : Fin p ↦ σ⁻¹) : PosReal) : ℝ) / 2) *
          ‖zSeq k - zSeq (k + 1)‖ ^ (2 : ℕ) ≤
        (((cbpg_min_block_stepsize (fun _ : Fin p ↦ σ⁻¹) : PosReal) : ℝ) / 2) *
          ‖toPiLp (zSeq k - zSeq (k + 1))‖ ^ (2 : ℕ) := by
    -- Scale the squared-step comparison by the common Chapter 11 coefficient `L_min / 2`.
    exact mul_le_mul_of_nonneg_left hraw_sq hcoeff_nonneg
  have hleft :
      (((((cbpg_min_block_stepsize (fun _ : Fin p ↦ σ⁻¹) : PosReal) : ℝ) / 2) *
          ‖zSeq k - zSeq (k + 1)‖ ^ (2 : ℕ) : ℝ) : EReal) ≤
        (((((cbpg_min_block_stepsize (fun _ : Fin p ↦ σ⁻¹) : PosReal) : ℝ) / 2) *
            ‖toPiLp (zSeq k - zSeq (k + 1))‖ ^ (2 : ℕ) : ℝ) : EReal) := by
    exact EReal.coe_le_coe hreal
  -- Compose the raw-vs-`PiLp` comparison with the owner sufficient-decrease estimate.
  exact hleft.trans <|
    cbpg_sufficient_decrease_outer_step hblock y0_eff k

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  y0 x y h_problem h_trajectory α0 h_initial_level R h_R in
/-- Helper for Theorem 12.17 (`thm:12.17`): for the constant block stepsize family `σ⁻¹`, both
finite Chapter 11 extrema collapse to that same constant. -/
lemma cbpgConstantBlockStepsizeExtrema :
    cbpg_min_block_stepsize (fun _ : Fin p ↦ σ⁻¹) = σ⁻¹ ∧
      cbpg_max_block_stepsize (fun _ : Fin p ↦ σ⁻¹) = σ⁻¹ := by
  classical
  constructor
  · -- The finite minimum of a constant family is the shared constant.
    unfold cbpg_min_block_stepsize
    simp
  · -- The finite maximum of the same constant family is again the shared constant.
    rw [cbpg_max_block_stepsize_def]
    simp

/-- Helper for Theorem 12.17 (`thm:12.17`): once the Chapter 11 coefficient uses
`Lf = p / σ` and `Li = σ⁻¹`, its sublinear branch is exactly the textbook
`8 p (p + 1)^2 R^2 / (σ (k - 1))` term from `cyclicGapBound`. -/
lemma dualBlockMinimizationViewCyclicCoeff_eq_cyclicGapBound
    (initialGap : ℝ) (k : ℕ) :
    max
        (((1 / 2 : ℝ) ^ (((k - 1 : ℕ) : ℝ) / 2)) * initialGap)
        (4 /
          (cbpg_quadratic_gap_constant
            (Real.toNNReal ((p : ℝ) / (σ : ℝ)))
            (fun _ : Fin p ↦ σ⁻¹)
            R *
            (((k - 1 : ℕ) : ℝ)))) =
      cyclicGapBound p σ R initialGap k := by
  have hσ_pos : 0 < (σ : ℝ) := PosReal.coe_pos σ
  have hσ_ne : (σ : ℝ) ≠ 0 := hσ_pos.ne'
  have hLf_nonneg : 0 ≤ (p : ℝ) / (σ : ℝ) := by
    exact div_nonneg (show 0 ≤ (p : ℝ) by exact_mod_cast Nat.zero_le p) hσ_pos.le
  rcases cbpgConstantBlockStepsizeExtrema (σ := σ) (p := p) with ⟨hmin, hmax⟩
  rw [cyclicGapBound_apply, cbpg_quadratic_gap_constant_def, hmin, hmax]
  have hLf :
      ((Real.toNNReal ((p : ℝ) / (σ : ℝ)) : NNReal) : ℝ) = (p : ℝ) / (σ : ℝ) := by
    exact congrArg (fun x : NNReal ↦ (x : ℝ)) (Real.toNNReal_of_nonneg hLf_nonneg)
  rw [hLf]
  have hp_ne : (p : ℝ) ≠ 0 := by
    exact_mod_cast NeZero.ne p
  have hR_ne : (R : ℝ) ≠ 0 := (PosReal.coe_pos R).ne'
  have hσinv :
      (((σ⁻¹ : PosReal) : ℝ)) = 1 / (σ : ℝ) := by
    simp [PosReal.coe_inv]
  have hsum :
      (p : ℝ) / (σ : ℝ) + (((σ⁻¹ : PosReal) : ℝ)) = ((p + 1 : ℝ) / (σ : ℝ)) := by
    rw [hσinv]
    field_simp [hσ_ne]
  rw [hsum]
  by_cases hk1 : (((k - 1 : ℕ) : ℝ)) = 0
  · -- When `k - 1 = 0`, both sublinear branches are definitionally zero.
    simp [hk1]
  · -- Away from the zero denominator, this is the textbook scalar normalization.
    rw [hσinv]
    field_simp [hσ_ne, hp_ne, hR_ne, hk1]
    ring

/-- Helper for Theorem 12.17 (`thm:12.17`): the theorem-local final residual at outer step `k`
combines the stagewise prox residual with the smooth-gradient drift from the stage point to the
outer successor. -/
def dualBlockMinimizationViewFinalResidual
    {LfRaw : NNReal}
    (hblock :
      BlockProximalGradientAssumptions
        (DualBlockMinimizationView.smoothTerm f)
        (fun i z ↦ ((g i)∗) (-z))
        (fun _ : Fin p ↦ fun w : Fin p → E ↦
          gradient (fun z : E ↦ (((f∗) z).toReal)) (∑ j : Fin p, w j))
        (unconstrained_problem_solutions (DualBlockMinimizationView.objective f g))
        (-EReal.toReal (q_opt(f, g)))
        LfRaw
        (fun _ : Fin p ↦ σ⁻¹))
    (y0Eff : effective_domain (DualBlockMinimizationView.regularizer g))
    (k : ℕ) : Fin p → E :=
  let x0I := hblock.interior_effective_domain_point y0Eff
  let xCbpg : ℕ → Fin p → E := fun m ↦
    cyclic_block_proximal_gradient_method hblock x0I m
  fun j ↦
    hblock.toIsBlockProximalGradientProblem.gradient_mapping
        (σ⁻¹)
        j
        (cyclic_block_proximal_gradient_inner_iterate hblock (xCbpg k) j.1) +
      (gradient (fun z : E ↦ (((f∗) z).toReal)) (∑ i : Fin p, xCbpg (k + 1) i) -
        gradient (fun z : E ↦ (((f∗) z).toReal))
          (∑ i : Fin p, cyclic_block_proximal_gradient_inner_iterate hblock (xCbpg k) j.1 i))

/-- Helper for Theorem 12.17 (`thm:12.17`): the suffix of one outer cycle, from the stage point
before block `j` is revisited to the final outer successor, is no longer than the full outer
step in the raw ambient norm. -/
lemma dualBlockMinimizationViewSuffixDisplacementNormLeOuterStepNorm
    {LfRaw : NNReal}
    (hblock :
      BlockProximalGradientAssumptions
        (DualBlockMinimizationView.smoothTerm f)
        (fun i z ↦ ((g i)∗) (-z))
        (fun _ : Fin p ↦ fun w : Fin p → E ↦
          gradient (fun z : E ↦ (((f∗) z).toReal)) (∑ j : Fin p, w j))
        (unconstrained_problem_solutions (DualBlockMinimizationView.objective f g))
        (-EReal.toReal (q_opt(f, g)))
        LfRaw
        (fun _ : Fin p ↦ σ⁻¹))
    (y0Eff : effective_domain (DualBlockMinimizationView.regularizer g))
    (k : ℕ) (j : Fin p) :
    ‖cyclic_block_proximal_gradient_inner_iterate
        hblock
        (cyclic_block_proximal_gradient_method
          hblock
          (hblock.interior_effective_domain_point y0Eff)
          k)
        j.1 -
      cyclic_block_proximal_gradient_method
        hblock
        (hblock.interior_effective_domain_point y0Eff)
        (k + 1)‖ ≤
      ‖cyclic_block_proximal_gradient_method
          hblock
          (hblock.interior_effective_domain_point y0Eff)
          k -
        cyclic_block_proximal_gradient_method
          hblock
          (hblock.interior_effective_domain_point y0Eff)
          (k + 1)‖ := by
  let x0I := hblock.interior_effective_domain_point y0Eff
  let xCbpg : ℕ → Fin p → E := fun m ↦
    cyclic_block_proximal_gradient_method hblock x0I m
  let xStage : Fin p → E :=
    cyclic_block_proximal_gradient_inner_iterate hblock (xCbpg k) j.1
  let toPiLp := blockToPiLp (E := E) (p := p)
  have hsq_stage :
      ‖xStage - xCbpg (k + 1)‖ ^ (2 : ℕ) =
        Finset.sum Finset.univ
          (fun i : Fin p ↦ ‖(xStage - xCbpg (k + 1)) i‖ ^ (2 : ℕ)) := by
    simpa using
      (blockNorm_sq_eq_sum_sq (v := xStage - xCbpg (k + 1)))
  have hsq_outer :
      ‖xCbpg k - xCbpg (k + 1)‖ ^ (2 : ℕ) =
        Finset.sum Finset.univ
          (fun i : Fin p ↦ ‖(xCbpg k - xCbpg (k + 1)) i‖ ^ (2 : ℕ)) := by
    simpa using
      (blockNorm_sq_eq_sum_sq (v := xCbpg k - xCbpg (k + 1)))
  have hcoord_sq :
      ∀ i : Fin p,
        ‖(xStage - xCbpg (k + 1)) i‖ ^ (2 : ℕ) ≤
          ‖(xCbpg k - xCbpg (k + 1)) i‖ ^ (2 : ℕ) := by
    intro i
    by_cases hij : i.1 < j.1
    · have hstage_eq :
          xStage i = xCbpg (k + 1) i := by
        exact
          cbpg_auxiliary_iterate_apply_eq_outer_successor_of_lt
            hblock
            y0Eff
            k
            j.1
            i
            hij
            (Nat.le_of_lt j.2)
      -- Coordinates updated before stage `j` have already stabilized to the outer successor.
      have hsubeq : (xStage - xCbpg (k + 1)) i = 0 := by
        rw [Pi.sub_apply, hstage_eq, sub_self]
      simp [hsubeq]
    · have hstage_eq :
          xStage i = xCbpg k i := by
        exact
          cbpg_auxiliary_iterate_apply_eq_outer_iterate
            hblock
            y0Eff
            k
            j.1
            i
            (le_of_not_gt hij)
      -- Coordinates not yet updated at stage `j` still agree with the current outer iterate.
      have hsubeq :
          (xStage - xCbpg (k + 1)) i = xCbpg k i - xCbpg (k + 1) i := by
        rw [Pi.sub_apply, hstage_eq]
      simp [hsubeq]
  have hsq_le :
      ‖xStage - xCbpg (k + 1)‖ ^ (2 : ℕ) ≤ ‖xCbpg k - xCbpg (k + 1)‖ ^ (2 : ℕ) := by
    calc
      ‖xStage - xCbpg (k + 1)‖ ^ (2 : ℕ) =
          Finset.sum Finset.univ
            (fun i : Fin p ↦ ‖(xStage - xCbpg (k + 1)) i‖ ^ (2 : ℕ)) := hsq_stage
      _ ≤ Finset.sum Finset.univ
            (fun i : Fin p ↦ ‖(xCbpg k - xCbpg (k + 1)) i‖ ^ (2 : ℕ)) := by
          exact Finset.sum_le_sum fun i _ ↦ hcoord_sq i
      _ = ‖xCbpg k - xCbpg (k + 1)‖ ^ (2 : ℕ) := hsq_outer.symm
  have hstage_nonneg : 0 ≤ ‖xStage - xCbpg (k + 1)‖ := by
    have hEq :
        ‖xStage - xCbpg (k + 1)‖ =
          ‖toPiLp (xStage - xCbpg (k + 1))‖ := by
      simpa [toPiLp, blockToPiLp] using
        (PiLp.norm_seminormedAddCommGroupToPi
          (p := 2)
          (α := fun _ : Fin p ↦ E)
          (xStage - xCbpg (k + 1)))
    rw [hEq]
    exact norm_nonneg _
  have houter_nonneg : 0 ≤ ‖xCbpg k - xCbpg (k + 1)‖ := by
    have hEq :
        ‖xCbpg k - xCbpg (k + 1)‖ =
          ‖toPiLp (xCbpg k - xCbpg (k + 1))‖ := by
      simpa [toPiLp, blockToPiLp] using
        (PiLp.norm_seminormedAddCommGroupToPi
          (p := 2)
          (α := fun _ : Fin p ↦ E)
          (xCbpg k - xCbpg (k + 1)))
    rw [hEq]
    exact norm_nonneg _
  nlinarith

/-- Helper for Theorem 12.17 (`thm:12.17`): the smooth-gradient drift from the stage point to the
outer successor is controlled by the displayed coefficient `p / σ` times the outer-step norm. -/
lemma dualBlockMinimizationViewBlockGradientDriftLeExplicitOuterStep
    {LfRaw : NNReal}
    (hblock :
      BlockProximalGradientAssumptions
        (DualBlockMinimizationView.smoothTerm f)
        (fun i z ↦ ((g i)∗) (-z))
        (fun _ : Fin p ↦ fun w : Fin p → E ↦
          gradient (fun z : E ↦ (((f∗) z).toReal)) (∑ j : Fin p, w j))
        (unconstrained_problem_solutions (DualBlockMinimizationView.objective f g))
        (-EReal.toReal (q_opt(f, g)))
        LfRaw
        (fun _ : Fin p ↦ σ⁻¹))
    (y0Eff : effective_domain (DualBlockMinimizationView.regularizer g))
    (k : ℕ) (j : Fin p) :
    ‖gradient (fun z : E ↦ (((f∗) z).toReal))
        (∑ i : Fin p,
          cyclic_block_proximal_gradient_method
            hblock
            (hblock.interior_effective_domain_point y0Eff)
            (k + 1) i) -
      gradient (fun z : E ↦ (((f∗) z).toReal))
        (∑ i : Fin p,
          cyclic_block_proximal_gradient_inner_iterate
            hblock
            (cyclic_block_proximal_gradient_method
              hblock
              (hblock.interior_effective_domain_point y0Eff)
              k)
            j.1 i)‖ ≤
      ((p : ℝ) / (σ : ℝ)) *
        ‖cyclic_block_proximal_gradient_method
            hblock
            (hblock.interior_effective_domain_point y0Eff)
            k -
          cyclic_block_proximal_gradient_method
            hblock
            (hblock.interior_effective_domain_point y0Eff)
            (k + 1)‖ := by
  let x0I := hblock.interior_effective_domain_point y0Eff
  let xCbpg : ℕ → Fin p → E := fun m ↦
    cyclic_block_proximal_gradient_method hblock x0I m
  let xStage : Fin p → E :=
    cyclic_block_proximal_gradient_inner_iterate hblock (xCbpg k) j.1
  let φ : E → ℝ := fun z ↦ (((f∗) z).toReal)
  have hsmooth :
      is_l_smooth_on φ Set.univ (Real.toNNReal (1 / (σ : ℝ))) := by
    -- Global `1 / σ` smoothness of `f∗` controls the gradient drift between the two summed
    -- dual points.
    simpa [φ] using
      conjugate_function_primal_is_l_smooth_on_of_proper_closed_strongConvexOn
        (σ := σ)
        (f := f)
        h_problem.toIsProperExtendedRealFunction
        h_problem.f_closed
        h_problem.f_strongly_convex
  have hσ_nonneg : 0 ≤ 1 / (σ : ℝ) := by
    exact div_nonneg (by norm_num) (le_of_lt (PosReal.coe_pos σ))
  have hgrad_base :
      ‖gradient φ (∑ i : Fin p, xCbpg (k + 1) i) -
          gradient φ (∑ i : Fin p, xStage i)‖ ≤
        (1 / (σ : ℝ)) * ‖(∑ i : Fin p, xCbpg (k + 1) i) - ∑ i : Fin p, xStage i‖ := by
    have hgrad :=
      (is_l_smooth_on_iff_forall_norm_sub_le.mp hsmooth).2
        (∑ i : Fin p, xCbpg (k + 1) i)
        (by simp)
        (∑ i : Fin p, xStage i)
        (by simp)
    calc
      ‖gradient φ (∑ i : Fin p, xCbpg (k + 1) i) -
          gradient φ (∑ i : Fin p, xStage i)‖
          ≤ ((Real.toNNReal (1 / (σ : ℝ)) : NNReal) : ℝ) *
              ‖(∑ i : Fin p, xCbpg (k + 1) i) - ∑ i : Fin p, xStage i‖ := hgrad
      _ = (1 / (σ : ℝ)) * ‖(∑ i : Fin p, xCbpg (k + 1) i) - ∑ i : Fin p, xStage i‖ := by
          have hσ_cast :
              (((Real.toNNReal (1 / (σ : ℝ)) : NNReal) : ℝ)) = 1 / (σ : ℝ) := by
            exact congrArg (fun x : NNReal ↦ (x : ℝ)) (Real.toNNReal_of_nonneg hσ_nonneg)
          rw [hσ_cast]
  have hsum :
      ‖(∑ i : Fin p, xCbpg (k + 1) i) - ∑ i : Fin p, xStage i‖ ≤
        (p : ℝ) * ‖xCbpg (k + 1) - xStage‖ := by
    simpa [xStage, Finset.sum_sub_distrib] using
      (sumBlockNorm_le_p_mul_rawAmbientNorm
        (E := E)
        (p := p)
        (v := xCbpg (k + 1) - xStage))
  have hsuffix :
      ‖xCbpg (k + 1) - xStage‖ ≤ ‖xCbpg k - xCbpg (k + 1)‖ := by
    have hsuffix0 :
        ‖xStage - xCbpg (k + 1)‖ ≤ ‖xCbpg k - xCbpg (k + 1)‖ := by
      simpa [xStage] using
        (dualBlockMinimizationViewSuffixDisplacementNormLeOuterStepNorm
          (σ := σ)
          (f := f)
          (g := g)
          (y0 := y0)
          (x := x)
          (y := y)
          (h_problem := h_problem)
          (h_trajectory := h_trajectory)
          (α0 := α0)
          (h_initial_level := h_initial_level)
          (R := R)
          (h_R := h_R)
          hblock
          y0Eff
          k
          j)
    calc
      ‖xCbpg (k + 1) - xStage‖ = ‖xStage - xCbpg (k + 1)‖ := by
        simpa [blockToPiLp, sub_eq_add_neg] using
          norm_sub_rev
            ((blockToPiLp (E := E) (p := p)) (xCbpg (k + 1)))
            ((blockToPiLp (E := E) (p := p)) xStage)
      _ ≤ ‖xCbpg k - xCbpg (k + 1)‖ := hsuffix0
  have hscaled_sum :
      (1 / (σ : ℝ)) * ‖(∑ i : Fin p, xCbpg (k + 1) i) - ∑ i : Fin p, xStage i‖ ≤
        (1 / (σ : ℝ)) * ((p : ℝ) * ‖xCbpg (k + 1) - xStage‖) := by
    exact mul_le_mul_of_nonneg_left hsum hσ_nonneg
  have hscaled_suffix :
      (1 / (σ : ℝ)) * ((p : ℝ) * ‖xCbpg (k + 1) - xStage‖) ≤
        (1 / (σ : ℝ)) * ((p : ℝ) * ‖xCbpg k - xCbpg (k + 1)‖) := by
    have hp_nonneg : 0 ≤ (p : ℝ) := by exact_mod_cast Nat.zero_le p
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hsuffix hp_nonneg)
      hσ_nonneg
  -- Separate the smoothness estimate from the product-norm and suffix-displacement bridges.
  calc
    ‖gradient (fun z : E ↦ (((f∗) z).toReal))
        (∑ i : Fin p, xCbpg (k + 1) i) -
      gradient (fun z : E ↦ (((f∗) z).toReal))
        (∑ i : Fin p, xStage i)‖ ≤
      (1 / (σ : ℝ)) * ‖(∑ i : Fin p, xCbpg (k + 1) i) - ∑ i : Fin p, xStage i‖ := hgrad_base
    _ ≤ (1 / (σ : ℝ)) * ((p : ℝ) * ‖xCbpg (k + 1) - xStage‖) := hscaled_sum
    _ ≤ (1 / (σ : ℝ)) * ((p : ℝ) * ‖xCbpg k - xCbpg (k + 1)‖) := hscaled_suffix
    _ = ((p : ℝ) / (σ : ℝ)) * ‖xCbpg k - xCbpg (k + 1)‖ := by
      ring

/-- Helper for Theorem 12.17 (`thm:12.17`): each coordinate of the theorem-local final residual
is bounded by the full outer-step norm with the explicit coefficient `(p / σ) + σ⁻¹`. -/
lemma dualBlockMinimizationViewFinalResidualCoordinateNormLeExplicitOuterStep
    {LfRaw : NNReal}
    (hblock :
      BlockProximalGradientAssumptions
        (DualBlockMinimizationView.smoothTerm f)
        (fun i z ↦ ((g i)∗) (-z))
        (fun _ : Fin p ↦ fun w : Fin p → E ↦
          gradient (fun z : E ↦ (((f∗) z).toReal)) (∑ j : Fin p, w j))
        (unconstrained_problem_solutions (DualBlockMinimizationView.objective f g))
        (-EReal.toReal (q_opt(f, g)))
        LfRaw
        (fun _ : Fin p ↦ σ⁻¹))
    (y0Eff : effective_domain (DualBlockMinimizationView.regularizer g))
    (k : ℕ) (j : Fin p) :
    ‖dualBlockMinimizationViewFinalResidual (σ := σ) (f := f) (g := g)
        (LfRaw := LfRaw) hblock y0Eff k j‖ ≤
      (((p : ℝ) / (σ : ℝ)) + (((σ⁻¹ : PosReal) : ℝ))) *
        ‖cyclic_block_proximal_gradient_method
            hblock
            (hblock.interior_effective_domain_point y0Eff)
            k -
          cyclic_block_proximal_gradient_method
            hblock
            (hblock.interior_effective_domain_point y0Eff)
            (k + 1)‖ := by
  let x0I := hblock.interior_effective_domain_point y0Eff
  let xCbpg : ℕ → Fin p → E := fun m ↦
    cyclic_block_proximal_gradient_method hblock x0I m
  let xStage : Fin p → E :=
    cyclic_block_proximal_gradient_inner_iterate hblock (xCbpg k) j.1
  have hbefore_eq :
      xStage j = xCbpg k j := by
    exact
      cbpg_auxiliary_iterate_apply_eq_outer_iterate
        hblock
        y0Eff
        k
        j.1
        j
        (le_rfl)
  have hafter_eq :
      cyclic_block_proximal_gradient_inner_iterate hblock (xCbpg k) (j.1 + 1) j =
        xCbpg (k + 1) j := by
    exact
      cbpg_auxiliary_iterate_apply_eq_outer_successor_of_lt
        hblock
        y0Eff
        k
        (j.1 + 1)
        j
        (Nat.lt_succ_self j.1)
        (Nat.succ_le_of_lt j.2)
  have hsucc :
      cyclic_block_proximal_gradient_inner_iterate hblock (xCbpg k) (j.1 + 1) =
        block_coordinate_update
          xStage
          j
          (hblock.toIsBlockProximalGradientProblem.prox_point (σ⁻¹) j xStage - xStage j) := by
    -- The next inner stage is exactly the owner one-block prox update at block `j`.
    simpa [xStage] using
      cyclic_block_proximal_gradient_method_inner_succ hblock x0I k j.2
  have hprox :
      hblock.toIsBlockProximalGradientProblem.prox_point (σ⁻¹) j xStage =
        cyclic_block_proximal_gradient_inner_iterate hblock (xCbpg k) (j.1 + 1) j := by
    have hcoord := congrArg (fun z : Fin p → E ↦ z j) hsucc
    simpa [block_coordinate_update] using hcoord.symm
  have hstage_coord :
      hblock.toIsBlockProximalGradientProblem.gradient_mapping (σ⁻¹) j xStage =
        ((σ⁻¹ : PosReal) : ℝ) • (xCbpg k j - xCbpg (k + 1) j) := by
    -- Rewrite the stage residual through the updated block and then transport it to the outer
    -- coordinates.
    calc
      hblock.toIsBlockProximalGradientProblem.gradient_mapping (σ⁻¹) j xStage =
          ((σ⁻¹ : PosReal) : ℝ) •
            (xStage j -
              hblock.toIsBlockProximalGradientProblem.prox_point (σ⁻¹) j xStage) := by
        simpa using
          hblock.toIsBlockProximalGradientProblem.gradient_mapping_def
            (σ⁻¹)
            xStage
            j
      _ =
          ((σ⁻¹ : PosReal) : ℝ) •
            (xStage j -
              cyclic_block_proximal_gradient_inner_iterate hblock (xCbpg k) (j.1 + 1) j) := by
        rw [hprox]
      _ = ((σ⁻¹ : PosReal) : ℝ) • (xCbpg k j - xCbpg (k + 1) j) := by
        rw [hbefore_eq, hafter_eq]
  have hstage :
      ‖hblock.toIsBlockProximalGradientProblem.gradient_mapping (σ⁻¹) j xStage‖ ≤
        (((σ⁻¹ : PosReal) : ℝ)) * ‖xCbpg k - xCbpg (k + 1)‖ := by
    calc
      ‖hblock.toIsBlockProximalGradientProblem.gradient_mapping (σ⁻¹) j xStage‖ =
          (((σ⁻¹ : PosReal) : ℝ)) * ‖xCbpg k j - xCbpg (k + 1) j‖ := by
        rw [hstage_coord, norm_smul, Real.norm_of_nonneg (le_of_lt (PosReal.coe_pos (σ⁻¹)))]
      _ ≤ (((σ⁻¹ : PosReal) : ℝ)) * ‖xCbpg k - xCbpg (k + 1)‖ := by
        have hcoord :
            ‖xCbpg k j - xCbpg (k + 1) j‖ ≤ ‖xCbpg k - xCbpg (k + 1)‖ := by
          simpa [Pi.sub_apply, blockToPiLp] using
            (PiLp.norm_apply_le
              ((blockToPiLp (E := E) (p := p)) (xCbpg k - xCbpg (k + 1)))
              j)
        exact mul_le_mul_of_nonneg_left hcoord (le_of_lt (PosReal.coe_pos (σ⁻¹)))
  have hdrift :
      ‖gradient (fun z : E ↦ (((f∗) z).toReal)) (∑ i : Fin p, xCbpg (k + 1) i) -
          gradient (fun z : E ↦ (((f∗) z).toReal)) (∑ i : Fin p, xStage i)‖ ≤
        ((p : ℝ) / (σ : ℝ)) * ‖xCbpg k - xCbpg (k + 1)‖ := by
    have hdrift0 :=
      dualBlockMinimizationViewBlockGradientDriftLeExplicitOuterStep
        (σ := σ)
        (f := f)
        (g := g)
        (y0 := y0)
        (x := x)
        (y := y)
        (h_problem := h_problem)
        (h_trajectory := h_trajectory)
        (α0 := α0)
        (h_initial_level := h_initial_level)
        (R := R)
        (h_R := h_R)
        hblock
        y0Eff
        k
        j
    simpa [xStage, xCbpg] using hdrift0
  have hsum_bound :
      ‖hblock.toIsBlockProximalGradientProblem.gradient_mapping (σ⁻¹) j xStage‖ +
          ‖gradient (fun z : E ↦ (((f∗) z).toReal)) (∑ i : Fin p, xCbpg (k + 1) i) -
              gradient (fun z : E ↦ (((f∗) z).toReal)) (∑ i : Fin p, xStage i)‖ ≤
        (((σ⁻¹ : PosReal) : ℝ)) * ‖xCbpg k - xCbpg (k + 1)‖ +
          ((p : ℝ) / (σ : ℝ)) * ‖xCbpg k - xCbpg (k + 1)‖ := by
    exact add_le_add hstage hdrift
  -- Separate the stage-residual and smooth-drift contributions before recombining the explicit
  -- coefficient.
  calc
    ‖dualBlockMinimizationViewFinalResidual (σ := σ) (f := f) (g := g)
        (LfRaw := LfRaw) hblock y0Eff k j‖ ≤
      ‖hblock.toIsBlockProximalGradientProblem.gradient_mapping (σ⁻¹) j xStage‖ +
        ‖gradient (fun z : E ↦ (((f∗) z).toReal)) (∑ i : Fin p, xCbpg (k + 1) i) -
            gradient (fun z : E ↦ (((f∗) z).toReal)) (∑ i : Fin p, xStage i)‖ := by
      -- Unfold the theorem-local residual only at the final coordinatewise estimate.
      dsimp [dualBlockMinimizationViewFinalResidual, x0I, xCbpg, xStage]
      exact
        norm_add_le
          (hblock.toIsBlockProximalGradientProblem.gradient_mapping (σ⁻¹) j xStage)
          (gradient (fun z : E ↦ (((f∗) z).toReal)) (∑ i : Fin p, xCbpg (k + 1) i) -
            gradient (fun z : E ↦ (((f∗) z).toReal)) (∑ i : Fin p, xStage i))
    _ ≤
        ((((σ⁻¹ : PosReal) : ℝ)) * ‖xCbpg k - xCbpg (k + 1)‖ +
          ((p : ℝ) / (σ : ℝ)) * ‖xCbpg k - xCbpg (k + 1)‖) := hsum_bound
    _ =
        (((p : ℝ) / (σ : ℝ)) + (((σ⁻¹ : PosReal) : ℝ))) *
          ‖xCbpg k - xCbpg (k + 1)‖ := by
      ring

/-- Helper for Theorem 12.17 (`thm:12.17`): the theorem-local final residual has the explicit
square-norm bound needed by the displayed coefficient branch of the Chapter 11 certificate. -/
lemma dualBlockMinimizationViewFinalResidualNormSqLeExplicitOuterStep
    {LfRaw : NNReal}
    (hblock :
      BlockProximalGradientAssumptions
        (DualBlockMinimizationView.smoothTerm f)
        (fun i z ↦ ((g i)∗) (-z))
        (fun _ : Fin p ↦ fun w : Fin p → E ↦
          gradient (fun z : E ↦ (((f∗) z).toReal)) (∑ j : Fin p, w j))
        (unconstrained_problem_solutions (DualBlockMinimizationView.objective f g))
        (-EReal.toReal (q_opt(f, g)))
        LfRaw
        (fun _ : Fin p ↦ σ⁻¹))
    (y0Eff : effective_domain (DualBlockMinimizationView.regularizer g))
    (k : ℕ) :
    ‖dualBlockMinimizationViewFinalResidual (σ := σ) (f := f) (g := g)
        (LfRaw := LfRaw) hblock y0Eff k‖ ^ (2 : ℕ) ≤
      (p : ℝ) *
        ((((p : ℝ) / (σ : ℝ)) + (((σ⁻¹ : PosReal) : ℝ))) ^ (2 : ℕ)) *
        ‖cyclic_block_proximal_gradient_method
            hblock
            (hblock.interior_effective_domain_point y0Eff)
            k -
          cyclic_block_proximal_gradient_method
            hblock
            (hblock.interior_effective_domain_point y0Eff)
            (k + 1)‖ ^ (2 : ℕ) := by
  let x0I := hblock.interior_effective_domain_point y0Eff
  let xCbpg : ℕ → Fin p → E := fun m ↦
    cyclic_block_proximal_gradient_method hblock x0I m
  let r : Fin p → E :=
    dualBlockMinimizationViewFinalResidual
      (σ := σ)
      (f := f)
      (g := g)
      (LfRaw := LfRaw)
      hblock
      y0Eff
      k
  let toPiLp :=
    ContinuousLinearEquiv.symm
      (PiLp.continuousLinearEquiv (2 : ENNReal) ℝ (fun _ : Fin p ↦ E))
  let C : ℝ := ((p : ℝ) / (σ : ℝ)) + (((σ⁻¹ : PosReal) : ℝ))
  let s : ℝ := ‖xCbpg k - xCbpg (k + 1)‖
  have hraw :
      ‖r‖ ≤ ‖toPiLp r‖ := by
    -- Compare the raw residual norm with the canonical `PiLp` norm before summing the coordinate
    -- bounds.
    simpa [r, toPiLp] using
      rawAmbientNorm_le_toPiLpNorm (v := r)
  have hraw_sq :
      ‖r‖ ^ (2 : ℕ) ≤ ‖toPiLp r‖ ^ (2 : ℕ) := by
    have hnonneg : 0 ≤ ‖r‖ := by
      have hEq : ‖r‖ = ‖toPiLp r‖ := by
        simpa [toPiLp, blockToPiLp] using
          (PiLp.norm_seminormedAddCommGroupToPi
            (p := 2)
            (α := fun _ : Fin p ↦ E)
            r)
      rw [hEq]
      exact norm_nonneg _
    exact pow_le_pow_left₀ hnonneg hraw 2
  have hpilp_sq :
      ‖toPiLp r‖ ^ (2 : ℕ) =
        Finset.sum Finset.univ (fun j : Fin p ↦ ‖r j‖ ^ (2 : ℕ)) := by
    -- Expand the canonical `L²` norm as the sum of the squared coordinates.
    simpa [r, toPiLp] using
      (PiLp.norm_sq_eq_of_L2 (fun _ : Fin p ↦ E) (toPiLp r))
  have hcoord_sq :
      ∀ j : Fin p, ‖r j‖ ^ (2 : ℕ) ≤ (C * s) ^ (2 : ℕ) := by
    intro j
    exact
      pow_le_pow_left₀
        (norm_nonneg _)
        (dualBlockMinimizationViewFinalResidualCoordinateNormLeExplicitOuterStep
          (σ := σ)
          (f := f)
          (g := g)
          (y0 := y0)
          (x := x)
          (y := y)
          (h_problem := h_problem)
          (h_trajectory := h_trajectory)
          (α0 := α0)
          (h_initial_level := h_initial_level)
          (R := R)
          (h_R := h_R)
          hblock
          y0Eff
          k
          j)
        2
  have hsum :
      Finset.sum Finset.univ (fun j : Fin p ↦ ‖r j‖ ^ (2 : ℕ)) ≤
        Finset.sum Finset.univ (fun _ : Fin p ↦ (C * s) ^ (2 : ℕ)) := by
    -- Sum the uniform coordinatewise residual bound over all blocks.
    exact Finset.sum_le_sum fun j _ ↦ hcoord_sq j
  calc
    ‖r‖ ^ (2 : ℕ) ≤ ‖toPiLp r‖ ^ (2 : ℕ) := hraw_sq
    _ = Finset.sum Finset.univ (fun j : Fin p ↦ ‖r j‖ ^ (2 : ℕ)) := by
      exact hpilp_sq
    _ ≤ Finset.sum Finset.univ (fun _ : Fin p ↦ (C * s) ^ (2 : ℕ)) := hsum
    _ = (p : ℝ) * (C * s) ^ (2 : ℕ) := by
      simp [C, s, Finset.card_univ, mul_assoc, mul_left_comm, mul_comm]
    _ = (p : ℝ) * (C ^ (2 : ℕ)) * (s ^ (2 : ℕ)) := by
      rw [pow_two, pow_two]
      ring
    _ =
        (p : ℝ) *
          ((((p : ℝ) / (σ : ℝ)) + (((σ⁻¹ : PosReal) : ℝ))) ^ (2 : ℕ)) *
          ‖xCbpg k - xCbpg (k + 1)‖ ^ (2 : ℕ) := by
      rfl

/-- Helper for Theorem 12.17 (`thm:12.17`): after one full outer step, each coordinate of the
theorem-local final residual minus the current smooth gradient belongs to the Euclidean
subdifferential of the corresponding conjugate block term. -/
lemma dualBlockMinimizationViewFinalResidualCoordinate_mem_euclideanSubdifferential
    {LfRaw : NNReal}
    (hblock :
      BlockProximalGradientAssumptions
        (DualBlockMinimizationView.smoothTerm f)
        (fun i z ↦ ((g i)∗) (-z))
        (fun _ : Fin p ↦ fun w : Fin p → E ↦
          gradient (fun z : E ↦ (((f∗) z).toReal)) (∑ j : Fin p, w j))
        (unconstrained_problem_solutions (DualBlockMinimizationView.objective f g))
        (-EReal.toReal (q_opt(f, g)))
        LfRaw
        (fun _ : Fin p ↦ σ⁻¹))
    (y0Eff : effective_domain (DualBlockMinimizationView.regularizer g))
    (n : ℕ) (j : Fin p) :
    dualBlockMinimizationViewFinalResidual (σ := σ) (f := f) (g := g)
        (LfRaw := LfRaw) hblock y0Eff n j -
          gradient (fun z : E ↦ (((f∗) z).toReal))
            (∑ i : Fin p,
              cyclic_block_proximal_gradient_method
                hblock
                (hblock.interior_effective_domain_point y0Eff)
                (n + 1) i) ∈
      euclideanSubdifferential (fun z : E ↦ ((g j)∗) (-z))
        ((cyclic_block_proximal_gradient_method
            hblock
            (hblock.interior_effective_domain_point y0Eff)
            (n + 1)) j) := by
  let x0I := hblock.interior_effective_domain_point y0Eff
  let xCbpg : ℕ → Fin p → E := fun m ↦
    cyclic_block_proximal_gradient_method hblock x0I m
  let xStage : Fin p → E :=
    cyclic_block_proximal_gradient_inner_iterate hblock (xCbpg n) j.1
  let xNext : E :=
    cyclic_block_proximal_gradient_inner_iterate hblock (xCbpg n) (j.1 + 1) j
  have hsucc :
      cyclic_block_proximal_gradient_inner_iterate hblock (xCbpg n) (j.1 + 1) =
        block_coordinate_update
          xStage
          j
          (hblock.toIsBlockProximalGradientProblem.prox_point (σ⁻¹) j xStage - xStage j) := by
    -- The next inner stage is exactly the owner one-block prox update at block `j`.
    simpa [xStage] using
      cyclic_block_proximal_gradient_method_inner_succ hblock x0I n j.2
  have hprox :
      hblock.toIsBlockProximalGradientProblem.prox_point (σ⁻¹) j xStage = xNext := by
    -- Reading the active coordinate of the one-block update recovers the prox point itself.
    have hcoord := congrArg (fun z : Fin p → E ↦ z j) hsucc
    simpa [xNext, block_coordinate_update] using hcoord.symm
  have hprox_eq :
      prox[((((1 / (σ⁻¹) : PosReal) : EReal) • (fun z : E ↦ ((g j)∗) (-z))))]
          (xStage j -
            (1 / (σ⁻¹) : ℝ) •
              gradient (fun z : E ↦ (((f∗) z).toReal)) (∑ i : Fin p, xStage i)) =
        {xNext} := by
    -- The block prox owner already packages the updated coordinate as a singleton prox set.
    have hprox_eq' :=
      hblock.toIsBlockProximalGradientProblem.prox_point_eq_singleton (σ⁻¹) j xStage
    rw [hprox] at hprox_eq'
    simpa [xNext] using hprox_eq'
  have hscaled :=
    scaled_function_proper_closed_convex_of_pos
      (fun z : E ↦ ((g j)∗) (-z))
      (hblock.block_g_proper j)
      (hblock.block_g_closed j)
      (hblock.block_g_convex j)
      (1 / (σ⁻¹))
  have hprox_sub :
      InnerProductSpace.toDualMap ℝ E
          ((xStage j -
              (1 / (σ⁻¹) : ℝ) •
                gradient (fun z : E ↦ (((f∗) z).toReal)) (∑ i : Fin p, xStage i)) - xNext) ∈
        strongDualSubdifferential
          ((((1 / (σ⁻¹) : PosReal) : EReal) • (fun z : E ↦ ((g j)∗) (-z))))
          xNext := by
    -- Convert the singleton prox description into the standard subgradient certificate.
    exact
      (prox_eq_singleton_iff_toDualMap_sub_mem_strongDualSubdifferential
        ((((1 / (σ⁻¹) : PosReal) : EReal) • (fun z : E ↦ ((g j)∗) (-z))))
        hscaled.1
        hscaled.2.2
        (xStage j -
          (1 / (σ⁻¹) : ℝ) •
            gradient (fun z : E ↦ (((f∗) z).toReal)) (∑ i : Fin p, xStage i))
        xNext).mp hprox_eq
  have hscaled_sub :
      (InnerProductSpace.toDualMap ℝ E
          (hblock.toIsBlockProximalGradientProblem.gradient_mapping (σ⁻¹) j xStage -
            gradient (fun z : E ↦ (((f∗) z).toReal)) (∑ i : Fin p, xStage i)) :
            Module.Dual ℝ E) ∈
        subdifferential (fun z : E ↦ ((g j)∗) (-z)) xNext := by
    let gradStage : E := gradient (fun z : E ↦ (((f∗) z).toReal)) (∑ i : Fin p, xStage i)
    let residualVec : E :=
      hblock.toIsBlockProximalGradientProblem.gradient_mapping (σ⁻¹) j xStage - gradStage
    have hσinv_pos : 0 < (1 / (σ⁻¹) : ℝ) := by
      exact one_div_pos.mpr (PosReal.coe_pos (σ⁻¹))
    have hσinv_ne : (1 / (σ⁻¹) : ℝ) ≠ 0 := by
      exact one_div_ne_zero (PosReal.coe_pos (σ⁻¹)).ne'
    have hσraw_ne : (((σ⁻¹ : PosReal) : ℝ)) ≠ 0 := by
      exact ne_of_gt (PosReal.coe_pos (σ⁻¹))
    have hdisplacement :
        xStage j - xNext =
          (1 / (σ⁻¹) : ℝ) •
            hblock.toIsBlockProximalGradientProblem.gradient_mapping (σ⁻¹) j xStage := by
      calc
        xStage j - xNext =
            (1 / (σ⁻¹) : ℝ) • ((((σ⁻¹ : PosReal) : ℝ)) • (xStage j - xNext)) := by
              rw [smul_smul, one_div, inv_mul_cancel₀ hσraw_ne, one_smul]
        _ =
            (1 / (σ⁻¹) : ℝ) •
              hblock.toIsBlockProximalGradientProblem.gradient_mapping (σ⁻¹) j xStage := by
                rw [hblock.toIsBlockProximalGradientProblem.gradient_mapping_def (σ⁻¹) xStage j, hprox]
    have hscaled_vec :
        xStage j - (1 / (σ⁻¹) : ℝ) • gradStage - xNext =
          (1 / (σ⁻¹) : ℝ) •
            residualVec := by
      calc
        xStage j - (1 / (σ⁻¹) : ℝ) • gradStage - xNext =
            (xStage j - xNext) - (1 / (σ⁻¹) : ℝ) • gradStage := by
              abel
        _ =
            (1 / (σ⁻¹) : ℝ) •
              hblock.toIsBlockProximalGradientProblem.gradient_mapping (σ⁻¹) j xStage -
                (1 / (σ⁻¹) : ℝ) • gradStage := by
                  rw [hdisplacement]
        _ =
            (1 / (σ⁻¹) : ℝ) • residualVec := by
                rw [smul_sub]
    have hscaled_dual :
        (InnerProductSpace.toDualMap ℝ E
          (xStage j - (1 / (σ⁻¹) : ℝ) • gradStage - xNext) : Module.Dual ℝ E) =
          (InnerProductSpace.toDualMap ℝ E ((1 / (σ⁻¹) : ℝ) • residualVec) :
            Module.Dual ℝ E) := by
      exact congrArg (fun v : E ↦ (InnerProductSpace.toDualMap ℝ E v : Module.Dual ℝ E)) hscaled_vec
    have hsub_scaled :
        (InnerProductSpace.toDualMap ℝ E
          ((1 / (σ⁻¹) : ℝ) • residualVec) :
            Module.Dual ℝ E) ∈
          subdifferential
            ((((1 / (σ⁻¹) : PosReal) : EReal) • (fun z : E ↦ ((g j)∗) (-z))))
            xNext := by
      -- Rewrite the prox-generated strong-dual certificate into the scaled residual form expected
      -- by the positive-scaling transport lemma.
      rw [mem_strongDualSubdifferential] at hprox_sub
      rw [← hscaled_dual]
      exact hprox_sub
    have htransport :=
      (mem_subdifferential_pos_real_mul_iff
        (fun z : E ↦ ((g j)∗) (-z))
        (1 / (σ⁻¹) : ℝ)
        hσinv_pos
        xNext
        (InnerProductSpace.toDualMap ℝ E
          ((1 / (σ⁻¹) : ℝ) • residualVec))).mp
        hsub_scaled
    have hdescale_dual :
        ((1 / (σ⁻¹) : ℝ)⁻¹) •
            (InnerProductSpace.toDualMap ℝ E ((1 / (σ⁻¹) : ℝ) • residualVec) :
              Module.Dual ℝ E) =
          (InnerProductSpace.toDualMap ℝ E residualVec : Module.Dual ℝ E) := by
      have hscalar :
          ((1 / (σ⁻¹) : ℝ)⁻¹) * (1 / (σ⁻¹) : ℝ) = 1 := by
        exact inv_mul_cancel₀ hσinv_ne
      calc
        ((1 / (σ⁻¹) : ℝ)⁻¹) •
            (InnerProductSpace.toDualMap ℝ E ((1 / (σ⁻¹) : ℝ) • residualVec) :
              Module.Dual ℝ E) =
          (InnerProductSpace.toDualMap ℝ E
            (((1 / (σ⁻¹) : ℝ)⁻¹) • ((1 / (σ⁻¹) : ℝ) • residualVec)) :
              Module.Dual ℝ E) := by
                ext z
                simp [InnerProductSpace.toDual_apply_eq_toDualMap_apply, inner_smul_left]
        _ = (InnerProductSpace.toDualMap ℝ E residualVec : Module.Dual ℝ E) := by
              rw [smul_smul, hscalar, one_smul]
    exact hdescale_dual ▸ htransport
  have hstage_mem :
      hblock.toIsBlockProximalGradientProblem.gradient_mapping (σ⁻¹) j xStage -
          gradient (fun z : E ↦ (((f∗) z).toReal)) (∑ i : Fin p, xStage i) ∈
        euclideanSubdifferential (fun z : E ↦ ((g j)∗) (-z)) xNext := by
    -- Pass from the owner dual subgradient to the Euclidean/vector-side subgradient.
    rw [mem_euclideanSubdifferential_iff, mem_strongDualSubdifferential]
    simpa [InnerProductSpace.toDual_apply_eq_toDualMap_apply] using hscaled_sub
  have hafter_eq :
      xNext = xCbpg (n + 1) j := by
    -- The updated coordinate persists until the end of the full outer cycle.
    simpa [xNext, xCbpg] using
      cbpg_auxiliary_iterate_apply_eq_outer_successor_of_lt
        hblock
        y0Eff
        n
        (j.1 + 1)
        j
        (Nat.lt_succ_self j.1)
        (Nat.succ_le_of_lt j.2)
  have hresidual_eq :
      dualBlockMinimizationViewFinalResidual (σ := σ) (f := f) (g := g)
          (LfRaw := LfRaw) hblock y0Eff n j -
            gradient (fun z : E ↦ (((f∗) z).toReal))
              (∑ i : Fin p, xCbpg (n + 1) i) =
        hblock.toIsBlockProximalGradientProblem.gradient_mapping (σ⁻¹) j xStage -
          gradient (fun z : E ↦ (((f∗) z).toReal)) (∑ i : Fin p, xStage i) := by
    -- After subtracting the final smooth gradient, only the stage residual remains.
    dsimp [dualBlockMinimizationViewFinalResidual, xCbpg, xStage, x0I]
    abel
  have hstage_mem' :
      hblock.toIsBlockProximalGradientProblem.gradient_mapping (σ⁻¹) j xStage -
          gradient (fun z : E ↦ (((f∗) z).toReal)) (∑ i : Fin p, xStage i) ∈
        euclideanSubdifferential (fun z : E ↦ ((g j)∗) (-z)) (xCbpg (n + 1) j) := by
    simpa [hafter_eq] using hstage_mem
  rw [hresidual_eq]
  exact hstage_mem'

/-- Helper for Theorem 12.17 (`thm:12.17`): once the theorem-local CBPG outer sequence is known
to stay inside the initial radius-controlled sublevel, the only remaining Chapter 11 input is the
explicit objective-gap-square certificate with displayed smoothness coefficient `Lf = p / σ`. -/
lemma dualBlockMinimizationViewObjectiveGapLeResidualMulDist
    {LfRaw : NNReal}
    (hblock :
      BlockProximalGradientAssumptions
        (DualBlockMinimizationView.smoothTerm f)
        (fun i z ↦ ((g i)∗) (-z))
        (fun _ : Fin p ↦ fun w : Fin p → E ↦
          gradient (fun z : E ↦ (((f∗) z).toReal)) (∑ j : Fin p, w j))
        (unconstrained_problem_solutions (DualBlockMinimizationView.objective f g))
        (-EReal.toReal (q_opt(f, g)))
        LfRaw
        (fun _ : Fin p ↦ σ⁻¹))
    (y0Eff : effective_domain (DualBlockMinimizationView.regularizer g))
    (n : ℕ)
    {wStar : Fin p → E}
    (hwStar : wStar ∈ unconstrained_problem_solutions (DualBlockMinimizationView.objective f g)) :
    let x0I := hblock.interior_effective_domain_point y0Eff
    let xCbpg : ℕ → Fin p → E := fun m ↦
      cyclic_block_proximal_gradient_method hblock x0I m
    let r : Fin p → E :=
      dualBlockMinimizationViewFinalResidual
        (σ := σ)
        (f := f)
        (g := g)
        (LfRaw := LfRaw)
        hblock
        y0Eff
        n
    let toPiLp :=
      ContinuousLinearEquiv.symm
        (PiLp.continuousLinearEquiv (2 : ENNReal) ℝ (fun _ : Fin p ↦ E))
    (DualBlockMinimizationView.objective f g (xCbpg (n + 1))).toReal -
        (-EReal.toReal (q_opt(f, g))) ≤
      ‖r‖ * dist (xCbpg (n + 1)) wStar := by
  let x0I := hblock.interior_effective_domain_point y0Eff
  let xCbpg : ℕ → Fin p → E := fun m ↦
    cyclic_block_proximal_gradient_method hblock x0I m
  let r : Fin p → E :=
    dualBlockMinimizationViewFinalResidual
      (σ := σ)
      (f := f)
      (g := g)
      (LfRaw := LfRaw)
      hblock
      y0Eff
      n
  let toPiLp :=
    ContinuousLinearEquiv.symm
      (PiLp.continuousLinearEquiv (2 : ENNReal) ℝ (fun _ : Fin p ↦ E))
  let φ : E → ℝ := fun z ↦ ((f∗) z).toReal
  let hRBPG :
      RandomizedBlockProximalGradientAssumptions
        (DualBlockMinimizationView.smoothTerm f)
        (fun i z ↦ ((g i)∗) (-z))
        (fun _ : Fin p ↦ fun w : Fin p → E ↦
          gradient (fun z : E ↦ (((f∗) z).toReal)) (∑ j : Fin p, w j))
        (unconstrained_problem_solutions (DualBlockMinimizationView.objective f g))
        (-EReal.toReal (q_opt(f, g)))
        (fun _ : Fin p ↦ σ⁻¹) :=
    hblock.toRandomizedBlockProximalGradientAssumptions
      (dualBlockMinimizationViewSmoothTermConvex
        (σ := σ)
        (f := f)
        (g := g)
        (y0 := y0)
        (x := x)
        (y := y)
        (h_problem := h_problem)
        (h_trajectory := h_trajectory)
        (α0 := α0)
        (h_initial_level := h_initial_level)
        (R := R)
        (h_R := h_R))
  have hxkp1_g :
      xCbpg (n + 1) ∈ effective_domain (DualBlockMinimizationView.regularizer g) := by
    -- The theorem-local CBPG outer iterates stay feasible for the blockwise conjugate regularizer.
    simpa [xCbpg] using
      cbpg_auxiliary_iterate_mem_effective_domain hblock y0Eff (n + 1) 0 (Nat.zero_le p)
  have hwStar_g :
      wStar ∈ effective_domain (DualBlockMinimizationView.regularizer g) := by
    -- Any minimizer of the minimization view has finite blockwise regularizer value.
    simpa using rbpgMemEffectiveDomain_of_mem_optimal_set hRBPG hwStar
  have hobj_xkp1 :
      DualBlockMinimizationView.objective f g (xCbpg (n + 1)) =
        ((((DualBlockMinimizationView.smoothTerm f (xCbpg (n + 1))).toReal +
            ∑ j : Fin p, (((g j)∗) (-(xCbpg (n + 1) j))).toReal : ℝ)) : EReal) := by
    simpa [DualBlockMinimizationView.objective, DualBlockMinimizationView.regularizer] using
      rbpgObjective_eq_real_sum_of_mem_effective_domain hRBPG hxkp1_g
  have hobj_star :
      DualBlockMinimizationView.objective f g wStar =
        ((((DualBlockMinimizationView.smoothTerm f wStar).toReal +
            ∑ j : Fin p, (((g j)∗) (-wStar j)).toReal : ℝ)) : EReal) := by
    simpa [DualBlockMinimizationView.objective, DualBlockMinimizationView.regularizer] using
      rbpgObjective_eq_real_sum_of_mem_effective_domain hRBPG hwStar_g
  have hopt :
      DualBlockMinimizationView.objective f g wStar =
        (((-EReal.toReal (q_opt(f, g)) : ℝ)) : EReal) := by
    simpa [DualBlockMinimizationView.objective, DualBlockMinimizationView.regularizer] using
      rbpgObjective_eq_optimal_value_of_mem_optimal_set hRBPG hwStar
  have hsum_xkp1 :
      (DualBlockMinimizationView.objective f g (xCbpg (n + 1))).toReal =
        (DualBlockMinimizationView.smoothTerm f (xCbpg (n + 1))).toReal +
          ∑ j : Fin p, (((g j)∗) (-(xCbpg (n + 1) j))).toReal := by
    simpa using congrArg EReal.toReal hobj_xkp1
  have hsum_star :
      (DualBlockMinimizationView.smoothTerm f wStar).toReal +
          ∑ j : Fin p, (((g j)∗) (-wStar j)).toReal =
        -EReal.toReal (q_opt(f, g)) := by
    have hstar_eq :
        ((((DualBlockMinimizationView.smoothTerm f wStar).toReal +
              ∑ j : Fin p, (((g j)∗) (-wStar j)).toReal : ℝ)) : EReal) =
          (((-EReal.toReal (q_opt(f, g)) : ℝ)) : EReal) := by
      exact hobj_star.symm.trans hopt
    simpa using congrArg EReal.toReal hstar_eq
  have hconj_convex : is_convex_function (f∗) := by
    simpa using
      dual_based_proximal_gradient_dual_F_primal_convex
        (f := f)
        (A := (LinearMap.id : E →ₗ[ℝ] E))
  have hconj_finite :
      ∀ z : E, (f∗) z ≠ ⊥ ∧ (f∗) z < ⊤ := by
    intro z
    simpa using
      dual_based_proximal_gradient_dual_F_primal_finite_valued
        (σ := σ)
        (f := f)
        (A := (LinearMap.id : E →ₗ[ℝ] E))
        h_problem.toIsProperExtendedRealFunction
        h_problem.f_closed
        h_problem.f_strongly_convex
        z
  have hφ_convex : ConvexOn ℝ (effective_domain (f∗)) φ := by
    exact
      convexOn_toReal_of_is_convex_function
        hconj_convex
        (fun z _ ↦ (hconj_finite z).1)
  let s : E := ∑ i : Fin p, xCbpg (n + 1) i
  let sStar : E := ∑ i : Fin p, wStar i
  have hs_mem : s ∈ effective_domain (f∗) := by
    exact mem_effective_domain.mpr (hconj_finite s).2
  have hsStar_mem : sStar ∈ effective_domain (f∗) := by
    exact mem_effective_domain.mpr (hconj_finite sStar).2
  have hdiffAt : DifferentiableAt ℝ φ s := by
    exact
      (conjugate_function_primal_is_l_smooth_on_of_proper_closed_strongConvexOn
        (σ := σ)
        (f := f)
        h_problem.toIsProperExtendedRealFunction
        h_problem.f_closed
        h_problem.f_strongly_convex).1
        s
        (by simpa [s] using hs_mem)
  have hsupport :
      φ s - φ sStar ≤ inner ℝ (gradient φ s) (s - sStar) := by
    let line : ℝ →ᵃ[ℝ] E := AffineMap.lineMap s sStar
    let ψ : ℝ → ℝ := fun t ↦ φ (line t)
    have hψ_convex :
        ConvexOn ℝ (line ⁻¹' effective_domain (f∗)) ψ := by
      simpa [ψ, line] using hφ_convex.comp_affineMap line
    have hψ_zero :
        (0 : ℝ) ∈ line ⁻¹' effective_domain (f∗) := by
      simpa [line] using hs_mem
    have hψ_one :
        (1 : ℝ) ∈ line ⁻¹' effective_domain (f∗) := by
      simpa [line] using hsStar_mem
    have hψ_deriv :
        HasDerivAt ψ (inner ℝ (gradient φ s) (sStar - s)) 0 := by
      have hbase :
          HasFDerivAt
            φ
            (fderiv ℝ φ s)
            s := by
        simpa [φ, s] using hdiffAt.hasFDerivAt
      have hline :
          HasDerivAt line (sStar - s) 0 := by
        simpa [line] using
          (show HasDerivAt (AffineMap.lineMap s sStar) (sStar - s) (0 : ℝ) from
            AffineMap.hasDerivAt_lineMap)
      have hcomp :
          HasDerivAt ψ
            (fderiv ℝ φ s (sStar - s))
            0 := by
        have hbase0 :
            HasFDerivAt φ (fderiv ℝ φ s) (line 0) := by
          simpa [line] using hbase
        simpa [ψ, line] using HasFDerivAt.comp_hasDerivAt (x := 0) hbase0 hline
      have hgrad :
          fderiv ℝ φ s (sStar - s) = inner ℝ (gradient φ s) (sStar - s) := by
        simpa [φ] using
          (show
              fderiv ℝ φ s (sStar - s) = inner ℝ (gradient φ s) (sStar - s)
            from HasGradientAt.fderiv_apply hdiffAt.hasGradientAt)
      simpa [hgrad] using hcomp
    have hsecant :
        inner ℝ (gradient φ s) (sStar - s) ≤ slope ψ 0 1 := by
      exact hψ_convex.le_slope_of_hasDerivAt hψ_zero hψ_one zero_lt_one hψ_deriv
    have hsecant' :
        inner ℝ (gradient φ s) (sStar - s) ≤ φ sStar - φ s := by
      simpa [ψ, line, slope] using hsecant
    have hflip : s - sStar = -(sStar - s) := by
      abel
    calc
      φ s - φ sStar ≤ -inner ℝ (gradient φ s) (sStar - s) := by
        linarith [hsecant']
      _ = inner ℝ (gradient φ s) (s - sStar) := by
        rw [hflip, inner_neg_right]
  have hsupport_f :
      (DualBlockMinimizationView.smoothTerm f (xCbpg (n + 1))).toReal -
          (DualBlockMinimizationView.smoothTerm f wStar).toReal ≤
        ∑ i : Fin p,
          inner ℝ
            (gradient (fun z : E ↦ (((f∗) z).toReal)) s)
            (xCbpg (n + 1) i - wStar i) := by
    have hinner_sum :
        inner ℝ (gradient φ s) (s - sStar) =
          ∑ i : Fin p,
            inner ℝ
              (gradient φ s)
              (xCbpg (n + 1) i - wStar i) := by
      calc
        inner ℝ (gradient φ s) (s - sStar) =
            inner ℝ
              (gradient φ s)
              (∑ i : Fin p, (xCbpg (n + 1) i - wStar i)) := by
          simp [s, sStar, Finset.sum_sub_distrib]
        _ = ∑ i : Fin p, inner ℝ (gradient φ s) (xCbpg (n + 1) i - wStar i) := by
          simpa using
            (inner_sum
              Finset.univ
              (fun i : Fin p ↦ xCbpg (n + 1) i - wStar i)
              (gradient φ s))
    rw [DualBlockMinimizationView.smoothTerm_apply, DualBlockMinimizationView.smoothTerm_apply]
    rw [hinner_sum] at hsupport
    simpa [φ, s, sStar] using hsupport
  have hblock_gap :
      ∀ j : Fin p,
        (((g j)∗) (-(xCbpg (n + 1) j))).toReal - (((g j)∗) (-wStar j)).toReal ≤
          inner ℝ
            (r j -
              gradient (fun z : E ↦ (((f∗) z).toReal)) (∑ i : Fin p, xCbpg (n + 1) i))
            (xCbpg (n + 1) j - wStar j) := by
    intro j
    have hxkp1j :
        xCbpg (n + 1) j ∈ effective_domain (fun z : E ↦ ((g j)∗) (-z)) := by
      exact
        block_mem_effective_domain_of_mem_separableSum_effective_domain
          (fun i z ↦ ((g i)∗) (-z))
          hblock.block_g_proper
          hxkp1_g
          j
    have hxStarj :
        wStar j ∈ effective_domain (fun z : E ↦ ((g j)∗) (-z)) := by
      exact
        block_mem_effective_domain_of_mem_separableSum_effective_domain
          (fun i z ↦ ((g i)∗) (-z))
          hblock.block_g_proper
          hwStar_g
          j
    have hmem :
        r j -
            gradient (fun z : E ↦ (((f∗) z).toReal)) (∑ i : Fin p, xCbpg (n + 1) i) ∈
          euclideanSubdifferential (fun z : E ↦ ((g j)∗) (-z)) (xCbpg (n + 1) j) := by
      simpa [r, xCbpg] using
        dualBlockMinimizationViewFinalResidualCoordinate_mem_euclideanSubdifferential
          (σ := σ)
          (f := f)
          (g := g)
          (y0 := y0)
          (x := x)
          (y := y)
          (h_problem := h_problem)
          (h_trajectory := h_trajectory)
          (α0 := α0)
          (h_initial_level := h_initial_level)
          (R := R)
          (h_R := h_R)
          hblock
          y0Eff
          n
          j
    have hsub :
        (InnerProductSpace.toDualMap ℝ E
            (r j -
              gradient (fun z : E ↦ (((f∗) z).toReal)) (∑ i : Fin p, xCbpg (n + 1) i)))
            (wStar j - xCbpg (n + 1) j) ≤
          (((g j)∗) (-wStar j)).toReal - (((g j)∗) (-(xCbpg (n + 1) j))).toReal := by
      rw [mem_euclideanSubdifferential_iff, mem_strongDualSubdifferential] at hmem
      exact
        subgradient_eval_le_toReal_sub
          (fun z : E ↦ ((g j)∗) (-z))
          (xCbpg (n + 1) j)
          (wStar j)
          (fun z hz ↦ (hblock.block_g_proper j).ne_bot z)
          hxkp1j
          hxStarj
          (by simpa [InnerProductSpace.toDual_apply_eq_toDualMap_apply] using hmem)
    have hflip :
        wStar j - xCbpg (n + 1) j = -(xCbpg (n + 1) j - wStar j) := by
      abel
    calc
      (((g j)∗) (-(xCbpg (n + 1) j))).toReal - (((g j)∗) (-wStar j)).toReal ≤
          -((InnerProductSpace.toDualMap ℝ E
              (r j -
                gradient (fun z : E ↦ (((f∗) z).toReal)) (∑ i : Fin p, xCbpg (n + 1) i)))
              (wStar j - xCbpg (n + 1) j)) := by
            linarith [hsub]
      _ =
          inner ℝ
            (r j -
              gradient (fun z : E ↦ (((f∗) z).toReal)) (∑ i : Fin p, xCbpg (n + 1) i))
            (xCbpg (n + 1) j - wStar j) := by
          rw [InnerProductSpace.toDualMap_apply_apply, hflip, inner_neg_right, neg_neg]
  have hsupport_g :
      (∑ j : Fin p, ((((g j)∗) (-(xCbpg (n + 1) j))).toReal - (((g j)∗) (-wStar j)).toReal)) ≤
        ∑ j : Fin p,
          inner ℝ
            (r j -
              gradient (fun z : E ↦ (((f∗) z).toReal)) (∑ i : Fin p, xCbpg (n + 1) i))
            (xCbpg (n + 1) j - wStar j) := by
    exact Finset.sum_le_sum fun j _ ↦ hblock_gap j
  have hsum_residual :
      (∑ i : Fin p,
          inner ℝ
            (gradient (fun z : E ↦ (((f∗) z).toReal)) (∑ j : Fin p, xCbpg (n + 1) j))
            (xCbpg (n + 1) i - wStar i)) +
          (∑ j : Fin p,
            inner ℝ
              (r j -
                gradient (fun z : E ↦ (((f∗) z).toReal)) (∑ i : Fin p, xCbpg (n + 1) i))
              (xCbpg (n + 1) j - wStar j)) =
        ∑ j : Fin p, inner ℝ (r j) (xCbpg (n + 1) j - wStar j) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro j hj
    rw [inner_sub_left]
    ring
  have hgap_sum :
      (DualBlockMinimizationView.objective f g (xCbpg (n + 1))).toReal -
          (-EReal.toReal (q_opt(f, g))) =
        (DualBlockMinimizationView.smoothTerm f (xCbpg (n + 1))).toReal -
            (DualBlockMinimizationView.smoothTerm f wStar).toReal +
          ∑ j : Fin p,
            ((((g j)∗) (-(xCbpg (n + 1) j))).toReal - (((g j)∗) (-wStar j)).toReal) := by
    calc
      (DualBlockMinimizationView.objective f g (xCbpg (n + 1))).toReal -
          (-EReal.toReal (q_opt(f, g))) =
        (DualBlockMinimizationView.objective f g (xCbpg (n + 1))).toReal -
          ((DualBlockMinimizationView.smoothTerm f wStar).toReal +
            ∑ j : Fin p, (((g j)∗) (-wStar j)).toReal) := by
          rw [hsum_star]
      _ =
        ((DualBlockMinimizationView.smoothTerm f (xCbpg (n + 1))).toReal +
            ∑ j : Fin p, (((g j)∗) (-(xCbpg (n + 1) j))).toReal) -
          ((DualBlockMinimizationView.smoothTerm f wStar).toReal +
            ∑ j : Fin p, (((g j)∗) (-wStar j)).toReal) := by
          rw [hsum_xkp1]
      _ =
        ((DualBlockMinimizationView.smoothTerm f (xCbpg (n + 1))).toReal -
            (DualBlockMinimizationView.smoothTerm f wStar).toReal) +
          ((∑ j : Fin p, (((g j)∗) (-(xCbpg (n + 1) j))).toReal) -
            (∑ j : Fin p, (((g j)∗) (-wStar j)).toReal)) := by
          ring
      _ =
        (DualBlockMinimizationView.smoothTerm f (xCbpg (n + 1))).toReal -
            (DualBlockMinimizationView.smoothTerm f wStar).toReal +
          ∑ j : Fin p,
            ((((g j)∗) (-(xCbpg (n + 1) j))).toReal - (((g j)∗) (-wStar j)).toReal) := by
          rw [Finset.sum_sub_distrib]
  have hsum_gap :
      (DualBlockMinimizationView.objective f g (xCbpg (n + 1))).toReal -
          (-EReal.toReal (q_opt(f, g))) ≤
        ∑ j : Fin p, inner ℝ (r j) (xCbpg (n + 1) j - wStar j) := by
    rw [hgap_sum]
    have hpair :
        (DualBlockMinimizationView.smoothTerm f (xCbpg (n + 1))).toReal -
            (DualBlockMinimizationView.smoothTerm f wStar).toReal +
          ∑ j : Fin p,
            ((((g j)∗) (-(xCbpg (n + 1) j))).toReal - (((g j)∗) (-wStar j)).toReal) ≤
        (∑ i : Fin p,
            inner ℝ
              (gradient (fun z : E ↦ (((f∗) z).toReal)) (∑ j : Fin p, xCbpg (n + 1) j))
              (xCbpg (n + 1) i - wStar i)) +
          (∑ j : Fin p,
            inner ℝ
              (r j -
                gradient (fun z : E ↦ (((f∗) z).toReal)) (∑ i : Fin p, xCbpg (n + 1) i))
              (xCbpg (n + 1) j - wStar j)) := by
      linarith [hsupport_f, hsupport_g]
    calc
      (DualBlockMinimizationView.smoothTerm f (xCbpg (n + 1))).toReal -
          (DualBlockMinimizationView.smoothTerm f wStar).toReal +
        ∑ j : Fin p,
          ((((g j)∗) (-(xCbpg (n + 1) j))).toReal - (((g j)∗) (-wStar j)).toReal) ≤
          (∑ i : Fin p,
              inner ℝ
                (gradient (fun z : E ↦ (((f∗) z).toReal)) (∑ j : Fin p, xCbpg (n + 1) j))
                (xCbpg (n + 1) i - wStar i)) +
            (∑ j : Fin p,
              inner ℝ
                (r j -
                  gradient (fun z : E ↦ (((f∗) z).toReal)) (∑ i : Fin p, xCbpg (n + 1) i))
                (xCbpg (n + 1) j - wStar j)) := hpair
      _ = ∑ j : Fin p, inner ℝ (r j) (xCbpg (n + 1) j - wStar j) := hsum_residual
  have hinner_residual :
      ∑ j : Fin p, inner ℝ (r j) (xCbpg (n + 1) j - wStar j) =
        inner ℝ (toPiLp r) (toPiLp (xCbpg (n + 1) - wStar)) := by
    symm
    simpa [toPiLp] using
      (PiLp.inner_apply
        (WithLp.toLp 2 r)
        (WithLp.toLp 2 (xCbpg (n + 1) - wStar)))
  have hcs :
      inner ℝ (toPiLp r) (toPiLp (xCbpg (n + 1) - wStar)) ≤
        ‖toPiLp r‖ * ‖toPiLp (xCbpg (n + 1) - wStar)‖ := by
    exact real_inner_le_norm _ _
  have hnorm_residual :
      ‖toPiLp r‖ = ‖r‖ := by
    simpa [toPiLp] using
      (rawAmbientNorm_eq_toPiLpNorm (E := E) (p := p) (v := r)).symm
  have hnorm_dist :
      ‖toPiLp (xCbpg (n + 1) - wStar)‖ = dist (xCbpg (n + 1)) wStar := by
    have hdist :
        dist (xCbpg (n + 1)) wStar = ‖xCbpg (n + 1) - wStar‖ := by
      simpa using dist_eq_norm (xCbpg (n + 1)) wStar
    rw [hdist]
    simpa [toPiLp] using
      (rawAmbientNorm_eq_toPiLpNorm
        (E := E)
        (p := p)
        (v := xCbpg (n + 1) - wStar)).symm
  simpa [xCbpg, r, toPiLp] using
    (calc
      (DualBlockMinimizationView.objective f g (xCbpg (n + 1))).toReal -
          (-EReal.toReal (q_opt(f, g))) ≤
        ∑ j : Fin p, inner ℝ (r j) (xCbpg (n + 1) j - wStar j) := hsum_gap
      _ = inner ℝ (toPiLp r) (toPiLp (xCbpg (n + 1) - wStar)) := hinner_residual
      _ ≤ ‖toPiLp r‖ * ‖toPiLp (xCbpg (n + 1) - wStar)‖ := hcs
      _ = ‖r‖ * dist (xCbpg (n + 1)) wStar := by
        rw [hnorm_residual, hnorm_dist])

/-- Helper for Theorem 12.17 (`thm:12.17`): once the theorem-local CBPG outer sequence is known
to stay inside the initial radius-controlled sublevel, the only remaining Chapter 11 input is the
explicit objective-gap-square certificate with displayed smoothness coefficient `Lf = p / σ`. -/
lemma dualBlockMinimizationViewObjectiveGapSqBoundExplicitLf
    {LfRaw : NNReal}
    (hblock :
      BlockProximalGradientAssumptions
        (DualBlockMinimizationView.smoothTerm f)
        (fun i z ↦ ((g i)∗) (-z))
        (fun _ : Fin p ↦ fun w : Fin p → E ↦
          gradient (fun z : E ↦ (((f∗) z).toReal)) (∑ j : Fin p, w j))
        (unconstrained_problem_solutions (DualBlockMinimizationView.objective f g))
        (-EReal.toReal (q_opt(f, g)))
        LfRaw
        (fun _ : Fin p ↦ σ⁻¹))
    (y0Eff : effective_domain (DualBlockMinimizationView.regularizer g))
    (hradius :
      ∀ n : ℕ,
        Metric.infDist
            (cyclic_block_proximal_gradient_method
              hblock
              (hblock.interior_effective_domain_point y0Eff)
              (n + 1))
            (unconstrained_problem_solutions (DualBlockMinimizationView.objective f g)) ≤
          R)
    (n : ℕ) :
    cbpgObjectiveGapSqBound
      (Real.toNNReal ((p : ℝ) / (σ : ℝ)))
      (fun _ : Fin p ↦ σ⁻¹)
      R
      (DualBlockMinimizationView.objective f g)
      (fun m ↦
        cyclic_block_proximal_gradient_method
          hblock
          (hblock.interior_effective_domain_point y0Eff)
          m)
      (-EReal.toReal (q_opt(f, g)))
      n := by
  -- Route correction: the explicit residual-norm branch with coefficient `(p / σ) + σ⁻¹` is now
  -- isolated above. What remains is the coefficient-free convex-analysis bridge
  -- `objective gap ≤ ‖final residual‖ * infDist`, after which `hradius` will close the textbook
  -- Chapter 11 certificate.
  let x0I := hblock.interior_effective_domain_point y0Eff
  let xCbpg : ℕ → Fin p → E := fun m ↦
    cyclic_block_proximal_gradient_method hblock x0I m
  let r : Fin p → E :=
    dualBlockMinimizationViewFinalResidual
      (σ := σ)
      (f := f)
      (g := g)
      (LfRaw := LfRaw)
      hblock
      y0Eff
      n
  let toPiLp :=
    ContinuousLinearEquiv.symm
      (PiLp.continuousLinearEquiv (2 : ENNReal) ℝ (fun _ : Fin p ↦ E))
  let hRBPG :
      RandomizedBlockProximalGradientAssumptions
        (DualBlockMinimizationView.smoothTerm f)
        (fun i z ↦ ((g i)∗) (-z))
        (fun _ : Fin p ↦ fun w : Fin p → E ↦
          gradient (fun z : E ↦ (((f∗) z).toReal)) (∑ j : Fin p, w j))
        (unconstrained_problem_solutions (DualBlockMinimizationView.objective f g))
        (-EReal.toReal (q_opt(f, g)))
        (fun _ : Fin p ↦ σ⁻¹) :=
    hblock.toRandomizedBlockProximalGradientAssumptions
      (dualBlockMinimizationViewSmoothTermConvex
        (σ := σ)
        (f := f)
        (g := g)
        (y0 := y0)
        (x := x)
        (y := y)
        (h_problem := h_problem)
        (h_trajectory := h_trajectory)
        (α0 := α0)
        (h_initial_level := h_initial_level)
        (R := R)
        (h_R := h_R))
  have hxkp1_g :
      xCbpg (n + 1) ∈ effective_domain (DualBlockMinimizationView.regularizer g) := by
    -- The theorem-local CBPG outer iterates stay feasible for the blockwise conjugate regularizer.
    simpa [xCbpg] using
      cbpg_auxiliary_iterate_mem_effective_domain hblock y0Eff (n + 1) 0 (Nat.zero_le p)
  have hgap_dist :
      ∀ {wStar : Fin p → E},
        wStar ∈ unconstrained_problem_solutions (DualBlockMinimizationView.objective f g) →
          (DualBlockMinimizationView.objective f g (xCbpg (n + 1))).toReal -
              (-EReal.toReal (q_opt(f, g))) ≤
            ‖r‖ * dist (xCbpg (n + 1)) wStar := by
    intro wStar hwStar
    simpa [r, xCbpg] using
      dualBlockMinimizationViewObjectiveGapLeResidualMulDist
        (σ := σ)
        (f := f)
        (g := g)
        (y0 := y0)
        (x := x)
        (y := y)
        (h_problem := h_problem)
        (h_trajectory := h_trajectory)
        (α0 := α0)
        (h_initial_level := h_initial_level)
        (R := R)
        (h_R := h_R)
        hblock
        y0Eff
        n
        hwStar
  have hgap_inf :
      (DualBlockMinimizationView.objective f g (xCbpg (n + 1))).toReal -
          (-EReal.toReal (q_opt(f, g))) ≤
        ‖r‖ *
          Metric.infDist
            (xCbpg (n + 1))
            (unconstrained_problem_solutions (DualBlockMinimizationView.objective f g)) := by
    have hnorm_nonneg : 0 ≤ ‖r‖ := by
      have hEq : ‖r‖ = ‖toPiLp r‖ := by
        simpa [toPiLp] using
          (rawAmbientNorm_eq_toPiLpNorm (E := E) (p := p) (v := r))
      rw [hEq]
      exact norm_nonneg (toPiLp r)
    by_cases hzero : ‖r‖ = 0
    · rcases hblock.optimal_set_nonempty with ⟨wStar, hwStar⟩
      have hgap_zero :
          (DualBlockMinimizationView.objective f g (xCbpg (n + 1))).toReal -
              (-EReal.toReal (q_opt(f, g))) ≤ 0 := by
        simpa [hzero] using hgap_dist hwStar
      simpa [hzero] using hgap_zero
    · have hnorm_pos : 0 < ‖r‖ := by
        have hne : 0 ≠ ‖r‖ := by
          intro hnorm
          exact hzero hnorm.symm
        exact lt_of_le_of_ne hnorm_nonneg hne
      have hscaled_le_dist :
          ∀ {wStar : Fin p → E},
            wStar ∈ unconstrained_problem_solutions (DualBlockMinimizationView.objective f g) →
              ((DualBlockMinimizationView.objective f g (xCbpg (n + 1))).toReal -
                  (-EReal.toReal (q_opt(f, g)))) / ‖r‖ ≤
                dist (xCbpg (n + 1)) wStar := by
        intro wStar hwStar
        have hgap := hgap_dist hwStar
        exact (div_le_iff₀ hnorm_pos).2 <| by
          simpa [mul_assoc, mul_left_comm, mul_comm] using hgap
      have hscaled_le_infDist :
          ((DualBlockMinimizationView.objective f g (xCbpg (n + 1))).toReal -
              (-EReal.toReal (q_opt(f, g)))) / ‖r‖ ≤
            Metric.infDist
              (xCbpg (n + 1))
              (unconstrained_problem_solutions (DualBlockMinimizationView.objective f g)) := by
        exact
          (Metric.le_infDist hblock.optimal_set_nonempty).2 <| by
            intro wStar hwStar
            exact hscaled_le_dist hwStar
      have hmul :
          (((DualBlockMinimizationView.objective f g (xCbpg (n + 1))).toReal -
                (-EReal.toReal (q_opt(f, g)))) / ‖r‖) * ‖r‖ ≤
            Metric.infDist
                (xCbpg (n + 1))
                (unconstrained_problem_solutions (DualBlockMinimizationView.objective f g)) * ‖r‖ := by
        exact
          mul_le_mul_of_nonneg_right hscaled_le_infDist hnorm_nonneg
      simpa [div_eq_mul_inv, hzero, mul_assoc, mul_left_comm, mul_comm] using hmul
  have hgap_radius :
      (DualBlockMinimizationView.objective f g (xCbpg (n + 1))).toReal -
          (-EReal.toReal (q_opt(f, g))) ≤
        ‖r‖ * (R : ℝ) := by
    have hnorm_nonneg : 0 ≤ ‖r‖ := by
      have hEq : ‖r‖ = ‖toPiLp r‖ := by
        simpa [toPiLp] using
          (rawAmbientNorm_eq_toPiLpNorm (E := E) (p := p) (v := r))
      rw [hEq]
      exact norm_nonneg (toPiLp r)
    -- The radius hypothesis upgrades `infDist` to the textbook constant `R`.
    calc
      (DualBlockMinimizationView.objective f g (xCbpg (n + 1))).toReal -
          (-EReal.toReal (q_opt(f, g))) ≤
        ‖r‖ *
          Metric.infDist
            (xCbpg (n + 1))
            (unconstrained_problem_solutions (DualBlockMinimizationView.objective f g)) := hgap_inf
      _ ≤ ‖r‖ * (R : ℝ) := by
        exact mul_le_mul_of_nonneg_left (hradius n) hnorm_nonneg
  have hobj_coe :
      DualBlockMinimizationView.objective f g (xCbpg (n + 1)) =
        ((((DualBlockMinimizationView.objective f g (xCbpg (n + 1))).toReal : ℝ)) : EReal) := by
    -- Feasibility of the current outer iterate gives finiteness of the minimization-view objective.
    exact rbpgObjective_eq_coeToReal_of_mem_effective_domain hRBPG hxkp1_g
  have hobj_ne_bot :
      DualBlockMinimizationView.objective f g (xCbpg (n + 1)) ≠ ⊥ := by
    rw [hobj_coe]
    simp
  have hobj_ne_top :
      DualBlockMinimizationView.objective f g (xCbpg (n + 1)) ≠ ⊤ := by
    rw [hobj_coe]
    simp
  have hgap_nonneg :
      0 ≤
        (DualBlockMinimizationView.objective f g (xCbpg (n + 1))).toReal -
          (-EReal.toReal (q_opt(f, g))) := by
    -- The optimal-value lower bound turns the current real objective gap nonnegative.
    have hlower :
        (((-EReal.toReal (q_opt(f, g))) : ℝ) : EReal) ≤
          DualBlockMinimizationView.objective f g (xCbpg (n + 1)) :=
      hblock.optimal_value_isGLB.1 ⟨xCbpg (n + 1), rfl⟩
    have hreal :
        -EReal.toReal (q_opt(f, g)) ≤
          (DualBlockMinimizationView.objective f g (xCbpg (n + 1))).toReal :=
      EReal.toReal_le_toReal hlower (by simp) hobj_ne_top
    exact sub_nonneg.mpr hreal
  have hgap_sq :
      ((DualBlockMinimizationView.objective f g (xCbpg (n + 1))).toReal -
            (-EReal.toReal (q_opt(f, g)))) ^ (2 : ℕ) ≤
        ((R : ℝ) ^ (2 : ℕ)) * (‖r‖ ^ (2 : ℕ)) := by
    -- Square the radius-controlled residual-gap inequality.
    have hR_nonneg : 0 ≤ (R : ℝ) := le_of_lt (PosReal.coe_pos R)
    nlinarith [hgap_radius, hgap_nonneg, norm_nonneg r, hR_nonneg]
  have hresidual_sq :
      ‖r‖ ^ (2 : ℕ) ≤
        (p : ℝ) *
          ((((p : ℝ) / (σ : ℝ)) + (((σ⁻¹ : PosReal) : ℝ))) ^ (2 : ℕ)) *
          ‖xCbpg n - xCbpg (n + 1)‖ ^ (2 : ℕ) := by
    simpa [r, xCbpg] using
      dualBlockMinimizationViewFinalResidualNormSqLeExplicitOuterStep
        (σ := σ)
        (f := f)
        (g := g)
        (y0 := y0)
        (x := x)
        (y := y)
        (h_problem := h_problem)
        (h_trajectory := h_trajectory)
        (α0 := α0)
        (h_initial_level := h_initial_level)
        (R := R)
        (h_R := h_R)
        hblock
        y0Eff
        n
  have hLf_nonneg : 0 ≤ (p : ℝ) / (σ : ℝ) := by
    exact div_nonneg (show 0 ≤ (p : ℝ) by exact_mod_cast Nat.zero_le p) (le_of_lt (PosReal.coe_pos σ))
  have hLf_cast :
      (((Real.toNNReal ((p : ℝ) / (σ : ℝ)) : NNReal) : ℝ)) = (p : ℝ) / (σ : ℝ) := by
    exact congrArg (fun x : NNReal ↦ (x : ℝ)) (Real.toNNReal_of_nonneg hLf_nonneg)
  rcases cbpgConstantBlockStepsizeExtrema (σ := σ) (p := p) with ⟨_hmin, hmax⟩
  rw [cbpgObjectiveGapSqBound]
  have hscaled :
      ((R : ℝ) ^ (2 : ℕ)) * (‖r‖ ^ (2 : ℕ)) ≤
        ((R : ℝ) ^ (2 : ℕ)) *
          ((p : ℝ) *
            ((((p : ℝ) / (σ : ℝ)) + (((σ⁻¹ : PosReal) : ℝ))) ^ (2 : ℕ)) *
            ‖xCbpg n - xCbpg (n + 1)‖ ^ (2 : ℕ)) := by
    exact mul_le_mul_of_nonneg_left hresidual_sq (sq_nonneg (R : ℝ))
  calc
    ((DualBlockMinimizationView.objective f g (xCbpg (n + 1))).toReal -
          (-EReal.toReal (q_opt(f, g)))) ^ (2 : ℕ) ≤
      ((R : ℝ) ^ (2 : ℕ)) * (‖r‖ ^ (2 : ℕ)) := hgap_sq
    _ ≤
      ((R : ℝ) ^ (2 : ℕ)) *
        ((p : ℝ) *
          ((((p : ℝ) / (σ : ℝ)) + (((σ⁻¹ : PosReal) : ℝ))) ^ (2 : ℕ)) *
          ‖xCbpg n - xCbpg (n + 1)‖ ^ (2 : ℕ)) := hscaled
    _ =
      (p : ℝ) *
        ((((Real.toNNReal ((p : ℝ) / (σ : ℝ)) : NNReal) : ℝ) +
            ((cbpg_max_block_stepsize (fun _ : Fin p ↦ σ⁻¹) : PosReal) : ℝ)) ^ (2 : ℕ)) *
        ((R : ℝ) ^ (2 : ℕ)) *
        ‖xCbpg n - xCbpg (n + 1)‖ ^ (2 : ℕ) := by
          rw [hLf_cast, hmax]
          ring
    _ =
      (p : ℝ) *
        ((((Real.toNNReal ((p : ℝ) / (σ : ℝ)) : NNReal) : ℝ) +
            ((cbpg_max_block_stepsize (fun _ : Fin p ↦ σ⁻¹) : PosReal) : ℝ)) ^ (2 : ℕ)) *
        ((R : ℝ) ^ (2 : ℕ)) *
        ‖cyclic_block_proximal_gradient_method
            hblock
            (hblock.interior_effective_domain_point y0Eff)
            n -
          cyclic_block_proximal_gradient_method
            hblock
            (hblock.interior_effective_domain_point y0Eff)
            (n + 1)‖ ^ (2 : ℕ) := by
          rfl

/-- Helper for Theorem 12.17 (`thm:12.17`): once the explicit gap-square certificate is
available, the Chapter 11 sufficient-decrease estimate yields the scalar quadratic recurrence on
the concrete theorem-local CBPG outer sequence. -/
lemma dualBlockMinimizationViewGapStepRecurrence
    {LfRaw : NNReal}
    (hblock :
      BlockProximalGradientAssumptions
        (DualBlockMinimizationView.smoothTerm f)
        (fun i z ↦ ((g i)∗) (-z))
        (fun _ : Fin p ↦ fun w : Fin p → E ↦
          gradient (fun z : E ↦ (((f∗) z).toReal)) (∑ j : Fin p, w j))
        (unconstrained_problem_solutions (DualBlockMinimizationView.objective f g))
        (-EReal.toReal (q_opt(f, g)))
        LfRaw
        (fun _ : Fin p ↦ σ⁻¹))
    (y0Eff : effective_domain (DualBlockMinimizationView.regularizer g))
    (hGapSq :
      ∀ n : ℕ,
        cbpgObjectiveGapSqBound
          (Real.toNNReal ((p : ℝ) / (σ : ℝ)))
          (fun _ : Fin p ↦ σ⁻¹)
          R
          (DualBlockMinimizationView.objective f g)
          (fun m ↦
            cyclic_block_proximal_gradient_method
              hblock
              (hblock.interior_effective_domain_point y0Eff)
              m)
          (-EReal.toReal (q_opt(f, g)))
          n)
    (hstep :
      ∀ n : ℕ,
        cbpgStepDecreaseBound
          (fun _ : Fin p ↦ σ⁻¹)
          (DualBlockMinimizationView.objective f g)
          (fun m ↦
            cyclic_block_proximal_gradient_method
              hblock
              (hblock.interior_effective_domain_point y0Eff)
              m)
          n)
    (n : ℕ) :
    let Δ : ℕ → ℝ := fun m ↦
      (DualBlockMinimizationView.objective f g
          (cyclic_block_proximal_gradient_method
            hblock
            (hblock.interior_effective_domain_point y0Eff)
            m)).toReal -
        (-EReal.toReal (q_opt(f, g)))
    Δ n - Δ (n + 1) ≥
      cbpg_quadratic_gap_constant
        (Real.toNNReal ((p : ℝ) / (σ : ℝ)))
        (fun _ : Fin p ↦ σ⁻¹)
        R * (Δ (n + 1) ^ (2 : ℕ)) := by
  let xCbpg : ℕ → Fin p → E := fun m ↦
    cyclic_block_proximal_gradient_method
      hblock
      (hblock.interior_effective_domain_point y0Eff)
      m
  let Δ : ℕ → ℝ := fun m ↦
    (DualBlockMinimizationView.objective f g (xCbpg m)).toReal -
      (-EReal.toReal (q_opt(f, g)))
  let c : ℝ :=
    cbpg_quadratic_gap_constant
      (Real.toNNReal ((p : ℝ) / (σ : ℝ)))
      (fun _ : Fin p ↦ σ⁻¹)
      R
  have hdropE :
      DualBlockMinimizationView.objective f g (xCbpg n) -
          DualBlockMinimizationView.objective f g (xCbpg (n + 1)) ≥
        (((c *
            (((DualBlockMinimizationView.objective f g (xCbpg (n + 1))).toReal -
                (-EReal.toReal (q_opt(f, g)))) ^ (2 : ℕ))) : ℝ) : EReal) := by
    -- Compose the explicit gap-square certificate with the sufficient-decrease estimate from
    -- Lemma 11.6.
    exact
      cbpg_step_decrease_ge_sq_objective_gap
        (Lf := Real.toNNReal ((p : ℝ) / (σ : ℝ)))
        (Li := fun _ : Fin p ↦ σ⁻¹)
        (F := DualBlockMinimizationView.objective f g)
        (x := xCbpg)
        (FOpt := -EReal.toReal (q_opt(f, g)))
        R
        n
        (hGapSq n)
        (hstep n)
  have hdropR :
      (DualBlockMinimizationView.objective f g (xCbpg n)).toReal -
          (DualBlockMinimizationView.objective f g (xCbpg (n + 1))).toReal ≥
        c *
          (((DualBlockMinimizationView.objective f g (xCbpg (n + 1))).toReal -
              (-EReal.toReal (q_opt(f, g)))) ^ (2 : ℕ)) := by
    -- Rewrite the finite EReal objective drop as the matching real subtraction.
    rw [cbpg_objective_gap_eq_coe_toReal_sub hblock y0Eff n] at hdropE
    exact EReal.coe_le_coe_iff.mp hdropE
  -- Expanding `Δ` shows that the common optimal-value offset cancels on the left-hand side.
  simpa [xCbpg, Δ, c, pow_two] using hdropR

/-- Helper for Theorem 12.17 (`thm:12.17`): the theorem-local CBPG outer gap equals the
source-facing sampled dual gap at every outer time `p * n`. -/
lemma dualBlockMinimizationViewGap_eqSampledDualGap
    {yStar : Fin p → E} {xCbpg : ℕ → Fin p → E}
    (hyStar : yStar ∈ Λ*(f, g))
    (hyStar_finite : yStar ∈ finite_domain (q(f, g)))
    (houter : ∀ n : ℕ, (y (p * n)).ofLp = xCbpg n)
    (n : ℕ) :
    (DualBlockMinimizationView.objective f g (xCbpg n)).toReal -
        (-EReal.toReal (q_opt(f, g))) =
      (q_opt(f, g) - q(f, g) (y (p * n)).ofLp).toReal := by
  have hy_iter_finite :
      (y (p * n)).ofLp ∈ finite_domain (q(f, g)) :=
    cyclicDbpgDualIterateMemFiniteDomain
      (σ := σ)
      (f := f)
      (g := g)
      (y0 := y0)
      (x := x)
      (y := y)
      (h_problem := h_problem)
      (h_trajectory := h_trajectory)
      (α0 := α0)
      (h_initial_level := h_initial_level)
      (R := R)
      (h_R := h_R)
      (p * n)
  -- Rewrite the minimization-view gap through the sampled cyclic iterate and apply the fixed
  -- Chapter 12 gap bridge `Hdual = -q`.
  rw [(houter n).symm]
  exact
    dual_block_minimization_view_gap_toReal_eq_dual_gap
      (f := f)
      (g := g)
      h_problem.toIsProperExtendedRealFunction
      h_problem.g_proper
      hyStar
      hyStar_finite
      hy_iter_finite

/-- Helper for Theorem 12.17 (`thm:12.17`): every theorem-local outer-gap value is nonnegative,
because it is the sampled dual gap and `q_opt` dominates every dual objective value. -/
lemma dualBlockMinimizationViewGapNonnegOnOuterSequence
    {yStar : Fin p → E} {xCbpg : ℕ → Fin p → E}
    (hyStar : yStar ∈ Λ*(f, g))
    (hyStar_finite : yStar ∈ finite_domain (q(f, g)))
    (houter : ∀ n : ℕ, (y (p * n)).ofLp = xCbpg n)
    (n : ℕ) :
    0 ≤
      (DualBlockMinimizationView.objective f g (xCbpg n)).toReal -
        (-EReal.toReal (q_opt(f, g))) := by
  have hy_iter_finite :
      (y (p * n)).ofLp ∈ finite_domain (q(f, g)) :=
    cyclicDbpgDualIterateMemFiniteDomain
      (σ := σ)
      (f := f)
      (g := g)
      (y0 := y0)
      (x := x)
      (y := y)
      (h_problem := h_problem)
      (h_trajectory := h_trajectory)
      (α0 := α0)
      (h_initial_level := h_initial_level)
      (R := R)
      (h_R := h_R)
      (p * n)
  -- First rewrite to the sampled source-facing dual gap, then use `q(y) ≤ q_opt`.
  rw [dualBlockMinimizationViewGap_eqSampledDualGap
    (σ := σ)
    (f := f)
    (g := g)
    (y0 := y0)
    (x := x)
    (y := y)
    (h_problem := h_problem)
    (h_trajectory := h_trajectory)
    (α0 := α0)
    (h_initial_level := h_initial_level)
    (R := R)
    (h_R := h_R)
    hyStar
    hyStar_finite
    houter
    n]
  rw [dual_gap_toReal_eq_of_mem_finite_domain
    (f := f)
    (g := g)
    (yBar := (y (p * n)).ofLp)
    (yStar := yStar)
    hyStar
    hyStar_finite
    hy_iter_finite]
  have hqOpt_ne_top : q_opt(f, g) ≠ ⊤ := by
    rw [← dual_block_proximal_gradient_dual_objective_eq_dual_problem_value_of_mem_optimal_set
      f g hyStar]
    exact (mem_finite_domain.mp hyStar_finite).1.ne
  have hy_iter_ne_bot : q(f, g) (y (p * n)).ofLp ≠ ⊥ :=
    (mem_finite_domain.mp hy_iter_finite).2
  exact sub_nonneg.mpr <|
    EReal.toReal_le_toReal
      (dual_objective_le_dual_problem_value f g (y (p * n)).ofLp)
      hy_iter_ne_bot
      hqOpt_ne_top

/-- Theorem 12.17 GPT-5.4 high proof-only provider diagnostic: for a cyclic DBPG trajectory and
the Assumption 12.16 radius `R = R(q(y⁰))`, every sampled dual iterate `y^(p k)` with `k ≥ 2`
satisfies the textbook geometric-or-sublinear dual-gap bound
`DualBlockProximalGradient.cyclicGapBound`. -/
theorem cyclic_dual_gap_le_max_geometric_or_sublinear (k : ℕ) (hk : 2 ≤ k) :
    (q_opt(f, g) - q(f, g) (y (p * k)).ofLp).toReal ≤
      cyclicGapBound p σ R (q_opt(f, g) - q(f, g) y0.ofLp).toReal k := by
  -- Route correction: the transport blocker at time `p * k + m` is gone. What remains is the
  -- Chapter 11 scalar recurrence step on the theorem-local CBPG outer sequence, using
  -- `cyclicDbpgSampledOuterIterate_eqCbpgOuterIterate` plus
  -- `dualBlockMinimizationViewInitialRadiusBound` to feed the explicit initial-radius theorem.
  rcases h_problem.dual_optimal_set_nonempty with ⟨yStar, hyStar⟩
  have hyStar_finite :
      yStar ∈ finite_domain (q(f, g)) :=
    optimalDualPointMemFiniteDomain
      (σ := σ)
      (f := f)
      (g := g)
      (y0 := y0)
      (x := x)
      (y := y)
      (h_problem := h_problem)
      (h_trajectory := h_trajectory)
      (α0 := α0)
      (h_initial_level := h_initial_level)
      (R := R)
      (h_R := h_R)
      hyStar
  rcases
      cyclicDbpgSampledOuterIterate_eqCbpgOuterIterate
        (σ := σ)
        (f := f)
        (g := g)
        (y0 := y0)
        (x := x)
        (y := y)
        (h_problem := h_problem)
        (h_trajectory := h_trajectory)
        (α0 := α0)
        (h_initial_level := h_initial_level)
        (R := R)
        (h_R := h_R)
        hyStar
        hyStar_finite with
    ⟨LfRaw, hblock, houter⟩
  have hy0_finite :
      y0.ofLp ∈ finite_domain (q(f, g)) :=
    initialDualPointMemFiniteDomain
      (σ := σ)
      (f := f)
      (g := g)
      (h_problem := h_problem)
      (y0 := y0)
      (x := x)
      (y := y)
      (h_trajectory := h_trajectory)
      (α0 := α0)
      (h_initial_level := h_initial_level)
      (R := R)
      (h_R := h_R)
  have hy0_eff :
      y0.ofLp ∈ effective_domain (DualBlockMinimizationView.regularizer g) :=
    initial_dual_point_mem_effective_domain_minimization_view
      f
      g
      y0.ofLp
      h_problem.toIsProperExtendedRealFunction
      h_problem.g_proper
      hy0_finite
  let y0Eff : effective_domain (DualBlockMinimizationView.regularizer g) :=
    ⟨y0.ofLp, hy0_eff⟩
  let xCbpg : ℕ → Fin p → E := fun m ↦
    cyclic_block_proximal_gradient_method
      hblock
      (hblock.interior_effective_domain_point y0Eff)
      m
  have hstep :
      cbpgStepDecreaseBound
        (fun _ : Fin p ↦ σ⁻¹)
        (DualBlockMinimizationView.objective f g)
        xCbpg
        k :=
    dualBlockMinimizationViewOuterStepDecreaseBound
      (σ := σ)
      (f := f)
      (g := g)
      (y0 := y0)
      (x := x)
      (y := y)
      (h_problem := h_problem)
      (h_trajectory := h_trajectory)
      (α0 := α0)
      (h_initial_level := h_initial_level)
      (R := R)
      (h_R := h_R)
      hblock
      y0Eff
      k
  have hstep_all :
      ∀ n : ℕ,
        cbpgStepDecreaseBound
          (fun _ : Fin p ↦ σ⁻¹)
          (DualBlockMinimizationView.objective f g)
          xCbpg
          n := by
    intro n
    -- The same sufficient-decrease estimate holds at every outer step of the local CBPG
    -- trajectory.
    exact
      dualBlockMinimizationViewOuterStepDecreaseBound
        (σ := σ)
        (f := f)
        (g := g)
        (y0 := y0)
        (x := x)
        (y := y)
        (h_problem := h_problem)
        (h_trajectory := h_trajectory)
        (α0 := α0)
        (h_initial_level := h_initial_level)
        (R := R)
        (h_R := h_R)
        hblock
        y0Eff
        n
  have houter_antitone :
      Antitone (fun m ↦ DualBlockMinimizationView.objective f g (xCbpg m)) := by
    let _ : Nonempty (Fin p) :=
      ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne p)⟩⟩
    refine antitone_nat_of_succ_le ?_
    intro n
    let j0 : Fin p := ⟨0, Nat.pos_of_ne_zero (NeZero.ne p)⟩
    have hgap_nonneg :
        0 ≤
          (DualBlockMinimizationView.objective f g (xCbpg n)).toReal -
            (DualBlockMinimizationView.objective f g (xCbpg (n + 1))).toReal :=
      (cbpg_objective_gap_real_bounds hblock y0Eff n j0).1
    have hdrop_nonneg :
        (0 : EReal) ≤
          DualBlockMinimizationView.objective f g (xCbpg n) -
            DualBlockMinimizationView.objective f g (xCbpg (n + 1)) := by
      rw [cbpg_objective_gap_eq_coe_toReal_sub hblock y0Eff n]
      exact_mod_cast hgap_nonneg
    have hfinite_n :
        DualBlockMinimizationView.objective f g (xCbpg n) ≠ ⊤ ∨
          DualBlockMinimizationView.objective f g (xCbpg (n + 1)) ≠ ⊤ := by
      exact Or.inl (cbpg_objective_value_finite hblock y0Eff n).1
    have hfinite_bot :
        DualBlockMinimizationView.objective f g (xCbpg n) ≠ ⊥ ∨
          DualBlockMinimizationView.objective f g (xCbpg (n + 1)) ≠ ⊥ := by
      exact Or.inl (cbpg_objective_value_finite hblock y0Eff n).2
    exact (EReal.sub_nonneg hfinite_n hfinite_bot).mp hdrop_nonneg
  have hradius :
      ∀ n : ℕ,
        Metric.infDist
            (xCbpg (n + 1))
            (unconstrained_problem_solutions (DualBlockMinimizationView.objective f g)) ≤
          R := by
    intro n
    -- The CBPG outer objective is antitone, so every later outer iterate stays in the initial
    -- minimization-view sublevel controlled by Assumption 12.16.
    refine dualBlockMinimizationViewInitialRadiusBound
      (σ := σ)
      (f := f)
      (g := g)
      (y0 := y0)
      (x := x)
      (y := y)
      (h_problem := h_problem)
      (h_trajectory := h_trajectory)
      (α0 := α0)
      (h_initial_level := h_initial_level)
      (R := R)
      (h_R := h_R)
      ?_
    simpa [xCbpg] using houter_antitone (Nat.zero_le (n + 1))
  let Δ : ℕ → ℝ := fun n ↦
    (DualBlockMinimizationView.objective f g (xCbpg n)).toReal -
      (-EReal.toReal (q_opt(f, g)))
  have hGapSq :
      ∀ n : ℕ,
        cbpgObjectiveGapSqBound
          (Real.toNNReal ((p : ℝ) / (σ : ℝ)))
          (fun _ : Fin p ↦ σ⁻¹)
          R
          (DualBlockMinimizationView.objective f g)
          xCbpg
          (-EReal.toReal (q_opt(f, g)))
          n := by
    intro n
    -- The only nontrivial Chapter 11 input is isolated in the dedicated theorem-local support
    -- lemma above.
    simpa [xCbpg] using
      dualBlockMinimizationViewObjectiveGapSqBoundExplicitLf
        (σ := σ)
        (f := f)
        (g := g)
        (y0 := y0)
        (x := x)
        (y := y)
        (h_problem := h_problem)
        (h_trajectory := h_trajectory)
        (α0 := α0)
        (h_initial_level := h_initial_level)
        (R := R)
        (h_R := h_R)
        hblock
        y0Eff
        hradius
        n
  have hrecurrence :
      ∀ n : ℕ,
        Δ n - Δ (n + 1) ≥
          cbpg_quadratic_gap_constant
            (Real.toNNReal ((p : ℝ) / (σ : ℝ)))
            (fun _ : Fin p ↦ σ⁻¹)
            R * (Δ (n + 1) ^ (2 : ℕ)) := by
    intro n
    -- With the objective-gap-square certificate isolated, the recurrence is the standard
    -- Chapter 11 decrease step.
    simpa [Δ, xCbpg] using
      dualBlockMinimizationViewGapStepRecurrence
        (σ := σ)
        (f := f)
        (g := g)
        (y0 := y0)
        (x := x)
        (y := y)
        (h_trajectory := h_trajectory)
        (α0 := α0)
        (h_initial_level := h_initial_level)
        (R := R)
        (h_R := h_R)
        (hblock := hblock)
        (y0Eff := y0Eff)
        (hGapSq := hGapSq)
        (hstep := hstep_all)
        (n := n)
  have hnonneg :
      ∀ n : ℕ, 0 ≤ Δ n := by
    intro n
    -- Nonnegativity is transported once from the sampled source-facing dual gap.
    simpa [Δ, xCbpg] using
      dualBlockMinimizationViewGapNonnegOnOuterSequence
        (σ := σ)
        (f := f)
        (g := g)
        (y0 := y0)
        (x := x)
        (y := y)
        (h_problem := h_problem)
        (h_trajectory := h_trajectory)
        (α0 := α0)
        (h_initial_level := h_initial_level)
        (R := R)
        (h_R := h_R)
        hyStar
        hyStar_finite
        houter
        n
  let c : ℝ :=
    cbpg_quadratic_gap_constant
      (Real.toNNReal ((p : ℝ) / (σ : ℝ)))
      (fun _ : Fin p ↦ σ⁻¹)
      R
  have hc_pos : 0 < c := by
    have hσ_pos : 0 < (σ : ℝ) := PosReal.coe_pos σ
    have hLf_nonneg : 0 ≤ (p : ℝ) / (σ : ℝ) := by
      exact div_nonneg (show 0 ≤ (p : ℝ) by exact_mod_cast Nat.zero_le p) hσ_pos.le
    have hp_pos : 0 < (p : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
    rcases cbpgConstantBlockStepsizeExtrema (σ := σ) (p := p) with ⟨hmin, hmax⟩
    dsimp [c]
    rw [hmin, hmax]
    rw [max_eq_left hLf_nonneg]
    have hsum_pos :
        0 < (p : ℝ) / (σ : ℝ) + (((σ⁻¹ : PosReal) : ℝ)) := by
      exact add_pos (div_pos hp_pos hσ_pos) (PosReal.coe_pos (σ⁻¹))
    have hfront_pos : 0 < 2 * (p : ℝ) := by
      positivity
    have hsq_pos :
        0 < (((p : ℝ) / (σ : ℝ) + (((σ⁻¹ : PosReal) : ℝ))) ^ (2 : ℕ)) := by
      positivity
    have hR_sq_pos : 0 < ((R : ℝ) ^ (2 : ℕ)) := by
      have hR_pos : 0 < (R : ℝ) := PosReal.coe_pos R
      nlinarith [sq_pos_of_pos hR_pos]
    have hden_left_pos :
        0 <
          2 * (p : ℝ) *
            (((p : ℝ) / (σ : ℝ) + (((σ⁻¹ : PosReal) : ℝ))) ^ (2 : ℕ)) := by
      exact mul_pos hfront_pos hsq_pos
    have hden_pos :
        0 <
          2 * (p : ℝ) *
            (((p : ℝ) / (σ : ℝ) + (((σ⁻¹ : PosReal) : ℝ))) ^ (2 : ℕ)) *
            ((R : ℝ) ^ (2 : ℕ)) := by
      exact mul_pos hden_left_pos hR_sq_pos
    exact div_pos (PosReal.coe_pos (σ⁻¹)) hden_pos
  let γ : PosReal := ⟨c⁻¹, inv_pos.mpr hc_pos⟩
  have hrecurrence_gamma :
      ∀ n : ℕ, Δ n - Δ (n + 1) ≥ (1 / (γ : ℝ)) * (Δ (n + 1) ^ (2 : ℕ)) := by
    intro n
    -- Package the same recurrence with the reciprocal parameter expected by Lemma 11.7.
    simpa [γ, c, one_div] using hrecurrence n
  have hmain :
      Δ k ≤
        max
          (((1 / 2 : ℝ) ^ (((k - 1 : ℕ) : ℝ) / 2)) * Δ 0)
          (4 * (γ : ℝ) / (((k - 1 : ℕ) : ℝ))) :=
    nonnegative_sequence_le_max_geometric_or_sublinear_of_quadratic_step_recurrence
      (a := Δ)
      (γ := γ)
      hnonneg
      hrecurrence_gamma
      hk
  have hΔ0 :
      Δ 0 = (q_opt(f, g) - q(f, g) y0.ofLp).toReal := by
    -- The initial outer iterate is exactly the source initial dual point `y0`.
    calc
      Δ 0 =
          (q_opt(f, g) - q(f, g) (y (p * 0)).ofLp).toReal := by
            simpa [Δ, xCbpg] using
              dualBlockMinimizationViewGap_eqSampledDualGap
                (σ := σ)
                (f := f)
                (g := g)
                (y0 := y0)
                (x := x)
                (y := y)
                (h_problem := h_problem)
                (h_trajectory := h_trajectory)
                (α0 := α0)
                (h_initial_level := h_initial_level)
                (R := R)
                (h_R := h_R)
                hyStar
                hyStar_finite
                houter
                0
      _ = (q_opt(f, g) - q(f, g) (y 0).ofLp).toReal := by simp
      _ = (q_opt(f, g) - q(f, g) y0.ofLp).toReal := by
            simpa [is_dual_block_proximal_gradient_primal_trajectory_zero h_trajectory]
  have hγcoeff :
      4 * (γ : ℝ) / (((k - 1 : ℕ) : ℝ)) = 4 / (c * (((k - 1 : ℕ) : ℝ)) ) := by
    have hk1_nat : 1 ≤ k - 1 := by
      omega
    have hk1_ne : (((k - 1 : ℕ) : ℝ)) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hk1_nat)
    have hc_ne : c ≠ 0 := hc_pos.ne'
    dsimp [γ]
    field_simp [hc_ne, hk1_ne]
  -- The main theorem now only rewrites the recurrence output back to the sampled dual gap and the
  -- textbook coefficient owner `cyclicGapBound`.
  calc
    (q_opt(f, g) - q(f, g) (y (p * k)).ofLp).toReal = Δ k := by
      symm
      simpa [Δ, xCbpg] using
        dualBlockMinimizationViewGap_eqSampledDualGap
          (σ := σ)
          (f := f)
          (g := g)
          (y0 := y0)
          (x := x)
          (y := y)
          (h_problem := h_problem)
          (h_trajectory := h_trajectory)
          (α0 := α0)
          (h_initial_level := h_initial_level)
          (R := R)
          (h_R := h_R)
          hyStar
          hyStar_finite
          houter
          k
    _ ≤
        max
          (((1 / 2 : ℝ) ^ (((k - 1 : ℕ) : ℝ) / 2)) * Δ 0)
          (4 * (γ : ℝ) / (((k - 1 : ℕ) : ℝ))) := hmain
    _ =
        max
          (((1 / 2 : ℝ) ^ (((k - 1 : ℕ) : ℝ) / 2)) *
            (q_opt(f, g) - q(f, g) y0.ofLp).toReal)
          (4 / (c * (((k - 1 : ℕ) : ℝ)))) := by
            rw [hΔ0, hγcoeff]
    _ =
        max
          (((1 / 2 : ℝ) ^ (((k - 1 : ℕ) : ℝ) / 2)) *
            (q_opt(f, g) - q(f, g) y0.ofLp).toReal)
          (4 /
            (cbpg_quadratic_gap_constant
              (Real.toNNReal ((p : ℝ) / (σ : ℝ)))
              (fun _ : Fin p ↦ σ⁻¹)
              R *
              (((k - 1 : ℕ) : ℝ)))) := by
                rfl
    _ =
        cyclicGapBound p σ R (q_opt(f, g) - q(f, g) y0.ofLp).toReal k := by
          exact
            dualBlockMinimizationViewCyclicCoeff_eq_cyclicGapBound
              (σ := σ)
              (f := f)
              (g := g)
              (y0 := y0)
              (x := x)
              (y := y)
              (h_problem := h_problem)
              (h_trajectory := h_trajectory)
              (α0 := α0)
              (h_initial_level := h_initial_level)
              (p := p)
              (R := R)
              (h_R := h_R)
              (initialGap := (q_opt(f, g) - q(f, g) y0.ofLp).toReal)
              (k := k)

/-- Theorem 12.17 (2) (`thm:12.17`): under the same cyclic DBPG hypotheses, every sampled
primal iterate `x^(p k)` with `k ≥ 2` satisfies the corresponding squared-distance estimate for
each minimizer `xStar`. The conclusion uses the original norm on `E`. -/
theorem cyclic_primal_sqdist_le_max_geometric_or_sublinear
    (xStar : E)
    (h_xStar :
      xStar ∈ unconstrained_problem_solutions
        (composite_model_objective f (finite_sum_objective g)))
    (k : ℕ) (hk : 2 ≤ k) :
    ‖x (p * k) - xStar‖ ^ 2 ≤
      (2 / (σ : ℝ)) *
        cyclicGapBound p σ R (q_opt(f, g) - q(f, g) y0.ofLp).toReal k := by
  -- First bound the sampled primal distance by the same-iterate dual gap.
  have hsqdist :
      ‖x (p * k) - xStar‖ ^ 2 ≤
        (2 / (σ : ℝ)) * (q_opt(f, g) - q(f, g) (y (p * k)).ofLp).toReal :=
    cyclicDbpgPrimalSqdist_le_dualGap
      (σ := σ)
      (f := f)
      (g := g)
      (y0 := y0)
      (x := x)
      (y := y)
      (h_problem := h_problem)
      (h_trajectory := h_trajectory)
      (α0 := α0)
      (h_initial_level := h_initial_level)
      (R := R)
      (h_R := h_R)
      xStar
      h_xStar
      k
      (Nat.mul_pos
        (Nat.pos_of_ne_zero (NeZero.ne p))
        (lt_of_lt_of_le zero_lt_two hk))
  -- Then insert the dual-gap rate from part (1) and preserve the inequality under the positive
  -- scalar factor `2 / σ`.
  have hgap :
      (q_opt(f, g) - q(f, g) (y (p * k)).ofLp).toReal ≤
        cyclicGapBound p σ R (q_opt(f, g) - q(f, g) y0.ofLp).toReal k :=
    cyclic_dual_gap_le_max_geometric_or_sublinear
      (σ := σ)
      (f := f)
      (g := g)
      (y0 := y0)
      (x := x)
      (y := y)
      (h_problem := h_problem)
      (h_trajectory := h_trajectory)
      (α0 := α0)
      (h_initial_level := h_initial_level)
      (R := R)
      (h_R := h_R)
      k
      hk
  have hfactor_nonneg : 0 ≤ 2 / (σ : ℝ) := by
    exact div_nonneg (by norm_num) (le_of_lt σ.2)
  exact
    hsqdist.trans <|
      mul_le_mul_of_nonneg_left hgap hfactor_nonneg

/-- Diagnostic companion for Theorem 12.17 GPT-5.4 high proof-only provider diagnostic: for
cyclic DBPG, the sampled dual gap and the sampled primal squared distance both satisfy the
textbook `O(1 / k)`-or-geometric rate bounds at every outer iterate `k ≥ 2`. -/
theorem cyclic_dbpg_rate_bounds
    (k : ℕ) (hk : 2 ≤ k) :
    (q_opt(f, g) - q(f, g) (y (p * k)).ofLp).toReal ≤
        cyclicGapBound p σ R (q_opt(f, g) - q(f, g) y0.ofLp).toReal k ∧
      ∀ xStar : E,
        xStar ∈ unconstrained_problem_solutions
            (composite_model_objective f (finite_sum_objective g)) →
          ‖x (p * k) - xStar‖ ^ 2 ≤
            (2 / (σ : ℝ)) *
              cyclicGapBound p σ R (q_opt(f, g) - q(f, g) y0.ofLp).toReal k := by
  constructor
  · -- Part (a) is the dual-gap estimate already proved above.
    exact
      cyclic_dual_gap_le_max_geometric_or_sublinear
        (σ := σ)
        (f := f)
        (g := g)
        (y0 := y0)
        (x := x)
        (y := y)
        (h_problem := h_problem)
        (h_trajectory := h_trajectory)
        (α0 := α0)
        (h_initial_level := h_initial_level)
        (R := R)
        (h_R := h_R)
        k
        hk
  · intro xStar h_xStar
    -- Part (b) is the companion primal-distance estimate for each minimizer.
    exact
      cyclic_primal_sqdist_le_max_geometric_or_sublinear
        (σ := σ)
        (f := f)
        (g := g)
        (y0 := y0)
        (x := x)
        (y := y)
        (h_problem := h_problem)
        (h_trajectory := h_trajectory)
        (α0 := α0)
        (h_initial_level := h_initial_level)
        (R := R)
        (h_R := h_R)
        xStar
        h_xStar
        k
        hk

end

#check cyclic_dual_gap_le_max_geometric_or_sublinear
#check cyclic_primal_sqdist_le_max_geometric_or_sublinear

#print axioms DualBlockProximalGradient.cyclicGapBound
#print axioms DualBlockProximalGradient.cyclicGapBound_apply
