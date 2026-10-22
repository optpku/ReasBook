/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap10.Algorithm_10_6
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Lemma_10_33
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_35
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Theorem_10_16
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Theorem_10_21
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Remark_10_32

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Gradient

section ObjectiveBridge

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
variable {f : E → ℝ} {g : E → EReal} {XStar : Set E} {FOpt : ℝ} {Lf : NNReal}
variable [hproblem : IsFastProximalGradientProblem f g XStar FOpt Lf]

/-- Helper for Theorem 10.34: on `effective_domain g`, the composite objective is the finite real
sum `f + g`. -/
theorem fista_objective_eq_real_of_mem_effective_domain
    (hproblem : IsFastProximalGradientProblem f g XStar FOpt Lf)
    {xPoint : E} (hxPoint : xPoint ∈ effective_domain g) :
    composite_model_objective f.toEReal g xPoint =
      (((f xPoint + (g xPoint).toReal : ℝ)) : EReal) := by
  -- Route correction: reuse the Chapter 10 finite-objective normalization already proved for the
  -- same fast-problem interface.
  exact
    objectiveEqReal_of_memEffectiveDomainG
      (hproblem := hproblem.toIsConvexCompositeSmoothMinimizationProblem)
      hxPoint

/-- Helper for Theorem 10.34: every finite objective gap is the cast of its real gap. -/
theorem fista_objective_gap_eq_coe_sub_toReal_of_mem_effective_domain
    (hproblem : IsFastProximalGradientProblem f g XStar FOpt Lf)
    {xPoint : E} (hxPoint : xPoint ∈ effective_domain g) :
    ((((composite_model_objective f.toEReal g xPoint).toReal - FOpt : ℝ)) : EReal) =
      composite_model_objective f.toEReal g xPoint - (FOpt : EReal) := by
  -- The earlier owner theorem already identifies a finite objective gap with the corresponding
  -- real difference.
  exact
    objectiveMinusFOpt_eq_coe_sub_toReal_of_memEffectiveDomainG
      (hproblem := hproblem.toIsConvexCompositeSmoothMinimizationProblem)
      hxPoint

/-- Helper for Theorem 10.34: every finite objective value is at least the optimal value `FOpt`. -/
theorem fista_toReal_ge_FOpt_of_mem_effective_domain
    (hproblem : IsFastProximalGradientProblem f g XStar FOpt Lf)
    {xPoint : E} (hxPoint : xPoint ∈ effective_domain g) :
    FOpt ≤ (composite_model_objective f.toEReal g xPoint).toReal := by
  -- Finite feasible objective values inherit the global lower bound `FOpt`.
  exact
    toReal_ge_FOpt_of_memEffectiveDomainG
      (hproblem := hproblem.toIsConvexCompositeSmoothMinimizationProblem)
      hxPoint

end ObjectiveBridge

section FistaRate

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
variable {f : E → ℝ} {g : E → EReal} {XStar : Set E} {FOpt : ℝ} {Lf : NNReal}
variable [hproblem : IsFastProximalGradientProblem f g XStar FOpt Lf]
variable (x0 : E) (L : ℕ → PosReal) {α : ℝ} {xStar : E}

/-- Helper for Theorem 10.34: canonical explicit-owner spelling of the FISTA iterate sequence. -/
private abbrev fistaX
    (hproblem : IsFastProximalGradientProblem f g XStar FOpt Lf)
    (x0 : E) (L : ℕ → PosReal) : ℕ → E :=
  @fista_x E _ _ _ f g hproblem.g_proper ⟨hproblem.g_closed⟩ ⟨hproblem.g_convex⟩ x0 L

/-- Helper for Theorem 10.34: canonical explicit-owner spelling of the FISTA momentum sequence. -/
private abbrev fistaT
    (hproblem : IsFastProximalGradientProblem f g XStar FOpt Lf)
    (x0 : E) (L : ℕ → PosReal) : ℕ → ℝ :=
  @fista_t E _ _ _ f g hproblem.g_proper ⟨hproblem.g_closed⟩ ⟨hproblem.g_convex⟩ x0 L

/-- Helper for Theorem 10.34: canonical explicit-owner spelling of the FISTA extrapolated
sequence. -/
private abbrev fistaY
    (hproblem : IsFastProximalGradientProblem f g XStar FOpt Lf)
    (x0 : E) (L : ℕ → PosReal) : ℕ → E :=
  @fista_y E _ _ _ f g hproblem.g_proper ⟨hproblem.g_closed⟩ ⟨hproblem.g_convex⟩ x0 L

/-- Helper for Theorem 10.34: the source Lyapunov residual
`u^0 = x^0 - xStar` and
`u^(k+1) = t_k x^(k+1) - (xStar + (t_k - 1) x^k)`. -/
def fista_lyapunov_residual
    (hproblem : IsFastProximalGradientProblem f g XStar FOpt Lf)
    (x0 : E) (L : ℕ → PosReal) (xStar : E) : ℕ → E
  | 0 => x0 - xStar
  | k + 1 =>
      ((fistaT hproblem x0 L k : ℝ) •
          fistaX hproblem x0 L (k + 1)) -
        (xStar + ((fistaT hproblem x0 L k : ℝ) - 1) •
          fistaX hproblem x0 L k)

/-- Helper for Theorem 10.34: the first positive Lyapunov residual is the explicit
`u^1 = x^1 - xStar`. -/
@[simp] theorem fista_lyapunov_residual_one (xStar : E) :
    fista_lyapunov_residual hproblem x0 L xStar 1 =
      fistaX hproblem x0 L 1 - xStar := by
  -- Evaluate the residual at the first positive index and simplify the initial momentum
  -- parameter `t_0 = 1`.
  simp [fista_lyapunov_residual]

/-- Helper for Theorem 10.34: every positive FISTA objective gap is nonnegative as a real
number. -/
theorem fistaPositiveIterate_memEffectiveDomain
    {n : ℕ} (hn : 1 ≤ n) :
    fistaX hproblem x0 L n ∈ effective_domain g := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  -- Every positive FISTA iterate is a prox-gradient point, hence it lies in `effective_domain g`.
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  simpa [Nat.add_comm, fistaX, fistaY, fista_x_succ] using
    (prox_grad_step_mem_effective_domain_g
      (f := f.toEReal)
      (g := g)
      (y := interior_effective_domain_point_of_real f
        (fistaY hproblem x0 L k))
      (L := L k))

/-- Helper for Theorem 10.34: every positive FISTA objective gap is nonnegative as a real
number. -/
theorem fista_positive_iterate_gap_nonneg
    {n : ℕ} (hn : 1 ≤ n) :
    0 ≤
      (composite_model_objective f.toEReal g
        (fistaX hproblem x0 L n)).toReal - FOpt := by
  have hxsucc_g :
      fistaX hproblem x0 L n ∈ effective_domain g :=
    fistaPositiveIterate_memEffectiveDomain (hproblem := hproblem) (x0 := x0) (L := L) hn
  -- The finite iterate value is bounded below by the optimal objective value.
  exact sub_nonneg.mpr <|
    fista_toReal_ge_FOpt_of_mem_effective_domain hproblem hxsucc_g

/-- Helper for Theorem 10.34: every admissible FISTA stepsize is bounded above by `α * Lf`. -/
theorem fistaSublinearRateStepsizeBound
    (hrule : hproblem.SublinearRateStepsizeRule
      (fistaY hproblem x0 L) L α)
    (n : ℕ) :
    (L n : ℝ) ≤ α * (Lf : ℝ) := by
  rcases hrule with ⟨hα, hLf_rule⟩ | ⟨hLf_pos, s, η, hB3α, hB3⟩
  · -- In the constant branch, the rule is literally `L_n = L_f` with `α = 1`.
    rw [hα, hLf_rule n]
    simpa using (le_rfl : (Lf : ℝ) ≤ (Lf : ℝ))
  · -- In the B3 branch, compare the global bound from Remark 10.32 against
    -- `α = max {η, s / L_f}`.
    rcases
        hproblem.uses_backtracking_procedure_B3_rule_stepsize_bounds s η hB3 n with
      ⟨_, hLn_upper⟩
    have hη_upper : (η : ℝ) * (Lf : ℝ) ≤ α * (Lf : ℝ) := by
      rw [hB3α]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (le_of_lt hLf_pos)
    have hs_upper : (s : ℝ) ≤ α * (Lf : ℝ) := by
      rw [hB3α]
      exact (div_le_iff₀ hLf_pos).1 (le_max_right _ _)
    have hmax_upper : max ((η : ℝ) * (Lf : ℝ)) (s : ℝ) ≤ α * (Lf : ℝ) := by
      exact max_le hη_upper hs_upper
    exact le_trans hLn_upper hmax_upper

/-- Helper for Theorem 10.34: every admissible FISTA stepsize sequence is monotone. -/
theorem fistaStepsizeMonotone
    (hrule : hproblem.SublinearRateStepsizeRule
      (fistaY hproblem x0 L) L α)
    (n : ℕ) :
    (L n : ℝ) ≤ (L (n + 1) : ℝ) := by
  rcases hrule with ⟨_, hLf_rule⟩ | ⟨_, s, η, _, hB3⟩
  · -- In the constant branch, all stepsizes are equal to `L_f`.
    rw [hLf_rule n, hLf_rule (n + 1)]
  · -- In the B3 branch, B3 compares `L_(n+1)` against the previous accepted stepsize `L_n`.
    -- Local instance justification (owner reuse): the B3 local-bounds theorem is stated in the
    -- shared prox-gradient API, so we expose the `g`-regularity package carried by `hproblem`.
    letI : IsProperExtendedRealFunction g := hproblem.g_proper
    -- Local instance justification (owner reuse): the same B3 bridge also expects the closedness
    -- witness stored in the standing fast-problem assumptions.
    letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
    -- Local instance justification (owner reuse): the same B3 bridge finally expects the
    -- convexity witness already stored in `hproblem`.
    letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
    simpa [proximal_gradient_backtracking_B2_previous_stepsize_succ] using
      (backtracking_B3_local_stepsize_bounds
        (f := f) (g := g) (Lf := Lf)
        hproblem.f_smooth hB3 (n + 1)).1

/-- Helper for Theorem 10.34: any optimizer has finite `g`-value, hence lies in
`effective_domain g`. -/
theorem fistaOptimalPoint_memEffectiveDomain
    [hproblem : IsFastProximalGradientProblem f g XStar FOpt Lf]
    (hxStar : xStar ∈ XStar) :
    xStar ∈ effective_domain g := by
  -- Read the optimizer through the canonical fast-problem objective-value bridge.
  have hxStar_value :
      composite_model_objective f.toEReal g xStar = (FOpt : EReal) :=
    IsConvexCompositeSmoothMinimizationProblem.objective_eq_optimalValue_of_mem_optimalSet
      (h := hproblem.toIsConvexCompositeSmoothMinimizationProblem)
      hxStar
  have hg_top : g xStar ≠ ⊤ := by
    intro hg_top
    have hobj_top :
        composite_model_objective f.toEReal g xStar = ⊤ := by
      simp [composite_model_objective_apply, Function.toEReal, hg_top]
    rw [hobj_top] at hxStar_value
    simp at hxStar_value
  exact mem_effective_domain.mpr (lt_top_iff_ne_top.mpr hg_top)

/-- Helper for Theorem 10.34: the reciprocal of the FISTA momentum coefficient is a genuine
convex-combination weight. -/
theorem fistaOneDivMomentum_memIcc
    (n : ℕ) :
    (1 / fistaT hproblem x0 L (n + 1) : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  -- Local instance justification (scalar owner reuse): `fista_t_lower_bound` is stated for the
  -- canonical FISTA owner with the `g`-regularity package exposed as typeclass data.
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  -- Read the reciprocal coefficient through the textbook lower bound `t_(n+1) ≥ 1`.
  have hone_le :
      (1 : ℝ) ≤ fistaT hproblem x0 L (n + 1) := by
    have hone_le_half :
        (1 : ℝ) ≤ (((n + 1 : ℕ) : ℝ) + 2) / 2 := by
      have hn1_nonneg :
          (0 : ℝ) ≤ (((n + 1 : ℕ) : ℝ)) := by
        exact_mod_cast Nat.zero_le (n + 1)
      nlinarith
    exact le_trans hone_le_half <| by
      simpa [fistaT] using
      (fista_t_lower_bound (f := f) (g := g) (x0 := x0) (L := L) (k := n + 1))
  have hpos :
      0 < fistaT hproblem x0 L (n + 1) := lt_of_lt_of_le zero_lt_one hone_le
  constructor
  · exact one_div_nonneg.mpr (le_of_lt hpos)
  · have hrecip_le :
        1 / fistaT hproblem x0 L (n + 1) ≤ 1 / (1 : ℝ) := by
      exact one_div_le_one_div_of_le zero_lt_one hone_le
    simpa using hrecip_le

/-- Helper for Theorem 10.34: the FISTA momentum recursion satisfies
`t_(n+1)^2 - t_(n+1) = t_n^2`. -/
theorem fistaMomentumSqSub_eq_prevSq
    (n : ℕ) :
    fistaT hproblem x0 L (n + 1) ^ (2 : ℕ) -
        fistaT hproblem x0 L (n + 1) =
      fistaT hproblem x0 L n ^ (2 : ℕ) := by
  -- Local instance justification (scalar owner reuse): `fista_t_succ` is the canonical FISTA
  -- owner theorem and requires the regularity package as explicit instances.
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  -- Rewrite the successor momentum by the canonical update formula and square the resulting
  -- explicit radical identity.
  have hsucc :
      fistaT hproblem x0 L (n + 1) =
        fista_momentum_update (fistaT hproblem x0 L n) := by
    simpa [fistaT] using
      (fista_t_succ (f := f) (g := g) (x0 := x0) (L := L) n)
  rw [fista_momentum_update_eq] at hsucc
  have hrad_nonneg :
      0 ≤ 1 + 4 * fistaT hproblem x0 L n ^ (2 : ℕ) := by
    positivity
  have hsqrt :
      Real.sqrt (1 + 4 * fistaT hproblem x0 L n ^ (2 : ℕ)) =
        2 * fistaT hproblem x0 L (n + 1) - 1 := by
    nlinarith [hsucc]
  have hsq :
      (Real.sqrt (1 + 4 * fistaT hproblem x0 L n ^ (2 : ℕ))) ^ (2 : ℕ) =
        (2 * fistaT hproblem x0 L (n + 1) - 1) ^ (2 : ℕ) := by
    simpa using congrArg (fun t : ℝ ↦ t ^ (2 : ℕ)) hsqrt
  rw [Real.sq_sqrt hrad_nonneg] at hsq
  -- The squared radical identity is exactly the source recurrence
  -- `t_(n+1)^2 - t_(n+1) = t_n^2`.
  nlinarith

/-- Helper for Theorem 10.34: the source comparison point
`(1 / t_(n+1)) • xStar + (1 - 1 / t_(n+1)) • x^(n+1)` stays in `effective_domain g`. -/
theorem fistaCombinationPoint_memEffectiveDomain
    (hxStar : xStar ∈ XStar)
    (n : ℕ) :
    let θ : ℝ := 1 / fistaT hproblem x0 L (n + 1)
    let w : E := θ • xStar + (1 - θ) • fistaX hproblem x0 L (n + 1)
    w ∈ effective_domain g := by
  dsimp
  have hxStar_eff :
      xStar ∈ effective_domain g :=
    fistaOptimalPoint_memEffectiveDomain (hproblem := hproblem) hxStar
  have hxsucc_eff :
      fistaX hproblem x0 L (n + 1) ∈ effective_domain g :=
    fistaPositiveIterate_memEffectiveDomain (hproblem := hproblem) (x0 := x0) (L := L)
      (show 1 ≤ n + 1 by exact Nat.succ_le_succ (Nat.zero_le n))
  have hθ_mem :
      (1 / fistaT hproblem x0 L (n + 1) : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    simpa using fistaOneDivMomentum_memIcc (hproblem := hproblem) (x0 := x0) (L := L) n
  -- Convexity of `g` keeps the source comparison point inside the effective domain.
  exact combo_mem_effective_domain_of_is_convex_function hproblem.g_convex
    hxStar_eff hxsucc_eff hθ_mem

/-- Helper for Theorem 10.34: convexity bounds the objective of the source comparison point by
`(1 - 1 / t_(n+1)) v_(n+1) + FOpt` on the real layer. -/
private theorem fistaCombinationObjectiveUpperBoundReal
    (hxStar : xStar ∈ XStar)
    (n : ℕ) :
    let θ : ℝ := 1 / fistaT hproblem x0 L (n + 1)
    let w : E := θ • xStar + (1 - θ) • fistaX hproblem x0 L (n + 1)
    (composite_model_objective f.toEReal g w).toReal ≤
      (1 - θ) *
          ((composite_model_objective f.toEReal g
              (fistaX hproblem x0 L (n + 1))).toReal - FOpt) +
        FOpt := by
  -- Local instance justification (segment owner reuse): the convex-segment theorem for `g`
  -- expects the properness package as an instance.
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  dsimp
  let θ : ℝ := 1 / fistaT hproblem x0 L (n + 1)
  let w : E := θ • xStar + (1 - θ) • fistaX hproblem x0 L (n + 1)
  have hxStar_eff :
      xStar ∈ effective_domain g :=
    fistaOptimalPoint_memEffectiveDomain (hproblem := hproblem) hxStar
  have hxsucc_eff :
      fistaX hproblem x0 L (n + 1) ∈ effective_domain g :=
    fistaPositiveIterate_memEffectiveDomain (hproblem := hproblem) (x0 := x0) (L := L)
      (show 1 ≤ n + 1 by exact Nat.succ_le_succ (Nat.zero_le n))
  have hθ_mem : θ ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [θ] using fistaOneDivMomentum_memIcc (hproblem := hproblem) (x0 := x0) (L := L) n
  have hθ_nonneg : 0 ≤ θ := hθ_mem.1
  have hθ_le_one : θ ≤ 1 := hθ_mem.2
  have hone_sub_nonneg : 0 ≤ 1 - θ := sub_nonneg.mpr hθ_le_one
  have hw_eff : w ∈ effective_domain g := by
    -- Reuse the feasibility lemma at the exact comparison point.
    simpa [θ, w] using
      fistaCombinationPoint_memEffectiveDomain
        (hproblem := hproblem) (x0 := x0) (L := L) (xStar := xStar) hxStar n
  have hw_obj :
      composite_model_objective f.toEReal g w =
        (((f w + (g w).toReal : ℝ)) : EReal) :=
    fista_objective_eq_real_of_mem_effective_domain hproblem hw_eff
  have hxsucc_obj :
      composite_model_objective f.toEReal g (fistaX hproblem x0 L (n + 1)) =
        (((f (fistaX hproblem x0 L (n + 1)) +
            (g (fistaX hproblem x0 L (n + 1))).toReal : ℝ)) : EReal) :=
    fista_objective_eq_real_of_mem_effective_domain hproblem hxsucc_eff
  have hxStar_obj :
      composite_model_objective f.toEReal g xStar =
        (((f xStar + (g xStar).toReal : ℝ)) : EReal) :=
    fista_objective_eq_real_of_mem_effective_domain hproblem hxStar_eff
  have hxStar_value :
      composite_model_objective f.toEReal g xStar = (FOpt : EReal) :=
    IsConvexCompositeSmoothMinimizationProblem.objective_eq_optimalValue_of_mem_optimalSet
      (h := hproblem.toIsConvexCompositeSmoothMinimizationProblem)
      hxStar
  have hxStar_toReal :
      f xStar + (g xStar).toReal = FOpt := by
    have hxStar_value' :
        (((f xStar + (g xStar).toReal : ℝ)) : EReal) = (FOpt : EReal) := by
      simpa [hxStar_obj] using hxStar_value
    exact EReal.coe_eq_coe_iff.mp hxStar_value'
  have hxsucc_toReal :
      (composite_model_objective f.toEReal g (fistaX hproblem x0 L (n + 1))).toReal =
        f (fistaX hproblem x0 L (n + 1)) +
          (g (fistaX hproblem x0 L (n + 1))).toReal := by
    rw [hxsucc_obj, EReal.toReal_coe]
  have hg_convexE :
      g w ≤
        (θ : EReal) * g xStar +
          ((1 - θ : ℝ) : EReal) * g (fistaX hproblem x0 L (n + 1)) := by
    -- Jensen's inequality for the nonsmooth term is read on the source combination point.
    simpa [w, θ, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
      (is_convex_function_iff_segment_ineq.mp hproblem.g_convex)
        xStar hxStar_eff (fistaX hproblem x0 L (n + 1)) hxsucc_eff hθ_mem
  have hg_convex :
      (g w).toReal ≤
        θ * (g xStar).toReal +
          (1 - θ) * (g (fistaX hproblem x0 L (n + 1))).toReal := by
    have hgw_val :
        g w = (((g w).toReal : ℝ) : EReal) :=
      (EReal.coe_toReal (mem_effective_domain.mp hw_eff).ne
        (hproblem.g_proper.ne_bot _)).symm
    have hgxStar_val :
        g xStar = (((g xStar).toReal : ℝ) : EReal) :=
      (EReal.coe_toReal (mem_effective_domain.mp hxStar_eff).ne
        (hproblem.g_proper.ne_bot _)).symm
    have hgxsucc_val :
        g (fistaX hproblem x0 L (n + 1)) =
          (((g (fistaX hproblem x0 L (n + 1))).toReal : ℝ) : EReal) :=
      (EReal.coe_toReal (mem_effective_domain.mp hxsucc_eff).ne
        (hproblem.g_proper.ne_bot _)).symm
    have hg_convex' :
        (((g w).toReal : ℝ) : EReal) ≤
          (((θ * (g xStar).toReal +
              (1 - θ) * (g (fistaX hproblem x0 L (n + 1))).toReal : ℝ)) : EReal) := by
      rw [hgw_val, hgxStar_val, hgxsucc_val] at hg_convexE
      simpa [EReal.coe_add, EReal.coe_mul] using hg_convexE
    exact EReal.coe_le_coe_iff.mp hg_convex'
  have hf_convex :
      f w ≤
        θ * f xStar + (1 - θ) * f (fistaX hproblem x0 L (n + 1)) := by
    -- The smooth term is convex on `Set.univ`, so it satisfies the same Jensen bound.
    simpa [w, θ, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
      hproblem.f_convex.2 (by simp) (by simp) hθ_nonneg hone_sub_nonneg (by nlinarith)
  have hw_toReal :
      (composite_model_objective f.toEReal g w).toReal = f w + (g w).toReal := by
    rw [hw_obj, EReal.toReal_coe]
  have hupper_real :
      (composite_model_objective f.toEReal g w).toReal ≤
        (1 - θ) *
            ((composite_model_objective f.toEReal g
                (fistaX hproblem x0 L (n + 1))).toReal - FOpt) +
          FOpt := by
    -- Add the convex bounds for `f` and `g`, then substitute `F(xStar) = FOpt`.
    rw [hw_toReal, hxsucc_toReal]
    nlinarith [hf_convex, hg_convex, hxStar_toReal]
  exact hupper_real

/-- Helper for Theorem 10.34: once both endpoints are finite, the accepted upper-model inequality
becomes the real prox-gap estimate used in the source Lyapunov proof. -/
private theorem fistaAcceptedProxGapReal
    {xPoint yPoint : E} {Lbar : PosReal}
    (hxPoint : xPoint ∈ effective_domain g)
    (haccepts :
      let xPlus := hproblem.proxPoint Lbar yPoint
      f xPlus ≤
        f yPoint +
          inner ℝ (∇ f yPoint) (xPlus - yPoint) +
          ((Lbar : ℝ) / 2) * ‖xPlus - yPoint‖ ^ (2 : ℕ)) :
    let yI := interior_effective_domain_point_of_real f yPoint
    let xPlus : E := hproblem.proxPoint Lbar yI
    ((Lbar : ℝ) / 2) * ‖xPoint - xPlus‖ ^ (2 : ℕ) -
        ((Lbar : ℝ) / 2) * ‖xPoint - yPoint‖ ^ (2 : ℕ) ≤
      (composite_model_objective f.toEReal g xPoint).toReal -
        (composite_model_objective f.toEReal g xPlus).toReal := by
  -- Local instance justification (prox-gap owner reuse): the accepted-step and prox-point owners
  -- are stated in the shared prox-gradient API, so we expose the regularity package from
  -- `hproblem` explicitly.
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  let yI := interior_effective_domain_point_of_real f yPoint
  let xPlus : E := hproblem.proxPoint Lbar yI
  have hxPlus :
      xPlus ∈ effective_domain g := by
    -- The prox-gradient step at the real base point always lands in `effective_domain g`.
    simpa [xPlus, yI, IsFastProximalGradientProblem.proxPoint] using
      (prox_grad_step_mem_effective_domain_g (f := f.toEReal) (g := g) yI Lbar)
  have haccepts' :
      proximal_gradient_backtracking_B2_accepts f.toEReal g Lbar yI := by
    -- Repackage the displayed upper model as the canonical B2 acceptance predicate.
    simpa [yI, IsFastProximalGradientProblem.proxPoint] using
      (proximal_gradient_backtracking_B2_accepts_iff_fista_upper_model f g Lbar yPoint).2
        haccepts
  have hfund :
      (((((Lbar : ℝ) / 2) * ‖xPoint - xPlus‖ ^ (2 : ℕ) -
          ((Lbar : ℝ) / 2) * ‖xPoint - yPoint‖ ^ (2 : ℕ) : ℝ)) : EReal) +
        ℓ[f.toEReal, xPoint, yI] ≤
        composite_model_objective f.toEReal g xPoint -
          composite_model_objective f.toEReal g xPlus := by
    -- Specialize the fundamental prox-gradient inequality at `xPoint` and the accepted point.
    simpa [xPlus, yI, IsFastProximalGradientProblem.proxPoint] using
      (fundamental_prox_grad_inequality
        (f := f.toEReal) (g := g) xPoint yI Lbar haccepts')
  have hxPoint_f :
      xPoint ∈ effective_domain f.toEReal := by
    let hconv := hproblem.toIsConvexCompositeSmoothMinimizationProblem
    exact interior_subset
      (hconv.g_effective_domain_subset_interior_f_effective_domain hxPoint)
  have hdefect_nonneg :
      (0 : EReal) ≤ ℓ[f.toEReal, xPoint, yI] := by
    -- Convexity lets us drop the linearization defect from the accepted-step estimate.
    simpa [yI] using
      (convexLinearizationDefect_nonneg
        (hproblem := hproblem.toIsConvexCompositeSmoothMinimizationProblem)
        (xPoint := xPoint) hxPoint_f yI)
  have hstepE :
      (((((Lbar : ℝ) / 2) * ‖xPoint - xPlus‖ ^ (2 : ℕ) -
          ((Lbar : ℝ) / 2) * ‖xPoint - yPoint‖ ^ (2 : ℕ) : ℝ)) : EReal) ≤
        composite_model_objective f.toEReal g xPoint -
          composite_model_objective f.toEReal g xPlus := by
    have hbase :
        (((((Lbar : ℝ) / 2) * ‖xPoint - xPlus‖ ^ (2 : ℕ) -
            ((Lbar : ℝ) / 2) * ‖xPoint - yPoint‖ ^ (2 : ℕ) : ℝ)) : EReal) ≤
          (((((Lbar : ℝ) / 2) * ‖xPoint - xPlus‖ ^ (2 : ℕ) -
              ((Lbar : ℝ) / 2) * ‖xPoint - yPoint‖ ^ (2 : ℕ) : ℝ)) : EReal) +
            ℓ[f.toEReal, xPoint, yI] := by
      exact le_add_of_nonneg_right hdefect_nonneg
    exact le_trans hbase hfund
  have hxPoint_obj :
      composite_model_objective f.toEReal g xPoint =
        (((f xPoint + (g xPoint).toReal : ℝ)) : EReal) :=
    fista_objective_eq_real_of_mem_effective_domain hproblem hxPoint
  have hxPlus_obj :
      composite_model_objective f.toEReal g xPlus =
        (((f xPlus + (g xPlus).toReal : ℝ)) : EReal) :=
    fista_objective_eq_real_of_mem_effective_domain hproblem hxPlus
  have hxPoint_toReal :
      (composite_model_objective f.toEReal g xPoint).toReal =
        f xPoint + (g xPoint).toReal := by
    rw [hxPoint_obj, EReal.toReal_coe]
  have hxPlus_toReal :
      (composite_model_objective f.toEReal g xPlus).toReal =
        f xPlus + (g xPlus).toReal := by
    rw [hxPlus_obj, EReal.toReal_coe]
  have hdiff :
      composite_model_objective f.toEReal g xPoint -
          composite_model_objective f.toEReal g xPlus =
        ((((composite_model_objective f.toEReal g xPoint).toReal -
            (composite_model_objective f.toEReal g xPlus).toReal : ℝ)) : EReal) := by
    rw [hxPoint_toReal, hxPlus_toReal, hxPoint_obj, hxPlus_obj]
    simp [EReal.coe_sub]
  have hstepE' := hstepE
  -- Rewrite the finite objective difference into the canonical real subtraction before stripping
  -- the final `EReal` coercion.
  rw [hdiff] at hstepE'
  exact EReal.coe_le_coe_iff.mp hstepE'

/-- Helper for Theorem 10.34: the first source energy is bounded by the initial distance to an
optimizer on the exact `2 / L_0` source surface. -/
private theorem fistaInitialEnergyBound
    (hrule : hproblem.SublinearRateStepsizeRule
      (fistaY hproblem x0 L) L α)
    (hxStar : xStar ∈ XStar) :
    let vR : ℕ → ℝ :=
      fun n ↦ (composite_model_objective f.toEReal g
        (fistaX hproblem x0 L n)).toReal - FOpt
    ‖fista_lyapunov_residual hproblem x0 L xStar 1‖ ^ (2 : ℕ) +
        (2 / (L 0 : ℝ)) * fistaT hproblem x0 L 0 ^ (2 : ℕ) * vR 1 ≤
      ‖x0 - xStar‖ ^ (2 : ℕ) := by
  -- Local instance justification (owner normalization): the public `x/y/t` view lemmas are stated
  -- for the canonical FISTA owner and require the regularity package as explicit instances.
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  dsimp
  have hL0_pos : 0 < (L 0 : ℝ) := PosReal.coe_pos (L 0)
  have hxStar_eff :
      xStar ∈ effective_domain g :=
    fistaOptimalPoint_memEffectiveDomain (hproblem := hproblem) hxStar
  have hx1_eff :
      fistaX hproblem x0 L 1 ∈ effective_domain g :=
    fistaPositiveIterate_memEffectiveDomain (hproblem := hproblem) (x0 := x0) (L := L)
      (show 1 ≤ 1 by simp)
  have hxStar_value :
      composite_model_objective f.toEReal g xStar = (FOpt : EReal) :=
    IsConvexCompositeSmoothMinimizationProblem.objective_eq_optimalValue_of_mem_optimalSet
      (h := hproblem.toIsConvexCompositeSmoothMinimizationProblem)
      hxStar
  have hxStar_toReal :
      (composite_model_objective f.toEReal g xStar).toReal = FOpt := by
    rw [hxStar_value, EReal.toReal_coe]
  have hxStar_sum_toReal :
      f xStar + (g xStar).toReal = FOpt := by
    rw [← hxStar_toReal]
    rw [fista_objective_eq_real_of_mem_effective_domain hproblem (xPoint := xStar) hxStar_eff,
      EReal.toReal_coe]
  have hxStar_obj_toReal :
      (↑(f xStar) + g xStar).toReal = FOpt := by
    have hgx_top : g xStar ≠ ⊤ := (mem_effective_domain.mp hxStar_eff).ne
    have hgx_bot : g xStar ≠ ⊥ := hproblem.g_proper.ne_bot _
    rw [EReal.toReal_add (EReal.coe_ne_top _) (EReal.coe_ne_bot _) hgx_top hgx_bot]
    exact hxStar_sum_toReal
  have haccepted0 :
      ((L 0 : ℝ) / 2) * ‖xStar - fistaX hproblem x0 L 1‖ ^ (2 : ℕ) -
          ((L 0 : ℝ) / 2) * ‖xStar - x0‖ ^ (2 : ℕ) ≤
        FOpt - (composite_model_objective f.toEReal g (fistaX hproblem x0 L 1)).toReal := by
    have hgap0 :=
      fistaAcceptedProxGapReal
        (hproblem := hproblem) (xPoint := xStar) (yPoint := x0) (Lbar := L 0)
        hxStar_eff
        (hproblem.sublinearRateStepsizeRule_accepts hrule 0)
    -- Normalize the optimizer value, the initial base point, and the first prox step `x¹`.
    simpa [hxStar_obj_toReal, interior_effective_domain_point_of_real,
      fistaX, fistaY, fista_y_zero, fista_x_succ,
      IsFastProximalGradientProblem.proxPoint, norm_sub_rev] using hgap0
  have hbase_x1 :
      ‖fistaX hproblem x0 L 1 - xStar‖ ^ (2 : ℕ) +
          (2 / (L 0 : ℝ)) *
            ((composite_model_objective f.toEReal g (fistaX hproblem x0 L 1)).toReal - FOpt) ≤
        ‖x0 - xStar‖ ^ (2 : ℕ) := by
    have hbase_scaled :
        ((L 0 : ℝ) / 2) *
            (‖xStar - fistaX hproblem x0 L 1‖ ^ (2 : ℕ) +
              (2 / (L 0 : ℝ)) *
                ((composite_model_objective f.toEReal g
                    (fistaX hproblem x0 L 1)).toReal - FOpt)) ≤
          ((L 0 : ℝ) / 2) * ‖xStar - x0‖ ^ (2 : ℕ) := by
      have hbase_scaled' :
          ((L 0 : ℝ) / 2) * ‖xStar - fistaX hproblem x0 L 1‖ ^ (2 : ℕ) +
              ((composite_model_objective f.toEReal g
                  (fistaX hproblem x0 L 1)).toReal - FOpt) ≤
            ((L 0 : ℝ) / 2) * ‖xStar - x0‖ ^ (2 : ℕ) := by
        -- This is the accepted prox-gap inequality with the objective drop moved to the left.
        nlinarith [haccepted0]
      have hscale_eq :
          ((L 0 : ℝ) / 2) *
              (‖xStar - fistaX hproblem x0 L 1‖ ^ (2 : ℕ) +
                (2 / (L 0 : ℝ)) *
                  ((composite_model_objective f.toEReal g
                      (fistaX hproblem x0 L 1)).toReal - FOpt)) =
            ((L 0 : ℝ) / 2) * ‖xStar - fistaX hproblem x0 L 1‖ ^ (2 : ℕ) +
              ((composite_model_objective f.toEReal g
                  (fistaX hproblem x0 L 1)).toReal - FOpt) := by
        field_simp [hL0_pos.ne']
      rw [hscale_eq]
      exact hbase_scaled'
    have hcoef_pos : 0 < ((L 0 : ℝ) / 2) := by
      positivity
    have hbase_rev :
        ‖xStar - fistaX hproblem x0 L 1‖ ^ (2 : ℕ) +
            (2 / (L 0 : ℝ)) *
              ((composite_model_objective f.toEReal g
                  (fistaX hproblem x0 L 1)).toReal - FOpt) ≤
          ‖xStar - x0‖ ^ (2 : ℕ) := by
      nlinarith [hbase_scaled, hcoef_pos]
    -- Replace the reversed norms by the source spelling used in the theorem statement.
    simpa [norm_sub_rev] using hbase_rev
  -- Collapse `u¹ = x¹ - xStar` and `t₀ = 1` to recover the displayed source energy.
  simpa [fista_lyapunov_residual_one, fistaT, fista_t_zero, norm_sub_rev] using hbase_x1

/-- Helper for Theorem 10.34: the source comparison point at step `n + 1` satisfies the exact
current-step objective-gap estimate on the real layer. -/
theorem fistaCurrentStepGapUpperBound
    (hxStar : xStar ∈ XStar)
    (n : ℕ) :
    let vR : ℕ → ℝ :=
      fun m ↦ (composite_model_objective f.toEReal g
        (fistaX hproblem x0 L m)).toReal - FOpt
    let θ : ℝ := 1 / fistaT hproblem x0 L (n + 1)
    let w : E := θ • xStar + (1 - θ) • fistaX hproblem x0 L (n + 1)
    (composite_model_objective f.toEReal g w).toReal -
        (composite_model_objective f.toEReal g
          (fistaX hproblem x0 L (n + 2))).toReal ≤
      (1 - θ) * vR (n + 1) - vR (n + 2) := by
  dsimp
  let vR : ℕ → ℝ :=
    fun m ↦ (composite_model_objective f.toEReal g
      (fistaX hproblem x0 L m)).toReal - FOpt
  let θ : ℝ := 1 / fistaT hproblem x0 L (n + 1)
  let w : E := θ • xStar + (1 - θ) • fistaX hproblem x0 L (n + 1)
  have hw_upper :
      (composite_model_objective f.toEReal g w).toReal ≤
        (1 - θ) * vR (n + 1) + FOpt := by
    -- First bound the comparison-point objective by convexity at the exact source point.
    simpa [vR, θ, w] using
      (fistaCombinationObjectiveUpperBoundReal
        (hproblem := hproblem) (x0 := x0) (L := L) (xStar := xStar) hxStar n)
  -- Then rewrite the terminal objective through the shifted real gap `vR (n + 2)`.
  dsimp [vR] at hw_upper ⊢
  linarith

/-- Helper for Theorem 10.34: the FISTA extrapolation formula gives the exact predecessor
transport from the pre-step vector to the previous residual. -/
theorem fistaPrestepVector_eq_previousResidual
    (n : ℕ) :
    fistaT hproblem x0 L (n + 1) • fistaY hproblem x0 L (n + 1) -
        (xStar + (fistaT hproblem x0 L (n + 1) - 1) •
          fistaX hproblem x0 L (n + 1)) =
      fista_lyapunov_residual hproblem x0 L xStar (n + 1) := by
  -- Local instance justification (owner reuse): the explicit FISTA `x/y/t` view lemmas below are
  -- stated with the regularity package supplied by `hproblem` as ambient instances.
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  have ht_one_le : (1 : ℝ) ≤ fistaT hproblem x0 L (n + 1) := by
    have hone_le_half :
        (1 : ℝ) ≤ (((n + 1 : ℕ) : ℝ) + 2) / 2 := by
      have hn1_nonneg :
          (0 : ℝ) ≤ (((n + 1 : ℕ) : ℝ)) := by
        exact_mod_cast Nat.zero_le (n + 1)
      nlinarith
    exact le_trans hone_le_half <| by
      simpa [fistaT] using
        (fista_t_lower_bound (f := f) (g := g) (x0 := x0) (L := L) (k := n + 1))
  have ht_pos : 0 < fistaT hproblem x0 L (n + 1) := by
    exact lt_of_lt_of_le zero_lt_one ht_one_le
  have hmul_x :
      fistaT hproblem x0 L (n + 1) *
          ((fistaT hproblem x0 L n - 1) / fistaT hproblem x0 L (n + 1)) =
        fistaT hproblem x0 L n - 1 := by
    field_simp [ht_pos.ne']
  have hy_succ :
      fistaY hproblem x0 L (n + 1) =
        fistaX hproblem x0 L (n + 1) +
          ((fistaT hproblem x0 L n - 1) / fistaT hproblem x0 L (n + 1)) •
            (fistaX hproblem x0 L (n + 1) - fistaX hproblem x0 L n) := by
    simpa [fistaY, fistaX, fistaT] using
      (fista_y_succ (f := f) (g := g) (x0 := x0) (L := L) n)
  -- Route correction: normalize the pre-step vector directly through `fista_y_succ` on the honest
  -- same-index residual surface instead of reopening the older packet transport route.
  rw [hy_succ]
  simp_rw [smul_add, smul_sub, smul_smul]
  rw [hmul_x]
  simp_rw [sub_eq_add_neg, fista_lyapunov_residual]
  module

/-- Helper for Theorem 10.34: combining the accepted prox-gap with the current-step objective
bound yields the exact shared-denominator Lyapunov balance. -/
theorem fistaAcceptedStepEnergyBalance
    (hrule : hproblem.SublinearRateStepsizeRule
      (fistaY hproblem x0 L) L α)
    (hxStar : xStar ∈ XStar)
    (n : ℕ) :
    let vR : ℕ → ℝ :=
      fun m ↦ (composite_model_objective f.toEReal g
        (fistaX hproblem x0 L m)).toReal - FOpt
    ‖fista_lyapunov_residual hproblem x0 L xStar (n + 2)‖ ^ (2 : ℕ) +
        (2 / (L (n + 1) : ℝ)) *
          fistaT hproblem x0 L (n + 1) ^ (2 : ℕ) * vR (n + 2) ≤
      ‖fista_lyapunov_residual hproblem x0 L xStar (n + 1)‖ ^ (2 : ℕ) +
        (2 / (L (n + 1) : ℝ)) *
          fistaT hproblem x0 L n ^ (2 : ℕ) * vR (n + 1) := by
  -- Local instance justification (owner reuse): the explicit `x/y/t` FISTA owner lemmas used
  -- below are stated with the `g`-regularity package as ambient instance data.
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  dsimp
  let vR : ℕ → ℝ :=
    fun m ↦ (composite_model_objective f.toEReal g
      (fistaX hproblem x0 L m)).toReal - FOpt
  let t : ℝ := fistaT hproblem x0 L (n + 1)
  let θ : ℝ := 1 / t
  let w : E := θ • xStar + (1 - θ) • fistaX hproblem x0 L (n + 1)
  have hL_pos : 0 < (L (n + 1) : ℝ) := PosReal.coe_pos (L (n + 1))
  have ht_one_le : (1 : ℝ) ≤ t := by
    have hone_le_half :
        (1 : ℝ) ≤ (((n + 1 : ℕ) : ℝ) + 2) / 2 := by
      have hn1_nonneg :
          (0 : ℝ) ≤ (((n + 1 : ℕ) : ℝ)) := by
        exact_mod_cast Nat.zero_le (n + 1)
      nlinarith
    exact le_trans hone_le_half <| by
      simpa [t, fistaT] using
        (fista_t_lower_bound (f := f) (g := g) (x0 := x0) (L := L) (k := n + 1))
  have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht_one_le
  have hw_eff :
      w ∈ effective_domain g := by
    -- The accepted prox-gap is applied at the same source comparison point.
    simpa [t, θ, w] using
      (fistaCombinationPoint_memEffectiveDomain
        (hproblem := hproblem) (x0 := x0) (L := L) (xStar := xStar) hxStar n)
  have hprox :
      ((L (n + 1) : ℝ) / 2) * ‖w - fistaX hproblem x0 L (n + 2)‖ ^ (2 : ℕ) -
          ((L (n + 1) : ℝ) / 2) * ‖w - fistaY hproblem x0 L (n + 1)‖ ^ (2 : ℕ) ≤
        (composite_model_objective f.toEReal g w).toReal -
          (composite_model_objective f.toEReal g
            (fistaX hproblem x0 L (n + 2))).toReal := by
    -- Read the accepted prox-gap on the real layer at step `n + 1`.
    simpa [w, fistaX, fistaY, interior_effective_domain_point_of_real,
      IsFastProximalGradientProblem.proxPoint, fista_x_succ, Nat.add_assoc] using
      (fistaAcceptedProxGapReal
        (hproblem := hproblem)
        (xPoint := w)
        (yPoint := fistaY hproblem x0 L (n + 1))
        (Lbar := L (n + 1))
        hw_eff
        (hproblem.sublinearRateStepsizeRule_accepts hrule (n + 1)))
  have hobj :
      (composite_model_objective f.toEReal g w).toReal -
          (composite_model_objective f.toEReal g
            (fistaX hproblem x0 L (n + 2))).toReal ≤
        (1 - θ) * vR (n + 1) - vR (n + 2) := by
    -- The current-step objective side is already packaged in the source normal form.
    simpa [vR, t, θ, w] using
      (fistaCurrentStepGapUpperBound
        (hproblem := hproblem) (x0 := x0) (L := L) (xStar := xStar) hxStar n)
  have hraw :
      ((L (n + 1) : ℝ) / 2) * ‖w - fistaX hproblem x0 L (n + 2)‖ ^ (2 : ℕ) -
          ((L (n + 1) : ℝ) / 2) * ‖w - fistaY hproblem x0 L (n + 1)‖ ^ (2 : ℕ) ≤
        (1 - θ) * vR (n + 1) - vR (n + 2) := by
    -- Compose the accepted prox-gap with the current-step objective estimate.
    exact le_trans hprox hobj
  have hscaled :
      t ^ (2 : ℕ) *
          (((L (n + 1) : ℝ) / 2) * ‖w - fistaX hproblem x0 L (n + 2)‖ ^ (2 : ℕ) -
            ((L (n + 1) : ℝ) / 2) * ‖w - fistaY hproblem x0 L (n + 1)‖ ^ (2 : ℕ)) ≤
        t ^ (2 : ℕ) * ((1 - θ) * vR (n + 1) - vR (n + 2)) := by
    -- Scale the whole inequality by `t_(n+1)^2`, matching the source Lyapunov normalization.
    exact mul_le_mul_of_nonneg_left hraw (by positivity)
  have hw_scaled :
      t • w = xStar + (t - 1) • fistaX hproblem x0 L (n + 1) := by
    have htθ : t * θ = 1 := by
      dsimp [θ]
      field_simp [ht_pos.ne']
    have ht_one_sub : t * (1 - θ) = t - 1 := by
      dsimp [θ]
      field_simp [ht_pos.ne']
    -- Rewrite the scaled comparison point into the exact source affine surface.
    calc
      t • w = t • (θ • xStar + (1 - θ) • fistaX hproblem x0 L (n + 1)) := by rfl
      _ = (t * θ) • xStar + (t * (1 - θ)) • fistaX hproblem x0 L (n + 1) := by
        simp [smul_add, smul_smul]
      _ = xStar + (t - 1) • fistaX hproblem x0 L (n + 1) := by
        rw [htθ, ht_one_sub, one_smul]
  have hpost_vector :
      t • (w - fistaX hproblem x0 L (n + 2)) =
        -fista_lyapunov_residual hproblem x0 L xStar (n + 2) := by
    -- The post-step vector is exactly the next residual, up to sign.
    calc
      t • (w - fistaX hproblem x0 L (n + 2)) =
          t • w - t • fistaX hproblem x0 L (n + 2) := by
        simp [smul_sub]
      _ = (xStar + (t - 1) • fistaX hproblem x0 L (n + 1)) -
            t • fistaX hproblem x0 L (n + 2) := by
        rw [hw_scaled]
      _ = -(t • fistaX hproblem x0 L (n + 2) -
            (xStar + (t - 1) • fistaX hproblem x0 L (n + 1))) := by
        abel
      _ = -fista_lyapunov_residual hproblem x0 L xStar (n + 2) := by
        simp [fista_lyapunov_residual, t]
  have hpre_vector :
      t • (w - fistaY hproblem x0 L (n + 1)) =
        -fista_lyapunov_residual hproblem x0 L xStar (n + 1) := by
    -- The pre-step vector collapses to the previous residual via the FISTA extrapolation rule.
    calc
      t • (w - fistaY hproblem x0 L (n + 1)) =
          t • w - t • fistaY hproblem x0 L (n + 1) := by
        simp [smul_sub]
      _ = (xStar + (t - 1) • fistaX hproblem x0 L (n + 1)) -
            t • fistaY hproblem x0 L (n + 1) := by
        rw [hw_scaled]
      _ = -(t • fistaY hproblem x0 L (n + 1) -
            (xStar + (t - 1) • fistaX hproblem x0 L (n + 1))) := by
        abel
      _ = -fista_lyapunov_residual hproblem x0 L xStar (n + 1) := by
        simpa using congrArg (fun v : E ↦ -v)
          (fistaPrestepVector_eq_previousResidual
            (hproblem := hproblem) (x0 := x0) (L := L) (xStar := xStar) n)
  have hpost :
      t ^ (2 : ℕ) * ‖w - fistaX hproblem x0 L (n + 2)‖ ^ (2 : ℕ) =
        ‖fista_lyapunov_residual hproblem x0 L xStar (n + 2)‖ ^ (2 : ℕ) := by
    -- Rewrite the post-step norm into the residual norm at index `n + 2`.
    calc
      t ^ (2 : ℕ) * ‖w - fistaX hproblem x0 L (n + 2)‖ ^ (2 : ℕ) =
          ‖t • (w - fistaX hproblem x0 L (n + 2))‖ ^ (2 : ℕ) := by
        rw [norm_smul]
        have ht_norm : ‖t‖ = t := Real.norm_of_nonneg (le_of_lt ht_pos)
        rw [ht_norm]
        ring
      _ = ‖fista_lyapunov_residual hproblem x0 L xStar (n + 2)‖ ^ (2 : ℕ) := by
        rw [hpost_vector]
        simp
  have hpre :
      t ^ (2 : ℕ) * ‖w - fistaY hproblem x0 L (n + 1)‖ ^ (2 : ℕ) =
        ‖fista_lyapunov_residual hproblem x0 L xStar (n + 1)‖ ^ (2 : ℕ) := by
    -- Rewrite the pre-step norm into the previous residual norm.
    calc
      t ^ (2 : ℕ) * ‖w - fistaY hproblem x0 L (n + 1)‖ ^ (2 : ℕ) =
          ‖t • (w - fistaY hproblem x0 L (n + 1))‖ ^ (2 : ℕ) := by
        rw [norm_smul]
        have ht_norm : ‖t‖ = t := Real.norm_of_nonneg (le_of_lt ht_pos)
        rw [ht_norm]
        ring
      _ = ‖fista_lyapunov_residual hproblem x0 L xStar (n + 1)‖ ^ (2 : ℕ) := by
        rw [hpre_vector]
        simp
  have hcoef_gap :
      t ^ (2 : ℕ) * (1 - θ) = fistaT hproblem x0 L n ^ (2 : ℕ) := by
    have ht_ne : t ≠ 0 := ne_of_gt ht_pos
    -- Normalize the source scalar coefficient `t_(n+1)^2 (1 - 1 / t_(n+1))`.
    calc
      t ^ (2 : ℕ) * (1 - θ) = t ^ (2 : ℕ) - t := by
        dsimp [θ]
        field_simp [pow_two, ht_ne]
      _ = fistaT hproblem x0 L n ^ (2 : ℕ) := by
        simpa [t] using
          (fistaMomentumSqSub_eq_prevSq
            (hproblem := hproblem) (x0 := x0) (L := L) n)
  have hscaled' :
      ((L (n + 1) : ℝ) / 2) *
          (t ^ (2 : ℕ) * ‖w - fistaX hproblem x0 L (n + 2)‖ ^ (2 : ℕ)) -
          ((L (n + 1) : ℝ) / 2) *
            (t ^ (2 : ℕ) * ‖w - fistaY hproblem x0 L (n + 1)‖ ^ (2 : ℕ)) ≤
        (t ^ (2 : ℕ) * (1 - θ)) * vR (n + 1) -
          t ^ (2 : ℕ) * vR (n + 2) := by
    -- Expand the scaled inequality so the norm and scalar transports can be rewritten separately.
    simpa [sub_eq_add_neg, mul_add, add_mul, mul_sub, sub_mul,
      mul_assoc, mul_left_comm, mul_comm] using hscaled
  have hrewritten :
      ((L (n + 1) : ℝ) / 2) *
          ‖fista_lyapunov_residual hproblem x0 L xStar (n + 2)‖ ^ (2 : ℕ) -
          ((L (n + 1) : ℝ) / 2) *
            ‖fista_lyapunov_residual hproblem x0 L xStar (n + 1)‖ ^ (2 : ℕ) ≤
        fistaT hproblem x0 L n ^ (2 : ℕ) * vR (n + 1) -
          fistaT hproblem x0 L (n + 1) ^ (2 : ℕ) * vR (n + 2) := by
    -- Put the scaled balance into the exact residual and momentum notation.
    have hrewritten' := hscaled'
    rw [hpost, hpre, hcoef_gap] at hrewritten'
    simpa [t] using hrewritten'
  have hbalance_scaled :
      ((L (n + 1) : ℝ) / 2) *
          (‖fista_lyapunov_residual hproblem x0 L xStar (n + 2)‖ ^ (2 : ℕ) +
            (2 / (L (n + 1) : ℝ)) *
              fistaT hproblem x0 L (n + 1) ^ (2 : ℕ) * vR (n + 2)) ≤
        ((L (n + 1) : ℝ) / 2) *
          (‖fista_lyapunov_residual hproblem x0 L xStar (n + 1)‖ ^ (2 : ℕ) +
            (2 / (L (n + 1) : ℝ)) *
              fistaT hproblem x0 L n ^ (2 : ℕ) * vR (n + 1)) := by
    have hleft_eq :
        ((L (n + 1) : ℝ) / 2) *
            (‖fista_lyapunov_residual hproblem x0 L xStar (n + 2)‖ ^ (2 : ℕ) +
              (2 / (L (n + 1) : ℝ)) *
                fistaT hproblem x0 L (n + 1) ^ (2 : ℕ) * vR (n + 2)) =
          ((L (n + 1) : ℝ) / 2) *
              ‖fista_lyapunov_residual hproblem x0 L xStar (n + 2)‖ ^ (2 : ℕ) +
            fistaT hproblem x0 L (n + 1) ^ (2 : ℕ) * vR (n + 2) := by
      field_simp [hL_pos.ne']
    have hright_eq :
        ((L (n + 1) : ℝ) / 2) *
            (‖fista_lyapunov_residual hproblem x0 L xStar (n + 1)‖ ^ (2 : ℕ) +
              (2 / (L (n + 1) : ℝ)) *
                fistaT hproblem x0 L n ^ (2 : ℕ) * vR (n + 1)) =
          ((L (n + 1) : ℝ) / 2) *
              ‖fista_lyapunov_residual hproblem x0 L xStar (n + 1)‖ ^ (2 : ℕ) +
            fistaT hproblem x0 L n ^ (2 : ℕ) * vR (n + 1) := by
      field_simp [hL_pos.ne']
    rw [hleft_eq, hright_eq]
    nlinarith [hrewritten]
  have hcoef_pos : 0 < ((L (n + 1) : ℝ) / 2) := by
    positivity
  -- Divide the source balance by `L_(n+1) / 2` to recover the shared-denominator energy step.
  exact le_of_mul_le_mul_left hbalance_scaled hcoef_pos

/-- Helper for Theorem 10.34: the exact FISTA Lyapunov energy contracts in one step. -/
theorem fistaEnergyStep
    (hrule : hproblem.SublinearRateStepsizeRule
      (fistaY hproblem x0 L) L α)
    (hxStar : xStar ∈ XStar)
    (n : ℕ) :
    let vR : ℕ → ℝ :=
      fun m ↦ (composite_model_objective f.toEReal g
        (fistaX hproblem x0 L m)).toReal - FOpt
    let ER : ℕ → ℝ :=
      fun m ↦
        ‖fista_lyapunov_residual hproblem x0 L xStar (m + 1)‖ ^ (2 : ℕ) +
          (2 / (L m : ℝ)) * fistaT hproblem x0 L m ^ (2 : ℕ) * vR (m + 1)
    ER (n + 1) ≤ ER n := by
  dsimp
  let vR : ℕ → ℝ :=
    fun m ↦ (composite_model_objective f.toEReal g
      (fistaX hproblem x0 L m)).toReal - FOpt
  let ER : ℕ → ℝ :=
    fun m ↦
      ‖fista_lyapunov_residual hproblem x0 L xStar (m + 1)‖ ^ (2 : ℕ) +
        (2 / (L m : ℝ)) * fistaT hproblem x0 L m ^ (2 : ℕ) * vR (m + 1)
  have hbalance :
      ‖fista_lyapunov_residual hproblem x0 L xStar (n + 2)‖ ^ (2 : ℕ) +
          (2 / (L (n + 1) : ℝ)) *
            fistaT hproblem x0 L (n + 1) ^ (2 : ℕ) * vR (n + 2) ≤
        ‖fista_lyapunov_residual hproblem x0 L xStar (n + 1)‖ ^ (2 : ℕ) +
          (2 / (L (n + 1) : ℝ)) *
            fistaT hproblem x0 L n ^ (2 : ℕ) * vR (n + 1) := by
    -- Start from the raw shared-denominator Lyapunov balance.
    simpa [vR] using
      (fistaAcceptedStepEnergyBalance
        (hproblem := hproblem) (x0 := x0) (L := L) (α := α)
        (xStar := xStar) hrule hxStar n)
  have hstepsize_mono :
      (L n : ℝ) ≤ (L (n + 1) : ℝ) :=
    fistaStepsizeMonotone
      (hproblem := hproblem) (x0 := x0) (L := L) (α := α) hrule n
  have hgap_nonneg :
      0 ≤ vR (n + 1) := by
    have hgap_nonneg :=
      fista_positive_iterate_gap_nonneg
        (hproblem := hproblem) (x0 := x0) (L := L)
        (n := n + 1)
        (show 1 ≤ n + 1 by exact Nat.succ_le_succ (Nat.zero_le n))
    simpa [vR] using hgap_nonneg
  have htransport :
      (2 / (L (n + 1) : ℝ)) * fistaT hproblem x0 L n ^ (2 : ℕ) * vR (n + 1) ≤
        (2 / (L n : ℝ)) * fistaT hproblem x0 L n ^ (2 : ℕ) * vR (n + 1) := by
    have hLn_pos : 0 < (L n : ℝ) := PosReal.coe_pos (L n)
    have hrecip :
        2 / (L (n + 1) : ℝ) ≤ 2 / (L n : ℝ) := by
      have hone_div :
          1 / (L (n + 1) : ℝ) ≤ 1 / (L n : ℝ) := by
        exact one_div_le_one_div_of_le hLn_pos hstepsize_mono
      have htwo_mul :
          (2 : ℝ) * (1 / (L (n + 1) : ℝ)) ≤
            (2 : ℝ) * (1 / (L n : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hone_div (by positivity)
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using htwo_mul
    have hterm_nonneg :
        0 ≤ fistaT hproblem x0 L n ^ (2 : ℕ) * vR (n + 1) := by
      exact mul_nonneg (by positivity) hgap_nonneg
    -- Only the right-hand denominator changes when transporting the energy from `L_(n+1)` to
    -- `L_n`.
    simpa [mul_assoc] using mul_le_mul_of_nonneg_right hrecip hterm_nonneg
  have hfinal :
      ER (n + 1) ≤
        ‖fista_lyapunov_residual hproblem x0 L xStar (n + 1)‖ ^ (2 : ℕ) +
          (2 / (L n : ℝ)) * fistaT hproblem x0 L n ^ (2 : ℕ) * vR (n + 1) := by
    -- Compose the raw balance with the one-line denominator transport.
    nlinarith [hbalance, htransport]
  simpa [ER] using hfinal

/-- Theorem 10.34: under Assumption 10.31, FISTA satisfies the textbook
`O(1 / k^2)` objective-gap bound. -/
theorem fista_objective_gap_le_two_alpha_Lf_dist_sq_div_sq
    (hrule : hproblem.SublinearRateStepsizeRule
      (fistaY hproblem x0 L) L α)
    (hxStar : xStar ∈ XStar) (k : ℕ) (hk : 1 ≤ k) :
    composite_model_objective f.toEReal g
        (fistaX hproblem x0 L k) - (FOpt : EReal) ≤
      (((2 * α * (Lf : ℝ) * ‖x0 - xStar‖ ^ (2 : ℕ)) / (k + 1 : ℝ) ^ (2 : ℕ) : ℝ) : EReal) := by
  -- Local instance justification (owner reuse): the explicit `x/y/t` FISTA owner lemmas used in
  -- the final telescope are stated with the `g`-regularity package as ambient instance data.
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  obtain ⟨K, rfl⟩ := Nat.exists_eq_add_of_le hk
  let vR : ℕ → ℝ :=
    fun n ↦ (composite_model_objective f.toEReal g
      (fistaX hproblem x0 L n)).toReal - FOpt
  let ER : ℕ → ℝ :=
    fun n ↦
      ‖fista_lyapunov_residual hproblem x0 L xStar (n + 1)‖ ^ (2 : ℕ) +
        (2 / (L n : ℝ)) * fistaT hproblem x0 L n ^ (2 : ℕ) * vR (n + 1)
  have henergy_le_zero : ∀ n, ER n ≤ ER 0 := by
    intro n
    induction n with
    | zero =>
        exact le_rfl
    | succ n ihn =>
        -- Iterate the one-step Lyapunov contraction from `ER n` back to the initial energy.
        exact le_trans
          (by
            simpa [ER, vR] using
              (fistaEnergyStep
                (hproblem := hproblem) (x0 := x0) (L := L) (α := α)
                (xStar := xStar) hrule hxStar n))
          ihn
  have hinitial :
      ER 0 ≤ ‖x0 - xStar‖ ^ (2 : ℕ) := by
    -- The first Lyapunov energy is already bounded by the starting distance to the optimizer.
    simpa [ER, vR] using
      (fistaInitialEnergyBound
        (hproblem := hproblem) (x0 := x0) (L := L) (α := α) (xStar := xStar)
        hrule hxStar)
  have henergyK :
      ER K ≤ ‖x0 - xStar‖ ^ (2 : ℕ) := by
    exact le_trans (henergy_le_zero K) hinitial
  have hgap_term :
      (2 / (L K : ℝ)) * fistaT hproblem x0 L K ^ (2 : ℕ) * vR (K + 1) ≤
        ‖x0 - xStar‖ ^ (2 : ℕ) := by
    have hdrop :
        (2 / (L K : ℝ)) * fistaT hproblem x0 L K ^ (2 : ℕ) * vR (K + 1) ≤ ER K := by
      -- Drop the nonnegative residual norm from the Lyapunov energy.
      dsimp [ER]
      have hres_nonneg :
          0 ≤ ‖fista_lyapunov_residual hproblem x0 L xStar (K + 1)‖ ^ (2 : ℕ) := by
        positivity
      nlinarith
    exact le_trans hdrop henergyK
  have hstepsize_cap :
      (L K : ℝ) ≤ α * (Lf : ℝ) := by
    exact
      fistaSublinearRateStepsizeBound
        (hproblem := hproblem) (x0 := x0) (L := L) (α := α) hrule K
  have hvR_nonneg : 0 ≤ vR (K + 1) := by
    -- The final real objective gap is nonnegative on positive iterates.
    have hvR_nonneg :=
      fista_positive_iterate_gap_nonneg
        (hproblem := hproblem) (x0 := x0) (L := L)
        (n := K + 1)
        (show 1 ≤ K + 1 by exact Nat.succ_le_succ (Nat.zero_le K))
    simpa [vR] using hvR_nonneg
  have hscaled_gap :
      2 * fistaT hproblem x0 L K ^ (2 : ℕ) * vR (K + 1) ≤
        α * (Lf : ℝ) * ‖x0 - xStar‖ ^ (2 : ℕ) := by
    have hmul :
        (L K : ℝ) *
            ((2 / (L K : ℝ)) * fistaT hproblem x0 L K ^ (2 : ℕ) * vR (K + 1)) ≤
          (L K : ℝ) * ‖x0 - xStar‖ ^ (2 : ℕ) := by
      exact mul_le_mul_of_nonneg_left hgap_term (le_of_lt (PosReal.coe_pos (L K)))
    have hmul' :
        2 * fistaT hproblem x0 L K ^ (2 : ℕ) * vR (K + 1) ≤
          (L K : ℝ) * ‖x0 - xStar‖ ^ (2 : ℕ) := by
      -- Clear the positive denominator `L_K` from the gap estimate.
      have hLK_pos : 0 < (L K : ℝ) := PosReal.coe_pos (L K)
      have hmul' := hmul
      field_simp [hLK_pos.ne'] at hmul'
      simpa [mul_assoc, mul_left_comm, mul_comm] using hmul'
    exact le_trans hmul' <|
      mul_le_mul_of_nonneg_right hstepsize_cap (by positivity)
  have hmomentum_lower :
      (((K : ℝ) + 2) / 2) ≤ fistaT hproblem x0 L K := by
    exact
      fista_t_lower_bound
        (f := f) (g := g) (x0 := x0) (L := L) (k := K)
  have hmomentum_sq :
      ((K : ℝ) + 2) ^ (2 : ℕ) ≤ 4 * fistaT hproblem x0 L K ^ (2 : ℕ) := by
    -- Square the standard lower bound `((K : ℝ) + 2) / 2 ≤ t_K`.
    have htK_nonneg : 0 ≤ fistaT hproblem x0 L K := by
      have hone_le_half :
          (1 : ℝ) ≤ ((K : ℝ) + 2) / 2 := by
        have hK_nonneg : (0 : ℝ) ≤ (K : ℝ) := by
          exact_mod_cast Nat.zero_le K
        nlinarith
      exact le_trans zero_le_one (le_trans hone_le_half hmomentum_lower)
    have hone_div_nonneg : 0 ≤ ((K : ℝ) + 2) / 2 := by
      have hK_nonneg : (0 : ℝ) ≤ (K : ℝ) := by
        exact_mod_cast Nat.zero_le K
      nlinarith
    have hsq :
        (((K : ℝ) + 2) / 2) * (((K : ℝ) + 2) / 2) ≤
          fistaT hproblem x0 L K * fistaT hproblem x0 L K := by
      exact mul_le_mul hmomentum_lower hmomentum_lower hone_div_nonneg htK_nonneg
    nlinarith [hsq]
  have hscaled_final :
      ((K : ℝ) + 2) ^ (2 : ℕ) * vR (K + 1) ≤
        2 * α * (Lf : ℝ) * ‖x0 - xStar‖ ^ (2 : ℕ) := by
    have hleft :
        ((K : ℝ) + 2) ^ (2 : ℕ) * vR (K + 1) ≤
          (4 * fistaT hproblem x0 L K ^ (2 : ℕ)) * vR (K + 1) := by
      exact mul_le_mul_of_nonneg_right hmomentum_sq hvR_nonneg
    have hright :
        (4 * fistaT hproblem x0 L K ^ (2 : ℕ)) * vR (K + 1) ≤
          2 * α * (Lf : ℝ) * ‖x0 - xStar‖ ^ (2 : ℕ) := by
      nlinarith [hscaled_gap]
    exact le_trans hleft hright
  have hk_den_pos :
      0 < ((K : ℝ) + 2) ^ (2 : ℕ) := by
    positivity
  have hreal :
      vR (K + 1) ≤
        (2 * α * (Lf : ℝ) * ‖x0 - xStar‖ ^ (2 : ℕ)) /
          ((K : ℝ) + 2) ^ (2 : ℕ) := by
    -- Divide the scaled estimate by the positive factor `((K : ℝ) + 2)^2`.
    exact (le_div_iff₀ hk_den_pos).2 <| by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hscaled_final
  have hreal_succ :
      vR (K + 1) ≤
        (2 * α * (Lf : ℝ) * ‖x0 - xStar‖ ^ (2 : ℕ)) /
          ((K : ℝ) + (1 + 1)) ^ (2 : ℕ) := by
    convert hreal using 1
    ring_nf
  have hK_eff :
      fistaX hproblem x0 L (K + 1) ∈ effective_domain g :=
    fistaPositiveIterate_memEffectiveDomain
      (hproblem := hproblem) (x0 := x0) (L := L)
      (n := K + 1)
      (show 1 ≤ K + 1 by exact Nat.succ_le_succ (Nat.zero_le K))
  have hK_obj :
      composite_model_objective f.toEReal g (fistaX hproblem x0 L (K + 1)) =
        (((f (fistaX hproblem x0 L (K + 1)) +
            (g (fistaX hproblem x0 L (K + 1))).toReal : ℝ)) : EReal) :=
    fista_objective_eq_real_of_mem_effective_domain hproblem hK_eff
  have hK_toReal :
      (composite_model_objective f.toEReal g
          (fistaX hproblem x0 L (K + 1))).toReal =
        f (fistaX hproblem x0 L (K + 1)) +
          (g (fistaX hproblem x0 L (K + 1))).toReal := by
    rw [hK_obj, EReal.toReal_coe]
  have hgap_eq :
      ((((composite_model_objective f.toEReal g
            (fistaX hproblem x0 L (K + 1))).toReal - FOpt : ℝ)) : EReal) =
        composite_model_objective f.toEReal g
            (fistaX hproblem x0 L (K + 1)) - (FOpt : EReal) := by
    rw [hK_toReal, hK_obj]
    simp [EReal.coe_sub]
  have hgap_eq_succ :
      ((((composite_model_objective f.toEReal g
            (fistaX hproblem x0 L (1 + K))).toReal - FOpt : ℝ)) : EReal) =
        composite_model_objective f.toEReal g
            (fistaX hproblem x0 L (1 + K)) - (FOpt : EReal) := by
    simpa [Nat.add_comm] using hgap_eq
  -- Convert the final real estimate back to the public `EReal` objective-gap statement.
  rw [← hgap_eq_succ]
  simpa [vR, Nat.add_comm, Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm,
    mul_assoc, mul_left_comm, mul_comm] using
    (EReal.coe_le_coe_iff.mpr hreal_succ)

end FistaRate
