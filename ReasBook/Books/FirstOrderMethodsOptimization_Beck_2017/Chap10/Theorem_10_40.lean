/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_2
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Algorithm_10_6
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Algorithm_10_11
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Lemma_10_33
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Remark_10_32
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Theorem_10_16

noncomputable section

universe u

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

variable {f : E → ℝ} {g : E → EReal} {XStar : Set E} {FOpt : ℝ} {Lf : NNReal}
variable [hproblem : IsFastProximalGradientProblem f g XStar FOpt Lf]
variable {x y z : ℕ → E} {L : ℕ → PosReal} {α : ℝ} {xStar : E}

/-- Helper for Theorem 10.40: the theorem uses the source residual
`u_n = t_n z^n - (x* + (t_n - 1) x^n)`. -/
def mfistaResidualToOptimal
    (x z : ℕ → E) (xStar : E) (n : ℕ) : E :=
  fista_momentum_sequence n • z n -
    (xStar + (fista_momentum_sequence n - 1) • x n)

/-- Helper for Theorem 10.40: the canonical momentum sequence stays above `1`. -/
lemma mfistaMomentum_one_le
    (n : ℕ) :
    (1 : ℝ) ≤ fista_momentum_sequence n := by
  have hlower :=
    fista_momentum_sequence_lower_bound
      (t := fista_momentum_sequence)
      (h0 := fista_momentum_sequence_zero)
      (hsucc := fista_momentum_sequence_succ)
      n
  have hone_le_half :
      (1 : ℝ) ≤ ((n : ℝ) + 2) / 2 := by
    nlinarith [show (0 : ℝ) ≤ n by exact_mod_cast Nat.zero_le n]
  exact le_trans hone_le_half hlower

/-- Helper for Theorem 10.40: the FISTA momentum recursion satisfies
`t_(n+1)^2 - t_(n+1) = t_n^2`. -/
lemma mfistaMomentum_sq_sub_eq_prev_sq
    (n : ℕ) :
    fista_momentum_sequence (n + 1) ^ (2 : ℕ) -
        fista_momentum_sequence (n + 1) =
      fista_momentum_sequence n ^ (2 : ℕ) := by
  have hsucc := fista_momentum_sequence_succ n
  rw [fista_momentum_update_eq] at hsucc
  have hrad_nonneg :
      0 ≤ 1 + 4 * fista_momentum_sequence n ^ (2 : ℕ) := by
    positivity
  have hsqrt :
      Real.sqrt (1 + 4 * fista_momentum_sequence n ^ (2 : ℕ)) =
        2 * fista_momentum_sequence (n + 1) - 1 := by
    nlinarith [hsucc]
  have hsq :
      (Real.sqrt (1 + 4 * fista_momentum_sequence n ^ (2 : ℕ))) ^ (2 : ℕ) =
        (2 * fista_momentum_sequence (n + 1) - 1) ^ (2 : ℕ) := by
    simpa using congrArg (fun t : ℝ ↦ t ^ (2 : ℕ)) hsqrt
  rw [Real.sq_sqrt hrad_nonneg] at hsq
  nlinarith

/-- Helper for Theorem 10.40: the textbook backtracking constant
`α = max {η, s / L_f}` is equivalent to the stepsize cap `α L_f = max {η L_f, s}`. -/
lemma mfistaAlphaMulLf_eq_maxStepsize
    {s : PosReal} {η : ProximalGradientBacktrackingGrowthFactor}
    (hLf : 0 < (Lf : ℝ))
    (hα : α = max (η : ℝ) ((s : ℝ) / (Lf : ℝ))) :
    max ((η : ℝ) * (Lf : ℝ)) (s : ℝ) = α * (Lf : ℝ) := by
  -- Split on which branch of the textbook `max` determines `α`.
  rw [hα]
  by_cases hη : (η : ℝ) ≤ (s : ℝ) / (Lf : ℝ)
  · have hs :
        (s : ℝ) = ((s : ℝ) / (Lf : ℝ)) * (Lf : ℝ) := by
      field_simp [hLf.ne']
    have hηLf : (η : ℝ) * (Lf : ℝ) ≤ (s : ℝ) := by
      nlinarith
    rw [max_eq_right hηLf, max_eq_right hη]
    exact hs
  · have hηlt : (s : ℝ) / (Lf : ℝ) < (η : ℝ) := lt_of_not_ge hη
    have hsLf : (s : ℝ) < (η : ℝ) * (Lf : ℝ) := by
      have hmul :
          ((s : ℝ) / (Lf : ℝ)) * (Lf : ℝ) < (η : ℝ) * (Lf : ℝ) := by
        exact mul_lt_mul_of_pos_right hηlt hLf
      have hs :
          ((s : ℝ) / (Lf : ℝ)) * (Lf : ℝ) = (s : ℝ) := by
        field_simp [hLf.ne']
      rw [hs] at hmul
      exact hmul
    rw [max_eq_left (le_of_lt hsLf), max_eq_left (le_of_lt hηlt)]

omit hproblem in
/-- Helper for Theorem 10.40: on `effective_domain g`, the composite objective is the finite real
sum `f + g`. -/
lemma mfistaObjectiveEqReal_of_memEffectiveDomain
    (hproblem : IsFastProximalGradientProblem f g XStar FOpt Lf)
    {xPoint : E} (hxPoint : xPoint ∈ effective_domain g) :
    composite_model_objective f.toEReal g xPoint =
      (((f xPoint + (g xPoint).toReal : ℝ)) : EReal) := by
  let hg_proper : IsProperExtendedRealFunction g := hproblem.g_proper
  have hgx_val :
      g xPoint = (((g xPoint).toReal : ℝ) : EReal) := by
    exact
      (EReal.coe_toReal (mem_effective_domain.mp hxPoint).ne
        (hg_proper.ne_bot xPoint)).symm
  -- Once `g xPoint` is finite, the composite objective is the cast of the real sum.
  rw [composite_model_objective_apply, Function.toEReal, hgx_val]
  simp [EReal.coe_add]

omit hproblem in
/-- Helper for Theorem 10.40: every finite objective gap is the cast of its real gap. -/
lemma mfistaObjectiveGap_eq_coe_sub_toReal_of_memEffectiveDomain
    (hproblem : IsFastProximalGradientProblem f g XStar FOpt Lf)
    {xPoint : E} (hxPoint : xPoint ∈ effective_domain g) :
    ((((composite_model_objective f.toEReal g xPoint).toReal - FOpt : ℝ)) : EReal) =
      composite_model_objective f.toEReal g xPoint - (FOpt : EReal) := by
  have hxPoint_toReal :
      (composite_model_objective f.toEReal g xPoint).toReal =
        f xPoint + (g xPoint).toReal := by
    rw [mfistaObjectiveEqReal_of_memEffectiveDomain hproblem hxPoint]
    simpa [Function.toEReal] using EReal.toReal_coe (f xPoint + (g xPoint).toReal)
  -- Rewrite the finite objective value through its real representative before subtracting `FOpt`.
  rw [hxPoint_toReal, mfistaObjectiveEqReal_of_memEffectiveDomain hproblem hxPoint]
  simp [EReal.coe_sub]

omit hproblem in
/-- Helper for Theorem 10.40: once both composite values are finite, their difference is the
canonical `EReal` coercion of the real difference of their `toReal` values. -/
lemma mfistaObjectiveDiff_eq_coe_sub_of_memEffectiveDomain
    (hproblem : IsFastProximalGradientProblem f g XStar FOpt Lf)
    {xPoint zPoint : E}
    (hxPoint : xPoint ∈ effective_domain g)
    (hzPoint : zPoint ∈ effective_domain g) :
    composite_model_objective f.toEReal g zPoint -
        composite_model_objective f.toEReal g xPoint =
      ((((composite_model_objective f.toEReal g zPoint).toReal -
            (composite_model_objective f.toEReal g xPoint).toReal : ℝ)) : EReal) := by
  have hzPoint_toReal :
      (composite_model_objective f.toEReal g zPoint).toReal =
        f zPoint + (g zPoint).toReal := by
    rw [mfistaObjectiveEqReal_of_memEffectiveDomain hproblem hzPoint]
    simpa [Function.toEReal] using EReal.toReal_coe (f zPoint + (g zPoint).toReal)
  have hxPoint_toReal :
      (composite_model_objective f.toEReal g xPoint).toReal =
        f xPoint + (g xPoint).toReal := by
    rw [mfistaObjectiveEqReal_of_memEffectiveDomain hproblem hxPoint]
    simpa [Function.toEReal] using EReal.toReal_coe (f xPoint + (g xPoint).toReal)
  -- Rewrite both finite objective values through their real representatives before subtracting.
  rw [hzPoint_toReal, hxPoint_toReal,
    mfistaObjectiveEqReal_of_memEffectiveDomain hproblem hzPoint,
    mfistaObjectiveEqReal_of_memEffectiveDomain hproblem hxPoint]
  simp [EReal.coe_sub]

omit hproblem in
/-- Helper for Theorem 10.40: every finite objective value is at least the optimal value `FOpt`. -/
lemma mfistaToReal_ge_FOpt_of_memEffectiveDomain
    (hproblem : IsFastProximalGradientProblem f g XStar FOpt Lf)
    {xPoint : E} (hxPoint : xPoint ∈ effective_domain g) :
    FOpt ≤ (composite_model_objective f.toEReal g xPoint).toReal := by
  have hxPoint_toReal :
      (composite_model_objective f.toEReal g xPoint).toReal =
        f xPoint + (g xPoint).toReal := by
    rw [mfistaObjectiveEqReal_of_memEffectiveDomain hproblem hxPoint]
    simpa [Function.toEReal] using EReal.toReal_coe (f xPoint + (g xPoint).toReal)
  have hxPoint_finite :
      (((composite_model_objective f.toEReal g xPoint).toReal : ℝ) : EReal) =
        composite_model_objective f.toEReal g xPoint := by
    rw [hxPoint_toReal, mfistaObjectiveEqReal_of_memEffectiveDomain hproblem hxPoint]
  have hlower : (FOpt : EReal) ≤ composite_model_objective f.toEReal g xPoint :=
    hproblem.optimal_value_isGLB.1 ⟨xPoint, rfl⟩
  -- Once the feasible objective value is known to be finite, the `EReal` lower bound reads as a
  -- plain real inequality.
  rw [← hxPoint_finite] at hlower
  exact EReal.coe_le_coe_iff.mp hlower

omit hproblem in
/-- Helper for Theorem 10.40: every optimizer has finite `g`-value, hence lies in
`effective_domain g`. -/
lemma mfistaOptimalPoint_memEffectiveDomain
    (hproblem : IsFastProximalGradientProblem f g XStar FOpt Lf)
    (hxStar : xStar ∈ XStar) :
    xStar ∈ effective_domain g := by
  -- Read the optimizer through the canonical fast-problem objective-value bridge.
  have hxStar_value :
      composite_model_objective f.toEReal g xStar = (FOpt : EReal) :=
    IsConvexCompositeSmoothMinimizationProblem.objective_eq_optimalValue_of_mem_optimalSet
      (h := hproblem.toIsConvexCompositeSmoothMinimizationProblem)
      hxStar
  have hg_top : g xStar ≠ ⊤ := by
    -- If `g xStar = ⊤`, then the composite objective is also `⊤`, contradicting optimality.
    intro hg_top
    have htop :
        composite_model_objective f.toEReal g xStar = ⊤ := by
      rw [composite_model_objective_apply, Function.toEReal, hg_top]
      simp
    rw [htop] at hxStar_value
    exact EReal.coe_ne_top FOpt hxStar_value.symm
  exact mem_effective_domain.mpr (lt_top_iff_ne_top.mpr hg_top)

/-- Helper for Theorem 10.40: every positive MFISTA iterate has finite `g`-value because its
objective is bounded above by the finite prox-point objective. -/
lemma mfistaPositiveIterate_memEffectiveDomainG
    (htraj : hproblem.IsMfistaTrajectory x y z L)
    (n : ℕ) :
    x (n + 1) ∈ effective_domain g := by
  -- Local instance justification (owner reuse): the prox-step finiteness theorem is stated in the
  -- shared prox-gradient API, so we expose the regularity data carried by `hproblem`.
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  -- Local instance justification (owner reuse): the same prox-step theorem also expects the
  -- closedness witness from the standing fast-problem assumptions.
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  -- Local instance justification (owner reuse): the same prox-step theorem finally expects the
  -- convexity witness already stored in `hproblem`.
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  have hz :
      z n ∈ effective_domain g := by
    -- Each prox-point `z n` is finite for `g` by the Chapter 10 prox-gradient domain lemma.
    simpa [is_mfista_trajectory.z_eq htraj n] using
      (prox_grad_step_mem_effective_domain_g
        (interior_effective_domain_point_of_real f (y n))
        (L n))
  have hz_obj_ne_top :
      composite_model_objective f.toEReal g (z n) ≠ ⊤ := by
    -- Finite prox-point objectives are real coercions, hence cannot be `⊤`.
    rw [mfistaObjectiveEqReal_of_memEffectiveDomain (hproblem := hproblem) hz]
    exact (EReal.add_lt_top (EReal.coe_ne_top _) (EReal.coe_ne_top _)).ne
  have hx_obj_ne_top :
      composite_model_objective f.toEReal g (x (n + 1)) ≠ ⊤ := by
    -- Monotonicity of MFISTA transfers finite objective values from `z n` to `x (n + 1)`.
    intro hx_top
    have hchoose := is_mfista_trajectory_x_next_objective_le_prox htraj n
    rw [hx_top] at hchoose
    exact hz_obj_ne_top (top_le_iff.mp hchoose)
  have hg_top :
      g (x (n + 1)) ≠ ⊤ := by
    -- If `g (x (n + 1)) = ⊤`, then the composite objective would also be `⊤`.
    intro hg_top
    have hobj_top :
        composite_model_objective f.toEReal g (x (n + 1)) = ⊤ := by
      rw [composite_model_objective_apply, Function.toEReal, hg_top]
      simp
    exact hx_obj_ne_top hobj_top
  exact mem_effective_domain.mpr (lt_top_iff_ne_top.mpr hg_top)

/-- Helper for Theorem 10.40: every positive MFISTA objective gap is nonnegative on the real
layer. -/
lemma mfistaPositiveIterateGapNonneg
    (htraj : hproblem.IsMfistaTrajectory x y z L)
    (n : ℕ) :
    0 ≤ (composite_model_objective f.toEReal g (x (n + 1))).toReal - FOpt := by
  have hxsucc :
      x (n + 1) ∈ effective_domain g :=
    mfistaPositiveIterate_memEffectiveDomainG (hproblem := hproblem) htraj n
  -- Finite feasible objective values are bounded below by the optimal value.
  exact sub_nonneg.mpr <|
    mfistaToReal_ge_FOpt_of_memEffectiveDomain (hproblem := hproblem) hxsucc

/-- Helper for Theorem 10.40: the reciprocal of the MFISTA momentum coefficient belongs to
`Set.Icc 0 1`. -/
lemma mfistaOneDivMomentum_memIcc
    (n : ℕ) :
    (1 / fista_momentum_sequence (n + 1) : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  -- The textbook lower bound `t_(n+1) ≥ 1` controls the reciprocal coefficient.
  have hone_le :
      (1 : ℝ) ≤ fista_momentum_sequence (n + 1) :=
    mfistaMomentum_one_le (n + 1)
  have hpos :
      0 < fista_momentum_sequence (n + 1) := lt_of_lt_of_le zero_lt_one hone_le
  constructor
  · exact one_div_nonneg.mpr (le_of_lt hpos)
  · have hrecip_le :
        1 / fista_momentum_sequence (n + 1) ≤ 1 / (1 : ℝ) := by
      exact one_div_le_one_div_of_le zero_lt_one hone_le
    simpa using hrecip_le

/-- Helper for Theorem 10.40: the source comparison point
`(1 / t_(n+1)) • xStar + (1 - 1 / t_(n+1)) • x^(n+1)` stays in `effective_domain g`. -/
lemma mfistaCombinationPoint_memEffectiveDomain
    (htraj : hproblem.IsMfistaTrajectory x y z L)
    (hxStar : xStar ∈ XStar)
    (n : ℕ) :
    let θ : ℝ := 1 / fista_momentum_sequence (n + 1)
    let w : E := θ • xStar + (1 - θ) • x (n + 1)
    w ∈ effective_domain g := by
  dsimp
  have hxStar_eff :
      xStar ∈ effective_domain g :=
    mfistaOptimalPoint_memEffectiveDomain (hproblem := hproblem) hxStar
  have hxsucc_eff :
      x (n + 1) ∈ effective_domain g :=
    mfistaPositiveIterate_memEffectiveDomainG (hproblem := hproblem) htraj n
  have hθ_mem :
      (1 / fista_momentum_sequence (n + 1) : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    simpa using mfistaOneDivMomentum_memIcc n
  -- Convexity of `g` keeps the source comparison point inside the effective domain.
  exact combo_mem_effective_domain_of_is_convex_function hproblem.g_convex
    hxStar_eff hxsucc_eff hθ_mem

/-- Helper for Theorem 10.40: convexity bounds the objective of the source comparison point by
`(1 - 1 / t_(n+1)) v_(n+1) + FOpt` on the real layer. -/
lemma mfistaCombinationObjectiveUpperBoundReal
    (htraj : hproblem.IsMfistaTrajectory x y z L)
    (hxStar : xStar ∈ XStar)
    (n : ℕ) :
    let θ : ℝ := 1 / fista_momentum_sequence (n + 1)
    let w : E := θ • xStar + (1 - θ) • x (n + 1)
    (composite_model_objective f.toEReal g w).toReal ≤
      (1 - θ) *
          ((composite_model_objective f.toEReal g (x (n + 1))).toReal - FOpt) +
        FOpt := by
  -- Local instance justification (owner reuse): the convex-segment owner for `g` expects the
  -- properness witness carried by `hproblem`.
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  dsimp
  let θ : ℝ := 1 / fista_momentum_sequence (n + 1)
  let w : E := θ • xStar + (1 - θ) • x (n + 1)
  have hxStar_eff :
      xStar ∈ effective_domain g :=
    mfistaOptimalPoint_memEffectiveDomain (hproblem := hproblem) hxStar
  have hxsucc_eff :
      x (n + 1) ∈ effective_domain g :=
    mfistaPositiveIterate_memEffectiveDomainG (hproblem := hproblem) htraj n
  have hθ_mem : θ ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [θ] using mfistaOneDivMomentum_memIcc n
  have hθ_nonneg : 0 ≤ θ := hθ_mem.1
  have hθ_le_one : θ ≤ 1 := hθ_mem.2
  have hone_sub_nonneg : 0 ≤ 1 - θ := sub_nonneg.mpr hθ_le_one
  have hw_eff : w ∈ effective_domain g := by
    -- Reuse the feasibility lemma at the exact comparison point.
    simpa [θ, w] using
      mfistaCombinationPoint_memEffectiveDomain
        (hproblem := hproblem) (htraj := htraj) (hxStar := hxStar) n
  have hw_obj :
      composite_model_objective f.toEReal g w =
        (((f w + (g w).toReal : ℝ)) : EReal) :=
    mfistaObjectiveEqReal_of_memEffectiveDomain (hproblem := hproblem) hw_eff
  have hxsucc_obj :
      composite_model_objective f.toEReal g (x (n + 1)) =
        (((f (x (n + 1)) + (g (x (n + 1))).toReal : ℝ)) : EReal) :=
    mfistaObjectiveEqReal_of_memEffectiveDomain (hproblem := hproblem) hxsucc_eff
  have hxStar_obj :
      composite_model_objective f.toEReal g xStar =
        (((f xStar + (g xStar).toReal : ℝ)) : EReal) :=
    mfistaObjectiveEqReal_of_memEffectiveDomain (hproblem := hproblem) hxStar_eff
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
      (composite_model_objective f.toEReal g (x (n + 1))).toReal =
        f (x (n + 1)) + (g (x (n + 1))).toReal := by
    rw [hxsucc_obj, EReal.toReal_coe]
  have hg_convexE :
      g w ≤
        (θ : EReal) * g xStar + ((1 - θ : ℝ) : EReal) * g (x (n + 1)) := by
    -- Jensen's inequality for the nonsmooth term is read on the source combination point.
    simpa [w, θ, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
      (is_convex_function_iff_segment_ineq.mp hproblem.g_convex)
        xStar hxStar_eff (x (n + 1)) hxsucc_eff hθ_mem
  have hg_convex :
      (g w).toReal ≤ θ * (g xStar).toReal + (1 - θ) * (g (x (n + 1))).toReal := by
    have hgw_val :
        g w = (((g w).toReal : ℝ) : EReal) :=
      (EReal.coe_toReal (mem_effective_domain.mp hw_eff).ne
        (hproblem.g_proper.ne_bot _)).symm
    have hgxStar_val :
        g xStar = (((g xStar).toReal : ℝ) : EReal) :=
      (EReal.coe_toReal (mem_effective_domain.mp hxStar_eff).ne
        (hproblem.g_proper.ne_bot _)).symm
    have hgxsucc_val :
        g (x (n + 1)) = (((g (x (n + 1))).toReal : ℝ) : EReal) :=
      (EReal.coe_toReal (mem_effective_domain.mp hxsucc_eff).ne
        (hproblem.g_proper.ne_bot _)).symm
    have hg_convex' :
        (((g w).toReal : ℝ) : EReal) ≤
          (((θ * (g xStar).toReal + (1 - θ) * (g (x (n + 1))).toReal : ℝ)) : EReal) := by
      rw [hgw_val, hgxStar_val, hgxsucc_val] at hg_convexE
      simpa [EReal.coe_add, EReal.coe_mul] using hg_convexE
    exact EReal.coe_le_coe_iff.mp hg_convex'
  have hf_convex :
      f w ≤ θ * f xStar + (1 - θ) * f (x (n + 1)) := by
    -- The smooth term is convex on `Set.univ`, so it satisfies the same Jensen bound.
    simpa [w, θ, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
      hproblem.f_convex.2 (by simp) (by simp) hθ_nonneg hone_sub_nonneg (by nlinarith)
  have hw_toReal :
      (composite_model_objective f.toEReal g w).toReal = f w + (g w).toReal := by
    rw [hw_obj, EReal.toReal_coe]
  have hupper_real :
      (composite_model_objective f.toEReal g w).toReal ≤
        (1 - θ) *
            ((composite_model_objective f.toEReal g (x (n + 1))).toReal - FOpt) +
          FOpt := by
    -- Add the convex bounds for `f` and `g`, then substitute `F(x*) = FOpt`.
    rw [hw_toReal, hxsucc_toReal]
    nlinarith [hf_convex, hg_convex, hxStar_toReal]
  exact hupper_real

omit hproblem in
/-- Helper for Theorem 10.40: convexity of the real-valued smooth term makes the local
linearization defect of `f.toEReal` nonnegative at every base point. -/
lemma mfistaConvexLinearizationDefect_nonneg
    (hfast : IsFastProximalGradientProblem f g XStar FOpt Lf)
    {xPoint : E} (yI : interior (effective_domain f.toEReal)) :
    (0 : EReal) ≤ ℓ[f.toEReal, xPoint, yI] := by
  let line : ℝ →ᵃ[ℝ] E := AffineMap.lineMap (yI : E) xPoint
  let φ : ℝ → ℝ := fun t ↦ f (line t)
  have hconv :
      ConvexOn ℝ (effective_domain f.toEReal) (fun z ↦ (f.toEReal z).toReal) := by
    simpa [effective_domain, Function.toEReal] using hfast.f_convex
  have hφ_convex :
      ConvexOn ℝ (line ⁻¹' effective_domain f.toEReal) φ := by
    -- Restrict the real-valued model of `f` to the segment from `yI` to `xPoint`.
    simpa [φ, line] using hconv.comp_affineMap line
  have hφ_zero :
      (0 : ℝ) ∈ line ⁻¹' effective_domain f.toEReal := by
    simpa [line] using interior_subset yI.2
  have hφ_one :
      (1 : ℝ) ∈ line ⁻¹' effective_domain f.toEReal := by
    simp [line, effective_domain, Function.toEReal]
  have hyDiff :
      DifferentiableAt ℝ f (yI : E) :=
    hfast.f_smooth.1 (yI : E) (by simp)
  have hφ_deriv :
      HasDerivAt φ
        (inner ℝ (∇ f (yI : E)) (xPoint - (yI : E))) 0 := by
    have hcomp :
        HasDerivAt φ
          (fderiv ℝ f (yI : E) (xPoint - (yI : E))) 0 := by
      have hbase :
          HasFDerivAt f (fderiv ℝ f (yI : E)) (line 0) := by
        simpa [line] using hyDiff.hasFDerivAt
      have hline : HasDerivAt line (xPoint - (yI : E)) 0 := by
        simpa [line] using
          (show HasDerivAt (AffineMap.lineMap (yI : E) xPoint) (xPoint - (yI : E)) (0 : ℝ) from
            AffineMap.hasDerivAt_lineMap)
      simpa [φ, line] using HasFDerivAt.comp_hasDerivAt 0 hbase hline
    have hgrad :
        fderiv ℝ f (yI : E) (xPoint - (yI : E)) =
          inner ℝ (∇ f (yI : E)) (xPoint - (yI : E)) := by
      simpa using
        (show
            fderiv ℝ f (yI : E) (xPoint - (yI : E)) =
              inner ℝ (∇ f (yI : E)) (xPoint - (yI : E)) from
          HasGradientAt.fderiv_apply hyDiff.hasGradientAt)
    simpa [hgrad] using hcomp
  have hsupport :
      inner ℝ (∇ f (yI : E)) (xPoint - (yI : E)) ≤ f xPoint - f (yI : E) := by
    have hsecant :
        inner ℝ (∇ f (yI : E)) (xPoint - (yI : E)) ≤ slope φ 0 1 := by
      -- Convexity bounds the directional derivative by the secant slope on the segment.
      exact hφ_convex.le_slope_of_hasDerivAt hφ_zero hφ_one zero_lt_one hφ_deriv
    simpa [φ, line, slope] using hsecant
  have hreal :
      0 ≤ f xPoint - f (yI : E) - inner ℝ (∇ f (yI : E)) (xPoint - (yI : E)) := by
    linarith
  -- Rewrite the defect once and then read the supporting-hyperplane inequality on the real layer.
  rw [prox_gradient_linearization_defect_eq]
  simpa [Function.toEReal] using (EReal.coe_le_coe_iff.mpr hreal)

/-- Helper for Theorem 10.40: after dropping the nonnegative convex linearization defect, the
fundamental prox-gradient inequality becomes a real inequality on finite endpoints. -/
lemma mfistaAcceptedProxGapReal
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
  -- Local instance justification (owner reuse): the prox-gap owners are stated in the shared
  -- prox-gradient API, so we expose the regularity data already carried by `hproblem`.
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  let yI := interior_effective_domain_point_of_real f yPoint
  let xPlus : E := hproblem.proxPoint Lbar yI
  have hxPlus :
      xPlus ∈ effective_domain g := by
    -- The prox-gradient step at the real base point always lands in `effective_domain g`.
    simpa [xPlus, yI, IsFastProximalGradientProblem.proxPoint] using
      (prox_grad_step_mem_effective_domain_g yI Lbar)
  have haccepts' :
      proximal_gradient_backtracking_B2_accepts f.toEReal g Lbar yI := by
    -- Repackage the displayed upper model as the canonical B2 acceptance predicate.
    simpa [yI, IsFastProximalGradientProblem.proxPoint] using
      (proximal_gradient_backtracking_B2_accepts_iff_fista_upper_model f g Lbar yPoint).2 haccepts
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
  have hdefect_nonneg :
      (0 : EReal) ≤ ℓ[f.toEReal, xPoint, yI] := by
    -- Convexity lets us drop the linearization defect from the accepted-step estimate.
    simpa [yI] using
      (mfistaConvexLinearizationDefect_nonneg
        (hfast := hproblem) (xPoint := xPoint) (yI := yI))
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
  have hstepE' := hstepE
  -- Rewrite the finite objective difference as the canonical real subtraction before stripping
  -- the final `EReal` coercion.
  rw [mfistaObjectiveDiff_eq_coe_sub_of_memEffectiveDomain
    (hproblem := hproblem) (xPoint := xPlus) (zPoint := xPoint) hxPlus hxPoint] at hstepE'
  exact EReal.coe_le_coe_iff.mp hstepE'

/-- Helper for Theorem 10.40: the MFISTA extrapolation formula gives the exact predecessor
transport from the pre-step vector to the previous residual. -/
lemma mfistaPrestepVector_eq_previousResidual
    (htraj : hproblem.IsMfistaTrajectory x y z L)
    (n : ℕ) :
    fista_momentum_sequence (n + 1) • y (n + 1) -
        (xStar + (fista_momentum_sequence (n + 1) - 1) • x (n + 1)) =
      mfistaResidualToOptimal x z xStar n :=
  by
  -- Local instance justification (owner reuse): the trajectory projection theorem is stated for
  -- the raw MFISTA owner, so we expose the regularity witnesses already stored in `hproblem`.
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  have htnNext_pos : 0 < fista_momentum_sequence (n + 1) := by
    exact lt_of_lt_of_le zero_lt_one (mfistaMomentum_one_le (n + 1))
  have hmul_z :
      fista_momentum_sequence (n + 1) *
          (fista_momentum_sequence n / fista_momentum_sequence (n + 1)) =
        fista_momentum_sequence n := by
    field_simp [htnNext_pos.ne']
  have hmul_x :
      fista_momentum_sequence (n + 1) *
          ((fista_momentum_sequence n - 1) / fista_momentum_sequence (n + 1)) =
        fista_momentum_sequence n - 1 := by
    field_simp [htnNext_pos.ne']
  -- Route correction: rewrite the MFISTA pre-step vector through the exact `y_succ` formula once,
  -- then collapse the scaled coefficients back to the previous residual.
  rw [is_mfista_trajectory.y_succ htraj n, mfistaResidualToOptimal]
  simp_rw [smul_add, smul_sub, smul_smul]
  rw [hmul_z, hmul_x]
  simp_rw [sub_eq_add_neg]
  module

/-- Helper for Theorem 10.40: the accepted stepsize rule supplies both monotonicity of
`L_n` and the uniform cap `L_n ≤ α L_f`. -/
lemma mfistaStepsizeControl
    (hrule : hproblem.SublinearRateStepsizeRule y L α) :
    (∀ n, (L n : ℝ) ≤ (L (n + 1) : ℝ)) ∧
      (∀ n, (L n : ℝ) ≤ α * (Lf : ℝ)) :=
  by
  constructor
  · intro n
    rcases hrule with ⟨_, hLf_rule⟩ | ⟨_, s, η, _, hB3⟩
    · -- In the constant branch, all stepsizes are exactly `L_f`.
      rw [hLf_rule n, hLf_rule (n + 1)]
    · -- In the B3 branch, each accepted stepsize is at least the previous accepted stepsize.
      -- Local instance justification (owner reuse): the local B3 bounds are stated in the shared
      -- prox-gradient API, so we expose the regularity data carried by `hproblem`.
      letI : IsProperExtendedRealFunction g := hproblem.g_proper
      -- Local instance justification (owner reuse): the same B3 bridge also expects the
      -- closedness witness from the standing fast-problem assumptions.
      letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
      -- Local instance justification (owner reuse): the same B3 bridge finally expects the
      -- convexity witness already stored in `hproblem`.
      letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
      simpa [proximal_gradient_backtracking_B2_previous_stepsize_succ] using
        (backtracking_B3_local_stepsize_bounds
          (f := f) (g := g) (Lf := Lf)
          hproblem.f_smooth hB3 (n + 1)).1
  · intro n
    rcases hrule with ⟨hα, hLf_rule⟩ | ⟨hLf_pos, s, η, hα, hB3⟩
    · -- In the constant branch, the stepsize rule is literally `L_n = L_f` and `α = 1`.
      rw [hα, hLf_rule n]
      simpa using (le_rfl : (Lf : ℝ) ≤ (Lf : ℝ))
    · -- In the B3 branch, combine Remark 10.32 with the textbook identity
      -- `α L_f = max {η L_f, s}`.
      rcases hproblem.uses_backtracking_procedure_B3_rule_stepsize_bounds s η hB3 n with
        ⟨_, hLn_upper⟩
      calc
        (L n : ℝ) ≤ max ((η : ℝ) * (Lf : ℝ)) (s : ℝ) := hLn_upper
        _ = α * (Lf : ℝ) := by
          exact mfistaAlphaMulLf_eq_maxStepsize (Lf := Lf) hLf_pos hα

/-- Helper for Theorem 10.40: the first source energy is bounded by the initial distance to an
optimizer on the exact source surface `2 / L_0`. -/
lemma mfistaInitialEnergyBound
    (htraj : hproblem.IsMfistaTrajectory x y z L)
    (hrule : hproblem.SublinearRateStepsizeRule y L α)
    (hxStar : xStar ∈ XStar) :
    let vR : ℕ → ℝ :=
      fun n ↦ (composite_model_objective f.toEReal g (x n)).toReal - FOpt
    ‖mfistaResidualToOptimal x z xStar 0‖ ^ (2 : ℕ) +
        (2 / (L 0 : ℝ)) * fista_momentum_sequence 0 ^ (2 : ℕ) * vR 1 ≤
      ‖x 0 - xStar‖ ^ (2 : ℕ) := by
  -- Local instance justification (owner reuse): the prox-step finiteness theorem used to identify
  -- `z 0` is stated in the shared prox-gradient API.
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  dsimp
  have hL0_pos : 0 < (L 0 : ℝ) := PosReal.coe_pos (L 0)
  have hxStar_eff :
      xStar ∈ effective_domain g :=
    mfistaOptimalPoint_memEffectiveDomain (hproblem := hproblem) hxStar
  have hx1_eff :
      x 1 ∈ effective_domain g :=
    mfistaPositiveIterate_memEffectiveDomainG (hproblem := hproblem) htraj 0
  have hz0_eff :
      z 0 ∈ effective_domain g := by
    simpa [is_mfista_trajectory.z_eq htraj 0, IsFastProximalGradientProblem.proxPoint] using
      (prox_grad_step_mem_effective_domain_g
        (interior_effective_domain_point_of_real f (y 0))
        (L 0))
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
    rw [mfistaObjectiveEqReal_of_memEffectiveDomain (hproblem := hproblem) hxStar_eff, EReal.toReal_coe]
  have haccepted0 :
      ((L 0 : ℝ) / 2) * ‖xStar - z 0‖ ^ (2 : ℕ) -
          ((L 0 : ℝ) / 2) * ‖xStar - x 0‖ ^ (2 : ℕ) ≤
        FOpt - (composite_model_objective f.toEReal g (z 0)).toReal := by
    have hgap0 :=
      mfistaAcceptedProxGapReal
        (hproblem := hproblem) (xPoint := xStar) (yPoint := y 0) (Lbar := L 0)
        hxStar_eff
        (hproblem.sublinearRateStepsizeRule_accepts hrule 0)
    rw [mfistaObjectiveEqReal_of_memEffectiveDomain (hproblem := hproblem) hxStar_eff, EReal.toReal_coe] at hgap0
    rw [hxStar_sum_toReal] at hgap0
    -- Normalize the optimizer value, the initial base point, and the prox-point `z 0`.
    simpa [interior_effective_domain_point_of_real,
      is_mfista_trajectory.y_zero htraj, is_mfista_trajectory.z_eq htraj 0,
      IsFastProximalGradientProblem.proxPoint, norm_sub_rev] using hgap0
  have hx1_le_z0 :
      (composite_model_objective f.toEReal g (x 1)).toReal ≤
        (composite_model_objective f.toEReal g (z 0)).toReal := by
    have hx1_le_z0E :
        composite_model_objective f.toEReal g (x 1) ≤
          composite_model_objective f.toEReal g (z 0) :=
      is_mfista_trajectory_x_next_objective_le_prox htraj 0
    have hx1_toReal :
        (composite_model_objective f.toEReal g (x 1)).toReal =
          f (x 1) + (g (x 1)).toReal := by
      rw [mfistaObjectiveEqReal_of_memEffectiveDomain (hproblem := hproblem) hx1_eff, EReal.toReal_coe]
    have hz0_toReal :
        (composite_model_objective f.toEReal g (z 0)).toReal =
          f (z 0) + (g (z 0)).toReal := by
      rw [mfistaObjectiveEqReal_of_memEffectiveDomain (hproblem := hproblem) hz0_eff, EReal.toReal_coe]
    rw [mfistaObjectiveEqReal_of_memEffectiveDomain (hproblem := hproblem) hx1_eff,
      mfistaObjectiveEqReal_of_memEffectiveDomain (hproblem := hproblem) hz0_eff] at hx1_le_z0E
    rw [hx1_toReal, hz0_toReal]
    exact EReal.coe_le_coe_iff.mp hx1_le_z0E
  have hx1_gap_le_z0_gap :
      (composite_model_objective f.toEReal g (x 1)).toReal - FOpt ≤
        (composite_model_objective f.toEReal g (z 0)).toReal - FOpt := by
    linarith
  have haccepted0_scaled :
      ‖z 0 - xStar‖ ^ (2 : ℕ) -
          ‖x 0 - xStar‖ ^ (2 : ℕ) ≤
        (2 / (L 0 : ℝ)) *
          (FOpt - (composite_model_objective f.toEReal g (z 0)).toReal) := by
    have hmult :
        (2 / (L 0 : ℝ)) *
            (((L 0 : ℝ) / 2) * ‖xStar - z 0‖ ^ (2 : ℕ) -
              ((L 0 : ℝ) / 2) * ‖xStar - x 0‖ ^ (2 : ℕ)) ≤
          (2 / (L 0 : ℝ)) *
            (FOpt - (composite_model_objective f.toEReal g (z 0)).toReal) := by
      exact mul_le_mul_of_nonneg_left haccepted0 (by positivity)
    -- Clear the positive factor `L₀ / 2` from the accepted prox-gap inequality.
    have hmult' := hmult
    field_simp [hL0_pos.ne'] at hmult'
    have hmult'' :
        (‖z 0 - xStar‖ ^ (2 : ℕ) - ‖x 0 - xStar‖ ^ (2 : ℕ)) * (L 0 : ℝ) ≤
          2 * (FOpt - (composite_model_objective f.toEReal g (z 0)).toReal) := by
      simpa [norm_sub_rev, mul_comm, mul_left_comm, mul_assoc] using hmult'
    have haccepted0_scaled' :
        ‖z 0 - xStar‖ ^ (2 : ℕ) - ‖x 0 - xStar‖ ^ (2 : ℕ) ≤
          (2 * (FOpt - (composite_model_objective f.toEReal g (z 0)).toReal)) / (L 0 : ℝ) := by
      exact (le_div_iff₀ hL0_pos).2 <| by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hmult''
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using haccepted0_scaled'
  have hbase_z0 :
      ‖z 0 - xStar‖ ^ (2 : ℕ) +
          (2 / (L 0 : ℝ)) *
            ((composite_model_objective f.toEReal g (z 0)).toReal - FOpt) ≤
        ‖x 0 - xStar‖ ^ (2 : ℕ) := by
    -- Rearranging the scaled accepted prox-gap gives the exact first source seed at `z 0`.
    nlinarith [haccepted0_scaled]
  have hbase_x1 :
      ‖z 0 - xStar‖ ^ (2 : ℕ) +
          (2 / (L 0 : ℝ)) *
            ((composite_model_objective f.toEReal g (x 1)).toReal - FOpt) ≤
        ‖x 0 - xStar‖ ^ (2 : ℕ) := by
    have hscale :
        (2 / (L 0 : ℝ)) *
            ((composite_model_objective f.toEReal g (x 1)).toReal - FOpt) ≤
          (2 / (L 0 : ℝ)) *
            ((composite_model_objective f.toEReal g (z 0)).toReal - FOpt) := by
      exact mul_le_mul_of_nonneg_left hx1_gap_le_z0_gap (by positivity)
    linarith
  -- Collapse the residual `u_0 = z^0 - x*` and the seed momentum value `t_0 = 1`.
  simpa [mfistaResidualToOptimal, fista_momentum_sequence_zero, norm_sub_rev] using hbase_x1

/-- Helper for Theorem 10.40: the source comparison point at step `n + 1` satisfies the exact
current-step objective-gap estimate on the real layer. -/
lemma mfistaCurrentStepGapUpperBound
    (htraj : hproblem.IsMfistaTrajectory x y z L)
    (hxStar : xStar ∈ XStar)
    (n : ℕ) :
    let vR : ℕ → ℝ :=
      fun m ↦ (composite_model_objective f.toEReal g (x m)).toReal - FOpt
    let θ : ℝ := 1 / fista_momentum_sequence (n + 1)
    let w : E := θ • xStar + (1 - θ) • x (n + 1)
    (composite_model_objective f.toEReal g w).toReal -
        (composite_model_objective f.toEReal g (z (n + 1))).toReal ≤
      (1 - θ) * vR (n + 1) - vR (n + 2) := by
  -- Local instance justification (owner reuse): the prox-point finiteness theorem for `z (n + 1)`
  -- lives in the shared prox-gradient API, so we expose the regularity data already in `hproblem`.
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  dsimp
  let vR : ℕ → ℝ :=
    fun m ↦ (composite_model_objective f.toEReal g (x m)).toReal - FOpt
  let θ : ℝ := 1 / fista_momentum_sequence (n + 1)
  let w : E := θ • xStar + (1 - θ) • x (n + 1)
  have hw_upper :
      (composite_model_objective f.toEReal g w).toReal ≤
        (1 - θ) * vR (n + 1) + FOpt := by
    -- First bound the comparison-point objective by convexity at the source combination point.
    simpa [vR, θ, w] using
      (mfistaCombinationObjectiveUpperBoundReal
        (hproblem := hproblem) (htraj := htraj) (hxStar := hxStar) n)
  have hxnext_eff :
      x (n + 2) ∈ effective_domain g :=
    mfistaPositiveIterate_memEffectiveDomainG (hproblem := hproblem) htraj (n + 1)
  have hzsucc_eff :
      z (n + 1) ∈ effective_domain g := by
    -- The prox-gradient point at the accepted step is also finite for `g`.
    simpa [is_mfista_trajectory.z_eq htraj (n + 1), IsFastProximalGradientProblem.proxPoint] using
      (prox_grad_step_mem_effective_domain_g
        (interior_effective_domain_point_of_real f (y (n + 1)))
        (L (n + 1)))
  have hchooseE :
      composite_model_objective f.toEReal g (x (n + 2)) ≤
        composite_model_objective f.toEReal g (z (n + 1)) :=
    is_mfista_trajectory_x_next_objective_le_prox htraj (n + 1)
  have hchoose_real :
      (composite_model_objective f.toEReal g (x (n + 2))).toReal ≤
        (composite_model_objective f.toEReal g (z (n + 1))).toReal := by
    -- Convert the accepted-step objective comparison to the finite real layer.
    have hchoose_real' :
        f (x (n + 2)) + (g (x (n + 2))).toReal ≤
          f (z (n + 1)) + (g (z (n + 1))).toReal := by
      rw [mfistaObjectiveEqReal_of_memEffectiveDomain (hproblem := hproblem) hxnext_eff,
        mfistaObjectiveEqReal_of_memEffectiveDomain (hproblem := hproblem) hzsucc_eff] at hchooseE
      exact EReal.coe_le_coe_iff.mp hchooseE
    simpa [mfistaObjectiveEqReal_of_memEffectiveDomain (hproblem := hproblem) hxnext_eff,
      mfistaObjectiveEqReal_of_memEffectiveDomain (hproblem := hproblem) hzsucc_eff,
      EReal.toReal_coe] using hchoose_real'
  have hsubtract :
      (composite_model_objective f.toEReal g w).toReal -
          (composite_model_objective f.toEReal g (z (n + 1))).toReal ≤
        (composite_model_objective f.toEReal g w).toReal -
          (composite_model_objective f.toEReal g (x (n + 2))).toReal := by
    -- Then replace `F(z^(n+1))` by the smaller chosen objective `F(x^(n+2))`.
    linarith
  have hgoal :
      (composite_model_objective f.toEReal g w).toReal -
          (composite_model_objective f.toEReal g (x (n + 2))).toReal ≤
        (1 - θ) * vR (n + 1) - vR (n + 2) := by
    -- Finally rewrite the terminal objective through the shifted real gap `vR (n + 2)`.
    dsimp [vR] at hw_upper ⊢
    linarith
  exact le_trans hsubtract hgoal

/-- Helper for Theorem 10.40: combining the accepted prox-gap with the current-step objective
bound yields the exact shared-denominator Lyapunov balance. -/
lemma mfistaAcceptedStepEnergyBalance
    (htraj : hproblem.IsMfistaTrajectory x y z L)
    (hrule : hproblem.SublinearRateStepsizeRule y L α)
    (hxStar : xStar ∈ XStar)
    (n : ℕ) :
    let vR : ℕ → ℝ :=
      fun m ↦ (composite_model_objective f.toEReal g (x m)).toReal - FOpt
    ‖mfistaResidualToOptimal x z xStar (n + 1)‖ ^ (2 : ℕ) +
        (2 / (L (n + 1) : ℝ)) *
          fista_momentum_sequence (n + 1) ^ (2 : ℕ) * vR (n + 2) ≤
      ‖mfistaResidualToOptimal x z xStar n‖ ^ (2 : ℕ) +
        (2 / (L (n + 1) : ℝ)) *
          fista_momentum_sequence n ^ (2 : ℕ) * vR (n + 1) := by
  -- Local instance justification (owner reuse): the accepted prox-gap bridge is stated in the
  -- shared prox-gradient API, so we expose the regularity data already stored in `hproblem`.
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  dsimp
  let vR : ℕ → ℝ :=
    fun m ↦ (composite_model_objective f.toEReal g (x m)).toReal - FOpt
  let t : ℝ := fista_momentum_sequence (n + 1)
  let θ : ℝ := 1 / t
  let w : E := θ • xStar + (1 - θ) • x (n + 1)
  have hL_pos : 0 < (L (n + 1) : ℝ) := PosReal.coe_pos (L (n + 1))
  have ht_one_le : (1 : ℝ) ≤ t := by
    simpa [t] using mfistaMomentum_one_le (n + 1)
  have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht_one_le
  have hw_eff :
      w ∈ effective_domain g := by
    -- The accepted prox-gap is applied at the same source comparison point.
    simpa [t, θ, w] using
      (mfistaCombinationPoint_memEffectiveDomain
        (hproblem := hproblem) (htraj := htraj) (hxStar := hxStar) n)
  have hprox :
      ((L (n + 1) : ℝ) / 2) * ‖w - z (n + 1)‖ ^ (2 : ℕ) -
          ((L (n + 1) : ℝ) / 2) * ‖w - y (n + 1)‖ ^ (2 : ℕ) ≤
        (composite_model_objective f.toEReal g w).toReal -
          (composite_model_objective f.toEReal g (z (n + 1))).toReal := by
    -- Read the accepted prox-gap on the real layer at step `n + 1`.
    simpa [w, θ, interior_effective_domain_point_of_real,
      is_mfista_trajectory.z_eq htraj (n + 1),
      IsFastProximalGradientProblem.proxPoint] using
      (mfistaAcceptedProxGapReal
        (hproblem := hproblem)
        (xPoint := w) (yPoint := y (n + 1)) (Lbar := L (n + 1))
        hw_eff
        (hproblem.sublinearRateStepsizeRule_accepts hrule (n + 1)))
  have hobj :
      (composite_model_objective f.toEReal g w).toReal -
          (composite_model_objective f.toEReal g (z (n + 1))).toReal ≤
        (1 - θ) * vR (n + 1) - vR (n + 2) := by
    -- The current-step objective side is already packaged in the source normal form.
    simpa [vR, t, θ, w] using
      (mfistaCurrentStepGapUpperBound
        (hproblem := hproblem) (htraj := htraj) (hxStar := hxStar) n)
  have hraw :
      ((L (n + 1) : ℝ) / 2) * ‖w - z (n + 1)‖ ^ (2 : ℕ) -
          ((L (n + 1) : ℝ) / 2) * ‖w - y (n + 1)‖ ^ (2 : ℕ) ≤
        (1 - θ) * vR (n + 1) - vR (n + 2) := by
    -- Compose the accepted prox-gap with the current-step objective estimate.
    exact le_trans hprox hobj
  have hscaled :
      t ^ (2 : ℕ) *
          (((L (n + 1) : ℝ) / 2) * ‖w - z (n + 1)‖ ^ (2 : ℕ) -
            ((L (n + 1) : ℝ) / 2) * ‖w - y (n + 1)‖ ^ (2 : ℕ)) ≤
        t ^ (2 : ℕ) * ((1 - θ) * vR (n + 1) - vR (n + 2)) := by
    -- Scale the whole inequality by `t_(n+1)^2`, matching the source Lyapunov normalization.
    exact mul_le_mul_of_nonneg_left hraw (by positivity)
  have hw_scaled :
      t • w = xStar + (t - 1) • x (n + 1) := by
    -- Rewrite the scaled comparison point into the exact source affine surface.
    have ht_ne : t ≠ 0 := ne_of_gt ht_pos
    have ht_div : t * (1 / t) = 1 := by
      field_simp [ht_ne]
    have ht_one_sub : t * (1 - 1 / t) = t - 1 := by
      field_simp [ht_ne]
    calc
      t • w = t • (θ • xStar + (1 - θ) • x (n + 1)) := by rfl
      _ = (t * θ) • xStar + (t * (1 - θ)) • x (n + 1) := by
        simp [smul_add, smul_smul]
      _ = xStar + (t - 1) • x (n + 1) := by
        dsimp [θ]
        rw [ht_div, ht_one_sub, one_smul]
  have hpost_vector :
      t • (w - z (n + 1)) = - mfistaResidualToOptimal x z xStar (n + 1) := by
    -- The post-step vector is exactly the residual at index `n + 1`, up to sign.
    calc
      t • (w - z (n + 1)) = t • w - t • z (n + 1) := by simp [smul_sub]
      _ = (xStar + (t - 1) • x (n + 1)) - t • z (n + 1) := by rw [hw_scaled]
      _ = -(t • z (n + 1) - (xStar + (t - 1) • x (n + 1))) := by abel
      _ = - mfistaResidualToOptimal x z xStar (n + 1) := by
        simp [mfistaResidualToOptimal, t]
  have hpre_vector :
      t • (w - y (n + 1)) = - mfistaResidualToOptimal x z xStar n := by
    -- The pre-step vector collapses to the previous residual via the MFISTA extrapolation rule.
    calc
      t • (w - y (n + 1)) = t • w - t • y (n + 1) := by simp [smul_sub]
      _ = (xStar + (t - 1) • x (n + 1)) - t • y (n + 1) := by rw [hw_scaled]
      _ = -(t • y (n + 1) - (xStar + (t - 1) • x (n + 1))) := by abel
      _ = - mfistaResidualToOptimal x z xStar n := by
        simpa [t] using
          congrArg (fun v : E ↦ -v)
            (mfistaPrestepVector_eq_previousResidual
              (hproblem := hproblem) (htraj := htraj) (xStar := xStar) n)
  have hpost :
      t ^ (2 : ℕ) * ‖w - z (n + 1)‖ ^ (2 : ℕ) =
        ‖mfistaResidualToOptimal x z xStar (n + 1)‖ ^ (2 : ℕ) := by
    -- Rewrite the post-step norm into the residual norm at index `n + 1`.
    calc
      t ^ (2 : ℕ) * ‖w - z (n + 1)‖ ^ (2 : ℕ) =
          ‖t • (w - z (n + 1))‖ ^ (2 : ℕ) := by
        rw [norm_smul]
        have ht_norm : ‖t‖ = t := Real.norm_of_nonneg (le_of_lt ht_pos)
        rw [ht_norm]
        ring
      _ = ‖mfistaResidualToOptimal x z xStar (n + 1)‖ ^ (2 : ℕ) := by
        rw [hpost_vector]
        simp
  have hpre :
      t ^ (2 : ℕ) * ‖w - y (n + 1)‖ ^ (2 : ℕ) =
        ‖mfistaResidualToOptimal x z xStar n‖ ^ (2 : ℕ) := by
    -- Rewrite the pre-step norm into the previous residual norm.
    calc
      t ^ (2 : ℕ) * ‖w - y (n + 1)‖ ^ (2 : ℕ) =
          ‖t • (w - y (n + 1))‖ ^ (2 : ℕ) := by
        rw [norm_smul]
        have ht_norm : ‖t‖ = t := Real.norm_of_nonneg (le_of_lt ht_pos)
        rw [ht_norm]
        ring
      _ = ‖mfistaResidualToOptimal x z xStar n‖ ^ (2 : ℕ) := by
        rw [hpre_vector]
        simp
  have hcoef_gap :
      t ^ (2 : ℕ) * (1 - θ) = fista_momentum_sequence n ^ (2 : ℕ) := by
    have ht_ne : t ≠ 0 := ne_of_gt ht_pos
    -- Normalize the source scalar coefficient `t_(n+1)^2 (1 - 1 / t_(n+1))`.
    calc
      t ^ (2 : ℕ) * (1 - θ) = t ^ (2 : ℕ) - t := by
        dsimp [θ]
        field_simp [pow_two, ht_ne]
      _ = fista_momentum_sequence n ^ (2 : ℕ) := by
        simpa [t] using mfistaMomentum_sq_sub_eq_prev_sq n
  have hscaled' :
      ((L (n + 1) : ℝ) / 2) *
          (t ^ (2 : ℕ) * ‖w - z (n + 1)‖ ^ (2 : ℕ)) -
          ((L (n + 1) : ℝ) / 2) *
            (t ^ (2 : ℕ) * ‖w - y (n + 1)‖ ^ (2 : ℕ)) ≤
        (t ^ (2 : ℕ) * (1 - θ)) * vR (n + 1) -
          t ^ (2 : ℕ) * vR (n + 2) := by
    -- Expand the scaled inequality so the norm and scalar transports can be rewritten separately.
    simpa [sub_eq_add_neg, mul_add, add_mul, mul_sub, sub_mul,
      mul_assoc, mul_left_comm, mul_comm] using hscaled
  have hrewritten :
      ((L (n + 1) : ℝ) / 2) *
          ‖mfistaResidualToOptimal x z xStar (n + 1)‖ ^ (2 : ℕ) -
          ((L (n + 1) : ℝ) / 2) *
            ‖mfistaResidualToOptimal x z xStar n‖ ^ (2 : ℕ) ≤
        fista_momentum_sequence n ^ (2 : ℕ) * vR (n + 1) -
          fista_momentum_sequence (n + 1) ^ (2 : ℕ) * vR (n + 2) := by
    -- Put the scaled balance into the exact source residual and momentum notation.
    have hrewritten' := hscaled'
    rw [hpost, hpre, hcoef_gap] at hrewritten'
    simpa [t] using hrewritten'
  -- Divide the source balance by `L_(n+1) / 2` to recover the shared-denominator energy step.
  have hmult :
      (2 / (L (n + 1) : ℝ)) *
          ((((L (n + 1) : ℝ) / 2) *
              ‖mfistaResidualToOptimal x z xStar (n + 1)‖ ^ (2 : ℕ) -
            ((L (n + 1) : ℝ) / 2) *
              ‖mfistaResidualToOptimal x z xStar n‖ ^ (2 : ℕ))) ≤
        (2 / (L (n + 1) : ℝ)) *
          (fista_momentum_sequence n ^ (2 : ℕ) * vR (n + 1) -
            fista_momentum_sequence (n + 1) ^ (2 : ℕ) * vR (n + 2)) := by
    exact mul_le_mul_of_nonneg_left hrewritten (by positivity)
  -- Clear the positive factor `L_(n+1) / 2` after scaling the source balance.
  have htwice :
      (L (n + 1) : ℝ) * ‖mfistaResidualToOptimal x z xStar (n + 1)‖ ^ (2 : ℕ) -
          (L (n + 1) : ℝ) * ‖mfistaResidualToOptimal x z xStar n‖ ^ (2 : ℕ) ≤
        2 *
          (fista_momentum_sequence n ^ (2 : ℕ) * vR (n + 1) -
            fista_momentum_sequence (n + 1) ^ (2 : ℕ) * vR (n + 2)) := by
    nlinarith [hrewritten]
  have hstep_diff :
      ‖mfistaResidualToOptimal x z xStar (n + 1)‖ ^ (2 : ℕ) -
          ‖mfistaResidualToOptimal x z xStar n‖ ^ (2 : ℕ) ≤
        (2 *
            (fista_momentum_sequence n ^ (2 : ℕ) * vR (n + 1) -
              fista_momentum_sequence (n + 1) ^ (2 : ℕ) * vR (n + 2))) /
          (L (n + 1) : ℝ) := by
    have htwice' :
        (‖mfistaResidualToOptimal x z xStar (n + 1)‖ ^ (2 : ℕ) -
            ‖mfistaResidualToOptimal x z xStar n‖ ^ (2 : ℕ)) *
            (L (n + 1) : ℝ) ≤
          2 *
            (fista_momentum_sequence n ^ (2 : ℕ) * vR (n + 1) -
              fista_momentum_sequence (n + 1) ^ (2 : ℕ) * vR (n + 2)) := by
      simpa [mul_sub, mul_comm, mul_left_comm, mul_assoc] using htwice
    exact (le_div_iff₀ hL_pos).2 <| by
      exact htwice'
  have hstep_diff' :
      ‖mfistaResidualToOptimal x z xStar (n + 1)‖ ^ (2 : ℕ) -
          ‖mfistaResidualToOptimal x z xStar n‖ ^ (2 : ℕ) ≤
        (2 / (L (n + 1) : ℝ)) *
            fista_momentum_sequence n ^ (2 : ℕ) * vR (n + 1) -
          (2 / (L (n + 1) : ℝ)) *
            fista_momentum_sequence (n + 1) ^ (2 : ℕ) * vR (n + 2) := by
    have hrewrite :
        (2 *
            (fista_momentum_sequence n ^ (2 : ℕ) * vR (n + 1) -
              fista_momentum_sequence (n + 1) ^ (2 : ℕ) * vR (n + 2))) /
            (L (n + 1) : ℝ) =
          (2 / (L (n + 1) : ℝ)) *
              fista_momentum_sequence n ^ (2 : ℕ) * vR (n + 1) -
            (2 / (L (n + 1) : ℝ)) *
              fista_momentum_sequence (n + 1) ^ (2 : ℕ) * vR (n + 2) := by
      field_simp [ne_of_gt hL_pos]
    rw [hrewrite] at hstep_diff
    exact hstep_diff
  have hshift1 :=
      add_le_add_right
        hstep_diff'
        (‖mfistaResidualToOptimal x z xStar n‖ ^ (2 : ℕ))
  have hshift1' :
      ‖mfistaResidualToOptimal x z xStar (n + 1)‖ ^ (2 : ℕ) ≤
        ‖mfistaResidualToOptimal x z xStar n‖ ^ (2 : ℕ) +
          ((2 / (L (n + 1) : ℝ)) *
              fista_momentum_sequence n ^ (2 : ℕ) * vR (n + 1) -
            (2 / (L (n + 1) : ℝ)) *
              fista_momentum_sequence (n + 1) ^ (2 : ℕ) * vR (n + 2)) := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hshift1
  have hshift2 :=
      add_le_add_right
        hshift1'
        ((2 / (L (n + 1) : ℝ)) *
          fista_momentum_sequence (n + 1) ^ (2 : ℕ) * vR (n + 2))
  simpa [vR, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hshift2

/-- Helper for Theorem 10.40: the exact MFISTA Lyapunov energy contracts in one step. -/
lemma mfistaEnergyStep
    (htraj : hproblem.IsMfistaTrajectory x y z L)
    (hrule : hproblem.SublinearRateStepsizeRule y L α)
    (hxStar : xStar ∈ XStar)
    (n : ℕ) :
    let vR : ℕ → ℝ :=
      fun m ↦ (composite_model_objective f.toEReal g (x m)).toReal - FOpt
    let ER : ℕ → ℝ :=
      fun m ↦
        ‖mfistaResidualToOptimal x z xStar m‖ ^ (2 : ℕ) +
          (2 / (L m : ℝ)) * fista_momentum_sequence m ^ (2 : ℕ) * vR (m + 1)
    ER (n + 1) ≤ ER n := by
  dsimp
  let vR : ℕ → ℝ :=
    fun m ↦ (composite_model_objective f.toEReal g (x m)).toReal - FOpt
  let ER : ℕ → ℝ :=
    fun m ↦
      ‖mfistaResidualToOptimal x z xStar m‖ ^ (2 : ℕ) +
        (2 / (L m : ℝ)) * fista_momentum_sequence m ^ (2 : ℕ) * vR (m + 1)
  have hbalance :
      ‖mfistaResidualToOptimal x z xStar (n + 1)‖ ^ (2 : ℕ) +
          (2 / (L (n + 1) : ℝ)) *
            fista_momentum_sequence (n + 1) ^ (2 : ℕ) * vR (n + 2) ≤
        ‖mfistaResidualToOptimal x z xStar n‖ ^ (2 : ℕ) +
          (2 / (L (n + 1) : ℝ)) *
            fista_momentum_sequence n ^ (2 : ℕ) * vR (n + 1) := by
    -- Start from the raw shared-denominator Lyapunov balance.
    simpa [vR] using
      (mfistaAcceptedStepEnergyBalance
        (hproblem := hproblem) (htraj := htraj) (hrule := hrule) (hxStar := hxStar) n)
  have hstepsize_mono :
      (L n : ℝ) ≤ (L (n + 1) : ℝ) :=
    (mfistaStepsizeControl (hproblem := hproblem) hrule).1 n
  have hgap_nonneg :
      0 ≤ vR (n + 1) := by
    -- The transport from `L_(n+1)` back to `L_n` is valid because the previous gap is nonnegative.
    simpa [vR] using
      (mfistaPositiveIterateGapNonneg
        (hproblem := hproblem) (htraj := htraj) n)
  have htransport :
      (2 / (L (n + 1) : ℝ)) * fista_momentum_sequence n ^ (2 : ℕ) * vR (n + 1) ≤
        (2 / (L n : ℝ)) * fista_momentum_sequence n ^ (2 : ℕ) * vR (n + 1) := by
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
        0 ≤ fista_momentum_sequence n ^ (2 : ℕ) * vR (n + 1) := by
      exact mul_nonneg (by positivity) hgap_nonneg
    -- Only the right-hand denominator changes when we transport the energy from `L_(n+1)` to `L_n`.
    have htransport' := mul_le_mul_of_nonneg_right hrecip hterm_nonneg
    simpa [mul_assoc, mul_left_comm, mul_comm] using htransport'
  have hfinal :
      ER (n + 1) ≤
        ‖mfistaResidualToOptimal x z xStar n‖ ^ (2 : ℕ) +
          (2 / (L n : ℝ)) * fista_momentum_sequence n ^ (2 : ℕ) * vR (n + 1) := by
    -- Compose the raw balance with the one-line denominator transport.
    nlinarith [hbalance, htransport]
  simpa [ER] using hfinal

/-- Theorem 10.40: under Assumption 10.31, any MFISTA trajectory whose curvature estimates are
chosen either by the constant rule `L_k = L_f` with `α = 1` or by backtracking procedure B3 with
`α = max {η, s / L_f}` satisfies the accelerated objective-gap bound
`F(x^k) - F_opt ≤ 2 α L_f ‖x^0 - x*‖^2 / (k + 1)^2` for every optimizer `x* ∈ X^*` and every
`k ≥ 1`. -/
theorem mfista_objective_gap_le_two_alpha_Lf_dist_sq_div_sq
    (htraj : hproblem.IsMfistaTrajectory x y z L)
    (hrule : hproblem.SublinearRateStepsizeRule y L α)
    (hxStar : xStar ∈ XStar) (k : ℕ) (hk : 1 ≤ k) :
    composite_model_objective f.toEReal g (x k) - (FOpt : EReal) ≤
      (((2 * α * (Lf : ℝ) * ‖x 0 - xStar‖ ^ (2 : ℕ)) / (k + 1 : ℝ) ^ (2 : ℕ) : ℝ) : EReal) :=
  by
  obtain ⟨K, rfl⟩ := Nat.exists_eq_add_of_le hk
  let vR : ℕ → ℝ :=
    fun n ↦ (composite_model_objective f.toEReal g (x n)).toReal - FOpt
  let ER : ℕ → ℝ :=
    fun n ↦
      ‖mfistaResidualToOptimal x z xStar n‖ ^ (2 : ℕ) +
        (2 / (L n : ℝ)) * fista_momentum_sequence n ^ (2 : ℕ) * vR (n + 1)
  have henergy_le_zero : ∀ n, ER n ≤ ER 0 := by
    intro n
    induction n with
    | zero =>
        exact le_rfl
    | succ n ihn =>
        -- Iterate the one-step Lyapunov contraction from `ER n` down to the initial energy.
        exact le_trans
          (by
            simpa [ER, vR] using
              (mfistaEnergyStep
                (hproblem := hproblem) (htraj := htraj) (hrule := hrule)
                (hxStar := hxStar) n))
          ihn
  have hinitial :
      ER 0 ≤ ‖x 0 - xStar‖ ^ (2 : ℕ) := by
    -- The initial source energy is already bounded by the starting distance to the optimizer.
    simpa [ER, vR] using
      (mfistaInitialEnergyBound
        (hproblem := hproblem) (htraj := htraj) (hrule := hrule) (hxStar := hxStar))
  have henergyK :
      ER K ≤ ‖x 0 - xStar‖ ^ (2 : ℕ) := by
    exact le_trans (henergy_le_zero K) hinitial
  have hgap_term :
      (2 / (L K : ℝ)) * fista_momentum_sequence K ^ (2 : ℕ) * vR (K + 1) ≤
        ‖x 0 - xStar‖ ^ (2 : ℕ) := by
    have hdrop :
        (2 / (L K : ℝ)) * fista_momentum_sequence K ^ (2 : ℕ) * vR (K + 1) ≤ ER K := by
      -- Drop the nonnegative residual norm from the Lyapunov energy.
      dsimp [ER]
      have hres_nonneg :
          0 ≤ ‖mfistaResidualToOptimal x z xStar K‖ ^ (2 : ℕ) := by positivity
      nlinarith
    exact le_trans hdrop henergyK
  have hstepsize_cap :
      (L K : ℝ) ≤ α * (Lf : ℝ) :=
    (mfistaStepsizeControl (hproblem := hproblem) hrule).2 K
  have hLf_pos : 0 < (Lf : ℝ) :=
    hproblem.sublinearRateStepsizeRule_lf_pos hrule
  have hαLf_pos : 0 < α * (Lf : ℝ) := by
    exact lt_of_lt_of_le (PosReal.coe_pos (L K)) hstepsize_cap
  have hvR_nonneg : 0 ≤ vR (K + 1) := by
    -- The final real gap is nonnegative because `x^(K+1)` lies in `effective_domain g`.
    simpa [vR] using
      (mfistaPositiveIterateGapNonneg
        (hproblem := hproblem) (htraj := htraj) K)
  have hscaled_gap :
      2 * fista_momentum_sequence K ^ (2 : ℕ) * vR (K + 1) ≤
        α * (Lf : ℝ) * ‖x 0 - xStar‖ ^ (2 : ℕ) := by
    have hmul :
        (L K : ℝ) *
            ((2 / (L K : ℝ)) * fista_momentum_sequence K ^ (2 : ℕ) * vR (K + 1)) ≤
          (L K : ℝ) * ‖x 0 - xStar‖ ^ (2 : ℕ) := by
      exact mul_le_mul_of_nonneg_left hgap_term (le_of_lt (PosReal.coe_pos (L K)))
    have hmul' :
        2 * fista_momentum_sequence K ^ (2 : ℕ) * vR (K + 1) ≤
          (L K : ℝ) * ‖x 0 - xStar‖ ^ (2 : ℕ) := by
      -- Clear the positive denominator `L_K` from the gap estimate.
      have hmul'' := hmul
      field_simp [ne_of_gt (PosReal.coe_pos (L K))] at hmul''
      nlinarith [hmul'', PosReal.coe_pos (L K)]
    exact le_trans hmul' <|
      mul_le_mul_of_nonneg_right hstepsize_cap (by positivity)
  have hmomentum_lower :
      (((K : ℝ) + 2) / 2) ≤ fista_momentum_sequence K := by
    exact
      fista_momentum_sequence_lower_bound
        (t := fista_momentum_sequence)
        (h0 := fista_momentum_sequence_zero)
        (hsucc := fista_momentum_sequence_succ)
        K
  have hmomentum_sq :
      ((K : ℝ) + 2) ^ (2 : ℕ) ≤ 4 * fista_momentum_sequence K ^ (2 : ℕ) := by
    -- Square the standard lower bound `((K : ℝ) + 2) / 2 ≤ t_K`.
    have hdouble :
        (K : ℝ) + 2 ≤ 2 * fista_momentum_sequence K := by
      nlinarith [hmomentum_lower]
    nlinarith [hdouble]
  have hscaled_final :
      ((K : ℝ) + 2) ^ (2 : ℕ) * vR (K + 1) ≤
        2 * α * (Lf : ℝ) * ‖x 0 - xStar‖ ^ (2 : ℕ) := by
    have hleft :
        ((K : ℝ) + 2) ^ (2 : ℕ) * vR (K + 1) ≤
          (4 * fista_momentum_sequence K ^ (2 : ℕ)) * vR (K + 1) := by
      exact mul_le_mul_of_nonneg_right hmomentum_sq hvR_nonneg
    have hright :
        (4 * fista_momentum_sequence K ^ (2 : ℕ)) * vR (K + 1) ≤
          2 * α * (Lf : ℝ) * ‖x 0 - xStar‖ ^ (2 : ℕ) := by
      nlinarith [hscaled_gap]
    exact le_trans hleft hright
  have hk_den_pos :
      0 < ((K : ℝ) + 2) ^ (2 : ℕ) := by
    positivity
  have hreal :
      vR (K + 1) ≤
        (2 * α * (Lf : ℝ) * ‖x 0 - xStar‖ ^ (2 : ℕ)) /
          ((K : ℝ) + 2) ^ (2 : ℕ) := by
    -- Divide the scaled bound by the positive factor `((K : ℝ) + 2)^2`.
    exact (le_div_iff₀ hk_den_pos).2 <| by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hscaled_final
  have hK_eff :
      x (K + 1) ∈ effective_domain g :=
    mfistaPositiveIterate_memEffectiveDomainG (hproblem := hproblem) htraj K
  have hK_eff' :
      x (1 + K) ∈ effective_domain g := by
    simpa [Nat.add_comm] using hK_eff
  have hreal' :
      vR (K + 1) ≤
        (2 * α * (Lf : ℝ) * ‖x 0 - xStar‖ ^ (2 : ℕ)) /
          (((K + 1 : ℕ) : ℝ) + 1) ^ (2 : ℕ) := by
    have hdenom :
        ((K : ℝ) + 2) ^ (2 : ℕ) = ((K : ℝ) + (1 + 1)) ^ (2 : ℕ) := by
      ring
    rw [Nat.cast_add, Nat.cast_one, add_assoc]
    rw [← hdenom]
    exact hreal
  -- Convert the final real estimate back to the public `EReal` objective-gap statement.
  rw [← mfistaObjectiveGap_eq_coe_sub_toReal_of_memEffectiveDomain
    (hproblem := hproblem) hK_eff']
  simpa [vR, Nat.add_comm, Nat.cast_add, Nat.cast_one, mul_assoc, mul_left_comm, mul_comm] using
    (EReal.coe_le_coe_iff.mpr hreal')

end
