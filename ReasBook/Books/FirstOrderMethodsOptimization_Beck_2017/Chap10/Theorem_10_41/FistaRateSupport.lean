/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap10.Algorithm_10_6
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Definition_5_16
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Lemma_10_33
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_2
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_21
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Theorem_10_16
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Theorem_10_21

noncomputable section

universe u

open scoped Gradient

section ObjectiveBridge

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
variable {f : E → ℝ} {g : E → EReal} {XStar : Set E} {FOpt : ℝ} {Lf : NNReal}
variable [hproblem : IsFastProximalGradientProblem f g XStar FOpt Lf]

/-- Helper for Theorem 10.41: on `effective_domain g`, the composite objective is the finite real
sum `f + g`. -/
theorem fistaObjectiveEqRealOfMemEffectiveDomain
    (hproblem : IsFastProximalGradientProblem f g XStar FOpt Lf)
    {xPoint : E} (hxPoint : xPoint ∈ effective_domain g) :
    composite_model_objective f.toEReal g xPoint =
      (((f xPoint + (g xPoint).toReal : ℝ)) : EReal) := by
  -- Normalize finite composite objectives through the canonical Chapter 10 bridge once.
  exact
    objectiveEqReal_of_memEffectiveDomainG
      (hproblem := hproblem.toIsConvexCompositeSmoothMinimizationProblem)
      hxPoint

/-- Helper for Theorem 10.41: every finite objective gap is the cast of its real gap. -/
theorem fistaObjectiveGapEqCoeSubToRealOfMemEffectiveDomain
    (hproblem : IsFastProximalGradientProblem f g XStar FOpt Lf)
    {xPoint : E} (hxPoint : xPoint ∈ effective_domain g) :
    ((((composite_model_objective f.toEReal g xPoint).toReal - FOpt : ℝ)) : EReal) =
      composite_model_objective f.toEReal g xPoint - (FOpt : EReal) := by
  -- Reuse the existing finite-gap bridge instead of reopening the `EReal` arithmetic locally.
  exact
    objectiveMinusFOpt_eq_coe_sub_toReal_of_memEffectiveDomainG
      (hproblem := hproblem.toIsConvexCompositeSmoothMinimizationProblem)
      hxPoint

/-- Helper for Theorem 10.41: every finite objective value is at least the optimal value `FOpt`. -/
theorem fistaToRealGeFOptOfMemEffectiveDomain
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

/-- Helper for Theorem 10.41: explicit-owner spelling of the generic FISTA iterate sequence. -/
private abbrev fistaX
    (hproblem : IsFastProximalGradientProblem f g XStar FOpt Lf)
    (x0 : E) (L : ℕ → PosReal) : ℕ → E :=
  @fista_x E _ _ _ f g hproblem.g_proper ⟨hproblem.g_closed⟩ ⟨hproblem.g_convex⟩ x0 L

/-- Helper for Theorem 10.41: explicit-owner spelling of the generic FISTA momentum sequence. -/
private abbrev fistaT
    (hproblem : IsFastProximalGradientProblem f g XStar FOpt Lf)
    (x0 : E) (L : ℕ → PosReal) : ℕ → ℝ :=
  @fista_t E _ _ _ f g hproblem.g_proper ⟨hproblem.g_closed⟩ ⟨hproblem.g_convex⟩ x0 L

/-- Helper for Theorem 10.41: explicit-owner spelling of the generic FISTA extrapolated sequence.
-/
private abbrev fistaY
    (hproblem : IsFastProximalGradientProblem f g XStar FOpt Lf)
    (x0 : E) (L : ℕ → PosReal) : ℕ → E :=
  @fista_y E _ _ _ f g hproblem.g_proper ⟨hproblem.g_closed⟩ ⟨hproblem.g_convex⟩ x0 L

/-- Helper for Theorem 10.41: the generic FISTA Lyapunov residual
`u^0 = x^0 - xStar` and
`u^(k+1) = t_k x^(k+1) - (xStar + (t_k - 1) x^k)`. -/
def fistaLyapunovResidual
    (hproblem : IsFastProximalGradientProblem f g XStar FOpt Lf)
    (x0 : E) (L : ℕ → PosReal) (xStar : E) : ℕ → E
  | 0 => x0 - xStar
  | k + 1 =>
      ((fistaT hproblem x0 L k : ℝ) •
          fistaX hproblem x0 L (k + 1)) -
        (xStar + ((fistaT hproblem x0 L k : ℝ) - 1) •
          fistaX hproblem x0 L k)

/-- Helper for Theorem 10.41: the first positive Lyapunov residual is
`u^1 = x^1 - xStar`. -/
@[simp] theorem fistaLyapunovResidualOne
    (hproblem : IsFastProximalGradientProblem f g XStar FOpt Lf)
    (x0 : E) (L : ℕ → PosReal) (xStar : E) :
    fistaLyapunovResidual hproblem x0 L xStar 1 =
      fistaX hproblem x0 L 1 - xStar := by
  -- Evaluate the residual at the first positive index and simplify `t_0 = 1`.
  simp [fistaLyapunovResidual]

/-- Helper for Theorem 10.41: every positive generic FISTA iterate lies in `effective_domain g`.
-/
theorem fistaPositiveIterateMemEffectiveDomain
    {n : ℕ} (hn : 1 ≤ n) :
    fistaX hproblem x0 L n ∈ effective_domain g := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  -- Positive FISTA iterates are prox-gradient points, so they are feasible for `g`.
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

/-- Helper for Theorem 10.41: every positive generic FISTA objective gap is nonnegative on the
real layer. -/
theorem fistaPositiveIterateGapNonneg
    {n : ℕ} (hn : 1 ≤ n) :
    0 ≤
      (composite_model_objective f.toEReal g
        (fistaX hproblem x0 L n)).toReal - FOpt := by
  have hxsucc_g :
      fistaX hproblem x0 L n ∈ effective_domain g :=
    fistaPositiveIterateMemEffectiveDomain
      (hproblem := hproblem) (x0 := x0) (L := L) hn
  -- Feasible positive iterates inherit the global lower bound `FOpt`.
  exact sub_nonneg.mpr <|
    fistaToRealGeFOptOfMemEffectiveDomain hproblem hxsucc_g

/-- Helper for Theorem 10.41: any optimizer has finite `g`-value. -/
theorem fistaOptimalPointMemEffectiveDomain
    (hproblem : IsFastProximalGradientProblem f g XStar FOpt Lf)
    (hxStar : xStar ∈ XStar) :
    xStar ∈ effective_domain g := by
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
  -- An optimizer cannot have infinite regularizer value because its composite value is `FOpt`.
  exact mem_effective_domain.mpr (lt_top_iff_ne_top.mpr hg_top)

/-- Helper for Theorem 10.41: the reciprocal of the generic FISTA momentum coefficient belongs to
`[0, 1]`. -/
theorem fistaOneDivMomentumMemIcc
    (n : ℕ) :
    (1 / fistaT hproblem x0 L (n + 1) : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
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

/-- Helper for Theorem 10.41: the generic FISTA momentum recursion satisfies
`t_(n+1)^2 - t_(n+1) = t_n^2`. -/
theorem fistaMomentumSqSubEqPrevSq
    (n : ℕ) :
    fistaT hproblem x0 L (n + 1) ^ (2 : ℕ) -
        fistaT hproblem x0 L (n + 1) =
      fistaT hproblem x0 L n ^ (2 : ℕ) := by
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
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
  -- The squared radical identity is exactly the source recurrence.
  nlinarith

/-- Helper for Theorem 10.41: the generic FISTA comparison point
`(1 / t_(n+1)) • xStar + (1 - 1 / t_(n+1)) • x^(n+1)` stays in `effective_domain g`. -/
theorem fistaCombinationPointMemEffectiveDomain
    (hxStar : xStar ∈ XStar)
    (n : ℕ) :
    let θ : ℝ := 1 / fistaT hproblem x0 L (n + 1)
    let w : E := θ • xStar + (1 - θ) • fistaX hproblem x0 L (n + 1)
    w ∈ effective_domain g := by
  dsimp
  have hxStar_eff :
      xStar ∈ effective_domain g :=
    fistaOptimalPointMemEffectiveDomain
      hproblem hxStar
  have hxsucc_eff :
      fistaX hproblem x0 L (n + 1) ∈ effective_domain g :=
    fistaPositiveIterateMemEffectiveDomain
      (hproblem := hproblem) (x0 := x0) (L := L)
      (show 1 ≤ n + 1 by exact Nat.succ_le_succ (Nat.zero_le n))
  have hθ_mem :
      (1 / fistaT hproblem x0 L (n + 1) : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    simpa using
      fistaOneDivMomentumMemIcc
        (hproblem := hproblem) (x0 := x0) (L := L) n
  -- Convexity of `g` keeps the comparison point inside `effective_domain g`.
  exact combo_mem_effective_domain_of_is_convex_function hproblem.g_convex
    hxStar_eff hxsucc_eff hθ_mem

/-- Helper for Theorem 10.41: convexity bounds the objective of the generic FISTA comparison point
by `(1 - 1 / t_(n+1)) v_(n+1) + FOpt` on the real layer. -/
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
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  dsimp
  let θ : ℝ := 1 / fistaT hproblem x0 L (n + 1)
  let w : E := θ • xStar + (1 - θ) • fistaX hproblem x0 L (n + 1)
  have hxStar_eff :
      xStar ∈ effective_domain g :=
    fistaOptimalPointMemEffectiveDomain
      hproblem hxStar
  have hxsucc_eff :
      fistaX hproblem x0 L (n + 1) ∈ effective_domain g :=
    fistaPositiveIterateMemEffectiveDomain
      (hproblem := hproblem) (x0 := x0) (L := L)
      (show 1 ≤ n + 1 by exact Nat.succ_le_succ (Nat.zero_le n))
  have hθ_mem : θ ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [θ] using
      fistaOneDivMomentumMemIcc
        (hproblem := hproblem) (x0 := x0) (L := L) n
  have hθ_nonneg : 0 ≤ θ := hθ_mem.1
  have hθ_le_one : θ ≤ 1 := hθ_mem.2
  have hone_sub_nonneg : 0 ≤ 1 - θ := sub_nonneg.mpr hθ_le_one
  have hw_eff : w ∈ effective_domain g := by
    -- Reuse the feasibility lemma at the exact comparison point.
    simpa [θ, w] using
      fistaCombinationPointMemEffectiveDomain
        (hproblem := hproblem) (x0 := x0) (L := L) hxStar n
  have hw_obj :
      composite_model_objective f.toEReal g w =
        (((f w + (g w).toReal : ℝ)) : EReal) :=
    fistaObjectiveEqRealOfMemEffectiveDomain hproblem hw_eff
  have hxsucc_obj :
      composite_model_objective f.toEReal g (fistaX hproblem x0 L (n + 1)) =
        (((f (fistaX hproblem x0 L (n + 1)) +
            (g (fistaX hproblem x0 L (n + 1))).toReal : ℝ)) : EReal) :=
    fistaObjectiveEqRealOfMemEffectiveDomain hproblem hxsucc_eff
  have hxStar_obj :
      composite_model_objective f.toEReal g xStar =
        (((f xStar + (g xStar).toReal : ℝ)) : EReal) :=
    fistaObjectiveEqRealOfMemEffectiveDomain hproblem hxStar_eff
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
    -- Jensen's inequality for `g` is read at the exact comparison point.
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
    -- Convexity of `f` gives the same Jensen bound on the smooth term.
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

/-- Helper for Theorem 10.41: once both endpoints are finite, the accepted upper-model inequality
becomes the real prox-gap estimate used in the FISTA Lyapunov proof. -/
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
    -- Apply the fundamental prox-gradient inequality at the accepted point.
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
    fistaObjectiveEqRealOfMemEffectiveDomain hproblem hxPoint
  have hxPlus_obj :
      composite_model_objective f.toEReal g xPlus =
        (((f xPlus + (g xPlus).toReal : ℝ)) : EReal) :=
    fistaObjectiveEqRealOfMemEffectiveDomain hproblem hxPlus
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
  -- Rewrite the finite objective difference into the canonical real subtraction.
  rw [hdiff] at hstepE'
  exact EReal.coe_le_coe_iff.mp hstepE'

/-- Helper for Theorem 10.41: the first generic FISTA Lyapunov energy is bounded by the initial
distance to an optimizer on the exact `2 / L_0` source surface. -/
private theorem fistaInitialEnergyBound
    (hrule : hproblem.SublinearRateStepsizeRule
      (fistaY hproblem x0 L) L α)
    (hxStar : xStar ∈ XStar) :
    let vR : ℕ → ℝ :=
      fun n ↦ (composite_model_objective f.toEReal g
        (fistaX hproblem x0 L n)).toReal - FOpt
    ‖fistaLyapunovResidual hproblem x0 L xStar 1‖ ^ (2 : ℕ) +
        (2 / (L 0 : ℝ)) * fistaT hproblem x0 L 0 ^ (2 : ℕ) * vR 1 ≤
      ‖x0 - xStar‖ ^ (2 : ℕ) := by
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  dsimp
  have hL0_pos : 0 < (L 0 : ℝ) := PosReal.coe_pos (L 0)
  have hxStar_eff :
      xStar ∈ effective_domain g :=
    fistaOptimalPointMemEffectiveDomain
      hproblem hxStar
  have hx1_eff :
      fistaX hproblem x0 L 1 ∈ effective_domain g :=
    fistaPositiveIterateMemEffectiveDomain
      (hproblem := hproblem) (x0 := x0) (L := L) (show 1 ≤ 1 by simp)
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
    rw [fistaObjectiveEqRealOfMemEffectiveDomain hproblem (xPoint := xStar) hxStar_eff,
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
        (xPoint := xStar) (yPoint := x0) (Lbar := L 0)
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
        -- Move the objective drop to the left side of the accepted prox-gap inequality.
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
  -- Collapse `u¹ = x¹ - xStar` and `t₀ = 1`.
  simpa [fistaLyapunovResidualOne, fistaT, fista_t_zero, norm_sub_rev] using hbase_x1

/-- Helper for Theorem 10.41: squaring the momentum lower bound gives
`((n : ℝ) + 2)^2 ≤ 4 t_n^2`. -/
theorem fistaMomentumSqLowerBound
    (n : ℕ) :
    ((n : ℝ) + 2) ^ (2 : ℕ) ≤ 4 * fista_momentum_sequence n ^ (2 : ℕ) := by
  have hlinear : (n : ℝ) + 2 ≤ 2 * fista_momentum_sequence n := by
    have hlower :=
      fista_momentum_sequence_lower_bound
        (t := fista_momentum_sequence)
        (h0 := fista_momentum_sequence_zero)
        (hsucc := fista_momentum_sequence_succ)
        n
    nlinarith [hlower]
  -- Square the standard linear lower bound on the momentum sequence.
  nlinarith [hlinear]

end FistaRate
