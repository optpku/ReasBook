/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap10.Algorithm_10_13
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Algorithm_10_6
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Definition_5_16
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Lemma_5_20
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Theorem_5_25
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Assumption_10_31
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_2
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_21
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Theorem_10_16
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Theorem_10_21
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Theorem_10_34

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
variable {f : E → ℝ} {g : E → EReal} {XStar : Set E} {FOpt : ℝ}
variable {Lf σ : PosReal}
variable {xStar zMinusOne : E} {N : ℕ+} {R : ℝ}

section Problem

variable [hproblem : IsFastProximalGradientProblem f g XStar FOpt (PosReal.toNNReal Lf)]

/-- Helper for Theorem 10.41: explicit owner spelling of the restarted FISTA outer sequence. -/
private abbrev restartedZ : ℕ → E :=
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  restarted_fista f g Lf zMinusOne N

/-- Helper for Theorem 10.41: after the initial prox step, the constant-stepsize FISTA iterate
owner from Algorithm 10.13 agrees with the generic FISTA iterate owner from Algorithm 10.6 under
the constant schedule `fun _ ↦ Lf`, shifted by one index because Algorithm 10.13 starts from
`x⁰ = T[Lf; f, g] z` while Algorithm 10.6 starts from `x⁰ = z`. -/
theorem constantStepsizeIterateEqFistaFromFirstProx
    [IsProperExtendedRealFunction g] [Fact (LowerSemicontinuous g)]
    [Fact (is_convex_function g)]
    (z : E) (k : ℕ) :
    fista_constant_stepsize_x f g Lf z k =
      fista_x f g z (fun _ ↦ Lf) (k + 1) := by
  have ht :
      ∀ m : ℕ,
        fista_t f g z (fun _ ↦ Lf) m =
          fista_momentum_sequence m := by
    intro m
    induction m with
    | zero =>
        rw [fista_t_zero, fista_momentum_sequence_zero]
    | succ m ihm =>
        rw [fista_t_succ, ihm, fista_momentum_sequence_succ]
  -- Route correction: synchronize the constant-stepsize and generic `x`/`y` views with the
  -- one-index shift forced by the different initial states in Algorithms 10.13 and 10.6.
  have hviews :
      ∀ m : ℕ,
        fista_constant_stepsize_x f g Lf z m =
            fista_x f g z (fun _ ↦ Lf) (m + 1) ∧
          fista_constant_stepsize_y f g Lf z m =
            fista_y f g z (fun _ ↦ Lf) (m + 1) := by
    intro m
    induction m with
    | zero =>
        constructor
        · -- The first constant-stepsize iterate is exactly the first positive
          -- generic FISTA iterate.
          rw [fista_constant_stepsize_x_zero, fista_x_succ, fista_y_zero]
        · -- The first extrapolated points also agree because the generic first
          -- correction vanishes.
          rw [fista_constant_stepsize_y_zero, fista_y_succ, fista_x_zero,
            fista_x_succ, fista_y_zero, ht 0, ht 1]
          simp
    | succ m ih =>
        rcases ih with ⟨hx, hy⟩
        constructor
        · -- Matching extrapolated points gives the same next prox-gradient iterate.
          rw [fista_constant_stepsize_x_succ, fista_x_succ, hy]
        · -- Matching consecutive iterates and momenta makes the extrapolated-point formulas agree.
          have hxNext :
              fista_constant_stepsize_x f g Lf z (m + 1) =
                fista_x f g z (fun _ ↦ Lf) (m + 1 + 1) := by
            rw [fista_constant_stepsize_x_succ, fista_x_succ, hy]
          rw [fista_constant_stepsize_y_succ, fista_y_succ, hxNext, hx, ht (m + 1), ht (m + 2)]
  simpa [Nat.add_comm] using (hviews k).1

/-- Helper for Theorem 10.41: every restarted outer iterate lies in `effective_domain g`
because it is always obtained from a prox-gradient step. -/
theorem restartedIterateMemEffectiveDomain
    (k : ℕ) :
    restartedZ (f := f) (g := g) (Lf := Lf) (XStar := XStar) (FOpt := FOpt)
      (zMinusOne := zMinusOne) (N := N) k ∈ effective_domain g := by
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  cases k with
  | zero =>
      -- The initial restarted point is exactly the first prox-gradient step from `zMinusOne`.
      simpa [restartedZ] using
        (prox_grad_step_mem_effective_domain_g (f := f.toEReal) (g := g)
          (y := interior_effective_domain_point_of_real f zMinusOne) (L := Lf))
  | succ k =>
      have hNpos : 1 ≤ (N : ℕ) := Nat.succ_le_of_lt N.2
      obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le hNpos
      -- A positive inner iterate is again a prox-gradient step taken at the corresponding
      -- extrapolated point.
      rw [restartedZ, restarted_fista_succ, hn, Nat.add_comm, fista_constant_stepsize_x_succ]
      exact
        (prox_grad_step_mem_effective_domain_g (f := f.toEReal) (g := g)
          (y := interior_effective_domain_point_of_real f
            (fista_constant_stepsize_y f g Lf
              (restartedZ (f := f) (g := g) (Lf := Lf) (XStar := XStar) (FOpt := FOpt)
                (zMinusOne := zMinusOne) (N := N) k)
              n))
          (L := Lf))

/-- Helper for Theorem 10.41: every restarted objective gap is the cast of its real-valued gap
because every restart point lies in `effective_domain g`. -/
lemma restartedObjectiveGap_eq_coe_sub_toReal
    (k : ℕ) :
    ((((composite_model_objective f.toEReal g
        (restartedZ (f := f) (g := g) (Lf := Lf) (XStar := XStar) (FOpt := FOpt)
          (zMinusOne := zMinusOne) (N := N) k)).toReal - FOpt : ℝ)) : EReal) =
      composite_model_objective f.toEReal g
        (restartedZ (f := f) (g := g) (Lf := Lf) (XStar := XStar) (FOpt := FOpt)
          (zMinusOne := zMinusOne) (N := N) k) -
        (FOpt : EReal) := by
  -- Normalize the restarted objective gap through the Chapter 10 finite-objective bridge.
  exact
    objectiveMinusFOpt_eq_coe_sub_toReal_of_memEffectiveDomainG
      (hproblem := hproblem.toIsConvexCompositeSmoothMinimizationProblem)
      (restartedIterateMemEffectiveDomain
        (f := f) (g := g) (Lf := Lf) (XStar := XStar) (FOpt := FOpt)
        (zMinusOne := zMinusOne) (N := N) (hproblem := hproblem) k)

/-- Helper for Theorem 10.41: every restarted objective gap is nonnegative on the real layer. -/
lemma restartedObjectiveGapRealNonneg
    (k : ℕ) :
    0 ≤
      (composite_model_objective f.toEReal g
        (restartedZ (f := f) (g := g) (Lf := Lf) (XStar := XStar) (FOpt := FOpt)
          (zMinusOne := zMinusOne) (N := N) k)).toReal - FOpt := by
  have hrestartEff :
      restartedZ (f := f) (g := g) (Lf := Lf) (XStar := XStar) (FOpt := FOpt)
        (zMinusOne := zMinusOne) (N := N) k ∈ effective_domain g :=
    restartedIterateMemEffectiveDomain
      (f := f) (g := g) (Lf := Lf) (XStar := XStar) (FOpt := FOpt)
      (zMinusOne := zMinusOne) (N := N) (hproblem := hproblem) k
  -- Feasible restarted points inherit the global lower bound `FOpt`.
  exact sub_nonneg.mpr <|
    toReal_ge_FOpt_of_memEffectiveDomainG
      (hproblem := hproblem.toIsConvexCompositeSmoothMinimizationProblem)
      hrestartEff

/-- Helper for Theorem 10.41: the restart-length choice forces the cycle contraction factor
`4 κ(PosReal.toNNReal Lf, σ) / (N + 1)^2` to be at most `1 / 2`. -/
theorem restartLengthContractionFactorLeHalf
    (hN : (N : ℕ) = Nat.ceil (Real.sqrt (8 * κ(PosReal.toNNReal Lf, σ) - 1))) :
    4 * κ(PosReal.toNNReal Lf, σ) / (((N : ℕ) + 1 : ℝ) ^ (2 : ℕ)) ≤ 1 / 2 := by
  let κR : ℝ := κ(PosReal.toNNReal Lf, σ)
  have hNpos : 0 < (N : ℕ) := N.2
  have hsqrt_pos : 0 < Real.sqrt (8 * κR - 1) := by
    rw [hN] at hNpos
    exact Nat.ceil_pos.mp hNpos
  have hrad_nonneg : 0 ≤ 8 * κR - 1 := le_of_lt (Real.sqrt_pos.mp hsqrt_pos)
  have hsqrt_le : Real.sqrt (8 * κR - 1) ≤ (N : ℝ) := by
    rw [hN]
    exact Nat.le_ceil _
  have hsqrt_add_le : Real.sqrt (8 * κR - 1) + 1 ≤ ((N : ℕ) + 1 : ℝ) := by
    nlinarith
  have hbound_from_root :
      8 * κR ≤ (Real.sqrt (8 * κR - 1) + 1) ^ (2 : ℕ) := by
    have hsqrt_nonneg : 0 ≤ Real.sqrt (8 * κR - 1) := Real.sqrt_nonneg _
    have hsq : Real.sqrt (8 * κR - 1) * Real.sqrt (8 * κR - 1) = 8 * κR - 1 := by
      simpa [pow_two] using Real.sq_sqrt hrad_nonneg
    rw [pow_two, add_mul, mul_add, mul_one, one_mul]
    nlinarith
  have hbound :
      8 * κR ≤ (((N : ℕ) + 1 : ℝ) ^ (2 : ℕ)) := by
    have hsq :
        (Real.sqrt (8 * κR - 1) + 1) ^ (2 : ℕ) ≤
          (((N : ℕ) + 1 : ℝ) ^ (2 : ℕ)) := by
      nlinarith [hsqrt_add_le, Real.sqrt_nonneg (8 * κR - 1)]
    exact le_trans hbound_from_root hsq
  have hden_pos : 0 < (((N : ℕ) + 1 : ℝ) ^ (2 : ℕ)) := by
    positivity
  -- Rewrite the denominator estimate into the displayed `1 / 2` contraction factor.
  have hhalf :
      4 * κR ≤ (1 / 2 : ℝ) * (((N : ℕ) + 1 : ℝ) ^ (2 : ℕ)) := by
    nlinarith [hbound]
  have hden_ne : (((N : ℕ) + 1 : ℝ) ^ (2 : ℕ)) ≠ 0 := by
    exact hden_pos.ne'
  field_simp [hden_ne]
  linarith

/-- Helper for Theorem 10.41: the ceil formula for the restart length gives the exact upper bound
`N < √(8 κ(PosReal.toNNReal Lf, σ) - 1) + 1`. -/
theorem restartLengthLtSqrtEightKappaSubOneAddOne
    (hN : (N : ℕ) = Nat.ceil (Real.sqrt (8 * κ(PosReal.toNNReal Lf, σ) - 1))) :
    ((N : ℕ) : ℝ) < Real.sqrt (8 * κ(PosReal.toNNReal Lf, σ) - 1) + 1 := by
  -- This is the standard upper bound on a natural ceiling.
  rw [hN]
  exact Nat.ceil_lt_add_one (Real.sqrt_nonneg _)

/-- Helper for Theorem 10.41: the constant schedule `L_k = L_f` is the constant branch of the
generic FISTA sublinear-rate rule. -/
lemma genericConstantScheduleRule
    [IsProperExtendedRealFunction g] [Fact (LowerSemicontinuous g)]
    [Fact (is_convex_function g)]
    (z : E) :
    hproblem.SublinearRateStepsizeRule
      (fista_y f g z (fun _ ↦ Lf))
      (fun _ ↦ Lf) 1 := by
  -- The Chapter 10 rule is in the constant branch because every curvature estimate is exactly
  -- `L_f`.
  left
  constructor
  · norm_num
  · intro n
    simp [PosReal.coe_toNNReal]


omit hproblem in
/-- Helper for Theorem 10.41: the first prox-gradient step from any restart point is no farther
from the optimizer `xStar` than the restart point itself. -/
lemma proxStepDistSqLeRestartDist
    [IsProperExtendedRealFunction g] [Fact (LowerSemicontinuous g)]
    [Fact (is_convex_function g)]
    [hfast : IsFastProximalGradientProblem f g XStar FOpt (PosReal.toNNReal Lf)]
    {xStar : E}
    (hxStar : xStar ∈ XStar)
    (z : E) :
    ‖T[Lf; f, g] z - xStar‖ ^ (2 : ℕ) ≤ ‖z - xStar‖ ^ (2 : ℕ) := by
  let x : ℕ → E := fun n ↦ Nat.rec z (fun _ xk ↦ T[Lf; f, g] xk) n
  let hconv := hfast.toIsConvexCompositeSmoothMinimizationProblem
  have htraj :
      is_proximal_gradient_trajectory f.toEReal g x (fun _ ↦ Lf) :=
    by
      intro n
      constructor
      · exact mem_interior_effective_domain_of_coe_real f (x n)
      · have hsingleton :
            proximal_gradient_step f.toEReal g (x n) Lf = {x (n + 1)} := by
          rw [show x (n + 1) = T[Lf; f, g] (x n) by simp [x]]
          simpa [prox_gradient_operator_apply] using
            (prox_grad_operator_eq_singleton f.toEReal g Lf
              (interior_effective_domain_point_of_real f (x n)))
        rw [hsingleton]
        simp
  have hrule :
      hconv.SourceSublinearRateStepsizeRule
        x
        (fun _ ↦ Lf)
        htraj
        1 :=
    by
      -- The orbit uses the exact constant schedule `L_k = L_f`, so it is the constant branch.
      left
      constructor
      · norm_num
      · intro n
        simp [PosReal.coe_toNNReal]
  have hx1_g :
      x 1 ∈ effective_domain g :=
    proximalGradientPositiveIterate_memEffectiveDomainG
      (hproblem := hconv)
      htraj
      0
  have hgap_nonneg :
      0 ≤ (composite_model_objective f.toEReal g (x 1)).toReal - FOpt := by
    -- The first prox-gradient iterate has finite objective value, so its
    -- objective gap is nonnegative.
    exact sub_nonneg.mpr <|
      toReal_ge_FOpt_of_memEffectiveDomainG
        (hproblem := hconv)
        hx1_g
  have hdrop :
      ((composite_model_objective f.toEReal g (x 1)).toReal - FOpt) /
          (1 * (PosReal.toNNReal Lf : ℝ)) ≤
        (‖xStar - x 0‖ ^ (2 : ℕ) - ‖xStar - x 1‖ ^ (2 : ℕ)) / 2 := by
    -- Route correction: use Theorem 10.21's one-step prox-gradient gap/drop inequality at `n = 0`
    -- instead of routing the first-step distance bound through the unfinished FISTA Lyapunov owner.
    simpa [x, PosReal.coe_toNNReal] using
      (proximalGradientOneStepGapDivLeDistSqDrop
        (hproblem := hconv)
        (x := x)
        (L := fun _ ↦ Lf)
        (α := 1)
        (xStar := xStar)
        htraj
        hrule
        hxStar
        0)
  have hquot_nonneg :
      0 ≤
        ((composite_model_objective f.toEReal g (x 1)).toReal - FOpt) /
          (1 * (PosReal.toNNReal Lf : ℝ)) := by
    have hden_pos : 0 < (1 * (PosReal.toNNReal Lf : ℝ)) := by
      have hLf_pos : 0 < (PosReal.toNNReal Lf : ℝ) := by
        exact_mod_cast PosReal.coe_pos Lf
      nlinarith
    exact div_nonneg hgap_nonneg (le_of_lt hden_pos)
  have hdist :
      ‖xStar - x 1‖ ^ (2 : ℕ) ≤ ‖xStar - x 0‖ ^ (2 : ℕ) := by
    -- Dropping the nonnegative normalized objective gap leaves the desired squared-distance drop.
    nlinarith
  simpa [x, norm_sub_rev] using hdist

/-- Helper for Theorem 10.41: strong convexity of `f` and convexity of `g` force every restarted
objective gap to dominate `σ ‖z^n - xStar‖² / 2`. -/
lemma restartedObjectiveGapLowerQuadraticReal
    (hstrong : StrongConvexOn Set.univ (σ : ℝ) f)
    (hxStar : xStar ∈ XStar)
    (n : ℕ) :
    ((σ : ℝ) / 2) *
        ‖restartedZ (f := f) (g := g) (Lf := Lf) (XStar := XStar) (FOpt := FOpt)
          (zMinusOne := zMinusOne) (N := N) n - xStar‖ ^ (2 : ℕ) ≤
      (composite_model_objective f.toEReal g
        (restartedZ (f := f) (g := g) (Lf := Lf) (XStar := XStar) (FOpt := FOpt)
          (zMinusOne := zMinusOne) (N := N) n)).toReal - FOpt := by
  let restartPoint :=
    restartedZ (f := f) (g := g) (Lf := Lf) (XStar := XStar) (FOpt := FOpt)
      (zMinusOne := zMinusOne) (N := N) n
  let F := composite_model_objective f.toEReal g
  have hfStrong : is_strongly_convex_function f.toEReal (σ : ℝ) := by
    -- Transport the real-valued strong-convexity hypothesis to the Chapter 5 owner on `f.toEReal`.
    refine is_strongly_convex_function_iff_strongConvexOn_toReal.mpr ?_
    refine ⟨PosReal.coe_pos σ, ?_, ?_⟩
    · intro x
      simp [Function.toEReal]
    · have hdom : effective_domain f.toEReal = Set.univ := by
        ext x
        simp [effective_domain, Function.toEReal]
      rw [hdom]
      simpa [Function.toEReal] using hstrong
  have hFStrong : is_strongly_convex_function F (σ : ℝ) := by
    -- Add the convex regularizer `g` to obtain strong convexity of the composite objective.
    simpa [F, composite_model_objective_apply, Function.toEReal] using
      (is_strongly_convex_function_add_of_is_convex_function
        hfStrong hproblem.g_convex hproblem.g_proper.ne_bot)
  have hxStarMin : IsMinOn F Set.univ xStar := by
    -- Rewrite optimizer membership as the global minimizer property for the composite objective.
    rw [isMinOn_univ_iff]
    have hxOpt : xStar ∈ unconstrained_problem_solutions F := by
      simpa [hproblem.optimal_set_eq] using hxStar
    exact mem_unconstrained_problem_solutions_iff_forall_le.mp hxOpt
  have hrestartEffG :
      restartPoint ∈ effective_domain g :=
    restartedIterateMemEffectiveDomain
      (f := f) (g := g) (Lf := Lf) (XStar := XStar) (FOpt := FOpt)
      (zMinusOne := zMinusOne) (N := N) (hproblem := hproblem) n
  have hrestartEff :
      restartPoint ∈ effective_domain F := by
    -- The restarted point has finite `g`-value, so the composite objective is finite there too.
    have hvalue :
        F restartPoint =
          (((f restartPoint + (g restartPoint).toReal : ℝ)) : EReal) := by
      exact
        objectiveEqReal_of_memEffectiveDomainG
          (hproblem := hproblem.toIsConvexCompositeSmoothMinimizationProblem)
          hrestartEffG
    exact mem_effective_domain.mpr <| by
      rw [hvalue]
      simpa using (EReal.coe_lt_top (f restartPoint + (g restartPoint).toReal))
  have hquad :
      F restartPoint ≥
        F xStar +
          ((((σ : ℝ) / 2) * ‖restartPoint - xStar‖ ^ (2 : ℕ) : ℝ) : EReal) := by
    -- Apply the Chapter 5 quadratic-growth theorem to the strongly convex composite objective.
    simpa [F, restartPoint] using
      (lower_quadratic_bound_of_isMinOn_of_strongly_convex
        (f := F) (σ := (σ : ℝ))
        hFStrong xStar hxStarMin restartPoint hrestartEff)
  have hrestartReal :
      F restartPoint = ((((F restartPoint).toReal : ℝ)) : EReal) := by
    -- Normalize the finite restarted objective value to its real representative.
    have hF_ne_top : F restartPoint ≠ ⊤ :=
      (mem_effective_domain.mp hrestartEff).ne
    have hF_ne_bot : F restartPoint ≠ ⊥ := by
      dsimp [F]
      exact EReal.add_ne_bot_iff.mpr ⟨by simp, hproblem.g_proper.ne_bot _⟩
    exact (EReal.coe_toReal hF_ne_top hF_ne_bot).symm
  have hsum :
      (((FOpt + ((σ : ℝ) / 2) * ‖restartPoint - xStar‖ ^ (2 : ℕ) : ℝ)) : EReal) ≤
        ((((F restartPoint).toReal : ℝ)) : EReal) := by
    -- Rewrite the optimizer value and the restarted-point value onto the finite real surface.
    have hxStarValue :
        F xStar = (FOpt : EReal) :=
      IsConvexCompositeSmoothMinimizationProblem.objective_eq_optimalValue_of_mem_optimalSet
        (h := hproblem.toIsConvexCompositeSmoothMinimizationProblem)
        hxStar
    rw [hxStarValue, hrestartReal] at hquad
    simpa [EReal.coe_add] using hquad
  have hsumReal :
      FOpt + ((σ : ℝ) / 2) * ‖restartPoint - xStar‖ ^ (2 : ℕ) ≤
        (F restartPoint).toReal :=
    EReal.coe_le_coe_iff.mp hsum
  nlinarith

/-- Helper for Theorem 10.41: one completed restart cycle contracts the restarted objective gap by
the exact factor `4 κ(PosReal.toNNReal Lf, σ) / (N + 1)^2`. -/
lemma restartedCycleGapRealLeFactor
    (hstrong : StrongConvexOn Set.univ (σ : ℝ) f)
    (hxStar : xStar ∈ XStar)
    (n : ℕ) :
    (composite_model_objective f.toEReal g
      (restartedZ (f := f) (g := g) (Lf := Lf) (XStar := XStar) (FOpt := FOpt)
        (zMinusOne := zMinusOne) (N := N) (n + 1))).toReal - FOpt ≤
      (4 * κ(PosReal.toNNReal Lf, σ) / (((N : ℕ) + 1 : ℝ) ^ (2 : ℕ))) *
        ((composite_model_objective f.toEReal g
          (restartedZ (f := f) (g := g) (Lf := Lf) (XStar := XStar) (FOpt := FOpt)
            (zMinusOne := zMinusOne) (N := N) n)).toReal - FOpt) := by
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  let restartPoint :=
    restartedZ (f := f) (g := g) (Lf := Lf) (XStar := XStar) (FOpt := FOpt)
      (zMinusOne := zMinusOne) (N := N) n
  let gapNow :=
    (composite_model_objective f.toEReal g restartPoint).toReal - FOpt
  let distSq := ‖restartPoint - xStar‖ ^ (2 : ℕ)
  let dPrev : ℝ := (((N : ℕ) + 1 : ℝ) ^ (2 : ℕ))
  let dNext : ℝ := (((N : ℕ) + 2 : ℝ) ^ (2 : ℕ))
  let a : ℝ := (2 * (Lf : ℝ)) / dPrev
  let b : ℝ := 4 * κ(PosReal.toNNReal Lf, σ) / dPrev
  have hrateE :
      composite_model_objective f.toEReal g
          (restartedZ (f := f) (g := g) (Lf := Lf) (XStar := XStar) (FOpt := FOpt)
            (zMinusOne := zMinusOne) (N := N) (n + 1)) -
          (FOpt : EReal) ≤
        (((2 * (Lf : ℝ) * distSq / dNext : ℝ)) : EReal) := by
    -- Rewrite one outer restart cycle as the shifted constant-schedule FISTA iterate and apply
    -- the published Theorem 10.34 rate before any scalar simplification.
    rw [restartedZ, restarted_fista_succ, constantStepsizeIterateEqFistaFromFirstProx]
    change composite_model_objective f.toEReal g
        (@fista_x E _ _ _ f g hproblem.g_proper ⟨hproblem.g_closed⟩ ⟨hproblem.g_convex⟩
          (restartedZ (f := f) (g := g) (Lf := Lf) (XStar := XStar) (FOpt := FOpt)
            (zMinusOne := zMinusOne) (N := N) n)
          (fun _ ↦ Lf) ((N : ℕ) + 1)) -
          (FOpt : EReal) ≤
      (((2 * (Lf : ℝ) * distSq / dNext : ℝ)) : EReal)
    have hbase :
        composite_model_objective f.toEReal g
            (@fista_x E _ _ _ f g hproblem.g_proper ⟨hproblem.g_closed⟩ ⟨hproblem.g_convex⟩
              (restartedZ (f := f) (g := g) (Lf := Lf) (XStar := XStar) (FOpt := FOpt)
                (zMinusOne := zMinusOne) (N := N) n)
              (fun _ ↦ Lf) ((N : ℕ) + 1)) -
            (FOpt : EReal) ≤
          (((2 * (1 : ℝ) * (Lf : ℝ) *
                ‖restartedZ (f := f) (g := g) (Lf := Lf) (XStar := XStar) (FOpt := FOpt)
                    (zMinusOne := zMinusOne) (N := N) n - xStar‖ ^ (2 : ℕ) /
                ((((N : ℕ) + 1 : ℕ) : ℝ) + 1) ^ (2 : ℕ) : ℝ)) : EReal) := by
      exact
        fista_objective_gap_le_two_alpha_Lf_dist_sq_div_sq
        (hproblem := hproblem)
        (x0 := restartPoint)
        (L := fun _ ↦ Lf)
        (α := 1)
        (hrule := genericConstantScheduleRule
          (f := f) (g := g) (XStar := XStar) (FOpt := FOpt) (Lf := Lf)
          (z := restartPoint) (hproblem := hproblem))
        (hxStar := hxStar)
        (k := (N : ℕ) + 1)
        (hk := by exact Nat.succ_le_succ (Nat.zero_le (N : ℕ)))
    have hdNext_eq :
        ((((N : ℕ) + 1 : ℕ) : ℝ) + 1) ^ (2 : ℕ) = dNext := by
      have hsum : ((((N : ℕ) + 1 : ℕ) : ℝ) + 1) = ((N : ℕ) + 2 : ℝ) := by
        norm_num [Nat.cast_add, add_assoc]
      calc
        ((((N : ℕ) + 1 : ℕ) : ℝ) + 1) ^ (2 : ℕ) = (((N : ℕ) + 2 : ℝ) ^ (2 : ℕ)) := by
          rw [hsum]
        _ = dNext := by
          rfl
    rw [hdNext_eq] at hbase
    simpa [restartPoint, distSq, dNext, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hbase
  have hrateReal :
      (composite_model_objective f.toEReal g
        (restartedZ (f := f) (g := g) (Lf := Lf) (XStar := XStar) (FOpt := FOpt)
          (zMinusOne := zMinusOne) (N := N) (n + 1))).toReal - FOpt ≤
        2 * (Lf : ℝ) * distSq / dNext := by
    -- Move the next-cycle objective gap from `EReal` back to the finite real layer.
    rw [← restartedObjectiveGap_eq_coe_sub_toReal
      (f := f) (g := g) (Lf := Lf) (XStar := XStar) (FOpt := FOpt)
      (zMinusOne := zMinusOne) (N := N) (hproblem := hproblem) (n + 1)] at hrateE
    exact EReal.coe_le_coe_iff.mp hrateE
  have hdNext_pos : 0 < dNext := by
    positivity
  have hdPrev_pos : 0 < dPrev := by
    positivity
  have hdPrev_le_hdNext : dPrev ≤ dNext := by
    -- The shifted Theorem 10.34 denominator `(N + 2)^2` is stronger than the `(N + 1)^2`
    -- denominator used in the restart-cycle factor.
    have hbase : ((N : ℕ) + 1 : ℝ) ≤ ((N : ℕ) + 2 : ℝ) := by
      exact_mod_cast Nat.le_succ ((N : ℕ) + 1)
    dsimp [dPrev, dNext]
    exact pow_le_pow_left₀ (by positivity) hbase 2
  have hrecip :
      1 / dNext ≤ 1 / dPrev := by
    exact one_div_le_one_div_of_le hdPrev_pos hdPrev_le_hdNext
  have hnumerator_nonneg : 0 ≤ 2 * (Lf : ℝ) * distSq := by
    have hdistSq_nonneg : 0 ≤ distSq := by
      dsimp [distSq]
      positivity
    nlinarith [PosReal.coe_pos Lf, hdistSq_nonneg]
  have hdenom :
      2 * (Lf : ℝ) * distSq / dNext ≤ a * distSq := by
    have hmul := mul_le_mul_of_nonneg_left hrecip hnumerator_nonneg
    simpa [a, dPrev, dNext, div_eq_mul_inv, distSq, mul_assoc, mul_left_comm, mul_comm] using hmul
  have hdist_to_gap_seed :
      (2 / (σ : ℝ)) * (((σ : ℝ) / 2) * distSq) ≤ (2 / (σ : ℝ)) * gapNow := by
    -- Strong convexity turns the squared distance at the restart point into the current gap.
    exact
      mul_le_mul_of_nonneg_left
        (restartedObjectiveGapLowerQuadraticReal
          (f := f) (g := g) (XStar := XStar) (FOpt := FOpt) (Lf := Lf) (σ := σ)
          (xStar := xStar) (zMinusOne := zMinusOne) (N := N)
          (hproblem := hproblem) hstrong hxStar n)
        (by
          exact div_nonneg (by positivity) (le_of_lt (PosReal.coe_pos σ)))
  have hdist_to_gap :
      distSq ≤ (2 / (σ : ℝ)) * gapNow := by
    have hsigma_ne : (σ : ℝ) ≠ 0 := (PosReal.coe_pos σ).ne'
    have hcancel :
        (2 / (σ : ℝ)) * (((σ : ℝ) / 2) * distSq) = distSq := by
      field_simp [distSq, hsigma_ne]
    rw [hcancel] at hdist_to_gap_seed
    exact hdist_to_gap_seed
  have ha_nonneg : 0 ≤ a := by
    exact div_nonneg (by nlinarith [PosReal.coe_pos Lf]) hdPrev_pos.le
  have ha_gap :
      a * distSq ≤ b * gapNow := by
    have hscaled := mul_le_mul_of_nonneg_left hdist_to_gap ha_nonneg
    have hrewrite :
        a * ((2 / (σ : ℝ)) * gapNow) = b * gapNow := by
      have hdPrev_ne : dPrev ≠ 0 := hdPrev_pos.ne'
      have hsigma_ne : (σ : ℝ) ≠ 0 := (PosReal.coe_pos σ).ne'
      dsimp [a, b]
      field_simp [hdPrev_ne, hsigma_ne]
      ring
    calc
      a * distSq ≤ a * ((2 / (σ : ℝ)) * gapNow) := hscaled
      _ = b * gapNow := hrewrite
  -- Keep the exact factor visible; the half-factor corollary is recovered separately.
  calc
    (composite_model_objective f.toEReal g
      (restartedZ (f := f) (g := g) (Lf := Lf) (XStar := XStar) (FOpt := FOpt)
        (zMinusOne := zMinusOne) (N := N) (n + 1))).toReal - FOpt
        ≤ 2 * (Lf : ℝ) * distSq / dNext := hrateReal
    _ ≤ a * distSq := hdenom
    _ ≤ b * gapNow := ha_gap
    _ =
        (4 * κ(PosReal.toNNReal Lf, σ) / (((N : ℕ) + 1 : ℝ) ^ (2 : ℕ))) *
          ((composite_model_objective f.toEReal g
            (restartedZ (f := f) (g := g) (Lf := Lf) (XStar := XStar) (FOpt := FOpt)
              (zMinusOne := zMinusOne) (N := N) n)).toReal - FOpt) := by
          rfl

/-- Helper for Theorem 10.41: one completed restart cycle contracts the restarted objective gap by
the displayed factor `1 / 2`. -/
lemma restartedCycleGapRealLeHalf
    (hstrong : StrongConvexOn Set.univ (σ : ℝ) f)
    (hxStar : xStar ∈ XStar)
    (hN : (N : ℕ) = Nat.ceil (Real.sqrt (8 * κ(PosReal.toNNReal Lf, σ) - 1)))
    (n : ℕ) :
    (composite_model_objective f.toEReal g
      (restartedZ (f := f) (g := g) (Lf := Lf) (XStar := XStar) (FOpt := FOpt)
        (zMinusOne := zMinusOne) (N := N) (n + 1))).toReal - FOpt ≤
      (1 / 2 : ℝ) *
        ((composite_model_objective f.toEReal g
          (restartedZ (f := f) (g := g) (Lf := Lf) (XStar := XStar) (FOpt := FOpt)
            (zMinusOne := zMinusOne) (N := N) n)).toReal - FOpt) := by
  have hfactor :
      (composite_model_objective f.toEReal g
        (restartedZ (f := f) (g := g) (Lf := Lf) (XStar := XStar) (FOpt := FOpt)
          (zMinusOne := zMinusOne) (N := N) (n + 1))).toReal - FOpt ≤
        (4 * κ(PosReal.toNNReal Lf, σ) / (((N : ℕ) + 1 : ℝ) ^ (2 : ℕ))) *
          ((composite_model_objective f.toEReal g
            (restartedZ (f := f) (g := g) (Lf := Lf) (XStar := XStar) (FOpt := FOpt)
              (zMinusOne := zMinusOne) (N := N) n)).toReal - FOpt) :=
    restartedCycleGapRealLeFactor
      (f := f) (g := g) (XStar := XStar) (FOpt := FOpt) (Lf := Lf) (σ := σ)
      (xStar := xStar) (zMinusOne := zMinusOne) (N := N)
      (hproblem := hproblem) hstrong hxStar n
  have hhalfScaled :
      (4 * κ(PosReal.toNNReal Lf, σ) / (((N : ℕ) + 1 : ℝ) ^ (2 : ℕ))) *
          ((composite_model_objective f.toEReal g
            (restartedZ (f := f) (g := g) (Lf := Lf) (XStar := XStar) (FOpt := FOpt)
              (zMinusOne := zMinusOne) (N := N) n)).toReal - FOpt) ≤
        (1 / 2 : ℝ) *
          ((composite_model_objective f.toEReal g
            (restartedZ (f := f) (g := g) (Lf := Lf) (XStar := XStar) (FOpt := FOpt)
              (zMinusOne := zMinusOne) (N := N) n)).toReal - FOpt) := by
    -- The restart-length hypothesis turns the exact factor into the displayed `1 / 2` rate.
    exact
      mul_le_mul_of_nonneg_right
        (restartLengthContractionFactorLeHalf
          (Lf := Lf) (σ := σ) (N := N) hN)
        (restartedObjectiveGapRealNonneg
          (f := f) (g := g) (XStar := XStar) (FOpt := FOpt) (Lf := Lf)
          (zMinusOne := zMinusOne) (N := N) (hproblem := hproblem) n)
  exact hfactor.trans hhalfScaled

/-- Helper for Theorem 10.41: the first restarted objective gap already satisfies the
`L_f R² / 2` base bound. -/
lemma restartedZeroGapRealLeInitialRadius
    (hxStar : xStar ∈ XStar)
    (hR : ‖zMinusOne - xStar‖ ≤ R) :
    (composite_model_objective f.toEReal g
      (restartedZ (f := f) (g := g) (Lf := Lf) (XStar := XStar) (FOpt := FOpt)
        (zMinusOne := zMinusOne) (N := N) 0)).toReal - FOpt ≤
      (Lf : ℝ) * R ^ (2 : ℕ) / 2 := by
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  let x : ℕ → E := fun n ↦ Nat.rec zMinusOne (fun _ xk ↦ T[Lf; f, g] xk) n
  let hconv := hproblem.toIsConvexCompositeSmoothMinimizationProblem
  have htraj :
      is_proximal_gradient_trajectory f.toEReal g x (fun _ ↦ Lf) :=
    by
      intro n
      constructor
      · exact mem_interior_effective_domain_of_coe_real f (x n)
      · have hsingleton :
            proximal_gradient_step f.toEReal g (x n) Lf = {x (n + 1)} := by
          rw [show x (n + 1) = T[Lf; f, g] (x n) by simp [x]]
          simpa [prox_gradient_operator_apply] using
            (prox_grad_operator_eq_singleton f.toEReal g Lf
              (interior_effective_domain_point_of_real f (x n)))
        rw [hsingleton]
        simp
  have hrule :
      hconv.SourceSublinearRateStepsizeRule
        x
        (fun _ ↦ Lf)
        htraj
        1 :=
    by
      -- The orbit uses the exact constant schedule `L_k = L_f`, so it is the constant branch.
      left
      constructor
      · norm_num
      · intro n
        simp [PosReal.coe_toNNReal]
  have hx1_g :
      x 1 ∈ effective_domain g :=
    proximalGradientPositiveIterate_memEffectiveDomainG
      (hproblem := hconv)
      htraj
      0
  have hfirst :
      composite_model_objective f.toEReal g (x 1) - (FOpt : EReal) ≤
        ((((Lf : ℝ) * ‖x 0 - xStar‖ ^ (2 : ℕ) / 2 : ℝ)) : EReal) := by
    -- Route correction: the restarted base bound is already the `k = 1` case of Theorem 10.21
    -- for the constant-`L_f` proximal-gradient orbit started from `zMinusOne`.
    simpa [x, PosReal.coe_toNNReal] using
      (proximal_gradient_convex_objective_gap_le
        (hproblem := hconv)
        (x := x)
        (L := fun _ ↦ Lf)
        (α := 1)
        (xStar := xStar)
        htraj
        hrule
        hxStar
        1
        (by norm_num : 1 ≤ (1 : ℕ)))
  have hfirstReal :
      (composite_model_objective f.toEReal g (x 1)).toReal - FOpt ≤
        (Lf : ℝ) * ‖x 0 - xStar‖ ^ (2 : ℕ) / 2 := by
    rw [← objectiveMinusFOpt_eq_coe_sub_toReal_of_memEffectiveDomainG
      (hproblem := hconv) hx1_g] at hfirst
    exact EReal.coe_le_coe_iff.mp hfirst
  have hradius :
      (Lf : ℝ) * ‖x 0 - xStar‖ ^ (2 : ℕ) / 2 ≤
        (Lf : ℝ) * R ^ (2 : ℕ) / 2 := by
    -- The radius hypothesis controls the initial point `zMinusOne = x 0`.
    have hsq : ‖x 0 - xStar‖ ^ (2 : ℕ) ≤ R ^ (2 : ℕ) := by
      have hx0 : x 0 = zMinusOne := by
        simp [x]
      have hnorm_nonneg : 0 ≤ ‖x 0 - xStar‖ := norm_nonneg _
      have hR_nonneg : 0 ≤ R := by
        simpa [hx0] using le_trans (norm_nonneg (zMinusOne - xStar)) hR
      have hnorm_le : ‖x 0 - xStar‖ ≤ R := by
        simpa [hx0] using hR
      nlinarith
    nlinarith [hsq, PosReal.coe_pos Lf]
  simpa [x, restartedZ] using le_trans hfirstReal hradius

/-- Part (1) of Theorem 10.41: if restarted FISTA uses the restart length
`N = ⌈√(8 κ(PosReal.toNNReal Lf, σ) - 1)⌉`, `f` is `σ`-strongly convex, and
`R` bounds `‖zMinusOne - xStar‖` for some optimizer `xStar ∈ XStar`, then the restarted
outer objective gap decays geometrically as
`(L_f R^2 / 2) * (1 / 2)^k`. -/
theorem restarted_fista_objective_gap_le_geometric_half_pow
    (hstrong : StrongConvexOn Set.univ (σ : ℝ) f)
    (hxStar : xStar ∈ XStar)
    (hR : ‖zMinusOne - xStar‖ ≤ R)
    (hN : (N : ℕ) = Nat.ceil (Real.sqrt (8 * κ(PosReal.toNNReal Lf, σ) - 1)))
    (k : ℕ) :
    composite_model_objective f.toEReal g
      (restartedZ (f := f) (g := g) (Lf := Lf) (XStar := XStar) (FOpt := FOpt)
        (zMinusOne := zMinusOne) (N := N) k) -
        (FOpt : EReal) ≤
      (((((Lf : ℝ) * R ^ (2 : ℕ) / 2) * ((1 / 2 : ℝ) ^ k)) : ℝ) : EReal) := by
  induction k with
  | zero =>
      -- The base cycle is already controlled by the direct prox-gradient estimate at `z^{-1}`.
      rw [← restartedObjectiveGap_eq_coe_sub_toReal
        (f := f) (g := g) (Lf := Lf) (XStar := XStar) (FOpt := FOpt)
        (zMinusOne := zMinusOne) (N := N) (hproblem := hproblem) 0]
      exact EReal.coe_le_coe_iff.mpr <| by
        simpa using
          restartedZeroGapRealLeInitialRadius
            (f := f) (g := g) (XStar := XStar) (FOpt := FOpt) (Lf := Lf)
            (xStar := xStar) (zMinusOne := zMinusOne) (N := N)
            (R := R) (hproblem := hproblem) hxStar hR
  | succ k ih =>
      have hcycle :
          (composite_model_objective f.toEReal g
            (restartedZ (f := f) (g := g) (Lf := Lf) (XStar := XStar) (FOpt := FOpt)
              (zMinusOne := zMinusOne) (N := N) (k + 1))).toReal - FOpt ≤
            (1 / 2 : ℝ) *
              ((composite_model_objective f.toEReal g
                (restartedZ (f := f) (g := g) (Lf := Lf) (XStar := XStar) (FOpt := FOpt)
                  (zMinusOne := zMinusOne) (N := N) k)).toReal - FOpt) :=
        restartedCycleGapRealLeHalf
          (f := f) (g := g) (XStar := XStar) (FOpt := FOpt) (Lf := Lf) (σ := σ)
          (xStar := xStar) (zMinusOne := zMinusOne) (N := N)
          (hproblem := hproblem) hstrong hxStar hN k
      have hprev :
          (composite_model_objective f.toEReal g
            (restartedZ (f := f) (g := g) (Lf := Lf) (XStar := XStar) (FOpt := FOpt)
              (zMinusOne := zMinusOne) (N := N) k)).toReal - FOpt ≤
            ((Lf : ℝ) * R ^ (2 : ℕ) / 2) * ((1 / 2 : ℝ) ^ k) := by
        -- Rewrite the induction hypothesis back to the real layer of the finite restarted gap.
        rw [← restartedObjectiveGap_eq_coe_sub_toReal
          (f := f) (g := g) (Lf := Lf) (XStar := XStar) (FOpt := FOpt)
          (zMinusOne := zMinusOne) (N := N) (hproblem := hproblem) k] at ih
        exact EReal.coe_le_coe_iff.mp ih
      rw [← restartedObjectiveGap_eq_coe_sub_toReal
        (f := f) (g := g) (Lf := Lf) (XStar := XStar) (FOpt := FOpt)
        (zMinusOne := zMinusOne) (N := N) (hproblem := hproblem) (k + 1)]
      apply EReal.coe_le_coe_iff.mpr
      -- Once the cycle contraction is available, the remaining induction is a scalar power rewrite.
      calc
        (composite_model_objective f.toEReal g
          (restartedZ (f := f) (g := g) (Lf := Lf) (XStar := XStar) (FOpt := FOpt)
            (zMinusOne := zMinusOne) (N := N) (k + 1))).toReal - FOpt
            ≤ (1 / 2 : ℝ) *
                ((composite_model_objective f.toEReal g
                  (restartedZ (f := f) (g := g) (Lf := Lf) (XStar := XStar) (FOpt := FOpt)
                    (zMinusOne := zMinusOne) (N := N) k)).toReal - FOpt) := hcycle
        _ ≤ (1 / 2 : ℝ) * (((Lf : ℝ) * R ^ (2 : ℕ) / 2) * ((1 / 2 : ℝ) ^ k)) := by
            exact mul_le_mul_of_nonneg_left hprev (by norm_num)
        _ = ((Lf : ℝ) * R ^ (2 : ℕ) / 2) * ((1 / 2 : ℝ) ^ (k + 1)) := by
            rw [pow_succ]
            ring

/-- Helper for Theorem 10.41: keeping the exact restart-cycle factor visible gives a stronger
geometric estimate for the restarted outer gap than the public half-rate corollary. -/
lemma restartedObjectiveGapLeQPow
    (hstrong : StrongConvexOn Set.univ (σ : ℝ) f)
    (hxStar : xStar ∈ XStar)
    (hR : ‖zMinusOne - xStar‖ ≤ R)
    (k : ℕ) :
    composite_model_objective f.toEReal g
      (restartedZ (f := f) (g := g) (Lf := Lf) (XStar := XStar) (FOpt := FOpt)
        (zMinusOne := zMinusOne) (N := N) k) -
        (FOpt : EReal) ≤
      (((((Lf : ℝ) * R ^ (2 : ℕ) / 2) *
          (4 * κ(PosReal.toNNReal Lf, σ) / (((N : ℕ) + 1 : ℝ) ^ (2 : ℕ))) ^ k : ℝ)) : EReal) := by
  let q : ℝ := 4 * κ(PosReal.toNNReal Lf, σ) / (((N : ℕ) + 1 : ℝ) ^ (2 : ℕ))
  let A : ℝ := (Lf : ℝ) * R ^ (2 : ℕ) / 2
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    have hratio_nonneg : 0 ≤ (Lf : ℝ) / (σ : ℝ) := by
      exact div_nonneg (le_of_lt (PosReal.coe_pos Lf)) (le_of_lt (PosReal.coe_pos σ))
    have hnum_nonneg : 0 ≤ 4 * ((Lf : ℝ) / (σ : ℝ)) := by
      nlinarith
    have hden_nonneg : 0 ≤ (((N : ℕ) + 1 : ℝ) ^ (2 : ℕ)) := by
      positivity
    exact div_nonneg hnum_nonneg hden_nonneg
  induction k with
  | zero =>
      -- The base restarted gap is controlled directly by the first prox-gradient estimate.
      rw [← restartedObjectiveGap_eq_coe_sub_toReal
        (f := f) (g := g) (Lf := Lf) (XStar := XStar) (FOpt := FOpt)
        (zMinusOne := zMinusOne) (N := N) (hproblem := hproblem) 0]
      apply EReal.coe_le_coe_iff.mpr
      simpa [A, q] using
        restartedZeroGapRealLeInitialRadius
          (f := f) (g := g) (XStar := XStar) (FOpt := FOpt) (Lf := Lf)
          (xStar := xStar) (zMinusOne := zMinusOne) (N := N)
          (R := R) (hproblem := hproblem) hxStar hR
  | succ k ih =>
      have hcycle :
          (composite_model_objective f.toEReal g
            (restartedZ (f := f) (g := g) (Lf := Lf) (XStar := XStar) (FOpt := FOpt)
              (zMinusOne := zMinusOne) (N := N) (k + 1))).toReal - FOpt ≤
            q *
              ((composite_model_objective f.toEReal g
                (restartedZ (f := f) (g := g) (Lf := Lf) (XStar := XStar) (FOpt := FOpt)
                  (zMinusOne := zMinusOne) (N := N) k)).toReal - FOpt) := by
        -- Route correction: keep the exact factor `q` from the one-cycle estimate instead of
        -- collapsing immediately to `1 / 2`; the scalar close for part (2) depends on `q`.
        simpa [q] using
          restartedCycleGapRealLeFactor
            (f := f) (g := g) (XStar := XStar) (FOpt := FOpt) (Lf := Lf) (σ := σ)
            (xStar := xStar) (zMinusOne := zMinusOne) (N := N)
            (hproblem := hproblem) hstrong hxStar k
      have hprev :
          (composite_model_objective f.toEReal g
            (restartedZ (f := f) (g := g) (Lf := Lf) (XStar := XStar) (FOpt := FOpt)
              (zMinusOne := zMinusOne) (N := N) k)).toReal - FOpt ≤
            A * q ^ k := by
        -- Rewrite the induction hypothesis onto the real layer before multiplying by `q`.
        rw [← restartedObjectiveGap_eq_coe_sub_toReal
          (f := f) (g := g) (Lf := Lf) (XStar := XStar) (FOpt := FOpt)
          (zMinusOne := zMinusOne) (N := N) (hproblem := hproblem) k] at ih
        simpa [A, q] using EReal.coe_le_coe_iff.mp ih
      rw [← restartedObjectiveGap_eq_coe_sub_toReal
        (f := f) (g := g) (Lf := Lf) (XStar := XStar) (FOpt := FOpt)
        (zMinusOne := zMinusOne) (N := N) (hproblem := hproblem) (k + 1)]
      apply EReal.coe_le_coe_iff.mpr
      -- The exact one-cycle factor propagates through the induction exactly as a geometric power.
      calc
        (composite_model_objective f.toEReal g
          (restartedZ (f := f) (g := g) (Lf := Lf) (XStar := XStar) (FOpt := FOpt)
            (zMinusOne := zMinusOne) (N := N) (k + 1))).toReal - FOpt
            ≤ q *
                ((composite_model_objective f.toEReal g
                  (restartedZ (f := f) (g := g) (Lf := Lf) (XStar := XStar) (FOpt := FOpt)
                    (zMinusOne := zMinusOne) (N := N) k)).toReal - FOpt) := hcycle
        _ ≤ q * (A * q ^ k) := by
            exact mul_le_mul_of_nonneg_left hprev hq_nonneg
        _ = A * q ^ (k + 1) := by
            rw [pow_succ]
            ring

/-- Helper for Theorem 10.41: the scale `√(8 κ(PosReal.toNNReal Lf, σ))` is strictly positive. -/
lemma restartSqrtEightKappaPos :
    0 < Real.sqrt (8 * κ(PosReal.toNNReal Lf, σ)) := by
  have hkappa_pos : 0 < κ(PosReal.toNNReal Lf, σ) := by
    rw [condition_number_eq]
    exact div_pos (PosReal.coe_pos Lf) (PosReal.coe_pos σ)
  exact Real.sqrt_pos.2 <| by positivity

/-- Helper for Theorem 10.41: the restart-length hypothesis forces `√(8 κ(PosReal.toNNReal Lf, σ))`
to exceed `1`, so the hard branch `√(8 κ) < N` automatically has `N > 1`. -/
lemma one_lt_restartSqrtEightKappa
    (hN : (N : ℕ) = Nat.ceil (Real.sqrt (8 * κ(PosReal.toNNReal Lf, σ) - 1))) :
    1 < Real.sqrt (8 * κ(PosReal.toNNReal Lf, σ)) := by
  have hNpos : 0 < (N : ℕ) := N.2
  have hsqrt_sub_pos : 0 < Real.sqrt (8 * κ(PosReal.toNNReal Lf, σ) - 1) := by
    rw [hN] at hNpos
    exact Nat.ceil_pos.mp hNpos
  have hrad_pos : 0 < 8 * κ(PosReal.toNNReal Lf, σ) - 1 :=
    Real.sqrt_pos.mp hsqrt_sub_pos
  have hsq_gt_one : 1 < 8 * κ(PosReal.toNNReal Lf, σ) := by
    linarith
  have hsqrt_sq :
      Real.sqrt (8 * κ(PosReal.toNNReal Lf, σ)) ^ (2 : ℕ) =
        8 * κ(PosReal.toNNReal Lf, σ) := by
    simpa [pow_two] using
      (Real.sq_sqrt (show 0 ≤ 8 * κ(PosReal.toNNReal Lf, σ) by positivity))
  have hsqrt_pos := restartSqrtEightKappaPos (Lf := Lf) (σ := σ)
  by_contra hs
  have hs_le : Real.sqrt (8 * κ(PosReal.toNNReal Lf, σ)) ≤ 1 := le_of_not_gt hs
  have hsq_le : Real.sqrt (8 * κ(PosReal.toNNReal Lf, σ)) ^ (2 : ℕ) ≤ 1 := by
    have := pow_le_pow_left₀ hsqrt_pos.le hs_le 2
    simpa [pow_two] using this
  rw [hsqrt_sq] at hsq_le
  linarith

/-- Helper for Theorem 10.41: the Euclidean-division remainder from `k = (k / N) * N + k % N`
is at most `√(8 κ(PosReal.toNNReal Lf, σ))`. -/
lemma restartRemainderLeSqrtEightKappa
    (hN : (N : ℕ) = Nat.ceil (Real.sqrt (8 * κ(PosReal.toNNReal Lf, σ) - 1)))
    (k : ℕ) :
    ((k % (N : ℕ) : ℕ) : ℝ) ≤ Real.sqrt (8 * κ(PosReal.toNNReal Lf, σ)) := by
  let s : ℝ := Real.sqrt (8 * κ(PosReal.toNNReal Lf, σ))
  have hs_pos : 0 < s := restartSqrtEightKappaPos (Lf := Lf) (σ := σ)
  have hmod_lt : ((k % (N : ℕ) : ℕ) : ℝ) < (N : ℕ) := by
    exact_mod_cast Nat.mod_lt k N.2
  by_cases hNs : ((N : ℕ) : ℝ) ≤ s
  · exact hmod_lt.le.trans hNs
  · have hs_lt_N : s < (N : ℕ) := lt_of_not_ge hNs
    have hsqrt_sub_lt_s :
        Real.sqrt (8 * κ(PosReal.toNNReal Lf, σ) - 1) < s := by
      have hrad_nonneg : 0 ≤ 8 * κ(PosReal.toNNReal Lf, σ) - 1 := by
        have hsqrt_sub_pos : 0 < Real.sqrt (8 * κ(PosReal.toNNReal Lf, σ) - 1) := by
          have hNpos : 0 < (N : ℕ) := N.2
          rw [hN] at hNpos
          exact Nat.ceil_pos.mp hNpos
        exact le_of_lt (Real.sqrt_pos.mp hsqrt_sub_pos)
      have hrad_lt :
          8 * κ(PosReal.toNNReal Lf, σ) - 1 < 8 * κ(PosReal.toNNReal Lf, σ) := by
        linarith
      exact Real.sqrt_lt_sqrt hrad_nonneg hrad_lt
    have hpred_lt_s : ((N : ℕ) : ℝ) - 1 < s := by
      have hceil :
          ((N : ℕ) : ℝ) < Real.sqrt (8 * κ(PosReal.toNNReal Lf, σ) - 1) + 1 :=
        restartLengthLtSqrtEightKappaSubOneAddOne
          (Lf := Lf) (σ := σ) (N := N) hN
      linarith
    have hmod_le_pred : ((k % (N : ℕ) : ℕ) : ℝ) ≤ ((N : ℕ) : ℝ) - 1 := by
      have hmod_succ_le : k % (N : ℕ) + 1 ≤ (N : ℕ) :=
        Nat.succ_le_of_lt (Nat.mod_lt k N.2)
      have hmod_real_succ_le : ((k % (N : ℕ) : ℕ) : ℝ) + 1 ≤ (N : ℕ) := by
        exact_mod_cast hmod_succ_le
      nlinarith
    exact hmod_le_pred.trans hpred_lt_s.le

/-- Helper for Theorem 10.41: Bernoulli's inequality gives the quantitative bound
`2 ≤ (1 + 1 / n)^(2(n - 1))` for every natural `n > 1`. -/
lemma two_le_one_add_inv_pow_double_pred
    {n : ℕ} (hn : 1 < n) :
    (2 : ℝ) ≤ (1 + 1 / (n : ℝ)) ^ (2 * (n - 1) : ℕ) := by
  have hn_ge_two : (2 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hn_pos : 0 < (n : ℝ) := by
    positivity
  have hbernoulli :
      1 + (((2 * (n - 1) : ℕ) : ℝ)) * (1 / (n : ℝ)) ≤
        (1 + 1 / (n : ℝ)) ^ (2 * (n - 1) : ℕ) := by
    have hone_div_nonneg : 0 ≤ 1 / (n : ℝ) := by
      positivity
    exact one_add_mul_le_pow (by linarith) (2 * (n - 1))
  have hleft_ge_two :
      (2 : ℝ) ≤ 1 + (((2 * (n - 1) : ℕ) : ℝ)) * (1 / (n : ℝ)) := by
    have hfactor_ge : (n : ℝ) ≤ ((2 * (n - 1) : ℕ) : ℝ) := by
      exact_mod_cast (by omega : n ≤ 2 * (n - 1))
    have hmul_ge_one : (1 : ℝ) ≤ (((2 * (n - 1) : ℕ) : ℝ)) * (1 / (n : ℝ)) := by
      rw [show (((2 * (n - 1) : ℕ) : ℝ)) * (1 / (n : ℝ)) =
          (((2 * (n - 1) : ℕ) : ℝ)) / (n : ℝ) by ring]
      rw [one_le_div₀ hn_pos]
      exact hfactor_ge
    nlinarith
  calc
    (2 : ℝ) ≤ 1 + (((2 * (n - 1) : ℕ) : ℝ)) * (1 / (n : ℝ)) := hleft_ge_two
    _ ≤ (1 + 1 / (n : ℝ)) ^ (2 * (n - 1) : ℕ) := hbernoulli

/-- Helper for Theorem 10.41: on the hard ceiling branch `N - 1 < s < N`, Bernoulli's
inequality converts the ratio `(N / (N + 1))^2` into the half-base real-exponent benchmark
`(1 / 2)^(N / s)`. -/
lemma restartHardBranchRatioLeHalfRpow
    (hNgt : 1 < (N : ℕ)) {s : ℝ}
    (hNs_left : ((N : ℕ) : ℝ) - 1 < s)
    (hNs_right : s < ((N : ℕ) : ℝ)) :
    (1 / 2 : ℝ) * ((((N : ℕ) : ℝ) / (((N : ℕ) : ℝ) + 1)) ^ (2 : ℕ)) ≤
      (1 / 2 : ℝ) ^ (((N : ℕ) : ℝ) / s) := by
  let nR : ℝ := (N : ℕ)
  have hnR_gt_one : (1 : ℝ) < nR := by
    dsimp [nR]
    exact_mod_cast hNgt
  have hnR_sub_pos : 0 < nR - 1 := by
    linarith
  have hs_pos : 0 < s := by
    linarith
  have hnR_ne : nR ≠ 0 := by
    linarith
  have hbern :
      (2 : ℝ) ≤ (1 + 1 / nR) ^ (2 * (N - 1) : ℕ) :=
    two_le_one_add_inv_pow_double_pred (n := (N : ℕ)) hNgt
  have hratio_pow_raw :
      (nR / (nR + 1)) ^ (2 * (N - 1) : ℕ) ≤ 1 / 2 := by
    -- Invert Bernoulli's bound and rewrite the reciprocal base as `N / (N + 1)`.
    have hrecip :
        1 / ((1 + 1 / nR) ^ (2 * (N - 1) : ℕ)) ≤ 1 / (2 : ℝ) := by
      exact one_div_le_one_div_of_le (by norm_num) hbern
    have hratio_eq : nR / (nR + 1) = (1 + 1 / nR)⁻¹ := by
      field_simp [hnR_ne]
    have hpow_eq :
        (nR / (nR + 1)) ^ (2 * (N - 1) : ℕ) =
          ((1 + 1 / nR) ^ (2 * (N - 1) : ℕ))⁻¹ := by
      rw [hratio_eq, one_div, inv_pow]
    have hrecip' :
        ((1 + 1 / nR) ^ (2 * (N - 1) : ℕ))⁻¹ ≤ (2 : ℝ)⁻¹ := by
      simpa [one_div] using hrecip
    have hratio_pow_raw' :
        (nR / (nR + 1)) ^ (2 * (N - 1) : ℕ) ≤ (2 : ℝ)⁻¹ := by
      calc
        (nR / (nR + 1)) ^ (2 * (N - 1) : ℕ) =
            ((1 + 1 / nR) ^ (2 * (N - 1) : ℕ))⁻¹ := hpow_eq
        _ ≤ (2 : ℝ)⁻¹ := hrecip'
    simpa [one_div] using hratio_pow_raw'
  have hsub_cast : ((N - 1 : ℕ) : ℝ) = nR - 1 := by
    have hsucc : ((N - 1 : ℕ) : ℝ) + 1 = nR := by
      dsimp [nR]
      exact_mod_cast Nat.succ_pred_eq_of_pos N.2
    linarith
  have hcore :
      ((nR / (nR + 1)) ^ (2 : ℕ)) ≤ (1 / 2 : ℝ) ^ (1 / (nR - 1)) := by
    -- Move the `(N - 1)`-fold power back across the positive exponent `N - 1`.
    rw [← Real.rpow_le_rpow_iff (by positivity) (by positivity) hnR_sub_pos]
    have hhalf_rpow :
        ((1 / 2 : ℝ) ^ (1 / (nR - 1))) ^ (nR - 1) = (1 / 2 : ℝ) := by
      have hsub_ne : nR - 1 ≠ 0 := by linarith
      rw [← Real.rpow_mul (by positivity : 0 ≤ (1 / 2 : ℝ))]
      have hmul : (1 / (nR - 1)) * (nR - 1) = 1 := by
        field_simp [hsub_ne]
      rw [hmul, Real.rpow_one]
    rw [hhalf_rpow, ← hsub_cast, Real.rpow_natCast]
    simpa [pow_mul] using hratio_pow_raw
  have hscaled :
      (1 / 2 : ℝ) * ((nR / (nR + 1)) ^ (2 : ℕ)) ≤
        (1 / 2 : ℝ) ^ (nR / (nR - 1)) := by
    -- Multiply the ratio bound by the leading `1 / 2` and merge the exponents.
    calc
      (1 / 2 : ℝ) * ((nR / (nR + 1)) ^ (2 : ℕ))
          ≤ (1 / 2 : ℝ) * ((1 / 2 : ℝ) ^ (1 / (nR - 1))) := by
              exact mul_le_mul_of_nonneg_left hcore (by norm_num)
      _ = ((1 / 2 : ℝ) ^ (1 : ℝ)) * ((1 / 2 : ℝ) ^ (1 / (nR - 1))) := by
            rw [Real.rpow_one]
      _ = (1 / 2 : ℝ) ^ (1 + 1 / (nR - 1)) := by
            rw [← Real.rpow_add (by norm_num : 0 < (1 / 2 : ℝ))]
      _ = (1 / 2 : ℝ) ^ (nR / (nR - 1)) := by
            congr 1
            field_simp [show (nR - 1) ≠ 0 by linarith]
            ring
  have hdiv_order : nR / s ≤ nR / (nR - 1) := by
    -- The hard branch keeps `s` above `N - 1`, so `N / s` is no larger than `N / (N - 1)`.
    have hrecip : 1 / s ≤ 1 / (nR - 1) := by
      exact one_div_le_one_div_of_le hnR_sub_pos hNs_left.le
    have hnR_nonneg : 0 ≤ nR := by linarith
    have hmul := mul_le_mul_of_nonneg_left hrecip hnR_nonneg
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
  have hpow_order :
      (1 / 2 : ℝ) ^ (nR / (nR - 1)) ≤ (1 / 2 : ℝ) ^ (nR / s) := by
    exact Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hdiv_order
  -- Route correction: separate the Bernoulli ratio step from the final `s`-dependent exponent
  -- comparison instead of attacking the exact `q`-expression directly.
  exact hscaled.trans hpow_order

/-- Helper for Theorem 10.41: the exact restart factor is dominated by the half-base real-exponent
benchmark `(1 / 2)^(N / √(8 κ(PosReal.toNNReal Lf, σ)))`. -/
lemma restartContractionFactorLeHalfRpow
    (hN : (N : ℕ) = Nat.ceil (Real.sqrt (8 * κ(PosReal.toNNReal Lf, σ) - 1))) :
    4 * κ(PosReal.toNNReal Lf, σ) / (((N : ℕ) + 1 : ℝ) ^ (2 : ℕ)) ≤
      (1 / 2 : ℝ) ^ (((N : ℕ) : ℝ) / Real.sqrt (8 * κ(PosReal.toNNReal Lf, σ))) := by
  let s : ℝ := Real.sqrt (8 * κ(PosReal.toNNReal Lf, σ))
  let q : ℝ := 4 * κ(PosReal.toNNReal Lf, σ) / (((N : ℕ) + 1 : ℝ) ^ (2 : ℕ))
  have hs_pos : 0 < s := by
    dsimp [s]
    exact restartSqrtEightKappaPos (Lf := Lf) (σ := σ)
  by_cases hNs : ((N : ℕ) : ℝ) ≤ s
  · have hq_half : q ≤ (1 / 2 : ℝ) := by
      -- On the easy branch, the existing restart-length estimate already gives `q ≤ 1 / 2`.
      simpa [q] using
        restartLengthContractionFactorLeHalf
          (Lf := Lf) (σ := σ) (N := N) hN
    have hhalf_le :
        (1 / 2 : ℝ) ≤ (1 / 2 : ℝ) ^ (((N : ℕ) : ℝ) / s) := by
      -- Since `N / s ≤ 1`, the decreasing half-base power is at least `1 / 2`.
      have hexp_le_one : (((N : ℕ) : ℝ) / s) ≤ 1 := by
        exact (div_le_iff₀ hs_pos).2 <| by
          simpa [one_mul, mul_comm] using hNs
      simpa using
        (Real.rpow_le_rpow_of_exponent_ge
          (x := (1 / 2 : ℝ)) (hx0 := by norm_num) (hx1 := by norm_num) hexp_le_one)
    simpa [q, s] using hq_half.trans hhalf_le
  · have hs_lt_N : s < ((N : ℕ) : ℝ) := lt_of_not_ge hNs
    have hN_gt_one : 1 < (N : ℕ) := by
      -- The hard branch `s < N`, together with `s > 1`, forces `N > 1`.
      have hone_lt_s : 1 < s := by
        simpa [s] using
          one_lt_restartSqrtEightKappa (Lf := Lf) (σ := σ) (N := N) hN
      have hone_lt_N : (1 : ℝ) < ((N : ℕ) : ℝ) := lt_trans hone_lt_s hs_lt_N
      exact_mod_cast hone_lt_N
    have hsqrt_sub_lt_s :
        Real.sqrt (8 * κ(PosReal.toNNReal Lf, σ) - 1) < s := by
      -- The hard branch compares `sqrt(8 κ - 1)` and `sqrt(8 κ)` through monotonicity of `sqrt`.
      have hrad_nonneg : 0 ≤ 8 * κ(PosReal.toNNReal Lf, σ) - 1 := by
        have hsqrt_sub_pos : 0 < Real.sqrt (8 * κ(PosReal.toNNReal Lf, σ) - 1) := by
          have hNpos : 0 < (N : ℕ) := N.2
          rw [hN] at hNpos
          exact Nat.ceil_pos.mp hNpos
        exact le_of_lt (Real.sqrt_pos.mp hsqrt_sub_pos)
      have hrad_lt :
          8 * κ(PosReal.toNNReal Lf, σ) - 1 < 8 * κ(PosReal.toNNReal Lf, σ) := by
        linarith
      simpa [s] using Real.sqrt_lt_sqrt hrad_nonneg hrad_lt
    have hNs_left : ((N : ℕ) : ℝ) - 1 < s := by
      -- The ceiling interval gives the sharp hard-branch window `N - 1 < s < N`.
      have hceil :
          ((N : ℕ) : ℝ) < Real.sqrt (8 * κ(PosReal.toNNReal Lf, σ) - 1) + 1 :=
        restartLengthLtSqrtEightKappaSubOneAddOne
          (Lf := Lf) (σ := σ) (N := N) hN
      linarith
    have hs_sq : s ^ (2 : ℕ) = 8 * κ(PosReal.toNNReal Lf, σ) := by
      -- Rewrite `s` back to `sqrt(8 κ)` once to expose the exact factor normalization.
      have hkappa_nonneg : 0 ≤ 8 * κ(PosReal.toNNReal Lf, σ) := by
        have hkappa_pos : 0 < κ(PosReal.toNNReal Lf, σ) := by
          rw [condition_number_eq]
          exact div_pos (PosReal.coe_pos Lf) (PosReal.coe_pos σ)
        positivity
      dsimp [s]
      simpa [pow_two] using
        Real.sq_sqrt hkappa_nonneg
    have hq_eq :
        q = (1 / 2 : ℝ) * (s / (((N : ℕ) : ℝ) + 1)) ^ (2 : ℕ) := by
      -- Normalize the exact restart factor into the `sqrt(8 κ)` form used by the hard branch.
      calc
        q = 4 * κ(PosReal.toNNReal Lf, σ) / ((((N : ℕ) : ℝ) + 1) ^ (2 : ℕ)) := by
              rfl
        _ = ((1 / 2 : ℝ) * (8 * κ(PosReal.toNNReal Lf, σ))) /
              ((((N : ℕ) : ℝ) + 1) ^ (2 : ℕ)) := by
              ring
        _ = ((1 / 2 : ℝ) * (s ^ (2 : ℕ))) /
              ((((N : ℕ) : ℝ) + 1) ^ (2 : ℕ)) := by
              rw [hs_sq]
        _ = (1 / 2 : ℝ) * (s / (((N : ℕ) : ℝ) + 1)) ^ (2 : ℕ) := by
              field_simp [pow_two]
    have hratio_sq :
        (s / (((N : ℕ) : ℝ) + 1)) ^ (2 : ℕ) ≤
          ((((N : ℕ) : ℝ) / (((N : ℕ) : ℝ) + 1)) ^ (2 : ℕ)) := by
      -- Replacing `s` by the larger endpoint `N` weakens the normalized factor in the hard branch.
      have hden_pos : 0 < (((N : ℕ) : ℝ) + 1) := by
        positivity
      have hfrac :
          s / (((N : ℕ) : ℝ) + 1) ≤
            ((N : ℕ) : ℝ) / (((N : ℕ) : ℝ) + 1) := by
        exact (div_le_div_iff_of_pos_right hden_pos).2 hs_lt_N.le
      exact pow_le_pow_left₀ (by positivity) hfrac 2
    have hq_ratio :
        q ≤ (1 / 2 : ℝ) *
            ((((N : ℕ) : ℝ) / (((N : ℕ) : ℝ) + 1)) ^ (2 : ℕ)) := by
      rw [hq_eq]
      exact mul_le_mul_of_nonneg_left hratio_sq (by norm_num)
    have hhard :
        (1 / 2 : ℝ) * ((((N : ℕ) : ℝ) / (((N : ℕ) : ℝ) + 1)) ^ (2 : ℕ)) ≤
          (1 / 2 : ℝ) ^ (((N : ℕ) : ℝ) / s) := by
      exact
        restartHardBranchRatioLeHalfRpow
          (N := N) hN_gt_one (s := s) hNs_left hs_lt_N
    -- Route correction: handle the hard branch through the normalized ratio and the dedicated
    -- Bernoulli-to-`rpow` bridge instead of comparing the exact `q` expression in one step.
    simpa [q, s] using hq_ratio.trans hhard

/-- Helper for Theorem 10.41: the explicit leading factor `1 / 2` absorbs the Euclidean-division
remainder, so the exact cycle factor `q^(k / N)` is bounded by the half-base real-exponent
benchmark at scale `k / √(8 κ(PosReal.toNNReal Lf, σ))`. -/
lemma restartScaledFactorPowLeHalfRpow
    (hN : (N : ℕ) = Nat.ceil (Real.sqrt (8 * κ(PosReal.toNNReal Lf, σ) - 1)))
    (k : ℕ) :
    (1 / 2 : ℝ) *
        (4 * κ(PosReal.toNNReal Lf, σ) / (((N : ℕ) + 1 : ℝ) ^ (2 : ℕ))) ^ (k / (N : ℕ)) ≤
      (1 / 2 : ℝ) ^ ((k : ℝ) / Real.sqrt (8 * κ(PosReal.toNNReal Lf, σ))) := by
  let s : ℝ := Real.sqrt (8 * κ(PosReal.toNNReal Lf, σ))
  let q : ℝ := 4 * κ(PosReal.toNNReal Lf, σ) / (((N : ℕ) + 1 : ℝ) ^ (2 : ℕ))
  let m : ℕ := k / (N : ℕ)
  let r : ℕ := k % (N : ℕ)
  have hs_pos : 0 < s := by
    dsimp [s]
    exact restartSqrtEightKappaPos (Lf := Lf) (σ := σ)
  have hq_nonneg : 0 ≤ q := by
    -- The exact restart factor is nonnegative because both its numerator and denominator are.
    have hkappa_pos : 0 < κ(PosReal.toNNReal Lf, σ) := by
      rw [condition_number_eq]
      exact div_pos (PosReal.coe_pos Lf) (PosReal.coe_pos σ)
    dsimp [q]
    exact div_nonneg (by positivity) (by positivity)
  have hfactor :
      q ≤ (1 / 2 : ℝ) ^ (((N : ℕ) : ℝ) / s) := by
    -- First control one restart cycle by the half-base real-exponent benchmark.
    simpa [q, s] using
      restartContractionFactorLeHalfRpow
        (Lf := Lf) (σ := σ) (N := N) hN
  have hpow :
      q ^ m ≤ (1 / 2 : ℝ) ^ ((((N : ℕ) : ℝ) / s) * m) := by
    -- Raise the one-cycle factor comparison to the quotient power `m = k / N`.
    calc
      q ^ m ≤ ((1 / 2 : ℝ) ^ (((N : ℕ) : ℝ) / s)) ^ m := by
          exact pow_le_pow_left₀ hq_nonneg hfactor m
      _ = (1 / 2 : ℝ) ^ ((((N : ℕ) : ℝ) / s) * m) := by
          rw [← Real.rpow_mul_natCast (by norm_num : 0 ≤ (1 / 2 : ℝ))]
  have hrem :
      (r : ℝ) ≤ s := by
    -- The Euclidean remainder is at most `sqrt(8 κ)`.
    simpa [r, s] using
      restartRemainderLeSqrtEightKappa
        (Lf := Lf) (σ := σ) (N := N) hN k
  have hk_eq :
      (k : ℝ) = (m : ℝ) * ((N : ℕ) : ℝ) + r := by
    -- Rewrite the total iteration count by Euclidean division.
    have hk_nat : m * (N : ℕ) + r = k := by
      dsimp [m, r]
      simpa [Nat.mul_comm] using Nat.div_add_mod k (N : ℕ)
    exact_mod_cast hk_nat.symm
  have hexp_order :
      (k : ℝ) / s ≤ 1 + (((N : ℕ) : ℝ) / s) * m := by
    -- The leading factor `1 / 2` covers exactly the missing remainder exponent `r / s ≤ 1`.
    refine (div_le_iff₀ hs_pos).2 ?_
    calc
      (k : ℝ) = (m : ℝ) * ((N : ℕ) : ℝ) + r := hk_eq
      _ ≤ (m : ℝ) * ((N : ℕ) : ℝ) + s := by
            gcongr
      _ = (1 + (((N : ℕ) : ℝ) / s) * m) * s := by
            field_simp [hs_pos.ne']
            ring
  have hlead :
      (1 / 2 : ℝ) * q ^ m ≤
        (1 / 2 : ℝ) ^ (1 + (((N : ℕ) : ℝ) / s) * m) := by
    -- Merge the explicit leading factor with the quotient-power estimate.
    calc
      (1 / 2 : ℝ) * q ^ m ≤
          (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ ((((N : ℕ) : ℝ) / s) * m) := by
            exact mul_le_mul_of_nonneg_left hpow (by norm_num)
      _ = (1 / 2 : ℝ) ^ (1 : ℝ) * (1 / 2 : ℝ) ^ ((((N : ℕ) : ℝ) / s) * m) := by
            rw [Real.rpow_one]
      _ = (1 / 2 : ℝ) ^ (1 + (((N : ℕ) : ℝ) / s) * m) := by
            rw [← Real.rpow_add (by norm_num : 0 < (1 / 2 : ℝ))]
  have htarget :
      (1 / 2 : ℝ) ^ (1 + (((N : ℕ) : ℝ) / s) * m) ≤
        (1 / 2 : ℝ) ^ ((k : ℝ) / s) := by
    exact
      Real.rpow_le_rpow_of_exponent_ge
        (x := (1 / 2 : ℝ)) (hx0 := by norm_num) (hx1 := by norm_num) hexp_order
  -- Route correction: isolate the quotient-power step from the Euclidean-remainder absorption
  -- instead of proving the final `q^(k / N)` bridge in a single scalar calculation.
  simpa [q, s, m] using hlead.trans htarget

/-- Helper for Theorem 10.41: the remaining work in part (2) is purely scalar. Once the total
iteration lower bound is converted into this exact `q^(k / N)` estimate, the public theorem is an
immediate `EReal` coercion. -/
lemma restartedFactorPowLeEpsilonOfIterationBound
    (hN : (N : ℕ) = Nat.ceil (Real.sqrt (8 * κ(PosReal.toNNReal Lf, σ) - 1)))
    (ε : PosReal)
    (k : ℕ)
    (hiter :
      Real.sqrt (8 * κ(PosReal.toNNReal Lf, σ)) *
          (Real.log (1 / (ε : ℝ)) / Real.log 2 +
            Real.log ((Lf : ℝ) * R ^ (2 : ℕ)) / Real.log 2) ≤
        (k : ℝ)) :
    ((Lf : ℝ) * R ^ (2 : ℕ) / 2) *
        (4 * κ(PosReal.toNNReal Lf, σ) / (((N : ℕ) + 1 : ℝ) ^ (2 : ℕ))) ^ (k / (N : ℕ)) ≤
      (ε : ℝ) := by
  let s : ℝ := Real.sqrt (8 * κ(PosReal.toNNReal Lf, σ))
  let A0 : ℝ := (Lf : ℝ) * R ^ (2 : ℕ)
  have hs_pos : 0 < s := restartSqrtEightKappaPos (Lf := Lf) (σ := σ)
  have hscaled :
      (1 / 2 : ℝ) *
          (4 * κ(PosReal.toNNReal Lf, σ) / (((N : ℕ) + 1 : ℝ) ^ (2 : ℕ))) ^ (k / (N : ℕ)) ≤
        (1 / 2 : ℝ) ^ ((k : ℝ) / s) := by
    simpa [s] using
      restartScaledFactorPowLeHalfRpow
        (Lf := Lf) (σ := σ) (N := N) hN k
  by_cases hA0_zero : A0 = 0
  · -- If the initial radius term vanishes, the scalar target is immediate.
    have hleft_zero :
        (A0 / 2) *
            (4 * κ(PosReal.toNNReal Lf, σ) / (((N : ℕ) + 1 : ℝ) ^ (2 : ℕ))) ^
              (k / (N : ℕ)) = 0 := by
      simp [hA0_zero]
    rw [show (Lf : ℝ) * R ^ (2 : ℕ) / 2 = A0 / 2 by rfl, hleft_zero]
    exact le_of_lt ε.2
  · have hA0_nonneg : 0 ≤ A0 := by
      dsimp [A0]
      have hsq_nonneg : 0 ≤ R ^ (2 : ℕ) := by positivity
      nlinarith [PosReal.coe_pos Lf, hsq_nonneg]
    have hA0_pos : 0 < A0 := by
      have hA0_ne : 0 ≠ A0 := by
        intro hzero
        apply hA0_zero
        exact hzero.symm
      exact lt_of_le_of_ne hA0_nonneg hA0_ne
    have hk_div :
        Real.log (1 / (ε : ℝ)) / Real.log 2 + Real.log A0 / Real.log 2 ≤ (k : ℝ) / s := by
      apply (le_div_iff₀ hs_pos).2
      simpa [s, A0, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm] using hiter
    have hlog2_pos : 0 < Real.log 2 := by
      have : (1 : ℝ) < 2 := by norm_num
      exact Real.log_pos this
    have hk_div_combined :
        (Real.log (1 / (ε : ℝ)) + Real.log A0) / Real.log 2 ≤ (k : ℝ) / s := by
      have hsplit :
          Real.log (1 / (ε : ℝ)) / Real.log 2 + Real.log A0 / Real.log 2 =
            (Real.log (1 / (ε : ℝ)) + Real.log A0) / Real.log 2 := by
        field_simp [hlog2_pos.ne']
      rwa [hsplit] at hk_div
    have hlog_bound :
        Real.log A0 - (k : ℝ) / s * Real.log 2 ≤ Real.log (ε : ℝ) := by
      have hk_mul :
          Real.log (1 / (ε : ℝ)) + Real.log A0 ≤ (k : ℝ) / s * Real.log 2 := by
        exact (div_le_iff₀ hlog2_pos).1 hk_div_combined
      rw [one_div, Real.log_inv] at hk_mul
      nlinarith
    have hhalf_decay :
        A0 * (1 / 2 : ℝ) ^ ((k : ℝ) / s) ≤ (ε : ℝ) := by
      have hlog_mul :
          Real.log (A0 * (1 / 2 : ℝ) ^ ((k : ℝ) / s)) ≤ Real.log (ε : ℝ) := by
        calc
          Real.log (A0 * (1 / 2 : ℝ) ^ ((k : ℝ) / s))
              = Real.log A0 + Real.log ((1 / 2 : ℝ) ^ ((k : ℝ) / s)) := by
                  rw [Real.log_mul hA0_pos.ne' (Real.rpow_pos_of_pos (by norm_num) _).ne']
          _ = Real.log A0 + ((k : ℝ) / s) * Real.log (1 / 2 : ℝ) := by
                  rw [Real.log_rpow (by norm_num : 0 < (1 / 2 : ℝ)) _]
          _ = Real.log A0 - (k : ℝ) / s * Real.log 2 := by
                  rw [one_div, Real.log_inv]
                  ring
          _ ≤ Real.log (ε : ℝ) := hlog_bound
      exact
        (Real.log_le_log_iff (mul_pos hA0_pos (Real.rpow_pos_of_pos (by norm_num) _)) ε.2).1
          hlog_mul
    have hmain :
        (A0 / 2) *
            (4 * κ(PosReal.toNNReal Lf, σ) / (((N : ℕ) + 1 : ℝ) ^ (2 : ℕ))) ^ (k / (N : ℕ)) ≤
          A0 * (1 / 2 : ℝ) ^ ((k : ℝ) / s) := by
      calc
        (A0 / 2) *
            (4 * κ(PosReal.toNNReal Lf, σ) / (((N : ℕ) + 1 : ℝ) ^ (2 : ℕ))) ^ (k / (N : ℕ))
            = A0 * ((1 / 2 : ℝ) *
                (4 * κ(PosReal.toNNReal Lf, σ) / (((N : ℕ) + 1 : ℝ) ^ (2 : ℕ))) ^
                  (k / (N : ℕ))) := by
                    ring
        _ ≤ A0 * ((1 / 2 : ℝ) ^ ((k : ℝ) / s)) := by
            exact mul_le_mul_of_nonneg_left hscaled hA0_pos.le
    calc
      ((Lf : ℝ) * R ^ (2 : ℕ) / 2) *
          (4 * κ(PosReal.toNNReal Lf, σ) / (((N : ℕ) + 1 : ℝ) ^ (2 : ℕ))) ^ (k / (N : ℕ))
          = (A0 / 2) *
              (4 * κ(PosReal.toNNReal Lf, σ) / (((N : ℕ) + 1 : ℝ) ^ (2 : ℕ))) ^
                (k / (N : ℕ)) := by
                  rfl
      _ ≤ A0 * (1 / 2 : ℝ) ^ ((k : ℝ) / s) := hmain
      _ ≤ (ε : ℝ) := hhalf_decay

/-- Theorem 10.41 (2): if the same restart length
`N = ⌈√(8 κ(PosReal.toNNReal Lf, σ) - 1)⌉` is used and the total iteration count `k`
satisfies the displayed logarithmic lower bound, then the restart point at the last
completed cycle is `ε`-optimal. In Lean, the textbook index `⌊k / N⌋` is written
`k / (N : ℕ)`. -/
theorem restarted_fista_objective_gap_le_epsilon_of_iteration_bound
    (hstrong : StrongConvexOn Set.univ (σ : ℝ) f)
    (hxStar : xStar ∈ XStar)
    (hR : ‖zMinusOne - xStar‖ ≤ R)
    (hN : (N : ℕ) = Nat.ceil (Real.sqrt (8 * κ(PosReal.toNNReal Lf, σ) - 1)))
    (ε : PosReal)
    (k : ℕ)
    (hiter :
      Real.sqrt (8 * κ(PosReal.toNNReal Lf, σ)) *
          (Real.log (1 / (ε : ℝ)) / Real.log 2 +
            Real.log ((Lf : ℝ) * R ^ (2 : ℕ)) / Real.log 2) ≤
        (k : ℝ)) :
    composite_model_objective f.toEReal g
      (restartedZ (f := f) (g := g) (Lf := Lf) (XStar := XStar) (FOpt := FOpt)
        (zMinusOne := zMinusOne) (N := N) (k / (N : ℕ))) -
        (FOpt : EReal) ≤
      ((ε : ℝ) : EReal) := by
  have hgap :=
    restartedObjectiveGapLeQPow
      (f := f) (g := g) (XStar := XStar) (FOpt := FOpt) (Lf := Lf) (σ := σ)
      (xStar := xStar) (zMinusOne := zMinusOne) (N := N) (R := R)
      (hproblem := hproblem) hstrong hxStar hR (k / (N : ℕ))
  have hscalar :
      (((((Lf : ℝ) * R ^ (2 : ℕ) / 2) *
          (4 * κ(PosReal.toNNReal Lf, σ) / (((N : ℕ) + 1 : ℝ) ^ (2 : ℕ))) ^
            (k / (N : ℕ)) : ℝ)) : EReal) ≤
        ((ε : ℝ) : EReal) := by
    exact EReal.coe_le_coe_iff.mpr <|
      restartedFactorPowLeEpsilonOfIterationBound
        (Lf := Lf) (σ := σ) (N := N) (R := R) hN ε k hiter
  exact hgap.trans hscalar

end Problem

end
