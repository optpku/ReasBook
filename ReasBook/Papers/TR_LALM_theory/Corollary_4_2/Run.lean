/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Proposition_4_1.Parameters
public import TR_LALM_theory.Theorem_2_13.LiftedState
import TR_LALM_theory.Theorem_2_10

public section

open Filter Topology
open scoped LALM

namespace LALM.Correction

variable {n m : ℕ}
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
variable {x₀ : EuclideanSpace ℝ (Fin n)}
variable {multiplier₀ : EuclideanSpace ℝ (Fin m)}
variable {ρ β : ℝ}

/-- A deterministic NR-LALM+SOC run, storing the base-model steps and the explicitly
corrected point and multiplier updates. -/
structure Run
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (ρ β : ℝ) (x₀ : EuclideanSpace ℝ (Fin n))
    (multiplier₀ : EuclideanSpace ℝ (Fin m)) where
  /-- The penalty parameter is positive. -/
  rho_pos : 0 < ρ
  /-- The proximal parameter is positive. -/
  beta_pos : 0 < β
  /-- The corrected primal iterates. -/
  point : ℕ → EuclideanSpace ℝ (Fin n)
  /-- The classical multipliers evaluated at the corrected iterates. -/
  multiplier : ℕ → EuclideanSpace ℝ (Fin m)
  /-- The minimizers of the uncorrected quadratic step model. -/
  baseStep : ℕ → EuclideanSpace ℝ (Fin n)
  /-- The point sequence starts at the prescribed initial point. -/
  point_zero : point 0 = x₀
  /-- The multiplier sequence starts at the prescribed initial multiplier. -/
  multiplier_zero : multiplier 0 = multiplier₀
  /-- Each base step globally minimizes the corresponding LALM model. -/
  minimizes_baseStep (k : ℕ) :
    IsMinOn (LALM.stepModel f c ρ β (point k) (multiplier k)) Set.univ (baseStep k)
  /-- The next point is the trial point plus the Proposition 4.1 correction. -/
  point_succ (k : ℕ) :
    point (k + 1) = nextPoint c (point k) (baseStep k)
  /-- The classical multiplier update is evaluated at the corrected point. -/
  multiplier_succ (k : ℕ) :
    multiplier (k + 1) = nextMultiplier c ρ (point k) (multiplier k) (baseStep k)

namespace Run

/-- Construct a corrected run from explicit sequences and certificates for all
initialization, minimization, and update laws. -/
def ofSequences
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (ρ β : ℝ) (x₀ : EuclideanSpace ℝ (Fin n))
    (multiplier₀ : EuclideanSpace ℝ (Fin m))
    (rho_pos : 0 < ρ) (beta_pos : 0 < β)
    (point : ℕ → EuclideanSpace ℝ (Fin n))
    (multiplier : ℕ → EuclideanSpace ℝ (Fin m))
    (baseStep : ℕ → EuclideanSpace ℝ (Fin n))
    (point_zero : point 0 = x₀) (multiplier_zero : multiplier 0 = multiplier₀)
    (minimizes_baseStep : ∀ k,
      IsMinOn (LALM.stepModel f c ρ β (point k) (multiplier k)) Set.univ (baseStep k))
    (point_succ : ∀ k, point (k + 1) = nextPoint c (point k) (baseStep k))
    (multiplier_succ : ∀ k,
      multiplier (k + 1) = nextMultiplier c ρ (point k) (multiplier k) (baseStep k)) :
    Run f c ρ β x₀ multiplier₀ :=
  { rho_pos
    beta_pos
    point
    multiplier
    baseStep
    point_zero
    multiplier_zero
    minimizes_baseStep
    point_succ
    multiplier_succ }

/-- A corrected run exposes its initialization and its model-minimization and
corrected-update laws. -/
theorem spec (run : Run f c ρ β x₀ multiplier₀) :
    (run.point 0 = x₀ ∧ run.multiplier 0 = multiplier₀) ∧
      ∀ k,
        IsMinOn (LALM.stepModel f c ρ β (run.point k) (run.multiplier k))
            Set.univ (run.baseStep k) ∧
          run.point (k + 1) = nextPoint c (run.point k) (run.baseStep k) ∧
          run.multiplier (k + 1) =
            nextMultiplier c ρ (run.point k) (run.multiplier k) (run.baseStep k) := by
  -- Package the initialization and transition fields in their public conjunction form.
  exact ⟨⟨run.point_zero, run.multiplier_zero⟩,
    fun k ↦ ⟨run.minimizes_baseStep k, run.point_succ k, run.multiplier_succ k⟩⟩

/-- Helper for Corollary 4.2: the canonical corrected base step is the unique
global minimizer of the underlying NR-LALM quadratic model. -/
private noncomputable def canonicalBaseStep
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (rho beta : ℝ) (x : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m))
    (hrho : 0 < rho) (hbeta : 0 < beta) : EuclideanSpace ℝ (Fin n) :=
  Classical.choose
    (LALM.Run.existsUniqueStepModelMinimizer f c rho beta x multiplier hrho hbeta).exists

/-- Helper for Corollary 4.2: the canonical corrected base step minimizes its
underlying quadratic model. -/
private lemma canonicalBaseStep_minimizes
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (rho beta : ℝ) (x : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m))
    (hrho : 0 < rho) (hbeta : 0 < beta) :
    IsMinOn (LALM.stepModel f c rho beta x multiplier) Set.univ
      (canonicalBaseStep f c rho beta x multiplier hrho hbeta) := by
  unfold canonicalBaseStep
  exact Classical.choose_spec
    (LALM.Run.existsUniqueStepModelMinimizer f c rho beta x multiplier hrho hbeta).exists

/-- Helper for Corollary 4.2: one canonical corrected transition applies the
unique base-model minimizer followed by the SOC point and multiplier updates. -/
private noncomputable def canonicalTransition
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (rho beta : ℝ) (hrho : 0 < rho) (hbeta : 0 < beta)
    (state : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) :=
  let p := canonicalBaseStep f c rho beta state.1 state.2 hrho hbeta
  (nextPoint c state.1 p, nextMultiplier c rho state.1 state.2 p)

/-- Corrected deterministic runs with the same objective, constraint,
coefficients, and initial data are equal. -/
theorem eq (run₁ run₂ : Run f c ρ β x₀ multiplier₀) : run₁ = run₂ := by
  have hsequences (k : ℕ) :
      run₁.point k = run₂.point k ∧
        run₁.multiplier k = run₂.multiplier k ∧
          run₁.baseStep k = run₂.baseStep k := by
    induction k with
    | zero =>
        have hpoint : run₁.point 0 = run₂.point 0 :=
          run₁.point_zero.trans run₂.point_zero.symm
        have hmultiplier : run₁.multiplier 0 = run₂.multiplier 0 :=
          run₁.multiplier_zero.trans run₂.multiplier_zero.symm
        have hminimizes :
            IsMinOn (LALM.stepModel f c ρ β (run₂.point 0) (run₂.multiplier 0))
              Set.univ (run₁.baseStep 0) := by
          simpa only [hpoint, hmultiplier] using run₁.minimizes_baseStep 0
        have hbaseStep : run₁.baseStep 0 = run₂.baseStep 0 :=
          (LALM.Run.existsUniqueStepModelMinimizer f c ρ β
            (run₂.point 0) (run₂.multiplier 0) run₂.rho_pos run₂.beta_pos).unique
              hminimizes (run₂.minimizes_baseStep 0)
        exact ⟨hpoint, hmultiplier, hbaseStep⟩
    | succ k ih =>
        have hpoint : run₁.point (k + 1) = run₂.point (k + 1) := by
          calc
            run₁.point (k + 1) = nextPoint c (run₁.point k) (run₁.baseStep k) :=
              run₁.point_succ k
            _ = nextPoint c (run₂.point k) (run₂.baseStep k) := by
              rw [ih.1, ih.2.2]
            _ = run₂.point (k + 1) := (run₂.point_succ k).symm
        have hmultiplier :
            run₁.multiplier (k + 1) = run₂.multiplier (k + 1) := by
          calc
            run₁.multiplier (k + 1) =
                nextMultiplier c ρ (run₁.point k) (run₁.multiplier k)
                  (run₁.baseStep k) := run₁.multiplier_succ k
            _ = nextMultiplier c ρ (run₂.point k) (run₂.multiplier k)
                (run₂.baseStep k) := by
              rw [ih.1, ih.2.1, ih.2.2]
            _ = run₂.multiplier (k + 1) := (run₂.multiplier_succ k).symm
        have hminimizes :
            IsMinOn
              (LALM.stepModel f c ρ β (run₂.point (k + 1))
                (run₂.multiplier (k + 1))) Set.univ (run₁.baseStep (k + 1)) := by
          simpa only [hpoint, hmultiplier] using run₁.minimizes_baseStep (k + 1)
        have hbaseStep : run₁.baseStep (k + 1) = run₂.baseStep (k + 1) :=
          (LALM.Run.existsUniqueStepModelMinimizer f c ρ β
            (run₂.point (k + 1)) (run₂.multiplier (k + 1))
              run₂.rho_pos run₂.beta_pos).unique
                hminimizes (run₂.minimizes_baseStep (k + 1))
        exact ⟨hpoint, hmultiplier, hbaseStep⟩
  have hpoint : run₁.point = run₂.point :=
    funext fun k ↦ (hsequences k).1
  have hmultiplier : run₁.multiplier = run₂.multiplier :=
    funext fun k ↦ (hsequences k).2.1
  have hbaseStep : run₁.baseStep = run₂.baseStep :=
    funext fun k ↦ (hsequences k).2.2
  cases run₁
  cases run₂
  rw [Run.mk.injEq]
  exact ⟨hpoint, hmultiplier, hbaseStep⟩

/-- The structural uniqueness of a deterministic NR-LALM+SOC run with fixed
coefficients and initial data. -/
theorem unique (run₁ run₂ : Run f c ρ β x₀ multiplier₀) : run₁ = run₂ :=
  eq run₁ run₂

/-- Admissible corrected parameters determine at least one infinite
deterministic NR-LALM+SOC run from the prescribed initial data. -/
theorem nonempty_of_parameters
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀) :
    Nonempty (Run f c params.rho params.beta x₀ multiplier₀) := by
  let hrho : (0 : ℝ) < params.rho := params.spec.1.2.2.1
  let hbeta : (0 : ℝ) < params.beta := params.spec.1.2.1
  let transition := canonicalTransition f c (params.rho : ℝ) (params.beta : ℝ)
    hrho hbeta
  let state : ℕ → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) :=
    fun k ↦ transition^[k] (x₀, multiplier₀)
  let point : ℕ → EuclideanSpace ℝ (Fin n) := fun k ↦ (state k).1
  let multiplier : ℕ → EuclideanSpace ℝ (Fin m) := fun k ↦ (state k).2
  let baseStep : ℕ → EuclideanSpace ℝ (Fin n) := fun k ↦
    canonicalBaseStep f c params.rho params.beta (point k) (multiplier k) hrho hbeta
  have hstateZero : state 0 = (x₀, multiplier₀) := by
    simp only [state, Function.iterate_zero_apply]
  have hstateSucc (k : ℕ) : state (k + 1) = transition (state k) := by
    simp only [state, Function.iterate_succ_apply']
  refine ⟨Run.ofSequences f c params.rho params.beta x₀ multiplier₀
    hrho hbeta point multiplier baseStep ?_ ?_ ?_ ?_ ?_⟩
  · simpa only [point] using congrArg Prod.fst hstateZero
  · simpa only [multiplier] using congrArg Prod.snd hstateZero
  · intro k
    simpa only [baseStep] using canonicalBaseStep_minimizes f c
      (params.rho : ℝ) (params.beta : ℝ) (point k) (multiplier k) hrho hbeta
  · intro k
    have hnext := congrArg Prod.fst (hstateSucc k)
    simpa only [point, baseStep, transition, canonicalTransition] using hnext
  · intro k
    have hnext := congrArg Prod.snd (hstateSucc k)
    simpa only [point, multiplier, baseStep, transition, canonicalTransition] using hnext

/-- For admissible corrected parameters and fixed initial data, there exists
exactly one infinite deterministic NR-LALM+SOC run. -/
theorem existsUnique
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀) :
    ∃! run : Run f c params.rho params.beta x₀ multiplier₀,
      run.point 0 = x₀ := by
  obtain ⟨run⟩ := nonempty_of_parameters h params
  refine ⟨run, run.point_zero, ?_⟩
  intro other hother
  exact unique other run

/-- The explicit minimum-norm correction used at one corrected transition. -/
noncomputable def correction (run : Run f c ρ β x₀ multiplier₀) (k : ℕ) :
    EuclideanSpace ℝ (Fin n) :=
  step c (run.point k) (run.baseStep k)

/-- A run-facing correction is the Proposition 4.1 correction of its base step. -/
theorem correction_apply (run : Run f c ρ β x₀ multiplier₀) (k : ℕ) :
    run.correction k = step c (run.point k) (run.baseStep k) := by
  -- Expose the correction attached to this transition.
  rfl

/-- Helper for Corollary 4.2: the stored corrected multiplier transition is the
classical update evaluated at the next corrected point. -/
theorem multiplier_succ_eq_add (run : Run f c ρ β x₀ multiplier₀) (k : ℕ) :
    run.multiplier (k + 1) =
      run.multiplier k + ρ • c (run.point (k + 1)) := by
  -- Rewrite the owner update and identify its corrected point with the stored successor.
  rw [run.multiplier_succ, nextMultiplier_def, run.point_succ]

/-- The lifted corrected iterate stores the current point and multiplier together
with the preceding base-model step. -/
@[expose] def liftedIterate (run : Run f c ρ β x₀ multiplier₀) :
    ℕ → LiftedState n m :=
  fun k ↦ liftedState (run.point k) (run.multiplier k) (run.baseStep (k - 1))

/-- A lifted corrected iterate exposes its point, multiplier, and preceding base step. -/
theorem liftedIterate_apply (run : Run f c ρ β x₀ multiplier₀) (k : ℕ) :
    run.liftedIterate k =
      liftedState (run.point k) (run.multiplier k) (run.baseStep (k - 1)) := rfl

/-- Convergence of corrected lifted iterates to a state with zero base step
implies convergence of the whole point--multiplier sequence. -/
theorem pairTendsto_of_liftedTendsto
    (run : Run f c ρ β x₀ multiplier₀)
    (xStar : EuclideanSpace ℝ (Fin n))
    (multiplierStar : EuclideanSpace ℝ (Fin m))
    (h_lifted : Tendsto run.liftedIterate atTop
      (𝓝 (liftedState xStar multiplierStar 0))) :
    Tendsto (fun k ↦ (run.point k, run.multiplier k)) atTop
      (𝓝 (xStar, multiplierStar)) := by
  -- Project lifted convergence onto the primal coordinate.
  have hPoint : Tendsto (fun k ↦ run.point k) atTop (𝓝 xStar) := by
    have hProjection : Continuous (fun u : LiftedState n m ↦ u.fst) :=
      WithLp.continuous_fst 2 _ _
    have hProjected :=
      (hProjection.tendsto (liftedState xStar multiplierStar 0)).comp h_lifted
    exact hProjected.congr fun k ↦ by
      simp only [Function.comp_apply, liftedIterate_apply, liftedState_point]
  -- Project once more through the nested product to obtain the multiplier coordinate.
  have hMultiplier : Tendsto (fun k ↦ run.multiplier k) atTop (𝓝 multiplierStar) := by
    have hProjection : Continuous (fun u : LiftedState n m ↦ u.snd.fst) :=
      (WithLp.continuous_fst 2 _ _).comp (WithLp.continuous_snd 2 _ _)
    have hProjected :=
      (hProjection.tendsto (liftedState xStar multiplierStar 0)).comp h_lifted
    exact hProjected.congr fun k ↦ by
      simp only [Function.comp_apply, liftedIterate_apply, liftedState_multiplier]
  -- Reassemble the two coordinate limits in the product topology.
  exact hPoint.prodMk_nhds hMultiplier

/-- The corrected deterministic Lyapunov value uses the corrected
multiplier--primal constant and the preceding base step. -/
noncomputable def lyapunov
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀) (k : ℕ) : ℝ :=
  ℒ[f, c; params.rho](run.point k, run.multiplier k) +
    (multiplierPrimalConstant h params.delta params.beta params.rho
      params.multiplierBound / params.rho) * ‖run.baseStep (k - 1)‖ ^ 2

/-- The corrected Lyapunov value has its explicit source formula. -/
theorem lyapunov_def
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀) (k : ℕ) :
    run.lyapunov h params k =
      ℒ[f, c; params.rho](run.point k, run.multiplier k) +
        (multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound / params.rho) * ‖run.baseStep (k - 1)‖ ^ 2 := by
  -- Expose the augmented-Lagrangian and preceding-base-step terms.
  rfl

end Run

end LALM.Correction

end
