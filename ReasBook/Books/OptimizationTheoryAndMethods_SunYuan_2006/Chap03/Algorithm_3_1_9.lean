/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Algorithm_2_5_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Definition_2_5_extra_5
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Definition_3_1_extra_1
import Mathlib.Data.Real.Basic

universe u

-- Source/core/bridge triage:
-- * source-facing: the Barzilai-Borwein Step 2 cutoff, the Step 4 nonmonotone acceptance
--   inequality, and the Step 6 spectral update recorded along one run;
-- * core/canonical owners inspected: `steepestDescentDirection`, `steepestDescentStep`,
--   `nonmonotoneArmijoReferenceValue`, and `IsBacktrackingLineSearchStep`;
-- * bridge/view: the normalized backtracking factor sequence
--   `backtrackingArmijoStepSizes params.σ₁ (shrinkFactors k)` on the scaled canonical
--   steepest-descent direction
--   `(barzilaiBorweinTrialStep params (α k)) • steepestDescentDirection f (x k)`.

/-- Input data and scalar side conditions for the Barzilai-Borwein gradient algorithm,
including the Step 0 cutoff parameters `α^(l)` and `α^(u)`. -/
structure BarzilaiBorweinGradientParams (E : Type u) where
  x0 : E
  ε : ℝ
  M : ℕ
  ρ : ℝ
  δ : ℝ
  σ₁ : ℝ
  σ₂ : ℝ
  αLower : ℝ
  αUpper : ℝ
  epsilon_pos : 0 < ε
  rho_mem : ρ ∈ Set.Ioo (0 : ℝ) 1
  delta_pos : 0 < δ
  sigma_bounds : 0 < σ₁ ∧ σ₁ < σ₂ ∧ σ₂ < 1
  alpha_bounds : 0 < αLower ∧ αLower < αUpper

variable {E : Type u}

/-- The Step 2 reset rule for the spectral parameter `α_k`. -/
noncomputable def barzilaiBorweinTrialAlpha (params : BarzilaiBorweinGradientParams E)
    (αk : ℝ) : ℝ :=
  if αk ∈ Set.Icc params.αLower params.αUpper then αk else params.δ

/-- The Step 3 trial step size `λ = 1 / α_k` after the Step 2 reset rule. -/
noncomputable def barzilaiBorweinTrialStep (params : BarzilaiBorweinGradientParams E)
    (αk : ℝ) : ℝ :=
  1 / barzilaiBorweinTrialAlpha params αk

/-- The Step 2 cutoff rule always produces a positive spectral parameter. -/
theorem barzilaiBorweinTrialAlpha_pos (params : BarzilaiBorweinGradientParams E)
    (αk : ℝ) : 0 < barzilaiBorweinTrialAlpha params αk := by
  by_cases hα : αk ∈ Set.Icc params.αLower params.αUpper
  · have hPos : 0 < αk := lt_of_lt_of_le params.alpha_bounds.1 hα.1
    simpa [barzilaiBorweinTrialAlpha, hα] using hPos
  · simpa [barzilaiBorweinTrialAlpha, hα] using params.delta_pos

/-- The Step 3 reciprocal trial step size is positive. -/
theorem barzilaiBorweinTrialStep_pos (params : BarzilaiBorweinGradientParams E)
    (αk : ℝ) : 0 < barzilaiBorweinTrialStep params αk := by
  simpa [barzilaiBorweinTrialStep] using
    one_div_pos.mpr (barzilaiBorweinTrialAlpha_pos params αk)

/-- The accepted Step 5 backtracking scale is the recorded accepted Chapter 2 scale. -/
def barzilaiBorweinAcceptedScale (σ₁ : ℝ) (shrinkFactors : ℕ → List ℝ) (k : ℕ) : ℝ :=
  backtrackingArmijoStepSizes σ₁ (shrinkFactors k) (shrinkFactors k).length

/-- The accepted Step 5 step length `λ_k` is the accepted backtracking scale times the Step 3
trial step. -/
noncomputable def barzilaiBorweinStepSize (params : BarzilaiBorweinGradientParams E)
    (α : ℕ → ℝ) (shrinkFactors : ℕ → List ℝ) (k : ℕ) : ℝ :=
  barzilaiBorweinAcceptedScale params.σ₁ shrinkFactors k * barzilaiBorweinTrialStep params (α k)

section

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The Step 4 acceptance inequality for the nonmonotone line search along the canonical
steepest-descent update. -/
def barzilaiBorweinAccepts (params : BarzilaiBorweinGradientParams E)
    (f : E → ℝ) (x : ℕ → E) (k : ℕ) (stepSize : ℝ) : Prop :=
  f (steepestDescentStep f (x k) stepSize) ≤
    nonmonotoneArmijoReferenceValue f x k params.M -
      params.ρ * stepSize * ‖gradient f (x k)‖ ^ 2

/-- The canonical backtracking acceptability predicate obtained by scaling the initial BB trial
step by the normalized backtracking factors and evaluating Step 4 at the resulting trial point. -/
def barzilaiBorweinAcceptable (params : BarzilaiBorweinGradientParams E)
    (f : E → ℝ) (x : ℕ → E) (k : ℕ) (αk : ℝ) : ℝ → E → Prop :=
  fun scale z ↦
    f z ≤
      nonmonotoneArmijoReferenceValue f x k params.M -
        params.ρ * (scale * barzilaiBorweinTrialStep params αk) * ‖gradient f (x k)‖ ^ 2

/-- Evaluating the canonical acceptability predicate at the corresponding scaled steepest-descent
trial point recovers the source Step 4 inequality. -/
theorem barzilaiBorweinAcceptable_iff_accepts
    (params : BarzilaiBorweinGradientParams E) (f : E → ℝ) (x : ℕ → E) (k : ℕ) (αk scale : ℝ) :
    barzilaiBorweinAcceptable params f x k αk scale
        (steepestDescentStep f (x k) (scale * barzilaiBorweinTrialStep params αk)) ↔
      barzilaiBorweinAccepts params f x k (scale * barzilaiBorweinTrialStep params αk) := by
  rfl

/-- The Step 6 gradient difference is the canonical increment `g_{k+1} - g_k`. -/
def barzilaiBorweinGradientDifference (g : ℕ → E) (k : ℕ) : E :=
  g (k + 1) - g k

/-- Chapter03 Algorithm 3.1.9: a run of the Barzilai-Borwein gradient algorithm with
nonmonotone line search on a real Hilbert space.

The primitive run data are `x`, `g`, `α`, and the recorded shrink-factor traces
`shrinkFactors`; the Step 5 accepted step `λ_k` and the Step 6 difference `y_k = g_{k+1} - g_k`
are derived from those owners rather than stored separately. At every iterate `k`, the field
`hasGradientAt` records that `g k` is the gradient of `f` at `x k`. The parameter object carries
the Step 0 cutoff parameters `α^(l)` and `α^(u)` together with the source cutoff hypothesis
`0 < α^(l) < α^(u)`. For every index `k` with `params.ε < ‖g k‖`, the fields
`shrinkFactors_mem`, `lineSearch`, `nextPoint_eq`, and `nextAlpha_eq` encode Step 2 through
Step 6: reset `α_k` if it leaves the admissible interval, start from the reciprocal trial step
size, shrink it by finitely many factors in `[σ₁, σ₂]`, package the Step 4/Step 5 least-accepted
trial through the canonical backtracking owner, update `x_{k+1}` by the canonical
steepest-descent owner with the derived accepted step `λ_k`, and then update `α_{k+1}` by the
source quotient formula on that nonterminal step. The positivity of `λ_k` is derived from the
cutoff bounds, `δ > 0`, and the canonical backtracking owner rather than stored as extra
primitive data. -/
structure BarzilaiBorweinGradientRun (E : Type u)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  params : BarzilaiBorweinGradientParams E
  f : E → ℝ
  x : ℕ → E
  g : ℕ → E
  α : ℕ → ℝ
  shrinkFactors : ℕ → List ℝ
  start : x 0 = params.x0
  hasGradientAt (k : ℕ) : HasGradientAt f (g k) (x k)
  shrinkFactors_mem (k : ℕ) (hk : params.ε < ‖g k‖) (σ : ℝ) (hσ : σ ∈ shrinkFactors k) :
      params.σ₁ ≤ σ ∧ σ ≤ params.σ₂
  lineSearch (k : ℕ) (hk : params.ε < ‖g k‖) :
      IsBacktrackingLineSearchStep
        (barzilaiBorweinAcceptable params f x k (α k))
        (x k)
        ((barzilaiBorweinTrialStep params (α k)) • steepestDescentDirection f (x k))
        (backtrackingArmijoStepSizes params.σ₁ (shrinkFactors k))
        (shrinkFactors k).length
  nextPoint_eq (k : ℕ) (hk : params.ε < ‖g k‖) :
      x (k + 1) =
        steepestDescentStep f (x k) (barzilaiBorweinStepSize params α shrinkFactors k)
  nextAlpha_eq (k : ℕ) (hk : params.ε < ‖g k‖) :
      α (k + 1) =
        -(inner ℝ (g k) (barzilaiBorweinGradientDifference g k)) /
          (barzilaiBorweinStepSize params α shrinkFactors k * inner ℝ (g k) (g k))

namespace BarzilaiBorweinGradientRun

/-- A Barzilai-Borwein run coerces to its iterate sequence `k ↦ x_k`. -/
instance : CoeFun (BarzilaiBorweinGradientRun E) (fun _ ↦ ℕ → E) where
  coe run := run.x

/-- The accepted Step 5 backtracking scale at iteration `k`. -/
def acceptedScale (run : BarzilaiBorweinGradientRun E) (k : ℕ) : ℝ :=
  barzilaiBorweinAcceptedScale run.params.σ₁ run.shrinkFactors k

/-- The accepted Step 5 step length `λ_k` determined by the recorded backtracking trace. -/
noncomputable def stepSize (run : BarzilaiBorweinGradientRun E) (k : ℕ) : ℝ :=
  barzilaiBorweinStepSize run.params run.α run.shrinkFactors k

/-- The Step 6 gradient difference `y_k = g_{k+1} - g_k`. -/
def y (run : BarzilaiBorweinGradientRun E) (k : ℕ) : E :=
  barzilaiBorweinGradientDifference run.g k

/-- Evaluating a Barzilai-Borwein run as a function returns its iterate sequence. -/
theorem coe_apply (run : BarzilaiBorweinGradientRun E) (k : ℕ) :
    run k = run.x k := rfl

/-- Unfolding `acceptedScale` recovers the accepted Chapter 2 backtracking scale. -/
theorem acceptedScale_eq (run : BarzilaiBorweinGradientRun E) (k : ℕ) :
    run.acceptedScale k =
      backtrackingArmijoStepSizes run.params.σ₁ (run.shrinkFactors k)
        (run.shrinkFactors k).length :=
  rfl

/-- Unfolding `stepSize` recovers the accepted backtracking scale times the Step 3 trial step. -/
theorem stepSize_eq (run : BarzilaiBorweinGradientRun E) (k : ℕ) :
    run.stepSize k =
      backtrackingArmijoStepSizes run.params.σ₁ (run.shrinkFactors k) (run.shrinkFactors k).length *
        barzilaiBorweinTrialStep run.params (run.α k) :=
  rfl

/-- Unfolding `y` recovers the Step 6 gradient difference `g_{k+1} - g_k`. -/
theorem y_eq (run : BarzilaiBorweinGradientRun E) (k : ℕ) :
    run.y k = run.g (k + 1) - run.g k :=
  rfl

/-- The explicit gradient data in a Barzilai-Borwein run agree with the canonical gradient. -/
theorem gradient_eq (run : BarzilaiBorweinGradientRun E) (k : ℕ) :
    gradient run.f (run.x k) = run.g k :=
  (run.hasGradientAt k).gradient

/-- A nonterminal iteration of a Barzilai-Borwein run carries the canonical Chapter 2
backtracking witness for the Step 4/Step 5 search on the scaled steepest-descent direction. -/
theorem lineSearch_of_not_stopped
    (run : BarzilaiBorweinGradientRun E) {k : ℕ} (hk : run.params.ε < ‖run.g k‖) :
    IsBacktrackingLineSearchStep
      (barzilaiBorweinAcceptable run.params run.f run.x k (run.α k))
      (run.x k)
      ((barzilaiBorweinTrialStep run.params (run.α k)) •
        steepestDescentDirection run.f (run.x k))
      (backtrackingArmijoStepSizes run.params.σ₁ (run.shrinkFactors k))
      (run.shrinkFactors k).length :=
  run.lineSearch k hk

/-- A nonterminal iteration of a Barzilai-Borwein run satisfies the Step 4 acceptance test. -/
theorem accepts_of_not_stopped
    (run : BarzilaiBorweinGradientRun E) {k : ℕ} (hk : run.params.ε < ‖run.g k‖) :
    barzilaiBorweinAccepts run.params run.f run.x k (run.stepSize k) := by
  have hAcceptable :
      barzilaiBorweinAcceptable run.params run.f run.x k (run.α k)
        (run.acceptedScale k)
        (steepestDescentStep run.f (run.x k) (run.stepSize k)) := by
    simpa [BarzilaiBorweinGradientRun.acceptedScale, barzilaiBorweinAcceptedScale,
      run.stepSize_eq k, backtrackingTrialPoint, steepestDescentStep, smul_smul, mul_assoc] using
      (run.lineSearch_of_not_stopped hk).accepts
  simpa [BarzilaiBorweinGradientRun.acceptedScale, barzilaiBorweinAcceptedScale,
    run.stepSize_eq k] using
    (barzilaiBorweinAcceptable_iff_accepts run.params run.f run.x k (run.α k)
      (run.acceptedScale k)).mp hAcceptable

/-- A nonterminal iteration of a Barzilai-Borwein run uses a positive accepted step `λ_k`. -/
theorem stepSize_pos_of_not_stopped
    (run : BarzilaiBorweinGradientRun E) {k : ℕ} (hk : run.params.ε < ‖run.g k‖) :
    0 < run.stepSize k := by
  rw [run.stepSize_eq k]
  exact mul_pos
    (run.lineSearch_of_not_stopped hk).acceptedStep_pos
    (barzilaiBorweinTrialStep_pos run.params (run.α k))

/-- Every earlier Step 4/Step 5 backtracking index fails the nonmonotone acceptance test
before the accepted step `λ_k`. -/
theorem not_accepts_of_lt
    (run : BarzilaiBorweinGradientRun E) {k : ℕ} (hk : run.params.ε < ‖run.g k‖)
    {m : ℕ} (hm : m < (run.shrinkFactors k).length) :
    ¬ barzilaiBorweinAccepts run.params run.f run.x k
      (backtrackingArmijoStepSizes run.params.σ₁ (run.shrinkFactors k) m *
        barzilaiBorweinTrialStep run.params (run.α k)) := by
  intro hAccepts
  apply (run.lineSearch_of_not_stopped hk).not_accepts_of_lt hm
  have hAcceptable :
      barzilaiBorweinAcceptable run.params run.f run.x k (run.α k)
        (backtrackingArmijoStepSizes run.params.σ₁ (run.shrinkFactors k) m)
        (steepestDescentStep run.f (run.x k)
          (backtrackingArmijoStepSizes run.params.σ₁ (run.shrinkFactors k) m *
            barzilaiBorweinTrialStep run.params (run.α k))) :=
    (barzilaiBorweinAcceptable_iff_accepts run.params run.f run.x k (run.α k)
      (backtrackingArmijoStepSizes run.params.σ₁ (run.shrinkFactors k) m)).mpr hAccepts
  simpa [backtrackingTrialPoint, steepestDescentStep, smul_smul, mul_assoc] using hAcceptable

/-- A nonterminal iteration of a Barzilai-Borwein run updates the next iterate by the
canonical steepest-descent owner with the accepted step `λ_k`. -/
theorem nextPoint_eq_of_not_stopped
    (run : BarzilaiBorweinGradientRun E) {k : ℕ} (hk : run.params.ε < ‖run.g k‖) :
    run.x (k + 1) = steepestDescentStep run.f (run.x k) (run.stepSize k) := by
  simpa [BarzilaiBorweinGradientRun.stepSize, barzilaiBorweinStepSize] using
    run.nextPoint_eq k hk

/-- The canonical steepest-descent update expands to the source Step 5 formula
`x_{k+1} = x_k - λ_k g_k`. -/
theorem nextPoint_eq_sub_of_not_stopped
    (run : BarzilaiBorweinGradientRun E) {k : ℕ} (hk : run.params.ε < ‖run.g k‖) :
    run.x (k + 1) = run.x k - (run.stepSize k) • run.g k := by
  simpa [steepestDescentStep_eq, run.gradient_eq k] using
    run.nextPoint_eq_of_not_stopped hk

/-- On every nonterminal iteration, the Step 6 denominator is strictly positive. -/
theorem nextAlpha_denom_pos_of_not_stopped
    (run : BarzilaiBorweinGradientRun E) {k : ℕ} (hk : run.params.ε < ‖run.g k‖) :
    0 < run.stepSize k * inner ℝ (run.g k) (run.g k) := by
  refine mul_pos (run.stepSize_pos_of_not_stopped hk) ?_
  have hg_norm_pos : 0 < ‖run.g k‖ := lt_trans run.params.epsilon_pos hk
  have hg_ne : run.g k ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hg_norm_pos)
  simpa [real_inner_self_eq_norm_sq] using
    sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hg_ne)

/-- On a nonterminal iteration, Step 6 updates the spectral parameter by the textbook
Barzilai-Borwein quotient formula. -/
theorem nextAlpha_eq_of_not_stopped
    (run : BarzilaiBorweinGradientRun E) {k : ℕ} (hk : run.params.ε < ‖run.g k‖) :
    run.α (k + 1) = -(inner ℝ (run.g k) (run.y k)) /
      (run.stepSize k * inner ℝ (run.g k) (run.g k)) := by
  simpa [BarzilaiBorweinGradientRun.y, BarzilaiBorweinGradientRun.stepSize,
    barzilaiBorweinGradientDifference, barzilaiBorweinStepSize] using
    run.nextAlpha_eq k hk

end BarzilaiBorweinGradientRun

end
