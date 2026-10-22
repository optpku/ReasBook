/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Algorithm_10_2
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Algorithm_10_61
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Lemma_10_61

local notation "Λ[" a "]" => primalCounterparts a

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped DualNorm

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Algorithm 10.62 is `source-facing` in the chapter's non-Euclidean first-order API.

Domain sampling against the nearby Chapter 10 files shows that the canonical owners already
available in the workspace are:
- `proximal_gradient_backtracking_trial_stepsize` together with the parameter types
  `ProximalGradientBacktrackingDecreaseFraction` and
  `ProximalGradientBacktrackingGrowthFactor` from Algorithm 10.2 for the geometric family
  `s η^i`;
- the operator norm surface `‖fderiv ℝ f x‖_*` from Algorithm 10.61 for the dual norm
  `‖f'(x^k)‖_*`;
- `Λ[·]` from Lemma 10.61 for the source set `Λ_{f'(x^k)}`;
- the Chapter 10 owner pattern
  `is_backtracking_procedure_B1_index` / `is_backtracking_procedure_B2_index` for recording that
  a trial is accepted and is the first accepted geometric one.

The source item does not define a new recursive trajectory; it only specifies how, for a fixed
iterate `x^k` and a chosen primal counterpart `f'(x^k)^†`, one selects the smallest accepted
curvature estimate in the geometric family `s η^i`. The primitive data are therefore the current
point `x`, the chosen counterpart `xDagger`, and the acceptance/minimality facts for a trial
curvature `L`; there is no separate source-facing trial-point owner beyond the displayed update
formula itself. These declarations only use the normed-space Fréchet-derivative and
primal-counterpart API above, so finite-dimensionality is not part of their public content. -/

/-- The B4 acceptance test accepts a trial curvature `L` at the current point `x` with chosen
primal counterpart `xDagger` exactly when the objective decrease produced by the trial point is at
least `(γ / L) ‖f'(x)‖_*²`. -/
def non_euclidean_gradient_backtracking_B4_accepts
    (f : E → ℝ) (γ : ProximalGradientBacktrackingDecreaseFraction)
    (L : PosReal) (x xDagger : E) : Prop :=
  let xNext := x - (‖fderiv ℝ f x‖_* / (L : ℝ)) • xDagger
  f x - f xNext ≥
    (γ : ℝ) / (L : ℝ) * ‖fderiv ℝ f x‖_* ^ (2 : ℕ)

/-- The B4 acceptance predicate is exactly the displayed sufficient-decrease inequality for the
trial curvature `L`. -/
theorem non_euclidean_gradient_backtracking_B4_accepts_iff
    (f : E → ℝ) (γ : ProximalGradientBacktrackingDecreaseFraction)
    (L : PosReal) (x xDagger : E) :
    non_euclidean_gradient_backtracking_B4_accepts f γ L x xDagger ↔
      let xNext := x - (‖fderiv ℝ f x‖_* / (L : ℝ)) • xDagger
      f x - f xNext ≥
        (γ : ℝ) / (L : ℝ) * ‖fderiv ℝ f x‖_* ^ (2 : ℕ) :=
  Iff.rfl

/-- Algorithm 10.62: given parameters `s > 0`, `γ ∈ (0,1)`, and `η > 1`, an index `i_k` is a
valid output of backtracking procedure B4 at a current iterate `x^k` with chosen primal
counterpart `xDagger = f'(x^k)^†` when `f` is differentiable at `x^k`, the chosen direction
belongs to `Λ_{f'(x^k)}`, the trial curvature `s η^{i_k}` satisfies
`f(x^k) - f(x^k - (‖f'(x^k)‖_* / (s η^{i_k})) • xDagger) ≥ (γ / (s η^{i_k})) ‖f'(x^k)‖_*²`,
and every earlier geometric trial fails this inequality. -/
class is_backtracking_procedure_B4_index
    (f : E → ℝ) (s : PosReal) (γ : ProximalGradientBacktrackingDecreaseFraction)
    (η : ProximalGradientBacktrackingGrowthFactor)
    (x xDagger : E) (i : ℕ) : Prop where
  differentiableAt : DifferentiableAt ℝ f x
  counterpart_mem : xDagger ∈ Λ[fderiv ℝ f x]
  accepts :
    non_euclidean_gradient_backtracking_B4_accepts f γ
      (proximal_gradient_backtracking_trial_stepsize s η i) x xDagger
  minimal (j : ℕ) (hj : j < i) :
    ¬ non_euclidean_gradient_backtracking_B4_accepts f γ
        (proximal_gradient_backtracking_trial_stepsize s η j) x xDagger

/-- An accepted B4 backtracking index yields the corresponding acceptance fact as a `Fact`
instance. -/
instance is_backtracking_procedure_B4_index_accepts_fact
    {f : E → ℝ} {s : PosReal} {γ : ProximalGradientBacktrackingDecreaseFraction}
    {η : ProximalGradientBacktrackingGrowthFactor}
    {x xDagger : E} {i : ℕ}
    [h : is_backtracking_procedure_B4_index f s γ η x xDagger i] :
    Fact
      (non_euclidean_gradient_backtracking_B4_accepts f γ
        (proximal_gradient_backtracking_trial_stepsize s η i) x xDagger) :=
  ⟨h.accepts⟩

/-- A valid B4 backtracking index records differentiability of `f` at the current iterate `x`. -/
theorem is_backtracking_procedure_B4_index_differentiableAt
    {f : E → ℝ} {s : PosReal} {γ : ProximalGradientBacktrackingDecreaseFraction}
    {η : ProximalGradientBacktrackingGrowthFactor}
    {x xDagger : E} {i : ℕ}
    (hi : is_backtracking_procedure_B4_index f s γ η x xDagger i) :
    DifferentiableAt ℝ f x :=
  hi.differentiableAt

/-- A valid B4 backtracking index records that the chosen direction belongs to
`Λ_{f'(x)}`. -/
theorem is_backtracking_procedure_B4_index_counterpart_mem
    {f : E → ℝ} {s : PosReal} {γ : ProximalGradientBacktrackingDecreaseFraction}
    {η : ProximalGradientBacktrackingGrowthFactor}
    {x xDagger : E} {i : ℕ}
    (hi : is_backtracking_procedure_B4_index f s γ η x xDagger i) :
    xDagger ∈ Λ[fderiv ℝ f x] :=
  hi.counterpart_mem

/-- A valid B4 backtracking index has an accepted trial curvature `s η^i`. -/
theorem is_backtracking_procedure_B4_index_accepts
    {f : E → ℝ} {s : PosReal} {γ : ProximalGradientBacktrackingDecreaseFraction}
    {η : ProximalGradientBacktrackingGrowthFactor}
    {x xDagger : E} {i : ℕ}
    (hi : is_backtracking_procedure_B4_index f s γ η x xDagger i) :
    non_euclidean_gradient_backtracking_B4_accepts
      f γ (proximal_gradient_backtracking_trial_stepsize s η i) x xDagger :=
  hi.accepts

/-- A valid B4 backtracking index is minimal among the accepted geometric trials based on `s`. -/
theorem is_backtracking_procedure_B4_index_minimal
    {f : E → ℝ} {s : PosReal} {γ : ProximalGradientBacktrackingDecreaseFraction}
    {η : ProximalGradientBacktrackingGrowthFactor}
    {x xDagger : E} {i j : ℕ}
    (hi : is_backtracking_procedure_B4_index f s γ η x xDagger i)
    (hj : j < i) :
    ¬ non_euclidean_gradient_backtracking_B4_accepts
        f γ (proximal_gradient_backtracking_trial_stepsize s η j) x xDagger :=
  hi.minimal j hj

/-- A trajectory uses backtracking procedure B4 when, at every iteration `k`, the accepted
curvature estimate `L_k` is the first accepted geometric trial `s η^{i_k}` at the current
iterate `x^k` and chosen primal counterpart `xDagger^k`. -/
def uses_non_euclidean_backtracking_B4_rule
    (f : E → ℝ) (x : ℕ → E) (L : ℕ → PosReal) (xDagger : ℕ → E)
    (s : PosReal) (γ : ProximalGradientBacktrackingDecreaseFraction)
    (η : ProximalGradientBacktrackingGrowthFactor) : Prop :=
  ∀ k : ℕ, ∃ i : ℕ,
    is_backtracking_procedure_B4_index f s γ η (x k) (xDagger k) i ∧
      L k = proximal_gradient_backtracking_trial_stepsize s η i

-- Proof sketch: specialize `uses_non_euclidean_backtracking_B4_rule` at iteration `k`; the
-- chosen index carries the acceptance fact as its `accepts` field, and the defining equality
-- identifies the actual curvature estimate `L_k` with that accepted trial.
/-- Under backtracking procedure B4, the chosen curvature estimate `L_k` satisfies the B4
acceptance inequality at the iterate `x^k` with chosen primal counterpart `xDagger^k`. -/
theorem uses_non_euclidean_backtracking_B4_rule_accepts
    {f : E → ℝ} {x : ℕ → E} {L : ℕ → PosReal} {xDagger : ℕ → E}
    {s : PosReal} {γ : ProximalGradientBacktrackingDecreaseFraction}
    {η : ProximalGradientBacktrackingGrowthFactor}
    (hrule : uses_non_euclidean_backtracking_B4_rule f x L xDagger s γ η)
    (k : ℕ) :
    non_euclidean_gradient_backtracking_B4_accepts
      f γ (L k) (x k) (xDagger k) := by
  rcases hrule k with ⟨i, hi, hLk⟩
  simpa [hLk] using is_backtracking_procedure_B4_index_accepts hi

end
