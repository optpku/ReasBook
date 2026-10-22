/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Algorithm_10_1
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Algorithm_10_2
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_9

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

/- Algorithm 10.3 is `source-facing` in the Chapter 10 proximal-gradient API.

Domain sampling in the existing chapter points to:
- `is_proximal_gradient_trajectory` and `proximal_gradient_trajectory_iterate` from Algorithm
  10.1 as the canonical owner of the iterate sequence `x^k` and its interior-domain view;
- `proximal_gradient_backtracking_trial_stepsize` from Algorithm 10.2 as the canonical owner of
  the geometric trial family `LPrev η^i`;
- `ProximalGradientBacktrackingGrowthFactor` from Algorithm 10.2 as the canonical owner of the
  parameter constraint `η > 1`;
- `prox_grad_operator` from Definition 10.9 as the canonical prox-gradient update map.

So the B2 file should keep only the procedure-specific acceptance predicate and the predicate
saying that an index is the first accepted trial, while reusing the chapter owner for the trial
curvature itself. -/

/-- The acceptance test in backtracking procedure B2 accepts `L` at `x` exactly when the prox-grad
point `T_L(x)` satisfies the quadratic upper-model inequality
`f(T_L(x)) ≤ f(x) + ⟪∇f(x), T_L(x) - x⟫ + (L / 2) ‖T_L(x) - x‖²`. -/
def proximal_gradient_backtracking_B2_accepts
    (f g : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (L : PosReal) (x : interior (effective_domain f)) : Prop :=
  let xNext := T[L, f, g] x
  f xNext ≤
    f (x : E) +
      ((inner ℝ (∇ (fun y ↦ (f y).toReal) (x : E)) (xNext - (x : E)) +
        ((L : ℝ) / 2) * ‖xNext - (x : E)‖ ^ (2 : ℕ) : ℝ) : EReal)

-- Proof sketch: unfold `proximal_gradient_backtracking_B2_accepts`; the statement is exactly the
-- textbook quadratic upper-model inequality written with the chapter's prox-grad operator `T_L`.
/-- The B2 acceptance predicate is exactly the displayed quadratic upper-model inequality for the
trial curvature `L`. -/
theorem proximal_gradient_backtracking_B2_accepts_iff
    (f g : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (L : PosReal) (x : interior (effective_domain f)) :
    proximal_gradient_backtracking_B2_accepts f g L x ↔
      let xNext := T[L, f, g] x
      f xNext ≤
        f (x : E) +
          ((inner ℝ (∇ (fun y ↦ (f y).toReal) (x : E)) (xNext - (x : E)) +
            ((L : ℝ) / 2) * ‖xNext - (x : E)‖ ^ (2 : ℕ) : ℝ) : EReal) :=
  Iff.rfl

/-- The previous curvature estimate used by backtracking procedure B2 is `s` at the initial step
and `L_k` at the next step. -/
def proximal_gradient_backtracking_B2_previous_stepsize
    (s : PosReal) (L : ℕ → PosReal) : ℕ → PosReal
  | 0 => s
  | k + 1 => L k

-- Proof sketch: unfold `proximal_gradient_backtracking_B2_previous_stepsize` at `0`; the
-- recursive equation gives the result immediately.
/-- The initial previous curvature estimate for B2 is `s = L_(-1)`. -/
@[simp] theorem proximal_gradient_backtracking_B2_previous_stepsize_zero
    (s : PosReal) (L : ℕ → PosReal) :
    proximal_gradient_backtracking_B2_previous_stepsize s L 0 = s :=
  rfl

-- Proof sketch: unfold `proximal_gradient_backtracking_B2_previous_stepsize` at `k + 1`; the
-- recursive equation identifies the previous estimate with `L_k`.
/-- At step `k + 1`, the previous B2 curvature estimate is `L_k`. -/
@[simp] theorem proximal_gradient_backtracking_B2_previous_stepsize_succ
    (s : PosReal) (L : ℕ → PosReal) (k : ℕ) :
    proximal_gradient_backtracking_B2_previous_stepsize s L (k + 1) = L k :=
  rfl

/-- Algorithm 10.3: given a previous curvature estimate `LPrev > 0` and a growth factor `η > 1`,
an index `i` is a valid B2 backtracking output at the current iterate `x` when the trial
curvature `LPrev η^i` is the first geometric trial satisfying the quadratic upper-model
acceptance test. At iteration `k`, this applies with `LPrev = L_(k-1)`, and at the initial step
with `LPrev = s = L_(-1)`. -/
class is_backtracking_procedure_B2_index
    (f g : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (LPrev : PosReal) (η : ProximalGradientBacktrackingGrowthFactor)
    (x : interior (effective_domain f)) (i : ℕ) : Prop where
  accepts :
    proximal_gradient_backtracking_B2_accepts f g
      (proximal_gradient_backtracking_trial_stepsize LPrev η i) x
  minimal (j : ℕ) (hj : j < i) :
    ¬ proximal_gradient_backtracking_B2_accepts f g
        (proximal_gradient_backtracking_trial_stepsize LPrev η j) x

/-- An accepted B2 backtracking index yields the corresponding acceptance fact as a `Fact`
instance. -/
instance is_backtracking_procedure_B2_index_accepts_fact
    {f g : E → EReal} [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    {LPrev : PosReal} {η : ProximalGradientBacktrackingGrowthFactor}
    {x : interior (effective_domain f)} {i : ℕ}
    [h : is_backtracking_procedure_B2_index f g LPrev η x i] :
    Fact
      (proximal_gradient_backtracking_B2_accepts f g
        (proximal_gradient_backtracking_trial_stepsize LPrev η i) x) :=
  ⟨h.accepts⟩

-- Proof sketch: use the `accepts` field of `is_backtracking_procedure_B2_index`; it states that
-- the geometric trial `LPrev η^i` satisfies the B2 acceptance inequality at the current iterate.
/-- A valid B2 backtracking index has an accepted trial curvature `LPrev η^i`. -/
theorem is_backtracking_procedure_B2_index_accepts
    {f g : E → EReal} [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    {LPrev : PosReal} {η : ProximalGradientBacktrackingGrowthFactor}
    {x : interior (effective_domain f)} {i : ℕ}
    (hi : is_backtracking_procedure_B2_index f g LPrev η x i) :
    proximal_gradient_backtracking_B2_accepts f g
      (proximal_gradient_backtracking_trial_stepsize LPrev η i) x :=
  hi.accepts

-- Proof sketch: use the `minimal` field of `is_backtracking_procedure_B2_index`; every earlier
-- trial index `j < i` is required to fail the B2 acceptance test.
/-- A valid B2 backtracking index is minimal among the accepted geometric trials based on
`LPrev`. -/
theorem is_backtracking_procedure_B2_index_minimal
    {f g : E → EReal} [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    {LPrev : PosReal} {η : ProximalGradientBacktrackingGrowthFactor}
    {x : interior (effective_domain f)} {i j : ℕ}
    (hi : is_backtracking_procedure_B2_index f g LPrev η x i)
    (hj : j < i) :
    ¬ proximal_gradient_backtracking_B2_accepts f g
        (proximal_gradient_backtracking_trial_stepsize LPrev η j) x :=
  hi.minimal j hj

/-- A proximal-gradient trajectory uses backtracking procedure B2 when, at every iteration `k`,
the accepted curvature estimate `L_k` is the first accepted geometric trial based on `s` at
`k = 0` and on `L_(k-1)` at later iterates. The regularity assumptions on `g` are ambient
instance data, matching the acceptance owner `proximal_gradient_backtracking_B2_accepts`. -/
def uses_proximal_gradient_backtracking_B2_rule
    (f g : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (x : ℕ → E) (L : ℕ → PosReal)
    (htraj : is_proximal_gradient_trajectory f g x L)
    (s : PosReal) (η : ProximalGradientBacktrackingGrowthFactor) : Prop :=
  ∀ k : ℕ, ∃ i : ℕ,
    is_backtracking_procedure_B2_index
      f g (proximal_gradient_backtracking_B2_previous_stepsize s L k) η
      (proximal_gradient_trajectory_iterate htraj k) i ∧
    L k =
      proximal_gradient_backtracking_trial_stepsize
        (proximal_gradient_backtracking_B2_previous_stepsize s L k) η i

-- Proof sketch: specialize `uses_proximal_gradient_backtracking_B2_rule` at the iteration `k`;
-- the chosen index is accepted by `is_backtracking_procedure_B2_index_accepts`, and the defining
-- equality identifies the actual stepsize `L_k` with that accepted trial.
/-- Under backtracking procedure B2, the chosen stepsize `L_k` satisfies the B2 acceptance
inequality at the iterate `x^k`. -/
theorem uses_proximal_gradient_backtracking_B2_rule_accepts
    {f g : E → EReal} [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    {x : ℕ → E} {L : ℕ → PosReal}
    {htraj : is_proximal_gradient_trajectory f g x L}
    {s : PosReal} {η : ProximalGradientBacktrackingGrowthFactor}
    (hrule : uses_proximal_gradient_backtracking_B2_rule
      f g x L htraj s η)
    (k : ℕ) :
    proximal_gradient_backtracking_B2_accepts
      f g (L k) (proximal_gradient_trajectory_iterate htraj k) := by
  rcases hrule k with ⟨i, hi, hLk⟩
  rw [hLk]
  exact hi.accepts

end
