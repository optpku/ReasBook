/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap05.Definition_5_1
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Lemma_5_7
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Algorithm_10_2
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Algorithm_10_13
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Assumption_10_31
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Remark_10_19

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Gradient

section

variable {E : Type u}

/-- The initial FISTA state determined by the input point `x0`, with
`x^{-1} = x^0 = x0` and `t_0 = 1`. -/
def fista_initial_state (x0 : E) : FISTAState E :=
  { xPrev := x0
    xCur := x0
    tCur := 1 }

-- Proof sketch: unfold `fista_initial_state`; the current iterate field is definitionally the
-- initial point `x0`.
/-- The current iterate of the initial FISTA state is the input point `x0`. -/
@[simp] theorem fista_initial_state_xCur (x0 : E) :
    (fista_initial_state x0).xCur = x0 := by
  -- Unfold the initial state: its `xCur` field is definitionally `x0`.
  rfl

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

/- Algorithm 10.6 is `source-facing` in the chapter's fast proximal-gradient API.

Domain sampling:
- `T[...]` from Definition 10.9 and `fista_momentum_update`, `FISTAState`, and
  `fista_extrapolated_point` from Algorithm 10.13 are already the local owner abstractions for
  the prox-gradient map `T_L`, the momentum update, the triple `(x^{k-1}, x^k, t_k)`, and its
  derived extrapolated point `y^k`;
- `proximal_gradient_backtracking_trial_stepsize` and
  `ProximalGradientBacktrackingGrowthFactor` from Algorithm 10.2 already encode the geometric
  trial family `L_(k-1) η^i` used by B3;
- `proximal_gradient_backtracking_B2_accepts`,
  `proximal_gradient_backtracking_B2_previous_stepsize`, and
  `is_backtracking_procedure_B2_index` from Algorithm 10.3 are already the chapter owners for the
  quadratic upper-model acceptance test, the recursion for the previous accepted stepsize, and the
  minimal accepted trial index;
- `uses_proximal_gradient_Lf_stepsize_rule` from Remark 10.19 is already the chapter owner for
  the exact constant rule `L_k = L_f`.

The genuinely new content here is the variable-stepsize FISTA recursion, together with the B3
stepsize rule along the extrapolated sequence and the two admissible stepsize regimes. The public
API therefore reuses the existing owner abstractions and adds only the general state update and
the B3 rule itself, rather than introducing a second FISTA wrapper package or a parallel B3
acceptance layer. -/

/-- One accelerated prox-gradient state update driven by the extrapolated point attached to
`state`: it advances `xCur` to `T_(L)(fista_extrapolated_point state)`, shifts the current
iterate into `xPrev`, and updates the momentum parameter. This matches the constant-stepsize
update from Algorithm 10.13 and remains a useful bridge owner for later accelerated variants. -/
def fista_state_update
    (f : E → ℝ) (g : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (L : PosReal) (state : FISTAState E) :
    FISTAState E :=
  let tNext := fista_momentum_update state.tCur
  let y := fista_extrapolated_point state
  { xPrev := state.xCur
    xCur := T[L; f, g] y
    tCur := tNext }

-- Proof sketch: both definitions use the same extrapolated point `y` and the same momentum
-- update `tNext`; after unfolding, the two record expressions coincide field by field.
/-- When the curvature parameter is fixed to `L_f`, the general FISTA state update agrees with the
constant-stepsize FISTA update from Algorithm 10.13. -/
theorem fista_state_update_eq_constant_stepsize_state_update
    (f : E → ℝ) (g : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (Lf : PosReal) (state : FISTAState E) :
    fista_state_update f g Lf state =
      fista_constant_stepsize_state_update f g Lf state := by
  -- Unfold both updates: they are the same record built from the same `y` and `tNext`.
  rfl

/-- The internal recursive pair implementing Algorithm 10.6 faithfully: the first component is the
FISTA state `(x^(k-1), x^k, t_k)`, and the second component is the textbook extrapolated point
`y^k` used to form `x^(k+1)`. -/
private def fista_state_and_y
    (f : E → ℝ) (g : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (x0 : E) (L : ℕ → PosReal) :
    ℕ → FISTAState E × E
  | 0 => (fista_initial_state x0, x0)
  | k + 1 =>
      let (state, yk) := fista_state_and_y f g x0 L k
      let tNext := fista_momentum_update state.tCur
      let xNext := T[L k; f, g] yk
      let nextState : FISTAState E :=
        { xPrev := state.xCur
          xCur := xNext
          tCur := tNext }
      let yNext := xNext + ((state.tCur - 1) / tNext) • (xNext - state.xCur)
      (nextState, yNext)

/-- For a real-valued smooth term `f`, a proper closed convex regularizer `g`,
an initial point `x^0 = x0`, and positive curvature estimates `L_k`, the FISTA recursion is the
state sequence whose companion internal recursion stores both the state `(x^(k-1), x^k, t_k)` and
the textbook extrapolated point `y^k`, starts from `(x^0, x^0, 1)` with `y^0 = x^0`, and then
evolves by the source formulas
`x^(k+1) = T_(L_k)(y^k)`, `t_(k+1) = (1 + √(1 + 4 t_k^2)) / 2`, and
`y^(k+1) = x^(k+1) + ((t_k - 1) / t_(k+1)) (x^(k+1) - x^k)`. -/
def fista
    (f : E → ℝ) (g : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (x0 : E) (L : ℕ → PosReal) :
    ℕ → FISTAState E :=
  fun k ↦ (fista_state_and_y f g x0 L k).1

/-- The FISTA iterate `x^k`, namely the current iterate field of the `k`-th FISTA state. -/
def fista_x
    (f : E → ℝ) (g : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (x0 : E) (L : ℕ → PosReal) (k : ℕ) : E :=
  (fista f g x0 L k).xCur

/-- The FISTA momentum parameter `t_k`, namely the momentum field of the `k`-th FISTA state. -/
def fista_t
    (f : E → ℝ) (g : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (x0 : E) (L : ℕ → PosReal) (k : ℕ) : ℝ :=
  (fista f g x0 L k).tCur

/-- The FISTA extrapolated point `y^k` from the companion source-faithful recursion. -/
def fista_y
    (f : E → ℝ) (g : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (x0 : E) (L : ℕ → PosReal) (k : ℕ) : E :=
  (fista_state_and_y f g x0 L k).2

-- Proof sketch: unfold `fista` at the base index `0`; the initial state's current iterate is
-- definitionally `x0`.
/-- FISTA starts from the initial iterate `x^0 = x0`. -/
@[simp] theorem fista_x_zero
    (f : E → ℝ) (g : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (x0 : E) (L : ℕ → PosReal) :
    fista_x f g x0 L 0 = x0 := by
  -- Evaluate the recursion at `0` and read off the initial state's current iterate.
  rfl

-- Proof sketch: unfold `fista` at the base index `0`; the initial state's momentum field is
-- definitionally `1`.
/-- The initial FISTA momentum parameter is `t_0 = 1`. -/
@[simp] theorem fista_t_zero
    (f : E → ℝ) (g : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (x0 : E) (L : ℕ → PosReal) :
    fista_t f g x0 L 0 = 1 := by
  -- Evaluate the recursion at `0` and read off the initial momentum field.
  rfl

-- Proof sketch: at the initial state one has `x^{-1} = x^0 = x0` and `t_0 = 1`, so the
-- extrapolation coefficient vanishes and the extrapolated point reduces to `x0`.
/-- The initial FISTA extrapolated point satisfies `y^0 = x^0 = x0`. -/
@[simp] theorem fista_y_zero
    (f : E → ℝ) (g : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (x0 : E) (L : ℕ → PosReal) :
    fista_y f g x0 L 0 = x0 := by
  -- The companion recursion stores `y^0 = x0` in its second component.
  rfl

-- Proof sketch: unfold `fista` at `k + 1`; by definition, the current iterate field of the
-- updated state is the prox-gradient point `T_(L_k)(y^k)`.
/-- Each FISTA successor iterate satisfies
`x^(k+1) = T_(L_k)(y^k)`. -/
theorem fista_x_succ
    (f : E → ℝ) (g : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (x0 : E) (L : ℕ → PosReal) (k : ℕ) :
    fista_x f g x0 L (k + 1) =
      T[L k; f, g] (fista_y f g x0 L k) := by
  -- Unfold the successor clause of the recursion: `x^(k+1)` is the stored prox-gradient point.
  rfl

-- Proof sketch: unfold `fista` at `k + 1`; the updated state's momentum field is
-- `fista_momentum_update t_k` by definition.
/-- The FISTA momentum sequence satisfies
`t_(k+1) = (1 + √(1 + 4 t_k^2)) / 2`. -/
theorem fista_t_succ
    (f : E → ℝ) (g : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (x0 : E) (L : ℕ → PosReal) (k : ℕ) :
    fista_t f g x0 L (k + 1) =
      fista_momentum_update (fista_t f g x0 L k) := by
  -- Unfold the successor clause of the recursion: the new momentum is `fista_momentum_update t_k`.
  rfl

-- Proof sketch: unfold the companion internal recursion at `k + 1`; the stored extrapolated point
-- is definitionally the textbook formula built from `x^(k+1)`, `x^k`, `t_k`, and `t_(k+1)`.
/-- The FISTA extrapolated sequence satisfies
`y^(k+1) = x^(k+1) + ((t_k - 1) / t_(k+1)) (x^(k+1) - x^k)`. -/
theorem fista_y_succ
    (f : E → ℝ) (g : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (x0 : E) (L : ℕ → PosReal) (k : ℕ) :
    fista_y f g x0 L (k + 1) =
      fista_x f g x0 L (k + 1) +
        ((fista_t f g x0 L k - 1) / fista_t f g x0 L (k + 1)) •
          (fista_x f g x0 L (k + 1) - fista_x f g x0 L k) := by
  -- Unfold the stored `yNext` field and rewrite it through the public `x` and `t` views.
  rfl

/-- The canonical B2 upper-model acceptance predicate for `f.toEReal` at the bridge point
`interior_effective_domain_point_of_real f y` is exactly the displayed FISTA upper-model
inequality `(10.39)` at `y`. -/
theorem proximal_gradient_backtracking_B2_accepts_iff_fista_upper_model
    (f : E → ℝ) (g : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)] (L : PosReal) (y : E) :
    proximal_gradient_backtracking_B2_accepts
      f.toEReal g L (interior_effective_domain_point_of_real f y) ↔
  let xNext := T[L; f, g] y
  f xNext ≤
    f y +
      inner ℝ (∇ f y) (xNext - y) +
      ((L : ℝ) / 2) * ‖xNext - y‖ ^ (2 : ℕ) := by
  constructor
  · intro haccepts
    -- Expand the canonical B2 predicate at the real base point and drop the `EReal` coercions.
    have haccepts' :=
      (proximal_gradient_backtracking_B2_accepts_iff
        f.toEReal g L (interior_effective_domain_point_of_real f y)).1 haccepts
    exact EReal.coe_le_coe_iff.mp <| by
      simpa [prox_gradient_operator_apply, Function.toEReal, add_assoc] using haccepts'
  · intro hmodel
    -- Repackage the displayed real inequality as the Chapter 10 B2 acceptance predicate.
    refine
      (proximal_gradient_backtracking_B2_accepts_iff
        f.toEReal g L (interior_effective_domain_point_of_real f y)).2 ?_
    exact EReal.coe_le_coe_iff.mpr <| by
      simpa [prox_gradient_operator_apply, Function.toEReal, add_assoc] using hmodel

/-- A stepsize schedule uses backtracking procedure B3 along a point sequence `y` when, at every
iteration `k`, the accepted curvature estimate `L_k` is the first accepted geometric trial based
on `s` at `k = 0` and on `L_(k-1)` at later steps, evaluated at the point `y^k`. -/
def uses_backtracking_procedure_B3_rule
    (f : E → ℝ) (g : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (y : ℕ → E) (L : ℕ → PosReal) (s : PosReal)
    (η : ProximalGradientBacktrackingGrowthFactor) : Prop :=
  ∀ k : ℕ, ∃ i : ℕ,
    is_backtracking_procedure_B2_index
      f.toEReal g
      (proximal_gradient_backtracking_B2_previous_stepsize s L k) η
      (interior_effective_domain_point_of_real f (y k)) i ∧
    L k =
      proximal_gradient_backtracking_trial_stepsize
        (proximal_gradient_backtracking_B2_previous_stepsize s L k) η i

-- Proof sketch: specialize `uses_backtracking_procedure_B3_rule` at the iteration `k`; the chosen
-- index `i` is accepted by `is_backtracking_procedure_B2_index_accepts` for the canonical
-- Chapter 10 B2 owner applied to `f.toEReal` at `interior_effective_domain_point_of_real f (y k)`.
-- The bridge theorem
-- `proximal_gradient_backtracking_B2_accepts_iff_fista_upper_model` then rewrites this canonical
-- acceptance predicate as the displayed FISTA upper-model inequality.
/-- Under backtracking procedure B3, the chosen stepsize `L_k` satisfies the displayed
quadratic upper-model inequality `(10.39)` at the point `y^k`. -/
theorem uses_backtracking_procedure_B3_rule_accepts
    {f : E → ℝ} {g : E → EReal} [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)] {y : ℕ → E} {L : ℕ → PosReal}
    {s : PosReal} {η : ProximalGradientBacktrackingGrowthFactor}
    (hrule : uses_backtracking_procedure_B3_rule f g y L s η)
    (k : ℕ) :
    let xNext := T[L k; f, g] (y k)
    f xNext ≤
      f (y k) +
        inner ℝ (∇ f (y k)) (xNext - y k) +
        ((L k : ℝ) / 2) * ‖xNext - y k‖ ^ (2 : ℕ) := by
  rcases hrule k with ⟨i, hi, hLk⟩
  -- The chosen backtracking index is accepted for the corresponding geometric trial.
  rw [hLk]
  exact
    (proximal_gradient_backtracking_B2_accepts_iff_fista_upper_model
      f g
      (proximal_gradient_backtracking_trial_stepsize
        (proximal_gradient_backtracking_B2_previous_stepsize s L k) η i)
      (y k)).1
      (is_backtracking_procedure_B2_index_accepts hi)

/-- The constant/B3 stepsize rule in the fast proximal-gradient analysis: either every
`L_k = L_f`, giving `α = 1`, or the schedule is produced by backtracking procedure B3 along the
point sequence `y`, with `α = max {η, s / L_f}`. The B3 branch records `0 < L_f` explicitly so
the quotient `s / L_f` remains faithful to the textbook constant rather than Lean's
division-by-zero convention. -/
def fast_proximal_gradient_sublinear_rate_stepsize_rule
    (f : E → ℝ) (g : E → EReal) (Lf : NNReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (y : ℕ → E) (L : ℕ → PosReal) (α : ℝ) : Prop :=
  (α = 1 ∧ uses_proximal_gradient_Lf_stepsize_rule Lf L) ∨
    0 < (Lf : ℝ) ∧ ∃ s : PosReal, ∃ η : ProximalGradientBacktrackingGrowthFactor,
      α = max (η : ℝ) ((s : ℝ) / (Lf : ℝ)) ∧
        uses_backtracking_procedure_B3_rule f g y L s η

-- Proof sketch: in the constant branch, `L_0 = L_f` and `L_0` is positive because it is a
-- `PosReal`. In the B3 branch, the required positivity witness is stored explicitly in the rule.
/-- The shared fast proximal-gradient stepsize rule forces the smoothness constant `L_f` to be
positive. -/
theorem fast_proximal_gradient_sublinear_rate_stepsize_rule_lf_pos
    (f : E → ℝ) (g : E → EReal) (Lf : NNReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    {y : ℕ → E} {L : ℕ → PosReal} {α : ℝ}
    (hrule : fast_proximal_gradient_sublinear_rate_stepsize_rule f g Lf y L α) :
    0 < (Lf : ℝ) := by
  rcases hrule with ⟨_, hLf_rule⟩ | ⟨hLf_pos, _, _, _, _⟩
  · -- The exact constant rule already forces `L_f` to be positive.
    exact uses_proximal_gradient_Lf_stepsize_rule_lf_pos hLf_rule
  · -- The B3 branch records the required positivity explicitly.
    exact hLf_pos

-- Proof sketch: in the constant-rule case, use the global `L_f`-smoothness inequality at `y^k`
-- and specialize `uses_proximal_gradient_Lf_stepsize_rule Lf L` at `k`. In the
-- backtracking case, the conclusion is exactly
-- `uses_backtracking_procedure_B3_rule_accepts hrule k`.
/-- If the curvature estimates are chosen either by the constant rule `L_k = L_f` or by
backtracking procedure B3 encoded by
`fast_proximal_gradient_sublinear_rate_stepsize_rule`, then the quadratic upper-model inequality
`(10.39)` holds at every point `y^k`. -/
theorem fast_proximal_gradient_sublinear_rate_stepsize_rule_accepts
    (f : E → ℝ) (g : E → EReal) (Lf : NNReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (hf_smooth : is_l_smooth_on f Set.univ Lf)
    {α : ℝ}
    {y : ℕ → E} {L : ℕ → PosReal}
    (hrule : fast_proximal_gradient_sublinear_rate_stepsize_rule f g Lf y L α)
    (k : ℕ) :
    let xNext := T[L k; f, g] (y k)
    f xNext ≤
      f (y k) +
        inner ℝ (∇ f (y k)) (xNext - y k) +
        ((L k : ℝ) / 2) * ‖xNext - y k‖ ^ (2 : ℕ) := by
  rcases hrule with ⟨_, hLf_rule⟩ | ⟨_, s, η, _, hB3⟩
  · let LfPos : PosReal := hLf_rule.stepsize
    have hLk : L k = LfPos := by
      apply Subtype.ext
      exact hLf_rule k
    -- The constant branch is the global smoothness descent lemma at the point `y^k`.
    have hdescent :
        let xNext := T[LfPos; f, g] (y k)
        f xNext ≤
          f (y k) +
            inner ℝ (∇ f (y k)) (xNext - y k) +
            ((LfPos : ℝ) / 2) * ‖xNext - y k‖ ^ (2 : ℕ) := by
      simpa [LfPos, PosReal.coe_toNNReal, norm_sub_rev] using
        (is_l_smooth_on_univ_descent_lemma hf_smooth (y k) (T[LfPos; f, g] (y k)))
    -- Rewriting `L k` to the constant stepsize closes the displayed inequality.
    simpa [hLk] using hdescent
  · -- The B3 branch is exactly the accepted-trial bridge proved above.
    exact uses_backtracking_procedure_B3_rule_accepts hB3 k

variable {f : E → ℝ} {g : E → EReal}
variable {XStar : Set E} {FOpt : ℝ} {Lf : NNReal}

namespace IsFastProximalGradientProblem

variable [hproblem : IsFastProximalGradientProblem f g XStar FOpt Lf]

/-- Helper for Algorithm 10.6: under Assumption 10.31, the prox-gradient point `T[L; f, g] y`
can be formed using the canonical `g`-regularity data supplied by `hproblem`. -/
abbrev proxPoint
    (hproblem : IsFastProximalGradientProblem f g XStar FOpt Lf)
    (L : PosReal) (y : E) : E :=
  @prox_gradient_operator E _ _ _ f g
    hproblem.g_proper ⟨hproblem.g_closed⟩ ⟨hproblem.g_convex⟩ L y

/-- Bridge/view layer: Assumption 10.31 canonically supplies the `g`-regularity data required by
the shared constant/B3 sublinear-rate stepsize owner from Algorithm 10.6. -/
abbrev SublinearRateStepsizeRule
    (hproblem : IsFastProximalGradientProblem f g XStar FOpt Lf)
    (y : ℕ → E) (L : ℕ → PosReal) (α : ℝ) : Prop :=
  @fast_proximal_gradient_sublinear_rate_stepsize_rule E _ _ _ f g Lf
    hproblem.g_proper ⟨hproblem.g_closed⟩ ⟨hproblem.g_convex⟩ y L α

/-- The canonical fast-problem bridge owner `SublinearRateStepsizeRule` already includes
positivity of the smoothness constant `L_f`. -/
theorem sublinearRateStepsizeRule_lf_pos
    {y : ℕ → E} {L : ℕ → PosReal} {α : ℝ}
    (hrule : hproblem.SublinearRateStepsizeRule y L α) :
    0 < (Lf : ℝ) := by
  -- Local instance justification (defeq pin): the explicit fast-problem witness `hproblem`
  -- canonically fixes the properness instance for `g`, so the shared owner theorem elaborates
  -- through the same regularity data without changing the public theorem surface.
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  -- Local instance justification (defeq pin): the explicit fast-problem witness `hproblem`
  -- canonically fixes the lower-semicontinuity witness for `g`, so the shared owner theorem
  -- uses the same closedness data as the fast-problem assumptions.
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  -- Local instance justification (defeq pin): the explicit fast-problem witness `hproblem`
  -- canonically fixes the convexity witness for `g`, so the shared owner theorem reuses the
  -- source-facing regularity package verbatim.
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  -- Reduce to the shared owner theorem, now elaborated through the local `hproblem` instances.
  simpa [SublinearRateStepsizeRule] using
    (fast_proximal_gradient_sublinear_rate_stepsize_rule_lf_pos f g Lf hrule)

/-- Algorithm 10.6: under Assumption 10.31, the owner-level fast stepsize
bridge supplies the FISTA upper-model inequality `(10.39)` at every point `y^k`. -/
theorem sublinearRateStepsizeRule_accepts
    {α : ℝ} {y : ℕ → E} {L : ℕ → PosReal}
    (hrule : hproblem.SublinearRateStepsizeRule y L α)
    (k : ℕ) :
    let xNext := hproblem.proxPoint (L k) (y k)
    f xNext ≤
      f (y k) +
        inner ℝ (∇ f (y k)) (xNext - y k) +
        ((L k : ℝ) / 2) * ‖xNext - y k‖ ^ (2 : ℕ) := by
  -- Local instance justification (defeq pin): the explicit fast-problem witness `hproblem`
  -- canonically fixes the properness instance for `g`, so the shared owner theorem elaborates
  -- through the same regularity data without changing the public theorem surface.
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  -- Local instance justification (defeq pin): the explicit fast-problem witness `hproblem`
  -- canonically fixes the lower-semicontinuity witness for `g`, so the shared owner theorem
  -- uses the same closedness data as the fast-problem assumptions.
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  -- Local instance justification (defeq pin): the explicit fast-problem witness `hproblem`
  -- canonically fixes the convexity witness for `g`, so the shared owner theorem reuses the
  -- source-facing regularity package verbatim.
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  -- Route correction: use the shared owner theorem directly, then unfold only the bridge views.
  simpa [SublinearRateStepsizeRule, proxPoint] using
    (fast_proximal_gradient_sublinear_rate_stepsize_rule_accepts
      f g Lf hproblem.f_smooth hrule k)

end IsFastProximalGradientProblem

end
