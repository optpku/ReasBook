/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Algorithm_2_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Lemma_2_18
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Remark_2_41_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped MaxTypeStep StrongConvexSmooth

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
variable {ι : Type*} [Fintype ι] [Nonempty ι] {μ L : ℝ}

-- Route correction: `Definition_2_38.olean` is currently unavailable, but Algorithm 2.9 only
-- uses the minimax owner data and its affine-approximation bridge. Reconstruct that minimal API
-- here from earlier chapter dependencies so the target file remains dependency-closed.

/-- Local owner for Algorithm 2.9: a smooth minimax problem consists of a nonempty closed convex
feasible set together with finitely many `𝓢^{1,1}_{μ,L}` component functions. -/
structure SmoothMinimaxProblem
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (ι : Type*) [Fintype ι] [Nonempty ι] (μ L : ℝ) where
  /-- The closed convex feasible set `Q`. -/
  feasibleSet : Set E
  /-- The feasible set is nonempty. -/
  feasible_nonempty : feasibleSet.Nonempty
  /-- The feasible set is closed. -/
  feasible_closed : IsClosed feasibleSet
  /-- The feasible set is convex. -/
  feasible_convex : Convex ℝ feasibleSet
  /-- The component family whose maximum defines the minimax objective. -/
  components : ι → E → ℝ
  /-- Each component belongs to the common smooth strongly convex class. -/
  components_mem : ∀ i : ι, components i ∈ 𝓢[μ, L]¹¹

namespace SmoothMinimaxProblem

/-- Local bridge for Algorithm 2.9: the affine approximation is the canonical max-type affine
model attached to the component family at `xBar`. -/
abbrev affineApproximation
    (problem : SmoothMinimaxProblem E ι μ L) (xBar : E) : E → ℝ :=
  maxTypeAffineApproximation problem.components xBar

end SmoothMinimaxProblem

/- Primary domain: exact accelerated minimax recurrences on a proper real inner-product space.

Owner declarations sampled for this refinement:
* `constantStepSchemeII` and `constantStepSchemeIIAlphaNext` in `Algorithm_2_4`, which give the
  chapter's recursive owner pattern and the canonical scalar update for scheme II;
* `ConstantStepSchemeIIMomentumRecurrence` in `Algorithm_2_4`, the upstream owner abstraction for
  the shared `(x_k, y_k, α_k)` momentum data;
* `SmoothMinimaxProblem` in `Definition_2_38`, the owner of the feasible set and component
  family;
* `maxTypeGradientMapping` together with the notation `x_f[...]` in `Remark_2_41_1`, the
  canonical exact minimax step;
* `maxTypeGradientMapping_isMinOn` in `Remark_2_41_1`, the derived minimizer theorem for that
  owner exact step.

Best owner abstraction:
* source-facing: the recursive Algorithm 2.9 trajectory `constantStepSchemeIIMinimax`;
* core/canonical: `ConstantStepSchemeIIMomentumRecurrence`, `constantStepSchemeIIAlphaNext`,
  `SmoothMinimaxProblem`, and `maxTypeGradientMapping`;
* bridge/view: `constantStepSchemeIIMinimaxToMomentumRecurrence` and
  `constantStepSchemeIIMinimaxX_succ_isMinOn`.

Primitive data:
* the smooth minimax problem `problem`;
* the positive step parameter witness `hL : 0 < L`;
* the initial feasible point `x0`;
* the admissible source parameter
  `α₀ ∈ (√q[μ, L], constantStepSchemeIIAlphaUpper q[μ, L]]`.

Derived API:
* the projected sequences `x_k`, `y_k`, and `α_k`;
* the quadratic scalar recurrence and interval facts for `α_k`;
* the bridge to the upstream momentum owner;
* the minimizer statement for the exact max-type step.

Accordingly this file should not keep a parallel wrapper structure of arbitrary sequences. The
public owner is the recursive trajectory itself, while the shared momentum recurrence and the
exact-step minimizer property are derived from that trajectory. -/

section

variable (problem : SmoothMinimaxProblem E ι μ L) (hL : 0 < L)

local notation "qf" => q[μ, L]
local notation "αRange" => Set.Ioc (Real.sqrt qf) (constantStepSchemeIIAlphaUpper qf)
local notation "Q" => problem.feasibleSet
local notation "γL" => (Units.mk0 (Real.toNNReal L) (by positivity) : NNRealˣ)

local instance instLocalChap02_Algorithm_2_91 : Fact (Set.Nonempty Q) := ⟨problem.feasible_nonempty⟩
local instance instLocalChap02_Algorithm_2_92 : Fact (IsClosed Q) := ⟨problem.feasible_closed⟩
local instance instLocalChap02_Algorithm_2_93 : Fact (Convex ℝ Q) := ⟨problem.feasible_convex⟩

/-- The one-step state update of Algorithm 2.9 on triples `(x_k, y_k, α_k)`. -/
noncomputable def constantStepSchemeIIMinimaxStep :
    Q × E × ℝ → Q × E × ℝ :=
  fun state ↦
    let xk := state.1
    let yk := state.2.1
    let alphak := state.2.2
    let alphaNext := constantStepSchemeIIAlphaNext qf alphak
    let xNext : Q :=
      ⟨x_f[Q | problem.components; γL](yk),
        (maxTypeGradientMapping_mem_and_isMinOn_ofFact
          Q
          problem.components
          yk
          γL).1⟩
    let yNext :=
      (xNext : E) +
        ((alphak * (1 - alphak)) / (alphak ^ (2 : ℕ) + alphaNext)) •
          ((xNext : E) - (xk : E))
    (xNext, yNext, alphaNext)

/-- Algorithm 2.9: for a smooth minimax problem, a positive step parameter `L`, an initial
feasible point `x0`, and an admissible source parameter
`α₀ ∈ (√q[μ, L], constantStepSchemeIIAlphaUpper q[μ, L]]`, the recursive minimax trajectory
`(x_k, y_k, α_k)` starts from `(x₀, y₀, α₀) = (x0, x0, α₀)` and applies the canonical exact
max-type step `x_{k+1} = x_f(y_k; L)`, the scheme-II quadratic scalar update for `α_{k+1}`, and
the textbook momentum formula for `y_{k+1}`. -/
noncomputable def constantStepSchemeIIMinimax
    (problem : SmoothMinimaxProblem E ι μ L) (hL : 0 < L)
    (x0 : problem.feasibleSet) (alpha0 : αRange) :
    ℕ → problem.feasibleSet × E × ℝ
  | 0 => (x0, (x0 : E), (alpha0 : ℝ))
  | k + 1 =>
      constantStepSchemeIIMinimaxStep problem hL
        (constantStepSchemeIIMinimax problem hL x0 alpha0 k)

/-- The main iterate sequence `x_k` of the recursive Algorithm 2.9 trajectory. -/
noncomputable def constantStepSchemeIIMinimaxX
    (x0 : problem.feasibleSet) (alpha0 : αRange) :
    ℕ → problem.feasibleSet :=
  fun k ↦ (constantStepSchemeIIMinimax problem hL x0 alpha0 k).1

/-- The extrapolated sequence `y_k` of the recursive Algorithm 2.9 trajectory. -/
noncomputable def constantStepSchemeIIMinimaxY
    (x0 : problem.feasibleSet) (alpha0 : αRange) :
    ℕ → E :=
  fun k ↦ (constantStepSchemeIIMinimax problem hL x0 alpha0 k).2.1

/-- The scalar sequence `α_k` of the recursive Algorithm 2.9 trajectory. -/
noncomputable def constantStepSchemeIIMinimaxAlpha
    (x0 : problem.feasibleSet) (alpha0 : αRange) :
    ℕ → ℝ :=
  fun k ↦ (constantStepSchemeIIMinimax problem hL x0 alpha0 k).2.2

section Trajectory

variable (x0 : problem.feasibleSet)

@[simp] theorem constantStepSchemeIIMinimax_zero
    (alpha0 : αRange) :
    constantStepSchemeIIMinimax problem hL x0 alpha0 0 = (x0, (x0 : E), (alpha0 : ℝ)) :=
  rfl

/-- The recursive Algorithm 2.9 state satisfies the one-step update law. -/
@[simp] theorem constantStepSchemeIIMinimax_succ
    (alpha0 : αRange) (k : ℕ) :
    constantStepSchemeIIMinimax problem hL x0 alpha0 (k + 1) =
      constantStepSchemeIIMinimaxStep
        problem
        hL
        (constantStepSchemeIIMinimax problem hL x0 alpha0 k) :=
  rfl

@[simp] theorem constantStepSchemeIIMinimaxX_zero
    (alpha0 : αRange) :
    constantStepSchemeIIMinimaxX problem hL x0 alpha0 0 = x0 :=
  rfl

@[simp] theorem constantStepSchemeIIMinimaxY_zero
    (alpha0 : αRange) :
    constantStepSchemeIIMinimaxY problem hL x0 alpha0 0 = (x0 : E) :=
  rfl

@[simp] theorem constantStepSchemeIIMinimaxAlpha_zero
    (alpha0 : αRange) :
    constantStepSchemeIIMinimaxAlpha problem hL x0 alpha0 0 = (alpha0 : ℝ) :=
  rfl

/-- The recursively chosen scalar `α_{k+1}` is the positive quadratic root determined by
`α_k`. -/
@[simp] theorem constantStepSchemeIIMinimaxAlpha_succ
    (alpha0 : αRange) (k : ℕ) :
    constantStepSchemeIIMinimaxAlpha problem hL x0 alpha0 (k + 1) =
      constantStepSchemeIIAlphaNext qf (constantStepSchemeIIMinimaxAlpha problem hL x0 alpha0 k) :=
  rfl

/-- The recursive Algorithm 2.9 scalar sequence satisfies the textbook quadratic recurrence. -/
theorem constantStepSchemeIIMinimaxAlpha_succ_equation
    (alpha0 : αRange) (k : ℕ) :
    constantStepSchemeIIMinimaxAlpha problem hL x0 alpha0 (k + 1) ^ (2 : ℕ) =
      (1 - constantStepSchemeIIMinimaxAlpha problem hL x0 alpha0 (k + 1)) *
          constantStepSchemeIIMinimaxAlpha problem hL x0 alpha0 k ^ (2 : ℕ) +
        q[μ, L] * constantStepSchemeIIMinimaxAlpha problem hL x0 alpha0 (k + 1) := by
  simpa [constantStepSchemeIIMinimaxAlpha_succ] using
    constantStepSchemeIIAlphaNext_satisfies_equation
      qf
      (constantStepSchemeIIMinimaxAlpha problem hL x0 alpha0 k)

/-- Under the source-facing Algorithm 2.9 hypotheses, every scalar in the recursive trajectory
lies in `(0, 1)`. -/
theorem constantStepSchemeIIMinimaxAlpha_mem_Ioo
    (alpha0 : αRange) (k : ℕ) :
    constantStepSchemeIIMinimaxAlpha problem hL x0 alpha0 k ∈ Set.Ioo (0 : ℝ) 1 := by
  classical
  let i : ι := Classical.choice ‹Nonempty ι›
  have hcomponent : IsStrongConvexSmoothObjective μ L (problem.components i) := by
    simpa [Set.mem_setOf_eq] using problem.components_mem i
  have hμ : 0 < μ :=
    IsStrongConvexSmoothObjective.mu_pos hcomponent
  have hqf : qf ∈ Set.Ico (0 : ℝ) 1 := by
    exact ⟨(constantStepSchemeII_qf_mem_Ioo μ L hμ hL alpha0.2).1.le,
      (constantStepSchemeII_qf_mem_Ioo μ L hμ hL alpha0.2).2⟩
  induction k with
  | zero =>
      simpa [constantStepSchemeIIMinimaxAlpha_zero] using
        (constantStepSchemeII_alpha_mem_Ioo_of_mem_Ioc alpha0.2 :
          (alpha0 : ℝ) ∈ Set.Ioo (0 : ℝ) 1)
  | succ k hk =>
      simpa [constantStepSchemeIIMinimaxAlpha_succ] using
        constantStepSchemeIIAlphaNext_mem_Ioo hqf hk

/-- Helper for Algorithm 2.9: the scalar recurrence stays in the half-open interval `[0, 1)`. -/
theorem constantStepSchemeIIMinimaxAlpha_mem_Ico
    (alpha0 : αRange) (k : ℕ) :
    constantStepSchemeIIMinimaxAlpha problem hL x0 alpha0 k ∈ Set.Ico (0 : ℝ) 1 := by
  -- Project the stronger open-interval invariant to the closed-left form often used downstream.
  rcases constantStepSchemeIIMinimaxAlpha_mem_Ioo problem hL x0 alpha0 k with ⟨hk0, hk1⟩
  exact ⟨hk0.le, hk1⟩

/-- The recursive Algorithm 2.9 iterates satisfy the textbook exact minimax step
`x_{k+1} = x_f(y_k; L)`. -/
@[simp] theorem constantStepSchemeIIMinimaxX_succ
    (alpha0 : αRange) (k : ℕ) :
    (constantStepSchemeIIMinimaxX problem hL x0 alpha0 (k + 1) : E) =
      x_f[Q | problem.components; γL](constantStepSchemeIIMinimaxY problem hL x0 alpha0 k) := by
  rfl

/-- The recursive Algorithm 2.9 extrapolated points satisfy the textbook momentum update. -/
@[simp] theorem constantStepSchemeIIMinimaxY_succ
    (alpha0 : αRange) (k : ℕ) :
    constantStepSchemeIIMinimaxY problem hL x0 alpha0 (k + 1) =
      (constantStepSchemeIIMinimaxX problem hL x0 alpha0 (k + 1) : E) +
        ((constantStepSchemeIIMinimaxAlpha problem hL x0 alpha0 k *
              (1 - constantStepSchemeIIMinimaxAlpha problem hL x0 alpha0 k)) /
            (constantStepSchemeIIMinimaxAlpha problem hL x0 alpha0 k ^ (2 : ℕ) +
              constantStepSchemeIIMinimaxAlpha problem hL x0 alpha0 (k + 1))) •
          ((constantStepSchemeIIMinimaxX problem hL x0 alpha0 (k + 1) : E) -
            (constantStepSchemeIIMinimaxX problem hL x0 alpha0 k : E)) :=
  rfl

/-- The recursive Algorithm 2.9 trajectory, viewed through the upstream type-II momentum
owner. -/
def constantStepSchemeIIMinimaxToMomentumRecurrence
    (alpha0 : αRange) :
    ConstantStepSchemeIIMomentumRecurrence E problem.feasibleSet qf x0 (alpha0 : ℝ) :=
  { x := constantStepSchemeIIMinimaxX problem hL x0 alpha0
    y := constantStepSchemeIIMinimaxY problem hL x0 alpha0
    alpha := constantStepSchemeIIMinimaxAlpha problem hL x0 alpha0
    x_zero := constantStepSchemeIIMinimaxX_zero problem hL x0 alpha0
    y_zero := constantStepSchemeIIMinimaxY_zero problem hL x0 alpha0
    alpha_zero := constantStepSchemeIIMinimaxAlpha_zero problem hL x0 alpha0
    alpha_succ_equation := fun k ↦
      constantStepSchemeIIMinimaxAlpha_succ_equation problem hL x0 alpha0 k
    y_succ := constantStepSchemeIIMinimaxY_succ problem hL x0 alpha0 }

/-- The exact minimax step in Algorithm 2.9 minimizes the owner regularized affine max-type
model on the feasible set. -/
theorem constantStepSchemeIIMinimaxX_succ_isMinOn
    (alpha0 : αRange) (k : ℕ) :
    IsMinOn
      (quadraticallyRegularizedObjective
        (problem.affineApproximation (constantStepSchemeIIMinimaxY problem hL x0 alpha0 k))
        L
        (constantStepSchemeIIMinimaxY problem hL x0 alpha0 k))
      Q
      (constantStepSchemeIIMinimaxX problem hL x0 alpha0 (k + 1) : E) := by
  simpa [constantStepSchemeIIMinimaxX_succ, SmoothMinimaxProblem.affineApproximation,
    Real.toNNReal_of_nonneg hL.le] using
    (maxTypeGradientMapping_mem_and_isMinOn_ofFact
      Q
      problem.components
      (constantStepSchemeIIMinimaxY problem hL x0 alpha0 k)
      γL).2

end Trajectory

end

end
