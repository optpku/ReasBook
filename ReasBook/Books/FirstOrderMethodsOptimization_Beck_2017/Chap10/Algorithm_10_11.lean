/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap10.Algorithm_10_13
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Assumption_10_31
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

/- Algorithm 10.11 is `source-facing` in the chapter's fast proximal-gradient API.

Domain sampling:
- `T[...]` from Definition 10.9 is the canonical owner for the prox-gradient point
  `z^k = T_(L_k)(y^k)` attached to a real-valued smooth term and an extended-real-valued
  regularizer;
- `fista_momentum_sequence` and `fista_momentum_update` from Algorithm 10.13 are already the
  local owners for the textbook momentum recursion
  `t_0 = 1`, `t_(k+1) = (1 + √(1 + 4 t_k^2)) / 2`;
- `FISTAState` and `fista_extrapolated_point` from Algorithm 10.13 are the chapter's canonical
  affine owners for generic FISTA state data, so any extra MFISTA owner here should record only
  the genuinely new source content beyond that generic state layer;
- `composite_model_objective` from Definition 10.2 is the chapter owner for the composite value
  `F = f + g`, and the project already uses the bridge `f.toEReal` for real-valued smooth terms.

The genuinely new source content is the monotone MFISTA trajectory relation on the explicit
sequences `(x^k, y^k, z^k, L_k)`: after forming the prox-gradient point `z^k`, the source keeps
the monotonicity clause only as the displayed objective inequality
`F (x^(k+1)) ≤ min (F (z^k)) (F (x^k))`, together with the canonical FISTA momentum recursion and
the MFISTA extrapolation formula. Because this step is noncanonical, the faithful public API is a
trajectory predicate on those sequences, reusing `fista_momentum_sequence` rather than adding a
second public momentum owner or a chosen iterate package.

Primitive data are exactly the `g`-side regularity assumptions needed to form the prox-gradient
point `T_(L_k)(y^k)`. The `f`-side convexity and `L_f`-smoothness hypotheses from Assumption
10.31(A)-(B) are mathematically ambient standing assumptions for the later rate theorems, not
primitive fields of the trajectory relation itself, so they belong in the fast-problem bridge
below rather than in the core owner header. -/

/-- Algorithm 10.11: sequences `(x^k, y^k, z^k, L_k)` form an MFISTA trajectory for `f` and `g`
when `y 0 = x 0`, each `z k` is the prox-gradient point `T[L k; f, g] (y k)`, the monotonicity
clause is stated exactly by the displayed inequality
`composite_model_objective f.toEReal g (x (k + 1)) ≤
  min (composite_model_objective f.toEReal g (z k))
    (composite_model_objective f.toEReal g (x k))`,
and `y (k + 1)` is given by the MFISTA extrapolation formula using the canonical Chapter 10
momentum sequence `fista_momentum_sequence`. Under Assumption 10.31, the bridge
`IsFastProximalGradientProblem.IsMfistaTrajectory` recovers the standing regularity assumptions on
`f` and `g`. -/
class is_mfista_trajectory
    (f : E → ℝ) (g : E → EReal)
    [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (x y z : ℕ → E) (L : ℕ → PosReal) : Prop where
  /-- The MFISTA initialization clause is `y 0 = x 0`. -/
  init : y 0 = x 0
  /-- At each iteration `k`, MFISTA records the prox-gradient point, the source monotonicity
  inequality, and the extrapolated next search point. -/
  step : ∀ k : ℕ,
    z k = T[L k; f, g] (y k) ∧
      composite_model_objective f.toEReal g (x (k + 1)) ≤
        min (composite_model_objective f.toEReal g (z k))
          (composite_model_objective f.toEReal g (x k)) ∧
      y (k + 1) =
        x (k + 1) +
          (fista_momentum_sequence k / fista_momentum_sequence (k + 1)) •
            (z k - x (k + 1)) +
          ((fista_momentum_sequence k - 1) / fista_momentum_sequence (k + 1)) •
            (x (k + 1) - x k)

section

variable {f : E → ℝ} {g : E → EReal}
variable [IsProperExtendedRealFunction g]
variable [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
variable {x y z : ℕ → E} {L : ℕ → PosReal}

namespace is_mfista_trajectory

/-- Coercion from an MFISTA trajectory to its per-iteration step data. -/
instance instCoeFun :
    CoeFun
      (is_mfista_trajectory f g x y z L)
      (fun _ ↦
        ∀ k : ℕ,
          z k = T[L k; f, g] (y k) ∧
            composite_model_objective f.toEReal g (x (k + 1)) ≤
              min (composite_model_objective f.toEReal g (z k))
                (composite_model_objective f.toEReal g (x k)) ∧
            y (k + 1) =
              x (k + 1) +
                (fista_momentum_sequence k / fista_momentum_sequence (k + 1)) •
                  (z k - x (k + 1)) +
                ((fista_momentum_sequence k - 1) / fista_momentum_sequence (k + 1)) •
                  (x (k + 1) - x k)) where
  coe htraj := htraj.step

/-- Along an MFISTA trajectory, the initialization clause is `y 0 = x 0`. -/
theorem y_zero
    (htraj : is_mfista_trajectory f g x y z L) :
    y 0 = x 0 := by
  -- The initialization clause is stored directly in the trajectory owner.
  exact htraj.init

/-- Along an MFISTA trajectory, `z k` is the canonical prox-gradient point `T[L k; f, g] (y k)`.
-/
theorem z_eq
    (htraj : is_mfista_trajectory f g x y z L) (k : ℕ) :
    z k = T[L k; f, g] (y k) := by
  -- The first component of the per-step data is the prox-gradient identity.
  exact (htraj k).1

/-- Along an MFISTA trajectory, the source monotonicity clause holds exactly in the displayed
objective form. -/
theorem x_next_objective_le_min
    (htraj : is_mfista_trajectory f g x y z L) (k : ℕ) :
    composite_model_objective f.toEReal g (x (k + 1)) ≤
      min (composite_model_objective f.toEReal g (z k))
        (composite_model_objective f.toEReal g (x k)) := by
  -- The second component of the per-step data is the monotonicity inequality.
  exact (htraj k).2.1

/-- Along an MFISTA trajectory, `y (k + 1)` is given by the MFISTA extrapolation formula. -/
theorem y_succ
    (htraj : is_mfista_trajectory f g x y z L) (k : ℕ) :
    y (k + 1) =
      x (k + 1) +
        (fista_momentum_sequence k / fista_momentum_sequence (k + 1)) •
          (z k - x (k + 1)) +
        ((fista_momentum_sequence k - 1) / fista_momentum_sequence (k + 1)) •
          (x (k + 1) - x k) := by
  -- The final component of the per-step data is the MFISTA extrapolation rule.
  exact (htraj k).2.2

end is_mfista_trajectory

/-- An MFISTA trajectory is equivalent to the four defining clauses of Algorithm 10.11. -/
theorem is_mfista_trajectory_iff :
    is_mfista_trajectory f g x y z L ↔
      y 0 = x 0 ∧
        (∀ k : ℕ, z k = T[L k; f, g] (y k)) ∧
        (∀ k : ℕ,
          composite_model_objective f.toEReal g (x (k + 1)) ≤
            min (composite_model_objective f.toEReal g (z k))
              (composite_model_objective f.toEReal g (x k))) ∧
        (∀ k : ℕ,
          y (k + 1) =
            x (k + 1) +
              (fista_momentum_sequence k / fista_momentum_sequence (k + 1)) •
                (z k - x (k + 1)) +
              ((fista_momentum_sequence k - 1) / fista_momentum_sequence (k + 1)) •
                (x (k + 1) - x k)) := by
  constructor
  · intro htraj
    -- Read the owner through its public companion projections.
    refine ⟨is_mfista_trajectory.y_zero htraj, ?_, ?_, ?_⟩
    · intro k
      -- Each prox-gradient point is recovered from the step projection.
      exact is_mfista_trajectory.z_eq htraj k
    · intro k
      -- The displayed monotonicity clause is recovered from the same step data.
      exact is_mfista_trajectory.x_next_objective_le_min htraj k
    · intro k
      -- The extrapolated search point is the third component of the step data.
      exact is_mfista_trajectory.y_succ htraj k
  · rintro ⟨hy0, hz, hobj, hy⟩
    -- Repackage the four textbook clauses into the owner fields.
    refine ⟨hy0, ?_⟩
    intro k
    exact ⟨hz k, hobj k, hy k⟩

/-- In Algorithm 10.11, the chosen MFISTA iterate has objective no larger than the
prox-gradient point `z k`. -/
theorem is_mfista_trajectory_x_next_objective_le_prox
    (htraj : is_mfista_trajectory f g x y z L) (k : ℕ) :
    composite_model_objective f.toEReal g (x (k + 1)) ≤
      composite_model_objective f.toEReal g (z k) := by
  -- Project the `min` bound to its left branch.
  exact le_trans (is_mfista_trajectory.x_next_objective_le_min htraj k) (min_le_left _ _)

/-- In Algorithm 10.11, the chosen MFISTA iterate has objective no larger than the previous
iterate `x k`. -/
theorem is_mfista_trajectory_x_next_objective_le_current
    (htraj : is_mfista_trajectory f g x y z L) (k : ℕ) :
    composite_model_objective f.toEReal g (x (k + 1)) ≤
      composite_model_objective f.toEReal g (x k) := by
  -- Project the same `min` bound to the current-iterate branch.
  exact le_trans (is_mfista_trajectory.x_next_objective_le_min htraj k) (min_le_right _ _)

end

namespace IsFastProximalGradientProblem

variable {f : E → ℝ} {g : E → EReal} {XStar : Set E} {FOpt : ℝ} {Lf : NNReal}

/-- Bridge/view layer: Assumption 10.31 canonically supplies the standing hypotheses required by
the owner-level MFISTA trajectory predicate from Algorithm 10.11. -/
abbrev IsMfistaTrajectory
    (hproblem : IsFastProximalGradientProblem f g XStar FOpt Lf)
    (x y z : ℕ → E) (L : ℕ → PosReal) : Prop :=
  @is_mfista_trajectory E _ _ _ f g
    (instIsProperExtendedRealFunctionRightOfIsFastProximalGradientProblem hproblem)
    (instFactLowerSemicontinuousRightOfIsFastProximalGradientProblem hproblem)
    (instFactIsConvexFunctionRightOfIsFastProximalGradientProblem hproblem)
    x y z L

end IsFastProximalGradientProblem

end
