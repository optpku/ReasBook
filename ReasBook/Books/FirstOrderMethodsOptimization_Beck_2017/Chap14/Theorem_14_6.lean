/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_6
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Assumption_10_31

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

/- The source-facing Assumption 14.10 owner below keeps only the live API used by downstream
results. Earlier local proof drafts are intentionally excluded from this item file. -/

section

variable {p : ℕ} {Ei : Fin p → Type u}
variable [∀ i, NormedAddCommGroup (Ei i)] [∀ i, NormedSpace ℝ (Ei i)]

/-- Theorem 14.6 (Assumption 14.10). For the general `p`-block alternating-minimization problem,
`(A)` each block penalty `g_i : E_i → (-∞, ∞]` is proper, closed, and convex; `(B)` the smooth
term `f : E → ℝ` is convex and globally `L_f`-smooth; `(C)` for every `α > 0` there exists
`Rα > 0` such that every `x` with `F x ≤ α` and every optimal point `xStar ∈ XStar = X^*`
satisfy `‖x - xStar‖ ≤ Rα`, where `F(x) = f(x) + ∑ i, g_i(x_i)`; and `(D)` `XStar` is the
nonempty optimal set and `FOpt = F_opt` is the optimal value. The Chapter 10 composite smooth
owners for `f.toEReal` are recovered canonically from the inherited Chapter 10 fast
proximal-gradient owner rather than stored as duplicate primitive data. -/
class IsAlternatingMinimizationConvexRateProblem
    (f : ((i : Fin p) → Ei i) → ℝ) (g : ∀ i : Fin p, Ei i → EReal)
    (XStar : outParam (Set ((i : Fin p) → Ei i))) (FOpt : outParam ℝ)
    (Lf : outParam NNReal) : Prop
    extends IsFastProximalGradientProblem f (separableSum g) XStar FOpt Lf where
  bounded_sublevel_distance_to_each_optimal_point (α : PosReal) :
    ∃ Rα : PosReal, ∀ {x xStar : (i : Fin p) → Ei i},
      composite_model_objective f.toEReal (separableSum g) x ≤ ((α : ℝ) : EReal) →
      xStar ∈ XStar →
      ‖x - xStar‖ ≤ (Rα : ℝ)

namespace IsAlternatingMinimizationConvexRateProblem

open Metric

variable {f : ((i : Fin p) → Ei i) → ℝ} {g : ∀ i : Fin p, Ei i → EReal}
variable {XStar : Set ((i : Fin p) → Ei i)} {FOpt : ℝ} {Lf : NNReal}

local notation "F" => composite_model_objective f.toEReal (separableSum g)

/-- Assumption 14.10 canonically induces the Chapter 10 composite smooth minimization owner for
the aggregate regularizer `x ↦ ∑ i, g_i(x_i)`. -/
theorem toIsCompositeSmoothMinimizationProblem
    (h : IsAlternatingMinimizationConvexRateProblem f g XStar FOpt Lf) :
    IsCompositeSmoothMinimizationProblem f.toEReal (separableSum g) XStar FOpt Lf :=
  h.toIsFastProximalGradientProblem.toIsCompositeSmoothMinimizationProblem

/-- Assumption 14.10 canonically provides the Chapter 10 composite smooth minimization owner for
`f.toEReal` and `separableSum g` by typeclass inference. -/
instance instIsCompositeSmoothMinimizationProblemOfIsAlternatingMinimizationConvexRateProblem
    [h : IsAlternatingMinimizationConvexRateProblem f g XStar FOpt Lf] :
    IsCompositeSmoothMinimizationProblem f.toEReal (separableSum g) XStar FOpt Lf :=
  h.toIsCompositeSmoothMinimizationProblem

/-- Assumption 14.10 canonically induces the Chapter 10 convex composite smooth minimization owner
for the aggregate regularizer `x ↦ ∑ i, g_i(x_i)`. -/
theorem toIsConvexCompositeSmoothMinimizationProblem
    (h : IsAlternatingMinimizationConvexRateProblem f g XStar FOpt Lf) :
    IsConvexCompositeSmoothMinimizationProblem f.toEReal (separableSum g) XStar FOpt Lf :=
  h.toIsFastProximalGradientProblem.toIsConvexCompositeSmoothMinimizationProblem

/-- Assumption 14.10 canonically provides the Chapter 10 convex composite smooth minimization
owner for `f.toEReal` and `separableSum g` by typeclass inference. -/
instance instIsConvexCompositeSmoothMinimizationProblemOfIsAlternatingMinimizationConvexRateProblem
    [h : IsAlternatingMinimizationConvexRateProblem f g XStar FOpt Lf] :
    IsConvexCompositeSmoothMinimizationProblem f.toEReal (separableSum g) XStar FOpt Lf :=
  h.toIsConvexCompositeSmoothMinimizationProblem

/-- The source-facing pairwise sublevel-radius bound in Assumption 14.10 implies the weaker
distance-to-optimal-set estimate on the same composite objective. -/
theorem bounded_sublevel_distance_to_optimal_set
    (h : IsAlternatingMinimizationConvexRateProblem f g XStar FOpt Lf)
    (α : PosReal) :
    ∃ Rα : PosReal,
      ∀ ⦃x : (i : Fin p) → Ei i⦄, F x ≤ ((α : ℝ) : EReal) → infDist x XStar ≤ Rα := by
  -- Reuse the source-facing pairwise radius by comparing with one optimal point.
  rcases h.bounded_sublevel_distance_to_each_optimal_point α with ⟨Rα, hRα⟩
  refine ⟨Rα, ?_⟩
  intro x hx
  rcases h.optimal_set_nonempty with ⟨xStar, hxStar⟩
  refine (infDist_le_dist_of_mem hxStar).trans ?_
  simpa [dist_eq_norm] using hRα hx hxStar

/-- The source-facing pairwise sublevel-radius clause in Assumption 14.10 yields a radius that
controls the whole initial sublevel set `{y | F y ≤ F x0}`. -/
theorem bounded_initial_sublevel_distance_to_each_optimal_point
    (h : IsAlternatingMinimizationConvexRateProblem f g XStar FOpt Lf)
    {x0 : (i : Fin p) → Ei i} {α : PosReal}
    (hx0 : F x0 ≤ ((α : ℝ) : EReal)) :
    ∃ Rα : PosReal,
      ∀ {x xStar : (i : Fin p) → Ei i},
        F x ≤ F x0 →
        xStar ∈ XStar →
        ‖x - xStar‖ ≤ (Rα : ℝ) := by
  -- Any point below `F x0` is also below the positive level `α`.
  rcases h.bounded_sublevel_distance_to_each_optimal_point α with ⟨Rα, hRα⟩
  refine ⟨Rα, ?_⟩
  intro x xStar hx hxStar
  exact hRα (hx.trans hx0) hxStar

/-- If the initial objective value is bounded by a positive level `α`, then the same Assumption
14.10 radius controls the whole initial sublevel set in the weaker distance-to-optimal-set form
used by the rate analysis. -/
theorem bounded_initial_sublevel_distance_to_optimal_set
    (h : IsAlternatingMinimizationConvexRateProblem f g XStar FOpt Lf)
    {x0 : (i : Fin p) → Ei i} {α : PosReal}
    (hx0 : F x0 ≤ ((α : ℝ) : EReal)) :
    ∃ Rα : PosReal,
      ∀ ⦃x : (i : Fin p) → Ei i⦄, F x ≤ F x0 → infDist x XStar ≤ Rα := by
  rcases h.bounded_initial_sublevel_distance_to_each_optimal_point hx0 with ⟨Rα, hRα⟩
  refine ⟨Rα, ?_⟩
  intro x hx
  rcases h.optimal_set_nonempty with ⟨xStar, hxStar⟩
  refine (infDist_le_dist_of_mem hxStar).trans ?_
  simpa [dist_eq_norm] using hRα hx hxStar

end IsAlternatingMinimizationConvexRateProblem

end
