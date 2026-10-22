/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap11.Definition_11_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open Metric

variable {ι : Type u} [Fintype ι] {Ei : ι → Type v}
variable [∀ i, NormedAddCommGroup (Ei i)] [∀ i, InnerProductSpace ℝ (Ei i)]
variable {Lf : NNReal} {Li : (i : ι) → PosReal}

/-- A radius `Rα` bounds the positive `α`-sublevel of the Chapter 11 composite objective relative
to every optimal point if every `x` with `F x ≤ α` stays within distance at most `Rα` of each
`xStar ∈ XStar`. -/
def SublevelDistanceToEachOptimalPointBound
    (f : ((i : ι) → Ei i) → EReal) (g : (i : ι) → Ei i → EReal)
    (XStar : Set ((i : ι) → Ei i)) (α Rα : PosReal) : Prop :=
  ∀ {x xStar : (i : ι) → Ei i},
    composite_model_objective f (separableSum g) x ≤ ((α : ℝ) : EReal) →
    xStar ∈ XStar →
      ‖x - xStar‖ ≤ (Rα : ℝ)

/- Apply a fixed-radius Chapter 11 pairwise sublevel-distance bound to a point `x` in the
positive `α`-sublevel and an optimal point `xStar ∈ XStar`. -/
omit [∀ i, InnerProductSpace ℝ (Ei i)] in
theorem SublevelDistanceToEachOptimalPointBound.apply
    {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
    {XStar : Set ((i : ι) → Ei i)} {α Rα : PosReal}
    (h : SublevelDistanceToEachOptimalPointBound f g XStar α Rα)
    {x xStar : (i : ι) → Ei i}
    (hx : composite_model_objective f (separableSum g) x ≤ ((α : ℝ) : EReal))
    (hxStar : xStar ∈ XStar) :
    ‖x - xStar‖ ≤ (Rα : ℝ) :=
  h hx hxStar

/- Theorem 11.6 is `source-facing` for the convex-case analysis of the cyclic block proximal
gradient method. Domain sampling in Chapter 11 points to
`BlockProximalGradientAssumptions` as the ambient `core/canonical` owner for the blockwise data.

Accordingly, this item refines that owner by adding exactly the extra source-facing data not
already owned upstream:
1. convexity of the smooth term `f`;
2. the stronger textbook pairwise sublevel estimate `‖x - x*‖ ≤ Rα` for every `x* ∈ X^*`.

The weaker `infDist`-to-`X^*` statement remains derived API, not primitive data. -/

/-- Theorem 11.6: in the convex case of the cyclic block proximal gradient method, the standing
Chapter 11 block proximal-gradient assumptions are supplemented by (A) convexity of the smooth
term `f` and (B) the requirement that every positive sublevel set of the composite objective
`F(x) = f(x) + ∑ i, g_i(x_i)` stays within a uniformly bounded distance of every optimal point
`x* ∈ X^*`: for each `α > 0` there is `Rα > 0` such that `F(x) ≤ α` implies
`‖x - x*‖ ≤ Rα` for all `x* ∈ X^*`. The weaker `infDist` reformulation is derived below as a
bridge theorem, but it is not the primitive source-facing field. -/
class CyclicBlockProximalGradientConvexAssumptions
    (f : ((i : ι) → Ei i) → EReal) (g : (i : ι) → Ei i → EReal)
    (block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i)
    (XStar : Set ((i : ι) → Ei i)) (FOpt : ℝ)
    (Lf : NNReal) (Li : (i : ι) → PosReal) : Prop
    extends BlockProximalGradientAssumptions f g block_gradient XStar FOpt Lf Li where
  f_convex : is_convex_function f
  bounded_sublevel_distance_to_each_optimal_point (α : PosReal) :
    ∃ Rα : PosReal, SublevelDistanceToEachOptimalPointBound f g XStar α Rα

namespace CyclicBlockProximalGradientConvexAssumptions

variable {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
variable {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
variable {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ}

local notation "F" => composite_model_objective f (separableSum g)

/-- The source-facing pairwise sublevel bound in Theorem 11.6 implies the weaker canonical
distance-to-set estimate used in later convergence proofs. -/
theorem bounded_sublevel_distance_to_optimal_set
    (h : CyclicBlockProximalGradientConvexAssumptions f g block_gradient XStar FOpt Lf Li)
    (α : PosReal) :
    ∃ Rα : PosReal,
      ∀ ⦃x : (i : ι) → Ei i⦄,
        F x ≤ ((α : ℝ) : EReal) →
        infDist x XStar ≤ Rα := by
  rcases h.bounded_sublevel_distance_to_each_optimal_point α with ⟨Rα, hRα⟩
  refine ⟨Rα, ?_⟩
  intro x hx
  rcases h.optimal_set_nonempty with ⟨xStar, hxStar⟩
  refine (infDist_le_dist_of_mem hxStar).trans ?_
  simpa [dist_eq_norm] using hRα.apply hx hxStar

/-- If the initial objective value is bounded by a positive level `α`, then the same radius from
Definition 11.6 controls the whole initial sublevel set `{x | F x ≤ F x0}` in the weaker
distance-to-optimal-set form used later in the convergence analysis. -/
theorem bounded_initial_sublevel_distance_to_optimal_set
    (h : CyclicBlockProximalGradientConvexAssumptions f g block_gradient XStar FOpt Lf Li)
    {x0 : (i : ι) → Ei i} {α : PosReal}
    (hx0 : F x0 ≤ ((α : ℝ) : EReal)) :
    ∃ Rα : PosReal,
      ∀ ⦃x : (i : ι) → Ei i⦄,
        F x ≤ F x0 →
        infDist x XStar ≤ Rα := by
  rcases h.bounded_sublevel_distance_to_optimal_set α with ⟨Rα, hRα⟩
  refine ⟨Rα, ?_⟩
  intro x hx
  exact hRα (hx.trans hx0)

end CyclicBlockProximalGradientConvexAssumptions

end
