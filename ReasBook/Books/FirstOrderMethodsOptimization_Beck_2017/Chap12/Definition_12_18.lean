/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Definition_12_17
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_7
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Definition_12_15

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open Metric
open scoped BigOperators

section

variable {E : Type u}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Definition 12.18 is `source-facing`: it adds the bounded-distance hypothesis for positive
superlevel sets of the block dual objective from Definition 12.17.

Domain sampling against the surrounding project points to:
- `IsDualBlockProximalGradientProblem` from Definition 12.15 as the ambient standing-assumptions
  owner;
- `dual_block_proximal_gradient_dual_objective` from Definition 12.17 as the source-facing block
  dual objective owner; and
- `dual_block_proximal_gradient_dual_optimal_set` from Definition 12.17 as the canonical owner
  for the optimal dual set `Λ*`.

The right public API is therefore the canonical optimal-set owner together with the source-facing
bounded-superlevel assumption class extending the existing Chapter 12 problem data. -/

namespace DualBlockProximalGradient

/-- A positive real `R` is a radius for the `α`-superlevel set of the block dual objective when
every point of that superlevel set is within Euclidean product distance `R` of every optimal dual
point. -/
def IsSuperlevelRadius
    {p : ℕ} (f : E → EReal) (g : Fin p → E → EReal) (α R : PosReal) : Prop :=
  ∀ (y yStar : PiLp (2 : ENNReal) (fun _ : Fin p ↦ E))
    (_ : ((α : ℝ) : EReal) ≤ q(f, g) y.ofLp)
    (_ : yStar.ofLp ∈ Λ*(f, g)),
    ‖y - yStar‖ ≤ (R : ℝ)

end DualBlockProximalGradient

/-- Definition 12.18 is `source-facing`: under Assumption 12.14, the block dual optimal set `Λ*`
is nonempty and, for every `α > 0`, every dual point `y` with `q(y) ≥ α` lies within a uniformly
bounded Euclidean product distance of every optimal dual solution `y* ∈ Λ*`, where
`q(y) = -f*(∑ i, y_i) - ∑ i, g_i*(-y_i)`.

The stronger pairwise bound is primitive source data. The weaker canonical
`infDist y Λ* ≤ Rα` reformulation is derived API below. -/
class IsDualBlockProximalGradientSuperlevelDistanceBoundedProblem
    {p : ℕ} (f : E → EReal) (g : Fin p → E → EReal) (σ : PosReal) : Prop
    extends IsDualBlockProximalGradientProblem f g σ where
  dual_optimal_set_nonempty :
    (Λ*(f, g)).Nonempty
  bounded_dual_superlevel_distance_to_each_optimal_point (α : PosReal) :
    ∃ Rα : PosReal,
      DualBlockProximalGradient.IsSuperlevelRadius f g α Rα

namespace IsDualBlockProximalGradientSuperlevelDistanceBoundedProblem

variable {p : ℕ} {f : E → EReal} {g : Fin p → E → EReal} {σ : PosReal}

/-- The source-facing pairwise superlevel bound from Definition 12.18 implies the weaker canonical
distance-to-optimal-set estimate used downstream. -/
theorem bounded_dual_superlevel_distance_to_optimal_set
    (h : IsDualBlockProximalGradientSuperlevelDistanceBoundedProblem f g σ) (α : PosReal) :
    ∃ Rα : PosReal,
      ∀ (y : PiLp (2 : ENNReal) (fun _ : Fin p ↦ E))
        (_ : ((α : ℝ) : EReal) ≤ q(f, g) y.ofLp),
        infDist y {yStar | yStar.ofLp ∈ Λ*(f, g)} ≤ Rα := by
  rcases h.bounded_dual_superlevel_distance_to_each_optimal_point α with ⟨Rα, hRα⟩
  refine ⟨Rα, ?_⟩
  intro y hy
  rcases h.dual_optimal_set_nonempty with ⟨yStar, hyStar⟩
  let yStarLp : PiLp (2 : ENNReal) (fun _ : Fin p ↦ E) := WithLp.toLp 2 yStar
  have hyStarLp : yStarLp.ofLp ∈ Λ*(f, g) := by
    simpa [yStarLp] using hyStar
  have hyStarLp_mem : yStarLp ∈ {yStar | yStar.ofLp ∈ Λ*(f, g)} := hyStarLp
  refine (Metric.infDist_le_dist_of_mem hyStarLp_mem).trans ?_
  simpa [dist_eq_norm] using hRα y yStarLp hy hyStarLp

end IsDualBlockProximalGradientSuperlevelDistanceBoundedProblem

end
