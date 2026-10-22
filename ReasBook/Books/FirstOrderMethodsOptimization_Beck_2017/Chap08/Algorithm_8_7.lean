/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_12

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Algorithm 8.7 is `source-facing` in the convex-feasibility API. The canonical owner for each
projection step is the chapter map `metricProjection`. Since the initialization lies in `S₂` and
every full iteration ends with a projection onto `S₂`, the iterate sequence is most naturally
valued in the subtype `S₂`. -/

/-- Algorithm 8.7: for two nonempty closed convex sets `S₁` and `S₂` and an initial point
`x0 ∈ S₂`, the alternating projection method generates the sequence
`x^{k+1} = P_{S₂}(P_{S₁}(x^k))`. -/
def alternating_projection_method (S₁ S₂ : Set E)
    (hS₁_nonempty : S₁.Nonempty) (hS₁_closed : IsClosed S₁) (hS₁_convex : Convex ℝ S₁)
    (hS₂_nonempty : S₂.Nonempty) (hS₂_closed : IsClosed S₂) (hS₂_convex : Convex ℝ S₂)
    (x0 : S₂) : ℕ → S₂
  | 0 => x0
  | k + 1 =>
      -- The recursive invariant stays subtype-valued in `S₂`, so each full step ends with the
      -- projection onto `S₂` using completeness derived from closedness.
      let xk :=
        alternating_projection_method S₁ S₂ hS₁_nonempty hS₁_closed hS₁_convex
          hS₂_nonempty hS₂_closed hS₂_convex x0 k
      metricProjection S₂ hS₂_nonempty hS₂_closed hS₂_convex
        (metricProjection S₁ hS₁_nonempty hS₁_closed hS₁_convex (xk : E))

section

variable (S₁ S₂ : Set E)
variable (hS₁_nonempty : S₁.Nonempty) (hS₁_closed : IsClosed S₁) (hS₁_convex : Convex ℝ S₁)
variable (hS₂_nonempty : S₂.Nonempty) (hS₂_closed : IsClosed S₂) (hS₂_convex : Convex ℝ S₂)
variable (x0 : S₂)

local notation "x[" k "]" =>
  alternating_projection_method S₁ S₂ hS₁_nonempty hS₁_closed hS₁_convex
    hS₂_nonempty hS₂_closed hS₂_convex x0 k

-- Proof sketch: unfold the recursive definition of `alternating_projection_method` at `0`.
/-- The alternating-projection sequence starts at the prescribed initial point in `S₂`. -/
theorem alternating_projection_method_zero :
    x[0] = x0 := by
  -- The base case is the `0` branch of the recursive definition.
  rfl

-- Proof sketch: unfold the recursive definition of `alternating_projection_method` at `k + 1`.
/-- One step of the alternating projection method applies the metric projection onto `S₁`
followed by the metric projection onto `S₂`. -/
theorem alternating_projection_method_succ (k : ℕ) :
    x[k + 1] =
      metricProjection S₂ hS₂_nonempty hS₂_closed hS₂_convex
        (metricProjection S₁ hS₁_nonempty hS₁_closed hS₁_convex (x[k] : E)) := by
  -- The successor case is exactly the recursive update after the projection API repair.
  rfl

end

end
