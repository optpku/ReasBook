/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap14.Lemma_14_4.InactiveBlockSupport

noncomputable section

universe u

open scoped Gradient

section

variable {E1 : Type u} {E2 : Type u}
variable [NormedAddCommGroup E1] [NormedAddCommGroup E2]
variable [InnerProductSpace ℝ E1] [ProperSpace E1]
variable [InnerProductSpace ℝ E2] [ProperSpace E2]

variable (f : E1 × E2 → ℝ) (g1 : E1 → EReal) (g2 : E2 → EReal)
variable (x1 : ℕ → E1) (x2 : ℕ → E2) (k : ℕ)

local notation "F" => two_block_alternating_minimization_objective f.toEReal g1 g2
local notation "xk" => (x1 k, x2 k)
local notation "xHalf" => two_block_alternating_minimization_half_step x1 x2 k
local notation "xNext" => (x1 (k + 1), x2 (k + 1))
local notation "f1" => fun y1 ↦ f (y1, x2 k)
local notation "f2" => fun y2 ↦ f (x1 (k + 1), y2)

/- Lemma 14.4: for a two-block alternating-minimization trajectory, the half-step and next-step
objective gaps are controlled by the corresponding block gradient mappings on the frozen slices
`y₁ ↦ f (y₁, x₂ᵏ)` and `y₂ ↦ f (x₁ᵏ⁺¹, y₂)`, provided `f` is jointly convex and the initial pair
lies in `effective_domain F`. -/
theorem two_block_alternating_minimization_objective_gap_le_gradient_mapping
    (L1 L2 : PosReal)
    [IsProperExtendedRealFunction g1]
    [Fact (LowerSemicontinuous g1)]
    [Fact (is_convex_function g1)]
    [IsProperExtendedRealFunction g2]
    [Fact (LowerSemicontinuous g2)]
    [Fact (is_convex_function g2)]
    (htraj : is_two_block_alternating_minimization_trajectory f.toEReal g1 g2 x1 x2)
    (hx0 : (x1 0, x2 0) ∈ effective_domain F)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_x1_smooth : is_l_smooth_on f1 Set.univ (PosReal.toNNReal L1))
    (hf_x2_smooth : is_l_smooth_on f2 Set.univ (PosReal.toNNReal L2))
    (xStar : E1 × E2)
    (hxStar : IsMinOn F Set.univ xStar) :
    F xHalf - F xStar ≤ (((‖G[L1; f1, g1] (x1 k)‖ * ‖xk - xStar‖ : ℝ) : EReal)) ∧
      F xNext - F xStar ≤ (((‖G[L2; f2, g2] (x2 k)‖ * ‖xHalf - xStar‖ : ℝ) : EReal)) := by
  constructor
  · exact
      two_block_half_step_objective_gap_le_x1_gradient_mapping
        f g1 g2 x1 x2 k L1 htraj hx0 hf_convex hf_x1_smooth xStar hxStar
  · exact
      two_block_next_iterate_objective_gap_le_x2_gradient_mapping
        f g1 g2 x1 x2 k L2 htraj hx0 hf_convex hf_x2_smooth xStar hxStar

end
