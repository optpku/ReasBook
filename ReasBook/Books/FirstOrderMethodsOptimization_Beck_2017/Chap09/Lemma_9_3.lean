/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Definition_9_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Gradient

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {ω : E → EReal} {a b c : E}

/- Lemma 9.3 is `source-facing`: it records the standard three-point identity for the Chapter 9
owner `bregmanDistance` on the mathematically meaningful differentiable domain of the two anchor
points. The Chapter 9 owner on the right is still `bregmanDistance`, while the gradient data on
the left should be supplied through the canonical mathlib owner `HasGradientAt` rather than through
the global totalized surface `∇`. -/

-- Proof sketch: expand the three owner-level Bregman terms `B[ω] c a`, `B[ω] a b`, and
-- `B[ω] c b`, cancel the function values, and use `c - b = (c - a) + (a - b)` to collect the
-- remaining inner products into the canonical gradient difference.
/-- Lemma 9.3: if `ω.toReal` has gradients `ωa` at `a` and `ωb` at `b`, then the associated
three-point identity for the Chapter 9 Bregman distance is
`⟪ωb - ωa, c - a⟫ = B_ω(c, a) + B_ω(a, b) - B_ω(c, b)`. -/
theorem bregman_three_point_identity
    {ωa ωb : E}
    (ha : HasGradientAt (fun x ↦ (ω x).toReal) ωa a)
    (hb : HasGradientAt (fun x ↦ (ω x).toReal) ωb b) :
    inner ℝ (ωb - ωa) (c - a) =
      B[ω] c a + B[ω] a b - B[ω] c b := by
  rw [bregmanDistance_def, bregmanDistance_def, bregmanDistance_def, ha.gradient, hb.gradient]
  have hcb : c - b = (c - a) + (a - b) := by
    abel
  rw [hcb, inner_add_right, inner_sub_left]
  ring

end
