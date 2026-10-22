/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Filter
open scoped Topology

section

variable {E : Type u} [AddCommMonoid E] [Module ℝ E]

/- Definition 8.3 is `source-facing` at the standard right-limit owner data
`Tendsto (𝓝[>] 0)`. In this item-file setting the notion is stated directly in those canonical
terms, rather than through an extra wrapper around auxiliary data. -/

/-- Definition 8.3: a nonzero vector `d` is a descent direction of `f` at `x` when the
directional derivative of `f` at `x` along `d` exists and is strictly negative. -/
def is_descent_direction_at (f : E → EReal) (x d : E) : Prop :=
  d ≠ 0 ∧
    ∃ ℓ : EReal,
      Tendsto (fun α : ℝ ↦ (f (x + α • d) - f x) / (α : EReal)) (𝓝[>] (0 : ℝ)) (𝓝 ℓ) ∧
        ℓ < 0

-- Proof sketch: unfold `is_descent_direction_at`; the statement is exactly the defining
-- right-limit characterization of a descent direction.
/-- A descent direction is equivalently a nonzero direction admitting a negative right-limit for
the directional difference quotient. -/
theorem is_descent_direction_at_iff
    {f : E → EReal} {x d : E} :
    is_descent_direction_at f x d ↔
      d ≠ 0 ∧
        ∃ ℓ : EReal,
          Tendsto (fun α : ℝ ↦ (f (x + α • d) - f x) / (α : EReal)) (𝓝[>] (0 : ℝ)) (𝓝 ℓ) ∧
            ℓ < 0 := by
  -- Unfold the definition once; the theorem states exactly the defining condition.
  rfl

end
