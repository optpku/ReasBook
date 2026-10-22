/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped Topology
open Filter

section

variable {E : Type u} [AddCommMonoid E] [Module ℝ E]

/- Definition 3.8 is `source-facing` in the chapter directional-derivative API. Its
`core/canonical` owner abstractions are the right-hand filter `𝓝[>] (0 : ℝ)`, convergence
`Tendsto`, and the canonical right-limit operator `limUnder`. The bridge/view theorem below is
just the generic Hausdorff uniqueness statement for `limUnder`, specialized to the directional
difference quotient. -/

/-- A directional derivative of `f` at `x` in the direction `d` exists with value `ℓ` when the
directional difference quotients converge to `ℓ` as `α → 0⁺`. -/
def has_directional_derivative_at (f : E → EReal) (x d : E) (ℓ : EReal) : Prop :=
  Tendsto (fun α : ℝ ↦ (f (x + α • d) - f x) / (α : EReal)) (𝓝[>] (0 : ℝ)) (𝓝 ℓ)

/-- Definition 3.8: the directional derivative of an extended-real-valued function at `x` in the
direction `d` is the right-hand limit of the difference quotient
`α ↦ (f (x + α • d) - f x) / α`. The book introduces this at interior points of the effective
domain of a proper function. -/
noncomputable def directional_derivative (f : E → EReal) (x d : E) : EReal :=
  limUnder (𝓝[>] (0 : ℝ)) (fun α : ℝ ↦ (f (x + α • d) - f x) / (α : EReal))

-- Proof sketch: if the difference quotient tends to `ℓ` along `𝓝[>] 0`, then Hausdorff
-- uniqueness of limits identifies `limUnder` with that same value.
/-- If the directional difference quotients converge to `ℓ` as `α → 0⁺`, then the directional
derivative is equal to `ℓ`. -/
theorem directional_derivative_eq_of_has_directional_derivative_at
    {f : E → EReal} {x d : E} {ℓ : EReal}
    (h : has_directional_derivative_at f x d ℓ) :
    directional_derivative f x d = ℓ := by
  simpa [directional_derivative] using h.limUnder_eq

end
