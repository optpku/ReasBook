/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Example_6_59

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

noncomputable section

section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Definition 10.54 is `bridge/view` in Chapter 10's smoothing discussion. Domain sampling in the
Moreau-envelope/Huber API gives:
- `M[μ, f]` from Definition 6.7 as the canonical Moreau-envelope owner;
- `H[μ]` from Definition 6.8 as the scalar Huber owner;
- `moreau_envelope_l1_sum_toReal_eq_sum_huber` from Example 6.59 as the owner-level real-valued
  `ℓ¹` bridge.

The Chapter 10 item adds no new primitive data beyond the Euclidean specialization
`E = EuclideanSpace ℝ (Fin n)`, so the main entry here should be direct reuse of that Chapter 6
bridge rather than a parallel local reproving theorem. -/

/- Definition 10.54: for `h(x) = ‖x‖₁` on `ℝ^n` and any `μ > 0`, the real-valued Moreau envelope
of `h` is the sum of the scalar Huber values on the coordinates:
`M_h^μ(x) = ∑ i, H_μ(x_i)`. -/
#check
  (moreau_envelope_l1_sum_toReal_eq_sum_huber :
    ∀ μ : PosReal,
      ∀ x : E, (M[μ, fun y : E ↦ (‖y‖₁ : EReal)] x).toReal = ∑ i, H[μ] (x i))

end
