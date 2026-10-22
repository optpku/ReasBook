/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Example_6_54

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Definition 10.53 is `bridge/view`. Domain sampling in the local smoothing API gives:
- `H[μ]` from Definition 6.8 as the source-facing owner for the Huber smoothing;
- `M[μ, f]` from Definition 6.7 as the canonical Moreau-envelope owner;
- `moreau_envelope_norm_penalty_toReal_eq_huber_function` from Example 6.54 as the existing
  bridge from the norm envelope to the Huber owner.

The primitive data already live upstream. The only local content is the Euclidean specialization
to `EuclideanSpace ℝ (Fin n)` together with the textbook reading of `x ↦ ‖x‖` as `norm_penalty 1`.
The explicit piecewise formula is therefore derived API via `huber_function_apply`, and the
Chapter 10 item itself is only the Euclidean specialization of the existing Chapter 6 bridge, so
the main entry here should be direct reuse of that theorem rather than a parallel local alias. -/
recall huber_function

/- Definition 10.53: on `ℝ^n`, the real-valued Moreau envelope of the Euclidean norm agrees
with the canonical Huber function `H[μ]`. This is exactly the Chapter 6 bridge theorem specialized
to `E = EuclideanSpace ℝ (Fin n)`. -/
#check
  (moreau_envelope_norm_penalty_toReal_eq_huber_function :
    ∀ μ : PosReal, EReal.toReal ∘ M[μ, norm_penalty 1] = (H[μ] : E → ℝ))

end
