/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/- Definition 1.40: the identity transformation on a real vector space `E` is the canonical real
linear endomorphism `LinearMap.id : E →ₗ[ℝ] E`. -/
recall LinearMap.id

/- The defining pointwise relation `𝓘(x) = x` is the canonical theorem `LinearMap.id_apply`. -/
recall LinearMap.id_apply

end
