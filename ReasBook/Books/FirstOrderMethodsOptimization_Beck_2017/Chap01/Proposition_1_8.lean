/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Proposition 1.8 is recall-only: the textbook statement that the Euclidean norm is self-dual is
exactly the specialization of the owner theorem `LinearIsometryEquiv.norm_map` to the canonical
Fréchet-Riesz equivalence `InnerProductSpace.toDual ℝ E : E ≃ₗᵢ⋆[ℝ] StrongDual ℝ E`, whose
canonical hypothesis is completeness of the inner-product space. -/
#check (InnerProductSpace.toDual ℝ E).norm_map

end
