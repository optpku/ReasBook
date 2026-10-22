/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [AddCommGroup E]

/-- Definition 2.8: the infimal convolution of two extended-real-valued functions is the
pointwise infimum of the translates `u ↦ h1 u + h2 (x - u)`. -/
noncomputable def infimal_convolution (h1 h2 : E → EReal) : E → EReal :=
  fun x ↦ ⨅ u : E, h1 u + h2 (x - u)

-- Textbook notation for infimal convolution.
infixl:70 " □ " => infimal_convolution

-- Proof sketch: unfold `infimal_convolution`; the statement is the defining equation of the
-- pointwise infimum over all decompositions `x = u + (x - u)`.
/-- Evaluating the infimal convolution at `x` gives the infimum of `h1 u + h2 (x - u)` over
all `u : E`. -/
lemma infimal_convolution_apply (h1 h2 : E → EReal) (x : E) :
    (h1 □ h2) x = ⨅ u : E, h1 u + h2 (x - u) := rfl

end
