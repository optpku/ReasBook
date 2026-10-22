/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap09.Definition_9_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {g ω : E → EReal} {σ : ℝ}

/- Definition 9.5 is a `source-facing` specialization in the Chapter 9 mirror-descent API. The
`core/canonical` owner remains `IsBregmanPotentialOn`, but the textbook statement is not the bare
owner itself: it is the composite-model specialization obtained by instantiating the constraint set
to `dom(g) = effective_domain g`. The main entry should therefore present that specialized type
expression directly, rather than recalling the unspecialized owner name alone. -/

/- Definition 9.5: in the composite model, the standing assumptions on the mirror map `ω` are
exactly that `ω` is a Bregman potential on `dom(g) = effective_domain g` with modulus `σ`. -/
#check (IsBregmanPotentialOn ω (effective_domain g) σ)

end
