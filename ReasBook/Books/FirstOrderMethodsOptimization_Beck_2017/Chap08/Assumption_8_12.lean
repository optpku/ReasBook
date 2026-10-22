/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Assumption 8.12 is `source-facing`: the textbook assumes one uniform constant controlling the
norms of all subgradients on the feasible set `C`. Domain sampling against Chapter 3 shows that
the canonical owner for norm-bounded subgradients is the continuous-dual bridge
`strongDualSubdifferential f x`, not a separate wrapper around chosen Euclidean selections. The
public API therefore packages one chosen bound together with its positivity and the pointwise norm
estimate on that owner set. -/

/-- Assumption 8.12: a subgradient norm bound on `f` over `C` consists of a constant `L_f > 0`
such that every continuous-dual subgradient of `f` at every point of `C` has norm at most
`L_f`. -/
structure SubgradientNormBoundOn (f : E → EReal) (C : Set E) where
  L_f : ℝ
  L_f_pos : 0 < L_f
  norm_le {x : E} {g : StrongDual ℝ E}
      (hx : x ∈ C) (hg : g ∈ strongDualSubdifferential f x) : ‖g‖ ≤ L_f

/-- A subgradient norm bound is canonically used as its underlying bound constant `L_f`. -/
instance {f : E → EReal} {C : Set E} : CoeOut (SubgradientNormBoundOn f C) ℝ where
  coe h := h.L_f

end
