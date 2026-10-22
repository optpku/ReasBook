/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_5
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Assumption 8.38 is `source-facing`: the textbook fixes a finite family of component objectives
for the incremental projected subgradient method and requires one common subgradient bound on the
feasible set `C`. The canonical owners already present in the project are
`IsProperExtendedRealFunction`, `LowerSemicontinuous`, `is_convex_function`, and
`strongDualSubdifferential`, so the public API packages exactly that componentwise convex-analysis
data together with the chosen common bound constant. -/

/-- Assumption 8.38: a finite family of component functions `f i`, indexed by `i = 1, …, m`,
admits a common constant `L > 0` such that (a) each `f i` is proper, closed, and convex, and (b)
every continuous-dual subgradient of every `f i` at every point of `C` has norm at most `L`. -/
structure IncrementalProjectedSubgradientAssumptions {m : ℕ}
    (f : Fin m → E → EReal) (C : Set E) where
  L : ℝ
  L_pos : 0 < L
  proper (i : Fin m) : IsProperExtendedRealFunction (f i)
  closed (i : Fin m) : LowerSemicontinuous (f i)
  convex (i : Fin m) : is_convex_function (f i)
  norm_le {i : Fin m} {x : E} {g : StrongDual ℝ E}
      (hx : x ∈ C) (hg : g ∈ strongDualSubdifferential (f i) x) : ‖g‖ ≤ L

/-- An incremental projected subgradient assumption package is canonically used as its common
bound constant `L`. -/
instance {m : ℕ} {f : Fin m → E → EReal} {C : Set E} :
    CoeOut (IncrementalProjectedSubgradientAssumptions f C) ℝ where
  coe h := h.L

end
