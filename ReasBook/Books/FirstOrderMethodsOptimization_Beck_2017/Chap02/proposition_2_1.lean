/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_2
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_2

-- Declarations for this item will be appended below by the statement pipeline.

open Set

universe u

/- Source-facing geometric description: the real epigraph of `δ_C` is exactly `C ×ˢ Ici 0`. -/
/-- The real epigraph of the extended-real-valued indicator function is `C ×ˢ Ici 0`. -/
theorem extendedIndicator_real_epigraph_eq {α : Type u} (C : Set α) :
    realEpigraph (δ_ C) = C ×ˢ Ici (0 : ℝ) := by
  ext p
  by_cases hp : p.1 ∈ C <;> simp [realEpigraph, extendedIndicator, hp]

section

variable {α : Type u} [TopologicalSpace α]

-- Bridge/view layer: transport the canonical lower-semicontinuity criterion for `δ_C`
-- through the chapter equivalence between lower semicontinuity and closed real epigraph.
/-- Proposition 2.1: the indicator function `δ_C` has closed real epigraph if and only if its
underlying set `C` is closed. -/
theorem extendedIndicator_isClosed_real_epigraph_iff_isClosed (C : Set α) :
    IsClosed (realEpigraph (δ_ C)) ↔ IsClosed C := by
  rw [← lowerSemicontinuous_iff_isClosed_real_epigraph,
    extendedIndicator_lowerSemicontinuous_iff_isClosed]

end
