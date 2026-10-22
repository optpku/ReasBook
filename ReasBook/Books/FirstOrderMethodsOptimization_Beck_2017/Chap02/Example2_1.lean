/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_2
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_2
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {E : Type u}

/-
Example 2.1: this item is a canonical recall of the chapter owners for indicator functions,
their effective domains, real epigraphs, and proper extended-real-valued functions. -/
recall extendedIndicator

/- The finite-value locus is the canonical owner `effective_domain`, and the textbook identity
`dom(δ_C) = C` is already recorded by `effective_domain_extendedIndicator`. -/
recall effective_domain
recall effective_domain_extendedIndicator
recall mem_effective_domain_extendedIndicator

/- The real-epigraph owner for extended-real-valued functions is the chapter declaration
`realEpigraph`. -/
recall realEpigraph
recall mem_realEpigraph

-- Proof sketch: unfold the displayed real-epigraph set and `effective_domain`; if `f x ≤ y` with
-- `y : ℝ`, then
-- `(y : EReal) < ⊤`, so transitivity gives `f x < ⊤`.
/-- A point in the real epigraph projects to a point in the effective domain. -/
theorem mem_effective_domain_of_mem_realEpigraph {f : E → EReal} {x : E} {y : ℝ}
    (h : (x, y) ∈ realEpigraph f) : x ∈ effective_domain f := by
  -- Semantic recall: `EReal.coe_lt_top` is the canonical finite-value bridge for real heights.
  rw [mem_effective_domain]
  exact lt_of_le_of_lt (mem_realEpigraph.mp h) (EReal.coe_lt_top y)

/- Proper extended-real-valued functions are already owned upstream in Definition 2.5. -/
recall IsProperExtendedRealFunction
