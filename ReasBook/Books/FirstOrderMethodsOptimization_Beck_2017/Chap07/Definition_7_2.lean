/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 7.2 is recall-only in the Chapter 7 symmetry API. The `core/canonical` owner
abstraction is mathlib's `Function.Even`; the textbook identity `f x = f (-x)` is a thin
`bridge/view` reformulation of that owner, not a second definition. -/
recall Function.Even

/-- Evenness of an extended-real-valued function on `ℝⁿ` is exactly the textbook identity
`f x = f (-x)` for every `x`. -/
theorem function_even_iff_forall_eq_neg {n : ℕ} (f : (Fin n → ℝ) → EReal) :
    Function.Even f ↔ ∀ x, f x = f (-x) := by
  constructor
  · intro hf x
    exact (hf x).symm
  · intro hf x
    simpa using hf (-x)
