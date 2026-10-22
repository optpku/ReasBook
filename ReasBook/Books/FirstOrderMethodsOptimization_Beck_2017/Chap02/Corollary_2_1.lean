/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {E : Type u} [TopologicalSpace E]

-- Proof sketch: compose `hf` with the continuous coercion `ℝ → EReal`, then apply
-- `Continuous.lowerSemicontinuous` to the resulting `EReal`-valued function.
/-- Corollary 2.1: a continuous real-valued function is closed, i.e. lower semicontinuous after
viewing it as an `EReal`-valued function. -/
theorem continuous_real_isClosed {f : E → ℝ} (hf : Continuous f) :
    LowerSemicontinuous (fun x ↦ (f x : EReal)) :=
  (continuous_coe_real_ereal.comp hf).lowerSemicontinuous
