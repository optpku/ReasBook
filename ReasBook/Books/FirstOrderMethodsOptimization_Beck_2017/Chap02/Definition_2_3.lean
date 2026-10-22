/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {α : Type u}

/- Definition 2.3: the project records the textbook notion of lower semicontinuity at a point via
the canonical mathlib owner declaration `LowerSemicontinuousAt`. -/
recall LowerSemicontinuousAt

/- The global notion of lower semicontinuity is the canonical pointwise owner statement
`lowerSemicontinuous_iff`. -/
recall lowerSemicontinuous_iff

/- The liminf formulation used by the textbook is the canonical complete-linear-order
characterization `lowerSemicontinuousAt_iff_le_liminf`. -/
recall lowerSemicontinuousAt_iff_le_liminf

section

variable {f : α → EReal} {a : ℝ} {x : α}

/- The textbook real level-set notation is canonically the preimage `f ⁻¹' Iic (a : EReal)`. -/
#check (f ⁻¹' Set.Iic (a : EReal))

/- Membership in that real sublevel set is definitionally the inequality `f x ≤ a`. -/
#check (show x ∈ f ⁻¹' Set.Iic (a : EReal) ↔ f x ≤ (a : EReal) from Iff.rfl)

end
