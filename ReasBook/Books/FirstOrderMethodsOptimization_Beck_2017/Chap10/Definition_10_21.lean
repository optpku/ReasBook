/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/- Definition 10.21 is `source-facing`: the primitive data are the smoothness constant `L_f` and
the positive strong-convexity modulus `σ`. The chapter owner for their ratio is the condition
number itself; notation and elementary positivity facts are derived API. When `L_f` is itself
positive, Chapter 6 already provides the canonical bridge `Lf.toNNReal : NNReal`, so downstream
files should reuse `κ(Lf.toNNReal, σ)` rather than rebuilding that bridge through
`Real.toNNReal (Lf : ℝ)`. -/

/-- Definition 10.21: the condition number attached to the smoothness constant `L_f` and the
positive strong-convexity modulus `σ` is the ratio `L_f / σ`. -/
def condition_number (Lf : NNReal) (σ : PosReal) : ℝ :=
  (Lf : ℝ) / (σ : ℝ)

notation "κ(" Lf ", " σ ")" => condition_number Lf σ

-- Proof sketch: this is just the defining formula of `condition_number`.
/-- Expanding `condition_number` yields the ratio `L_f / σ`. -/
@[simp] theorem condition_number_eq (Lf : NNReal) (σ : PosReal) :
    κ(Lf, σ) = (Lf : ℝ) / (σ : ℝ) :=
  rfl

-- Proof sketch: unfold `condition_number`; the numerator `(Lf : ℝ)` is nonnegative because
-- `Lf : NNReal`, and division by the positive modulus `σ` preserves nonnegativity.
/-- The condition number is nonnegative. -/
theorem condition_number_nonneg (Lf : NNReal) (σ : PosReal) :
    0 ≤ κ(Lf, σ) := by
  exact div_nonneg Lf.2 (le_of_lt σ.2)

end
