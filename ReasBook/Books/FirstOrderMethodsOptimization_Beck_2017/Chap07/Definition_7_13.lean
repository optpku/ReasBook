/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap01.Definition_1_30

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Matrix
open Matrix

noncomputable section

section

variable {n : ℕ}

local notation "𝕊" => symmetricMatrices n

/-- Definition 7.13: the Schatten `1`-norm on the symmetric matrix space `𝕊^n` is the sum of the
absolute values of the ordered eigenvalues of the matrix. -/
noncomputable def symmetric_schatten_one_norm (X : 𝕊) : ℝ :=
  let hX := X.property.isHermitian
  ∑ i, |hX.eigenvalues i|

-- Proof sketch: unfold `symmetric_schatten_one_norm`; its defining `let` names the Hermitian
-- structure carried by `X`, after which the statement is the displayed finite sum of absolute
-- eigenvalues.
/-- The defining formula for `symmetric_schatten_one_norm` is the sum of the absolute values of the
ordered eigenvalues of the symmetric matrix. -/
@[simp] theorem symmetric_schatten_one_norm_def (X : 𝕊) :
    symmetric_schatten_one_norm X = (let hX := X.property.isHermitian; ∑ i, |hX.eigenvalues i|) :=
  by
    -- Unfolding the definition produces exactly the displayed formula.
    rfl

notation "‖" X "‖ₛ₁" => symmetric_schatten_one_norm X

-- Proof sketch: this is the defining formula with the auxiliary Hermitian structure written
-- directly as `X.property.isHermitian` instead of via the local `let`-binding.
/-- The Schatten `1`-norm of a symmetric matrix is the sum of the absolute values of the ordered
eigenvalues of its canonical Hermitian representative. -/
@[simp] theorem symmetric_schatten_one_norm_apply (X : 𝕊) :
    symmetric_schatten_one_norm X = ∑ i, |X.property.isHermitian.eigenvalues i| := by
  -- Collapse the defining `let`-binding to the canonical Hermitian structure of `X`.
  simp [symmetric_schatten_one_norm]

-- Proof sketch: rewrite the notation `‖X‖ₛ₁` as `symmetric_schatten_one_norm X` and unfold the
-- definition to identify the resulting finite sum with the ordered Hermitian eigenvalue list.
/-- The Schatten `1`-norm of a symmetric matrix is the sum of the absolute values of its ordered
eigenvalues. -/
@[simp] theorem symmetric_schatten_one_norm_eq_sum_abs_eigenvalues (X : 𝕊) :
    ‖X‖ₛ₁ = (let hX := X.property.isHermitian; ∑ i, |hX.eigenvalues i|) := by
  -- The notation `‖X‖ₛ₁` is just the defining function applied to `X`.
  exact symmetric_schatten_one_norm_def X

-- Proof sketch: rewrite `‖X‖ₛ₁` using `symmetric_schatten_one_norm_apply`; each summand is
-- nonnegative because it is an absolute value, and the finite sum of nonnegative real numbers is
-- nonnegative.
/-- The Schatten `1`-norm of a symmetric matrix is nonnegative. -/
theorem symmetric_schatten_one_norm_nonneg (X : 𝕊) :
    0 ≤ ‖X‖ₛ₁ := by
  -- Rewrite the norm as a finite sum of absolute values.
  rw [symmetric_schatten_one_norm_apply]
  -- Each term is nonnegative, so the full finite sum is nonnegative.
  exact Finset.sum_nonneg fun i _ => abs_nonneg _

end
