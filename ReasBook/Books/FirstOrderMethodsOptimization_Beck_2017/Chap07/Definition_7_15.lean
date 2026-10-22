/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix

noncomputable section

section

variable {m n : ℕ}

/- Definition 7.15 is `source-facing`: the textbook introduces the finite vector of singular
values of a real `m × n` matrix. The `core/canonical` owner in mathlib is
`LinearMap.singularValues` for the Euclidean linear map `X.toEuclideanLin`, and the source-facing
vector is obtained by restricting that ordered sequence to the first `min m n` entries. -/

/-- Definition 7.15: the singular values function sends a real `m × n` matrix to the vector in
`ℝ^(min m n)` whose entries are the singular values of the matrix in weakly decreasing order. -/
noncomputable def singular_value_function (X : Matrix (Fin m) (Fin n) ℝ) : Fin (min m n) → ℝ :=
  fun i ↦ X.toEuclideanLin.singularValues i

-- Proof sketch: unfold `singular_value_function`; evaluation at `i` is definitionally the `i`-th
-- entry of the ordered singular-value sequence of the Euclidean linear map associated to `X`.
/-- Evaluating `singular_value_function X` at `i` returns the `i`-th singular value of the
Euclidean linear map associated to `X`. -/
@[simp] theorem singular_value_function_apply (X : Matrix (Fin m) (Fin n) ℝ)
    (i : Fin (min m n)) :
    singular_value_function X i = X.toEuclideanLin.singularValues i := by
  -- This is the defining evaluation rule for the source-facing wrapper.
  rfl

-- Proof sketch: the canonical singular-value sequence of `X.toEuclideanLin` is antitone on `ℕ`;
-- restricting it along `Fin.val : Fin (min m n) → ℕ` preserves weak decrease on the finite index
-- set `Fin (min m n)`.
/-- The coordinates of `singular_value_function X` are weakly decreasing along the natural order on
`Fin (min m n)`. -/
theorem singular_value_function_antitone (X : Matrix (Fin m) (Fin n) ℝ) :
    Antitone (singular_value_function X) := by
  intro i j hij
  -- Restrict the canonical antitone singular-value sequence on `ℕ` along `Fin.val`.
  simpa [singular_value_function_apply] using
    X.toEuclideanLin.singularValues_antitone (show (i : ℕ) ≤ (j : ℕ) from hij)

-- Proof sketch: each singular value of `X.toEuclideanLin` is nonnegative in mathlib, and
-- `singular_value_function X` is obtained by evaluating that sequence on `Fin (min m n)`.
/-- Every coordinate of `singular_value_function X` is nonnegative. -/
theorem singular_value_function_nonneg (X : Matrix (Fin m) (Fin n) ℝ)
    (i : Fin (min m n)) :
    0 ≤ singular_value_function X i := by
  -- Each entry comes from mathlib's nonnegative singular-value sequence.
  simpa [singular_value_function_apply] using X.toEuclideanLin.singularValues_nonneg (i : ℕ)

end
