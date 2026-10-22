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

variable {n : ℕ}

local notation "𝕊" => selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)

/- Definition 7.10 is `source-facing`: the textbook introduces the ordered eigenvalue vector of a
real symmetric matrix. The canonical owner already available in the project is the symmetric-matrix
space `selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)`, and the ordered spectral data is
provided by mathlib's Hermitian eigenvalue enumeration `Matrix.IsHermitian.eigenvalues₀`. -/

/-- Definition 7.10: the eigenvalue function `λ : 𝕊^n → ℝ^n` sends a real symmetric matrix to its
eigenvalues listed in weakly decreasing order. -/
noncomputable def symmetric_eigenvalue_function (X : 𝕊) : Fin n → ℝ :=
  fun i ↦ (X.property.isHermitian).eigenvalues₀ (Fin.cast (Fintype.card_fin n).symm i)

-- Proof sketch: unfold `symmetric_eigenvalue_function`; its `i`-th coordinate is definitionally
-- the `i`-th entry of the ordered Hermitian spectrum of `X`, transported along the canonical
-- equality `Fintype.card (Fin n) = n`.
/-- The `i`-th coordinate of `symmetric_eigenvalue_function X` is the `i`-th ordered eigenvalue of
`X`. -/
@[simp] theorem symmetric_eigenvalue_function_apply (X : 𝕊) (i : Fin n) :
    symmetric_eigenvalue_function X i =
      (X.property.isHermitian).eigenvalues₀ (Fin.cast (Fintype.card_fin n).symm i) := by
  -- Unfolding the definition exposes the canonical reindexing of the ordered Hermitian spectrum.
  rfl

-- Route correction: the ordered monotonicity theorem in mathlib is stated for `eigenvalues₀`, so
-- the proof runs through that canonical enumeration and transports the `Fin` inequality by `cast`.
-- Proof sketch: `symmetric_eigenvalue_function X` is defined using the ordered Hermitian spectrum
-- `eigenvalues₀`, and the canonical `Fin.cast` preserves the index order.
/-- The coordinates of `symmetric_eigenvalue_function X` are weakly decreasing along the natural
order on `Fin n`. -/
theorem symmetric_eigenvalue_function_antitone (X : 𝕊) :
    Antitone (symmetric_eigenvalue_function X) := by
  intro i j hij
  -- Rewrite to the canonical ordered spectrum and then reuse mathlib's antitonicity theorem.
  rw [symmetric_eigenvalue_function_apply, symmetric_eigenvalue_function_apply]
  exact (X.property.isHermitian).eigenvalues₀_antitone (by simpa using hij)

end
