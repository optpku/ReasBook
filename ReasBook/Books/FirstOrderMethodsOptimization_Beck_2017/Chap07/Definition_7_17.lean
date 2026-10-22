/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

namespace Matrix

/-- Definition 7.17: a real `m × n` matrix is generalized diagonal if every entry outside the
main diagonal vanishes. -/
def IsGeneralizedDiag {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∀ i : Fin m, ∀ j : Fin n, (i : ℕ) ≠ (j : ℕ) → X i j = 0

-- Proof sketch: when the matrix is square, `Matrix.IsDiag` is defined by the same off-diagonal
-- vanishing condition. For `Fin n` indices, `i ≠ j` is equivalent to `(i : ℕ) ≠ (j : ℕ)`.
/-- A square real matrix is generalized diagonal exactly when it is diagonal in the standard
mathlib sense. -/
theorem isGeneralizedDiag_iff_isDiag {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) :
    X.IsGeneralizedDiag ↔ X.IsDiag := by
  -- Unfold both predicates so each direction compares the same off-diagonal vanishing condition.
  unfold IsGeneralizedDiag IsDiag
  constructor
  · intro h i j hij
    -- Convert inequality of `Fin` indices into inequality of their natural-number values.
    exact h i j (Fin.val_injective.ne_iff.mpr hij)
  · intro h i j hij
    -- Convert inequality of values back to inequality of `Fin` indices before using `IsDiag`.
    exact h (i := i) (j := j) (Fin.val_injective.ne_iff.mp hij)

end Matrix
