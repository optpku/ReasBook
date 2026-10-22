/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/- Definition 1.32: The set of all `n × n` orthogonal real matrices is represented in mathlib by
`Matrix.orthogonalGroup`; for matrices indexed by `Fin n`, this is `Matrix.orthogonalGroup (Fin n) ℝ`. -/
recall Matrix.orthogonalGroup

/-- Membership in the orthogonal group is equivalent to satisfying both transpose-inverse equations. -/
-- Proof sketch: combine `Matrix.mem_orthogonalGroup_iff` and
-- `Matrix.mem_orthogonalGroup_iff'`, which separately identify membership with the two matrix
-- inverse identities.
theorem mem_orthogonalGroup_iff_mul_transpose_eq_one_and_transpose_mul_eq_one
    {n : Type u} [Fintype n] [DecidableEq n] {R : Type v} [CommRing R] {A : Matrix n n R} :
    A ∈ Matrix.orthogonalGroup n R ↔
      A * A.transpose = 1 ∧ A.transpose * A = 1 := by
  constructor
  · intro hA
    exact ⟨(Matrix.mem_orthogonalGroup_iff n R).1 hA, (Matrix.mem_orthogonalGroup_iff' n R).1 hA⟩
  · rintro ⟨hAA, _⟩
    exact (Matrix.mem_orthogonalGroup_iff n R).2 hAA
