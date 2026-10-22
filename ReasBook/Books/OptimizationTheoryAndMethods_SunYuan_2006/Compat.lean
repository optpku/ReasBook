/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

module

public import Mathlib

@[expose] public section

/-!
Compatibility layer for the small API gap between the Sun--Yuan source snapshot (`v4.31.0`)
and the stable `v4.30.0` revision locked by ReasBook's remote `v4.30.0` branch.
-/

namespace Set

alias insert_sdiff_singleton := insert_diff_singleton
alias mem_sdiff := mem_diff

end Set

namespace Submodule

noncomputable abbrev orthogonalProjectionOnto := @Submodule.orthogonalProjection

alias isCompl_orthogonal := isCompl_orthogonal_of_hasOrthogonalProjection
alias orthogonalProjectionOnto_mem_subspace_eq_self :=
  orthogonalProjection_mem_subspace_eq_self
alias orthogonalProjectionOnto_eq_zero_iff := orthogonalProjection_eq_zero_iff

end Submodule

namespace Matrix

/-- Over the reals, Hermitian matrices are exactly symmetric matrices. -/
theorem isHermitian_iff_isSymm {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} : A.IsHermitian ↔ A.IsSymm := by
  sorry

/-- The bilinear form represented by a matrix is symmetric exactly when its matrix is symmetric. -/
theorem isSymm_toBilin'_iff_isSymm {R n : Type*} [CommSemiring R] [Fintype n]
    [DecidableEq n] {A : Matrix n n R} : A.toBilin'.IsSymm ↔ A.IsSymm := by
  sorry

/-- Coordinate expansion of a row-vector/matrix/vector product. -/
theorem dot_mulVec_eq_sum_sum {R m n : Type*} [CommSemiring R] [Fintype m] [Fintype n]
    (v : m → R) (A : Matrix m n R) (w : n → R) :
    dotProduct v (A.mulVec w) = ∑ i, ∑ j, v i * A i j * w j := by
  simp only [dotProduct, mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ac_rfl

end Matrix

namespace AffineMap

/-- A line map between two points is smooth to every finite or infinite order. -/
theorem contDiff_lineMap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x y : E) (n : WithTop ℕ∞) : ContDiff ℝ n (AffineMap.lineMap x y : ℝ → E) := by
  sorry

end AffineMap
