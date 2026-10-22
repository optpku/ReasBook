/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_4_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open scoped RealSymmetricMatrixSpace

section

variable {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "SymmMat" => 𝕊^n

private theorem mem_positiveSemidefiniteCone_iff_dotProduct_nonneg
    (X : SymmMat) :
    X ∈ (𝕊^n₊ : Set SymmMat) ↔ ∀ x : Fin n → ℝ, 0 ≤ x ⬝ᵥ ((X : Mat) *ᵥ x) := by
  rw [mem_positiveSemidefiniteCone_iff, Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · rintro ⟨_, hX⟩
    simpa using hX
  · intro hX
    exact ⟨RealSymmetricMatrixSpace.isHermitian X, by simpa using hX⟩

/- Theorem 5.4.4.1 lies in the chapter's positive-semidefinite symmetric-matrix cone domain.

Sampled owner-style declarations:
- Chapter 5 `𝕊^n` from `Definition_5_4_4_1`, the symmetric-matrix carrier owner;
- Chapter 5 `𝕊^n₊` and `mem_positiveSemidefiniteCone_iff` from `Definition_5_4_4_3`, the
  source-facing cone owner and its canonical membership bridge;
- mathlib `Matrix.PosSemidef`, the core owner predicate for positive semidefiniteness;
- mathlib `Matrix.isPositive_toEuclideanLin_iff`, the quadratic-form bridge for
  positive-semidefinite matrices.

Best owner abstraction:
- source-facing: the cone `𝕊^n₊ : Set (𝕊^n)`;
- core/canonical: `Matrix.PosSemidef`;
- bridge/view: the membership and quadratic-form characterizations already provided upstream in
  `Definition_5_4_4_3`.

Primitive data:
- `n : ℕ`

Derived API:
- the source-facing theorem that `𝕊^n₊` is a closed convex set;
- the companion projection lemmas giving closedness and convexity separately.

This file therefore stays at the theorem layer over the existing cone owner `𝕊^n₊`. It does not
introduce a new set owner or restate matrix positivity as primitive data. The closedness and
convexity statements are kept only as thin projections from the textbook combined conclusion.
-/

/-- The positive-semidefinite cone is closed in the symmetric-matrix space `𝕊^n`. -/
theorem positiveSemidefiniteCone_isClosed (n : ℕ) :
    IsClosed (𝕊^n₊) := by
  rw [show (𝕊^n₊ : Set (𝕊^n)) =
      ⋂ x : Fin n → ℝ,
        {X : 𝕊^n | 0 ≤ x ⬝ᵥ ((X : Matrix (Fin n) (Fin n) ℝ) *ᵥ x)} by
    ext X
    simpa using (mem_positiveSemidefiniteCone_iff_dotProduct_nonneg X)]
  refine isClosed_iInter fun x ↦ ?_
  exact isClosed_le continuous_const <| by fun_prop

/-- The positive-semidefinite cone is convex in the symmetric-matrix space `𝕊^n`. -/
theorem positiveSemidefiniteCone_convex (n : ℕ) :
    Convex ℝ (𝕊^n₊) := by
  intro X hX Y hY a b ha hb hab
  rw [mem_positiveSemidefiniteCone_iff] at hX hY ⊢
  simpa using (hX.smul ha).add (hY.smul hb)

/-- Theorem 5.4.4.1: the cone `𝕊ⁿ₊` of positive semidefinite real `n × n` matrices is a closed
convex set. -/
theorem positiveSemidefiniteCone_isClosed_convex (n : ℕ) :
    IsClosed (𝕊^n₊) ∧ Convex ℝ (𝕊^n₊) :=
  ⟨positiveSemidefiniteCone_isClosed n, positiveSemidefiniteCone_convex n⟩

end

end
