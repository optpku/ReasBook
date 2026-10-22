/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_21
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_17
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_18
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_4_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open RealSymmetricMatrixSpace
open scoped RealSymmetricMatrixSpace
open scoped BigOperators

variable {m n : ℕ}

local notation "Eₘ" => EuclideanSpace ℝ (Fin m)
local notation "Mₙ" => Matrix (Fin n) (Fin n) ℝ

/- Definition 7.45 lies in Chapter 7's spectral-radius minimization domain.

Sampled owner-style declarations:
- `spectralRadiusObjective` in `Definition_7_18`, the chapter owner for the objective
  `y ↦ ρ(∑ᵢ yᵢ Aᵢ)`;
- `linearMatrixCombination` in `Definition_7_21`, the chapter owner for the coefficient-sum
  matrix map;
- `Matrix.gram`, `Matrix.gram_apply`, and `Matrix.posDef_gram_of_linearIndependent`, the
  canonical Gram-matrix owner and positivity API for a finite family in an inner-product space;
- `RealSymmetricMatrixSpace.inner_eq_frobeniusInner`, the Chapter 5 bridge identifying the
  intrinsic inner product on `𝕊^n` with the Frobenius pairing;
- `SetConstrainedMinimizationProblem` and `SetConstrainedMinimizationProblem.optimalValue` in
  Chapter 1, the project owners for a feasible set together with a real-valued objective and its
  canonical optimal-value layer;
- `SupportFunctionOptimizationProblem.toSetConstrainedMinimizationProblem` in `Definition_7_10`,
  the nearby chapter bridge pattern from richer problem data to the Chapter 1 owner.

Best owner abstraction:
- source-facing: `SpectralRadiusMinimizationProblem m n`, which stores exactly the feasible set
  and symmetric coefficient family from the source;
- core/canonical: `spectralRadiusObjective`, `linearMatrixCombination`, `Matrix.gram ℝ` on the
  intrinsic family `coeffMatrices : Fin m → 𝕊^n`, `ρ(X)` on `𝕊^n`, and
  `SetConstrainedMinimizationProblem Eₘ`;
- bridge/view: `matrixMap`, the ambient coefficient formula for `matrixMap`, the ambient
  Frobenius-entry formula for `gramMatrix`, and `toSetConstrainedMinimizationProblem`.

Primitive data:
- the feasible set `Q ⊆ ℝ^m` together with its closed/convex/nonzero conditions;
- the symmetric coefficient matrices `A₁, …, A_m` and their linear independence.

Derived API:
- the symmetric-matrix map `y ↦ ∑ᵢ yᵢ Aᵢ`, landing directly in `𝕊^n`;
- the spectral-radius objective, via `spectralRadiusObjective`;
- the Frobenius Gram matrix, via `Matrix.gram ℝ` on `𝕊^n`;
- the Chapter 1 constrained-minimization owner and its canonical `optimalValue`.

This refinement keeps the textbook problem data as the public owner and deletes the duplicate local
objective wheel in favor of the existing chapter owner `spectralRadiusObjective`. The linear map
now lands directly in `𝕊^n`, so symmetry is primitive in the owner rather than recovered later,
the linear-independence hypothesis is intrinsic on `𝕊^n` rather than on coerced ambient matrices,
and the feasible-set / objective packaging is exposed only through the canonical bridge
`toSetConstrainedMinimizationProblem`, whose inherited `optimalValue : EReal` is the only
optimization-value owner. Ambient matrix formulas remain companion bridge lemmas. -/

/-- A spectral-radius minimization problem as in Definition 7.45 consists of a closed convex
feasible set `Q ⊆ ℝ^m` avoiding the origin together with linearly independent symmetric coefficient
matrices `A₁, …, A_m ∈ 𝕊ⁿ`, so that the associated linear matrix map is
`y ↦ ∑ᵢ yᵢ Aᵢ`. The objective, optimal value, Frobenius Gram matrix, and maximal rank notation
attached to this problem are defined below. -/
structure SpectralRadiusMinimizationProblem (m n : ℕ) where
  /-- The feasible set `Q ⊆ ℝ^m`. -/
  feasibleSet : Set (EuclideanSpace ℝ (Fin m))
  /-- The feasible set is closed. -/
  feasibleSet_isClosed : IsClosed feasibleSet
  /-- The feasible set is convex. -/
  feasibleSet_convex : Convex ℝ feasibleSet
  /-- The feasible set is separated from the origin in the sense that `0 ∉ Q`. -/
  zero_not_mem_feasibleSet : (0 : EuclideanSpace ℝ (Fin m)) ∉ feasibleSet
  /-- The symmetric coefficient matrices `A₁, …, A_m`. -/
  coeffMatrices : Fin m → 𝕊^n
  /-- The coefficient matrices are linearly independent. -/
  coeffMatrices_linearIndependent : LinearIndependent ℝ coeffMatrices

namespace SpectralRadiusMinimizationProblem

/-- The linear matrix map `A : ℝ^m → 𝕊^n` associated with the coefficient matrices. -/
def matrixMap (problem : SpectralRadiusMinimizationProblem m n) : Eₘ →ₗ[ℝ] 𝕊^n :=
  LinearMap.codRestrict (𝕊^n)
    (linearMatrixCombination fun i ↦ (problem.coeffMatrices i : Mₙ))
    fun y ↦ by
      simpa [linearMatrixCombination_apply] using
        (show (((∑ i : Fin m, y i • problem.coeffMatrices i : 𝕊^n) : Mₙ) ∈ 𝕊^n) from
          (∑ i : Fin m, y i • problem.coeffMatrices i).2)

/-- Evaluating `matrixMap` gives the coefficient formula `A(y) = ∑ᵢ yᵢ Aᵢ`. -/
@[simp] theorem matrixMap_apply
    (problem : SpectralRadiusMinimizationProblem m n) (y : Eₘ) :
    problem.matrixMap y = ∑ i : Fin m, y i • problem.coeffMatrices i := by
  ext a b
  simp [matrixMap, linearMatrixCombination_apply]

/-- Coercing `matrixMap y` to ambient matrices gives the textbook coefficient formula
`A(y) = ∑ᵢ yᵢ Aᵢ`. -/
theorem coe_matrixMap_apply
    (problem : SpectralRadiusMinimizationProblem m n) (y : Eₘ) :
    ((problem.matrixMap y : 𝕊^n) : Mₙ) =
      ∑ i : Fin m, y i • (problem.coeffMatrices i : Mₙ) := by
  simp [matrixMap, linearMatrixCombination_apply]

-- Proof sketch: `problem.matrixMap y` lies in `𝕊^n` by construction, so ambient symmetry follows
-- from the Chapter 5 coercion bridge `RealSymmetricMatrixSpace.isSymm`.
/-- The ambient matrix underlying `A(y)` is symmetric for every `y`. -/
theorem matrixMap_isSymm
    (problem : SpectralRadiusMinimizationProblem m n) (y : Eₘ) :
    Matrix.IsSymm (((problem.matrixMap y : 𝕊^n) : Mₙ)) := by
  simpa using RealSymmetricMatrixSpace.isSymm (problem.matrixMap y)

/-- Coercing the coefficient family to ambient matrices preserves its linear independence. -/
theorem coeffMatrices_linearIndependent_coe
    (problem : SpectralRadiusMinimizationProblem m n) :
    LinearIndependent ℝ (fun i ↦ (problem.coeffMatrices i : Mₙ)) := by
  simpa using
    problem.coeffMatrices_linearIndependent.map'
      (Submodule.subtype (𝕊^n : Submodule ℝ Mₙ)) (Submodule.ker_subtype (𝕊^n : Submodule ℝ Mₙ))

/-- The spectral-radius objective `φ(y) = ρ(A(y))`. -/
abbrev objective (problem : SpectralRadiusMinimizationProblem m n) : Eₘ → ℝ :=
  spectralRadiusObjective problem.coeffMatrices

/-- The canonical Chapter 1 constrained minimization owner attached to a spectral-radius
minimization problem. -/
def toSetConstrainedMinimizationProblem
    (problem : SpectralRadiusMinimizationProblem m n) :
    SetConstrainedMinimizationProblem Eₘ where
  feasibleSet := problem.feasibleSet
  objective := problem.objective

@[simp] theorem toSetConstrainedMinimizationProblem_feasibleSet
    (problem : SpectralRadiusMinimizationProblem m n) :
    problem.toSetConstrainedMinimizationProblem.feasibleSet = problem.feasibleSet :=
  rfl

@[simp] theorem toSetConstrainedMinimizationProblem_apply
    (problem : SpectralRadiusMinimizationProblem m n) (y : Eₘ) :
    problem.toSetConstrainedMinimizationProblem y = problem.objective y :=
  rfl

/-- A spectral-radius minimization problem can be used as its objective function `φ`. -/
instance : CoeFun (SpectralRadiusMinimizationProblem m n) (fun _ ↦ Eₘ → ℝ) where
  coe problem := problem.toSetConstrainedMinimizationProblem

/-- Evaluating `objective` applies the spectral radius to the matrix `A(y)`. -/
theorem objective_apply
    (problem : SpectralRadiusMinimizationProblem m n) (y : Eₘ) :
    problem.objective y = ρ(problem.matrixMap y) := by
  simpa [objective, coe_matrixMap_apply] using
    spectralRadiusObjective_apply problem.coeffMatrices y

@[simp] theorem coe_apply
    (problem : SpectralRadiusMinimizationProblem m n) (y : Eₘ) :
    problem y = problem.objective y :=
  rfl

/-- The canonical Chapter 1 optimal value of the associated constrained minimization problem is
the infimum of the feasible objective values, viewed in `EReal`. -/
theorem optimalValue_eq_sInf_image
    (problem : SpectralRadiusMinimizationProblem m n) :
    problem.toSetConstrainedMinimizationProblem.optimalValue =
      sInf ((fun y ↦ (problem.objective y : EReal)) '' problem.feasibleSet) := by
  simpa using problem.toSetConstrainedMinimizationProblem.optimalValue_eq_sInf_image

/-- The Frobenius Gram matrix `G` with entries `G^(i,j) = ⟨Aᵢ, Aⱼ⟩`. -/
abbrev gramMatrix (problem : SpectralRadiusMinimizationProblem m n) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.gram ℝ problem.coeffMatrices

/-- The intrinsic Gram matrix on `𝕊^n` agrees with the Chapter 7 ambient-matrix Gram owner. -/
theorem gramMatrix_eq_ambient_gram
    (problem : SpectralRadiusMinimizationProblem m n) :
    problem.gramMatrix = Matrix.gram ℝ (fun i ↦ (problem.coeffMatrices i : Mₙ)) := by
  ext i j
  rw [gramMatrix, Matrix.gram_apply, Matrix.gram_apply]
  exact
    Submodule.coe_inner (𝕊^n : Submodule ℝ Mₙ) (problem.coeffMatrices i)
      (problem.coeffMatrices j)

/-- The entries of `gramMatrix` are given by the textbook Frobenius double sum. -/
theorem gramMatrix_apply
    (problem : SpectralRadiusMinimizationProblem m n) (i j : Fin m) :
    problem.gramMatrix i j =
      ∑ a : Fin n, ∑ b : Fin n,
        (problem.coeffMatrices i : Mₙ) a b * (problem.coeffMatrices j : Mₙ) a b := by
  rw [problem.gramMatrix_eq_ambient_gram]
  simpa using
    matrix_gram_apply_eq_entrywise_sum (fun k ↦ (problem.coeffMatrices k : Mₙ)) i j

-- Proof sketch: the Frobenius inner product is positive definite on the real matrix space, so the
-- Gram matrix of a linearly independent family is positive definite.
/-- The Frobenius Gram matrix of the coefficient matrices is positive definite. -/
theorem gramMatrix_posDef
    (problem : SpectralRadiusMinimizationProblem m n) :
    problem.gramMatrix.PosDef := by
  simpa [gramMatrix] using
    Matrix.posDef_gram_of_linearIndependent problem.coeffMatrices_linearIndependent

/-- The maximal rank attained by the matrices `A(y)` as `y` ranges over `ℝ^m`. -/
def maxRank (problem : SpectralRadiusMinimizationProblem m n) : ℕ :=
  sSup (Set.range fun y : Eₘ ↦ Matrix.rank (((problem.matrixMap y : 𝕊^n) : Mₙ)))

-- Proof sketch: unfold `maxRank`; the right-hand side is the supremum of the ranks of the
-- matrices `A(y)` over all parameter values `y`.
/-- The notation `maxRank` is the supremum of the ranks of the matrices `A(y)`. -/
theorem maxRank_eq_sSup
    (problem : SpectralRadiusMinimizationProblem m n) :
    problem.maxRank =
      sSup (Set.range fun y : Eₘ ↦ Matrix.rank (((problem.matrixMap y : 𝕊^n) : Mₙ))) :=
  rfl

/-- Helper for Definition 7.45: scalar multiplication does not increase the rank of a square real
matrix. -/
private theorem matrixRankSmulLe (c : ℝ) (A : Mₙ) : Matrix.rank (c • A) ≤ Matrix.rank A := by
  -- Rewrite scalar multiplication as right multiplication by a scalar matrix and apply the
  -- standard multiplicative rank bound.
  simpa [smul_eq_mul] using Matrix.rank_mul_le_right (c • (1 : Mₙ)) A

/-- Helper for Definition 7.45: the rank of a sum of square real matrices is at most the sum of
their ranks. -/
private theorem matrixRankAddLe (A B : Mₙ) :
    Matrix.rank (A + B) ≤ Matrix.rank A + Matrix.rank B := by
  let f := A.mulVecLin
  let g := B.mulVecLin
  let Uf : Submodule ℝ (Fin n → ℝ) := f.range
  let Ug : Submodule ℝ (Fin n → ℝ) := g.range
  -- The image of `f + g` lands in the supremum of the individual ranges.
  have hrange : (f + g).range ≤ Uf ⊔ Ug := by
    rintro _ ⟨v, rfl⟩
    refine Submodule.mem_sup.2 ?_
    exact ⟨f v, ⟨v, by rfl⟩, g v, ⟨v, by rfl⟩, rfl⟩
  have hfg : (A + B).mulVecLin = f + g := by
    unfold f g
    exact Matrix.mulVecLin_add A B
  -- Passing to `finrank` converts the range inclusion into the usual rank-subadditivity estimate.
  calc
    Matrix.rank (A + B) = Module.finrank ℝ ((A + B).mulVecLin).range := rfl
    _ = Module.finrank ℝ (f + g).range := by rw [hfg]
    _ ≤ Module.finrank ℝ (((Uf ⊔ Ug) : Submodule ℝ (Fin n → ℝ))) := Submodule.finrank_mono hrange
    _ ≤ Module.finrank ℝ Uf + Module.finrank ℝ Ug :=
      Submodule.finrank_add_le_finrank_add_finrank _ _
    _ = Matrix.rank A + Matrix.rank B := by
      simp [Uf, Ug, f, g, Matrix.rank]

/-- Helper for Definition 7.45: the rank of a finite linear combination of square real matrices is
bounded by the sum of the ranks of the summands. -/
private theorem matrixRankLinearCombinationLe
    (coeffs : Fin m → ℝ) (A : Fin m → Mₙ) :
    Matrix.rank (∑ i : Fin m, coeffs i • A i) ≤ ∑ i : Fin m, Matrix.rank (A i) := by
  -- Induct over the finite support and combine the scalar and additive rank estimates.
  have hsum :
      ∀ s : Finset (Fin m),
        Matrix.rank (s.sum fun i ↦ coeffs i • A i) ≤ s.sum fun i ↦ Matrix.rank (A i) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro i s hi hs
      have hstep :
          Matrix.rank (coeffs i • A i + s.sum fun j ↦ coeffs j • A j) ≤
            Matrix.rank (A i) + s.sum fun j ↦ Matrix.rank (A j) := by
        exact (matrixRankAddLe _ _).trans (add_le_add (matrixRankSmulLe _ _) hs)
      simpa [Finset.sum_insert, hi, add_comm, add_left_comm, add_assoc] using hstep
  simpa using hsum Finset.univ

-- Proof sketch: for each `y`, use the rank bound `rank (∑ᵢ yᵢ Aᵢ) ≤ min {n, ∑ᵢ rank Aᵢ}` and
-- then take the supremum over all `y`.
/-- Definition 7.45: the maximal rank is bounded by `min {n, ∑ᵢ rank Aᵢ}`. -/
theorem maxRank_le_min_matrixSize_sum_coeffRanks
    (problem : SpectralRadiusMinimizationProblem m n) :
    problem.maxRank ≤
      min n (∑ i : Fin m, Matrix.rank (problem.coeffMatrices i : Mₙ)) := by
  classical
  rw [problem.maxRank_eq_sSup]
  refine csSup_le (Set.range_nonempty fun y : Eₘ ↦
    Matrix.rank (((problem.matrixMap y : 𝕊^n) : Mₙ))) ?_
  rintro _ ⟨y, rfl⟩
  -- The width bound gives the ambient `n` contribution to the final `min`.
  have hwidth : Matrix.rank (((problem.matrixMap y : 𝕊^n) : Mₙ)) ≤ n := by
    exact Matrix.rank_le_width _
  -- Rewriting `matrixMap y` to the coefficient sum reduces the second bound to a rank estimate for
  -- a finite linear combination of the coefficient matrices.
  have hsum :
      Matrix.rank (((problem.matrixMap y : 𝕊^n) : Mₙ)) ≤
        ∑ i : Fin m, Matrix.rank (problem.coeffMatrices i : Mₙ) := by
    rw [problem.coe_matrixMap_apply]
    -- The generic finite-sum rank bound applies directly to the coefficient family of `matrixMap`.
    simpa using
      matrixRankLinearCombinationLe (coeffs := fun i ↦ y i)
        (A := fun i ↦ (problem.coeffMatrices i : Mₙ))
  -- The fixed-`y` rank bound is now strong enough to discharge the `min` inequality.
  exact le_min hwidth hsum

end SpectralRadiusMinimizationProblem
