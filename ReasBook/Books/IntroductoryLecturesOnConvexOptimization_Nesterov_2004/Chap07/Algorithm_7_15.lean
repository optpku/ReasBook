/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Lemma_7_15

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open scoped MatrixOrder RealSymmetricMatrixSpace

variable {n : ℕ}

local notation "Mₙ" => Matrix (Fin n) (Fin n) ℝ
local notation "SymmMat" => 𝕊^n

/- Algorithm 7.15 lies in Chapter 7's semidefinite-cone / tridiagonal-reduction domain.

Sampled owner-style declarations:
- Chapter 5 `𝕊^n`, `𝕊^n₊`, and `𝕊^n₊₊`, the chapter owners for symmetric, positive-semidefinite,
  and strict positive-definite matrices;
- `factorizationSemidefiniteFeasibleSet` and `factorizationSemidefiniteObjective` in
  `Lemma_7_15`, the Chapter 7 owner layer for the semidefinite subproblem attached to an auxiliary
  matrix;
- mathlib `IsMaxOn`, the canonical maximizer predicate for a chosen next iterate.

Best owner abstraction:
- source-facing: Algorithm 7.15's next-iterate condition for the semidefinite-cone scheme;
- core/canonical: the Chapter 7 semidefinite feasible set and objective from `Lemma_7_15`;
- bridge/view: an orthogonal tridiagonal reduction of the auxiliary symmetric matrix together with
  the induced factor matrix for Lemma 7.15.

Primitive data:
- the strict-cone auxiliary matrix `A : 𝕊^n₊₊`;
- an orthogonal matrix `U`;
- a symmetric tridiagonal representative `T : 𝕊^n`;
- a candidate next iterate `X : 𝕊^n`.

Derived API:
- the orthogonal-tridiagonal reduction relation on the chapter symmetric carrier;
- the factor matrix `L = √T Uᵀ` canonically induced by the reduction data;
- the source-facing next-iterate predicate, expressed by feasibility and `IsMaxOn` for the
  canonical semidefinite objective attached to that factor matrix.

This refinement removes the raw `Matrix (Fin n) (Fin n) ℝ` owner layer, deletes the packaging
artifact `OrthogonalTridiagonalization`, and replaces the arbitrary `searchProcedure` parameter by
the canonical maximizer relation on the Chapter 7 semidefinite relaxation surface. The reduction
data now feeds Lemma 7.15 through the explicit bridge factor `L = √T Uᵀ`, so the public API still
speaks about the textbook factorization-based semidefinite problem rather than a different problem
posed directly on the similarity representative `T`. Sect. A.2 then belongs only to the
proof/implementation route for finding such a maximizer in the tridiagonal case, not to the public
mathematical API.
-/

/-- An orthogonal tridiagonal reduction of a symmetric auxiliary matrix `A` consists of an
orthogonal matrix `U` and a symmetric matrix `T` whose entries vanish outside the diagonal and the
first off-diagonals, with `A = U T Uᵀ`. The matrix data live on the chapter carrier `𝕊^n`; only
the orthogonal factor uses the ambient matrix owner. -/
def IsOrthogonalTridiagonalReduction
    (A : SymmMat) (U : Matrix.orthogonalGroup (Fin n) ℝ) (T : SymmMat) : Prop :=
  (∀ i j : Fin n, i.1 + 1 < j.1 ∨ j.1 + 1 < i.1 → (T : Mₙ) i j = 0) ∧
    (A : Mₙ) = (U : Mₙ) * (T : Mₙ) * ((U : Mₙ)ᵀ)

/-- Unfolding `IsOrthogonalTridiagonalReduction A U T` gives the entrywise tridiagonal condition
on `T` together with the orthogonal similarity formula `A = U T Uᵀ`. -/
theorem isOrthogonalTridiagonalReduction_iff
    (A : SymmMat) (U : Matrix.orthogonalGroup (Fin n) ℝ) (T : SymmMat) :
    IsOrthogonalTridiagonalReduction A U T ↔
      (∀ i j : Fin n, i.1 + 1 < j.1 ∨ j.1 + 1 < i.1 → (T : Mₙ) i j = 0) ∧
        (A : Mₙ) = (U : Mₙ) * (T : Mₙ) * ((U : Mₙ)ᵀ) :=
  Iff.rfl

namespace IsOrthogonalTridiagonalReduction

/-- The factor matrix canonically induced by an orthogonal tridiagonal reduction `A = U T Uᵀ`.
It is the bridge from the source-facing reduction data to Lemma 7.15's factorization-based
semidefinite objective. -/
def factor
    (U : Matrix.orthogonalGroup (Fin n) ℝ) (T : SymmMat) : Mₙ :=
  CFC.sqrt (T : Mₙ) * (U : Mₙ)ᵀ

/-- A strict-cone matrix and any of its orthogonal tridiagonal representatives determine the same
positive-definite form up to orthogonal conjugation, so the representative itself is
positive-definite. -/
theorem posDef
    {A : 𝕊^n₊₊} {U : Matrix.orthogonalGroup (Fin n) ℝ} {T : SymmMat}
    (hUT : IsOrthogonalTridiagonalReduction (A : SymmMat) U T) :
    (T : Mₙ).PosDef := by
  let hU : IsUnit (U : Mₙ) := Unitary.isUnit_coe
  have hA : ((A : SymmMat) : Mₙ).PosDef := strictPositiveSemidefiniteCone_posDef A
  have hconj : ((U : Mₙ) * (T : Mₙ) * star (U : Mₙ)).PosDef := by
    simpa [hUT.2] using hA
  exact
    (Matrix.IsUnit.posDef_star_right_conjugate_iff hU).mp hconj

/-- The induced factor matrix `√T Uᵀ` really is a factorization of the original strict-cone
matrix `A`. This is the bridge needed to feed Algorithm 7.15 back into Lemma 7.15's canonical
factorization-based semidefinite problem. -/
theorem factorization_eq
    {A : 𝕊^n₊₊} {U : Matrix.orthogonalGroup (Fin n) ℝ} {T : SymmMat}
    (hUT : IsOrthogonalTridiagonalReduction (A : SymmMat) U T) :
    ((A : SymmMat) : Mₙ) = (factor U T)ᵀ * factor U T := by
  have hT : (T : Mₙ).PosDef := hUT.posDef
  have hsqrt_symm : (CFC.sqrt (T : Mₙ)).IsSymm := by
    simpa [Matrix.IsHermitian, Matrix.IsSymm] using
      (CFC.sqrt_nonneg (T : Mₙ)).posSemidef.isHermitian
  have hsqrt_transpose : (CFC.sqrt (T : Mₙ))ᵀ = CFC.sqrt (T : Mₙ) := by
    simpa [Matrix.IsSymm] using hsqrt_symm
  calc
    ((A : SymmMat) : Mₙ) = (U : Mₙ) * (T : Mₙ) * (U : Mₙ)ᵀ := hUT.2
    _ = (U : Mₙ) * (CFC.sqrt (T : Mₙ) * CFC.sqrt (T : Mₙ)) * (U : Mₙ)ᵀ := by
      rw [CFC.sqrt_mul_sqrt_self _ hT.posSemidef.nonneg]
    _ = (U : Mₙ) * ((CFC.sqrt (T : Mₙ))ᵀ * CFC.sqrt (T : Mₙ)) * (U : Mₙ)ᵀ := by
      simp [hsqrt_transpose]
    _ = (factor U T)ᵀ * factor U T := by
      simp [factor, Matrix.transpose_mul, mul_assoc]

end IsOrthogonalTridiagonalReduction

open IsOrthogonalTridiagonalReduction

/-- Algorithm 7.15: a symmetric matrix `X` can serve as the next iterate for the semidefinite-cone
scheme at a strict-cone auxiliary matrix `A` if `A` admits an orthogonal tridiagonal reduction
`A = U T Uᵀ` and `X` is a feasible maximizer of the canonical semidefinite subproblem attached to
the induced factor matrix `√T Uᵀ`, which still factorizes `A` in the sense of Lemma 7.15. -/
def IsSemidefiniteConeNextIterate
    (A : 𝕊^n₊₊) (X : SymmMat) : Prop :=
  ∃ (U : Matrix.orthogonalGroup (Fin n) ℝ) (T : SymmMat),
    IsOrthogonalTridiagonalReduction (A : SymmMat) U T ∧
      X ∈ factorizationSemidefiniteFeasibleSet ∧
        IsMaxOn
          (factorizationSemidefiniteObjective (factor U T))
          factorizationSemidefiniteFeasibleSet
          X

/-- Unfolding `IsSemidefiniteConeNextIterate A X` gives exactly the orthogonal tridiagonal
reduction data together with the canonical feasible-maximizer condition for the Chapter 7
semidefinite objective of the induced factor matrix `√T Uᵀ`. -/
theorem isSemidefiniteConeNextIterate_iff
    (A : 𝕊^n₊₊) (X : SymmMat) :
    IsSemidefiniteConeNextIterate A X ↔
      ∃ (U : Matrix.orthogonalGroup (Fin n) ℝ) (T : SymmMat),
        IsOrthogonalTridiagonalReduction (A : SymmMat) U T ∧
          X ∈ factorizationSemidefiniteFeasibleSet ∧
            IsMaxOn
              (factorizationSemidefiniteObjective (factor U T))
              factorizationSemidefiniteFeasibleSet
              X :=
  Iff.rfl

/-- A displayed orthogonal tridiagonal reduction together with a feasible maximizer of the
corresponding Chapter 7 semidefinite objective of the induced factor matrix produces a valid
Algorithm 7.15 next iterate. -/
theorem IsOrthogonalTridiagonalReduction.isSemidefiniteConeNextIterate
    {A : 𝕊^n₊₊} {U : Matrix.orthogonalGroup (Fin n) ℝ} {T X : SymmMat}
    (hUT : IsOrthogonalTridiagonalReduction (A : SymmMat) U T)
    (hX :
      X ∈ factorizationSemidefiniteFeasibleSet ∧
        IsMaxOn
          (factorizationSemidefiniteObjective (factor U T))
          factorizationSemidefiniteFeasibleSet
          X) :
    IsSemidefiniteConeNextIterate A X :=
  ⟨U, T, hUT, hX.1, hX.2⟩

/-- Every Algorithm 7.15 next iterate is feasible for the Chapter 7 semidefinite subproblem. -/
theorem IsSemidefiniteConeNextIterate.mem_feasibleSet
    {A : 𝕊^n₊₊} {X : SymmMat} (hX : IsSemidefiniteConeNextIterate A X) :
    X ∈ factorizationSemidefiniteFeasibleSet := by
  rcases hX with ⟨_, _, _, hfeas, _⟩
  exact hfeas

end
