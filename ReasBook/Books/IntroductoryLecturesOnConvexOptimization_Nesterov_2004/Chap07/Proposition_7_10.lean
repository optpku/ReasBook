/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_23

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open scoped BigOperators PositiveDefMatrixNorm

variable {m n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)

/- Proposition 7.10 lies in the finite-family weighted-Gram / positive-definite dual-norm domain.

Relevant owners sampled before drafting:
- the weighted Gram matrix owner and the notation `B[a](w)`;
- `positiveDefMatrixNorm` and the dual notation `‖·‖[G,*]` in `Chap07/Definition_7_23`;
- mathlib `Matrix.trace`, `Matrix.trace_mul_comm`, and `Matrix.trace_vecMulVec`.

The source-facing item is therefore stated directly on the existing weighted-Gram owner and the
existing Chapter 7 dual norm surface, with the displayed consequence split into atomic clauses.
-/

/-- Helper for Proposition 7.10 [Chapter7_1.json:56]: the weighted Gram matrix
`∑ᵢ wᵢ aᵢ aᵢᵀ` attached to a finite family of vectors in `ℝⁿ`. -/
def weightedGramMatrix (a : Fin m → Eₙ) (w : Fin m → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  ∑ i : Fin m, w i • Matrix.vecMulVec (a i) (a i)

namespace WeightedGramMatrix

/- Source-facing notation for the weighted Gram operator attached to the family `a`. -/
scoped notation:max "B[" a:arg "](" w:arg ")" => weightedGramMatrix a w

end WeightedGramMatrix

open scoped WeightedGramMatrix

section WeightedTraceIdentity

-- Proof sketch: substitute the weighted Gram representation
-- `(G : Matrix (Fin n) (Fin n) ℝ) = B[a](weights.weights)` from Proposition 7.9 and multiply on
-- the left by `G⁻¹`; the left-hand side reduces to the identity matrix.
/-- Proposition 7.10 [Chapter7_1.json:56] (1): if the positive-definite matrix `G` is represented
as the weighted Gram matrix `B[a](weights.weights) = ∑ᵢ λᵢ aᵢ aᵢᵀ`, then the equivalent canonical
matrix identity `G⁻¹ B[a](weights.weights) = Iₙ` holds. -/
theorem inv_mul_weightedGramMatrix_eq_one
    (a : Fin m → Eₙ) (weights : StdSimplex ℝ (Fin m))
    (G : {A : Matrix (Fin n) (Fin n) ℝ // A.PosDef})
    (hG : (G : Matrix (Fin n) (Fin n) ℝ) = B[a](weights.weights)) :
    ((G : Matrix (Fin n) (Fin n) ℝ)⁻¹) * B[a](weights.weights) =
      (1 : Matrix (Fin n) (Fin n) ℝ) := by
  let _ := G.2.isUnit.invertible
  -- Substitute the weighted Gram representation and use the canonical inverse identity.
  rw [← hG]
  simpa using Matrix.inv_mul_of_invertible G.1

/-- Helper for Proposition 7.10 [Chapter7_1.json:56]: tracing the inverse matrix against the
rank-one matrix `aᵢ aᵢᵀ` recovers the squared dual norm `‖aᵢ‖[G,*]^2`. -/
lemma trace_inv_mul_rank_one_eq_dualNorm_sq
    (a : Fin m → Eₙ)
    (G : {A : Matrix (Fin n) (Fin n) ℝ // A.PosDef})
    (i : Fin m) :
    Matrix.trace (((G : Matrix (Fin n) (Fin n) ℝ)⁻¹) * Matrix.vecMulVec (a i) (a i)) =
      ‖a i‖[G,*] ^ (2 : ℕ) := by
  have hinner_eq_dotProduct :
      inner ℝ (a i) ((Matrix.toEuclideanLin G.1⁻¹) (a i)) =
        (a i).ofLp ⬝ᵥ (G.1⁻¹ *ᵥ (a i).ofLp) := by
    -- Rewrite the Euclidean inner product through the coordinate dot product of `G⁻¹ aᵢ`.
    change ((Matrix.toEuclideanLin G.1⁻¹) (a i)).ofLp ⬝ᵥ star ((a i).ofLp) =
      (a i).ofLp ⬝ᵥ (G.1⁻¹ *ᵥ (a i).ofLp)
    rw [Matrix.toEuclideanLin_apply, dotProduct_comm]
    simp
  have harg_nonneg :
      0 ≤ inner ℝ (a i) ((Matrix.toEuclideanLin G.1⁻¹) (a i)) := by
    -- The inverse positive-definite matrix defines a nonnegative quadratic form.
    have hnonneg :
        0 ≤ (a i).ofLp ⬝ᵥ (G.1⁻¹ *ᵥ (a i).ofLp) := by
      simpa using G.2.inv.posSemidef.dotProduct_mulVec_nonneg (a i).ofLp
    rw [hinner_eq_dotProduct]
    exact hnonneg
  -- Commute the trace, collapse the rank-one term, and rewrite it by the Chapter 7 dual norm.
  calc
    Matrix.trace (((G : Matrix (Fin n) (Fin n) ℝ)⁻¹) * Matrix.vecMulVec (a i) (a i))
        = Matrix.trace (Matrix.vecMulVec (a i) (a i) * ((G : Matrix (Fin n) (Fin n) ℝ)⁻¹)) := by
            simpa using
              (Matrix.trace_mul_comm ((G : Matrix (Fin n) (Fin n) ℝ)⁻¹)
                (Matrix.vecMulVec (a i) (a i)))
    _ = Matrix.trace (Matrix.vecMulVec (a i) ((a i) ᵥ* ((G : Matrix (Fin n) (Fin n) ℝ)⁻¹))) := by
          rw [Matrix.vecMulVec_mul]
    _ = a i ⬝ᵥ ((a i) ᵥ* ((G : Matrix (Fin n) (Fin n) ℝ)⁻¹)) := by
          rw [Matrix.trace_vecMulVec]
    _ = a i ⬝ᵥ (((G : Matrix (Fin n) (Fin n) ℝ)⁻¹) *ᵥ (a i)) := by
          rw [dotProduct_comm]
          symm
          exact Matrix.dotProduct_mulVec (a i) ((G : Matrix (Fin n) (Fin n) ℝ)⁻¹) (a i)
    _ = inner ℝ (a i) ((Matrix.toEuclideanLin G.1⁻¹) (a i)) := by
          rw [hinner_eq_dotProduct]
    _ = (Real.sqrt (inner ℝ (a i) ((Matrix.toEuclideanLin G.1⁻¹) (a i)))) ^ (2 : ℕ) := by
          symm
          exact Real.sq_sqrt harg_nonneg
    _ = ‖a i‖[G,*] ^ (2 : ℕ) := by
          rw [positiveDefMatrixNorm_dualNorm_eq_sqrt_inner_inv]

-- Proof sketch: take traces in `inv_mul_weightedGramMatrix_eq_one`, use `Matrix.trace_one`, expand
-- `B[a](weights.weights)`, commute traces cyclically, and identify each rank-one trace with
-- `‖a i‖[G,*]^2` via `positiveDefMatrixNorm_dualNorm_eq_sqrt_inner_inv`.
/-- Proposition 7.10 [Chapter7_1.json:56] (2): tracing the weighted Gram identity gives the exact
formula `(n : ℝ) = ∑ᵢ λᵢ ‖aᵢ‖[G,*]^2`. -/
theorem dim_eq_sum_weights_mul_dualNorm_sq
    (a : Fin m → Eₙ) (weights : StdSimplex ℝ (Fin m))
    (G : {A : Matrix (Fin n) (Fin n) ℝ // A.PosDef})
    (hG : (G : Matrix (Fin n) (Fin n) ℝ) = B[a](weights.weights)) :
    (n : ℝ) =
      ∑ i : Fin m, weights.weights i * ‖a i‖[G,*] ^ (2 : ℕ) := by
  have htrace :=
    congrArg Matrix.trace
      (inv_mul_weightedGramMatrix_eq_one (a := a) (weights := weights) (G := G) hG)
  -- Trace the matrix identity, expand the weighted Gram matrix, and rewrite each rank-one trace.
  calc
    (n : ℝ) = Matrix.trace (((G : Matrix (Fin n) (Fin n) ℝ)⁻¹) * B[a](weights.weights)) := by
      simpa [Matrix.trace_one] using htrace.symm
    _ = ∑ i : Fin m,
          weights.weights i *
            Matrix.trace
              (((G : Matrix (Fin n) (Fin n) ℝ)⁻¹) * Matrix.vecMulVec (a i) (a i)) := by
          simp [weightedGramMatrix, Matrix.mul_sum, Matrix.trace_smul]
    _ = ∑ i : Fin m, weights.weights i * ‖a i‖[G,*] ^ (2 : ℕ) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [trace_inv_mul_rank_one_eq_dualNorm_sq (a := a) (G := G) i]

-- Proof sketch: start from the exact identity
-- `(n : ℝ) = ∑ᵢ λᵢ ‖aᵢ‖[G,*]^2`, bound every squared dual norm by `r^2`, and use the simplex
-- relation `∑ᵢ λᵢ = 1`.
/-- Proposition 7.10 [Chapter7_1.json:56] (3): if every generator satisfies `‖aᵢ‖[G,*] ≤ r`, then
the previous identity implies the estimate `(n : ℝ) ≤ r^2`. -/
theorem dim_le_sq_of_dualNorm_le
    (a : Fin m → Eₙ) (weights : StdSimplex ℝ (Fin m))
    (G : {A : Matrix (Fin n) (Fin n) ℝ // A.PosDef})
    (htrace :
      (n : ℝ) =
        ∑ i : Fin m, weights.weights i * ‖a i‖[G,*] ^ (2 : ℕ))
    {r : ℝ} (hr : ∀ i : Fin m, ‖a i‖[G,*] ≤ r) :
    (n : ℝ) ≤ r ^ (2 : ℕ) := by
  obtain ⟨i₀⟩ := StdSimplex.nonempty weights
  have hr_nonneg : 0 ≤ r := by
    -- One simplex index already forces `r` to be nonnegative because dual norms are nonnegative.
    have hdual_nonneg : 0 ≤ ‖a i₀‖[G,*] := by
      rw [positiveDefMatrixNorm_dualNorm_eq_sqrt_inner_inv]
      exact Real.sqrt_nonneg _
    linarith [hr i₀]
  have hweights_total : ∑ i : Fin m, weights.weights i = 1 := by
    simpa [Finsupp.sum_fintype] using weights.total
  have hsum_le :
      (∑ i : Fin m, weights.weights i * ‖a i‖[G,*] ^ (2 : ℕ)) ≤
        ∑ i : Fin m, weights.weights i * r ^ (2 : ℕ) := by
    -- Bound each weighted summand by replacing `‖aᵢ‖[G,*]^2` with `r^2`.
    refine Finset.sum_le_sum ?_
    intro i hi
    have hdual_nonneg : 0 ≤ ‖a i‖[G,*] := by
      rw [positiveDefMatrixNorm_dualNorm_eq_sqrt_inner_inv]
      exact Real.sqrt_nonneg _
    have hsq_le : ‖a i‖[G,*] ^ (2 : ℕ) ≤ r ^ (2 : ℕ) := by
      nlinarith [hr i, hr_nonneg, hdual_nonneg]
    exact mul_le_mul_of_nonneg_left hsq_le (weights.nonneg i)
  calc
    (n : ℝ) = ∑ i : Fin m, weights.weights i * ‖a i‖[G,*] ^ (2 : ℕ) := htrace
    _ ≤ ∑ i : Fin m, weights.weights i * r ^ (2 : ℕ) := hsum_le
    _ = (∑ i : Fin m, weights.weights i) * r ^ (2 : ℕ) := by
          rw [Finset.sum_mul]
    _ = r ^ (2 : ℕ) := by
          simp [hweights_total]

end WeightedTraceIdentity

end
