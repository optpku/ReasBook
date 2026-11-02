import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_7.ch1_sec1_7_exercise_1_9.Encoding
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap09.section_9_1.ch9_sec9_1_1_theorem_9_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap09.section_9_1.ch9_sec9_1_1_theorem_9_4

open scoped BigOperators Matrix

noncomputable section Theorem96Reduction

open InnerProductSpace Module

/-- A rational basis input for `ℝ^n`, encoded by the nonsingular square matrix whose columns are
the basis vectors in the standard coordinates. -/
structure RationalBasis (n : ℕ) where
  basisMatrix : Matrix (Fin n) (Fin n) ℚ
  nonsingular : IsUnit basisMatrix.det

namespace RationalBasis

/-- The Euclidean basis whose columns are the rational basis matrix encoded by `B`. -/
noncomputable def basis {n : ℕ} (B : RationalBasis n) :
    Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
  euclideanBasisOfMatrix (B.basisMatrix.map (Rat.castHom ℝ)) <| by
    refine isUnit_iff_ne_zero.mpr ?_
    intro hzero
    apply B.nonsingular.ne_zero
    have hcast : (B.basisMatrix.det : ℝ) = 0 := by
      calc
        (B.basisMatrix.det : ℝ) = (B.basisMatrix.map (Rat.castHom ℝ)).det := by
          simpa using (Rat.cast_det B.basisMatrix)
        _ = 0 := hzero
    exact_mod_cast hcast

/-- The encoding size of a rational basis is the canonical matrix encoding size of its coordinate
matrix. -/
def encodingSize {n : ℕ} (B : RationalBasis n) : ℕ :=
  rational_matrix_encoding_size B.basisMatrix

/-- `B.encodingSize` is the canonical matrix encoding size of `B.basisMatrix`. -/
theorem encodingSize_eq {n : ℕ} (B : RationalBasis n) :
    B.encodingSize = rational_matrix_encoding_size B.basisMatrix :=
  rfl

/-- Expanding `B.encodingSize` gives the coordinatewise encoding-size sum. -/
theorem encodingSize_eq_sum {n : ℕ} (B : RationalBasis n) :
    B.encodingSize = ∑ i, ∑ j, EncodingSize.rational (B.basisMatrix i j) := by
  simp [encodingSize, rational_matrix_encoding_size, EncodingSize.rationalVector]

end RationalBasis

/-- A Lovász basis reduction algorithm on rational bases of `ℝ^n` produces a run of the basis
reduction procedure on successive bases, together with an explicit termination index and a
polynomial bit-operation bound in the encoding size of the original basis. Every basis in the run
generates the same lattice as the original input basis. -/
structure LovaszBasisReductionAlgorithm (n : ℕ) where
  basisAt : RationalBasis n → ℕ → Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))
  terminationIndex : RationalBasis n → ℕ
  bitOperationCount : RationalBasis n → ℕ
  starts_from_input :
    ∀ B : RationalBasis n, basisAt B 0 = B.basis
  preserves_lattice :
    ∀ (B : RationalBasis n) (t : ℕ),
      (EuclideanSpace.equiv (Fin n) ℝ).symm ''
          matrix_generated_lattice (B.basisMatrix.map (Rat.castHom ℝ)) =
        Submodule.span ℤ (Set.range (basisAt B t))
  size_reduction :
    ∀ (B : RationalBasis n) (t : ℕ), 0 < t → basis_reduction_condition_i (basisAt B t)
  termination_condition_i :
    ∀ B : RationalBasis n, basis_reduction_condition_i (basisAt B (terminationIndex B))
  termination_condition_ii :
    ∀ B : RationalBasis n, basis_reduction_condition_ii (basisAt B (terminationIndex B))
  polynomial_iteration_bound :
    ∃ p : Polynomial ℕ,
      ∀ B : RationalBasis n,
        terminationIndex B ≤ p.eval B.encodingSize
  polynomial_bit_bound :
    ∃ p : Polynomial ℕ,
      ∀ B : RationalBasis n,
        bitOperationCount B ≤ p.eval B.encodingSize

/-- A Lovász basis reduction algorithm terminates on every rational input basis. -/
theorem LovaszBasisReductionAlgorithm.terminates_on
    {n : ℕ} (A : LovaszBasisReductionAlgorithm n) (B : RationalBasis n) :
    ∃ t : ℕ, IsReducedBasis (A.basisAt B t) :=
  ⟨A.terminationIndex B,
    basis_reduction_algorithm_terminates_with_reduced_basis
      (A.termination_condition_i B) (A.termination_condition_ii B)⟩

/-- A Lovász basis reduction algorithm has a polynomial bound on its number of iterations in the
encoding size of the original basis. -/
theorem LovaszBasisReductionAlgorithm.iteration_count_polynomially_bounded
    {n : ℕ} (A : LovaszBasisReductionAlgorithm n) :
    ∃ p : Polynomial ℕ,
      ∀ B : RationalBasis n,
        A.terminationIndex B ≤ p.eval B.encodingSize := by
  -- The required polynomial bound is already stored as part of the algorithm data.
  simpa using A.polynomial_iteration_bound

/-- A Lovász basis reduction algorithm has a polynomial bound on its bit-operation count in the
encoding size of the original basis. -/
theorem LovaszBasisReductionAlgorithm.bit_operation_count_polynomially_bounded
    {n : ℕ} (A : LovaszBasisReductionAlgorithm n) :
    ∃ p : Polynomial ℕ,
      ∀ B : RationalBasis n,
        A.bitOperationCount B ≤ p.eval B.encodingSize := by
  -- The required bit-complexity bound is already stored as part of the algorithm data.
  simpa using A.polynomial_bit_bound

/-- The basis output by a Lovász basis reduction algorithm at its termination index is reduced. -/
theorem LovaszBasisReductionAlgorithm.reducedBasisAtTermination
    {n : ℕ} (A : LovaszBasisReductionAlgorithm n) (B : RationalBasis n) :
    IsReducedBasis (A.basisAt B (A.terminationIndex B)) :=
  basis_reduction_algorithm_terminates_with_reduced_basis
    (A.termination_condition_i B) (A.termination_condition_ii B)

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6/Reduction.lean.
Theorem 9.6 packages three guarantees of a Lovász basis reduction algorithm on rational bases:
the output at the stored termination index is reduced, the number of iterations is polynomially
bounded in the input encoding size, and the bit-operation count is polynomially bounded as well. -/
theorem lovaszBasisReductionAlgorithmSpec
    {n : ℕ} (A : LovaszBasisReductionAlgorithm n) :
    (∀ B : RationalBasis n, IsReducedBasis (A.basisAt B (A.terminationIndex B))) ∧
      (∃ p : Polynomial ℕ,
        ∀ B : RationalBasis n, A.terminationIndex B ≤ p.eval B.encodingSize) ∧
      ∃ p : Polynomial ℕ,
        ∀ B : RationalBasis n, A.bitOperationCount B ≤ p.eval B.encodingSize := by
  -- Unpack the termination certificate and both polynomial bounds already stored in `A`.
  refine ⟨?_, ?_⟩
  · intro B
    exact A.reducedBasisAtTermination B
  · refine ⟨A.polynomial_iteration_bound, A.polynomial_bit_bound⟩

end Theorem96Reduction
