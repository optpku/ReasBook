/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators ComplexOrder

noncomputable section

/-- Canonical additive-group form of positive semidefiniteness: a complex-valued function is
semidefinite if every finite difference-kernel matrix is positive semidefinite. Specializing to
`EuclideanSpace ℝ (Fin d)` recovers the textbook notion on `ℝ^d`. -/
def IsPositiveSemidefiniteFunction {G : Type*} [AddGroup G] (φ : G → ℂ) : Prop :=
  ∀ n (x : Fin n → G), (Matrix.of fun i j ↦ φ (x i - x j)).PosSemidef

/-- Expand the matrix quadratic form `star c ⬝ᵥ (A *ᵥ c)` into the
corresponding double sum. -/
lemma quadraticForm_eq_doubleSum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (c : Fin n → ℂ) :
    dotProduct (star c) (A.mulVec c) = ∑ i, ∑ j, star (c i) * A i j * c j := by
  -- Expand the left quadratic form into row-wise dot products and then distribute the scalar
  -- coefficient across the inner finite sum.
  calc
    dotProduct (star c) (A.mulVec c) = ∑ i, star (c i) * (A.mulVec c) i := by
      rfl
    _ = ∑ i, star (c i) * ((fun j ↦ A i j) ⬝ᵥ c) := by
      rfl
    _ = ∑ i, star (c i) * ∑ j, A i j * c j := by
      simp [dotProduct]
    _ = ∑ i, ∑ j, star (c i) * A i j * c j := by
      simp_rw [Finset.mul_sum, mul_assoc]

/-- Probing a matrix by scalar multiples of standard basis vectors
extracts the corresponding entry with the expected scalar weights. -/
lemma quadraticForm_single_scalarPair {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n)
    (a b : ℂ) :
    dotProduct (star (Pi.single i a)) (A.mulVec (Pi.single j b)) = star a * A i j * b := by
  -- Reduce to the `i,j` entry after evaluating the unique nonzero row and column coordinates.
  rw [Pi.star_single, Matrix.mulVec_single, single_dotProduct]
  simp [mul_assoc]

/-- Evaluating the quadratic form on two standard basis vectors reads
off the corresponding matrix entry. -/
lemma quadraticForm_single_pair {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    dotProduct (star (Pi.single i (1 : ℂ))) (A.mulVec (Pi.single j 1)) = A i j := by
  -- Specialize the scalar-weighted basis probe to coefficients `1` and `1`.
  simpa only [star_one, one_mul, mul_one] using
    (quadraticForm_single_scalarPair A i j (1 : ℂ) 1)

/-- The quadratic form of `A` on a basis vector reads off a diagonal
entry. -/
lemma quadraticForm_single {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    dotProduct (star (Pi.single i (1 : ℂ))) (A.mulVec (Pi.single i 1)) = A i i := by
  -- Specialize the basis-pair evaluation to the diagonal.
  exact quadraticForm_single_pair A i i

/-- Probing the quadratic form on `e_i + e_j` exposes the sum of the
four matrix entries in the `i,j` block. -/
lemma quadraticForm_single_add_single {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    dotProduct (star (Pi.single i (1 : ℂ) + Pi.single j 1))
        (A.mulVec (Pi.single i 1 + Pi.single j 1)) =
      A i i + A i j + A j i + A j j := by
  -- Expand by bilinearity and read off the four basis-vector interactions.
  rw [star_add, Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add]
  rw [quadraticForm_single_pair, quadraticForm_single_pair, quadraticForm_single_pair,
    quadraticForm_single_pair]
  simp [add_assoc]

/-- Probing the quadratic form on `e_i + I e_j` isolates the
off-diagonal skew combination needed for the Hermitian relation. -/
lemma quadraticForm_single_addI_single {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    dotProduct (star (Pi.single i (1 : ℂ) + Pi.single j Complex.I))
        (A.mulVec (Pi.single i 1 + Pi.single j Complex.I)) =
      A i i + A i j * Complex.I - Complex.I * A j i + A j j := by
  -- Normalize the `I`-weighted basis vector into a scalar multiple and then expand bilinearly.
  have hsingleI : Pi.single j Complex.I = Complex.I • (Pi.single j (1 : ℂ) : Fin n → ℂ) := by
    ext k
    simp [Pi.single_apply]
  rw [hsingleI, star_add, star_smul, Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct]
  rw [dotProduct_add]
  rw [dotProduct_add]
  rw [dotProduct_smul, smul_dotProduct]
  simp_rw [Pi.star_single]
  have hstarI : star (Complex.I : ℂ) = -(Complex.I : ℂ) := by
    simp
  rw [hstarI]
  -- Proof comment: the remaining basis probes collapse by `single_dotProduct`, and the final
  -- coefficient simplification is exactly `I^2 = -1`.
  simp only [star_one, Matrix.mulVec_single, MulOpposite.op_one, one_smul, single_dotProduct,
    Matrix.col_apply, one_mul, smul_eq_mul, neg_mul, neg_smul, dotProduct_smul, neg_dotProduct,
    smul_dotProduct, mul_neg]
  have hdiagI : -(Complex.I * (Complex.I * A j j)) = A j j := by
    have hmul : Complex.I * (Complex.I * A j j) = -A j j := by
      calc
        Complex.I * (Complex.I * A j j) = (Complex.I ^ 2) * A j j := by
          rw [pow_two, mul_assoc]
        _ = (-1 : ℂ) * A j j := by rw [Complex.I_sq]
        _ = -A j j := by ring
    rw [hmul]
    ring
  calc
    A i i + Complex.I * A i j + (-(Complex.I * A j i) + -(Complex.I * (Complex.I * A j j)))
        = A i i + Complex.I * A i j - Complex.I * A j i + A j j := by
            rw [hdiagI]
            ring
    _ = A i i + A i j * Complex.I - Complex.I * A j i + A j j := by
          ring

/-- A complex matrix whose quadratic form is always nonnegative is
Hermitian. -/
lemma isHermitian_ofNonnegQuadraticForm {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (h : ∀ c : Fin n → ℂ, 0 ≤ dotProduct (star c) (A.mulVec c)) : A.IsHermitian := by
  -- Route correction: avoid the unsupported subscript notation and the expensive Euclidean-operator
  -- detour; recover Hermitianity directly from the standard basis probes.
  refine Matrix.IsHermitian.ext ?_
  intro i j
  -- The diagonal probes force the diagonal entries to be real.
  have hDiag_i := h (Pi.single i (1 : ℂ))
  rw [quadraticForm_single] at hDiag_i
  have hDiag_j := h (Pi.single j (1 : ℂ))
  rw [quadraticForm_single] at hDiag_j
  have hDiagIm_i : 0 = (A i i).im := (Complex.nonneg_iff.mp hDiag_i).2
  have hDiagIm_j : 0 = (A j j).im := (Complex.nonneg_iff.mp hDiag_j).2
  -- The `e_i + e_j` probe controls the sum of the imaginary parts.
  have hSum := h (Pi.single i (1 : ℂ) + Pi.single j 1)
  rw [quadraticForm_single_add_single] at hSum
  have hSumIm : 0 = (A i i + A i j + A j i + A j j).im := (Complex.nonneg_iff.mp hSum).2
  rw [Complex.add_im, Complex.add_im, Complex.add_im] at hSumIm
  -- The `e_i + I e_j` probe controls the real parts.
  have hI := h (Pi.single i (1 : ℂ) + Pi.single j Complex.I)
  rw [quadraticForm_single_addI_single] at hI
  have hIIm : 0 = (A i i + A i j * Complex.I - Complex.I * A j i + A j j).im :=
    (Complex.nonneg_iff.mp hI).2
  have hRe : (A j i).re = (A i j).re := by
    rw [sub_eq_add_neg, Complex.add_im, Complex.add_im, Complex.add_im, Complex.neg_im,
      Complex.mul_I_im, Complex.I_mul_im] at hIIm
    linarith [hIIm, hDiagIm_i, hDiagIm_j]
  have hIm : -(A j i).im = (A i j).im := by
    linarith [hSumIm, hDiagIm_i, hDiagIm_j]
  -- Matching real parts and opposite imaginary parts gives the Hermitian relation.
  apply Complex.ext <;> simp [hRe, hIm]

/-- The textbook quadratic-sum condition makes the finite difference
kernel matrix positive semidefinite. -/
lemma differenceKernelPosSemidef_ofQuadraticNonneg {G : Type*} [AddGroup G] {φ : G → ℂ}
    {n : ℕ} (x : Fin n → G)
    (h :
      ∀ c : Fin n → ℂ, 0 ≤ ∑ i, ∑ j, star (c i) * φ (x i - x j) * c j) :
    (Matrix.of fun i j ↦ φ (x i - x j)).PosSemidef := by
  -- Package the kernel matrix once so the Hermitian and nonnegativity checks share the same API.
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · -- The quadratic-form hypothesis makes the associated Euclidean operator positive.
    apply isHermitian_ofNonnegQuadraticForm
    intro c
    simpa [quadraticForm_eq_doubleSum] using h c
  · -- The matrix quadratic form is exactly the textbook double sum.
    intro c
    simpa [quadraticForm_eq_doubleSum] using h c

-- Proof sketch: unfold `IsPositiveSemidefiniteFunction`, rewrite matrix positive semidefiniteness
-- with `Matrix.posSemidef_iff_dotProduct_mulVec`, and identify the resulting quadratic form with
-- the textbook double sum.
/-- Definition 15.27: a function is positive semidefinite exactly when all finite quadratic sums
`∑_{i,j} \overline{c_i} φ(x_i - x_j) c_j` are nonnegative in `ℂ`, equivalently are real and
nonnegative. -/
theorem isPositiveSemidefiniteFunction_iff_quadratic_sum_nonneg {G : Type*} [AddGroup G]
    {φ : G → ℂ} :
    IsPositiveSemidefiniteFunction φ ↔
      ∀ n (x : Fin n → G) (c : Fin n → ℂ),
        0 ≤ ∑ i, ∑ j, star (c i) * φ (x i - x j) * c j := by
  constructor
  · intro h n x c
    -- Rewrite positive semidefiniteness into nonnegativity of the matrix quadratic form.
    have hc := (Matrix.posSemidef_iff_dotProduct_mulVec.mp (h n x)).2 c
    simpa [quadraticForm_eq_doubleSum] using hc
  · intro h n x
    -- Repackage the textbook double-sum hypothesis as positivity of the kernel matrix.
    exact differenceKernelPosSemidef_ofQuadraticNonneg x (h n x)
