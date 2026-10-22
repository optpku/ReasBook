/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.Circulant
public import Mathlib.LinearAlgebra.Matrix.Hadamard
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Definition_5_13
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Definition_5_7.Fourier2D
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Definition_5_8.Convolution2D
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Definition_5_9.PeriodicExtension
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Notation_5_2.Coordinates

public section

open scoped BigOperators Kronecker Complex.FiniteDimensional

noncomputable section

namespace Matrix

/-- The source forward `fft2` notation from `(5.39)`, written as the
source-facing rescaling of the canonical normalized two-dimensional DFT. -/
abbrev fft2 (n_x n_y : ℕ) [NeZero n_x] [NeZero n_y] :
    ℂ^[n_x, n_y] → ℂ^[n_x, n_y] :=
  fun f ↦
    ((Real.sqrt n_x : ℂ) * Real.sqrt n_y) •
      Matrix.dft2D n_x n_y f

/-- `Matrix.fft2` is the source-facing scaled forward transform from `(5.39)`,
rewritten through the canonical two-dimensional DFT owner. -/
theorem fft2_def (n_x n_y : ℕ) [NeZero n_x] [NeZero n_y]
    (f : ℂ^[n_x, n_y]) :
    Matrix.fft2 n_x n_y f =
      ((Real.sqrt n_x : ℂ) * Real.sqrt n_y) •
        (Matrix.fourierMatrix n_x * f * (Matrix.fourierMatrix n_y)ᵀ) := by
  -- Expand the source-facing wrapper back to the canonical `Matrix.dft2D` owner.
  rw [Matrix.fft2, Matrix.dft2D_def]

/-- The source forward transform `Matrix.fft2` has the textbook double-sum
exponential coordinate formula from `(5.39)`. -/
theorem fft2_apply (n_x n_y : ℕ) [NeZero n_x] [NeZero n_y]
    (f : ℂ^[n_x, n_y]) (i : Fin n_x) (j : Fin n_y) :
    Matrix.fft2 n_x n_y f i j =
      ∑ i' : Fin n_x, ∑ j' : Fin n_y,
        f i' j' *
          Complex.exp
            (-Complex.I * 2 * Real.pi *
              ((((i : ℕ) * (i' : ℕ) : ℂ) / n_x) +
                (((j : ℕ) * (j' : ℕ) : ℂ) / n_y))) := by
  -- Reuse the canonical 2D DFT coordinate formula and fold the scalar back into `Matrix.fft2`.
  simpa [Matrix.fft2] using Matrix.dft2D_apply_exp n_x n_y f i j

/-- The source inverse `ifft2` notation, written as the source-facing rescaling
of the canonical normalized inverse two-dimensional DFT. -/
abbrev ifft2 (n_x n_y : ℕ) [NeZero n_x] [NeZero n_y] :
    ℂ^[n_x, n_y] → ℂ^[n_x, n_y] :=
  fun g ↦
    (((Real.sqrt n_x : ℂ) * Real.sqrt n_y)⁻¹) •
      Matrix.invDFT2D n_x n_y g

/-- `Matrix.ifft2` is the source-facing scaled inverse transform, written
through the canonical inverse two-dimensional DFT owner. -/
theorem ifft2_def (n_x n_y : ℕ) [NeZero n_x] [NeZero n_y]
    (g : ℂ^[n_x, n_y]) :
    Matrix.ifft2 n_x n_y g =
      (((Real.sqrt n_x : ℂ) * Real.sqrt n_y)⁻¹) •
        ((Matrix.fourierMatrix n_x)ᴴ * g * ((Matrix.fourierMatrix n_y)ᴴ)ᵀ) := by
  -- Expand the source-facing inverse wrapper back to the canonical `Matrix.invDFT2D` owner.
  rw [Matrix.ifft2, Matrix.invDFT2D_def]

/-- The source inverse transform `Matrix.ifft2` has the textbook double-sum
exponential coordinate formula. -/
theorem ifft2_apply (n_x n_y : ℕ) [NeZero n_x] [NeZero n_y]
    (g : ℂ^[n_x, n_y]) (i : Fin n_x) (j : Fin n_y) :
    Matrix.ifft2 n_x n_y g i j =
      (n_x * n_y : ℂ)⁻¹ *
        ∑ i' : Fin n_x, ∑ j' : Fin n_y,
          g i' j' *
            Complex.exp
              (Complex.I * 2 * Real.pi *
                ((((i : ℕ) * (i' : ℕ) : ℂ) / n_x) +
                  (((j : ℕ) * (j' : ℕ) : ℂ) / n_y))) := by
  -- Reuse the canonical inverse 2D DFT coordinate formula and refold the wrapper scaling.
  simpa [Matrix.ifft2] using Matrix.invDFT2D_apply_exp n_x n_y g i j

/-- Helper for Notation 5.2.2-extra-3: reducing an integer difference modulo a positive period
recovers the corresponding subtraction in `Fin n`. -/
theorem periodicIndex_sub_eq_finSub_of_pos {n : ℕ}
    (h : 0 < n) (i k : Fin n) :
    DiscreteSignal.periodicIndex n h (((i : ℕ) : ℤ) - ((k : ℕ) : ℤ)) = i - k := by
  -- Compare both reduced indices through the residue representative of the integer difference.
  apply Fin.ext
  have hsub : ((i - k : Fin n) : ℤ) = ((i : ℤ) - (k : ℤ)) % n :=
    Fin.coe_int_sub_eq_mod i k
  simpa [DiscreteSignal.periodicIndex_val] using congrArg Int.toNat hsub.symm

/-- Helper for Notation 5.2.2-extra-3: vectorizing `Matrix.fft2` turns the two-sided Fourier
action into the Kronecker-product Fourier matrix acting on `Matrix.vec`. -/
theorem vec_fft2_eq_kronFourier_mulVec (n_x n_y : ℕ) [NeZero n_x] [NeZero n_y]
    (f : ℂ^[n_x, n_y]) :
    Matrix.vec (Matrix.fft2 n_x n_y f) =
      (((Real.sqrt n_x : ℂ) * Real.sqrt n_y) •
        ((Matrix.fourierMatrix n_y) ⊗ₖ (Matrix.fourierMatrix n_x))) *ᵥ Matrix.vec f := by
  -- Expand `Matrix.fft2` to the owner formula and then vectorize the two-sided multiplication.
  calc
    Matrix.vec (Matrix.fft2 n_x n_y f)
      = ((Real.sqrt n_x : ℂ) * Real.sqrt n_y) •
          Matrix.vec (Matrix.fourierMatrix n_x * f * (Matrix.fourierMatrix n_y)ᵀ) := by
            rw [Matrix.fft2_def]
            simp [Matrix.vec_smul]
    _ = ((Real.sqrt n_x : ℂ) * Real.sqrt n_y) •
          (((Matrix.fourierMatrix n_y) ⊗ₖ (Matrix.fourierMatrix n_x)) *ᵥ Matrix.vec f) := by
            rw [← Matrix.kronecker_mulVec_vec]
    _ =
        (((Real.sqrt n_x : ℂ) * Real.sqrt n_y) •
          ((Matrix.fourierMatrix n_y) ⊗ₖ (Matrix.fourierMatrix n_x))) *ᵥ Matrix.vec f := by
            rw [smul_mulVec]

/-- Helper for Notation 5.2.2-extra-3: vectorizing `Matrix.ifft2` turns the inverse two-sided
Fourier action into the conjugate-Kronecker Fourier matrix acting on `Matrix.vec`. -/
theorem vec_ifft2_eq_kronConjFourier_mulVec (n_x n_y : ℕ) [NeZero n_x] [NeZero n_y]
    (g : ℂ^[n_x, n_y]) :
    Matrix.vec (Matrix.ifft2 n_x n_y g) =
      ((((Real.sqrt n_x : ℂ) * Real.sqrt n_y)⁻¹) •
        (((Matrix.fourierMatrix n_y)ᴴ) ⊗ₖ ((Matrix.fourierMatrix n_x)ᴴ))) *ᵥ Matrix.vec g := by
  -- Expand `Matrix.ifft2` to the owner formula and then vectorize the inverse two-sided action.
  calc
    Matrix.vec (Matrix.ifft2 n_x n_y g)
      = (((Real.sqrt n_x : ℂ) * Real.sqrt n_y)⁻¹) •
          Matrix.vec ((Matrix.fourierMatrix n_x)ᴴ * g * ((Matrix.fourierMatrix n_y)ᴴ)ᵀ) := by
            rw [Matrix.ifft2_def]
            simp [Matrix.vec_smul]
    _ = (((Real.sqrt n_x : ℂ) * Real.sqrt n_y)⁻¹) •
          ((((Matrix.fourierMatrix n_y)ᴴ) ⊗ₖ ((Matrix.fourierMatrix n_x)ᴴ)) *ᵥ
            Matrix.vec g) := by
            rw [← Matrix.kronecker_mulVec_vec]
    _ =
        ((((Real.sqrt n_x : ℂ) * Real.sqrt n_y)⁻¹) •
          (((Matrix.fourierMatrix n_y)ᴴ) ⊗ₖ ((Matrix.fourierMatrix n_x)ᴴ))) *ᵥ Matrix.vec g := by
            rw [smul_mulVec]

/-- Helper for Notation 5.2.2-extra-3: vectorizing a Hadamard product is diagonal multiplication
by the vectorized left factor. -/
theorem vec_hadamard_eq_diagonal_mulVec (n_x n_y : ℕ)
    (A B : ℂ^[n_x, n_y]) :
    Matrix.vec (Matrix.hadamard A B) =
      Matrix.diagonal (Matrix.vec A) *ᵥ Matrix.vec B := by
  ext ij
  rcases ij with ⟨j, i⟩
  -- Translate the product index back to matrix coordinates and use the diagonal mulVec formula.
  simpa [Matrix.hadamard_apply] using
    (Matrix.mulVec_diagonal (Matrix.vec A) (Matrix.vec B) (j, i)).symm

/-- Helper for Notation 5.2.2-extra-3: the HTTB matrix of the periodic extension of `c` is the
circulant matrix generated by `Matrix.vec c`. -/
theorem periodicExtension_httb_eq_circulantVec {n_x n_y : ℕ}
    (h_x : 0 < n_x) (h_y : 0 < n_y) (c : ℂ^[n_x, n_y]) :
    Matrix.httb n_x n_y (Matrix.periodicExtension h_x h_y c) = Matrix.circulant c.vec := by
  ext ji lk
  rcases ji with ⟨j, i⟩
  rcases lk with ⟨l, k⟩
  -- Expand both owners entrywise and normalize the periodic indices back to `Fin` subtraction.
  rw [Matrix.httb_apply, Matrix.periodicExtension_apply, Matrix.circulant_apply]
  rw [periodicIndex_sub_eq_finSub_of_pos h_x i k, periodicIndex_sub_eq_finSub_of_pos h_y j l]
  rfl

/-- Helper for Notation 5.2.2-extra-3: the local unnormalized Fourier spectrum used for the 1D
right-shift diagonalization is `k ↦ Matrix.fourierRoot n ^ k`. -/
abbrev fourierSpectrum (n : ℕ) [NeZero n] : ℂ^[n] :=
  WithLp.toLp 2 fun k : Fin n ↦ Matrix.fourierRoot n ^ (k : ℕ)

/-- Helper for Notation 5.2.2-extra-3: the local Fourier spectrum abbreviation evaluates to the
corresponding power of `Matrix.fourierRoot`. -/
theorem fourierSpectrum_apply (n : ℕ) [NeZero n] (k : Fin n) :
    Matrix.fourierSpectrum n k = Matrix.fourierRoot n ^ (k : ℕ) := sorry

/-- Helper for Notation 5.2.2-extra-3: the complex right-shift matrix sends the `k`th standard
basis vector to the basis vector at `finRotate n k`. -/
theorem circulantRightShift_mulVec_single_complex
    {n : ℕ} [NeZero n] (k : Fin n) :
    Matrix.circulantRightShift (α := ℂ) n *ᵥ Pi.single k (1 : ℂ) =
      Pi.single (finRotate n k) (1 : ℂ) := by
  ext i
  -- Compare the shift action pointwise against the basis-vector rotation formula.
  have hi :=
    congrFun (Matrix.circulantRightShift_mulVec (n := n) (Pi.single k (1 : ℂ))) i
  by_cases h : i = k + 1
  · have hsub : i - 1 = k := by
      simpa using (sub_eq_iff_eq_add.mpr h)
    simp [Function.comp_apply, finRotate_symm_apply, h] at hi ⊢
  · have hsub : i - 1 ≠ k := by
      intro hk
      apply h
      simpa [add_comm] using (sub_eq_iff_eq_add.mp hk)
    simp [Function.comp_apply, finRotate_symm_apply, h, hsub] at hi ⊢

/-- Helper for Notation 5.2.2-extra-3: the `m`th power of the complex right-shift matrix sends the
`k`th standard basis vector to the basis vector at `((finRotate n)^[m]) k`. -/
theorem rightShiftPow_mulVec_single_complex
    {n : ℕ} [NeZero n] (m : ℕ) (k : Fin n) :
    (Matrix.circulantRightShift (α := ℂ) n ^ m) *ᵥ Pi.single k (1 : ℂ) =
      Pi.single (((finRotate n)^[m]) k) (1 : ℂ) := by
  induction m generalizing k with
  | zero =>
      -- At power zero, the identity matrix fixes each basis vector.
      rw [pow_zero, Matrix.mulVec_single_one]
      ext i
      simp [Matrix.col_apply, Matrix.one_apply, Pi.single_apply]
  | succ m ih =>
      -- One more right shift advances the rotated basis index by one more `finRotate`.
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih]
      rw [Function.iterate_succ_apply']
      exact circulantRightShift_mulVec_single_complex (n := n) (((finRotate n)^[m]) k)

/-- Helper for Notation 5.2.2-extra-3: the circulant basis matrix generated by `Pi.single j 1`
acts on the `k`th standard basis vector by translating it to `k + j`. -/
theorem circulantSingle_mulVec_single_complex
    {n : ℕ} [NeZero n] (j k : Fin n) :
    Matrix.circulant (Pi.single j (1 : ℂ)) *ᵥ Pi.single k (1 : ℂ) =
      Pi.single (k + j) (1 : ℂ) := by
  -- Expand the `k`th column of the basis circulant and compare its unique nonzero entry.
  rw [Matrix.mulVec_single_one]
  ext i
  by_cases h : i = k + j
  · have hsub : i - k = j := by
      simpa [add_comm] using (sub_eq_iff_eq_add.mpr (by simpa [add_comm] using h : i = j + k))
    simp [Matrix.col_apply, Matrix.circulant_apply, h]
  · have hsub : i - k ≠ j := by
      intro hk
      apply h
      simpa [add_comm] using (sub_eq_iff_eq_add.mp hk)
    simp [Matrix.col_apply, Matrix.circulant_apply, h, hsub]

/-- Helper for Notation 5.2.2-extra-3: the `j`th power of the complex right-shift matrix is the
circulant basis matrix generated by `Pi.single j 1`. -/
theorem circulantRightShift_pow_eq_circulant_single_complex
    {n : ℕ} [NeZero n] (j : Fin n) :
    Matrix.circulantRightShift (α := ℂ) n ^ (j : ℕ) = Matrix.circulant (Pi.single j (1 : ℂ)) := by
  -- Compare both matrices on every standard basis vector, where both act by the same cyclic shift.
  apply Matrix.ext_of_mulVec_single
  intro k
  rw [rightShiftPow_mulVec_single_complex, circulantSingle_mulVec_single_complex]
  have hcycle : ((finRotate n)^[j.1]) k = k + j := by
    exact congrFun (finCycle_eq_finRotate_iterate (k := j)).symm k
  simp [hcycle]

/-- Helper for Notation 5.2.2-extra-3: one right shift is diagonalized by the normalized Fourier
matrix, written in the left-multiplication form used by the 2D Kronecker proof. -/
theorem fourier_mul_rightShift_eq_diagonal_mul_fourier (n : ℕ) [NeZero n] :
    Matrix.fourierMatrix n * Matrix.circulantRightShift (α := ℂ) n =
      Matrix.diagonal (Matrix.fourierSpectrum n) * Matrix.fourierMatrix n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  ext i j
  rw [Matrix.mul_apply, Matrix.diagonal_mul]
  -- The right-shift matrix has a single nonzero entry in column `j`, at the row `finRotate j`.
  have hsum :
      ∑ x : Fin (m + 1),
        Matrix.fourierMatrix (m + 1) i x *
          Matrix.circulantRightShift (α := ℂ) (m + 1) x j =
        Matrix.fourierMatrix (m + 1) i (finRotate (m + 1) j) := by
    rw [Fintype.sum_eq_single (finRotate (m + 1) j)]
    · have hone :
          Matrix.circulantRightShift (α := ℂ) (m + 1) (finRotate (m + 1) j) j = (1 : ℂ) := by
        have hfin : (finRotate (m + 1) j - j : Fin (m + 1)) = (1 : Fin (m + 1)) := by
          apply sub_eq_iff_eq_add.mpr
          simp [finRotate_apply, add_comm]
        rw [Matrix.circulantRightShift, Matrix.circulant_apply, hfin]
        simp
      calc
        Matrix.fourierMatrix (m + 1) i (finRotate (m + 1) j) *
            Matrix.circulantRightShift (α := ℂ) (m + 1) (finRotate (m + 1) j) j
          = Matrix.fourierMatrix (m + 1) i (finRotate (m + 1) j) * 1 := by rw [hone]
        _ = Matrix.fourierMatrix (m + 1) i (finRotate (m + 1) j) := by simp
    · intro x hx
      have hzero : Matrix.circulantRightShift (α := ℂ) (m + 1) x j = (0 : ℂ) := by
        have hsub : (x - j : Fin (m + 1)) ≠ (1 : Fin (m + 1)) := by
          intro hx1
          apply hx
          simpa [finRotate_apply, add_comm] using (sub_eq_iff_eq_add.mp hx1)
        have hsubval : ((x - j : Fin (m + 1)) : ℕ) ≠ 1 % (m + 1) := by
          intro hxval
          apply hsub
          apply Fin.ext
          simpa using hxval
        rw [Matrix.circulantRightShift, Matrix.circulant_apply]
        simp [hsubval]
      simp [hzero]
  rw [hsum]
  by_cases hj : j = Fin.last m
  · subst hj
    have hroot : Matrix.fourierRoot (m + 1) ^ (m + 1) = 1 := by
      rw [Matrix.fourierRoot_eq_stdAddChar, ← AddChar.map_nsmul_eq_pow]
      simp [nsmul_eq_mul]
    have hrooti :
        Matrix.fourierRoot (m + 1) ^ ((i : ℕ) * (m + 1)) = 1 := by
      rw [Nat.mul_comm, pow_mul, hroot, one_pow]
    have hexp : (i : ℕ) + (i : ℕ) * m = (i : ℕ) * (m + 1) := by ring
    calc
      Matrix.fourierMatrix (m + 1) i (finRotate (m + 1) (Fin.last m))
          = Matrix.fourierMatrix (m + 1) i 0 := by simp
      _ = Matrix.fourierRoot (m + 1) ^ ((i : ℕ) * (m + 1)) / Real.sqrt (m + 1) := by
            simp [Matrix.fourierMatrix_apply, hrooti]
      _ = Matrix.fourierSpectrum (m + 1) i * Matrix.fourierMatrix (m + 1) i (Fin.last m) := by
            rw [Matrix.fourierSpectrum_apply, Matrix.fourierMatrix_apply, Fin.val_last]
            simp only [div_eq_mul_inv]
            rw [← hexp, pow_add]
            ring_nf
            norm_num [Nat.cast_add]
  · have hrotate : (finRotate (m + 1) j : ℕ) = j + 1 := coe_finRotate_of_ne_last hj
    have hexp : (i : ℕ) * (j + 1) = (i : ℕ) * j + i := by ring
    calc
      Matrix.fourierMatrix (m + 1) i (finRotate (m + 1) j)
          =
            Matrix.fourierRoot (m + 1) ^ ((i : ℕ) * ↑(finRotate (m + 1) j)) /
              Real.sqrt (m + 1) := by
              simpa using Matrix.fourierMatrix_apply (m + 1) i (finRotate (m + 1) j)
      _ = Matrix.fourierRoot (m + 1) ^ ((i : ℕ) * (j + 1)) / Real.sqrt (m + 1) := by
            rw [hrotate]
      _ = Matrix.fourierSpectrum (m + 1) i * Matrix.fourierMatrix (m + 1) i j := by
            rw [Matrix.fourierSpectrum_apply, Matrix.fourierMatrix_apply]
            simp only [div_eq_mul_inv]
            rw [hexp, pow_add]
            ring_nf
            norm_num [Nat.cast_add]

/-- Helper for Notation 5.2.2-extra-3: left multiplication by the normalized Fourier matrix turns
the `m`th power of the Chapter 5 right shift into diagonal multiplication by
`Matrix.fourierSpectrum n ^ m`. -/
theorem fourier_mul_rightShiftPow_eq_diagonal_mul_fourier (n : ℕ) [NeZero n] (m : ℕ) :
    Matrix.fourierMatrix n * (Matrix.circulantRightShift (α := ℂ) n ^ m) =
      Matrix.diagonal (fun i ↦ Matrix.fourierSpectrum n i ^ m) * Matrix.fourierMatrix n := by
  induction m with
  | zero =>
      -- At exponent zero, both sides reduce to the identity action on the Fourier matrix.
      simp
  | succ m ih =>
      -- One more right-shift factor multiplies the Fourier diagonal by one more spectrum factor.
      calc
        Matrix.fourierMatrix n * (Matrix.circulantRightShift (α := ℂ) n ^ (m + 1))
          = (Matrix.fourierMatrix n * (Matrix.circulantRightShift (α := ℂ) n ^ m)) *
              Matrix.circulantRightShift (α := ℂ) n := by
                rw [pow_succ]
                simp [Matrix.mul_assoc]
        _ =
            (Matrix.diagonal (fun i ↦ Matrix.fourierSpectrum n i ^ m) * Matrix.fourierMatrix n) *
              Matrix.circulantRightShift (α := ℂ) n := by
                rw [ih]
        _ =
            Matrix.diagonal (fun i ↦ Matrix.fourierSpectrum n i ^ m) *
              (Matrix.fourierMatrix n * Matrix.circulantRightShift (α := ℂ) n) := by
                simp [Matrix.mul_assoc]
        _ =
            Matrix.diagonal (fun i ↦ Matrix.fourierSpectrum n i ^ m) *
              (Matrix.diagonal (Matrix.fourierSpectrum n) * Matrix.fourierMatrix n) := by
                rw [fourier_mul_rightShift_eq_diagonal_mul_fourier]
        _ =
            Matrix.diagonal (fun i ↦ Matrix.fourierSpectrum n i ^ (m + 1)) *
              Matrix.fourierMatrix n := by
                rw [← Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
                simp [pow_succ]

/-- Helper for Notation 5.2.2-extra-3: the product-index circulant basis vector at `(j, i)`
separates as the Kronecker product of the corresponding 1D right-shift powers. -/
theorem circulantPairSingle_eq_kronecker_rightShiftPow
    (n_x n_y : ℕ) [NeZero n_x] [NeZero n_y] (j : Fin n_y) (i : Fin n_x) :
    Matrix.circulant (Pi.single (j, i) (1 : ℂ)) =
      ((Matrix.circulantRightShift (α := ℂ) n_y) ^ (j : ℕ)) ⊗ₖ
        ((Matrix.circulantRightShift (α := ℂ) n_x) ^ (i : ℕ)) := by
  -- Rewrite each 1D shift power as its basis circulant and compare the product-index entries.
  rw [circulantRightShift_pow_eq_circulant_single_complex,
    circulantRightShift_pow_eq_circulant_single_complex]
  ext ab cd
  rcases ab with ⟨a, b⟩
  rcases cd with ⟨c, d⟩
  by_cases h1 : a - c = j
  · by_cases h2 : b - d = i
    · simp [Matrix.circulant_apply, h1, h2]
    · simp [Matrix.circulant_apply, h1, h2]
  · by_cases h2 : b - d = i
    · simp [Matrix.circulant_apply, h1, h2]
    · simp [Matrix.circulant_apply, h1, h2]

/-- Helper for Notation 5.2.2-extra-3: the product-index circulant generated by `Matrix.vec t`
is the sum of the basis circulants supported at each wrapped offset. -/
theorem sum_smul_circulantPairSingle_eq_circulantVec
    (n_x n_y : ℕ) [NeZero n_x] [NeZero n_y] (t : ℂ^[n_x, n_y]) :
    ∑ p : Fin n_y × Fin n_x, t p.2 p.1 • Matrix.circulant (Pi.single p (1 : ℂ)) =
      Matrix.circulant t.vec := by
  classical
  -- Pull `Matrix.circulant` through the finite sum, then collapse the product-index basis
  -- expansion.
  have hsum :
      ∀ s : Finset (Fin n_y × Fin n_x),
        Finset.sum s (fun p ↦ t p.2 p.1 • Matrix.circulant (Pi.single p (1 : ℂ))) =
          Matrix.circulant (Finset.sum s (fun p ↦ t p.2 p.1 • Pi.single p (1 : ℂ))) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        simp [Matrix.circulant_zero]
    | @insert a s ha ih =>
        simp [ha, ih, Matrix.circulant_add, Matrix.circulant_smul]
  calc
    ∑ p : Fin n_y × Fin n_x, t p.2 p.1 • Matrix.circulant (Pi.single p (1 : ℂ))
        = Matrix.circulant (∑ p : Fin n_y × Fin n_x, t p.2 p.1 • Pi.single p (1 : ℂ)) := by
            simpa using hsum Finset.univ
    _ = Matrix.circulant t.vec := by
        ext ab cd
        rw [Matrix.circulant_apply, Matrix.circulant_apply, Finset.sum_apply]
        simp [Pi.smul_apply, Pi.single_apply]

/-- Helper for Notation 5.2.2-extra-3: the exponential kernel in `Matrix.fft2_apply` separates
into the product of the local 1D Fourier spectra indexed by the product coordinates. -/
theorem fft2Kernel_eq_pairFourierSpectrum
    (n_x n_y : ℕ) [NeZero n_x] [NeZero n_y]
    (i i' : Fin n_x) (j j' : Fin n_y) :
    Complex.exp
      (-Complex.I * 2 * Real.pi *
        ((((i : ℕ) * (i' : ℕ) : ℂ) / n_x) + (((j : ℕ) * (j' : ℕ) : ℂ) / n_y))) =
      Matrix.fourierSpectrum n_y j ^ (j' : ℕ) *
        Matrix.fourierSpectrum n_x i ^ (i' : ℕ) := by
  have hnx : (n_x : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.pos_of_neZero n_x).ne'
  have hny : (n_y : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.pos_of_neZero n_y).ne'
  have hx :
      Matrix.fourierSpectrum n_x i ^ (i' : ℕ) =
        Complex.exp (((i : ℕ) * (i' : ℕ) : ℂ) * (-Complex.I * 2 * Real.pi / n_x)) := by
    rw [Matrix.fourierSpectrum_apply, ← pow_mul, Matrix.fourierRoot_eq_exp, ← Complex.exp_nat_mul]
    congr 1
    field_simp [hnx]
    norm_num [Nat.cast_mul]
  have hy :
      Matrix.fourierSpectrum n_y j ^ (j' : ℕ) =
        Complex.exp (((j : ℕ) * (j' : ℕ) : ℂ) * (-Complex.I * 2 * Real.pi / n_y)) := by
    rw [Matrix.fourierSpectrum_apply, ← pow_mul, Matrix.fourierRoot_eq_exp, ← Complex.exp_nat_mul]
    congr 1
    field_simp [hny]
    norm_num [Nat.cast_mul]
  have hphase :
      (((j : ℕ) * (j' : ℕ) : ℂ) * (-Complex.I * 2 * Real.pi / n_y)) +
          (((i : ℕ) * (i' : ℕ) : ℂ) * (-Complex.I * 2 * Real.pi / n_x)) =
        -Complex.I * 2 * Real.pi *
          ((((i : ℕ) * (i' : ℕ) : ℂ) / n_x) + (((j : ℕ) * (j' : ℕ) : ℂ) / n_y)) := by
    field_simp [hnx, hny]
    ring
  -- Rewrite the source exponential into a sum of 1D phases, then refold each phase as a spectrum.
  calc
    Complex.exp
        (-Complex.I * 2 * Real.pi *
          ((((i : ℕ) * (i' : ℕ) : ℂ) / n_x) + (((j : ℕ) * (j' : ℕ) : ℂ) / n_y)))
      = Complex.exp
          ((((j : ℕ) * (j' : ℕ) : ℂ) * (-Complex.I * 2 * Real.pi / n_y)) +
            (((i : ℕ) * (i' : ℕ) : ℂ) * (-Complex.I * 2 * Real.pi / n_x))) := by
              congr 1
              exact hphase.symm
    _ =
        Complex.exp (((j : ℕ) * (j' : ℕ) : ℂ) * (-Complex.I * 2 * Real.pi / n_y)) *
          Complex.exp (((i : ℕ) * (i' : ℕ) : ℂ) * (-Complex.I * 2 * Real.pi / n_x)) := by
            rw [Complex.exp_add]
    _ = Matrix.fourierSpectrum n_y j ^ (j' : ℕ) *
          Matrix.fourierSpectrum n_x i ^ (i' : ℕ) := by
            rw [← hy, ← hx]

/-- Helper for Notation 5.2.2-extra-3: one product-index circulant basis matrix is diagonalized by
the Kronecker Fourier matrix with the separated 2D Fourier spectrum on the diagonal. -/
theorem kronFourier_mul_circulantPairSingle_eq_diagonal_mul_kronFourier
    (n_x n_y : ℕ) [NeZero n_x] [NeZero n_y] (j : Fin n_y) (i : Fin n_x) :
    ((Matrix.fourierMatrix n_y) ⊗ₖ (Matrix.fourierMatrix n_x)) *
        Matrix.circulant (Pi.single (j, i) (1 : ℂ)) =
      Matrix.diagonal (fun q : Fin n_y × Fin n_x ↦
          Matrix.fourierSpectrum n_y q.1 ^ (j : ℕ) *
            Matrix.fourierSpectrum n_x q.2 ^ (i : ℕ)) *
        ((Matrix.fourierMatrix n_y) ⊗ₖ (Matrix.fourierMatrix n_x)) := by
  -- Separate the product-index basis circulant into 1D shifts and diagonalize each factor.
  rw [circulantPairSingle_eq_kronecker_rightShiftPow]
  calc
    ((Matrix.fourierMatrix n_y) ⊗ₖ (Matrix.fourierMatrix n_x)) *
        (((Matrix.circulantRightShift (α := ℂ) n_y) ^ (j : ℕ)) ⊗ₖ
          ((Matrix.circulantRightShift (α := ℂ) n_x) ^ (i : ℕ)))
      =
        (Matrix.fourierMatrix n_y * ((Matrix.circulantRightShift (α := ℂ) n_y) ^ (j : ℕ))) ⊗ₖ
          (Matrix.fourierMatrix n_x * ((Matrix.circulantRightShift (α := ℂ) n_x) ^ (i : ℕ))) := by
            rw [Matrix.mul_kronecker_mul]
    _ =
        (Matrix.diagonal (fun q : Fin n_y ↦ Matrix.fourierSpectrum n_y q ^ (j : ℕ)) *
            Matrix.fourierMatrix n_y) ⊗ₖ
          (Matrix.diagonal (fun q : Fin n_x ↦ Matrix.fourierSpectrum n_x q ^ (i : ℕ)) *
            Matrix.fourierMatrix n_x) := by
              rw [fourier_mul_rightShiftPow_eq_diagonal_mul_fourier,
                fourier_mul_rightShiftPow_eq_diagonal_mul_fourier]
    _ =
        (Matrix.diagonal (fun q : Fin n_y ↦ Matrix.fourierSpectrum n_y q ^ (j : ℕ)) ⊗ₖ
            Matrix.diagonal (fun q : Fin n_x ↦ Matrix.fourierSpectrum n_x q ^ (i : ℕ))) *
          ((Matrix.fourierMatrix n_y) ⊗ₖ (Matrix.fourierMatrix n_x)) := by
            rw [← Matrix.mul_kronecker_mul]
    _ =
        Matrix.diagonal (fun q : Fin n_y × Fin n_x ↦
            Matrix.fourierSpectrum n_y q.1 ^ (j : ℕ) *
              Matrix.fourierSpectrum n_x q.2 ^ (i : ℕ)) *
          ((Matrix.fourierMatrix n_y) ⊗ₖ (Matrix.fourierMatrix n_x)) := by
            rw [Matrix.diagonal_kronecker_diagonal]

/-- Helper for Notation 5.2.2-extra-3: evaluating `Matrix.vec (Matrix.fft2 n_x n_y t)` at a
product index gives the finite sum of separated 1D Fourier spectra against the entries of `t`. -/
theorem vec_fft2_apply_eq_sum_shiftSpectra
    (n_x n_y : ℕ) [NeZero n_x] [NeZero n_y] (t : ℂ^[n_x, n_y])
    (q : Fin n_y × Fin n_x) :
    Matrix.vec (Matrix.fft2 n_x n_y t) q =
      ∑ p : Fin n_y × Fin n_x,
        t p.2 p.1 *
          (Matrix.fourierSpectrum n_y q.1 ^ (p.1 : ℕ) *
            Matrix.fourierSpectrum n_x q.2 ^ (p.2 : ℕ)) := by
  rcases q with ⟨j, i⟩
  -- Expand `Matrix.fft2` at the product index `(j, i)` and rewrite the kernel into separated
  -- 1D Fourier spectra before repacking the nested sum over the product type.
  calc
    Matrix.vec (Matrix.fft2 n_x n_y t) (j, i)
      = ∑ i' : Fin n_x, ∑ j' : Fin n_y,
          t i' j' *
            Complex.exp
              (-Complex.I * 2 * Real.pi *
                ((((i : ℕ) * (i' : ℕ) : ℂ) / n_x) +
                  (((j : ℕ) * (j' : ℕ) : ℂ) / n_y))) := by
                    simpa [Matrix.vec] using Matrix.fft2_apply n_x n_y t i j
    _ = ∑ j' : Fin n_y, ∑ i' : Fin n_x,
          t i' j' *
            Complex.exp
              (-Complex.I * 2 * Real.pi *
                ((((i : ℕ) * (i' : ℕ) : ℂ) / n_x) +
                  (((j : ℕ) * (j' : ℕ) : ℂ) / n_y))) := by
                    rw [Finset.sum_comm]
    _ = ∑ p : Fin n_y × Fin n_x,
          t p.2 p.1 *
            Complex.exp
              (-Complex.I * 2 * Real.pi *
                ((((i : ℕ) * (p.2 : ℕ) : ℂ) / n_x) +
                  (((j : ℕ) * (p.1 : ℕ) : ℂ) / n_y))) := by
                    rw [← Fintype.sum_prod_type']
    _ = ∑ p : Fin n_y × Fin n_x,
          t p.2 p.1 *
            (Matrix.fourierSpectrum n_y j ^ (p.1 : ℕ) *
              Matrix.fourierSpectrum n_x i ^ (p.2 : ℕ)) := by
                refine Finset.sum_congr rfl fun p _ ↦ ?_
                rcases p with ⟨j', i'⟩
                rw [fft2Kernel_eq_pairFourierSpectrum]

/-- Helper for Notation 5.2.2-extra-3: the diagonal matrix built from `Matrix.vec (Matrix.fft2 t)`
is the sum of the separated Fourier-spectrum diagonal basis matrices weighted by the entries of
`t`. -/
theorem sum_smul_shiftSpectraDiagonal_eq_diagonal_vec_fft2
    (n_x n_y : ℕ) [NeZero n_x] [NeZero n_y] (t : ℂ^[n_x, n_y]) :
    ∑ p : Fin n_y × Fin n_x,
      t p.2 p.1 • Matrix.diagonal (fun q : Fin n_y × Fin n_x ↦
        Matrix.fourierSpectrum n_y q.1 ^ (p.1 : ℕ) *
          Matrix.fourierSpectrum n_x q.2 ^ (p.2 : ℕ)) =
      Matrix.diagonal (Matrix.vec (Matrix.fft2 n_x n_y t)) := by
  ext q r
  by_cases hqr : q = r
  · subst hqr
    -- On the diagonal, the matrix sum is exactly the normalized `Matrix.vec (Matrix.fft2 t)` entry.
    rw [Matrix.sum_apply, Matrix.diagonal_apply]
    simpa [Matrix.diagonal_apply] using (vec_fft2_apply_eq_sum_shiftSpectra n_x n_y t q).symm
  · -- Off the diagonal, every diagonal basis term vanishes.
    simp [Matrix.sum_apply, hqr]

/-- Helper for Notation 5.2.2-extra-3: the Kronecker Fourier matrix diagonalizes the product-index
circulant generated by `Matrix.vec t`, with diagonal entries `Matrix.vec (Matrix.fft2 t)`. -/
theorem kronFourier_mul_circulantVec_eq_diagonal_vec_fft2_mul
    (n_x n_y : ℕ) [NeZero n_x] [NeZero n_y] (t : ℂ^[n_x, n_y]) :
    ((Matrix.fourierMatrix n_y) ⊗ₖ (Matrix.fourierMatrix n_x)) * Matrix.circulant t.vec =
      Matrix.diagonal (Matrix.vec (Matrix.fft2 n_x n_y t)) *
        ((Matrix.fourierMatrix n_y) ⊗ₖ (Matrix.fourierMatrix n_x)) := by
  -- Expand the product-index circulant into basis terms, diagonalize each basis term, then factor
  -- the common Kronecker Fourier matrix on the right.
  calc
    ((Matrix.fourierMatrix n_y) ⊗ₖ (Matrix.fourierMatrix n_x)) * Matrix.circulant t.vec
      =
        ((Matrix.fourierMatrix n_y) ⊗ₖ (Matrix.fourierMatrix n_x)) *
          ∑ p : Fin n_y × Fin n_x, t p.2 p.1 • Matrix.circulant (Pi.single p (1 : ℂ)) := by
            rw [sum_smul_circulantPairSingle_eq_circulantVec]
    _ =
        ∑ p : Fin n_y × Fin n_x,
          t p.2 p.1 •
            (((Matrix.fourierMatrix n_y) ⊗ₖ (Matrix.fourierMatrix n_x)) *
              Matrix.circulant (Pi.single p (1 : ℂ))) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun p _ ↦ ?_
              rw [Matrix.mul_smul]
    _ =
        ∑ p : Fin n_y × Fin n_x,
          t p.2 p.1 •
            (Matrix.diagonal (fun q : Fin n_y × Fin n_x ↦
              Matrix.fourierSpectrum n_y q.1 ^ (p.1 : ℕ) *
                Matrix.fourierSpectrum n_x q.2 ^ (p.2 : ℕ)) *
              ((Matrix.fourierMatrix n_y) ⊗ₖ (Matrix.fourierMatrix n_x))) := by
              refine Finset.sum_congr rfl fun p _ ↦ ?_
              rcases p with ⟨j, i⟩
              rw [kronFourier_mul_circulantPairSingle_eq_diagonal_mul_kronFourier]
    _ =
        (∑ p : Fin n_y × Fin n_x,
          t p.2 p.1 • Matrix.diagonal (fun q : Fin n_y × Fin n_x ↦
            Matrix.fourierSpectrum n_y q.1 ^ (p.1 : ℕ) *
              Matrix.fourierSpectrum n_x q.2 ^ (p.2 : ℕ))) *
          ((Matrix.fourierMatrix n_y) ⊗ₖ (Matrix.fourierMatrix n_x)) := by
            simpa using
              (Matrix.sum_mul (s := Finset.univ)
                (f := fun p : Fin n_y × Fin n_x ↦
                  t p.2 p.1 • Matrix.diagonal (fun q : Fin n_y × Fin n_x ↦
                    Matrix.fourierSpectrum n_y q.1 ^ (p.1 : ℕ) *
                      Matrix.fourierSpectrum n_x q.2 ^ (p.2 : ℕ)))
                (((Matrix.fourierMatrix n_y) ⊗ₖ (Matrix.fourierMatrix n_x)))).symm
    _ =
        Matrix.diagonal (Matrix.vec (Matrix.fft2 n_x n_y t)) *
          ((Matrix.fourierMatrix n_y) ⊗ₖ (Matrix.fourierMatrix n_x)) := by
            rw [sum_smul_shiftSpectraDiagonal_eq_diagonal_vec_fft2]

/-- Notation 5.2.2-extra-3. Equation (5.41): convolving `f`
with the periodic extension `t^ext` of `t` agrees with applying `ifft2` to the
pointwise product of `fft2 t` and `fft2 f`. -/
theorem periodicExtension_discreteConvolution2D_eq_ifft2_hadamard_fft2
    (n_x n_y : ℕ) [NeZero n_x] [NeZero n_y]
    (t f : ℂ^[n_x, n_y]) :
    Matrix.discreteConvolution2D
        (Matrix.periodicExtension n_x.pos_of_neZero n_y.pos_of_neZero t) f =
      Matrix.ifft2 n_x n_y
        (Matrix.hadamard (Matrix.fft2 n_x n_y t) (Matrix.fft2 n_x n_y f)) := by
  -- Route correction: the direct `Prop_5_28`/`Prop_5_31` path is unavailable here, so reduce the
  -- theorem to a vec/Kronecker spectral identity inside this file instead.
  rw [← Matrix.vec_inj]
  rw [Matrix.discreteConvolution2D_def, Matrix.vec_of_swap]
  let F : Matrix (Fin n_y × Fin n_x) (Fin n_y × Fin n_x) ℂ :=
    (Matrix.fourierMatrix n_y) ⊗ₖ (Matrix.fourierMatrix n_x)
  let α : ℂ := (Real.sqrt n_x : ℂ) * Real.sqrt n_y
  -- Rewrite the convolution side to the product-index circulant action.
  rw [periodicExtension_httb_eq_circulantVec n_x.pos_of_neZero n_y.pos_of_neZero]
  have hsqrt_ne : α ≠ 0 := by
    have hx : (Real.sqrt n_x : ℂ) ≠ 0 := by
      exact_mod_cast
        (Real.sqrt_ne_zero'.2 (show (0 : ℝ) < n_x by exact_mod_cast Nat.pos_of_neZero n_x))
    have hy : (Real.sqrt n_y : ℂ) ≠ 0 := by
      exact_mod_cast
        (Real.sqrt_ne_zero'.2 (show (0 : ℝ) < n_y by exact_mod_cast Nat.pos_of_neZero n_y))
    exact mul_ne_zero hx hy
  have hunit : Fᴴ * F = 1 := by
    -- The Kronecker product of the two normalized Fourier matrices is still unitary.
    calc
      Fᴴ * F
        =
          (((Matrix.fourierMatrix n_y)ᴴ) ⊗ₖ ((Matrix.fourierMatrix n_x)ᴴ)) *
            (((Matrix.fourierMatrix n_y) ⊗ₖ (Matrix.fourierMatrix n_x))) := by
              simp [F, Matrix.conjTranspose_kronecker]
      _ =
          (((Matrix.fourierMatrix n_y)ᴴ * Matrix.fourierMatrix n_y) ⊗ₖ
            (((Matrix.fourierMatrix n_x)ᴴ * Matrix.fourierMatrix n_x))) := by
              rw [Matrix.mul_kronecker_mul]
      _ = (1 : Matrix (Fin n_y) (Fin n_y) ℂ) ⊗ₖ (1 : Matrix (Fin n_x) (Fin n_x) ℂ) := by
              rw [Matrix.fourierMatrix_conjTranspose_mul, Matrix.fourierMatrix_conjTranspose_mul]
      _ = 1 := by
              rw [Matrix.one_kronecker_one]
  have hvec_fft_f : Matrix.vec (Matrix.fft2 n_x n_y f) = (α • F) *ᵥ f.vec := by
    -- Refold the existing vec-level `fft2` identity into the local `F`/`α` notation.
    simpa [F, α] using vec_fft2_eq_kronFourier_mulVec n_x n_y f
  have hvec_ifft2 :
      Matrix.vec
          (Matrix.ifft2 n_x n_y
            (Matrix.hadamard (Matrix.fft2 n_x n_y t) (Matrix.fft2 n_x n_y f))) =
        Fᴴ *ᵥ
          (Matrix.diagonal (Matrix.vec (Matrix.fft2 n_x n_y t)) *ᵥ (F *ᵥ f.vec)) := by
    -- Rewrite `ifft2` and the Hadamard product in vec form, then cancel the forward/inverse
    -- normalization scalars around the common Fourier action.
    calc
      Matrix.vec
          (Matrix.ifft2 n_x n_y
            (Matrix.hadamard (Matrix.fft2 n_x n_y t) (Matrix.fft2 n_x n_y f)))
        = ((α⁻¹) • Fᴴ) *ᵥ
            Matrix.vec (Matrix.hadamard (Matrix.fft2 n_x n_y t) (Matrix.fft2 n_x n_y f)) := by
              simpa [F, α, Matrix.conjTranspose_kronecker] using
                vec_ifft2_eq_kronConjFourier_mulVec n_x n_y
                  (Matrix.hadamard (Matrix.fft2 n_x n_y t) (Matrix.fft2 n_x n_y f))
      _ =
          ((α⁻¹) • Fᴴ) *ᵥ
            (Matrix.diagonal (Matrix.vec (Matrix.fft2 n_x n_y t)) *ᵥ
              Matrix.vec (Matrix.fft2 n_x n_y f)) := by
                rw [vec_hadamard_eq_diagonal_mulVec]
      _ =
          ((α⁻¹) • Fᴴ) *ᵥ
            (Matrix.diagonal (Matrix.vec (Matrix.fft2 n_x n_y t)) *ᵥ ((α • F) *ᵥ f.vec)) := by
              rw [hvec_fft_f]
      _ =
          ((α⁻¹) • Fᴴ) *ᵥ
            (Matrix.diagonal (Matrix.vec (Matrix.fft2 n_x n_y t)) *ᵥ (α • (F *ᵥ f.vec))) := by
              have hinner : (α • F) *ᵥ f.vec = α • (F *ᵥ f.vec) := by
                rw [Matrix.smul_mulVec]
              rw [hinner]
      _ =
          ((α⁻¹) • Fᴴ) *ᵥ
            (α • (Matrix.diagonal (Matrix.vec (Matrix.fft2 n_x n_y t)) *ᵥ (F *ᵥ f.vec))) := by
              have hdiag :
                  Matrix.diagonal (Matrix.vec (Matrix.fft2 n_x n_y t)) *ᵥ (α • (F *ᵥ f.vec)) =
                    α • (Matrix.diagonal (Matrix.vec (Matrix.fft2 n_x n_y t)) *ᵥ (F *ᵥ f.vec)) := by
                      rw [Matrix.mulVec_smul]
              rw [hdiag]
      _ = Fᴴ *ᵥ (Matrix.diagonal (Matrix.vec (Matrix.fft2 n_x n_y t)) *ᵥ (F *ᵥ f.vec)) := by
            rw [Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul]
            simp [hsqrt_ne]
  -- Use the product-Fourier semiconjugation to move the circulant convolution matrix into
  -- diagonal Fourier coordinates, then identify the result with the `ifft2` vec formula above.
  calc
    Matrix.circulant t.vec *ᵥ f.vec = (1 * Matrix.circulant t.vec) *ᵥ f.vec := by
      simp
    _ = ((Fᴴ * F) * Matrix.circulant t.vec) *ᵥ f.vec := by
      rw [hunit]
    _ = (Fᴴ * (F * Matrix.circulant t.vec)) *ᵥ f.vec := by
      simp [Matrix.mul_assoc]
    _ =
        (Fᴴ * (Matrix.diagonal (Matrix.vec (Matrix.fft2 n_x n_y t)) * F)) *ᵥ f.vec := by
          rw [kronFourier_mul_circulantVec_eq_diagonal_vec_fft2_mul]
    _ = (Fᴴ * Matrix.diagonal (Matrix.vec (Matrix.fft2 n_x n_y t)) * F) *ᵥ f.vec := by
          simp [Matrix.mul_assoc]
    _ = Fᴴ *ᵥ (Matrix.diagonal (Matrix.vec (Matrix.fft2 n_x n_y t)) *ᵥ (F *ᵥ f.vec)) := by
          simp [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    _ =
        Matrix.vec
          (Matrix.ifft2 n_x n_y
            (Matrix.hadamard (Matrix.fft2 n_x n_y t) (Matrix.fft2 n_x n_y f))) := by
              simpa using hvec_ifft2.symm

end Matrix
