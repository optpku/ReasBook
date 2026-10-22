/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Definition_5_25.Array
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Definition_5_27.BCCB
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Notation_5_2_2

public section

open scoped Complex.FiniteDimensional Kronecker

noncomputable section

namespace Matrix

/-- The Fourier-side denominator in Algorithm 5.3.1. -/
def bccbTikhonovDenominator
    {n_x n_y : ℕ} [NeZero n_x] [NeZero n_y]
    (α : ℝ)
    (t ℓ : ℂ^[n_x, n_y]) :
    ℂ^[n_x, n_y] :=
  let tHat := fft2 n_x n_y t
  hadamard (fun i j ↦ star (tHat i j)) tHat + (α : ℂ) • fft2 n_x n_y ℓ

/-- Algorithm 5.3.1. The BCCB Tikhonov solution array obtained by taking the
two-dimensional Fourier transforms of `t`, `ℓ`, and `d`, forming the
entrywise quotient with numerator
`hadamard (fun i j ↦ star (tHat i j)) dHat` and denominator
`bccbTikhonovDenominator α t ℓ`, where the source notation `|tHat|^2` is
formalized as `hadamard (fun i j ↦ star (tHat i j)) tHat`, and then applying
`ifft2`. -/
def bccbTikhonovRegularization
    {n_x n_y : ℕ} [NeZero n_x] [NeZero n_y]
    (α : ℝ)
    (t ℓ d : ℂ^[n_x, n_y]) :
    ℂ^[n_x, n_y] :=
  let tHat := fft2 n_x n_y t
  let dHat := fft2 n_x n_y d
  let numer := hadamard (fun i j ↦ star (tHat i j)) dHat
  ifft2 n_x n_y
    (fun i j ↦ numer i j / bccbTikhonovDenominator α t ℓ i j)

/-- The defining Fourier-domain formula for `bccbTikhonovRegularization`. -/
theorem bccbTikhonovRegularization_def
    {n_x n_y : ℕ} [NeZero n_x] [NeZero n_y]
    (α : ℝ)
    (t ℓ d : ℂ^[n_x, n_y]) :
    bccbTikhonovRegularization α t ℓ d =
      let tHat := fft2 n_x n_y t
      let dHat := fft2 n_x n_y d
      let numer := hadamard (fun i j ↦ star (tHat i j)) dHat
      ifft2 n_x n_y
        (fun i j ↦ numer i j / bccbTikhonovDenominator α t ℓ i j) := by
  simp [bccbTikhonovRegularization]

/-- The vectorized output of `bccbTikhonovRegularization`, matching the final
source vectorization step `vec f`. -/
abbrev bccbTikhonovRegularizationVec
    {n_x n_y : ℕ} [NeZero n_x] [NeZero n_y]
    (α : ℝ)
    (t ℓ d : ℂ^[n_x, n_y]) :
    Fin n_y × Fin n_x → ℂ :=
  vec (bccbTikhonovRegularization α t ℓ d)

/-- The defining formula for `bccbTikhonovRegularizationVec`. -/
theorem bccbTikhonovRegularizationVec_def
    {n_x n_y : ℕ} [NeZero n_x] [NeZero n_y]
    (α : ℝ)
    (t ℓ d : ℂ^[n_x, n_y]) :
    bccbTikhonovRegularizationVec α t ℓ d =
      vec (bccbTikhonovRegularization α t ℓ d) := rfl

/-- Evaluating `bccbTikhonovRegularizationVec` at `(j, i)` returns the `(i, j)`
entry of the Tikhonov solution array. -/
theorem bccbTikhonovRegularizationVec_apply
    {n_x n_y : ℕ} [NeZero n_x] [NeZero n_y]
    (α : ℝ)
    (t ℓ d : ℂ^[n_x, n_y])
    (q : Fin n_y × Fin n_x) :
    bccbTikhonovRegularizationVec α t ℓ d q =
      bccbTikhonovRegularization α t ℓ d q.2 q.1 := by
  rcases q with ⟨j, i⟩
  rfl

/-- Helper for Algorithm 5.3.1: vectorizing `bccbTikhonovDenominator` exposes the
Fourier-side diagonal multiplier entrywise. -/
theorem bccbTikhonovDenominator_vec
    {n_x n_y : ℕ} [NeZero n_x] [NeZero n_y]
    (α : ℝ)
    (t ℓ : ℂ^[n_x, n_y]) :
    vec (bccbTikhonovDenominator α t ℓ) =
      fun q ↦
        star (vec (fft2 n_x n_y t) q) * vec (fft2 n_x n_y t) q +
          (α : ℂ) * vec (fft2 n_x n_y ℓ) q := by
  ext q
  rcases q with ⟨j, i⟩
  -- Unfold the denominator and translate the vector index back to matrix coordinates.
  simp [bccbTikhonovDenominator, Matrix.hadamard_apply, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Algorithm 5.3.1: the Kronecker Fourier matrix intertwines a BCCB
operator with the diagonal matrix of its `fft2` coefficients. -/
theorem bccbFourierIntertwining
    {n_x n_y : ℕ} [NeZero n_x] [NeZero n_y]
    (c : ℂ^[n_x, n_y]) :
    ((fourierMatrix n_y) ⊗ₖ (fourierMatrix n_x)) * bccb c =
      diagonal (vec (fft2 n_x n_y c)) * ((fourierMatrix n_y) ⊗ₖ (fourierMatrix n_x)) := by
  -- Rewrite `bccb` as the product-index circulant and reuse the existing Fourier diagonalization.
  rw [bccb_eq_circulant_vec]
  simpa using kronFourier_mul_circulantVec_eq_diagonal_vec_fft2_mul n_x n_y c

/-- Helper for Algorithm 5.3.1: `bccb c` is diagonalized by the Kronecker Fourier
matrix with diagonal `vec (fft2 n_x n_y c)`. -/
theorem bccbFourierDiagonalization
    {n_x n_y : ℕ} [NeZero n_x] [NeZero n_y]
    (c : ℂ^[n_x, n_y]) :
    bccb c =
      (((fourierMatrix n_y) ⊗ₖ (fourierMatrix n_x))ᴴ) *
        diagonal (vec (fft2 n_x n_y c)) *
        ((fourierMatrix n_y) ⊗ₖ (fourierMatrix n_x)) := by
  let F : Matrix (Fin n_y × Fin n_x) (Fin n_y × Fin n_x) ℂ :=
    (fourierMatrix n_y) ⊗ₖ (fourierMatrix n_x)
  have hdiag :
      F * bccb c =
        diagonal (vec (fft2 n_x n_y c)) * F := by
    -- The previous helper gives the Fourier intertwining identity in the local notation.
    simpa [F] using bccbFourierIntertwining c
  have hFhF : Fᴴ * F = 1 := by
    -- The Kronecker product of the normalized Fourier matrices is unitary.
    calc
      Fᴴ * F
          =
            (((fourierMatrix n_y)ᴴ) ⊗ₖ ((fourierMatrix n_x)ᴴ)) *
              (((fourierMatrix n_y) ⊗ₖ (fourierMatrix n_x))) := by
                simp [F, Matrix.conjTranspose_kronecker]
      _ =
          (((fourierMatrix n_y)ᴴ * fourierMatrix n_y) ⊗ₖ
            (((fourierMatrix n_x)ᴴ * fourierMatrix n_x))) := by
              rw [Matrix.mul_kronecker_mul]
      _ = (1 : Matrix (Fin n_y) (Fin n_y) ℂ) ⊗ₖ (1 : Matrix (Fin n_x) (Fin n_x) ℂ) := by
              rw [fourierMatrix_conjTranspose_mul, fourierMatrix_conjTranspose_mul]
      _ = 1 := by
              rw [Matrix.one_kronecker_one]
  -- Insert `Fᴴ * F = 1` and then replace `F * bccb c` by the diagonalized form.
  calc
    bccb c = 1 * bccb c := by simp
    _ = (Fᴴ * F) * bccb c := by rw [hFhF]
    _ = Fᴴ * (F * bccb c) := by rw [Matrix.mul_assoc]
    _ = Fᴴ * (diagonal (vec (fft2 n_x n_y c)) * F) := by rw [hdiag]
    _ = Fᴴ * diagonal (vec (fft2 n_x n_y c)) * F := by rw [Matrix.mul_assoc]

/-- The vector produced by `bccbTikhonovRegularization` satisfies the BCCB
normal equation with right-hand side `mulVec (bccb t)ᴴ (vec d)` when
`bccbTikhonovDenominator α t ℓ` is nonzero entrywise. -/
theorem bccbTikhonovRegularizationVec_spec
    {n_x n_y : ℕ} [NeZero n_x] [NeZero n_y]
    (α : ℝ)
    (t ℓ d : ℂ^[n_x, n_y])
    (h_denom : ∀ i j, bccbTikhonovDenominator α t ℓ i j ≠ 0) :
    mulVec (((bccb t)ᴴ * bccb t) + (α : ℂ) • bccb ℓ)
      (bccbTikhonovRegularizationVec α t ℓ d) =
        mulVec (bccb t)ᴴ (vec d) := by
  let F : Matrix (Fin n_y × Fin n_x) (Fin n_y × Fin n_x) ℂ :=
    (fourierMatrix n_y) ⊗ₖ (fourierMatrix n_x)
  let σ : ℂ := (Real.sqrt n_x : ℂ) * Real.sqrt n_y
  let tHatVec : Fin n_y × Fin n_x → ℂ := vec (fft2 n_x n_y t)
  let ellHatVec : Fin n_y × Fin n_x → ℂ := vec (fft2 n_x n_y ℓ)
  let dHatVec : Fin n_y × Fin n_x → ℂ := vec (fft2 n_x n_y d)
  let denomVec : Fin n_y × Fin n_x → ℂ := vec (bccbTikhonovDenominator α t ℓ)
  let numerVec : Fin n_y × Fin n_x → ℂ := fun q ↦ star (tHatVec q) * dHatVec q
  let quotVec : Fin n_y × Fin n_x → ℂ := fun q ↦ numerVec q / denomVec q
  let quotArray : ℂ^[n_x, n_y] := fun i j ↦
    hadamard (fun i j ↦ star ((fft2 n_x n_y t) i j)) (fft2 n_x n_y d) i j /
      bccbTikhonovDenominator α t ℓ i j
  let solVec : Fin n_y × Fin n_x → ℂ := bccbTikhonovRegularizationVec α t ℓ d
  have hsigma_ne : σ ≠ 0 := by
    have hx : (Real.sqrt n_x : ℂ) ≠ 0 := by
      exact_mod_cast
        (Real.sqrt_ne_zero'.2 (show (0 : ℝ) < n_x by exact_mod_cast Nat.pos_of_neZero n_x))
    have hy : (Real.sqrt n_y : ℂ) ≠ 0 := by
      exact_mod_cast
        (Real.sqrt_ne_zero'.2 (show (0 : ℝ) < n_y by exact_mod_cast Nat.pos_of_neZero n_y))
    exact mul_ne_zero hx hy
  have hFhF : Fᴴ * F = 1 := by
    -- The Fourier Kronecker matrix is unitary.
    calc
      Fᴴ * F
          =
            (((fourierMatrix n_y)ᴴ) ⊗ₖ ((fourierMatrix n_x)ᴴ)) *
              (((fourierMatrix n_y) ⊗ₖ (fourierMatrix n_x))) := by
                simp [F, Matrix.conjTranspose_kronecker]
      _ =
          (((fourierMatrix n_y)ᴴ * fourierMatrix n_y) ⊗ₖ
            (((fourierMatrix n_x)ᴴ * fourierMatrix n_x))) := by
              rw [Matrix.mul_kronecker_mul]
      _ = (1 : Matrix (Fin n_y) (Fin n_y) ℂ) ⊗ₖ (1 : Matrix (Fin n_x) (Fin n_x) ℂ) := by
              rw [fourierMatrix_conjTranspose_mul, fourierMatrix_conjTranspose_mul]
      _ = 1 := by
              rw [Matrix.one_kronecker_one]
  have hFFh : F * Fᴴ = 1 := by
    exact Matrix.mem_unitaryGroup_iff.mp <| Matrix.mem_unitaryGroup_iff'.mpr hFhF
  have hbccb_t :
      bccb t = Fᴴ * diagonal tHatVec * F := by
    -- Reuse the local Fourier diagonalization helper for `t`.
    simpa [F, tHatVec] using bccbFourierDiagonalization t
  have hbccb_ell :
      bccb ℓ = Fᴴ * diagonal ellHatVec * F := by
    -- Reuse the same diagonalization for `ℓ`.
    simpa [F, ellHatVec] using bccbFourierDiagonalization ℓ
  have hF_mul_bccb_t :
      F * bccb t = diagonal tHatVec * F := by
    -- This is the direct intertwining form needed for the forward action.
    simpa [F, tHatVec] using bccbFourierIntertwining t
  have hF_mul_bccb_ell :
      F * bccb ℓ = diagonal ellHatVec * F := by
    -- The same intertwining identity applies to the regularization operator.
    simpa [F, ellHatVec] using bccbFourierIntertwining ℓ
  have hF_mul_bccbAdj_t :
      F * (bccb t)ᴴ = diagonal (star tHatVec) * F := by
    -- Conjugating the Fourier diagonalization of `bccb t` yields the adjoint action.
    calc
      F * (bccb t)ᴴ = F * (Fᴴ * diagonal tHatVec * F)ᴴ := by rw [hbccb_t]
      _ = F * (Fᴴ * (diagonal (star tHatVec) * F)) := by
            simp [Matrix.diagonal_conjTranspose, Matrix.mul_assoc]
      _ = (F * Fᴴ) * (diagonal (star tHatVec) * F) := by
            rw [← Matrix.mul_assoc]
      _ = diagonal (star tHatVec) * F := by rw [hFFh, Matrix.one_mul]
  have hvec_dHat :
      dHatVec = mulVec (σ • F) (vec d) := by
    -- Rewrite `fft2 d` into the local Fourier-matrix notation.
    simpa [F, σ, dHatVec] using vec_fft2_eq_kronFourier_mulVec n_x n_y d
  have hF_mul_vec_d :
      mulVec F (vec d) = σ⁻¹ • dHatVec := by
    -- Cancel the common Fourier normalization scalar.
    have htmp : σ⁻¹ • dHatVec = mulVec F (vec d) := by
      rw [hvec_dHat]
      rw [Matrix.smul_mulVec]
      simp [smul_smul, hsigma_ne]
    exact htmp.symm
  have hquot :
      vec quotArray =
        quotVec := by
    ext q
    rcases q with ⟨j, i⟩
    -- Unfold the quotient and normalize both vectorized coordinates.
    simp [quotArray, quotVec, numerVec, tHatVec, dHatVec, denomVec, Matrix.hadamard_apply]
  have hsol :
      solVec = mulVec ((σ⁻¹) • Fᴴ) quotVec := by
    -- Rewrite the algorithm definition into vectorized inverse-Fourier form.
    calc
      solVec = vec (bccbTikhonovRegularization α t ℓ d) := by rfl
      _ = vec (ifft2 n_x n_y quotArray) := by
            rw [bccbTikhonovRegularization_def]
      _ = mulVec ((σ⁻¹) • Fᴴ) (vec quotArray) := by
              simpa [F, σ, Matrix.conjTranspose_kronecker] using
                vec_ifft2_eq_kronConjFourier_mulVec n_x n_y quotArray
      _ = mulVec ((σ⁻¹) • Fᴴ) quotVec := by rw [hquot]
  have hF_mul_sol :
      mulVec F solVec = σ⁻¹ • quotVec := by
    -- Apply the forward Fourier matrix to the inverse-Fourier formula and use unitarity.
    calc
      mulVec F solVec = mulVec F (mulVec ((σ⁻¹) • Fᴴ) quotVec) := by rw [hsol]
      _ = mulVec F (σ⁻¹ • mulVec Fᴴ quotVec) := by rw [Matrix.smul_mulVec]
      _ = σ⁻¹ • mulVec F (mulVec Fᴴ quotVec) := by rw [Matrix.mulVec_smul]
      _ = σ⁻¹ • mulVec (F * Fᴴ) quotVec := by rw [← Matrix.mulVec_mulVec]
      _ = σ⁻¹ • quotVec := by simp [hFFh]
  have hdiagDenom :
      diagonal (star tHatVec) * diagonal tHatVec +
          (α : ℂ) • diagonal ellHatVec =
        diagonal denomVec := by
    ext q r
    by_cases hqr : q = r
    · subst hqr
      -- On the diagonal, the denominator definition matches the Fourier multiplier formula.
      have hdenom_q :=
        congrFun (bccbTikhonovDenominator_vec (α := α) (t := t) (ℓ := ℓ)) q
      simpa [denomVec, tHatVec, ellHatVec, Matrix.diagonal_mul_diagonal, mul_assoc,
        mul_left_comm, mul_comm] using hdenom_q.symm
    · -- Off the diagonal, every diagonal matrix entry vanishes.
      simp [hqr]
  have hcancel :
      mulVec (diagonal denomVec) (σ⁻¹ • quotVec) = σ⁻¹ • numerVec := by
    ext q
    rcases q with ⟨j, i⟩
    have hdenom_ne : denomVec (j, i) ≠ 0 := by
      simpa [denomVec] using h_denom i j
    -- Cancel the nonzero denominator entrywise in Fourier coordinates.
    simp [quotVec, numerVec, Matrix.mulVec_diagonal, Pi.smul_apply, div_eq_mul_inv, hdenom_ne,
      mul_left_comm, mul_comm]
  have hF_mul_bccb_t_sol :
      mulVec F (mulVec (bccb t) solVec) = mulVec (diagonal tHatVec) (σ⁻¹ • quotVec) := by
    -- Move the forward BCCB action into Fourier coordinates.
    calc
      mulVec F (mulVec (bccb t) solVec)
        = mulVec (F * bccb t) solVec := by rw [← Matrix.mulVec_mulVec]
      _ = mulVec (diagonal tHatVec * F) solVec := by rw [hF_mul_bccb_t]
      _ = mulVec (diagonal tHatVec) (mulVec F solVec) := by rw [Matrix.mulVec_mulVec]
      _ = mulVec (diagonal tHatVec) (σ⁻¹ • quotVec) := by rw [hF_mul_sol]
  have hF_mul_bccb_ell_sol :
      mulVec F (mulVec (bccb ℓ) solVec) = mulVec (diagonal ellHatVec) (σ⁻¹ • quotVec) := by
    -- The regularization operator transforms in the same way.
    calc
      mulVec F (mulVec (bccb ℓ) solVec)
        = mulVec (F * bccb ℓ) solVec := by rw [← Matrix.mulVec_mulVec]
      _ = mulVec (diagonal ellHatVec * F) solVec := by rw [hF_mul_bccb_ell]
      _ = mulVec (diagonal ellHatVec) (mulVec F solVec) := by rw [Matrix.mulVec_mulVec]
      _ = mulVec (diagonal ellHatVec) (σ⁻¹ • quotVec) := by rw [hF_mul_sol]
  have hF_mul_adj_bccb_t_sol :
      mulVec F (mulVec (bccb t)ᴴ (mulVec (bccb t) solVec)) =
        mulVec (diagonal (star tHatVec))
          (mulVec (diagonal tHatVec) (σ⁻¹ • quotVec)) := by
    -- Combine the adjoint Fourier action with the forward BCCB Fourier action.
    calc
      mulVec F (mulVec (bccb t)ᴴ (mulVec (bccb t) solVec))
        = mulVec (F * (bccb t)ᴴ) (mulVec (bccb t) solVec) := by rw [← Matrix.mulVec_mulVec]
      _ = mulVec (diagonal (star tHatVec) * F) (mulVec (bccb t) solVec) := by
            rw [hF_mul_bccbAdj_t]
      _ =
          mulVec (diagonal (star tHatVec))
            (mulVec F (mulVec (bccb t) solVec)) := by
              simpa using
                (Matrix.mulVec_mulVec (mulVec (bccb t) solVec) (diagonal (star tHatVec)) F).symm
      _ =
          mulVec (diagonal (star tHatVec))
            (mulVec (diagonal tHatVec) (σ⁻¹ • quotVec)) := by
              rw [hF_mul_bccb_t_sol]
  have hcombine :
      mulVec (diagonal (star tHatVec))
          (mulVec (diagonal tHatVec) (σ⁻¹ • quotVec)) +
        (α : ℂ) • mulVec (diagonal ellHatVec) (σ⁻¹ • quotVec) =
      mulVec (diagonal denomVec) (σ⁻¹ • quotVec) := by
    -- Repackage the two Fourier-side diagonal actions into the denominator multiplier.
    calc
      mulVec (diagonal (star tHatVec))
          (mulVec (diagonal tHatVec) (σ⁻¹ • quotVec)) +
        (α : ℂ) • mulVec (diagonal ellHatVec) (σ⁻¹ • quotVec)
        =
          mulVec (diagonal (star tHatVec) * diagonal tHatVec) (σ⁻¹ • quotVec) +
            mulVec ((α : ℂ) • diagonal ellHatVec) (σ⁻¹ • quotVec) := by
              rw [← Matrix.mulVec_mulVec, ← Matrix.smul_mulVec]
      _ =
          mulVec
            (diagonal (star tHatVec) * diagonal tHatVec +
              (α : ℂ) • diagonal ellHatVec)
            (σ⁻¹ • quotVec) := by
              rw [← Matrix.add_mulVec]
      _ = mulVec (diagonal denomVec) (σ⁻¹ • quotVec) := by rw [hdiagDenom]
  have hF_lhs :
      mulVec F
          (mulVec (((bccb t)ᴴ * bccb t) + (α : ℂ) • bccb ℓ) solVec) =
        σ⁻¹ • numerVec := by
    -- Move the whole normal operator into Fourier coordinates one factor at a time.
    calc
      mulVec F
          (mulVec (((bccb t)ᴴ * bccb t) + (α : ℂ) • bccb ℓ) solVec)
        =
          mulVec F
            (mulVec (bccb t)ᴴ (mulVec (bccb t) solVec) + (α : ℂ) • mulVec (bccb ℓ) solVec) := by
              rw [Matrix.add_mulVec, Matrix.mulVec_mulVec, Matrix.smul_mulVec]
      _ =
          mulVec F (mulVec (bccb t)ᴴ (mulVec (bccb t) solVec)) +
            (α : ℂ) • mulVec F (mulVec (bccb ℓ) solVec) := by
              rw [Matrix.mulVec_add, Matrix.mulVec_smul]
      _ =
          mulVec (diagonal (star tHatVec))
            (mulVec (diagonal tHatVec) (σ⁻¹ • quotVec)) +
            (α : ℂ) • mulVec (diagonal ellHatVec) (σ⁻¹ • quotVec) := by
              rw [hF_mul_adj_bccb_t_sol, hF_mul_bccb_ell_sol]
      _ = mulVec (diagonal denomVec) (σ⁻¹ • quotVec) := hcombine
      _ = σ⁻¹ • numerVec := hcancel
  have hF_rhs :
      mulVec F (mulVec (bccb t)ᴴ (vec d)) = σ⁻¹ • numerVec := by
    -- The right-hand side has the same Fourier coordinates as the canceled numerator.
    calc
      mulVec F (mulVec (bccb t)ᴴ (vec d))
        = mulVec (F * (bccb t)ᴴ) (vec d) := by rw [← Matrix.mulVec_mulVec]
      _ = mulVec (diagonal (star tHatVec) * F) (vec d) := by rw [hF_mul_bccbAdj_t]
      _ = mulVec (diagonal (star tHatVec)) (mulVec F (vec d)) := by
            exact (Matrix.mulVec_mulVec (vec d) (diagonal (star tHatVec)) F).symm
      _ = mulVec (diagonal (star tHatVec)) (σ⁻¹ • dHatVec) := by rw [hF_mul_vec_d]
      _ = σ⁻¹ • numerVec := by
            ext q
            rw [Matrix.mulVec_diagonal, Pi.smul_apply]
            simp [numerVec]
            ring
  have hinj : Function.Injective (fun v ↦ mulVec F v) := by
    intro v w hvw
    -- Apply `Fᴴ` on the left and use `Fᴴ * F = 1`.
    have hleft := congrArg (fun x ↦ mulVec Fᴴ x) hvw
    simpa [Matrix.mulVec_mulVec, hFhF] using hleft
  -- Both sides have the same Fourier coordinates, so unitarity lets us cancel `F`.
  apply hinj
  change
    mulVec F (mulVec (((bccb t)ᴴ * bccb t) + (α : ℂ) • bccb ℓ) solVec) =
      mulVec F (mulVec (bccb t)ᴴ (vec d))
  calc
    mulVec F
        (mulVec (((bccb t)ᴴ * bccb t) + (α : ℂ) • bccb ℓ) solVec)
      = σ⁻¹ • numerVec := hF_lhs
    _ = mulVec F (mulVec (bccb t)ᴴ (vec d)) := hF_rhs.symm

end Matrix
