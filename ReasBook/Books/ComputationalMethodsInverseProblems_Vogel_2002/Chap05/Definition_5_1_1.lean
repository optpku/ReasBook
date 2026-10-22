/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.UnitaryGroup

public section

open scoped Matrix BigOperators

noncomputable section

namespace Matrix

/-- Helper for Definition 5.1: the primitive Fourier root `w` used for the Chapter 5
normalized Fourier matrix on `Fin n`. -/
@[expose] def fourierRoot (n : ℕ) [NeZero n] : ℂ :=
  ZMod.stdAddChar (-1 : ZMod n)

/-- Helper for Definition 5.1: `Matrix.fourierRoot n` is the standard additive character on
`ZMod n` evaluated at `-1`. -/
theorem fourierRoot_eq_stdAddChar (n : ℕ) [NeZero n] :
    Matrix.fourierRoot n = ZMod.stdAddChar (-1 : ZMod n) :=
  rfl

/-- Helper for Definition 5.1: the Chapter 5 normalized Fourier matrix on `Fin n`. -/
@[expose] def fourierMatrix (n : ℕ) [NeZero n] : Matrix (Fin n) (Fin n) ℂ :=
  fun i j ↦ Matrix.fourierRoot n ^ ((i : ℕ) * (j : ℕ)) / Real.sqrt n

/-- Helper for Definition 5.1: the Chapter 5 Fourier root has the exponential form
`Complex.exp (-Complex.I * 2 * Real.pi / n)`. -/
theorem fourierRoot_eq_exp (n : ℕ) [NeZero n] :
    Matrix.fourierRoot n = Complex.exp (-Complex.I * 2 * Real.pi / n) := by
  rw [Matrix.fourierRoot_eq_stdAddChar]
  simpa [mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using
    (ZMod.stdAddChar_coe (N := n) (-1))

/-- Helper for Definition 5.1: the entrywise formula for `Matrix.fourierMatrix`. -/
theorem fourierMatrix_apply (n : ℕ) [NeZero n] (i j : Fin n) :
    Matrix.fourierMatrix n i j =
      Matrix.fourierRoot n ^ ((i : ℕ) * (j : ℕ)) / Real.sqrt n :=
  rfl

/-- Helper for Definition 5.1: the Chapter 5 normalized Fourier matrix is unitary. -/
theorem fourierMatrix_mem_unitaryGroup (n : ℕ) [NeZero n] :
    Matrix.fourierMatrix n ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  classical
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  cases n with
  | zero =>
      cases NeZero.ne 0 rfl
  | succ n =>
      let t : ZMod (n + 1) := (((i : ℕ) : ZMod (n + 1)) - (((j : ℕ) : ZMod (n + 1))))
      have hnonneg : 0 ≤ (n + 1 : ℝ) := by
        positivity
      have hposR : 0 < (n + 1 : ℝ) := by
        positivity
      have hsqrtR : Real.sqrt (n + 1) ≠ 0 :=
        Real.sqrt_ne_zero'.2 hposR
      have hsqrtC : (Real.sqrt (n + 1) : ℂ) ≠ 0 := by
        exact_mod_cast hsqrtR
      have hsqR : Real.sqrt (n + 1) * Real.sqrt (n + 1) = (n + 1 : ℝ) := by
        exact Real.mul_self_sqrt hnonneg
      have hsq : ((Real.sqrt (n + 1) : ℂ) * Real.sqrt (n + 1)) = (n + 1 : ℂ) := by
        exact_mod_cast hsqR
      have hinv :
          ((Real.sqrt (n + 1) : ℂ)⁻¹) * (Real.sqrt (n + 1) : ℂ)⁻¹ = ((n + 1 : ℂ)⁻¹) := by
        simpa [mul_inv_rev] using congrArg Inv.inv hsq
      have hconj (a : ZMod (n + 1)) : star (ZMod.stdAddChar (-a)) = ZMod.stdAddChar a := by
        rw [ZMod.stdAddChar_apply, ZMod.stdAddChar_apply]
        have htoCircle : ZMod.toCircle (-a) = (ZMod.toCircle a)⁻¹ := by
          simpa using AddChar.map_neg_eq_inv (ZMod.toCircle (N := n + 1)) a
        calc
          star (((ZMod.toCircle (-a) : Circle) : ℂ)) =
              (((ZMod.toCircle (-a) : Circle) : ℂ))⁻¹ := by
            simpa using (Circle.coe_inv_eq_conj (ZMod.toCircle (-a))).symm
          _ = ((ZMod.toCircle a : Circle) : ℂ) := by
            rw [htoCircle]
            simp
      have hterm (k : Fin (n + 1)) :
          star (Matrix.fourierMatrix (n + 1) k i) * Matrix.fourierMatrix (n + 1) k j =
            ((n + 1 : ℂ)⁻¹) * ZMod.stdAddChar ((((k : ℕ) : ZMod (n + 1)) * t)) := by
        -- Reduce each entry of `star F * F` to one additive character evaluation.
        simp only [Matrix.fourierMatrix, Matrix.fourierRoot_eq_stdAddChar, RCLike.star_def]
        rw [← AddChar.map_nsmul_eq_pow, ← AddChar.map_nsmul_eq_pow]
        rw [nsmul_eq_mul, nsmul_eq_mul]
        simp_rw [div_eq_mul_inv]
        have hstarFactor :
            (starRingEnd ℂ)
                (ZMod.stdAddChar (((((k : ℕ) * (i : ℕ)) : ℕ) : ZMod (n + 1)) * (-1)) *
                  (((Real.sqrt ((n + 1 : ℕ) : ℝ)) : ℂ)⁻¹)) =
              ZMod.stdAddChar (((((k : ℕ) * (i : ℕ)) : ℕ) : ZMod (n + 1)) * 1) *
                (((Real.sqrt ((n + 1 : ℕ) : ℝ)) : ℂ)⁻¹) := by
          rw [map_mul]
          have hneg :
              (((((k : ℕ) * (i : ℕ)) : ℕ) : ZMod (n + 1)) * (-1)) =
                -(((((k : ℕ) * (i : ℕ)) : ℕ) : ZMod (n + 1))) := by
            ring
          rw [hneg]
          have hchar :
              (starRingEnd ℂ) (ZMod.stdAddChar (-(((((k : ℕ) * (i : ℕ)) : ℕ) : ZMod (n + 1))))) =
                ZMod.stdAddChar (((((k : ℕ) * (i : ℕ)) : ℕ) : ZMod (n + 1)) * 1) := by
            simpa [RCLike.star_def] using
              hconj (((((k : ℕ) * (i : ℕ)) : ℕ) : ZMod (n + 1)))
          rw [hchar]
          simp
        have hleft :
            (starRingEnd ℂ)
                (ZMod.stdAddChar (((((k : ℕ) * (i : ℕ)) : ℕ) : ZMod (n + 1)) * (-1)) *
                  (((Real.sqrt ((n + 1 : ℕ) : ℝ)) : ℂ)⁻¹)) *
                (ZMod.stdAddChar (((((k : ℕ) * (j : ℕ)) : ℕ) : ZMod (n + 1)) * (-1)) *
                  (((Real.sqrt ((n + 1 : ℕ) : ℝ)) : ℂ)⁻¹)) =
              (ZMod.stdAddChar (((((k : ℕ) * (i : ℕ)) : ℕ) : ZMod (n + 1)) * 1) *
                  (((Real.sqrt ((n + 1 : ℕ) : ℝ)) : ℂ)⁻¹)) *
                (ZMod.stdAddChar (((((k : ℕ) * (j : ℕ)) : ℕ) : ZMod (n + 1)) * (-1)) *
                  (((Real.sqrt ((n + 1 : ℕ) : ℝ)) : ℂ)⁻¹)) := by
          rw [hstarFactor]
        have hmul :
            ZMod.stdAddChar ((((k : ℕ) : ZMod (n + 1)) * (((i : ℕ) : ZMod (n + 1))) * 1)) *
                (Real.sqrt (n + 1) : ℂ)⁻¹ *
                (ZMod.stdAddChar
                    ((((k : ℕ) : ZMod (n + 1)) * (((j : ℕ) : ZMod (n + 1))) * (-1))) *
                  (Real.sqrt (n + 1) : ℂ)⁻¹) =
              (((Real.sqrt (n + 1) : ℂ)⁻¹) * (Real.sqrt (n + 1) : ℂ)⁻¹) *
                (ZMod.stdAddChar
                    ((((k : ℕ) : ZMod (n + 1)) * (((i : ℕ) : ZMod (n + 1))) * 1)) *
                  ZMod.stdAddChar
                    ((((k : ℕ) : ZMod (n + 1)) * (((j : ℕ) : ZMod (n + 1))) * (-1)))) := by
          ring
        have harg :
            ((((k : ℕ) : ZMod (n + 1)) * (((i : ℕ) : ZMod (n + 1))) * 1)) +
                ((((k : ℕ) : ZMod (n + 1)) * (((j : ℕ) : ZMod (n + 1))) * (-1))) =
              (((k : ℕ) : ZMod (n + 1)) * t) := by
          calc
            ((((k : ℕ) : ZMod (n + 1)) * (((i : ℕ) : ZMod (n + 1))) * 1)) +
                ((((k : ℕ) : ZMod (n + 1)) * (((j : ℕ) : ZMod (n + 1))) * (-1))) =
                  ((((k : ℕ) : ZMod (n + 1)) * (((i : ℕ) : ZMod (n + 1)))) -
                    (((k : ℕ) : ZMod (n + 1)) * (((j : ℕ) : ZMod (n + 1))))) := by
                  ring
            _ = (((k : ℕ) : ZMod (n + 1)) *
                  ((((i : ℕ) : ZMod (n + 1))) - (((j : ℕ) : ZMod (n + 1))))) := by
                  ring
            _ = (((k : ℕ) : ZMod (n + 1)) * t) := by
                  rfl
        have hmul' :
            ZMod.stdAddChar (((((k : ℕ) * (i : ℕ)) : ℕ) : ZMod (n + 1)) * 1) *
                (Real.sqrt (n + 1) : ℂ)⁻¹ *
                (ZMod.stdAddChar (((((k : ℕ) * (j : ℕ)) : ℕ) : ZMod (n + 1)) * (-1)) *
                  (Real.sqrt (n + 1) : ℂ)⁻¹) =
              (((Real.sqrt (n + 1) : ℂ)⁻¹) * (Real.sqrt (n + 1) : ℂ)⁻¹) *
                (ZMod.stdAddChar (((((k : ℕ) * (i : ℕ)) : ℕ) : ZMod (n + 1)) * 1) *
                  ZMod.stdAddChar (((((k : ℕ) * (j : ℕ)) : ℕ) : ZMod (n + 1)) * (-1))) := by
          simpa using hmul
        have harg' :
            (((((k : ℕ) * (i : ℕ)) : ℕ) : ZMod (n + 1)) * 1) +
                (((((k : ℕ) * (j : ℕ)) : ℕ) : ZMod (n + 1)) * (-1)) =
              (((k : ℕ) : ZMod (n + 1)) * t) := by
          simpa using harg
        change
          (starRingEnd ℂ)
              (ZMod.stdAddChar (((((k : ℕ) * (i : ℕ)) : ℕ) : ZMod (n + 1)) * (-1)) *
                (((Real.sqrt ((n + 1 : ℕ) : ℝ)) : ℂ)⁻¹)) *
              (ZMod.stdAddChar (((((k : ℕ) * (j : ℕ)) : ℕ) : ZMod (n + 1)) * (-1)) *
                (((Real.sqrt ((n + 1 : ℕ) : ℝ)) : ℂ)⁻¹)) =
            ((n + 1 : ℂ)⁻¹) * ZMod.stdAddChar ((((k : ℕ) : ZMod (n + 1)) * t))
        calc
          (starRingEnd ℂ)
              (ZMod.stdAddChar (((((k : ℕ) * (i : ℕ)) : ℕ) : ZMod (n + 1)) * (-1)) *
                (((Real.sqrt ((n + 1 : ℕ) : ℝ)) : ℂ)⁻¹)) *
              (ZMod.stdAddChar (((((k : ℕ) * (j : ℕ)) : ℕ) : ZMod (n + 1)) * (-1)) *
                (((Real.sqrt ((n + 1 : ℕ) : ℝ)) : ℂ)⁻¹)) =
              (ZMod.stdAddChar (((((k : ℕ) * (i : ℕ)) : ℕ) : ZMod (n + 1)) * 1) *
                  (((Real.sqrt ((n + 1 : ℕ) : ℝ)) : ℂ)⁻¹)) *
                (ZMod.stdAddChar (((((k : ℕ) * (j : ℕ)) : ℕ) : ZMod (n + 1)) * (-1)) *
                  (((Real.sqrt ((n + 1 : ℕ) : ℝ)) : ℂ)⁻¹)) := by
                convert hleft using 1
          _ = (((Real.sqrt (n + 1) : ℂ)⁻¹) * (Real.sqrt (n + 1) : ℂ)⁻¹) *
                (ZMod.stdAddChar (((((k : ℕ) * (i : ℕ)) : ℕ) : ZMod (n + 1)) * 1) *
                  ZMod.stdAddChar (((((k : ℕ) * (j : ℕ)) : ℕ) : ZMod (n + 1)) * (-1))) := by
                simpa using hmul
          _ = ((n + 1 : ℂ)⁻¹) * ZMod.stdAddChar ((((k : ℕ) : ZMod (n + 1)) * t)) := by
                rw [hinv, ← AddChar.map_add_eq_mul, harg']
      have hsumZ :
          ∑ x : ZMod (n + 1), ZMod.stdAddChar (((x.val : ZMod (n + 1)) * t)) =
            if t = 0 then (n + 1 : ℂ) else 0 := by
        simpa using (AddChar.sum_mulShift t (ZMod.isPrimitive_stdAddChar (n + 1)))
      have hsum :
          ∑ k : Fin (n + 1), ZMod.stdAddChar ((((k : ℕ) : ZMod (n + 1)) * t)) =
            if t = 0 then (n + 1 : ℂ) else 0 := by
        -- The character sum is `n + 1` on the diagonal and vanishes off the diagonal.
        convert hsumZ using 1
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        rfl
      have ht0 : t = 0 ↔ i = j := by
        constructor
        · intro ht
          apply Fin.ext
          have hijVal :
              ((((i : ℕ) : ZMod (n + 1))).val) = ((((j : ℕ) : ZMod (n + 1))).val) := by
            exact congrArg ZMod.val (sub_eq_zero.mp ht)
          simpa [ZMod.val_natCast_of_lt i.is_lt, ZMod.val_natCast_of_lt j.is_lt] using hijVal
        · intro hij
          simp [t, hij]
      rw [Matrix.mul_apply]
      simp_rw [Matrix.star_apply, hterm]
      calc
        ∑ k : Fin (n + 1), ((n + 1 : ℂ)⁻¹) * ZMod.stdAddChar ((((k : ℕ) : ZMod (n + 1)) * t)) =
            ((n + 1 : ℂ)⁻¹) * (if t = 0 then (n + 1 : ℂ) else 0) := by
              rw [← Finset.mul_sum, hsum]
        _ = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) i j := by
              rw [Matrix.one_apply]
              by_cases hij : i = j
              · rw [if_pos hij, if_pos (ht0.mpr hij)]
                have hcard : (n + 1 : ℂ) ≠ 0 := by
                  exact_mod_cast Nat.succ_ne_zero n
                field_simp [hcard]
              · rw [if_neg hij, if_neg (mt ht0.mp hij)]
                simp

/-- The normalized discrete Fourier transform on `Fin n → ℂ` as a linear map. -/
abbrev dft (n : ℕ) [NeZero n] : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
  Matrix.mulVecLin (Matrix.fourierMatrix n)

/-- Helper for Definition 5.1: the normalized discrete Fourier transform has the coordinate
formula `(Matrix.dft n f) i = ∑ j, Matrix.fourierMatrix n i j * f j`. -/
theorem dft_apply (n : ℕ) [NeZero n] (f : Fin n → ℂ) (i : Fin n) :
    Matrix.dft n f i = ∑ j : Fin n, Matrix.fourierMatrix n i j * f j := by
  simpa [Matrix.dft] using Matrix.mulVec_apply_eq_sum (Matrix.fourierMatrix n) f i

/- Definition 5.1 (2): the Chapter 5 normalized Fourier matrix is the existing owner
`Matrix.fourierMatrix`, with entrywise formula `Matrix.fourierMatrix_apply` and source
exponential description `Matrix.fourierRoot_eq_exp`. -/

/-- Helper for Definition 5.1: the DFT coordinates satisfy the textbook exponential sum formula. -/
theorem dft_apply_exp (n : ℕ) [NeZero n] (f : Fin n → ℂ) (i : Fin n) :
    Matrix.dft n f i =
      ∑ j : Fin n,
        (Complex.exp (-Complex.I * 2 * Real.pi / n)) ^ ((i : ℕ) * (j : ℕ)) / Real.sqrt n * f j := by
  -- Rewrite the Fourier-matrix entries using the imported exponential formula for the root.
  simpa [Matrix.fourierMatrix_apply, Matrix.fourierRoot_eq_exp] using Matrix.dft_apply n f i

/-- The inverse discrete Fourier transform on `Fin n → ℂ` as a linear map. -/
abbrev invDFT (n : ℕ) [NeZero n] : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
  Matrix.mulVecLin ((Matrix.fourierMatrix n)ᴴ)

/-- Helper for Definition 5.1: the inverse discrete Fourier transform has the coordinate
formula `(Matrix.invDFT n g) i = ∑ j, ((Matrix.fourierMatrix n)ᴴ) i j * g j`. -/
theorem invDFT_apply (n : ℕ) [NeZero n] (g : Fin n → ℂ) (i : Fin n) :
    Matrix.invDFT n g i = ∑ j : Fin n, ((Matrix.fourierMatrix n)ᴴ) i j * g j := by
  simpa [Matrix.invDFT] using Matrix.mulVec_apply_eq_sum ((Matrix.fourierMatrix n)ᴴ) g i

/-- Helper for Definition 5.1: after expanding the conjugated Fourier kernel
and collecting the normalization factors, the inverse DFT phase is the
textbook positive-sign exponential. -/
lemma invDFTKernel_mul_eq_exp (n : ℕ) [NeZero n] (i j : Fin n) (z : ℂ) :
    ((Real.sqrt n : ℂ)⁻¹) * (((Matrix.fourierMatrix n)ᴴ i j) * z) =
      (n : ℂ)⁻¹ *
        (z * Complex.exp (Complex.I * 2 * Real.pi * (((i : ℕ) * (j : ℕ) : ℂ) / n))) := by
  have hn : (n : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.pos_of_neZero n).ne'
  have hsqrt : (Real.sqrt n : ℂ) ≠ 0 := by
    simpa using
      (Real.sqrt_ne_zero'.2 (show (0 : ℝ) < n by exact_mod_cast Nat.pos_of_neZero n))
  have hsqrt_sq : ((Real.sqrt n : ℂ) * Real.sqrt n) = n := by
    exact_mod_cast (Real.mul_self_sqrt (show (0 : ℝ) ≤ n by exact_mod_cast Nat.zero_le n))
  have hexp :
      (((i : ℕ) * (j : ℕ) : ℂ)) * (Complex.I * 2 * Real.pi / n) =
        Complex.I * 2 * Real.pi * (((i : ℕ) * (j : ℕ) : ℂ) / n) := by
    field_simp [hn]
  have hstar_exp (x : ℂ) :
      (starRingEnd ℂ) (Complex.exp x) = Complex.exp ((starRingEnd ℂ) x) := by
    exact (Complex.exp_conj (x := x)).symm
  have htwo : ((starRingEnd ℂ) 2 : ℂ) = 2 := by
    change star (2 : ℂ) = 2
    simp
  calc
    ((Real.sqrt n : ℂ)⁻¹) * (((Matrix.fourierMatrix n)ᴴ i j) * z)
      = (((Real.sqrt n : ℂ) * Real.sqrt n)⁻¹) *
          (Complex.exp ((((i : ℕ) * (j : ℕ) : ℂ)) * (Complex.I * 2 * Real.pi / n)) * z) := by
            simp only [conjTranspose_apply, RCLike.star_def]
            rw [Matrix.fourierMatrix_apply, Matrix.fourierRoot_eq_exp, map_div₀]
            simp only [map_pow]
            rw [hstar_exp]
            simp only [_root_.mul_inv_rev, neg_mul, map_div₀, map_neg, map_mul, Complex.conj_I,
              Complex.conj_ofReal, neg_neg, map_natCast]
            rw [div_eq_mul_inv, ← Complex.exp_nat_mul]
            field_simp [hsqrt]
            simp [htwo, mul_assoc, mul_left_comm, mul_comm]
    _ = (n : ℂ)⁻¹ *
          (Complex.exp ((((i : ℕ) * (j : ℕ) : ℂ)) * (Complex.I * 2 * Real.pi / n)) * z) := by
            rw [hsqrt_sq]
    _ = (n : ℂ)⁻¹ *
          (Complex.exp (Complex.I * 2 * Real.pi * (((i : ℕ) * (j : ℕ) : ℂ) / n)) * z) := by
            rw [hexp]
    _ = (n : ℂ)⁻¹ *
          (z * Complex.exp (Complex.I * 2 * Real.pi * (((i : ℕ) * (j : ℕ) : ℂ) / n))) := by
            simp [mul_left_comm, mul_comm]

/-- Helper for Definition 5.1: the normalized inverse DFT has the textbook
positive-sign exponential coordinate formula. -/
theorem invDFT_apply_exp (n : ℕ) [NeZero n] (g : Fin n → ℂ) (i : Fin n) :
    ((Real.sqrt n : ℂ)⁻¹) * Matrix.invDFT n g i =
      (n : ℂ)⁻¹ *
        ∑ j : Fin n, g j *
          Complex.exp (Complex.I * 2 * Real.pi * (((i : ℕ) * (j : ℕ) : ℂ) / n)) := by
  rw [Matrix.invDFT_apply]
  simp_rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simpa [mul_assoc, mul_left_comm, mul_comm] using invDFTKernel_mul_eq_exp n i j (g j)

/-- Definition 5.1 (4): the Chapter 5 Fourier matrix satisfies the unitary identity
`(Matrix.fourierMatrix n)ᴴ * Matrix.fourierMatrix n = 1`. -/
theorem fourierMatrix_conjTranspose_mul (n : ℕ) [NeZero n] :
    (Matrix.fourierMatrix n)ᴴ * Matrix.fourierMatrix n = 1 :=
  Matrix.mem_unitaryGroup_iff'.mp <| Matrix.fourierMatrix_mem_unitaryGroup n

end Matrix
