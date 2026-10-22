/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Definition_5_1_1
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Logic.Equiv.Fin.Basic

public section

open scoped Matrix BigOperators

noncomputable section

namespace Matrix.FFT

universe u

/-- The Chapter 5 unnormalized discrete Fourier transform `√n • Matrix.dft n`. -/
def unnormalizedDft (n : ℕ) [NeZero n] : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
  (Real.sqrt n : ℂ) • Matrix.dft n

/-- Pointwise evaluation of `Matrix.FFT.unnormalizedDft`. -/
theorem unnormalizedDft_apply (n : ℕ) [NeZero n] (f : Fin n → ℂ) (i : Fin n) :
    unnormalizedDft n f i = (Real.sqrt n : ℂ) * Matrix.dft n f i := by
  simp [unnormalizedDft]

/-- The first contiguous half of a signal indexed by `Fin (2 * m)`. -/
def firstHalf {α : Type u} (m : ℕ) (f : Fin (2 * m) → α) : Fin m → α :=
  fun i ↦ f (finProdFinEquiv ((0 : Fin 2), i))

/-- Pointwise evaluation of `Matrix.FFT.firstHalf`. -/
theorem firstHalf_apply {α : Type u} (m : ℕ) (f : Fin (2 * m) → α) (i : Fin m) :
    firstHalf m f i = f (finProdFinEquiv ((0 : Fin 2), i)) := by
  rfl

/-- The second contiguous half of a signal indexed by `Fin (2 * m)`. -/
def secondHalf {α : Type u} (m : ℕ) (f : Fin (2 * m) → α) : Fin m → α :=
  fun i ↦ f (finProdFinEquiv ((1 : Fin 2), i))

/-- Pointwise evaluation of `Matrix.FFT.secondHalf`. -/
theorem secondHalf_apply {α : Type u} (m : ℕ) (f : Fin (2 * m) → α) (i : Fin m) :
    secondHalf m f i = f (finProdFinEquiv ((1 : Fin 2), i)) := by
  rfl

/-- The even-indexed subsequence `f₀, f₂, …, f_(2m-2)` of a signal on `Fin (2 * m)`. -/
def evenPart {α : Type u} (m : ℕ) (f : Fin (2 * m) → α) : Fin m → α :=
  fun i ↦ f ((finCongr (Nat.mul_comm m 2)) (finProdFinEquiv (i, (0 : Fin 2))))

/-- Pointwise evaluation of `Matrix.FFT.evenPart`. -/
theorem evenPart_apply {α : Type u} (m : ℕ) (f : Fin (2 * m) → α) (i : Fin m) :
    evenPart m f i =
      f ((finCongr (Nat.mul_comm m 2)) (finProdFinEquiv (i, (0 : Fin 2)))) := by
  rfl

/-- The odd-indexed subsequence `f₁, f₃, …, f_(2m-1)` of a signal on `Fin (2 * m)`. -/
def oddPart {α : Type u} (m : ℕ) (f : Fin (2 * m) → α) : Fin m → α :=
  fun i ↦ f ((finCongr (Nat.mul_comm m 2)) (finProdFinEquiv (i, (1 : Fin 2))))

/-- Pointwise evaluation of `Matrix.FFT.oddPart`. -/
theorem oddPart_apply {α : Type u} (m : ℕ) (f : Fin (2 * m) → α) (i : Fin m) :
    oddPart m f i =
      f ((finCongr (Nat.mul_comm m 2)) (finProdFinEquiv (i, (1 : Fin 2)))) := by
  rfl

/-- Helper for Remark 5.2.2-extra-1: `unnormalizedDft` is the raw Fourier-root sum. -/
lemma unnormalizedDft_eq_sum (n : ℕ) [NeZero n] (f : Fin n → ℂ) (i : Fin n) :
    unnormalizedDft n f i = ∑ j : Fin n, Matrix.fourierRoot n ^ ((i : ℕ) * (j : ℕ)) * f j := by
  have hn_pos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hsqrtR : (Real.sqrt n : ℝ) ≠ 0 := Real.sqrt_ne_zero'.2 (Nat.cast_pos.mpr hn_pos)
  have hsqrtC : (Real.sqrt n : ℂ) ≠ 0 := by
    exact_mod_cast hsqrtR
  -- Cancel the normalization factor against the Fourier-matrix denominator once and for all.
  rw [unnormalizedDft_apply, Matrix.dft_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [Matrix.fourierMatrix_apply]
  field_simp [hsqrtC]

/-- Helper for Remark 5.2.2-extra-1: the even embedding `l ↦ 2l` into `Fin (2 * m)`. -/
def evenIndex (m : ℕ) : Fin m → Fin (2 * m) :=
  fun l ↦ (finCongr (Nat.mul_comm m 2)) (finProdFinEquiv (l, (0 : Fin 2)))

/-- Helper for Remark 5.2.2-extra-1: the odd embedding `l ↦ 2l + 1` into `Fin (2 * m)`. -/
def oddIndex (m : ℕ) : Fin m → Fin (2 * m) :=
  fun l ↦ (finCongr (Nat.mul_comm m 2)) (finProdFinEquiv (l, (1 : Fin 2)))

/-- Helper for Remark 5.2.2-extra-1: splitting a sum over `Fin (2 * m)` into even and odd
positions. -/
lemma sum_splitByParity (m : ℕ) (g : Fin (2 * m) → ℂ) :
    ∑ j : Fin (2 * m), g j =
      ∑ l : Fin m,
        (g (evenIndex m l) + g (oddIndex m l)) := by
  let e : Fin m × Fin 2 ≃ Fin (2 * m) :=
    (finProdFinEquiv : Fin m × Fin 2 ≃ Fin (m * 2)).trans (finCongr (Nat.mul_comm m 2))
  -- Reindex the input by the parity equivalence and then evaluate the two `Fin 2` branches.
  calc
    ∑ j : Fin (2 * m), g j = ∑ x : Fin m × Fin 2, g (e x) := by
      symm
      exact Fintype.sum_equiv e (fun x : Fin m × Fin 2 ↦ g (e x)) g (fun x ↦ rfl)
    _ = ∑ l : Fin m, ∑ b : Fin 2, g (e (l, b)) := by
      simpa using (Fintype.sum_prod_type (f := fun x : Fin m × Fin 2 ↦ g (e x)))
    _ = ∑ l : Fin m, (g (evenIndex m l) + g (oddIndex m l)) := by
      simp [Fin.sum_univ_two, e, evenIndex, oddIndex]

/-- Helper for Remark 5.2.2-extra-1: the first half index is the unshifted index `i`. -/
lemma firstHalfIndex_val (m : ℕ) (i : Fin m) :
    ((finProdFinEquiv ((0 : Fin 2), i)) : ℕ) = i := by
  simp [finProdFinEquiv]

/-- Helper for Remark 5.2.2-extra-1: the second half index is the shifted index `m + i`. -/
lemma secondHalfIndex_val (m : ℕ) (i : Fin m) :
    ((finProdFinEquiv ((1 : Fin 2), i)) : ℕ) = m + i := by
  simp [finProdFinEquiv, Nat.add_comm]

/-- Helper for Remark 5.2.2-extra-1: the parity split encodes even indices as `2 * l`. -/
lemma evenIndex_val (m : ℕ) (l : Fin m) :
    ((evenIndex m l : Fin (2 * m)) : ℕ) = 2 * l := by
  simp [evenIndex, finProdFinEquiv]

/-- Helper for Remark 5.2.2-extra-1: the parity split encodes odd indices as `2 * l + 1`. -/
lemma oddIndex_val (m : ℕ) (l : Fin m) :
    ((oddIndex m l : Fin (2 * m)) : ℕ) = 2 * l + 1 := by
  have h : ((oddIndex m l : Fin (2 * m)) : ℕ) = 1 + 2 * l := by
    simp [oddIndex, finProdFinEquiv]
  rw [h]
  ring_nf

/-- Helper for Remark 5.2.2-extra-1: the basic Fourier root is an `n`th root of unity. -/
lemma fourierRootPowCard (n : ℕ) [NeZero n] :
    Matrix.fourierRoot n ^ n = 1 := by
  -- Switch to the additive-character model, where the `n`th power is immediate.
  rw [Matrix.fourierRoot_eq_stdAddChar, ← AddChar.map_nsmul_eq_pow]
  simp [nsmul_eq_mul]

/-- Helper for Remark 5.2.2-extra-1: squaring the size-`2m` Fourier root gives the size-`m`
Fourier root. -/
lemma fourierRootTwoMulSq (m : ℕ) [NeZero m] :
    Matrix.fourierRoot (2 * m) ^ 2 = Matrix.fourierRoot m := by
  have h2m : ((2 * m : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.mul_ne_zero (by decide : 2 ≠ 0) (NeZero.ne m)
  have hm : ((m : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (NeZero.ne m)
  -- Compare the two roots through their exponential formulas and simplify the exponent.
  rw [Matrix.fourierRoot_eq_exp, Matrix.fourierRoot_eq_exp, ← Complex.exp_nat_mul]
  congr 1
  field_simp [h2m, hm]
  norm_num [Nat.cast_mul]

/-- Helper for Remark 5.2.2-extra-1: shifting a size-`2m` Fourier-root power by `m` introduces a
minus sign. -/
lemma fourierRootTwoMulHalfShift (m : ℕ) [NeZero m] (k : ℕ) :
    Matrix.fourierRoot (2 * m) ^ (m + k) = -Matrix.fourierRoot (2 * m) ^ k := by
  -- Separate the half-period shift from the remaining power.
  have hmShift : Matrix.fourierRoot (2 * m) ^ m = (-1 : ℂ) := by
    have h2m : ((2 * m : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast Nat.mul_ne_zero (by decide : 2 ≠ 0) (NeZero.ne m)
    rw [Matrix.fourierRoot_eq_exp, ← Complex.exp_nat_mul]
    have hexp :
        (m : ℂ) * (-Complex.I * 2 * Real.pi / (2 * m : ℕ)) = -(Real.pi * Complex.I) := by
      field_simp [h2m]
      norm_num [Nat.cast_mul]
      ring
    rw [hexp, Complex.exp_neg_pi_mul_I]
  rw [pow_add, hmShift, mul_comm]
  ring

/-- Remark 5.2.2-extra-1 (1): for `i : Fin m`, the first output half of
`unnormalizedDft (2 * m) f` splits into the transforms of the even and odd
subsequences of `f`. -/
theorem splitFirstHalf (m : ℕ) [NeZero m] (f : Fin (2 * m) → ℂ) (i : Fin m) :
    firstHalf m (unnormalizedDft (2 * m) f) i =
      unnormalizedDft m (evenPart m f) i +
        Matrix.fourierRoot (2 * m) ^ (i : ℕ) * unnormalizedDft m (oddPart m f) i := by
  -- Expand the first output half to the raw Fourier sum indexed by `Fin (2 * m)`.
  rw [firstHalf_apply, unnormalizedDft_eq_sum]
  rw [firstHalfIndex_val]
  -- Split the input sum into even and odd positions, then rewrite both branches as size-`m`
  -- transforms.
  rw [sum_splitByParity, Finset.sum_add_distrib, unnormalizedDft_eq_sum, unnormalizedDft_eq_sum]
  congr 1
  · refine Finset.sum_congr rfl ?_
    intro l _
    unfold evenIndex
    have hEvenIdx :
        (((finCongr (Nat.mul_comm m 2)) (finProdFinEquiv (l, (0 : Fin 2)))) : ℕ) = 2 * l := by
      simp [finProdFinEquiv]
    rw [evenPart_apply, hEvenIdx]
    have hexp : (i : ℕ) * (2 * (l : ℕ)) = 2 * ((i : ℕ) * (l : ℕ)) := by
      ring
    rw [hexp, pow_mul, fourierRootTwoMulSq]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro l _
    unfold oddIndex
    have hOddIdx :
        (((finCongr (Nat.mul_comm m 2)) (finProdFinEquiv (l, (1 : Fin 2)))) : ℕ) = 2 * l + 1 := by
      simpa [oddIndex] using oddIndex_val m l
    rw [oddPart_apply, hOddIdx]
    have hexp : (i : ℕ) * (2 * (l : ℕ) + 1) = 2 * ((i : ℕ) * (l : ℕ)) + i := by
      ring
    rw [hexp, pow_add, pow_mul, fourierRootTwoMulSq]
    ring

/-- Function-level form of `splitFirstHalf`. -/
theorem firstHalf_unnormalizedDft_eq (m : ℕ) [NeZero m] (f : Fin (2 * m) → ℂ) :
    firstHalf m (unnormalizedDft (2 * m) f) =
      fun i ↦
        unnormalizedDft m (evenPart m f) i +
          Matrix.fourierRoot (2 * m) ^ (i : ℕ) * unnormalizedDft m (oddPart m f) i := by
  funext i
  simpa using splitFirstHalf m f i

/-- Remark 5.2.2-extra-1 (2): for `i : Fin m`, the second output half of
`unnormalizedDft (2 * m) f` is the same even transform minus the odd contribution
weighted by `Matrix.fourierRoot (2 * m) ^ (i : ℕ)`. -/
theorem splitSecondHalf (m : ℕ) [NeZero m] (f : Fin (2 * m) → ℂ) (i : Fin m) :
    secondHalf m (unnormalizedDft (2 * m) f) i =
      unnormalizedDft m (evenPart m f) i -
        Matrix.fourierRoot (2 * m) ^ (i : ℕ) * unnormalizedDft m (oddPart m f) i := by
  -- Expand the shifted output index and split the input sum by parity as before.
  rw [secondHalf_apply, unnormalizedDft_eq_sum]
  rw [secondHalfIndex_val]
  rw [sum_splitByParity, Finset.sum_add_distrib, unnormalizedDft_eq_sum, unnormalizedDft_eq_sum,
    sub_eq_add_neg]
  congr 1
  · refine Finset.sum_congr rfl ?_
    intro l _
    unfold evenIndex
    have hEvenIdx :
        (((finCongr (Nat.mul_comm m 2)) (finProdFinEquiv (l, (0 : Fin 2)))) : ℕ) = 2 * l := by
      simp [finProdFinEquiv]
    rw [evenPart_apply, hEvenIdx]
    have hexp : (m + (i : ℕ)) * (2 * (l : ℕ)) = 2 * (m * (l : ℕ) + (i : ℕ) * (l : ℕ)) := by
      ring
    rw [hexp, pow_mul, fourierRootTwoMulSq, pow_add, pow_mul, fourierRootPowCard]
    ring
  · rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl ?_
    intro l _
    unfold oddIndex
    have hOddIdx :
        (((finCongr (Nat.mul_comm m 2)) (finProdFinEquiv (l, (1 : Fin 2)))) : ℕ) = 2 * l + 1 := by
      simpa [oddIndex] using oddIndex_val m l
    rw [oddPart_apply, hOddIdx]
    have hexp :
        (m + (i : ℕ)) * (2 * (l : ℕ) + 1) =
          (2 * (m * (l : ℕ) + (i : ℕ) * (l : ℕ)) + (m + i)) := by
      ring
    rw [hexp, pow_add, pow_mul, fourierRootTwoMulSq, pow_add, pow_mul, fourierRootPowCard,
      fourierRootTwoMulHalfShift]
    ring

/-- Function-level form of `splitSecondHalf`. -/
theorem secondHalf_unnormalizedDft_eq (m : ℕ) [NeZero m] (f : Fin (2 * m) → ℂ) :
    secondHalf m (unnormalizedDft (2 * m) f) =
      fun i ↦
        unnormalizedDft m (evenPart m f) i -
          Matrix.fourierRoot (2 * m) ^ (i : ℕ) * unnormalizedDft m (oddPart m f) i := by
  funext i
  simpa using splitSecondHalf m f i

end Matrix.FFT
