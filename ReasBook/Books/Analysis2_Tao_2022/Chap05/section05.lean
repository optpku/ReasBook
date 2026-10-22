/-
Authors: Zichen Wang, Wanli Ma, Shu Miao, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib
import Analysis2_Tao_2022.Chap05.section04

section Chap05
section Section05

/-- Helper for Theorem 5.5.1: the Fourier series of `f` viewed in `L²` has the
expected coefficient formula and sums to `toLp f`. -/
lemma helperForTheorem_5_5_1_hasSum_fourier_series_toLp
    (f : C(AddCircle (1 : ℝ), ℂ)) :
    HasSum
      (fun n : ℤ => (fourierCoeff f n) • (fourierLp (T := (1 : ℝ)) (p := 2) n))
      (ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ f) := by
  have hsum :=
    hasSum_fourier_series_L2 (T := (1 : ℝ))
      (ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ f)
  simp_rw [fourierCoeff_toLp (T := (1 : ℝ)) (f := f)] at hsum
  exact hsum

/-- Helper for Theorem 5.5.1: symmetric integer windows `[-N, N]` tend to
`atTop` in `Finset ℤ`. -/
lemma helperForTheorem_5_5_1_tendsto_symmetricIntegerWindows :
    Filter.Tendsto (fun N : ℕ => Finset.Icc (-(N : ℤ)) (N : ℤ))
      Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop_finset_of_monotone ?_ ?_
  · intro m n hmn
    exact Finset.Icc_subset_Icc (neg_le_neg (Int.ofNat_le.mpr hmn)) (Int.ofNat_le.mpr hmn)
  · intro z
    refine ⟨Int.natAbs z, Finset.mem_Icc.mpr ?_⟩
    constructor
    · have hz : -z ≤ (Int.natAbs z : ℤ) := by
        simpa [Int.natAbs_neg] using (Int.le_natAbs (a := -z))
      simpa using (neg_le_neg hz)
    · exact Int.le_natAbs

/-- Helper for Theorem 5.5.1: symmetric Fourier partial sums converge to
`toLp f` in `L²`. -/
lemma helperForTheorem_5_5_1_tendsto_partialSums_in_Lp
    (f : C(AddCircle (1 : ℝ), ℂ)) :
    Filter.Tendsto
      (fun N : ℕ =>
        Finset.sum (Finset.Icc (-(N : ℤ)) (N : ℤ))
          (fun n => (fourierCoeff f n) • (fourierLp (T := (1 : ℝ)) (p := 2) n)))
      Filter.atTop
      (nhds (ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ f)) := by
  have hsum :
      Filter.Tendsto
        (fun s : Finset ℤ =>
          Finset.sum s
            (fun n => (fourierCoeff f n) • (fourierLp (T := (1 : ℝ)) (p := 2) n)))
        Filter.atTop
        (nhds (ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ f)) :=
    helperForTheorem_5_5_1_hasSum_fourier_series_toLp f
  exact hsum.comp helperForTheorem_5_5_1_tendsto_symmetricIntegerWindows

/-- Helper for Theorem 5.5.1: the `L²` norm of the Fourier approximation error
tends to `0`. -/
lemma helperForTheorem_5_5_1_normError_tendsto_zero
    (f : C(AddCircle (1 : ℝ), ℂ)) :
    Filter.Tendsto
      (fun N : ℕ =>
        ‖(ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ f) -
          (Finset.sum (Finset.Icc (-(N : ℤ)) (N : ℤ))
            (fun n => (fourierCoeff f n) • (fourierLp (T := (1 : ℝ)) (p := 2) n)))‖)
      Filter.atTop (nhds (0 : ℝ)) := by
  have hpartial := helperForTheorem_5_5_1_tendsto_partialSums_in_Lp f
  have hsub :
      Filter.Tendsto
        (fun N : ℕ =>
          (ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ f) -
            (Finset.sum (Finset.Icc (-(N : ℤ)) (N : ℤ))
              (fun n => (fourierCoeff f n) • (fourierLp (T := (1 : ℝ)) (p := 2) n))))
        Filter.atTop
        (nhds
          ((ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ f) -
            (ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ f))) :=
    tendsto_const_nhds.sub hpartial
  have hnorm :
      Filter.Tendsto
        (fun N : ℕ =>
          ‖(ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ f) -
            (Finset.sum (Finset.Icc (-(N : ℤ)) (N : ℤ))
              (fun n => (fourierCoeff f n) • (fourierLp (T := (1 : ℝ)) (p := 2) n)))‖)
        Filter.atTop
        (nhds
          ‖(ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ f) -
            (ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ f)‖) :=
    hsub.norm
  simpa using hnorm

/-- Theorem 5.5.1 (Fourier theorem): for every `f ∈ C(ℝ/ℤ; ℂ)`, the symmetric
Fourier partial sums `∑_{n=-N}^{N} \hat f(n) e_n` converge to `f` in the `L²`
metric, i.e. `lim_{N→∞} ‖f - ∑_{n=-N}^{N} \hat f(n)e_n‖₂ = 0`. -/
theorem fourier_series_tendsto_in_L2
    (f : C(AddCircle (1 : ℝ), ℂ)) :
    Filter.Tendsto
      (fun N : ℕ =>
        ‖(ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ f) -
          (Finset.sum (Finset.Icc (-(N : ℤ)) (N : ℤ))
            (fun n => (fourierCoeff f n) • (fourierLp (T := (1 : ℝ)) (p := 2) n)))‖)
      Filter.atTop (nhds (0 : ℝ)) :=
  helperForTheorem_5_5_1_normError_tendsto_zero f

/-- Helper for Theorem 5.5.3: absolute summability of Fourier coefficients
implies summability of the coefficients themselves. -/
lemma helperForTheorem_5_5_3_summable_fourierCoeff
    (f : C(AddCircle (1 : ℝ), ℂ))
    (habs : Summable (fun n : ℤ => ‖fourierCoeff f n‖)) :
    Summable (fun n : ℤ => fourierCoeff f n) :=
  habs.of_norm

/-- Helper for Theorem 5.5.3: summable Fourier coefficients force symmetric
Fourier partial sums to converge to `f` in `C(ℝ/ℤ; ℂ)`. -/
lemma helperForTheorem_5_5_3_tendsto_symmetricPartialSums
    (f : C(AddCircle (1 : ℝ), ℂ))
    (hcoeff : Summable (fun n : ℤ => fourierCoeff f n)) :
    Filter.Tendsto
      (fun N : ℕ =>
        Finset.sum (Finset.Icc (-(N : ℤ)) (N : ℤ))
          (fun n => (fourierCoeff f n) • (fourier (T := (1 : ℝ)) n)))
      Filter.atTop
      (nhds f) := by
  have hsum :
      HasSum
        (fun n : ℤ => (fourierCoeff f n) • (fourier (T := (1 : ℝ)) n))
        f :=
    hasSum_fourier_series_of_summable (T := (1 : ℝ)) (f := f) hcoeff
  have hsum_tendsto :
      Filter.Tendsto
        (fun s : Finset ℤ =>
          Finset.sum s (fun n => (fourierCoeff f n) • (fourier (T := (1 : ℝ)) n)))
        Filter.atTop
        (nhds f) :=
    hsum
  exact hsum_tendsto.comp helperForTheorem_5_5_1_tendsto_symmetricIntegerWindows

/-- Helper for Theorem 5.5.3: convergence of symmetric partial sums to `f`
implies convergence of the sup-norm error to `0`. -/
lemma helperForTheorem_5_5_3_normError_tendsto_zero
    (f : C(AddCircle (1 : ℝ), ℂ))
    (hpartial :
      Filter.Tendsto
        (fun N : ℕ =>
          Finset.sum (Finset.Icc (-(N : ℤ)) (N : ℤ))
            (fun n => (fourierCoeff f n) • (fourier (T := (1 : ℝ)) n)))
        Filter.atTop
        (nhds f)) :
    Filter.Tendsto
      (fun N : ℕ =>
        ‖f -
          (Finset.sum (Finset.Icc (-(N : ℤ)) (N : ℤ))
            (fun n => (fourierCoeff f n) • (fourier (T := (1 : ℝ)) n)))‖)
      Filter.atTop
      (nhds (0 : ℝ)) := by
  have hsub :
      Filter.Tendsto
        (fun N : ℕ =>
          f -
            (Finset.sum (Finset.Icc (-(N : ℤ)) (N : ℤ))
              (fun n => (fourierCoeff f n) • (fourier (T := (1 : ℝ)) n))))
        Filter.atTop
        (nhds (f - f)) :=
    tendsto_const_nhds.sub hpartial
  have hnorm :
      Filter.Tendsto
        (fun N : ℕ =>
          ‖f -
            (Finset.sum (Finset.Icc (-(N : ℤ)) (N : ℤ))
              (fun n => (fourierCoeff f n) • (fourier (T := (1 : ℝ)) n)))‖)
        Filter.atTop
        (nhds ‖f - f‖) :=
    hsub.norm
  simpa using hnorm

/-- Theorem 5.5.3: let `f ∈ C(ℝ/ℤ; ℂ)`. If `∑_{n∈ℤ} ‖\hat f(n)‖` converges,
then the symmetric Fourier partial sums `∑_{n=-N}^{N} \hat f(n)e_n` converge
uniformly to `f`, i.e. `lim_{N→∞} ‖f - ∑_{n=-N}^{N} \hat f(n)e_n‖∞ = 0`
(with `‖·‖` the sup norm on `C(ℝ/ℤ; ℂ)`). -/
theorem fourier_series_tendsto_uniform_of_summable_fourierCoefficients
    (f : C(AddCircle (1 : ℝ), ℂ))
    (habs : Summable (fun n : ℤ => ‖fourierCoeff f n‖)) :
    Filter.Tendsto
      (fun N : ℕ =>
        ‖f -
          (Finset.sum (Finset.Icc (-(N : ℤ)) (N : ℤ))
            (fun n => (fourierCoeff f n) • (fourier (T := (1 : ℝ)) n)))‖)
      Filter.atTop (nhds (0 : ℝ)) := by
  have hcoeff := helperForTheorem_5_5_3_summable_fourierCoeff f habs
  have hpartial := helperForTheorem_5_5_3_tendsto_symmetricPartialSums f hcoeff
  exact helperForTheorem_5_5_3_normError_tendsto_zero f hpartial

/-- Helper for Theorem 5.5.4: Parseval's `HasSum` identity for `toLp f`, with
Fourier coefficients rewritten in terms of the original continuous map `f`. -/
lemma helperForTheorem_5_5_4_hasSum_sq_fourierCoeff_toLp
    (f : C(AddCircle (1 : ℝ), ℂ)) :
    HasSum
      (fun n : ℤ => ‖fourierCoeff f n‖ ^ 2)
      (∫ t : AddCircle (1 : ℝ),
        ‖(ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ f) t‖ ^ 2
          ∂AddCircle.haarAddCircle) := by
  have hsum :=
    hasSum_sq_fourierCoeff (T := (1 : ℝ))
      (ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ f)
  simp_rw [fourierCoeff_toLp (T := (1 : ℝ)) (f := f)] at hsum
  exact hsum

/-- Helper for Theorem 5.5.4: for `toLp f`, the square of the `L²` norm equals
the integral of the pointwise squared norm. -/
lemma helperForTheorem_5_5_4_normSq_toLp_eq_integral_normSq
    (f : C(AddCircle (1 : ℝ), ℂ)) :
    ‖ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ f‖ ^ 2 =
      ∫ t : AddCircle (1 : ℝ),
        ‖(ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ f) t‖ ^ 2
          ∂AddCircle.haarAddCircle := by
  let g : MeasureTheory.Lp ℂ 2 AddCircle.haarAddCircle :=
    ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ f
  have hinner :=
    congr_arg RCLike.re
      (@MeasureTheory.L2.inner_def (AddCircle (1 : ℝ)) ℂ ℂ _ _ _ _ _ g g)
  rw [← integral_re] at hinner
  · simpa [g] using (show ‖g‖ ^ 2 =
      ∫ t : AddCircle (1 : ℝ), ‖g t‖ ^ 2 ∂AddCircle.haarAddCircle from by
        simpa only [← norm_sq_eq_re_inner] using hinner)
  · exact MeasureTheory.L2.integrable_inner g g

/-- Helper for Theorem 5.5.4: the Parseval `tsum` identity for continuous maps
on `AddCircle 1`. -/
lemma helperForTheorem_5_5_4_tsum_sq_fourierCoeff_eq_normSq
    (f : C(AddCircle (1 : ℝ), ℂ)) :
    (∑' n : ℤ, ‖fourierCoeff f n‖ ^ 2) =
      ‖ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ f‖ ^ 2 := by
  have hsum := helperForTheorem_5_5_4_hasSum_sq_fourierCoeff_toLp f
  have hnorm := helperForTheorem_5_5_4_normSq_toLp_eq_integral_normSq f
  calc
    (∑' n : ℤ, ‖fourierCoeff f n‖ ^ 2) =
        ∫ t : AddCircle (1 : ℝ),
          ‖(ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ f) t‖ ^ 2
            ∂AddCircle.haarAddCircle := hsum.tsum_eq
    _ = ‖ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ f‖ ^ 2 := by
      simpa using hnorm.symm

/-- Helper for Theorem 5.5.4: summability of squared Fourier coefficients for
continuous maps on `AddCircle 1`. -/
lemma helperForTheorem_5_5_4_summable_sq_fourierCoeff
    (f : C(AddCircle (1 : ℝ), ℂ)) :
    Summable (fun n : ℤ => ‖fourierCoeff f n‖ ^ 2) :=
  (helperForTheorem_5_5_4_hasSum_sq_fourierCoeff_toLp f).summable

/-- Theorem 5.5.4 (Plancherel / Parseval): for any `f ∈ C(ℝ/ℤ; ℂ)`, the series
`∑_{n∈ℤ} |\hat f(n)|^2` converges and the `L²` norm identity
`‖f‖₂^2 = ∑_{n=-∞}^{∞} |\hat f(n)|^2` holds. -/
theorem continuousMap_norm_sq_eq_tsum_sq_fourierCoeff
    (f : C(AddCircle (1 : ℝ), ℂ)) :
    Summable (fun n : ℤ => ‖fourierCoeff f n‖ ^ 2) ∧
      ‖ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ f‖ ^ 2 =
        ∑' n : ℤ, ‖fourierCoeff f n‖ ^ 2 := by
  constructor
  · exact helperForTheorem_5_5_4_summable_sq_fourierCoeff f
  · simpa using (helperForTheorem_5_5_4_tsum_sq_fourierCoeff_eq_normSq f).symm

end Section05
end Chap05
