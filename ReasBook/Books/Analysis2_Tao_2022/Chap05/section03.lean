/-
Authors: Zichen Wang, Wanli Ma, Shu Miao, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib
import Mathlib.Analysis.Fourier.AddCircle

section Chap05
section Section03

/-- The exponential mode `x ↦ exp(2π i n x)` is continuous and `1`-periodic on `ℝ`. -/
lemma fourierCharacter_formula_continuous_periodic (n : ℤ) :
    Continuous (fun x : ℝ => Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (x : ℂ))) ∧
      Function.Periodic (fun x : ℝ => Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (x : ℂ))) 1 := by
  constructor
  · continuity
  · intro x
    have hphase :
        2 * Real.pi * Complex.I * (n : ℂ) * (((x + 1 : ℝ) : ℂ)) =
          2 * Real.pi * Complex.I * (n : ℂ) * (x : ℂ) + n * (2 * Real.pi * Complex.I) := by
      calc
        2 * Real.pi * Complex.I * (n : ℂ) * (((x + 1 : ℝ) : ℂ))
            = 2 * Real.pi * Complex.I * (n : ℂ) * ((x : ℂ) + 1) := by simp
        _ = 2 * Real.pi * Complex.I * (n : ℂ) * (x : ℂ) + n * (2 * Real.pi * Complex.I) := by
              ring
    calc
      Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (((x + 1 : ℝ) : ℂ)))
          = Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (x : ℂ) + n * (2 * Real.pi * Complex.I)) := by
              rw [hphase]
      _ = Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (x : ℂ)) *
            Complex.exp (n * (2 * Real.pi * Complex.I)) := by rw [Complex.exp_add]
      _ = Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (x : ℂ)) := by simp

/-- Definition 5.3.1 (Characters): for every integer `n`, define
`e_n ∈ C(ℝ/ℤ; ℂ)` by `e_n(x) = exp(2π i n x)`. -/
noncomputable def fourierCharacter (n : ℤ) :
    C(AddCircle (1 : ℝ), ℂ) :=
  fourier (T := (1 : ℝ)) n

/-- Evaluation formula for the character `e_n`. -/
lemma fourierCharacter_apply (n : ℤ) (x : ℝ) :
    fourierCharacter n (x : AddCircle (1 : ℝ)) =
      Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (x : ℂ)) := by
  rw [fourierCharacter]
  convert (fourier_coe_apply (T := (1 : ℝ)) (n := n) (x := x)) using 1
  simp

/-- Lemma 5.3.5 (Characters are an orthonormal system): for integers `n, m`,
the Fourier characters satisfy `⟪e_n, e_m⟫ = 1` when `n = m` and `0` otherwise,
and `‖e_n‖_2 = 1`, where `e_k` is viewed in `L²` as `fourierLp (T := 1) (p := 2) k`. -/
lemma fourierCharacter_orthonormal_system (n m : ℤ) :
    (inner ℂ (fourierLp (T := (1 : ℝ)) (p := 2) n) (fourierLp (T := (1 : ℝ)) (p := 2) m) =
      (if n = m then (1 : ℂ) else 0)) ∧
    ‖fourierLp (T := (1 : ℝ)) (p := 2) n‖ = (1 : ℝ) := by
  have hOrtho : Orthonormal ℂ (fourierLp (T := (1 : ℝ)) (p := 2)) :=
    orthonormal_fourier (T := (1 : ℝ))
  constructor
  · exact (orthonormal_iff_ite.mp hOrtho) n m
  · exact hOrtho.norm_eq_one n

/-- Definition 5.3.2 (Trigonometric polynomials): a function
`f ∈ C(ℝ/ℤ; ℂ)` is a trigonometric polynomial if
`f = ∑_{n=-N}^{N} c_n e_n` for some integer bound `N ≥ 0` and coefficients `c_n ∈ ℂ`. -/
def IsTrigonometricPolynomial (f : C(AddCircle (1 : ℝ), ℂ)) : Prop :=
  ∃ N : ℕ, ∃ c : ℤ → ℂ,
    f = Finset.sum (Finset.Icc (-(N : ℤ)) (N : ℤ)) (fun n => c n • fourierCharacter n)

/-- Helper for Corollary 5.3.6: coefficient extraction on a finite support set. -/
lemma helperForCorollary_5_3_6_inner_on_support
    (s : Finset ℤ) (c : ℤ → ℂ) {n : ℤ} (hn : n ∈ s) :
    inner ℂ (fourierLp (T := (1 : ℝ)) (p := 2) n)
      (Finset.sum s (fun k => c k • fourierLp (T := (1 : ℝ)) (p := 2) k)) = c n := by
  have hOrtho : Orthonormal ℂ (fourierLp (T := (1 : ℝ)) (p := 2)) :=
    orthonormal_fourier (T := (1 : ℝ))
  simpa using hOrtho.inner_right_sum c hn

/-- Helper for Corollary 5.3.6: coefficient vanishing outside a finite support set. -/
lemma helperForCorollary_5_3_6_inner_off_support
    (s : Finset ℤ) (c : ℤ → ℂ) {n : ℤ} (hn : n ∉ s) :
    inner ℂ (fourierLp (T := (1 : ℝ)) (p := 2) n)
      (Finset.sum s (fun k => c k • fourierLp (T := (1 : ℝ)) (p := 2) k)) = 0 := by
  have hOrtho : Orthonormal ℂ (fourierLp (T := (1 : ℝ)) (p := 2)) :=
    orthonormal_fourier (T := (1 : ℝ))
  have hOrthoIte := orthonormal_iff_ite.mp hOrtho
  classical
  calc
    inner ℂ (fourierLp (T := (1 : ℝ)) (p := 2) n)
        (Finset.sum s (fun k => c k • fourierLp (T := (1 : ℝ)) (p := 2) k))
        = Finset.sum s
            (fun k => c k *
              inner ℂ (fourierLp (T := (1 : ℝ)) (p := 2) n)
                (fourierLp (T := (1 : ℝ)) (p := 2) k)) := by
          simp [inner_sum, inner_smul_right]
    _ = Finset.sum s (fun k => c k * (if n = k then (1 : ℂ) else 0)) := by
          simp [hOrthoIte]
    _ = 0 := by
          refine Finset.sum_eq_zero ?_
          intro k hk
          by_cases hnk : n = k
          · exfalso
            exact hn (hnk ▸ hk)
          · simp [hnk]

/-- Helper for Corollary 5.3.6: finite Parseval identity for a finite Fourier sum. -/
lemma helperForCorollary_5_3_6_normSq_finite_sum
    (s : Finset ℤ) (c : ℤ → ℂ) :
    ‖Finset.sum s (fun k => c k • fourierLp (T := (1 : ℝ)) (p := 2) k)‖ ^ (2 : ℕ) =
      Finset.sum s (fun k => ‖c k‖ ^ (2 : ℕ)) := by
  let f := Finset.sum s (fun k => c k • fourierLp (T := (1 : ℝ)) (p := 2) k)
  have hOrtho : Orthonormal ℂ (fourierLp (T := (1 : ℝ)) (p := 2)) :=
    orthonormal_fourier (T := (1 : ℝ))
  have hInner :
      inner ℂ f f = Finset.sum s (fun k => (starRingEnd ℂ) (c k) * c k) := by
    simpa [f] using hOrtho.inner_sum c c s
  have hReal : ‖f‖ ^ (2 : ℕ) = Finset.sum s (fun k => ‖c k‖ ^ (2 : ℕ)) := by
    calc
      ‖f‖ ^ (2 : ℕ) = Complex.re (inner ℂ f f) := by
        simpa using (norm_sq_eq_re_inner (𝕜 := ℂ) f)
      _ = Complex.re (Finset.sum s (fun k => (starRingEnd ℂ) (c k) * c k)) := by
        rw [hInner]
      _ = Finset.sum s (fun k => ‖c k‖ ^ (2 : ℕ)) := by
        simp [RCLike.conj_mul, pow_two]
  simpa [f] using hReal

/-- Corollary 5.3.6: for a trigonometric polynomial
`f = ∑_{n=-N}^{N} c_n e_n`, the Fourier coefficient at each `n` in the support interval is
`c_n`, the coefficients outside that interval vanish, and
`‖f‖_2^2 = ∑_{n=-N}^{N} |c_n|^2`. -/
theorem trigonometricPolynomial_fourierCoefficients_and_normSq (N : ℕ) (c : ℤ → ℂ) :
    let f :=
      Finset.sum (Finset.Icc (-(N : ℤ)) (N : ℤ))
        (fun n => c n • fourierLp (T := (1 : ℝ)) (p := 2) n)
    (∀ n : ℤ,
      n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) →
        inner ℂ (fourierLp (T := (1 : ℝ)) (p := 2) n) f = c n) ∧
    (∀ n : ℤ,
      n ∉ Finset.Icc (-(N : ℤ)) (N : ℤ) →
        inner ℂ (fourierLp (T := (1 : ℝ)) (p := 2) n) f = 0) ∧
    ‖f‖ ^ (2 : ℕ) =
      Finset.sum (Finset.Icc (-(N : ℤ)) (N : ℤ)) (fun n => ‖c n‖ ^ (2 : ℕ)) := by
  let s : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)
  let f := Finset.sum s (fun n => c n • fourierLp (T := (1 : ℝ)) (p := 2) n)
  change
    (∀ n : ℤ, n ∈ s → inner ℂ (fourierLp (T := (1 : ℝ)) (p := 2) n) f = c n) ∧
    (∀ n : ℤ, n ∉ s → inner ℂ (fourierLp (T := (1 : ℝ)) (p := 2) n) f = 0) ∧
    ‖f‖ ^ (2 : ℕ) = Finset.sum s (fun n => ‖c n‖ ^ (2 : ℕ))
  constructor
  · intro n hn
    simpa [f] using helperForCorollary_5_3_6_inner_on_support s c hn
  · constructor
    · intro n hn
      simpa [f] using helperForCorollary_5_3_6_inner_off_support s c hn
    · simpa [f] using helperForCorollary_5_3_6_normSq_finite_sum s c

/-- Definition 5.3.7 (Fourier transform): for `f ∈ C(ℝ/ℤ; ℂ)`, its Fourier transform is the
function `ℤ → ℂ` sending `n` to the `n`-th Fourier coefficient
`∫ x in (0 : ℝ)..1, f x * exp (-2π i n x)`. -/
noncomputable def fourierTransform (f : C(AddCircle (1 : ℝ), ℂ)) : ℤ → ℂ :=
  fourierCoeff f

/-- For `f ∈ C(ℝ/ℤ; ℂ)`, the Fourier series term family is
`n ↦ \hat f(n) e_n`. -/
noncomputable def fourierSeriesOnAddCircle (f : C(AddCircle (1 : ℝ), ℂ)) :
    ℤ → C(AddCircle (1 : ℝ), ℂ) :=
  fun n => (fourierTransform f n) • fourierCharacter n

/-- Definition 5.3.8 (Fourier inversion, Fourier series, and Plancherel formula):
for `f ∈ C(ℝ/ℤ; ℂ)`, the Fourier series is the formal family `n ↦ \hat f(n) e_n`; if `f`
is a trigonometric polynomial, then `f` equals a finite sum of these Fourier-series terms;
and in the same finite case one has the Parseval/Plancherel identity. -/
def fourierSeries_inversion_plancherel_onAddCircle
    (f : C(AddCircle (1 : ℝ), ℂ)) : Prop :=
    (fourierSeriesOnAddCircle f =
      fun n : ℤ => (fourierTransform f n) • fourierCharacter n) ∧
    (IsTrigonometricPolynomial f →
      ∃ s : Finset ℤ,
        (∀ n : ℤ, n ∉ s → fourierTransform f n = 0) ∧
        f = Finset.sum s (fun n => fourierSeriesOnAddCircle f n)) ∧
    (IsTrigonometricPolynomial f →
      ∃ s : Finset ℤ,
        (∀ n : ℤ, n ∉ s → fourierTransform f n = 0) ∧
        (∫ x : AddCircle (1 : ℝ), ‖f x‖ ^ (2 : ℕ)
          ∂(AddCircle.haarAddCircle : MeasureTheory.Measure (AddCircle (1 : ℝ)))) =
          Finset.sum s (fun n => ‖fourierTransform f n‖ ^ (2 : ℕ)))

/-- Bridge `fourierTransform` to the `L²` inner product with Fourier modes. -/
lemma fourierTransform_eq_inner_fourierLp_toLp
    (f : C(AddCircle (1 : ℝ), ℂ)) (n : ℤ) :
    fourierTransform f n =
      inner ℂ (fourierLp (T := (1 : ℝ)) (p := 2) n)
        (ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ f) := by
  calc
    fourierTransform f n
        = fourierCoeff (↑↑((ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ) f)) n := by
            simpa [fourierTransform] using (fourierCoeff_toLp (T := (1 : ℝ)) (f := f) n).symm
    _ = (fourierBasis (T := (1 : ℝ))).repr
          (ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ f) n := by
          simpa using (fourierBasis_repr (T := (1 : ℝ))
            (f := (ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ f)) (i := n)).symm
    _ = inner ℂ ((fourierBasis (T := (1 : ℝ))) n)
          (ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ f) := by
          simpa using (HilbertBasis.repr_apply_apply (fourierBasis (T := (1 : ℝ)))
            (ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ f) n)
    _ = inner ℂ (fourierLp (T := (1 : ℝ)) (p := 2) n)
          (ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ f) := by
          simp [coe_fourierBasis]

/-- If `f` is a trigonometric polynomial, then `f` equals a finite sum of its Fourier-series
terms (Fourier inversion in the finite case). -/
theorem trigonometricPolynomial_fourierInversion
    (f : C(AddCircle (1 : ℝ), ℂ)) (hf : IsTrigonometricPolynomial f) :
    ∃ s : Finset ℤ,
      (∀ n : ℤ, n ∉ s → fourierTransform f n = 0) ∧
      f = Finset.sum s (fun n => fourierSeriesOnAddCircle f n) := by
  rcases hf with ⟨N, c, hrepr⟩
  let s : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)
  have hreprLp :
      ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ f =
        Finset.sum s (fun k => c k • fourierLp (T := (1 : ℝ)) (p := 2) k) := by
    have h := congrArg (ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ) hrepr
    simpa [s, fourierCharacter, map_sum] using h
  have hcoeff_on : ∀ n : ℤ, n ∈ s → fourierTransform f n = c n := by
    intro n hn
    rw [fourierTransform_eq_inner_fourierLp_toLp]
    rw [hreprLp]
    simpa using helperForCorollary_5_3_6_inner_on_support s c hn
  have hcoeff_off : ∀ n : ℤ, n ∉ s → fourierTransform f n = 0 := by
    intro n hn
    rw [fourierTransform_eq_inner_fourierLp_toLp]
    rw [hreprLp]
    simpa using helperForCorollary_5_3_6_inner_off_support s c hn
  refine ⟨s, hcoeff_off, ?_⟩
  calc
    f = Finset.sum s (fun n => c n • fourierCharacter n) := by
      simpa [s] using hrepr
    _ = Finset.sum s (fun n => fourierSeriesOnAddCircle f n) := by
      refine Finset.sum_congr rfl ?_
      intro n hn
      simp [fourierSeriesOnAddCircle, hcoeff_on n hn]

/-- If `f` is a trigonometric polynomial, then the finite Parseval/Plancherel identity holds:
the `L²` norm identity on `AddCircle` equals a finite sum of squared Fourier coefficients. -/
theorem trigonometricPolynomial_plancherel_formula
    (f : C(AddCircle (1 : ℝ), ℂ)) (hf : IsTrigonometricPolynomial f) :
    ∃ s : Finset ℤ,
      (∀ n : ℤ, n ∉ s → fourierTransform f n = 0) ∧
      (∫ x : AddCircle (1 : ℝ), ‖f x‖ ^ (2 : ℕ)
        ∂(AddCircle.haarAddCircle : MeasureTheory.Measure (AddCircle (1 : ℝ)))) =
        Finset.sum s (fun n => ‖fourierTransform f n‖ ^ (2 : ℕ)) := by
  rcases trigonometricPolynomial_fourierInversion f hf with ⟨s, hOff, _⟩
  have hOffCoeff : ∀ n : ℤ, n ∉ s → fourierCoeff f n = 0 := by
    intro n hn
    simpa [fourierTransform] using hOff n hn
  have hParsevalCoeff :
      (∑' n : ℤ, ‖fourierCoeff f n‖ ^ (2 : ℕ)) =
        (∫ x : AddCircle (1 : ℝ), ‖f x‖ ^ (2 : ℕ)
          ∂(AddCircle.haarAddCircle : MeasureTheory.Measure (AddCircle (1 : ℝ)))) := by
    have htsum :=
      tsum_sq_fourierCoeff (T := (1 : ℝ))
        (ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ f)
    have hcoeffNorm :
        ∀ n : ℤ,
          ‖fourierCoeff f n‖ ^ (2 : ℕ) =
            ‖fourierCoeff (ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ f) n‖ ^
              (2 : ℕ) := by
      intro n
      simpa using congrArg (fun z : ℂ => ‖z‖ ^ (2 : ℕ))
        (fourierCoeff_toLp (T := (1 : ℝ)) (f := f) n).symm
    have hcoe :
        (ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ f)
          =ᵐ[AddCircle.haarAddCircle] f :=
      by
        simpa using (ContinuousMap.coeFn_toLp (E := ℂ) (p := (2 : ENNReal))
          (μ := AddCircle.haarAddCircle) (𝕜 := ℂ) f)
    calc
      (∑' n : ℤ, ‖fourierCoeff f n‖ ^ (2 : ℕ))
          = ∑' n : ℤ,
              ‖fourierCoeff (ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ f) n‖ ^
                (2 : ℕ) := by
              exact tsum_congr hcoeffNorm
      _ = ∫ x : AddCircle (1 : ℝ),
            ‖(ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ f) x‖ ^ (2 : ℕ)
              ∂(AddCircle.haarAddCircle : MeasureTheory.Measure (AddCircle (1 : ℝ))) := by
                simpa using htsum
      _ = (∫ x : AddCircle (1 : ℝ), ‖f x‖ ^ (2 : ℕ)
            ∂(AddCircle.haarAddCircle : MeasureTheory.Measure (AddCircle (1 : ℝ)))) := by
            exact MeasureTheory.integral_congr_ae <|
              hcoe.mono (fun x hx => by
                simpa using congrArg (fun z : ℂ => ‖z‖ ^ (2 : ℕ)) hx)
  have htsumToFinsetCoeff :
      (∑' n : ℤ, ‖fourierCoeff f n‖ ^ (2 : ℕ)) =
        Finset.sum s (fun n => ‖fourierCoeff f n‖ ^ (2 : ℕ)) := by
    refine tsum_eq_sum (s := s) ?_
    intro n hn
    simp [hOffCoeff n hn]
  refine ⟨s, hOff, ?_⟩
  calc
    (∫ x : AddCircle (1 : ℝ), ‖f x‖ ^ (2 : ℕ)
      ∂(AddCircle.haarAddCircle : MeasureTheory.Measure (AddCircle (1 : ℝ))))
        = (∑' n : ℤ, ‖fourierCoeff f n‖ ^ (2 : ℕ)) := hParsevalCoeff.symm
    _ = Finset.sum s (fun n => ‖fourierCoeff f n‖ ^ (2 : ℕ)) := htsumToFinsetCoeff
    _ = Finset.sum s (fun n => ‖fourierTransform f n‖ ^ (2 : ℕ)) := by
          simp [fourierTransform]

end Section03
end Chap05
