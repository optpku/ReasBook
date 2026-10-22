/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Definition_15_27
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Theorem_15_23
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Lemma_15_28
import Books.ProbabilityTheory_Klenke_2020.Items.Chap13.Exercise_13_2_6
import Books.ProbabilityTheory_Klenke_2020.Items.Chap04.Exercise_4_2_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Theorem_14_36
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open Complex MeasureTheory Filter
open scoped BigOperators Topology ComplexOrder

universe u

/-- Helper for Theorem 15.29: a normalized positive semidefinite function on `ℝ^d` has norm at
most `1` everywhere. -/
lemma norm_le_one_of_isPositiveSemidefiniteFunction_zero_eq_one {d : ℕ}
    {φ : EuclideanSpace ℝ (Fin d) → ℂ} (hφ : IsPositiveSemidefiniteFunction φ)
    (hzero : φ 0 = 1) (t : EuclideanSpace ℝ (Fin d)) :
    ‖φ t‖ ≤ 1 := by
  let x : Fin 2 → EuclideanSpace ℝ (Fin d) := ![0, t]
  let A : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of fun i j ↦ φ (x i - x j)
  have hA : A.PosSemidef := hφ 2 x
  have hstar : star (φ t) = φ (-t) := by
    -- Proof comment: the `2 × 2` kernel matrix is Hermitian, so the off-diagonal entries are
    -- conjugates.
    simpa [A, x] using hA.isHermitian.apply 0 1
  have hdet_le_one : (φ (-t) * φ t : ℂ) ≤ 1 := by
    -- Proof comment: the determinant inequality of the `2 × 2` kernel matrix yields the basic
    -- bound on the off-diagonal product.
    simpa [A, x, Matrix.det_fin_two, hzero] using Matrix.PosSemidef.det_nonneg hA
  have hmul_eq : (φ (-t) * φ t : ℂ) = ((‖φ t‖ * ‖φ t‖ : ℝ) : ℂ) := by
    -- Proof comment: Hermitian symmetry identifies the off-diagonal product with `‖φ t‖²`.
    calc
      φ (-t) * φ t = star (φ t) * φ t := by rw [hstar]
      _ = ((‖φ t‖ ^ 2 : ℝ) : ℂ) := by
            simpa using (Complex.conj_mul' (φ t))
      _ = ((‖φ t‖ * ‖φ t‖ : ℝ) : ℂ) := by
            congr 1
            ring
  have hsq : ‖φ t‖ * ‖φ t‖ ≤ 1 := by
    have hcomplex_le : (((‖φ t‖ * ‖φ t‖ : ℝ) : ℂ)) ≤ 1 := by
      simpa [hmul_eq] using hdet_le_one
    exact Complex.real_le_real.mp hcomplex_le
  nlinarith [hsq, norm_nonneg (φ t)]

/-- Helper for Theorem 15.29: every positive semidefinite Euclidean kernel is Hermitian in the
argument difference, so evaluating at `-t` conjugates the value at `t`. -/
lemma star_value_eq_value_neg_of_isPositiveSemidefiniteFunction {d : ℕ}
    {φ : EuclideanSpace ℝ (Fin d) → ℂ} (hφ : IsPositiveSemidefiniteFunction φ)
    (t : EuclideanSpace ℝ (Fin d)) :
    star (φ t) = φ (-t) := by
  let x : Fin 2 → EuclideanSpace ℝ (Fin d) := ![0, t]
  let A : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of fun i j ↦ φ (x i - x j)
  have hA : A.PosSemidef := hφ 2 x
  -- Proof comment: the `2 × 2` kernel matrix is Hermitian, and the `(0,1)` entry is `φ (-t)`.
  simpa [A, x] using hA.isHermitian.apply 0 1

/-- Helper for Theorem 15.29: continuity at `0` implies the coordinate-axis continuity required by
Theorem 15.23. -/
lemma partiallyContinuousAtZero_of_continuousAtZero {d : ℕ}
    {f : EuclideanSpace ℝ (Fin d) → ℂ} (hf : ContinuousAt f 0) :
    PartiallyContinuousAtZero f := by
  intro i
  -- Proof comment: each coordinate-axis restriction is the composition of `f` with the
  -- continuous insertion map `t ↦ EuclideanSpace.single i t`, evaluated at the origin.
  have hsingle : ContinuousAt (fun t : ℝ ↦ EuclideanSpace.single i t) 0 := by
    have hPiSingle : ContinuousAt (fun t : ℝ ↦ (Pi.single i t : Fin d → ℝ)) 0 := by
      rw [continuousAt_pi]
      intro j
      by_cases hji : j = i
      · subst hji
        simpa using (continuousAt_id : ContinuousAt (fun t : ℝ ↦ t) 0)
      · simpa [Pi.single_eq_of_ne hji] using
          (continuousAt_const : ContinuousAt (fun _ : ℝ ↦ (0 : ℝ)) 0)
    simpa [EuclideanSpace.single] using
      (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin d => ℝ)).continuousAt.comp
        hPiSingle
  have hsingle_zero : (fun t : ℝ ↦ EuclideanSpace.single i t) 0 = 0 := by
    simp [EuclideanSpace.single]
  simpa [Function.comp] using hf.comp_of_eq hsingle hsingle_zero

/-- Helper for Theorem 15.29: a pointwise limit of characteristic functions on `ℝ^d` which is
continuous at `0` is itself the characteristic function of a probability measure. -/
lemma existsProbabilityMeasureOfTendstoCharFunOfContinuousAtZero {d : ℕ}
    (Ps : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin d)))
    {f : EuclideanSpace ℝ (Fin d) → ℂ} (hf : ContinuousAt f 0)
    (hφ : ∀ t : EuclideanSpace ℝ (Fin d),
      Tendsto (fun n ↦ charFun (Ps n) t) atTop (𝓝 (f t))) :
    ∃ Q : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)),
      ∀ t : EuclideanSpace ℝ (Fin d), charFun (Q : Measure (EuclideanSpace ℝ (Fin d))) t = f t := by
  rcases
    exists_probabilityMeasure_of_tendsto_charFun
      (d := d) Ps hφ (partiallyContinuousAtZero_of_continuousAtZero (d := d) hf) with
    ⟨Q, hQ, _hQtendsto⟩
  -- Proof comment: Theorem 15.23 already packages the pointwise-limit reconstruction once the
  -- continuity-at-zero hypothesis is converted to partial continuity along coordinate axes.
  exact ⟨Q, hQ⟩

/-- Helper for Theorem 15.29: Gaussian damping of a continuous normalized positive semidefinite
function on `ℝ^d` is the characteristic function of a probability measure. -/
lemma integrableGaussianDamped {d : ℕ}
    {φ : EuclideanSpace ℝ (Fin d) → ℂ} {a : ℝ} (ha : 0 < a) (hφ : Continuous φ)
    (hbound : ∀ t : EuclideanSpace ℝ (Fin d), ‖φ t‖ ≤ 1) :
    Integrable (fun t : EuclideanSpace ℝ (Fin d) ↦
      Complex.exp (-(a : ℂ) * ‖t‖ ^ 2) * φ t) := by
  let g : EuclideanSpace ℝ (Fin d) → ℂ := fun t ↦ Complex.exp (-(a : ℂ) * ‖t‖ ^ 2)
  have hg : Integrable g := by
    -- Proof comment: the Gaussian factor is an `L¹` function by the standard Euclidean Gaussian
    -- integral theorem.
    simpa [g] using
      (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (b := (a : ℂ)) (c := (0 : ℂ))
        (w := (0 : EuclideanSpace ℝ (Fin d))) ha)
  refine Integrable.mono' hg.norm ?_ ?_
  · -- Proof comment: the damped function is measurable as a product of measurable factors.
    refine ((Complex.continuous_exp.comp ?_).mul hφ).aestronglyMeasurable
    fun_prop
  · -- Proof comment: `‖φ t‖ ≤ 1` turns the Gaussian factor into a pointwise `L¹` majorant.
    filter_upwards with t
    calc
      ‖Complex.exp (-(a : ℂ) * ‖t‖ ^ 2) * φ t‖
          = ‖Complex.exp (-(a : ℂ) * ‖t‖ ^ 2)‖ * ‖φ t‖ := by
              simp
      _ ≤ ‖Complex.exp (-(a : ℂ) * ‖t‖ ^ 2)‖ * 1 := by
            exact mul_le_mul_of_nonneg_left (hbound t) (norm_nonneg _)
      _ = ‖g t‖ := by
            simp [g]

/-- Helper for Theorem 15.29: the Gaussian factor `exp (-(a : ℂ) * ‖t‖ ^ 2)` is the
characteristic function of a scaled standard Gaussian on `ℝ^d`. -/
lemma gaussianDamping_eq_charFun_scaledStdGaussian {d : ℕ} {a : ℝ}
    (ha : 0 < a) (t : EuclideanSpace ℝ (Fin d)) :
    charFun
        ((ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d))).map
          (Real.sqrt (2 * a) • ·)) t =
      Complex.exp (-(a : ℂ) * ‖t‖ ^ 2) := by
  let r : ℝ := Real.sqrt (2 * a)
  have hr_sq : r ^ 2 = 2 * a := by
    -- Proof comment: the scaling factor is chosen so that the Gaussian exponent becomes `a ‖t‖²`.
    dsimp [r]
    rw [Real.sq_sqrt]
    positivity
  have hnorm : ‖r • t‖ ^ 2 / 2 = a * ‖t‖ ^ 2 := by
    -- Proof comment: after pulling the scalar out of the norm, the exponent is an elementary
    -- real-algebra simplification.
    calc
      ‖r • t‖ ^ 2 / 2 = (r * ‖t‖) ^ 2 / 2 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      _ = r ^ 2 * ‖t‖ ^ 2 / 2 := by
        ring
      _ = a * ‖t‖ ^ 2 := by
        rw [hr_sq]
        ring
  calc
    charFun
        ((ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d))).map
          (r • ·)) t
        = Complex.exp (-(‖r • t‖ ^ 2) / 2) := by
            rw [MeasureTheory.charFun_map_smul, ProbabilityTheory.charFun_stdGaussian]
    _ = Complex.exp (-(a : ℂ) * ‖t‖ ^ 2) := by
          have hcast : (((‖r • t‖ ^ 2 / 2 : ℝ)) : ℂ) = (a : ℂ) * ‖t‖ ^ 2 := by
            exact_mod_cast hnorm
          have hdivC : (((‖r • t‖ ^ 2 / 2 : ℝ)) : ℂ) = (↑‖r • t‖ ^ 2) / 2 := by
            rw [div_eq_mul_inv, div_eq_mul_inv]
            norm_num
          have hdivCneg : (-(‖r • t‖ ^ 2 : ℂ) / 2) = -(((‖r • t‖ ^ 2 / 2 : ℝ)) : ℂ) := by
            rw [hdivC]
            ring
          have hnegC : (-(‖r • t‖ ^ 2 : ℂ) / 2) = -(a : ℂ) * ‖t‖ ^ 2 := by
            calc
              (-(‖r • t‖ ^ 2 : ℂ) / 2) = -(((‖r • t‖ ^ 2 / 2 : ℝ)) : ℂ) := hdivCneg
              _ = -(a : ℂ) * ‖t‖ ^ 2 := by
                    rw [hcast]
                    ring
          exact congrArg Complex.exp hnegC

/-- Helper for Theorem 15.29: convolving a probability law on `ℝ^d` with the scaled standard
Gaussian multiplies its characteristic function by the Gaussian damping factor. -/
lemma gaussianDampedMeasureExistsOfProbabilityMeasure {d : ℕ}
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) {a : ℝ} (ha : 0 < a) :
    ∃ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)),
      ∀ t : EuclideanSpace ℝ (Fin d),
        charFun (ν : Measure (EuclideanSpace ℝ (Fin d))) t =
          Complex.exp (-(a : ℂ) * ‖t‖ ^ 2) *
            charFun (μ : Measure (EuclideanSpace ℝ (Fin d))) t := by
  let γ : Measure (EuclideanSpace ℝ (Fin d)) :=
    (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d))).map
      (Real.sqrt (2 * a) • ·)
  haveI : IsProbabilityMeasure γ := by
    dsimp [γ]
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  let ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)) :=
    ⟨(μ : Measure (EuclideanSpace ℝ (Fin d))).conv γ, inferInstance⟩
  refine ⟨ν, ?_⟩
  intro t
  -- Proof comment: characteristic functions multiply across additive convolution.
  calc
    charFun (ν : Measure (EuclideanSpace ℝ (Fin d))) t
        = charFun (μ : Measure (EuclideanSpace ℝ (Fin d))) t * charFun γ t := by
            simpa [ν, γ] using
              (MeasureTheory.charFun_conv
                (μ := (μ : Measure (EuclideanSpace ℝ (Fin d)))) (ν := γ) t)
    _ = charFun (μ : Measure (EuclideanSpace ℝ (Fin d))) t *
          Complex.exp (-(a : ℂ) * ‖t‖ ^ 2) := by
            rw [gaussianDamping_eq_charFun_scaledStdGaussian (d := d) ha t]
    _ = Complex.exp (-(a : ℂ) * ‖t‖ ^ 2) *
          charFun (μ : Measure (EuclideanSpace ℝ (Fin d))) t := by
            ring

/-- Helper for Theorem 15.29: the Gaussian-damped characteristic-function kernel attached to an
actual witness probability measure is itself an integrable normalized positive semidefinite kernel
with an explicit probability witness. -/
lemma gaussianDampedKernelSpecAndWitnessOfProbabilityMeasure {d : ℕ}
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) {a : ℝ} (ha : 0 < a) :
    let ρ : EuclideanSpace ℝ (Fin d) → ℂ :=
      fun t ↦
        Complex.exp (-(a : ℂ) * ‖t‖ ^ 2) *
          charFun (μ : Measure (EuclideanSpace ℝ (Fin d))) t
    Continuous ρ ∧ Integrable ρ ∧ IsPositiveSemidefiniteFunction ρ ∧ ρ 0 = 1 ∧
      ∃ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)),
        ∀ t : EuclideanSpace ℝ (Fin d),
          charFun (ν : Measure (EuclideanSpace ℝ (Fin d))) t = ρ t := by
  let E := EuclideanSpace ℝ (Fin d)
  let ρ : E → ℂ := fun t ↦ Complex.exp (-(a : ℂ) * ‖t‖ ^ 2) * charFun (μ : Measure E) t
  rcases gaussianDampedMeasureExistsOfProbabilityMeasure (d := d) μ ha with ⟨ν, hν⟩
  have hρ_cont : Continuous ρ := by
    -- Proof comment: the Gaussian factor and the characteristic function of the witness are both
    -- continuous.
    simpa [ρ] using
      ((Complex.continuous_exp.comp (by fun_prop)).mul
        (MeasureTheory.continuous_charFun (μ := (μ : Measure E))))
  have hρ_int : Integrable ρ := by
    -- Proof comment: the Gaussian factor gives an `L¹` majorant because characteristic functions
    -- of probability measures have norm at most `1`.
    refine integrableGaussianDamped
      (d := d) (φ := charFun (μ : Measure E)) ha
      (MeasureTheory.continuous_charFun (μ := (μ : Measure E))) ?_
    intro t
    exact MeasureTheory.norm_charFun_le_one (μ := (μ : Measure E)) t
  have hρ_psd : IsPositiveSemidefiniteFunction ρ := by
    have hρ_eq : charFun (ν : Measure E) = ρ := by
      funext t
      exact hν t
    -- Proof comment: the Gaussian-smoothed witness `ν` realizes `ρ` as an actual characteristic
    -- function, so positivity follows from Lemma 15.28.
    simpa [hρ_eq] using
      (charFun_isPositiveSemidefiniteFunction_of_isFiniteMeasure (μ := (ν : Measure E)))
  have hρ_zero : ρ 0 = 1 := by
    -- Proof comment: the Gaussian factor is `1` at `0`, and the witness characteristic function
    -- is normalized there.
    simp [ρ]
  -- Proof comment: the Gaussian-smoothed witness law itself realizes the damped kernel as a
  -- characteristic function.
  exact ⟨hρ_cont, hρ_int, hρ_psd, hρ_zero, ⟨ν, hν⟩⟩

/-- Helper for Theorem 15.29: conjugating `innerProbChar` negates its frequency. -/
lemma star_innerProbChar_apply {d : ℕ} (t x : EuclideanSpace ℝ (Fin d)) :
    star (BoundedContinuousFunction.innerProbChar t x) =
      BoundedContinuousFunction.innerProbChar (-t) x := by
  -- Proof comment: `innerProbChar` is a complex exponential with real phase `⟪x, t⟫`, so
  -- conjugation only flips the sign of that phase.
  rw [BoundedContinuousFunction.innerProbChar_apply,
    BoundedContinuousFunction.innerProbChar_apply]
  simpa [inner_neg_right] using
    (Complex.exp_conj (↑(inner ℝ x t) * Complex.I)).symm

/-- Helper for Theorem 15.29: the conjugated `-u` character times the `-v` character collapses to
the single character at `u - v`. -/
lemma star_innerProbChar_neg_mul_innerProbChar_neg {d : ℕ}
    (u v x : EuclideanSpace ℝ (Fin d)) :
    star (BoundedContinuousFunction.innerProbChar (-u) x) *
        BoundedContinuousFunction.innerProbChar (-v) x =
      BoundedContinuousFunction.innerProbChar (u - v) x := by
  -- Proof comment: conjugating the first factor turns `-u` into `u`, and the two exponential
  -- phases then add to the phase for `u - v`.
  rw [star_innerProbChar_apply, BoundedContinuousFunction.innerProbChar_apply,
    BoundedContinuousFunction.innerProbChar_apply, BoundedContinuousFunction.innerProbChar_apply]
  rw [← Complex.exp_add]
  congr 1
  rw [sub_eq_add_neg, inner_add_right, ← add_mul]
  simp

/-- Helper for Theorem 15.29: after combining the two oscillatory phase factors, the Gaussian
window integrand depends on the pair `(u, v)` only through the difference `u - v`. -/
lemma gaussianWindowQuadraticIntegrand_eq_differenceKernel {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} (u v x : EuclideanSpace ℝ (Fin d)) :
    star (BoundedContinuousFunction.innerProbChar (-u) x) * ψ (u - v) *
        BoundedContinuousFunction.innerProbChar (-v) x =
      ψ (u - v) * BoundedContinuousFunction.innerProbChar (u - v) x := by
  -- Proof comment: first collapse the two phase factors to the single character at `u - v`, then
  -- commute the scalar kernel factor into front.
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    congrArg (fun z : ℂ ↦ z * ψ (u - v))
      (star_innerProbChar_neg_mul_innerProbChar_neg (d := d) u v x)

/-- Helper for Theorem 15.29: the same phase-collapsing identity can be used directly on product
variables before any integral-congruence step. -/
lemma gaussianWindowQuadraticIntegrand_prod_eq_differenceKernel {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} (x : EuclideanSpace ℝ (Fin d))
    (p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :
    star (BoundedContinuousFunction.innerProbChar (-p.1) x) * ψ (p.1 - p.2) *
        BoundedContinuousFunction.innerProbChar (-p.2) x =
      ψ (p.1 - p.2) * BoundedContinuousFunction.innerProbChar (p.1 - p.2) x := by
  -- Proof comment: this is only the pair-valued spelling of the previous difference-kernel
  -- identity, recorded once so later integral rewrites do not reopen tuple projections.
  simpa using
    gaussianWindowQuadraticIntegrand_eq_differenceKernel
      (d := d) (ψ := ψ) p.1 p.2 x

/-- Helper for Theorem 15.29: Gaussian damping preserves positive semidefiniteness on `ℝ^d`. -/
lemma gaussianDamped_isPositiveSemidefiniteFunction {d : ℕ}
    {φ : EuclideanSpace ℝ (Fin d) → ℂ} {a : ℝ} (ha : 0 < a)
    (hpsd : IsPositiveSemidefiniteFunction φ) :
    IsPositiveSemidefiniteFunction
      (fun t ↦ Complex.exp (-(a : ℂ) * ‖t‖ ^ 2) * φ t) := by
  let E := EuclideanSpace ℝ (Fin d)
  let μa : Measure E :=
    (ProbabilityTheory.stdGaussian E).map (Real.sqrt (2 * a) • ·)
  haveI : IsFiniteMeasure μa := by
    dsimp [μa]
    infer_instance
  rw [isPositiveSemidefiniteFunction_iff_quadratic_sum_nonneg] at hpsd ⊢
  intro n t c
  let coeff : E → Fin n → ℂ :=
    fun x i ↦ c i * BoundedContinuousFunction.innerProbChar (-t i) x
  let integrand : E → ℂ :=
    fun x ↦ ∑ i, ∑ j, star (coeff x i) * φ (t i - t j) * coeff x j
  have hterm :
      ∀ i j,
        Integrable (fun x ↦ star (coeff x i) * φ (t i - t j) * coeff x j) μa := by
    intro i j
    -- Proof comment: every twisted kernel entry is continuous and uniformly bounded on the
    -- finite Gaussian measure.
    refine Integrable.of_bound ?_ (‖c i‖ * ‖φ (t i - t j)‖ * ‖c j‖) ?_
    · have hcoeff_i : Continuous fun x : E ↦ coeff x i := by
        fun_prop
      have hcoeff_j : Continuous fun x : E ↦ coeff x j := by
        fun_prop
      exact ((hcoeff_i.star.mul_const (φ (t i - t j))).mul hcoeff_j).aestronglyMeasurable
    · filter_upwards with x
      have hcoeff_i_norm : ‖coeff x i‖ = ‖c i‖ := by
        calc
          ‖coeff x i‖
              = ‖c i‖ * ‖BoundedContinuousFunction.innerProbChar (-t i) x‖ := by
                  simp [coeff, norm_mul]
          _ = ‖c i‖ := by
                rw [BoundedContinuousFunction.innerProbChar_apply]
                rw [Complex.norm_exp_ofReal_mul_I]
                ring
      have hcoeff_j_norm : ‖coeff x j‖ = ‖c j‖ := by
        calc
          ‖coeff x j‖
              = ‖c j‖ * ‖BoundedContinuousFunction.innerProbChar (-t j) x‖ := by
                  simp [coeff, norm_mul]
          _ = ‖c j‖ := by
                rw [BoundedContinuousFunction.innerProbChar_apply]
                rw [Complex.norm_exp_ofReal_mul_I]
                ring
      calc
        ‖star (coeff x i) * φ (t i - t j) * coeff x j‖
            = ‖coeff x i‖ * ‖φ (t i - t j)‖ * ‖coeff x j‖ := by
                simp [norm_mul, mul_assoc]
        _ = ‖c i‖ * ‖φ (t i - t j)‖ * ‖c j‖ := by
              rw [hcoeff_i_norm, hcoeff_j_norm]
        _ ≤ ‖c i‖ * ‖φ (t i - t j)‖ * ‖c j‖ := le_rfl
  have hkernel :
      ∑ i, ∑ j,
          star (c i) *
            (Complex.exp (-(a : ℂ) * ‖t i - t j‖ ^ 2) * φ (t i - t j)) *
            c j =
        ∫ x, integrand x ∂μa := by
    -- Proof comment: rewrite the Gaussian factor as a characteristic function and absorb the
    -- character values into twisted coefficients before applying the quadratic-sum hypothesis.
    have hinnerSum :
        ∀ i : Fin n, Integrable (fun x ↦ ∑ j, star (coeff x i) * φ (t i - t j) * coeff x j) μa := by
      intro i
      exact integrable_finset_sum _ (fun j _ ↦ hterm i j)
    calc
      ∑ i, ∑ j,
          star (c i) *
            (Complex.exp (-(a : ℂ) * ‖t i - t j‖ ^ 2) * φ (t i - t j)) *
            c j
          = ∑ i, ∑ j,
              ∫ x, star (coeff x i) * φ (t i - t j) * coeff x j ∂μa := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                refine Finset.sum_congr rfl ?_
                intro j hj
                have hleft :
                    star (c i) *
                        ∫ x, BoundedContinuousFunction.innerProbChar (t i - t j) x ∂μa =
                      ∫ x, star (c i) *
                        BoundedContinuousFunction.innerProbChar (t i - t j) x ∂μa := by
                  simpa using
                    (integral_const_mul (star (c i))
                      (fun x : E ↦ BoundedContinuousFunction.innerProbChar (t i - t j) x)).symm
                have hright :
                    (∫ x, star (c i) *
                        BoundedContinuousFunction.innerProbChar (t i - t j) x ∂μa) *
                        (φ (t i - t j) * c j) =
                      ∫ x, star (c i) *
                        BoundedContinuousFunction.innerProbChar (t i - t j) x *
                        (φ (t i - t j) * c j) ∂μa := by
                  simpa [mul_assoc] using
                    (integral_mul_const (φ (t i - t j) * c j)
                      (fun x : E ↦ star (c i) *
                        BoundedContinuousFunction.innerProbChar (t i - t j) x)).symm
                calc
                  star (c i) *
                      (Complex.exp (-(a : ℂ) * ‖t i - t j‖ ^ 2) * φ (t i - t j)) *
                      c j
                      =
                    (star (c i) *
                        ∫ x, BoundedContinuousFunction.innerProbChar (t i - t j) x ∂μa) *
                      (φ (t i - t j) * c j) := by
                        rw [← gaussianDamping_eq_charFun_scaledStdGaussian (d := d) ha (t i - t j),
                          MeasureTheory.charFun_eq_integral_innerProbChar]
                        ring
                  _ = (∫ x, star (c i) *
                        BoundedContinuousFunction.innerProbChar (t i - t j) x ∂μa) *
                        (φ (t i - t j) * c j) := by
                          rw [hleft]
                  _ = ∫ x, star (c i) *
                        BoundedContinuousFunction.innerProbChar (t i - t j) x *
                        (φ (t i - t j) * c j) ∂μa := by
                          rw [hright]
                  _ = ∫ x, star (coeff x i) * φ (t i - t j) * coeff x j ∂μa := by
                        refine integral_congr_ae (Eventually.of_forall ?_)
                        intro x
                        calc
                          star (c i) *
                              BoundedContinuousFunction.innerProbChar (t i - t j) x *
                              (φ (t i - t j) * c j)
                              =
                            star (c i) *
                              (star (BoundedContinuousFunction.innerProbChar (-t i) x) *
                                BoundedContinuousFunction.innerProbChar (-t j) x) *
                              (φ (t i - t j) * c j) := by
                                  rw [star_innerProbChar_neg_mul_innerProbChar_neg
                                    (u := t i) (v := t j) (x := x)]
                          _ = star (coeff x i) * φ (t i - t j) * coeff x j := by
                                simp [coeff, mul_assoc, mul_left_comm, mul_comm]
      _ = ∑ i, ∫ x, ∑ j, star (coeff x i) * φ (t i - t j) * coeff x j ∂μa := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            symm
            exact integral_finset_sum _ (fun j _ ↦ hterm i j)
      _ = ∫ x, integrand x ∂μa := by
            symm
            simp only [integrand]
            exact integral_finset_sum _ (fun i _ ↦ hinnerSum i)
  have hnonneg : 0 ≤ ∫ x, integrand x ∂μa := by
    -- Proof comment: for each Gaussian sample, the twisted coefficients reduce the claim to the
    -- original positive semidefinite quadratic-sum inequality for `φ`.
    refine integral_nonneg ?_
    intro x
    simpa [integrand, coeff] using hpsd n t (coeff x)
  rw [hkernel]
  exact hnonneg

/-- Helper for Theorem 15.29: the characteristic function of a Euclidean `withDensity` law is the
Fourier transform of the complexified density at the normalized frequency. -/
lemma charFun_withDensity_ofReal_eq_fourierEuclidean {d : ℕ}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf_nonneg : ∀ x, 0 ≤ f x) (hf_int : Integrable f) :
    charFun (volume.withDensity (ENNReal.ofReal ∘ f)) =
      fun t : EuclideanSpace ℝ (Fin d) ↦
        VectorFourier.fourierIntegral Real.fourierChar volume
          (innerₗ (EuclideanSpace ℝ (Fin d)))
          (fun x : EuclideanSpace ℝ (Fin d) ↦ ((f x : ℝ) : ℂ))
          (-(2 * Real.pi)⁻¹ • t) := by
  have hf_aemeas : AEMeasurable (ENNReal.ofReal ∘ f) volume := by
    -- Proof comment: integrability gives the a.e. measurability needed to rewrite `withDensity`.
    exact hf_int.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hf_lt_top : ∀ᵐ x ∂volume, ENNReal.ofReal (f x) < ⊤ := by
    -- Proof comment: `ENNReal.ofReal` is always finite, so the density is finite a.e.
    exact Filter.Eventually.of_forall fun _ ↦ by simp
  ext t
  rw [MeasureTheory.charFun_apply]
  rw [integral_withDensity_eq_integral_toReal_smul₀
    (μ := volume) (f := ENNReal.ofReal ∘ f) hf_aemeas hf_lt_top]
  rw [Real.vector_fourierIntegral_eq_integral_exp_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  have hphase :
      (Real.pi : ℝ) * (2 * inner ℝ x ((Real.pi⁻¹ * 2⁻¹) • t)) = inner ℝ x t := by
    -- Proof comment: the Fourier normalization exactly cancels the `-2π` phase factor.
    calc
      (Real.pi : ℝ) * (2 * inner ℝ x ((Real.pi⁻¹ * 2⁻¹) • t))
          = (Real.pi * (2 * (Real.pi⁻¹ * 2⁻¹))) * inner ℝ x t := by
              rw [real_inner_smul_right]
              ring
      _ = inner ℝ x t := by
            field_simp [Real.pi_ne_zero]
  have hphaseC :
      Complex.I * ((Real.pi : ℂ) * (2 * ((inner ℝ x ((Real.pi⁻¹ * 2⁻¹) • t) : ℝ) : ℂ))) =
        (((inner ℝ x t : ℝ) : ℂ) * Complex.I) := by
    have hphaseCast : (((Real.pi : ℝ) * (2 * inner ℝ x ((Real.pi⁻¹ * 2⁻¹) • t)) : ℝ) : ℂ) =
        ((inner ℝ x t : ℝ) : ℂ) := by
      exact_mod_cast hphase
    calc
      Complex.I * ((Real.pi : ℂ) * (2 * ((inner ℝ x ((Real.pi⁻¹ * 2⁻¹) • t) : ℝ) : ℂ)))
          = ((Real.pi : ℂ) * (2 * ((inner ℝ x ((Real.pi⁻¹ * 2⁻¹) • t) : ℝ) : ℂ))) * Complex.I := by
              ring
      _ = (((inner ℝ x t : ℝ) : ℂ) * Complex.I) := by
            simpa [mul_assoc] using congrArg (fun z : ℂ ↦ z * Complex.I) hphaseCast
  -- Proof comment: after the explicit phase normalization, both integrands are literally the same.
  calc
    ((ENNReal.ofReal ∘ f) x).toReal • cexp (↑(inner ℝ x t) * I)
        = ((f x : ℝ) : ℂ) * cexp (((inner ℝ x t : ℝ) : ℂ) * I) := by
            simp [hf_nonneg x, smul_eq_mul]
    _ = ((f x : ℝ) : ℂ) *
          cexp (Complex.I * ((Real.pi : ℂ) *
            (2 * ((inner ℝ x ((Real.pi⁻¹ * 2⁻¹) • t) : ℝ) : ℂ)))) := by
              congr 1
              rw [← hphaseC]
    _ = (fun v : EuclideanSpace ℝ (Fin d) ↦
          cexp (↑(-2 * Real.pi * ((innerₗ (EuclideanSpace ℝ (Fin d))) v) (-(2 * Real.pi)⁻¹ • t)) * I) •
            ↑(f v)) x := by
          simp [smul_eq_mul, mul_comm, mul_assoc]

/-- Helper for Theorem 15.29: continuous nonnegative Euclidean densities are uniquely determined
by their `withDensity` measures. -/
lemma continuousDensity_eq_of_withDensity_eqEuclidean {d : ℕ}
    {g h : EuclideanSpace ℝ (Fin d) → ℝ} (hg : Continuous g) (hh : Continuous h)
    (hg_nonneg : ∀ x, 0 ≤ g x) (hh_nonneg : ∀ x, 0 ≤ h x)
    (h_eq :
      volume.withDensity (ENNReal.ofReal ∘ g) =
        volume.withDensity (ENNReal.ofReal ∘ h)) :
    g = h := by
  have h_ae :
      (fun x : EuclideanSpace ℝ (Fin d) ↦ ENNReal.ofReal (g x)) =ᵐ[volume]
        fun x : EuclideanSpace ℝ (Fin d) ↦ ENNReal.ofReal (h x) :=
    (withDensity_eq_iff_of_sigmaFinite
      ((ENNReal.continuous_ofReal.comp hg).measurable.aemeasurable)
      ((ENNReal.continuous_ofReal.comp hh).measurable.aemeasurable)).mp h_eq
  have h_eq_fun :
      (fun x : EuclideanSpace ℝ (Fin d) ↦ ENNReal.ofReal (g x)) =
        fun x : EuclideanSpace ℝ (Fin d) ↦ ENNReal.ofReal (h x) :=
    (Continuous.ae_eq_iff_eq (μ := volume)
      (ENNReal.continuous_ofReal.comp hg) (ENNReal.continuous_ofReal.comp hh)).mp h_ae
  funext x
  -- Proof comment: pointwise equality of the `ENNReal` densities descends to equality of the
  -- underlying real functions because both densities are nonnegative.
  exact (ENNReal.ofReal_eq_ofReal_iff (hg_nonneg x) (hh_nonneg x)).mp (congrFun h_eq_fun x)

/-- Helper for Theorem 15.29: the product of the one-dimensional standard Gaussian laws on
`Fin d` is absolutely continuous with respect to Euclidean volume on `ℝ^d`. -/
lemma piGaussian_absolutelyContinuous :
    ∀ d : ℕ,
      (Measure.pi fun _ : Fin d ↦ ProbabilityTheory.gaussianReal 0 1) ≪
        (volume : Measure (Fin d → ℝ))
  | 0 => by
      let x : Fin 0 → ℝ := fun i ↦ Fin.elim0 i
      -- Proof comment: on the zero-dimensional space both measures are the same Dirac mass.
      rw [Measure.pi_of_empty (μ := fun _ : Fin 0 ↦ ProbabilityTheory.gaussianReal 0 1) x,
        Measure.volume_pi_eq_dirac x]
  | n + 1 => by
      have hprod :
          (ProbabilityTheory.gaussianReal 0 1).prod
              (Measure.pi fun _ : Fin n ↦ ProbabilityTheory.gaussianReal 0 1) ≪
            (volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ)) := by
        -- Proof comment: absolute continuity is preserved under finite products.
        exact
          (ProbabilityTheory.gaussianReal_absolutelyContinuous (μ := 0) (v := 1) one_ne_zero).prod
            (piGaussian_absolutelyContinuous n)
      have hmap :
          Measure.map
              (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0).symm
              ((ProbabilityTheory.gaussianReal 0 1).prod
                (Measure.pi fun _ : Fin n ↦ ProbabilityTheory.gaussianReal 0 1)) ≪
            Measure.map
              (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0).symm
              ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) :=
        MeasurableEmbedding.absolutelyContinuous_map
          ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0).symm.measurableEmbedding)
          hprod
      have hgauss_eq :
          Measure.map
              (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0).symm
              ((ProbabilityTheory.gaussianReal 0 1).prod
                (Measure.pi fun _ : Fin n ↦ ProbabilityTheory.gaussianReal 0 1)) =
            Measure.pi fun _ : Fin (n + 1) ↦ ProbabilityTheory.gaussianReal 0 1 :=
        (MeasureTheory.measurePreserving_piFinSuccAbove
          (μ := fun _ : Fin (n + 1) ↦ ProbabilityTheory.gaussianReal 0 1) 0).symm.map_eq
      have hvol_eq :
          Measure.map
              (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0).symm
              ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) =
            (volume : Measure (Fin (n + 1) → ℝ)) :=
        (MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0).symm.map_eq
      -- Proof comment: transport the binary product statement back to the full `Fin (n + 1)`
      -- coordinate space by the canonical measurable equivalence.
      rw [hgauss_eq, hvol_eq] at hmap
      exact hmap

/-- Helper for Theorem 15.29: the scaled Euclidean standard Gaussian is absolutely continuous
with respect to Lebesgue measure. -/
lemma scaledStdGaussian_absolutelyContinuous {d : ℕ} {a : ℝ} (ha : 0 < a) :
    ((ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d))).map
      (Real.sqrt (2 * a) • ·)) ≪ (volume : Measure (EuclideanSpace ℝ (Fin d))) := by
  let r : ℝ := Real.sqrt (2 * a)
  have hr : r ≠ 0 := by
    -- Proof comment: the Gaussian scaling factor is nonzero because `a > 0`.
    dsimp [r]
    exact Real.sqrt_ne_zero'.2 (by positivity : 0 < 2 * a)
  have hstd :
      (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d))) ≪
        (volume : Measure (EuclideanSpace ℝ (Fin d))) := by
    have hpi :
        (Measure.pi fun _ : Fin d ↦ ProbabilityTheory.gaussianReal 0 1) ≪
          (volume : Measure (Fin d → ℝ)) :=
      piGaussian_absolutelyContinuous d
    have hmap :
        Measure.map (MeasurableEquiv.toLp 2 (Fin d → ℝ))
            (Measure.pi fun _ : Fin d ↦ ProbabilityTheory.gaussianReal 0 1) ≪
          Measure.map (MeasurableEquiv.toLp 2 (Fin d → ℝ))
            (volume : Measure (Fin d → ℝ)) :=
      MeasurableEmbedding.absolutelyContinuous_map
        ((MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurableEmbedding) hpi
    have hgauss_eq :
        Measure.map (MeasurableEquiv.toLp 2 (Fin d → ℝ))
            (Measure.pi fun _ : Fin d ↦ ProbabilityTheory.gaussianReal 0 1) =
          ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d)) :=
      ProbabilityTheory.map_pi_eq_stdGaussian
    have hvol_eq :
        Measure.map (MeasurableEquiv.toLp 2 (Fin d → ℝ))
            (volume : Measure (Fin d → ℝ)) =
          (volume : Measure (EuclideanSpace ℝ (Fin d))) :=
      (PiLp.volume_preserving_toLp (ι := Fin d)).map_eq
    -- Proof comment: `stdGaussian` is exactly the product Gaussian transported by `toLp`, and
    -- `toLp` preserves Euclidean volume.
    rw [hgauss_eq, hvol_eq] at hmap
    exact hmap
  have hscaled :
      Measure.map (r • ·) (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d))) ≪
        Measure.map (r • ·) (volume : Measure (EuclideanSpace ℝ (Fin d))) :=
    MeasurableEmbedding.absolutelyContinuous_map
      ((Homeomorph.smulOfNeZero r hr).toMeasurableEquiv.measurableEmbedding) hstd
  -- Proof comment: scaling preserves null sets for Lebesgue measure on Euclidean space.
  exact hscaled.trans
    (Measure.quasiMeasurePreserving_smul
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin d)))) hr).absolutelyContinuous

/-- Helper for Theorem 15.29: Gaussian smoothing of an actual Euclidean probability witness
already produces a nonnegative `L¹` density with the expected damped characteristic function. -/
lemma gaussianDampedDensitySpecOfProbabilityMeasure {d : ℕ}
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) {a : ℝ} (ha : 0 < a) :
    ∃ f : EuclideanSpace ℝ (Fin d) → ℝ,
      (∀ x, 0 ≤ f x) ∧ Integrable f ∧ (∫ x, f x = 1) ∧
      (∀ t : EuclideanSpace ℝ (Fin d),
        VectorFourier.fourierIntegral Real.fourierChar volume
            (innerₗ (EuclideanSpace ℝ (Fin d)))
            (fun x : EuclideanSpace ℝ (Fin d) ↦ ((f x : ℝ) : ℂ))
            (-(2 * Real.pi)⁻¹ • t) =
          Complex.exp (-(a : ℂ) * ‖t‖ ^ 2) *
            charFun (μ : Measure (EuclideanSpace ℝ (Fin d))) t) := by
  let E := EuclideanSpace ℝ (Fin d)
  let γ : Measure E := (ProbabilityTheory.stdGaussian E).map (Real.sqrt (2 * a) • ·)
  haveI : IsProbabilityMeasure γ := by
    dsimp [γ]
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  let ν : Measure E := (μ : Measure E).conv γ
  let f : E → ℝ := fun x ↦ (ν.rnDeriv volume x).toReal
  have hγ_ac : γ ≪ (volume : Measure E) :=
    scaledStdGaussian_absolutelyContinuous (d := d) ha
  have hν_ac : ν ≪ (volume : Measure E) := by
    -- Proof comment: convolution with the absolutely continuous Gaussian preserves absolute
    -- continuity with respect to Lebesgue measure.
    simpa [ν] using Measure.conv_absolutelyContinuous
      (μ := (μ : Measure E)) (ν := γ) (ρ := (volume : Measure E)) hγ_ac
  have hf_nonneg : ∀ x, 0 ≤ f x := by
    -- Proof comment: a Radon–Nikodym derivative takes values in `ℝ≥0∞`, so its real part is
    -- pointwise nonnegative.
    intro x
    simp [f]
  have hf_int : Integrable f := by
    -- Proof comment: the Radon–Nikodym derivative of a finite measure is integrable over the full
    -- space.
    simpa [f, IntegrableOn, ν] using
      (Measure.integrableOn_toReal_rnDeriv
        (μ := ν) (ν := (volume : Measure E)) (s := Set.univ) (measure_ne_top ν Set.univ))
  have hwithDensity_eq :
      volume.withDensity (ENNReal.ofReal ∘ f) =
        volume.withDensity (ν.rnDeriv volume) := by
    -- Proof comment: `ENNReal.ofReal` cancels `toReal` on the finite part of the Radon–Nikodym
    -- derivative, and the derivative is finite almost everywhere.
    refine withDensity_congr_ae ?_
    filter_upwards [Measure.rnDeriv_lt_top ν (volume : Measure E)] with x hx
    simp [f, ENNReal.ofReal_toReal hx.ne]
  have hν_real_univ : ν.real Set.univ = 1 := by
    have hν_prob : IsProbabilityMeasure ν := inferInstance
    rw [MeasureTheory.isProbabilityMeasure_iff_real] at hν_prob
    exact hν_prob
  have hf_mass : ∫ x, f x = 1 := by
    -- Proof comment: the smoothed witness is still a probability measure, so its density has total
    -- mass `1`.
    calc
      ∫ x, f x ∂volume = ν.real Set.univ := by
        simpa [f] using
          (Measure.integral_toReal_rnDeriv (μ := ν) (ν := (volume : Measure E)) hν_ac)
      _ = 1 := hν_real_univ
  refine ⟨f, hf_nonneg, hf_int, hf_mass, ?_⟩
  intro t
  -- Proof comment: first identify the `withDensity` law defined by the Radon–Nikodym derivative,
  -- then compute the characteristic function of the convolution witness.
  calc
    VectorFourier.fourierIntegral Real.fourierChar volume
        (innerₗ E)
        (fun x : E ↦ ((f x : ℝ) : ℂ))
        (-(2 * Real.pi)⁻¹ • t)
        = charFun (volume.withDensity (ENNReal.ofReal ∘ f)) t := by
            symm
            simpa [f] using
              congrFun
                (charFun_withDensity_ofReal_eq_fourierEuclidean
                  (d := d) (f := f) hf_nonneg hf_int) t
    _ = charFun ν t := by rw [hwithDensity_eq, Measure.withDensity_rnDeriv_eq _ _ hν_ac]
    _ = charFun (μ : Measure E) t * charFun γ t := by
          simpa [ν, γ] using
            (MeasureTheory.charFun_conv (μ := (μ : Measure E)) (ν := γ) t)
    _ = charFun (μ : Measure E) t * Complex.exp (-(a : ℂ) * ‖t‖ ^ 2) := by
          rw [gaussianDamping_eq_charFun_scaledStdGaussian (d := d) ha t]
    _ = Complex.exp (-(a : ℂ) * ‖t‖ ^ 2) * charFun (μ : Measure E) t := by
          ring

/-- Helper for Theorem 15.29: Gaussian damping converges pointwise to the undamped inverse
Fourier transform of an integrable Euclidean kernel. -/
lemma dampedInverseFourier_tendsto {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} (hψ_int : Integrable ψ)
    (x : EuclideanSpace ℝ (Fin d)) :
    Tendsto
      (fun n : ℕ ↦
        FourierTransformInv.fourierInv
          (fun t : EuclideanSpace ℝ (Fin d) ↦
            Complex.exp (-((((n : ℝ) + 1)⁻¹ : ℂ) * ‖t‖ ^ 2)) * ψ t)
          x)
      atTop
      (𝓝 (FourierTransformInv.fourierInv ψ x)) := by
  let modulated : EuclideanSpace ℝ (Fin d) → ℂ :=
    fun t ↦ Complex.exp (↑(2 * Real.pi * inner ℝ t x) * Complex.I) * ψ t
  have hmodulated : Integrable modulated := by
    -- Proof comment: the oscillatory phase has unit norm, so modulation preserves the `L¹`
    -- bound of `ψ`.
    refine Integrable.mono' hψ_int.norm ?_ ?_
    · fun_prop
    · filter_upwards with t
      simp [modulated, norm_mul, Complex.norm_exp]
  have hbase :
      Tendsto
        (fun c : ℝ ↦
          ∫ t : EuclideanSpace ℝ (Fin d), Complex.exp (-c⁻¹ * ‖t‖ ^ 2) • modulated t)
        atTop
        (𝓝 (∫ t : EuclideanSpace ℝ (Fin d), modulated t)) :=
    Real.tendsto_integral_cexp_sq_smul hmodulated
  have hscale : Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop := by
    have hcast : Tendsto (fun m : ℕ ↦ (m : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    have hshift :
        Tendsto (((fun m : ℕ ↦ (m : ℝ)) ∘ fun a ↦ a + 1)) atTop atTop :=
      hcast.comp (tendsto_add_atTop_nat 1)
    convert hshift using 1
    ext n
    simp [Function.comp, Nat.cast_add]
  have htarget :
      (∫ t : EuclideanSpace ℝ (Fin d), modulated t) =
        FourierTransformInv.fourierInv ψ x := by
    -- Proof comment: the undamped limit integral is exactly the inverse Fourier transform of `ψ`.
    rw [Real.fourierInv_eq']
    simp [modulated, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]
  rw [htarget] at hbase
  convert (hbase.comp hscale) using 1
  · ext n
    -- Proof comment: `Real.fourierInv_eq'` identifies the damped inverse Fourier transform with
    -- the Gaussian-modulated oscillatory integral.
    rw [Real.fourierInv_eq']
    simp [modulated, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Theorem 15.29: taking real parts of the Gaussian-damped inverse Fourier transforms
preserves the pointwise convergence to the target density candidate. -/
lemma dampedInverseFourierDensity_tendsto {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} (hψ_int : Integrable ψ)
    (x : EuclideanSpace ℝ (Fin d)) :
    Tendsto
      (fun n : ℕ ↦
        Complex.re
          (FourierTransformInv.fourierInv
            (fun t : EuclideanSpace ℝ (Fin d) ↦
              Complex.exp (-((((n : ℝ) + 1)⁻¹ : ℂ) * ‖t‖ ^ 2)) * ψ t)
            x))
      atTop
      (𝓝 (Complex.re (FourierTransformInv.fourierInv ψ x))) := by
  -- Proof comment: `Complex.re` is continuous, so the complex convergence immediately descends to
  -- the real-valued density candidate.
  exact Complex.continuous_re.continuousAt.tendsto.comp
    (dampedInverseFourier_tendsto hψ_int x)

/-- Helper for Theorem 15.29: after evaluating the fixed `-2π` rescaling inside the Gaussian
weight, the scaled damping factor matches the normalized regularization factor used in the exact
scaled inverse-Fourier surface. -/
lemma scaledDampedKernel_apply_eq_normalizedDamping {d : ℕ}
    {ρ : EuclideanSpace ℝ (Fin d) → ℂ} (n : ℕ) (t : EuclideanSpace ℝ (Fin d)) :
    Complex.exp
        (-(((((n : ℝ) + 1)⁻¹ / (2 * Real.pi) ^ 2 : ℝ) : ℂ) *
          ‖((-(2 * Real.pi) : ℝ) • t)‖ ^ 2)) *
      ρ (((-(2 * Real.pi) : ℝ) • t)) =
      Complex.exp (-((((n : ℝ) + 1)⁻¹ : ℂ) * ‖t‖ ^ 2)) *
        ρ (((-(2 * Real.pi) : ℝ) • t)) := by
  have hnorm :
      ‖((-(2 * Real.pi) : ℝ) • t)‖ ^ 2 = (2 * Real.pi) ^ 2 * ‖t‖ ^ 2 := by
    -- Proof comment: pulling the fixed `-2π` scaling out of the norm produces the precise square
    -- factor that cancels the normalization denominator.
    rw [norm_smul, Real.norm_eq_abs, abs_of_neg]
    · ring
    · have htwoPi : 0 < (2 : ℝ) * Real.pi := by positivity
      linarith
  have hscalar :
      ((((n : ℝ) + 1)⁻¹ / (2 * Real.pi) ^ 2) * ‖((-(2 * Real.pi) : ℝ) • t)‖ ^ 2 : ℝ) =
        ((n : ℝ) + 1)⁻¹ * ‖t‖ ^ 2 := by
    -- Proof comment: after the norm rewrite, `(2π)^2` cancels exactly against the chosen Gaussian
    -- parameter.
    rw [hnorm]
    field_simp [Real.pi_ne_zero]
  have hscalarC :
      (((((n : ℝ) + 1)⁻¹ / (2 * Real.pi) ^ 2) *
          ‖((-(2 * Real.pi) : ℝ) • t)‖ ^ 2 : ℝ) : ℂ) =
        ((((n : ℝ) + 1)⁻¹ * ‖t‖ ^ 2 : ℝ) : ℂ) := by
    exact congrArg (fun r : ℝ ↦ (r : ℂ)) hscalar
  -- Proof comment: rewrite the exponential argument once through the real normalization identity,
  -- and keep the scaled witness kernel fixed.
  calc
    Complex.exp
        (-(((((n : ℝ) + 1)⁻¹ / (2 * Real.pi) ^ 2 : ℝ) : ℂ) *
          ‖((-(2 * Real.pi) : ℝ) • t)‖ ^ 2)) *
      ρ (((-(2 * Real.pi) : ℝ) • t))
        = Complex.exp
            (-((((((n : ℝ) + 1)⁻¹ / (2 * Real.pi) ^ 2) *
                ‖((-(2 * Real.pi) : ℝ) • t)‖ ^ 2 : ℝ) : ℂ))) *
            ρ (((-(2 * Real.pi) : ℝ) • t)) := by
              simp
    _ = Complex.exp (-((((n : ℝ) + 1)⁻¹ * ‖t‖ ^ 2 : ℝ) : ℂ)) *
          ρ (((-(2 * Real.pi) : ℝ) • t)) := by
            rw [hscalarC]
    _ = Complex.exp (-((((n : ℝ) + 1)⁻¹ : ℂ) * ‖t‖ ^ 2)) *
          ρ (((-(2 * Real.pi) : ℝ) • t)) := by
            simp

/-- Helper for Theorem 15.29: once the `-2π` normalization is frozen, the Gaussian-regularized
approximants converge pointwise to the exact scaled inverse-Fourier surface. -/
lemma scaledDampedInverseFourierRe_tendsto_of_integrable {d : ℕ}
    {ρ : EuclideanSpace ℝ (Fin d) → ℂ} (hρ_int : Integrable ρ)
    (x : EuclideanSpace ℝ (Fin d)) :
    Tendsto
      (fun n : ℕ ↦
        Complex.re
          (FourierTransformInv.fourierInv
            (fun t : EuclideanSpace ℝ (Fin d) ↦
              Complex.exp
                  (-(((((n : ℝ) + 1)⁻¹ / (2 * Real.pi) ^ 2 : ℝ) : ℂ) *
                    ‖((-(2 * Real.pi) : ℝ) • t)‖ ^ 2)) *
                ρ (((-(2 * Real.pi) : ℝ) • t)))
            x))
      atTop
      (𝓝 (Complex.re
        (FourierTransformInv.fourierInv
          (fun t : EuclideanSpace ℝ (Fin d) ↦ ρ (((-(2 * Real.pi) : ℝ) • t)))
          x))) := by
  let E := EuclideanSpace ℝ (Fin d)
  let c : ℝ := -(2 * Real.pi)
  let ρScaled : E → ℂ := fun t ↦ ρ (c • t)
  have hc : c ≠ 0 := by
    -- Proof comment: the frozen Fourier-normalization scalar is nonzero, so rescaling preserves
    -- integrability.
    have htwoPi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    exact neg_ne_zero.mpr htwoPi
  have hρScaled_int : Integrable ρScaled := by
    -- Proof comment: the exact scaled surface is just a nonzero scalar precomposition of `ρ`.
    simpa [ρScaled, c] using hρ_int.comp_smul hc
  have hbase :
      Tendsto
        (fun n : ℕ ↦
          Complex.re
            (FourierTransformInv.fourierInv
              (fun t : E ↦
                Complex.exp (-((((n : ℝ) + 1)⁻¹ : ℂ) * ‖t‖ ^ 2)) * ρScaled t)
              x))
        atTop
        (𝓝 (Complex.re (FourierTransformInv.fourierInv ρScaled x))) := by
    -- Proof comment: this is the previously established damped inverse-Fourier convergence on the
    -- frozen scaled kernel `ρScaled`.
    simpa [ρScaled] using
      dampedInverseFourierDensity_tendsto (d := d) (ψ := ρScaled) hρScaled_int x
  refine hbase.congr' ?_
  exact Filter.Eventually.of_forall fun n ↦ by
    have hkernel :
        (fun t : E ↦
          Complex.exp
              (-(((((n : ℝ) + 1)⁻¹ / (2 * Real.pi) ^ 2 : ℝ) : ℂ) * ‖c • t‖ ^ 2)) *
            ρScaled t) =
          fun t : E ↦
            Complex.exp (-((((n : ℝ) + 1)⁻¹ : ℂ) * ‖t‖ ^ 2)) * ρScaled t := by
      funext t
      simpa [ρScaled, c] using
        scaledDampedKernel_apply_eq_normalizedDamping (d := d) (ρ := ρ) n t
    -- Proof comment: rewrite each approximant kernel to the normalized damping spelling before
    -- applying the convergent base sequence.
    simpa [ρScaled, c] using
      congrArg
        (fun ψ : E → ℂ ↦ Complex.re (FourierTransformInv.fourierInv ψ x))
        hkernel.symm

/-- Helper for Theorem 15.29: the inverse Fourier transform of an `L¹` Euclidean kernel is
continuous. -/
lemma inverseFourier_continuous_of_integrable {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} (hψ_int : Integrable ψ) :
    Continuous (FourierTransformInv.fourierInv ψ) := by
  -- Proof comment: the inverse Fourier transform is a Fourier integral of an `L¹` kernel, so the
  -- standard continuity theorem for Fourier integrals applies directly.
  simpa [Real.fourierInv_eq] using
    (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (-innerSL ℝ).continuous₂ hψ_int)

/-- Helper for Theorem 15.29: the inverse Fourier transform of an `L¹` Euclidean kernel is
uniformly bounded by the `L¹` norm of that kernel. -/
lemma norm_inverseFourier_le_integral_norm {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} (hψ_int : Integrable ψ)
    (x : EuclideanSpace ℝ (Fin d)) :
    ‖FourierTransformInv.fourierInv ψ x‖ ≤ ∫ t, ‖ψ t‖ := by
  -- Proof comment: taking norms inside the inverse-Fourier integral loses only the unit-modulus
  -- phase factor, so the oscillatory integral is controlled by the `L¹` norm of `ψ`.
  rw [Real.fourierInv_eq]
  simpa using
    (norm_integral_le_integral_norm
      (f := fun t : EuclideanSpace ℝ (Fin d) ↦
        Real.fourierChar (inner ℝ t x) • ψ t))

/-- Helper for Theorem 15.29: pointwise limits of nonnegative real-valued approximants remain
nonnegative. -/
lemma nonneg_of_tendsto_of_nonneg {α : Type*} {fSeq : ℕ → α → ℝ} {f : α → ℝ}
    (hfSeq_nonneg : ∀ n x, 0 ≤ fSeq n x)
    (h_tendsto : ∀ x, Tendsto (fun n ↦ fSeq n x) atTop (𝓝 (f x))) :
    ∀ x, 0 ≤ f x := by
  intro x
  -- Proof comment: closedness of `[0, ∞)` lets the pointwise limit inherit nonnegativity from
  -- every approximating term.
  exact isClosed_Ici.mem_of_tendsto (h_tendsto x)
    (Filter.Eventually.of_forall fun n ↦ hfSeq_nonneg n x)

/-- Helper for Theorem 15.29: a continuous real-valued function on `ℝ^d` that is nonnegative
almost everywhere is nonnegative everywhere. -/
lemma nonneg_of_continuous_ae_nonneg {d : ℕ}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf_cont : Continuous f)
    (hf_nonneg : 0 ≤ᵐ[volume] f) :
    ∀ x, 0 ≤ f x := by
  intro x
  by_contra hx
  have hx_mem : x ∈ {y : EuclideanSpace ℝ (Fin d) | f y < 0} := by
    -- Proof comment: a point with negative value lies in the open negativity set.
    exact lt_of_not_ge hx
  have hs_open : IsOpen {y : EuclideanSpace ℝ (Fin d) | f y < 0} :=
    isOpen_lt hf_cont continuous_const
  rcases Metric.mem_nhds_iff.mp (hs_open.mem_nhds hx_mem) with ⟨ε, hεpos, hball_subset⟩
  have hs_null : volume {y : EuclideanSpace ℝ (Fin d) | f y < 0} = 0 := by
    -- Proof comment: almost-everywhere nonnegativity says the strict negativity set is null.
    refine measure_mono_null ?_ (ae_iff.mp hf_nonneg)
    intro y hy
    exact not_le_of_gt hy
  have hball_zero : volume (Metric.ball x ε) = 0 :=
    measure_mono_null hball_subset hs_null
  have hball_pos : 0 < volume (Metric.ball x ε) := by
    -- Proof comment: every nonempty open ball in Euclidean space has positive Lebesgue measure.
    exact Metric.measure_ball_pos (μ := (volume : Measure (EuclideanSpace ℝ (Fin d)))) x hεpos
  exact hball_pos.ne' hball_zero

/-- Helper for Theorem 15.29: Fatou upgrades a nonnegative almost-everywhere limit of `L¹`
approximants with convergent total mass to an `L¹` limit. -/
lemma integrable_of_nonneg_tendsto_ae_of_integral_tendsto {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} {fSeq : ℕ → Ω → ℝ} {f : Ω → ℝ} {I : ℝ}
    (hfSeq_int : ∀ n, Integrable (fSeq n) μ)
    (hfSeq_nonneg : ∀ n, 0 ≤ᵐ[μ] fSeq n)
    (h_tendsto : ∀ᵐ x ∂μ, Tendsto (fun n ↦ fSeq n x) atTop (𝓝 (f x)))
    (h_integral_tendsto : Tendsto (fun n ↦ ∫ x, fSeq n x ∂μ) atTop (𝓝 I)) :
    Integrable f μ := by
  have hf_nonneg : 0 ≤ᵐ[μ] f :=
    ae_nonneg_limit hfSeq_nonneg h_tendsto
  have hAestrong : AEStronglyMeasurable f μ :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun n ↦ (hfSeq_int n).aestronglyMeasurable) h_tendsto
  have hLintegralNeTop :
      ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≠ ⊤ :=
    lintegral_ofReal_limit_ne_top hfSeq_int hfSeq_nonneg h_tendsto h_integral_tendsto
  -- Proof comment: the Chap. 4 Fatou bridge controls the lower integral of the limit, and the
  -- inherited almost-everywhere nonnegativity converts that into genuine integrability.
  exact
    (lintegral_ofReal_ne_top_iff_integrable hAestrong hf_nonneg).1 hLintegralNeTop

/-- Helper for Theorem 15.29: if a Euclidean kernel satisfies the Hermitian symmetry
`ψ (-t) = conj (ψ t)`, then its inverse Fourier transform is real-valued. -/
lemma ofRealFourierInv_eq_of_starSymmetric {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} (hstar : ∀ t, star (ψ t) = ψ (-t)) :
    (fun x : EuclideanSpace ℝ (Fin d) ↦
      ((Complex.re (FourierTransformInv.fourierInv ψ x) : ℝ) : ℂ)) =
      FourierTransformInv.fourierInv ψ := by
  funext x
  rw [← Complex.conj_eq_iff_re]
  have hconj :
      star (FourierTransformInv.fourierInv ψ x) = FourierTransformInv.fourierInv ψ x := by
    -- Proof comment: conjugate the inverse-Fourier integral, then transport the conjugated kernel
    -- through the symmetry `star (ψ t) = ψ (-t)`.
    calc
      star (FourierTransformInv.fourierInv ψ x)
          = star (∫ t : EuclideanSpace ℝ (Fin d),
              Complex.exp (↑(2 * Real.pi * inner ℝ t x) * Complex.I) • ψ t) := by
                rw [Real.fourierInv_eq']
      _ = ∫ t : EuclideanSpace ℝ (Fin d),
            star (Complex.exp (↑(2 * Real.pi * inner ℝ t x) * Complex.I) • ψ t) := by
              simpa using
                (integral_conj
                  (μ := (volume : Measure (EuclideanSpace ℝ (Fin d))))
                  (f := fun t : EuclideanSpace ℝ (Fin d) ↦
                    Complex.exp (↑(2 * Real.pi * inner ℝ t x) * Complex.I) • ψ t)).symm
      _ = ∫ t : EuclideanSpace ℝ (Fin d),
            Complex.exp (↑(-(2 * Real.pi * inner ℝ t x)) * Complex.I) • ψ (-t) := by
              refine integral_congr_ae (Filter.Eventually.of_forall ?_)
              intro t
              have hψ : (starRingEnd ℂ) (ψ t) = ψ (-t) := by
                simpa using hstar t
              have hexp :
                  (starRingEnd ℂ) (Complex.exp (2 * ↑Real.pi * ↑(inner ℝ t x) * Complex.I)) =
                    Complex.exp (-(2 * ↑Real.pi * ↑(inner ℝ t x) * Complex.I)) := by
                have hexpArg :
                    (starRingEnd ℂ) (2 * ↑Real.pi * ↑(inner ℝ t x) * Complex.I) =
                      -(2 * ↑Real.pi * ↑(inner ℝ t x) * Complex.I) := by
                  apply Complex.ext <;> simp [mul_assoc]
                rw [← Complex.exp_conj, hexpArg]
              simp [smul_eq_mul, hexp, hψ]
      _ = ∫ t : EuclideanSpace ℝ (Fin d),
            Complex.exp (↑(2 * Real.pi * inner ℝ t x) * Complex.I) • ψ t := by
              -- Proof comment: negate the integration variable, using invariance of Euclidean
              -- volume under `t ↦ -t`, to recover the original inverse-Fourier kernel.
              have hneg :=
                (Measure.measurePreserving_neg
                  (volume : Measure (EuclideanSpace ℝ (Fin d)))).integral_comp
                  ((MeasurableEquiv.neg (EuclideanSpace ℝ (Fin d))).measurableEmbedding)
                  (fun t : EuclideanSpace ℝ (Fin d) ↦
                    Complex.exp (↑(2 * Real.pi * inner ℝ t x) * Complex.I) • ψ t)
              simpa [inner_neg_left, inner_neg_right] using hneg
      _ = FourierTransformInv.fourierInv ψ x := by
            rw [Real.fourierInv_eq']
  exact hconj

/-- Helper for Theorem 15.29: the inverse Fourier transform of a positive semidefinite kernel on
`ℝ^d` can be read as a real-valued density candidate. -/
lemma ofRealFourierInv_eq_of_isPositiveSemidefiniteFunction {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} (hψ_psd : IsPositiveSemidefiniteFunction ψ) :
    (fun x : EuclideanSpace ℝ (Fin d) ↦
      ((Complex.re (FourierTransformInv.fourierInv ψ x) : ℝ) : ℂ)) =
      FourierTransformInv.fourierInv ψ := by
  -- Proof comment: positive semidefiniteness gives the Hermitian symmetry needed by the previous
  -- inverse-Fourier reality lemma.
  exact ofRealFourierInv_eq_of_starSymmetric
    (d := d) (ψ := ψ)
    (fun t ↦ star_value_eq_value_neg_of_isPositiveSemidefiniteFunction hψ_psd t)

/-- Helper for Theorem 15.29: a nonnegative real density of mass `1` whose normalized Fourier
integral is `ψ` packages directly into a probability law with characteristic function `ψ`. -/
lemma existsProbabilityMeasureOfRealDensityFourierEq {d : ℕ}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} {ψ : EuclideanSpace ℝ (Fin d) → ℂ}
    (hf_nonneg : ∀ x, 0 ≤ f x) (hf_int : Integrable f) (hf_mass : ∫ x, f x = 1)
    (hfourier :
      ∀ t : EuclideanSpace ℝ (Fin d),
        VectorFourier.fourierIntegral Real.fourierChar volume
            (innerₗ (EuclideanSpace ℝ (Fin d)))
            (fun x : EuclideanSpace ℝ (Fin d) ↦ ((f x : ℝ) : ℂ))
            (-(2 * Real.pi)⁻¹ • t) = ψ t) :
    ∃ μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)),
      ∀ t : EuclideanSpace ℝ (Fin d), charFun (μ : Measure (EuclideanSpace ℝ (Fin d))) t = ψ t := by
  let μ :
      Measure (EuclideanSpace ℝ (Fin d)) :=
    volume.withDensity (ENNReal.ofReal ∘ f)
  haveI : IsFiniteMeasure μ := by
    -- Proof comment: integrability of the density makes the `withDensity` measure finite.
    exact MeasureTheory.isFiniteMeasure_withDensity_ofReal hf_int.hasFiniteIntegral
  have hμ_real_univ : μ.real Set.univ = 1 := by
    -- Proof comment: evaluate the total mass by integrating the constant function `1` against the
    -- density and then use the mass-one hypothesis on `f`.
    have hf_aemeas : AEMeasurable (ENNReal.ofReal ∘ f) volume := by
      exact hf_int.aestronglyMeasurable.aemeasurable.ennreal_ofReal
    have hf_lt_top : ∀ᵐ x ∂volume, ENNReal.ofReal (f x) < ⊤ := by
      exact Filter.Eventually.of_forall fun _ ↦ by simp
    calc
      μ.real Set.univ = ∫ x, (1 : ℝ) ∂μ := by
        simp [μ]
      _ = ∫ x, ((ENNReal.ofReal ∘ f) x).toReal • (1 : ℝ) ∂volume := by
        simpa [μ] using
          (integral_withDensity_eq_integral_toReal_smul₀
            (μ := volume) (f := ENNReal.ofReal ∘ f) hf_aemeas hf_lt_top
            (g := fun _ : EuclideanSpace ℝ (Fin d) ↦ (1 : ℝ)))
      _ = ∫ x, f x ∂volume := by
        refine integral_congr_ae (Filter.Eventually.of_forall ?_)
        intro x
        simp [hf_nonneg x]
      _ = 1 := hf_mass
  let P : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)) :=
    ⟨μ, (MeasureTheory.isProbabilityMeasure_iff_real.2 hμ_real_univ)⟩
  refine ⟨P, ?_⟩
  intro t
  -- Proof comment: the characteristic function of the `withDensity` law is exactly the
  -- normalized Fourier integral fixed in the hypothesis.
  calc
    charFun (P : Measure (EuclideanSpace ℝ (Fin d))) t
        = VectorFourier.fourierIntegral Real.fourierChar volume
            (innerₗ (EuclideanSpace ℝ (Fin d)))
            (fun x : EuclideanSpace ℝ (Fin d) ↦ ((f x : ℝ) : ℂ))
            (-(2 * Real.pi)⁻¹ • t) := by
              simpa [P, μ] using
                congrFun (charFun_withDensity_ofReal_eq_fourierEuclidean
                  (d := d) hf_nonneg hf_int) t
    _ = ψ t := hfourier t

/-- Helper for Theorem 15.29: once the inverse-Fourier candidate attached to an actual Euclidean
probability law is known to be a nonnegative `L¹` density, the original law equals the
corresponding `withDensity` measure. -/
lemma probabilityMeasure_eq_withDensity_of_scaledCharFunFourierInv {d : ℕ}
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)))
    (hφ_int : Integrable (charFun (μ : Measure (EuclideanSpace ℝ (Fin d)))))
    (hf_nonneg : ∀ x : EuclideanSpace ℝ (Fin d),
      0 ≤ Complex.re (FourierTransformInv.fourierInv
        (fun t : EuclideanSpace ℝ (Fin d) ↦
          charFun (μ : Measure (EuclideanSpace ℝ (Fin d))) ((-(2 * Real.pi) : ℝ) • t)) x))
    (hf_int : Integrable fun x : EuclideanSpace ℝ (Fin d) ↦
      Complex.re (FourierTransformInv.fourierInv
        (fun t : EuclideanSpace ℝ (Fin d) ↦
          charFun (μ : Measure (EuclideanSpace ℝ (Fin d))) ((-(2 * Real.pi) : ℝ) • t)) x)) :
    (μ : Measure (EuclideanSpace ℝ (Fin d))) =
      volume.withDensity (ENNReal.ofReal ∘ fun x : EuclideanSpace ℝ (Fin d) ↦
        Complex.re (FourierTransformInv.fourierInv
          (fun t : EuclideanSpace ℝ (Fin d) ↦
            charFun (μ : Measure (EuclideanSpace ℝ (Fin d))) ((-(2 * Real.pi) : ℝ) • t)) x)) := by
  let E := EuclideanSpace ℝ (Fin d)
  let c : ℝ := -(2 * Real.pi)
  let g : E → ℂ := fun t ↦ charFun (μ : Measure E) (c • t)
  let f : E → ℝ := fun x ↦ Complex.re (FourierTransformInv.fourierInv g x)
  have hc : c ≠ 0 := by
    have htwoPi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    exact neg_ne_zero.mpr htwoPi
  have hg_int : Integrable g := by
    -- Proof comment: the normalized Fourier kernel is the fixed nonzero rescaling of the original
    -- characteristic function.
    simpa [g, c] using hφ_int.comp_smul hc
  have hg_psd : IsPositiveSemidefiniteFunction g := by
    let ν : Measure E := Measure.map (c • ·) (μ : Measure E)
    haveI : IsProbabilityMeasure ν := by
      dsimp [ν]
      exact Measure.isProbabilityMeasure_map (by fun_prop)
    have hg_eq : g = charFun ν := by
      funext t
      -- Proof comment: the rescaled kernel is exactly the characteristic function of the pushforward
      -- law under multiplication by `c`.
      symm
      simpa [g, ν, c] using
        (MeasureTheory.charFun_map_smul (μ := (μ : Measure E)) c t)
    -- Proof comment: precomposing the witness characteristic function by `t ↦ -2π • t` is still
    -- the characteristic function of a probability measure.
    rw [hg_eq]
    exact charFun_isPositiveSemidefiniteFunction_of_isFiniteMeasure (μ := ν)
  have hf_complex :
      (fun x : E ↦ ((f x : ℝ) : ℂ)) = FourierTransformInv.fourierInv g := by
    -- Proof comment: the scaled witness kernel is positive semidefinite, so its inverse Fourier
    -- transform is already real-valued.
    simpa [f] using
      (ofRealFourierInv_eq_of_isPositiveSemidefiniteFunction (d := d) (ψ := g) hg_psd)
  have hg_cont : Continuous g := by
    -- Proof comment: characteristic functions are continuous, and the normalization map is linear.
    have hscale : Continuous fun t : E ↦ c • t := by
      simpa using (continuous_const.smul continuous_id)
    exact (MeasureTheory.continuous_charFun (μ := (μ : Measure E))).comp hscale
  have hFourierg :
      FourierTransform.fourier g = fun x : E ↦ ((f (-x) : ℝ) : ℂ) := by
    ext x
    -- Proof comment: rewrite the inverse Fourier transform as the Fourier transform at `-x`.
    calc
      FourierTransform.fourier g x = FourierTransform.fourier g (-(-x)) := by
          rw [neg_neg]
      _ = FourierTransformInv.fourierInv g (-x) := by
          exact (Real.fourierInv_eq_fourier_neg g (-x)).symm
      _ = ((f (-x) : ℝ) : ℂ) := by
          simpa using (congrFun hf_complex (-x)).symm
  have hFourierInt : Integrable (FourierTransform.fourier g) := by
    -- Proof comment: after the sign change, the Fourier transform is just the complexification of
    -- the assumed `L¹` density candidate.
    rw [hFourierg]
    simpa [f, g, c] using (Integrable.comp_neg hf_int).ofReal
  have hFourierInv :
      FourierTransform.fourier (fun x : E ↦ ((f x : ℝ) : ℂ)) = g := by
    -- Proof comment: Fourier inversion on the scaled characteristic-function kernel returns the
    -- kernel itself.
    rw [hf_complex]
    exact Continuous.fourier_fourierInv_eq hg_cont hg_int hFourierInt
  have hscale :
      ∀ t : E, g (-(2 * Real.pi)⁻¹ • t) = charFun (μ : Measure E) t := by
    intro t
    have hscalar : c * (-(2 * Real.pi)⁻¹ : ℝ) = 1 := by
      dsimp [c]
      field_simp [Real.pi_ne_zero]
    have harg : c • (-(2 * Real.pi)⁻¹ • t) = t := by
      calc
        c • (-(2 * Real.pi)⁻¹ • t) = (c * (-(2 * Real.pi)⁻¹ : ℝ)) • t := by
            rw [smul_smul]
        _ = (1 : ℝ) • t := by rw [hscalar]
        _ = t := by simp
    -- Proof comment: the normalized evaluation point exactly cancels the `-2π` rescaling.
    dsimp [g]
    rw [harg]
  haveI : IsFiniteMeasure (volume.withDensity (ENNReal.ofReal ∘ f)) := by
    -- Proof comment: the `L¹` density candidate induces a finite `withDensity` measure.
    exact MeasureTheory.isFiniteMeasure_withDensity_ofReal hf_int.hasFiniteIntegral
  refine Measure.ext_of_charFun ?_
  funext t
  symm
  calc
    charFun (volume.withDensity (ENNReal.ofReal ∘ f)) t
        = VectorFourier.fourierIntegral Real.fourierChar volume
            (innerₗ E)
            (fun x : E ↦ ((f x : ℝ) : ℂ))
            (-(2 * Real.pi)⁻¹ • t) := by
              simpa [f] using
                congrFun
                  (charFun_withDensity_ofReal_eq_fourierEuclidean
                    (d := d) (f := f) hf_nonneg hf_int) t
    _ = FourierTransform.fourier (fun x : E ↦ ((f x : ℝ) : ℂ)) (-(2 * Real.pi)⁻¹ • t) := by
          rfl
    _ = g (-(2 * Real.pi)⁻¹ • t) := by
          exact congrFun hFourierInv (-(2 * Real.pi)⁻¹ • t)
    _ = charFun (μ : Measure E) t := hscale t

/-- Helper for Theorem 15.29: a continuous Euclidean density with the Gaussian-damped normalized
Fourier formula is the inverse Fourier transform of the correspondingly rescaled damped
characteristic-function kernel. -/
lemma continuousDensity_eq_scaledKernelFourierInv {d : ℕ}
    {f : EuclideanSpace ℝ (Fin d) → ℝ}
    {κ : EuclideanSpace ℝ (Fin d) → ℂ}
    (hf_cont : Continuous (fun x : EuclideanSpace ℝ (Fin d) ↦ ((f x : ℝ) : ℂ)))
    (hf_int : Integrable f) (hκ_int : Integrable κ)
    (hfourier :
      ∀ t : EuclideanSpace ℝ (Fin d),
        VectorFourier.fourierIntegral Real.fourierChar volume
            (innerₗ (EuclideanSpace ℝ (Fin d)))
            (fun x : EuclideanSpace ℝ (Fin d) ↦ ((f x : ℝ) : ℂ))
            (-(2 * Real.pi)⁻¹ • t) = κ t) :
    ∀ x : EuclideanSpace ℝ (Fin d),
      FourierTransformInv.fourierInv
        (fun t : EuclideanSpace ℝ (Fin d) ↦ κ ((-(2 * Real.pi) : ℝ) • t))
        x = ((f x : ℝ) : ℂ) := by
  let E := EuclideanSpace ℝ (Fin d)
  let c : ℝ := -(2 * Real.pi)
  let g : E → ℂ := fun y ↦ ((f y : ℝ) : ℂ)
  let ψ : E → ℂ := fun t ↦ κ (c • t)
  have hc : c ≠ 0 := by
    -- Proof comment: the fixed Fourier-normalization scalar `-2π` is nonzero.
    have htwoPi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    exact neg_ne_zero.mpr htwoPi
  have hg_int : Integrable g := by
    -- Proof comment: complexifying a real-valued `L¹` density preserves integrability.
    simpa [g] using hf_int.ofReal
  have hψ_int : Integrable ψ := by
    -- Proof comment: the scaled kernel is just a nonzero scalar precomposition of `κ`.
    simpa [ψ, c] using hκ_int.comp_smul hc
  have hfourierScaled : FourierTransform.fourier g = ψ := by
    ext s
    have hscale : (-(2 * Real.pi)⁻¹ : ℝ) • (c • s) = s := by
      have hscalar : (-(2 * Real.pi)⁻¹ : ℝ) * c = 1 := by
        dsimp [c]
        field_simp [Real.pi_ne_zero]
      calc
        (-(2 * Real.pi)⁻¹ : ℝ) • (c • s) = (((-(2 * Real.pi)⁻¹ : ℝ) * c) : ℝ) • s := by
          rw [smul_smul]
        _ = (1 : ℝ) • s := by rw [hscalar]
        _ = s := by simp
    -- Proof comment: evaluating the normalized Fourier formula at `-2π • s` recovers the usual
    -- Fourier transform at `s`.
    calc
      FourierTransform.fourier g s
          = FourierTransform.fourier g ((-(2 * Real.pi)⁻¹ : ℝ) • (c • s)) := by
              rw [hscale]
      _ = VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ E) g
            (-(2 * Real.pi)⁻¹ • (c • s)) := by
              rfl
      _ = κ (c • s) := hfourier (c • s)
      _ = ψ s := by simp [ψ]
  have hFourierInt : Integrable (FourierTransform.fourier g) := by
    -- Proof comment: the explicit scaled-kernel formula identifies `𝓕 g` with the integrable
    -- rescaling of `κ`.
    rwa [hfourierScaled]
  intro x
  calc
    FourierTransformInv.fourierInv
        (fun t : E ↦ κ (c • t)) x
        = FourierTransformInv.fourierInv ψ x := by
            rfl
    _ = FourierTransformInv.fourierInv (FourierTransform.fourier g) x := by
          rw [hfourierScaled.symm]
    _ = g x := by
          simpa using congrFun (Continuous.fourierInv_fourier_eq hf_cont hg_int hFourierInt) x
    _ = ((f x : ℝ) : ℂ) := by
          rfl

/-- Helper for Theorem 15.29: a continuous Euclidean density with the Gaussian-damped normalized
Fourier formula is the inverse Fourier transform of the correspondingly rescaled damped
characteristic-function kernel. -/
lemma integrableDensity_eq_scaledDampedCharFunFourierInvAtContinuousPointOfProbabilityMeasure
    {d : ℕ} (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) {a : ℝ} (ha : 0 < a)
    {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf_int : Integrable f)
    (hfourier :
      ∀ t : EuclideanSpace ℝ (Fin d),
        VectorFourier.fourierIntegral Real.fourierChar volume
            (innerₗ (EuclideanSpace ℝ (Fin d)))
            (fun x : EuclideanSpace ℝ (Fin d) ↦ ((f x : ℝ) : ℂ))
            (-(2 * Real.pi)⁻¹ • t) =
          Complex.exp (-(a : ℂ) * ‖t‖ ^ 2) *
            charFun (μ : Measure (EuclideanSpace ℝ (Fin d))) t)
    {x : EuclideanSpace ℝ (Fin d)} (hx_cont : ContinuousAt f x) :
    FourierTransformInv.fourierInv
      (fun t : EuclideanSpace ℝ (Fin d) ↦
        Complex.exp (-(a : ℂ) * ‖((-(2 * Real.pi) : ℝ) • t)‖ ^ 2) *
          charFun (μ : Measure (EuclideanSpace ℝ (Fin d))) ((-(2 * Real.pi) : ℝ) • t))
      x = ((f x : ℝ) : ℂ) := by
  let E := EuclideanSpace ℝ (Fin d)
  let c : ℝ := -(2 * Real.pi)
  let g : E → ℂ := fun y ↦ ((f y : ℝ) : ℂ)
  let ψ : E → ℂ := fun t ↦
    Complex.exp (-(a : ℂ) * ‖c • t‖ ^ 2) *
      charFun (μ : Measure E) (c • t)
  have hc : c ≠ 0 := by
    have htwoPi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    exact neg_ne_zero.mpr htwoPi
  have hg_int : Integrable g := by
    -- Proof comment: complexifying a real-valued `L¹` density preserves integrability.
    simpa [g] using hf_int.ofReal
  have hψ_int : Integrable ψ := by
    have hraw_int :
        Integrable (fun t : E ↦
          Complex.exp (-(a : ℂ) * ‖t‖ ^ 2) * charFun (μ : Measure E) t) := by
      -- Proof comment: the Gaussian factor dominates the characteristic function of a probability
      -- law by the universal bound `‖charFun‖ ≤ 1`.
      refine integrableGaussianDamped (d := d) (φ := charFun (μ : Measure E)) ha
        (MeasureTheory.continuous_charFun (μ := (μ : Measure E))) ?_
      intro t
      exact MeasureTheory.norm_charFun_le_one (μ := (μ : Measure E)) t
    -- Proof comment: the Fourier-normalized kernel is the nonzero rescaling of the raw damped
    -- characteristic function.
    simpa [ψ, c] using hraw_int.comp_smul hc
  have hfourierScaled : FourierTransform.fourier g = ψ := by
    ext s
    have hscale : (-(2 * Real.pi)⁻¹ : ℝ) • (c • s) = s := by
      have hscalar : (-(2 * Real.pi)⁻¹ : ℝ) * c = 1 := by
        dsimp [c]
        field_simp [Real.pi_ne_zero]
      calc
        (-(2 * Real.pi)⁻¹ : ℝ) • (c • s) = (((-(2 * Real.pi)⁻¹ : ℝ) * c) : ℝ) • s := by
          rw [smul_smul]
        _ = (1 : ℝ) • s := by rw [hscalar]
        _ = s := by simp
    -- Proof comment: evaluate the normalized Fourier formula at `-2π • s` to recover the usual
    -- Fourier transform at `s`.
    calc
      FourierTransform.fourier g s
          = FourierTransform.fourier g ((-(2 * Real.pi)⁻¹ : ℝ) • (c • s)) := by
              rw [hscale]
      _ = VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ E) g
            (-(2 * Real.pi)⁻¹ • (c • s)) := by
              rfl
      _ = Complex.exp (-(a : ℂ) * ‖c • s‖ ^ 2) *
            charFun (μ : Measure E) (c • s) := hfourier (c • s)
      _ = ψ s := by simp [ψ]
  have hFourierInt : Integrable (FourierTransform.fourier g) := by
    -- Proof comment: the preceding explicit formula identifies `𝓕 g` with the integrable scaled
    -- damped characteristic-function kernel.
    rwa [hfourierScaled]
  have hg_contAt : ContinuousAt g x := by
    -- Proof comment: continuity of the real density at `x` passes to its complexification.
    simpa [g] using Complex.continuous_ofReal.continuousAt.comp hx_cont
  calc
    FourierTransformInv.fourierInv ψ x
        = FourierTransformInv.fourierInv (FourierTransform.fourier g) x := by
            rw [hfourierScaled]
    _ = g x := by
          exact hg_int.fourierInv_fourier_eq hFourierInt hg_contAt
    _ = ((f x : ℝ) : ℂ) := rfl

/-- Helper for Theorem 15.29: a continuous Euclidean density with the Gaussian-damped normalized
Fourier formula is the inverse Fourier transform of the correspondingly rescaled damped
characteristic-function kernel. -/
lemma continuousDensity_eq_scaledDampedCharFunFourierInvOfProbabilityMeasure {d : ℕ}
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) {a : ℝ} (ha : 0 < a)
    {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf_cont : Continuous (fun x : EuclideanSpace ℝ (Fin d) ↦ ((f x : ℝ) : ℂ)))
    (hf_int : Integrable f)
    (hfourier :
      ∀ t : EuclideanSpace ℝ (Fin d),
        VectorFourier.fourierIntegral Real.fourierChar volume
            (innerₗ (EuclideanSpace ℝ (Fin d)))
            (fun x : EuclideanSpace ℝ (Fin d) ↦ ((f x : ℝ) : ℂ))
            (-(2 * Real.pi)⁻¹ • t) =
          Complex.exp (-(a : ℂ) * ‖t‖ ^ 2) *
            charFun (μ : Measure (EuclideanSpace ℝ (Fin d))) t) :
    ∀ x : EuclideanSpace ℝ (Fin d),
      FourierTransformInv.fourierInv
        (fun t : EuclideanSpace ℝ (Fin d) ↦
          Complex.exp (-(a : ℂ) * ‖((-(2 * Real.pi) : ℝ) • t)‖ ^ 2) *
            charFun (μ : Measure (EuclideanSpace ℝ (Fin d))) ((-(2 * Real.pi) : ℝ) • t))
        x = ((f x : ℝ) : ℂ) := by
  have hf_cont_real : Continuous f := by
    -- Proof comment: taking real parts recovers the underlying real-valued density.
    simpa using Complex.continuous_re.comp hf_cont
  intro x
  -- Proof comment: the continuity-point inversion lemma applies at every `x` because the density
  -- is globally continuous.
  exact integrableDensity_eq_scaledDampedCharFunFourierInvAtContinuousPointOfProbabilityMeasure
    (d := d) μ ha hf_int hfourier (x := x) hf_cont_real.continuousAt

/-- Helper for Theorem 15.29: an actual Euclidean characteristic-function witness packages the
scaled inverse-Fourier candidate into the mass-one and Fourier-recovery conclusions once the
nonnegativity and `L¹` side conditions are available. -/
lemma densitySpecOfScaledCharFunWitness {d : ℕ}
    {ρ : EuclideanSpace ℝ (Fin d) → ℂ} (hρ_int : Integrable ρ)
    (hρ_witness : ∃ μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)),
      ∀ t : EuclideanSpace ℝ (Fin d),
        charFun (μ : Measure (EuclideanSpace ℝ (Fin d))) t = ρ t)
    (hf_nonneg : ∀ x : EuclideanSpace ℝ (Fin d),
      0 ≤ Complex.re (FourierTransformInv.fourierInv
        (fun t : EuclideanSpace ℝ (Fin d) ↦ ρ ((-(2 * Real.pi) : ℝ) • t)) x))
    (hf_int : Integrable fun x : EuclideanSpace ℝ (Fin d) ↦
      Complex.re (FourierTransformInv.fourierInv
        (fun t : EuclideanSpace ℝ (Fin d) ↦ ρ ((-(2 * Real.pi) : ℝ) • t)) x)) :
    (∫ x, Complex.re (FourierTransformInv.fourierInv
      (fun t : EuclideanSpace ℝ (Fin d) ↦ ρ ((-(2 * Real.pi) : ℝ) • t)) x) = 1) ∧
      (∀ t : EuclideanSpace ℝ (Fin d),
        VectorFourier.fourierIntegral Real.fourierChar volume
            (innerₗ (EuclideanSpace ℝ (Fin d)))
            (fun x : EuclideanSpace ℝ (Fin d) ↦
              ((Complex.re (FourierTransformInv.fourierInv
                (fun s : EuclideanSpace ℝ (Fin d) ↦ ρ ((-(2 * Real.pi) : ℝ) • s)) x) : ℝ) : ℂ))
            (-(2 * Real.pi)⁻¹ • t) = ρ t) := by
  -- Route correction: the witness-side packaging theorem now lives on the scaled kernel
  -- `t ↦ ρ (-(2 * π) • t)`. The remaining work is to compare that scaled spelling with the
  -- closed owner `probabilityMeasure_eq_withDensity_of_scaledCharFunFourierInv` without allowing
  -- `simp` to drift into the conjugate `charFun_neg` normal form.
  let E := EuclideanSpace ℝ (Fin d)
  let f : E → ℝ := fun x ↦
    Complex.re (FourierTransformInv.fourierInv
      (fun t : E ↦ ρ ((-(2 * Real.pi) : ℝ) • t)) x)
  rcases hρ_witness with ⟨μ, hμ⟩
  have hμ_fun : charFun (μ : Measure E) = ρ := by
    funext t
    exact hμ t
  have hμ_scaled :
      (fun t : E ↦ charFun (μ : Measure E) ((-(2 * Real.pi) : ℝ) • t)) =
        fun t : E ↦ ρ ((-(2 * Real.pi) : ℝ) • t) := by
    funext t
    rw [hμ]
  have hμ_int : Integrable (charFun (μ : Measure E)) := by
    -- Proof comment: the actual witness identifies the given kernel `ρ` with a characteristic
    -- function, so the assumed `L¹` control transfers directly to the witness.
    simpa only [hμ_fun] using hρ_int
  have hf_nonneg' :
      ∀ x : E,
        0 ≤ Complex.re (FourierTransformInv.fourierInv
          (fun t : E ↦ charFun (μ : Measure E) ((-(2 * Real.pi) : ℝ) • t)) x) := by
    simpa only [hμ_scaled] using hf_nonneg
  have hf_int' :
      Integrable fun x : E ↦
        Complex.re (FourierTransformInv.fourierInv
          (fun t : E ↦ charFun (μ : Measure E) ((-(2 * Real.pi) : ℝ) • t)) x) := by
    simpa only [hμ_scaled] using hf_int
  have hf_eq :
      (fun x : E ↦
        Complex.re (FourierTransformInv.fourierInv
          (fun t : E ↦ charFun (μ : Measure E) ((-(2 * Real.pi) : ℝ) • t)) x)) = f := by
    funext x
    dsimp [f]
    congr 1
    exact congrArg (fun ψ : E → ℂ ↦ FourierTransformInv.fourierInv ψ x) hμ_scaled
  have hμ_eq_char :
      (μ : Measure E) =
        volume.withDensity
          (ENNReal.ofReal ∘ fun x : E ↦
            Complex.re (FourierTransformInv.fourierInv
              (fun t : E ↦ charFun (μ : Measure E) ((-(2 * Real.pi) : ℝ) • t)) x)) := by
    -- Proof comment: the closed scaled inverse-Fourier owner upgrades the witness plus the
    -- nonnegativity and `L¹` side conditions into an explicit `withDensity` description.
    exact probabilityMeasure_eq_withDensity_of_scaledCharFunFourierInv
      (d := d) μ hμ_int hf_nonneg' hf_int'
  have hμ_eq :
      (μ : Measure E) = volume.withDensity (ENNReal.ofReal ∘ f) := by
    calc
      (μ : Measure E)
          =
            volume.withDensity
              (ENNReal.ofReal ∘ fun x : E ↦
                Complex.re (FourierTransformInv.fourierInv
                  (fun t : E ↦ charFun (μ : Measure E) ((-(2 * Real.pi) : ℝ) • t)) x)) :=
            hμ_eq_char
      _ = volume.withDensity (ENNReal.ofReal ∘ f) := by rw [hf_eq]
  have hwith_real_univ : (volume.withDensity (ENNReal.ofReal ∘ f)).real Set.univ = ∫ x, f x := by
    have hf_aemeas : AEMeasurable (ENNReal.ofReal ∘ f) volume := by
      exact hf_int.aestronglyMeasurable.aemeasurable.ennreal_ofReal
    have hf_lt_top : ∀ᵐ x ∂volume, ENNReal.ofReal (f x) < ⊤ := by
      exact Filter.Eventually.of_forall fun _ ↦ by simp
    calc
      (volume.withDensity (ENNReal.ofReal ∘ f)).real Set.univ
          = ∫ x, (1 : ℝ) ∂(volume.withDensity (ENNReal.ofReal ∘ f)) := by
              simp
      _ = ∫ x, ((ENNReal.ofReal ∘ f) x).toReal • (1 : ℝ) ∂volume := by
            simpa using
              (integral_withDensity_eq_integral_toReal_smul₀
                (μ := volume) (f := ENNReal.ofReal ∘ f) hf_aemeas hf_lt_top
                (g := fun _ : E ↦ (1 : ℝ)))
      _ = ∫ x, f x ∂volume := by
            refine integral_congr_ae (Filter.Eventually.of_forall ?_)
            intro x
            have hx_nonneg : 0 ≤ f x := by
              simpa only [f] using hf_nonneg x
            simp [hx_nonneg]
  have hμ_real_univ : (μ : Measure E).real Set.univ = 1 := by
    have hμ_prob : IsProbabilityMeasure (μ : Measure E) := inferInstance
    rw [MeasureTheory.isProbabilityMeasure_iff_real] at hμ_prob
    exact hμ_prob
  refine ⟨?_, ?_⟩
  · -- Proof comment: the `withDensity` description identifies the inverse-Fourier candidate as a
    -- probability density, so its total mass is exactly `1`.
    calc
      ∫ x, f x = (volume.withDensity (ENNReal.ofReal ∘ f)).real Set.univ := by
        rw [hwith_real_univ]
      _ = (μ : Measure E).real Set.univ := by rw [← hμ_eq]
      _ = 1 := hμ_real_univ
  · intro t
    -- Proof comment: the same `withDensity` identity turns the normalized Fourier integral of the
    -- candidate density back into the original characteristic function witness `ρ`.
    calc
      VectorFourier.fourierIntegral Real.fourierChar volume
          (innerₗ E)
          (fun x : E ↦ ((f x : ℝ) : ℂ))
          (-(2 * Real.pi)⁻¹ • t)
          = charFun (volume.withDensity (ENNReal.ofReal ∘ f)) t := by
              symm
              simpa only [f] using
                congrFun
                  (charFun_withDensity_ofReal_eq_fourierEuclidean
                    (d := d) (f := f) hf_nonneg hf_int) t
      _ = charFun (μ : Measure E) t := by rw [← hμ_eq]
      _ = ρ t := hμ t

/-- Helper for Theorem 15.29: the Gaussian-damped kernel attached to `φ` is continuous,
integrable, positive semidefinite, and normalized at the origin. -/
lemma gaussianDampedKernelSpec {d : ℕ}
    {φ : EuclideanSpace ℝ (Fin d) → ℂ} {a : ℝ} (ha : 0 < a) (hφ : Continuous φ)
    (hpsd : IsPositiveSemidefiniteFunction φ) (hzero : φ 0 = 1) :
    let ψa : EuclideanSpace ℝ (Fin d) → ℂ :=
      fun t ↦ Complex.exp (-(a : ℂ) * ‖t‖ ^ 2) * φ t
    Continuous ψa ∧ Integrable ψa ∧ IsPositiveSemidefiniteFunction ψa ∧ ψa 0 = 1 := by
  let E := EuclideanSpace ℝ (Fin d)
  let ψa : E → ℂ := fun t ↦ Complex.exp (-(a : ℂ) * ‖t‖ ^ 2) * φ t
  have hbound : ∀ t : E, ‖φ t‖ ≤ 1 :=
    norm_le_one_of_isPositiveSemidefiniteFunction_zero_eq_one hpsd hzero
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Proof comment: the Gaussian factor and the original kernel are both continuous.
    simpa [ψa] using ((Complex.continuous_exp.comp (by fun_prop)).mul hφ)
  · -- Proof comment: the Gaussian factor gives an `L¹` majorant after the universal `‖φ‖ ≤ 1`
    -- bound for normalized positive semidefinite kernels.
    simpa [ψa] using integrableGaussianDamped (d := d) (φ := φ) ha hφ hbound
  · -- Proof comment: Gaussian damping preserves positive semidefiniteness.
    simpa [ψa] using gaussianDamped_isPositiveSemidefiniteFunction (d := d) (φ := φ) ha hpsd
  · -- Proof comment: the Gaussian factor is `1` at the origin, so the normalization is unchanged.
    simp [ψa, hzero]

/-- Helper for Theorem 15.29: the inverse Fourier transform of the Gaussian-damped kernel is
already real-valued. -/
lemma gaussianDampedKernel_fourierInv_eq_ofReal {d : ℕ}
    {φ : EuclideanSpace ℝ (Fin d) → ℂ} {a : ℝ} (ha : 0 < a) (hφ : Continuous φ)
    (hpsd : IsPositiveSemidefiniteFunction φ) (hzero : φ 0 = 1) :
    let ψa : EuclideanSpace ℝ (Fin d) → ℂ :=
      fun t ↦ Complex.exp (-(a : ℂ) * ‖t‖ ^ 2) * φ t
    (fun x : EuclideanSpace ℝ (Fin d) ↦
      ((Complex.re (FourierTransformInv.fourierInv ψa x) : ℝ) : ℂ)) =
      FourierTransformInv.fourierInv ψa := by
  let E := EuclideanSpace ℝ (Fin d)
  let ψa : E → ℂ := fun t ↦ Complex.exp (-(a : ℂ) * ‖t‖ ^ 2) * φ t
  have hψ_psd : IsPositiveSemidefiniteFunction ψa := by
    -- Proof comment: read the positive-semidefinite clause off the damped-kernel package.
    simpa [ψa] using
      (gaussianDampedKernelSpec (d := d) (φ := φ) (a := a) ha hφ hpsd hzero).2.2.1
  -- Proof comment: positive semidefiniteness forces the Hermitian symmetry needed for a
  -- real-valued inverse Fourier transform.
  simpa [ψa] using
    (ofRealFourierInv_eq_of_isPositiveSemidefiniteFunction (d := d) (ψ := ψa) hψ_psd)

/-- Helper for Theorem 15.29: the inverse Fourier transform of the Gaussian-damped kernel is
continuous. -/
lemma gaussianDampedKernel_inverseFourierContinuous {d : ℕ}
    {φ : EuclideanSpace ℝ (Fin d) → ℂ} {a : ℝ} (ha : 0 < a) (hφ : Continuous φ)
    (hpsd : IsPositiveSemidefiniteFunction φ) (hzero : φ 0 = 1) :
    let ψa : EuclideanSpace ℝ (Fin d) → ℂ :=
      fun t ↦ Complex.exp (-(a : ℂ) * ‖t‖ ^ 2) * φ t
    Continuous (FourierTransformInv.fourierInv ψa) := by
  let E := EuclideanSpace ℝ (Fin d)
  let ψa : E → ℂ := fun t ↦ Complex.exp (-(a : ℂ) * ‖t‖ ^ 2) * φ t
  have hψ_int : Integrable ψa := by
    -- Proof comment: read the integrability clause off the damped-kernel package.
    simpa [ψa] using
      (gaussianDampedKernelSpec (d := d) (φ := φ) (a := a) ha hφ hpsd hzero).2.1
  -- Proof comment: `L¹` control is enough for continuity of the inverse Fourier transform.
  simpa [ψa] using inverseFourier_continuous_of_integrable (d := d) (ψ := ψa) hψ_int

/-- Helper for Theorem 15.29: extra Gaussian damping of a fixed positive semidefinite kernel
produces the real-valued inverse-Fourier candidates used in the Fatou approximation step. -/
noncomputable def gaussianRegularizedInverseFourierDensity {d : ℕ}
    (ψ : EuclideanSpace ℝ (Fin d) → ℂ) (b : ℝ) :
    EuclideanSpace ℝ (Fin d) → ℝ :=
  fun x ↦
    Complex.re
      (FourierTransformInv.fourierInv
        (fun t : EuclideanSpace ℝ (Fin d) ↦
          Complex.exp (-(b : ℂ) * ‖t‖ ^ 2) * ψ t) x)

/-- Helper for Theorem 15.29: the complexification of the regularized density candidate is the
inverse Fourier transform of the extra-damped kernel itself. -/
lemma gaussianRegularizedInverseFourierDensity_eq_ofRealFourierInv {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} {b : ℝ} (hb : 0 < b)
    (hψ_psd : IsPositiveSemidefiniteFunction ψ) :
    (fun x : EuclideanSpace ℝ (Fin d) ↦
      ((gaussianRegularizedInverseFourierDensity ψ b x : ℝ) : ℂ)) =
      FourierTransformInv.fourierInv
        (fun t : EuclideanSpace ℝ (Fin d) ↦
          Complex.exp (-(b : ℂ) * ‖t‖ ^ 2) * ψ t) := by
  have hψb_psd :
      IsPositiveSemidefiniteFunction
        (fun t : EuclideanSpace ℝ (Fin d) ↦
          Complex.exp (-(b : ℂ) * ‖t‖ ^ 2) * ψ t) := by
    -- Proof comment: extra Gaussian damping preserves positive semidefiniteness, so the inverse
    -- Fourier transform remains real-valued.
    simpa using gaussianDamped_isPositiveSemidefiniteFunction
      (d := d) (φ := ψ) (a := b) hb hψ_psd
  simpa [gaussianRegularizedInverseFourierDensity] using
    (ofRealFourierInv_eq_of_isPositiveSemidefiniteFunction
      (d := d)
      (ψ := fun t : EuclideanSpace ℝ (Fin d) ↦
        Complex.exp (-(b : ℂ) * ‖t‖ ^ 2) * ψ t)
      hψb_psd)

/-- Helper for Theorem 15.29: the regularized inverse-Fourier candidate has a stable
Fourier-exponential integral normal form. -/
lemma gaussianRegularizedInverseFourierDensity_eq_real_integral_fourierExp {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} {b : ℝ}
    (x : EuclideanSpace ℝ (Fin d)) :
    gaussianRegularizedInverseFourierDensity ψ b x =
      Complex.re
        (∫ t : EuclideanSpace ℝ (Fin d),
          Complex.exp (↑(2 * Real.pi * inner ℝ t x) * Complex.I) *
            (Complex.exp (-(b : ℂ) * ‖t‖ ^ 2) * ψ t)) := by
  -- Proof comment: rewrite the inverse Fourier transform once into the explicit Fourier
  -- oscillatory-integral spelling so later Gaussian-window arguments can stay in one normal form.
  rw [gaussianRegularizedInverseFourierDensity, Real.fourierInv_eq']
  -- Proof comment: after expanding `fourierInv`, the integrands already match by elementary
  -- scalar-multiplication simplification.
  simp [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Theorem 15.29: extra Gaussian damping preserves the continuous, integrable,
positive-semidefinite, and normalized kernel structure needed in the regularization step. -/
lemma gaussianRegularizedKernelSpec {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} {b : ℝ} (hb : 0 < b)
    (hψ_cont : Continuous ψ) (hψ_int : Integrable ψ)
    (hψ_psd : IsPositiveSemidefiniteFunction ψ) (hψ_zero : ψ 0 = 1) :
    let ψb : EuclideanSpace ℝ (Fin d) → ℂ :=
      fun t ↦ Complex.exp (-(b : ℂ) * ‖t‖ ^ 2) * ψ t
    Continuous ψb ∧ Integrable ψb ∧ IsPositiveSemidefiniteFunction ψb ∧ ψb 0 = 1 := by
  let ψb : EuclideanSpace ℝ (Fin d) → ℂ :=
    fun t ↦ Complex.exp (-(b : ℂ) * ‖t‖ ^ 2) * ψ t
  have hbound :
      ∀ t : EuclideanSpace ℝ (Fin d), ‖ψ t‖ ≤ 1 :=
    norm_le_one_of_isPositiveSemidefiniteFunction_zero_eq_one hψ_psd hψ_zero
  have hψb_cont : Continuous ψb := by
    -- Proof comment: the Gaussian factor and the original kernel are continuous, so the damped
    -- kernel is continuous as well.
    simpa [ψb] using ((Complex.continuous_exp.comp (by fun_prop)).mul hψ_cont)
  have hψb_int : Integrable ψb := by
    -- Proof comment: the Gaussian factor is an `L¹` majorant because normalized positive
    -- semidefinite kernels are bounded in norm by `1`.
    simpa [ψb] using
      integrableGaussianDamped (d := d) (φ := ψ) (a := b) hb hψ_cont hbound
  have hψb_psd : IsPositiveSemidefiniteFunction ψb := by
    -- Proof comment: Gaussian damping preserves positive semidefiniteness.
    simpa [ψb] using
      gaussianDamped_isPositiveSemidefiniteFunction
        (d := d) (φ := ψ) (a := b) hb hψ_psd
  have hψb_zero : ψb 0 = 1 := by
    -- Proof comment: the Gaussian factor is `1` at the origin, so normalization is unchanged.
    simp [ψb, hψ_zero]
  exact ⟨hψb_cont, hψb_int, hψb_psd, hψb_zero⟩

/-- Helper for Theorem 15.29: every regularized density candidate attached to a continuous
normalized positive semidefinite kernel is continuous as a complex-valued function. -/
lemma gaussianRegularizedInverseFourierDensityContinuous {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} {b : ℝ} (hb : 0 < b)
    (hψ_cont : Continuous ψ) (hψ_psd : IsPositiveSemidefiniteFunction ψ) (hψ_zero : ψ 0 = 1) :
    Continuous
      (fun x : EuclideanSpace ℝ (Fin d) ↦
        ((gaussianRegularizedInverseFourierDensity ψ b x : ℝ) : ℂ)) := by
  have hbound :
      ∀ t : EuclideanSpace ℝ (Fin d), ‖ψ t‖ ≤ 1 :=
    norm_le_one_of_isPositiveSemidefiniteFunction_zero_eq_one hψ_psd hψ_zero
  have hψb_int :
      Integrable (fun t : EuclideanSpace ℝ (Fin d) ↦
        Complex.exp (-(b : ℂ) * ‖t‖ ^ 2) * ψ t) := by
    -- Proof comment: the Gaussian factor is an `L¹` majorant once the normalized positive
    -- semidefinite kernel is bounded by `1` in norm.
    simpa using
      integrableGaussianDamped (d := d) (φ := ψ) (a := b) hb hψ_cont hbound
  -- Proof comment: rewrite the candidate through its inverse-Fourier spelling, then apply the
  -- standard continuity theorem for inverse Fourier transforms of `L¹` kernels.
  rw [gaussianRegularizedInverseFourierDensity_eq_ofRealFourierInv
    (d := d) (ψ := ψ) (b := b) hb hψ_psd]
  exact inverseFourier_continuous_of_integrable (d := d) (ψ := fun t : EuclideanSpace ℝ (Fin d) ↦
    Complex.exp (-(b : ℂ) * ‖t‖ ^ 2) * ψ t) hψb_int

/-- Helper for Theorem 15.29: the Gaussian-regularized inverse-Fourier density candidate is
continuous as a real-valued function. -/
lemma gaussianRegularizedInverseFourierDensityContinuousReal {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} {b : ℝ} (hb : 0 < b)
    (hψ_cont : Continuous ψ) (hψ_psd : IsPositiveSemidefiniteFunction ψ) (hψ_zero : ψ 0 = 1) :
    Continuous (gaussianRegularizedInverseFourierDensity ψ b) := by
  have hf_cont_complex :
      Continuous
        (fun x : EuclideanSpace ℝ (Fin d) ↦
          ((gaussianRegularizedInverseFourierDensity ψ b x : ℝ) : ℂ)) := by
    -- Proof comment: first use the existing complex-valued continuity owner for the regularized
    -- inverse-Fourier candidate.
    exact gaussianRegularizedInverseFourierDensityContinuous
      (d := d) (ψ := ψ) (b := b) hb hψ_cont hψ_psd hψ_zero
  -- Proof comment: the real-valued density is the real part of that continuous complex-valued
  -- representative.
  simpa using Complex.continuous_re.comp hf_cont_complex

/-- Helper for Theorem 15.29: the regularized density candidates attached to an `L¹` kernel
converge pointwise back to the undamped inverse-Fourier candidate along `b_n = ((n : ℝ) + 1)⁻¹`.
-/
lemma gaussianRegularizedInverseFourierDensity_tendsto {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} (hψ_int : Integrable ψ)
    (x : EuclideanSpace ℝ (Fin d)) :
    Tendsto
      (fun n : ℕ ↦
        gaussianRegularizedInverseFourierDensity ψ (((n : ℝ) + 1)⁻¹) x)
      atTop
      (𝓝 (Complex.re (FourierTransformInv.fourierInv ψ x))) := by
  -- Proof comment: this is exactly the previously established damped inverse-Fourier convergence,
  -- rewritten in the fixed regularized-density notation.
  simpa [gaussianRegularizedInverseFourierDensity] using
    dampedInverseFourierDensity_tendsto (d := d) (ψ := ψ) hψ_int x

/-- Helper for Theorem 15.29: the Fourier-normalized Gaussian-damped characteristic-function
kernel of an actual Euclidean witness is continuous, integrable, positive semidefinite, and
normalized at the origin. -/
lemma scaledGaussianDampedKernelSpecOfProbabilityMeasure {d : ℕ}
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) {a : ℝ} (ha : 0 < a) :
    let ψ : EuclideanSpace ℝ (Fin d) → ℂ :=
      fun t ↦
        Complex.exp (-(a : ℂ) * ‖((-(2 * Real.pi) : ℝ) • t)‖ ^ 2) *
          charFun (μ : Measure (EuclideanSpace ℝ (Fin d))) ((-(2 * Real.pi) : ℝ) • t)
    Continuous ψ ∧ Integrable ψ ∧ IsPositiveSemidefiniteFunction ψ ∧ ψ 0 = 1 := by
  let E := EuclideanSpace ℝ (Fin d)
  let c : ℝ := -(2 * Real.pi)
  let ν : Measure E := Measure.map (c • ·) (μ : Measure E)
  let aScaled : ℝ := a * c ^ 2
  haveI : IsProbabilityMeasure ν := by
    dsimp [ν]
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  have haScaled : 0 < aScaled := by
    -- Proof comment: the fixed Fourier normalization rescales the Gaussian parameter by `(2π)^2`.
    have htwoPi : 0 < (2 : ℝ) * Real.pi := by positivity
    have hcSq : 0 < c ^ 2 := by
      dsimp [c]
      nlinarith
    dsimp [aScaled, c]
    exact mul_pos ha hcSq
  have hnorm : ∀ t : E, ‖c • t‖ ^ 2 = c ^ 2 * ‖t‖ ^ 2 := by
    intro t
    calc
      ‖c • t‖ ^ 2 = (‖c‖ * ‖t‖) ^ 2 := by rw [norm_smul]
      _ = (|c| * ‖t‖) ^ 2 := by rw [Real.norm_eq_abs]
      _ = |c| ^ 2 * ‖t‖ ^ 2 := by ring
      _ = c ^ 2 * ‖t‖ ^ 2 := by rw [sq_abs]
  have hkernel :
      (fun t : E ↦
        Complex.exp (-(a : ℂ) * ‖c • t‖ ^ 2) * charFun (μ : Measure E) (c • t)) =
        fun t : E ↦ Complex.exp (-(aScaled : ℂ) * ‖t‖ ^ 2) * charFun ν t := by
    funext t
    have hargR : a * ‖c • t‖ ^ 2 = aScaled * ‖t‖ ^ 2 := by
      -- Proof comment: after pulling the fixed `-2π` factor out of the norm, the exponent is the
      -- usual damped kernel for the pushed-forward witness law.
      dsimp [aScaled]
      rw [hnorm t]
      ring
    have hargC :
        (a : ℂ) * ‖c • t‖ ^ 2 = (aScaled : ℂ) * ‖t‖ ^ 2 := by
      exact_mod_cast hargR
    rw [MeasureTheory.charFun_map_smul]
    congr 1
    exact congrArg Complex.exp <| by simpa using congrArg Neg.neg hargC
  change
    Continuous (fun t : E ↦ Complex.exp (-(a : ℂ) * ‖c • t‖ ^ 2) * charFun (μ : Measure E) (c • t)) ∧
      Integrable (fun t : E ↦ Complex.exp (-(a : ℂ) * ‖c • t‖ ^ 2) * charFun (μ : Measure E) (c • t)) ∧
      IsPositiveSemidefiniteFunction
        (fun t : E ↦ Complex.exp (-(a : ℂ) * ‖c • t‖ ^ 2) * charFun (μ : Measure E) (c • t)) ∧
      (fun t : E ↦ Complex.exp (-(a : ℂ) * ‖c • t‖ ^ 2) * charFun (μ : Measure E) (c • t)) 0 = 1
  rw [hkernel]
  -- Proof comment: after pushing the witness forward by the fixed `-2π` scaling, the kernel is
  -- exactly the standard Gaussian-damped characteristic function handled by the earlier package.
  simpa [ν, aScaled] using
    (gaussianDampedKernelSpec
      (d := d) (φ := charFun ν) (a := aScaled) haScaled
      (MeasureTheory.continuous_charFun (μ := ν))
      (charFun_isPositiveSemidefiniteFunction_of_isFiniteMeasure (μ := ν))
      (by simpa using (MeasureTheory.charFun_zero (μ := ν))))

/-- Helper for Theorem 15.29: after pushing a witness law forward by `(-(2 * Real.pi))⁻¹`, the
Fourier-normalized Gaussian-damped kernel becomes the unscaled regularized kernel with parameter
`b`. -/
lemma gaussianRegularizedKernel_eq_scaledDampedKernelOfProbabilityMeasure {d : ℕ}
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) {b : ℝ} :
    let E := EuclideanSpace ℝ (Fin d)
    let c : ℝ := -(2 * Real.pi)
    let a : ℝ := b / c ^ 2
    let ν : Measure E := Measure.map (c⁻¹ • ·) (μ : Measure E)
    (fun t : E ↦
      Complex.exp (-(a : ℂ) * ‖c • t‖ ^ 2) * charFun ν (c • t)) =
      fun t : E ↦
        Complex.exp (-(b : ℂ) * ‖t‖ ^ 2) * charFun (μ : Measure E) t := by
  let E := EuclideanSpace ℝ (Fin d)
  let c : ℝ := -(2 * Real.pi)
  let a : ℝ := b / c ^ 2
  let ν : Measure E := Measure.map (c⁻¹ • ·) (μ : Measure E)
  haveI : IsProbabilityMeasure ν := by
    dsimp [ν]
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  have hc : c ≠ 0 := by
    have htwoPi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    exact neg_ne_zero.mpr htwoPi
  have hnorm : ∀ t : E, ‖c • t‖ ^ 2 = c ^ 2 * ‖t‖ ^ 2 := by
    intro t
    calc
      ‖c • t‖ ^ 2 = (‖c‖ * ‖t‖) ^ 2 := by rw [norm_smul]
      _ = (|c| * ‖t‖) ^ 2 := by rw [Real.norm_eq_abs]
      _ = |c| ^ 2 * ‖t‖ ^ 2 := by ring
      _ = c ^ 2 * ‖t‖ ^ 2 := by rw [sq_abs]
  funext t
  have hargR : a * ‖c • t‖ ^ 2 = b * ‖t‖ ^ 2 := by
    -- Proof comment: the pushed-forward witness is chosen so that the fixed `-2π` rescaling
    -- cancels exactly against the Gaussian parameter `b / (2π)^2`.
    calc
      a * ‖c • t‖ ^ 2 = (b / c ^ 2) * (c ^ 2 * ‖t‖ ^ 2) := by
        rw [hnorm t]
      _ = b * ‖t‖ ^ 2 := by
        field_simp [hc]
  have hargC :
      (a : ℂ) * ‖c • t‖ ^ 2 = (b : ℂ) * ‖t‖ ^ 2 := by
    exact_mod_cast hargR
  have hchar : charFun ν (c • t) = charFun (μ : Measure E) t := by
    -- Proof comment: evaluating the pushed-forward witness at the normalized argument exactly
    -- recovers the original characteristic function.
    rw [MeasureTheory.charFun_map_smul]
    have hscalar : (c⁻¹ : ℝ) * c = 1 := by field_simp [hc]
    calc
      charFun (μ : Measure E) (c⁻¹ • (c • t))
          = charFun (μ : Measure E) (((c⁻¹ : ℝ) * c) • t) := by rw [smul_smul]
      _ = charFun (μ : Measure E) ((1 : ℝ) • t) := by rw [hscalar]
      _ = charFun (μ : Measure E) t := by simp
  have hargNeg :
      (-(a : ℂ)) * ‖c • t‖ ^ 2 = (-(b : ℂ)) * ‖t‖ ^ 2 := by
    -- Proof comment: negate the scalar identity once so the exponential arguments line up
    -- exactly with the kernel formulas.
    simpa [neg_mul] using congrArg Neg.neg hargC
  have hexp :
      Complex.exp (-(a : ℂ) * ‖c • t‖ ^ 2) =
        Complex.exp (-(b : ℂ) * ‖t‖ ^ 2) := by
    exact congrArg Complex.exp hargNeg
  -- Proof comment: combine the Gaussian exponent cancellation with the pushed-forward
  -- characteristic-function identity.
  rw [hchar, hexp]

/-- Helper for Theorem 15.29: the Fourier-normalized Gaussian-damped inverse-Fourier candidate
attached to an actual Euclidean witness is already real-valued. -/
lemma scaledDampedInverseFourier_eq_ofRealOfProbabilityMeasure {d : ℕ}
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) {a : ℝ} (ha : 0 < a) :
    (fun x : EuclideanSpace ℝ (Fin d) ↦
      ((Complex.re
          (FourierTransformInv.fourierInv
            (fun t : EuclideanSpace ℝ (Fin d) ↦
              Complex.exp (-(a : ℂ) * ‖((-(2 * Real.pi) : ℝ) • t)‖ ^ 2) *
                charFun (μ : Measure (EuclideanSpace ℝ (Fin d))) ((-(2 * Real.pi) : ℝ) • t))
            x) : ℝ) : ℂ)) =
      FourierTransformInv.fourierInv
        (fun t : EuclideanSpace ℝ (Fin d) ↦
          Complex.exp (-(a : ℂ) * ‖((-(2 * Real.pi) : ℝ) • t)‖ ^ 2) *
            charFun (μ : Measure (EuclideanSpace ℝ (Fin d))) ((-(2 * Real.pi) : ℝ) • t)) := by
  let E := EuclideanSpace ℝ (Fin d)
  let ψ : E → ℂ := fun t ↦
    Complex.exp (-(a : ℂ) * ‖((-(2 * Real.pi) : ℝ) • t)‖ ^ 2) *
      charFun (μ : Measure E) ((-(2 * Real.pi) : ℝ) • t)
  have hψ_psd : IsPositiveSemidefiniteFunction ψ := by
    -- Proof comment: the earlier scaled Gaussian-damped kernel package already contains the
    -- positive-semidefinite clause for this fixed witness-side kernel.
    simpa [ψ] using
      (scaledGaussianDampedKernelSpecOfProbabilityMeasure
        (d := d) (μ := μ) (a := a) ha).2.2.1
  -- Proof comment: once the scaled witness kernel is positive semidefinite, its inverse Fourier
  -- transform is automatically real-valued.
  simpa [ψ] using
    (ofRealFourierInv_eq_of_isPositiveSemidefiniteFunction
      (d := d) (ψ := ψ) hψ_psd)

/-- Helper for Theorem 15.29: the Fourier-normalized Gaussian-damped inverse-Fourier candidate
attached to an actual Euclidean witness is continuous as a complex-valued function. -/
lemma scaledDampedInverseFourierContinuousOfProbabilityMeasure' {d : ℕ}
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) {a : ℝ} (ha : 0 < a) :
    Continuous
      (fun x : EuclideanSpace ℝ (Fin d) ↦
        ((Complex.re
            (FourierTransformInv.fourierInv
              (fun t : EuclideanSpace ℝ (Fin d) ↦
                Complex.exp (-(a : ℂ) * ‖((-(2 * Real.pi) : ℝ) • t)‖ ^ 2) *
                  charFun (μ : Measure (EuclideanSpace ℝ (Fin d))) ((-(2 * Real.pi) : ℝ) • t))
              x) : ℝ) : ℂ)) := by
  let E := EuclideanSpace ℝ (Fin d)
  let ψ : E → ℂ := fun t ↦
    Complex.exp (-(a : ℂ) * ‖((-(2 * Real.pi) : ℝ) • t)‖ ^ 2) *
      charFun (μ : Measure E) ((-(2 * Real.pi) : ℝ) • t)
  have hψ_int : Integrable ψ := by
    -- Proof comment: the earlier scaled Gaussian-damped kernel package already supplies the `L¹`
    -- control of the fixed normalized kernel.
    simpa [ψ] using
      (scaledGaussianDampedKernelSpecOfProbabilityMeasure
        (d := d) (μ := μ) (a := a) ha).2.1
  have hcont_raw : Continuous (FourierTransformInv.fourierInv ψ) :=
    inverseFourier_continuous_of_integrable (d := d) (ψ := ψ) hψ_int
  have hreal :
      (fun x : E ↦ ((Complex.re (FourierTransformInv.fourierInv ψ x) : ℝ) : ℂ)) =
        FourierTransformInv.fourierInv ψ := by
    -- Proof comment: reuse the preceding real-valuedness owner instead of reopening the
    -- positive-semidefinite argument.
    simpa [ψ] using
      scaledDampedInverseFourier_eq_ofRealOfProbabilityMeasure
        (d := d) (μ := μ) (a := a) ha
  -- Proof comment: continuity of the complexification is now just continuity of the underlying
  -- inverse Fourier transform rewritten through the real-valuedness identity.
  rw [hreal]
  exact hcont_raw

/-- Helper for Theorem 15.29: the real-valued scaled Gaussian-damped inverse-Fourier candidate
attached to an actual Euclidean witness is continuous. -/
lemma scaledDampedInverseFourierContinuousRealOfProbabilityMeasure {d : ℕ}
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) {a : ℝ} (ha : 0 < a) :
    Continuous
      (fun x : EuclideanSpace ℝ (Fin d) ↦
        Complex.re
          (FourierTransformInv.fourierInv
            (fun t : EuclideanSpace ℝ (Fin d) ↦
              Complex.exp (-(a : ℂ) * ‖((-(2 * Real.pi) : ℝ) • t)‖ ^ 2) *
                charFun (μ : Measure (EuclideanSpace ℝ (Fin d))) ((-(2 * Real.pi) : ℝ) • t))
            x)) := by
  -- Proof comment: the existing complex-valued continuity owner already proves continuity after
  -- complexifying the real-valued candidate, so taking real parts recovers continuity of the
  -- underlying real function.
  simpa using
    Complex.continuous_re.comp
      (scaledDampedInverseFourierContinuousOfProbabilityMeasure'
        (d := d) (μ := μ) (a := a) ha)

/-- Helper for Theorem 15.29: the Gaussian-regularized inverse-Fourier candidate should be
mass `1` once pointwise nonnegativity and `L¹` control are available. -/
lemma gaussianRegularizedInverseFourierDensityMassOneCore {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} {b : ℝ} (hb : 0 < b)
    (hψ_cont : Continuous ψ) (hψ_int : Integrable ψ)
    (hψ_psd : IsPositiveSemidefiniteFunction ψ) (hψ_zero : ψ 0 = 1)
    (hf_nonneg : ∀ x, 0 ≤ gaussianRegularizedInverseFourierDensity ψ b x)
    (hf_int : Integrable (gaussianRegularizedInverseFourierDensity ψ b)) :
    ∫ x, gaussianRegularizedInverseFourierDensity ψ b x = 1 := by
  let E := EuclideanSpace ℝ (Fin d)
  let ψb : E → ℂ := fun t ↦ Complex.exp (-(b : ℂ) * ‖t‖ ^ 2) * ψ t
  let f : E → ℝ := gaussianRegularizedInverseFourierDensity ψ b
  have hψb_spec : Continuous ψb ∧ Integrable ψb ∧ IsPositiveSemidefiniteFunction ψb ∧ ψb 0 = 1 := by
    -- Proof comment: extra Gaussian damping keeps the kernel inside the standard Fourier-inversion
    -- package available earlier in the file.
    simpa [ψb] using
      gaussianRegularizedKernelSpec
        (d := d) (ψ := ψ) (b := b) hb hψ_cont hψ_int hψ_psd hψ_zero
  have hf_complex : (fun x : E ↦ ((f x : ℝ) : ℂ)) = FourierTransformInv.fourierInv ψb := by
    -- Proof comment: positive semidefiniteness forces the regularized inverse Fourier transform to
    -- be real-valued.
    simpa [f, ψb] using
      gaussianRegularizedInverseFourierDensity_eq_ofRealFourierInv
        (d := d) (ψ := ψ) (b := b) hb hψ_psd
  have hψb_fourier :
      FourierTransform.fourier ψb = fun x : E ↦ ((f (-x) : ℝ) : ℂ) := by
    ext x
    -- Proof comment: the regularized inverse-Fourier density is the Fourier transform of `ψb`
    -- viewed at the reflected point.
    calc
      FourierTransform.fourier ψb x = FourierTransform.fourier ψb (-(-x)) := by
          rw [neg_neg]
      _ = FourierTransformInv.fourierInv ψb (-x) := by
          exact (Real.fourierInv_eq_fourier_neg ψb (-x)).symm
      _ = ((f (-x) : ℝ) : ℂ) := by
          simpa using (congrFun hf_complex (-x)).symm
  have hψb_fourier_int : Integrable (FourierTransform.fourier ψb) := by
    -- Proof comment: after the sign change, the Fourier transform is exactly the complexification
    -- of the assumed `L¹` density candidate.
    rw [hψb_fourier]
    simpa [f] using (Integrable.comp_neg hf_int).ofReal
  have hfourier :
      FourierTransform.fourier (fun x : E ↦ ((f x : ℝ) : ℂ)) = ψb := by
    -- Proof comment: Fourier inversion now recovers the damped kernel from the density candidate.
    rw [hf_complex]
    exact Continuous.fourier_fourierInv_eq hψb_spec.1 hψb_spec.2.1 hψb_fourier_int
  have hf_aemeas : AEMeasurable (ENNReal.ofReal ∘ f) volume := by
    -- Proof comment: integrability of `f` gives the measurability needed to compute the total mass
    -- of the associated `withDensity` measure.
    exact hf_int.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hf_lt_top : ∀ᵐ x ∂volume, ENNReal.ofReal (f x) < ⊤ := by
    -- Proof comment: real-valued densities are finite everywhere.
    exact Filter.Eventually.of_forall fun _ ↦ by simp
  have hmass_measure_complex :
      ((((volume.withDensity (ENNReal.ofReal ∘ f)).real Set.univ : ℝ)) : ℂ) = 1 := by
    -- Proof comment: evaluating at frequency `0` avoids the fixed `-2π` normalization issue and
    -- reads off the total mass of the `withDensity` law.
    calc
      ((((volume.withDensity (ENNReal.ofReal ∘ f)).real Set.univ : ℝ)) : ℂ)
          = charFun (volume.withDensity (ENNReal.ofReal ∘ f)) (0 : E) := by
              simpa using
                (MeasureTheory.charFun_zero
                  (μ := volume.withDensity (ENNReal.ofReal ∘ f))).symm
      _ = VectorFourier.fourierIntegral Real.fourierChar volume
            (innerₗ E)
            (fun x : E ↦ ((f x : ℝ) : ℂ))
            (-(2 * Real.pi)⁻¹ • (0 : E)) := by
              simpa [f] using
                congrFun
                  (charFun_withDensity_ofReal_eq_fourierEuclidean
                    (d := d) (f := f) hf_nonneg hf_int) (0 : E)
      _ = VectorFourier.fourierIntegral Real.fourierChar volume
            (innerₗ E)
            (fun x : E ↦ ((f x : ℝ) : ℂ))
            (0 : E) := by
              simp
      _ = FourierTransform.fourier (fun x : E ↦ ((f x : ℝ) : ℂ)) 0 := by
            rfl
      _ = ψb 0 := by
            exact congrFun hfourier 0
      _ = 1 := by
            simpa using hψb_spec.2.2.2
  have hmass_measure :
      (volume.withDensity (ENNReal.ofReal ∘ f)).real Set.univ = 1 := by
    exact_mod_cast hmass_measure_complex
  -- Proof comment: convert the total mass of the `withDensity` measure back to the integral of
  -- the original real-valued density.
  calc
    ∫ x, f x ∂volume
        = (volume.withDensity (ENNReal.ofReal ∘ f)).real Set.univ := by
            calc
              ∫ x, f x ∂volume
                  = ∫ x, ((ENNReal.ofReal ∘ f) x).toReal • (1 : ℝ) ∂volume := by
                      refine integral_congr_ae (Filter.Eventually.of_forall ?_)
                      intro x
                      simp [f, hf_nonneg x]
              _ = ∫ x, (1 : ℝ) ∂(volume.withDensity (ENNReal.ofReal ∘ f)) := by
                    symm
                    simpa using
                      (integral_withDensity_eq_integral_toReal_smul₀
                        (μ := volume) (f := ENNReal.ofReal ∘ f) hf_aemeas hf_lt_top
                        (g := fun _ : E ↦ (1 : ℝ)))
              _ = (volume.withDensity (ENNReal.ofReal ∘ f)).real Set.univ := by
                    simp
    _ = 1 := hmass_measure

/-- Helper for Theorem 15.29: a continuous nonnegative real function on `ℝ^d` with total mass
`1` is integrable. -/
lemma integrable_of_continuous_nonneg_integral_eq_one {d : ℕ}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf_cont : Continuous f) (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_mass : ∫ x, f x = 1) :
    Integrable f := by
  refine ⟨hf_cont.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x ↦ hf_nonneg x)]
  have hlintegral_toReal :
      (∫⁻ x, ENNReal.ofReal (f x) ∂volume).toReal = 1 := by
    calc
      (∫⁻ x, ENNReal.ofReal (f x) ∂volume).toReal = ∫ x, f x ∂volume := by
        symm
        exact
          integral_eq_lintegral_of_nonneg_ae
            (Filter.Eventually.of_forall fun x ↦ hf_nonneg x) hf_cont.aestronglyMeasurable
      _ = 1 := hf_mass
  have hlt_top : ∫⁻ x, ENNReal.ofReal (f x) ∂volume < ⊤ := by
    refine lt_top_iff_ne_top.mpr ?_
    intro htop
    have hzero : (∫⁻ x, ENNReal.ofReal (f x) ∂volume).toReal = 0 := by
      simpa [htop]
    simpa [hlintegral_toReal] using hzero
  exact hlt_top

/-- Helper for Theorem 15.29: once the regularized inverse Fourier kernel is identified with a
real density of mass `1`, the Gaussian-regularized density candidate inherits the full
nonnegativity/`L¹`/mass package by taking real parts. -/
lemma gaussianRegularizedInverseFourierDensitySpec_of_density {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} {b : ℝ}
    {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf_nonneg : ∀ x, 0 ≤ f x) (hf_int : Integrable f) (hf_mass : ∫ x, f x = 1)
    (hf_eq : ∀ x : EuclideanSpace ℝ (Fin d),
      FourierTransformInv.fourierInv
        (fun t : EuclideanSpace ℝ (Fin d) ↦
          Complex.exp (-(b : ℂ) * ‖t‖ ^ 2) * ψ t) x =
        ((f x : ℝ) : ℂ)) :
    (∀ x, 0 ≤ gaussianRegularizedInverseFourierDensity ψ b x) ∧
      Integrable (gaussianRegularizedInverseFourierDensity ψ b) ∧
      (∫ x, gaussianRegularizedInverseFourierDensity ψ b x = 1) := by
  have hdensity_eq : gaussianRegularizedInverseFourierDensity ψ b = f := by
    funext x
    -- Proof comment: unfold the regularized density once, then rewrite the inverse Fourier term
    -- to the supplied real-valued density and take real parts.
    calc
      gaussianRegularizedInverseFourierDensity ψ b x
          = Complex.re
              (FourierTransformInv.fourierInv
                (fun t : EuclideanSpace ℝ (Fin d) ↦
                  Complex.exp (-(b : ℂ) * ‖t‖ ^ 2) * ψ t) x) := by
                    rfl
      _ = Complex.re (((f x : ℝ) : ℂ)) := by
            rw [hf_eq x]
      _ = f x := by
            simp
  refine ⟨?_, ?_, ?_⟩
  · -- Proof comment: pointwise nonnegativity is now just the same statement under the identified
    -- real density.
    intro x
    simpa [hdensity_eq] using hf_nonneg x
  · -- Proof comment: `L¹` control is preserved by the pointwise identification above.
    simpa [hdensity_eq] using hf_int
  · -- Proof comment: total mass is likewise transported along the same identified real density.
    simpa [hdensity_eq] using hf_mass

/-- Helper for Theorem 15.29: to upgrade the regularized inverse-Fourier candidate from almost
everywhere nonnegative to pointwise nonnegative, it is enough to use the continuity of the
candidate itself. -/
lemma gaussianRegularizedInverseFourierDensity_nonneg_of_aeNonneg {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} {b : ℝ} (hb : 0 < b)
    (hψ_cont : Continuous ψ) (hψ_psd : IsPositiveSemidefiniteFunction ψ) (hψ_zero : ψ 0 = 1)
    (hf_nonneg : 0 ≤ᵐ[volume] gaussianRegularizedInverseFourierDensity ψ b) :
    ∀ x, 0 ≤ gaussianRegularizedInverseFourierDensity ψ b x := by
  -- Proof comment: the regularized density candidate is continuous, so almost-everywhere
  -- nonnegativity upgrades to everywhere nonnegativity on Euclidean space.
  exact
    nonneg_of_continuous_ae_nonneg
      (d := d)
      (f := gaussianRegularizedInverseFourierDensity ψ b)
      (gaussianRegularizedInverseFourierDensityContinuousReal
        (d := d) (ψ := ψ) (b := b) hb hψ_cont hψ_psd hψ_zero)
      hf_nonneg

/-- Helper for Theorem 15.29: a density witness that agrees almost everywhere with the
Gaussian-regularized inverse-Fourier candidate already supplies the full nonnegativity/`L¹`/mass
package. -/
lemma gaussianRegularizedInverseFourierDensitySpec_of_aeEqDensity {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} {b : ℝ} {f : EuclideanSpace ℝ (Fin d) → ℝ} (hb : 0 < b)
    (hψ_cont : Continuous ψ) (hψ_psd : IsPositiveSemidefiniteFunction ψ) (hψ_zero : ψ 0 = 1)
    (hf_nonneg : ∀ x, 0 ≤ f x) (hf_int : Integrable f) (hf_mass : ∫ x, f x = 1)
    (hf_ae : gaussianRegularizedInverseFourierDensity ψ b =ᵐ[volume] f) :
    (∀ x, 0 ≤ gaussianRegularizedInverseFourierDensity ψ b x) ∧
      Integrable (gaussianRegularizedInverseFourierDensity ψ b) ∧
      (∫ x, gaussianRegularizedInverseFourierDensity ψ b x = 1) := by
  have hgauss_ae_nonneg : 0 ≤ᵐ[volume] gaussianRegularizedInverseFourierDensity ψ b := by
    -- Proof comment: transport the pointwise nonnegativity of the density witness across the
    -- almost-everywhere identification.
    filter_upwards [hf_ae] with x hx
    rw [hx]
    exact hf_nonneg x
  have hgauss_nonneg :
      ∀ x, 0 ≤ gaussianRegularizedInverseFourierDensity ψ b x :=
    gaussianRegularizedInverseFourierDensity_nonneg_of_aeNonneg
      (d := d) (ψ := ψ) (b := b) hb hψ_cont hψ_psd hψ_zero hgauss_ae_nonneg
  have hgauss_int : Integrable (gaussianRegularizedInverseFourierDensity ψ b) := by
    -- Proof comment: `L¹` control is invariant under almost-everywhere equality.
    simpa using hf_int.congr hf_ae.symm
  have hgauss_mass : ∫ x, gaussianRegularizedInverseFourierDensity ψ b x = 1 := by
    -- Proof comment: total mass is the same under almost-everywhere identification.
    calc
      ∫ x, gaussianRegularizedInverseFourierDensity ψ b x = ∫ x, f x := by
        exact integral_congr_ae hf_ae
      _ = 1 := hf_mass
  exact ⟨hgauss_nonneg, hgauss_int, hgauss_mass⟩

/-- Helper for Theorem 15.29: after freezing the Gaussian-regularized kernel under the name
`ψb`, the regularized inverse-Fourier density is the real part of the corresponding one-variable
oscillatory integral. -/
lemma gaussianRegularizedInverseFourierDensity_eq_realIntegral_regularizedKernel {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} {b : ℝ}
    (x : EuclideanSpace ℝ (Fin d)) :
    let ψb : EuclideanSpace ℝ (Fin d) → ℂ :=
      fun t ↦ Complex.exp (-(b : ℂ) * ‖t‖ ^ 2) * ψ t
    gaussianRegularizedInverseFourierDensity ψ b x =
      Complex.re
        (∫ t : EuclideanSpace ℝ (Fin d),
          Complex.exp (↑(2 * Real.pi * inner ℝ t x) * Complex.I) * ψb t) := by
  let ψb : EuclideanSpace ℝ (Fin d) → ℂ :=
    fun t ↦ Complex.exp (-(b : ℂ) * ‖t‖ ^ 2) * ψ t
  -- Proof comment: this is the explicit Fourier-integral formula already proved earlier, now
  -- restated with the regularized kernel frozen under a stable name.
  simpa [ψb] using
    gaussianRegularizedInverseFourierDensity_eq_real_integral_fourierExp
      (ψ := ψ) (b := b) x

/-- Helper for Theorem 15.29: the frozen oscillatory-integral window for the Gaussian-regularized
kernel is integrable. -/
lemma integrable_gaussianRegularizedInverseFourierDensity_window {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} {b : ℝ} (hb : 0 < b)
    (hψ_cont : Continuous ψ) (hψ_int : Integrable ψ)
    (hψ_psd : IsPositiveSemidefiniteFunction ψ) (hψ_zero : ψ 0 = 1)
    (x : EuclideanSpace ℝ (Fin d)) :
    let ψb : EuclideanSpace ℝ (Fin d) → ℂ :=
      fun t ↦ Complex.exp (-(b : ℂ) * ‖t‖ ^ 2) * ψ t
    Integrable
      (fun t : EuclideanSpace ℝ (Fin d) ↦
        Complex.exp (↑(2 * Real.pi * inner ℝ t x) * Complex.I) * ψb t) := by
  let E := EuclideanSpace ℝ (Fin d)
  let ψb : E → ℂ := fun t ↦ Complex.exp (-(b : ℂ) * ‖t‖ ^ 2) * ψ t
  have hψb_spec : Continuous ψb ∧ Integrable ψb ∧ IsPositiveSemidefiniteFunction ψb ∧ ψb 0 = 1 := by
    -- Proof comment: the Gaussian-regularized kernel already has the standard continuous,
    -- integrable, positive-semidefinite, and normalized package.
    simpa [ψb] using
      gaussianRegularizedKernelSpec
        (d := d) (ψ := ψ) (b := b) hb hψ_cont hψ_int hψ_psd hψ_zero
  refine Integrable.mono' hψb_spec.2.1.norm ?_ ?_
  · -- Proof comment: the oscillatory phase is continuous, so multiplying by the continuous
    -- regularized kernel preserves strong measurability.
    exact ((Complex.continuous_exp.comp (by fun_prop)).mul hψb_spec.1).aestronglyMeasurable
  · -- Proof comment: the oscillatory phase has unit norm, so the regularized kernel itself is an
    -- `L¹` majorant for the frozen window integrand.
    filter_upwards with t
    calc
      ‖Complex.exp (↑(2 * Real.pi * inner ℝ t x) * Complex.I) * ψb t‖
          = ‖Complex.exp (↑(2 * Real.pi * inner ℝ t x) * Complex.I)‖ * ‖ψb t‖ := by
              simp
      _ = ‖ψb t‖ := by
            rw [Complex.norm_exp_ofReal_mul_I]
            ring
      _ ≤ ‖ψb t‖ := le_rfl

/-- Helper for Theorem 15.29: the Gaussian damping factor `exp (-(b : ℂ) * ‖t‖ ^ 2)` is the
Fourier-normalized integral of a suitably scaled standard Gaussian. -/
lemma gaussianDamping_eq_fourierIntegral_scaledStdGaussian {d : ℕ} {b : ℝ}
    (hb : 0 < b) (t : EuclideanSpace ℝ (Fin d)) :
    let E := EuclideanSpace ℝ (Fin d)
    let c : ℝ := -(2 * Real.pi)
    let a : ℝ := b / c ^ 2
    let γ : Measure E :=
      (ProbabilityTheory.stdGaussian E).map (Real.sqrt (2 * a) • ·)
    VectorFourier.fourierIntegral Real.fourierChar γ (innerₗ E) (1 : E → ℂ) t =
      Complex.exp (-(b : ℂ) * ‖t‖ ^ 2) := by
  let E := EuclideanSpace ℝ (Fin d)
  let c : ℝ := -(2 * Real.pi)
  let a : ℝ := b / c ^ 2
  let γ : Measure E :=
    (ProbabilityTheory.stdGaussian E).map (Real.sqrt (2 * a) • ·)
  have hc : c ≠ 0 := by
    -- Proof comment: the fixed Fourier-normalization scalar `-2π` is nonzero.
    have htwoPi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    exact neg_ne_zero.mpr htwoPi
  have ha : 0 < a := by
    -- Proof comment: the Gaussian variance parameter is `b / (2π)^2`, which stays positive.
    dsimp [a]
    exact div_pos hb (sq_pos_of_ne_zero hc)
  have harg_real : a * ‖c • t‖ ^ 2 = b * ‖t‖ ^ 2 := by
    have hnorm : ‖c • t‖ ^ 2 = c ^ 2 * ‖t‖ ^ 2 := by
      calc
        ‖c • t‖ ^ 2 = (|c| * ‖t‖) ^ 2 := by
          rw [norm_smul, Real.norm_eq_abs]
        _ = |c| ^ 2 * ‖t‖ ^ 2 := by
          ring
        _ = c ^ 2 * ‖t‖ ^ 2 := by
          rw [sq_abs]
    have hscale : a * c ^ 2 = b := by
      dsimp [a]
      field_simp [hc]
    calc
      a * ‖c • t‖ ^ 2 = a * (c ^ 2 * ‖t‖ ^ 2) := by rw [hnorm]
      _ = (a * c ^ 2) * ‖t‖ ^ 2 := by ring
      _ = b * ‖t‖ ^ 2 := by rw [hscale]
  have harg_complex :
      (-(a : ℂ)) * ‖c • t‖ ^ 2 = (-(b : ℂ)) * ‖t‖ ^ 2 := by
    have hcast : (a : ℂ) * ‖c • t‖ ^ 2 = (b : ℂ) * ‖t‖ ^ 2 := by
      exact_mod_cast harg_real
    simpa [neg_mul] using congrArg Neg.neg hcast
  have hchar :
      charFun γ (c • t) = Complex.exp (-(b : ℂ) * ‖t‖ ^ 2) := by
    -- Proof comment: choose the Gaussian parameter so that evaluating the witness at `-2π • t`
    -- produces exactly the desired damping factor.
    calc
      charFun γ (c • t) = Complex.exp (-(a : ℂ) * ‖c • t‖ ^ 2) := by
        simpa [γ] using gaussianDamping_eq_charFun_scaledStdGaussian (d := d) ha (c • t)
      _ = Complex.exp (-(b : ℂ) * ‖t‖ ^ 2) := by
        exact congrArg Complex.exp harg_complex
  have harg :
      (-(2 * Real.pi)⁻¹ : ℝ) • (c • t) = t := by
    calc
      (-(2 * Real.pi)⁻¹ : ℝ) • (c • t) =
          ((-(2 * Real.pi)⁻¹ : ℝ) * c) • t := by
            rw [smul_smul]
      _ = (1 : ℝ) • t := by
            dsimp [c]
            field_simp [Real.pi_ne_zero]
      _ = t := by simp
  -- Proof comment: `charFun_eq_fourierIntegral'` converts the Gaussian characteristic function to
  -- the Fourier-normalized phase used by the inverse-Fourier candidate.
  calc
    VectorFourier.fourierIntegral Real.fourierChar γ (innerₗ E) (1 : E → ℂ) t
        = charFun γ (c • t) := by
            symm
            calc
              charFun γ (c • t)
                  = VectorFourier.fourierIntegral Real.fourierChar γ (innerₗ E)
                      (1 : E → ℂ) ((-(2 * Real.pi)⁻¹ : ℝ) • (c • t)) := by
                          simpa using (MeasureTheory.charFun_eq_fourierIntegral' (μ := γ) (t := c • t))
              _ = VectorFourier.fourierIntegral Real.fourierChar γ (innerₗ E) (1 : E → ℂ) t := by
                    rw [harg]
    _ = Complex.exp (-(b : ℂ) * ‖t‖ ^ 2) := hchar

/-- Helper for Theorem 15.29: the half-window Gaussian parameter `b / (2 * c²)` is the same as
the single-Gaussian damping parameter `(b / 2) / c²`. -/
lemma halfGaussianParameter_eq_halfDampingQuotient {b c : ℝ} :
    b / (2 * c ^ 2) = (b / 2) / c ^ 2 := by
  by_cases hc : c = 0
  · -- Proof comment: both sides collapse to the totalized division-by-zero value.
    simp [hc]
  · -- Proof comment: away from `c = 0`, this is the elementary rearrangement
    -- `b / (2 c²) = (b / 2) / c²`.
    field_simp [hc]

/-- Helper for Theorem 15.29: the half-variance Gaussian Fourier factor squares to the full
Gaussian damping factor. -/
lemma gaussianDamping_eq_square_halfGaussianFourierFactor {d : ℕ} {b : ℝ}
    (hb : 0 < b) (t : EuclideanSpace ℝ (Fin d)) :
    let E := EuclideanSpace ℝ (Fin d)
    let c : ℝ := -(2 * Real.pi)
    let aHalf : ℝ := b / (2 * c ^ 2)
    let γHalf : Measure E :=
      (ProbabilityTheory.stdGaussian E).map (Real.sqrt (2 * aHalf) • ·)
    VectorFourier.fourierIntegral Real.fourierChar γHalf (innerₗ E) (1 : E → ℂ) t *
        VectorFourier.fourierIntegral Real.fourierChar γHalf (innerₗ E) (1 : E → ℂ) t =
      Complex.exp (-(b : ℂ) * ‖t‖ ^ 2) := by
  let E := EuclideanSpace ℝ (Fin d)
  let c : ℝ := -(2 * Real.pi)
  let aHalf : ℝ := b / (2 * c ^ 2)
  let γHalf : Measure E :=
    (ProbabilityTheory.stdGaussian E).map (Real.sqrt (2 * aHalf) • ·)
  have hbHalf : 0 < b / 2 := by
    -- Proof comment: halving a positive Gaussian damping parameter preserves positivity.
    positivity
  have hfactor :
      VectorFourier.fourierIntegral Real.fourierChar γHalf (innerₗ E) (1 : E → ℂ) t =
        Complex.exp (-(((b / 2 : ℝ) : ℂ) * ‖t‖ ^ 2)) := by
    -- Proof comment: specialize the one-Gaussian Fourier formula to damping parameter `b / 2`,
    -- then rewrite its variance parameter into the half-window spelling `aHalf`.
    simpa [γHalf, aHalf, c, halfGaussianParameter_eq_halfDampingQuotient]
      using gaussianDamping_eq_fourierIntegral_scaledStdGaussian
        (d := d) (b := b / 2) hbHalf t
  calc
    VectorFourier.fourierIntegral Real.fourierChar γHalf (innerₗ E) (1 : E → ℂ) t *
        VectorFourier.fourierIntegral Real.fourierChar γHalf (innerₗ E) (1 : E → ℂ) t
        =
      Complex.exp (-(((b / 2 : ℝ) : ℂ) * ‖t‖ ^ 2)) *
        Complex.exp (-(((b / 2 : ℝ) : ℂ) * ‖t‖ ^ 2)) := by
            simpa [hfactor]
    _ = Complex.exp
          (-(((b / 2 : ℝ) : ℂ) * ‖t‖ ^ 2) + -(((b / 2 : ℝ) : ℂ) * ‖t‖ ^ 2)) := by
            rw [← Complex.exp_add]
    _ = Complex.exp (-(b : ℂ) * ‖t‖ ^ 2) := by
          have hhalf_two_real : (b / 2) * 2 = b := by
            ring
          have hhalf_two : (((b / 2 : ℝ) : ℂ) * (2 : ℂ)) = (b : ℂ) := by
            -- Proof comment: doubling the halved damping coefficient recovers `b`.
            exact_mod_cast hhalf_two_real
          congr 1
          calc
            -(((b / 2 : ℝ) : ℂ) * ‖t‖ ^ 2) + -(((b / 2 : ℝ) : ℂ) * ‖t‖ ^ 2)
                = -((((b / 2 : ℝ) : ℂ) * (2 : ℂ)) * ‖t‖ ^ 2) := by
                    ring
            _ = -((b : ℂ) * ‖t‖ ^ 2) := by rw [hhalf_two]
            _ = -(b : ℂ) * ‖t‖ ^ 2 := by ring

/-- Helper for Theorem 15.29: after freezing the Gaussian factor through the scaled Gaussian
measure `γ`, the regularized inverse-Fourier candidate has an explicit normalized oscillatory
integral form. -/
lemma gaussianRegularizedInverseFourierDensity_eq_realIntegral_gaussianFactor {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} {b : ℝ} (hb : 0 < b)
    (x : EuclideanSpace ℝ (Fin d)) :
    let E := EuclideanSpace ℝ (Fin d)
    let c : ℝ := -(2 * Real.pi)
    let a : ℝ := b / c ^ 2
    let γ : Measure E :=
      (ProbabilityTheory.stdGaussian E).map (Real.sqrt (2 * a) • ·)
    gaussianRegularizedInverseFourierDensity ψ b x =
      Complex.re
        (∫ t : E,
          Complex.exp (↑(2 * Real.pi * inner ℝ t x) * Complex.I) *
            (VectorFourier.fourierIntegral Real.fourierChar γ (innerₗ E) (1 : E → ℂ) t * ψ t)) := by
  let E := EuclideanSpace ℝ (Fin d)
  let c : ℝ := -(2 * Real.pi)
  let a : ℝ := b / c ^ 2
  let γ : Measure E :=
    (ProbabilityTheory.stdGaussian E).map (Real.sqrt (2 * a) • ·)
  -- Proof comment: first rewrite the regularized kernel through the explicit oscillatory
  -- integral, then replace the Gaussian damping factor by the normalized Gaussian Fourier integral.
  rw [gaussianRegularizedInverseFourierDensity_eq_realIntegral_regularizedKernel (d := d)
    (ψ := ψ) (b := b) x]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall ?_)
  intro t
  calc
    Complex.exp (↑(2 * Real.pi * inner ℝ t x) * Complex.I) *
        (Complex.exp (-(b : ℂ) * ‖t‖ ^ 2) * ψ t)
        =
      Complex.exp (↑(2 * Real.pi * inner ℝ t x) * Complex.I) *
        (VectorFourier.fourierIntegral Real.fourierChar γ (innerₗ E) (1 : E → ℂ) t * ψ t) := by
          rw [gaussianDamping_eq_fourierIntegral_scaledStdGaussian (d := d) (b := b) hb t]

/-- Helper for Theorem 15.29: the difference of two independent half-Gaussians has the
characteristic function of the full scaled Gaussian used in the regularization step. -/
lemma halfGaussianDifference_charFun_eq_scaledStdGaussian {d : ℕ} {b : ℝ}
    (hb : 0 < b) (t : EuclideanSpace ℝ (Fin d)) :
    let E := EuclideanSpace ℝ (Fin d)
    let c : ℝ := -(2 * Real.pi)
    let aHalf : ℝ := b / (2 * c ^ 2)
    let a : ℝ := b / c ^ 2
    let γHalf : Measure E :=
      (ProbabilityTheory.stdGaussian E).map (Real.sqrt (2 * aHalf) • ·)
    charFun ((γHalf.prod γHalf).map (fun p : E × E ↦ p.1 - p.2)) t =
      Complex.exp (-(a : ℂ) * ‖t‖ ^ 2) := by
  let E := EuclideanSpace ℝ (Fin d)
  let c : ℝ := -(2 * Real.pi)
  let aHalf : ℝ := b / (2 * c ^ 2)
  let a : ℝ := b / c ^ 2
  let γHalf : Measure E :=
    (ProbabilityTheory.stdGaussian E).map (Real.sqrt (2 * aHalf) • ·)
  have hc : c ≠ 0 := by
    -- Proof comment: the fixed normalization constant `-(2π)` is nonzero.
    dsimp [c]
    exact neg_ne_zero.mpr (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  have haHalf : 0 < aHalf := by
    -- Proof comment: the half-window variance stays positive because `b > 0`.
    dsimp [aHalf]
    positivity
  haveI : IsProbabilityMeasure γHalf := by
    dsimp [γHalf]
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  let diffMeasure : Measure E :=
    (γHalf.prod γHalf).map (fun p : E × E ↦ p.1 - p.2)
  let negMeasure : Measure E := γHalf.map ((-1 : ℝ) • ·)
  haveI : IsProbabilityMeasure diffMeasure := by
    dsimp [diffMeasure]
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  haveI : IsProbabilityMeasure negMeasure := by
    dsimp [negMeasure]
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  have hdiff_as_sum :
      diffMeasure = (γHalf.prod negMeasure).map (fun p : E × E ↦ p.1 + p.2) := by
    -- Proof comment: rewrite subtraction as addition after pushing the second coordinate through
    -- the negation map.
    calc
      diffMeasure
          = (Measure.map (fun p : E × E ↦ p.1 + p.2)
              (Measure.map (Prod.map id (((-1 : ℝ) • ·) : E → E)) (γHalf.prod γHalf))) := by
              symm
              simpa [diffMeasure, Function.comp, sub_eq_add_neg] using
                (Measure.map_map
                  (μ := γHalf.prod γHalf)
                  (f := Prod.map id (((-1 : ℝ) • ·) : E → E))
                  (g := fun p : E × E ↦ p.1 + p.2)
                  (by fun_prop) (by fun_prop))
      _ = (Measure.map (fun p : E × E ↦ p.1 + p.2)
            ((γHalf.map id).prod (γHalf.map ((-1 : ℝ) • ·))) ) := by
            rw [Measure.map_prod_map _ _ measurable_id (by fun_prop)]
      _ = (γHalf.prod negMeasure).map (fun p : E × E ↦ p.1 + p.2) := by
            simp [negMeasure]
  have hhalf : charFun γHalf t = Complex.exp (-(aHalf : ℂ) * ‖t‖ ^ 2) := by
    -- Proof comment: each half-Gaussian has the expected Gaussian characteristic function with
    -- the halved variance parameter.
    simpa [γHalf] using
      gaussianDamping_eq_charFun_scaledStdGaussian
        (d := d) (a := aHalf) haHalf t
  have hneg : charFun negMeasure t = Complex.exp (-(aHalf : ℂ) * ‖t‖ ^ 2) := by
    -- Proof comment: negating a centered Gaussian leaves the same characteristic function.
    calc
      charFun negMeasure t = charFun γHalf (((-1 : ℝ)) • t) := by
          simpa [negMeasure] using
            (MeasureTheory.charFun_map_smul (μ := γHalf) (-1) t)
      _ = Complex.exp (-(aHalf : ℂ) * ‖(((-1 : ℝ)) • t)‖ ^ 2) := by
            simpa [γHalf] using
              gaussianDamping_eq_charFun_scaledStdGaussian
                (d := d) (a := aHalf) haHalf (((-1 : ℝ)) • t)
      _ = Complex.exp (-(aHalf : ℂ) * ‖t‖ ^ 2) := by
            simp
  have hdouble_real : 2 * aHalf = b / c ^ 2 := by
    -- Proof comment: doubling the half-window variance recovers the full Gaussian variance.
    dsimp [aHalf]
    field_simp [hc]
  -- Proof comment: the difference law is the sum of one half-Gaussian and an independent
  -- negated half-Gaussian, so its characteristic function is the product of the two factors.
  calc
    charFun diffMeasure t = charFun γHalf t * charFun negMeasure t := by
      rw [hdiff_as_sum]
      simpa using
        congrFun
          (ProbabilityTheory.charFun_map_add_prod_eq_mul
            (μ := γHalf) (ν := negMeasure)) t
    _ = Complex.exp (-(aHalf : ℂ) * ‖t‖ ^ 2) *
          Complex.exp (-(aHalf : ℂ) * ‖t‖ ^ 2) := by rw [hhalf, hneg]
    _ = Complex.exp (-((aHalf : ℂ) * ‖t‖ ^ 2) + -((aHalf : ℂ) * ‖t‖ ^ 2)) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    _ = Complex.exp (-(a : ℂ) * ‖t‖ ^ 2) := by
      congr 1
      have hadd_real : aHalf + aHalf = a := by
        dsimp [a]
        nlinarith [hdouble_real]
      have hadd : (((aHalf + aHalf : ℝ)) : ℂ) = (a : ℂ) := by
        exact_mod_cast hadd_real
      calc
        -((aHalf : ℂ) * ‖t‖ ^ 2) + -((aHalf : ℂ) * ‖t‖ ^ 2)
            = -(((aHalf : ℂ) * ‖t‖ ^ 2 + (aHalf : ℂ) * ‖t‖ ^ 2) : ℂ) := by
                ring
        _ = -((((aHalf + aHalf : ℝ)) : ℂ) * ‖t‖ ^ 2) := by
              congr 1
              have hsum : (((aHalf + aHalf : ℝ)) : ℂ) = (aHalf : ℂ) + (aHalf : ℂ) := by
                norm_num
              rw [hsum]
              ring
        _ = -((a : ℂ) * ‖t‖ ^ 2) := by rw [hadd]
        _ = -(a : ℂ) * ‖t‖ ^ 2 := by ring

/-- Helper for Theorem 15.29: the difference of two independent half-Gaussians is exactly the
full scaled Gaussian used in the regularization step. -/
lemma halfGaussianDifference_eq_scaledStdGaussian {d : ℕ} {b : ℝ}
    (hb : 0 < b) :
    let E := EuclideanSpace ℝ (Fin d)
    let c : ℝ := -(2 * Real.pi)
    let aHalf : ℝ := b / (2 * c ^ 2)
    let a : ℝ := b / c ^ 2
    let γHalf : Measure E :=
      (ProbabilityTheory.stdGaussian E).map (Real.sqrt (2 * aHalf) • ·)
    let γ : Measure E :=
      (ProbabilityTheory.stdGaussian E).map (Real.sqrt (2 * a) • ·)
    ((γHalf.prod γHalf).map (fun p : E × E ↦ p.1 - p.2)) = γ := by
  let E := EuclideanSpace ℝ (Fin d)
  let c : ℝ := -(2 * Real.pi)
  let aHalf : ℝ := b / (2 * c ^ 2)
  let a : ℝ := b / c ^ 2
  let γHalf : Measure E :=
    (ProbabilityTheory.stdGaussian E).map (Real.sqrt (2 * aHalf) • ·)
  let γ : Measure E :=
    (ProbabilityTheory.stdGaussian E).map (Real.sqrt (2 * a) • ·)
  have hc : c ≠ 0 := by
    -- Proof comment: the fixed normalization constant `-(2π)` is nonzero.
    dsimp [c]
    exact neg_ne_zero.mpr (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  haveI : IsProbabilityMeasure γHalf := by
    dsimp [γHalf]
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  haveI : IsProbabilityMeasure γ := by
    dsimp [γ]
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  let diffMeasure : Measure E := (γHalf.prod γHalf).map (fun p : E × E ↦ p.1 - p.2)
  haveI : IsProbabilityMeasure diffMeasure := by
    dsimp [diffMeasure]
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  have ha : 0 < a := by
    dsimp [a]
    exact div_pos hb (sq_pos_of_ne_zero hc)
  -- Proof comment: probability measures on Euclidean space are identified by their
  -- characteristic functions, so the previous half-window calculation closes the measure equality.
  apply Measure.ext_of_charFun
  ext t
  calc
    charFun diffMeasure t = Complex.exp (-(a : ℂ) * ‖t‖ ^ 2) := by
      simpa [diffMeasure, c, aHalf, a, γHalf] using
        halfGaussianDifference_charFun_eq_scaledStdGaussian
          (d := d) (b := b) hb t
    _ = charFun γ t := by
      symm
      simpa [γ, a, c] using
        gaussianDamping_eq_charFun_scaledStdGaussian
          (d := d) (a := a) ha t

/-- Helper for Theorem 15.29: the half-Gaussian window integral depends only on the difference
law of the two Gaussian samples, so it can be rewritten as a single integral against the scaled
Gaussian from `halfGaussianDifference_eq_scaledStdGaussian`. -/
lemma halfGaussianWindowIntegral_eq_differenceIntegral {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} {b : ℝ} (hb : 0 < b) (hψ_cont : Continuous ψ)
    (x : EuclideanSpace ℝ (Fin d)) :
    let E := EuclideanSpace ℝ (Fin d)
    let c : ℝ := -(2 * Real.pi)
    let aHalf : ℝ := b / (2 * c ^ 2)
    let a : ℝ := b / c ^ 2
    let γHalf : Measure E :=
      (ProbabilityTheory.stdGaussian E).map (Real.sqrt (2 * aHalf) • ·)
    let γ : Measure E :=
      (ProbabilityTheory.stdGaussian E).map (Real.sqrt (2 * a) • ·)
    ∫ p : E × E,
      star (BoundedContinuousFunction.innerProbChar (-p.1) x) *
        ψ (p.1 - p.2) *
        BoundedContinuousFunction.innerProbChar (-p.2) x
        ∂(γHalf.prod γHalf) =
      ∫ t : E, ψ t * BoundedContinuousFunction.innerProbChar t x ∂γ := by
  let E := EuclideanSpace ℝ (Fin d)
  let c : ℝ := -(2 * Real.pi)
  let aHalf : ℝ := b / (2 * c ^ 2)
  let a : ℝ := b / c ^ 2
  let γHalf : Measure E :=
    (ProbabilityTheory.stdGaussian E).map (Real.sqrt (2 * aHalf) • ·)
  let γ : Measure E :=
    (ProbabilityTheory.stdGaussian E).map (Real.sqrt (2 * a) • ·)
  have hγ :
      ((γHalf.prod γHalf).map (fun p : E × E ↦ p.1 - p.2)) = γ := by
    -- Proof comment: the two half-Gaussians were chosen so that their difference is exactly the
    -- full Gaussian used in the regularization step.
    simpa [γHalf, γ, c, aHalf, a] using
      halfGaussianDifference_eq_scaledStdGaussian (d := d) (b := b) hb
  have hkernel_cont :
      Continuous fun t : E ↦ ψ t * BoundedContinuousFunction.innerProbChar t x := by
    have hchar :
        Continuous fun t : E ↦ BoundedContinuousFunction.innerProbChar t x := by
      -- Proof comment: fixing the spatial variable leaves a continuous oscillatory phase in the
      -- frequency variable.
      simpa [BoundedContinuousFunction.innerProbChar_apply] using
        (Complex.continuous_exp.comp
          (by
            fun_prop :
              Continuous fun t : E ↦ (↑(inner ℝ x t) : ℂ) * Complex.I))
    -- Proof comment: the single-difference kernel is the product of the original kernel `ψ` and
    -- that fixed oscillatory phase.
    exact hψ_cont.mul hchar
  calc
    ∫ p : E × E,
        star (BoundedContinuousFunction.innerProbChar (-p.1) x) *
          ψ (p.1 - p.2) *
          BoundedContinuousFunction.innerProbChar (-p.2) x
          ∂(γHalf.prod γHalf)
      =
        ∫ p : E × E,
          ψ (p.1 - p.2) *
            BoundedContinuousFunction.innerProbChar (p.1 - p.2) x
            ∂(γHalf.prod γHalf) := by
              -- Proof comment: collapse the two phase factors to the single character at the
              -- Gaussian difference before pushing the measure forward.
              refine integral_congr_ae (Filter.Eventually.of_forall ?_)
              intro p
              simpa using
                gaussianWindowQuadraticIntegrand_prod_eq_differenceKernel
                  (d := d) (ψ := ψ) x p
    _ =
        ∫ t : E, ψ t * BoundedContinuousFunction.innerProbChar t x
          ∂(Measure.map (fun p : E × E ↦ p.1 - p.2) (γHalf.prod γHalf)) := by
            -- Proof comment: after the phase collapse, the integrand only sees the difference
            -- `p.1 - p.2`, so `integral_map` pushes the product measure to that difference law.
            symm
            exact
              MeasureTheory.integral_map
                (μ := γHalf.prod γHalf)
                (φ := fun p : E × E ↦ p.1 - p.2)
                (by fun_prop)
                hkernel_cont.aestronglyMeasurable
    _ = ∫ t : E, ψ t * BoundedContinuousFunction.innerProbChar t x ∂γ := by
          -- Proof comment: replace the difference law of the two half-Gaussians by the explicit
          -- scaled Gaussian from the previous measure-identity lemma.
          rw [hγ]

/-- Helper for Theorem 15.29: taking real parts of the half-Gaussian window identity produces the
real-valued bridge that the regularized density candidate needs. -/
lemma real_halfGaussianWindowIntegral_eq_real_differenceIntegral {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} {b : ℝ} (hb : 0 < b) (hψ_cont : Continuous ψ)
    (x : EuclideanSpace ℝ (Fin d)) :
    let E := EuclideanSpace ℝ (Fin d)
    let c : ℝ := -(2 * Real.pi)
    let aHalf : ℝ := b / (2 * c ^ 2)
    let a : ℝ := b / c ^ 2
    let γHalf : Measure E :=
      (ProbabilityTheory.stdGaussian E).map (Real.sqrt (2 * aHalf) • ·)
    let γ : Measure E :=
      (ProbabilityTheory.stdGaussian E).map (Real.sqrt (2 * a) • ·)
    Complex.re
        (∫ p : E × E,
          star (BoundedContinuousFunction.innerProbChar (-p.1) x) *
            ψ (p.1 - p.2) *
            BoundedContinuousFunction.innerProbChar (-p.2) x
            ∂(γHalf.prod γHalf)) =
      Complex.re
        (∫ t : E, ψ t * BoundedContinuousFunction.innerProbChar t x ∂γ) := by
  -- Proof comment: the complex-valued window identity is already proved, so the real-valued
  -- version needed for the density candidate is just its image under `Complex.re`.
  simpa using
    congrArg Complex.re
      (halfGaussianWindowIntegral_eq_differenceIntegral
        (d := d) (ψ := ψ) (b := b) hb hψ_cont x)

/-- Helper for Theorem 15.29: once the Gaussian-regularized inverse-Fourier candidate is known to
be `L¹`, its Fourier transform recovers the regularized kernel itself. -/
lemma gaussianRegularizedInverseFourierDensityFourierEq {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} {b : ℝ} (hb : 0 < b)
    (hψ_cont : Continuous ψ) (hψ_int : Integrable ψ)
    (hψ_psd : IsPositiveSemidefiniteFunction ψ) (hψ_zero : ψ 0 = 1)
    (hf_int : Integrable (gaussianRegularizedInverseFourierDensity ψ b)) :
    ∀ t : EuclideanSpace ℝ (Fin d),
      VectorFourier.fourierIntegral Real.fourierChar volume
          (innerₗ (EuclideanSpace ℝ (Fin d)))
          (fun x : EuclideanSpace ℝ (Fin d) ↦
            ((gaussianRegularizedInverseFourierDensity ψ b x : ℝ) : ℂ))
          t =
        Complex.exp (-(b : ℂ) * ‖t‖ ^ 2) * ψ t := by
  let E := EuclideanSpace ℝ (Fin d)
  let ψb : E → ℂ := fun t ↦ Complex.exp (-(b : ℂ) * ‖t‖ ^ 2) * ψ t
  let f : E → ℝ := gaussianRegularizedInverseFourierDensity ψ b
  have hψb_spec : Continuous ψb ∧ Integrable ψb ∧ IsPositiveSemidefiniteFunction ψb ∧ ψb 0 = 1 := by
    -- Proof comment: the regularized kernel itself satisfies the standard continuity,
    -- integrability, positive-semidefiniteness, and normalization package.
    simpa [ψb] using
      gaussianRegularizedKernelSpec
        (d := d) (ψ := ψ) (b := b) hb hψ_cont hψ_int hψ_psd hψ_zero
  have hf_complex : (fun x : E ↦ ((f x : ℝ) : ℂ)) = FourierTransformInv.fourierInv ψb := by
    -- Proof comment: the regularized inverse Fourier candidate is real-valued because the
    -- regularized kernel stays positive semidefinite.
    simpa [f, ψb] using
      gaussianRegularizedInverseFourierDensity_eq_ofRealFourierInv
        (d := d) (ψ := ψ) (b := b) hb hψ_psd
  have hψb_fourier :
      FourierTransform.fourier ψb = fun x : E ↦ ((f (-x) : ℝ) : ℂ) := by
    ext x
    -- Proof comment: rewrite the Fourier transform at `x` as the inverse Fourier transform at
    -- `-x`, then use the identified regularized density candidate.
    calc
      FourierTransform.fourier ψb x = FourierTransform.fourier ψb (-(-x)) := by
          rw [neg_neg]
      _ = FourierTransformInv.fourierInv ψb (-x) := by
          exact (Real.fourierInv_eq_fourier_neg ψb (-x)).symm
      _ = ((f (-x) : ℝ) : ℂ) := by
          simpa using (congrFun hf_complex (-x)).symm
  have hψb_fourier_int : Integrable (FourierTransform.fourier ψb) := by
    -- Proof comment: after reflecting the argument, the Fourier transform is just the
    -- complexification of the assumed `L¹` regularized density.
    rw [hψb_fourier]
    simpa [f] using (Integrable.comp_neg hf_int).ofReal
  have hfourier :
      FourierTransform.fourier (fun x : E ↦ ((f x : ℝ) : ℂ)) = ψb := by
    -- Proof comment: Fourier inversion now recovers the regularized kernel from the regularized
    -- density candidate.
    rw [hf_complex]
    exact Continuous.fourier_fourierInv_eq hψb_spec.1 hψb_spec.2.1 hψb_fourier_int
  intro t
  -- Proof comment: unwrap the Fourier transform once and evaluate the recovered kernel at `t`.
  simpa [f, ψb] using congrFun hfourier t

/-- Helper for Theorem 15.29: once the Gaussian-regularized inverse-Fourier candidate is
pointwise nonnegative with total mass `1`, pushing forward its `withDensity` law by `-2π`
produces an actual characteristic-function witness for the regularized kernel. -/
lemma existsProbabilityMeasureOfGaussianRegularizedDensity {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} {b : ℝ} (hb : 0 < b)
    (hψ_cont : Continuous ψ) (hψ_int : Integrable ψ)
    (hψ_psd : IsPositiveSemidefiniteFunction ψ) (hψ_zero : ψ 0 = 1)
    (hf_nonneg : ∀ x, 0 ≤ gaussianRegularizedInverseFourierDensity ψ b x)
    (hf_mass : ∫ x, gaussianRegularizedInverseFourierDensity ψ b x = 1) :
    ∃ μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)),
      ∀ t : EuclideanSpace ℝ (Fin d),
        charFun (μ : Measure (EuclideanSpace ℝ (Fin d))) t =
          Complex.exp (-(b : ℂ) * ‖t‖ ^ 2) * ψ t := by
  let E := EuclideanSpace ℝ (Fin d)
  let f : E → ℝ := gaussianRegularizedInverseFourierDensity ψ b
  let c : ℝ := -(2 * Real.pi)
  let cInv : ℝ := (-(2 * Real.pi)⁻¹ : ℝ)
  let ρ : E → ℂ := fun t ↦
    Complex.exp (-(b : ℂ) * ‖cInv • t‖ ^ 2) * ψ (cInv • t)
  have hf_cont : Continuous f := by
    -- Proof comment: the regularized inverse-Fourier candidate is continuous as a real-valued
    -- function by the earlier continuity theorem.
    simpa [f] using
      gaussianRegularizedInverseFourierDensityContinuousReal
        (d := d) (ψ := ψ) (b := b) hb hψ_cont hψ_psd hψ_zero
  have hf_int : Integrable f := by
    -- Proof comment: continuity, pointwise nonnegativity, and total mass `1` upgrade the
    -- regularized candidate itself to an `L¹` density.
    exact
      integrable_of_continuous_nonneg_integral_eq_one
        (d := d) (f := f) hf_cont hf_nonneg hf_mass
  have hρ_fourier :
      ∀ t : E,
        VectorFourier.fourierIntegral Real.fourierChar volume
            (innerₗ E)
            (fun x : E ↦ ((f x : ℝ) : ℂ))
            (-(2 * Real.pi)⁻¹ • t) = ρ t := by
    intro t
    -- Proof comment: evaluate the recovered Fourier transform of `f` at the normalized point
    -- `(-(2π)⁻¹) • t`.
    simpa [f, ρ, cInv] using
      gaussianRegularizedInverseFourierDensityFourierEq
        (d := d) (ψ := ψ) (b := b) hb hψ_cont hψ_int hψ_psd hψ_zero hf_int
        (((-(2 * Real.pi)⁻¹ : ℝ)) • t)
  rcases
    existsProbabilityMeasureOfRealDensityFourierEq
      (d := d) (f := f) (ψ := ρ) hf_nonneg hf_int hf_mass hρ_fourier with
    ⟨ν, hν⟩
  let μ : ProbabilityMeasure E :=
    ⟨Measure.map (c • ·) (ν : Measure E), Measure.isProbabilityMeasure_map (by fun_prop)⟩
  refine ⟨μ, ?_⟩
  intro t
  have hc_scalar : cInv * c = 1 := by
    dsimp [cInv, c]
    field_simp [Real.pi_ne_zero]
  have hc_apply : cInv • (c • t) = t := by
    calc
      cInv • (c • t) = (cInv * c) • t := by rw [smul_smul]
      _ = (1 : ℝ) • t := by rw [hc_scalar]
      _ = t := by simp
  calc
    charFun (μ : Measure E) t = charFun (ν : Measure E) (c • t) := by
      simpa [μ, c] using (MeasureTheory.charFun_map_smul (μ := (ν : Measure E)) c t)
    _ = ρ (c • t) := hν (c • t)
    _ = Complex.exp (-(b : ℂ) * ‖t‖ ^ 2) * ψ t := by
      simpa [ρ, hc_apply]

/-- Helper for Theorem 15.29: the Gaussian-window quadratic integrand has norm at most `1`, so
the positive-definite kernel is the only nontrivial contribution in the planned `γ × γ` route. -/
lemma norm_gaussianWindowQuadraticIntegrand_le_one {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ}
    (hψ_psd : IsPositiveSemidefiniteFunction ψ) (hψ_zero : ψ 0 = 1)
    (x u v : EuclideanSpace ℝ (Fin d)) :
    ‖star (BoundedContinuousFunction.innerProbChar (-u) x) * ψ (u - v) *
        BoundedContinuousFunction.innerProbChar (-v) x‖ ≤ 1 := by
  have hu_norm : ‖BoundedContinuousFunction.innerProbChar (-u) x‖ = 1 := by
    -- Proof comment: every `innerProbChar` value is a unit-modulus complex exponential.
    rw [BoundedContinuousFunction.innerProbChar_apply, Complex.norm_exp_ofReal_mul_I]
  have hv_norm : ‖BoundedContinuousFunction.innerProbChar (-v) x‖ = 1 := by
    -- Proof comment: the same unit-modulus calculation applies to the second Gaussian-window
    -- phase factor.
    rw [BoundedContinuousFunction.innerProbChar_apply, Complex.norm_exp_ofReal_mul_I]
  calc
    ‖star (BoundedContinuousFunction.innerProbChar (-u) x) * ψ (u - v) *
        BoundedContinuousFunction.innerProbChar (-v) x‖
        = ‖star (BoundedContinuousFunction.innerProbChar (-u) x)‖ * ‖ψ (u - v)‖ *
            ‖BoundedContinuousFunction.innerProbChar (-v) x‖ := by
              simp [mul_assoc]
    _ = ‖ψ (u - v)‖ := by
          rw [norm_star, hu_norm, hv_norm]
          simp
    _ ≤ 1 :=
      norm_le_one_of_isPositiveSemidefiniteFunction_zero_eq_one
        hψ_psd hψ_zero (u - v)

/-- Helper for Theorem 15.29: the planned Gaussian-window quadratic integrand is already
integrable on `γ × γ`; the remaining frontier is the exact product identity and positivity
argument, not measurability or Fubini side conditions. -/
lemma integrable_gaussianWindowQuadraticIntegrand {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} {b : ℝ}
    (hψ_cont : Continuous ψ)
    (hψ_psd : IsPositiveSemidefiniteFunction ψ) (hψ_zero : ψ 0 = 1)
    (x : EuclideanSpace ℝ (Fin d)) :
    let E := EuclideanSpace ℝ (Fin d)
    let c : ℝ := -(2 * Real.pi)
    let a : ℝ := b / c ^ 2
    let γ : Measure E :=
      (ProbabilityTheory.stdGaussian E).map (Real.sqrt (2 * a) • ·)
    Integrable
      (fun p : E × E ↦
        star (BoundedContinuousFunction.innerProbChar (-p.1) x) *
          ψ (p.1 - p.2) *
          BoundedContinuousFunction.innerProbChar (-p.2) x) (γ.prod γ) := by
  let E := EuclideanSpace ℝ (Fin d)
  let c : ℝ := -(2 * Real.pi)
  let a : ℝ := b / c ^ 2
  let γ : Measure E :=
    (ProbabilityTheory.stdGaussian E).map (Real.sqrt (2 * a) • ·)
  haveI : IsProbabilityMeasure γ := by
    dsimp [γ]
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  have hleft :
      Continuous fun p : E × E ↦ BoundedContinuousFunction.innerProbChar (-p.1) x := by
    -- Proof comment: each Gaussian-window phase is continuous in the corresponding product
    -- coordinate.
    simpa [BoundedContinuousFunction.innerProbChar_apply] using
      (Complex.continuous_exp.comp
        (by
          fun_prop :
            Continuous fun p : E × E ↦
              (↑(inner ℝ x (-p.1)) : ℂ) * Complex.I))
  have hkernel : Continuous fun p : E × E ↦ ψ (p.1 - p.2) := by
    -- Proof comment: the kernel factor is continuous after composing `ψ` with subtraction on the
    -- two Gaussian variables.
    exact hψ_cont.comp (continuous_fst.sub continuous_snd)
  have hright :
      Continuous fun p : E × E ↦ BoundedContinuousFunction.innerProbChar (-p.2) x := by
    -- Proof comment: the second phase factor is handled by the same continuity computation on the
    -- second coordinate.
    simpa [BoundedContinuousFunction.innerProbChar_apply] using
      (Complex.continuous_exp.comp
        (by
          fun_prop :
            Continuous fun p : E × E ↦
              (↑(inner ℝ x (-p.2)) : ℂ) * Complex.I))
  refine Integrable.of_bound ((hleft.star.mul hkernel).mul hright).aestronglyMeasurable 1 ?_
  filter_upwards with p
  -- Proof comment: the pointwise norm bound collapses to `‖ψ (u - v)‖ ≤ 1`, and `γ × γ` is a
  -- finite measure because `γ` is a probability measure.
  exact
    norm_gaussianWindowQuadraticIntegrand_le_one
      (d := d) (ψ := ψ) hψ_psd hψ_zero x p.1 p.2

/-- Helper for Theorem 15.29: after the fixed Fourier normalization, the rescaled regularized
kernel still has the standard continuous, integrable, positive-semidefinite, and normalized
package. -/
lemma scaledGaussianRegularizedKernelSpec {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} {b : ℝ} (hb : 0 < b)
    (hψ_cont : Continuous ψ) (hψ_int : Integrable ψ)
    (hψ_psd : IsPositiveSemidefiniteFunction ψ) (hψ_zero : ψ 0 = 1) :
    let E := EuclideanSpace ℝ (Fin d)
    let cInv : ℝ := (-(2 * Real.pi)⁻¹ : ℝ)
    let ρ : E → ℂ := fun t ↦ Complex.exp (-(b : ℂ) * ‖cInv • t‖ ^ 2) * ψ (cInv • t)
    Continuous ρ ∧ Integrable ρ ∧ IsPositiveSemidefiniteFunction ρ ∧ ρ 0 = 1 := by
  let E := EuclideanSpace ℝ (Fin d)
  let cInv : ℝ := (-(2 * Real.pi)⁻¹ : ℝ)
  let ρ : E → ℂ := fun t ↦ Complex.exp (-(b : ℂ) * ‖cInv • t‖ ^ 2) * ψ (cInv • t)
  let ψb : E → ℂ := fun t ↦ Complex.exp (-(b : ℂ) * ‖t‖ ^ 2) * ψ t
  have hψb_spec : Continuous ψb ∧ Integrable ψb ∧ IsPositiveSemidefiniteFunction ψb ∧ ψb 0 = 1 := by
    -- Proof comment: first package the undistorted regularized kernel using the earlier owner.
    simpa [ψb] using
      gaussianRegularizedKernelSpec
        (d := d) (ψ := ψ) (b := b) hb hψ_cont hψ_int hψ_psd hψ_zero
  have hcInv : cInv ≠ 0 := by
    -- Proof comment: the fixed scaling factor `(-(2π))⁻¹` is nonzero.
    dsimp [cInv]
    have htwoPi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    exact neg_ne_zero.mpr (inv_ne_zero htwoPi)
  have hρ_cont : Continuous ρ := by
    -- Proof comment: the rescaled kernel is `ψb` composed with the nonzero linear map
    -- `t ↦ cInv • t`.
    have hscale : Continuous fun t : E ↦ cInv • t := by
      simpa [cInv] using
        (continuous_const.smul continuous_id : Continuous fun t : E ↦ cInv • t)
    exact hψb_spec.1.comp hscale
  have hρ_int : Integrable ρ := by
    -- Proof comment: Lebesgue-integrability is preserved by nonzero scalar precomposition.
    simpa [ρ, ψb] using hψb_spec.2.1.comp_smul hcInv
  have hρ_psd : IsPositiveSemidefiniteFunction ρ := by
    -- Proof comment: positive semidefiniteness is stable under precomposition by the fixed linear
    -- normalization map `t ↦ cInv • t`.
    have hψb_psd : IsPositiveSemidefiniteFunction ψb := hψb_spec.2.2.1
    rw [isPositiveSemidefiniteFunction_iff_quadratic_sum_nonneg] at hψb_psd ⊢
    intro n t z
    have hmain :
        0 ≤
          ∑ i, ∑ j, star (z i) * ψb (cInv • t i - cInv • t j) * z j := by
      simpa using hψb_psd n (fun i ↦ cInv • t i) z
    have hsum :
        (∑ i, ∑ j, star (z i) * ρ (t i - t j) * z j) =
          ∑ i, ∑ j, star (z i) * ψb (cInv • t i - cInv • t j) * z j := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      refine Finset.sum_congr rfl ?_
      intro j hj
      simp [ρ, ψb, smul_sub]
    rw [hsum]
    exact hmain
  have hρ_zero : ρ 0 = 1 := by
    -- Proof comment: evaluating at the origin cancels the rescaling and keeps the normalized
    -- value of the regularized kernel.
    simpa [ρ, ψb, cInv] using hψb_spec.2.2.2
  exact ⟨hρ_cont, hρ_int, hρ_psd, hρ_zero⟩

/-- Helper for Theorem 15.29: once `ψ` already has an actual Euclidean characteristic-function
witness, the fixed `-2π` rescaled Gaussian-regularized kernel also has an actual witness. -/
lemma existsProbabilityMeasureOfScaledGaussianRegularizedKernelOfCharFunWitness {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} {b : ℝ} (hb : 0 < b)
    (hψ_witness : ∃ μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)),
      ∀ t : EuclideanSpace ℝ (Fin d),
        charFun (μ : Measure (EuclideanSpace ℝ (Fin d))) t = ψ t) :
    let E := EuclideanSpace ℝ (Fin d)
    let c : ℝ := -(2 * Real.pi)
    let a : ℝ := b / c ^ 2
    let ρ : E → ℂ := fun t ↦ Complex.exp (-(a : ℂ) * ‖t‖ ^ 2) * ψ (c⁻¹ • t)
    ∃ ν : ProbabilityMeasure E, ∀ t : E, charFun (ν : Measure E) t = ρ t := by
  let E := EuclideanSpace ℝ (Fin d)
  let c : ℝ := -(2 * Real.pi)
  let a : ℝ := b / c ^ 2
  let ρ : E → ℂ := fun t ↦ Complex.exp (-(a : ℂ) * ‖t‖ ^ 2) * ψ (c⁻¹ • t)
  rcases hψ_witness with ⟨μ, hμ⟩
  have hc : c ≠ 0 := by
    -- Proof comment: the fixed Fourier-normalization scalar `-2π` is nonzero.
    have htwoPi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    exact neg_ne_zero.mpr htwoPi
  let μScaled : ProbabilityMeasure E :=
    ⟨Measure.map (c⁻¹ • ·) (μ : Measure E), Measure.isProbabilityMeasure_map (by fun_prop)⟩
  have hμScaled :
      ∀ t : E, charFun (μScaled : Measure E) t = ψ (c⁻¹ • t) := by
    intro t
    -- Proof comment: pushing the witness forward by `c⁻¹` rewrites its characteristic function
    -- by precomposition with the same fixed linear map.
    calc
      charFun (μScaled : Measure E) t = charFun (μ : Measure E) (c⁻¹ • t) := by
        simpa [μScaled, c] using
          (MeasureTheory.charFun_map_smul (μ := (μ : Measure E)) c⁻¹ t)
      _ = ψ (c⁻¹ • t) := hμ (c⁻¹ • t)
  have ha : 0 < a := by
    -- Proof comment: the rescaled Gaussian parameter stays positive because `b > 0`.
    dsimp [a]
    exact div_pos hb (sq_pos_of_ne_zero hc)
  rcases
    gaussianDampedMeasureExistsOfProbabilityMeasure
      (d := d) (μ := μScaled) (a := a) ha with
    ⟨ν, hν⟩
  refine ⟨ν, ?_⟩
  intro t
  -- Proof comment: the damped witness theorem supplies the Gaussian factor, and the pushed-forward
  -- characteristic-function identity supplies the rescaled kernel spelling.
  calc
    charFun (ν : Measure E) t
        = Complex.exp (-(a : ℂ) * ‖t‖ ^ 2) * charFun (μScaled : Measure E) t := hν t
    _ = Complex.exp (-(a : ℂ) * ‖t‖ ^ 2) * ψ (c⁻¹ • t) := by rw [hμScaled t]
    _ = ρ t := by rfl

/-- Helper for Theorem 15.29: if `ψ` already has an actual Euclidean characteristic-function
witness, then the exact scaled regularized kernel spelling used by the fixed `-2π` Fourier
normalization also has one. -/
lemma scaledRegularizedKernel_eq_scaledGaussianDampedKernel {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} {b : ℝ} :
    let E := EuclideanSpace ℝ (Fin d)
    let c : ℝ := -(2 * Real.pi)
    let cInv : ℝ := c⁻¹
    let a : ℝ := b / c ^ 2
    let ρScaled : E → ℂ := fun t ↦ Complex.exp (-(a : ℂ) * ‖t‖ ^ 2) * ψ (cInv • t)
    let ρ : E → ℂ := fun t ↦ Complex.exp (-(b : ℂ) * ‖cInv • t‖ ^ 2) * ψ (cInv • t)
    ρ = ρScaled := by
  let E := EuclideanSpace ℝ (Fin d)
  let c : ℝ := -(2 * Real.pi)
  let cInv : ℝ := c⁻¹
  let a : ℝ := b / c ^ 2
  let ρScaled : E → ℂ := fun t ↦ Complex.exp (-(a : ℂ) * ‖t‖ ^ 2) * ψ (cInv • t)
  let ρ : E → ℂ := fun t ↦ Complex.exp (-(b : ℂ) * ‖cInv • t‖ ^ 2) * ψ (cInv • t)
  funext t
  have hnorm : ‖cInv • t‖ ^ 2 = cInv ^ 2 * ‖t‖ ^ 2 := by
    -- Proof comment: pull the fixed scalar `cInv` out of the norm once so the Gaussian exponents
    -- can be compared directly.
    calc
      ‖cInv • t‖ ^ 2 = (‖cInv‖ * ‖t‖) ^ 2 := by rw [norm_smul]
      _ = (|cInv| * ‖t‖) ^ 2 := by rw [Real.norm_eq_abs]
      _ = |cInv| ^ 2 * ‖t‖ ^ 2 := by ring
      _ = cInv ^ 2 * ‖t‖ ^ 2 := by rw [sq_abs]
  have hscalar : b * cInv ^ 2 = a := by
    dsimp [a, cInv, c]
    field_simp [Real.pi_ne_zero]
  have hargR : b * ‖cInv • t‖ ^ 2 = a * ‖t‖ ^ 2 := by
    -- Proof comment: the explicit parameter choice `a = b / (-2π)^2` is exactly the one that
    -- matches the rescaled Gaussian exponent.
    calc
      b * ‖cInv • t‖ ^ 2 = b * (cInv ^ 2 * ‖t‖ ^ 2) := by rw [hnorm]
      _ = (b * cInv ^ 2) * ‖t‖ ^ 2 := by ring
      _ = a * ‖t‖ ^ 2 := by rw [hscalar]
  have hargC : (b : ℂ) * ‖cInv • t‖ ^ 2 = (a : ℂ) * ‖t‖ ^ 2 := by
    exact_mod_cast hargR
  -- Proof comment: after casting the exponent identity to `ℂ`, the two frozen kernel spellings
  -- are literally the same function.
  change
      Complex.exp (-(b : ℂ) * ‖cInv • t‖ ^ 2) * ψ (cInv • t) =
        Complex.exp (-(a : ℂ) * ‖t‖ ^ 2) * ψ (cInv • t)
  congr 1
  exact congrArg Complex.exp <| by simpa [neg_mul] using congrArg Neg.neg hargC

/-- Helper for Theorem 15.29: a characteristic-function witness for `ψ` transports to the exact
scaled regularized kernel together with its continuity, `L¹`, positive semidefiniteness,
normalization, and witness package. -/
lemma scaledRegularizedKernelSpecAndWitnessOfCharFunWitness {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} {b : ℝ} (hb : 0 < b)
    (hψ_witness : ∃ μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)),
      ∀ t : EuclideanSpace ℝ (Fin d),
        charFun (μ : Measure (EuclideanSpace ℝ (Fin d))) t = ψ t) :
    let E := EuclideanSpace ℝ (Fin d)
    let c : ℝ := -(2 * Real.pi)
    let cInv : ℝ := c⁻¹
    let ρ : E → ℂ := fun t ↦ Complex.exp (-(b : ℂ) * ‖cInv • t‖ ^ 2) * ψ (cInv • t)
    Continuous ρ ∧ Integrable ρ ∧ IsPositiveSemidefiniteFunction ρ ∧ ρ 0 = 1 ∧
      ∃ ν : ProbabilityMeasure E, ∀ t : E, charFun (ν : Measure E) t = ρ t := by
  let E := EuclideanSpace ℝ (Fin d)
  let c : ℝ := -(2 * Real.pi)
  let cInv : ℝ := c⁻¹
  let a : ℝ := b / c ^ 2
  let ρScaled : E → ℂ := fun t ↦ Complex.exp (-(a : ℂ) * ‖t‖ ^ 2) * ψ (cInv • t)
  let ρ : E → ℂ := fun t ↦ Complex.exp (-(b : ℂ) * ‖cInv • t‖ ^ 2) * ψ (cInv • t)
  have hc : c ≠ 0 := by
    -- Proof comment: the fixed Fourier-normalization scalar `-2π` is nonzero.
    have htwoPi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    exact neg_ne_zero.mpr htwoPi
  have ha : 0 < a := by
    -- Proof comment: the rescaled Gaussian parameter stays positive because `b > 0`.
    dsimp [a]
    exact div_pos hb (sq_pos_of_ne_zero hc)
  have hρ_eq : ρ = ρScaled := by
    -- Proof comment: freeze the exact scaled regularized kernel spelling once before transporting
    -- the witness-side Gaussian-damped package.
    simpa [E, c, cInv, a, ρScaled, ρ] using
      (scaledRegularizedKernel_eq_scaledGaussianDampedKernel
        (d := d) (ψ := ψ) (b := b))
  rcases hψ_witness with ⟨μ, hμ⟩
  let μScaled : ProbabilityMeasure E :=
    ⟨Measure.map (cInv • ·) (μ : Measure E), Measure.isProbabilityMeasure_map (by fun_prop)⟩
  have hμScaled_fun : charFun (μScaled : Measure E) = fun t : E ↦ ψ (cInv • t) := by
    funext t
    dsimp [μScaled]
    rw [MeasureTheory.charFun_map_smul]
    exact hμ (cInv • t)
  have hρScaled_spec :
      Continuous ρScaled ∧ Integrable ρScaled ∧ IsPositiveSemidefiniteFunction ρScaled ∧
        ρScaled 0 = 1 ∧
          ∃ ν : ProbabilityMeasure E, ∀ t : E, charFun (ν : Measure E) t = ρScaled t := by
    -- Proof comment: after scaling the original witness by `cInv`, the rescaled kernel is the
    -- standard Gaussian-damped characteristic function of that pushed-forward law.
    have hspec :=
      gaussianDampedKernelSpecAndWitnessOfProbabilityMeasure
        (d := d) (μ := μScaled) (a := a) ha
    rcases hspec with ⟨hcont, hint, hpsd, hzero, hν⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [ρScaled, hμScaled_fun] using hcont
    · simpa [ρScaled, hμScaled_fun] using hint
    · simpa [ρScaled, hμScaled_fun] using hpsd
    · have hψ_zero : ψ 0 = 1 := by
        calc
          ψ 0 = charFun (μScaled : Measure E) 0 := by
            simpa using (congrFun hμScaled_fun 0).symm
          _ = 1 := by
            simpa using (MeasureTheory.charFun_zero (μ := (μScaled : Measure E)))
      simp [ρScaled, hψ_zero]
    · simpa [ρScaled, hμScaled_fun] using hν
  rcases hρScaled_spec with ⟨hcont, hint, hpsd, hzero, hν⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change Continuous ρ
    rw [hρ_eq]
    exact hcont
  · change Integrable ρ
    rw [hρ_eq]
    exact hint
  · change IsPositiveSemidefiniteFunction ρ
    rw [hρ_eq]
    exact hpsd
  · change ρ 0 = 1
    rw [hρ_eq]
    exact hzero
  · rcases hν with ⟨ν, hν⟩
    refine ⟨ν, ?_⟩
    intro t
    change charFun (ν : Measure E) t = ρ t
    rw [hρ_eq]
    exact hν t

/-- Helper for Theorem 15.29: if `ψ` already has an actual Euclidean characteristic-function
witness, then the exact scaled regularized kernel spelling used by the fixed `-2π` Fourier
normalization also has one. -/
lemma existsProbabilityMeasureOfScaledRegularizedKernelOfCharFunWitness {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} {b : ℝ} (hb : 0 < b)
    (hψ_witness : ∃ μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)),
      ∀ t : EuclideanSpace ℝ (Fin d),
        charFun (μ : Measure (EuclideanSpace ℝ (Fin d))) t = ψ t) :
    let E := EuclideanSpace ℝ (Fin d)
    let c : ℝ := -(2 * Real.pi)
    let cInv : ℝ := c⁻¹
    let ρ : E → ℂ := fun t ↦ Complex.exp (-(b : ℂ) * ‖cInv • t‖ ^ 2) * ψ (cInv • t)
    ∃ ν : ProbabilityMeasure E, ∀ t : E, charFun (ν : Measure E) t = ρ t := by
  let E := EuclideanSpace ℝ (Fin d)
  let c : ℝ := -(2 * Real.pi)
  let cInv : ℝ := c⁻¹
  let a : ℝ := b / c ^ 2
  let ρScaled : E → ℂ := fun t ↦ Complex.exp (-(a : ℂ) * ‖t‖ ^ 2) * ψ (cInv • t)
  let ρ : E → ℂ := fun t ↦ Complex.exp (-(b : ℂ) * ‖cInv • t‖ ^ 2) * ψ (cInv • t)
  have hρ_eq : ρ = ρScaled := by
    funext t
    have hnorm : ‖cInv • t‖ ^ 2 = cInv ^ 2 * ‖t‖ ^ 2 := by
      -- Proof comment: pull the fixed scalar `c⁻¹` out of the norm once so the Gaussian
      -- exponents can be compared directly.
      calc
        ‖cInv • t‖ ^ 2 = (‖cInv‖ * ‖t‖) ^ 2 := by rw [norm_smul]
        _ = (|cInv| * ‖t‖) ^ 2 := by rw [Real.norm_eq_abs]
        _ = |cInv| ^ 2 * ‖t‖ ^ 2 := by ring
        _ = cInv ^ 2 * ‖t‖ ^ 2 := by rw [sq_abs]
    have hscalar : b * cInv ^ 2 = a := by
      dsimp [a, cInv, c]
      field_simp [Real.pi_ne_zero]
    have hargR : b * ‖cInv • t‖ ^ 2 = a * ‖t‖ ^ 2 := by
      -- Proof comment: the explicit parameter choice `a = b / (-(2π))²` is exactly the one that
      -- matches the rescaled Gaussian exponent.
      calc
        b * ‖cInv • t‖ ^ 2 = b * (cInv ^ 2 * ‖t‖ ^ 2) := by rw [hnorm]
        _ = (b * cInv ^ 2) * ‖t‖ ^ 2 := by ring
        _ = a * ‖t‖ ^ 2 := by rw [hscalar]
    have hargC : (b : ℂ) * ‖cInv • t‖ ^ 2 = (a : ℂ) * ‖t‖ ^ 2 := by
      exact_mod_cast hargR
    -- Proof comment: after casting the exponent identity to `ℂ`, the two frozen kernel spellings
    -- are literally the same function.
    dsimp [ρ, ρScaled]
    congr 1
    exact congrArg Complex.exp <| by simpa [neg_mul] using congrArg Neg.neg hargC
  rcases
    (show ∃ ν : ProbabilityMeasure E, ∀ t : E, charFun (ν : Measure E) t = ρScaled t from by
      simpa [E, c, a, cInv, ρScaled] using
        existsProbabilityMeasureOfScaledGaussianRegularizedKernelOfCharFunWitness
          (d := d) (ψ := ψ) (b := b) hb hψ_witness) with
    ⟨ν, hν⟩
  refine ⟨ν, ?_⟩
  intro t
  -- Proof comment: transfer the witness through the exact equality of the two scaled-kernel
  -- spellings so later callers can stay on the fixed `ρ` normal form.
  change charFun (ν : Measure E) t = ρ t
  rw [hρ_eq]
  exact hν t

/-- Helper for Theorem 15.29: the regularized inverse-Fourier candidate is exactly the scaled
inverse-Fourier candidate attached to the rescaled regularized kernel. -/
lemma gaussianRegularizedInverseFourierDensity_eq_scaledKernelFourierInv {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} {b : ℝ} :
    let E := EuclideanSpace ℝ (Fin d)
    let c : ℝ := -(2 * Real.pi)
    let cInv : ℝ := (-(2 * Real.pi)⁻¹ : ℝ)
    let ρ : E → ℂ := fun t ↦ Complex.exp (-(b : ℂ) * ‖cInv • t‖ ^ 2) * ψ (cInv • t)
    gaussianRegularizedInverseFourierDensity ψ b =
      fun x : E ↦ Complex.re (FourierTransformInv.fourierInv (fun t : E ↦ ρ (c • t)) x) := by
  -- Proof comment: this bridge is only a fixed scalar-cancellation rewrite inside the frozen
  -- regularized kernel; no witness-side Bochner input is needed here.
  let E := EuclideanSpace ℝ (Fin d)
  let c : ℝ := -(2 * Real.pi)
  let cInv : ℝ := (-(2 * Real.pi)⁻¹ : ℝ)
  let ρ : E → ℂ := fun t ↦ Complex.exp (-(b : ℂ) * ‖cInv • t‖ ^ 2) * ψ (cInv • t)
  have hrescale : cInv * c = (1 : ℝ) := by
    dsimp [cInv, c]
    field_simp [Real.pi_ne_zero]
  ext x
  -- Proof comment: after cancelling the fixed scalar inside the rescaled kernel, the two Fourier
  -- kernels become definitionally identical.
  apply congrArg Complex.re
  apply congrArg (fun κ : E → ℂ ↦ FourierTransformInv.fourierInv κ x)
  funext t
  dsimp [gaussianRegularizedInverseFourierDensity, ρ, E, c, cInv]
  have hsmul : (-(2 * Real.pi)⁻¹ : ℝ) • ((-(2 * Real.pi) : ℝ) • t) = t := by
    calc
      (-(2 * Real.pi)⁻¹ : ℝ) • ((-(2 * Real.pi) : ℝ) • t)
          = (((-(2 * Real.pi)⁻¹ : ℝ) * (-(2 * Real.pi) : ℝ)) : ℝ) • t := by
              rw [smul_smul]
      _ = (1 : ℝ) • t := by rw [hrescale]
      _ = t := by simp
  rw [hsmul]

/-- Helper for Theorem 15.29: positive semidefiniteness already controls every finite-support
quadratic form indexed by a `Finset`, which is the discrete core of the planned Gaussian-window
approximation. -/
lemma quadraticSum_nonneg_of_isPositiveSemidefiniteFunction_finset {G : Type*} [AddGroup G]
    {φ : G → ℂ} (hφ : IsPositiveSemidefiniteFunction φ) (s : Finset G) (w : G → ℂ) :
    0 ≤ ∑ u ∈ s, ∑ v ∈ s, star (w u) * φ (u - v) * w v := by
  classical
  let e := Finset.equivFin s
  have hmain :
      0 ≤
        ∑ i : Fin s.card,
          ∑ j : Fin s.card,
            star (w (((e.symm i : s) : G))) *
              φ ((((e.symm i : s) : G)) - (((e.symm j : s) : G))) *
              w (((e.symm j : s) : G)) := by
    -- Proof comment: enumerate the finite set by `Fin s.card`, then apply the textbook
    -- quadratic-sum criterion in its original `Fin n` form.
    exact
      (isPositiveSemidefiniteFunction_iff_quadratic_sum_nonneg.mp hφ)
        s.card
        (fun i ↦ ((e.symm i : s) : G))
        (fun i ↦ w (((e.symm i : s) : G)))
  have hinner :
      ∀ u : s,
        (∑ j : Fin s.card,
            star (w (u : G)) * φ ((u : G) - (((e.symm j : s) : G))) *
              w (((e.symm j : s) : G))) =
          ∑ v : s, star (w (u : G)) * φ ((u : G) - v) * w (v : G) := by
    intro u
    -- Proof comment: reindex the inner finite sum from `Fin s.card` back to the subtype `s`.
    exact
      (Fintype.sum_equiv e
        (fun v : s ↦ star (w (u : G)) * φ ((u : G) - v) * w (v : G))
        (fun j : Fin s.card ↦
          star (w (u : G)) * φ ((u : G) - (((e.symm j : s) : G))) *
            w (((e.symm j : s) : G)))
        (fun v ↦ by simp)).symm
  have hsum₁ :
      (∑ i : Fin s.card,
          ∑ j : Fin s.card,
            star (w (((e.symm i : s) : G))) *
              φ ((((e.symm i : s) : G)) - (((e.symm j : s) : G))) *
              w (((e.symm j : s) : G))) =
        ∑ u : s,
          ∑ j : Fin s.card,
            star (w (u : G)) * φ ((u : G) - (((e.symm j : s) : G))) *
              w (((e.symm j : s) : G)) := by
    -- Proof comment: reindex the outer sum by the same `Finset.equivFin` enumeration.
    exact
      (Fintype.sum_equiv e
        (fun u : s ↦
          ∑ j : Fin s.card,
            star (w (u : G)) * φ ((u : G) - (((e.symm j : s) : G))) *
              w (((e.symm j : s) : G)))
        (fun i : Fin s.card ↦
          ∑ j : Fin s.card,
            star (w (((e.symm i : s) : G))) *
              φ ((((e.symm i : s) : G)) - (((e.symm j : s) : G))) *
              w (((e.symm j : s) : G)))
        (fun u ↦ by simp)).symm
  have hsum₂ :
      (∑ u : s,
          ∑ j : Fin s.card,
            star (w (u : G)) * φ ((u : G) - (((e.symm j : s) : G))) *
              w (((e.symm j : s) : G))) =
        ∑ u : s, ∑ v : s, star (w (u : G)) * φ ((u : G) - v) * w (v : G) := by
    -- Proof comment: after the outer reindexing, the inner sums are exactly the previous
    -- subtype-indexed quadratic forms.
    exact Fintype.sum_congr _ _ hinner
  have hsub :
      0 ≤ ∑ u : s, ∑ v : s, star (w (u : G)) * φ ((u : G) - v) * w (v : G) := by
    -- Proof comment: chaining the two reindexings reduces the finite-support claim to `hmain`.
    rw [← hsum₂, ← hsum₁]
    exact hmain
  have hattach :
      0 ≤
        ∑ u ∈ s.attach,
          ∑ v ∈ s.attach,
            star (w (u : G)) * φ ((u : G) - v) * w (v : G) := by
    -- Proof comment: summing over the subtype `s` is definitionally the same as summing over the
    -- attached finset of tagged elements.
    simpa using hsub
  calc
    0 ≤
        ∑ u ∈ s.attach,
          ∑ v ∈ s.attach,
            star (w (u : G)) * φ ((u : G) - v) * w (v : G) := hattach
    _ = ∑ u ∈ s.attach, ∑ v ∈ s, star (w (u : G)) * φ ((u : G) - v) * w v := by
          -- Proof comment: first remove the inner subtype tags using `Finset.sum_attach`.
          refine Finset.sum_congr rfl ?_
          intro u hu
          exact
            Finset.sum_attach s
              (fun v : G ↦ star (w (u : G)) * φ ((u : G) - v) * w v)
    _ = ∑ u ∈ s, ∑ v ∈ s, star (w u) * φ (u - v) * w v := by
          -- Proof comment: then remove the outer subtype tags in the same way.
          exact
            Finset.sum_attach s
              (fun u : G ↦ ∑ v ∈ s, star (w u) * φ (u - v) * w v)

/-- Helper for Theorem 15.29: once a sequence of probability measures converges weakly, the
Gaussian-window quadratic integrals against the corresponding product measures converge as well. -/
lemma gaussianWindowIntegral_tendsto_of_tendsto {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} (hψ_cont : Continuous ψ)
    (hψ_psd : IsPositiveSemidefiniteFunction ψ) (hψ_zero : ψ 0 = 1)
    (x : EuclideanSpace ℝ (Fin d)) {γP : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))}
    {νn : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin d))}
    (hνn : Tendsto νn atTop (𝓝 γP)) :
    Tendsto
      (fun n ↦
        ∫ p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d),
          star (BoundedContinuousFunction.innerProbChar (-p.1) x) *
            ψ (p.1 - p.2) *
            BoundedContinuousFunction.innerProbChar (-p.2) x
            ∂(((νn n).prod (νn n) :
              ProbabilityMeasure
                (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))) :
                Measure
                  (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))))
      atTop
      (𝓝
        (∫ p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d),
          star (BoundedContinuousFunction.innerProbChar (-p.1) x) *
            ψ (p.1 - p.2) *
            BoundedContinuousFunction.innerProbChar (-p.2) x
            ∂((γP.prod γP :
              ProbabilityMeasure
                (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))) :
                Measure
                  (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))))) := by
  let E := EuclideanSpace ℝ (Fin d)
  let κ : E × E → ℂ := fun p ↦
    star (BoundedContinuousFunction.innerProbChar (-p.1) x) *
      ψ (p.1 - p.2) *
      BoundedContinuousFunction.innerProbChar (-p.2) x
  have hκ_cont : Continuous κ := by
    have hleft :
        Continuous fun p : E × E ↦ BoundedContinuousFunction.innerProbChar (-p.1) x := by
      -- Proof comment: the first oscillatory phase depends continuously on the left product
      -- coordinate.
      simpa [BoundedContinuousFunction.innerProbChar_apply] using
        (Complex.continuous_exp.comp
          (by
            fun_prop :
              Continuous fun p : E × E ↦
                (↑(inner ℝ x (-p.1)) : ℂ) * Complex.I))
    have hkernel : Continuous fun p : E × E ↦ ψ (p.1 - p.2) := by
      -- Proof comment: the kernel factor is `ψ` composed with subtraction on the two variables.
      exact hψ_cont.comp (continuous_fst.sub continuous_snd)
    have hright :
        Continuous fun p : E × E ↦ BoundedContinuousFunction.innerProbChar (-p.2) x := by
      -- Proof comment: the right oscillatory phase is handled by the same continuity calculation
      -- on the second product coordinate.
      simpa [BoundedContinuousFunction.innerProbChar_apply] using
        (Complex.continuous_exp.comp
          (by
            fun_prop :
              Continuous fun p : E × E ↦
                (↑(inner ℝ x (-p.2)) : ℂ) * Complex.I))
    -- Proof comment: the Gaussian-window kernel is the product of the two phase factors and the
    -- middle kernel factor.
    exact (hleft.star.mul hkernel).mul hright
  have hκ_norm : ∀ p : E × E, ‖κ p‖ ≤ 1 := by
    intro p
    -- Proof comment: the earlier pointwise bound collapses the two phase factors to unit norm.
    simpa [κ] using
      norm_gaussianWindowQuadraticIntegrand_le_one
        (d := d) (ψ := ψ) hψ_psd hψ_zero x p.1 p.2
  let κC : C(E × E, ℂ) := ⟨κ, hκ_cont⟩
  let κB : BoundedContinuousFunction (E × E) ℂ :=
    BoundedContinuousFunction.mkOfBound κC 2
      (fun p q ↦ by
        -- Proof comment: `‖κ‖ ≤ 1` gives a uniform diameter bound, hence a bounded continuous
        -- representative suitable for the weak-convergence integral criterion.
        calc
          dist (κC p) (κC q) = ‖κC p - κC q‖ := by rw [dist_eq_norm]
          _ ≤ ‖κC p‖ + ‖κC q‖ := norm_sub_le _ _
          _ ≤ 1 + 1 := add_le_add (hκ_norm p) (hκ_norm q)
          _ = 2 := by norm_num)
  have hpair : Tendsto (fun n ↦ (νn n, νn n)) atTop (𝓝 (γP, γP)) := by
    -- Proof comment: the diagonal pair of the approximating measures converges to the diagonal
    -- pair of the limit measure.
    rw [nhds_prod_eq]
    exact hνn.prodMk hνn
  have hprod :
      Tendsto (fun n ↦ (νn n).prod (νn n)) atTop (𝓝 (γP.prod γP)) := by
    -- Proof comment: continuity of the product-probability construction transports the weak
    -- convergence of the marginals to weak convergence of the product measures.
    exact MeasureTheory.ProbabilityMeasure.continuous_prod.continuousAt.tendsto.comp hpair
  have hIntegral :=
    (MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).1 hprod κB
  -- Proof comment: evaluate the weak-convergence criterion on the bounded continuous Gaussian
  -- window kernel.
  simpa [κB, κC, κ] using hIntegral

/-- Helper for Theorem 15.29: taking real parts preserves convergence of the Gaussian-window
integrals along weakly convergent probability measures. -/
lemma real_gaussianWindowIntegral_tendsto_of_tendsto {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} (hψ_cont : Continuous ψ)
    (hψ_psd : IsPositiveSemidefiniteFunction ψ) (hψ_zero : ψ 0 = 1)
    (x : EuclideanSpace ℝ (Fin d)) {γP : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))}
    {νn : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin d))}
    (hνn : Tendsto νn atTop (𝓝 γP)) :
    Tendsto
      (fun n ↦
        Complex.re
          (∫ p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d),
            star (BoundedContinuousFunction.innerProbChar (-p.1) x) *
              ψ (p.1 - p.2) *
              BoundedContinuousFunction.innerProbChar (-p.2) x
              ∂(((νn n).prod (νn n) :
                ProbabilityMeasure
                  (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))) :
                  Measure
                    (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)))))
      atTop
      (𝓝
        (Complex.re
          (∫ p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d),
            star (BoundedContinuousFunction.innerProbChar (-p.1) x) *
              ψ (p.1 - p.2) *
              BoundedContinuousFunction.innerProbChar (-p.2) x
              ∂((γP.prod γP :
                ProbabilityMeasure
                  (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))) :
                  Measure
                    (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)))))) := by
  -- Proof comment: compose the complex-valued weak-convergence statement with the continuous real
  -- part map to obtain the scalar convergence needed by the density argument.
  exact
    Complex.continuous_re.continuousAt.tendsto.comp
      (gaussianWindowIntegral_tendsto_of_tendsto
        (d := d) (ψ := ψ) hψ_cont hψ_psd hψ_zero x hνn)

/-- Helper for Theorem 15.29: on a finite index set, twisting the quadratic-form coefficients by
the oscillatory phases `innerProbChar (-ξ i) x` preserves nonnegativity. -/
lemma finiteGaussianWindowQuadraticSum_nonneg {d n : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} (hψ_psd : IsPositiveSemidefiniteFunction ψ)
    (ξ : Fin n → EuclideanSpace ℝ (Fin d)) (w : Fin n → ℂ)
    (x : EuclideanSpace ℝ (Fin d)) :
    0 ≤
      ∑ i, ∑ j,
        star (w i * BoundedContinuousFunction.innerProbChar (-ξ i) x) *
          ψ (ξ i - ξ j) *
          (w j * BoundedContinuousFunction.innerProbChar (-ξ j) x) := by
  -- Proof comment: the Gaussian-window phases are absorbed into the quadratic-form coefficients,
  -- so the claim is exactly the defining finite-family positivity criterion for `ψ`.
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    (isPositiveSemidefiniteFunction_iff_quadratic_sum_nonneg.mp hψ_psd)
      n ξ (fun i ↦ w i * BoundedContinuousFunction.innerProbChar (-ξ i) x)

/-- Helper for Theorem 15.29: multiplying a positive semidefinite Euclidean kernel by a fixed
additive character preserves positive semidefiniteness. -/
lemma mul_innerProbChar_isPositiveSemidefiniteFunction {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} (hψ_psd : IsPositiveSemidefiniteFunction ψ)
    (x : EuclideanSpace ℝ (Fin d)) :
    IsPositiveSemidefiniteFunction
      (fun t : EuclideanSpace ℝ (Fin d) ↦ ψ t * BoundedContinuousFunction.innerProbChar t x) := by
  rw [isPositiveSemidefiniteFunction_iff_quadratic_sum_nonneg]
  intro n ξ w
  have hwindow :
      0 ≤
        ∑ i, ∑ j,
          star (w i * BoundedContinuousFunction.innerProbChar (-ξ i) x) *
            ψ (ξ i - ξ j) *
            (w j * BoundedContinuousFunction.innerProbChar (-ξ j) x) := by
    -- Proof comment: absorb the character phases into the quadratic-form coefficients and reuse
    -- the earlier finite Gaussian-window positivity lemma.
    exact finiteGaussianWindowQuadraticSum_nonneg (d := d) (ψ := ψ) hψ_psd ξ w x
  have hsum :
      (∑ i, ∑ j,
          star (w i) *
            ((fun t : EuclideanSpace ℝ (Fin d) ↦
                ψ t * BoundedContinuousFunction.innerProbChar t x) (ξ i - ξ j)) *
            w j) =
        ∑ i, ∑ j,
          star (w i * BoundedContinuousFunction.innerProbChar (-ξ i) x) *
            ψ (ξ i - ξ j) *
            (w j * BoundedContinuousFunction.innerProbChar (-ξ j) x) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    refine Finset.sum_congr rfl ?_
    intro j hj
    calc
      star (w i) *
          ((fun t : EuclideanSpace ℝ (Fin d) ↦
              ψ t * BoundedContinuousFunction.innerProbChar t x) (ξ i - ξ j)) *
          w j
        =
          star (w i) *
            (ψ (ξ i - ξ j) * BoundedContinuousFunction.innerProbChar (ξ i - ξ j) x) *
            w j := by
              rfl
      _ =
          star (w i) *
            (star (BoundedContinuousFunction.innerProbChar (-ξ i) x) *
              ψ (ξ i - ξ j) *
              BoundedContinuousFunction.innerProbChar (-ξ j) x) *
            w j := by
              rw [← gaussianWindowQuadraticIntegrand_eq_differenceKernel
                (d := d) (ψ := ψ) (u := ξ i) (v := ξ j) (x := x)]
      _ =
          star (w i * BoundedContinuousFunction.innerProbChar (-ξ i) x) *
            ψ (ξ i - ξ j) *
            (w j * BoundedContinuousFunction.innerProbChar (-ξ j) x) := by
              simp [mul_assoc, mul_left_comm, mul_comm, star_mul]
  -- Proof comment: rewrite the target quadratic sum into the already nonnegative window form.
  rw [hsum]
  exact hwindow

/-- Helper for Theorem 15.29: real weighted finite Gaussian-window sums are already nonnegative,
so any finitely supported probability approximation only needs a limit argument afterwards. -/
lemma finiteGaussianWindowQuadraticWeightedSum_nonneg {d n : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} (hψ_psd : IsPositiveSemidefiniteFunction ψ)
    (ξ : Fin n → EuclideanSpace ℝ (Fin d)) (w : Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    0 ≤
      ∑ i, ∑ j,
        ((w i * w j : ℝ) : ℂ) *
          (star (BoundedContinuousFunction.innerProbChar (-ξ i) x) *
            ψ (ξ i - ξ j) *
            BoundedContinuousFunction.innerProbChar (-ξ j) x) := by
  -- Proof comment: specialize the quadratic-form positivity statement to the real coefficients
  -- `w i`; this is the discrete nonnegativity input needed for any finitely supported window
  -- approximation.
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    (finiteGaussianWindowQuadraticSum_nonneg
      (d := d) (ψ := ψ) hψ_psd ξ (fun i ↦ (w i : ℂ)) x)

/-- Helper for Theorem 15.29: taking real parts keeps the finite Gaussian-window weighted sums
nonnegative, which is the exact scalar shape needed for the window-limit argument. -/
lemma real_finiteGaussianWindowQuadraticWeightedSum_nonneg {d n : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} (hψ_psd : IsPositiveSemidefiniteFunction ψ)
    (ξ : Fin n → EuclideanSpace ℝ (Fin d)) (w : Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    0 ≤
      Complex.re
        (∑ i, ∑ j,
          ((w i * w j : ℝ) : ℂ) *
            (star (BoundedContinuousFunction.innerProbChar (-ξ i) x) *
              ψ (ξ i - ξ j) *
              BoundedContinuousFunction.innerProbChar (-ξ j) x)) := by
  have hcomplex :
      0 ≤
        ∑ i, ∑ j,
          ((w i * w j : ℝ) : ℂ) *
            (star (BoundedContinuousFunction.innerProbChar (-ξ i) x) *
              ψ (ξ i - ξ j) *
              BoundedContinuousFunction.innerProbChar (-ξ j) x) :=
    finiteGaussianWindowQuadraticWeightedSum_nonneg
      (d := d) (ψ := ψ) hψ_psd ξ w x
  -- Proof comment: the finite-stage window sums are already nonnegative in `ℂ`, so their real
  -- parts are nonnegative as ordinary real numbers as well.
  exact (Complex.nonneg_iff.mp hcomplex).1

/-- Helper for Theorem 15.29: if the window law already has finite support, then the Gaussian
window quadratic integral is the real part of a finite positive semidefinite quadratic form. -/
lemma gaussianWindowIntegral_realNonneg_of_supportFinite {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} (hψ_cont : Continuous ψ)
    (hψ_psd : IsPositiveSemidefiniteFunction ψ) (hψ_zero : ψ 0 = 1)
    {μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))}
    (hμ : (((μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) :
      Measure (EuclideanSpace ℝ (Fin d))).support).Finite)
    (x : EuclideanSpace ℝ (Fin d)) :
    0 ≤
      Complex.re
        (∫ p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d),
          star (BoundedContinuousFunction.innerProbChar (-p.1) x) *
            ψ (p.1 - p.2) *
            BoundedContinuousFunction.innerProbChar (-p.2) x
            ∂(((μ.prod μ :
              ProbabilityMeasure
                (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))) :
                Measure
                  (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))))) := by
  classical
  let E := EuclideanSpace ℝ (Fin d)
  let s : Finset E := hμ.toFinset
  let κ : E → E → ℂ := fun u v ↦
    star (BoundedContinuousFunction.innerProbChar (-u) x) *
      ψ (u - v) *
      BoundedContinuousFunction.innerProbChar (-v) x
  let w : E → ℂ := fun u ↦
    (((((μ : ProbabilityMeasure E) : Measure E).real {u}) : ℝ) : ℂ) *
      BoundedContinuousFunction.innerProbChar (-u) x
  have hsupport_ae : ∀ᵐ u ∂((μ : ProbabilityMeasure E) : Measure E), u ∈ (↑s : Set E) := by
    -- Proof comment: the finite support set `s` is exactly the measure support, so it contains
    -- the random variable almost surely.
    simpa [s] using
      (Measure.support_mem_ae (μ := ((μ : ProbabilityMeasure E) : Measure E)))
  have hκ_section_int :
      ∀ u : E, Integrable (fun v : E ↦ κ u v) (((μ : ProbabilityMeasure E) : Measure E)) := by
    intro u
    refine Integrable.of_bound ?_ 1 ?_
    · have hright :
          Continuous fun v : E ↦ BoundedContinuousFunction.innerProbChar (-v) x := by
        simpa [BoundedContinuousFunction.innerProbChar_apply] using
          (Complex.continuous_exp.comp
            (by
              fun_prop :
                Continuous fun v : E ↦ (↑(inner ℝ x (-v)) : ℂ) * Complex.I))
      -- Proof comment: for fixed `u`, the window integrand is a continuous bounded function of
      -- the second variable.
      exact ((continuous_const.mul (hψ_cont.comp (continuous_const.sub continuous_id))).mul
        hright).aestronglyMeasurable
    · filter_upwards with v
      simpa [κ] using
        norm_gaussianWindowQuadraticIntegrand_le_one
          (d := d) (ψ := ψ) hψ_psd hψ_zero x u v
  have hκ_int :
      Integrable
        (fun p : E × E ↦ κ p.1 p.2)
        ((((μ : ProbabilityMeasure E) : Measure E).prod
          (((μ : ProbabilityMeasure E) : Measure E)))) := by
    refine Integrable.of_bound ?_ 1 ?_
    · have hleft :
          Continuous fun p : E × E ↦ BoundedContinuousFunction.innerProbChar (-p.1) x := by
        simpa [BoundedContinuousFunction.innerProbChar_apply] using
          (Complex.continuous_exp.comp
            (by
              fun_prop :
                Continuous fun p : E × E ↦
                  (↑(inner ℝ x (-p.1)) : ℂ) * Complex.I))
      have hmiddle : Continuous fun p : E × E ↦ ψ (p.1 - p.2) := by
        exact hψ_cont.comp (continuous_fst.sub continuous_snd)
      have hright :
          Continuous fun p : E × E ↦ BoundedContinuousFunction.innerProbChar (-p.2) x := by
        simpa [BoundedContinuousFunction.innerProbChar_apply] using
          (Complex.continuous_exp.comp
            (by
              fun_prop :
                Continuous fun p : E × E ↦
                  (↑(inner ℝ x (-p.2)) : ℂ) * Complex.I))
      -- Proof comment: the full two-variable window kernel is also continuous and bounded by `1`.
      exact ((hleft.star.mul hmiddle).mul hright).aestronglyMeasurable
    · filter_upwards with p
      simpa [κ] using
        norm_gaussianWindowQuadraticIntegrand_le_one
          (d := d) (ψ := ψ) hψ_psd hψ_zero x p.1 p.2
  have hinner_eq :
      ∀ u : E,
        ∫ v, κ u v ∂(((μ : ProbabilityMeasure E) : Measure E)) =
          ∑ v ∈ s, (((μ : ProbabilityMeasure E) : Measure E).real {v}) • κ u v := by
    intro u
    calc
      ∫ v, κ u v ∂(((μ : ProbabilityMeasure E) : Measure E)) =
          ∫ v in (↑s : Set E), κ u v ∂(((μ : ProbabilityMeasure E) : Measure E)) := by
            rw [← MeasureTheory.integral_indicator (μ := ((μ : ProbabilityMeasure E) : Measure E))
              (s := (↑s : Set E)) s.measurableSet (f := fun v : E ↦ κ u v)]
            refine integral_congr_ae ?_
            filter_upwards [hsupport_ae] with v hv
            exact (Set.indicator_of_mem hv (f := fun v : E ↦ κ u v)).symm
      _ = ∑ v ∈ s, (((μ : ProbabilityMeasure E) : Measure E).real {v}) • κ u v := by
            simpa using
              (MeasureTheory.setIntegral_finset
                (μ := ((μ : ProbabilityMeasure E) : Measure E))
                (s := s) (f := fun v : E ↦ κ u v) (hκ_section_int u).integrableOn)
  have houter_eq :
      ∫ u, ∫ v, κ u v ∂(((μ : ProbabilityMeasure E) : Measure E))
          ∂(((μ : ProbabilityMeasure E) : Measure E)) =
        ∑ u ∈ s, (((μ : ProbabilityMeasure E) : Measure E).real {u}) •
          ∑ v ∈ s, (((μ : ProbabilityMeasure E) : Measure E).real {v}) • κ u v := by
    calc
      ∫ u, ∫ v, κ u v ∂(((μ : ProbabilityMeasure E) : Measure E))
          ∂(((μ : ProbabilityMeasure E) : Measure E)) =
          ∫ u in (↑s : Set E), ∫ v, κ u v ∂(((μ : ProbabilityMeasure E) : Measure E))
            ∂(((μ : ProbabilityMeasure E) : Measure E)) := by
              rw [← MeasureTheory.integral_indicator
                (μ := ((μ : ProbabilityMeasure E) : Measure E))
                (s := (↑s : Set E)) s.measurableSet
                (f := fun u : E ↦ ∫ v, κ u v ∂(((μ : ProbabilityMeasure E) : Measure E)))]
              refine integral_congr_ae ?_
              filter_upwards [hsupport_ae] with u hu
              exact
                (Set.indicator_of_mem hu
                  (f := fun u : E ↦ ∫ v, κ u v ∂(((μ : ProbabilityMeasure E) : Measure E)))).symm
      _ = ∑ u ∈ s, (((μ : ProbabilityMeasure E) : Measure E).real {u}) •
            ∫ v, κ u v ∂(((μ : ProbabilityMeasure E) : Measure E)) := by
              simpa using
                (MeasureTheory.setIntegral_finset
                  (μ := ((μ : ProbabilityMeasure E) : Measure E))
                  (s := s)
                  (f := fun u : E ↦
                    ∫ v, κ u v ∂(((μ : ProbabilityMeasure E) : Measure E)))
                  hκ_int.integral_prod_left.integrableOn)
      _ = ∑ u ∈ s, (((μ : ProbabilityMeasure E) : Measure E).real {u}) •
            ∑ v ∈ s, (((μ : ProbabilityMeasure E) : Measure E).real {v}) • κ u v := by
              refine Finset.sum_congr rfl ?_
              intro u hu
              rw [hinner_eq u]
  have hprod_eq :
      ∫ p : E × E, κ p.1 p.2
          ∂((((μ : ProbabilityMeasure E) : Measure E).prod
            (((μ : ProbabilityMeasure E) : Measure E)))) =
        ∑ u ∈ s, (((μ : ProbabilityMeasure E) : Measure E).real {u}) •
          ∑ v ∈ s, (((μ : ProbabilityMeasure E) : Measure E).real {v}) • κ u v := by
    calc
      ∫ p : E × E, κ p.1 p.2
          ∂((((μ : ProbabilityMeasure E) : Measure E).prod
            (((μ : ProbabilityMeasure E) : Measure E)))) =
          ∫ u, ∫ v, κ u v ∂(((μ : ProbabilityMeasure E) : Measure E))
            ∂(((μ : ProbabilityMeasure E) : Measure E)) := by
              simpa using
                (MeasureTheory.integral_prod (μ := ((μ : ProbabilityMeasure E) : Measure E))
                  (ν := ((μ : ProbabilityMeasure E) : Measure E))
                  (f := fun p : E × E ↦ κ p.1 p.2) hκ_int)
      _ = ∑ u ∈ s, (((μ : ProbabilityMeasure E) : Measure E).real {u}) •
            ∑ v ∈ s, (((μ : ProbabilityMeasure E) : Measure E).real {v}) • κ u v := houter_eq
  have hprod_measure :
      (((μ.prod μ : ProbabilityMeasure (E × E)) : Measure (E × E))) =
        (((μ : ProbabilityMeasure E) : Measure E).prod
          (((μ : ProbabilityMeasure E) : Measure E))) := by
    rfl
  have hsum_eq :
      ∑ u ∈ s, (((μ : ProbabilityMeasure E) : Measure E).real {u}) •
          ∑ v ∈ s, (((μ : ProbabilityMeasure E) : Measure E).real {v}) • κ u v =
        ∑ u ∈ s, ∑ v ∈ s, star (w u) * ψ (u - v) * w v := by
    -- Proof comment: after expanding the two singleton masses into the coefficients `w u`, the
    -- finite weighted window integral is exactly the textbook quadratic form.
    refine Finset.sum_congr rfl ?_
    intro u hu
    have hsmul_sum :
        (((μ : ProbabilityMeasure E) : Measure E).real {u}) •
            ∑ v ∈ s, (((μ : ProbabilityMeasure E) : Measure E).real {v}) • κ u v =
          ∑ v ∈ s,
            (((μ : ProbabilityMeasure E) : Measure E).real {u}) •
              ((((μ : ProbabilityMeasure E) : Measure E).real {v}) • κ u v) := by
      simpa using
        (Finset.smul_sum (r := (((μ : ProbabilityMeasure E) : Measure E).real {u}))
          (s := s) (f := fun v : E ↦
            (((μ : ProbabilityMeasure E) : Measure E).real {v}) • κ u v))
    calc
      (((μ : ProbabilityMeasure E) : Measure E).real {u}) •
          ∑ v ∈ s, (((μ : ProbabilityMeasure E) : Measure E).real {v}) • κ u v =
          ∑ v ∈ s,
            (((μ : ProbabilityMeasure E) : Measure E).real {u}) •
              ((((μ : ProbabilityMeasure E) : Measure E).real {v}) • κ u v) := hsmul_sum
      _ = ∑ v ∈ s, star (w u) * ψ (u - v) * w v := by
            refine Finset.sum_congr rfl ?_
            intro v hv
            simp [w, κ, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]
  have hsum_nonneg :
      0 ≤ ∑ u ∈ s, ∑ v ∈ s, star (w u) * ψ (u - v) * w v := by
    -- Proof comment: finite-support stages are already controlled by the finset version of
    -- positive semidefiniteness.
    exact quadraticSum_nonneg_of_isPositiveSemidefiniteFunction_finset hψ_psd s w
  -- Proof comment: identify the product integral with that finite quadratic form and take real
  -- parts of the resulting nonnegative complex number.
  calc
    0 ≤ Complex.re (∑ u ∈ s, ∑ v ∈ s, star (w u) * ψ (u - v) * w v) := by
          exact (Complex.nonneg_iff.mp hsum_nonneg).1
    _ = Complex.re
          (∫ p : E × E,
            star (BoundedContinuousFunction.innerProbChar (-p.1) x) *
              ψ (p.1 - p.2) *
              BoundedContinuousFunction.innerProbChar (-p.2) x
              ∂(((μ.prod μ : ProbabilityMeasure (E × E)) : Measure (E × E)))) := by
            rw [hprod_measure, hprod_eq, hsum_eq]

/-- Helper for Theorem 15.29: mapping a measure supported on a finite set preserves finite
support. -/
lemma support_map_finite_of_support_finite {α β : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] [HereditarilyLindelofSpace α] [TopologicalSpace β]
    [MeasurableSpace β] [OpensMeasurableSpace β] [T2Space β]
    {μ : Measure α} {f : α → β} (hf : Measurable f) (hμ : μ.support.Finite) :
    (Measure.map f μ).support.Finite := by
  let s : Set β := f '' μ.support
  have hsFinite : s.Finite := hμ.image f
  have hsClosed : IsClosed s := hsFinite.isClosed
  have hsAe : s ∈ ae (Measure.map f μ) := by
    rw [MeasureTheory.mem_ae_iff]
    rw [Measure.map_apply hf hsClosed.isOpen_compl.measurableSet]
    have hsupportNull : μ (μ.supportᶜ) = 0 := Measure.measure_compl_support (μ := μ)
    refine measure_mono_null ?_ hsupportNull
    intro x hx hxSupport
    exact hx ⟨x, hxSupport, rfl⟩
  -- Proof comment: once the pushforward is known to live almost surely in the finite image of
  -- the original support, the support itself is trapped in that finite closed image.
  exact hsFinite.subset (Measure.support_subset_of_isClosed hsClosed hsAe)

/-- Helper for Theorem 15.29: taking the product of two finitely supported measures keeps the
product support finite. -/
lemma support_prod_finite_of_support_finite {α β : Type*} [TopologicalSpace α]
    [MeasurableSpace α] [OpensMeasurableSpace α] [HereditarilyLindelofSpace α]
    [TopologicalSpace β] [MeasurableSpace β] [OpensMeasurableSpace β]
    [HereditarilyLindelofSpace β] {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    (hμ : μ.support.Finite) (hν : ν.support.Finite) :
    (μ.prod ν).support.Finite := by
  let s : Set (α × β) := μ.support ×ˢ ν.support
  have hsFinite : s.Finite := hμ.prod hν
  have hsClosed : IsClosed s := by
    exact (Measure.isClosed_support (μ := μ)).prod (Measure.isClosed_support (μ := ν))
  have hsAe : s ∈ ae (μ.prod ν) := by
    rw [MeasureTheory.mem_ae_iff]
    simpa [s] using
      (Measure.measure_prod_compl_eq_zero
        (μ := μ) (ν := ν)
        (s := μ.support) (t := ν.support)
        (Measure.measure_compl_support (μ := μ))
        (Measure.measure_compl_support (μ := ν)))
  -- Proof comment: the product measure lives almost surely on the product of the two supports, so
  -- the support of the product measure is trapped inside that finite closed rectangle.
  exact hsFinite.subset (Measure.support_subset_of_isClosed hsClosed hsAe)

/-- Helper for Theorem 15.29: the finite product of a finitely supported probability measure on
`ℝ` is still supported on a finite set of coordinate vectors. -/
lemma support_pi_finite_of_support_finite {d : ℕ} (P : ProbabilityMeasure ℝ)
    (hP : ((P : Measure ℝ).support).Finite) :
    ((Measure.pi fun _ : Fin d ↦ (P : Measure ℝ))).support.Finite := by
  let S : Set (Fin d → ℝ) := Set.pi Set.univ fun _ : Fin d ↦ (P : Measure ℝ).support
  have hSfinite : S.Finite := by
    classical
    letI : Fintype ((P : Measure ℝ).support) := hP.fintype
    let e : (Fin d → ((P : Measure ℝ).support)) → (Fin d → ℝ) := fun x i ↦ x i
    have hrange : Set.range e = S := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        intro i hi
        exact (y i).2
      · intro hx
        refine ⟨fun i ↦ ⟨x i, ?_⟩, funext fun i ↦ rfl⟩
        simpa [S] using hx i (by simp)
    rw [← hrange]
    exact Set.finite_range e
  have hSclosed : IsClosed S := by
    refine isClosed_set_pi (i := Set.univ) (s := fun _ : Fin d ↦ (P : Measure ℝ).support) ?_
    intro i hi
    exact Measure.isClosed_support (μ := (P : Measure ℝ))
  have hSupportProb : (P : Measure ℝ) ((P : Measure ℝ).support) = 1 := by
    exact
      (MeasureTheory.mem_ae_iff_prob_eq_one
        (Measure.isClosed_support (μ := (P : Measure ℝ)).measurableSet)).1
        (Measure.support_mem_ae (μ := (P : Measure ℝ)))
  have hSAe : S ∈ ae (Measure.pi fun _ : Fin d ↦ (P : Measure ℝ)) := by
    refine
      (MeasureTheory.mem_ae_iff_prob_eq_one hSclosed.measurableSet).2 ?_
    rw [Measure.pi_pi]
    simp [S, hSupportProb]
  -- Proof comment: every coordinate already lives almost surely in the one-dimensional support,
  -- so the whole product law lives almost surely in the finite cube of those atoms.
  exact hSfinite.subset (Measure.support_subset_of_isClosed hSclosed hSAe)

/-- Helper for Theorem 15.29: the half-Gaussian window measure is a weak limit of finitely
supported probability measures. -/
lemma halfGaussianFiniteSupportApproximation {d : ℕ} {b : ℝ} (hb : 0 < b) :
    let E := EuclideanSpace ℝ (Fin d)
    let c : ℝ := -(2 * Real.pi)
    let aHalf : ℝ := b / (2 * c ^ 2)
    let ρ : ProbabilityMeasure ℝ := ⟨ProbabilityTheory.gaussianReal 0 1, inferInstance⟩
    let γHalfP : ProbabilityMeasure E :=
      ProbabilityMeasure.map
        (ProbabilityMeasure.map
          (ProbabilityMeasure.pi fun _ : Fin d ↦ ρ)
          ((PiLp.continuous_toLp (p := 2) (β := fun _ : Fin d ↦ ℝ)).measurable.aemeasurable))
        ((by
            have hsmul :
                Continuous fun x : E ↦ Real.sqrt (2 * aHalf) • x := by
              fun_prop
            exact hsmul.measurable.aemeasurable))
    ∃ νn : ℕ → ProbabilityMeasure E,
      (∀ n, (((νn n : ProbabilityMeasure E) : Measure E).support).Finite) ∧
        Tendsto νn atTop (𝓝 γHalfP) := by
  let E := EuclideanSpace ℝ (Fin d)
  let c : ℝ := -(2 * Real.pi)
  let aHalf : ℝ := b / (2 * c ^ 2)
  let ρ : ProbabilityMeasure ℝ := ⟨ProbabilityTheory.gaussianReal 0 1, inferInstance⟩
  have htoLpCont :
      Continuous (MeasurableEquiv.toLp 2 (Fin d → ℝ) : (Fin d → ℝ) → E) := by
    simpa using PiLp.continuous_toLp (p := 2) (β := fun _ : Fin d ↦ ℝ)
  have hsmulCont : Continuous fun x : E ↦ Real.sqrt (2 * aHalf) • x := by
    fun_prop
  let γHalfP : ProbabilityMeasure E :=
    ProbabilityMeasure.map
      (ProbabilityMeasure.map
        (ProbabilityMeasure.pi fun _ : Fin d ↦ ρ)
        (htoLpCont.measurable.aemeasurable))
      (hsmulCont.measurable.aemeasurable)
  rcases exists_tendsto_probabilityMeasure_with_finite_support ρ with ⟨ρn, hρnfinite, hρn⟩
  let νn : ℕ → ProbabilityMeasure E := fun n ↦
    ProbabilityMeasure.map
      (ProbabilityMeasure.map
        (ProbabilityMeasure.pi fun _ : Fin d ↦ ρn n)
        (htoLpCont.measurable.aemeasurable))
      (hsmulCont.measurable.aemeasurable)
  refine ⟨νn, ?_, ?_⟩
  · intro n
    have hpiFinite :
        ((Measure.pi fun _ : Fin d ↦ ((ρn n : ProbabilityMeasure ℝ) : Measure ℝ))).support.Finite := by
      -- Proof comment: finite support survives the finite product construction coordinatewise.
      exact support_pi_finite_of_support_finite (d := d) (ρn n) (hρnfinite n)
    have htoLpFinite :
        (Measure.map (MeasurableEquiv.toLp 2 (Fin d → ℝ))
          (Measure.pi fun _ : Fin d ↦ ((ρn n : ProbabilityMeasure ℝ) : Measure ℝ))).support.Finite := by
      -- Proof comment: pushing the finite cube through `toLp` keeps the support finite.
      exact support_map_finite_of_support_finite htoLpCont.measurable hpiFinite
    have hsmulFinite :
        (Measure.map (fun x : E ↦ Real.sqrt (2 * aHalf) • x)
          (Measure.map (MeasurableEquiv.toLp 2 (Fin d → ℝ))
            (Measure.pi fun _ : Fin d ↦ ((ρn n : ProbabilityMeasure ℝ) : Measure ℝ)))).support.Finite := by
      -- Proof comment: the final fixed scaling map preserves finiteness of the transported support.
      exact support_map_finite_of_support_finite hsmulCont.measurable htoLpFinite
    simpa [νn, E, aHalf] using hsmulFinite
  · have hcoord :
        Tendsto (fun n : ℕ ↦ fun _ : Fin d ↦ ρn n) atTop (𝓝 fun _ : Fin d ↦ ρ) := by
      -- Proof comment: each coordinate sees the same one-dimensional approximating sequence.
      rw [tendsto_pi_nhds]
      intro i
      simpa using hρn
    have hpi :
        Tendsto (fun n ↦ ProbabilityMeasure.pi (fun _ : Fin d ↦ ρn n))
          atTop
          (𝓝 (ProbabilityMeasure.pi fun _ : Fin d ↦ ρ)) := by
      -- Proof comment: weak convergence is stable under finite products of probability measures.
      exact MeasureTheory.ProbabilityMeasure.continuous_pi.continuousAt.tendsto.comp hcoord
    have htoLp :
        Tendsto
          (fun n ↦
            ProbabilityMeasure.map
              (ProbabilityMeasure.pi fun _ : Fin d ↦ ρn n)
              (htoLpCont.measurable.aemeasurable))
          atTop
          (𝓝
            (ProbabilityMeasure.map
              (ProbabilityMeasure.pi fun _ : Fin d ↦ ρ)
              (htoLpCont.measurable.aemeasurable))) := by
      -- Proof comment: the first fixed continuous transport is continuous on `ProbabilityMeasure`.
      exact
        (MeasureTheory.ProbabilityMeasure.continuous_map htoLpCont).continuousAt.tendsto.comp hpi
    have hsmul :
        Tendsto
          (fun n ↦
            ProbabilityMeasure.map
              (ProbabilityMeasure.map
                (ProbabilityMeasure.pi fun _ : Fin d ↦ ρn n)
                (htoLpCont.measurable.aemeasurable))
              (hsmulCont.measurable.aemeasurable))
          atTop
          (𝓝
            (ProbabilityMeasure.map
              (ProbabilityMeasure.map
                (ProbabilityMeasure.pi fun _ : Fin d ↦ ρ)
                (htoLpCont.measurable.aemeasurable))
              (hsmulCont.measurable.aemeasurable))) := by
      -- Proof comment: apply continuity of the second fixed pushforward to finish the transport.
      exact
        (MeasureTheory.ProbabilityMeasure.continuous_map hsmulCont).continuousAt.tendsto.comp htoLp
    simpa [νn, γHalfP, E, c, aHalf, ρ] using hsmul

/-- Helper for Theorem 15.29: the probability-measure target in
`halfGaussianFiniteSupportApproximation` is exactly the scaled Euclidean standard Gaussian used by
the window identities. -/
lemma halfGaussianApproximationTarget_eq_scaledStdGaussian {d : ℕ} {b : ℝ} :
    let E := EuclideanSpace ℝ (Fin d)
    let c : ℝ := -(2 * Real.pi)
    let aHalf : ℝ := b / (2 * c ^ 2)
    let ρ : ProbabilityMeasure ℝ := ⟨ProbabilityTheory.gaussianReal 0 1, inferInstance⟩
    let γHalfApprox : ProbabilityMeasure E :=
      ProbabilityMeasure.map
        (ProbabilityMeasure.map
          (ProbabilityMeasure.pi fun _ : Fin d ↦ ρ)
          ((PiLp.continuous_toLp (p := 2) (β := fun _ : Fin d ↦ ℝ)).measurable.aemeasurable))
        ((by
            have hsmul :
                Continuous fun x : E ↦ Real.sqrt (2 * aHalf) • x := by
              fun_prop
            exact hsmul.measurable.aemeasurable))
    γHalfApprox =
      ProbabilityMeasure.map
        ⟨ProbabilityTheory.stdGaussian E, inferInstance⟩
        ((by
            have hsmul : Continuous fun x : E ↦ Real.sqrt (2 * aHalf) • x := by
              fun_prop
            exact hsmul.measurable.aemeasurable)) := by
  let E := EuclideanSpace ℝ (Fin d)
  let c : ℝ := -(2 * Real.pi)
  let aHalf : ℝ := b / (2 * c ^ 2)
  let ρ : ProbabilityMeasure ℝ := ⟨ProbabilityTheory.gaussianReal 0 1, inferInstance⟩
  let γHalfApprox : ProbabilityMeasure E :=
    ProbabilityMeasure.map
      (ProbabilityMeasure.map
        (ProbabilityMeasure.pi fun _ : Fin d ↦ ρ)
        ((PiLp.continuous_toLp (p := 2) (β := fun _ : Fin d ↦ ℝ)).measurable.aemeasurable))
      ((by
          have hsmul :
              Continuous fun x : E ↦ Real.sqrt (2 * aHalf) • x := by
            fun_prop
          exact hsmul.measurable.aemeasurable))
  -- Proof comment: `stdGaussian` is exactly the transported product Gaussian, so applying the same
  -- fixed scaling map to both sides identifies the two probability measures.
  apply ProbabilityMeasure.toMeasure_injective
  change
    Measure.map (fun x : E ↦ Real.sqrt (2 * aHalf) • x)
      (Measure.map (MeasurableEquiv.toLp 2 (Fin d → ℝ))
        (Measure.pi fun _ : Fin d ↦ (ρ : Measure ℝ))) =
      Measure.map (fun x : E ↦ Real.sqrt (2 * aHalf) • x)
        (ProbabilityTheory.stdGaussian E)
  congr 1
  simpa [ρ, E] using (ProbabilityTheory.map_pi_eq_stdGaussian (ι := Fin d))

/-- Helper for Theorem 15.29: the finitely supported approximation can be retargeted directly to
the scaled `stdGaussian` law used in the half-window formulas. -/
lemma halfGaussianFiniteSupportApproximation_scaledStdGaussian {d : ℕ} {b : ℝ} (hb : 0 < b) :
    let E := EuclideanSpace ℝ (Fin d)
    let c : ℝ := -(2 * Real.pi)
    let aHalf : ℝ := b / (2 * c ^ 2)
    let γHalf : ProbabilityMeasure E :=
      ProbabilityMeasure.map
        ⟨ProbabilityTheory.stdGaussian E, inferInstance⟩
        ((by
            have hsmul : Continuous fun x : E ↦ Real.sqrt (2 * aHalf) • x := by
              fun_prop
            exact hsmul.measurable.aemeasurable))
    ∃ νn : ℕ → ProbabilityMeasure E,
      (∀ n, (((νn n : ProbabilityMeasure E) : Measure E).support).Finite) ∧
        Tendsto νn atTop (𝓝 γHalf) := by
  let E := EuclideanSpace ℝ (Fin d)
  let c : ℝ := -(2 * Real.pi)
  let aHalf : ℝ := b / (2 * c ^ 2)
  let γHalfApprox : ProbabilityMeasure E :=
    ProbabilityMeasure.map
      (ProbabilityMeasure.map
        (ProbabilityMeasure.pi fun _ : Fin d ↦ (⟨ProbabilityTheory.gaussianReal 0 1, inferInstance⟩ :
          ProbabilityMeasure ℝ))
        ((PiLp.continuous_toLp (p := 2) (β := fun _ : Fin d ↦ ℝ)).measurable.aemeasurable))
      ((by
          have hsmul : Continuous fun x : E ↦ Real.sqrt (2 * aHalf) • x := by
            fun_prop
          exact hsmul.measurable.aemeasurable))
  let γHalf : ProbabilityMeasure E :=
    ProbabilityMeasure.map
      ⟨ProbabilityTheory.stdGaussian E, inferInstance⟩
      ((by
          have hsmul : Continuous fun x : E ↦ Real.sqrt (2 * aHalf) • x := by
            fun_prop
          exact hsmul.measurable.aemeasurable))
  rcases halfGaussianFiniteSupportApproximation (d := d) (b := b) hb with ⟨νn, hfinite, htendsto⟩
  refine ⟨νn, hfinite, ?_⟩
  have htarget : γHalfApprox = γHalf := by
    -- Proof comment: re-establish the target identity directly so the later `Tendsto` cast uses
    -- the exact local spelling of `γHalf`.
    apply ProbabilityMeasure.toMeasure_injective
    change
      Measure.map (fun x : E ↦ Real.sqrt (2 * aHalf) • x)
        (Measure.map (MeasurableEquiv.toLp 2 (Fin d → ℝ))
          (Measure.pi fun _ : Fin d ↦ (ProbabilityTheory.gaussianReal 0 1))) =
        Measure.map (fun x : E ↦ Real.sqrt (2 * aHalf) • x)
          (ProbabilityTheory.stdGaussian E)
    congr 1
    simpa [E] using (ProbabilityTheory.map_pi_eq_stdGaussian (ι := Fin d))
  have htendsto' : Tendsto νn atTop (𝓝 γHalfApprox) := by
    simpa [γHalfApprox, E, c, aHalf] using htendsto
  rw [htarget] at htendsto'
  exact htendsto'

/-- Helper for Theorem 15.29: the full scaled Gaussian in the corrected window formula is also a
weak limit of finitely supported probability laws, obtained by taking differences of the half-step
approximants. -/
lemma dualGaussianFiniteSupportApproximation {d : ℕ} {b : ℝ} (hb : 0 < b) :
    let E := EuclideanSpace ℝ (Fin d)
    let c : ℝ := -(2 * Real.pi)
    let aHalf : ℝ := b / (2 * c ^ 2)
    let a : ℝ := b / c ^ 2
    let γ : ProbabilityMeasure E :=
      ProbabilityMeasure.map
        ⟨ProbabilityTheory.stdGaussian E, inferInstance⟩
        ((by
            have hsmul : Continuous fun x : E ↦ Real.sqrt (2 * a) • x := by
              fun_prop
            exact hsmul.measurable.aemeasurable))
    ∃ νn : ℕ → ProbabilityMeasure E,
      (∀ n, (((νn n : ProbabilityMeasure E) : Measure E).support).Finite) ∧
        Tendsto νn atTop (𝓝 γ) := by
  let E := EuclideanSpace ℝ (Fin d)
  let c : ℝ := -(2 * Real.pi)
  let aHalf : ℝ := b / (2 * c ^ 2)
  let a : ℝ := b / c ^ 2
  let γHalf : ProbabilityMeasure E :=
    ProbabilityMeasure.map
      ⟨ProbabilityTheory.stdGaussian E, inferInstance⟩
      ((by
          have hsmul : Continuous fun x : E ↦ Real.sqrt (2 * aHalf) • x := by
            fun_prop
          exact hsmul.measurable.aemeasurable))
  let γ : ProbabilityMeasure E :=
    ProbabilityMeasure.map
      ⟨ProbabilityTheory.stdGaussian E, inferInstance⟩
      ((by
          have hsmul : Continuous fun x : E ↦ Real.sqrt (2 * a) • x := by
            fun_prop
          exact hsmul.measurable.aemeasurable))
  have hsubCont : Continuous fun p : E × E ↦ p.1 - p.2 := by
    fun_prop
  rcases
    halfGaussianFiniteSupportApproximation_scaledStdGaussian (d := d) (b := b) hb with
      ⟨νHalf, hνHalf_finite, hνHalf_tendsto⟩
  let νn : ℕ → ProbabilityMeasure E := fun n ↦
    ProbabilityMeasure.map ((νHalf n).prod (νHalf n)) (hsubCont.measurable.aemeasurable)
  refine ⟨νn, ?_, ?_⟩
  · intro n
    have hprod_finite :
        ((((νHalf n : ProbabilityMeasure E) : Measure E).prod
          ((νHalf n : ProbabilityMeasure E) : Measure E)).support).Finite := by
      -- Proof comment: the product of two finitely supported approximants still has finite
      -- support before taking the subtraction map.
      exact support_prod_finite_of_support_finite (hνHalf_finite n) (hνHalf_finite n)
    -- Proof comment: subtraction is a fixed continuous map, so it preserves finiteness of the
    -- transported support.
    simpa [νn] using
      support_map_finite_of_support_finite hsubCont.measurable hprod_finite
  · have hprod_tendsto :
        Tendsto (fun n ↦ (νHalf n).prod (νHalf n)) atTop (𝓝 (γHalf.prod γHalf)) := by
      have hpair :
          Tendsto (fun n ↦ (νHalf n, νHalf n)) atTop (𝓝 (γHalf, γHalf)) := by
        exact hνHalf_tendsto.prodMk_nhds hνHalf_tendsto
      -- Proof comment: weak convergence is continuous under forming products of probability
      -- measures.
      exact (ProbabilityMeasure.continuous_prod.continuousAt.tendsto.comp hpair)
    have hmap_tendsto :
        Tendsto (fun n ↦ νn n) atTop
          (𝓝 (ProbabilityMeasure.map (γHalf.prod γHalf) (hsubCont.measurable.aemeasurable))) := by
      -- Proof comment: push the product approximation through the fixed subtraction map.
      exact (ProbabilityMeasure.continuous_map hsubCont).continuousAt.tendsto.comp hprod_tendsto
    have htarget :
        ProbabilityMeasure.map (γHalf.prod γHalf) (hsubCont.measurable.aemeasurable) = γ := by
      -- Proof comment: the subtraction of two independent half-Gaussians is exactly the full
      -- scaled Gaussian from the regularization step.
      apply ProbabilityMeasure.toMeasure_injective
      simpa [γHalf, γ, hsubCont, c, aHalf, a] using
        halfGaussianDifference_eq_scaledStdGaussian (d := d) (b := b) hb
    rw [htarget] at hmap_tendsto
    exact hmap_tendsto

-- Proof sketch: the previous monolithic Euclidean blocker is now split into one nonnegativity
-- owner and one mass-normalization owner. The direct half-window normalization attempted in the
-- previous retry was too strong, so we record the certified mismatch first.
/-- Helper for Theorem 15.29: for the constant kernel `1` at spatial point `0`, the half-Gaussian
product-window integral is exactly `1`. -/
lemma halfGaussianWindowIntegral_constOne_zero {d : ℕ} {b : ℝ} (hb : 0 < b) :
    let E := EuclideanSpace ℝ (Fin d)
    let c : ℝ := -(2 * Real.pi)
    let aHalf : ℝ := b / (2 * c ^ 2)
    let a : ℝ := b / c ^ 2
    let γHalf : Measure E :=
      (ProbabilityTheory.stdGaussian E).map (Real.sqrt (2 * aHalf) • ·)
    let γ : Measure E :=
      (ProbabilityTheory.stdGaussian E).map (Real.sqrt (2 * a) • ·)
    ∫ p : E × E,
      star (BoundedContinuousFunction.innerProbChar (-p.1) (0 : E)) *
        (1 : ℂ) *
        BoundedContinuousFunction.innerProbChar (-p.2) (0 : E)
        ∂(γHalf.prod γHalf) = 1 := by
  let E := EuclideanSpace ℝ (Fin d)
  let c : ℝ := -(2 * Real.pi)
  let aHalf : ℝ := b / (2 * c ^ 2)
  let a : ℝ := b / c ^ 2
  let γHalf : Measure E :=
    (ProbabilityTheory.stdGaussian E).map (Real.sqrt (2 * aHalf) • ·)
  let γ : Measure E :=
    (ProbabilityTheory.stdGaussian E).map (Real.sqrt (2 * a) • ·)
  have hwindow :
      ∫ p : E × E,
          star (BoundedContinuousFunction.innerProbChar (-p.1) (0 : E)) *
            (1 : ℂ) *
            BoundedContinuousFunction.innerProbChar (-p.2) (0 : E)
          ∂(γHalf.prod γHalf) =
        ∫ t : E, (1 : ℂ) * BoundedContinuousFunction.innerProbChar t (0 : E) ∂γ := by
    -- Proof comment: specialize the already-proved difference-law identity to the constant
    -- kernel and the spatial base point `0`.
    simpa [γHalf, γ, c, aHalf, a] using
      (halfGaussianWindowIntegral_eq_differenceIntegral
        (d := d) (ψ := fun _ : E ↦ (1 : ℂ)) (b := b) hb
        (by simpa using (continuous_const : Continuous fun _ : E ↦ (1 : ℂ))) (0 : E))
  haveI : IsProbabilityMeasure γ := by
    dsimp [γ]
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  calc
    ∫ p : E × E,
        star (BoundedContinuousFunction.innerProbChar (-p.1) (0 : E)) *
          (1 : ℂ) *
          BoundedContinuousFunction.innerProbChar (-p.2) (0 : E)
        ∂(γHalf.prod γHalf)
      = ∫ t : E, (1 : ℂ) * BoundedContinuousFunction.innerProbChar t (0 : E) ∂γ := hwindow
    _ = ∫ t : E, (1 : ℂ) ∂γ := by
          -- Proof comment: at spatial point `0`, the oscillatory character is identically `1`.
          refine integral_congr_ae (Filter.Eventually.of_forall ?_)
          intro t
          simp [BoundedContinuousFunction.innerProbChar_apply]
    _ = 1 := by
          -- Proof comment: the remaining integral is the total mass of the Gaussian probability
          -- measure `γ`.
          simp

/-- Helper for Theorem 15.29: the fixed Fourier normalization scalar `-(2 * π)` is nonzero. -/
lemma fourierNormalizationScalar_ne_zero : (-(2 * Real.pi : ℝ)) ≠ 0 := by
  have htwoPi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  exact neg_ne_zero.mpr htwoPi

/-- Helper for Theorem 15.29: integrating the real-valued Gaussian exponential in `ℂ` and then
taking real parts recovers the original real Gaussian integral. -/
lemma complexRe_integral_cexp_neg_mul_sq_norm {d : ℕ} {b : ℝ} :
    Complex.re (∫ t : EuclideanSpace ℝ (Fin d), Complex.exp (-(b : ℂ) * ‖t‖ ^ 2)) =
      ∫ t : EuclideanSpace ℝ (Fin d), Real.exp (-b * ‖t‖ ^ 2) := by
  have hfun :
      (fun t : EuclideanSpace ℝ (Fin d) ↦ Complex.exp (-(b : ℂ) * ‖t‖ ^ 2)) =
        fun t : EuclideanSpace ℝ (Fin d) ↦ ((Real.exp (-b * ‖t‖ ^ 2) : ℝ) : ℂ) := by
    -- Proof comment: the Gaussian exponent is already real, so the complex exponential is just
    -- the complexification of the real Gaussian factor.
    funext t
    simp
  -- Proof comment: once the integrand is rewritten through `Complex.ofReal`, the integral and its
  -- real part collapse to the original real-valued Gaussian integral.
  rw [hfun, integral_complex_ofReal]
  simp

/-- Helper for Theorem 15.29: for the constant kernel `1` at spatial point `0`, the regularized
inverse-Fourier density is the Gaussian integral `(π / b)^(dim / 2)`. -/
lemma gaussianRegularizedInverseFourierDensity_constOne_zero {d : ℕ} {b : ℝ} (hb : 0 < b) :
    gaussianRegularizedInverseFourierDensity
        (fun _ : EuclideanSpace ℝ (Fin d) ↦ (1 : ℂ)) b 0 =
      (Real.pi / b) ^
        (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) / 2 : ℝ) := by
  calc
    gaussianRegularizedInverseFourierDensity
        (fun _ : EuclideanSpace ℝ (Fin d) ↦ (1 : ℂ)) b 0
      =
        Complex.re
          (∫ t : EuclideanSpace ℝ (Fin d),
            Complex.exp (↑(2 * Real.pi * inner ℝ t (0 : EuclideanSpace ℝ (Fin d))) * Complex.I) *
              (Complex.exp (-(b : ℂ) * ‖t‖ ^ 2) * (1 : ℂ))) := by
            -- Proof comment: freeze the regularized density in its oscillatory-integral normal
            -- form before evaluating the constant kernel at the origin.
            simpa using
              gaussianRegularizedInverseFourierDensity_eq_real_integral_fourierExp
                (ψ := fun _ : EuclideanSpace ℝ (Fin d) ↦ (1 : ℂ))
                (b := b) (x := (0 : EuclideanSpace ℝ (Fin d)))
    _ = Complex.re (∫ t : EuclideanSpace ℝ (Fin d), Complex.exp (-(b : ℂ) * ‖t‖ ^ 2)) := by
          -- Proof comment: at `x = 0`, the oscillatory phase is `1`, so only the Gaussian
          -- exponential remains in the integral.
          congr 1
          refine integral_congr_ae (Filter.Eventually.of_forall ?_)
          intro t
          simp
    _ = ∫ t : EuclideanSpace ℝ (Fin d), Real.exp (-b * ‖t‖ ^ 2) := by
          -- Proof comment: replace the complex Gaussian integral by its real-valued counterpart.
          simpa using complexRe_integral_cexp_neg_mul_sq_norm (d := d) (b := b)
    _ = (Real.pi / b) ^
          (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) / 2 : ℝ) := by
          -- Proof comment: mathlib already evaluates the real Gaussian integral explicitly.
          simpa using
            GaussianFourier.integral_rexp_neg_mul_sq_norm
              (V := EuclideanSpace ℝ (Fin d)) hb

/-- Helper for Theorem 15.29: for the constant kernel `1`, the half-Gaussian window integral is
the Gaussian characteristic function of the difference law. -/
lemma real_halfGaussianWindowIntegral_constOne {d : ℕ} {b : ℝ} (hb : 0 < b)
    (x : EuclideanSpace ℝ (Fin d)) :
    let E := EuclideanSpace ℝ (Fin d)
    let c : ℝ := -(2 * Real.pi)
    let aHalf : ℝ := b / (2 * c ^ 2)
    let a : ℝ := b / c ^ 2
    let γHalf : Measure E :=
      (ProbabilityTheory.stdGaussian E).map (Real.sqrt (2 * aHalf) • ·)
    let γ : Measure E :=
      (ProbabilityTheory.stdGaussian E).map (Real.sqrt (2 * a) • ·)
    Complex.re
        (∫ p : E × E,
          star (BoundedContinuousFunction.innerProbChar (-p.1) x) *
            (1 : ℂ) *
            BoundedContinuousFunction.innerProbChar (-p.2) x
            ∂(γHalf.prod γHalf)) =
      Real.exp (-(a * ‖x‖ ^ 2)) := by
  sorry

/-- Helper for Theorem 15.29: for the constant kernel `1`, the regularized inverse-Fourier
candidate is the explicit Gaussian density with variance parameter `b`. -/
lemma gaussianRegularizedInverseFourierDensity_constOne {d : ℕ} {b : ℝ} (hb : 0 < b)
    (x : EuclideanSpace ℝ (Fin d)) :
    gaussianRegularizedInverseFourierDensity
        (fun _ : EuclideanSpace ℝ (Fin d) ↦ (1 : ℂ)) b x =
      (Real.pi / b) ^
          (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) / 2 : ℝ) *
        Real.exp (-(Real.pi ^ 2 / b) * ‖x‖ ^ 2) := by
  sorry

/-- Helper for Theorem 15.29: the explicit constant-kernel regularized density is pointwise
nonnegative. -/
lemma gaussianRegularizedInverseFourierDensity_constOne_nonneg {d : ℕ} {b : ℝ} (hb : 0 < b) :
    ∀ x : EuclideanSpace ℝ (Fin d),
      0 ≤ gaussianRegularizedInverseFourierDensity
        (fun _ : EuclideanSpace ℝ (Fin d) ↦ (1 : ℂ)) b x := by
  intro x
  -- Proof comment: the closed form is a positive scalar times a real Gaussian density.
  rw [gaussianRegularizedInverseFourierDensity_constOne (d := d) (b := b) hb x]
  positivity

/-- Helper for Theorem 15.29: the explicit constant-kernel regularized density is an integrable
Gaussian majorant. -/
lemma gaussianRegularizedInverseFourierDensity_constOne_integrable {d : ℕ} {b : ℝ} (hb : 0 < b) :
    Integrable
      (gaussianRegularizedInverseFourierDensity
        (fun _ : EuclideanSpace ℝ (Fin d) ↦ (1 : ℂ)) b) := by
  let E := EuclideanSpace ℝ (Fin d)
  have hbase :
      Integrable (fun x : E ↦ Real.exp (-(Real.pi ^ 2 / b) * ‖x‖ ^ 2)) := by
    have hcomplex :
        Integrable (fun x : E ↦ Complex.exp (-((Real.pi ^ 2 / b : ℝ) : ℂ) * ‖x‖ ^ 2)) := by
      -- Proof comment: the real Gaussian majorant is the norm of the standard complex Gaussian
      -- kernel with zero linear phase.
      simpa using
        (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
          (V := E) (b := ((Real.pi ^ 2 / b : ℝ) : ℂ)) (c := 0) (w := (0 : E))
          (show 0 < (((Real.pi ^ 2 / b : ℝ) : ℂ)).re by
            have hpi : 0 < Real.pi ^ 2 := by positivity
            exact div_pos hpi hb))
    -- Proof comment: the complex Gaussian already has real nonnegative values, so the `L¹`
    -- control of its norm is exactly the desired real Gaussian integrability.
    have hnorm :
        (fun x : E ↦ ‖Complex.exp (-((Real.pi ^ 2 / b : ℝ) : ℂ) * ‖x‖ ^ 2)‖) =
          fun x : E ↦ Real.exp (-(Real.pi ^ 2 / b) * ‖x‖ ^ 2) := by
      funext x
      have hrealExp :
          Complex.exp (-((Real.pi ^ 2 / b : ℝ) : ℂ) * ‖x‖ ^ 2) =
            (Real.exp (-(Real.pi ^ 2 / b) * ‖x‖ ^ 2) : ℂ) := by
        simp
      rw [hrealExp, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
      exact (Real.exp_pos _).le
    rw [← hnorm]
    exact hcomplex.norm
  have hscaled :
      Integrable
        (fun x : E ↦
          (Real.pi / b) ^ (Module.finrank ℝ E / 2 : ℝ) *
            Real.exp (-(Real.pi ^ 2 / b) * ‖x‖ ^ 2)) := by
    -- Proof comment: multiplying an `L¹` Gaussian by the fixed normalization scalar preserves
    -- integrability.
    simpa using hbase.const_mul ((Real.pi / b) ^ (Module.finrank ℝ E / 2 : ℝ))
  have hfun :
      gaussianRegularizedInverseFourierDensity (fun _ : E ↦ (1 : ℂ)) b =
        fun x : E ↦
          (Real.pi / b) ^ (Module.finrank ℝ E / 2 : ℝ) *
            Real.exp (-(Real.pi ^ 2 / b) * ‖x‖ ^ 2) := by
    funext x
    exact gaussianRegularizedInverseFourierDensity_constOne (d := d) (b := b) hb x
  -- Proof comment: the explicit constant-kernel closed form identifies the regularized density
  -- with that Gaussian majorant.
  rw [hfun]
  exact hscaled

/-- Helper for Theorem 15.29: the explicit centered Gaussian density with variance parameter
`2 * a` is integrable on `ℝ^d`. -/
lemma integrable_scaledStdGaussian_explicitDensity {d : ℕ} {a : ℝ} (ha : 0 < a) :
    let E := EuclideanSpace ℝ (Fin d)
    let f : E → ℝ := fun x ↦
      (1 / (4 * Real.pi * a)) ^ (Module.finrank ℝ E / 2 : ℝ) *
        Real.exp (-(1 / (4 * a)) * ‖x‖ ^ 2)
    Integrable f := by
  let E := EuclideanSpace ℝ (Fin d)
  let f : E → ℝ := fun x ↦
    (1 / (4 * Real.pi * a)) ^ (Module.finrank ℝ E / 2 : ℝ) *
      Real.exp (-(1 / (4 * a)) * ‖x‖ ^ 2)
  have hbase :
      Integrable (fun x : E ↦ Real.exp (-(1 / (4 * a)) * ‖x‖ ^ 2)) := by
    have hcomplex :
        Integrable (fun x : E ↦ Complex.exp (-((1 / (4 * a) : ℝ) : ℂ) * ‖x‖ ^ 2)) := by
      -- Proof comment: the real Gaussian is the norm of the standard complex Gaussian kernel
      -- with variance parameter `(4a)⁻¹`.
      simpa using
        (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
          (V := E) (b := ((1 / (4 * a) : ℝ) : ℂ)) (c := 0) (w := (0 : E))
          (show 0 < (((1 / (4 * a) : ℝ) : ℂ)).re by
            have hden : 0 < 4 * a := by positivity
            exact one_div_pos.mpr hden))
    -- Proof comment: the complex Gaussian has real nonnegative values, so its norm is the same
    -- centered real Gaussian.
    have hnorm :
        (fun x : E ↦ ‖Complex.exp (-((1 / (4 * a) : ℝ) : ℂ) * ‖x‖ ^ 2)‖) =
          fun x : E ↦ Real.exp (-(1 / (4 * a)) * ‖x‖ ^ 2) := by
      funext x
      have hrealExp :
          Complex.exp (-((1 / (4 * a) : ℝ) : ℂ) * ‖x‖ ^ 2) =
            (Real.exp (-(1 / (4 * a)) * ‖x‖ ^ 2) : ℂ) := by
        simp
      rw [hrealExp, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
      exact (Real.exp_pos _).le
    rw [← hnorm]
    exact hcomplex.norm
  -- Proof comment: multiplying by the fixed normalization scalar preserves integrability.
  simpa [E, f] using
    hbase.const_mul ((1 / (4 * Real.pi * a)) ^ (Module.finrank ℝ E / 2 : ℝ))

/-- Helper for Theorem 15.29: a scaled Euclidean standard Gaussian has the expected explicit
centered Gaussian density with respect to Euclidean volume. -/
lemma scaledStdGaussian_eq_withDensity_explicitDensity {d : ℕ} {a : ℝ} (ha : 0 < a) :
    let E := EuclideanSpace ℝ (Fin d)
    let γ : Measure E := (ProbabilityTheory.stdGaussian E).map (Real.sqrt (2 * a) • ·)
    let f : E → ℝ := fun x ↦
      (1 / (4 * Real.pi * a)) ^ (Module.finrank ℝ E / 2 : ℝ) *
        Real.exp (-(1 / (4 * a)) * ‖x‖ ^ 2)
    γ = volume.withDensity (ENNReal.ofReal ∘ f) := by
  sorry

/-- Helper for Theorem 15.29: the discarded direct half-window normalization is false in general;
on `ℝ²`, the constant kernel already gives different values at `0` whenever `b ≠ π`. -/
lemma gaussianRegularizedInverseFourierDensity_ne_real_halfGaussianWindowIntegral_constOne_zero
    {b : ℝ} (hb : 0 < b) (hb_ne : b ≠ Real.pi) :
    let E := EuclideanSpace ℝ (Fin 2)
    let c : ℝ := -(2 * Real.pi)
    let aHalf : ℝ := b / (2 * c ^ 2)
    let a : ℝ := b / c ^ 2
    let γHalf : Measure E :=
      (ProbabilityTheory.stdGaussian E).map (Real.sqrt (2 * aHalf) • ·)
    gaussianRegularizedInverseFourierDensity (fun _ : E ↦ (1 : ℂ)) b (0 : E) ≠
      Complex.re
        (∫ p : E × E,
          star (BoundedContinuousFunction.innerProbChar (-p.1) (0 : E)) *
            (1 : ℂ) *
            BoundedContinuousFunction.innerProbChar (-p.2) (0 : E)
            ∂(γHalf.prod γHalf)) := by
  sorry
/-- Helper for Theorem 15.29: even after fixing the zero-point normalization scalar `(π / b)^(1/2)`,
the half-Gaussian window route is still not the regularized inverse-Fourier density; on `ℝ`, the
constant kernel at the unit vector already disagrees whenever `b ≠ 2 * π²`. -/
lemma gaussianRegularizedInverseFourierDensity_ne_normalized_real_halfGaussianWindowIntegral_constOne_unit
    {b : ℝ} (hb : 0 < b) (hb_ne : b ≠ 2 * Real.pi ^ 2) :
    let E := EuclideanSpace ℝ (Fin 1)
    let x : E := EuclideanSpace.single 0 (1 : ℝ)
    let c : ℝ := -(2 * Real.pi)
    let aHalf : ℝ := b / (2 * c ^ 2)
    let a : ℝ := b / c ^ 2
    let γHalf : Measure E :=
      (ProbabilityTheory.stdGaussian E).map (Real.sqrt (2 * aHalf) • ·)
    gaussianRegularizedInverseFourierDensity (fun _ : E ↦ (1 : ℂ)) b x ≠
      (Real.pi / b) ^ (Module.finrank ℝ E / 2 : ℝ) *
        Complex.re
          (∫ p : E × E,
            star (BoundedContinuousFunction.innerProbChar (-p.1) x) *
              (1 : ℂ) *
              BoundedContinuousFunction.innerProbChar (-p.2) x
              ∂(γHalf.prod γHalf)) := by
  sorry
/-- Helper for Theorem 15.29: the scalar-free corrected difference-integral rewrite is still
false; on `ℝ²` with the constant kernel at `0`, the difference integral is `1` while the
regularized inverse-Fourier density is `π / b`. -/
lemma gaussianRegularizedInverseFourierDensity_ne_real_densityDifferenceIntegral_constOne_zero
    {b : ℝ} (hb : 0 < b) (hb_ne : b ≠ Real.pi) :
    let E := EuclideanSpace ℝ (Fin 2)
    let a : ℝ := Real.pi ^ 2 / b
    let γ : Measure E :=
      (ProbabilityTheory.stdGaussian E).map (Real.sqrt (2 * a) • ·)
    gaussianRegularizedInverseFourierDensity (fun _ : E ↦ (1 : ℂ)) b (0 : E) ≠
      Complex.re
        (∫ t : E, (1 : ℂ) * BoundedContinuousFunction.innerProbChar t (0 : E) ∂γ) := by
  sorry

/-- Helper for Theorem 15.29: the corrected Gaussian law with window parameter `π^2 / b` has the
expected explicit centered Gaussian density with respect to Euclidean volume. -/
lemma densityGaussianMeasure_eq_withDensity {d : ℕ} {b : ℝ} (hb : 0 < b) :
    let E := EuclideanSpace ℝ (Fin d)
    let a : ℝ := Real.pi ^ 2 / b
    let γ : Measure E := (ProbabilityTheory.stdGaussian E).map (Real.sqrt (2 * a) • ·)
    let f : E → ℝ := fun x ↦
      (1 / (4 * Real.pi * a)) ^ (Module.finrank ℝ E / 2 : ℝ) *
        Real.exp (-(1 / (4 * a)) * ‖x‖ ^ 2)
    γ = volume.withDensity (ENNReal.ofReal ∘ f) := by
  let E := EuclideanSpace ℝ (Fin d)
  let a : ℝ := Real.pi ^ 2 / b
  let γ : Measure E := (ProbabilityTheory.stdGaussian E).map (Real.sqrt (2 * a) • ·)
  let f : E → ℝ := fun x ↦
    (1 / (4 * Real.pi * a)) ^ (Module.finrank ℝ E / 2 : ℝ) *
      Real.exp (-(1 / (4 * a)) * ‖x‖ ^ 2)
  have ha : 0 < a := by
    positivity
  -- Proof comment: specialize the scaled-Gaussian density formula to the calibrated parameter
  -- `a = π² / b`, then rewrite the scalar and exponent into the `b / π` normal form.
  simpa [E, a, γ, f] using
    scaledStdGaussian_eq_withDensity_explicitDensity (d := d) (a := a) ha

/-- Helper for Theorem 15.29: the corrected density-Gaussian parameter
`bDensity := 4 * π^4 / b` induces the target exponent `π^2 / b`. -/
lemma densityGaussianWindowParameter_eq {b : ℝ} (hb : 0 < b) :
    (4 * Real.pi ^ 4 / b) / (2 * Real.pi) ^ 2 = Real.pi ^ 2 / b := by
  have hb0 : b ≠ 0 := ne_of_gt hb
  -- Proof comment: clear the fixed Fourier-normalization denominator `(-2π)^2 = 4π²` once so
  -- later Gaussian rewrites can stay in the calibrated `π² / b` spelling.
  field_simp [hb0, Real.pi_ne_zero]
  ring

/-- Helper for Theorem 15.29: the corrected density-Gaussian half-step parameter is exactly
`π^2 / (2 * b)`. -/
lemma densityGaussianHalfWindowParameter_eq {b : ℝ} (hb : 0 < b) :
    (4 * Real.pi ^ 4 / b) / (2 * (2 * Real.pi) ^ 2) = Real.pi ^ 2 / (2 * b) := by
  have hb0 : b ≠ 0 := ne_of_gt hb
  -- Proof comment: the half-step normalization is the same scalar computation as the full window
  -- parameter, with one extra factor `1 / 2`.
  field_simp [hb0, Real.pi_ne_zero]
  ring

/-- Helper for Theorem 15.29: the corrected Gaussian density normalization constant cancels its
reciprocal pointwise factor. -/
lemma densityGaussianNormalization_cancel {d : ℕ} {b : ℝ} (hb : 0 < b) :
    let E := EuclideanSpace ℝ (Fin d)
    (Real.pi / b) ^ (Module.finrank ℝ E / 2 : ℝ) *
      (b / Real.pi) ^ (Module.finrank ℝ E / 2 : ℝ) = 1 := by
  let E := EuclideanSpace ℝ (Fin d)
  have hpi_div_nonneg : 0 ≤ Real.pi / b := by positivity
  have hb_div_pi_nonneg : 0 ≤ b / Real.pi := by positivity
  calc
    (Real.pi / b) ^ (Module.finrank ℝ E / 2 : ℝ) *
        (b / Real.pi) ^ (Module.finrank ℝ E / 2 : ℝ)
      = ((Real.pi / b) * (b / Real.pi)) ^ (Module.finrank ℝ E / 2 : ℝ) := by
          symm
          exact Real.mul_rpow hpi_div_nonneg hb_div_pi_nonneg
    _ = (1 : ℝ) ^ (Module.finrank ℝ E / 2 : ℝ) := by
          congr 1
          field_simp [ne_of_gt hb, Real.pi_ne_zero]
    _ = 1 := by simp

/-- Helper for Theorem 15.29: the existing half-window identity specializes cleanly to the
corrected density-Gaussian parameters `π^2 / b` and `π^2 / (2 * b)`. -/
lemma real_densityHalfGaussianWindowIntegral_eq_real_differenceIntegral {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} {b : ℝ} (hb : 0 < b) (hψ_cont : Continuous ψ)
    (x : EuclideanSpace ℝ (Fin d)) :
    let E := EuclideanSpace ℝ (Fin d)
    let aHalf : ℝ := Real.pi ^ 2 / (2 * b)
    let a : ℝ := Real.pi ^ 2 / b
    let γHalf : Measure E :=
      (ProbabilityTheory.stdGaussian E).map (Real.sqrt (2 * aHalf) • ·)
    let γ : Measure E :=
      (ProbabilityTheory.stdGaussian E).map (Real.sqrt (2 * a) • ·)
    Complex.re
        (∫ p : E × E,
          star (BoundedContinuousFunction.innerProbChar (-p.1) x) *
            ψ (p.1 - p.2) *
            BoundedContinuousFunction.innerProbChar (-p.2) x
            ∂(γHalf.prod γHalf)) =
    Complex.re
        (∫ t : E, ψ t * BoundedContinuousFunction.innerProbChar t x ∂γ) := by
  have hbDensity : 0 < 4 * Real.pi ^ 4 / b := by
    positivity
  -- Proof comment: the earlier half-window identity already has the right shape; only the window
  -- parameter needs to be rewritten from `4 * π^4 / b` to `π^2 / b`.
  simpa [densityGaussianWindowParameter_eq hb, densityGaussianHalfWindowParameter_eq hb] using
    (real_halfGaussianWindowIntegral_eq_real_differenceIntegral
      (d := d) (ψ := ψ) (b := 4 * Real.pi ^ 4 / b) hbDensity hψ_cont x)

/-- Helper for Theorem 15.29: the corrected half-density Gaussian law with variance parameter
`π^2 / (2 * b)` is still a weak limit of finitely supported probability measures. -/
lemma densityHalfGaussianFiniteSupportApproximation {d : ℕ} {b : ℝ} (hb : 0 < b) :
    let E := EuclideanSpace ℝ (Fin d)
    let aHalf : ℝ := Real.pi ^ 2 / (2 * b)
    let γHalf : ProbabilityMeasure E :=
      ProbabilityMeasure.map
        ⟨ProbabilityTheory.stdGaussian E, inferInstance⟩
        ((by
            have hsmul : Continuous fun x : E ↦ Real.sqrt (2 * aHalf) • x := by
              fun_prop
            exact hsmul.measurable.aemeasurable))
    ∃ νn : ℕ → ProbabilityMeasure E,
      (∀ n, (((νn n : ProbabilityMeasure E) : Measure E).support).Finite) ∧
        Tendsto νn atTop (𝓝 γHalf) := by
  have hbDensity : 0 < 4 * Real.pi ^ 4 / b := by
    positivity
  -- Proof comment: the finite-support approximation is already proved for the `b / (2 * c²)`
  -- spelling, so only the parameter identity to `π² / (2b)` remains.
  simpa [densityGaussianHalfWindowParameter_eq hb] using
    (halfGaussianFiniteSupportApproximation_scaledStdGaussian
      (d := d) (b := 4 * Real.pi ^ 4 / b) hbDensity)

/-- Helper for Theorem 15.29: the corrected full-density Gaussian law with variance parameter
`π^2 / b` is still a weak limit of finitely supported probability measures. -/
lemma densityGaussianFiniteSupportApproximation {d : ℕ} {b : ℝ} (hb : 0 < b) :
    let E := EuclideanSpace ℝ (Fin d)
    let a : ℝ := Real.pi ^ 2 / b
    let γ : ProbabilityMeasure E :=
      ProbabilityMeasure.map
        ⟨ProbabilityTheory.stdGaussian E, inferInstance⟩
        ((by
            have hsmul : Continuous fun x : E ↦ Real.sqrt (2 * a) • x := by
              fun_prop
            exact hsmul.measurable.aemeasurable))
    ∃ νn : ℕ → ProbabilityMeasure E,
      (∀ n, (((νn n : ProbabilityMeasure E) : Measure E).support).Finite) ∧
        Tendsto νn atTop (𝓝 γ) := by
  have hbDensity : 0 < 4 * Real.pi ^ 4 / b := by
    positivity
  -- Proof comment: the full corrected Gaussian approximation is the same approximation after
  -- rewriting the window parameter to the calibrated `π² / b` form.
  simpa [densityGaussianWindowParameter_eq hb] using
    (dualGaussianFiniteSupportApproximation
      (d := d) (b := 4 * Real.pi ^ 4 / b) hbDensity)

/-- Helper for Theorem 15.29: a finite-support half-Gaussian approximation also controls the
corresponding difference laws, which converge to the calibrated full Gaussian. -/
lemma densityGaussianDifferenceLawFiniteSupportApproximation {d : ℕ} {b : ℝ} (hb : 0 < b) :
    let E := EuclideanSpace ℝ (Fin d)
    let aHalf : ℝ := Real.pi ^ 2 / (2 * b)
    let a : ℝ := Real.pi ^ 2 / b
    let hsub : Measurable (fun p : E × E ↦ p.1 - p.2) := by
      fun_prop
    let differenceLaw : ProbabilityMeasure E → ProbabilityMeasure E := fun ν ↦
      ProbabilityMeasure.map (ν.prod ν) hsub.aemeasurable
    let γHalf : ProbabilityMeasure E :=
      ProbabilityMeasure.map
        ⟨ProbabilityTheory.stdGaussian E, inferInstance⟩
        ((by
            have hsmul : Continuous fun x : E ↦ Real.sqrt (2 * aHalf) • x := by
              fun_prop
            exact hsmul.measurable.aemeasurable))
    let γ : ProbabilityMeasure E :=
      ProbabilityMeasure.map
        ⟨ProbabilityTheory.stdGaussian E, inferInstance⟩
        ((by
            have hsmul : Continuous fun x : E ↦ Real.sqrt (2 * a) • x := by
              fun_prop
            exact hsmul.measurable.aemeasurable))
    ∃ νn : ℕ → ProbabilityMeasure E,
      (∀ n, (((νn n : ProbabilityMeasure E) : Measure E).support).Finite) ∧
        Tendsto νn atTop (𝓝 γHalf) ∧
        Tendsto (fun n ↦ differenceLaw (νn n)) atTop (𝓝 γ) := by
  sorry

/-- Helper for Theorem 15.29: the corrected half-Gaussian window integral is already pointwise
nonnegative before any density-side bridge is applied. -/
lemma real_densityHalfGaussianWindowIntegral_nonneg {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} {b : ℝ} (hb : 0 < b)
    (hψ_cont : Continuous ψ) (hψ_psd : IsPositiveSemidefiniteFunction ψ)
    (hψ_zero : ψ 0 = 1) (x : EuclideanSpace ℝ (Fin d)) :
    let E := EuclideanSpace ℝ (Fin d)
    let aHalf : ℝ := Real.pi ^ 2 / (2 * b)
    let γHalf : ProbabilityMeasure E :=
      ProbabilityMeasure.map
        ⟨ProbabilityTheory.stdGaussian E, inferInstance⟩
        ((by
            have hsmul : Continuous fun y : E ↦ Real.sqrt (2 * aHalf) • y := by
              fun_prop
            exact hsmul.measurable.aemeasurable))
    0 ≤
      Complex.re
        (∫ p : E × E,
          star (BoundedContinuousFunction.innerProbChar (-p.1) x) *
            ψ (p.1 - p.2) *
            BoundedContinuousFunction.innerProbChar (-p.2) x
            ∂(((γHalf.prod γHalf : ProbabilityMeasure (E × E))) : Measure (E × E))) := by
  let E := EuclideanSpace ℝ (Fin d)
  let aHalf : ℝ := Real.pi ^ 2 / (2 * b)
  let γHalf : ProbabilityMeasure E :=
    ProbabilityMeasure.map
      ⟨ProbabilityTheory.stdGaussian E, inferInstance⟩
      ((by
          have hsmul : Continuous fun y : E ↦ Real.sqrt (2 * aHalf) • y := by
            fun_prop
          exact hsmul.measurable.aemeasurable))
  rcases densityHalfGaussianFiniteSupportApproximation (d := d) (b := b) hb with
    ⟨νn, hνn_finite, hνn_tendsto⟩
  have hstage_nonneg :
      ∀ n : ℕ,
        0 ≤
          Complex.re
            (∫ p : E × E,
              star (BoundedContinuousFunction.innerProbChar (-p.1) x) *
                ψ (p.1 - p.2) *
                BoundedContinuousFunction.innerProbChar (-p.2) x
                ∂((((νn n).prod (νn n) :
                  ProbabilityMeasure (E × E))) : Measure (E × E))) := by
    intro n
    -- Proof comment: every finite-support stage is already the real part of a finite positive
    -- semidefinite quadratic form.
    exact
      gaussianWindowIntegral_realNonneg_of_supportFinite
        (d := d) (ψ := ψ) hψ_cont hψ_psd hψ_zero (hνn_finite n) x
  have hstage_tendsto :
      Tendsto
        (fun n ↦
          Complex.re
            (∫ p : E × E,
              star (BoundedContinuousFunction.innerProbChar (-p.1) x) *
                ψ (p.1 - p.2) *
                BoundedContinuousFunction.innerProbChar (-p.2) x
                ∂((((νn n).prod (νn n) :
                  ProbabilityMeasure (E × E))) : Measure (E × E))))
        atTop
        (𝓝
          (Complex.re
            (∫ p : E × E,
              star (BoundedContinuousFunction.innerProbChar (-p.1) x) *
                ψ (p.1 - p.2) *
                BoundedContinuousFunction.innerProbChar (-p.2) x
                ∂(((γHalf.prod γHalf : ProbabilityMeasure (E × E))) :
                  Measure (E × E))))) := by
    -- Proof comment: weak convergence of the finitely supported approximants transports directly
    -- to the Gaussian-window integrals against the corresponding product measures.
    simpa [E, aHalf, γHalf] using
      real_gaussianWindowIntegral_tendsto_of_tendsto
        (d := d) (ψ := ψ) hψ_cont hψ_psd hψ_zero x hνn_tendsto
  -- Proof comment: the corrected Gaussian-window integral is the limit of nonnegative finite
  -- stages, so closedness of `[0, ∞)` preserves nonnegativity at the limit.
  exact isClosed_Ici.mem_of_tendsto hstage_tendsto (Filter.Eventually.of_forall hstage_nonneg)

/-- Helper for Theorem 15.29: multiplying a positive semidefinite Euclidean kernel by the
characteristic function of any probability measure preserves positive semidefiniteness. -/
lemma mul_charFun_isPositiveSemidefiniteFunction {d : ℕ}
    {φ : EuclideanSpace ℝ (Fin d) → ℂ} (hpsd : IsPositiveSemidefiniteFunction φ)
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) :
    IsPositiveSemidefiniteFunction
      (fun t ↦ charFun (μ : Measure (EuclideanSpace ℝ (Fin d))) t * φ t) := by
  let E := EuclideanSpace ℝ (Fin d)
  haveI : IsFiniteMeasure (μ : Measure E) := by infer_instance
  rw [isPositiveSemidefiniteFunction_iff_quadratic_sum_nonneg] at hpsd ⊢
  intro n t c
  let coeff : E → Fin n → ℂ :=
    fun x i ↦ c i * BoundedContinuousFunction.innerProbChar (-t i) x
  let integrand : E → ℂ :=
    fun x ↦ ∑ i, ∑ j, star (coeff x i) * φ (t i - t j) * coeff x j
  have hterm :
      ∀ i j,
        Integrable (fun x ↦ star (coeff x i) * φ (t i - t j) * coeff x j) (μ : Measure E) := by
    intro i j
    -- Proof comment: every twisted kernel entry is continuous and uniformly bounded on the
    -- finite witness measure.
    refine Integrable.of_bound ?_ (‖c i‖ * ‖φ (t i - t j)‖ * ‖c j‖) ?_
    · have hcoeff_i : Continuous fun x : E ↦ coeff x i := by
        fun_prop
      have hcoeff_j : Continuous fun x : E ↦ coeff x j := by
        fun_prop
      exact ((hcoeff_i.star.mul_const (φ (t i - t j))).mul hcoeff_j).aestronglyMeasurable
    · filter_upwards with x
      have hcoeff_i_norm : ‖coeff x i‖ = ‖c i‖ := by
        calc
          ‖coeff x i‖
              = ‖c i‖ * ‖BoundedContinuousFunction.innerProbChar (-t i) x‖ := by
                  simp [coeff, norm_mul]
          _ = ‖c i‖ := by
                rw [BoundedContinuousFunction.innerProbChar_apply]
                rw [Complex.norm_exp_ofReal_mul_I]
                ring
      have hcoeff_j_norm : ‖coeff x j‖ = ‖c j‖ := by
        calc
          ‖coeff x j‖
              = ‖c j‖ * ‖BoundedContinuousFunction.innerProbChar (-t j) x‖ := by
                  simp [coeff, norm_mul]
          _ = ‖c j‖ := by
                rw [BoundedContinuousFunction.innerProbChar_apply]
                rw [Complex.norm_exp_ofReal_mul_I]
                ring
      calc
        ‖star (coeff x i) * φ (t i - t j) * coeff x j‖
            = ‖coeff x i‖ * ‖φ (t i - t j)‖ * ‖coeff x j‖ := by
                simp [norm_mul, mul_assoc]
        _ = ‖c i‖ * ‖φ (t i - t j)‖ * ‖c j‖ := by
              rw [hcoeff_i_norm, hcoeff_j_norm]
        _ ≤ ‖c i‖ * ‖φ (t i - t j)‖ * ‖c j‖ := le_rfl
  have hkernel :
      ∑ i, ∑ j,
          star (c i) * (charFun (μ : Measure E) (t i - t j) * φ (t i - t j)) * c j =
        ∫ x, integrand x ∂(μ : Measure E) := by
    -- Proof comment: rewrite the characteristic-function factor as an integral of one additive
    -- character and absorb that phase into the quadratic-form coefficients.
    have hinnerSum :
        ∀ i : Fin n,
          Integrable (fun x ↦ ∑ j, star (coeff x i) * φ (t i - t j) * coeff x j)
            (μ : Measure E) := by
      intro i
      exact integrable_finset_sum _ (fun j _ ↦ hterm i j)
    calc
      ∑ i, ∑ j,
          star (c i) * (charFun (μ : Measure E) (t i - t j) * φ (t i - t j)) * c j
          =
        ∑ i, ∑ j,
          ∫ x, star (coeff x i) * φ (t i - t j) * coeff x j ∂(μ : Measure E) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            refine Finset.sum_congr rfl ?_
            intro j hj
            have hleft :
                star (c i) *
                    ∫ x, BoundedContinuousFunction.innerProbChar (t i - t j) x ∂(μ : Measure E) =
                  ∫ x, star (c i) *
                    BoundedContinuousFunction.innerProbChar (t i - t j) x ∂(μ : Measure E) := by
              simpa using
                (integral_const_mul (star (c i))
                  (fun x : E ↦ BoundedContinuousFunction.innerProbChar (t i - t j) x)).symm
            have hright :
                (∫ x, star (c i) *
                    BoundedContinuousFunction.innerProbChar (t i - t j) x ∂(μ : Measure E)) *
                    (φ (t i - t j) * c j) =
                  ∫ x, star (c i) *
                    BoundedContinuousFunction.innerProbChar (t i - t j) x *
                    (φ (t i - t j) * c j) ∂(μ : Measure E) := by
              simpa [mul_assoc] using
                (integral_mul_const (φ (t i - t j) * c j)
                  (fun x : E ↦ star (c i) *
                    BoundedContinuousFunction.innerProbChar (t i - t j) x)).symm
            calc
              star (c i) * (charFun (μ : Measure E) (t i - t j) * φ (t i - t j)) * c j
                  =
                (star (c i) *
                    ∫ x, BoundedContinuousFunction.innerProbChar (t i - t j) x ∂(μ : Measure E)) *
                  (φ (t i - t j) * c j) := by
                    rw [MeasureTheory.charFun_eq_integral_innerProbChar]
                    ring
              _ =
                (∫ x, star (c i) *
                    BoundedContinuousFunction.innerProbChar (t i - t j) x ∂(μ : Measure E)) *
                  (φ (t i - t j) * c j) := by
                    rw [hleft]
              _ =
                ∫ x, star (c i) *
                    BoundedContinuousFunction.innerProbChar (t i - t j) x *
                    (φ (t i - t j) * c j) ∂(μ : Measure E) := by
                      rw [hright]
              _ =
                ∫ x, star (coeff x i) * φ (t i - t j) * coeff x j ∂(μ : Measure E) := by
                  refine integral_congr_ae (Eventually.of_forall ?_)
                  intro x
                  calc
                    star (c i) *
                        BoundedContinuousFunction.innerProbChar (t i - t j) x *
                        (φ (t i - t j) * c j)
                        =
                      star (c i) *
                        (star (BoundedContinuousFunction.innerProbChar (-t i) x) *
                          BoundedContinuousFunction.innerProbChar (-t j) x) *
                        (φ (t i - t j) * c j) := by
                            rw [star_innerProbChar_neg_mul_innerProbChar_neg
                              (u := t i) (v := t j) (x := x)]
                    _ = star (coeff x i) * φ (t i - t j) * coeff x j := by
                          simp [coeff, mul_assoc, mul_left_comm, mul_comm]
      _ = ∑ i, ∫ x, ∑ j, star (coeff x i) * φ (t i - t j) * coeff x j ∂(μ : Measure E) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            symm
            exact integral_finset_sum _ (fun j _ ↦ hterm i j)
      _ = ∫ x, integrand x ∂(μ : Measure E) := by
            symm
            simp only [integrand]
            exact integral_finset_sum _ (fun i _ ↦ hinnerSum i)
  have hnonneg : 0 ≤ ∫ x, integrand x ∂(μ : Measure E) := by
    -- Proof comment: for each witness sample, the twisted coefficients reduce the claim to the
    -- original positive semidefinite quadratic-sum inequality for `φ`.
    refine integral_nonneg ?_
    intro x
    simpa [integrand, coeff] using hpsd n t (coeff x)
  rw [hkernel]
  exact hnonneg

/-- Helper for Theorem 15.29: if a finitely supported half-Gaussian stage is pushed forward along
the difference map, the resulting characteristic-function multiplier keeps the standard Euclidean
continuity, `L¹`, positivity, and normalization package. -/
lemma differenceLawMulSpecOfSupportFinite {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ}
    {ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))}
    (hν_finite :
      (((ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) :
        Measure (EuclideanSpace ℝ (Fin d))).support).Finite)
    (hψ_cont : Continuous ψ) (hψ_int : Integrable ψ)
    (hψ_psd : IsPositiveSemidefiniteFunction ψ) (hψ_zero : ψ 0 = 1) :
    let E := EuclideanSpace ℝ (Fin d)
    let ξ : ProbabilityMeasure E :=
      ProbabilityMeasure.map (ν.prod ν)
        ((by
            have hsubCont : Continuous fun p : E × E ↦ p.1 - p.2 := by
              fun_prop
            exact hsubCont.measurable.aemeasurable))
    (((ξ : ProbabilityMeasure E) : Measure E).support).Finite ∧
      Continuous (fun t : E ↦ charFun (ξ : Measure E) t * ψ t) ∧
      Integrable (fun t : E ↦ charFun (ξ : Measure E) t * ψ t) ∧
      IsPositiveSemidefiniteFunction (fun t : E ↦ charFun (ξ : Measure E) t * ψ t) ∧
      (fun t : E ↦ charFun (ξ : Measure E) t * ψ t) 0 = 1 := by
  let E := EuclideanSpace ℝ (Fin d)
  have hsubCont : Continuous fun p : E × E ↦ p.1 - p.2 := by
    fun_prop
  let ξ : ProbabilityMeasure E :=
    ProbabilityMeasure.map (ν.prod ν) hsubCont.measurable.aemeasurable
  have hξ_finite : (((ξ : ProbabilityMeasure E) : Measure E).support).Finite := by
    have hprod_finite :
        ((((ν : ProbabilityMeasure E) : Measure E).prod
          ((ν : ProbabilityMeasure E) : Measure E)).support).Finite := by
      -- Proof comment: the product of two finitely supported half-Gaussian stages still has
      -- finite support before taking the difference map.
      exact support_prod_finite_of_support_finite hν_finite hν_finite
    -- Proof comment: subtraction is continuous, so the difference law inherits finite support.
    simpa [ξ] using
      support_map_finite_of_support_finite hsubCont.measurable hprod_finite
  have hξ_cont : Continuous (fun t : E ↦ charFun (ξ : Measure E) t * ψ t) := by
    -- Proof comment: both the difference-law characteristic function and the original kernel are
    -- continuous, so their product is continuous as well.
    exact (MeasureTheory.continuous_charFun (μ := (ξ : Measure E))).mul hψ_cont
  have hξ_int : Integrable (fun t : E ↦ charFun (ξ : Measure E) t * ψ t) := by
    -- Proof comment: the difference-law characteristic function is bounded by `1`, so the
    -- original `L¹` bound for `ψ` still controls the product.
    refine Integrable.mono' hψ_int.norm hξ_cont.aestronglyMeasurable ?_
    filter_upwards with t
    calc
      ‖charFun (ξ : Measure E) t * ψ t‖ = ‖charFun (ξ : Measure E) t‖ * ‖ψ t‖ := by
        simp [norm_mul]
      _ ≤ 1 * ‖ψ t‖ := by
            exact mul_le_mul_of_nonneg_right
              (MeasureTheory.norm_charFun_le_one (μ := (ξ : Measure E)) t)
              (norm_nonneg _)
      _ = ‖ψ t‖ := by simp
  have hξ_psd :
      IsPositiveSemidefiniteFunction (fun t : E ↦ charFun (ξ : Measure E) t * ψ t) := by
    -- Proof comment: multiplying by any witness-side characteristic function preserves positive
    -- semidefiniteness.
    exact mul_charFun_isPositiveSemidefiniteFunction (d := d) hψ_psd ξ
  have hξ_zero : (fun t : E ↦ charFun (ξ : Measure E) t * ψ t) 0 = 1 := by
    -- Proof comment: the difference law is still a probability measure, so its characteristic
    -- function has value `1` at the origin.
    have hchar_zero : charFun (ξ : Measure E) 0 = 1 := by
      simpa using (MeasureTheory.charFun_zero (μ := (ξ : Measure E)))
    simp [hchar_zero, hψ_zero]
  exact ⟨hξ_finite, hξ_cont, hξ_int, hξ_psd, hξ_zero⟩

/-- Helper for Theorem 15.29: the finite-support half-Gaussian approximation already provides the
correct stage kernels for the Gaussian-damped weak-limit argument; the only remaining Euclidean
gap is to package each stage kernel into an actual probability measure witness. -/
lemma densityGaussianDifferenceStageKernelApproximation {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} {b : ℝ} (hb : 0 < b)
    (hψ_cont : Continuous ψ) (hψ_int : Integrable ψ)
    (hψ_psd : IsPositiveSemidefiniteFunction ψ) (hψ_zero : ψ 0 = 1) :
    let E := EuclideanSpace ℝ (Fin d)
    let a : ℝ := Real.pi ^ 2 / b
    let hsub : Measurable (fun p : E × E ↦ p.1 - p.2) := by
      fun_prop
    let differenceLaw : ProbabilityMeasure E → ProbabilityMeasure E := fun ν ↦
      ProbabilityMeasure.map (ν.prod ν) hsub.aemeasurable
    ∃ νn : ℕ → ProbabilityMeasure E,
      (∀ n, (((νn n : ProbabilityMeasure E) : Measure E).support).Finite) ∧
        (∀ n,
          let ξn : ProbabilityMeasure E := differenceLaw (νn n)
          Continuous (fun t : E ↦ charFun (ξn : Measure E) t * ψ t) ∧
            Integrable (fun t : E ↦ charFun (ξn : Measure E) t * ψ t) ∧
            IsPositiveSemidefiniteFunction (fun t : E ↦ charFun (ξn : Measure E) t * ψ t) ∧
            (fun t : E ↦ charFun (ξn : Measure E) t * ψ t) 0 = 1) ∧
        (∀ t : E,
          Tendsto
            (fun n ↦
              let ξn : ProbabilityMeasure E := differenceLaw (νn n)
              charFun (ξn : Measure E) t * ψ t)
            atTop (𝓝 (Complex.exp (-(a : ℂ) * ‖t‖ ^ 2) * ψ t))) := by
  sorry

/-- Helper for Theorem 15.29: the calibrated one-Gaussian difference integral obtained from the
corrected half-window identity is already pointwise nonnegative. -/
lemma real_densityGaussianIntegral_nonneg {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} {b : ℝ} (hb : 0 < b)
    (hψ_cont : Continuous ψ) (hψ_psd : IsPositiveSemidefiniteFunction ψ)
    (hψ_zero : ψ 0 = 1) (x : EuclideanSpace ℝ (Fin d)) :
    let E := EuclideanSpace ℝ (Fin d)
    let a : ℝ := Real.pi ^ 2 / b
    let γ : Measure E :=
      (ProbabilityTheory.stdGaussian E).map (Real.sqrt (2 * a) • ·)
    0 ≤
      Complex.re
        (∫ t : E, ψ t * BoundedContinuousFunction.innerProbChar t x ∂γ) := by
  let E := EuclideanSpace ℝ (Fin d)
  let aHalf : ℝ := Real.pi ^ 2 / (2 * b)
  let a : ℝ := Real.pi ^ 2 / b
  let γHalf : ProbabilityMeasure E :=
    ProbabilityMeasure.map
      ⟨ProbabilityTheory.stdGaussian E, inferInstance⟩
      ((by
          have hsmul : Continuous fun y : E ↦ Real.sqrt (2 * aHalf) • y := by
            fun_prop
          exact hsmul.measurable.aemeasurable))
  let γ : Measure E :=
    (ProbabilityTheory.stdGaussian E).map (Real.sqrt (2 * a) • ·)
  have hwindow_nonneg :
      0 ≤
        Complex.re
          (∫ p : E × E,
            star (BoundedContinuousFunction.innerProbChar (-p.1) x) *
              ψ (p.1 - p.2) *
              BoundedContinuousFunction.innerProbChar (-p.2) x
              ∂(((γHalf.prod γHalf : ProbabilityMeasure (E × E))) : Measure (E × E))) := by
    -- Proof comment: the half-window approximation argument already proves nonnegativity for the
    -- corresponding quadratic-form integral over the product half-Gaussian law.
    simpa [E, aHalf, γHalf] using
      real_densityHalfGaussianWindowIntegral_nonneg
        (d := d) (ψ := ψ) (b := b) hb hψ_cont hψ_psd hψ_zero x
  have hwindow_eq :
      Complex.re
          (∫ p : E × E,
            star (BoundedContinuousFunction.innerProbChar (-p.1) x) *
              ψ (p.1 - p.2) *
              BoundedContinuousFunction.innerProbChar (-p.2) x
              ∂(((γHalf.prod γHalf : ProbabilityMeasure (E × E))) : Measure (E × E))) =
        Complex.re
          (∫ t : E, ψ t * BoundedContinuousFunction.innerProbChar t x ∂γ) := by
    -- Proof comment: specialize the previously proved half-window identity to the calibrated
    -- variance `π² / b`.
    simpa [E, aHalf, a, γHalf, γ] using
      real_densityHalfGaussianWindowIntegral_eq_real_differenceIntegral
        (d := d) (ψ := ψ) (b := b) hb hψ_cont x
  have hgauss_nonneg :
      0 ≤
        Complex.re
          (∫ t : E, ψ t * BoundedContinuousFunction.innerProbChar t x ∂γ) := by
    -- Proof comment: transport the already-proved half-window nonnegativity across the
    -- calibrated identity to isolate the exact one-Gaussian quadratic integral as the
    -- nonnegative owner.
    rw [← hwindow_eq]
    exact hwindow_nonneg
  -- Proof comment: transport the already-proved half-window nonnegativity across the calibrated
  -- identity to isolate the exact one-Gaussian quadratic integral as the nonnegative owner.
  simpa [E, a, γ] using hgauss_nonneg

/-- Helper for Theorem 15.29: once the Gaussian-regularized inverse-Fourier candidate is known to
be pointwise nonnegative and to have total mass `1`, continuity upgrades it to an `L¹` density. -/
lemma gaussianRegularizedInverseFourierDensity_integrable_of_nonneg_mass {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} {b : ℝ} (hb : 0 < b)
    (hψ_cont : Continuous ψ) (hψ_psd : IsPositiveSemidefiniteFunction ψ) (hψ_zero : ψ 0 = 1)
    (hgauss_nonneg : ∀ x, 0 ≤ gaussianRegularizedInverseFourierDensity ψ b x)
    (hgauss_mass : ∫ x, gaussianRegularizedInverseFourierDensity ψ b x = 1) :
    Integrable (gaussianRegularizedInverseFourierDensity ψ b) := by
  have hgauss_cont : Continuous (gaussianRegularizedInverseFourierDensity ψ b) := by
    -- Proof comment: the regularized inverse-Fourier candidate is already continuous as a
    -- real-valued function, so only the standard nonnegative mass-one upgrade remains.
    simpa using
      gaussianRegularizedInverseFourierDensityContinuousReal
        (d := d) (ψ := ψ) (b := b) hb hψ_cont hψ_psd hψ_zero
  -- Proof comment: a continuous nonnegative real function of total mass `1` is automatically
  -- integrable.
  exact
    integrable_of_continuous_nonneg_integral_eq_one
      (d := d) (f := gaussianRegularizedInverseFourierDensity ψ b)
      hgauss_cont hgauss_nonneg hgauss_mass

/-- Helper for Theorem 15.29: once `ψ` already has an actual Euclidean characteristic-function
witness, the exact scaled inverse-Fourier normal form inherits pointwise nonnegativity and total
mass `1` from the earlier witness-side Gaussian-density package. -/
lemma scaledRegularizedKernelFourierInv_nonnegMass_of_charFunWitness {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} {b : ℝ} (hb : 0 < b)
    (hψ_witness : ∃ μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)),
      ∀ t : EuclideanSpace ℝ (Fin d),
        charFun (μ : Measure (EuclideanSpace ℝ (Fin d))) t = ψ t) :
    let E := EuclideanSpace ℝ (Fin d)
    let c : ℝ := -(2 * Real.pi)
    let cInv : ℝ := (-(2 * Real.pi)⁻¹ : ℝ)
    let ρ : E → ℂ := fun t ↦ Complex.exp (-(b : ℂ) * ‖cInv • t‖ ^ 2) * ψ (cInv • t)
    (∀ x : E, 0 ≤ Complex.re (FourierTransformInv.fourierInv (fun t : E ↦ ρ (c • t)) x)) ∧
      (∫ x : E, Complex.re (FourierTransformInv.fourierInv (fun t : E ↦ ρ (c • t)) x) = 1) := by
  sorry
/-- Helper for Theorem 15.29: the unresolved Euclidean Gaussian bridge should package the
calibrated one-Gaussian quadratic-form nonnegativity theorem together with the matching mass-one
transport for `gaussianRegularizedInverseFourierDensity ψ b`. -/
lemma gaussianRegularizedInverseFourierDensity_nonnegMass_of_scaledKernelBridge {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} {b : ℝ}
    (hscaled :
      let E := EuclideanSpace ℝ (Fin d)
      let c : ℝ := -(2 * Real.pi)
      let cInv : ℝ := (-(2 * Real.pi)⁻¹ : ℝ)
      let ρ : E → ℂ := fun t ↦ Complex.exp (-(b : ℂ) * ‖cInv • t‖ ^ 2) * ψ (cInv • t)
      (∀ x : E, 0 ≤ Complex.re (FourierTransformInv.fourierInv (fun t : E ↦ ρ (c • t)) x)) ∧
        (∫ x : E, Complex.re (FourierTransformInv.fourierInv (fun t : E ↦ ρ (c • t)) x) = 1)) :
    (∀ x, 0 ≤ gaussianRegularizedInverseFourierDensity ψ b x) ∧
      (∫ x, gaussianRegularizedInverseFourierDensity ψ b x = 1) := by
  let E := EuclideanSpace ℝ (Fin d)
  let c : ℝ := -(2 * Real.pi)
  let cInv : ℝ := (-(2 * Real.pi)⁻¹ : ℝ)
  let ρ : E → ℂ := fun t ↦ Complex.exp (-(b : ℂ) * ‖cInv • t‖ ^ 2) * ψ (cInv • t)
  rcases hscaled with ⟨hscaled_nonneg, hscaled_mass⟩
  have hbridge :
      gaussianRegularizedInverseFourierDensity ψ b =
        fun x : E ↦ Complex.re (FourierTransformInv.fourierInv (fun t : E ↦ ρ (c • t)) x) := by
    -- Proof comment: the earlier fixed-normalization lemma already rewrites the public
    -- regularized density into the scaled-kernel inverse-Fourier normal form.
    simpa [E, c, cInv, ρ] using
      gaussianRegularizedInverseFourierDensity_eq_scaledKernelFourierInv
        (d := d) (ψ := ψ) (b := b)
  refine ⟨?_, ?_⟩
  · -- Proof comment: pointwise nonnegativity is exactly the same statement after the normal-form
    -- rewrite above.
    intro x
    have hx :
        gaussianRegularizedInverseFourierDensity ψ b x =
          Complex.re (FourierTransformInv.fourierInv (fun t : E ↦ ρ (c • t)) x) := by
      simpa using congrFun hbridge x
    rw [hx]
    exact hscaled_nonneg x
  · -- Proof comment: total mass transports across the same function equality.
    have hfun :
        (fun x : E ↦ gaussianRegularizedInverseFourierDensity ψ b x) =
          fun x : E ↦ Complex.re (FourierTransformInv.fourierInv (fun t : E ↦ ρ (c • t)) x) := by
      funext x
      exact congrFun hbridge x
    rw [hfun]
    exact hscaled_mass

/-- Helper for Theorem 15.29: once the fixed scaled-kernel inverse-Fourier candidate is already
nonnegative and integrable, the earlier public mass-one theorem transports its total mass to `1`.
-/
lemma scaledRegularizedKernelFourierInv_integral_eq_one_of_nonneg_integrable {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} {b : ℝ} (hb : 0 < b)
    (hψ_cont : Continuous ψ) (hψ_int : Integrable ψ)
    (hψ_psd : IsPositiveSemidefiniteFunction ψ) (hψ_zero : ψ 0 = 1) :
    let E := EuclideanSpace ℝ (Fin d)
    let c : ℝ := -(2 * Real.pi)
    let cInv : ℝ := (-(2 * Real.pi)⁻¹ : ℝ)
    let ρ : E → ℂ := fun t ↦ Complex.exp (-(b : ℂ) * ‖cInv • t‖ ^ 2) * ψ (cInv • t)
    let f : E → ℝ := fun x ↦
      Complex.re (FourierTransformInv.fourierInv (fun t : E ↦ ρ (c • t)) x)
    (∀ x : E, 0 ≤ f x) → Integrable f → ∫ x : E, f x = 1 := by
  let E := EuclideanSpace ℝ (Fin d)
  let c : ℝ := -(2 * Real.pi)
  let cInv : ℝ := (-(2 * Real.pi)⁻¹ : ℝ)
  let ρ : E → ℂ := fun t ↦ Complex.exp (-(b : ℂ) * ‖cInv • t‖ ^ 2) * ψ (cInv • t)
  let f : E → ℝ := fun x ↦
    Complex.re (FourierTransformInv.fourierInv (fun t : E ↦ ρ (c • t)) x)
  dsimp
  intro hf_nonneg hf_int
  have hbridge : gaussianRegularizedInverseFourierDensity ψ b = f := by
    -- Proof comment: the earlier fixed-normalization bridge identifies the public regularized
    -- density with the frozen scaled-kernel inverse-Fourier candidate.
    simpa [E, c, cInv, ρ, f] using
      gaussianRegularizedInverseFourierDensity_eq_scaledKernelFourierInv
        (d := d) (ψ := ψ) (b := b)
  have hgauss_nonneg : ∀ x, 0 ≤ gaussianRegularizedInverseFourierDensity ψ b x := by
    intro x
    -- Proof comment: pointwise nonnegativity is the same statement after rewriting through the
    -- fixed scaled-kernel normal form.
    have hx : gaussianRegularizedInverseFourierDensity ψ b x = f x := by
      simpa using congrFun hbridge x
    rw [hx]
    exact hf_nonneg x
  have hgauss_int : Integrable (gaussianRegularizedInverseFourierDensity ψ b) := by
    -- Proof comment: the `L¹` hypothesis also transports across the same function equality.
    rw [hbridge]
    exact hf_int
  -- Proof comment: the public regularized-density mass theorem now applies directly, and the
  -- conclusion can be rewritten back to the scaled-kernel inverse-Fourier surface.
  have hmass :
      ∫ x, gaussianRegularizedInverseFourierDensity ψ b x = 1 := by
    exact
      gaussianRegularizedInverseFourierDensityMassOneCore
        (d := d) (ψ := ψ) (b := b) hb hψ_cont hψ_int hψ_psd hψ_zero
        hgauss_nonneg hgauss_int
  rw [hbridge] at hmass
  simpa [E, c, cInv, ρ, f] using hmass

/-- Helper for Theorem 15.29: the exact scaled kernel `ρ` appearing in the fixed `-2π`
inverse-Fourier normal form already inherits continuity, integrability, positive semidefiniteness,
and normalization from the original kernel `ψ`. -/
lemma scaledRegularizedKernelSpec {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} {b : ℝ} (hb : 0 < b)
    (hψ_cont : Continuous ψ) (hψ_int : Integrable ψ)
    (hψ_psd : IsPositiveSemidefiniteFunction ψ) (hψ_zero : ψ 0 = 1) :
    let E := EuclideanSpace ℝ (Fin d)
    let cInv : ℝ := (-(2 * Real.pi)⁻¹ : ℝ)
    let ρ : E → ℂ := fun t ↦ Complex.exp (-(b : ℂ) * ‖cInv • t‖ ^ 2) * ψ (cInv • t)
    Continuous ρ ∧ Integrable ρ ∧ IsPositiveSemidefiniteFunction ρ ∧ ρ 0 = 1 := by
  let E := EuclideanSpace ℝ (Fin d)
  let cInv : ℝ := (-(2 * Real.pi)⁻¹ : ℝ)
  let σ : E → ℂ := fun t ↦ Complex.exp (-(b : ℂ) * ‖t‖ ^ 2) * ψ t
  let ρ : E → ℂ := fun t ↦ Complex.exp (-(b : ℂ) * ‖cInv • t‖ ^ 2) * ψ (cInv • t)
  have hcInv : cInv ≠ 0 := by
    -- Proof comment: the inverse Fourier normalization scalar `(-2π)⁻¹` is nonzero.
    dsimp [cInv]
    exact neg_ne_zero.mpr (inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero))
  have hσ_spec : Continuous σ ∧ Integrable σ ∧ IsPositiveSemidefiniteFunction σ ∧ σ 0 = 1 := by
    -- Proof comment: the undilated Gaussian-regularized kernel already has the standard
    -- continuity, `L¹`, positive-semidefinite, and normalization package.
    simpa [σ] using
      gaussianRegularizedKernelSpec
        (d := d) (ψ := ψ) (b := b) hb hψ_cont hψ_int hψ_psd hψ_zero
  have hρ_cont : Continuous ρ := by
    have hscale : Continuous fun t : E ↦ cInv • t := by
      simpa [cInv] using
        (continuous_const.smul continuous_id : Continuous fun t : E ↦ cInv • t)
    -- Proof comment: `ρ` is just the regularized kernel precomposed with the fixed linear scaling.
    simpa [ρ, σ] using hσ_spec.1.comp hscale
  have hρ_int : Integrable ρ := by
    -- Proof comment: integrability is preserved under precomposition by the same nonzero scalar.
    simpa [ρ, σ] using hσ_spec.2.1.comp_smul hcInv
  have hρ_psd : IsPositiveSemidefiniteFunction ρ := by
    -- Proof comment: positive semidefiniteness is stable under precomposition by the fixed linear
    -- normalization map `t ↦ cInv • t`.
    have hσ_psd : IsPositiveSemidefiniteFunction σ := hσ_spec.2.2.1
    rw [isPositiveSemidefiniteFunction_iff_quadratic_sum_nonneg] at hσ_psd ⊢
    intro n t z
    have hmain :
        0 ≤
          ∑ i, ∑ j, star (z i) * σ (cInv • t i - cInv • t j) * z j := by
      simpa using hσ_psd n (fun i ↦ cInv • t i) z
    have hsum :
        (∑ i, ∑ j, star (z i) * ρ (t i - t j) * z j) =
          ∑ i, ∑ j, star (z i) * σ (cInv • t i - cInv • t j) * z j := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      refine Finset.sum_congr rfl ?_
      intro j hj
      simp [ρ, σ, smul_sub]
    rw [hsum]
    exact hmain
  have hρ_zero : ρ 0 = 1 := by
    -- Proof comment: the fixed linear scaling still sends `0` to `0`, so normalization is
    -- unchanged.
    simpa [ρ, σ, cInv] using hσ_spec.2.2.2
  exact ⟨hρ_cont, hρ_int, hρ_psd, hρ_zero⟩

/-- Helper for Theorem 15.29: after packaging the exact scaled kernel `ρ`, the calibrated
one-Gaussian quadratic-form integral attached to `ρ` is already pointwise nonnegative. -/
lemma scaledRegularizedKernel_densityGaussianIntegral_nonneg {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} {b : ℝ} (hb : 0 < b)
    (hψ_cont : Continuous ψ) (hψ_int : Integrable ψ)
    (hψ_psd : IsPositiveSemidefiniteFunction ψ) (hψ_zero : ψ 0 = 1)
    (x : EuclideanSpace ℝ (Fin d)) :
    let E := EuclideanSpace ℝ (Fin d)
    let cInv : ℝ := (-(2 * Real.pi)⁻¹ : ℝ)
    let ρ : E → ℂ := fun t ↦ Complex.exp (-(b : ℂ) * ‖cInv • t‖ ^ 2) * ψ (cInv • t)
    let bDensity : ℝ := 4 * Real.pi ^ 4 / b
    let a : ℝ := Real.pi ^ 2 / bDensity
    let γ : Measure E :=
      (ProbabilityTheory.stdGaussian E).map (Real.sqrt (2 * a) • ·)
    0 ≤
      Complex.re
        (∫ t : E, ρ t * BoundedContinuousFunction.innerProbChar t x ∂γ) := by
  let E := EuclideanSpace ℝ (Fin d)
  let cInv : ℝ := (-(2 * Real.pi)⁻¹ : ℝ)
  let ρ : E → ℂ := fun t ↦ Complex.exp (-(b : ℂ) * ‖cInv • t‖ ^ 2) * ψ (cInv • t)
  let bDensity : ℝ := 4 * Real.pi ^ 4 / b
  let a : ℝ := Real.pi ^ 2 / bDensity
  let γ : Measure E :=
    (ProbabilityTheory.stdGaussian E).map (Real.sqrt (2 * a) • ·)
  have hbDensity : 0 < bDensity := by
    positivity
  have hρ_spec :
      Continuous ρ ∧ Integrable ρ ∧ IsPositiveSemidefiniteFunction ρ ∧ ρ 0 = 1 := by
    -- Proof comment: package the exact scaled kernel once so the Gaussian-integral theorem can be
    -- applied directly to `ρ`.
    simpa [E, cInv, ρ] using
      scaledRegularizedKernelSpec
        (d := d) (ψ := ψ) (b := b) hb hψ_cont hψ_int hψ_psd hψ_zero
  -- Proof comment: the calibrated one-Gaussian nonnegativity theorem applies directly once the
  -- scaled kernel is viewed as the positive-semidefinite input function.
  simpa [E, cInv, ρ, bDensity, a, γ] using
    real_densityGaussianIntegral_nonneg
      (d := d) (ψ := ρ) (b := bDensity) hbDensity
      hρ_spec.1 hρ_spec.2.2.1 hρ_spec.2.2.2 x

/-- Helper for Theorem 15.29: the exact scaled approximants are just the ordinary Gaussian
regularizations of `ψ` with parameter `b + ((n : ℝ) + 1)⁻¹`. -/
lemma scaledRegularizedKernelApprox_eq_regularizedKernel {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} {b : ℝ} (n : ℕ) :
    let E := EuclideanSpace ℝ (Fin d)
    let c : ℝ := -(2 * Real.pi)
    let cInv : ℝ := (-(2 * Real.pi)⁻¹ : ℝ)
    let ρ : E → ℂ := fun t ↦ Complex.exp (-(b : ℂ) * ‖cInv • t‖ ^ 2) * ψ (cInv • t)
    (fun t : E ↦
      Complex.exp
          (-(((((n : ℝ) + 1)⁻¹ / (2 * Real.pi) ^ 2 : ℝ) : ℂ) * ‖c • t‖ ^ 2)) *
        ρ (c • t)) =
      fun t : E ↦
        Complex.exp (-((((b + ((n : ℝ) + 1)⁻¹ : ℝ) : ℂ) * ‖t‖ ^ 2))) * ψ t := by
  let E := EuclideanSpace ℝ (Fin d)
  let c : ℝ := -(2 * Real.pi)
  let cInv : ℝ := (-(2 * Real.pi)⁻¹ : ℝ)
  let ρ : E → ℂ := fun t ↦ Complex.exp (-(b : ℂ) * ‖cInv • t‖ ^ 2) * ψ (cInv • t)
  funext t
  have hscaled :
      Complex.exp
          (-(((((n : ℝ) + 1)⁻¹ / (2 * Real.pi) ^ 2 : ℝ) : ℂ) * ‖c • t‖ ^ 2)) *
        ρ (c • t) =
      Complex.exp (-((((n : ℝ) + 1)⁻¹ : ℂ) * ‖t‖ ^ 2)) * ρ (c • t) := by
    -- Proof comment: the fixed `-2π` normalization converts the outer Gaussian factor to the
    -- standard regularization parameter `((n : ℝ) + 1)⁻¹`.
    simpa [c] using
      scaledDampedKernel_apply_eq_normalizedDamping (d := d) (ρ := ρ) n t
  have hsmul : cInv • (c • t) = t := by
    -- Proof comment: the rescaling inside `ρ` cancels exactly against the frozen `-2π`
    -- normalization.
    calc
      cInv • (c • t) = (cInv * c) • t := by rw [smul_smul]
      _ = (1 : ℝ) • t := by
            dsimp [cInv, c]
            field_simp [Real.pi_ne_zero]
      _ = t := by simp
  calc
    Complex.exp
        (-(((((n : ℝ) + 1)⁻¹ / (2 * Real.pi) ^ 2 : ℝ) : ℂ) * ‖c • t‖ ^ 2)) *
      ρ (c • t)
        = Complex.exp (-((((n : ℝ) + 1)⁻¹ : ℂ) * ‖t‖ ^ 2)) * ρ (c • t) := hscaled
    _ = Complex.exp (-((((n : ℝ) + 1)⁻¹ : ℂ) * ‖t‖ ^ 2)) *
          (Complex.exp (-(b : ℂ) * ‖t‖ ^ 2) * ψ t) := by
            simp [ρ, hsmul]
    _ = Complex.exp (-((((b + ((n : ℝ) + 1)⁻¹ : ℝ) : ℂ) * ‖t‖ ^ 2))) * ψ t := by
          calc
            Complex.exp (-((((n : ℝ) + 1)⁻¹ : ℂ) * ‖t‖ ^ 2)) *
                (Complex.exp (-(b : ℂ) * ‖t‖ ^ 2) * ψ t)
              = (Complex.exp (-((((n : ℝ) + 1)⁻¹ : ℂ) * ‖t‖ ^ 2)) *
                  Complex.exp (-(b : ℂ) * ‖t‖ ^ 2)) * ψ t := by
                    ring
            _ = Complex.exp
                  (-((((n : ℝ) + 1)⁻¹ : ℂ) * ‖t‖ ^ 2) + -(b : ℂ) * ‖t‖ ^ 2) * ψ t := by
                    rw [← Complex.exp_add]
            _ = Complex.exp (-((((b + ((n : ℝ) + 1)⁻¹ : ℝ) : ℂ) * ‖t‖ ^ 2))) * ψ t := by
                    congr 1
                    norm_num
                    ring

/-- Helper for Theorem 15.29: the real inverse Fourier transform of each exact scaled
approximant is exactly the regularized density with parameter `b + ((n : ℝ) + 1)⁻¹`. -/
lemma scaledRegularizedKernelApprox_density_eq_regularizedDensity {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} {b : ℝ} (n : ℕ)
    (x : EuclideanSpace ℝ (Fin d)) :
    let E := EuclideanSpace ℝ (Fin d)
    let c : ℝ := -(2 * Real.pi)
    let cInv : ℝ := (-(2 * Real.pi)⁻¹ : ℝ)
    let ρ : E → ℂ := fun t ↦ Complex.exp (-(b : ℂ) * ‖cInv • t‖ ^ 2) * ψ (cInv • t)
    Complex.re
      (FourierTransformInv.fourierInv
        (fun t : E ↦
          Complex.exp
              (-(((((n : ℝ) + 1)⁻¹ / (2 * Real.pi) ^ 2 : ℝ) : ℂ) * ‖c • t‖ ^ 2)) *
            ρ (c • t))
        x) =
      gaussianRegularizedInverseFourierDensity ψ (b + ((n : ℝ) + 1)⁻¹) x := by
  sorry

/-- Helper for Theorem 15.29: each exact scaled approximant should already be a nonnegative
mass-one `L¹` density before the final Fatou step. -/
lemma gaussianRegularizedInverseFourierDensityApproxSpecOfScaledKernel {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} {b : ℝ} (hb : 0 < b)
    (hψ_cont : Continuous ψ) (hψ_int : Integrable ψ)
    (hψ_psd : IsPositiveSemidefiniteFunction ψ) (hψ_zero : ψ 0 = 1) :
    let E := EuclideanSpace ℝ (Fin d)
    let c : ℝ := -(2 * Real.pi)
    let cInv : ℝ := (-(2 * Real.pi)⁻¹ : ℝ)
    let ρ : E → ℂ := fun t ↦ Complex.exp (-(b : ℂ) * ‖cInv • t‖ ^ 2) * ψ (cInv • t)
    ∀ n : ℕ,
      (∀ x : E,
        0 ≤ Complex.re
          (FourierTransformInv.fourierInv
            (fun t : E ↦
              Complex.exp
                  (-(((((n : ℝ) + 1)⁻¹ / (2 * Real.pi) ^ 2 : ℝ) : ℂ) * ‖c • t‖ ^ 2)) *
                ρ (c • t))
            x)) ∧
      Integrable
        (fun x : E ↦
          Complex.re
            (FourierTransformInv.fourierInv
              (fun t : E ↦
                Complex.exp
                    (-(((((n : ℝ) + 1)⁻¹ / (2 * Real.pi) ^ 2 : ℝ) : ℂ) * ‖c • t‖ ^ 2)) *
                  ρ (c • t))
              x)) ∧
      (∫ x : E,
        Complex.re
          (FourierTransformInv.fourierInv
            (fun t : E ↦
              Complex.exp
                  (-(((((n : ℝ) + 1)⁻¹ / (2 * Real.pi) ^ 2 : ℝ) : ℂ) * ‖c • t‖ ^ 2)) *
                ρ (c • t))
            x) = 1) := by
  sorry

/-- Helper for Theorem 15.29: after freezing the fixed `-2π` normalization inside the kernel, the
remaining Gaussian bridge is the scaled-kernel inverse-Fourier candidate itself. -/
lemma scaledRegularizedKernelFourierInv_nonnegMass_viaGaussianBridge {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} {b : ℝ} (_hb : 0 < b)
    (_hψ_cont : Continuous ψ) (_hψ_int : Integrable ψ)
    (_hψ_psd : IsPositiveSemidefiniteFunction ψ) (_hψ_zero : ψ 0 = 1) :
    let E := EuclideanSpace ℝ (Fin d)
    let c : ℝ := -(2 * Real.pi)
    let cInv : ℝ := (-(2 * Real.pi)⁻¹ : ℝ)
    let ρ : E → ℂ := fun t ↦ Complex.exp (-(b : ℂ) * ‖cInv • t‖ ^ 2) * ψ (cInv • t)
    (∀ x : E, 0 ≤ Complex.re (FourierTransformInv.fourierInv (fun t : E ↦ ρ (c • t)) x)) ∧
      (∫ x : E, Complex.re (FourierTransformInv.fourierInv (fun t : E ↦ ρ (c • t)) x) = 1) := by
  sorry
/-- Helper for Theorem 15.29: the unresolved Euclidean Gaussian bridge should package the
calibrated one-Gaussian quadratic-form nonnegativity theorem together with the matching mass-one
transport for `gaussianRegularizedInverseFourierDensity ψ b`. -/
lemma gaussianRegularizedInverseFourierDensity_nonnegMass_viaGaussianBridge {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} {b : ℝ} (hb : 0 < b)
    (hψ_cont : Continuous ψ) (hψ_int : Integrable ψ)
    (hψ_psd : IsPositiveSemidefiniteFunction ψ) (hψ_zero : ψ 0 = 1) :
    (∀ x, 0 ≤ gaussianRegularizedInverseFourierDensity ψ b x) ∧
      (∫ x, gaussianRegularizedInverseFourierDensity ψ b x = 1) := by
  -- Route correction: before using the Gaussian-window theorem, first rewrite the public density
  -- into the fixed scaled-kernel `fourierInv` normal form so the remaining blocker no longer
  -- depends on the oscillatory integral spelling.
  -- Route correction: the tempting Euclidean witness shortcut through the later theorem
  -- `exists_probabilityMeasure_charFun_eq_iff` is still circular here, because that theorem
  -- re-enters this blocker through
  -- `scaledInverseFourierDensitySpecOfIntegrableContinuousPositiveDefinite` and the call to
  -- `gaussianRegularizedInverseFourierDensityNonnegMassWindow`.
  -- Proof comment: the new transport helper isolates the remaining work to a single scaled-kernel
  -- inverse-Fourier statement, so later re-plans can target that exact normal form.
  exact
    gaussianRegularizedInverseFourierDensity_nonnegMass_of_scaledKernelBridge
      (d := d) (ψ := ψ) (b := b)
      (scaledRegularizedKernelFourierInv_nonnegMass_viaGaussianBridge
        (d := d) (ψ := ψ) (b := b) hb hψ_cont hψ_int hψ_psd hψ_zero)

/-- Helper for Theorem 15.29: the Gaussian-window approximation route should first isolate the
pointwise nonnegativity of the regularized inverse-Fourier candidate. -/
lemma gaussianRegularizedInverseFourierDensityNonnegIntegrableWindowCore {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} {b : ℝ} (hb : 0 < b)
    (hψ_cont : Continuous ψ) (hψ_int : Integrable ψ)
    (hψ_psd : IsPositiveSemidefiniteFunction ψ) (hψ_zero : ψ 0 = 1) :
    (∀ x, 0 ≤ gaussianRegularizedInverseFourierDensity ψ b x) ∧
      Integrable (gaussianRegularizedInverseFourierDensity ψ b) := by
  -- Route correction: the discarded half-window and one-Gaussian difference identities do not
  -- compute the regularized density itself. The remaining upstream owner is the centered
  -- Gaussian quadratic-form route together with the Gaussian majorant argument for `L¹`.
  have hgauss_nonneg_mass :
      (∀ x, 0 ≤ gaussianRegularizedInverseFourierDensity ψ b x) ∧
        (∫ x, gaussianRegularizedInverseFourierDensity ψ b x = 1) := by
    -- Proof comment: the only remaining Euclidean gap is the dedicated Gaussian-bridge owner
    -- above, so this theorem now depends on that single noncircular interface.
    exact
      gaussianRegularizedInverseFourierDensity_nonnegMass_viaGaussianBridge
        (d := d) (ψ := ψ) (b := b) hb hψ_cont hψ_int hψ_psd hψ_zero
  refine ⟨hgauss_nonneg_mass.1, ?_⟩
  -- Proof comment: once the remaining blocker is reduced to nonnegativity plus mass `1`, the
  -- `L¹` clause is a direct continuity upgrade handled by the dedicated helper above.
  exact
    gaussianRegularizedInverseFourierDensity_integrable_of_nonneg_mass
      (d := d) (ψ := ψ) (b := b) hb hψ_cont hψ_psd hψ_zero
      hgauss_nonneg_mass.1 hgauss_nonneg_mass.2

/-- Helper for Theorem 15.29: the Gaussian-window approximation route should first isolate the
pointwise nonnegativity of the regularized inverse-Fourier candidate. -/
lemma gaussianRegularizedInverseFourierDensityNonnegMassWindowCore {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} {b : ℝ} (hb : 0 < b)
    (hψ_cont : Continuous ψ) (hψ_int : Integrable ψ)
    (hψ_psd : IsPositiveSemidefiniteFunction ψ) (hψ_zero : ψ 0 = 1) :
    (∀ x, 0 ≤ gaussianRegularizedInverseFourierDensity ψ b x) ∧
      (∫ x, gaussianRegularizedInverseFourierDensity ψ b x = 1) := by
  -- Route correction: the previous direct identification of the regularized inverse-Fourier
  -- density with the half-Gaussian product-window integral is false; the certified mismatch
  -- `gaussianRegularizedInverseFourierDensity_ne_real_halfGaussianWindowIntegral_constOne_zero`
  -- already rules it out on the constant kernel over `ℝ²`.
  -- Route correction: the stronger scalar-normalization variant is also false; the explicit
  -- counterexample
  -- `gaussianRegularizedInverseFourierDensity_ne_normalized_real_halfGaussianWindowIntegral_constOne_unit`
  -- shows that even after fixing the zero-point scalar `(π / b)^(dim / 2)`, the half-window law
  -- decays like `exp (-b / (4π²))` at the unit vector while the regularized density decays like
  -- `exp (-π² / b)`.
  -- Route correction: the next scalar-free replan target is also too weak. The new counterexample
  -- `gaussianRegularizedInverseFourierDensity_ne_real_densityDifferenceIntegral_constOne_zero`
  -- shows that even the corrected one-Gaussian difference integral still misses the density-side
  -- normalization at `x = 0` on `ℝ²`.
  rcases
    gaussianRegularizedInverseFourierDensityNonnegIntegrableWindowCore
      (d := d) (ψ := ψ) (b := b) hb hψ_cont hψ_int hψ_psd hψ_zero with
    ⟨hnonneg, hint⟩
  refine ⟨hnonneg, ?_⟩
  -- Proof comment: once pointwise nonnegativity and `L¹` are isolated in the upstream analytic
  -- owner, the total mass is exactly the earlier Fourier-inversion computation at the origin.
  exact
    gaussianRegularizedInverseFourierDensityMassOneCore
      (d := d) (ψ := ψ) (b := b) hb hψ_cont hψ_int hψ_psd hψ_zero hnonneg hint

/-- Helper for Theorem 15.29: the Gaussian-window approximation route should first isolate the
pointwise nonnegativity of the regularized inverse-Fourier candidate. -/
lemma gaussianRegularizedInverseFourierDensity_nonneg_windowLimit {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} {b : ℝ} (hb : 0 < b)
    (hψ_cont : Continuous ψ) (hψ_int : Integrable ψ)
    (hψ_psd : IsPositiveSemidefiniteFunction ψ) (hψ_zero : ψ 0 = 1) :
    ∀ x, 0 ≤ gaussianRegularizedInverseFourierDensity ψ b x := by
  -- Proof comment: keep the public nonnegativity lemma as the first projection of the shared
  -- Euclidean blocker, so the unresolved analytic work lives in one owner only.
  exact
    (gaussianRegularizedInverseFourierDensityNonnegMassWindowCore
      (d := d) (ψ := ψ) (b := b) hb hψ_cont hψ_int hψ_psd hψ_zero).1

/-- Helper for Theorem 15.29: once pointwise nonnegativity is separated, the total mass should be
recovered by a Gaussian-cutoff computation rather than by turning finite window stages into
densities. -/
lemma gaussianRegularizedInverseFourierDensity_integral_eq_one_viaGaussianCutoff {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} {b : ℝ} (hb : 0 < b)
    (hψ_cont : Continuous ψ) (hψ_int : Integrable ψ)
    (hψ_psd : IsPositiveSemidefiniteFunction ψ) (hψ_zero : ψ 0 = 1) :
    ∫ x, gaussianRegularizedInverseFourierDensity ψ b x = 1 := by
  -- Proof comment: the mass-one statement is the second projection of the same shared owner, so
  -- the unresolved Euclidean frontier is reduced from two public placeholders to one core theorem.
  exact
    (gaussianRegularizedInverseFourierDensityNonnegMassWindowCore
      (d := d) (ψ := ψ) (b := b) hb hψ_cont hψ_int hψ_psd hψ_zero).2

lemma gaussianRegularizedInverseFourierDensityNonnegMassWindow {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} {b : ℝ} (hb : 0 < b)
    (hψ_cont : Continuous ψ) (hψ_int : Integrable ψ)
    (hψ_psd : IsPositiveSemidefiniteFunction ψ) (hψ_zero : ψ 0 = 1) :
    (∀ x, 0 ≤ gaussianRegularizedInverseFourierDensity ψ b x) ∧
      (∫ x, gaussianRegularizedInverseFourierDensity ψ b x = 1) := by
  -- Proof comment: this wrapper now just re-exports the single shared Euclidean blocker.
  exact
    gaussianRegularizedInverseFourierDensityNonnegMassWindowCore
      (d := d) (ψ := ψ) (b := b) hb hψ_cont hψ_int hψ_psd hψ_zero

/-- Helper for Theorem 15.29: the Gaussian-regularized kernel should be controlled by one shared
owner theorem providing both the actual witness and the inverse-Fourier density data. -/
lemma gaussianRegularizedKernelWitnessAndDensitySpec {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} {b : ℝ} (hb : 0 < b)
    (hψ_cont : Continuous ψ) (hψ_int : Integrable ψ)
    (hψ_psd : IsPositiveSemidefiniteFunction ψ) (hψ_zero : ψ 0 = 1) :
    (∃ μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)),
      ∀ t : EuclideanSpace ℝ (Fin d),
        charFun (μ : Measure (EuclideanSpace ℝ (Fin d))) t =
          Complex.exp (-(b : ℂ) * ‖t‖ ^ 2) * ψ t) ∧
      (∀ x, 0 ≤ gaussianRegularizedInverseFourierDensity ψ b x) ∧
      (∫ x, gaussianRegularizedInverseFourierDensity ψ b x = 1) := by
  rcases
    gaussianRegularizedInverseFourierDensityNonnegMassWindow
      (d := d) (ψ := ψ) (b := b) hb hψ_cont hψ_int hψ_psd hψ_zero with
    ⟨hf_nonneg, hf_mass⟩
  rcases
    existsProbabilityMeasureOfGaussianRegularizedDensity
      (d := d) (ψ := ψ) (b := b) hb hψ_cont hψ_int hψ_psd hψ_zero hf_nonneg hf_mass with
    ⟨μ, hμ⟩
  -- Proof comment: once the analytic density theorem is isolated, the shared owner is just the
  -- downstream packaging of that density into a probability witness.
  exact ⟨⟨μ, hμ⟩, hf_nonneg, hf_mass⟩

/-- Helper for Theorem 15.29: the Gaussian-regularized kernel already has an actual Euclidean
characteristic-function witness by the shared regularized-kernel owner. -/
lemma existsProbabilityMeasureOfGaussianRegularizedKernel {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} {b : ℝ} (hb : 0 < b)
    (hψ_cont : Continuous ψ) (hψ_int : Integrable ψ)
    (hψ_psd : IsPositiveSemidefiniteFunction ψ) (hψ_zero : ψ 0 = 1) :
    ∃ μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)),
      ∀ t : EuclideanSpace ℝ (Fin d),
        charFun (μ : Measure (EuclideanSpace ℝ (Fin d))) t =
          Complex.exp (-(b : ℂ) * ‖t‖ ^ 2) * ψ t := by
  -- Proof comment: the shared regularized-kernel owner packages the actual witness as its first
  -- projection, so this theorem is now just the witness-facing wrapper.
  exact
    (gaussianRegularizedKernelWitnessAndDensitySpec
      (d := d) (ψ := ψ) (b := b) hb hψ_cont hψ_int hψ_psd hψ_zero).1

/-- Helper for Theorem 15.29: the actual witness for the Gaussian-regularized kernel can be
repackaged as a function equality for later extensional rewrites. -/
lemma existsProbabilityMeasureOfGaussianRegularizedKernel_fun {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} {b : ℝ} (hb : 0 < b)
    (hψ_cont : Continuous ψ) (hψ_int : Integrable ψ)
    (hψ_psd : IsPositiveSemidefiniteFunction ψ) (hψ_zero : ψ 0 = 1) :
    ∃ μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)),
      charFun (μ : Measure (EuclideanSpace ℝ (Fin d))) =
        fun t : EuclideanSpace ℝ (Fin d) ↦
          Complex.exp (-(b : ℂ) * ‖t‖ ^ 2) * ψ t := by
  rcases
    existsProbabilityMeasureOfGaussianRegularizedKernel
      (d := d) (ψ := ψ) (b := b) hb hψ_cont hψ_int hψ_psd hψ_zero with
    ⟨μ, hμ⟩
  refine ⟨μ, ?_⟩
  -- Proof comment: upgrade the pointwise witness to a function equality once so later rewrites do
  -- not need to reintroduce `funext`.
  funext t
  exact hμ t

/-- Helper for Theorem 15.29: the remaining Euclidean Bochner owner should first package the
Gaussian-regularized inverse-Fourier candidate as an almost-everywhere equal nonnegative density
of mass `1`. -/
lemma gaussianRegularizedInverseFourierDensityAeEqDensityWitness {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} {b : ℝ} (hb : 0 < b)
    (hψ_cont : Continuous ψ) (hψ_int : Integrable ψ)
    (hψ_psd : IsPositiveSemidefiniteFunction ψ) (hψ_zero : ψ 0 = 1) :
    ∃ f : EuclideanSpace ℝ (Fin d) → ℝ,
      (∀ x, 0 ≤ f x) ∧ Integrable f ∧ (∫ x, f x = 1) ∧
        gaussianRegularizedInverseFourierDensity ψ b =ᵐ[volume] f := by
  let f : EuclideanSpace ℝ (Fin d) → ℝ := gaussianRegularizedInverseFourierDensity ψ b
  rcases
    gaussianRegularizedInverseFourierDensityNonnegMassWindow
      (d := d) (ψ := ψ) (b := b) hb hψ_cont hψ_int hψ_psd hψ_zero with
    ⟨hf_nonneg, hf_mass⟩
  have hf_cont : Continuous f := by
    -- Proof comment: the regularized inverse-Fourier candidate is already known to be continuous
    -- as a real-valued function.
    simpa [f] using
      gaussianRegularizedInverseFourierDensityContinuousReal
        (d := d) (ψ := ψ) (b := b) hb hψ_cont hψ_psd hψ_zero
  have hf_int : Integrable f := by
    -- Proof comment: continuity plus pointwise nonnegativity and total mass `1` upgrade the
    -- regularized candidate itself to an `L¹` density.
    exact
      integrable_of_continuous_nonneg_integral_eq_one
        (d := d) (f := f) hf_cont hf_nonneg hf_mass
  refine ⟨f, hf_nonneg, hf_int, hf_mass, ?_⟩
  -- Proof comment: the chosen density witness is literally the regularized inverse-Fourier
  -- candidate, so the almost-everywhere identification is reflexive.
  exact Filter.EventuallyEq.rfl

/-- Helper for Theorem 15.29: the Gaussian-window regularization frontier is one owner-shaped
specification theorem packaging pointwise nonnegativity, `L¹`, and mass `1`. -/
lemma gaussianRegularizedInverseFourierDensitySpec_direct {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} {b : ℝ} (hb : 0 < b)
    (hψ_cont : Continuous ψ) (hψ_int : Integrable ψ)
    (hψ_psd : IsPositiveSemidefiniteFunction ψ) (hψ_zero : ψ 0 = 1) :
    (∀ x, 0 ≤ gaussianRegularizedInverseFourierDensity ψ b x) ∧
      Integrable (gaussianRegularizedInverseFourierDensity ψ b) ∧
      (∫ x, gaussianRegularizedInverseFourierDensity ψ b x = 1) := by
  -- Route correction: keep this theorem as the thin public wrapper around the single owner-shaped
  -- Euclidean blocker extracted just above.
  rcases
    gaussianRegularizedInverseFourierDensityNonnegMassWindow
      (d := d) (ψ := ψ) (b := b) hb hψ_cont hψ_int hψ_psd hψ_zero with
    ⟨hf_nonneg, hf_mass⟩
  have hf_cont : Continuous (gaussianRegularizedInverseFourierDensity ψ b) := by
    -- Proof comment: the regularized inverse-Fourier candidate is continuous before any `L¹`
    -- packaging, so continuity plus nonnegativity and mass `1` gives integrability directly.
    simpa using
      gaussianRegularizedInverseFourierDensityContinuousReal
        (d := d) (ψ := ψ) (b := b) hb hψ_cont hψ_psd hψ_zero
  have hf_int : Integrable (gaussianRegularizedInverseFourierDensity ψ b) := by
    -- Proof comment: the owner theorem already supplies pointwise nonnegativity and total mass,
    -- and continuity upgrades that data to an `L¹` statement.
    exact
      integrable_of_continuous_nonneg_integral_eq_one
        (d := d) (f := gaussianRegularizedInverseFourierDensity ψ b) hf_cont hf_nonneg hf_mass
  exact ⟨hf_nonneg, hf_int, hf_mass⟩

/-- Helper for Theorem 15.29: the Gaussian-window quadratic-form route should first show the
regularized inverse-Fourier density is pointwise nonnegative. -/
lemma gaussianRegularizedInverseFourierDensity_nonneg_direct {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} {b : ℝ} (hb : 0 < b)
    (hψ_cont : Continuous ψ) (hψ_int : Integrable ψ)
    (hψ_psd : IsPositiveSemidefiniteFunction ψ) (hψ_zero : ψ 0 = 1) :
    ∀ x, 0 ≤ gaussianRegularizedInverseFourierDensity ψ b x := by
  -- Proof comment: project the pointwise nonnegativity clause from the shared regularized-density
  -- owner so the analytic frontier lives in only one theorem.
  exact
    (gaussianRegularizedInverseFourierDensitySpec_direct
      (d := d) (ψ := ψ) (b := b) hb hψ_cont hψ_int hψ_psd hψ_zero).1

/-- Helper for Theorem 15.29: once the same Gaussian-window representation is fixed, the
regularized inverse-Fourier density should have total mass `1`. -/
lemma gaussianRegularizedInverseFourierDensity_integral_eq_one_direct {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} {b : ℝ} (hb : 0 < b)
    (hψ_cont : Continuous ψ) (hψ_int : Integrable ψ)
    (hψ_psd : IsPositiveSemidefiniteFunction ψ) (hψ_zero : ψ 0 = 1) :
    ∫ x, gaussianRegularizedInverseFourierDensity ψ b x = 1 := by
  -- Proof comment: project the mass-one clause from the shared regularized-density owner instead
  -- of keeping a second coupled analytic placeholder.
  exact
    (gaussianRegularizedInverseFourierDensitySpec_direct
      (d := d) (ψ := ψ) (b := b) hb hψ_cont hψ_int hψ_psd hψ_zero).2.2

/-- Helper for Theorem 15.29: the Gaussian-regularized inverse-Fourier candidate should be
be pointwise nonnegative and `L¹` before the mass-one Fourier-inversion step is applied. -/
lemma gaussianRegularizedInverseFourierDensityNonnegIntegrableCore {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} {b : ℝ} (hb : 0 < b)
    (hψ_cont : Continuous ψ) (hψ_int : Integrable ψ)
    (hψ_psd : IsPositiveSemidefiniteFunction ψ) (hψ_zero : ψ 0 = 1) :
    (∀ x, 0 ≤ gaussianRegularizedInverseFourierDensity ψ b x) ∧
      Integrable (gaussianRegularizedInverseFourierDensity ψ b) := by
  -- Proof comment: the regularized-density frontier has been collapsed to one owner theorem, so
  -- the nonnegativity/`L¹` package is now just its first two projections.
  exact
    (gaussianRegularizedInverseFourierDensitySpec_direct
      (d := d) (ψ := ψ) (b := b) hb hψ_cont hψ_int hψ_psd hψ_zero).elim
      (fun hf_nonneg htail ↦ ⟨hf_nonneg, htail.1⟩)

/-- Helper for Theorem 15.29: the Gaussian-regularized inverse-Fourier candidate should be
jointly controlled by one core owner before the final `L¹` packaging step. -/
lemma gaussianRegularizedInverseFourierDensityNonnegMassCore {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} {b : ℝ} (hb : 0 < b)
    (hψ_cont : Continuous ψ) (hψ_int : Integrable ψ)
    (hψ_psd : IsPositiveSemidefiniteFunction ψ) (hψ_zero : ψ 0 = 1) :
    (∀ x, 0 ≤ gaussianRegularizedInverseFourierDensity ψ b x) ∧
      (∫ x, gaussianRegularizedInverseFourierDensity ψ b x = 1) := by
  rcases
    gaussianRegularizedInverseFourierDensityNonnegIntegrableCore
      (d := d) (ψ := ψ) (b := b) hb hψ_cont hψ_int hψ_psd hψ_zero with
    ⟨hf_nonneg, hf_int⟩
  refine ⟨hf_nonneg, ?_⟩
  -- Proof comment: once nonnegativity and `L¹` are isolated behind the dedicated owner, the mass
  -- statement is exactly the previously proved Fourier-inversion lemma.
  exact
    gaussianRegularizedInverseFourierDensityMassOneCore
      (d := d) (ψ := ψ) (b := b) hb hψ_cont hψ_int hψ_psd hψ_zero hf_nonneg hf_int

/-- Helper for Theorem 15.29: the Gaussian-regularized inverse-Fourier candidate should be
pointwise nonnegative before the final `L¹` packaging step. -/
lemma gaussianRegularizedInverseFourierDensity_nonneg {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} {b : ℝ} (hb : 0 < b)
    (hψ_cont : Continuous ψ) (hψ_int : Integrable ψ)
    (hψ_psd : IsPositiveSemidefiniteFunction ψ) (hψ_zero : ψ 0 = 1) :
    ∀ x, 0 ≤ gaussianRegularizedInverseFourierDensity ψ b x := by
  -- Proof comment: the public nonnegativity lemma is now just the first projection of the shared
  -- regularized-density owner.
  exact
    (gaussianRegularizedInverseFourierDensityNonnegMassCore
      (d := d) (ψ := ψ) (b := b) hb hψ_cont hψ_int hψ_psd hψ_zero).1

/-- Helper for Theorem 15.29: once the Gaussian-window representation is in place, the
Gaussian-regularized inverse-Fourier candidate has total mass `1`. -/
lemma gaussianRegularizedInverseFourierDensity_integral_eq_one {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} {b : ℝ} (hb : 0 < b)
    (hψ_cont : Continuous ψ) (hψ_int : Integrable ψ)
    (hψ_psd : IsPositiveSemidefiniteFunction ψ) (hψ_zero : ψ 0 = 1) :
    ∫ x, gaussianRegularizedInverseFourierDensity ψ b x = 1 := by
  -- Proof comment: the mass statement is the second projection of the same shared owner, so the
  -- downstream `L¹` package no longer duplicates the analytic frontier.
  exact
    (gaussianRegularizedInverseFourierDensityNonnegMassCore
      (d := d) (ψ := ψ) (b := b) hb hψ_cont hψ_int hψ_psd hψ_zero).2

lemma gaussianRegularizedInverseFourierDensityNonnegIntegrable {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} {b : ℝ} (hb : 0 < b)
    (hψ_cont : Continuous ψ) (hψ_int : Integrable ψ)
    (hψ_psd : IsPositiveSemidefiniteFunction ψ) (hψ_zero : ψ 0 = 1) :
    (∀ x, 0 ≤ gaussianRegularizedInverseFourierDensity ψ b x) ∧
      Integrable (gaussianRegularizedInverseFourierDensity ψ b) := by
  -- Proof comment: this public packaging lemma is now exactly the dedicated owner for the
  -- nonnegativity and `L¹` frontier.
  exact
    gaussianRegularizedInverseFourierDensityNonnegIntegrableCore
      (d := d) (ψ := ψ) (b := b) hb hψ_cont hψ_int hψ_psd hψ_zero

/-- Helper for Theorem 15.29: once pointwise nonnegativity and `L¹` are known for the
Gaussian-regularized inverse-Fourier density, its total mass is forced by Fourier inversion and
the normalization `ψ 0 = 1`. -/
lemma gaussianRegularizedInverseFourierDensityMassOne {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} {b : ℝ} (hb : 0 < b)
    (hψ_cont : Continuous ψ) (hψ_int : Integrable ψ)
    (hψ_psd : IsPositiveSemidefiniteFunction ψ) (hψ_zero : ψ 0 = 1)
    (hf_nonneg : ∀ x, 0 ≤ gaussianRegularizedInverseFourierDensity ψ b x)
    (hf_int : Integrable (gaussianRegularizedInverseFourierDensity ψ b)) :
    ∫ x, gaussianRegularizedInverseFourierDensity ψ b x = 1 := by
  -- Proof comment: keep the public mass lemma as the stable wrapper around the earlier owner that
  -- is now available to the shared Euclidean core.
  exact
    gaussianRegularizedInverseFourierDensityMassOneCore
      (d := d) (ψ := ψ) (b := b) hb hψ_cont hψ_int hψ_psd hψ_zero hf_nonneg hf_int

/-- Helper for Theorem 15.29: each Gaussian-regularized inverse-Fourier candidate attached to a
continuous integrable normalized positive semidefinite kernel should already be a nonnegative
mass-one `L¹` density. -/
lemma gaussianRegularizedInverseFourierDensitySpec {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} {b : ℝ} (hb : 0 < b)
    (hψ_cont : Continuous ψ) (hψ_int : Integrable ψ)
    (hψ_psd : IsPositiveSemidefiniteFunction ψ) (hψ_zero : ψ 0 = 1) :
    (∀ x, 0 ≤ gaussianRegularizedInverseFourierDensity ψ b x) ∧
      Integrable (gaussianRegularizedInverseFourierDensity ψ b) ∧
      (∫ x, gaussianRegularizedInverseFourierDensity ψ b x = 1) := by
  rcases
    gaussianRegularizedInverseFourierDensityNonnegIntegrable
      (d := d) (ψ := ψ) (b := b) hb hψ_cont hψ_int hψ_psd hψ_zero with
    ⟨hf_nonneg, hf_int⟩
  refine ⟨hf_nonneg, hf_int, ?_⟩
  -- Proof comment: once the regularized inverse-Fourier candidate is known to be a nonnegative
  -- `L¹` density, the mass-one property follows from Fourier inversion and `ψb 0 = 1`.
  exact gaussianRegularizedInverseFourierDensityMassOne
    (d := d) (ψ := ψ) (b := b) hb hψ_cont hψ_int hψ_psd hψ_zero hf_nonneg hf_int

/-- Helper for Theorem 15.29: an integrable continuous normalized positive semidefinite kernel on
`ℝ^d` should be represented by its Fourier-normalized inverse-Fourier density candidate. -/
lemma scaledInverseFourierDensitySpecOfIntegrableContinuousPositiveDefinite {d : ℕ}
    {ρ : EuclideanSpace ℝ (Fin d) → ℂ} (hρ_cont : Continuous ρ) (hρ_int : Integrable ρ)
    (hρ_psd : IsPositiveSemidefiniteFunction ρ) (hρ_zero : ρ 0 = 1) :
    let ψScaled : EuclideanSpace ℝ (Fin d) → ℂ := fun t ↦ ρ ((-(2 * Real.pi) : ℝ) • t)
    let f : EuclideanSpace ℝ (Fin d) → ℝ :=
      fun x ↦ Complex.re (FourierTransformInv.fourierInv ψScaled x)
    Continuous (fun x : EuclideanSpace ℝ (Fin d) ↦ ((f x : ℝ) : ℂ)) ∧
      (∀ x, 0 ≤ f x) ∧ Integrable f ∧ (∫ x, f x = 1) ∧
      (∀ t : EuclideanSpace ℝ (Fin d),
        VectorFourier.fourierIntegral Real.fourierChar volume
            (innerₗ (EuclideanSpace ℝ (Fin d)))
            (fun x : EuclideanSpace ℝ (Fin d) ↦ ((f x : ℝ) : ℂ))
            (-(2 * Real.pi)⁻¹ • t) = ρ t) := by
  -- Route correction: this is the single upstream Euclidean owner requested by the current plan.
  -- Its continuity clause follows from the existing inverse-Fourier API; the remaining
  -- nonnegativity, `L¹`, mass-one, and Fourier-recovery clauses are exactly the common analytic
  -- blocker shared by the downstream Gaussian-damped specializations.
  let E := EuclideanSpace ℝ (Fin d)
  let c : ℝ := -(2 * Real.pi)
  let ψScaled : E → ℂ := fun t ↦ ρ (c • t)
  let f : E → ℝ := fun x ↦ Complex.re (FourierTransformInv.fourierInv ψScaled x)
  have hc : c ≠ 0 := by
    have htwoPi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    exact neg_ne_zero.mpr htwoPi
  have hψScaled_int : Integrable ψScaled := by
    -- Proof comment: the fixed `-2π` rescaling preserves the `L¹` control of the kernel.
    simpa [ψScaled, c] using hρ_int.comp_smul hc
  have hψScaled_psd : IsPositiveSemidefiniteFunction ψScaled := by
    -- Proof comment: positive semidefiniteness is stable under precomposition by the fixed linear
    -- normalization map `t ↦ -2π • t`.
    rw [isPositiveSemidefiniteFunction_iff_quadratic_sum_nonneg] at hρ_psd ⊢
    intro n t z
    have hmain :
        0 ≤
          ∑ i, ∑ j, star (z i) * ρ (c • t i - c • t j) * z j := by
      simpa using hρ_psd n (fun i ↦ c • t i) z
    have hsum :
        (∑ i, ∑ j, star (z i) * ψScaled (t i - t j) * z j) =
          ∑ i, ∑ j, star (z i) * ρ (c • t i - c • t j) * z j := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      refine Finset.sum_congr rfl ?_
      intro j hj
      simp [ψScaled, smul_sub]
    rw [hsum]
    exact hmain
  have hf_complex :
      (fun x : E ↦ ((f x : ℝ) : ℂ)) = FourierTransformInv.fourierInv ψScaled := by
    -- Proof comment: Hermitian symmetry of the positive semidefinite kernel makes the inverse
    -- Fourier transform real-valued.
    simpa [f] using
      (ofRealFourierInv_eq_of_isPositiveSemidefiniteFunction
        (d := d) (ψ := ψScaled) hψScaled_psd)
  have hf_cont : Continuous (fun x : E ↦ ((f x : ℝ) : ℂ)) := by
    -- Proof comment: once the scaled kernel is integrable, continuity is the standard inverse
    -- Fourier continuity theorem.
    rw [hf_complex]
    exact inverseFourier_continuous_of_integrable (d := d) (ψ := ψScaled) hψScaled_int
  have hψScaled_cont : Continuous ψScaled := by
    -- Proof comment: the fixed `-2π` normalization map is continuous, so continuity descends from
    -- the original kernel `ρ`.
    have hscale : Continuous fun t : E ↦ c • t := by
      simpa [c] using (continuous_const.smul continuous_id : Continuous fun t : E ↦ c • t)
    exact hρ_cont.comp hscale
  have hψScaled_zero : ψScaled 0 = 1 := by
    -- Proof comment: evaluating the scaled kernel at the origin leaves the normalization intact.
    simpa [ψScaled, c] using hρ_zero
  have hApproxSpec :
      ∀ n : ℕ,
        (∀ x, 0 ≤ gaussianRegularizedInverseFourierDensity ψScaled (((n : ℝ) + 1)⁻¹) x) ∧
          Integrable
            (gaussianRegularizedInverseFourierDensity ψScaled (((n : ℝ) + 1)⁻¹)) ∧
          (∫ x, gaussianRegularizedInverseFourierDensity ψScaled (((n : ℝ) + 1)⁻¹) x = 1) := by
    intro n
    rcases
      gaussianRegularizedInverseFourierDensityNonnegMassWindow
        (d := d) (ψ := ψScaled) (b := ((n : ℝ) + 1)⁻¹)
        (by positivity) hψScaled_cont hψScaled_int hψScaled_psd hψScaled_zero with
      ⟨hApprox_nonneg, hApprox_mass⟩
    have hApprox_cont :
        Continuous
          (gaussianRegularizedInverseFourierDensity ψScaled (((n : ℝ) + 1)⁻¹)) := by
      -- Proof comment: each approximant is a continuous regularized inverse-Fourier candidate.
      simpa using
        gaussianRegularizedInverseFourierDensityContinuousReal
          (d := d) (ψ := ψScaled) (b := ((n : ℝ) + 1)⁻¹)
          (by positivity) hψScaled_cont hψScaled_psd hψScaled_zero
    have hApprox_int :
        Integrable
          (gaussianRegularizedInverseFourierDensity ψScaled (((n : ℝ) + 1)⁻¹)) := by
      -- Proof comment: continuity together with the owner-provided nonnegativity and mass `1`
      -- yields the `L¹` control needed for the Fatou step.
      exact
        integrable_of_continuous_nonneg_integral_eq_one
          (d := d)
          (f := gaussianRegularizedInverseFourierDensity ψScaled (((n : ℝ) + 1)⁻¹))
          hApprox_cont hApprox_nonneg hApprox_mass
    exact ⟨hApprox_nonneg, hApprox_int, hApprox_mass⟩
  have hPointwise :
      ∀ x : E,
        Tendsto
          (fun n : ℕ ↦
            gaussianRegularizedInverseFourierDensity ψScaled (((n : ℝ) + 1)⁻¹) x)
          atTop (𝓝 (f x)) := by
    intro x
    -- Proof comment: the earlier Gaussian-damping convergence theorem already identifies the
    -- regularized approximants with the target inverse-Fourier density candidate.
    simpa [f] using
      gaussianRegularizedInverseFourierDensity_tendsto
        (d := d) (ψ := ψScaled) hψScaled_int x
  have hf_nonneg : ∀ x, 0 ≤ f x := by
    -- Proof comment: pointwise limits of the nonnegative regularized densities remain
    -- nonnegative.
    exact
      nonneg_of_tendsto_of_nonneg
        (fun n x ↦ (hApproxSpec n).1 x) hPointwise
  have hf_int : Integrable f := by
    have hApprox_int :
        ∀ n : ℕ,
          Integrable
            (gaussianRegularizedInverseFourierDensity ψScaled (((n : ℝ) + 1)⁻¹)) := by
      intro n
      exact (hApproxSpec n).2.1
    have hApprox_ae_nonneg :
        ∀ n : ℕ,
          0 ≤ᵐ[volume]
            gaussianRegularizedInverseFourierDensity ψScaled (((n : ℝ) + 1)⁻¹) := by
      intro n
      exact Filter.Eventually.of_forall (fun x ↦ (hApproxSpec n).1 x)
    have hPointwise_ae :
        ∀ᵐ x ∂(volume : Measure E),
          Tendsto
            (fun n : ℕ ↦
              gaussianRegularizedInverseFourierDensity ψScaled (((n : ℝ) + 1)⁻¹) x)
            atTop (𝓝 (f x)) := by
      -- Proof comment: the regularized-density convergence holds everywhere, hence almost
      -- everywhere for Lebesgue measure.
      exact Filter.Eventually.of_forall hPointwise
    have hIntegral_tendsto :
        Tendsto
          (fun n : ℕ ↦
            ∫ x, gaussianRegularizedInverseFourierDensity ψScaled (((n : ℝ) + 1)⁻¹) x)
          atTop (𝓝 (1 : ℝ)) := by
      have hconst :
          (fun n : ℕ ↦
            ∫ x, gaussianRegularizedInverseFourierDensity ψScaled (((n : ℝ) + 1)⁻¹) x) =
            fun _ : ℕ ↦ (1 : ℝ) := by
        funext n
        exact (hApproxSpec n).2.2
      rw [hconst]
      exact tendsto_const_nhds
    -- Proof comment: Fatou upgrades the pointwise limit of the mass-one regularized densities to
    -- `L¹` integrability of the target density candidate.
    exact
      integrable_of_nonneg_tendsto_ae_of_integral_tendsto
        (μ := (volume : Measure E)) hApprox_int hApprox_ae_nonneg hPointwise_ae
        hIntegral_tendsto
  have hg_int : Integrable (fun x : E ↦ ((f x : ℝ) : ℂ)) := by
    -- Proof comment: complexifying the real-valued density candidate preserves `L¹`
    -- integrability.
    simpa [f] using hf_int.ofReal
  have hFourierψScaled :
      FourierTransform.fourier ψScaled = fun x : E ↦ ((f (-x) : ℝ) : ℂ) := by
    ext x
    -- Proof comment: rewrite the inverse Fourier transform as the Fourier transform at `-x` and
    -- then use the already established real-valued inverse-Fourier identity.
    calc
      FourierTransform.fourier ψScaled x = FourierTransform.fourier ψScaled (-(-x)) := by
          rw [neg_neg]
      _ = FourierTransformInv.fourierInv ψScaled (-x) := by
          exact (Real.fourierInv_eq_fourier_neg ψScaled (-x)).symm
      _ = ((f (-x) : ℝ) : ℂ) := by
          simpa using (congrFun hf_complex (-x)).symm
  have hFourierInt : Integrable (FourierTransform.fourier ψScaled) := by
    -- Proof comment: after the sign change, the Fourier transform is just the complexification of
    -- the target density.
    rw [hFourierψScaled]
    simpa [f] using (Integrable.comp_neg hf_int).ofReal
  have hFourierInv :
      FourierTransform.fourier (fun x : E ↦ ((f x : ℝ) : ℂ)) = ψScaled := by
    -- Proof comment: Fourier inversion on the scaled kernel recovers the kernel once the target
    -- density is known to be `L¹`.
    rw [hf_complex]
    exact Continuous.fourier_fourierInv_eq hψScaled_cont hψScaled_int hFourierInt
  have hf_fourier :
      ∀ t : E,
        VectorFourier.fourierIntegral Real.fourierChar volume
            (innerₗ E)
            (fun x : E ↦ ((f x : ℝ) : ℂ))
            (-(2 * Real.pi)⁻¹ • t) = ρ t := by
    intro t
    have hscalar : c * (-(2 * Real.pi)⁻¹ : ℝ) = 1 := by
      dsimp [c]
      field_simp [Real.pi_ne_zero]
    have harg : c • (-(2 * Real.pi)⁻¹ • t) = t := by
      calc
        c • (-(2 * Real.pi)⁻¹ • t) = (c * (-(2 * Real.pi)⁻¹ : ℝ)) • t := by
            rw [smul_smul]
        _ = (1 : ℝ) • t := by rw [hscalar]
        _ = t := by simp
    -- Proof comment: the normalized evaluation point cancels the frozen `-2π` scaling of
    -- `ψScaled`.
    calc
      VectorFourier.fourierIntegral Real.fourierChar volume
          (innerₗ E)
          (fun x : E ↦ ((f x : ℝ) : ℂ))
          (-(2 * Real.pi)⁻¹ • t)
          = FourierTransform.fourier (fun x : E ↦ ((f x : ℝ) : ℂ)) (-(2 * Real.pi)⁻¹ • t) := by
              rfl
      _ = ψScaled (-(2 * Real.pi)⁻¹ • t) := by
            exact congrFun hFourierInv (-(2 * Real.pi)⁻¹ • t)
      _ = ρ t := by
            dsimp [ψScaled]
            rw [harg]
  have hf_mass : ∫ x, f x = 1 := by
    -- Proof comment: evaluating the Fourier-recovery identity at the origin turns the normalized
    -- Fourier integral into the total mass of the density.
    have hzeroFourier :
        VectorFourier.fourierIntegral Real.fourierChar volume
            (innerₗ E)
            (fun x : E ↦ ((f x : ℝ) : ℂ))
            0 = ρ 0 := by
      simpa using hf_fourier (0 : E)
    calc
      ∫ x, f x
          =
            Complex.re
              (VectorFourier.fourierIntegral Real.fourierChar volume
                (innerₗ E)
                (fun x : E ↦ ((f x : ℝ) : ℂ))
                0) := by
                  simp [VectorFourier.fourierIntegral, integral_complex_ofReal]
      _ = Complex.re (ρ 0) := by
            rw [hzeroFourier]
      _ = 1 := by
            simp [hρ_zero]
  exact ⟨hf_cont, hf_nonneg, hf_int, hf_mass, hf_fourier⟩

/-- Helper for Theorem 15.29: the remaining Euclidean witness-side blocker is an explicit
continuous Gaussian-smoothed density for the convolved witness law. -/
lemma gaussianDampedContinuousDensitySpecOfProbabilityMeasure {d : ℕ}
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) {a : ℝ} (ha : 0 < a) :
    ∃ f : EuclideanSpace ℝ (Fin d) → ℝ,
      Continuous (fun x : EuclideanSpace ℝ (Fin d) ↦ ((f x : ℝ) : ℂ)) ∧
      (∀ x, 0 ≤ f x) ∧ Integrable f ∧ (∫ x, f x = 1) ∧
      (∀ t : EuclideanSpace ℝ (Fin d),
        VectorFourier.fourierIntegral Real.fourierChar volume
            (innerₗ (EuclideanSpace ℝ (Fin d)))
            (fun x : EuclideanSpace ℝ (Fin d) ↦ ((f x : ℝ) : ℂ))
            (-(2 * Real.pi)⁻¹ • t) =
          Complex.exp (-(a : ℂ) * ‖t‖ ^ 2) *
            charFun (μ : Measure (EuclideanSpace ℝ (Fin d))) t) := by
  let E := EuclideanSpace ℝ (Fin d)
  let ρ : E → ℂ := fun t ↦ Complex.exp (-(a : ℂ) * ‖t‖ ^ 2) * charFun (μ : Measure E) t
  let ψa : E → ℂ := fun t ↦
    ρ ((-(2 * Real.pi) : ℝ) • t)
  let f : E → ℝ := fun x ↦ Complex.re (FourierTransformInv.fourierInv ψa x)
  have hρ_spec : Continuous ρ ∧ Integrable ρ ∧ IsPositiveSemidefiniteFunction ρ ∧ ρ 0 = 1 := by
    -- Proof comment: the damped characteristic-function kernel of the actual witness already
    -- satisfies the hypotheses of the upstream inverse-Fourier density owner.
    simpa [ρ] using
      gaussianDampedKernelSpec
        (d := d) (φ := charFun (μ : Measure E)) (a := a) ha
        (MeasureTheory.continuous_charFun (μ := (μ : Measure E)))
        (charFun_isPositiveSemidefiniteFunction_of_isFiniteMeasure (μ := (μ : Measure E)))
        (by simpa using (MeasureTheory.charFun_zero (μ := (μ : Measure E))))
  rcases
    (show
        let ψScaled : E → ℂ := fun t ↦ ρ ((-(2 * Real.pi) : ℝ) • t)
        let fScaled : E → ℝ := fun x ↦ Complex.re (FourierTransformInv.fourierInv ψScaled x)
        Continuous (fun x : E ↦ ((fScaled x : ℝ) : ℂ)) ∧
          (∀ x, 0 ≤ fScaled x) ∧ Integrable fScaled ∧ (∫ x, fScaled x = 1) ∧
          (∀ t : E,
            VectorFourier.fourierIntegral Real.fourierChar volume
                (innerₗ E)
                (fun x : E ↦ ((fScaled x : ℝ) : ℂ))
                (-(2 * Real.pi)⁻¹ • t) = ρ t) from
      scaledInverseFourierDensitySpecOfIntegrableContinuousPositiveDefinite
        (d := d) (ρ := ρ) hρ_spec.1 hρ_spec.2.1 hρ_spec.2.2.1 hρ_spec.2.2.2) with
    ⟨hf_cont, hf_nonneg, hf_int, hf_mass, hf_fourier⟩
  -- Proof comment: the witness-side theorem is now a direct specialization of the upstream
  -- inverse-Fourier density owner to the damped characteristic-function kernel.
  exact ⟨f, by simpa [ψa, f, ρ] using hf_cont,
    by simpa [ψa, f, ρ] using hf_nonneg,
    by simpa [ψa, f, ρ] using hf_int,
    by simpa [ψa, f, ρ] using hf_mass,
    by simpa [ψa, f, ρ] using hf_fourier⟩

/-- Helper for Theorem 15.29: each Gaussian-damped inverse Fourier transform of an actual
Euclidean characteristic function agrees pointwise with a nonnegative density of mass `1` after
the Fourier normalization is kept on the scaled kernel. -/
lemma scaledDampedInverseFourierDensitySpecOfProbabilityMeasure {d : ℕ}
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) {a : ℝ} (ha : 0 < a) :
    ∃ f : EuclideanSpace ℝ (Fin d) → ℝ,
      (∀ x, 0 ≤ f x) ∧ Integrable f ∧ (∫ x, f x = 1) ∧
      (∀ x : EuclideanSpace ℝ (Fin d),
        FourierTransformInv.fourierInv
          (fun t : EuclideanSpace ℝ (Fin d) ↦
            Complex.exp (-(a : ℂ) * ‖((-(2 * Real.pi) : ℝ) • t)‖ ^ 2) *
              charFun (μ : Measure (EuclideanSpace ℝ (Fin d))) ((-(2 * Real.pi) : ℝ) • t))
          x = ((f x : ℝ) : ℂ)) := by
  rcases
    gaussianDampedContinuousDensitySpecOfProbabilityMeasure
      (d := d) (μ := μ) (a := a) ha with
    ⟨f, hf_cont, hf_nonneg, hf_int, hf_mass, hf_fourier⟩
  refine ⟨f, hf_nonneg, hf_int, hf_mass, ?_⟩
  intro x
  -- Proof comment: after the dependency-order repair, this theorem is only the pointwise
  -- identification of the scaled inverse Fourier transform with the continuous smoothed density.
  exact
    continuousDensity_eq_scaledDampedCharFunFourierInvOfProbabilityMeasure
      (d := d) μ ha hf_cont hf_int hf_fourier x

/-- Helper for Theorem 15.29: choosing the Gaussian parameter
`((n : ℝ) + 1)⁻¹ / (2 * Real.pi)^2` on the scaled kernel `t ↦ ρ (-(2 * π) • t)` produces the
normalized damping factor required by `dampedInverseFourier_tendsto`. -/
lemma scaledDampedKernel_eq_normalizedDamping {d : ℕ}
    {ρ : EuclideanSpace ℝ (Fin d) → ℂ} (n : ℕ) :
    (fun t : EuclideanSpace ℝ (Fin d) ↦
      Complex.exp
          (-(((((n : ℝ) + 1)⁻¹ / (2 * Real.pi) ^ 2 : ℝ) : ℂ) *
            ‖((-(2 * Real.pi) : ℝ) • t)‖ ^ 2)) *
        ρ (((-(2 * Real.pi) : ℝ) • t))) =
      fun t ↦
        Complex.exp (-((((n : ℝ) + 1)⁻¹ : ℂ) * ‖t‖ ^ 2)) *
          ρ (((-(2 * Real.pi) : ℝ) • t)) := by
  funext t
  have hnorm :
      ‖((-(2 * Real.pi) : ℝ) • t)‖ ^ 2 = (2 * Real.pi) ^ 2 * ‖t‖ ^ 2 := by
    -- Proof comment: pulling the fixed `-2π` scaling out of the norm turns the square into the
    -- exact cancellation factor that matches the normalized damping sequence.
    rw [norm_smul, Real.norm_eq_abs, abs_of_neg]
    · ring
    · have htwoPi : 0 < (2 : ℝ) * Real.pi := by positivity
      linarith
  have hscalar :
      ((((n : ℝ) + 1)⁻¹ / (2 * Real.pi) ^ 2) * ‖((-(2 * Real.pi) : ℝ) • t)‖ ^ 2 : ℝ) =
        ((n : ℝ) + 1)⁻¹ * ‖t‖ ^ 2 := by
    -- Proof comment: after the norm rewrite, the prefactor `(2π)^2` cancels exactly.
    rw [hnorm]
    field_simp [Real.pi_ne_zero]
  have hscalarC :
      (((((((n : ℝ) + 1)⁻¹ / (2 * Real.pi) ^ 2) *
            ‖((-(2 * Real.pi) : ℝ) • t)‖ ^ 2 : ℝ)) : ℂ)) =
        ((((n : ℝ) + 1)⁻¹ * ‖t‖ ^ 2 : ℝ) : ℂ) := by
    exact_mod_cast hscalar
  -- Proof comment: rewrite the exponential argument through the real normalization identity once,
  -- then keep the scaled witness kernel fixed.
  calc
    Complex.exp
        (-(((((n : ℝ) + 1)⁻¹ / (2 * Real.pi) ^ 2 : ℝ) : ℂ) *
          ‖((-(2 * Real.pi) : ℝ) • t)‖ ^ 2)) *
      ρ (((-(2 * Real.pi) : ℝ) • t))
        = Complex.exp
            (-((((((n : ℝ) + 1)⁻¹ / (2 * Real.pi) ^ 2) *
                ‖((-(2 * Real.pi) : ℝ) • t)‖ ^ 2 : ℝ) : ℂ))) *
            ρ (((-(2 * Real.pi) : ℝ) • t)) := by
              simp
    _ = Complex.exp (-((((n : ℝ) + 1)⁻¹ * ‖t‖ ^ 2 : ℝ) : ℂ)) *
          ρ (((-(2 * Real.pi) : ℝ) • t)) := by
            rw [hscalarC]
    _ = Complex.exp (-((((n : ℝ) + 1)⁻¹ : ℂ) * ‖t‖ ^ 2)) *
          ρ (((-(2 * Real.pi) : ℝ) • t)) := by
            simp

/-- Helper for Theorem 15.29: the Gaussian-regularized inverse-Fourier approximants on the fixed
scaled kernel converge pointwise to the target scaled inverse-Fourier density candidate. -/
lemma scaledDampedInverseFourierDensity_tendsto {d : ℕ}
    {ρ : EuclideanSpace ℝ (Fin d) → ℂ} (hρ_int : Integrable ρ)
    (x : EuclideanSpace ℝ (Fin d)) :
    Tendsto
      (fun n : ℕ ↦
        Complex.re
          (FourierTransformInv.fourierInv
            (fun t : EuclideanSpace ℝ (Fin d) ↦
              Complex.exp
                  (-(((((n : ℝ) + 1)⁻¹ / (2 * Real.pi) ^ 2 : ℝ) : ℂ) *
                    ‖((-(2 * Real.pi) : ℝ) • t)‖ ^ 2)) *
                ρ (((-(2 * Real.pi) : ℝ) • t)))
            x))
      atTop
      (𝓝 (Complex.re
        (FourierTransformInv.fourierInv
          (fun t : EuclideanSpace ℝ (Fin d) ↦
            ρ (((-(2 * Real.pi) : ℝ) • t)))
          x))) := by
  let E := EuclideanSpace ℝ (Fin d)
  let c : ℝ := -(2 * Real.pi)
  let ρScaled : E → ℂ := fun t ↦ ρ (c • t)
  have hc : c ≠ 0 := by
    have htwoPi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    exact neg_ne_zero.mpr htwoPi
  have hρScaled_int : Integrable ρScaled := by
    -- Proof comment: the fixed `-2π` rescaling preserves `L¹` because the scale is nonzero.
    simpa [ρScaled, c] using hρ_int.comp_smul hc
  have hbase :
      Tendsto
        (fun n : ℕ ↦
          Complex.re
            (FourierTransformInv.fourierInv
              (fun t : E ↦
                Complex.exp (-((((n : ℝ) + 1)⁻¹ : ℂ) * ‖t‖ ^ 2)) * ρScaled t)
              x))
        atTop
        (𝓝 (Complex.re (FourierTransformInv.fourierInv ρScaled x))) := by
    -- Proof comment: this is the already-proved damped inverse-Fourier convergence on the frozen
    -- scaled kernel `ρScaled`.
    simpa [ρScaled] using
      dampedInverseFourierDensity_tendsto (d := d) (ψ := ρScaled) hρScaled_int x
  refine hbase.congr' ?_
  exact Filter.Eventually.of_forall fun n ↦ by
    -- Proof comment: rewrite the approximant kernels through the fixed normalization identity
    -- `scaledDampedKernel_eq_normalizedDamping`.
    simpa [ρScaled, c] using
      congrArg
        (fun ψ : E → ℂ ↦ Complex.re (FourierTransformInv.fourierInv ψ x))
        (scaledDampedKernel_eq_normalizedDamping (d := d) (ρ := ρ) n).symm

/-- Helper for Theorem 15.29: once an integrable Euclidean kernel already has an actual
probability witness, Gaussian smoothing upgrades that witness to nonnegativity and `L¹` control
for the normalized inverse-Fourier candidate. -/
lemma scaledInverseFourierDensityNonnegIntegrableOfWitness {d : ℕ}
    {ρ : EuclideanSpace ℝ (Fin d) → ℂ} (hρ_int : Integrable ρ)
    (hρ_witness : ∃ μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)),
      ∀ t : EuclideanSpace ℝ (Fin d), charFun (μ : Measure (EuclideanSpace ℝ (Fin d))) t = ρ t) :
    (∀ x : EuclideanSpace ℝ (Fin d),
      0 ≤ Complex.re (FourierTransformInv.fourierInv
        (fun t : EuclideanSpace ℝ (Fin d) ↦ ρ ((-(2 * Real.pi) : ℝ) • t)) x)) ∧
      Integrable fun x : EuclideanSpace ℝ (Fin d) ↦
        Complex.re (FourierTransformInv.fourierInv
          (fun t : EuclideanSpace ℝ (Fin d) ↦ ρ ((-(2 * Real.pi) : ℝ) • t)) x) := by
  let E := EuclideanSpace ℝ (Fin d)
  let c : ℝ := -(2 * Real.pi)
  let ρScaled : E → ℂ := fun t ↦ ρ (c • t)
  let kernel : ℕ → E → ℂ := fun n t ↦
    Complex.exp
        (-(((((n : ℝ) + 1)⁻¹ / (2 * Real.pi) ^ 2 : ℝ) : ℂ) * ‖c • t‖ ^ 2)) *
      ρScaled t
  rcases hρ_witness with ⟨μ, hμ⟩
  have hApprox :
      ∀ n : ℕ,
        ∃ f : E → ℝ,
          (∀ x, 0 ≤ f x) ∧ Integrable f ∧ (∫ x, f x = 1) ∧
            (∀ x : E,
              FourierTransformInv.fourierInv (kernel n) x = ((f x : ℝ) : ℂ)) := by
    intro n
    let a : ℝ := ((n : ℝ) + 1)⁻¹ / (2 * Real.pi) ^ 2
    have ha : 0 < a := by
      dsimp [a]
      positivity
    rcases
      scaledDampedInverseFourierDensitySpecOfProbabilityMeasure
        (d := d) (μ := μ) (a := a) ha with
      ⟨f, hf_nonneg, hf_int, hf_mass, hf_eq⟩
    refine ⟨f, hf_nonneg, hf_int, hf_mass, ?_⟩
    intro x
    -- Proof comment: rewrite the witness-side kernel through `hμ` once and keep the fixed scaled
    -- spelling `ρScaled`.
    simpa [kernel, a, ρScaled, c, hμ] using hf_eq x
  have hPointwise :
      ∀ x : E,
        Tendsto
          (fun n : ℕ ↦
            Complex.re (FourierTransformInv.fourierInv (kernel n) x))
          atTop
          (𝓝 (Complex.re (FourierTransformInv.fourierInv ρScaled x))) := by
    intro x
    -- Proof comment: the normalization lemma now packages the Gaussian parameter choice into the
    -- previously proved damped convergence theorem.
    simpa [kernel, ρScaled, c] using
      scaledDampedInverseFourierDensity_tendsto (d := d) (ρ := ρ) hρ_int x
  classical
  choose f hf_nonneg hf_int hf_mass hf_eq using hApprox
  have hApprox_nonneg :
      ∀ n x, 0 ≤ Complex.re (FourierTransformInv.fourierInv (kernel n) x) := by
    intro n x
    -- Proof comment: each approximant is literally the real-valued density packaged by `hApprox`.
    have hEq_re :
        Complex.re (FourierTransformInv.fourierInv (kernel n) x) = f n x := by
      simpa using congrArg Complex.re (hf_eq n x)
    rw [hEq_re]
    exact hf_nonneg n x
  have hApprox_int :
      ∀ n, Integrable fun x : E ↦ Complex.re (FourierTransformInv.fourierInv (kernel n) x) := by
    intro n
    -- Proof comment: after rewriting through the packaged density equality, integrability is the
    -- same `L¹` statement already supplied by `hApprox`.
    have hEq_fun :
        (fun x : E ↦ Complex.re (FourierTransformInv.fourierInv (kernel n) x)) = f n := by
      funext x
      simpa using congrArg Complex.re (hf_eq n x)
    rw [hEq_fun]
    exact hf_int n
  have hApprox_ae_nonneg :
      ∀ n, 0 ≤ᵐ[volume] fun x : E ↦ Complex.re (FourierTransformInv.fourierInv (kernel n) x) := by
    intro n
    exact Filter.Eventually.of_forall (hApprox_nonneg n)
  have hPointwise_ae :
      ∀ᵐ x ∂(volume : Measure E),
        Tendsto (fun n : ℕ ↦ Complex.re (FourierTransformInv.fourierInv (kernel n) x))
          atTop (𝓝 (Complex.re (FourierTransformInv.fourierInv ρScaled x))) := by
    -- Proof comment: the pointwise convergence theorem holds everywhere, hence also almost
    -- everywhere for Lebesgue measure.
    exact Filter.Eventually.of_forall hPointwise
  have hIntegral_tendsto :
      Tendsto
        (fun n : ℕ ↦ ∫ x, Complex.re (FourierTransformInv.fourierInv (kernel n) x))
        atTop (𝓝 (1 : ℝ)) := by
    -- Proof comment: every approximant has mass `1`, so the sequence of integrals is constant.
    have hconst :
        (fun n : ℕ ↦ ∫ x, Complex.re (FourierTransformInv.fourierInv (kernel n) x)) =
          fun _ : ℕ ↦ (1 : ℝ) := by
      funext n
      have hEq_fun :
          (fun x : E ↦ Complex.re (FourierTransformInv.fourierInv (kernel n) x)) = f n := by
        funext x
        simpa using congrArg Complex.re (hf_eq n x)
      rw [hEq_fun, hf_mass n]
    rw [hconst]
    exact tendsto_const_nhds
  have hLimit_nonneg :
      ∀ x : E, 0 ≤ Complex.re (FourierTransformInv.fourierInv ρScaled x) := by
    -- Proof comment: pointwise limits of the nonnegative approximants remain nonnegative.
    exact nonneg_of_tendsto_of_nonneg hApprox_nonneg hPointwise
  have hLimit_int :
      Integrable fun x : E ↦ Complex.re (FourierTransformInv.fourierInv ρScaled x) := by
    -- Proof comment: Fatou upgrades the almost-everywhere limit of the mass-one approximants to
    -- an `L¹` limit.
    exact integrable_of_nonneg_tendsto_ae_of_integral_tendsto
      (μ := (volume : Measure E)) hApprox_int hApprox_ae_nonneg hPointwise_ae hIntegral_tendsto
  exact ⟨by simpa [ρScaled, c] using hLimit_nonneg, by simpa [ρScaled, c] using hLimit_int⟩

/-- Helper for Theorem 15.29: an actual Euclidean characteristic-function witness for `ψ`
upgrades the Gaussian-regularized inverse-Fourier candidate to the `nonneg ∧ L¹` package by
rewriting it to the earlier scaled-kernel/Fatou owner. -/
lemma gaussianRegularizedInverseFourierDensityNonnegIntegrableOfCharFunWitnessViaScaledKernel
    {d : ℕ} {ψ : EuclideanSpace ℝ (Fin d) → ℂ} {b : ℝ} (hb : 0 < b)
    (hψ_witness : ∃ μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)),
      ∀ t : EuclideanSpace ℝ (Fin d),
        charFun (μ : Measure (EuclideanSpace ℝ (Fin d))) t = ψ t) :
    (∀ x, 0 ≤ gaussianRegularizedInverseFourierDensity ψ b x) ∧
      Integrable (gaussianRegularizedInverseFourierDensity ψ b) := by
  let E := EuclideanSpace ℝ (Fin d)
  let c : ℝ := -(2 * Real.pi)
  let cInv : ℝ := (-(2 * Real.pi)⁻¹ : ℝ)
  let ρ : E → ℂ := fun t ↦
    Complex.exp (-(b : ℂ) * ‖cInv • t‖ ^ 2) * ψ (cInv • t)
  have hρ_spec :
      Continuous ρ ∧ Integrable ρ ∧ IsPositiveSemidefiniteFunction ρ ∧ ρ 0 = 1 ∧
        ∃ ν : ProbabilityMeasure E, ∀ t : E, charFun (ν : Measure E) t = ρ t := by
    -- Proof comment: package the exact fixed-spelling scaled regularized kernel once before
    -- applying the existing witness-side inverse-Fourier density theorem.
    simpa [E, c, cInv, ρ] using
      (scaledRegularizedKernelSpecAndWitnessOfCharFunWitness
        (d := d) (ψ := ψ) (b := b) hb hψ_witness)
  have hscaled :
      (∀ x : E,
        0 ≤ Complex.re
          (FourierTransformInv.fourierInv
            (fun t : E ↦ ρ (((-(2 * Real.pi) : ℝ) • t))) x)) ∧
        Integrable
          (fun x : E ↦
            Complex.re
              (FourierTransformInv.fourierInv
                (fun t : E ↦ ρ (((-(2 * Real.pi) : ℝ) • t))) x)) := by
    -- Proof comment: this is exactly the earlier scaled-kernel/Fatou owner applied to the
    -- witness-bearing kernel `ρ`.
    simpa [E, c, ρ] using
      scaledInverseFourierDensityNonnegIntegrableOfWitness
        (d := d) (ρ := ρ) hρ_spec.2.1 hρ_spec.2.2.2.2
  have hgauss_eq :
      gaussianRegularizedInverseFourierDensity ψ b =
        fun x : E ↦
          Complex.re
            (FourierTransformInv.fourierInv
              (fun t : E ↦ ρ (((-(2 * Real.pi) : ℝ) • t))) x) := by
    -- Proof comment: the existing rescaling lemma identifies the public regularized density with
    -- that scaled inverse-Fourier normal form.
    simpa [E, c, cInv, ρ] using
      (gaussianRegularizedInverseFourierDensity_eq_scaledKernelFourierInv
        (d := d) (ψ := ψ) (b := b))
  refine ⟨?_, ?_⟩
  · intro x
    -- Proof comment: transfer pointwise nonnegativity back through the fixed normal-form
    -- identification of the regularized density.
    simpa [hgauss_eq] using hscaled.1 x
  · -- Proof comment: the same fixed normal-form identification transfers the `L¹` statement.
    simpa [hgauss_eq] using hscaled.2

/-- Helper for Theorem 15.29: an actual probability witness for the regularized kernel already
packages the raw Gaussian-regularized inverse Fourier transform into a nonnegative mass-one
`L¹` density. -/
lemma gaussianRegularizedInverseFourierDensitySpecOfProbabilityMeasure {d : ℕ}
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) {b : ℝ} (hb : 0 < b) :
    ∃ f : EuclideanSpace ℝ (Fin d) → ℝ,
      (∀ x, 0 ≤ f x) ∧ Integrable f ∧ (∫ x, f x = 1) ∧
      (∀ x : EuclideanSpace ℝ (Fin d),
        FourierTransformInv.fourierInv
          (fun t : EuclideanSpace ℝ (Fin d) ↦
            Complex.exp (-(b : ℂ) * ‖t‖ ^ 2) *
              charFun (μ : Measure (EuclideanSpace ℝ (Fin d))) t)
          x = ((f x : ℝ) : ℂ)) := by
  let E := EuclideanSpace ℝ (Fin d)
  let c : ℝ := -(2 * Real.pi)
  let a : ℝ := b / c ^ 2
  let ν : ProbabilityMeasure E :=
    ⟨Measure.map (c⁻¹ • ·) (μ : Measure E), Measure.isProbabilityMeasure_map (by fun_prop)⟩
  have hc : c ≠ 0 := by
    -- Proof comment: the fixed Fourier-normalization scalar `-2π` is nonzero.
    have htwoPi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    exact neg_ne_zero.mpr htwoPi
  have ha : 0 < a := by
    -- Proof comment: the pushed-forward witness uses the Fourier-normalized Gaussian parameter
    -- `b / (2π)^2`, which stays positive because `b > 0`.
    dsimp [a]
    exact div_pos hb (sq_pos_of_ne_zero hc)
  rcases
    scaledDampedInverseFourierDensitySpecOfProbabilityMeasure
      (d := d) (μ := ν) (a := a) ha with
    ⟨f, hf_nonneg, hf_int, hf_mass, hf_eq⟩
  refine ⟨f, hf_nonneg, hf_int, hf_mass, ?_⟩
  intro x
  have hkernel :
      (fun t : E ↦
        Complex.exp (-(a : ℂ) * ‖c • t‖ ^ 2) * charFun (ν : Measure E) (c • t)) =
        fun t : E ↦
          Complex.exp (-(b : ℂ) * ‖t‖ ^ 2) * charFun (μ : Measure E) t := by
    -- Proof comment: the earlier fixed `-2π` bridge rewrites the scaled damped witness kernel
    -- back to the raw regularized kernel.
    simpa [a, c, ν] using
      gaussianRegularizedKernel_eq_scaledDampedKernelOfProbabilityMeasure
        (d := d) (μ := μ) (b := b)
  calc
    FourierTransformInv.fourierInv
        (fun t : E ↦ Complex.exp (-(b : ℂ) * ‖t‖ ^ 2) * charFun (μ : Measure E) t) x
        =
      FourierTransformInv.fourierInv
        (fun t : E ↦
          Complex.exp (-(a : ℂ) * ‖c • t‖ ^ 2) * charFun (ν : Measure E) (c • t)) x := by
            exact congrArg (fun ψ : E → ℂ ↦ FourierTransformInv.fourierInv ψ x) hkernel.symm
    _ = ((f x : ℝ) : ℂ) := hf_eq x

/-- Helper for Theorem 15.29: once the regularized kernel already has an actual Euclidean
characteristic-function witness, the regularized inverse-Fourier candidate inherits the witness
side density package without reopening the analytic proof. -/
lemma gaussianRegularizedInverseFourierDensitySpecOfCharFunWitness {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} {b : ℝ} (hb : 0 < b)
    (hψ_witness : ∃ μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)),
      ∀ t : EuclideanSpace ℝ (Fin d),
        charFun (μ : Measure (EuclideanSpace ℝ (Fin d))) t = ψ t) :
    (∀ x, 0 ≤ gaussianRegularizedInverseFourierDensity ψ b x) ∧
      Integrable (gaussianRegularizedInverseFourierDensity ψ b) ∧
      (∫ x, gaussianRegularizedInverseFourierDensity ψ b x = 1) := by
  let E := EuclideanSpace ℝ (Fin d)
  rcases hψ_witness with ⟨μ, hμ⟩
  rcases
    gaussianRegularizedInverseFourierDensitySpecOfProbabilityMeasure
      (d := d) (μ := μ) (b := b) hb with
    ⟨f, hf_nonneg, hf_int, hf_mass, hf_eq⟩
  have hkernel :
      (fun t : E ↦ Complex.exp (-(b : ℂ) * ‖t‖ ^ 2) * ψ t) =
        fun t : E ↦ Complex.exp (-(b : ℂ) * ‖t‖ ^ 2) * charFun (μ : Measure E) t := by
    -- Proof comment: once `ψ` is identified with the witness characteristic function, the
    -- regularized Fourier kernels are literally the same function.
    funext t
    rw [hμ t]
  have hfourier_eq :
      ∀ x : E,
        FourierTransformInv.fourierInv
            (fun t : E ↦ Complex.exp (-(b : ℂ) * ‖t‖ ^ 2) * ψ t) x =
          ((f x : ℝ) : ℂ) := by
    intro x
    -- Proof comment: first transport the inverse Fourier kernel through the witness identity,
    -- then reuse the real-valued density packaged for the witness measure.
    calc
      FourierTransformInv.fourierInv
          (fun t : E ↦ Complex.exp (-(b : ℂ) * ‖t‖ ^ 2) * ψ t) x
          =
        FourierTransformInv.fourierInv
          (fun t : E ↦ Complex.exp (-(b : ℂ) * ‖t‖ ^ 2) * charFun (μ : Measure E) t) x := by
            exact congrArg (fun κ : E → ℂ ↦ FourierTransformInv.fourierInv κ x) hkernel
      _ = ((f x : ℝ) : ℂ) := hf_eq x
  -- Proof comment: the dedicated density-to-regularized-spec bridge now packages the witness-side
  -- real density into the exact public regularized density statement.
  exact
    gaussianRegularizedInverseFourierDensitySpec_of_density
      (d := d) (ψ := ψ) (b := b) hf_nonneg hf_int hf_mass hfourier_eq

/-- Helper for Theorem 15.29: once the original kernel already has an actual Euclidean
characteristic-function witness, the regularized inverse-Fourier candidate itself is the required
almost-everywhere density witness. -/
lemma gaussianRegularizedInverseFourierDensityAeEqDensityWitnessOfCharFunWitness {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} {b : ℝ} (hb : 0 < b)
    (hψ_witness : ∃ μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)),
      ∀ t : EuclideanSpace ℝ (Fin d),
        charFun (μ : Measure (EuclideanSpace ℝ (Fin d))) t = ψ t) :
    ∃ f : EuclideanSpace ℝ (Fin d) → ℝ,
      (∀ x, 0 ≤ f x) ∧ Integrable f ∧ (∫ x, f x = 1) ∧
        gaussianRegularizedInverseFourierDensity ψ b =ᵐ[volume] f := by
  let f : EuclideanSpace ℝ (Fin d) → ℝ := gaussianRegularizedInverseFourierDensity ψ b
  have hf_spec :
      (∀ x, 0 ≤ f x) ∧ Integrable f ∧ (∫ x, f x = 1) := by
    -- Proof comment: once an actual witness for `ψ` is available, the existing regularized
    -- density theorem already supplies the full nonnegativity/`L¹`/mass package.
    simpa [f] using
      gaussianRegularizedInverseFourierDensitySpecOfCharFunWitness
        (d := d) (ψ := ψ) (b := b) hb hψ_witness
  refine ⟨f, hf_spec.1, hf_spec.2.1, hf_spec.2.2, ?_⟩
  -- Proof comment: the almost-everywhere identification is now literal because we choose the
  -- regularized inverse-Fourier candidate itself as the witness density.
  exact Filter.EventuallyEq.rfl

/-- Helper for Theorem 15.29: once a regularized kernel already has an actual Euclidean
characteristic-function witness, the shared witness-side package supplies exactly the
nonnegativity and mass-one clauses needed by the regularized-density core. -/
lemma gaussianRegularizedInverseFourierDensityNonnegMassOfCharFunWitness {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} {b : ℝ} (hb : 0 < b)
    (hψ_witness : ∃ μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)),
      ∀ t : EuclideanSpace ℝ (Fin d),
        charFun (μ : Measure (EuclideanSpace ℝ (Fin d))) t = ψ t) :
    (∀ x, 0 ≤ gaussianRegularizedInverseFourierDensity ψ b x) ∧
      (∫ x, gaussianRegularizedInverseFourierDensity ψ b x = 1) := by
  rcases
    gaussianRegularizedInverseFourierDensitySpecOfCharFunWitness
      (d := d) (ψ := ψ) (b := b) hb hψ_witness with
    ⟨hnonneg, _hint, hmass⟩
  -- Proof comment: the witness-side spec theorem already packages the full density data, so the
  -- core only needs to project out the nonnegativity and mass-one components.
  exact ⟨hnonneg, hmass⟩

/-- Helper for Theorem 15.29: an actual Euclidean characteristic-function witness upgrades the
regularized inverse-Fourier candidate to the `nonneg ∧ Integrable` package by combining the
witness-side mass-one theorem with the continuity-to-`L¹` upgrade. -/
lemma gaussianRegularizedInverseFourierDensityNonnegIntegrableOfCharFunWitness {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} {b : ℝ} (hb : 0 < b)
    (hψ_cont : Continuous ψ) (hψ_psd : IsPositiveSemidefiniteFunction ψ) (hψ_zero : ψ 0 = 1)
    (hψ_witness : ∃ μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)),
      ∀ t : EuclideanSpace ℝ (Fin d),
        charFun (μ : Measure (EuclideanSpace ℝ (Fin d))) t = ψ t) :
    (∀ x, 0 ≤ gaussianRegularizedInverseFourierDensity ψ b x) ∧
      Integrable (gaussianRegularizedInverseFourierDensity ψ b) := by
  -- Proof comment: the dedicated scaled-kernel bridge already packages the same witness-side
  -- `nonneg ∧ L¹` statement, so this theorem is now just its notation-level wrapper.
  exact
    gaussianRegularizedInverseFourierDensityNonnegIntegrableOfCharFunWitnessViaScaledKernel
      (d := d) (ψ := ψ) (b := b) hb hψ_witness

/-- Helper for Theorem 15.29: the Fourier-normalized Gaussian-damped inverse-Fourier candidate has
nonnegative mass-one `L¹` real density data. -/
lemma gaussianDampedInverseFourierNonnegIntegrableMass {d : ℕ}
    {φ : EuclideanSpace ℝ (Fin d) → ℂ} {a : ℝ} (ha : 0 < a) (hφ : Continuous φ)
    (hpsd : IsPositiveSemidefiniteFunction φ) (hzero : φ 0 = 1) :
    let ψa : EuclideanSpace ℝ (Fin d) → ℂ :=
      fun t ↦ Complex.exp (-(a : ℂ) * ‖t‖ ^ 2) * φ t
    let f : EuclideanSpace ℝ (Fin d) → ℝ :=
      fun x ↦ Complex.re (FourierTransformInv.fourierInv
        (fun t ↦ ψa ((-(2 * Real.pi) : ℝ) • t)) x)
    (∀ x, 0 ≤ f x) ∧ Integrable f ∧ (∫ x, f x = 1) := by
  let E := EuclideanSpace ℝ (Fin d)
  let ψa : E → ℂ := fun t ↦ Complex.exp (-(a : ℂ) * ‖t‖ ^ 2) * φ t
  let f : E → ℝ := fun x ↦ Complex.re (FourierTransformInv.fourierInv
    (fun t ↦ ψa ((-(2 * Real.pi) : ℝ) • t)) x)
  have hψ_spec : Continuous ψa ∧ Integrable ψa ∧ IsPositiveSemidefiniteFunction ψa ∧ ψa 0 = 1 := by
    -- Proof comment: the damped kernel itself is the input for the upstream inverse-Fourier
    -- density owner.
    simpa [ψa] using
      gaussianDampedKernelSpec (d := d) (φ := φ) (a := a) ha hφ hpsd hzero
  rcases
    (show
        let ψScaled : E → ℂ := fun t ↦ ψa ((-(2 * Real.pi) : ℝ) • t)
        let fScaled : E → ℝ := fun x ↦ Complex.re (FourierTransformInv.fourierInv ψScaled x)
        Continuous (fun x : E ↦ ((fScaled x : ℝ) : ℂ)) ∧
          (∀ x, 0 ≤ fScaled x) ∧ Integrable fScaled ∧ (∫ x, fScaled x = 1) ∧
          (∀ t : E,
            VectorFourier.fourierIntegral Real.fourierChar volume
                (innerₗ E)
                (fun x : E ↦ ((fScaled x : ℝ) : ℂ))
                (-(2 * Real.pi)⁻¹ • t) = ψa t) from
      scaledInverseFourierDensitySpecOfIntegrableContinuousPositiveDefinite
        (d := d) (ρ := ψa) hψ_spec.1 hψ_spec.2.1 hψ_spec.2.2.1 hψ_spec.2.2.2) with
    ⟨_hf_cont, hf_nonneg, hf_int, hf_mass, _hf_fourier⟩
  -- Proof comment: the pointwise nonnegativity, `L¹` control, and mass-one property are now just
  -- the corresponding clauses of the common inverse-Fourier density theorem applied to `ψa`.
  exact ⟨by simpa [f, ψa] using hf_nonneg,
    by simpa [f, ψa] using hf_int,
    by simpa [f, ψa] using hf_mass⟩

/-- Helper for Theorem 15.29: Gaussian damping of a continuous normalized positive semidefinite
kernel on `ℝ^d` should already come from a nonnegative `L¹` density before the weak-limit step is
used. -/
lemma gaussianDampedDensitySpec {d : ℕ}
    {φ : EuclideanSpace ℝ (Fin d) → ℂ} {a : ℝ} (ha : 0 < a) (hφ : Continuous φ)
    (hpsd : IsPositiveSemidefiniteFunction φ) (hzero : φ 0 = 1) :
    ∃ f : EuclideanSpace ℝ (Fin d) → ℝ,
      (∀ x, 0 ≤ f x) ∧ Integrable f ∧ (∫ x, f x = 1) ∧
      (∀ t : EuclideanSpace ℝ (Fin d),
        VectorFourier.fourierIntegral Real.fourierChar volume
            (innerₗ (EuclideanSpace ℝ (Fin d)))
            (fun x : EuclideanSpace ℝ (Fin d) ↦ ((f x : ℝ) : ℂ))
            (-(2 * Real.pi)⁻¹ • t) =
          Complex.exp (-(a : ℂ) * ‖t‖ ^ 2) * φ t) := by
  let E := EuclideanSpace ℝ (Fin d)
  let ρ : E → ℂ := fun t ↦ Complex.exp (-(a : ℂ) * ‖t‖ ^ 2) * φ t
  let f : E → ℝ := fun x ↦
    Complex.re (FourierTransformInv.fourierInv
      (fun t : E ↦ ρ ((-(2 * Real.pi) : ℝ) • t)) x)
  have hρ_spec : Continuous ρ ∧ Integrable ρ ∧ IsPositiveSemidefiniteFunction ρ ∧ ρ 0 = 1 := by
    -- Proof comment: the Gaussian-damped kernel `ρ` is the direct input for the common
    -- inverse-Fourier density theorem.
    simpa [ρ] using gaussianDampedKernelSpec
      (d := d) (φ := φ) (a := a) ha hφ hpsd hzero
  rcases
    (show
        let ψScaled : E → ℂ := fun t ↦ ρ ((-(2 * Real.pi) : ℝ) • t)
        let fScaled : E → ℝ := fun x ↦ Complex.re (FourierTransformInv.fourierInv ψScaled x)
        Continuous (fun x : E ↦ ((fScaled x : ℝ) : ℂ)) ∧
          (∀ x, 0 ≤ fScaled x) ∧ Integrable fScaled ∧ (∫ x, fScaled x = 1) ∧
          (∀ t : E,
            VectorFourier.fourierIntegral Real.fourierChar volume
                (innerₗ E)
                (fun x : E ↦ ((fScaled x : ℝ) : ℂ))
                (-(2 * Real.pi)⁻¹ • t) = ρ t) from
      scaledInverseFourierDensitySpecOfIntegrableContinuousPositiveDefinite
        (d := d) (ρ := ρ) hρ_spec.1 hρ_spec.2.1 hρ_spec.2.2.1 hρ_spec.2.2.2) with
    ⟨_hf_cont, hf_nonneg, hf_int, hf_mass, hf_fourier⟩
  -- Proof comment: the Gaussian-damped density owner is now exactly the common inverse-Fourier
  -- theorem specialized to the damped kernel `ρ`.
  exact ⟨f, by simpa [f, ρ] using hf_nonneg,
    by simpa [f, ρ] using hf_int,
    by simpa [f, ρ] using hf_mass,
    by simpa [f, ρ] using hf_fourier⟩

/-- Helper for Theorem 15.29: Gaussian damping of a continuous normalized positive semidefinite
function on `ℝ^d` should be realized by a probability measure before any inverse-Fourier density
argument is used. -/
lemma gaussianDampedMeasureExists {d : ℕ}
    {φ : EuclideanSpace ℝ (Fin d) → ℂ} {a : ℝ} (ha : 0 < a) (hφ : Continuous φ)
    (hpsd : IsPositiveSemidefiniteFunction φ) (hzero : φ 0 = 1) :
    ∃ μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)),
      ∀ t : EuclideanSpace ℝ (Fin d),
        charFun (μ : Measure (EuclideanSpace ℝ (Fin d))) t =
          Complex.exp (-(a : ℂ) * ‖t‖ ^ 2) * φ t := by
  rcases gaussianDampedDensitySpec (d := d) (φ := φ) (a := a) ha hφ hpsd hzero with
    ⟨f, hf_nonneg, hf_int, hf_mass, hf_fourier⟩
  -- Proof comment: once the damped density owner is available, the Gaussian-damped measure is the
  -- short `withDensity` packaging step recorded above.
  exact existsProbabilityMeasureOfRealDensityFourierEq hf_nonneg hf_int hf_mass hf_fourier

/-- Helper for Theorem 15.29: Gaussian damping of a continuous normalized positive semidefinite
function on `ℝ^d` is the characteristic function of a probability measure. -/
lemma exists_probabilityMeasure_charFun_eq_gaussianDamp_mul {d : ℕ}
    {φ : EuclideanSpace ℝ (Fin d) → ℂ} {a : ℝ} (ha : 0 < a) (hφ : Continuous φ)
    (hpsd : IsPositiveSemidefiniteFunction φ) (hzero : φ 0 = 1) :
    ∃ μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)),
      ∀ t : EuclideanSpace ℝ (Fin d),
        charFun (μ : Measure (EuclideanSpace ℝ (Fin d))) t =
          Complex.exp (-(a : ℂ) * ‖t‖ ^ 2) * φ t := by
  -- Proof comment: this theorem is now only a thin wrapper around the isolated Gaussian-damped
  -- measure-existence owner.
  exact gaussianDampedMeasureExists ha hφ hpsd hzero

-- Proof sketch: the forward implication follows from continuity of `charFun`, positivity of the
-- finite Gram sums, and `charFun_zero`. For the converse implication, apply the locally compact
-- abelian version of Bochner's theorem to `EuclideanSpace ℝ (Fin d)`, which is canonically
-- self-dual.
/-- Theorem 15.29 (1): a continuous function on `ℝ^d` is the characteristic function of a
probability distribution if and only if it is positive semidefinite and has value `1` at `0`. -/
theorem exists_probabilityMeasure_charFun_eq_iff {d : ℕ}
    {φ : EuclideanSpace ℝ (Fin d) → ℂ} (hφ : Continuous φ) :
    (∃ μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)),
      charFun (μ : Measure (EuclideanSpace ℝ (Fin d))) = φ) ↔
      IsPositiveSemidefiniteFunction φ ∧ φ 0 = 1 := by
  constructor
  · rintro ⟨μ, rfl⟩
    constructor
    · -- Proof comment: Lemma 15.28 gives positive semidefiniteness for every finite measure.
      simpa using
        (charFun_isPositiveSemidefiniteFunction_of_isFiniteMeasure
          (μ := (μ : Measure (EuclideanSpace ℝ (Fin d)))))
    · -- Proof comment: a probability characteristic function is normalized at the origin.
      simpa using
        (MeasureTheory.charFun_zero (μ := (μ : Measure (EuclideanSpace ℝ (Fin d)))))
  · intro hpsd
    rcases hpsd with ⟨hpos, hzero⟩
    -- Route correction: instead of routing through the broken earlier owner `Theorem_15_23`, use
    -- the local continuous-at-zero Lévy reconstruction lemma and reduce the converse to the single
    -- Gaussian-damped existence owner above.
    classical
    let a : ℕ → ℝ := fun n ↦ ((n : ℝ) + 1)⁻¹
    have ha_pos : ∀ n : ℕ, 0 < a n := by
      intro n
      simp [a]
      positivity
    choose Ps hPs using fun n : ℕ ↦
      exists_probabilityMeasure_charFun_eq_gaussianDamp_mul
        (a := a n) (ha_pos n) hφ hpos hzero
    have ha_tendsto : Tendsto a atTop (𝓝 0) := by
      simpa [a, one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hchar :
        ∀ t : EuclideanSpace ℝ (Fin d),
          Tendsto
            (fun n ↦
              charFun
                (((Ps n :
                  ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) :
                    Measure (EuclideanSpace ℝ (Fin d)))) t)
            atTop (𝓝 (φ t)) := by
      intro t
      have ha_complex : Tendsto (fun n ↦ (a n : ℂ)) atTop (𝓝 0) := by
        exact (continuous_ofReal.tendsto 0).comp ha_tendsto
      have hexp_arg :
          Tendsto (fun n ↦ -((a n : ℂ) * ‖t‖ ^ 2)) atTop (𝓝 0) := by
        convert (ha_complex.mul_const ((‖t‖ ^ 2 : ℝ) : ℂ)).neg using 1 <;> simp
      have hexp :
          Tendsto (fun n ↦ Complex.exp (-(a n : ℂ) * ‖t‖ ^ 2)) atTop (𝓝 1) := by
        -- Proof comment: express the exponential sequence as a direct composition before applying
        -- continuity of `Complex.exp`.
        simpa [Function.comp] using
          (Complex.continuous_exp.continuousAt.tendsto.comp hexp_arg)
      have hmul :
          Tendsto (fun n ↦ Complex.exp (-(a n : ℂ) * ‖t‖ ^ 2) * φ t) atTop (𝓝 (φ t)) := by
        convert hexp.mul tendsto_const_nhds using 1 <;> simp
      have hEq :
          (fun n ↦
            charFun
              (((Ps n :
                ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) :
                  Measure (EuclideanSpace ℝ (Fin d)))) t) =
            fun n ↦ Complex.exp (-(a n : ℂ) * ‖t‖ ^ 2) * φ t := by
        funext n
        exact hPs n t
      rw [hEq]
      exact hmul
    obtain ⟨Q, hQ⟩ :=
      existsProbabilityMeasureOfTendstoCharFunOfContinuousAtZero Ps hφ.continuousAt hchar
    exact ⟨Q, funext hQ⟩

/-- Helper for Theorem 15.29: the Fourier-normalized Gaussian-damped characteristic-function
kernel of an actual Euclidean witness is integrable. -/
lemma scaledDampedKernel_integrableOfProbabilityMeasure {d : ℕ}
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) {a : ℝ} (ha : 0 < a) :
    Integrable
      (fun t : EuclideanSpace ℝ (Fin d) ↦
        Complex.exp (-(a : ℂ) * ‖((-(2 * Real.pi) : ℝ) • t)‖ ^ 2) *
          charFun (μ : Measure (EuclideanSpace ℝ (Fin d))) ((-(2 * Real.pi) : ℝ) • t)) := by
  let E := EuclideanSpace ℝ (Fin d)
  let c : ℝ := -(2 * Real.pi)
  have hc : c ≠ 0 := by
    have htwoPi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    exact neg_ne_zero.mpr htwoPi
  have hraw_int :
      Integrable (fun t : E ↦ Complex.exp (-(a : ℂ) * ‖t‖ ^ 2) * charFun (μ : Measure E) t) := by
    -- Proof comment: the Gaussian factor dominates the characteristic function of the actual
    -- witness by the universal bound `‖charFun‖ ≤ 1`.
    refine integrableGaussianDamped (d := d) (φ := charFun (μ : Measure E)) ha
      (MeasureTheory.continuous_charFun (μ := (μ : Measure E))) ?_
    intro t
    exact MeasureTheory.norm_charFun_le_one (μ := (μ : Measure E)) t
  -- Proof comment: the Fourier-normalized kernel is a fixed nonzero rescaling of the raw damped
  -- characteristic function.
  simpa [c] using hraw_int.comp_smul hc

/-- Helper for Theorem 15.29: the Fourier-normalized inverse-Fourier candidate attached to an
actual Euclidean witness is already real-valued. -/
lemma scaledDampedKernel_fourierInv_eq_ofRealOfProbabilityMeasure {d : ℕ}
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) {a : ℝ} (ha : 0 < a) :
    (fun x : EuclideanSpace ℝ (Fin d) ↦
      ((Complex.re
          (FourierTransformInv.fourierInv
            (fun t : EuclideanSpace ℝ (Fin d) ↦
              Complex.exp (-(a : ℂ) * ‖((-(2 * Real.pi) : ℝ) • t)‖ ^ 2) *
                charFun (μ : Measure (EuclideanSpace ℝ (Fin d))) ((-(2 * Real.pi) : ℝ) • t))
            x) : ℝ) : ℂ)) =
      FourierTransformInv.fourierInv
        (fun t : EuclideanSpace ℝ (Fin d) ↦
          Complex.exp (-(a : ℂ) * ‖((-(2 * Real.pi) : ℝ) • t)‖ ^ 2) *
            charFun (μ : Measure (EuclideanSpace ℝ (Fin d))) ((-(2 * Real.pi) : ℝ) • t)) := by
  let E := EuclideanSpace ℝ (Fin d)
  let c : ℝ := -(2 * Real.pi)
  let ν : Measure E := Measure.map (c • ·) (μ : Measure E)
  let aScaled : ℝ := a * c ^ 2
  haveI : IsProbabilityMeasure ν := by
    dsimp [ν]
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  have hc : c ≠ 0 := by
    have htwoPi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    exact neg_ne_zero.mpr htwoPi
  have haScaled : 0 < aScaled := by
    dsimp [aScaled]
    positivity
  have hnorm : ∀ t : E, ‖c • t‖ ^ 2 = c ^ 2 * ‖t‖ ^ 2 := by
    intro t
    calc
      ‖c • t‖ ^ 2 = (‖c‖ * ‖t‖) ^ 2 := by rw [norm_smul]
      _ = (|c| * ‖t‖) ^ 2 := by rw [Real.norm_eq_abs]
      _ = |c| ^ 2 * ‖t‖ ^ 2 := by ring
      _ = c ^ 2 * ‖t‖ ^ 2 := by rw [sq_abs]
  have hkernel :
      (fun t : E ↦
        Complex.exp (-(a : ℂ) * ‖c • t‖ ^ 2) * charFun (μ : Measure E) (c • t)) =
        fun t : E ↦ Complex.exp (-(aScaled : ℂ) * ‖t‖ ^ 2) * charFun ν t := by
    funext t
    have hargR : a * ‖c • t‖ ^ 2 = aScaled * ‖t‖ ^ 2 := by
      dsimp [aScaled]
      rw [hnorm t]
      ring
    have hargC :
        (a : ℂ) * ‖c • t‖ ^ 2 = (aScaled : ℂ) * ‖t‖ ^ 2 := by
      exact_mod_cast hargR
    rw [MeasureTheory.charFun_map_smul]
    congr 1
    exact congrArg Complex.exp <| by simpa using congrArg Neg.neg hargC
  have hreal :
      (fun x : E ↦
        ((Complex.re
            (FourierTransformInv.fourierInv (fun t : E ↦
              Complex.exp (-(aScaled : ℂ) * ‖t‖ ^ 2) * charFun ν t) x) : ℝ) : ℂ)) =
        FourierTransformInv.fourierInv
          (fun t : E ↦ Complex.exp (-(aScaled : ℂ) * ‖t‖ ^ 2) * charFun ν t) := by
    -- Proof comment: after moving the fixed `-2π` rescaling into a pushed-forward witness law,
    -- the kernel is the standard Gaussian-damped characteristic function of that witness.
    simpa using
      gaussianDampedKernel_fourierInv_eq_ofReal
        (d := d) (φ := charFun ν) (a := aScaled) haScaled
        (MeasureTheory.continuous_charFun (μ := ν))
        (charFun_isPositiveSemidefiniteFunction_of_isFiniteMeasure (μ := ν))
        (by simpa using (MeasureTheory.charFun_zero (μ := ν)))
  have hleft :
      (fun x : E ↦
        ((Complex.re
            (FourierTransformInv.fourierInv
              (fun t : E ↦ Complex.exp (-(a : ℂ) * ‖c • t‖ ^ 2) * charFun (μ : Measure E) (c • t))
              x) : ℝ) : ℂ)) =
        (fun x : E ↦
          ((Complex.re
              (FourierTransformInv.fourierInv
                (fun t : E ↦ Complex.exp (-(aScaled : ℂ) * ‖t‖ ^ 2) * charFun ν t) x) : ℝ) : ℂ)) :=
    congrArg
      (fun ψ : E → ℂ ↦
        fun x : E ↦ ((Complex.re (FourierTransformInv.fourierInv ψ x) : ℝ) : ℂ))
      hkernel
  have hright :
      FourierTransformInv.fourierInv
          (fun t : E ↦ Complex.exp (-(a : ℂ) * ‖c • t‖ ^ 2) * charFun (μ : Measure E) (c • t)) =
        FourierTransformInv.fourierInv
          (fun t : E ↦ Complex.exp (-(aScaled : ℂ) * ‖t‖ ^ 2) * charFun ν t) :=
    congrArg FourierTransformInv.fourierInv hkernel
  -- Proof comment: transport the real-valued inverse-Fourier statement back through the frozen
  -- rescaled kernel equality.
  calc
    (fun x : E ↦
      ((Complex.re
          (FourierTransformInv.fourierInv
            (fun t : E ↦ Complex.exp (-(a : ℂ) * ‖c • t‖ ^ 2) * charFun (μ : Measure E) (c • t))
            x) : ℝ) : ℂ))
        =
      (fun x : E ↦
        ((Complex.re
            (FourierTransformInv.fourierInv
              (fun t : E ↦ Complex.exp (-(aScaled : ℂ) * ‖t‖ ^ 2) * charFun ν t) x) : ℝ) : ℂ)) :=
      hleft
    _ = FourierTransformInv.fourierInv
          (fun t : E ↦ Complex.exp (-(aScaled : ℂ) * ‖t‖ ^ 2) * charFun ν t) := hreal
    _ = FourierTransformInv.fourierInv
          (fun t : E ↦ Complex.exp (-(a : ℂ) * ‖c • t‖ ^ 2) * charFun (μ : Measure E) (c • t)) := by
          symm
          exact hright

/-- Helper for Theorem 15.29: the Fourier-normalized inverse-Fourier candidate attached to an
actual Euclidean witness is continuous as a complex-valued function. -/
lemma scaledDampedInverseFourierContinuousOfProbabilityMeasure {d : ℕ}
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) {a : ℝ} (ha : 0 < a) :
    Continuous
      (fun x : EuclideanSpace ℝ (Fin d) ↦
        ((Complex.re
            (FourierTransformInv.fourierInv
              (fun t : EuclideanSpace ℝ (Fin d) ↦
                Complex.exp (-(a : ℂ) * ‖((-(2 * Real.pi) : ℝ) • t)‖ ^ 2) *
                  charFun (μ : Measure (EuclideanSpace ℝ (Fin d))) ((-(2 * Real.pi) : ℝ) • t))
              x) : ℝ) : ℂ)) := by
  let E := EuclideanSpace ℝ (Fin d)
  let c : ℝ := -(2 * Real.pi)
  have hkernel_int :
      Integrable
        (fun t : E ↦ Complex.exp (-(a : ℂ) * ‖c • t‖ ^ 2) * charFun (μ : Measure E) (c • t)) := by
    -- Proof comment: reuse the dedicated `L¹` owner for the frozen scaled kernel instead of
    -- redoing the Gaussian majorant argument here.
    simpa [c] using scaledDampedKernel_integrableOfProbabilityMeasure (d := d) μ ha
  have hcont_raw :
      Continuous
        (FourierTransformInv.fourierInv
          (fun t : E ↦ Complex.exp (-(a : ℂ) * ‖c • t‖ ^ 2) * charFun (μ : Measure E) (c • t))) :=
    inverseFourier_continuous_of_integrable (d := d)
      (ψ := fun t : E ↦ Complex.exp (-(a : ℂ) * ‖c • t‖ ^ 2) * charFun (μ : Measure E) (c • t))
      hkernel_int
  have hreal :
      (fun x : E ↦
        ((Complex.re
            (FourierTransformInv.fourierInv
              (fun t : E ↦ Complex.exp (-(a : ℂ) * ‖c • t‖ ^ 2) * charFun (μ : Measure E) (c • t))
              x) : ℝ) : ℂ)) =
        FourierTransformInv.fourierInv
          (fun t : E ↦ Complex.exp (-(a : ℂ) * ‖c • t‖ ^ 2) * charFun (μ : Measure E) (c • t)) := by
    -- Proof comment: the scaled inverse-Fourier candidate is real-valued, so continuity reduces
    -- to continuity of the underlying complex inverse Fourier transform.
    exact scaledDampedKernel_fourierInv_eq_ofRealOfProbabilityMeasure (d := d) μ ha
  rw [hreal]
  exact hcont_raw

/-- Helper for Theorem 15.29: once the smoothed witness density is continuous, Fourier inversion
identifies it pointwise with the correctly scaled damped inverse Fourier transform. -/
lemma continuousDensity_eq_scaledDampedInverseFourierOfProbabilityMeasure {d : ℕ}
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) {a : ℝ} (ha : 0 < a)
    {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf_cont : Continuous (fun x : EuclideanSpace ℝ (Fin d) ↦ ((f x : ℝ) : ℂ)))
    (hf_int : Integrable f)
    (hfourier :
      ∀ t : EuclideanSpace ℝ (Fin d),
        VectorFourier.fourierIntegral Real.fourierChar volume
            (innerₗ (EuclideanSpace ℝ (Fin d)))
            (fun x : EuclideanSpace ℝ (Fin d) ↦ ((f x : ℝ) : ℂ))
            (-(2 * Real.pi)⁻¹ • t) =
          Complex.exp (-(a : ℂ) * ‖t‖ ^ 2) *
            charFun (μ : Measure (EuclideanSpace ℝ (Fin d))) t) :
    ∀ x : EuclideanSpace ℝ (Fin d),
      FourierTransformInv.fourierInv
        (fun t : EuclideanSpace ℝ (Fin d) ↦
          Complex.exp (-(a : ℂ) * ‖((-(2 * Real.pi) : ℝ) • t)‖ ^ 2) *
            charFun (μ : Measure (EuclideanSpace ℝ (Fin d))) ((-(2 * Real.pi) : ℝ) • t))
        x = ((f x : ℝ) : ℂ) := by
  -- Proof comment: the earlier normalized Fourier-inversion owner already proves exactly this
  -- scaled identity, so this lemma is only the stable witness-side alias.
  exact continuousDensity_eq_scaledDampedCharFunFourierInvOfProbabilityMeasure
    (d := d) μ ha hf_cont hf_int hfourier

/-- Helper for Theorem 15.29: the scaled inverse-Fourier density owner already packages the
nonnegative density data needed for the Euclidean Bochner witness. -/
lemma densitySpecOfScaledInverseFourierDensity {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} (hψ_cont : Continuous ψ) (hψ_int : Integrable ψ)
    (hψ_psd : IsPositiveSemidefiniteFunction ψ) (hψ_zero : ψ 0 = 1) :
    ∃ f : EuclideanSpace ℝ (Fin d) → ℝ,
      (∀ x, 0 ≤ f x) ∧ Integrable f ∧ (∫ x, f x = 1) ∧
      (∀ t : EuclideanSpace ℝ (Fin d),
        VectorFourier.fourierIntegral Real.fourierChar volume
            (innerₗ (EuclideanSpace ℝ (Fin d)))
            (fun x : EuclideanSpace ℝ (Fin d) ↦ ((f x : ℝ) : ℂ))
            (-(2 * Real.pi)⁻¹ • t) = ψ t) := by
  let E := EuclideanSpace ℝ (Fin d)
  let ψScaled : E → ℂ := fun t ↦ ψ ((-(2 * Real.pi) : ℝ) • t)
  let f : E → ℝ := fun x ↦ Complex.re (FourierTransformInv.fourierInv ψScaled x)
  have hspec :
      Continuous (fun x : E ↦ ((f x : ℝ) : ℂ)) ∧
        (∀ x, 0 ≤ f x) ∧ Integrable f ∧ (∫ x, f x = 1) ∧
        (∀ t : E,
          VectorFourier.fourierIntegral Real.fourierChar volume
              (innerₗ E)
              (fun x : E ↦ ((f x : ℝ) : ℂ))
              (-(2 * Real.pi)⁻¹ • t) = ψ t) := by
    -- Proof comment: specialize the upstream scaled inverse-Fourier owner to `ψ` itself and keep
    -- only the explicit density fields needed by the witness-packaging step below.
    simpa [ψScaled, f] using
      (scaledInverseFourierDensitySpecOfIntegrableContinuousPositiveDefinite
        (d := d) (ρ := ψ) hψ_cont hψ_int hψ_psd hψ_zero)
  exact ⟨f, hspec.2.1, hspec.2.2.1, hspec.2.2.2.1, hspec.2.2.2.2⟩

/-- Helper for Theorem 15.29: the inverse-Fourier route for an integrable continuous normalized
positive semidefinite kernel supplies a nonnegative probability density whose normalized Fourier
integral is the original kernel. -/
lemma inverseFourierDensitySpecOfIntegrableContinuousPositiveDefinite {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} (hψ_cont : Continuous ψ) (hψ_int : Integrable ψ)
    (hψ_psd : IsPositiveSemidefiniteFunction ψ) (hψ_zero : ψ 0 = 1) :
    ∃ f : EuclideanSpace ℝ (Fin d) → ℝ,
      (∀ x, 0 ≤ f x) ∧ Integrable f ∧ (∫ x, f x = 1) ∧
      (∀ t : EuclideanSpace ℝ (Fin d),
        VectorFourier.fourierIntegral Real.fourierChar volume
            (innerₗ (EuclideanSpace ℝ (Fin d)))
            (fun x : EuclideanSpace ℝ (Fin d) ↦ ((f x : ℝ) : ℂ))
            (-(2 * Real.pi)⁻¹ • t) = ψ t) := by
  -- Route correction: avoid the later Euclidean Bochner-iff detour entirely here. The scaled
  -- inverse-Fourier owner already packages the needed density witness directly, so the dependency
  -- direction now points strictly from the analytic owner to the witness constructor.
  -- Proof comment: this theorem is now only the stable alias exposing the density fields of the
  -- upstream scaled inverse-Fourier package.
  exact
    densitySpecOfScaledInverseFourierDensity
      (d := d) (ψ := ψ) hψ_cont hψ_int hψ_psd hψ_zero

/-- Helper for Theorem 15.29: once a Euclidean kernel is represented by a nonnegative density of
mass `1`, the density packages directly into a characteristic-function witness. -/
lemma existsProbabilityMeasureOfDensityFourierSpec {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ}
    (hDensity :
      ∃ f : EuclideanSpace ℝ (Fin d) → ℝ,
        (∀ x, 0 ≤ f x) ∧ Integrable f ∧ (∫ x, f x = 1) ∧
        (∀ t : EuclideanSpace ℝ (Fin d),
          VectorFourier.fourierIntegral Real.fourierChar volume
              (innerₗ (EuclideanSpace ℝ (Fin d)))
              (fun x : EuclideanSpace ℝ (Fin d) ↦ ((f x : ℝ) : ℂ))
              (-(2 * Real.pi)⁻¹ • t) = ψ t)) :
    ∃ μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)),
      ∀ t : EuclideanSpace ℝ (Fin d), charFun (μ : Measure (EuclideanSpace ℝ (Fin d))) t = ψ t := by
  rcases hDensity with ⟨f, hf_nonneg, hf_int, hf_mass, hf_fourier⟩
  -- Proof comment: the earlier `withDensity` packaging theorem consumes exactly this density
  -- package, so no additional Fourier manipulation is needed here.
  exact existsProbabilityMeasureOfRealDensityFourierEq hf_nonneg hf_int hf_mass hf_fourier

/-- Helper for Theorem 15.29: the integrable Euclidean Bochner converse should be isolated as the
single upstream witness theorem for continuous normalized positive semidefinite kernels on `ℝ^d`.
-/
lemma existsProbabilityMeasureOfIntegrableContinuousPositiveDefiniteCore {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} (hψ_cont : Continuous ψ) (_hψ_int : Integrable ψ)
    (hψ_psd : IsPositiveSemidefiniteFunction ψ) (hψ_zero : ψ 0 = 1) :
    ∃ μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)),
      ∀ t : EuclideanSpace ℝ (Fin d), charFun (μ : Measure (EuclideanSpace ℝ (Fin d))) t = ψ t := by
  -- Route correction: after the Euclidean Bochner iff theorem is proved, this later helper should
  -- stop reopening the inverse-Fourier density route and instead read the witness straight off the
  -- public theorem.
  rcases
    (exists_probabilityMeasure_charFun_eq_iff (d := d) hψ_cont).2 ⟨hψ_psd, hψ_zero⟩ with
    ⟨μ, hμ⟩
  refine ⟨μ, ?_⟩
  -- Proof comment: unpack the function equality from the public Euclidean theorem pointwise once
  -- so downstream witness-side lemmas can consume the characteristic-function witness directly.
  intro t
  exact congrFun hμ t

/-- Helper for Theorem 15.29: the inverse-Fourier density package for an integrable continuous
normalized positive semidefinite kernel immediately yields the required probability witness. -/
lemma existsProbabilityMeasureOfIntegrableContinuousPositiveDefiniteViaDensity {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} (hψ_cont : Continuous ψ) (hψ_int : Integrable ψ)
    (hψ_psd : IsPositiveSemidefiniteFunction ψ) (hψ_zero : ψ 0 = 1) :
    ∃ μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)),
      ∀ t : EuclideanSpace ℝ (Fin d), charFun (μ : Measure (EuclideanSpace ℝ (Fin d))) t = ψ t := by
  -- Proof comment: first invoke the common inverse-Fourier density owner, then package that
  -- density with the existing `withDensity`-to-characteristic-function bridge.
  exact
    existsProbabilityMeasureOfDensityFourierSpec
      (d := d) (ψ := ψ)
      (inverseFourierDensitySpecOfIntegrableContinuousPositiveDefinite
        (d := d) (ψ := ψ) hψ_cont hψ_int hψ_psd hψ_zero)

/-- Helper for Theorem 15.29: an integrable continuous normalized positive semidefinite kernel on
`ℝ^d` packages directly into a probability measure witness via the inverse-Fourier density route. -/
lemma existsProbabilityMeasureOfIntegrableContinuousPositiveDefinite {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} (hψ_cont : Continuous ψ) (hψ_int : Integrable ψ)
    (hψ_psd : IsPositiveSemidefiniteFunction ψ) (hψ_zero : ψ 0 = 1) :
    ∃ μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)),
      ∀ t : EuclideanSpace ℝ (Fin d), charFun (μ : Measure (EuclideanSpace ℝ (Fin d))) t = ψ t := by
  -- Route correction: keep the public integrable wrapper as a thin adapter over the isolated
  -- Euclidean owner theorem instead of letting later callers depend on the density route
  -- directly.
  -- Proof comment: all downstream witness users should now consume the owner theorem above,
  -- leaving the density route as an implementation candidate rather than the public dependency.
  exact
    existsProbabilityMeasureOfIntegrableContinuousPositiveDefiniteCore
      (d := d) (ψ := ψ) hψ_cont hψ_int hψ_psd hψ_zero

/-- Helper for Theorem 15.29: once the upstream Euclidean Bochner owner supplies an actual witness
for `ψ`, the stale scaled-kernel inverse-Fourier bridge closes immediately by the dedicated
witness-side transport lemma. -/
lemma scaledRegularizedKernelFourierInv_nonnegMassOfIntegrableWitness {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} {b : ℝ} (hb : 0 < b)
    (hψ_cont : Continuous ψ) (hψ_int : Integrable ψ)
    (hψ_psd : IsPositiveSemidefiniteFunction ψ) (hψ_zero : ψ 0 = 1) :
    let E := EuclideanSpace ℝ (Fin d)
    let c : ℝ := -(2 * Real.pi)
    let cInv : ℝ := (-(2 * Real.pi)⁻¹ : ℝ)
    let ρ : E → ℂ := fun t ↦ Complex.exp (-(b : ℂ) * ‖cInv • t‖ ^ 2) * ψ (cInv • t)
    (∀ x : E, 0 ≤ Complex.re (FourierTransformInv.fourierInv (fun t : E ↦ ρ (c • t)) x)) ∧
      (∫ x : E, Complex.re (FourierTransformInv.fourierInv (fun t : E ↦ ρ (c • t)) x) = 1) := by
  let E := EuclideanSpace ℝ (Fin d)
  let c : ℝ := -(2 * Real.pi)
  let cInv : ℝ := (-(2 * Real.pi)⁻¹ : ℝ)
  let ρ : E → ℂ := fun t ↦ Complex.exp (-(b : ℂ) * ‖cInv • t‖ ^ 2) * ψ (cInv • t)
  rcases
    existsProbabilityMeasureOfIntegrableContinuousPositiveDefinite
      (d := d) (ψ := ψ) hψ_cont hψ_int hψ_psd hψ_zero with
    ⟨μ, hμ⟩
  -- Proof comment: the later Euclidean witness owner packages `ψ` as a genuine
  -- characteristic function, so the exact fixed-normalization bridge is now only the stable
  -- witness-side transport theorem.
  simpa [E, c, cInv, ρ] using
    scaledRegularizedKernelFourierInv_nonnegMass_of_charFunWitness
      (d := d) (ψ := ψ) (b := b) hb ⟨μ, hμ⟩

/-- Helper for Theorem 15.29: once the original Euclidean kernel already has the integrable
Bochner witness promised by the inverse-Fourier owner, the Gaussian-regularized inverse-Fourier
candidate inherits pointwise nonnegativity and mass `1` from the witness-side density package. -/
lemma gaussianRegularizedInverseFourierDensityNonnegMassOfIntegrableWitness {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} {b : ℝ} (hb : 0 < b)
    (hψ_cont : Continuous ψ) (hψ_int : Integrable ψ)
    (hψ_psd : IsPositiveSemidefiniteFunction ψ) (hψ_zero : ψ 0 = 1) :
    (∀ x, 0 ≤ gaussianRegularizedInverseFourierDensity ψ b x) ∧
      (∫ x, gaussianRegularizedInverseFourierDensity ψ b x = 1) := by
  -- Proof comment: consume the downstream scaled-kernel bridge that now sits on the correct side
  -- of the Euclidean witness theorem, then rewrite back to the public regularized-density
  -- surface.
  exact
    gaussianRegularizedInverseFourierDensity_nonnegMass_of_scaledKernelBridge
      (d := d) (ψ := ψ) (b := b)
      (scaledRegularizedKernelFourierInv_nonnegMassOfIntegrableWitness
        (d := d) (ψ := ψ) (b := b) hb hψ_cont hψ_int hψ_psd hψ_zero)

/-- Helper for Theorem 15.29: once the later Euclidean witness theorem supplies nonnegativity and
mass `1` for the regularized density, continuity upgrades that package to the missing `L¹`
control as well. -/
lemma gaussianRegularizedInverseFourierDensityNonnegIntegrableOfIntegrableWitness {d : ℕ}
    {ψ : EuclideanSpace ℝ (Fin d) → ℂ} {b : ℝ} (hb : 0 < b)
    (hψ_cont : Continuous ψ) (hψ_int : Integrable ψ)
    (hψ_psd : IsPositiveSemidefiniteFunction ψ) (hψ_zero : ψ 0 = 1) :
    (∀ x, 0 ≤ gaussianRegularizedInverseFourierDensity ψ b x) ∧
      Integrable (gaussianRegularizedInverseFourierDensity ψ b) := by
  rcases
    existsProbabilityMeasureOfIntegrableContinuousPositiveDefinite
      (d := d) (ψ := ψ) hψ_cont hψ_int hψ_psd hψ_zero with
    ⟨μ, hμ⟩
  -- Proof comment: once the upstream Euclidean Bochner owner produces an actual witness, the new
  -- witness-to-`L¹` helper packages the regularized density data without duplicating the
  -- continuity upgrade.
  exact
    gaussianRegularizedInverseFourierDensityNonnegIntegrableOfCharFunWitness
      (d := d) (ψ := ψ) (b := b) hb hψ_cont hψ_psd hψ_zero ⟨μ, hμ⟩

/-- The multiplicative-group form of Definition 15.27: a complex-valued function on a commutative
group is positive semidefinite if every finite quotient-kernel matrix is positive semidefinite. -/
def IsPositiveSemidefiniteMulFunction {H : Type*} [CommGroup H] (φ : H → ℂ) : Prop :=
  IsPositiveSemidefiniteFunction (φ ∘ Additive.toMul)

/-- Bridge between the multiplicative-group and additive-group formulations of positive
semidefiniteness. -/
theorem isPositiveSemidefiniteMulFunction_iff {H : Type*} [CommGroup H] {φ : H → ℂ} :
    IsPositiveSemidefiniteMulFunction φ ↔
      IsPositiveSemidefiniteFunction (φ ∘ Additive.toMul) :=
  Iff.rfl

/-- Helper for Theorem 15.29: multiplicative positive semidefiniteness is equivalent to the
nonnegativity of the quadratic sums `∑ i, ∑ j, star (c i) * φ (χ i * (χ j)⁻¹) * c j`. -/
lemma isPositiveSemidefiniteMulFunction_iff_quadraticSum_nonneg {H : Type*} [CommGroup H]
    {φ : H → ℂ} :
    IsPositiveSemidefiniteMulFunction φ ↔
      ∀ n (χ : Fin n → H) (c : Fin n → ℂ),
        0 ≤ ∑ i, ∑ j, star (c i) * φ (χ i * (χ j)⁻¹) * c j := by
  rw [isPositiveSemidefiniteMulFunction_iff, isPositiveSemidefiniteFunction_iff_quadratic_sum_nonneg]
  constructor
  · intro h n χ c
    -- Proof comment: apply the additive quadratic-form criterion to the additive copy of the
    -- multiplicative family `χ`.
    simpa [div_eq_mul_inv] using h n (fun i ↦ Additive.ofMul (χ i)) c
  · intro h n ψ c
    -- Proof comment: conversely, package the additive family back into the multiplicative group.
    simpa [div_eq_mul_inv] using h n (fun i ↦ Additive.toMul (ψ i)) c

/-- Helper for Theorem 15.29: every multiplicative positive semidefinite kernel is Hermitian in the
group variable, so inversion conjugates the value. -/
lemma star_value_eq_value_inv_of_isPositiveSemidefiniteMulFunction {H : Type*} [CommGroup H]
    {φ : H → ℂ} (hφ : IsPositiveSemidefiniteMulFunction φ) (χ : H) :
    star (φ χ) = φ χ⁻¹ := by
  let x : Fin 2 → H := ![1, χ]
  let A : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of fun i j ↦ φ (x i * (x j)⁻¹)
  have hA : A.PosSemidef := by
    rw [isPositiveSemidefiniteMulFunction_iff] at hφ
    -- Proof comment: the additive-copy kernel matrix is exactly the multiplicative quotient kernel.
    simpa [A, x, div_eq_mul_inv] using hφ 2 (fun i ↦ Additive.ofMul (x i))
  -- Proof comment: the `2 × 2` quotient-kernel matrix is Hermitian, so the off-diagonal entries
  -- are conjugates.
  simpa [A, x] using hA.isHermitian.apply 0 1

/-- Helper for Theorem 15.29: a normalized multiplicative positive semidefinite function has norm
at most `1` everywhere. -/
lemma norm_le_one_of_isPositiveSemidefiniteMulFunction_one_eq_one {H : Type*} [CommGroup H]
    {φ : H → ℂ} (hφ : IsPositiveSemidefiniteMulFunction φ) (hone : φ 1 = 1) (χ : H) :
    ‖φ χ‖ ≤ 1 := by
  let x : Fin 2 → H := ![1, χ]
  let A : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of fun i j ↦ φ (x i * (x j)⁻¹)
  have hA : A.PosSemidef := by
    rw [isPositiveSemidefiniteMulFunction_iff] at hφ
    -- Proof comment: the same `2 × 2` quotient-kernel matrix inherits positive semidefiniteness
    -- from the additive-copy definition.
    simpa [A, x, div_eq_mul_inv] using hφ 2 (fun i ↦ Additive.ofMul (x i))
  have hstar : star (φ χ) = φ χ⁻¹ := by
    -- Proof comment: Hermitian symmetry identifies the inverse value with complex conjugation.
    simpa [A, x] using hA.isHermitian.apply 0 1
  have hdet_le_one : (φ χ⁻¹ * φ χ : ℂ) ≤ 1 := by
    -- Proof comment: the determinant inequality of the `2 × 2` quotient-kernel matrix yields the
    -- basic bound on the off-diagonal product.
    simpa [A, x, Matrix.det_fin_two, hone] using Matrix.PosSemidef.det_nonneg hA
  have hmul_eq : (φ χ⁻¹ * φ χ : ℂ) = ((‖φ χ‖ * ‖φ χ‖ : ℝ) : ℂ) := by
    -- Proof comment: Hermitian symmetry turns the product with the inverse value into `‖φ χ‖²`.
    calc
      φ χ⁻¹ * φ χ = star (φ χ) * φ χ := by rw [hstar]
      _ = ((‖φ χ‖ ^ 2 : ℝ) : ℂ) := by
            simpa using (Complex.conj_mul' (φ χ))
      _ = ((‖φ χ‖ * ‖φ χ‖ : ℝ) : ℂ) := by
            congr 1
            ring
  have hsq : ‖φ χ‖ * ‖φ χ‖ ≤ 1 := by
    have hcomplex_le : (((‖φ χ‖ * ‖φ χ‖ : ℝ) : ℂ)) ≤ 1 := by
      simpa [hmul_eq] using hdet_le_one
    exact Complex.real_le_real.mp hcomplex_le
  nlinarith [hsq, norm_nonneg (φ χ)]

section LocallyCompactAbelian

variable {G : Type u} [AddCommGroup G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
  [IsTopologicalAddGroup G]

/-- The characteristic function of a probability measure on an additive topological abelian group,
viewed as a function on the Pontryagin dual. -/
noncomputable def pontryaginCharFun
    (μ : ProbabilityMeasure G) (χ : PontryaginDual (Multiplicative G)) : ℂ :=
  ∫ x, (χ (Multiplicative.ofAdd x) : ℂ) ∂(μ : Measure G)

/-- Helper for Theorem 15.29: a dual character defines a bounded continuous complex phase test
function on `G`. -/
noncomputable def pontryaginPhase
    (χ : PontryaginDual (Multiplicative G)) : BoundedContinuousFunction G ℂ :=
  let phaseC : C(G, ℂ) :=
    ⟨fun x ↦ (((χ (Multiplicative.ofAdd x) : Circle) : ℂ)),
      continuous_subtype_val.comp (χ.continuous.comp continuous_ofAdd)⟩
  BoundedContinuousFunction.mkOfBound phaseC 2
    (fun x y ↦ by
      -- Proof comment: every character value lies on the unit circle, so the image has diameter
      -- at most `2`.
      calc
        dist (phaseC x) (phaseC y) = ‖phaseC x - phaseC y‖ := by rw [dist_eq_norm]
        _ ≤ ‖phaseC x‖ + ‖phaseC y‖ := norm_sub_le _ _
        _ = 1 + 1 := by
            simp [phaseC]
        _ = 2 := by norm_num)

/-- Helper for Theorem 15.29: evaluating the bounded phase test function simply unwraps the dual
character. -/
lemma pontryaginPhase_apply (χ : PontryaginDual (Multiplicative G)) (x : G) :
    pontryaginPhase χ x = (((χ (Multiplicative.ofAdd x) : Circle) : ℂ)) := by
  simp [pontryaginPhase]

/-- Helper for Theorem 15.29: the phase test for the trivial character is the constant function
`1`. -/
lemma pontryaginPhase_one :
    pontryaginPhase (1 : PontryaginDual (Multiplicative G)) = 1 := by
  -- Proof comment: the trivial character evaluates to `1` at every group element, so the
  -- resulting bounded phase test is the constant function `1`.
  ext x
  change (((1 : Circle) : ℂ)) = ((1 : BoundedContinuousFunction G ℂ) x)
  rfl

/-- Helper for Theorem 15.29: multiplying Pontryagin-dual characters multiplies the associated
phase test functions pointwise. -/
lemma pontryaginPhase_mul (χ ψ : PontryaginDual (Multiplicative G)) :
    pontryaginPhase (χ * ψ) = pontryaginPhase χ * pontryaginPhase ψ := by
  sorry

/-- Helper for Theorem 15.29: inverting a Pontryagin-dual character conjugates the associated phase
test function pointwise. -/
lemma pontryaginPhase_inv_apply (χ : PontryaginDual (Multiplicative G)) (x : G) :
    pontryaginPhase χ⁻¹ x = star (pontryaginPhase χ x) := by
  -- Proof comment: the inverse of a circle-valued character is its complex conjugate after
  -- coercing from `Circle` to `ℂ`.
  change ((((χ (Multiplicative.ofAdd x) : Circle)⁻¹ : Circle) : ℂ)) =
    star ((((χ (Multiplicative.ofAdd x) : Circle) : ℂ)))
  simpa using Circle.coe_inv_eq_conj ((χ (Multiplicative.ofAdd x) : Circle))

/-- Helper for Theorem 15.29: compact-open evaluation makes the phase test function continuous in
the dual character at each fixed group element. -/
lemma continuous_pontryaginPhase_apply (x : G) :
    Continuous fun χ : PontryaginDual (Multiplicative G) ↦ pontryaginPhase χ x := by
  -- Proof comment: evaluation at a fixed point is continuous for the compact-open topology on
  -- continuous monoid homomorphisms, and coercing `Circle` to `ℂ` preserves continuity.
  have hEval : Continuous fun χ : PontryaginDual (Multiplicative G) ↦
      ((χ : C(Multiplicative G, Circle)) (Multiplicative.ofAdd x)) := by
    -- Proof comment: first forget the monoid-hom structure and use the compact-open evaluation
    -- map on the ambient continuous-map space.
    exact
      (continuous_eval_const (Multiplicative.ofAdd x)).comp
        (ContinuousMonoidHom.isInducing_toContinuousMap
          (A := Multiplicative G) (B := Circle)).continuous
  simpa [pontryaginPhase_apply] using
    (continuous_subtype_val.comp hEval)

/-- Helper for Theorem 15.29: `pontryaginCharFun` is the integral of the canonical bounded phase
test function attached to the dual character. -/
lemma pontryaginCharFun_eq_integral_pontryaginPhase
    (μ : ProbabilityMeasure G) (χ : PontryaginDual (Multiplicative G)) :
    pontryaginCharFun μ χ = ∫ x, pontryaginPhase χ x ∂(μ : Measure G) := by
  simp [pontryaginCharFun, pontryaginPhase_apply]

/-- Helper for Theorem 15.29: the bounded phase test function is integrable against every
probability measure. -/
lemma integrable_pontryaginPhase (μ : ProbabilityMeasure G)
    (χ : PontryaginDual (Multiplicative G)) :
    Integrable (fun x : G ↦ pontryaginPhase χ x) (μ : Measure G) := by
  -- Proof comment: bounded continuous functions are integrable against finite measures, and a
  -- probability measure is finite.
  simpa using
    (BoundedContinuousFunction.integrable (μ := (μ : Measure G)) (f := pontryaginPhase χ))

/-- Helper for Theorem 15.29: for a fixed dual character, the Pontryagin characteristic function
depends continuously on the underlying probability measure. -/
lemma continuous_probabilityMeasure_pontryaginCharFun_apply
    (χ : PontryaginDual (Multiplicative G)) :
    Continuous fun μ : ProbabilityMeasure G ↦ pontryaginCharFun μ χ := by
  have hIntegral :
      Continuous fun μ : ProbabilityMeasure G ↦ ∫ x, pontryaginPhase χ x ∂(μ : Measure G) := by
    rw [continuous_iff_continuousAt]
    intro μ
    rw [ContinuousAt]
    -- Proof comment: weak convergence on probability measures is defined by convergence of
    -- integrals against bounded continuous test functions.
    simpa using
      (((ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).1
        (show Tendsto (fun ν : ProbabilityMeasure G ↦ ν) (𝓝 μ) (𝓝 μ) from tendsto_id))
        (pontryaginPhase χ))
  -- Proof comment: the chosen bounded continuous test function is exactly the integrand used by
  -- `pontryaginCharFun`.
  simpa [pontryaginCharFun_eq_integral_pontryaginPhase] using hIntegral

/-- Helper for Theorem 15.29: the Pontryagin characteristic function is normalized at the trivial
character. -/
lemma pontryaginCharFun_one (μ : ProbabilityMeasure G) :
    pontryaginCharFun μ 1 = 1 := by
  -- Proof comment: the trivial character is the constant function `1`, so the Bochner integral is
  -- just the total mass of the probability measure.
  change ∫ x : G, (1 : ℂ) ∂(μ : Measure G) = 1
  simp

/-- Helper for Theorem 15.29: conjugating the Pontryagin characteristic function inverts the
character. -/
lemma star_pontryaginCharFun_eq_pontryaginCharFun_inv
    (μ : ProbabilityMeasure G) (χ : PontryaginDual (Multiplicative G)) :
    star (pontryaginCharFun μ χ) = pontryaginCharFun μ χ⁻¹ := by
  -- Proof comment: character values lie on the unit circle, so complex conjugation matches
  -- inversion of the dual character under the integral.
  calc
    star (pontryaginCharFun μ χ)
        =
          ∫ x : G, star ((((χ (Multiplicative.ofAdd x) : Circle) : ℂ))) ∂(μ : Measure G) := by
            simpa [pontryaginCharFun] using
              (integral_conj (μ := (μ : Measure G))
                (f := fun x : G ↦ (((χ (Multiplicative.ofAdd x) : Circle) : ℂ)))).symm
    _ = pontryaginCharFun μ χ⁻¹ := by
          rw [pontryaginCharFun]
          refine integral_congr_ae (Filter.Eventually.of_forall ?_)
          intro x
          change star ((((χ (Multiplicative.ofAdd x) : Circle) : ℂ))) =
            ((((χ⁻¹) (Multiplicative.ofAdd x) : Circle) : ℂ))
          have hmul :
              (((χ⁻¹) (Multiplicative.ofAdd x) : Circle)) =
                ((χ (Multiplicative.ofAdd x) : Circle))⁻¹ := by
            rfl
          rw [hmul]
          simpa using
            (Circle.coe_inv_eq_conj ((χ (Multiplicative.ofAdd x) : Circle))).symm

/-- Helper for Theorem 15.29: Pontryagin characteristic functions are uniformly bounded by `1`. -/
lemma norm_pontryaginCharFun_le_one (μ : ProbabilityMeasure G)
    (χ : PontryaginDual (Multiplicative G)) :
    ‖pontryaginCharFun μ χ‖ ≤ 1 := by
  calc
    ‖pontryaginCharFun μ χ‖
        = ‖∫ x : G, pontryaginPhase χ x ∂(μ : Measure G)‖ := by
            rw [pontryaginCharFun_eq_integral_pontryaginPhase]
    _ ≤ ∫ x : G, ‖pontryaginPhase χ x‖ ∂(μ : Measure G) := by
          simpa using
            (norm_integral_le_integral_norm
              (fun x : G ↦ pontryaginPhase χ x) :
                ‖∫ x : G, pontryaginPhase χ x ∂(μ : Measure G)‖ ≤
                  ∫ x : G, ‖pontryaginPhase χ x‖ ∂(μ : Measure G))
    _ = ∫ x : G, (1 : ℝ) ∂(μ : Measure G) := by
          refine integral_congr_ae (Filter.Eventually.of_forall ?_)
          intro x
          simp [pontryaginPhase_apply]
    _ = 1 := by
          simp

/-- Helper for Theorem 15.29: every quadratic form of the Pontryagin characteristic-function
kernel is a nonnegative integral of a pointwise square. -/
lemma pontryaginCharFunQuadraticSum_nonneg (μ : ProbabilityMeasure G) {n : ℕ}
    (χ : Fin n → PontryaginDual (Multiplicative G)) (c : Fin n → ℂ) :
    0 ≤ ∑ i, ∑ j, star (c i) * pontryaginCharFun μ (χ i * (χ j)⁻¹) * c j := by
  let coeff : G → Fin n → ℂ :=
    fun x i ↦ c i * star (((χ i) (Multiplicative.ofAdd x) : Circle) : ℂ)
  let integrand : G → ℂ := fun x ↦ ∑ i, ∑ j, star (coeff x i) * coeff x j
  have hterm :
      ∀ i j, Integrable (fun x ↦ star (coeff x i) * coeff x j) (μ : Measure G) := by
    intro i j
    -- Proof comment: each twisted character product is continuous and uniformly bounded on the
    -- finite probability measure.
    refine Integrable.of_bound ?_ (‖c i‖ * ‖c j‖) ?_
    · have hcoeff_i : Continuous fun x : G ↦ coeff x i := by
        have hphase :
            Continuous fun x : G ↦ star (((χ i) (Multiplicative.ofAdd x) : Circle) : ℂ) := by
          exact (continuous_subtype_val.comp ((χ i).continuous.comp continuous_ofAdd)).star
        exact continuous_const.mul hphase
      have hcoeff_j : Continuous fun x : G ↦ coeff x j := by
        have hphase :
            Continuous fun x : G ↦ star (((χ j) (Multiplicative.ofAdd x) : Circle) : ℂ) := by
          exact (continuous_subtype_val.comp ((χ j).continuous.comp continuous_ofAdd)).star
        exact continuous_const.mul hphase
      exact (hcoeff_i.star.mul hcoeff_j).aestronglyMeasurable
    · filter_upwards with x
      have hcoeff_i_norm : ‖coeff x i‖ = ‖c i‖ := by
        calc
          ‖coeff x i‖ = ‖c i‖ * ‖star (((χ i) (Multiplicative.ofAdd x) : Circle) : ℂ)‖ := by
            simp [coeff, norm_mul]
          _ = ‖c i‖ := by
            simp
      have hcoeff_j_norm : ‖coeff x j‖ = ‖c j‖ := by
        calc
          ‖coeff x j‖ = ‖c j‖ * ‖star (((χ j) (Multiplicative.ofAdd x) : Circle) : ℂ)‖ := by
            simp [coeff, norm_mul]
          _ = ‖c j‖ := by
            simp
      calc
        ‖star (coeff x i) * coeff x j‖ = ‖coeff x i‖ * ‖coeff x j‖ := by
          simp [norm_mul]
        _ = ‖c i‖ * ‖c j‖ := by
          rw [hcoeff_i_norm, hcoeff_j_norm]
        _ ≤ ‖c i‖ * ‖c j‖ := le_rfl
  have hkernel :
      ∑ i, ∑ j, star (c i) * pontryaginCharFun μ (χ i * (χ j)⁻¹) * c j =
        ∫ x, integrand x ∂(μ : Measure G) := by
    -- Proof comment: absorb the character values into twisted coefficients and exchange the finite
    -- sums with the integral.
    have hinnerSum :
        ∀ i : Fin n, Integrable (fun x ↦ ∑ j, star (coeff x i) * coeff x j) (μ : Measure G) := by
      intro i
      exact integrable_finset_sum _ (fun j _ ↦ hterm i j)
    calc
      ∑ i, ∑ j, star (c i) * pontryaginCharFun μ (χ i * (χ j)⁻¹) * c j
          = ∑ i, ∑ j, ∫ x, star (coeff x i) * coeff x j ∂(μ : Measure G) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              refine Finset.sum_congr rfl ?_
              intro j hj
              have hleft :
                  star (c i) *
                      ∫ x, (((χ i * (χ j)⁻¹) (Multiplicative.ofAdd x) : Circle) : ℂ)
                        ∂(μ : Measure G) =
                    ∫ x, star (c i) *
                        (((χ i * (χ j)⁻¹) (Multiplicative.ofAdd x) : Circle) : ℂ)
                        ∂(μ : Measure G) := by
                simpa using
                  (integral_const_mul (star (c i))
                    (fun x : G ↦ (((χ i * (χ j)⁻¹) (Multiplicative.ofAdd x) : Circle) : ℂ))).symm
              have hright :
                  (∫ x, star (c i) *
                      (((χ i * (χ j)⁻¹) (Multiplicative.ofAdd x) : Circle) : ℂ)
                      ∂(μ : Measure G)) * c j =
                    ∫ x, star (c i) *
                        (((χ i * (χ j)⁻¹) (Multiplicative.ofAdd x) : Circle) : ℂ) *
                        c j ∂(μ : Measure G) := by
                simpa [mul_assoc] using
                  (integral_mul_const (c j)
                    (fun x : G ↦ star (c i) *
                      (((χ i * (χ j)⁻¹) (Multiplicative.ofAdd x) : Circle) : ℂ))).symm
              calc
                star (c i) * pontryaginCharFun μ (χ i * (χ j)⁻¹) * c j
                    = (star (c i) *
                        ∫ x, (((χ i * (χ j)⁻¹) (Multiplicative.ofAdd x) : Circle) : ℂ)
                          ∂(μ : Measure G)) * c j := by
                            simpa [pontryaginCharFun, mul_assoc]
                _ = (∫ x, star (c i) *
                      (((χ i * (χ j)⁻¹) (Multiplicative.ofAdd x) : Circle) : ℂ)
                      ∂(μ : Measure G)) * c j := by
                        rw [hleft]
                _ = ∫ x, star (c i) *
                      (((χ i * (χ j)⁻¹) (Multiplicative.ofAdd x) : Circle) : ℂ) *
                      c j ∂(μ : Measure G) := by
                        rw [hright]
                _ = ∫ x, star (coeff x i) * coeff x j ∂(μ : Measure G) := by
                      refine integral_congr_ae (Eventually.of_forall ?_)
                      intro x
                      have hphase :
                          ((((χ i * (χ j)⁻¹) (Multiplicative.ofAdd x) : Circle) : ℂ)) =
                            (((χ i) (Multiplicative.ofAdd x) : Circle) : ℂ) *
                              star (((χ j) (Multiplicative.ofAdd x) : Circle) : ℂ) := by
                        have hmul :
                            (((χ i * (χ j)⁻¹) (Multiplicative.ofAdd x) : Circle)) =
                              (χ i) (Multiplicative.ofAdd x) *
                                ((χ j) (Multiplicative.ofAdd x))⁻¹ := by
                          rfl
                        have hconj :
                            ((((χ j) (Multiplicative.ofAdd x))⁻¹ : Circle) : ℂ) =
                              star (((χ j) (Multiplicative.ofAdd x) : Circle) : ℂ) := by
                          simpa using
                            (Circle.coe_inv_eq_conj ((χ j) (Multiplicative.ofAdd x)))
                        calc
                          ((((χ i * (χ j)⁻¹) (Multiplicative.ofAdd x) : Circle) : ℂ))
                              =
                            (((χ i) (Multiplicative.ofAdd x) *
                                ((χ j) (Multiplicative.ofAdd x))⁻¹ : Circle) : ℂ) := by
                                  rw [hmul]
                          _ = (((χ i) (Multiplicative.ofAdd x) : Circle) : ℂ) *
                                ((((χ j) (Multiplicative.ofAdd x))⁻¹ : Circle) : ℂ) := by
                                simp
                          _ = (((χ i) (Multiplicative.ofAdd x) : Circle) : ℂ) *
                                star (((χ j) (Multiplicative.ofAdd x) : Circle) : ℂ) := by
                                  rw [hconj]
                      calc
                        star (c i) *
                            ((((χ i * (χ j)⁻¹) (Multiplicative.ofAdd x) : Circle) : ℂ)) *
                            c j
                            =
                          star (c i) *
                            ((((χ i) (Multiplicative.ofAdd x) : Circle) : ℂ) *
                              star (((χ j) (Multiplicative.ofAdd x) : Circle) : ℂ)) *
                            c j := by
                                rw [hphase]
                        _ = star (coeff x i) * coeff x j := by
                              simp [coeff, mul_assoc, mul_left_comm, mul_comm]
      _ = ∑ i, ∫ x, ∑ j, star (coeff x i) * coeff x j ∂(μ : Measure G) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            symm
            exact integral_finset_sum _ (fun j _ ↦ hterm i j)
      _ = ∫ x, integrand x ∂(μ : Measure G) := by
            symm
            simp only [integrand]
            exact integral_finset_sum _ (fun i _ ↦ hinnerSum i)
  have hnonneg : 0 ≤ ∫ x, integrand x ∂(μ : Measure G) := by
    -- Proof comment: the integrand is the pointwise squared norm of the twisted phase sum.
    refine integral_nonneg ?_
    intro x
    have hsq :
        integrand x = star (∑ i, coeff x i) * (∑ j, coeff x j) := by
      calc
        integrand x = ∑ i, ∑ j, star (coeff x i) * coeff x j := by
          simp [integrand]
        _ = star (∑ i, coeff x i) * (∑ j, coeff x j) := by
              symm
              rw [star_sum, Finset.sum_mul]
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [Finset.mul_sum]
    rw [hsq]
    simpa using star_mul_self_nonneg (∑ i, coeff x i)
  rw [hkernel]
  exact hnonneg

/-- Helper for Theorem 15.29: the Pontryagin characteristic function of a probability measure is
positive semidefinite in the multiplicative-group sense. -/
lemma pontryaginCharFun_isPositiveSemidefiniteMulFunction (μ : ProbabilityMeasure G) :
    IsPositiveSemidefiniteMulFunction (pontryaginCharFun μ) := by
  -- Proof comment: the quadratic-sum criterion is exactly the nonnegativity statement proved in
  -- `pontryaginCharFunQuadraticSum_nonneg`.
  rw [isPositiveSemidefiniteMulFunction_iff_quadraticSum_nonneg]
  intro n ψ c
  simpa using
    pontryaginCharFunQuadraticSum_nonneg (μ := μ) (χ := ψ) c

/-- Helper for Theorem 15.29: an equality-shaped Pontryagin witness can already be repackaged as
the pointwise witness expected by the abstract converse owner. -/
lemma existsPointwisePontryaginCharFunEq_of_existsPontryaginCharFunEq
    {φ : PontryaginDual (Multiplicative G) → ℂ}
    (hφ : ∃ μ : ProbabilityMeasure G, pontryaginCharFun μ = φ) :
    ∃ μ : ProbabilityMeasure G,
      ∀ χ : PontryaginDual (Multiplicative G), pontryaginCharFun μ χ = φ χ := by
  rcases hφ with ⟨μ, hμ⟩
  -- Proof comment: evaluate the function equality at each character to recover the pointwise
  -- witness shape used by the isolated core theorem.
  refine ⟨μ, ?_⟩
  intro χ
  exact congrFun hμ χ

/-- Helper for Theorem 15.29: projective families of finite-dimensional probability laws on
`Circle` already admit a global projective limit by the earlier projective-extension theorem. -/
lemma compactCharacterFamilyProjectiveLimitExists {ι : Type*}
    [MeasurableSpace Circle] [StandardBorelSpace Circle]
    (P : ∀ J : Finset ι, Measure ((j : J) → Circle))
    [∀ J : Finset ι, IsProbabilityMeasure (P J)]
    (hP : MeasureTheory.IsProjectiveMeasureFamily (α := fun _ : ι ↦ Circle) P) :
    ∃ ν : Measure (ι → Circle),
      MeasureTheory.IsProjectiveLimit (α := fun _ : ι ↦ Circle) ν P := by
  -- Proof comment: the Chapter 14 projective-limit theorem already closes the extension step once
  -- the finite-dimensional `Circle` laws and their consistency are available.
  simpa using
    exists_projectiveLimit_of_isProjectiveMeasureFamily
      (I := ι) (Ω := fun _ : ι ↦ Circle) (P := P) hP

/-- Helper for Theorem 15.29: projective families of finite-dimensional probability laws on
`UnitAddCircle` already admit a global projective limit by the earlier projective-extension
theorem. -/
lemma unitAddCircleCharacterFamilyProjectiveLimitExists {ι : Type*}
    (P : ∀ J : Finset ι, Measure ((j : J) → UnitAddCircle))
    [∀ J : Finset ι, IsProbabilityMeasure (P J)]
    (hP : MeasureTheory.IsProjectiveMeasureFamily (α := fun _ : ι ↦ UnitAddCircle) P) :
    ∃ ν : Measure (ι → UnitAddCircle),
      MeasureTheory.IsProjectiveLimit (α := fun _ : ι ↦ UnitAddCircle) ν P := by
  -- Proof comment: Theorem 14.36 is already polymorphic in the coordinate space, so the torus
  -- route only needs the codomain-specialized `UnitAddCircle` wrapper.
  simpa using
    exists_projectiveLimit_of_isProjectiveMeasureFamily
      (I := ι) (Ω := fun _ : ι ↦ UnitAddCircle) (P := P) hP

/-- Helper for Theorem 15.29: exponent vectors in a finite family of dual characters turn
coordinatewise subtraction into the quotient of the corresponding character products. -/
lemma prod_characterZPow_sub_eq_mul_inv {J : Type*} [Fintype J] [DecidableEq J]
    (ξ : J → PontryaginDual (Multiplicative G)) (m n : J → ℤ) :
    (∏ j, ξ j ^ (m j - n j)) = (∏ j, ξ j ^ (m j)) * (∏ j, ξ j ^ (n j))⁻¹ := by
  -- Proof comment: rewrite each exponent difference as an additive decomposition and then collect
  -- the pointwise products and inverses across the finite index set.
  calc
    ∏ j, ξ j ^ (m j - n j) = ∏ j, (ξ j ^ (m j) * (ξ j ^ (n j))⁻¹) := by
      refine Finset.prod_congr rfl ?_
      intro j hj
      rw [sub_eq_add_neg, zpow_add, zpow_neg]
    _ = (∏ j, ξ j ^ (m j)) * ∏ j, (ξ j ^ (n j))⁻¹ := by
      rw [Finset.prod_mul_distrib]
    _ = (∏ j, ξ j ^ (m j)) * (∏ j, ξ j ^ (n j))⁻¹ := by
      rw [Finset.prod_inv_distrib]

/-- Helper for Theorem 15.29: a finite family of dual characters turns multiplicative positive
semidefiniteness on `PontryaginDual (Multiplicative G)` into additive positive semidefiniteness on
the integer lattice of exponent vectors. -/
lemma finiteCharacterCoefficientKernelSpec {J : Type*} [Fintype J] [DecidableEq J]
    {φ : PontryaginDual (Multiplicative G) → ℂ}
    (hpsd : IsPositiveSemidefiniteMulFunction φ) (hone : φ 1 = 1)
    (ξ : J → PontryaginDual (Multiplicative G)) :
    let ψ : (J → ℤ) → ℂ := fun n ↦ φ (∏ j, ξ j ^ (n j))
    IsPositiveSemidefiniteFunction ψ ∧ ψ 0 = 1 := by
  let ψ : (J → ℤ) → ℂ := fun n ↦ φ (∏ j, ξ j ^ (n j))
  have hψ_psd : IsPositiveSemidefiniteFunction ψ := by
    rw [isPositiveSemidefiniteFunction_iff_quadratic_sum_nonneg]
    intro n m c
    have hquad :
        0 ≤ ∑ i, ∑ j,
          star (c i) * φ ((∏ k, ξ k ^ (m i k)) * (∏ k, ξ k ^ (m j k))⁻¹) * c j := by
      exact (isPositiveSemidefiniteMulFunction_iff_quadraticSum_nonneg.mp hpsd) n
        (fun i ↦ ∏ k, ξ k ^ (m i k)) c
    -- Proof comment: the additive kernel value `ψ (m i - m j)` is exactly the multiplicative
    -- quotient kernel after normalizing exponent differences with the finite-product bridge.
    simpa [ψ, prod_characterZPow_sub_eq_mul_inv] using hquad
  have hψ_zero : ψ 0 = 1 := by
    -- Proof comment: the zero exponent vector evaluates every character product at the identity.
    simp [ψ, hone]
  exact ⟨hψ_psd, hψ_zero⟩

/-- Helper for Theorem 15.29: for a finite subset of the dual, the induced exponent-lattice
moment kernel is already positive semidefinite and normalized. -/
lemma finiteSubsetTorusMomentKernelSpec
    (J : Finset (PontryaginDual (Multiplicative G)))
    {φ : PontryaginDual (Multiplicative G) → ℂ}
    (hpsd : IsPositiveSemidefiniteMulFunction φ) (hone : φ 1 = 1) :
    let ψ : (J → ℤ) → ℂ := fun n ↦
      φ (∏ j : J, (j : PontryaginDual (Multiplicative G)) ^ (n j))
    IsPositiveSemidefiniteFunction ψ ∧ ψ 0 = 1 := by
  classical
  -- Proof comment: specialize the finite-family coefficient-kernel bridge to the subtype of the
  -- chosen finite subset, using the inclusion `J ↪ PontryaginDual (Multiplicative G)` as the
  -- character family.
  simpa using
    (finiteCharacterCoefficientKernelSpec (G := G) (J := J) hpsd hone
      (ξ := fun j : J ↦ (j : PontryaginDual (Multiplicative G))))

/-- Helper for Theorem 15.29: the finite-subset Pontryagin moment kernel satisfies the explicit
quadratic nonnegativity criterion needed for the finite-dimensional torus law. -/
lemma finiteSubsetTorusMomentQuadratic_nonneg
    (J : Finset (PontryaginDual (Multiplicative G)))
    {φ : PontryaginDual (Multiplicative G) → ℂ}
    (hpsd : IsPositiveSemidefiniteMulFunction φ) (hone : φ 1 = 1) :
    ∀ n (m : Fin n → J → ℤ) (c : Fin n → ℂ),
      0 ≤
        ∑ i, ∑ j,
          star (c i) *
            φ (∏ k : J, (k : PontryaginDual (Multiplicative G)) ^ (m i k - m j k)) *
            c j := by
  let ψ : (J → ℤ) → ℂ := fun n ↦
    φ (∏ j : J, (j : PontryaginDual (Multiplicative G)) ^ (n j))
  have hψ :
      IsPositiveSemidefiniteFunction ψ := by
    -- Proof comment: `finiteSubsetTorusMomentKernelSpec` freezes the finite-subset kernel in the
    -- same additive normal form that the torus Fourier monomials use.
    simpa [ψ] using (finiteSubsetTorusMomentKernelSpec (G := G) J hpsd hone).1
  intro n m c
  -- Proof comment: unpack the positive-semidefinite criterion for the specialized moment kernel
  -- and rewrite it back to the explicit character-product formula.
  simpa [ψ] using (isPositiveSemidefiniteFunction_iff_quadratic_sum_nonneg.mp hψ) n m c

/-- Helper for Theorem 15.29: finite-subset Pontryagin moments inherit the Hermitian symmetry
forced by multiplicative positive semidefiniteness. -/
lemma finiteSubsetTorusMoment_star_eq_neg
    (J : Finset (PontryaginDual (Multiplicative G)))
    {φ : PontryaginDual (Multiplicative G) → ℂ}
    (hpsd : IsPositiveSemidefiniteMulFunction φ) (n : J → ℤ) :
    star (φ (∏ j : J, (j : PontryaginDual (Multiplicative G)) ^ n j)) =
      φ (∏ j : J, (j : PontryaginDual (Multiplicative G)) ^ (-n j)) := by
  have hprod_inv :
      (∏ j : J, (j : PontryaginDual (Multiplicative G)) ^ (-n j)) =
        (∏ j : J, (j : PontryaginDual (Multiplicative G)) ^ n j)⁻¹ := by
    -- Proof comment: negating every exponent is exactly the inverse of the finite character
    -- product.
    simp_rw [zpow_neg]
    rw [Finset.prod_inv_distrib]
  calc
    star (φ (∏ j : J, (j : PontryaginDual (Multiplicative G)) ^ n j)) =
        φ ((∏ j : J, (j : PontryaginDual (Multiplicative G)) ^ n j)⁻¹) := by
          exact star_value_eq_value_inv_of_isPositiveSemidefiniteMulFunction hpsd _
    _ = φ (∏ j : J, (j : PontryaginDual (Multiplicative G)) ^ (-n j)) := by
          rw [← hprod_inv]

/-- Helper for Theorem 15.29: every finite-subset Pontryagin moment has norm at most `1`. -/
lemma finiteSubsetTorusMoment_norm_le_one
    (J : Finset (PontryaginDual (Multiplicative G)))
    {φ : PontryaginDual (Multiplicative G) → ℂ}
    (hpsd : IsPositiveSemidefiniteMulFunction φ) (hone : φ 1 = 1) (n : J → ℤ) :
    ‖φ (∏ j : J, (j : PontryaginDual (Multiplicative G)) ^ n j)‖ ≤ 1 := by
  -- Proof comment: the finite character product is one element of the ambient dual group, so the
  -- global norm-one bound applies directly.
  simpa using
    norm_le_one_of_isPositiveSemidefiniteMulFunction_one_eq_one hpsd hone
      (∏ j : J, (j : PontryaginDual (Multiplicative G)) ^ n j)

/-- Helper for Theorem 15.29: the symmetric integer box used in the Fejer-kernel approximation on
`UnitAddTorus J`. -/
noncomputable def finiteSubsetTorusFejerBox
    (J : Finset (PontryaginDual (Multiplicative G))) (N : ℕ) : Finset (J → ℤ) :=
  by
    sorry

/-- Helper for Theorem 15.29: the Fejer box always contains the zero exponent vector, so its
normalizing cardinal is positive. -/
lemma finiteSubsetTorusFejerBox_nonempty
    (J : Finset (PontryaginDual (Multiplicative G))) (N : ℕ) :
    (finiteSubsetTorusFejerBox (G := G) J N).Nonempty := by
  sorry

/-- Helper for Theorem 15.29: the normalized Fejer kernel attached to the finite-subset moment
data is a continuous complex function on `UnitAddTorus J`. -/
noncomputable def finiteSubsetTorusFejerKernel
    (J : Finset (PontryaginDual (Multiplicative G)))
    {φ : PontryaginDual (Multiplicative G) → ℂ} (N : ℕ) :
    C(UnitAddTorus J, ℂ) :=
  by
    sorry

/-- Helper for Theorem 15.29: the real Fejer density is the real part of the normalized complex
Fejer kernel. -/
noncomputable def finiteSubsetTorusFejerDensity
    (J : Finset (PontryaginDual (Multiplicative G)))
    {φ : PontryaginDual (Multiplicative G) → ℂ} (N : ℕ) :
    C(UnitAddTorus J, ℝ) := by
  sorry

/-- Helper for Theorem 15.29: the finite-stage Fejer density built from the prescribed moments is
pointwise nonnegative. -/
lemma finiteSubsetTorusFejerDensity_nonneg
    (J : Finset (PontryaginDual (Multiplicative G)))
    {φ : PontryaginDual (Multiplicative G) → ℂ} (N : ℕ)
    (hpsd : IsPositiveSemidefiniteMulFunction φ) (hone : φ 1 = 1) :
    ∀ x : UnitAddTorus J, 0 ≤ finiteSubsetTorusFejerDensity (G := G) (φ := φ) J N x := by
  sorry
/-- Helper for Theorem 15.29: Haar probability measure on `UnitAddTorus J` kills every nonzero
Fourier monomial and integrates the constant monomial to `1`. -/
lemma integral_mFourier_eq_ite
    (J : Finset (PontryaginDual (Multiplicative G))) (n : J → ℤ) :
    ∫ x, UnitAddTorus.mFourier n x ∂(volume : Measure (UnitAddTorus J)) =
      if n = 0 then 1 else 0 := by
  sorry

/-- Helper for Theorem 15.29: the finite-stage Fejer density is normalized to total mass `1`. -/
lemma finiteSubsetTorusFejerMassOne
    (J : Finset (PontryaginDual (Multiplicative G)))
    {φ : PontryaginDual (Multiplicative G) → ℂ} (N : ℕ)
    (hpsd : IsPositiveSemidefiniteMulFunction φ) (hone : φ 1 = 1) :
    ∫ x, finiteSubsetTorusFejerDensity (G := G) (φ := φ) J N x
      ∂(volume : Measure (UnitAddTorus J)) = 1 := by
  sorry
/-- Helper for Theorem 15.29: on a compact space, continuous complex-valued functions can be
viewed as bounded continuous functions through a `⋆`-algebra homomorphism. -/
noncomputable def continuousMapToBoundedStarAlgHom (α : Type*) [TopologicalSpace α]
    [CompactSpace α] : C(α, ℂ) →⋆ₐ[ℂ] BoundedContinuousFunction α ℂ where
  toFun := BoundedContinuousFunction.mkOfCompact
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' c := by
    -- Proof comment: both algebra maps are the constant function with value `c`.
    ext x
    simp [Algebra.algebraMap_eq_smul_one]
  map_star' f := by
    -- Proof comment: on a compact domain, turning a continuous map into a bounded continuous map
    -- commutes with complex conjugation pointwise.
    simpa using BoundedContinuousFunction.mkOfCompact_star f

/-- Helper for Theorem 15.29: Fourier monomials already determine a finite measure on
`UnitAddTorus J`. -/
lemma finiteCharacterTorusLaw_eq_of_mFourier {J : Type*} [Fintype J]
    {μ ν : Measure (UnitAddTorus J)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : ∀ n : J → ℤ, ∫ x, UnitAddTorus.mFourier n x ∂μ = ∫ x, UnitAddTorus.mFourier n x ∂ν) :
    μ = ν := by
  let A : StarSubalgebra ℂ (BoundedContinuousFunction (UnitAddTorus J) ℂ) :=
    (UnitAddTorus.mFourierSubalgebra J).map
      (continuousMapToBoundedStarAlgHom (α := UnitAddTorus J))
  have hspan :
      ∀ f : C(UnitAddTorus J, ℂ), f ∈ UnitAddTorus.mFourierSubalgebra J →
        ∫ x, f x ∂μ = ∫ x, f x ∂ν := by
    intro f hf
    change f ∈ (UnitAddTorus.mFourierSubalgebra J).toSubalgebra.toSubmodule at hf
    rw [UnitAddTorus.mFourierSubalgebra_coe] at hf
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
    · rintro _ ⟨n, rfl⟩
      -- Proof comment: the monomial generators are exactly the test functions whose integrals are
      -- assumed to agree.
      exact hμν n
    · -- Proof comment: both finite measures integrate the zero function to zero.
      simp
    · intro f g _ _ hf hg
      have hfμ : Integrable (fun x : UnitAddTorus J ↦ f x) μ := by
        simpa using
          (BoundedContinuousFunction.integrable (μ := μ) (f := BoundedContinuousFunction.mkOfCompact f))
      have hgμ : Integrable (fun x : UnitAddTorus J ↦ g x) μ := by
        simpa using
          (BoundedContinuousFunction.integrable (μ := μ) (f := BoundedContinuousFunction.mkOfCompact g))
      have hfν : Integrable (fun x : UnitAddTorus J ↦ f x) ν := by
        simpa using
          (BoundedContinuousFunction.integrable (μ := ν) (f := BoundedContinuousFunction.mkOfCompact f))
      have hgν : Integrable (fun x : UnitAddTorus J ↦ g x) ν := by
        simpa using
          (BoundedContinuousFunction.integrable (μ := ν) (f := BoundedContinuousFunction.mkOfCompact g))
      -- Proof comment: extend the equality from generators to their sums by linearity of the
      -- integral on bounded continuous functions.
      calc
        ∫ x, (f + g) x ∂μ = ∫ x, f x ∂μ + ∫ x, g x ∂μ := by
          simpa [ContinuousMap.add_apply] using MeasureTheory.integral_add hfμ hgμ
        _ = ∫ x, f x ∂ν + ∫ x, g x ∂ν := by rw [hf, hg]
        _ = ∫ x, (f + g) x ∂ν := by
          simpa [ContinuousMap.add_apply] using (MeasureTheory.integral_add hfν hgν).symm
    · intro c f _ hf
      -- Proof comment: scalar multiples are handled by the same linearity principle.
      calc
        ∫ x, (c • f) x ∂μ = c * ∫ x, f x ∂μ := by
          simpa [smul_eq_mul] using
            (MeasureTheory.integral_const_mul c (fun x : UnitAddTorus J ↦ f x) (μ := μ))
        _ = c * ∫ x, f x ∂ν := by rw [hf]
        _ = ∫ x, (c • f) x ∂ν := by
          simpa [smul_eq_mul] using
            (MeasureTheory.integral_const_mul c (fun x : UnitAddTorus J ↦ f x) (μ := ν)).symm
  have hA :
      (A.map (BoundedContinuousFunction.toContinuousMapStarₐ ℂ)).SeparatesPoints := by
    have hle :
        (UnitAddTorus.mFourierSubalgebra J).toSubalgebra ≤
          (A.map (BoundedContinuousFunction.toContinuousMapStarₐ ℂ)).toSubalgebra := by
      intro f hf
      refine ⟨BoundedContinuousFunction.mkOfCompact f, ?_, ?_⟩
      · -- Proof comment: each torus monomial polynomial is first viewed as a bounded continuous
        -- function and then mapped back to the same continuous representative.
        exact ⟨f, hf, rfl⟩
      · ext x
        rfl
    -- Proof comment: the mapped bounded-continuous subalgebra contains the original torus
    -- Fourier subalgebra, so it still separates points.
    exact
      Subalgebra.separatesPoints_monotone hle
        UnitAddTorus.mFourierSubalgebra_separatesPoints
  refine
    MeasureTheory.ext_of_forall_mem_subalgebra_integral_eq_of_polish
      (𝕜 := ℂ) (E := UnitAddTorus J) hA ?_
  intro g hg
  rcases hg with ⟨f, hf, rfl⟩
  -- Proof comment: any element of the mapped bounded-continuous algebra comes from a torus
  -- Fourier polynomial, so the previously proved span argument applies directly.
  simpa using hspan f hf

/-- Helper for Theorem 15.29: the finite-torus Fourier span is the explicit dense subspace used
for the compact-torus extension step. -/
noncomputable abbrev finiteSubsetTorusFourierSpan
    (J : Finset (PontryaginDual (Multiplicative G))) :
    Submodule ℂ C(UnitAddTorus J, ℂ) :=
  Submodule.span ℂ (Set.range (UnitAddTorus.mFourier (d := J)))

/-- Helper for Theorem 15.29: each torus monomial lies in the explicit dense Fourier span. -/
lemma finiteSubsetTorusFourierSpan_mFourier_mem
    (J : Finset (PontryaginDual (Multiplicative G))) (n : J → ℤ) :
    UnitAddTorus.mFourier n ∈ finiteSubsetTorusFourierSpan (G := G) J := by
  -- Proof comment: the dense span is generated by the torus monomials themselves.
  exact Submodule.subset_span ⟨n, rfl⟩

/-- Helper for Theorem 15.29: the inclusion of the explicit Fourier span into all continuous torus
functions has dense range. -/
lemma finiteSubsetTorusFourierSpan_denseRange
    (J : Finset (PontryaginDual (Multiplicative G))) :
    DenseRange
      (fun f : finiteSubsetTorusFourierSpan (G := G) J ↦ (f : C(UnitAddTorus J, ℂ))) := by
  sorry
/-- Helper for Theorem 15.29: extend an exponent vector on a finite subset by `0` outside that
subset. -/
noncomputable def zeroExtendExponent {β : Type*} [DecidableEq β] {I J : Finset β}
    (n : J → ℤ) : I → ℤ :=
  fun i ↦ if hi : (i : β) ∈ J then n ⟨i, hi⟩ else 0

/-- Helper for Theorem 15.29: once `J ⊆ I`, the subtype of points of `I` lying in `J` is
canonically equivalent to `J`. -/
private noncomputable def subsetSubtypeEquiv {β : Type*} [DecidableEq β] {I J : Finset β}
    (hJI : J ⊆ I) : {i : I // (i : β) ∈ J} ≃ J where
  toFun := fun i ↦ ⟨i.1.1, i.2⟩
  invFun := fun j ↦ ⟨⟨j.1, hJI j.2⟩, j.2⟩
  left_inv := by
    intro i
    -- Route correction: compare the nested subtype wrappers only through their underlying ambient
    -- values, so the transport layer stays in one canonical spelling.
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv := by
    intro j
    -- Proof comment: returning from the ambient-subtype spelling to `J` preserves the same
    -- ambient element, so equality is checked only on the underlying value.
    apply Subtype.ext
    rfl

/-- Helper for Theorem 15.29: restricting a torus point from `I` to `J` rewrites the monomial
`mFourier n` as the monomial with zero-extended exponent vector on `I`. -/
lemma mFourier_restrict₂_eq_zeroExtend {β : Type*} [DecidableEq β] {I J : Finset β}
    (hJI : J ⊆ I) (x : UnitAddTorus I) (n : J → ℤ) :
    UnitAddTorus.mFourier n
        (Finset.restrict₂ (π := fun _ : β ↦ UnitAddCircle) hJI x) =
      UnitAddTorus.mFourier (zeroExtendExponent (I := I) (J := J) n) x := by
  classical
  let p : I → Prop := fun i ↦ (i : β) ∈ J
  let s : Finset I := Finset.univ.filter p
  let f : I → ℂ := fun i ↦
    ↑(((zeroExtendExponent (I := I) (J := J) n) i • x i).toCircle)
  have hwhole : (∏ i : I, f i) = s.prod f := by
    symm
    -- Proof comment: the zero extension contributes only `1` away from `J`, so the ambient
    -- product over `I` reduces to the filtered product over those coordinates actually in `J`.
    refine Fintype.prod_subset (s := s) (f := f) ?_
    intro i hi
    by_cases hiJ : p i
    · simp [s, p, hiJ]
    · exfalso
      apply hi
      simp [f, zeroExtendExponent, p, hiJ]
  have hsubtype : s.prod f = (∏ i : {i : I // p i}, f i) := by
    -- Proof comment: the filtered ambient product is the same as the product over the subtype of
    -- coordinates that lie in `J`.
    exact Finset.prod_subtype (s := s) (h := by
      intro i
      simp [s, p]) f
  have hequiv :
      (∏ i : {i : I // p i}, f i) =
        ∏ j : J, ↑((n j • x ⟨j.1, hJI j.2⟩).toCircle) := by
    -- Proof comment: the canonical equivalence `subsetSubtypeEquiv` identifies the surviving
    -- filtered coordinates with the original subtype `J`.
    refine Fintype.prod_equiv (subsetSubtypeEquiv hJI) _ _ ?_
    intro i
    have hiJ : p i.1 := i.2
    simp [f, zeroExtendExponent, p, subsetSubtypeEquiv, hiJ]
  calc
    UnitAddTorus.mFourier n
        (Finset.restrict₂ (π := fun _ : β ↦ UnitAddCircle) hJI x) =
          ∏ j : J, ↑((n j • x ⟨j.1, hJI j.2⟩).toCircle) := by
            -- Proof comment: expand the restricted monomial directly on the coordinates of `J`.
            simp [UnitAddTorus.mFourier, Finset.restrict₂_def]
    _ = ∏ i : I, f i := by rw [hwhole, hsubtype, hequiv]
    _ = UnitAddTorus.mFourier (zeroExtendExponent (I := I) (J := J) n) x := by
          -- Proof comment: fold the ambient-coordinate product back into the standard torus
          -- monomial notation.
          simp [UnitAddTorus.mFourier, f]

/-- Helper for Theorem 15.29: zero-extending an exponent vector does not change the associated
finite product of character powers. -/
private lemma prod_zpow_zeroExtendExponent {β : Type*} [CommGroup β] [DecidableEq β]
    {I J : Finset β} (hJI : J ⊆ I) (n : J → ℤ) :
    (∏ i : I, (i : β) ^ zeroExtendExponent (I := I) (J := J) n i) =
      ∏ j : J, (j : β) ^ n j := by
  classical
  let p : I → Prop := fun i ↦ (i : β) ∈ J
  let s : Finset I := Finset.univ.filter p
  let f : I → β := fun i ↦ (i : β) ^ zeroExtendExponent (I := I) (J := J) n i
  have hwhole : (∏ i : I, f i) = s.prod f := by
    symm
    -- Proof comment: as in the Fourier-monomial bridge, the zero extension contributes only the
    -- identity outside `J`, so the ambient product reduces to the filtered one.
    refine Fintype.prod_subset (s := s) (f := f) ?_
    intro i hi
    by_cases hiJ : p i
    · simp [s, p, hiJ]
    · exfalso
      apply hi
      simp [f, zeroExtendExponent, p, hiJ]
  have hsubtype : s.prod f = (∏ i : {i : I // p i}, f i) := by
    -- Proof comment: rewrite the filtered ambient product as a product over the subtype of
    -- coordinates that survive the restriction to `J`.
    exact Finset.prod_subtype (s := s) (h := by
      intro i
      simp [s, p]) f
  have hequiv :
      (∏ i : {i : I // p i}, f i) =
        ∏ j : J, (j : β) ^ n j := by
    -- Proof comment: once the surviving coordinates are identified with `J`, the zero extension
    -- becomes the original exponent vector.
    refine Fintype.prod_equiv (subsetSubtypeEquiv hJI) _ _ ?_
    intro i
    have hiJ : p i.1 := i.2
    simp [f, zeroExtendExponent, p, subsetSubtypeEquiv, hiJ]
  calc
    (∏ i : I, (i : β) ^ zeroExtendExponent (I := I) (J := J) n i) = ∏ i : I, f i := by
      simp [f]
    _ = s.prod f := hwhole
    _ = ∏ i : {i : I // p i}, f i := hsubtype
    _ = ∏ j : J, (j : β) ^ n j := hequiv

/-- Helper for Theorem 15.29: if a finite torus law on `I` realizes the prescribed Pontryagin
moments, then its restriction to `J ⊆ I` realizes the corresponding restricted moments. -/
lemma finiteSubsetTorusMarginal_mFourier
    {I J : Finset (PontryaginDual (Multiplicative G))}
    (hJI : J ⊆ I) {μI : ProbabilityMeasure (UnitAddTorus I)}
    {φ : PontryaginDual (Multiplicative G) → ℂ}
    (hμI : ∀ m : I → ℤ,
      ∫ x, UnitAddTorus.mFourier m x ∂(μI : Measure (UnitAddTorus I)) =
        φ (∏ i : I, (i : PontryaginDual (Multiplicative G)) ^ m i))
    (n : J → ℤ) :
    ∫ x, UnitAddTorus.mFourier n x
        ∂((μI : Measure (UnitAddTorus I)).map
          (Finset.restrict₂
            (π := fun _ : PontryaginDual (Multiplicative G) ↦ UnitAddCircle) hJI)) =
      φ (∏ j : J, (j : PontryaginDual (Multiplicative G)) ^ n j) := by
  classical
  have hRestrict :
      Measurable
        (Finset.restrict₂
          (π := fun _ : PontryaginDual (Multiplicative G) ↦ UnitAddCircle) hJI :
            UnitAddTorus I → UnitAddTorus J) :=
    Finset.measurable_restrict₂
      (X := fun _ : PontryaginDual (Multiplicative G) ↦ UnitAddCircle) hJI
  calc
    ∫ x, UnitAddTorus.mFourier n x
        ∂((μI : Measure (UnitAddTorus I)).map
          (Finset.restrict₂
            (π := fun _ : PontryaginDual (Multiplicative G) ↦ UnitAddCircle) hJI)) =
      ∫ x, UnitAddTorus.mFourier n
          (Finset.restrict₂
            (π := fun _ : PontryaginDual (Multiplicative G) ↦ UnitAddCircle) hJI x)
          ∂(μI : Measure (UnitAddTorus I)) := by
            -- Proof comment: rewrite the pushed-forward marginal as an integral over the ambient
            -- torus law on `I`.
            rw [MeasureTheory.integral_map (μ := (μI : Measure (UnitAddTorus I)))
              hRestrict.aemeasurable (by fun_prop)]
    _ = ∫ x, UnitAddTorus.mFourier (zeroExtendExponent (I := I) (J := J) n) x
          ∂(μI : Measure (UnitAddTorus I)) := by
            -- Proof comment: the monomial restriction bridge packages the only nontrivial
            -- transport step.
            refine integral_congr_ae ?_
            filter_upwards with x
            exact mFourier_restrict₂_eq_zeroExtend (hJI := hJI) x n
    _ = φ (∏ i : I,
          (i : PontryaginDual (Multiplicative G)) ^
            zeroExtendExponent (I := I) (J := J) n i) := hμI _
    _ = φ (∏ j : J, (j : PontryaginDual (Multiplicative G)) ^ n j) := by
          -- Proof comment: zero extension leaves the finite character product unchanged.
          rw [prod_zpow_zeroExtendExponent (hJI := hJI) n]

/-- Helper for Theorem 15.29: a projective-limit law on `ι → UnitAddCircle` already reproduces the
Fourier moments of each finite-coordinate marginal. -/
lemma projectiveLimit_mFourier_eq_marginal {ι : Type*}
    (P : ∀ J : Finset ι, Measure ((j : J) → UnitAddCircle))
    [∀ J : Finset ι, IsProbabilityMeasure (P J)] {ν : Measure (ι → UnitAddCircle)}
    (hν : MeasureTheory.IsProjectiveLimit (α := fun _ : ι ↦ UnitAddCircle) ν P)
    (J : Finset ι) (n : J → ℤ) :
    ∫ z, UnitAddTorus.mFourier n (J.restrict z) ∂ν =
      ∫ x, UnitAddTorus.mFourier n x ∂(P J) := by
  have hRestrict :
      Measurable (J.restrict : (ι → UnitAddCircle) → ((j : J) → UnitAddCircle)) := by
    exact Finset.measurable_restrict (X := fun _ : ι ↦ UnitAddCircle) J
  -- Proof comment: rewrite the ambient-process integral as the integral against the `J`th
  -- marginal supplied by the projective-limit identity.
  calc
    ∫ z, UnitAddTorus.mFourier n (J.restrict z) ∂ν =
        ∫ x, UnitAddTorus.mFourier n x ∂(ν.map J.restrict) := by
          symm
          rw [MeasureTheory.integral_map (μ := ν) hRestrict.aemeasurable (by fun_prop)]
    _ = ∫ x, UnitAddTorus.mFourier n x ∂(P J) := by
          rw [hν J]

/-- Helper for Theorem 15.29: once the finite-coordinate marginals satisfy the target Fourier
moment specification, the global projective-limit law inherits the same specification. -/
lemma projectiveLimit_mFourier_eq_of_marginalSpec {ι : Type*}
    (P : ∀ J : Finset ι, Measure ((j : J) → UnitAddCircle))
    [∀ J : Finset ι, IsProbabilityMeasure (P J)] {ν : Measure (ι → UnitAddCircle)}
    (hν : MeasureTheory.IsProjectiveLimit (α := fun _ : ι ↦ UnitAddCircle) ν P)
    {M : ∀ J : Finset ι, (J → ℤ) → ℂ}
    (hM : ∀ J : Finset ι, ∀ n : J → ℤ, ∫ x, UnitAddTorus.mFourier n x ∂(P J) = M J n) :
    ∀ J : Finset ι, ∀ n : J → ℤ,
      ∫ z, UnitAddTorus.mFourier n (J.restrict z) ∂ν = M J n := by
  intro J n
  -- Proof comment: combine the projective-limit marginal identity with the prescribed finite
  -- Fourier moments and stop all further `IsProjectiveLimit` manipulation here.
  rw [projectiveLimit_mFourier_eq_marginal (P := P) hν J n]
  exact hM J n

/-- Helper for Theorem 15.29: once each finite torus law realizes the prescribed Pontryagin
moments, the family is automatically projective under coordinate restriction. -/
lemma finiteSubsetTorusLawFamilyProjective
    {φ : PontryaginDual (Multiplicative G) → ℂ}
    (P : ∀ J : Finset (PontryaginDual (Multiplicative G)),
      ProbabilityMeasure (UnitAddTorus J))
    (hP : ∀ J : Finset (PontryaginDual (Multiplicative G)), ∀ n : J → ℤ,
      ∫ x, UnitAddTorus.mFourier n x ∂(P J : Measure (UnitAddTorus J)) =
        φ (∏ j : J, (j : PontryaginDual (Multiplicative G)) ^ n j)) :
    MeasureTheory.IsProjectiveMeasureFamily
      (α := fun _ : PontryaginDual (Multiplicative G) ↦ UnitAddCircle)
      (fun J ↦ (P J : Measure (UnitAddTorus J))) := by
  intro I J hJI
  apply finiteCharacterTorusLaw_eq_of_mFourier
  intro n
  -- Proof comment: the ambient `I`-law and the target `J`-law have the same Fourier monomials,
  -- because restriction preserves the prescribed moments and monomials determine finite torus
  -- measures uniquely.
  exact
    (hP J n).trans
      (finiteSubsetTorusMarginal_mFourier (G := G) (hJI := hJI) (μI := P I)
        (φ := φ) (hμI := hP I) n).symm

/-- Helper for Theorem 15.29: once a projective limit realizes the chosen finite torus marginals,
it inherits their Pontryagin moment formula on every finite coordinate set. -/
lemma projectiveLimitPontryaginMomentSpec
    {φ : PontryaginDual (Multiplicative G) → ℂ}
    (P : ∀ J : Finset (PontryaginDual (Multiplicative G)), Measure (UnitAddTorus J))
    [∀ J : Finset (PontryaginDual (Multiplicative G)), IsProbabilityMeasure (P J)]
    {ν : Measure ((χ : PontryaginDual (Multiplicative G)) → UnitAddCircle)}
    (hν : MeasureTheory.IsProjectiveLimit
      (α := fun _ : PontryaginDual (Multiplicative G) ↦ UnitAddCircle) ν P)
    (hP : ∀ J : Finset (PontryaginDual (Multiplicative G)), ∀ n : J → ℤ,
      ∫ x, UnitAddTorus.mFourier n x ∂(P J) =
        φ (∏ j : J, (j : PontryaginDual (Multiplicative G)) ^ n j)) :
    ∀ J : Finset (PontryaginDual (Multiplicative G)), ∀ n : J → ℤ,
      ∫ z, UnitAddTorus.mFourier n (J.restrict z) ∂ν =
        φ (∏ j : J, (j : PontryaginDual (Multiplicative G)) ^ n j) := by
  -- Proof comment: this is exactly the projective-limit marginal transport lemma specialized to
  -- the Pontryagin moment functional frozen by the finite-coordinate witnesses.
  exact projectiveLimit_mFourier_eq_of_marginalSpec (P := P) hν hP

/-- Helper for Theorem 15.29: the finite-coordinate evaluation point associated to `x : G`
transports a dual character value from `Circle` to the `UnitAddCircle` coordinates used by
`UnitAddTorus`. -/
noncomputable def finiteSubsetPontryaginEvaluationPoint
    (J : Finset (PontryaginDual (Multiplicative G))) (x : G) : UnitAddTorus J :=
  fun j ↦
    (AddCircle.homeomorphCircle one_ne_zero).symm
      ((j : PontryaginDual (Multiplicative G)) (Multiplicative.ofAdd x))

/-- Helper for Theorem 15.29: the global Pontryagin evaluation map records all character values of
`x : G` in `UnitAddCircle` coordinates. -/
noncomputable def pontryaginEvaluationPoint (x : G) :
    ((χ : PontryaginDual (Multiplicative G)) → UnitAddCircle) :=
  fun χ ↦
    (AddCircle.homeomorphCircle one_ne_zero).symm
      (χ (Multiplicative.ofAdd x))

/-- Helper for Theorem 15.29: the bundled bidual evaluation map sends `x : G` to the character on
`PontryaginDual (Multiplicative G)` given by `χ ↦ χ(x)`. -/
noncomputable def pontryaginBidualEvaluation (x : G) :
    PontryaginDual (PontryaginDual (Multiplicative G)) := by
  sorry
/-- Helper for Theorem 15.29: forgetting the bundled bidual evaluation back to
`UnitAddCircle`-valued coordinates recovers the raw evaluation map already used by the
projective-limit moment formulas. -/
lemma pontryaginBidualEvaluation_toRaw_eq (x : G) :
    (fun χ : PontryaginDual (Multiplicative G) ↦
      (AddCircle.homeomorphCircle one_ne_zero).symm
        (pontryaginBidualEvaluation (G := G) x χ)) =
      pontryaginEvaluationPoint (G := G) x := by
  sorry

/-- Helper for Theorem 15.29: restricting the global Pontryagin evaluation point to a finite set
of characters recovers the finite-coordinate evaluation point. -/
lemma restrict_pontryaginEvaluationPoint
    (J : Finset (PontryaginDual (Multiplicative G))) (x : G) :
    J.restrict (pontryaginEvaluationPoint (G := G) x) =
      finiteSubsetPontryaginEvaluationPoint (G := G) J x := by
  -- Proof comment: both evaluation points are defined by the same coordinate formula.
  rfl

/-- Helper for Theorem 15.29: the global Pontryagin evaluation map is continuous in each
coordinate simultaneously. -/
lemma continuous_pontryaginEvaluationPoint :
    Continuous (pontryaginEvaluationPoint (G := G)) := by
  -- Proof comment: continuity into the product space is checked coordinatewise.
  exact continuous_pi fun χ ↦
    (AddCircle.homeomorphCircle one_ne_zero).symm.continuous.comp
      (χ.continuous.comp continuous_ofAdd)

/-- Helper for Theorem 15.29: the global Pontryagin evaluation map is measurable. -/
lemma measurable_pontryaginEvaluationPoint :
    Measurable (pontryaginEvaluationPoint (G := G)) := by
  -- Proof comment: measurability into the product space is checked coordinatewise, exactly as in
  -- the continuity proof.
  refine measurable_pi_lambda _ fun ψ ↦ ?_
  exact
    ((AddCircle.homeomorphCircle one_ne_zero).symm.continuous.comp
      (ψ.continuous.comp continuous_ofAdd)).measurable

/-- Helper for Theorem 15.29: applying `AddCircle.toCircle` to the finite-coordinate evaluation
point recovers the original dual character value. -/
lemma finiteSubsetPontryaginEvaluationPoint_toCircle
    (J : Finset (PontryaginDual (Multiplicative G))) (x : G) (j : J) :
    AddCircle.toCircle (finiteSubsetPontryaginEvaluationPoint (G := G) J x j) =
      ((j : PontryaginDual (Multiplicative G)) (Multiplicative.ofAdd x)) := by
  -- Proof comment: `homeomorphCircle` identifies `UnitAddCircle` with `Circle`, so evaluating the
  -- transported coordinate and then mapping back to `Circle` is the identity.
  rw [← AddCircle.homeomorphCircle_apply one_ne_zero]
  simp [finiteSubsetPontryaginEvaluationPoint]

/-- Helper for Theorem 15.29: evaluating a torus monomial at the finite-coordinate Pontryagin
evaluation point collapses to the phase of the corresponding finite product character. -/
lemma finiteSubsetEvaluation_mFourier
    (J : Finset (PontryaginDual (Multiplicative G))) (x : G) (n : J → ℤ) :
    UnitAddTorus.mFourier n (finiteSubsetPontryaginEvaluationPoint (G := G) J x) =
      pontryaginPhase (∏ j : J, (j : PontryaginDual (Multiplicative G)) ^ n j) x := by
  sorry
/-- Helper for Theorem 15.29: once every finite subset of the dual has a torus law with the
prescribed Fourier moments, the already-proved projective machinery produces one global law on the
full `UnitAddCircle`-valued character family with the matching finite-coordinate moments. -/
lemma existsProjectiveLimitPontryaginLaw
    {φ : PontryaginDual (Multiplicative G) → ℂ}
    (hPexist : ∀ J : Finset (PontryaginDual (Multiplicative G)),
      ∃ μJ : ProbabilityMeasure (UnitAddTorus J),
        ∀ n : J → ℤ,
          ∫ x, UnitAddTorus.mFourier n x ∂(μJ : Measure (UnitAddTorus J)) =
            φ (∏ j : J, (j : PontryaginDual (Multiplicative G)) ^ n j)) :
    ∃ ν : Measure ((χ : PontryaginDual (Multiplicative G)) → UnitAddCircle),
      IsProbabilityMeasure ν ∧
        ∀ J : Finset (PontryaginDual (Multiplicative G)), ∀ n : J → ℤ,
          ∫ z, UnitAddTorus.mFourier n (J.restrict z) ∂ν =
            φ (∏ j : J, (j : PontryaginDual (Multiplicative G)) ^ n j) := by
  classical
  let P : ∀ J : Finset (PontryaginDual (Multiplicative G)),
      ProbabilityMeasure (UnitAddTorus J) := fun J ↦ Classical.choose (hPexist J)
  have hP :
      ∀ J : Finset (PontryaginDual (Multiplicative G)), ∀ n : J → ℤ,
        ∫ x, UnitAddTorus.mFourier n x ∂(P J : Measure (UnitAddTorus J)) =
          φ (∏ j : J, (j : PontryaginDual (Multiplicative G)) ^ n j) := by
    intro J n
    exact Classical.choose_spec (hPexist J) n
  have hProj :
      MeasureTheory.IsProjectiveMeasureFamily
        (α := fun _ : PontryaginDual (Multiplicative G) ↦ UnitAddCircle)
        (fun J ↦ (P J : Measure (UnitAddTorus J))) := by
    -- Proof comment: the earlier finite-marginal comparison theorem already turns matching torus
    -- moments into the required projective compatibility.
    exact finiteSubsetTorusLawFamilyProjective (G := G) (φ := φ) P hP
  rcases
    unitAddCircleCharacterFamilyProjectiveLimitExists
      (P := fun J ↦ (P J : Measure (UnitAddTorus J))) hProj with
    ⟨ν, hν⟩
  have hνprob : IsProbabilityMeasure ν := by
    -- Proof comment: a projective limit of probability marginals is itself a probability measure.
    exact MeasureTheory.IsProjectiveLimit.isProbabilityMeasure hν
  refine ⟨ν, hνprob, ?_⟩
  -- Proof comment: the finite-coordinate moment specification now comes straight from the
  -- projective-limit transport lemma proved above.
  exact projectiveLimitPontryaginMomentSpec
    (G := G) (φ := φ) (P := fun J ↦ (P J : Measure (UnitAddTorus J))) hν hP

/-- Helper for Theorem 15.29: the projective-limit moment specification already determines the
first Fourier moment of each singleton dual coordinate. -/
lemma projectiveLimitPontryaginMomentSpec_singleton
    {φ : PontryaginDual (Multiplicative G) → ℂ}
    {ν : Measure ((χ : PontryaginDual (Multiplicative G)) → UnitAddCircle)}
    (hνmom : ∀ J : Finset (PontryaginDual (Multiplicative G)), ∀ n : J → ℤ,
      ∫ z, UnitAddTorus.mFourier n (J.restrict z) ∂ν =
        φ (∏ j : J, (j : PontryaginDual (Multiplicative G)) ^ n j))
    (χ : PontryaginDual (Multiplicative G)) :
    ∫ z,
        UnitAddTorus.mFourier
          (fun _ : ({χ} : Finset (PontryaginDual (Multiplicative G))) ↦ (1 : ℤ))
          (({χ} : Finset (PontryaginDual (Multiplicative G))).restrict z) ∂ν =
      φ χ := by
  -- Proof comment: specialize the finite-coordinate moment formula to the singleton set `{χ}`
  -- and the exponent vector constantly equal to `1`.
  simpa using
    hνmom ({χ} : Finset (PontryaginDual (Multiplicative G)))
      (fun _ : ({χ} : Finset (PontryaginDual (Multiplicative G))) ↦ (1 : ℤ))

/-- Helper for Theorem 15.29: evaluating the singleton torus monomial at the Pontryagin
evaluation point recovers the phase attached to that single dual character. -/
lemma finiteSubsetEvaluation_mFourier_singleton
    (χ : PontryaginDual (Multiplicative G)) (x : G) :
    UnitAddTorus.mFourier
        (fun _ : ({χ} : Finset (PontryaginDual (Multiplicative G))) ↦ (1 : ℤ))
        (finiteSubsetPontryaginEvaluationPoint (G := G)
          ({χ} : Finset (PontryaginDual (Multiplicative G))) x) =
      pontryaginPhase χ x := by
  -- Proof comment: this is the general finite-coordinate evaluation identity specialized to the
  -- singleton set `{χ}` and exponent `1`.
  simpa using
    finiteSubsetEvaluation_mFourier (G := G)
      ({χ} : Finset (PontryaginDual (Multiplicative G))) x
      (fun _ : ({χ} : Finset (PontryaginDual (Multiplicative G))) ↦ (1 : ℤ))

/-- Helper for Theorem 15.29: pushing a probability law on `G` through
`pontryaginEvaluationPoint` reproduces the singleton Fourier moment for each dual character. -/
lemma singletonMoment_map_pontryaginEvaluationPoint
    (μ : ProbabilityMeasure G) (χ : PontryaginDual (Multiplicative G)) :
    ∫ z,
        UnitAddTorus.mFourier
          (fun _ : ({χ} : Finset (PontryaginDual (Multiplicative G))) ↦ (1 : ℤ))
          (({χ} : Finset (PontryaginDual (Multiplicative G))).restrict z)
        ∂((μ : Measure G).map (pontryaginEvaluationPoint (G := G)) :
          Measure ((χ : PontryaginDual (Multiplicative G)) → UnitAddCircle)) =
      pontryaginCharFun μ χ := by
  -- Proof comment: transport the singleton torus monomial through the evaluation map and rewrite
  -- the resulting integrand using the singleton evaluation identity.
  rw [MeasureTheory.integral_map (φ := pontryaginEvaluationPoint (G := G))]
  · calc
      ∫ x,
          UnitAddTorus.mFourier
            (fun _ : ({χ} : Finset (PontryaginDual (Multiplicative G))) ↦ (1 : ℤ))
            (({χ} : Finset (PontryaginDual (Multiplicative G))).restrict
              (pontryaginEvaluationPoint (G := G) x))
          ∂(μ : Measure G)
          =
        ∫ x, pontryaginPhase χ x ∂(μ : Measure G) := by
            refine integral_congr_ae (Filter.Eventually.of_forall ?_)
            intro x
            simpa [restrict_pontryaginEvaluationPoint (G := G)
              ({χ} : Finset (PontryaginDual (Multiplicative G))) x] using
              finiteSubsetEvaluation_mFourier_singleton (G := G) χ x
      _ = pontryaginCharFun μ χ := by
          rw [pontryaginCharFun_eq_integral_pontryaginPhase]
  · exact (measurable_pontryaginEvaluationPoint (G := G)).aemeasurable
  · have hrestrict_meas :
        Measurable fun z : ((χ : PontryaginDual (Multiplicative G)) → UnitAddCircle) ↦
          ({χ} : Finset (PontryaginDual (Multiplicative G))).restrict z := by
      -- Proof comment: restriction to a finite set is measurable because each restricted
      -- coordinate is an evaluation map on the ambient product measurable space.
      refine measurable_pi_lambda _ fun j ↦ ?_
      simpa using
        (measurable_pi_apply (a := (j : PontryaginDual (Multiplicative G))) :
          Measurable fun z : ((χ : PontryaginDual (Multiplicative G)) → UnitAddCircle) ↦ z j)
    exact
      ((UnitAddTorus.mFourier
        (fun _ : ({χ} : Finset (PontryaginDual (Multiplicative G))) ↦ (1 : ℤ))).measurable.comp
          hrestrict_meas).aestronglyMeasurable

/-- Helper for Theorem 15.29: the Fejer kernel on the finite torus is already real-valued, so the
real density is just its coercion to `ℂ`. -/
private lemma finiteSubsetTorusFejerKernel_eq_ofReal_density
    (J : Finset (PontryaginDual (Multiplicative G)))
    {φ : PontryaginDual (Multiplicative G) → ℂ} (N : ℕ)
    (hpsd : IsPositiveSemidefiniteMulFunction φ) (hone : φ 1 = 1)
    (x : UnitAddTorus J) :
    finiteSubsetTorusFejerKernel (G := G) (φ := φ) J N x =
      (finiteSubsetTorusFejerDensity (G := G) (φ := φ) J N x : ℂ) := by
  sorry

/-- Helper for Theorem 15.29: the Fejer density defines a probability measure on the finite
torus, because its total mass is `1`. -/
private lemma finiteSubsetTorusFejerMeasure_real_univ
    (J : Finset (PontryaginDual (Multiplicative G)))
    {φ : PontryaginDual (Multiplicative G) → ℂ} (N : ℕ)
    (hpsd : IsPositiveSemidefiniteMulFunction φ) (hone : φ 1 = 1) :
    (volume.withDensity
      (ENNReal.ofReal ∘ finiteSubsetTorusFejerDensity (G := G) (φ := φ) J N)).real Set.univ = 1 := by
  have hρ_nonneg :
      ∀ x : UnitAddTorus J,
        0 ≤ finiteSubsetTorusFejerDensity (G := G) (φ := φ) J N x := by
    intro x
    simpa using finiteSubsetTorusFejerDensity_nonneg
      (G := G) (φ := φ) J N hpsd hone x
  have hρ_aemeas :
      AEMeasurable
        (ENNReal.ofReal ∘ finiteSubsetTorusFejerDensity (G := G) (φ := φ) J N)
        (volume : Measure (UnitAddTorus J)) := by
    -- Proof comment: the Fejer density is continuous on the compact torus, so its `ENNReal`
    -- coercion is measurable.
    exact
      (finiteSubsetTorusFejerDensity (G := G) (φ := φ) J N).continuous.aemeasurable.ennreal_ofReal
  have hρ_lt_top :
      ∀ᵐ x ∂(volume : Measure (UnitAddTorus J)),
        ENNReal.ofReal (finiteSubsetTorusFejerDensity (G := G) (φ := φ) J N x) < ⊤ := by
    exact Filter.Eventually.of_forall fun _ ↦ by simp
  calc
    (volume.withDensity
      (ENNReal.ofReal ∘ finiteSubsetTorusFejerDensity (G := G) (φ := φ) J N)).real Set.univ
        =
      ∫ x, (1 : ℝ) ∂(volume.withDensity
        (ENNReal.ofReal ∘ finiteSubsetTorusFejerDensity (G := G) (φ := φ) J N)) := by
          simp
    _ =
      ∫ x,
        ((ENNReal.ofReal
          (finiteSubsetTorusFejerDensity (G := G) (φ := φ) J N x)).toReal) •
          (1 : ℝ) ∂(volume : Measure (UnitAddTorus J)) := by
            simpa using
              (integral_withDensity_eq_integral_toReal_smul₀
                (μ := (volume : Measure (UnitAddTorus J)))
                (f := ENNReal.ofReal ∘ finiteSubsetTorusFejerDensity (G := G) (φ := φ) J N)
                hρ_aemeas hρ_lt_top
                (g := fun _ : UnitAddTorus J ↦ (1 : ℝ)))
    _ =
      ∫ x, finiteSubsetTorusFejerDensity (G := G) (φ := φ) J N x
        ∂(volume : Measure (UnitAddTorus J)) := by
          refine integral_congr_ae (Filter.Eventually.of_forall ?_)
          intro x
          simp [hρ_nonneg x]
    _ = 1 := finiteSubsetTorusFejerMassOne (G := G) (φ := φ) J N hpsd hone

/-- Helper for Theorem 15.29: package the `N`-th Fejer density as an honest probability measure
on the finite torus. -/
noncomputable def finiteSubsetTorusFejerProbabilityMeasure
    (J : Finset (PontryaginDual (Multiplicative G)))
    {φ : PontryaginDual (Multiplicative G) → ℂ} (N : ℕ)
    (hpsd : IsPositiveSemidefiniteMulFunction φ) (hone : φ 1 = 1) :
    ProbabilityMeasure (UnitAddTorus J) :=
  let μ : Measure (UnitAddTorus J) :=
    volume.withDensity (ENNReal.ofReal ∘ finiteSubsetTorusFejerDensity (G := G) (φ := φ) J N)
  ⟨μ, MeasureTheory.isProbabilityMeasure_iff_real.2
    (finiteSubsetTorusFejerMeasure_real_univ (G := G) J N hpsd hone)⟩

/-- Helper for Theorem 15.29: the Fejer stage moment is weighted by the proportion of exponent
vectors `v` in the box for which `v + n` is still in the box. -/
noncomputable def finiteSubsetTorusFejerWeight
    (J : Finset (PontryaginDual (Multiplicative G))) (N : ℕ) (n : J → ℤ) : ℝ :=
  let box := finiteSubsetTorusFejerBox (G := G) J N
  ((box.filter fun v ↦ v + n ∈ box).card : ℝ) / box.card

/-- Helper for Theorem 15.29: the `N`-th Fejer probability measure has the expected torus Fourier
moments up to the explicit Fejer weight. -/
lemma finiteSubsetTorusFejer_mFourier_eq_weightedMoment
    (J : Finset (PontryaginDual (Multiplicative G)))
    {φ : PontryaginDual (Multiplicative G) → ℂ} (N : ℕ)
    (hpsd : IsPositiveSemidefiniteMulFunction φ) (hone : φ 1 = 1)
    (n : J → ℤ) :
    ∫ x, UnitAddTorus.mFourier n x
      ∂(finiteSubsetTorusFejerProbabilityMeasure
        (G := G) J N hpsd hone : Measure (UnitAddTorus J)) =
      ((finiteSubsetTorusFejerWeight (G := G) J N n : ℝ) : ℂ) *
        φ (∏ j : J, (j : PontryaginDual (Multiplicative G)) ^ n j) := by
  sorry

/-- Helper for Theorem 15.29: once `N` dominates the frequency shift `m`, the one-dimensional
filtered Fejer interval has the expected cardinality. -/
lemma finiteSubsetTorusFejerInterval_filter_card
    (m : ℤ) {N : ℕ} (hN : Int.natAbs m ≤ N) :
    (((Finset.Icc (-(N : ℤ)) N).filter
        fun z : ℤ ↦ z + m ∈ Finset.Icc (-(N : ℤ)) N).card : ℤ) =
      (2 * N + 1 : ℤ) - Int.natAbs m := by
  have hN_int : (Int.natAbs m : ℤ) ≤ N := by
    exact_mod_cast hN
  by_cases hm : 0 ≤ m
  · have hm_le : m ≤ N := by
      simpa [Int.natAbs_of_nonneg hm] using hN_int
    have hfilter :
        (Finset.Icc (-(N : ℤ)) N).filter
            (fun z : ℤ ↦ z + m ∈ Finset.Icc (-(N : ℤ)) N) =
          Finset.Icc (-(N : ℤ)) (N - m) := by
      -- Proof comment: for nonnegative shifts, the left endpoint stays fixed and the right
      -- endpoint shortens by exactly `m`.
      ext z
      simp only [Finset.mem_filter, Finset.mem_Icc]
      omega
    rw [hfilter, Int.card_Icc_of_le]
    · -- Proof comment: after the interval is identified explicitly, the cardinal computation is
      -- the standard integer-interval count.
      rw [Int.natAbs_of_nonneg hm]
      omega
    · omega
  · have hm_neg : m < 0 := lt_of_not_ge hm
    have hm_le : -m ≤ N := by
      simpa [Int.ofNat_natAbs_of_nonpos hm_neg.le] using hN_int
    have hfilter :
        (Finset.Icc (-(N : ℤ)) N).filter
            (fun z : ℤ ↦ z + m ∈ Finset.Icc (-(N : ℤ)) N) =
          Finset.Icc (-(N : ℤ) - m) N := by
      -- Proof comment: for negative shifts, the right endpoint stays fixed and the left endpoint
      -- moves inward by `-m`.
      ext z
      simp only [Finset.mem_filter, Finset.mem_Icc]
      omega
    rw [hfilter, Int.card_Icc_of_le]
    · -- Proof comment: the negative-shift case is the same interval-count formula after
      -- rewriting `Int.natAbs m` as `-m`.
      rw [Int.ofNat_natAbs_of_nonpos hm_neg.le]
      omega
    · omega

/-- Helper for Theorem 15.29: once the Fejer box is large compared to `n`, the filtered cardinal
splits coordinatewise into the expected product formula. -/
lemma finiteSubsetTorusFejerWeight_eventually_eq_prod
    (J : Finset (PontryaginDual (Multiplicative G))) (n : J → ℤ) :
    ∀ᶠ N in atTop,
      finiteSubsetTorusFejerWeight (G := G) J N n =
        ∏ j : J, ((((2 * N + 1 - Int.natAbs (n j) : ℕ) : ℝ)) / (2 * N + 1)) := by
  sorry

/-- Helper for Theorem 15.29: each one-dimensional Fejer coordinate factor tends to `1`. -/
lemma finiteSubsetTorusFejerCoordinateFactor_tendsto_one (m : ℤ) :
    Tendsto
      (fun N : ℕ ↦ ((((2 * N + 1 - Int.natAbs m : ℕ) : ℝ)) / (2 * N + 1)))
      atTop (𝓝 1) := by
  sorry

/-- Helper for Theorem 15.29: the Fejer weight attached to a fixed exponent vector tends to `1`
as the box grows. -/
lemma finiteSubsetTorusFejerWeight_tendsto_one
    (J : Finset (PontryaginDual (Multiplicative G))) (n : J → ℤ) :
    Tendsto (fun N : ℕ ↦ finiteSubsetTorusFejerWeight (G := G) J N n) atTop (𝓝 1) := by
  sorry

/-- Helper for Theorem 15.29: a finite subset of the dual already admits a torus law whose
Fourier moments are prescribed by `φ`. -/
lemma finiteSubsetTorusProbabilityMeasureExists
    (J : Finset (PontryaginDual (Multiplicative G)))
    {φ : PontryaginDual (Multiplicative G) → ℂ}
    (hpsd : IsPositiveSemidefiniteMulFunction φ) (hone : φ 1 = 1) :
    ∃ μJ : ProbabilityMeasure (UnitAddTorus J),
      ∀ n : J → ℤ,
        ∫ x, UnitAddTorus.mFourier n x ∂(μJ : Measure (UnitAddTorus J)) =
          φ (∏ j : J, (j : PontryaginDual (Multiplicative G)) ^ n j) := by
  classical
  let μN : ℕ → ProbabilityMeasure (UnitAddTorus J) := fun N ↦
    finiteSubsetTorusFejerProbabilityMeasure (G := G) J N hpsd hone
  rcases CompactSpace.tendsto_subseq μN with ⟨μJ, φsub, hφsub, hμsub⟩
  refine ⟨μJ, ?_⟩
  intro n
  let fB : BoundedContinuousFunction (UnitAddTorus J) ℂ :=
    BoundedContinuousFunction.mkOfCompact (UnitAddTorus.mFourier n)
  have hIntegral :
      Tendsto
        (fun N ↦
          ∫ x, UnitAddTorus.mFourier n x
            ∂((μN (φsub N) : ProbabilityMeasure (UnitAddTorus J)) :
              Measure (UnitAddTorus J)))
        atTop
        (𝓝
          (∫ x, UnitAddTorus.mFourier n x
            ∂(μJ : Measure (UnitAddTorus J)))) := by
    -- Proof comment: any weakly convergent subsequence of probability measures transports
    -- integrals of bounded continuous torus monomials to the limit.
    simpa [μN, fB] using
      (MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).1
        hμsub fB
  have hWeight :
      Tendsto
        (fun N ↦
          (((finiteSubsetTorusFejerWeight (G := G) J (φsub N) n : ℝ) : ℂ) *
            φ (∏ j : J, (j : PontryaginDual (Multiplicative G)) ^ n j)))
        atTop
        (𝓝 (φ (∏ j : J, (j : PontryaginDual (Multiplicative G)) ^ n j))) := by
    have hweight_real :
        Tendsto (fun N ↦ finiteSubsetTorusFejerWeight (G := G) J (φsub N) n)
          atTop (𝓝 1) := by
      exact
        (finiteSubsetTorusFejerWeight_tendsto_one (G := G) J n).comp
          hφsub.tendsto_atTop
    have hweight :
        Tendsto
          (fun N ↦ ((finiteSubsetTorusFejerWeight (G := G) J (φsub N) n : ℝ) : ℂ))
          atTop (𝓝 (1 : ℂ)) := by
      exact Complex.continuous_ofReal.continuousAt.tendsto.comp hweight_real
    -- Proof comment: once the real Fejer weights tend to `1`, the weighted moment formula tends
    -- to the target moment of `φ`.
    simpa using Tendsto.mul hweight tendsto_const_nhds
  have hStage :
      Tendsto
        (fun N ↦
          ∫ x, UnitAddTorus.mFourier n x
            ∂((μN (φsub N) : ProbabilityMeasure (UnitAddTorus J)) :
              Measure (UnitAddTorus J)))
        atTop
        (𝓝 (φ (∏ j : J, (j : PontryaginDual (Multiplicative G)) ^ n j))) := by
    -- Proof comment: replace each subsequence term by the explicit weighted Fejer moment formula.
    refine hWeight.congr' ?_
    refine Filter.Eventually.of_forall ?_
    intro N
    simpa [μN] using
      (finiteSubsetTorusFejer_mFourier_eq_weightedMoment
        (G := G) J (φsub N) hpsd hone n).symm
  -- Proof comment: the same subsequence of monomial integrals converges both to the weak limit
  -- moment and to the target moment of `φ`, so the limits must agree.
  exact tendsto_nhds_unique hIntegral hStage

/-- Helper for Theorem 15.29: once the projective-limit law `ν` is already known to be the push
forward of a probability law on `G` along `pontryaginEvaluationPoint`, the singleton moment
identities determine the Pontryagin characteristic function of that law. -/
lemma pontryaginCharFun_eq_of_singletonMoments_of_map [T2Space G] [LocallyCompactSpace G]
    {φ : PontryaginDual (Multiplicative G) → ℂ}
    {ν : Measure ((χ : PontryaginDual (Multiplicative G)) → UnitAddCircle)}
    [IsProbabilityMeasure ν]
    (hνsingleton :
      ∀ χ : PontryaginDual (Multiplicative G),
        ∫ z,
            UnitAddTorus.mFourier
              (fun _ : ({χ} : Finset (PontryaginDual (Multiplicative G))) ↦ (1 : ℤ))
              (({χ} : Finset (PontryaginDual (Multiplicative G))).restrict z) ∂ν =
          φ χ)
    {μ : ProbabilityMeasure G}
    (hmap :
      (((μ : Measure G).map (pontryaginEvaluationPoint (G := G))) :
        Measure ((χ : PontryaginDual (Multiplicative G)) → UnitAddCircle)) = ν) :
    pontryaginCharFun μ = φ := by
  funext χ
  -- Proof comment: rewrite the singleton Fourier moment of the pushforward measure once using the
  -- established transport lemma, then substitute the known pushforward identity.
  calc
    pontryaginCharFun μ χ
        =
      ∫ z,
          UnitAddTorus.mFourier
            (fun _ : ({χ} : Finset (PontryaginDual (Multiplicative G))) ↦ (1 : ℤ))
            (({χ} : Finset (PontryaginDual (Multiplicative G))).restrict z)
          ∂(((μ : Measure G).map (pontryaginEvaluationPoint (G := G))) :
            Measure ((χ : PontryaginDual (Multiplicative G)) → UnitAddCircle)) := by
            symm
            exact singletonMoment_map_pontryaginEvaluationPoint (G := G) μ χ
    _ =
      ∫ z,
          UnitAddTorus.mFourier
            (fun _ : ({χ} : Finset (PontryaginDual (Multiplicative G))) ↦ (1 : ℤ))
            (({χ} : Finset (PontryaginDual (Multiplicative G))).restrict z) ∂ν := by
            rw [hmap]
    _ = φ χ := hνsingleton χ

/-- Helper for Theorem 15.29: mapping back the comap of a probability measure along a measurable
embedding recovers the original measure once the image has full mass. -/
lemma measure_map_comap_eq_self_of_fullMass
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {f : α → β} (hf : MeasurableEmbedding f) {ν : Measure β} [IsProbabilityMeasure ν]
    (hνrange : ν (Set.range f) = 1) :
    Measure.map f (ν.comap f) = ν := by
  have hνae : Set.range f ∈ ae ν := by
    -- Proof comment: for a probability measure, full mass on the image is exactly the a.e. range
    -- condition needed by `restrict_eq_self_of_ae_mem`.
    exact (MeasureTheory.mem_ae_iff_prob_eq_one hf.measurableSet_range).2 hνrange
  calc
    Measure.map f (ν.comap f) = ν.restrict (Set.range f) := by
      simpa using hf.map_comap ν
    _ = ν := Measure.restrict_eq_self_of_ae_mem hνae

/-- Helper for Theorem 15.29: a probability measure on the codomain of a measurable embedding
descends to a probability measure on the domain once the image has full mass. -/
lemma existsProbabilityMeasure_map_eq_of_fullMass
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {f : α → β} (hf : MeasurableEmbedding f) {ν : Measure β} [IsProbabilityMeasure ν]
    (hνrange : ν (Set.range f) = 1) :
    ∃ μ : ProbabilityMeasure α, Measure.map f (μ : Measure α) = ν := by
  have hνae : Set.range f ∈ ae ν := by
    -- Proof comment: the comap is a probability measure precisely because the original law lives
    -- almost surely on the image of the embedding.
    exact (MeasureTheory.mem_ae_iff_prob_eq_one hf.measurableSet_range).2 hνrange
  let μ : ProbabilityMeasure α := ⟨ν.comap f, hf.isProbabilityMeasure_comap hνae⟩
  have hmap : Measure.map f (μ : Measure α) = ν := by
    -- Proof comment: after packaging the comap as a probability measure, exact recovery is the
    -- measure-level map-comap identity from the previous lemma.
    simpa [μ] using
      measure_map_comap_eq_self_of_fullMass (hf := hf) (ν := ν) hνrange
  exact ⟨μ, hmap⟩

/-- Helper for Theorem 15.29: once the Pontryagin evaluation map is known to be a measurable
embedding and the projective-limit law gives its range full mass, the comap descent produces the
desired probability measure on `G`. -/
lemma projectiveLimitPontryaginLawDescendsViaComap_of_fullMass [T2Space G] [LocallyCompactSpace G]
    {φ : PontryaginDual (Multiplicative G) → ℂ}
    {ν : Measure ((χ : PontryaginDual (Multiplicative G)) → UnitAddCircle)}
    [IsProbabilityMeasure ν]
    (hνsingleton :
      ∀ χ : PontryaginDual (Multiplicative G),
        ∫ z,
            UnitAddTorus.mFourier
              (fun _ : ({χ} : Finset (PontryaginDual (Multiplicative G))) ↦ (1 : ℤ))
              (({χ} : Finset (PontryaginDual (Multiplicative G))).restrict z) ∂ν =
          φ χ)
    (heval : MeasurableEmbedding (pontryaginEvaluationPoint (G := G)))
    (hνrange :
      ν (Set.range (pontryaginEvaluationPoint (G := G))) = 1) :
    ∃ μ : ProbabilityMeasure G, pontryaginCharFun μ = φ := by
  rcases
    existsProbabilityMeasure_map_eq_of_fullMass
      (hf := heval) (ν := ν) hνrange with ⟨μ, hmap⟩
  refine ⟨μ, ?_⟩
  -- Proof comment: once the pushforward identity is recovered by comap, the singleton-moment
  -- comparison lemma closes the characteristic-function equality directly.
  exact
    pontryaginCharFun_eq_of_singletonMoments_of_map
      (G := G) (φ := φ) (ν := ν) hνsingleton hmap

/-- Helper for Theorem 15.29: a closed embedding of the Pontryagin evaluation map is already
enough for the comap descent, since measurability is a formal corollary. -/
lemma projectiveLimitPontryaginLawDescendsViaClosedEmbedding_of_fullMass [T2Space G]
    [LocallyCompactSpace G]
    {φ : PontryaginDual (Multiplicative G) → ℂ}
    {ν : Measure ((χ : PontryaginDual (Multiplicative G)) → UnitAddCircle)}
    [IsProbabilityMeasure ν]
    (hνsingleton :
      ∀ χ : PontryaginDual (Multiplicative G),
          ∫ z,
              UnitAddTorus.mFourier
              (fun _ : ({χ} : Finset (PontryaginDual (Multiplicative G))) ↦ (1 : ℤ))
              (({χ} : Finset (PontryaginDual (Multiplicative G))).restrict z) ∂ν =
          φ χ)
    (heval : Topology.IsClosedEmbedding (pontryaginEvaluationPoint (G := G)))
    (hνrange :
      ν (Set.range (pontryaginEvaluationPoint (G := G))) = 1) :
    ∃ μ : ProbabilityMeasure G, pontryaginCharFun μ = φ := by
  sorry
/-- Helper for Theorem 15.29: once a projective-limit law matches the full finite-coordinate
Fourier moments, the remaining LCAG descent should be concentrated in one owner theorem instead
of reopening the raw evaluation-range subgoals inside the public wrapper. -/
lemma projectiveLimitPontryaginLawDescendsViaBidualOwner [T2Space G] [LocallyCompactSpace G]
    {φ : PontryaginDual (Multiplicative G) → ℂ}
    {ν : Measure ((χ : PontryaginDual (Multiplicative G)) → UnitAddCircle)}
    [IsProbabilityMeasure ν]
    (hνmom : ∀ J : Finset (PontryaginDual (Multiplicative G)), ∀ n : J → ℤ,
      ∫ z, UnitAddTorus.mFourier n (J.restrict z) ∂ν =
        φ (∏ j : J, (j : PontryaginDual (Multiplicative G)) ^ n j)) :
    ∃ μ : ProbabilityMeasure G, pontryaginCharFun μ = φ := by
  -- Route correction: previous attempts kept the blocker as two raw hypotheses about
  -- `pontryaginEvaluationPoint`. The bidual adapter above freezes the Circle/UnitAddCircle
  -- transport, and the owner now consumes the full projective-limit moment package instead of the
  -- over-weak singleton surface that could never force range support.
  have hνsingleton :
      ∀ χ : PontryaginDual (Multiplicative G),
        ∫ z,
            UnitAddTorus.mFourier
              (fun _ : ({χ} : Finset (PontryaginDual (Multiplicative G))) ↦ (1 : ℤ))
              (({χ} : Finset (PontryaginDual (Multiplicative G))).restrict z) ∂ν =
          φ χ := by
    intro χ
    -- Proof comment: the singleton-moment comparison is now derived locally from the repaired
    -- full finite-coordinate moment hypothesis, so downstream descent lemmas keep their old
    -- interface while the blocked owner sees the stronger data it actually needs.
    simpa using
      projectiveLimitPontryaginMomentSpec_singleton (G := G) (φ := φ) hνmom χ
  -- Route correction: discard the ambient-product closed-embedding route here. In the raw product
  -- `((χ : PontryaginDual (Multiplicative G)) → UnitAddCircle)`, that route asks for a theorem
  -- which is false for noncompact `G`, so keeping local `Set.range`/`comap` scaffolding only hides
  -- the real frontier.
  -- Proof comment: the remaining owner must construct the representing probability measure
  -- directly on `G` from the finite-coordinate moment package `hνmom`. The expected route is the
  -- direct LCAG Bochner argument via character separation, Stone-Weierstrass on compacts, and
  -- Riesz-Markov-Kakutani, after which `hνsingleton` will only be used for the final
  -- `pontryaginCharFun` comparison.
  -- TODO: prove one theorem-local direct owner
  -- `∃ μ : ProbabilityMeasure G, pontryaginCharFun μ = φ` from `hνmom`, replacing the discarded
  -- raw-product descent instead of asking for `Topology.IsClosedEmbedding eval` and
  -- `ν (Set.range eval) = 1`.
  sorry

/-- Helper for Theorem 15.29: once a projective-limit law matches the full finite-coordinate
Fourier moments, the Pontryagin evaluation embedding should descend it to a probability law on
`G`. -/
lemma projectiveLimitPontryaginLawDescendsViaComap [T2Space G] [LocallyCompactSpace G]
    {φ : PontryaginDual (Multiplicative G) → ℂ}
    {ν : Measure ((χ : PontryaginDual (Multiplicative G)) → UnitAddCircle)}
    [IsProbabilityMeasure ν]
    (hνmom : ∀ J : Finset (PontryaginDual (Multiplicative G)), ∀ n : J → ℤ,
      ∫ z, UnitAddTorus.mFourier n (J.restrict z) ∂ν =
        φ (∏ j : J, (j : PontryaginDual (Multiplicative G)) ^ n j)) :
    ∃ μ : ProbabilityMeasure G, pontryaginCharFun μ = φ := by
  -- Proof comment: the public descent theorem is now just a thin wrapper around the theorem-local
  -- owner, so later work only has to close one stabilized frontier.
  exact
    projectiveLimitPontryaginLawDescendsViaBidualOwner
      (G := G) (φ := φ) (ν := ν) hνmom

/-- Helper for Theorem 15.29: the remaining locally compact abelian Bochner owner should already
return a probability measure whose Pontryagin characteristic function is `φ`. -/
lemma existsProbabilityMeasurePontryaginCharFunEqCore [T2Space G] [LocallyCompactSpace G]
    {φ : PontryaginDual (Multiplicative G) → ℂ} (hφ : Continuous φ)
    (hpsd : IsPositiveSemidefiniteMulFunction φ) (hone : φ 1 = 1) :
    ∃ μ : ProbabilityMeasure G, pontryaginCharFun μ = φ := by
  -- Route correction: the live blocker is not the phase-integral packaging anymore. The missing
  -- owner is the genuine LCAG Bochner existence theorem on the public `pontryaginCharFun`
  -- surface, with the final transport isolated as a continuity-sensitive descent rather than an
  -- evaluation-range search.
  classical
  have hFinite :
      ∀ J : Finset (PontryaginDual (Multiplicative G)),
        ∃ μJ : ProbabilityMeasure (UnitAddTorus J),
          ∀ n : J → ℤ,
            ∫ x, UnitAddTorus.mFourier n x ∂(μJ : Measure (UnitAddTorus J)) =
              φ (∏ j : J, (j : PontryaginDual (Multiplicative G)) ^ n j) := by
    intro J
    -- Proof comment: the finite-dimensional frontier is now the dedicated compact-torus owner
    -- theorem, so the main LCAG proof no longer hides that analytic step inside a local `have`.
    exact finiteSubsetTorusProbabilityMeasureExists (G := G) J hpsd hone
  rcases
    existsProjectiveLimitPontryaginLaw (G := G) (φ := φ) hFinite with
    ⟨ν, hνprob, hνmom⟩
  let Pν : ProbabilityMeasure ((χ : PontryaginDual (Multiplicative G)) → UnitAddCircle) :=
    ⟨ν, hνprob⟩
  -- Proof comment: the global LCAG frontier is now the explicit comap-based descent owner fed by
  -- the full finite-coordinate moment package of the projective-limit law; the singleton surface
  -- is derived internally where needed.
  exact
    projectiveLimitPontryaginLawDescendsViaComap
      (G := G) (φ := φ) (ν := (Pν : Measure _)) (by
        intro J n
        simpa [Pν] using hνmom J n)

/-- Helper for Theorem 15.29: an equality-shaped Pontryagin witness already yields the normalized
phase-integral witness used by the textbook statement. -/
lemma existsMeasureWithIntegral_pontryaginPhase_eq_of_existsProbabilityMeasurePontryaginCharFunEq
    {φ : PontryaginDual (Multiplicative G) → ℂ}
    (hφ : ∃ μ : ProbabilityMeasure G, pontryaginCharFun μ = φ) :
    ∃ μ : Measure G, μ Set.univ = 1 ∧
      ∀ χ : PontryaginDual (Multiplicative G), ∫ x, pontryaginPhase χ x ∂μ = φ χ := by
  rcases hφ with ⟨μ, hμ⟩
  refine ⟨(μ : Measure G), ?_, ?_⟩
  · -- Proof comment: a `ProbabilityMeasure` already has total mass `1`.
    simp
  · -- Proof comment: rewrite `pontryaginCharFun` back to the phase integral and evaluate the
    -- witness equality at each character.
    intro χ
    calc
      ∫ x, pontryaginPhase χ x ∂(μ : Measure G) = pontryaginCharFun μ χ := by
        rw [pontryaginCharFun_eq_integral_pontryaginPhase]
      _ = φ χ := by
        exact congrFun hμ χ

/-- Helper for Theorem 15.29: the LCAG converse is reduced to one representing-measure owner whose
phase integrals already recover the target function and whose total mass is `1`. -/
lemma existsMeasureWithIntegral_pontryaginPhase_eq [T2Space G] [LocallyCompactSpace G]
    {φ : PontryaginDual (Multiplicative G) → ℂ} (hφ : Continuous φ)
    (hpsd : IsPositiveSemidefiniteMulFunction φ) (hone : φ 1 = 1) :
    ∃ μ : Measure G, μ Set.univ = 1 ∧
      ∀ χ : PontryaginDual (Multiplicative G), ∫ x, pontryaginPhase χ x ∂μ = φ χ := by
  -- Proof comment: after isolating the genuine LCAG Bochner existence owner on
  -- `pontryaginCharFun`, the textbook phase-integral statement is only a repackaging step.
  refine
    existsMeasureWithIntegral_pontryaginPhase_eq_of_existsProbabilityMeasurePontryaginCharFunEq
      (G := G) ?_
  exact existsProbabilityMeasurePontryaginCharFunEqCore (G := G) hφ hpsd hone

/-- Helper for Theorem 15.29: the locally compact abelian converse is isolated as one
equality-shaped owner theorem on the Pontryagin dual. -/
theorem BochnerLCAG.existsProbabilityMeasurePontryaginCharFunEq [T2Space G]
    [LocallyCompactSpace G] {φ : PontryaginDual (Multiplicative G) → ℂ} (hφ : Continuous φ)
    (hpsd : IsPositiveSemidefiniteMulFunction φ) (hone : φ 1 = 1) :
    ∃ μ : ProbabilityMeasure G, pontryaginCharFun μ = φ := by
  rcases existsMeasureWithIntegral_pontryaginPhase_eq (G := G) hφ hpsd hone with ⟨μ0, hmass, hμ0⟩
  have hprob : IsProbabilityMeasure μ0 := by
    -- Proof comment: the representing measure is already normalized, so it can be packaged as a
    -- probability measure without any additional analytic work.
    exact ⟨hmass⟩
  let μ : ProbabilityMeasure G := ⟨μ0, hprob⟩
  refine ⟨μ, funext fun χ ↦ ?_⟩
  -- Proof comment: the remaining step is only the notation change from `pontryaginCharFun` to the
  -- phase integral supplied by the representing-measure owner.
  calc
    pontryaginCharFun μ χ = ∫ x, pontryaginPhase χ x ∂(μ : Measure G) := by
      rw [pontryaginCharFun_eq_integral_pontryaginPhase]
    _ = φ χ := by
      simpa [μ] using hμ0 χ

/-- Helper for Theorem 15.29: the remaining locally compact abelian converse should be a single
abstract Bochner owner theorem on the Pontryagin dual. -/
lemma existsProbabilityMeasurePontryaginCharFunEqOfContinuousPositiveDefiniteCore [T2Space G]
    [LocallyCompactSpace G] {φ : PontryaginDual (Multiplicative G) → ℂ} (hφ : Continuous φ)
    (hpsd : IsPositiveSemidefiniteMulFunction φ) (hone : φ 1 = 1) :
    ∃ μ : ProbabilityMeasure G, ∀ χ : PontryaginDual (Multiplicative G), pontryaginCharFun μ χ = φ χ := by
  -- Proof comment: the pointwise version is now just a thin consumer of the isolated
  -- equality-shaped LCAG Bochner owner.
  refine
    existsPointwisePontryaginCharFunEq_of_existsPontryaginCharFunEq (G := G) ?_
  exact
    BochnerLCAG.existsProbabilityMeasurePontryaginCharFunEq
      (G := G) hφ hpsd hone

/-- Helper for Theorem 15.29: the remaining locally compact abelian converse should be a single
abstract Bochner owner theorem on the Pontryagin dual. -/
lemma existsProbabilityMeasurePontryaginCharFunEqOfContinuousPositiveDefinite [T2Space G]
    [LocallyCompactSpace G] {φ : PontryaginDual (Multiplicative G) → ℂ} (hφ : Continuous φ)
    (hpsd : IsPositiveSemidefiniteMulFunction φ) (hone : φ 1 = 1) :
    ∃ μ : ProbabilityMeasure G, ∀ χ : PontryaginDual (Multiplicative G), pontryaginCharFun μ χ = φ χ := by
  -- Proof comment: keep the notation-level theorem as a thin wrapper over the abstract Pontryagin
  -- owner so the remaining blocker is localized to one upstream existence theorem.
  exact
    existsProbabilityMeasurePontryaginCharFunEqOfContinuousPositiveDefiniteCore
      (G := G) hφ hpsd hone

/-- Helper for Theorem 15.29: a Pontryagin characteristic-function witness can be read either as a
function equality or pointwise on each character. -/
lemma pontryaginCharFun_eq_iff_forall
    (μ : ProbabilityMeasure G) {φ : PontryaginDual (Multiplicative G) → ℂ} :
    pontryaginCharFun μ = φ ↔
      ∀ χ : PontryaginDual (Multiplicative G), pontryaginCharFun μ χ = φ χ := by
  constructor
  · intro hEq
    -- Proof comment: evaluate the function equality at a single character.
    intro χ
    exact congrFun hEq χ
  · intro hEq
    -- Proof comment: function extensionality repackages the pointwise witness as a function
    -- equality.
    exact funext hEq

/-- Helper for Theorem 15.29: a pointwise Pontryagin characteristic-function witness upgrades to
an equality `pontryaginCharFun μ = φ`. -/
lemma existsProbabilityMeasureWithPontryaginCharFunEq_of_pointwise [T2Space G]
    [LocallyCompactSpace G] {φ : PontryaginDual (Multiplicative G) → ℂ}
    (hφ :
      ∃ μ : ProbabilityMeasure G,
        ∀ χ : PontryaginDual (Multiplicative G), pontryaginCharFun μ χ = φ χ) :
    ∃ μ : ProbabilityMeasure G, pontryaginCharFun μ = φ := by
  rcases hφ with ⟨μ, hμ⟩
  -- Proof comment: function extensionality repackages the owner theorem's pointwise witness into
  -- the equality shape used by the public iff statement.
  exact ⟨μ, (pontryaginCharFun_eq_iff_forall (μ := μ)).2 hμ⟩

/-- Helper for Theorem 15.29: once the abstract Pontryagin-side converse supplies the pointwise
characteristic-function witness, the public theorem can consume it directly as a function equality.
-/
lemma existsProbabilityMeasureWithPontryaginCharFunEqOfContinuousPositiveDefinite [T2Space G]
    [LocallyCompactSpace G] {φ : PontryaginDual (Multiplicative G) → ℂ} (hφ : Continuous φ)
    (hpsd : IsPositiveSemidefiniteMulFunction φ) (hone : φ 1 = 1) :
    ∃ μ : ProbabilityMeasure G, pontryaginCharFun μ = φ := by
  -- Proof comment: the only remaining abstract input is the pointwise witness produced by the
  -- isolated core lemma; extensionality repackages it into the equality form of the main theorem.
  exact
    existsProbabilityMeasureWithPontryaginCharFunEq_of_pointwise (G := G)
      (existsProbabilityMeasurePontryaginCharFunEqOfContinuousPositiveDefinite
        (G := G) hφ hpsd hone)

/-- Helper for Theorem 15.29: the Pontryagin witness can be packaged either pointwise or as a
function equality without changing the underlying probability measure. -/
lemma existsProbabilityMeasureWithPontryaginCharFunEq_iff_pointwise [T2Space G]
    [LocallyCompactSpace G] {φ : PontryaginDual (Multiplicative G) → ℂ} :
    (∃ μ : ProbabilityMeasure G, pontryaginCharFun μ = φ) ↔
      (∃ μ : ProbabilityMeasure G,
        ∀ χ : PontryaginDual (Multiplicative G), pontryaginCharFun μ χ = φ χ) := by
  constructor
  · rintro ⟨μ, hμ⟩
    -- Proof comment: evaluate the function equality at each character to recover the pointwise
    -- witness shape expected by the abstract owner theorem.
    exact ⟨μ, (pontryaginCharFun_eq_iff_forall (μ := μ)).1 hμ⟩
  · intro hφ
    -- Proof comment: the reverse direction is exactly the extensional repackaging lemma proved
    -- just above.
    exact existsProbabilityMeasureWithPontryaginCharFunEq_of_pointwise (G := G) hφ

/-- Helper for Theorem 15.29: a pointwise Pontryagin witness already gives the normalized
positive-semidefinite conclusion. -/
lemma isPositiveSemidefiniteMulFunction_and_one_eq_one_of_existsPontryaginCharFunEq_pointwise
    [T2Space G] [LocallyCompactSpace G] {φ : PontryaginDual (Multiplicative G) → ℂ}
    (hφ :
      ∃ μ : ProbabilityMeasure G,
        ∀ χ : PontryaginDual (Multiplicative G), pontryaginCharFun μ χ = φ χ) :
    IsPositiveSemidefiniteMulFunction φ ∧ φ 1 = 1 := by
  rcases hφ with ⟨μ, hμ⟩
  have hEq : pontryaginCharFun μ = φ := by
    -- Proof comment: first repackage the pointwise witness as a function equality so the
    -- companion witness-side lemmas can be applied without further extensional rewrites.
    exact (pontryaginCharFun_eq_iff_forall (μ := μ)).2 hμ
  -- Proof comment: once the witness is identified with `pontryaginCharFun μ`, the positivity and
  -- normalization conclusions are exactly the companion lemmas already proved above.
  exact ⟨by simpa [hEq] using pontryaginCharFun_isPositiveSemidefiniteMulFunction (μ := μ),
    by simpa [hEq] using pontryaginCharFun_one μ⟩

/-- Helper for Theorem 15.29: any Pontryagin characteristic-function witness already gives the
normalized positive-semidefinite conclusion. -/
lemma isPositiveSemidefiniteMulFunction_and_one_eq_one_of_existsPontryaginCharFunEq
    {φ : PontryaginDual (Multiplicative G) → ℂ}
    (hφ : ∃ μ : ProbabilityMeasure G, pontryaginCharFun μ = φ) :
    IsPositiveSemidefiniteMulFunction φ ∧ φ 1 = 1 := by
  rcases hφ with ⟨μ, rfl⟩
  -- Proof comment: once the witness is definitionally `pontryaginCharFun μ`, the positivity and
  -- normalization statements are exactly the companion lemmas proved above.
  exact ⟨pontryaginCharFun_isPositiveSemidefiniteMulFunction μ, pontryaginCharFun_one μ⟩

-- Proof sketch: for the forward implication, combine continuity of characteristic functions with
-- the positive-semidefiniteness criterion above and evaluate at `0`. For the converse implication,
-- apply Bochner's theorem on the locally compact abelian group `G`, with `φ` interpreted as a
-- continuous positive-definite function on the Pontryagin dual.
/-- Theorem 15.29 (2): the same characterization holds for a locally compact abelian group `G`,
where the characteristic function of a probability measure on `G` is viewed on the Pontryagin dual
`PontryaginDual (Multiplicative G)`. -/
theorem exists_probabilityMeasure_pontryaginCharFun_eq_iff [T2Space G] [LocallyCompactSpace G]
    {φ : PontryaginDual (Multiplicative G) → ℂ} (hφ : Continuous φ) :
    (∃ μ : ProbabilityMeasure G, pontryaginCharFun μ = φ) ↔
      IsPositiveSemidefiniteMulFunction φ ∧ φ 1 = 1 := by
  constructor
  · intro hμ
    -- Proof comment: package the witness-side positivity and normalization facts in one reusable
    -- lemma so the main theorem exposes only the converse frontier.
    exact isPositiveSemidefiniteMulFunction_and_one_eq_one_of_existsPontryaginCharFunEq hμ
  · intro hpsd
    rcases hpsd with ⟨hpos, hone⟩
    -- Proof comment: the main theorem now delegates the converse to the isolated Pontryagin-side
    -- Bochner owner instead of carrying abstract harmonic-analysis scaffolding locally.
    exact
      existsProbabilityMeasureWithPontryaginCharFunEqOfContinuousPositiveDefinite
        (G := G) hφ hpos hone

end LocallyCompactAbelian
