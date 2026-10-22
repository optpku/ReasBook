/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Books.ProbabilityTheory_Klenke_2020.Items.Chap04.Exercise_4_2_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Exercise_15_4_4
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Lemma_15_30

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- A Poisson point process with intensity `μ`, encoded through the characteristic-function
identity of Theorem 24.14 for stochastic integrals of integrable real test functions. -/
def IsPoissonPointProcess
    (P : ProbabilityMeasure Ω) (X : Ω → Measure E) (μ : Measure E) : Prop :=
  ∀ ⦃f : E → ℝ⦄, Integrable f μ →
    ∀ t : ℝ,
      ∫ ω, Complex.exp ((((t * ∫ x, f x ∂ X ω) : ℝ) : ℂ) * Complex.I) ∂(P : Measure Ω) =
        Complex.exp (∫ x, (Complex.exp ((((t * f x) : ℝ) : ℂ) * Complex.I) - 1) ∂μ)

-- Proof sketch: unfold `IsPoissonPointProcess`; this is exactly the characteristic-function
-- formula from Theorem 24.14 written as a predicate on the random measure `X`.
/-- Unfolding `IsPoissonPointProcess P X μ` gives the characteristic-function formula for
stochastic integrals against the Poisson point process `X` with intensity `μ`. -/
theorem isPoissonPointProcess_iff
    (P : ProbabilityMeasure Ω) (X : Ω → Measure E) (μ : Measure E) :
    IsPoissonPointProcess P X μ ↔
      ∀ ⦃f : E → ℝ⦄, Integrable f μ →
        ∀ t : ℝ,
          ∫ ω, Complex.exp ((((t * ∫ x, f x ∂ X ω) : ℝ) : ℂ) * Complex.I) ∂
              (P : Measure Ω) =
            Complex.exp (∫ x, (Complex.exp ((((t * f x) : ℝ) : ℂ) * Complex.I) - 1) ∂μ) := by
  -- Proof comment: the local predicate was defined by exactly this characteristic-function formula.
  rfl

/-- Helper for Corollary 24.15: the two oscillatory phases
`y ↦ (exp (iy), exp (i√2 y))` form a measurable embedding of `ℝ`. -/
private theorem twoPhase_measurableEmbedding :
    MeasurableEmbedding
      (fun y : ℝ ↦
        (Complex.exp ((y : ℂ) * Complex.I),
          Complex.exp ((((Real.sqrt 2) * y : ℝ) : ℂ) * Complex.I))) := by
  have hcont :
      Continuous
        (fun y : ℝ ↦
          (Complex.exp ((y : ℂ) * Complex.I),
            Complex.exp ((((Real.sqrt 2) * y : ℝ) : ℂ) * Complex.I))) := by
    -- Proof comment: both phase coordinates are continuous compositions of `Complex.exp`.
    fun_prop
  have hinj :
      Function.Injective
        (fun y : ℝ ↦
          (Complex.exp ((y : ℂ) * Complex.I),
            Complex.exp ((((Real.sqrt 2) * y : ℝ) : ℂ) * Complex.I))) := by
    intro y z h
    have hfst :
        Complex.exp ((y : ℂ) * Complex.I) = Complex.exp ((z : ℂ) * Complex.I) :=
      congrArg Prod.fst h
    have hsnd :
        Complex.exp ((((Real.sqrt 2) * y : ℝ) : ℂ) * Complex.I) =
          Complex.exp ((((Real.sqrt 2) * z : ℝ) : ℂ) * Complex.I) :=
      congrArg Prod.snd h
    rcases Complex.exp_eq_exp_iff_exists_int.mp hfst with ⟨m, hm⟩
    rcases Complex.exp_eq_exp_iff_exists_int.mp hsnd with ⟨n, hn⟩
    have hmReal : y - z = 2 * Real.pi * m := by
      -- Proof comment: equality of the first phases pins the difference down to an integer
      -- multiple of `2π`.
      have him := congrArg Complex.im hm
      have hyz_eq : y = z + 2 * Real.pi * m := by
        simpa [sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm] using him
      linarith
    have hnReal : Real.sqrt 2 * (y - z) = 2 * Real.pi * n := by
      -- Proof comment: the second phase gives the same difference scaled by `√2`.
      have him := congrArg Complex.im hn
      have hyz_eq : Real.sqrt 2 * y = Real.sqrt 2 * z + 2 * Real.pi * n := by
        simpa [sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm, left_distrib, right_distrib]
          using him
      linarith
    by_cases hyz : y = z
    · exact hyz
    · have hm_ne : m ≠ 0 := by
        intro hm_zero
        apply hyz
        have : y - z = 0 := by simpa [hm_zero] using hmReal
        linarith
      have hm_real_ne : (m : ℝ) ≠ 0 := by
        exact_mod_cast hm_ne
      have hmul : Real.sqrt 2 * (m : ℝ) = n := by
        have htwoPi_ne : (2 * Real.pi : ℝ) ≠ 0 := by
          positivity
        apply (mul_right_cancel₀ htwoPi_ne)
        calc
          Real.sqrt 2 * (m : ℝ) * (2 * Real.pi)
              = Real.sqrt 2 * (2 * Real.pi * (m : ℝ)) := by ring
          _ = Real.sqrt 2 * (y - z) := by rw [hmReal]
          _ = 2 * Real.pi * n := hnReal
          _ = n * (2 * Real.pi) := by ring
      have hrat : Real.sqrt 2 = n / m := by
        exact (eq_div_iff hm_real_ne).2 hmul
      exfalso
      exact (irrational_sqrt_two.ne_rational n m) hrat
  exact hcont.measurableEmbedding hinj

/-- Helper for Corollary 24.15: the PPP characteristic-function surface forces
`ω ↦ ∫ x, f x ∂ X ω` to be `P`-a.e. measurable. -/
private theorem stochasticIntegral_aemeasurable
    (P : ProbabilityMeasure Ω) (X : Ω → Measure E) (μ : Measure E) {f : E → ℝ}
    (hX : IsPoissonPointProcess P X μ) (hf : Integrable f μ) :
    AEMeasurable (fun ω ↦ ∫ x, f x ∂ X ω) (P : Measure Ω) := by
  let Y : Ω → ℝ := fun ω ↦ ∫ x, f x ∂ X ω
  have hPhase1 :
      AEMeasurable
        (fun ω ↦ Complex.exp ((((Y ω) : ℝ) : ℂ) * Complex.I))
        (P : Measure Ω) := by
    -- Proof comment: the characteristic-function identity gives a nonzero integral at frequency
    -- `1`, so the phase integrand must be genuinely integrable and hence measurable.
    exact
      (MeasureTheory.Integrable.of_integral_ne_zero
        (μ := (P : Measure Ω))
        (f := fun ω ↦ Complex.exp ((((Y ω) : ℝ) : ℂ) * Complex.I))
        (by
          simpa [Y] using
            (show
              ∫ ω, Complex.exp ((((1 * ∫ x, f x ∂ X ω) : ℝ) : ℂ) * Complex.I) ∂(P : Measure Ω) ≠ 0 by
                rw [hX hf 1]
                exact Complex.exp_ne_zero _))).1.aemeasurable
  have hPhaseSqrt2 :
      AEMeasurable
        (fun ω ↦ Complex.exp ((((Real.sqrt 2 * Y ω : ℝ) : ℂ) * Complex.I)))
        (P : Measure Ω) := by
    -- Proof comment: the same argument at frequency `√2` supplies the second phase coordinate.
    exact
      (MeasureTheory.Integrable.of_integral_ne_zero
        (μ := (P : Measure Ω))
        (f := fun ω ↦ Complex.exp ((((Real.sqrt 2 * Y ω : ℝ) : ℂ) * Complex.I)))
        (by
          simpa [Y, mul_assoc, mul_left_comm, mul_comm] using
            (show
              ∫ ω,
                  Complex.exp
                    ((((Real.sqrt 2 * ∫ x, f x ∂ X ω : ℝ) : ℂ) * Complex.I)) ∂
                    (P : Measure Ω) ≠ 0 by
                rw [hX hf (Real.sqrt 2)]
                exact Complex.exp_ne_zero _))).1.aemeasurable
  have hPair :
      AEMeasurable
        (fun ω ↦
          (Complex.exp ((((Y ω) : ℝ) : ℂ) * Complex.I),
            Complex.exp ((((Real.sqrt 2 * Y ω : ℝ) : ℂ) * Complex.I))))
        (P : Measure Ω) :=
    hPhase1.prodMk hPhaseSqrt2
  -- Proof comment: the two phase coordinates separate real values, so the measurable embedding
  -- recovers the stochastic integral itself.
  simpa [Function.comp, Y] using
    (MeasurableEmbedding.aemeasurable_comp_iff
      (μ := (P : Measure Ω))
      (f := fun ω ↦ Y ω)
      twoPhase_measurableEmbedding).mp hPair

/-- Helper for Corollary 24.15: the explicit Poisson characteristic exponent has first derivative
at `0`, and that derivative is `Complex.I` times `∫ f dμ`. -/
private theorem poissonCharacteristicExponent_hasDerivAt_zero
    (μ : Measure E) {f : E → ℝ} (hf : Integrable f μ) :
    HasDerivAt
      (fun t : ℝ ↦
        Complex.exp (∫ x, (Complex.exp ((((t * f x) : ℝ) : ℂ) * Complex.I) - 1) ∂μ))
      (((∫ x, f x ∂μ : ℝ) : ℂ) * Complex.I) 0 := by
  let F : ℝ → E → ℂ := fun t x ↦
    Complex.exp ((((t * f x) : ℝ) : ℂ) * Complex.I) - 1
  let F' : ℝ → E → ℂ := fun t x ↦
    ((f x : ℂ) * Complex.I) * Complex.exp ((((t * f x) : ℝ) : ℂ) * Complex.I)
  have hIntegralDeriv :
      HasDerivAt (fun t : ℝ ↦ ∫ x, F t x ∂μ) (((∫ x, f x ∂μ : ℝ) : ℂ) * Complex.I) 0 := by
    -- Proof comment: differentiate under the `μ`-integral, using `|f|` as the uniform bound for
    -- the pointwise derivatives of the oscillatory kernel.
    have h :=
      hasDerivAt_integral_of_dominated_loc_of_deriv_le
        (bound := fun x ↦ |f x|)
        (F := F) (x₀ := (0 : ℝ)) (s := Set.univ) (μ := μ) (F' := F')
        (by simpa using Filter.univ_mem)
        (Filter.Eventually.of_forall fun _ ↦ by fun_prop)
        (by simpa [F] using (integrable_zero : Integrable (fun _ : E ↦ (0 : ℂ)) μ))
        (by fun_prop)
        (ae_of_all _ fun x t _ ↦ by
          have hnorm : ‖Complex.exp (Complex.I * (↑t * ↑(f x)))‖ = 1 := by
            rw [Complex.norm_exp]
            simp
          simpa [F', mul_assoc, mul_left_comm, mul_comm, hnorm])
        (by simpa using hf.norm)
        (ae_of_all _ fun x t _ ↦ by
          have hPhase :
              HasDerivAt (fun s : ℝ ↦ (((s * f x : ℝ) : ℂ) * Complex.I))
                (((f x : ℂ) * Complex.I)) t := by
            have hPhaseReal : HasDerivAt (fun s : ℝ ↦ s * f x) (f x) t := by
              simpa using (hasDerivAt_mul_const (x := t) (f x))
            have hPhaseComplex :
                HasDerivAt (fun s : ℝ ↦ ((s * f x : ℝ) : ℂ)) (f x : ℂ) t :=
              hPhaseReal.ofReal_comp
            simpa [mul_assoc, mul_left_comm, mul_comm] using
              hPhaseComplex.mul_const Complex.I
          simpa [F, F', sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm] using
            (Complex.hasDerivAt_exp ((((t * f x) : ℝ) : ℂ) * Complex.I)).comp t hPhase)
    have hIntegral :
        (∫ x, ((f x : ℂ) * Complex.I) ∂μ) = (((∫ x, f x ∂μ : ℝ) : ℂ) * Complex.I) := by
      calc
        ∫ x, ((f x : ℂ) * Complex.I) ∂μ = (∫ x, (f x : ℂ) ∂μ) * Complex.I := by
          simpa using (integral_mul_const Complex.I (fun x => (f x : ℂ)))
        _ = (((∫ x, f x ∂μ : ℝ) : ℂ) * Complex.I) := by
          rw [integral_complex_ofReal]
    simpa [F, F', hIntegral] using h.2
  have hZeroExponent : (∫ x, F 0 x ∂μ) = 0 := by
    simp [F]
  -- Proof comment: at `t = 0` the exponent itself vanishes, so the outer derivative is the
  -- derivative of `Complex.exp` at `0` composed with the integral derivative above.
  simpa [Function.comp, F, hZeroExponent] using
    (HasDerivAt.comp_of_eq
      (h := fun t : ℝ ↦ ∫ x, F t x ∂μ)
      (h₂ := Complex.exp) (x := (0 : ℝ)) (y := (0 : ℂ))
      (Complex.hasDerivAt_exp (0 : ℂ)) hIntegralDeriv hZeroExponent.symm)

/-- Helper for Corollary 24.15: the Poisson exponent integral vanishes at `0`. -/
private theorem poissonCharacteristicIntegral_zero
    (μ : Measure E) {f : E → ℝ} :
    (∫ x, (Complex.exp ((((0 * f x) : ℝ) : ℂ) * Complex.I) - 1) ∂μ) = 0 := by
  -- Proof comment: the oscillatory phase is exactly `1` at frequency `0`.
  simp

/-- Helper for Corollary 24.15: the first-derivative kernel at `0` integrates to
`Complex.I * ∫ f dμ`. -/
private theorem poissonCharacteristicIntegral_firstKernel_zero
    (μ : Measure E) {f : E → ℝ} :
    (∫ x, ((f x : ℂ) * Complex.I) * Complex.exp ((((0 * f x) : ℝ) : ℂ) * Complex.I) ∂μ) =
      (((∫ x, f x ∂μ : ℝ) : ℂ) * Complex.I) := by
  -- Proof comment: at `0` the exponential factor drops out, so only the complexified integral of
  -- `f` remains.
  calc
    ∫ x, ((f x : ℂ) * Complex.I) * Complex.exp ((((0 * f x) : ℝ) : ℂ) * Complex.I) ∂μ
        = ∫ x, ((f x : ℂ) * Complex.I) ∂μ := by simp
    _ = (∫ x, (f x : ℂ) ∂μ) * Complex.I := by
          simpa using (integral_mul_const Complex.I (fun x ↦ (f x : ℂ)))
    _ = (((∫ x, f x ∂μ : ℝ) : ℂ) * Complex.I) := by rw [integral_complex_ofReal]

/-- Helper for Corollary 24.15: the Poisson exponent integral itself is differentiable at every
frequency, with derivative obtained by differentiating under the integral sign. -/
private theorem poissonCharacteristicIntegral_hasDerivAt
    (μ : Measure E) {f : E → ℝ} (hf : Integrable f μ) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ ↦ ∫ x, (Complex.exp ((((s * f x) : ℝ) : ℂ) * Complex.I) - 1) ∂μ)
      (∫ x, ((f x : ℂ) * Complex.I) * Complex.exp ((((t * f x) : ℝ) : ℂ) * Complex.I) ∂μ) t := by
  let F : ℝ → E → ℂ := fun s x ↦
    Complex.exp ((((s * f x) : ℝ) : ℂ) * Complex.I) - 1
  let F' : ℝ → E → ℂ := fun s x ↦
    ((f x : ℂ) * Complex.I) * Complex.exp ((((s * f x) : ℝ) : ℂ) * Complex.I)
  have hFt_int : Integrable (F t) μ := by
    -- Proof comment: `|exp (i t f) - 1|` is controlled by `|t| * |f|`, so the original kernel is
    -- integrable whenever `f ∈ L¹(μ)`.
    refine Integrable.mono' (hf.norm.const_mul |t|) ?_ ?_
    · have hf_meas : AEMeasurable f μ := hf.aestronglyMeasurable.aemeasurable
      simpa [F] using
        ((hf_meas.const_mul t).complex_ofReal.mul_const Complex.I).cexp.sub_const (1 : ℂ)
          |>.aestronglyMeasurable
    · filter_upwards with x
      calc
        ‖F t x‖
            = ‖Complex.exp (((((t * f x) : ℝ) : ℂ) * Complex.I)) - 1‖ := by simp [F]
        _ ≤ |t * f x| := by
              simpa [mul_assoc, mul_left_comm, mul_comm] using
                (Real.norm_exp_I_mul_ofReal_sub_one_le (x := t * f x))
        _ = |t| * |f x| := abs_mul _ _
  -- Proof comment: with the `|f|` domination in place, differentiate under the integral sign at
  -- the arbitrary frequency `t`.
  simpa [F, F'] using
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (bound := fun x ↦ |f x|)
      (F := F) (x₀ := t) (s := Set.univ) (μ := μ) (F' := F')
      (by simpa using Filter.univ_mem)
      (Filter.Eventually.of_forall fun s ↦ by
        have hf_meas : AEMeasurable f μ := hf.aestronglyMeasurable.aemeasurable
        simpa [F] using
          ((((hf_meas.const_mul s).complex_ofReal).mul_const Complex.I).cexp.sub_const
            (1 : ℂ)).aestronglyMeasurable)
      hFt_int
      (by
        have hf_meas : AEMeasurable f μ := hf.aestronglyMeasurable.aemeasurable
        have hLeft :
            AEStronglyMeasurable (fun x ↦ ((f x : ℂ) * Complex.I)) μ := by
          simpa using ((hf_meas.complex_ofReal).mul_const Complex.I).aestronglyMeasurable
        have hRight :
            AEStronglyMeasurable
              (fun x ↦ Complex.exp ((((t * f x) : ℝ) : ℂ) * Complex.I)) μ := by
          simpa using
            (((hf_meas.const_mul t).complex_ofReal.mul_const Complex.I).cexp).aestronglyMeasurable
        simpa [F'] using hLeft.mul hRight)
      (ae_of_all _ fun x s _ ↦ by
        have hnorm : ‖Complex.exp (Complex.I * (↑s * ↑(f x)))‖ = 1 := by
          rw [Complex.norm_exp]
          simp
        simpa [F', mul_assoc, mul_left_comm, mul_comm, hnorm])
      (by simpa using hf.norm)
      (ae_of_all _ fun x s _ ↦ by
        have hPhase :
            HasDerivAt (fun u : ℝ ↦ (((u * f x : ℝ) : ℂ) * Complex.I))
              (((f x : ℂ) * Complex.I)) s := by
          have hPhaseReal : HasDerivAt (fun u : ℝ ↦ u * f x) (f x) s := by
            simpa using (hasDerivAt_mul_const (x := s) (f x))
          have hPhaseComplex :
              HasDerivAt (fun u : ℝ ↦ ((u * f x : ℝ) : ℂ)) (f x : ℂ) s :=
            hPhaseReal.ofReal_comp
          simpa [mul_assoc, mul_left_comm, mul_comm] using hPhaseComplex.mul_const Complex.I
        simpa [F, F', sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm] using
          (Complex.hasDerivAt_exp ((((s * f x) : ℝ) : ℂ) * Complex.I)).comp s hPhase)).2

/-- Helper for Corollary 24.15: the derivative of the Poisson exponent integral has derivative at
`0` given by the negative `μ`-integral of `f²`. -/
private theorem poissonCharacteristicIntegral_deriv_hasDerivAt_zero
    (μ : Measure E) {f : E → ℝ} (hf_int : Integrable f μ) (hf_sq : MemLp f 2 μ) :
    HasDerivAt
      (fun t : ℝ ↦
        deriv
          (fun s : ℝ ↦ ∫ x, (Complex.exp ((((s * f x) : ℝ) : ℂ) * Complex.I) - 1) ∂μ) t)
      (-((∫ x, (f x) ^ 2 ∂μ : ℝ) : ℂ)) 0 := by
  let G : ℝ → ℂ := fun s ↦
    ∫ x, (Complex.exp ((((s * f x) : ℝ) : ℂ) * Complex.I) - 1) ∂μ
  let K : ℝ → E → ℂ := fun t x ↦
    ((f x : ℂ) * Complex.I) * Complex.exp ((((t * f x) : ℝ) : ℂ) * Complex.I)
  let K' : ℝ → E → ℂ := fun t x ↦
    (-((f x) ^ 2 : ℂ)) * Complex.exp ((((t * f x) : ℝ) : ℂ) * Complex.I)
  have hDerivEq :
      deriv G = fun t ↦ ∫ x, K t x ∂μ := by
    -- Proof comment: the previous lemma already gives the derivative of the exponent integral at
    -- every frequency.
    funext t
    simpa [G, K] using (poissonCharacteristicIntegral_hasDerivAt μ hf_int t).deriv
  have hK0_meas : AEStronglyMeasurable (K' 0) μ := by
    -- Proof comment: at frequency `0`, the second kernel collapses to the complexified square
    -- integrand, which is integrable by the `L²` hypothesis.
    have hInt : Integrable (K' 0) μ := by
      refine ((hf_sq.integrable_sq.ofReal).const_mul (-1 : ℂ)).congr ?_
      filter_upwards with x
      simp [K']
    exact hInt.aestronglyMeasurable
  have hIntegralDeriv :
      HasDerivAt (fun t : ℝ ↦ ∫ x, K t x ∂μ) (-((∫ x, (f x) ^ 2 ∂μ : ℝ) : ℂ)) 0 := by
    -- Proof comment: differentiate the explicit first-derivative kernel under the integral sign,
    -- using `f²` as the uniform bound.
    have h :=
      hasDerivAt_integral_of_dominated_loc_of_deriv_le
        (bound := fun x ↦ (f x) ^ 2)
        (F := K) (x₀ := (0 : ℝ)) (s := Set.univ) (μ := μ) (F' := K')
        (by simpa using Filter.univ_mem)
        (Filter.Eventually.of_forall fun t ↦ by
          have hf_meas : AEMeasurable f μ := hf_int.aestronglyMeasurable.aemeasurable
          have hLeft :
              AEStronglyMeasurable (fun x ↦ ((f x : ℂ) * Complex.I)) μ := by
            simpa using ((hf_meas.complex_ofReal).mul_const Complex.I).aestronglyMeasurable
          have hRight :
              AEStronglyMeasurable
                (fun x ↦ Complex.exp ((((t * f x) : ℝ) : ℂ) * Complex.I)) μ := by
            simpa using
              (((hf_meas.const_mul t).complex_ofReal.mul_const Complex.I).cexp).aestronglyMeasurable
          simpa [K] using hLeft.mul hRight)
        (by
          refine ((hf_int.ofReal).mul_const Complex.I).congr ?_
          filter_upwards with x
          simp [K])
        hK0_meas
        (ae_of_all _ fun x t _ ↦ by
          have hnorm : ‖Complex.exp ((((t * f x) : ℝ) : ℂ) * Complex.I)‖ = 1 := by
            rw [Complex.norm_exp]
            simp
          have hEq :
              ‖K' t x‖ = (f x) ^ 2 := by
            calc
            ‖K' t x‖
                = ‖-((f x) ^ 2 : ℂ)‖ * ‖Complex.exp ((((t * f x) : ℝ) : ℂ) * Complex.I)‖ := by
                    simp [K', norm_mul]
              _ = |(f x) ^ 2| * 1 := by rw [hnorm]; simp
              _ = (f x) ^ 2 * 1 := by rw [abs_of_nonneg (sq_nonneg (f x))]
              _ = (f x) ^ 2 := by ring
          calc
            ‖K' t x‖ = (f x) ^ 2 := hEq
            _ ≤ (fun x ↦ (f x) ^ 2) x := le_rfl)
        (by simpa using hf_sq.integrable_sq)
        (ae_of_all _ fun x t _ ↦ by
          have hPhase :
              HasDerivAt (fun u : ℝ ↦ (((u * f x : ℝ) : ℂ) * Complex.I))
                (((f x : ℂ) * Complex.I)) t := by
            have hPhaseReal : HasDerivAt (fun u : ℝ ↦ u * f x) (f x) t := by
              simpa using (hasDerivAt_mul_const (x := t) (f x))
            have hPhaseComplex :
                HasDerivAt (fun u : ℝ ↦ ((u * f x : ℝ) : ℂ)) (f x : ℂ) t :=
              hPhaseReal.ofReal_comp
            simpa [mul_assoc, mul_left_comm, mul_comm] using hPhaseComplex.mul_const Complex.I
          have hExp :
              HasDerivAt
                (fun u : ℝ ↦ Complex.exp ((((u * f x) : ℝ) : ℂ) * Complex.I))
                (Complex.exp ((((t * f x) : ℝ) : ℂ) * Complex.I) * ((f x : ℂ) * Complex.I)) t := by
            simpa [mul_assoc, mul_left_comm, mul_comm] using
              (Complex.hasDerivAt_exp ((((t * f x) : ℝ) : ℂ) * Complex.I)).comp t hPhase
          have hK :
              HasDerivAt (fun u : ℝ ↦ K u x)
                (((f x : ℂ) * Complex.I) *
                  (Complex.exp ((((t * f x) : ℝ) : ℂ) * Complex.I) * ((f x : ℂ) * Complex.I))) t := by
            simpa [K, mul_assoc, mul_left_comm, mul_comm] using
              (hExp.const_mul ((f x : ℂ) * Complex.I))
          have hCoeff :
              (((f x : ℂ) * Complex.I) *
                (Complex.exp ((((t * f x) : ℝ) : ℂ) * Complex.I) * ((f x : ℂ) * Complex.I))) =
                (-((f x) ^ 2 : ℂ)) * Complex.exp ((((t * f x) : ℝ) : ℂ) * Complex.I) := by
            calc
              (((f x : ℂ) * Complex.I) *
                  (Complex.exp ((((t * f x) : ℝ) : ℂ) * Complex.I) * ((f x : ℂ) * Complex.I)))
                  = ((f x : ℂ) * (f x : ℂ)) * (Complex.I * Complex.I) *
                      Complex.exp ((((t * f x) : ℝ) : ℂ) * Complex.I) := by ring
              _ = (-((f x) ^ 2 : ℂ)) * Complex.exp ((((t * f x) : ℝ) : ℂ) * Complex.I) := by
                    simp [pow_two, Complex.I_sq, mul_assoc, mul_left_comm, mul_comm]
          exact hK.congr_deriv hCoeff)
    have hIntegralK0 :
        (∫ x, K' 0 x ∂μ) = -((∫ x, (f x) ^ 2 ∂μ : ℝ) : ℂ) := by
      calc
        ∫ x, K' 0 x ∂μ = ∫ x, (-((f x) ^ 2 : ℂ)) ∂μ := by simp [K']
        _ = -∫ x, ((f x) ^ 2 : ℂ) ∂μ := by simpa using integral_neg (f := fun x ↦ ((f x) ^ 2 : ℂ))
        _ = -((∫ x, (f x) ^ 2 ∂μ : ℝ) : ℂ) := by
              have hCast :
                  (∫ x, ((f x) ^ 2 : ℂ) ∂μ) = ((∫ x, (f x) ^ 2 ∂μ : ℝ) : ℂ) := by
                simpa [pow_two] using
                  (integral_complex_ofReal (f := fun x : E ↦ f x * f x) (μ := μ))
              rw [hCast]
    exact h.2.congr_deriv hIntegralK0
  -- Proof comment: replace `deriv G` by its explicit integral formula and transport the
  -- derivative through this normal form.
  rw [Filter.EventuallyEq.hasDerivAt_iff (Filter.Eventually.of_forall fun t ↦ by rw [hDerivEq])]
  simpa [G] using hIntegralDeriv

/-- Helper for Corollary 24.15: the explicit Poisson characteristic exponent has second
derivative at `0`, giving the `f²` term plus the squared mean term. -/
private theorem poissonCharacteristicExponent_secondDerivAt_zero
    (μ : Measure E) {f : E → ℝ} (hf_int : Integrable f μ) (hf_sq : MemLp f 2 μ) :
    HasDerivAt
      (fun t : ℝ ↦
        deriv
          (fun s : ℝ ↦
            Complex.exp (∫ x, (Complex.exp ((((s * f x) : ℝ) : ℂ) * Complex.I) - 1) ∂μ)) t)
      (-((∫ x, (f x) ^ 2 ∂μ : ℝ) : ℂ) - (((∫ x, f x ∂μ : ℝ) : ℂ) ^ 2)) 0 := by
  let H : ℝ → ℂ := fun s ↦
    ∫ x, (Complex.exp ((((s * f x) : ℝ) : ℂ) * Complex.I) - 1) ∂μ
  let A : ℝ → ℂ := fun t ↦
    deriv (fun s : ℝ ↦ ∫ x, (Complex.exp ((((s * f x) : ℝ) : ℂ) * Complex.I) - 1) ∂μ) t
  let B : ℝ → ℂ := fun t ↦ Complex.exp (H t)
  have hBDeriv : HasDerivAt B ((((∫ x, f x ∂μ : ℝ) : ℂ) * Complex.I)) 0 := by
    -- Proof comment: the first derivative of the outer Poisson characteristic exponent was proved
    -- earlier as the mean term.
    simpa [B, H] using poissonCharacteristicExponent_hasDerivAt_zero μ hf_int
  have hADeriv :
      HasDerivAt A (-((∫ x, (f x) ^ 2 ∂μ : ℝ) : ℂ)) 0 := by
    -- Proof comment: the derivative of the inner exponent integral contributes the `f²` term.
    simpa [A] using poissonCharacteristicIntegral_deriv_hasDerivAt_zero μ hf_int hf_sq
  have hDerivEq :
      deriv B = fun t ↦ A t * B t := by
    -- Proof comment: away from any transport tricks, the derivative of `exp ∘ H` is the standard
    -- product `H' * exp(H)`.
    funext t
    have hHt := poissonCharacteristicIntegral_hasDerivAt μ hf_int t
    have hAeq :
        A t = ∫ x, ((f x : ℂ) * Complex.I) *
          Complex.exp ((((t * f x) : ℝ) : ℂ) * Complex.I) ∂μ := by
      simpa [A, mul_assoc, mul_left_comm, mul_comm] using hHt.deriv
    have hBt :
        HasDerivAt B
          (B t *
            (∫ x, ((f x : ℂ) * Complex.I) *
              Complex.exp ((((t * f x) : ℝ) : ℂ) * Complex.I) ∂μ)) t := by
      simpa [B, H, mul_assoc, mul_left_comm, mul_comm] using
        (Complex.hasDerivAt_exp (H t)).comp t hHt
    calc
      deriv B t
          = B t *
              (∫ x, ((f x : ℂ) * Complex.I) *
                Complex.exp ((((t * f x) : ℝ) : ℂ) * Complex.I) ∂μ) := by
                  exact hBt.deriv
      _ = B t * A t := by rw [hAeq]
      _ = A t * B t := by ring
  -- Proof comment: after rewriting `deriv B` in the stable product normal form, the product rule
  -- at `0` produces the variance coefficient.
  rw [Filter.EventuallyEq.hasDerivAt_iff (Filter.Eventually.of_forall fun t ↦ by rw [hDerivEq])]
  have hA0 :
      A 0 = (((∫ x, f x ∂μ : ℝ) : ℂ) * Complex.I) := by
    calc
      A 0 = ∫ x, ((f x : ℂ) * Complex.I) *
          Complex.exp ((((0 * f x) : ℝ) : ℂ) * Complex.I) ∂μ := by
            simpa [A] using (poissonCharacteristicIntegral_hasDerivAt μ hf_int 0).deriv
      _ = (((∫ x, f x ∂μ : ℝ) : ℂ) * Complex.I) := by
            exact poissonCharacteristicIntegral_firstKernel_zero (μ := μ) (f := f)
  have hB0 : B 0 = 1 := by
    simp [B, H, poissonCharacteristicIntegral_zero]
  have hProd :
      HasDerivAt (fun t ↦ A t * B t)
        (-((∫ x, (f x) ^ 2 ∂μ : ℝ) : ℂ) +
          ((((∫ x, f x ∂μ : ℝ) : ℂ) * Complex.I) *
            (((∫ x, f x ∂μ : ℝ) : ℂ) * Complex.I))) 0 := by
    simpa [B, H, hB0, hA0, poissonCharacteristicIntegral_zero, mul_assoc, mul_left_comm, mul_comm] using
      (show HasDerivAt (fun t ↦ A t * B t)
        (-((∫ x, (f x) ^ 2 ∂μ : ℝ) : ℂ) * B 0 + A 0 * (((∫ x, f x ∂μ : ℝ) : ℂ) * Complex.I)) 0 from
        hADeriv.mul hBDeriv)
  have hCoeff :
      (-((∫ x, (f x) ^ 2 ∂μ : ℝ) : ℂ) +
        ((((∫ x, f x ∂μ : ℝ) : ℂ) * Complex.I) *
          (((∫ x, f x ∂μ : ℝ) : ℂ) * Complex.I))) =
        (-((∫ x, (f x) ^ 2 ∂μ : ℝ) : ℂ) - (((∫ x, f x ∂μ : ℝ) : ℂ) ^ 2)) := by
    have hI :
        (((∫ x, f x ∂μ : ℝ) : ℂ) * (((∫ x, f x ∂μ : ℝ) : ℂ)) * (Complex.I * Complex.I)) =
          -(((∫ x, f x ∂μ : ℝ) : ℂ) ^ 2) := by
      have hII : Complex.I * Complex.I = (-1 : ℂ) := by simp [Complex.I_sq]
      rw [hII]
      ring
    calc
      (-((∫ x, (f x) ^ 2 ∂μ : ℝ) : ℂ) +
        ((((∫ x, f x ∂μ : ℝ) : ℂ) * Complex.I) *
          (((∫ x, f x ∂μ : ℝ) : ℂ) * Complex.I)))
          = (-((∫ x, (f x) ^ 2 ∂μ : ℝ) : ℂ) +
              (((((∫ x, f x ∂μ : ℝ) : ℂ) * (((∫ x, f x ∂μ : ℝ) : ℂ))) *
                (Complex.I * Complex.I)))) := by ring
      _ = (-((∫ x, (f x) ^ 2 ∂μ : ℝ) : ℂ) - (((∫ x, f x ∂μ : ℝ) : ℂ) ^ 2)) := by
            rw [hI]
            ring
  exact hProd.congr_deriv hCoeff

/-- Helper for Corollary 24.15: a nonnegative test function has stochastic-integral mean equal to
its `μ`-integral. -/
private theorem poissonPointProcess_integral_expectation_eq_of_nonneg
    (P : ProbabilityMeasure Ω) (X : Ω → Measure E) (μ : Measure E) {g : E → ℝ}
    (hX : IsPoissonPointProcess P X μ) (hg : Integrable g μ) (hg_nonneg : ∀ x, 0 ≤ g x) :
    ∫ ω, (∫ x, g x ∂ X ω) ∂(P : Measure Ω) = ∫ x, g x ∂μ := by
  let Y : Ω → ℝ := fun ω ↦ ∫ x, g x ∂ X ω
  have hY : AEMeasurable Y (P : Measure Ω) :=
    stochasticIntegral_aemeasurable P X μ hX hg
  haveI : IsProbabilityMeasure ((P : Measure Ω).map Y) :=
    Measure.isProbabilityMeasure_map hY
  have hChar :
      MeasureTheory.charFun ((P : Measure Ω).map Y) =
        fun t : ℝ ↦
          Complex.exp (∫ x, (Complex.exp ((((t * g x) : ℝ) : ℂ) * Complex.I) - 1) ∂μ) := by
    funext t
    rw [MeasureTheory.charFun_apply_real, MeasureTheory.integral_map hY]
    · simpa [Y, mul_assoc, mul_left_comm, mul_comm] using hX hg t
    · fun_prop
  have hDeriv :
      HasDerivAt (MeasureTheory.charFun ((P : Measure Ω).map Y))
        (((∫ x, g x ∂μ : ℝ) : ℂ) * Complex.I) 0 := by
    -- Proof comment: transfer the explicit Poisson derivative to the characteristic function of
    -- the pushed-forward law of the stochastic integral.
    simpa [hChar] using poissonCharacteristicExponent_hasDerivAt_zero μ hg
  have hNonneg :
      ∀ᵐ y ∂((P : Measure Ω).map Y), 0 ≤ y := by
    -- Proof comment: a nonnegative integrand has nonnegative integral under every random measure.
    rw [ae_map_iff hY measurableSet_Ici]
    filter_upwards with ω
    exact MeasureTheory.integral_nonneg hg_nonneg
  rcases integrable_id_of_nonnegative_hasDerivAt_charFun_zero
      (μ := (P : Measure Ω).map Y) hDeriv hNonneg with ⟨hIntId, hMean⟩
  have hMapIntegral :
      ∫ y, y ∂((P : Measure Ω).map Y) = ∫ x, g x ∂μ := by
    -- Proof comment: compare imaginary parts of the derivative identity to read off the mean.
    have hMul := congrArg (fun z : ℂ ↦ (-Complex.I) * z) hMean
    have hComplex :
        (((∫ x, g x ∂μ : ℝ) : ℂ)) =
          ∫ y, (y : ℂ) ∂((P : Measure Ω).map Y) := by
      simpa [mul_assoc] using hMul
    rw [integral_complex_ofReal] at hComplex
    exact_mod_cast hComplex.symm
  calc
    ∫ ω, (∫ x, g x ∂ X ω) ∂(P : Measure Ω) = ∫ y, y ∂((P : Measure Ω).map Y) := by
      simpa [Y] using
        (MeasureTheory.integral_map hY
          (by fun_prop : AEStronglyMeasurable (fun y : ℝ ↦ y) ((P : Measure Ω).map Y))).symm
    _ = ∫ x, g x ∂μ := hMapIntegral

/-- Helper for Corollary 24.15: a nonnegative test function produces an integrable stochastic
integral random variable. -/
private theorem stochasticIntegral_integrable_of_nonneg
    (P : ProbabilityMeasure Ω) (X : Ω → Measure E) (μ : Measure E) {g : E → ℝ}
    (hX : IsPoissonPointProcess P X μ) (hg : Integrable g μ) (hg_nonneg : ∀ x, 0 ≤ g x) :
    Integrable (fun ω ↦ ∫ x, g x ∂ X ω) (P : Measure Ω) := by
  let Y : Ω → ℝ := fun ω ↦ ∫ x, g x ∂ X ω
  have hY : AEMeasurable Y (P : Measure Ω) :=
    stochasticIntegral_aemeasurable P X μ hX hg
  haveI : IsProbabilityMeasure ((P : Measure Ω).map Y) :=
    Measure.isProbabilityMeasure_map hY
  have hChar :
      MeasureTheory.charFun ((P : Measure Ω).map Y) =
        fun t : ℝ ↦
          Complex.exp (∫ x, (Complex.exp ((((t * g x) : ℝ) : ℂ) * Complex.I) - 1) ∂μ) := by
    funext t
    rw [MeasureTheory.charFun_apply_real, MeasureTheory.integral_map hY]
    · simpa [Y, mul_assoc, mul_left_comm, mul_comm] using hX hg t
    · fun_prop
  have hDeriv :
      HasDerivAt (MeasureTheory.charFun ((P : Measure Ω).map Y))
        (((∫ x, g x ∂μ : ℝ) : ℂ) * Complex.I) 0 := by
    -- Proof comment: the characteristic-function derivative calculation for the nonnegative case
    -- is identical to the one already used for the mean identity.
    simpa [hChar] using poissonCharacteristicExponent_hasDerivAt_zero μ hg
  have hNonneg :
      ∀ᵐ y ∂((P : Measure Ω).map Y), 0 ≤ y := by
    -- Proof comment: a nonnegative test function integrates to a nonnegative real under every
    -- random measure.
    rw [ae_map_iff hY measurableSet_Ici]
    filter_upwards with ω
    exact MeasureTheory.integral_nonneg hg_nonneg
  rcases integrable_id_of_nonnegative_hasDerivAt_charFun_zero
      (μ := (P : Measure Ω).map Y) hDeriv hNonneg with ⟨hIntId, _⟩
  -- Proof comment: pull the integrable identity function on the pushed-forward law back along
  -- the stochastic integral random variable `Y`.
  simpa [Function.comp, Y] using
    (integrable_map_measure aestronglyMeasurable_id hY).1 hIntId

-- Route correction: instead of forcing a pointwise positive/negative-part decomposition under
-- each random measure `X ω`, control the signed stochastic integral by the nonnegative one built
-- from `|f|` and then read the mean directly from the derivative of the pushed-forward law.
/-- Companion to Corollary 24.15: item (i). If `X` is a Poisson point process with intensity `μ` and
`f ∈ L¹(μ)`, then the expectation of the stochastic integral `∫ f dX` is `∫ f dμ`. -/
theorem poissonPointProcess_integral_expectation_eq
    (P : ProbabilityMeasure Ω) (X : Ω → Measure E) (μ : Measure E) {f : E → ℝ}
    (hX : IsPoissonPointProcess P X μ) (hf : Integrable f μ) :
    ∫ ω, (∫ x, f x ∂ X ω) ∂(P : Measure Ω) = ∫ x, f x ∂μ := by
  let Y : Ω → ℝ := fun ω ↦ ∫ x, f x ∂ X ω
  let Yabs : Ω → ℝ := fun ω ↦ ∫ x, |f x| ∂ X ω
  have hY : AEMeasurable Y (P : Measure Ω) :=
    stochasticIntegral_aemeasurable P X μ hX hf
  have hYabs_int : Integrable Yabs (P : Measure Ω) :=
    stochasticIntegral_integrable_of_nonneg P X μ hX hf.norm fun _ ↦ abs_nonneg _
  have hY_int : Integrable Y (P : Measure Ω) := by
    -- Proof comment: the unsigned stochastic integral dominates the signed one pointwise, so the
    -- nonnegative `|f|` route upgrades the signed stochastic integral to an `L¹` random variable.
    refine Integrable.mono' hYabs_int hY.aestronglyMeasurable ?_
    filter_upwards with ω
    simpa [Y, Yabs] using (MeasureTheory.abs_integral_le_integral_abs (f := f) (μ := X ω))
  haveI : IsProbabilityMeasure ((P : Measure Ω).map Y) :=
    Measure.isProbabilityMeasure_map hY
  have hChar :
      MeasureTheory.charFun ((P : Measure Ω).map Y) =
        fun t : ℝ ↦
          Complex.exp (∫ x, (Complex.exp ((((t * f x) : ℝ) : ℂ) * Complex.I) - 1) ∂μ) := by
    funext t
    rw [MeasureTheory.charFun_apply_real, MeasureTheory.integral_map hY]
    · simpa [Y, mul_assoc, mul_left_comm, mul_comm] using hX hf t
    · fun_prop
  have hDeriv :
      HasDerivAt (MeasureTheory.charFun ((P : Measure Ω).map Y))
        (((∫ x, f x ∂μ : ℝ) : ℂ) * Complex.I) 0 := by
    -- Proof comment: the PPP characteristic-function identity identifies the derivative at `0`
    -- of the stochastic integral law with the derivative of the explicit Poisson exponent.
    simpa [hChar] using poissonCharacteristicExponent_hasDerivAt_zero μ hf
  have hIntId : Integrable id ((P : Measure Ω).map Y) := by
    -- Proof comment: transport the `L¹` control of `Y` to the pushed-forward law where the
    -- characteristic-function moment formula is stated.
    simpa [Function.comp, Y] using
      (integrable_map_measure aestronglyMeasurable_id hY).2 hY_int
  have hMemId : MemLp id 1 ((P : Measure Ω).map Y) := by
    simpa using (MeasureTheory.memLp_one_iff_integrable.2 hIntId)
  have hDerivIntegral :
      deriv (MeasureTheory.charFun ((P : Measure Ω).map Y)) 0 =
        Complex.I * (((∫ y, y ∂((P : Measure Ω).map Y) : ℝ) : ℂ)) := by
    -- Proof comment: Chapter 15 rewrites the derivative of the characteristic function of an
    -- integrable real law as `Complex.I` times its mean.
    simpa using
      (MeasureTheory.iteratedDeriv_charFun_zero
        (μ := ((P : Measure Ω).map Y)) (n := 1) (hint := by simpa using hMemId))
  have hMapIntegral :
      ∫ y, y ∂((P : Measure Ω).map Y) = ∫ x, f x ∂μ := by
    -- Proof comment: compare the two derivative formulas at `0` and cancel the common factor
    -- `Complex.I`.
    have hCompare :
        Complex.I * (((∫ y, y ∂((P : Measure Ω).map Y) : ℝ) : ℂ)) =
          (((∫ x, f x ∂μ : ℝ) : ℂ) * Complex.I) := by
      calc
        Complex.I * (((∫ y, y ∂((P : Measure Ω).map Y) : ℝ) : ℂ)) =
            deriv (MeasureTheory.charFun ((P : Measure Ω).map Y)) 0 := by
              symm
              exact hDerivIntegral
        _ = (((∫ x, f x ∂μ : ℝ) : ℂ) * Complex.I) := by
              simpa using hDeriv.deriv
    have hMul := congrArg (fun z : ℂ ↦ (-Complex.I) * z) hCompare
    have hComplex :
        (((∫ y, y ∂((P : Measure Ω).map Y) : ℝ) : ℂ)) =
          (((∫ x, f x ∂μ : ℝ) : ℂ)) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hMul
    exact_mod_cast hComplex
  calc
    ∫ ω, (∫ x, f x ∂ X ω) ∂(P : Measure Ω) = ∫ y, y ∂((P : Measure Ω).map Y) := by
      simpa [Y] using
        (MeasureTheory.integral_map hY
          (by fun_prop : AEStronglyMeasurable (fun y : ℝ ↦ y) ((P : Measure Ω).map Y))).symm
    _ = ∫ x, f x ∂μ := hMapIntegral

/-- Helper for Corollary 24.15: after centering by `∫ f dμ`, the stochastic-integral law has
characteristic function equal to the PPP exponent multiplied by the compensating phase. -/
private theorem centeredPoissonIntegral_charFun_eq
    (P : ProbabilityMeasure Ω) (X : Ω → Measure E) (μ : Measure E) {f : E → ℝ}
    (hX : IsPoissonPointProcess P X μ) (hf : Integrable f μ) :
    let Y : Ω → ℝ := fun ω ↦ ∫ x, f x ∂ X ω
    let m : ℝ := ∫ x, f x ∂μ
    let Z : Ω → ℝ := fun ω ↦ Y ω - m
    MeasureTheory.charFun ((P : Measure Ω).map Z) =
      fun t : ℝ ↦
        Complex.exp (-((((t * m) : ℝ) : ℂ) * Complex.I)) *
          Complex.exp (∫ x, (Complex.exp ((((t * f x) : ℝ) : ℂ) * Complex.I) - 1) ∂μ) := by
  let Y : Ω → ℝ := fun ω ↦ ∫ x, f x ∂ X ω
  let m : ℝ := ∫ x, f x ∂μ
  let Z : Ω → ℝ := fun ω ↦ Y ω - m
  have hY : AEMeasurable Y (P : Measure Ω) :=
    stochasticIntegral_aemeasurable P X μ hX hf
  have hZ : AEMeasurable Z (P : Measure Ω) := hY.sub_const m
  funext t
  rw [MeasureTheory.charFun_apply_real, MeasureTheory.integral_map hZ]
  · calc
      ∫ ω, Complex.exp ((t : ℂ) * (Z ω : ℂ) * Complex.I) ∂(P : Measure Ω)
          = ∫ ω,
              Complex.exp (-((t : ℂ) * (m : ℂ) * Complex.I)) *
                Complex.exp ((t : ℂ) * (Y ω : ℂ) * Complex.I) ∂(P : Measure Ω) := by
                  refine integral_congr_ae ?_
                  filter_upwards with ω
                  rw [← Complex.exp_add]
                  congr 1
                  simp [Y, Z, m, sub_eq_add_neg]
                  ring
      _ = Complex.exp (-((t : ℂ) * (m : ℂ) * Complex.I)) *
            ∫ ω, Complex.exp ((t : ℂ) * (Y ω : ℂ) * Complex.I) ∂(P : Measure Ω) := by
              exact integral_const_mul _ _
      _ = Complex.exp (-((t : ℂ) * (m : ℂ) * Complex.I)) *
            Complex.exp (∫ x, (Complex.exp ((((t * f x) : ℝ) : ℂ) * Complex.I) - 1) ∂μ) := by
              simpa [Y, m, mul_assoc, mul_left_comm, mul_comm] using hX hf t
      _ = Complex.exp (-(↑(t * m) * Complex.I)) *
            Complex.exp (∫ x, (Complex.exp ((((t * f x) : ℝ) : ℂ) * Complex.I) - 1) ∂μ) := by
              congr 1
              simp [m, mul_assoc, mul_left_comm, mul_comm]
  · fun_prop

/-- Helper for Corollary 24.15: the centered stochastic-integral law has zero first derivative at
the origin. -/
private theorem centeredPoissonIntegral_hasDerivAt_zero
    (P : ProbabilityMeasure Ω) (X : Ω → Measure E) (μ : Measure E) {f : E → ℝ}
    (hX : IsPoissonPointProcess P X μ) (hf : Integrable f μ) :
    let Z : Ω → ℝ := fun ω ↦ (∫ x, f x ∂ X ω) - ∫ x, f x ∂μ
    HasDerivAt (MeasureTheory.charFun ((P : Measure Ω).map Z)) 0 0 := by
  let m : ℝ := ∫ x, f x ∂μ
  let A : ℝ → ℂ := fun t ↦ Complex.exp ((((t * (-m)) : ℝ) : ℂ) * Complex.I)
  let B : ℝ → ℂ := fun t ↦
    Complex.exp (∫ x, (Complex.exp ((((t * f x) : ℝ) : ℂ) * Complex.I) - 1) ∂μ)
  let Z : Ω → ℝ := fun ω ↦ (∫ x, f x ∂ X ω) - m
  have hChar :
      MeasureTheory.charFun ((P : Measure Ω).map Z) = fun t : ℝ ↦ A t * B t := by
    -- Proof comment: rewrite the centered pushed-forward law using the compensating phase factor.
    simpa [A, B, Z, m, neg_mul, mul_assoc, mul_left_comm, mul_comm] using
      centeredPoissonIntegral_charFun_eq P X μ hX hf
  have hA :
      HasDerivAt A (-(((m : ℝ) : ℂ) * Complex.I)) 0 := by
    -- Proof comment: the deterministic centering phase contributes the negative mean derivative.
    let g : ℝ → ℂ := fun t ↦ (((t * (-m) : ℝ) : ℂ) * Complex.I)
    have hPhase :
        HasDerivAt g
          (-(((m : ℝ) : ℂ) * Complex.I)) 0 := by
      have hReal : HasDerivAt (fun t : ℝ ↦ t * (-m)) (-m) 0 := by
        simpa using hasDerivAt_mul_const (x := (0 : ℝ)) (-m)
      have hComplex :
          HasDerivAt (fun t : ℝ ↦ ((t * (-m) : ℝ) : ℂ)) ((-m : ℝ) : ℂ) 0 := by
        simpa using hReal.ofReal_comp
      simpa [g, mul_assoc, mul_left_comm, mul_comm] using hComplex.mul_const Complex.I
    have hExp : HasDerivAt (fun t : ℝ ↦ Complex.exp (g t)) (-(((m : ℝ) : ℂ) * Complex.I)) 0 := by
      simpa [g] using
        (HasDerivAt.comp (x := (0 : ℝ)) (h := g) (Complex.hasDerivAt_exp (g 0)) hPhase)
    simpa [A, g, mul_assoc, mul_left_comm, mul_comm] using
      hExp
  have hB :
      HasDerivAt B ((((m : ℝ) : ℂ) * Complex.I)) 0 := by
    -- Proof comment: the uncentered PPP exponent still differentiates to the mean term.
    simpa [B, m] using poissonCharacteristicExponent_hasDerivAt_zero μ hf
  have hA0 : A 0 = 1 := by simp [A]
  have hB0 : B 0 = 1 := by
    simp [B, poissonCharacteristicIntegral_zero]
  have hProd : HasDerivAt (fun t ↦ A t * B t) 0 0 := by
    -- Proof comment: the negative centering phase derivative cancels the positive mean derivative
    -- of the original PPP exponent exactly at `t = 0`.
    simpa [hA0, hB0, A, B, m, mul_assoc, mul_left_comm, mul_comm] using
      hA.mul hB
  -- Proof comment: transport the product-rule cancellation back to the actual centered law.
  dsimp [Z]
  rw [hChar]
  exact hProd

/-- Helper for Corollary 24.15: after centering by `∫ f dμ`, the pushed-forward law has second
characteristic-function derivative at `0` given by `-∫ f² dμ`. -/
private theorem centeredPoissonIntegral_secondDerivAt_zero
    (P : ProbabilityMeasure Ω) (X : Ω → Measure E) (μ : Measure E) {f : E → ℝ}
    (hX : IsPoissonPointProcess P X μ) (hf_int : Integrable f μ) (hf_sq : MemLp f 2 μ) :
    let Z : Ω → ℝ := fun ω ↦ (∫ x, f x ∂ X ω) - ∫ x, f x ∂μ
    HasDerivAt
      (fun t : ℝ ↦ deriv (MeasureTheory.charFun ((P : Measure Ω).map Z)) t)
      (-((∫ x, (f x) ^ 2 ∂μ : ℝ) : ℂ)) 0 := by
  let m : ℝ := ∫ x, f x ∂μ
  let A : ℝ → ℂ := fun t ↦ Complex.exp ((((t * (-m)) : ℝ) : ℂ) * Complex.I)
  let B : ℝ → ℂ := fun t ↦
    Complex.exp (∫ x, (Complex.exp ((((t * f x) : ℝ) : ℂ) * Complex.I) - 1) ∂μ)
  let Z : Ω → ℝ := fun ω ↦ (∫ x, f x ∂ X ω) - m
  let c : ℂ := -(((m : ℝ) : ℂ) * Complex.I)
  have hChar :
      MeasureTheory.charFun ((P : Measure Ω).map Z) = fun t : ℝ ↦ A t * B t := by
    -- Proof comment: reuse the centered characteristic-function factorization from the previous
    -- helper as the stable normal form for the second-derivative computation.
    simpa [A, B, Z, m, neg_mul, mul_assoc, mul_left_comm, mul_comm] using
      centeredPoissonIntegral_charFun_eq P X μ hX hf_int
  have hAt : ∀ t : ℝ, HasDerivAt A (c * A t) t := by
    intro t
    -- Proof comment: the deterministic centering phase is just an exponential with constant
    -- linear exponent, so its derivative is itself times the fixed coefficient `c`.
    let g : ℝ → ℂ := fun s ↦ (((s * (-m) : ℝ) : ℂ) * Complex.I)
    have hPhase :
        HasDerivAt g c t := by
      have hReal : HasDerivAt (fun s : ℝ ↦ s * (-m)) (-m) t := by
        simpa using hasDerivAt_mul_const (x := t) (-m)
      have hComplex :
          HasDerivAt (fun s : ℝ ↦ ((s * (-m) : ℝ) : ℂ)) ((-m : ℝ) : ℂ) t := by
        simpa using hReal.ofReal_comp
      simpa [g, c, mul_assoc, mul_left_comm, mul_comm] using hComplex.mul_const Complex.I
    simpa [A, g, c, mul_assoc, mul_left_comm, mul_comm] using
      (Complex.hasDerivAt_exp (g t)).comp t hPhase
  have hA : HasDerivAt A c 0 := by
    -- Proof comment: specialize the phase derivative at the origin, where the exponential is `1`.
    simpa [A, c] using hAt 0
  have hDerivAEq : deriv A = fun t ↦ c * A t := by
    -- Proof comment: record the explicit derivative of `A` once so the second derivative only
    -- sees a short product formula.
    funext t
    exact (hAt t).deriv
  have hSecondA : HasDerivAt (fun t : ℝ ↦ deriv A t) (c ^ 2) 0 := by
    -- Proof comment: differentiating `deriv A = c * A` one more time contributes the square of
    -- the deterministic phase coefficient.
    rw [Filter.EventuallyEq.hasDerivAt_iff
      (Filter.Eventually.of_forall fun t ↦ by rw [hDerivAEq])]
    simpa [hDerivAEq, A, c, pow_two, mul_assoc, mul_left_comm, mul_comm] using
      (hA.mul_const c)
  let bCoeff : ℝ → ℂ := fun t ↦
    (∫ x, ((f x : ℂ) * Complex.I) * Complex.exp ((((t * f x) : ℝ) : ℂ) * Complex.I) ∂μ) * B t
  have hBt : ∀ t : ℝ, HasDerivAt B (bCoeff t) t := by
    intro t
    -- Proof comment: the uncentered Poisson exponent differentiates at every frequency by the
    -- already-proved under-the-integral-sign formula for the exponent integral.
    simpa [B, bCoeff, mul_assoc, mul_left_comm, mul_comm] using
      (Complex.hasDerivAt_exp
        (∫ x, (Complex.exp ((((t * f x) : ℝ) : ℂ) * Complex.I) - 1) ∂μ)).comp t
        (poissonCharacteristicIntegral_hasDerivAt μ hf_int t)
  have hDerivBEq : deriv B = bCoeff := by
    -- Proof comment: freeze the explicit first derivative of `B` as a reusable normal form.
    funext t
    exact (hBt t).deriv
  have hB :
      HasDerivAt B ((((∫ x, f x ∂μ : ℝ) : ℂ) * Complex.I)) 0 := by
    -- Proof comment: the first derivative of the uncentered exponent is still the mean term.
    simpa [B, m] using poissonCharacteristicExponent_hasDerivAt_zero μ hf_int
  have hSecondB :
      HasDerivAt (fun t : ℝ ↦ deriv B t)
        (-((∫ x, (f x) ^ 2 ∂μ : ℝ) : ℂ) - (((m : ℝ) : ℂ) ^ 2)) 0 := by
    -- Proof comment: the second derivative of the uncentered exponent gives the raw second
    -- moment coefficient `-(∫ f²) - m²`.
    simpa [B, m] using poissonCharacteristicExponent_secondDerivAt_zero μ hf_int hf_sq
  have hA0 : A 0 = 1 := by simp [A]
  have hB0 : B 0 = 1 := by simp [B, poissonCharacteristicIntegral_zero]
  have hDerivA0 : deriv A 0 = c := by
    rw [hDerivAEq]
    simpa [hA0]
  have hDerivB0 : deriv B 0 = (((m : ℝ) : ℂ) * Complex.I) := by
    rw [hDerivBEq]
    calc
      bCoeff 0
          = (∫ x, ((f x : ℂ) * Complex.I) *
              Complex.exp ((((0 * f x) : ℝ) : ℂ) * Complex.I) ∂μ) * B 0 := by
                rfl
      _ = (((∫ x, f x ∂μ : ℝ) : ℂ) * Complex.I) * 1 := by
            rw [poissonCharacteristicIntegral_firstKernel_zero (μ := μ) (f := f), hB0]
      _ = (((m : ℝ) : ℂ) * Complex.I) := by simp [m]
  have hDerivEq :
      deriv (MeasureTheory.charFun ((P : Measure Ω).map Z)) =
        fun t ↦ deriv A t * B t + A t * deriv B t := by
    -- Proof comment: the derivative of the centered law is the product-rule expansion of the
    -- phase factor and the original Poisson exponent.
    funext t
    rw [hChar]
    calc
      deriv (fun s : ℝ ↦ A s * B s) t
          = (c * A t) * B t + A t * bCoeff t := by
              simpa [bCoeff, mul_assoc, mul_left_comm, mul_comm] using ((hAt t).mul (hBt t)).deriv
      _ = deriv A t * B t + A t * deriv B t := by rw [hDerivAEq, hDerivBEq]
  have hSum :
      HasDerivAt
        (fun t ↦ deriv A t * B t + A t * deriv B t)
        (c ^ 2 + c * (((m : ℝ) : ℂ) * Complex.I) +
          (c * (((m : ℝ) : ℂ) * Complex.I) +
            (-((∫ x, (f x) ^ 2 ∂μ : ℝ) : ℂ) - (((m : ℝ) : ℂ) ^ 2)))) 0 := by
    -- Proof comment: combine the two product-rule branches and evaluate all order-one data at
    -- `0`, where both exponentials equal `1`.
    have hTerm1 :
        HasDerivAt (fun t ↦ deriv A t * B t)
          (c ^ 2 * B 0 + deriv A 0 * (((m : ℝ) : ℂ) * Complex.I)) 0 := by
      simpa using hSecondA.mul hB
    have hTerm2 :
        HasDerivAt (fun t ↦ A t * deriv B t)
          (c * deriv B 0 + A 0 *
            (-((∫ x, (f x) ^ 2 ∂μ : ℝ) : ℂ) - (((m : ℝ) : ℂ) ^ 2))) 0 := by
      simpa using hA.mul hSecondB
    simpa [hA0, hB0, hDerivA0, hDerivB0, mul_assoc, mul_left_comm, mul_comm] using
      hTerm1.add hTerm2
  have hCoeff :
      c ^ 2 + c * (((m : ℝ) : ℂ) * Complex.I) +
          (c * (((m : ℝ) : ℂ) * Complex.I) +
            (-((∫ x, (f x) ^ 2 ∂μ : ℝ) : ℂ) - (((m : ℝ) : ℂ) ^ 2))) =
        -((∫ x, (f x) ^ 2 ∂μ : ℝ) : ℂ) := by
    -- Proof comment: the two mixed terms from centering cancel the extra squared-mean term from
    -- the raw second derivative exactly, leaving only `-∫ f² dμ`.
    simp [c, pow_two, mul_assoc, mul_left_comm, mul_comm]
    have hI :
        -(Complex.I * (Complex.I * (((m : ℝ) : ℂ) * (((m : ℝ) : ℂ))))) =
          (((m : ℝ) : ℂ) * (((m : ℝ) : ℂ))) := by
      calc
        -(Complex.I * (Complex.I * (((m : ℝ) : ℂ) * (((m : ℝ) : ℂ)))))
            = -((Complex.I * Complex.I) * (((m : ℝ) : ℂ) * (((m : ℝ) : ℂ)))) := by ring
        _ = -((-1 : ℂ) * (((m : ℝ) : ℂ) * (((m : ℝ) : ℂ)))) := by simp [Complex.I_sq]
        _ = (((m : ℝ) : ℂ) * (((m : ℝ) : ℂ))) := by ring
    rw [hI]
    ring
  -- Proof comment: transport the simplified product-rule derivative back to the actual centered
  -- characteristic function.
  dsimp [Z]
  rw [Filter.EventuallyEq.hasDerivAt_iff
    (Filter.Eventually.of_forall fun t ↦ by rw [hDerivEq])]
  exact hSum.congr_deriv hCoeff

/-- Helper for Corollary 24.15: for a real probability law, the positive sine kernel integral is
the corresponding quadratic quotient of the real part of the characteristic function. -/
private theorem squareKernelIntegral_eq_charFunQuotient
    {ν : Measure ℝ} [IsProbabilityMeasure ν] {t : ℝ} (ht : t ≠ 0) :
    ∫ y, ((2 * Real.sin (t * y / 2)) / t) ^ 2 ∂ν =
      2 * (1 - Complex.re (MeasureTheory.charFun ν t)) / t ^ 2 := by
  have hPhaseInt :
      Integrable (fun y : ℝ ↦ Complex.exp ((((t * y) : ℝ) : ℂ) * Complex.I)) ν := by
    -- Proof comment: the oscillatory phase has norm `1`, so it is integrable on the probability
    -- space.
    refine Integrable.mono' (integrable_const (1 : ℝ)) ?_ ?_
    · fun_prop
    · filter_upwards with y
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (Complex.norm_exp_ofReal_mul_I (t * y)).le
  have hCosInt : Integrable (fun y : ℝ ↦ Real.cos (t * y)) ν := by
    -- Proof comment: `cos` is uniformly bounded by `1`, so it is integrable on every probability
    -- space.
    refine Integrable.mono' (integrable_const (1 : ℝ)) ?_ ?_
    · fun_prop
    · filter_upwards with y
      exact (Real.abs_cos_le_one (t * y))
  have hReChar :
      Complex.re (MeasureTheory.charFun ν t) = ∫ y, Real.cos (t * y) ∂ν := by
    -- Proof comment: taking real parts under the characteristic-function integral replaces the
    -- complex phase by `cos`.
    rw [MeasureTheory.charFun_apply_real]
    have hPhaseInt' :
        Integrable (fun y : ℝ ↦ Complex.exp (((t : ℂ) * (y : ℂ)) * Complex.I)) ν := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hPhaseInt
    calc
      Complex.re (∫ y : ℝ, Complex.exp (((t : ℂ) * (y : ℂ)) * Complex.I) ∂ν)
          = ∫ y : ℝ, Complex.re (Complex.exp (((t : ℂ) * (y : ℂ)) * Complex.I)) ∂ν := by
              simpa using
                (integral_re
                  (μ := ν)
                  (f := fun y : ℝ ↦ Complex.exp (((t : ℂ) * (y : ℂ)) * Complex.I))
                  hPhaseInt').symm
      _ = ∫ y, Real.cos (t * y) ∂ν := by
            refine integral_congr_ae ?_
            filter_upwards with y
            simpa [mul_assoc, mul_left_comm, mul_comm] using Complex.exp_ofReal_mul_I_re (t * y)
  have hKernel :
      (fun y : ℝ ↦ ((2 * Real.sin (t * y / 2)) / t) ^ 2) =
        fun y : ℝ ↦ (2 / t ^ 2) * (1 - Real.cos (t * y)) := by
    funext y
    let a : ℝ := t * y / 2
    calc
      ((2 * Real.sin (t * y / 2)) / t) ^ 2 = ((2 * Real.sin (t * y / 2)) ^ 2) / t ^ 2 := by
        rw [div_pow]
      _ = (4 * Real.sin a ^ 2) / t ^ 2 := by
        have hNum : ((2 * Real.sin (t * y / 2)) ^ 2) = 4 * Real.sin a ^ 2 := by
          simp [pow_two, a]
          ring
        rw [hNum]
      _ = (2 * (1 - Real.cos (t * y))) / t ^ 2 := by
        have hTrig : 4 * Real.sin a ^ 2 = 2 * (1 - Real.cos (t * y)) := by
          rw [show Real.cos (t * y) = Real.cos (2 * a) by simp [a, two_mul, mul_assoc]]
          rw [Real.cos_two_mul]
          nlinarith [Real.sin_sq_add_cos_sq a]
        rw [hTrig]
      _ = (2 / t ^ 2) * (1 - Real.cos (t * y)) := by
        field_simp [pow_two]
  calc
    ∫ y, ((2 * Real.sin (t * y / 2)) / t) ^ 2 ∂ν
        = ∫ y, (2 / t ^ 2) * (1 - Real.cos (t * y)) ∂ν := by
            rw [hKernel]
    _ = (2 / t ^ 2) * ∫ y, (1 - Real.cos (t * y)) ∂ν := by
          rw [integral_const_mul]
    _ = (2 / t ^ 2) * (∫ y, (1 : ℝ) ∂ν - ∫ y, Real.cos (t * y) ∂ν) := by
          rw [integral_sub (integrable_const (1 : ℝ)) hCosInt]
    _ = (2 / t ^ 2) * (1 - Complex.re (MeasureTheory.charFun ν t)) := by
          simp [hReChar]
    _ = 2 * (1 - Complex.re (MeasureTheory.charFun ν t)) / t ^ 2 := by
          field_simp [pow_two, ht]

/-- Helper for Corollary 24.15: away from a zero mesh, the basic sine quotient is `y * sinc`. -/
private theorem squareKernelBase_eq_mul_sinc {t y : ℝ} (ht : t ≠ 0) :
    (2 * Real.sin (t * y / 2)) / t = y * Real.sinc (t * y / 2) := by
  by_cases hy : y = 0
  · -- Proof comment: at `y = 0`, both sides collapse to `0`.
    subst hy
    simp [Real.sinc_zero]
  · -- Proof comment: away from `0`, unfold `sinc` once and clear the mesh denominator.
    have hty : t * y / 2 ≠ 0 := by
      refine div_ne_zero ?_ (by norm_num)
      exact mul_ne_zero ht hy
    rw [Real.sinc_of_ne_zero hty]
    field_simp [ht, hy]

/-- Helper for Corollary 24.15: each square sine kernel is integrable on a probability law
because `|sin| ≤ 1` bounds it by a mesh-dependent constant. -/
private theorem squareKernel_integrable
    {ν : Measure ℝ} [IsProbabilityMeasure ν] (t : ℝ) :
    Integrable (fun y : ℝ ↦ ((2 * Real.sin (t * y / 2)) / t) ^ 2) ν := by
  refine Integrable.of_bound ?_ ((2 / |t|) ^ 2) ?_
  · -- Proof comment: the kernel is a continuous real function of `y`.
    simpa using
      (by
        fun_prop :
          AEStronglyMeasurable (fun y : ℝ ↦ ((2 * Real.sin (t * y / 2)) / t) ^ 2) ν)
  · filter_upwards with y
    by_cases ht : t = 0
    · -- Proof comment: at zero mesh the kernel is identically zero.
      subst ht
      simp
    · -- Proof comment: the sine factor is bounded by `1`, so the whole quotient is bounded by
      -- `2 / |t|`, and squaring preserves the inequality.
      have hsin :
          2 * |Real.sin (t * y / 2)| ≤ 2 := by
        nlinarith [Real.abs_sin_le_one (t * y / 2)]
      have habs :
          |(2 * Real.sin (t * y / 2)) / t| ≤ 2 / |t| := by
        calc
          |(2 * Real.sin (t * y / 2)) / t|
              = (2 * |Real.sin (t * y / 2)|) / |t| := by
                  rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
          _ ≤ 2 / |t| := by
                exact div_le_div_of_nonneg_right hsin (abs_pos.mpr ht).le
      calc
        ‖(((2 * Real.sin (t * y / 2)) / t) ^ 2 : ℝ)‖
            = |((2 * Real.sin (t * y / 2)) / t) ^ 2| := by rw [Real.norm_eq_abs]
        _ = |(2 * Real.sin (t * y / 2)) / t| ^ 2 := by rw [abs_pow]
        _ ≤ (2 / |t|) ^ 2 := by
              exact pow_le_pow_left₀ (abs_nonneg _) habs 2

/-- Helper for Corollary 24.15: along the reciprocal mesh, the square sine kernels converge
pointwise to `y²`. -/
private theorem squareKernel_pointwise_tendsto_sq (y : ℝ) :
    Tendsto
      (fun n : ℕ ↦
        ((2 * Real.sin ((((n + 1 : ℝ)⁻¹) * y) / 2)) / ((n + 1 : ℝ)⁻¹)) ^ 2)
      atTop
      (nhds (y ^ 2)) := by
  let tSeq : ℕ → ℝ := fun n ↦ ((n + 1 : ℝ)⁻¹)
  have hSeqEq :
      (fun n : ℕ ↦ ((2 * Real.sin (tSeq n * y / 2)) / tSeq n) ^ 2) =
        fun n : ℕ ↦ (y * Real.sinc (tSeq n * y / 2)) ^ 2 := by
    funext n
    have ht : tSeq n ≠ 0 := by
      dsimp [tSeq]
      positivity
    simpa using congrArg (fun z : ℝ ↦ z ^ 2) (squareKernelBase_eq_mul_sinc (y := y) ht)
  have htSeq_zero : Tendsto tSeq atTop (nhds 0) := by
    -- Proof comment: the reciprocal mesh tends to the origin.
    simpa [tSeq, one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (nhds (0 : ℝ)))
  have hSinc :
      Tendsto (fun n : ℕ ↦ Real.sinc (tSeq n * y / 2)) atTop (nhds 1) := by
    -- Proof comment: `sinc` is continuous at `0`, and the mesh-scaled argument tends to `0`.
    have hArg : Tendsto (fun n : ℕ ↦ tSeq n * y / 2) atTop (nhds 0) := by
      have hCont : Continuous fun t : ℝ ↦ t * y / 2 := by
        fun_prop
      simpa using hCont.continuousAt.tendsto.comp htSeq_zero
    simpa [Real.sinc_zero] using Real.continuous_sinc.continuousAt.tendsto.comp hArg
  have hBase :
      Tendsto (fun n : ℕ ↦ y * Real.sinc (tSeq n * y / 2)) atTop (nhds y) := by
    -- Proof comment: multiplying by a `sinc` factor tending to `1` recovers `y`.
    simpa using tendsto_const_nhds.mul hSinc
  have hPow :
      Tendsto (fun n : ℕ ↦ (y * Real.sinc (tSeq n * y / 2)) ^ 2) atTop (nhds (y ^ 2)) := by
    -- Proof comment: squaring is continuous on `ℝ`.
    have hCont : Continuous fun z : ℝ ↦ z ^ 2 := by
      fun_prop
    simpa using hCont.continuousAt.tendsto.comp hBase
  rw [hSeqEq]
  exact hPow

/-- Helper for Corollary 24.15: taking real parts commutes with `deriv` for differentiable
complex-valued functions on `ℝ`. -/
private theorem deriv_re_comp_eq {g : ℝ → ℂ} {x : ℝ} (hg : DifferentiableAt ℝ g x) :
    deriv (fun t : ℝ ↦ Complex.re (g t)) x = Complex.re (deriv g x) := by
  -- Proof comment: `Complex.re` is continuous linear, so its derivative is itself and may be
  -- composed directly with the derivative of `g`.
  have hDeriv :
      HasDerivAt (fun t : ℝ ↦ Complex.re (g t)) (Complex.re (deriv g x)) x := by
    simpa using (Complex.reCLM.hasFDerivAt.comp x hg.hasDerivAt.hasFDerivAt).hasDerivAt
  exact hDeriv.deriv

/-- Helper for Corollary 24.15: the real part of the centered pushed-forward characteristic
function is differentiable at every frequency. -/
private theorem centeredPoissonIntegral_reCharFun_differentiableAt
    (P : ProbabilityMeasure Ω) (X : Ω → Measure E) (μ : Measure E) {f : E → ℝ}
    (hX : IsPoissonPointProcess P X μ) (hf_int : Integrable f μ) :
    let Z : Ω → ℝ := fun ω ↦ (∫ x, f x ∂ X ω) - ∫ x, f x ∂μ
    let ν : Measure ℝ := (P : Measure Ω).map Z
    ∀ t : ℝ, DifferentiableAt ℝ (fun s : ℝ ↦ Complex.re (MeasureTheory.charFun ν s)) t := by
  let m : ℝ := ∫ x, f x ∂μ
  let Y : Ω → ℝ := fun ω ↦ ∫ x, f x ∂ X ω
  let Z : Ω → ℝ := fun ω ↦ Y ω - m
  let ν : Measure ℝ := (P : Measure Ω).map Z
  let A : ℝ → ℂ := fun t ↦ Complex.exp (-((((t * m) : ℝ) : ℂ) * Complex.I))
  let B : ℝ → ℂ := fun t ↦
    Complex.exp (∫ x, (Complex.exp ((((t * f x) : ℝ) : ℂ) * Complex.I) - 1) ∂μ)
  have hY : AEMeasurable Y (P : Measure Ω) :=
    stochasticIntegral_aemeasurable P X μ hX hf_int
  have hZ : AEMeasurable Z (P : Measure Ω) := hY.sub_const m
  haveI : IsProbabilityMeasure ν := by
    dsimp [ν]
    exact Measure.isProbabilityMeasure_map hZ
  have hChar :
      MeasureTheory.charFun ν = fun t : ℝ ↦ A t * B t := by
    -- Proof comment: reuse the centered characteristic-function factorization as the stable
    -- differentiability normal form.
    simpa [ν, Z, Y, m, A, B, neg_mul, mul_assoc, mul_left_comm, mul_comm] using
      centeredPoissonIntegral_charFun_eq P X μ hX hf_int
  refine fun s : ℝ ↦ ?_
  have hA :
      DifferentiableAt ℝ A s := by
    -- Proof comment: the centering phase is a complex exponential of a linear real function.
    have hPhase :
        HasDerivAt (fun r : ℝ ↦ -((((r * m) : ℝ) : ℂ) * Complex.I))
          (-((m : ℂ) * Complex.I)) s := by
      have hReal : HasDerivAt (fun r : ℝ ↦ r * m) m s := by
        simpa using hasDerivAt_mul_const (x := s) m
      have hComplex :
          HasDerivAt (fun r : ℝ ↦ ((r * m : ℝ) : ℂ)) (m : ℂ) s := by
        simpa using hReal.ofReal_comp
      simpa [mul_assoc, mul_left_comm, mul_comm] using (hComplex.mul_const Complex.I).neg
    simpa [A] using ((Complex.hasDerivAt_exp _).comp s hPhase).differentiableAt
  have hB :
      DifferentiableAt ℝ B s := by
    -- Proof comment: the PPP exponent is differentiable everywhere because the integral exponent
    -- is differentiable by the under-the-integral-sign lemma proved earlier.
    have hExpB :
        HasDerivAt B
          (Complex.exp
              (∫ x, (Complex.exp ((((s * f x) : ℝ) : ℂ) * Complex.I) - 1) ∂μ) *
            ∫ x, ((f x : ℂ) * Complex.I) *
              Complex.exp ((((s * f x) : ℝ) : ℂ) * Complex.I) ∂μ) s := by
      simpa [B] using
        ((Complex.hasDerivAt_exp _).comp s (poissonCharacteristicIntegral_hasDerivAt μ hf_int s))
    exact hExpB.differentiableAt
  have hCharDiff :
      DifferentiableAt ℝ (MeasureTheory.charFun ν) s := by
    -- Proof comment: multiply the differentiable phase factor and PPP exponent.
    rw [hChar]
    simpa using hA.mul hB
  -- Proof comment: the real part of a differentiable complex function is differentiable.
  simpa using Complex.reCLM.differentiableAt.comp s hCharDiff

/-- Helper for Corollary 24.15: the quadratic defect of the centered characteristic function is
exactly the Poisson variance coefficient `∫ f² dμ`. -/
private theorem centeredCharFun_realQuotient_tendsto
    (P : ProbabilityMeasure Ω) (X : Ω → Measure E) (μ : Measure E) {f : E → ℝ}
    (hX : IsPoissonPointProcess P X μ) (hf_int : Integrable f μ) (hf_sq : MemLp f 2 μ) :
    let Z : Ω → ℝ := fun ω ↦ (∫ x, f x ∂ X ω) - ∫ x, f x ∂μ
    let ν : Measure ℝ := (P : Measure Ω).map Z
    let σ2 : ℝ := ∫ x, (f x) ^ 2 ∂μ
    Tendsto
      (fun t : ℝ ↦ 2 * (1 - Complex.re (MeasureTheory.charFun ν t)) / t ^ 2)
      (nhdsWithin (0 : ℝ) ({0}ᶜ))
      (nhds σ2) := by
  let m : ℝ := ∫ x, f x ∂μ
  let Y : Ω → ℝ := fun ω ↦ ∫ x, f x ∂ X ω
  let Z : Ω → ℝ := fun ω ↦ Y ω - m
  let ν : Measure ℝ := (P : Measure Ω).map Z
  let σ2 : ℝ := ∫ x, (f x) ^ 2 ∂μ
  let u : ℝ → ℝ := fun t ↦ Complex.re (MeasureTheory.charFun ν t)
  have hY : AEMeasurable Y (P : Measure Ω) :=
    stochasticIntegral_aemeasurable P X μ hX hf_int
  have hZ : AEMeasurable Z (P : Measure Ω) := hY.sub_const m
  haveI : IsProbabilityMeasure ν := by
    dsimp [ν]
    exact Measure.isProbabilityMeasure_map hZ
  have hUDiff :
      ∀ t : ℝ, DifferentiableAt ℝ u t := by
    -- Proof comment: the centered law already has a differentiable real-part characteristic
    -- function at every frequency.
    intro t
    simpa [u, ν, Z, Y, m] using
      centeredPoissonIntegral_reCharFun_differentiableAt P X μ hX hf_int t
  have hCharDiff :
      ∀ t : ℝ, DifferentiableAt ℝ (MeasureTheory.charFun ν) t := by
    intro t
    let A : ℝ → ℂ := fun s ↦ Complex.exp (-((((s * m) : ℝ) : ℂ) * Complex.I))
    let B : ℝ → ℂ := fun s ↦
      Complex.exp (∫ x, (Complex.exp ((((s * f x) : ℝ) : ℂ) * Complex.I) - 1) ∂μ)
    have hChar :
        MeasureTheory.charFun ν = fun s : ℝ ↦ A s * B s := by
      -- Proof comment: keep the centered characteristic function in the product normal form used
      -- throughout the first- and second-derivative computations.
      simpa [ν, Z, Y, m, A, B, neg_mul, mul_assoc, mul_left_comm, mul_comm] using
        centeredPoissonIntegral_charFun_eq P X μ hX hf_int
    have hA :
        DifferentiableAt ℝ A t := by
      -- Proof comment: the deterministic centering phase is differentiable everywhere.
      have hPhase :
          HasDerivAt (fun s : ℝ ↦ -((((s * m) : ℝ) : ℂ) * Complex.I))
            (-((m : ℂ) * Complex.I)) t := by
        have hReal : HasDerivAt (fun s : ℝ ↦ s * m) m t := by
          simpa using hasDerivAt_mul_const (x := t) m
        have hComplex :
            HasDerivAt (fun s : ℝ ↦ ((s * m : ℝ) : ℂ)) (m : ℂ) t := by
          simpa using hReal.ofReal_comp
        simpa [mul_assoc, mul_left_comm, mul_comm] using (hComplex.mul_const Complex.I).neg
      simpa [A] using ((Complex.hasDerivAt_exp _).comp t hPhase).differentiableAt
    have hB :
        DifferentiableAt ℝ B t := by
      -- Proof comment: the explicit PPP exponent is differentiable at every frequency.
      have hExpB :
          HasDerivAt B
            (Complex.exp
                (∫ x, (Complex.exp ((((t * f x) : ℝ) : ℂ) * Complex.I) - 1) ∂μ) *
              ∫ x, ((f x : ℂ) * Complex.I) *
                Complex.exp ((((t * f x) : ℝ) : ℂ) * Complex.I) ∂μ) t := by
        simpa [B] using
          ((Complex.hasDerivAt_exp _).comp t
            (poissonCharacteristicIntegral_hasDerivAt μ hf_int t))
      exact hExpB.differentiableAt
    rw [hChar]
    simpa using hA.mul hB
  have hCenteredDeriv :
      HasDerivAt (MeasureTheory.charFun ν) 0 0 := by
    simpa [ν, Z, Y, m] using centeredPoissonIntegral_hasDerivAt_zero P X μ hX hf_int
  have hCenteredSecondDeriv :
      HasDerivAt (fun t : ℝ ↦ deriv (MeasureTheory.charFun ν) t) (-((σ2 : ℝ) : ℂ)) 0 := by
    simpa [ν, Z, Y, m, σ2] using centeredPoissonIntegral_secondDerivAt_zero P X μ hX hf_int hf_sq
  have hDerivEq :
      deriv u = fun t : ℝ ↦ Complex.re (deriv (MeasureTheory.charFun ν) t) := by
    -- Proof comment: identify the derivative of the real part with the real part of the complex
    -- derivative once, so the second-derivative data transports cleanly.
    funext t
    exact deriv_re_comp_eq (hCharDiff t)
  have hDerivZero : deriv u 0 = 0 := by
    have hReDeriv :
        HasDerivAt u 0 0 := by
      simpa [u] using (Complex.reCLM.hasFDerivAt.comp 0 hCenteredDeriv.hasFDerivAt).hasDerivAt
    exact hReDeriv.deriv
  have hSecondU :
      HasDerivAt (fun t : ℝ ↦ deriv u t) (-σ2) 0 := by
    -- Proof comment: transport the centered complex second-derivative computation through
    -- `Complex.re`.
    rw [hDerivEq]
    simpa [σ2] using
      (Complex.reCLM.hasFDerivAt.comp 0 hCenteredSecondDeriv.hasFDerivAt).hasDerivAt
  have hDerivDiv :
      Tendsto (fun t : ℝ ↦ deriv u t / t) (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds (-σ2)) := by
    -- Proof comment: the derivative of `u` has slope `-σ2` at the origin, and `deriv u 0 = 0`.
    simpa [hDerivZero, div_eq_mul_inv, sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm] using
      hSecondU.tendsto_slope_zero
  have hff' :
      ∀ᶠ x in nhdsWithin (0 : ℝ) ({0}ᶜ), HasDerivAt (fun t : ℝ ↦ 1 - u t) (-deriv u x) x := by
    -- Proof comment: the numerator inherits differentiability from `u`.
    refine Filter.Eventually.of_forall ?_
    intro x
    simpa using (hUDiff x).hasDerivAt.const_sub (1 : ℝ)
  have hgg' :
      ∀ᶠ x in nhdsWithin (0 : ℝ) ({0}ᶜ), HasDerivAt (fun t : ℝ ↦ t ^ 2 / 2) x x := by
    -- Proof comment: the quadratic denominator has derivative `t`.
    refine Filter.Eventually.of_forall ?_
    intro x
    simpa [pow_two, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      ((hasDerivAt_pow 2 x).div_const (2 : ℝ))
  have hg' : ∀ᶠ x in nhdsWithin (0 : ℝ) ({0}ᶜ), x ≠ 0 := by
    -- Proof comment: every point in the punctured-neighborhood filter is already nonzero.
    exact self_mem_nhdsWithin
  have hfa :
      Tendsto (fun t : ℝ ↦ 1 - u t) (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds 0) := by
    -- Proof comment: continuity of `u` at `0` gives the vanishing numerator.
    have hTendstoU :
        Tendsto u (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds 1) := by
      simpa [u, MeasureTheory.charFun_zero] using
        (hUDiff 0).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    simpa using
      (show Tendsto (fun t : ℝ ↦ (1 : ℝ) - u t) (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds (1 - 1)) from
        tendsto_const_nhds.sub hTendstoU)
  have hga :
      Tendsto (fun t : ℝ ↦ t ^ 2 / 2) (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds 0) := by
    -- Proof comment: the quadratic denominator itself tends to `0`.
    have hCont : ContinuousAt (fun t : ℝ ↦ t ^ 2 / 2) 0 := by
      fun_prop
    simpa using hCont.tendsto.mono_left nhdsWithin_le_nhds
  have hdiv :
      Tendsto (fun t : ℝ ↦ (-deriv u t) / t) (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds σ2) := by
    -- Proof comment: negate the derivative quotient limit from the previous step.
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hDerivDiv.neg
  have hQuot :
      Tendsto (fun t : ℝ ↦ (1 - u t) / (t ^ 2 / 2))
        (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds σ2) := by
    -- Proof comment: one L'Hospital step turns the centered quadratic defect into the derivative
    -- quotient already identified above.
    exact HasDerivAt.lhopital_zero_nhdsNE hff' hgg' hg' hfa hga hdiv
  have hEq :
      (fun t : ℝ ↦ (1 - u t) / (t ^ 2 / 2)) =ᶠ[nhdsWithin (0 : ℝ) ({0}ᶜ)]
        fun t : ℝ ↦ 2 * (1 - u t) / t ^ 2 := by
    -- Proof comment: away from `0`, clearing the denominator rewrites the L'Hospital quotient in
    -- the exact kernel-normalization surface.
    filter_upwards [self_mem_nhdsWithin] with t ht
    calc
      (1 - u t) / (t ^ 2 / 2) = (1 - u t) * (2 / t ^ 2) := by
        field_simp [pow_two, ht]
      _ = 2 * (1 - u t) / t ^ 2 := by ring
  simpa [ν, Z, Y, m, σ2, u] using hQuot.congr' hEq

/-- Helper for Corollary 24.15: the reciprocal mesh tends to `0` through nonzero real points. -/
private theorem reciprocalMesh_tendsto_punctured_zero :
    Tendsto (fun n : ℕ ↦ ((n + 1 : ℝ)⁻¹)) atTop (nhdsWithin (0 : ℝ) ({0}ᶜ)) := by
  -- Proof comment: the reciprocal mesh converges to `0`, and every mesh point is already
  -- nonzero.
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      (fun n : ℕ ↦ ((n + 1 : ℝ)⁻¹)) ?_ ?_
  · simpa [one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (nhds (0 : ℝ)))
  · exact Filter.Eventually.of_forall fun n ↦ by
      have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
      exact inv_ne_zero hn

/-- Helper for Corollary 24.15: the centered pushed-forward law has reciprocal-mesh square-kernel
integrals tending to the Poisson second-moment coefficient `∫ f² dμ`. -/
private theorem centeredPoissonIntegral_reciprocalKernelIntegral_tendsto
    (P : ProbabilityMeasure Ω) (X : Ω → Measure E) (μ : Measure E) {f : E → ℝ}
    (hX : IsPoissonPointProcess P X μ) (hf_int : Integrable f μ) (hf_sq : MemLp f 2 μ) :
    let Z : Ω → ℝ := fun ω ↦ (∫ x, f x ∂ X ω) - ∫ x, f x ∂μ
    let ν : Measure ℝ := (P : Measure Ω).map Z
    let σ2 : ℝ := ∫ x, (f x) ^ 2 ∂μ
    Tendsto
      (fun n : ℕ ↦
        ∫ y, ((2 * Real.sin ((((n + 1 : ℝ)⁻¹) * y) / 2)) / ((n + 1 : ℝ)⁻¹)) ^ 2 ∂ν)
      atTop
      (nhds σ2) := by
  let m : ℝ := ∫ x, f x ∂μ
  let Y : Ω → ℝ := fun ω ↦ ∫ x, f x ∂ X ω
  let Z : Ω → ℝ := fun ω ↦ Y ω - m
  let ν : Measure ℝ := (P : Measure Ω).map Z
  let σ2 : ℝ := ∫ x, (f x) ^ 2 ∂μ
  have hY : AEMeasurable Y (P : Measure Ω) :=
    stochasticIntegral_aemeasurable P X μ hX hf_int
  have hZ : AEMeasurable Z (P : Measure Ω) := hY.sub_const m
  haveI : IsProbabilityMeasure ν := by
    dsimp [ν]
    exact Measure.isProbabilityMeasure_map hZ
  have hQuot :
      Tendsto
        (fun t : ℝ ↦ 2 * (1 - Complex.re (MeasureTheory.charFun ν t)) / t ^ 2)
        (nhdsWithin (0 : ℝ) ({0}ᶜ))
        (nhds σ2) := by
    -- Proof comment: first package the centered second-derivative data into the exact real-part
    -- quadratic quotient.
    simpa [ν, Z, Y, m, σ2] using
      centeredCharFun_realQuotient_tendsto P X μ hX hf_int hf_sq
  have hAlongMesh :
      Tendsto
        (fun n : ℕ ↦
          2 * (1 - Complex.re (MeasureTheory.charFun ν (((n + 1 : ℝ)⁻¹)))) /
            (((n + 1 : ℝ)⁻¹) ^ 2))
        atTop
        (nhds σ2) := by
    -- Proof comment: specialize the punctured-zero quotient limit along the reciprocal mesh.
    exact hQuot.comp reciprocalMesh_tendsto_punctured_zero
  have hEq :
      (fun n : ℕ ↦
        ∫ y, ((2 * Real.sin ((((n + 1 : ℝ)⁻¹) * y) / 2)) / ((n + 1 : ℝ)⁻¹)) ^ 2 ∂ν) =
        fun n : ℕ ↦
          2 * (1 - Complex.re (MeasureTheory.charFun ν (((n + 1 : ℝ)⁻¹)))) /
            (((n + 1 : ℝ)⁻¹) ^ 2) := by
    -- Proof comment: the kernel identity exactly matches the specialized quadratic quotient at
    -- each nonzero mesh point.
    funext n
    have ht : ((n + 1 : ℝ)⁻¹) ≠ 0 := by
      have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
      exact inv_ne_zero hn
    simpa using squareKernelIntegral_eq_charFunQuotient (ν := ν) (t := ((n + 1 : ℝ)⁻¹)) ht
  have hEqPoint :
      ∀ n : ℕ,
        2 * (1 - Complex.re (MeasureTheory.charFun ν (((n + 1 : ℝ)⁻¹)))) /
            (((n + 1 : ℝ)⁻¹) ^ 2) =
          ∫ y, ((2 * Real.sin ((((n + 1 : ℝ)⁻¹) * y) / 2)) / ((n + 1 : ℝ)⁻¹)) ^ 2 ∂ν := by
    intro n
    exact (congrFun hEq n).symm
  simpa [ν, Z, Y, m, σ2] using hAlongMesh.congr hEqPoint

-- Route correction: the new measurable-interface helper already puts the stochastic integral on a
-- genuine law surface, and the remaining blocker is the second-moment converse needed to turn the
-- new first/second derivative data into an `L²` statement on the pushed-forward law.
/-- Corollary 24.15 (2): item (ii). If `X` is a Poisson point process with intensity `μ` and
`f ∈ L²(μ) ∩ L¹(μ)`, then the variance of `∫ f dX` is `∫ f^2 dμ`. -/
theorem poissonPointProcess_integral_variance_eq
    (P : ProbabilityMeasure Ω) (X : Ω → Measure E) (μ : Measure E) {f : E → ℝ}
    (hX : IsPoissonPointProcess P X μ) (hf_int : Integrable f μ) (hf_sq : MemLp f 2 μ) :
    Var[fun ω ↦ ∫ x, f x ∂ X ω; (P : Measure Ω)] = ∫ x, (f x) ^ 2 ∂μ := by
  let Y : Ω → ℝ := fun ω ↦ ∫ x, f x ∂ X ω
  let m : ℝ := ∫ x, f x ∂μ
  let Z : Ω → ℝ := fun ω ↦ Y ω - m
  let ν : Measure ℝ := (P : Measure Ω).map Z
  let σ2 : ℝ := ∫ x, (f x) ^ 2 ∂μ
  let tSeq : ℕ → ℝ := fun n ↦ ((n + 1 : ℝ)⁻¹)
  have hY : AEMeasurable Y (P : Measure Ω) :=
    stochasticIntegral_aemeasurable P X μ hX hf_int
  have hZ : AEMeasurable Z (P : Measure Ω) := hY.sub_const m
  have hYsm : AEStronglyMeasurable Y (P : Measure Ω) := hY.aestronglyMeasurable
  haveI : IsProbabilityMeasure ν := by
    dsimp [ν]
    exact Measure.isProbabilityMeasure_map hZ
  have hMemId2 : MemLp id 2 ν := by
    have hKernelIntegralTendsto :
        Tendsto
          (fun n : ℕ ↦
            ∫ y, ((2 * Real.sin ((((n + 1 : ℝ)⁻¹) * y) / 2)) / ((n + 1 : ℝ)⁻¹)) ^ 2 ∂ν)
          atTop
          (nhds σ2) := by
      -- Proof comment: package the centered derivative computation into the exact reciprocal-kernel
      -- limit needed by the `L²` converse.
      simpa [ν, Z, Y, m, σ2] using
        centeredPoissonIntegral_reciprocalKernelIntegral_tendsto P X μ hX hf_int hf_sq
    have hSqIntegrable : Integrable (fun y : ℝ ↦ y ^ 2) ν := by
      -- Proof comment: Scheffé upgrades the nonnegative pointwise kernel convergence together
      -- with convergence of the kernel integrals to integrability of `y ↦ y²`.
      exact
        (scheffe_of_nonnegative_ae_tendsto
          (μ := ν)
          (fSeq := fun n y ↦
            ((2 * Real.sin ((((n + 1 : ℝ)⁻¹) * y) / 2)) / ((n + 1 : ℝ)⁻¹)) ^ 2)
          (f := fun y : ℝ ↦ y ^ 2)
          (I := σ2)
          (fun n ↦ squareKernel_integrable (ν := ν) ((n + 1 : ℝ)⁻¹))
          (fun n ↦ by
            filter_upwards with y
            exact sq_nonneg _)
          (Filter.Eventually.of_forall squareKernel_pointwise_tendsto_sq)
          hKernelIntegralTendsto).1
    -- Proof comment: convert integrability of `y²` into the `L²` statement for the identity.
    exact
      (MeasureTheory.memLp_two_iff_integrable_sq (μ := ν) measurable_id.aestronglyMeasurable).2
        hSqIntegrable
  -- Proof comment: once the centered law is in `L²`, the first and second derivatives of its
  -- characteristic function identify its mean and second moment.
  have hCenteredDeriv :
      HasDerivAt (MeasureTheory.charFun ν) 0 0 := by
    simpa [ν, Z, Y, m] using centeredPoissonIntegral_hasDerivAt_zero P X μ hX hf_int
  have hCenteredSecondDeriv :
      HasDerivAt (fun t : ℝ ↦ deriv (MeasureTheory.charFun ν) t) (-((σ2 : ℝ) : ℂ)) 0 := by
    simpa [ν, Z, Y, m, σ2] using centeredPoissonIntegral_secondDerivAt_zero P X μ hX hf_int hf_sq
  have hMemId1 : MemLp id 1 ν := by
    simpa using (MeasureTheory.memLp_one_iff_integrable.2 (hMemId2.integrable one_le_two))
  have hMemIdNat1 : MemLp id (1 : ℕ) ν := by
    simpa using hMemId1
  have hMeanZero :
      ∫ y, y ∂ν = 0 := by
    have hDerivIntegral :
        deriv (MeasureTheory.charFun ν) 0 =
          Complex.I * (((∫ y, y ∂ν : ℝ) : ℂ)) := by
      simpa using
        (MeasureTheory.iteratedDeriv_charFun_zero (μ := ν) (n := 1) (hint := hMemIdNat1))
    have hCompare :
        Complex.I * (((∫ y, y ∂ν : ℝ) : ℂ)) = 0 := by
      calc
        Complex.I * (((∫ y, y ∂ν : ℝ) : ℂ)) = deriv (MeasureTheory.charFun ν) 0 := by
          symm
          exact hDerivIntegral
        _ = 0 := by
          exact hCenteredDeriv.deriv
    have hMul := congrArg (fun z : ℂ ↦ (-Complex.I) * z) hCompare
    have hComplex : (((∫ y, y ∂ν : ℝ) : ℂ)) = 0 := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hMul
    exact_mod_cast hComplex
  have hSecondMoment :
      ∫ y, y ^ 2 ∂ν = σ2 := by
    have hDerivIntegral :
        deriv (fun t : ℝ ↦ deriv (MeasureTheory.charFun ν) t) 0 =
          -(((∫ y, y ^ 2 ∂ν : ℝ) : ℂ)) := by
      simpa [iteratedDeriv_succ, iteratedDeriv_one, pow_two, Complex.I_sq] using
        (MeasureTheory.iteratedDeriv_charFun_zero (μ := ν) (n := 2) (hint := hMemId2))
    have hCompare :
        -(((∫ y, y ^ 2 ∂ν : ℝ) : ℂ)) = -((σ2 : ℝ) : ℂ) := by
      calc
        -(((∫ y, y ^ 2 ∂ν : ℝ) : ℂ)) =
            deriv (fun t : ℝ ↦ deriv (MeasureTheory.charFun ν) t) 0 := by
              symm
              exact hDerivIntegral
        _ = -((σ2 : ℝ) : ℂ) := by
              exact hCenteredSecondDeriv.deriv
    have hComplex : (((∫ y, y ^ 2 ∂ν : ℝ) : ℂ)) = ((σ2 : ℝ) : ℂ) := by
      simpa using congrArg Neg.neg hCompare
    exact_mod_cast hComplex
  have hVarNu : Var[id; ν] = σ2 := by
    calc
      Var[id; ν] = ∫ y, y ^ 2 ∂ν := by
        exact ProbabilityTheory.variance_of_integral_eq_zero measurable_id.aemeasurable hMeanZero
      _ = σ2 := hSecondMoment
  have hVarZ : Var[Z; (P : Measure Ω)] = σ2 := by
    calc
      Var[Z; (P : Measure Ω)] = Var[id; ν] := by
        symm
        simpa [ν] using (ProbabilityTheory.variance_id_map (μ := (P : Measure Ω)) (X := Z) hZ)
      _ = σ2 := hVarNu
  calc
    Var[fun ω ↦ ∫ x, f x ∂ X ω; (P : Measure Ω)] = Var[Z; (P : Measure Ω)] := by
      simpa [Y, Z, m] using (ProbabilityTheory.variance_sub_const hYsm m).symm
    _ = σ2 := hVarZ
    _ = ∫ x, (f x) ^ 2 ∂μ := rfl

end ProbabilityTheory
