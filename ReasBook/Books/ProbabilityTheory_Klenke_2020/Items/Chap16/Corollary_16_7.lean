/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Theorem_15_23
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Definition_16_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Definition_16_3
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Exercise_16_1_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Theorem_16_6

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory

noncomputable section

section

variable {φs : ℕ → ℝ → ℂ} {ψ : ℝ → ℂ}

variable (hcfp : ∀ n : ℕ, IsCFP (φs n))
variable (hlin : ∀ t : ℝ, Tendsto (fun n : ℕ ↦ (n : ℂ) * (φs n t - 1)) atTop (nhds (ψ t)))
variable (hψ_cont : ContinuousAt ψ 0)

/-- Helper for Corollary 16.7: the unique coordinate map `EuclideanSpace ℝ (Fin 1) → ℝ` is
measurable. -/
private theorem measurable_euclidean1ToReal :
    Measurable (euclidean1ToReal : EuclideanSpace ℝ (Fin 1) → ℝ) := by
  -- Proof comment: `euclidean1ToReal` is evaluation at the unique coordinate of the Euclidean
  -- one-space.
  simpa [euclidean1ToReal] using
    (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 1 ↦ ℝ) (0 : Fin 1)).measurable

/-- Helper for Corollary 16.7: continuity at `0` on `ℝ` yields the one-dimensional
`PartiallyContinuousAtZero` condition after reading the unique coordinate of `ℝ¹`. -/
private theorem partiallyContinuousAtZero_comp_euclidean1ToReal
    {φ : ℝ → ℂ} (hφ0 : ContinuousAt φ 0) :
    PartiallyContinuousAtZero (d := 1)
      (fun x : EuclideanSpace ℝ (Fin 1) ↦ φ (euclidean1ToReal x)) := by
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  -- Proof comment: in dimension one there is only one coordinate axis, so the axis restriction
  -- is exactly the original real function.
  simpa [euclidean1ToReal, realToEuclidean1] using hφ0

/-- Helper for Corollary 16.7: pushing a one-dimensional Euclidean law forward along the unique
coordinate map recovers its characteristic function on `ℝ` by evaluating at `realToEuclidean1`. -/
private theorem charFun_map_euclidean1ToReal
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin 1))) (t : ℝ) :
    charFun
      (μ.map measurable_euclidean1ToReal.aemeasurable : Measure ℝ) t =
      charFun (μ : Measure (EuclideanSpace ℝ (Fin 1))) (realToEuclidean1 t) := by
  -- Proof comment: rewrite the pushforward characteristic function by `integral_map`, then
  -- identify the one-dimensional inner product with multiplication by the unique coordinate.
  change
    charFun (Measure.map euclidean1ToReal (μ : Measure (EuclideanSpace ℝ (Fin 1)))) t =
      charFun (μ : Measure (EuclideanSpace ℝ (Fin 1))) (realToEuclidean1 t)
  rw [MeasureTheory.charFun_apply_real, MeasureTheory.charFun_apply,
    MeasureTheory.integral_map
      measurable_euclidean1ToReal.aemeasurable (by fun_prop)]
  congr with x
  congr 1
  have hinner :
      inner ℝ x (realToEuclidean1 t) = t * euclidean1ToReal x := by
    simpa [euclidean1ToReal, realToEuclidean1] using
      (EuclideanSpace.inner_single_right (i := (0 : Fin 1)) t x)
  exact congrArg (fun z : ℂ ↦ z * Complex.I) (by exact_mod_cast hinner.symm)

/-- Helper for Corollary 16.7: scaling a probability-law intensity by a nonnegative real rate
turns the compound-Poisson characteristic function into the centered exponential form. -/
private theorem charFun_compoundPoissonMeasure_nonnegRateProbability
    (μ : ProbabilityMeasure ℝ) {a : ℝ} (ha : 0 ≤ a) (t : ℝ) :
    charFun
      (compoundPoissonMeasure
        ((((Real.toNNReal a) : NNReal) • μ.toFiniteMeasure) : FiniteMeasure ℝ) : Measure ℝ) t =
      Complex.exp ((a : ℂ) * (charFun (μ : Measure ℝ) t - 1)) := by
  -- Proof comment: identify the centered Lévy exponent of a probability law, then pull the scalar
  -- `a` out of the integral over the scaled intensity measure.
  have hintegrable :
      Integrable (fun x : ℝ ↦ Complex.exp (t * x * Complex.I)) (μ := (μ : Measure ℝ)) := by
    refine Integrable.of_bound (by fun_prop) 1 ?_
    exact Filter.Eventually.of_forall fun x ↦ by
      exact le_of_eq (by simpa using (Complex.norm_exp_ofReal_mul_I (t * x)))
  have hcentered :
      ∫ x, (Complex.exp (t * x * Complex.I) - 1) ∂(μ : Measure ℝ) =
        charFun (μ : Measure ℝ) t - 1 := by
    -- Proof comment: the nonconstant part is exactly the characteristic function, and the
    -- constant part contributes the total mass `1`.
    rw [integral_sub hintegrable (integrable_const (1 : ℂ)), MeasureTheory.charFun_apply_real]
    simp
  rw [charFun_compoundPoissonMeasure]
  congr 1
  let c : ENNReal := (Real.toNNReal a : NNReal)
  change
    (∫ x, (Complex.exp (t * x * Complex.I) - 1) ∂
      (((((Real.toNNReal a : NNReal) • μ.toFiniteMeasure) : FiniteMeasure ℝ) : Measure ℝ))) =
        (a : ℂ) * (charFun (μ : Measure ℝ) t - 1)
  have hscaledMeasure :
      (((((Real.toNNReal a : NNReal) • μ.toFiniteMeasure) : FiniteMeasure ℝ) : Measure ℝ)) = c •
        (μ : Measure ℝ) := by
    rfl
  rw [hscaledMeasure, integral_smul_measure, hcentered]
  change ((c.toReal : ℂ) * (charFun (μ : Measure ℝ) t - 1)) =
      (a : ℂ) * (charFun (μ : Measure ℝ) t - 1)
  simp [c, Real.toNNReal_of_nonneg ha]

/-- Helper for Corollary 16.7: the centered compound-Poisson exponential attached to a
characteristic function is again a characteristic function whenever the rate is nonnegative. -/
private theorem isCFP_compoundPoissonExponent
    {χ : ℝ → ℂ} (hχ : IsCFP χ) {a : ℝ} (ha : 0 ≤ a) :
    IsCFP (fun t ↦ Complex.exp ((a : ℂ) * (χ t - 1))) := by
  rcases hχ with ⟨μ, hμ⟩
  refine ⟨compoundPoissonMeasure
    ((((Real.toNNReal a) : NNReal) • μ.toFiniteMeasure) : FiniteMeasure ℝ), ?_⟩
  funext t
  -- Proof comment: use the specialized compound-Poisson characteristic-function formula and then
  -- rewrite the witness characteristic function back to `χ`.
  simpa [hμ] using charFun_compoundPoissonMeasure_nonnegRateProbability (μ := μ) ha t

/-- Helper for Corollary 16.7: exponentiating the `1 / n`-scaled exponent produces an exact
positive-integer root after taking the `n`th power. -/
private theorem complexExp_invPNat_mul_pow (n : ℕ+) (z : ℂ) :
    (Complex.exp ((((1 / (n : ℝ)) : ℂ) * z))) ^ (n : ℕ) = Complex.exp z := by
  have hcoeff : ((n : ℂ) * (((1 / (n : ℝ)) : ℂ))) = 1 := by
    have hn0 : (n : ℝ) ≠ 0 := by
      exact_mod_cast n.ne_zero
    have hreal : (n : ℝ) * (1 / (n : ℝ)) = 1 := by
      field_simp [hn0]
    exact_mod_cast hreal
  -- Proof comment: collapse the `n`th power of the exponential to a single exponential and then
  -- cancel the factor `n` against its reciprocal.
  calc
    (Complex.exp ((((1 / (n : ℝ)) : ℂ) * z))) ^ (n : ℕ)
        = Complex.exp (((n : ℂ) * ((((1 / (n : ℝ)) : ℂ) * z)))) := by
            rw [← Complex.exp_nat_mul]
    _ = Complex.exp ((((n : ℂ) * (((1 / (n : ℝ)) : ℂ))) * z)) := by
          ring
    _ = Complex.exp z := by
          rw [hcoeff, one_mul]

-- Proof sketch: if `φs n` is the characteristic function of `μₙ`, then for each `r > 0` the
-- compound-Poisson law with intensity `r * μₙ` has characteristic function
-- `t ↦ exp (((r * n : ℝ) : ℂ) * (φs n t - 1))`. The assumed convergence
-- `n (φs n(t) - 1) → ψ(t)` upgrades this to pointwise convergence toward `exp (r ψ(t))`, and the
-- continuity of `ψ` at `0` gives continuity at `0` of the limit. Lévy's continuity theorem then
-- yields a probability measure with characteristic function `exp (r ψ)`.
/-- Corollary 16.7: under the linearized-limit hypothesis from Theorem 16.6, the scaled exponent
`t ↦ exp (r ψ(t))` is again a characteristic function for every `r > 0`. -/
theorem levyKhinchin_scaledExponent_isCharacteristicFunction
    {r : ℝ}
    (hcfp : ∀ n : ℕ, IsCFP (φs n))
    (hlin : ∀ t : ℝ, Tendsto (fun n : ℕ ↦ (n : ℂ) * (φs n t - 1)) atTop (nhds (ψ t)))
    (hψ_cont : ContinuousAt ψ 0)
    (hr : 0 < r) :
    IsCFP (fun t ↦ Complex.exp ((r : ℂ) * ψ t)) := by
  classical
  let χs : ℕ → ℝ → ℂ := fun n t ↦ Complex.exp ((((r * n : ℝ) : ℂ) * (φs n t - 1)))
  have hχs : ∀ n : ℕ, IsCFP (χs n) := by
    intro n
    have hrate : 0 ≤ r * n := by
      exact mul_nonneg hr.le (Nat.cast_nonneg n)
    -- Proof comment: each approximant is the characteristic function of the compound-Poisson law
    -- with rate `r * n` built from the witness law of `φs n`.
    simpa [χs] using
      (isCFP_compoundPoissonExponent (hχ := hcfp n) (a := r * n) hrate)
  let μs : ℕ → ProbabilityMeasure ℝ := fun n ↦ Classical.choose (hχs n)
  have hμs : ∀ n : ℕ, charFun (μs n : Measure ℝ) = χs n := by
    intro n
    exact Classical.choose_spec (hχs n)
  let Ps : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin 1)) := fun n ↦ pushRealToEuclidean1 (μs n)
  have hchar :
      ∀ x : EuclideanSpace ℝ (Fin 1),
        Tendsto (fun n ↦ charFun (Ps n : Measure (EuclideanSpace ℝ (Fin 1))) x) atTop
          (nhds ((fun y : EuclideanSpace ℝ (Fin 1) ↦
            Complex.exp ((r : ℂ) * ψ (euclidean1ToReal y))) x)) := by
    intro x
    have hpoint :
        Tendsto
          (fun n : ℕ ↦ Complex.exp ((((r * n : ℝ) : ℂ) * (φs n (euclidean1ToReal x) - 1))))
          atTop (nhds (Complex.exp ((r : ℂ) * ψ (euclidean1ToReal x)))) := by
      have hscaled :
          Tendsto
            (fun n : ℕ ↦ (((r * n : ℝ) : ℂ) * (φs n (euclidean1ToReal x) - 1)))
            atTop (nhds ((r : ℂ) * ψ (euclidean1ToReal x))) := by
        -- Proof comment: the assumed linearized limit is stable under multiplication by the
        -- fixed scalar `r`.
        simpa [mul_assoc, mul_comm, mul_left_comm] using
          (hlin (euclidean1ToReal x)).const_mul (r : ℂ)
      exact Complex.continuous_exp.continuousAt.tendsto.comp hscaled
    have hrewrite :
        (fun n ↦ charFun (Ps n : Measure (EuclideanSpace ℝ (Fin 1))) x) =
          fun n : ℕ ↦ Complex.exp ((((r * n : ℝ) : ℂ) * (φs n (euclidean1ToReal x) - 1))) := by
      funext n
      calc
        charFun (Ps n : Measure (EuclideanSpace ℝ (Fin 1))) x
            = charFun (μs n : Measure ℝ) (euclidean1ToReal x) := by
                simpa [Ps] using charFun_map_realToEuclidean1 (μ := μs n) x
        _ = χs n (euclidean1ToReal x) := by
              rw [hμs n]
        _ = Complex.exp ((((r * n : ℝ) : ℂ) * (φs n (euclidean1ToReal x) - 1))) := by
              rfl
    -- Proof comment: after transporting each witness law to `ℝ¹`, the approximating
    -- characteristic functions converge pointwise to the transported limit.
    rw [hrewrite]
    exact hpoint
  have hlimit0 : ContinuousAt (fun t : ℝ ↦ Complex.exp ((r : ℂ) * ψ t)) 0 := by
    -- Proof comment: continuity at `0` survives multiplication by `r` and composition with `exp`.
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      (Complex.continuous_exp.continuousAt.comp (hψ_cont.const_mul (r : ℂ)))
  have hφE0 :
      PartiallyContinuousAtZero (d := 1) (fun x : EuclideanSpace ℝ (Fin 1) ↦
        Complex.exp ((r : ℂ) * ψ (euclidean1ToReal x))) :=
    partiallyContinuousAtZero_comp_euclidean1ToReal hlimit0
  rcases exists_probabilityMeasure_of_tendsto_charFun (d := 1) Ps hchar hφE0 with
    ⟨Q, hQchar, -⟩
  refine ⟨Q.map measurable_euclidean1ToReal.aemeasurable, ?_⟩
  funext t
  -- Proof comment: read the unique coordinate of the limiting `ℝ¹` law to recover the desired
  -- real characteristic function.
  rw [charFun_map_euclidean1ToReal]
  simpa [realToEuclidean1, euclidean1ToReal] using hQchar (realToEuclidean1 t)

-- Proof sketch: for each positive integer `n`, apply
-- `levyKhinchin_scaledExponent_isCharacteristicFunction` with `r = 1 / n` to obtain a
-- characteristic function root `t ↦ exp (((1 / n : ℝ) : ℂ) * ψ t)`. Its `n`th pointwise power is
-- `t ↦ exp (ψ t)`, so the definition of `IsInfinitelyDivisibleCFP` applies.
/-- Under the linearized-limit hypothesis from Theorem 16.6, the characteristic function `e^ψ` is
infinitely divisible in the owner predicate `IsInfinitelyDivisibleCFP`. -/
theorem levyKhinchin_exponential_has_characteristicRoots
    (hcfp : ∀ n : ℕ, IsCFP (φs n))
    (hlin : ∀ t : ℝ, Tendsto (fun n : ℕ ↦ (n : ℂ) * (φs n t - 1)) atTop (nhds (ψ t)))
    (hψ_cont : ContinuousAt ψ 0) :
    IsInfinitelyDivisibleCFP (fun t ↦ Complex.exp (ψ t)) := by
  intro n
  refine ⟨fun t ↦ Complex.exp ((((1 / (n : ℝ)) : ℂ) * ψ t)), ?_, ?_⟩
  · have hrootRate : 0 < (1 / (n : ℝ)) := by
      exact one_div_pos.mpr (by exact_mod_cast n.pos)
    -- Proof comment: the previous theorem supplies a characteristic-function root for each
    -- positive integer reciprocal rate.
    simpa using
      levyKhinchin_scaledExponent_isCharacteristicFunction
        (φs := φs) (ψ := ψ) hcfp hlin hψ_cont hrootRate
  · funext t
    -- Proof comment: the chosen root is exact because the exponential law turns scalar
    -- multiplication of the exponent into pointwise powers.
    simpa using (complexExp_invPNat_mul_pow n (ψ t)).symm

end
