/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory

universe u

section

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {Xn Y : ℕ → Ω → ℝ} {X : Ω → ℝ}
variable
    (hY_law : ∀ n, HasLaw (Y n) (gaussianReal 0 ⟨((n + 1 : ℝ)⁻¹), by positivity⟩) P)

include hY_law

/-- Helper for Exercise 13.2.10: each Gaussian perturbation has mean `0`. -/
lemma gaussianNoiseMeanZero (n : ℕ) :
    P[Y n] = 0 := by
  -- Move the expectation to the Gaussian reference law.
  simpa using (hY_law n).integral_eq

/-- Helper for Exercise 13.2.10: each Gaussian perturbation has variance `(n + 1)⁻¹`. -/
lemma gaussianNoiseVarianceEq (n : ℕ) :
    Var[Y n; P] = ((n + 1 : ℝ)⁻¹) := by
  -- Identify the variance through the prescribed Gaussian law.
  simpa using (hY_law n).variance_eq

/-- Helper for Exercise 13.2.10: Chebyshev bounds the Gaussian perturbation tails uniformly by
their explicit variances. -/
lemma gaussianNoiseChebyshevBound {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    P {ω | ε ≤ ‖Y n ω‖} ≤ ENNReal.ofReal (((n + 1 : ℝ)⁻¹) / ε ^ 2) := by
  -- Use square-integrability coming from the Gaussian law.
  have h_memLp : MemLp (Y n) 2 P := (hY_law n).hasGaussianLaw.memLp_two
  have h_mean : P[Y n] = 0 := gaussianNoiseMeanZero (P := P) (Y := Y) hY_law n
  have h_var : Var[Y n; P] = ((n + 1 : ℝ)⁻¹) :=
    gaussianNoiseVarianceEq (P := P) (Y := Y) hY_law n
  -- Chebyshev applies after rewriting the centered event using the zero mean.
  have h_event : {ω | ε ≤ ‖Y n ω‖} = {ω | ε ≤ |Y n ω - P[Y n]|} := by
    ext ω
    simp [h_mean, Real.norm_eq_abs]
  rw [h_event]
  calc
    P {ω | ε ≤ |Y n ω - P[Y n]|} ≤ ENNReal.ofReal (Var[Y n; P] / ε ^ 2) :=
      meas_ge_le_variance_div_sq h_memLp hε
    _ = ENNReal.ofReal (((n + 1 : ℝ)⁻¹) / ε ^ 2) := by rw [h_var]

-- Proof sketch: for every `ε > 0`, the event `{ω | ε ≤ |Yₙ ω|}` depends only on the law of `Yₙ`;
-- rewrite its probability using `hY_law n`, identify it with the corresponding Gaussian tail
-- probability for variance `(n + 1)⁻¹`, and show that this tail tends to `0` as the variance
-- shrinks to `0`.
/-- A Gaussian perturbation whose variances are `(n + 1)⁻¹` converges to `0` in probability. -/
theorem gaussian_noise_tendstoInMeasure_zero :
    TendstoInMeasure P Y atTop 0 := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  -- The explicit Gaussian variance gives a deterministic upper bound tending to `0`.
  have h_bound :
      ∀ n, P {ω | ε ≤ ‖Y n ω - 0‖} ≤ ENNReal.ofReal (((n + 1 : ℝ)⁻¹) / ε ^ 2) := by
    intro n
    simpa using gaussianNoiseChebyshevBound (P := P) (Y := Y) hY_law hε n
  have h_rhs_real : Tendsto (fun n : ℕ ↦ (((n + 1 : ℝ)⁻¹) / ε ^ 2)) atTop (nhds 0) := by
    have h_inv : Tendsto (fun n : ℕ ↦ ((n + 1 : ℝ)⁻¹)) atTop (nhds 0) := by
      simpa [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa using h_inv.div_const (ε ^ 2)
  have h_rhs :
      Tendsto (fun n : ℕ ↦ ENNReal.ofReal (((n + 1 : ℝ)⁻¹) / ε ^ 2)) atTop (nhds 0) := by
    simpa using ENNReal.tendsto_ofReal h_rhs_real
  -- Squeeze the probabilities between `0` and the vanishing bound.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_rhs ?_ h_bound
  intro n
  exact zero_le _

/-- Helper for Exercise 13.2.10: negating the Gaussian perturbation preserves convergence in
measure to `0`. -/
lemma negGaussianNoiseTendstoInMeasureZero :
    TendstoInMeasure P (-Y) atTop 0 := by
  -- Rewrite convergence in measure through norms, where negation disappears.
  have h_noise : TendstoInMeasure P Y atTop 0 :=
    gaussian_noise_tendstoInMeasure_zero (P := P) (Y := Y) hY_law
  rw [tendstoInMeasure_iff_norm] at ⊢
  rw [tendstoInMeasure_iff_norm] at h_noise
  intro ε hε
  simpa using h_noise ε hε

/-- Helper for Exercise 13.2.10: adding `0` to the limit random variable does not change it. -/
lemma addZeroLimitEq : (fun ω ↦ X ω + (0 : ℝ)) = X := by
  -- Extensionality reduces the claim to scalar addition by zero.
  ext ω
  simp

/-- Helper for Exercise 13.2.10: adding the perturbation and then `-Yₙ` recovers `Xₙ`
pointwise. -/
lemma addNegNoiseCancels : (fun n ω ↦ (Xn n ω + Y n ω) + (-Y n ω)) = Xn := by
  -- Pointwise cancellation removes the Gaussian noise from each summand.
  ext n ω
  simp [add_assoc]

-- Proof sketch: first use `gaussian_noise_tendstoInMeasure_zero` to obtain `Yₙ → 0` in
-- probability. For the forward implication, apply the canonical owner theorem
-- `TendstoInDistribution.add_of_tendstoInMeasure_const` to `Xₙ` and `Yₙ`. For the reverse
-- implication, apply the same theorem to `Xₙ + Yₙ` and `-Yₙ`.
/-- Exercise 13.2.10: with Lean's `0`-based indexing, the textbook Gaussian laws
`\mathcal{N}_{0,1/n}` are represented as `gaussianReal 0 ((n + 1)⁻¹)`. Under this shrinking
Gaussian perturbation, `Xₙ` converges in distribution to `X` if and only if `Xₙ + Yₙ` converges
in distribution to `X`. -/
theorem tendstoInDistribution_iff_add_gaussian_noise :
    TendstoInDistribution Xn atTop X (fun _ ↦ P) P ↔
      TendstoInDistribution (Xn + Y) atTop X (fun _ ↦ P) P := by
  constructor
  · intro hX
    -- Add the perturbation with the owner Slutsky addition lemma.
    change TendstoInDistribution (fun n ↦ Xn n + Y n) atTop X (fun _ ↦ P) P
    have h_add :
        TendstoInDistribution (fun n ↦ Xn n + Y n) atTop (fun ω ↦ X ω + 0) (fun _ ↦ P) P :=
      hX.add_of_tendstoInMeasure_const
        (gaussian_noise_tendstoInMeasure_zero (P := P) (Y := Y) hY_law)
        (fun n ↦ (hY_law n).aemeasurable)
    -- Normalize the perturbed limit back to `X`.
    simpa [addZeroLimitEq (X := X)] using h_add
  · intro hXY
    -- Route correction: reverse the perturbation by adding `-Y`, which still vanishes in measure.
    change TendstoInDistribution (fun n ↦ Xn n + Y n) atTop X (fun _ ↦ P) P at hXY
    change TendstoInDistribution (fun n ↦ Xn n) atTop X (fun _ ↦ P) P
    have h_cancel :
        TendstoInDistribution
          (fun n ↦ (Xn n + Y n) + (-Y n)) atTop (fun ω ↦ X ω + 0) (fun _ ↦ P) P :=
      hXY.add_of_tendstoInMeasure_const
        (negGaussianNoiseTendstoInMeasureZero (P := P) (Y := Y) hY_law)
        (fun n ↦ (hY_law n).aemeasurable.neg)
    -- Normalize the sequence and the limit after the cancellation step.
    simpa [Pi.add_def, Pi.neg_def, addZeroLimitEq (X := X), addNegNoiseCancels (Xn := Xn) (Y := Y)]
      using h_cancel

end
