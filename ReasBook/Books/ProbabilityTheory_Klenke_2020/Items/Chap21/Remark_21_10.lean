/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

universe u v w

variable {T : Type u} {Ω : Type v} {Ω' : Type w}
variable [MeasurableSpace Ω] [MeasurableSpace Ω']

set_option backward.isDefEq.respectTransparency false in
/-- Helper for Remark 21.10: the transported finite-dimensional laws agree once centeredness and
the covariance kernel agree on the chosen index set. -/
private lemma finiteDimensionalToLpLaw_eq_of_centered_covariance
    {P : Measure Ω} {Q : Measure Ω'}
    {X : T → Ω → ℝ} {Y : T → Ω' → ℝ}
    (I : Finset T)
    (hLawX : HasGaussianLaw (fun ω ↦ WithLp.toLp 2 (fun i : I ↦ X i ω)) P)
    (hLawY : HasGaussianLaw (fun ω ↦ WithLp.toLp 2 (fun i : I ↦ Y i ω)) Q)
    (hMemX : ∀ i : I, MemLp (X i) 2 P)
    (hMemY : ∀ i : I, MemLp (Y i) 2 Q)
    (hX_centered : ∀ t, P[X t] = 0)
    (hY_centered : ∀ t, Q[Y t] = 0)
    (hcov : ∀ s t, cov[X s, X t; P] = cov[Y s, Y t; Q]) :
    P.map (fun ω ↦ WithLp.toLp 2 (fun i : I ↦ X i ω)) =
      Q.map (fun ω ↦ WithLp.toLp 2 (fun i : I ↦ Y i ω)) := by
  letI : IsProbabilityMeasure P := hLawX.isProbabilityMeasure
  letI : IsProbabilityMeasure Q := hLawY.isProbabilityMeasure
  have hInnerX (t : PiLp 2 (fun _ : I ↦ ℝ)) :
      (fun ω ↦ inner ℝ t (WithLp.toLp 2 (fun i : I ↦ X i ω))) = fun ω ↦ ∑ i, t i * X i ω := by
    ext ω
    simp [PiLp.inner_apply, mul_comm]
  have hInnerY (t : PiLp 2 (fun _ : I ↦ ℝ)) :
      (fun ω ↦ inner ℝ t (WithLp.toLp 2 (fun i : I ↦ Y i ω))) = fun ω ↦ ∑ i, t i * Y i ω := by
    ext ω
    simp [PiLp.inner_apply, mul_comm]
  have hMeanX (t : PiLp 2 (fun _ : I ↦ ℝ)) :
      P[fun ω ↦ ∑ i, t i * X i ω] = 0 := by
    rw [integral_finset_sum]
    · simp_rw [integral_const_mul, hX_centered, mul_zero]
      simp
    · intro i _
      exact ((hMemX i).integrable (by norm_num)).const_mul _
  have hMeanY (t : PiLp 2 (fun _ : I ↦ ℝ)) :
      Q[fun ω ↦ ∑ i, t i * Y i ω] = 0 := by
    rw [integral_finset_sum]
    · simp_rw [integral_const_mul, hY_centered, mul_zero]
      simp
    · intro i _
      exact ((hMemY i).integrable (by norm_num)).const_mul _
  have hVarX (t : PiLp 2 (fun _ : I ↦ ℝ)) :
      Var[fun ω ↦ ∑ i, t i * X i ω; P] =
        ∑ i, ∑ j, t i * t j * cov[X i, X j; P] := by
    rw [variance_fun_sum fun i ↦ (hMemX i).const_mul _]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    rw [covariance_const_mul_left, covariance_const_mul_right]
    ring
  have hVarY (t : PiLp 2 (fun _ : I ↦ ℝ)) :
      Var[fun ω ↦ ∑ i, t i * Y i ω; Q] =
        ∑ i, ∑ j, t i * t j * cov[Y i, Y j; Q] := by
    rw [variance_fun_sum fun i ↦ (hMemY i).const_mul _]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    rw [covariance_const_mul_left, covariance_const_mul_right]
    ring
  -- Characteristic functions of Gaussian laws are determined by the means and variances of all
  -- linear combinations of the coordinates.
  refine Measure.ext_of_charFun <| funext fun t ↦ ?_
  rw [hLawX.charFun_map_eq, hLawY.charFun_map_eq, hInnerX, hInnerY, hMeanX, hMeanY, hVarX, hVarY]
  congr 1
  simp_rw [hcov]

-- Proof sketch: for a finite index set `I`, the owner finite-dimensional laws
-- `P.map (fun ω ↦ I.restrict (X · ω))` and `Q.map (fun ω ↦ I.restrict (Y · ω))` are Gaussian by
-- `IsGaussianProcess.hasGaussianLaw`; centeredness identifies their means with `0`, and the
-- covariance-function hypothesis identifies their covariance bilinear forms, so equality follows
-- from the finite-dimensional uniqueness of Gaussian laws by mean and covariance.
/-- Remark 21.10: the covariance function determines each finite-dimensional law of a centered
Gaussian process. Concretely, two centered Gaussian processes with the same covariance function
have the same finite-dimensional laws. -/
theorem finiteDimensionalDistributions_eq_of_centered_gaussian_covariance
    {P : Measure Ω} {Q : Measure Ω'}
    {X : T → Ω → ℝ} {Y : T → Ω' → ℝ}
    (hX : IsGaussianProcess X P) (hY : IsGaussianProcess Y Q)
    (hX_centered : ∀ t, P[X t] = 0)
    (hY_centered : ∀ t, Q[Y t] = 0)
    (hcov : ∀ s t, cov[X s, X t; P] = cov[Y s, Y t; Q])
    (I : Finset T) :
    P.map (fun ω ↦ I.restrict (X · ω)) = Q.map (fun ω ↦ I.restrict (Y · ω)) := by
  let hRestrictLawX : HasGaussianLaw (fun ω ↦ I.restrict (X · ω)) P := hX.hasGaussianLaw I
  let hRestrictLawY : HasGaussianLaw (fun ω ↦ I.restrict (Y · ω)) Q := hY.hasGaussianLaw I
  have hMemX : ∀ i : I, MemLp (X i) 2 P := fun i ↦ by
    simpa using (hRestrictLawX.eval i).memLp_two
  have hMemY : ∀ i : I, MemLp (Y i) 2 Q := fun i ↦ by
    simpa using (hRestrictLawY.eval i).memLp_two
  let e : (I → ℝ) ≃L[ℝ] PiLp 2 (fun _ : I ↦ ℝ) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : I ↦ ℝ)).symm
  have he : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  have hLawX :
      HasGaussianLaw (fun ω ↦ WithLp.toLp 2 (fun i : I ↦ X i ω)) P := by
    -- Transport the restricted law to the Hilbert-space model where Gaussian uniqueness applies.
    simpa [e, Function.comp_def] using hRestrictLawX.map_equiv e
  have hLawY :
      HasGaussianLaw (fun ω ↦ WithLp.toLp 2 (fun i : I ↦ Y i ω)) Q := by
    -- The same transport is used for the second process.
    simpa [e, Function.comp_def] using hRestrictLawY.map_equiv e
  -- Compare the laws after the measurable embedding `e`; injectivity then gives the original claim.
  refine (MeasurableEmbedding.map_injective he) ?_
  rw [AEMeasurable.map_map_of_aemeasurable e.continuous.measurable.aemeasurable
      hRestrictLawX.aemeasurable,
    AEMeasurable.map_map_of_aemeasurable e.continuous.measurable.aemeasurable
      hRestrictLawY.aemeasurable]
  simpa [e, Function.comp_def] using
    finiteDimensionalToLpLaw_eq_of_centered_covariance I hLawX hLawY hMemX hMemY
      hX_centered hY_centered hcov
