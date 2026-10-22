/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Remark_9_11
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Example_14_45
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Exercise_15_4_6
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_12
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_8
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Exercise_21_2_5
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Exercise_21_2_4
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_6
import Books.ProbabilityTheory_Klenke_2020.Items.Chap22.Lemma_22_8

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal NNReal Topology

noncomputable section

namespace ProbabilityTheory

local notation "PairSpace" => Set.Iio (0 : ℝ) × Set.Ici (0 : ℝ)

/-- Helper for Theorem 22.5: `L²` control of `id` gives integrability of the second-moment
integrand `x ↦ x ^ 2`. -/
private lemma integrable_square_of_memLp_id
    (hμ_memLp : MemLp id 2 (μ : Measure ℝ)) :
    Integrable (fun x : ℝ ↦ x ^ 2) (μ : Measure ℝ) := by
  -- Proof comment: the `MemLp` API already packages the square-integrability implication.
  simpa using hμ_memLp.integrable_sq

/-- Helper for Theorem 22.5: for a centered square-integrable law, the variance is exactly the
second moment. -/
private lemma variance_id_eq_secondMoment_of_mean_zero
    (μ : ProbabilityMeasure ℝ)
    (hμ_mean_zero : ∫ x, x ∂(μ : Measure ℝ) = 0)
    (hμ_memLp : MemLp id 2 (μ : Measure ℝ)) :
    Var[id; (μ : Measure ℝ)] = ∫ x, x ^ 2 ∂(μ : Measure ℝ) := by
  -- Proof comment: expand the variance and collapse the centered first-moment term.
  rw [variance_eq_integral hμ_memLp.aemeasurable]
  simp [hμ_mean_zero]

/-- Helper for Theorem 22.5: Lemma 22.8 turns the target law into a mixture of centered two-point
laws and rewrites its variance as the averaged barrier product `-u v`. -/
private lemma existsSkorohodMixtureData
    (μ : ProbabilityMeasure ℝ)
    (hμ_mean_zero : ∫ x, x ∂(μ : Measure ℝ) = 0)
    (hμ_memLp : MemLp id 2 (μ : Measure ℝ)) :
    ∃ θ : ProbabilityMeasure PairSpace,
      (μ : Measure ℝ) =
        negativeNonnegativeTwoPointKernel ∘ₘ (θ : Measure PairSpace) ∧
      Var[id; (μ : Measure ℝ)] =
        ∫ z, -((z.1 : ℝ) * z.2) ∂(θ : Measure PairSpace) := by
  obtain ⟨θ, hθ_mix, hθ_second⟩ :=
    exists_centered_two_point_mixture μ hμ_mean_zero
      (integrable_square_of_memLp_id (μ := μ) hμ_memLp)
  refine ⟨θ, hθ_mix, ?_⟩
  -- Proof comment: substitute the second-moment identity from Lemma 22.8 into the centered
  -- variance formula.
  calc
    Var[id; (μ : Measure ℝ)] = ∫ x, x ^ 2 ∂(μ : Measure ℝ) :=
      variance_id_eq_secondMoment_of_mean_zero μ hμ_mean_zero hμ_memLp
    _ = ∫ z, -((z.1 : ℝ) * z.2) ∂(θ : Measure PairSpace) := hθ_second

/-- Helper for Theorem 22.5: when the right barrier is strictly positive, Chapter 21 computes the
expected two-sided Brownian exit time as `-u v`. -/
private lemma brownianTwoPointExitMean_eq_of_pos
    {Ω : Type*} [MeasurableSpace Ω] {P : ProbabilityMeasure Ω}
    {B : NNReal → Ω → ℝ}
    (hB : IsBrownianMotion (P : Measure Ω) B)
    (z : PairSpace) (hz : 0 < (z.2 : ℝ)) :
    ∫ ω, ENNReal.toReal (hittingAfter B ({(z.1 : ℝ), (z.2 : ℝ)} : Set ℝ) 0 ω)
        ∂(P : Measure Ω) =
      -((z.1 : ℝ) * z.2) := by
  -- Proof comment: this is exactly the fixed-fiber two-sided Brownian exit-time identity from
  -- Chapter 21, specialized to the support pair `z = (u,v)`.
  simpa using
    brownianMotion_twoSidedHittingTime_expectation_eq
      (μ := (P : Measure Ω)) (B := B) (hB := hB) (a := (z.1 : ℝ)) (b := (z.2 : ℝ)) z.1.2 hz

/-- Helper for Theorem 22.5: Gaussian laws are stable under precomposition with a
measure-preserving map. -/
private theorem hasGaussianLaw_comp_measurePreserving
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E] [MeasurableSpace E]
    {μ : Measure β} {ν : Measure α} {f : α → β} {X : β → E}
    (hX : HasGaussianLaw X μ) (hf : MeasurePreserving f ν μ) :
    HasGaussianLaw (X ∘ f) ν := by
  let hLawX : HasLaw X (μ.map X) μ := { map_eq := rfl }
  let hComp : HasLaw (X ∘ f) (μ.map X) ν := HasLaw.comp hLawX hf.hasLaw
  letI : IsGaussian (μ.map X) := hX.isGaussian_map
  -- Proof comment: Gaussianity depends only on the pushforward law, which `hf` preserves.
  exact hComp.hasGaussianLaw

/-- Helper for Theorem 22.5: Brownian motion is stable under precomposition with a
measure-preserving map. -/
private theorem isBrownianMotion_comp_measurePreserving
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {ν : Measure α} [IsProbabilityMeasure ν]
    {μ : Measure β} [IsProbabilityMeasure μ]
    {f : α → β}
    (hf : MeasurePreserving f ν μ)
    {B : NNReal → β → ℝ}
    (hB : IsBrownianMotion μ B) :
    IsBrownianMotion ν (fun t x ↦ B t (f x)) := by
  -- Proof comment: pull back the Brownian characterization field-by-field through the
  -- measure-preserving map.
  refine
    (isBrownianMotion_iff_isCenteredGaussianProcessWithBrownianCovariance
      ν (fun t x ↦ B t (f x))).2 ?_
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- Proof comment: the deterministic time-zero normalization survives unchanged.
    funext x
    simpa using congrFun hB.zero (f x)
  · refine ⟨fun I ↦ ?_⟩
    -- Proof comment: finite-dimensional Gaussian laws pull back along measure-preserving maps.
    simpa [Function.comp_def] using
      hasGaussianLaw_comp_measurePreserving
        (hX := hB.isGaussianProcess.hasGaussianLaw I) hf
  · intro t
    -- Proof comment: expectations are preserved because `hf` identifies the pushforward law.
    calc
      ∫ x, B t (f x) ∂ν = ∫ y, B t y ∂μ := by
          simpa [Function.comp_def] using
            (hf.hasLaw.integral_comp
              (f := fun y ↦ B t y)
              (hB.stronglyMeasurable t).aestronglyMeasurable)
      _ = 0 := hB.mean_zero t
  · intro s t
    -- Proof comment: the Brownian covariance kernel is equally stable under pullback.
    calc
      cov[(fun x ↦ B s (f x)), (fun x ↦ B t (f x)); ν]
          = cov[(fun y ↦ B s y), (fun y ↦ B t y); μ] := by
              simpa [Function.comp_def] using
                (hf.hasLaw.covariance_comp
                  (f := fun y ↦ B s y)
                  (g := fun y ↦ B t y)
                  (hB.stronglyMeasurable s).aemeasurable
                  (hB.stronglyMeasurable t).aemeasurable)
      _ = ((s ⊓ t : NNReal) : ℝ) := hB.covariance_eq s t
  · -- Proof comment: pull back the exceptional null set for path continuity along `hf`.
    refine (ae_iff.2 ?_)
    have hnull : μ {y | ¬ Continuous (processPath B y)} = 0 :=
      (ae_iff.1 hB.continuous_paths)
    simpa [HasAlmostSurelyContinuousPaths, processPath, Function.comp] using
      hf.preimage_null hnull

/-- Helper for Theorem 22.5: the time-zero coordinate under the canonical Gaussian increment path
law is almost surely equal to `0`. -/
private theorem gaussianIncrementCoordinate_zero_ae :
    Function.eval 0 =ᵐ[gaussianIncrementPathMeasure] fun _ : NNReal → ℝ ↦ 0 := by
  -- Proof comment: the time-zero marginal is `δ₀`, so the zero coordinate hits `{0}` with
  -- probability one.
  refine (ae_iff_prob_eq_one ((measurable_pi_apply 0).eq measurable_const)).2 ?_
  have hMap :
      gaussianIncrementPathMeasure.map (Function.eval 0) = Measure.dirac 0 :=
    gaussianIncrementPathMeasure_start_hasLaw.map_eq
  have hOne :
      gaussianIncrementPathMeasure ((Function.eval 0) ⁻¹' ({0} : Set ℝ)) = 1 := by
    calc
      gaussianIncrementPathMeasure ((Function.eval 0) ⁻¹' ({0} : Set ℝ))
          = gaussianIncrementPathMeasure.map (Function.eval 0) ({0} : Set ℝ) := by
              symm
              exact Measure.map_apply (measurable_pi_apply 0) (measurableSet_singleton 0)
      _ = 1 := by
            rw [hMap]
            simp
  simpa [Function.eval] using hOne

/-- Helper for Theorem 22.5: each deterministic coordinate of the canonical Gaussian increment
path law has the centered Gaussian law `N(0,t)`. -/
private theorem gaussianIncrementCoordinate_eval_hasLaw (t : NNReal) :
    HasLaw (Function.eval t) (gaussianReal 0 t) gaussianIncrementPathMeasure := by
  by_cases ht : t = 0
  · -- Proof comment: the time-zero marginal is exactly `δ₀ = N(0,0)`.
    subst ht
    simpa [gaussianReal_zero_var] using gaussianIncrementPathMeasure_start_hasLaw
  · have hInc :
        HasLaw (fun ω : NNReal → ℝ ↦ ω t - ω 0) (gaussianReal 0 (t - 0))
          gaussianIncrementPathMeasure := by
      simpa using
        gaussianIncrementPathMeasure_increment_hasLaw
          (s := 0) (t := t) (show (0 : NNReal) ≤ t by simp)
    have hEval :
        HasLaw (Function.eval t) (gaussianReal 0 (t - 0)) gaussianIncrementPathMeasure :=
      hInc.congr <| by
        -- Proof comment: the zero-time coordinate vanishes almost surely, so the `0`-increment
        -- is just the time-`t` coordinate almost surely.
        filter_upwards [gaussianIncrementCoordinate_zero_ae] with ω hω
        simp [Function.eval, hω]
    simpa using hEval

/-- Helper for Theorem 22.5: each deterministic coordinate of the canonical Gaussian increment
path law is centered. -/
private theorem gaussianIncrementCoordinate_mean_zero (t : NNReal) :
    ∫ ω, Function.eval t ω ∂gaussianIncrementPathMeasure = 0 := by
  -- Proof comment: the fixed-time marginal is the centered Gaussian law `N(0,t)`.
  simpa using (gaussianIncrementCoordinate_eval_hasLaw t).integral_eq

/-- Helper for Theorem 22.5: the canonical Gaussian increment path law has Brownian covariance
kernel `cov(B_s, B_t) = s ∧ t`. -/
private theorem gaussianIncrementCoordinate_covariance_eq (s t : NNReal) :
    cov[Function.eval s, Function.eval t; gaussianIncrementPathMeasure] = ((s ⊓ t : NNReal) : ℝ) := by
  letI : IsProbabilityMeasure gaussianIncrementPathMeasure := inferInstance
  -- Proof comment: order the times, split the later coordinate into the earlier coordinate plus
  -- the future increment, and use independent increments to kill the mixed covariance term.
  wlog hst : s ≤ t generalizing s t with hswap
  · rw [covariance_comm, inf_comm]
    exact hswap t s (le_of_not_ge hst)
  have hs_mem : MemLp (Function.eval s) 2 gaussianIncrementPathMeasure :=
    (gaussianIncrementCoordinate_eval_hasLaw s).hasGaussianLaw.memLp_two
  have hIncLaw :
      HasLaw (fun ω : NNReal → ℝ ↦ Function.eval t ω - Function.eval s ω)
        (gaussianReal 0 (t - s)) gaussianIncrementPathMeasure := by
    simpa [Function.eval] using
      gaussianIncrementPathMeasure_increment_hasLaw (s := s) (t := t) hst
  have hInc_mem :
      MemLp (fun ω : NNReal → ℝ ↦ Function.eval t ω - Function.eval s ω) 2
        gaussianIncrementPathMeasure :=
    hIncLaw.hasGaussianLaw.memLp_two
  have hIndep :
      (Function.eval s) ⟂ᵢ[gaussianIncrementPathMeasure]
        (fun ω : NNReal → ℝ ↦ Function.eval t ω - Function.eval s ω) :=
    gaussianIncrementPathMeasure_hasStationaryIndependentIncrements.1.indepFun_eval_sub
      (show (0 : NNReal) ≤ s by simp) hst gaussianIncrementCoordinate_zero_ae
  have hSplit :
      Function.eval t =
        fun ω : NNReal → ℝ ↦ Function.eval s ω + (Function.eval t ω - Function.eval s ω) := by
    funext ω
    ring
  have hVarS : Var[Function.eval s; gaussianIncrementPathMeasure] = (s : ℝ) := by
    simpa using (gaussianIncrementCoordinate_eval_hasLaw s).variance_eq
  rw [hSplit]
  change
    cov[Function.eval s,
      Function.eval s + (fun ω : NNReal → ℝ ↦ Function.eval t ω - Function.eval s ω);
      gaussianIncrementPathMeasure] = ((s ⊓ t : NNReal) : ℝ)
  rw [covariance_add_right hs_mem hs_mem hInc_mem,
    hIndep.covariance_eq_zero hs_mem hInc_mem, covariance_self hs_mem.aemeasurable, hVarS]
  simp [inf_eq_left.mpr hst]

/-- Helper for Theorem 22.5: covariance is unchanged after replacing each input by an
almost-everywhere equal random variable. -/
private theorem covariance_congr_ae
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X X' Y Y' : Ω → ℝ} (hX : X =ᵐ[μ] X') (hY : Y =ᵐ[μ] Y') :
    cov[X, Y; μ] = cov[X', Y'; μ] := by
  have hIntX : ∫ ω, X ω ∂μ = ∫ ω, X' ω ∂μ := integral_congr_ae hX
  have hIntY : ∫ ω, Y ω ∂μ = ∫ ω, Y' ω ∂μ := integral_congr_ae hY
  rw [ProbabilityTheory.covariance, ProbabilityTheory.covariance]
  refine integral_congr_ae ?_
  filter_upwards [hX, hY] with ω hωX hωY
  simp [hωX, hωY, hIntX, hIntY]

/-- Helper for Theorem 22.5: monotone finite families of canonical Gaussian-increment coordinates
have a joint Gaussian law. -/
private theorem gaussianIncrementCoordinate_hasGaussianLaw_of_monotone
    {n : ℕ} (t : Fin n → NNReal) (ht : Monotone t) :
    HasGaussianLaw (fun ω i ↦ Function.eval (t i) ω) gaussianIncrementPathMeasure := by
  classical
  let tAux : Fin (n + 1) → NNReal := Fin.cases 0 t
  have htAux : Monotone tAux := by
    intro i j hij
    cases i using Fin.cases with
    | zero =>
        cases j using Fin.cases with
        | zero =>
            simp [tAux]
        | succ j =>
            simp [tAux]
    | succ i =>
        cases j using Fin.cases with
        | zero =>
            cases hij
        | succ j =>
            simpa [tAux] using ht (show i ≤ j by simpa using hij)
  let Y : Fin n → (NNReal → ℝ) → ℝ :=
    fun i ω ↦ Function.eval (tAux i.succ) ω - Function.eval (tAux i.castSucc) ω
  have hY_gauss : ∀ i : Fin n, HasGaussianLaw (Y i) gaussianIncrementPathMeasure := by
    intro i
    -- Proof comment: each ordered increment has the prescribed centered Gaussian law.
    exact
      (gaussianIncrementPathMeasure_increment_hasLaw
        (s := tAux i.castSucc)
        (t := tAux i.succ)
        (htAux i.castSucc_le_succ)).hasGaussianLaw
  have hY_indep : iIndepFun Y gaussianIncrementPathMeasure := by
    -- Proof comment: the ordered increment family is independent by the stationary-independent
    -- increment owner of the canonical path measure.
    simpa [Y] using
      gaussianIncrementPathMeasure_hasStationaryIndependentIncrements.1 n tAux htAux
  have hY_joint : HasGaussianLaw (fun ω i ↦ Y i ω) gaussianIncrementPathMeasure :=
    hY_indep.hasGaussianLaw hY_gauss
  let cumulativeSumFun : (Fin n → ℝ) → Fin n → ℝ := fun x i ↦
    Finset.sum (Finset.Iic i) (fun j ↦ x j)
  let cumulativeSumsLinear : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    { toFun := cumulativeSumFun
      map_add' := by
        intro x y
        ext i
        simp [cumulativeSumFun, Finset.sum_add_distrib]
      map_smul' := by
        intro c x
        ext i
        simp [cumulativeSumFun, smul_eq_mul, Finset.mul_sum] }
  let cumulativeSums : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
    ⟨cumulativeSumsLinear, cumulativeSumsLinear.continuous_of_finiteDimensional⟩
  have hCumulativeSums :
      ∀ x i, cumulativeSums x i = Fin.partialSum x i.succ := by
    intro x i
    change Finset.sum (Finset.Iic i) (fun j ↦ x j) = Fin.partialSum x i.succ
    rw [← Finset.sum_Iio_add_eq_sum_Iic (f := x) i]
    rw [← Finset.filter_gt_eq_Iio]
    simp [Fin.partialSum, List.sum_take_ofFn]
  have hCumulative :
      ∀ ω i, cumulativeSums (fun j ↦ Y j ω) i = Function.eval (t i) ω - Function.eval 0 ω := by
    intro ω i
    let f : Fin (n + 1) → ℝ := fun j ↦ Function.eval (tAux j) ω
    have hPartial :
        Fin.partialSum (fun j ↦ Y j ω) i.succ = f i.succ - f 0 := by
      have h :
          f 0 + Fin.partialSum (fun j ↦ -f j.castSucc + f j.succ) i.succ = f i.succ := by
        simpa using congrFun (Fin.partialSum_left_neg f) i.succ
      have hY :
          (fun j ↦ Y j ω) = fun j ↦ -f j.castSucc + f j.succ := by
        funext j
        simp [Y, f, sub_eq_add_neg, add_comm]
      have h' : f 0 + Fin.partialSum (fun j ↦ Y j ω) i.succ = f i.succ := by
        simpa [hY] using h
      linarith
    rw [hCumulativeSums]
    simpa [f, tAux]
      using hPartial
  have hRecover :
      (fun ω ↦ cumulativeSums (fun j ↦ Y j ω)) =ᵐ[gaussianIncrementPathMeasure]
        fun ω i ↦ Function.eval (t i) ω := by
    -- Proof comment: the cumulative increments recover the coordinate vector because the canonical
    -- process starts at `0` almost surely.
    filter_upwards [gaussianIncrementCoordinate_zero_ae] with ω hω
    ext i
    simp [hCumulative ω i, hω]
  exact (hY_joint.map cumulativeSums).congr hRecover

/-- Helper for Theorem 22.5: the canonical coordinate process under the Gaussian-increment owner
is a centered Gaussian process. -/
private theorem gaussianIncrementCoordinate_isGaussianProcess :
    IsGaussianProcess Function.eval gaussianIncrementPathMeasure := by
  classical
  -- Proof comment: sort any finite family of times, prove Gaussianity on the monotone `Fin`
  -- model, and transport that law back to the original finite index set.
  refine ⟨fun I ↦ ?_⟩
  let e : Fin I.card ≃o I := I.orderIsoOfFin rfl
  let eCL : (Fin I.card → ℝ) ≃L[ℝ] (I → ℝ) :=
    (LinearEquiv.funCongrLeft ℝ ℝ e.toEquiv.symm).toContinuousLinearEquivOfContinuous
      (LinearEquiv.funCongrLeft ℝ ℝ e.toEquiv.symm).continuous_of_finiteDimensional
  have hFin :
      HasGaussianLaw (fun ω (i : Fin I.card) ↦ ω (e i : NNReal))
        gaussianIncrementPathMeasure :=
    gaussianIncrementCoordinate_hasGaussianLaw_of_monotone (t := fun i ↦ (e i : NNReal)) e.monotone
  have hRestrict :
      (fun ω : NNReal → ℝ ↦ I.restrict ω) =
        fun ω : NNReal → ℝ ↦ eCL (fun i : Fin I.card ↦ ω (e i : NNReal)) := by
    ext ω i
    simp [eCL, LinearEquiv.funCongrLeft_apply]
  rw [hRestrict]
  exact hFin.map_equiv eCL

/-- Helper for Theorem 22.5: the fourth power of the real-valued distance is the quartic power
of the increment. -/
private lemma realEdist_pow_four_eq_ofReal_sub_pow_four (a b : ℝ) :
    edist a b ^ (4 : ℝ) = ENNReal.ofReal ((b - a) ^ 4) := by
  -- Proof comment: raise the real distance to the fourth power, rewrite through `|a - b|`,
  -- and then remove the absolute value because the exponent is even.
  rw [show (4 : ℝ) = (4 : ℕ) by norm_num, ENNReal.rpow_natCast]
  rw [edist_dist, Real.dist_eq, ← ENNReal.ofReal_pow (abs_nonneg (a - b))]
  congr 1
  have habs : |a - b| ^ 4 = (a - b) ^ 4 := by
    rw [show |a - b| ^ 4 = (|a - b| ^ 2) ^ 2 by ring,
      show (a - b) ^ 4 = ((a - b) ^ 2) ^ 2 by ring, sq_abs]
  calc
    |a - b| ^ 4 = (a - b) ^ 4 := habs
    _ = (b - a) ^ 4 := by ring_nf

/-- Helper for Theorem 22.5: a standard Gaussian variable has fourth moment `3`. -/
private lemma gaussianRealFourthMoment_eq_three
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {Y : Ω → ℝ} (hY : HasLaw Y (gaussianReal 0 1) μ) :
    ∫ ω, Y ω ^ (4 : ℕ) ∂μ = 3 := by
  letI : IsProbabilityMeasure (μ.map Y) := by
    rw [hY.map_eq]
    infer_instance
  letI : IsProbabilityMeasure μ := μ.isProbabilityMeasure_of_map Y
  have hStdId : HasLaw (id : ℝ → ℝ) (gaussianReal 0 1) (gaussianReal 0 1) :=
    { aemeasurable := measurable_id'.aemeasurable
      map_eq := by simp }
  have hStdFourth :
      ∫ x : ℝ, x ^ (4 : ℕ) ∂gaussianReal 0 1 = 3 := by
    -- Proof comment: evaluate the standard Gaussian fourth moment through the public even-moment
    -- formula at `k = 2`.
    have hMoment :=
      gaussianReal_even_moments_eq_factorial_ratio hStdId 2
    norm_num at hMoment
    exact hMoment
  -- Proof comment: transport the quartic moment from `Y` to the canonical Gaussian owner.
  exact
    (hY.integral_comp ((continuous_pow 4).aestronglyMeasurable)).trans hStdFourth

/-- Helper for Theorem 22.5: a centered Gaussian random variable has fourth moment
`3 * Var[Y]^2`. -/
private lemma centeredGaussianFourthMoment_eq_three_mul_variance_sq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {Y : Ω → ℝ} (hY : HasGaussianLaw Y μ) (hY_mean : ∫ ω, Y ω ∂μ = 0) :
    ∫ ω, Y ω ^ (4 : ℕ) ∂μ = 3 * Var[Y; μ] ^ (2 : ℕ) := by
  letI : IsProbabilityMeasure μ := hY.isProbabilityMeasure
  let v : NNReal := Var[Y; μ].toNNReal
  have hLaw :
      HasLaw Y (gaussianReal (∫ ω, Y ω ∂μ) v) μ := by
    refine ⟨hY.aemeasurable, ?_⟩
    calc
      μ.map Y = gaussianReal ((μ.map Y)[id]) Var[id; μ.map Y].toNNReal := by
        exact ProbabilityTheory.IsGaussian.eq_gaussianReal (μ.map Y) hY.isGaussian_map
      _ = gaussianReal (∫ ω, Y ω ∂μ) v := by
        congr 1
        · simpa using
            (integral_map hY.aemeasurable measurable_id'.aestronglyMeasurable :
              ∫ x : ℝ, id x ∂Measure.map Y μ = ∫ ω, id (Y ω) ∂μ)
        · simpa [v] using
            congrArg Real.toNNReal
              (variance_map measurable_id'.aemeasurable hY.aemeasurable :
                Var[id; μ.map Y] = Var[id ∘ Y; μ])
  have hLaw0 :
      HasLaw Y (gaussianReal 0 v) μ := by
    refine ⟨hY.aemeasurable, ?_⟩
    -- Proof comment: the centered hypothesis collapses the Gaussian mean parameter to `0`.
    simpa [v, hY_mean] using hLaw.map_eq
  let c : ℝ := Real.sqrt (v : ℝ)
  have hStdId : HasLaw (id : ℝ → ℝ) (gaussianReal 0 1) (gaussianReal 0 1) :=
    { aemeasurable := measurable_id'.aemeasurable
      map_eq := by simp }
  have hStdFourth :
      ∫ x : ℝ, x ^ (4 : ℕ) ∂gaussianReal 0 1 = 3 := by
    -- Proof comment: reuse the standard Gaussian fourth moment before scaling.
    simpa using gaussianRealFourthMoment_eq_three hStdId
  have hScaleLaw :
      HasLaw (fun x : ℝ ↦ c * x) (gaussianReal 0 v) (gaussianReal 0 1) := by
    -- Proof comment: `N(0, v)` is the image of the standard Gaussian under multiplication by
    -- `sqrt v`.
    simpa [c, sq_abs, Real.sq_sqrt] using
      gaussianReal_const_mul hStdId c
  have hFourthBase :
      ∫ x : ℝ, x ^ (4 : ℕ) ∂gaussianReal 0 v = 3 * ((v : ℝ) ^ (2 : ℕ)) := by
    calc
      ∫ x : ℝ, x ^ (4 : ℕ) ∂gaussianReal 0 v
          = ∫ x : ℝ, (c * x) ^ (4 : ℕ) ∂gaussianReal 0 1 := by
              symm
              simpa [Function.comp] using
                (hScaleLaw.integral_comp ((continuous_pow 4).aestronglyMeasurable))
      _ = ∫ x : ℝ, c ^ (4 : ℕ) * x ^ (4 : ℕ) ∂gaussianReal 0 1 := by
            refine integral_congr_ae ?_
            filter_upwards with x
            rw [mul_pow]
      _ = c ^ (4 : ℕ) * ∫ x : ℝ, x ^ (4 : ℕ) ∂gaussianReal 0 1 := by
            rw [integral_const_mul]
      _ = c ^ (4 : ℕ) * 3 := by
            rw [hStdFourth]
      _ = 3 * ((v : ℝ) ^ (2 : ℕ)) := by
            have hv_nonneg : 0 ≤ (v : ℝ) := by
              exact_mod_cast v.2
            have hsq : c ^ (2 : ℕ) = (v : ℝ) := by
              simp [c, Real.sq_sqrt, hv_nonneg]
            have hpow : c ^ (4 : ℕ) = (v : ℝ) ^ (2 : ℕ) := by
              rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hsq]
            rw [hpow, mul_comm]
  calc
    ∫ ω, Y ω ^ (4 : ℕ) ∂μ = 3 * ((v : ℝ) ^ (2 : ℕ)) := by
      -- Proof comment: push the quartic moment to the Gaussian owner and evaluate it there.
      exact
        ((hLaw0.integral_comp ((continuous_pow 4).aestronglyMeasurable)).trans hFourthBase)
    _ = 3 * Var[Y; μ] ^ (2 : ℕ) := by
          have hv : (v : ℝ) = Var[Y; μ] := by
            simp [v, variance_nonneg Y μ]
          rw [hv]

/-- Helper for Theorem 22.5: on an ordered pair of times in `Set.Icc (0,T)`, the squared subtype
distance is the squared real time gap. -/
private lemma subtypeIccEdistPowTwoEqOfLe
    {T : NNReal} {s t : Set.Icc (0 : NNReal) T} (hst : s.1 ≤ t.1) :
    edist s t ^ (2 : ℝ) = ENNReal.ofReal (((t.1 : ℝ) - s.1) ^ 2) := by
  -- Proof comment: in the ordered branch, the ambient `NNReal` distance is exactly `t - s`.
  rw [show (2 : ℝ) = (2 : ℕ) by norm_num, ENNReal.rpow_natCast]
  rw [edist_dist, Subtype.dist_eq, NNReal.dist_eq]
  have hst_real : (s.1 : ℝ) ≤ t.1 := by
    exact_mod_cast hst
  have hgap_nonneg : 0 ≤ (t.1 : ℝ) - s.1 := sub_nonneg.mpr hst_real
  have habs : |(s.1 : ℝ) - t.1| = (t.1 : ℝ) - s.1 := by
    rw [abs_of_nonpos (sub_nonpos.mpr hst_real)]
    ring
  rw [habs, ← ENNReal.ofReal_pow hgap_nonneg]

/-- Helper for Theorem 22.5: Brownian covariance forces the quartic increment moment to equal
`3 * (t - s)^2`. -/
private lemma brownianIncrementFourthMoment_eq_three_mul_sq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : NNReal → Ω → ℝ}
    (hgauss : IsGaussianProcess X μ)
    (hmean_zero : ∀ t : NNReal, ∫ ω, X t ω ∂μ = 0)
    (hcov : ∀ s t : NNReal, cov[X s, X t; μ] = ((s ⊓ t : NNReal) : ℝ))
    {s t : NNReal} (hst : s ≤ t) :
    ∫ ω, (X t ω - X s ω) ^ (4 : ℕ) ∂μ =
      3 * (((t - s : NNReal) : ℝ) ^ (2 : ℕ)) := by
  letI : IsProbabilityMeasure μ := hgauss.isProbabilityMeasure
  let inc : Ω → ℝ := fun ω ↦ X t ω - X s ω
  have hLaw :
      HasLaw inc (gaussianReal 0 (t - s)) μ :=
    centeredGaussianIncrement_hasLaw_of_brownianCovariance hgauss hmean_zero hcov hst
  have hIncGaussian : HasGaussianLaw inc μ := hLaw.hasGaussianLaw
  have hMean : ∫ ω, inc ω ∂μ = 0 := by
    -- Proof comment: the increment law is the centered Gaussian `N(0, t - s)`.
    simpa [inc] using hLaw.integral_eq
  calc
    ∫ ω, (X t ω - X s ω) ^ (4 : ℕ) ∂μ = 3 * Var[inc; μ] ^ (2 : ℕ) := by
      -- Proof comment: apply the centered Gaussian fourth-moment formula to the increment.
      simpa [inc] using
        centeredGaussianFourthMoment_eq_three_mul_variance_sq hIncGaussian hMean
    _ = 3 * (((t - s : NNReal) : ℝ) ^ (2 : ℕ)) := by
          rw [show Var[inc; μ] = ((t - s : NNReal) : ℝ) by simpa [inc] using hLaw.variance_eq]

/-- Helper for Theorem 22.5: on an ordered pair of times in `Set.Icc (0,T)`, Brownian covariance
gives the quartic Kolmogorov bound with constant `3`. -/
private lemma brownianCovarianceKolmogorovOrderedPairBound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : NNReal → Ω → ℝ}
    (hgauss : IsGaussianProcess X μ)
    (hmean_zero : ∀ t : NNReal, ∫ ω, X t ω ∂μ = 0)
    (hcov : ∀ s t : NNReal, cov[X s, X t; μ] = ((s ⊓ t : NNReal) : ℝ))
    {T : NNReal} :
    ∀ {s t : Set.Icc (0 : NNReal) T}, s.1 ≤ t.1 →
      (∫⁻ ω, edist (X s.1 ω) (X t.1 ω) ^ (4 : ℝ) ∂μ) ≤
        ENNReal.ofReal (3 * (((t.1 : ℝ) - s.1) ^ 2)) := by
  intro s t hst
  let inc : Ω → ℝ := fun ω ↦ X t.1 ω - X s.1 ω
  letI : IsProbabilityMeasure μ := hgauss.isProbabilityMeasure
  have hIncGaussian : HasGaussianLaw inc μ := by
    -- Proof comment: Brownian covariance fixes the ordered increment law.
    exact
      (centeredGaussianIncrement_hasLaw_of_brownianCovariance
        hgauss hmean_zero hcov hst).hasGaussianLaw
  have hIncMemLp : MemLp inc (4 : ℝ≥0∞) μ := hIncGaussian.memLp (by norm_num)
  have hinc_int : Integrable (fun ω ↦ inc ω ^ (4 : ℕ)) μ := by
    -- Proof comment: Gaussian variables have moments of every order.
    refine (hIncMemLp.integrable_norm_pow').congr ?_
    filter_upwards with ω
    have habs : |inc ω| ^ 4 = inc ω ^ 4 := by
      rw [show |inc ω| ^ 4 = (|inc ω| ^ 2) ^ 2 by ring,
        show inc ω ^ 4 = (inc ω ^ 2) ^ 2 by ring, sq_abs]
    simpa [Real.norm_eq_abs] using habs
  have hedist_eq :
      ∫⁻ ω, edist (X s.1 ω) (X t.1 ω) ^ (4 : ℝ) ∂μ =
        ∫⁻ ω, ENNReal.ofReal (inc ω ^ (4 : ℕ)) ∂μ := by
    -- Proof comment: rewrite the metric quartic into the quartic polynomial of the increment.
    refine lintegral_congr_ae ?_
    filter_upwards with ω
    simpa [inc] using realEdist_pow_four_eq_ofReal_sub_pow_four (X s.1 ω) (X t.1 ω)
  have hmoment :
      ∫ ω, inc ω ^ (4 : ℕ) ∂μ = 3 * (((t.1 - s.1 : NNReal) : ℝ) ^ (2 : ℕ)) := by
    -- Proof comment: the explicit Brownian fourth-moment identity supplies the Kolmogorov bound.
    simpa [inc] using
      brownianIncrementFourthMoment_eq_three_mul_sq hgauss hmean_zero hcov hst
  calc
    ∫⁻ ω, edist (X s.1 ω) (X t.1 ω) ^ (4 : ℝ) ∂μ
        = ENNReal.ofReal (∫ ω, inc ω ^ (4 : ℕ) ∂μ) := by
            rw [hedist_eq]
            symm
            exact
              MeasureTheory.ofReal_integral_eq_lintegral_ofReal hinc_int
                (Filter.Eventually.of_forall fun ω ↦ by positivity)
    _ = ENNReal.ofReal (3 * (((t.1 - s.1 : NNReal) : ℝ) ^ (2 : ℕ))) := by
          rw [hmoment]
    _ = ENNReal.ofReal (3 * (((t.1 : ℝ) - s.1) ^ 2)) := by
          rw [NNReal.coe_sub hst]
    _ ≤ ENNReal.ofReal (3 * (((t.1 : ℝ) - s.1) ^ 2)) := le_rfl

/-- Helper for Theorem 22.5: Brownian covariance yields the quartic increment bound required on
every finite interval `[0,T]`. -/
private lemma brownianCovarianceKolmogorovOnIcc_quartic
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : NNReal → Ω → ℝ}
    (hgauss : IsGaussianProcess X μ)
    (hmean_zero : ∀ t : NNReal, ∫ ω, X t ω ∂μ = 0)
    (hcov : ∀ s t : NNReal, cov[X s, X t; μ] = ((s ⊓ t : NNReal) : ℝ))
    (T : NNReal) :
    ∀ s t : Set.Icc (0 : NNReal) T,
      (∫⁻ ω, edist (X s.1 ω) (X t.1 ω) ^ (4 : ℝ) ∂μ) ≤
        (3 : ℝ≥0∞) * edist s t ^ (2 : ℝ) := by
  intro s t
  -- Proof comment: reduce to the ordered branch; the reversed branch only swaps the endpoints.
  by_cases hst : s.1 ≤ t.1
  · have hthree_nonneg : (0 : ℝ) ≤ 3 := by norm_num
    rw [subtypeIccEdistPowTwoEqOfLe hst]
    calc
      ∫⁻ ω, edist (X s.1 ω) (X t.1 ω) ^ (4 : ℝ) ∂μ
          ≤ ENNReal.ofReal (3 * (((t.1 : ℝ) - s.1) ^ 2)) := by
              exact brownianCovarianceKolmogorovOrderedPairBound hgauss hmean_zero hcov hst
      _ = (3 : ℝ≥0∞) * ENNReal.ofReal (((t.1 : ℝ) - s.1) ^ 2) := by
            rw [ENNReal.ofReal_mul hthree_nonneg]
            norm_num
  · have hts : t.1 ≤ s.1 := le_of_not_ge hst
    have hthree_nonneg : (0 : ℝ) ≤ 3 := by norm_num
    rw [edist_comm, subtypeIccEdistPowTwoEqOfLe hts]
    calc
      ∫⁻ ω, edist (X s.1 ω) (X t.1 ω) ^ (4 : ℝ) ∂μ
          = ∫⁻ ω, edist (X t.1 ω) (X s.1 ω) ^ (4 : ℝ) ∂μ := by
              refine lintegral_congr_ae ?_
              filter_upwards with ω
              rw [edist_comm]
      _ ≤ ENNReal.ofReal (3 * (((s.1 : ℝ) - t.1) ^ 2)) := by
            simpa using
              (brownianCovarianceKolmogorovOrderedPairBound hgauss hmean_zero hcov hts :
                (∫⁻ ω, edist (X t.1 ω) (X s.1 ω) ^ (4 : ℝ) ∂μ) ≤
                  ENNReal.ofReal (3 * (((s.1 : ℝ) - t.1) ^ 2)))
      _ = (3 : ℝ≥0∞) * ENNReal.ofReal (((s.1 : ℝ) - t.1) ^ 2) := by
            rw [ENNReal.ofReal_mul hthree_nonneg]
            norm_num

/-- Helper for Theorem 22.5: the quartic Brownian increment bound on `[0,T]` matches the
Kolmogorov-owner exponent spelling `q = 1 + 1`. -/
private lemma brownianCovarianceKolmogorovOnIcc_quarticOwnerBound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : NNReal → Ω → ℝ}
    (hgauss : IsGaussianProcess X μ)
    (hmean_zero : ∀ t : NNReal, ∫ ω, X t ω ∂μ = 0)
    (hcov : ∀ s t : NNReal, cov[X s, X t; μ] = ((s ⊓ t : NNReal) : ℝ))
    (T : NNReal) :
    ∀ s t : Set.Icc (0 : NNReal) T,
      (∫⁻ ω, edist (X s.1 ω) (X t.1 ω) ^ ((4 : ℝ≥0) : ℝ) ∂μ) ≤
        (3 : ℝ≥0∞) * edist s t ^ (1 + ((1 : ℝ≥0) : ℝ)) := by
  intro s t
  have hquartic :=
    brownianCovarianceKolmogorovOnIcc_quartic hgauss hmean_zero hcov T s t
  convert hquartic using 1 <;> norm_num

/-- Helper for Theorem 22.5: Brownian covariance data admit an almost surely continuous
modification via the quartic Kolmogorov-Chentsov owner. -/
private theorem existsAeContinuousRealModificationOfBrownianCovariance
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : NNReal → Ω → ℝ}
    (hgauss : IsGaussianProcess X μ)
    (hmean_zero : ∀ t : NNReal, ∫ ω, X t ω ∂μ = 0)
    (hcov : ∀ s t : NNReal, cov[X s, X t; μ] = ((s ⊓ t : NNReal) : ℝ)) :
    ∃ Y : NNReal → Ω → ℝ,
      AreModifications μ Y X ∧
        HasAlmostSurelyContinuousPaths μ Y := by
  let γ : ℝ≥0 := (1 : ℝ≥0) / 8
  have hγpos : 0 < γ := by
    norm_num [γ]
  have hγlt : (γ : ℝ) < (1 : ℝ) / 4 := by
    norm_num [γ]
  have hγle : γ ≤ 1 := by
    have h8 : (1 : ℝ≥0) ≤ 8 := by norm_num
    have h : ((1 : ℝ≥0) / 8 : ℝ≥0) ≤ 1 := by
      exact div_le_self (by positivity : 0 ≤ (1 : ℝ≥0)) h8
    change ((1 : ℝ≥0) / 8 : ℝ≥0) ≤ 1
    exact h
  let Xm : NNReal → Ω → ℝ := fun t ↦ (hgauss.aemeasurable t).mk (X t)
  have hXmEq : ∀ t : NNReal, X t =ᵐ[μ] Xm t := by
    intro t
    simpa [Xm] using (hgauss.aemeasurable t).ae_eq_mk
  have hXmGauss : IsGaussianProcess Xm μ := by
    -- Proof comment: fixed-time measurable representatives preserve the finite-dimensional
    -- Gaussian laws of the original process.
    exact hgauss.congr hXmEq
  have hXmMeanZero : ∀ t : NNReal, ∫ ω, Xm t ω ∂μ = 0 := by
    intro t
    -- Proof comment: the centered mean transfers across the almost-sure equality `X t = Xm t`.
    calc
      ∫ ω, Xm t ω ∂μ = ∫ ω, X t ω ∂μ := by
        symm
        exact integral_congr_ae (hXmEq t)
      _ = 0 := hmean_zero t
  have hXmCov : ∀ s t : NNReal, cov[Xm s, Xm t; μ] = ((s ⊓ t : NNReal) : ℝ) := by
    intro s t
    -- Proof comment: covariance is invariant under almost-sure replacement of each coordinate.
    rw [← covariance_congr_ae (hXmEq s) (hXmEq t), hcov s t]
  have hkolm :
      ∀ T : NNReal, ∃ α β C : ℝ≥0, IsKolmogorovProcessOnIcc μ Xm T α β C := by
    intro T
    refine ⟨(4 : ℝ≥0), (1 : ℝ≥0), (3 : ℝ≥0), ?_⟩
    refine ⟨by norm_num, by norm_num, ?_⟩
    exact
      IsKolmogorovProcess.mk_of_secondCountableTopology
        (fun t : Set.Icc (0 : NNReal) T ↦ (hgauss.aemeasurable t.1).measurable_mk)
        (brownianCovarianceKolmogorovOnIcc_quarticOwnerBound
          hXmGauss hXmMeanZero hXmCov T)
        (by norm_num)
        (by norm_num)
  rcases exists_modification_with_locally_holder_paths hkolm with
    ⟨Y, hmod, hholder, -⟩
  refine ⟨Y, ?_, ?_⟩
  · intro t
    -- Proof comment: the Kolmogorov output modifies the measurable proxy `Xm`, which in turn
    -- agrees almost surely with the original process `X`.
    filter_upwards [hXmEq t, hmod t] with ω hωXm hωmod
    exact hωmod.symm.trans hωXm.symm
  let γIoc : Set.Ioc (0 : ℝ≥0) (1 : ℝ≥0) := ⟨γ, ⟨hγpos, hγle⟩⟩
  refine Filter.Eventually.of_forall fun ω ↦ ?_
  -- Proof comment: the returned local Hölder control at exponent `1 / 8` upgrades every path to
  -- continuity.
  have hloc : LocallyHolderWith γIoc (processPath Y ω) := by
    simpa [processPath_apply, γIoc, γ] using hholder γ hγpos
      (fun T ↦ by
        refine ⟨(4 : ℝ≥0), (1 : ℝ≥0), (3 : ℝ≥0), ?_, ?_⟩
        · refine ⟨by norm_num, by norm_num, ?_⟩
          exact
            IsKolmogorovProcess.mk_of_secondCountableTopology
              (fun t : Set.Icc (0 : NNReal) T ↦ (hgauss.aemeasurable t.1).measurable_mk)
              (brownianCovarianceKolmogorovOnIcc_quarticOwnerBound
                hXmGauss hXmMeanZero hXmCov T)
              (by norm_num)
              (by norm_num)
        · simpa using hγlt) ω
  exact continuous_of_locallyHolderWith hloc

/-- Helper for Theorem 22.5: patching an almost surely continuous modification on the
discontinuity null set yields an everywhere-continuous modification. -/
private theorem patchContinuousModificationToEverywhere
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X Y : NNReal → Ω → ℝ}
    (hmod : AreModifications μ Y X)
    (hcont : HasAlmostSurelyContinuousPaths μ Y) :
    ∃ Yc : NNReal → Ω → ℝ,
      AreModifications μ Yc X ∧
        (∀ ω, Continuous fun t : NNReal ↦ Yc t ω) := by
  classical
  let S : Set Ω := {ω | Continuous fun t : NNReal ↦ Y t ω}
  let Yc : NNReal → Ω → ℝ := fun t ω ↦ if ω ∈ S then Y t ω else 0
  have hSae : ∀ᵐ ω ∂μ, ω ∈ S := by
    simpa [S, HasAlmostSurelyContinuousPaths, processPath] using hcont
  refine ⟨Yc, ?_, ?_⟩
  · intro t
    -- Proof comment: outside the null exceptional set, the patched process agrees with `Y`,
    -- hence still modifies `X`.
    filter_upwards [hSae, hmod t] with ω hω hωmod
    simpa [Yc, hω] using hωmod
  · intro ω
    -- Proof comment: each path is either the original continuous path or the constant zero path.
    by_cases hω : ω ∈ S
    · have hcont : Continuous fun t : NNReal ↦ Y t ω := by
        simpa [S] using hω
      simpa [Yc, hω] using hcont
    · simpa [Yc, hω] using (continuous_const : Continuous fun _ : NNReal ↦ (0 : ℝ))

/-- Helper for Theorem 22.5: Brownian covariance data on the canonical Gaussian owner admit an
everywhere-continuous modification. -/
private theorem existsContinuousRealModificationOfBrownianCovariance
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : NNReal → Ω → ℝ}
    (hgauss : IsGaussianProcess X μ)
    (hmean_zero : ∀ t : NNReal, ∫ ω, X t ω ∂μ = 0)
    (hcov : ∀ s t : NNReal, cov[X s, X t; μ] = ((s ⊓ t : NNReal) : ℝ)) :
    ∃ Y : NNReal → Ω → ℝ,
      AreModifications μ Y X ∧
        (∀ ω, Continuous fun t : NNReal ↦ Y t ω) := by
  -- Route correction: split the Kolmogorov-Chentsov step from the final null-set patch so the
  -- heavy measurable-representative assembly only happens once.
  obtain ⟨Y, hmodY, hcontY⟩ :=
    existsAeContinuousRealModificationOfBrownianCovariance
      (μ := μ) hgauss hmean_zero hcov
  -- Proof comment: the a.s.-continuous modification becomes everywhere continuous after replacing
  -- the exceptional paths by the zero path.
  exact patchContinuousModificationToEverywhere hmodY hcontY

/-- Helper for Theorem 22.5: patching a Brownian motion on a null exceptional set preserves the
Brownian owner while producing pointwise continuous paths. -/
private theorem brownianContinuousVersion_isBrownianMotionLocal
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : NNReal → Ω → ℝ}
    (hB : IsBrownianMotion μ B) :
    IsBrownianMotion μ (brownianContinuousVersion (μ := μ) (B := B) hB) := by
  -- Proof comment: the Brownian characterization is stable under fixed-time almost-everywhere
  -- modification, and the patched process has continuous paths by construction.
  rw [isBrownianMotion_iff_isCenteredGaussianProcessWithBrownianCovariance]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · funext ω
    simpa using brownianContinuousVersion_zero (μ := μ) (B := B) hB ω
  · exact
      hB.isGaussianProcess.congr
        (fun t ↦ brownianContinuousVersion_areModifications (μ := μ) (B := B) hB t)
  · intro t
    exact
      (integral_congr_ae
        (brownianContinuousVersion_areModifications (μ := μ) (B := B) hB t)).symm.trans
        (hB.mean_zero t)
  · intro s t
    exact
      (covariance_congr_ae
        (brownianContinuousVersion_areModifications (μ := μ) (B := B) hB s)
        (brownianContinuousVersion_areModifications (μ := μ) (B := B) hB t)).symm.trans
        (hB.covariance_eq s t)
  · filter_upwards with ω
    simpa [HasAlmostSurelyContinuousPaths, processPath] using
      brownianContinuousVersion_continuous (μ := μ) (B := B) hB ω

/-- Helper for Theorem 22.5: for a closed nonempty target set, the exact hitting time is the
same as the `0`-hitting time of the associated distance process. -/
private theorem hittingAfter_eq_infDist_hittingAfter
    {Ω State : Type*} [MeasurableSpace Ω] [MetricSpace State]
    {X : NNReal → Ω → State} {C : Set State}
    (hCclosed : IsClosed C) (hCnonempty : C.Nonempty) :
    MeasureTheory.hittingAfter X C (0 : NNReal) =
      MeasureTheory.hittingAfter (fun t ω ↦ Metric.infDist (X t ω) C) ({0} : Set ℝ)
        (0 : NNReal) := by
  classical
  ext ω
  -- Proof comment: after rewriting membership in `C` as vanishing distance to `C`, both
  -- `hittingAfter` definitions use the same witness condition and the same `sInf` set.
  have hCond :
      (∃ j, (0 : NNReal) ≤ j ∧ X j ω ∈ C) ↔
        ∃ j, (0 : NNReal) ≤ j ∧ Metric.infDist (X j ω) C ∈ ({0} : Set ℝ) := by
    simp [Set.mem_singleton_iff, hCclosed.mem_iff_infDist_zero hCnonempty]
  change
    (if ∃ j, (0 : NNReal) ≤ j ∧ X j ω ∈ C then
        ((sInf {i : NNReal | (0 : NNReal) ≤ i ∧ X i ω ∈ C} : NNReal) : ENNReal)
      else ⊤) =
      (if ∃ j, (0 : NNReal) ≤ j ∧ Metric.infDist (X j ω) C ∈ ({0} : Set ℝ) then
        ((sInf
            {i : NNReal | (0 : NNReal) ≤ i ∧ Metric.infDist (X i ω) C ∈ ({0} : Set ℝ)} :
              NNReal) : ENNReal)
      else ⊤)
  by_cases h : ∃ j, (0 : NNReal) ≤ j ∧ X j ω ∈ C
  · have h' :
        ∃ j, (0 : NNReal) ≤ j ∧ Metric.infDist (X j ω) C ∈ ({0} : Set ℝ) :=
      hCond.mp h
    rw [if_pos h, if_pos h']
    congr 1
    ext j
    simp [Set.mem_singleton_iff, hCclosed.mem_iff_infDist_zero hCnonempty]
  · have h' :
        ¬ ∃ j, (0 : NNReal) ≤ j ∧ Metric.infDist (X j ω) C ∈ ({0} : Set ℝ) := by
      exact mt hCond.mpr h
    rw [if_neg h, if_neg h']

/-- Helper for Theorem 22.5: a continuous process hits any closed nonempty target at a stopping
time in its natural filtration. -/
private theorem hittingClosed_isStoppingTime_of_continuous_natural
    {Ω State : Type*} [MeasurableSpace Ω] [MetricSpace State] [MeasurableSpace State]
    [BorelSpace State]
    {X : NNReal → Ω → State}
    (hXsm : ∀ t, StronglyMeasurable (X t))
    (hXcont : ∀ ω, Continuous fun t : NNReal ↦ X t ω)
    {C : Set State} (hCclosed : IsClosed C) (hCnonempty : C.Nonempty) :
    IsStoppingTime (Filtration.natural X hXsm) (hittingAfter X C 0) := by
  let D : NNReal → Ω → ℝ := fun t ω ↦ Metric.infDist (X t ω) C
  have hDsm : ∀ t : NNReal, StronglyMeasurable (D t) := by
    intro t
    -- Proof comment: each distance slice is the measurable time-`t` slice of `X`
    -- followed by the continuous map `x ↦ infDist x C`.
    exact ((Metric.continuous_infDist_pt C).measurable.comp (hXsm t).measurable).stronglyMeasurable
  have hXstrong :
      StronglyAdapted (Filtration.natural X hXsm) X :=
    Filtration.stronglyAdapted_natural (u := X) hXsm
  have hDadapted : Adapted (Filtration.natural X hXsm) D := by
    intro t
    -- Proof comment: the natural filtration already sees `X t`, so it also sees the
    -- distance-to-`C` observable at time `t`.
    exact ((Metric.continuous_infDist_pt C).measurable.comp
      (hXstrong.stronglyMeasurable_le (i := t) (j := t) le_rfl).measurable)
  have hDnat :
      Filtration.natural D hDsm ≤ Filtration.natural X hXsm :=
    (adapted_iff_natural_le hDsm).1 hDadapted
  have hτdist :
      IsStoppingTime (Filtration.natural D hDsm) (hittingAfter D ({0} : Set ℝ) 0) := by
    have hpair : ({(0 : ℝ), 0} : Set ℝ) = ({0} : Set ℝ) := by
      ext y
      simp
    -- Proof comment: the closed-target hitting time becomes a scalar `0`-hitting time
    -- for the continuous distance process.
    simpa [hpair] using
      twoSidedBoundaryHittingTime_isStoppingTime_of_continuous
        (X := D) hDsm (fun ω ↦ (Metric.continuous_infDist_pt C).comp (hXcont ω)) (a := 0) (b := 0)
  have hτdistX :
      IsStoppingTime (Filtration.natural X hXsm) (hittingAfter D ({0} : Set ℝ) 0) := by
    intro t
    exact hDnat t _ (hτdist t)
  -- Proof comment: transport the scalar stopping-time statement back through the exact
  -- identification of the two hitting times.
  simpa [D, hittingAfter_eq_infDist_hittingAfter
    (X := X) (C := C) hCclosed hCnonempty] using hτdistX

/-- Helper for Theorem 22.5: the exact two-sided boundary hit for a Brownian motion agrees almost
surely with the same construction on its continuous modification. -/
private theorem twoSidedBoundaryExact_ae_eq_continuousVersion
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : NNReal → Ω → ℝ}
    (hB : IsBrownianMotion μ B) {a b : ℝ} :
    let Bc := brownianContinuousVersion (μ := μ) (B := B) hB
    let τ : Ω → ENNReal := hittingAfter B ({a, b} : Set ℝ) 0
    let τc : Ω → ENNReal := hittingAfter Bc ({a, b} : Set ℝ) 0
    ∀ᵐ ω ∂μ,
      τ ω = τc ω ∧
        stoppedValue B τ ω = stoppedValue Bc τc ω := by
  let Bc := brownianContinuousVersion (μ := μ) (B := B) hB
  let τ : Ω → ENNReal := hittingAfter B ({a, b} : Set ℝ) 0
  let τc : Ω → ENNReal := hittingAfter Bc ({a, b} : Set ℝ) 0
  filter_upwards [brownianContinuousVersion_ae_eq (μ := μ) (B := B) hB] with ω hω
  have hτ :
      τ ω = τc ω := by
    -- Proof comment: pathwise equality of every time slice identifies the exact hitting time.
    simpa [τ, τc, Bc] using
      (twoSidedBoundaryHittingTime_eq_of_forall_eq
        (X := B) (Y := Bc) (a := a) (b := b) (ω := ω) fun t ↦ (hω t).symm)
  have hidx :
      (τ ω).untopA = (τc ω).untopA := by
    simpa using congrArg WithTop.untopA hτ
  refine ⟨hτ, ?_⟩
  -- Proof comment: once the exact hitting times agree, the stopped values are evaluations of
  -- pointwise-equal paths at the same index.
  calc
    stoppedValue B τ ω = B (τ ω).untopA ω := rfl
    _ = Bc (τ ω).untopA ω := by simpa using (hω (τ ω).untopA).symm
    _ = Bc (τc ω).untopA ω := by rw [hidx]
    _ = stoppedValue Bc τc ω := rfl

/-- Helper for Theorem 22.5: the exact two-sided stopped value is almost everywhere measurable. -/
private theorem twoSidedBoundaryStoppedValue_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : NNReal → Ω → ℝ}
    (hB : IsBrownianMotion μ B) {a b : ℝ} :
    let Bc := brownianContinuousVersion (μ := μ) (B := B) hB
    let hBc : IsBrownianMotion μ Bc :=
      brownianContinuousVersion_isBrownianMotionLocal (μ := μ) (B := B) hB
    let τ : Ω → ENNReal := hittingAfter B ({a, b} : Set ℝ) 0
    let τc : Ω → ENNReal := hittingAfter Bc ({a, b} : Set ℝ) 0
    AEMeasurable (fun ω ↦ stoppedValue B τ ω) μ := by
  let Bc := brownianContinuousVersion (μ := μ) (B := B) hB
  let hBc : IsBrownianMotion μ Bc :=
    brownianContinuousVersion_isBrownianMotionLocal (μ := μ) (B := B) hB
  let τ : Ω → ENNReal := hittingAfter B ({a, b} : Set ℝ) 0
  let τc : Ω → ENNReal := hittingAfter Bc ({a, b} : Set ℝ) 0
  have hτc :
      IsStoppingTime (Filtration.natural Bc hBc.stronglyMeasurable) τc := by
    -- Proof comment: the exact hit time is measurable for the continuous Brownian version.
    simpa [τc] using
      (twoSidedBoundaryHittingTime_isStoppingTime_of_continuous
        (X := Bc) hBc.stronglyMeasurable
        (brownianContinuousVersion_continuous (μ := μ) (B := B) hB) (a := a) (b := b))
  have hBcStrong :
      StronglyAdapted (Filtration.natural Bc hBc.stronglyMeasurable) Bc :=
    Filtration.stronglyAdapted_natural (u := Bc) hBc.stronglyMeasurable
  have hBcProg :
      ProgMeasurable (Filtration.natural Bc hBc.stronglyMeasurable) Bc :=
    hBcStrong.progMeasurable_of_continuous
      (brownianContinuousVersion_continuous (μ := μ) (B := B) hB)
  have hMeasBc : Measurable (stoppedValue Bc τc) := by
    exact (measurable_stoppedValue hBcProg hτc).mono hτc.measurableSpace_le le_rfl
  have hEqAe :
      (fun ω ↦ stoppedValue B τ ω) =ᵐ[μ] fun ω ↦ stoppedValue Bc τc ω := by
    filter_upwards
      [twoSidedBoundaryExact_ae_eq_continuousVersion
        (μ := μ) (B := B) (hB := hB) (a := a) (b := b)]
      with ω hω
    exact hω.2
  -- Proof comment: transport almost-surely from the measurable continuous-version stopped value.
  exact hMeasBc.aemeasurable.congr hEqAe.symm

/-- Helper for Theorem 22.5: the lower-tail event of an endpoint-valued piecewise random variable
has the three textbook regimes `∅`, `Eᶜ`, and `univ`. -/
private lemma twoPointPiecewise_preimage_Iic
    {Ω : Type*} (E : Set Ω) [DecidablePred (· ∈ E)] {u v x : ℝ} (huv : u ≤ v) :
    {ω | E.piecewise (fun _ ↦ v) (fun _ ↦ u) ω ≤ x} =
      if x < u then ∅ else if x < v then Eᶜ else Set.univ := by
  by_cases hxu : x < u
  · have hxv : x < v := lt_of_lt_of_le hxu huv
    ext ω
    by_cases hω : ω ∈ E
    · -- Proof comment: below the left endpoint, neither branch of the piecewise variable can
      -- fall into `Iic x`.
      simpa [Set.mem_setOf_eq, hω, hxu, hxv, not_le.mpr hxv]
    · simpa [Set.mem_setOf_eq, hω, hxu, hxv, not_le.mpr hxu]
  · have hux : u ≤ x := le_of_not_gt hxu
    by_cases hxv : x < v
    · ext ω
      by_cases hω : ω ∈ E
      · -- Proof comment: in the middle regime, the upper branch lies above `x`, so only the
        -- complement event contributes to the lower tail.
        simpa [Set.mem_setOf_eq, hω, hxu, hxv, not_le.mpr hxv]
      · simpa [Set.mem_setOf_eq, hω, hxu, hxv, hux]
    · have hvx : v ≤ x := le_of_not_gt hxv
      ext ω
      by_cases hω : ω ∈ E
      · -- Proof comment: once `x` is above the right endpoint, both branches lie in `Iic x`.
        simpa [Set.mem_setOf_eq, hω, hxu, hxv, hvx]
      · simpa [Set.mem_setOf_eq, hω, hxu, hxv, hux]

/-- Helper for Theorem 22.5: at a fixed pair of barriers, the stopped Brownian value has exactly
the centered two-point law from Lemma 22.8. -/
private lemma negativeNonnegativeTwoPointKernel_apply_Iic
    (z : PairSpace) (x : ℝ) :
    negativeNonnegativeTwoPointKernel z (Set.Iic x) =
      if x < (z.1 : ℝ) then 0
      else if x < z.2 then ENNReal.ofReal (z.2 / (z.2 - (z.1 : ℝ))) else 1 := by
  rcases z with ⟨u, v⟩
  have huv : (u : ℝ) < v := lt_of_lt_of_le u.2 v.2
  have hdenom : 0 < (v : ℝ) - (u : ℝ) := sub_pos.mpr huv
  have hweightFst_nonneg : 0 ≤ (v : ℝ) / ((v : ℝ) - (u : ℝ)) := by
    exact div_nonneg v.2 hdenom.le
  have hweightSnd_nonneg : 0 ≤ (-(u : ℝ)) / ((v : ℝ) - (u : ℝ)) := by
    exact div_nonneg (neg_nonneg.mpr u.2.le) hdenom.le
  have hsum :
      (v : ℝ) / ((v : ℝ) - (u : ℝ)) + (-(u : ℝ)) / ((v : ℝ) - (u : ℝ)) = 1 := by
    field_simp [hdenom.ne']
    ring
  by_cases hxu : x < (u : ℝ)
  · have hxv : x < (v : ℝ) := lt_of_lt_of_le hxu huv.le
    have hu_not_mem : (u : ℝ) ∉ Set.Iic x := by
      simpa [Set.mem_Iic] using not_le.mpr hxu
    have hv_not_mem : (v : ℝ) ∉ Set.Iic x := by
      simpa [Set.mem_Iic] using not_le.mpr hxv
    -- Proof comment: below the left endpoint, neither Dirac atom contributes to the lower tail.
    rw [negativeNonnegativeTwoPointKernel_apply, Measure.add_apply]
    simp only [Measure.coe_smul, Pi.smul_apply, smul_eq_mul]
    rw [Measure.dirac_apply, Measure.dirac_apply]
    rw [Set.indicator_of_notMem hu_not_mem, Set.indicator_of_notMem hv_not_mem]
    simp [hxu, hxv]
  · have hux : (u : ℝ) ≤ x := le_of_not_gt hxu
    by_cases hxv : x < (v : ℝ)
    · have hu_mem : (u : ℝ) ∈ Set.Iic x := by
        simpa [Set.mem_Iic] using hux
      have hv_not_mem : (v : ℝ) ∉ Set.Iic x := by
        simpa [Set.mem_Iic] using not_le.mpr hxv
      -- Proof comment: between the two endpoints, only the left atom at `u` lies in `Iic x`.
      rw [negativeNonnegativeTwoPointKernel_apply, Measure.add_apply]
      simp only [Measure.coe_smul, Pi.smul_apply, smul_eq_mul]
      rw [Measure.dirac_apply, Measure.dirac_apply]
      rw [Set.indicator_of_mem hu_mem, Set.indicator_of_notMem hv_not_mem]
      rw [if_neg hxu, if_pos hxv]
      simp
    · have hvx : (v : ℝ) ≤ x := le_of_not_gt hxv
      have hu_mem : (u : ℝ) ∈ Set.Iic x := by
        simpa [Set.mem_Iic] using hux
      have hv_mem : (v : ℝ) ∈ Set.Iic x := by
        simpa [Set.mem_Iic] using hvx
      have hsumENN :
          ENNReal.ofReal ((v : ℝ) / ((v : ℝ) - (u : ℝ))) +
            ENNReal.ofReal (-(u : ℝ) / ((v : ℝ) - (u : ℝ))) = 1 := by
        rw [← ENNReal.ofReal_add hweightFst_nonneg hweightSnd_nonneg, hsum, ENNReal.ofReal_one]
      -- Proof comment: above the right endpoint, both atoms contribute and their weights add to
      -- `1`.
      rw [negativeNonnegativeTwoPointKernel_apply, Measure.add_apply]
      simp only [Measure.coe_smul, Pi.smul_apply, smul_eq_mul]
      rw [Measure.dirac_apply, Measure.dirac_apply]
      rw [Set.indicator_of_mem hu_mem, Set.indicator_of_mem hv_mem]
      rw [if_neg hxu, if_neg hxv]
      simpa [hsumENN]

private theorem brownianTwoPointExit_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {P : ProbabilityMeasure Ω}
    {B : NNReal → Ω → ℝ}
    (hB : IsBrownianMotion (P : Measure Ω) B)
    (z : PairSpace) :
    HasLaw
      (stoppedValue B (hittingAfter B ({(z.1 : ℝ), (z.2 : ℝ)} : Set ℝ) 0))
      (negativeNonnegativeTwoPointKernel z)
      (P : Measure Ω) := by
  classical
  let τ : Ω → ENNReal := hittingAfter B ({(z.1 : ℝ), (z.2 : ℝ)} : Set ℝ) 0
  let X : Ω → ℝ := stoppedValue B τ
  by_cases hz0 : (z.2 : ℝ) = 0
  · have hτ_zero : ∀ ω, τ ω = 0 := by
      intro ω
      apply le_antisymm
      · have hmem : B 0 ω ∈ ({(z.1 : ℝ), (z.2 : ℝ)} : Set ℝ) := by
          rw [Set.mem_insert_iff, Set.mem_singleton_iff, congrFun hB.zero ω]
          exact Or.inr hz0.symm
        exact hittingAfter_le_of_mem (u := B) (s := ({(z.1 : ℝ), (z.2 : ℝ)} : Set ℝ))
          (n := 0) (ω := ω) (by simp) hmem
      · exact le_hittingAfter (u := B) (s := ({(z.1 : ℝ), (z.2 : ℝ)} : Set ℝ)) (n := 0) ω
    have hX_eq : ∀ ω : Ω, X ω = 0 := by
      intro ω
      -- Proof comment: when the upper endpoint is `0`, the exact hit occurs at time `0`, so the
      -- stopped value is the Brownian start value `0`.
      calc
        X ω = B (τ ω).untopA ω := rfl
        _ = B 0 ω := by
              have hidx : (τ ω).untopA = 0 := by
                rw [hτ_zero ω]
                rw [WithTop.untopA_eq_untop (show (0 : ENNReal) ≠ ⊤ by simp)]
                rfl
              rw [hidx]
        _ = 0 := congrFun hB.zero ω
    have hX_ae : X =ᵐ[(P : Measure Ω)] fun _ : Ω ↦ (0 : ℝ) := by
      exact Filter.Eventually.of_forall hX_eq
    refine
      { aemeasurable := aemeasurable_const.congr hX_ae.symm
        map_eq := ?_ }
    refine Measure.ext_of_Iic (μ := (P : Measure Ω).map X) (ν := negativeNonnegativeTwoPointKernel z)
      fun x ↦ ?_
    have hmapX :
        (P : Measure Ω).map X (Set.Iic x) = (P : Measure Ω) {ω | X ω ≤ x} := by
      rw [Measure.map_apply_of_aemeasurable
        ((aemeasurable_const : AEMeasurable (fun _ : Ω ↦ (0 : ℝ)) (P : Measure Ω)).congr
          hX_ae.symm) measurableSet_Iic]
      rfl
    have hset :
        {ω | X ω ≤ x} = if x < 0 then ∅ else Set.univ := by
      by_cases hx0 : x < 0
      · ext ω
        simp [hX_eq ω, hx0]
      · have hx0' : 0 ≤ x := le_of_not_gt hx0
        ext ω
        simp [hX_eq ω, hx0, hx0']
    have hkernel :
        negativeNonnegativeTwoPointKernel z (Set.Iic x) = if x < 0 then 0 else 1 := by
      by_cases hx0 : x < 0
      · by_cases hxu : x < (z.1 : ℝ)
        · calc
            negativeNonnegativeTwoPointKernel z (Set.Iic x) = 0 := by
              rw [negativeNonnegativeTwoPointKernel_apply_Iic, if_pos hxu]
          _ = if x < 0 then 0 else 1 := by simp [hx0]
        · have hxv : x < (z.2 : ℝ) := by
            rw [hz0]
            exact hx0
          calc
            negativeNonnegativeTwoPointKernel z (Set.Iic x)
                = ENNReal.ofReal (z.2 / (z.2 - (z.1 : ℝ))) := by
                    rw [negativeNonnegativeTwoPointKernel_apply_Iic, if_neg hxu, if_pos hxv]
            _ = 0 := by rw [hz0]; simp
            _ = if x < 0 then 0 else 1 := by simp [hx0]
      · have hx0' : 0 ≤ x := le_of_not_gt hx0
        have hxu : ¬ x < (z.1 : ℝ) := by
          exact not_lt.mpr (le_trans z.1.2.le hx0')
        have hxv : ¬ x < (z.2 : ℝ) := by
          rw [hz0]
          exact hx0
        calc
          negativeNonnegativeTwoPointKernel z (Set.Iic x) = 1 := by
            rw [negativeNonnegativeTwoPointKernel_apply_Iic, if_neg hxu, if_neg hxv]
          _ = if x < 0 then 0 else 1 := by simp [hx0]
    -- Proof comment: both the stopped value and the kernel collapse to the Dirac law at `0`.
    rw [hmapX, hset, hkernel]
    by_cases hx0 : x < 0 <;> simp [hx0]
  · have hzpos : 0 < (z.2 : ℝ) := by
      exact lt_of_le_of_ne z.2.2 fun h ↦ hz0 h.symm
    have hX_aemeas : AEMeasurable X (P : Measure Ω) :=
      twoSidedBoundaryStoppedValue_aemeasurable (μ := (P : Measure Ω)) (B := B)
        (hB := hB) (a := (z.1 : ℝ)) (b := (z.2 : ℝ))
    have hE_null :
        NullMeasurableSet {ω | X ω = (z.2 : ℝ)} (P : Measure Ω) := by
      simpa [X, τ] using
        hX_aemeas.nullMeasurableSet_preimage (measurableSet_singleton (z.2 : ℝ))
    refine
      { aemeasurable := hX_aemeas
        map_eq := ?_ }
    refine Measure.ext_of_Iic (μ := (P : Measure Ω).map X) (ν := negativeNonnegativeTwoPointKernel z)
      fun x ↦ ?_
    have hmapX :
        (P : Measure Ω).map X (Set.Iic x) = (P : Measure Ω) {ω | X ω ≤ x} := by
      rw [Measure.map_apply_of_aemeasurable hX_aemeas measurableSet_Iic]
      rfl
    have hpiece :
        ∀ᵐ ω ∂(P : Measure Ω),
          X ω =
            ({ω' | X ω' = (z.2 : ℝ)} : Set Ω).piecewise
              (fun _ ↦ (z.2 : ℝ)) (fun _ ↦ (z.1 : ℝ)) ω := by
      simpa [X, τ] using
        twoSidedBoundaryStoppedValue_ae_eq_piecewise
          (hB := hB) (a := (z.1 : ℝ)) (b := (z.2 : ℝ)) z.1.2 hzpos
    have hpieceSet :
        {ω | X ω ≤ x} =ᵐ[(P : Measure Ω)]
          {ω |
            ({ω' | X ω' = (z.2 : ℝ)} : Set Ω).piecewise
              (fun _ ↦ (z.2 : ℝ)) (fun _ ↦ (z.1 : ℝ)) ω ≤ x} := by
      filter_upwards [hpiece] with ω hω
      change (X ω ≤ x) = ((({ω' | X ω' = (z.2 : ℝ)} : Set Ω).piecewise
        (fun _ ↦ (z.2 : ℝ)) (fun _ ↦ (z.1 : ℝ)) ω) ≤ x)
      rw [hω]
    have hprob :
        (P : Measure Ω) {ω | X ω = (z.2 : ℝ)} =
          ENNReal.ofReal (-(z.1 : ℝ) / (z.2 - (z.1 : ℝ))) := by
      simpa [X, τ] using
        brownianMotion_twoSidedHittingTime_prob_hit_right
          (μ := (P : Measure Ω)) (B := B) (hB := hB) (a := (z.1 : ℝ)) (b := (z.2 : ℝ))
            z.1.2 hzpos
    have hdenom : 0 < z.2 - (z.1 : ℝ) := by
      exact sub_pos.mpr (lt_of_lt_of_le z.1.2 hzpos.le)
    have hweightFst_nonneg : 0 ≤ z.2 / (z.2 - (z.1 : ℝ)) := by
      exact div_nonneg z.2.2 hdenom.le
    have hweightSnd_nonneg : 0 ≤ (-(z.1 : ℝ)) / (z.2 - (z.1 : ℝ)) := by
      exact div_nonneg (neg_nonneg.mpr z.1.2.le) hdenom.le
    have hsum :
        z.2 / (z.2 - (z.1 : ℝ)) + (-(z.1 : ℝ)) / (z.2 - (z.1 : ℝ)) = 1 := by
      field_simp [hdenom.ne']
      ring
    have hprob_compl :
        (P : Measure Ω) {ω | X ω = (z.2 : ℝ)}ᶜ =
          ENNReal.ofReal (z.2 / (z.2 - (z.1 : ℝ))) := by
      have hsumENN :
          ENNReal.ofReal (z.2 / (z.2 - (z.1 : ℝ))) +
            ENNReal.ofReal (-(z.1 : ℝ) / (z.2 - (z.1 : ℝ))) = 1 := by
        rw [← ENNReal.ofReal_add hweightFst_nonneg hweightSnd_nonneg, hsum, ENNReal.ofReal_one]
      calc
        (P : Measure Ω) {ω | X ω = (z.2 : ℝ)}ᶜ
            = 1 - (P : Measure Ω) {ω | X ω = (z.2 : ℝ)} := by
                simpa using prob_compl_eq_one_sub₀ (μ := (P : Measure Ω)) hE_null
        _ = 1 - ENNReal.ofReal (-(z.1 : ℝ) / (z.2 - (z.1 : ℝ))) := by rw [hprob]
        _ = (ENNReal.ofReal (z.2 / (z.2 - (z.1 : ℝ))) +
              ENNReal.ofReal (-(z.1 : ℝ) / (z.2 - (z.1 : ℝ)))) -
              ENNReal.ofReal (-(z.1 : ℝ) / (z.2 - (z.1 : ℝ))) := by
                rw [← hsumENN]
        _ = ENNReal.ofReal (z.2 / (z.2 - (z.1 : ℝ))) := by
              exact ENNReal.add_sub_cancel_right ENNReal.ofReal_ne_top
    -- Proof comment: compare the pushforward law and the kernel on all lower half-lines `Iic x`,
    -- using the exact piecewise stopped-value description and the Chapter 21 exit probability.
    rw [hmapX]
    calc
      (P : Measure Ω) {ω | X ω ≤ x}
          = (P : Measure Ω)
              {ω |
                ({ω' | X ω' = (z.2 : ℝ)} : Set Ω).piecewise
                  (fun _ ↦ (z.2 : ℝ)) (fun _ ↦ (z.1 : ℝ)) ω ≤ x} :=
            measure_congr hpieceSet
      _ = (P : Measure Ω) (if x < (z.1 : ℝ) then ∅
            else if x < z.2 then {ω | X ω = (z.2 : ℝ)}ᶜ
            else Set.univ) := by
              have huz : (z.1 : ℝ) ≤ z.2 := le_of_lt (lt_of_lt_of_le z.1.2 z.2.2)
              simpa using
                congrArg
                  (fun s : Set Ω ↦ (P : Measure Ω) s)
                  (twoPointPiecewise_preimage_Iic
                    ({ω | X ω = (z.2 : ℝ)} : Set Ω)
                    (u := (z.1 : ℝ)) (v := z.2) (x := x) huz)
      _ = if x < (z.1 : ℝ) then 0
          else if x < z.2 then ENNReal.ofReal (z.2 / (z.2 - (z.1 : ℝ))) else 1 := by
            by_cases hxu : x < (z.1 : ℝ)
            · calc
                (P : Measure Ω)
                    (if x < (z.1 : ℝ) then ∅ else if x < z.2 then {ω | X ω = (z.2 : ℝ)}ᶜ
                      else Set.univ) = 0 := by
                        rw [if_pos hxu]
                        simp
                _ = if x < (z.1 : ℝ) then 0
                    else if x < z.2 then ENNReal.ofReal (z.2 / (z.2 - (z.1 : ℝ))) else 1 := by
                      simp [hxu]
            · by_cases hxv : x < z.2
              · calc
                  (P : Measure Ω)
                      (if x < (z.1 : ℝ) then ∅ else if x < z.2 then {ω | X ω = (z.2 : ℝ)}ᶜ
                        else Set.univ)
                      = (P : Measure Ω) {ω | X ω = (z.2 : ℝ)}ᶜ := by
                          rw [if_neg hxu, if_pos hxv]
                  _ = ENNReal.ofReal (z.2 / (z.2 - (z.1 : ℝ))) := hprob_compl
                  _ = if x < (z.1 : ℝ) then 0
                      else if x < z.2 then ENNReal.ofReal (z.2 / (z.2 - (z.1 : ℝ))) else 1 := by
                        rw [if_neg hxu, if_pos hxv]
              · calc
                  (P : Measure Ω)
                      (if x < (z.1 : ℝ) then ∅ else if x < z.2 then {ω | X ω = (z.2 : ℝ)}ᶜ
                        else Set.univ)
                      = 1 := by
                          rw [if_neg hxu, if_neg hxv]
                          simp
                  _ = if x < (z.1 : ℝ) then 0
                      else if x < z.2 then ENNReal.ofReal (z.2 / (z.2 - (z.1 : ℝ))) else 1 := by
                        rw [if_neg hxu, if_neg hxv]
      _ = negativeNonnegativeTwoPointKernel z (Set.Iic x) := by
            rw [negativeNonnegativeTwoPointKernel_apply_Iic]

/-- Helper for Theorem 22.5: the stopping-time predicate is monotone under filtration inclusion. -/
private theorem isStoppingTime_of_filtration_le
    {Ω : Type*} [MeasurableSpace Ω]
    {ℱ 𝒢 : Filtration NNReal ‹MeasurableSpace Ω›}
    (hle : ℱ ≤ 𝒢) {τ : Ω → ENNReal}
    (hτ : IsStoppingTime ℱ τ) :
    IsStoppingTime 𝒢 τ := by
  -- Proof comment: every time-slice event already measurable for `ℱ` remains measurable for the
  -- larger filtration `𝒢`.
  intro t
  change MeasurableSet[𝒢 t] {ω | τ ω ≤ t}
  exact hle t {ω | τ ω ≤ t} (hτ t)

/-- Helper for Theorem 22.5: adjoining an auxiliary coordinate can only enlarge the Brownian
natural filtration. -/
private theorem naturalFiltration_le_processFiltration_pair
    {Ω Aux : Type*} [MeasurableSpace Ω] [MeasurableSpace Aux]
    {Ξ : Ω → Aux} {B : NNReal → Ω → ℝ}
    (hBsm : ∀ t, StronglyMeasurable (B t)) :
    Filtration.natural B hBsm ≤ processFiltration (fun s ω ↦ (Ξ ω, B s ω)) := by
  intro t
  -- Proof comment: each Brownian coordinate `B s` is the second projection of the paired
  -- observable `(Ξ, B s)`, so its generated sigma-algebra is contained in the pair history.
  refine le_inf ((Filtration.natural B hBsm).le t) ?_
  refine iSup₂_le fun s hs ↦ ?_
  have hcomap :
      MeasurableSpace.comap (B s) inferInstance ≤
        MeasurableSpace.comap (fun ω ↦ (Ξ ω, B s ω)) inferInstance := by
    change
      MeasurableSpace.comap ((fun p : Aux × ℝ ↦ p.2) ∘ fun ω ↦ (Ξ ω, B s ω)) inferInstance ≤
        MeasurableSpace.comap (fun ω ↦ (Ξ ω, B s ω)) inferInstance
    simpa using MeasurableSpace.comap_mono <| Measurable.comap_le (by fun_prop)
  exact le_iSup_of_le s (le_iSup_of_le hs hcomap)

/-- Helper for Theorem 22.5: replacing the value `⊤` of an `ENNReal` clock by `0` produces an
`NNReal`-valued stopping time candidate. -/
private def finitePartStoppingTime {Ω : Type*} [MeasurableSpace Ω]
    (τ : Ω → ENNReal) : Ω → NNReal :=
  fun ω ↦ if h : τ ω = ⊤ then 0 else (τ ω).untop h

/-- Helper for Theorem 22.5: the finite-part replacement preserves the stopping-time property once
the exceptional event `{τ = ⊤}` is already measurable at every deterministic time. -/
private theorem finitePartStoppingTime_isStoppingTime
    {Ω : Type*} [MeasurableSpace Ω] {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    {τ : Ω → ENNReal} (hτ : IsStoppingTime ℱ τ)
    (hτ_top : ∀ t : NNReal, MeasurableSet[ℱ t] {ω | τ ω = ⊤}) :
    IsStoppingTime ℱ (fun ω ↦ (finitePartStoppingTime τ ω : ENNReal)) := by
  intro t
  have hset :
      {ω | (finitePartStoppingTime τ ω : ENNReal) ≤ t} =
        {ω | τ ω ≤ t} ∪ {ω | τ ω = ⊤} := by
    ext ω
    by_cases hω : τ ω = ⊤
    · simp [finitePartStoppingTime, hω]
    · constructor <;> intro h
      · simpa [finitePartStoppingTime, hω] using h
      · simpa [finitePartStoppingTime, hω] using h
  -- Proof comment: below level `t`, the finite-part clock is either already below `t` or
  -- comes from an infinite original clock that got reset to `0`; the extra hypothesis records
  -- exactly the measurability of that exceptional top event.
  change MeasurableSet[ℱ t] {ω | (finitePartStoppingTime τ ω : ENNReal) ≤ t}
  rw [hset]
  exact (hτ t).union (hτ_top t)

/-- Helper for Theorem 22.5: decoding the real auxiliary variable recovers the original pair
coordinate on the product owner. -/
private theorem decodeEmbeddingReal_pair_eq_fst_prod
    {β : Type*}
    [Nonempty PairSpace] [StandardBorelSpace PairSpace] :
    let decode : ℝ → PairSpace :=
      (MeasureTheory.measurableEmbedding_embeddingReal PairSpace).invFun
    let Ξ : PairSpace × β → ℝ := MeasureTheory.embeddingReal PairSpace ∘ Prod.fst
    decode ∘ Ξ = Prod.fst := by
  let hme := MeasureTheory.measurableEmbedding_embeddingReal PairSpace
  -- Proof comment: `invFun` is a left inverse to the measurable embedding on the image of
  -- every actual pair, independently of the auxiliary product factor.
  funext ω
  exact hme.leftInverse_invFun (Prod.fst ω)

/-- Helper for Theorem 22.5: decoding the real auxiliary variable recovers the original pair
coordinate on the canonical path product owner. -/
private theorem decodeEmbeddingReal_pair_eq_fst
    [Nonempty PairSpace] [StandardBorelSpace PairSpace] :
    let decode : ℝ → PairSpace :=
      (MeasureTheory.measurableEmbedding_embeddingReal PairSpace).invFun
    let Ξ : PairSpace × (NNReal → ℝ) → ℝ := MeasureTheory.embeddingReal PairSpace ∘ Prod.fst
    decode ∘ Ξ = Prod.fst := by
  -- Proof comment: this is the path-owner specialization of the general product decoding lemma.
  simpa using (decodeEmbeddingReal_pair_eq_fst_prod (β := NNReal → ℝ))

/-- Helper for Theorem 22.5: the decoded pair history is measurable with respect to the coded
real-auxiliary filtration generated by `(Ξ, B)`. -/
private theorem decodedPairFiltration_le_codedFiltration_prod
    {β : Type*} [MeasurableSpace β]
    [Nonempty PairSpace] [StandardBorelSpace PairSpace]
    {B : NNReal → PairSpace × β → ℝ} :
    let decode : ℝ → PairSpace :=
      (MeasureTheory.measurableEmbedding_embeddingReal PairSpace).invFun
    let Ξ : PairSpace × β → ℝ := MeasureTheory.embeddingReal PairSpace ∘ Prod.fst
    processFiltration (fun s ω ↦ (decode (Ξ ω), B s ω)) ≤
      processFiltration (fun s ω ↦ (Ξ ω, B s ω)) := by
  dsimp
  intro t
  rw [processFiltration, processFiltration]
  let hme := MeasureTheory.measurableEmbedding_embeddingReal PairSpace
  let decode : ℝ → PairSpace := hme.invFun
  let Ξ : PairSpace × β → ℝ := MeasureTheory.embeddingReal PairSpace ∘ Prod.fst
  have hdecodeMeas : Measurable decode := hme.measurable_invFun
  refine inf_le_inf le_rfl ?_
  refine iSup₂_le fun s hs ↦ ?_
  have hcoded :
      Measurable[
        ⨆ r ≤ t, MeasurableSpace.comap (fun ω ↦ (Ξ ω, B r ω)) inferInstance]
        (fun ω ↦ (Ξ ω, B s ω)) := by
    exact Measurable.of_comap_le <| le_iSup_of_le s <| le_iSup_of_le hs le_rfl
  have hmap : Measurable fun p : ℝ × ℝ ↦ (decode p.1, p.2) := by
    -- Proof comment: decoding the first coordinate and keeping the Brownian value is a
    -- measurable map on the coded state space for any auxiliary factor `β`.
    fun_prop
  -- Proof comment: each decoded observable is the coded observable composed with this
  -- measurable coordinate map, so every generator of the decoded history is already in the
  -- coded process filtration.
  simpa [decode, Ξ, Function.comp] using (hmap.comp hcoded).comap_le

/-- Helper for Theorem 22.5: the decoded pair history is measurable with respect to the coded
real-auxiliary filtration generated by `(Ξ, B)` on the canonical path product owner. -/
private theorem decodedPairFiltration_le_codedFiltration
    [Nonempty PairSpace] [StandardBorelSpace PairSpace]
    {B : NNReal → PairSpace × (NNReal → ℝ) → ℝ} :
    let decode : ℝ → PairSpace :=
      (MeasureTheory.measurableEmbedding_embeddingReal PairSpace).invFun
    let Ξ : PairSpace × (NNReal → ℝ) → ℝ := MeasureTheory.embeddingReal PairSpace ∘ Prod.fst
    processFiltration (fun s ω ↦ (decode (Ξ ω), B s ω)) ≤
      processFiltration (fun s ω ↦ (Ξ ω, B s ω)) := by
  -- Proof comment: this is the canonical-path specialization of the product-level transport
  -- lemma needed later for the restricted subtype owner.
  simpa using
    (decodedPairFiltration_le_codedFiltration_prod (β := NNReal → ℝ) (B := B))

/-- Helper for Theorem 22.5: the remaining Brownian-side blocker is one continuous scalar witness
on the canonical Gaussian-increment owner. -/
private theorem existsContinuousGaussianIncrementBrownianWitness :
    ∃ W : NNReal → (NNReal → ℝ) → ℝ,
      IsBrownianMotion gaussianIncrementPathMeasure W ∧
        (∀ ω, Continuous (fun t : NNReal ↦ W t ω)) ∧
        (∀ t, W t =ᵐ[gaussianIncrementPathMeasure] Function.eval t) := by
  letI : IsProbabilityMeasure gaussianIncrementPathMeasure := inferInstance
  obtain ⟨Y, hmodY, hcontY⟩ :=
    existsContinuousRealModificationOfBrownianCovariance
      (μ := gaussianIncrementPathMeasure)
      gaussianIncrementCoordinate_isGaussianProcess
      gaussianIncrementCoordinate_mean_zero
      gaussianIncrementCoordinate_covariance_eq
  let W : NNReal → (NNReal → ℝ) → ℝ := fun t ω ↦ Y t ω - Y 0 ω
  have hYzeroAe : Y 0 =ᵐ[gaussianIncrementPathMeasure] fun _ : NNReal → ℝ ↦ 0 := by
    -- Proof comment: the continuous modification still starts from `0` almost surely because it
    -- agrees with the canonical coordinate process at time `0`.
    filter_upwards [hmodY 0, gaussianIncrementCoordinate_zero_ae] with ω hωY hω0
    exact hωY.trans hω0
  have hmodW : ∀ t, W t =ᵐ[gaussianIncrementPathMeasure] Function.eval t := by
    intro t
    -- Proof comment: subtract the almost-surely zero initial coordinate from the continuous
    -- modification to force the pointwise normalization `W 0 = 0`.
    filter_upwards [hmodY t, hYzeroAe] with ω hωt hω0
    simp [W, hωt, hω0]
  have hgaussW : IsGaussianProcess W gaussianIncrementPathMeasure := by
    -- Proof comment: finite-dimensional Gaussian laws are preserved under fixed-time
    -- almost-sure equality with the canonical coordinates.
    exact gaussianIncrementCoordinate_isGaussianProcess.congr fun t ↦ (hmodW t).symm
  have hW : IsBrownianMotion gaussianIncrementPathMeasure W := by
    -- Proof comment: the recentered continuous modification now satisfies the standard Brownian
    -- characterization exactly.
    refine
      (isBrownianMotion_iff_isCenteredGaussianProcessWithBrownianCovariance
        gaussianIncrementPathMeasure W).2 ?_
    refine ⟨?_, hgaussW, ?_, ?_, ?_⟩
    · funext ω
      simp [W]
    · intro t
      calc
        ∫ ω, W t ω ∂gaussianIncrementPathMeasure
            = ∫ ω, Function.eval t ω ∂gaussianIncrementPathMeasure := by
                exact integral_congr_ae (hmodW t)
        _ = 0 := gaussianIncrementCoordinate_mean_zero t
    · intro s t
      rw [covariance_congr_ae (hmodW s) (hmodW t)]
      exact gaussianIncrementCoordinate_covariance_eq s t
    · exact Filter.Eventually.of_forall fun ω ↦ (hcontY ω).sub continuous_const
  refine ⟨W, hW, ?_, hmodW⟩
  intro ω
  -- Proof comment: subtracting the deterministic initial value keeps the everywhere-continuous
  -- modification continuous for each path.
  exact (hcontY ω).sub continuous_const

/-- Helper for Theorem 22.5: pushing a full-measure subtype pullback back along `Subtype.val`
recovers the ambient measure. -/
private theorem map_comap_subtypeVal_eq_self_of_ae_mem
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {S : Set α}
    (hS : MeasurableSet S) (hSae : ∀ᵐ x ∂μ, x ∈ S) :
    (Measure.comap Subtype.val μ : Measure S).map Subtype.val = μ := by
  -- Proof comment: `map_comap_subtype_coe` identifies the round trip with restriction to `S`,
  -- and the full-measure hypothesis removes that restriction.
  rw [map_comap_subtype_coe hS, Measure.restrict_eq_self_of_ae_mem hSae]

/-- Helper for Theorem 22.5: on the canonical Brownian owner, the paths that hit every positive
integer level form a measurable full-measure set. -/
private theorem brownianPositiveIntegerHitFullPathSet
    {W : NNReal → (NNReal → ℝ) → ℝ}
    (hW : IsBrownianMotion gaussianIncrementPathMeasure W)
    (hWcont : ∀ ω, Continuous fun t : NNReal ↦ W t ω) :
    ∃ S : Set (NNReal → ℝ),
      MeasurableSet S ∧
        gaussianIncrementPathMeasure S = 1 ∧
        ∀ ω ∈ S, ∀ n : ℕ, brownianLevelHittingTime W (n + 1) ω ≠ ⊤ := by
  let S : Set (NNReal → ℝ) :=
    {ω | ∀ n : ℕ, brownianLevelHittingTime W (n + 1) ω ≠ ⊤}
  have hA_meas :
      ∀ n : ℕ,
        MeasurableSet {ω : NNReal → ℝ | brownianLevelHittingTime W (n + 1) ω ≠ ⊤} := by
    intro n
    let τn : (NNReal → ℝ) → ENNReal := brownianLevelHittingTime W (n + 1)
    have hτn :
        IsStoppingTime (Filtration.natural W hW.stronglyMeasurable) τn := by
      simpa [τn] using
        brownianLevelHittingTime_isStoppingTime
          (B := W) hW.stronglyMeasurable hWcont (n + 1 : ℝ)
    have hτn_meas : Measurable τn := by
      exact (hτn.measurable).mono hτn.measurableSpace_le le_rfl
    have htop : Measurable fun ω : NNReal → ℝ ↦ τn ω = (⊤ : ENNReal) := by
      simpa [Set.preimage, Set.mem_singleton_iff] using
        (hτn_meas (measurableSet_singleton (⊤ : ENNReal)))
    simpa [τn] using htop.not
  have hS_meas : MeasurableSet S := by
    -- Proof comment: the owner is a countable intersection of the measurable single-level hit
    -- events.
    rw [show S = ⋂ n : ℕ, {ω : NNReal → ℝ | brownianLevelHittingTime W (n + 1) ω ≠ ⊤} by
      ext ω
      simp [S]]
    exact MeasurableSet.iInter hA_meas
  have hS_ae : ∀ᵐ ω ∂gaussianIncrementPathMeasure, ω ∈ S := by
    have hAll :
        ∀ᵐ ω ∂gaussianIncrementPathMeasure, ∀ n : ℕ,
          brownianLevelHittingTime W (n + 1) ω ≠ ⊤ := by
      rw [ae_all_iff]
      intro n
      simpa using
        brownianLevelHittingTime_ae_ne_top
          (μ := gaussianIncrementPathMeasure) (B := W) hW
          (show (0 : ℝ) < (n + 1 : ℝ) by exact_mod_cast Nat.succ_pos n)
    simpa [S] using hAll
  have hS_null : gaussianIncrementPathMeasure Sᶜ = 0 := by
    exact (ae_iff.1 hS_ae)
  have hS_one : gaussianIncrementPathMeasure S = 1 := by
    simpa using
      (measure_of_measure_compl_eq_zero (μ := gaussianIncrementPathMeasure) (s := S) hS_null)
  refine ⟨S, hS_meas, hS_one, ?_⟩
  intro ω hω n
  exact hω n

/-- Helper for Theorem 22.5: on the positive-integer-hit path owner, every sampled two-point
boundary is reached in finite exact time. -/
private theorem twoSidedExitFinite_of_memPositiveIntegerHitFullPathSet
    {Ω : Type*} [MeasurableSpace Ω] {W : NNReal → Ω → ℝ}
    (hWcont : ∀ ω, Continuous fun t : NNReal ↦ W t ω)
    (hWzero : ∀ ω, W 0 ω = 0)
    {S : Set Ω}
    (hS : ∀ ω ∈ S, ∀ n : ℕ, brownianLevelHittingTime W (n + 1) ω ≠ ⊤)
    {ω : Ω} (hω : ω ∈ S) (z : PairSpace) :
    hittingAfter W ({(z.1 : ℝ), (z.2 : ℝ)} : Set ℝ) 0 ω ≠ ⊤ := by
  by_cases hz0 : (z.2 : ℝ) = 0
  · have hτ_le :
        hittingAfter W ({(z.1 : ℝ), (z.2 : ℝ)} : Set ℝ) 0 ω ≤ 0 := by
      -- Proof comment: if the upper barrier is `0`, the process is already at that boundary at
      -- time `0`.
      exact
        twoSidedBoundaryHittingTime_le_of_eq_left_or_right
          (B := W) (a := (z.1 : ℝ)) (b := (z.2 : ℝ)) (ω := ω) (t := 0)
          (Or.inr <| by
            calc
              W 0 ω = 0 := hWzero ω
              _ = (z.2 : ℝ) := hz0.symm)
    exact ne_of_lt (lt_of_le_of_lt hτ_le (by simp))
  · have hzpos : 0 < (z.2 : ℝ) := by
      exact lt_of_le_of_ne z.2.2 fun h ↦ hz0 h.symm
    let n : ℕ := Nat.ceil (z.2 : ℝ)
    have hhit_ne :
        brownianLevelHittingTime W (n + 1) ω ≠ ⊤ :=
      hS ω hω n
    rcases (brownianLevelHittingTime_ne_top_iff_exists_eq
      (B := W) (b := (n + 1 : ℝ)) (ω := ω)).1 hhit_ne with ⟨tN, htN⟩
    have hright_mem : (z.2 : ℝ) ∈ Set.Icc (W 0 ω) (W tN ω) := by
      have hzero : W 0 ω = 0 := hWzero ω
      refine ⟨?_, ?_⟩
      · simpa [hzero] using z.2.2
      · have hceil_lt : (n : ℝ) < (z.2 : ℝ) + 1 := Nat.ceil_lt_add_one z.2.2
        have hz2_lt : (z.2 : ℝ) < (n + 1 : ℝ) := by
          have hz2_le_n : (z.2 : ℝ) ≤ n := by
            exact_mod_cast Nat.le_ceil (z.2 : ℝ)
          linarith
        exact le_of_lt <| by
          calc
            (z.2 : ℝ) < (n + 1 : ℝ) := hz2_lt
            _ = W tN ω := by rw [htN]
    obtain ⟨t, ht_mem, ht_eq⟩ :=
      (intermediate_value_Icc (a := (0 : NNReal)) (b := tN) (by simp)
        (hWcont ω).continuousOn) hright_mem
    have hτ_le :
        hittingAfter W ({(z.1 : ℝ), (z.2 : ℝ)} : Set ℝ) 0 ω ≤ t := by
      -- Proof comment: once the path reaches the right barrier `z.2`, the two-sided boundary
      -- hitting time is bounded by that explicit hitting time.
      exact
        twoSidedBoundaryHittingTime_le_of_eq_left_or_right
          (B := W) (a := (z.1 : ℝ)) (b := (z.2 : ℝ)) (ω := ω) (t := t)
          (Or.inr ht_eq)
    have hfinite : ((t : ENNReal) < ⊤) := by simp
    exact ne_of_lt (lt_of_le_of_lt hτ_le hfinite)

/-- Helper for Theorem 22.5: coordinatewise measurability makes a process adapted to its own
process filtration. -/
private theorem adapted_processFiltration_of_measurable
    {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    {X : NNReal → Ω → β}
    (hX_meas : ∀ t : NNReal, Measurable (X t)) :
    Adapted (processFiltration X) X := by
  intro t
  -- Proof comment: the time-`t` coordinate is one of the generators of `processFiltration X t`.
  refine measurable_iff_comap_le.2 ?_
  exact le_inf (measurable_iff_comap_le.1 (hX_meas t)) <| by
    refine le_iSup_of_le t ?_
    refine le_iSup_of_le le_rfl ?_
    exact le_rfl

/-- Theorem 22.5: every centered square-integrable real probability law admits a Skorohod
embedding on a suitable probability space, realized by an auxiliary variable `Ξ`, a Brownian
motion `B` independent of `Ξ`, and a stopping time `τ` for the filtration generated by `(Ξ, B)`,
such that `B_τ` has the target law and `E[τ]` equals its variance. -/
theorem exists_skorohod_embedding (μ : ProbabilityMeasure ℝ)
    (hμ_mean_zero : ∫ x, x ∂(μ : Measure ℝ) = 0)
    (hμ_memLp : MemLp id 2 (μ : Measure ℝ)) :
    ∃ (Ω : Type) (_mΩ : MeasurableSpace Ω) (P : ProbabilityMeasure Ω)
      (Ξ : Ω → ℝ) (B : NNReal → Ω → ℝ) (τ : Ω → NNReal),
      Ξ ⟂ᵢ[(P : Measure Ω)] (fun ω t ↦ B t ω) ∧
      IsBrownianMotion (P : Measure Ω) B ∧
      IsStoppingTime (processFiltration (fun s ω ↦ (Ξ ω, B s ω)))
        (fun ω ↦ (τ ω : WithTop NNReal)) ∧
      HasLaw (stoppedValue B (fun ω ↦ (τ ω : WithTop NNReal))) (μ : Measure ℝ)
        (P : Measure Ω) ∧
      (P : Measure Ω)[fun ω ↦ (τ ω : ℝ)] = Var[id; (μ : Measure ℝ)] := by
  letI : Nonempty PairSpace := inferInstance
  letI : StandardBorelSpace (Set.Iio (0 : ℝ)) := measurableSet_Iio.standardBorel
  letI : StandardBorelSpace (Set.Ici (0 : ℝ)) := measurableSet_Ici.standardBorel
  letI : StandardBorelSpace PairSpace := inferInstance
  obtain ⟨θ, hθ_mix, hθ_var⟩ :=
    existsSkorohodMixtureData μ hμ_mean_zero hμ_memLp
  obtain ⟨W, hW, hWcont, hWmod⟩ :=
    existsContinuousGaussianIncrementBrownianWitness
  obtain ⟨S, hS_meas, hS_one, hS_hit⟩ := brownianPositiveIntegerHitFullPathSet hW hWcont
  have hS_ae : ∀ᵐ ω ∂gaussianIncrementPathMeasure, ω ∈ S := by
    exact (MeasureTheory.mem_ae_iff_prob_eq_one₀ hS_meas.nullMeasurableSet).2 hS_one
  have hS_null : gaussianIncrementPathMeasure Sᶜ = 0 := by
    exact ae_iff.1 hS_ae
  letI : IsProbabilityMeasure (Measure.comap Subtype.val gaussianIncrementPathMeasure : Measure S) := by
    refine ⟨?_⟩
    rw [show (Measure.comap Subtype.val gaussianIncrementPathMeasure : Measure S) Set.univ =
        gaussianIncrementPathMeasure S by
          simpa using
            comap_subtype_coe_apply hS_meas gaussianIncrementPathMeasure (Set.univ : Set S)]
    exact hS_one
  let PS : ProbabilityMeasure S := ⟨Measure.comap Subtype.val gaussianIncrementPathMeasure, inferInstance⟩
  let WS : NNReal → S → ℝ := fun t ω ↦ W t ω.1
  have hSubtype :
      MeasurePreserving (Subtype.val : S → (NNReal → ℝ))
        (PS : Measure S) gaussianIncrementPathMeasure := by
    refine
      { measurable := measurable_subtype_coe
        map_eq := ?_ }
    simpa [PS] using
      map_comap_subtypeVal_eq_self_of_ae_mem
        (μ := gaussianIncrementPathMeasure) hS_meas hS_ae
  have hWS : IsBrownianMotion (PS : Measure S) WS := by
    -- Proof comment: the restricted path owner keeps the same Brownian witness via
    -- `Subtype.val`.
    simpa [WS] using isBrownianMotion_comp_measurePreserving hSubtype hW
  have hWScont : ∀ ω, Continuous fun t : NNReal ↦ WS t ω := by
    intro ω
    -- Proof comment: continuity survives the path-only restriction because the witness is just
    -- precomposed with `Subtype.val`.
    simpa [WS] using hWcont ω.1
  have hWSzero : ∀ ω, WS 0 ω = 0 := by
    intro ω
    simpa [WS] using congrFun hW.zero ω.1
  let Ω : Type := PairSpace × ↥S
  let P : ProbabilityMeasure Ω := ProbabilityMeasure.prod θ PS
  let Ξ : Ω → ℝ := MeasureTheory.embeddingReal PairSpace ∘ Prod.fst
  let B : NNReal → Ω → ℝ := fun t ω ↦ WS t ω.2
  have hPathMeas : Measurable (processPath WS) := by
    -- Proof comment: deterministic-time measurability of each restricted Brownian coordinate gives
    -- measurability of the full restricted path map.
    exact measurable_pi_lambda _ fun t ↦ (hWS.stronglyMeasurable t).measurable
  have hIndepPath : Ξ ⟂ᵢ[(P : Measure Ω)] processPath B := by
    -- Proof comment: after restricting only the path factor, the auxiliary coordinate still
    -- depends only on `Prod.fst` and the Brownian path only on `Prod.snd`.
    simpa [P, Ξ, B, processPath, Function.comp] using
      (indepFun_prod
        (μ := (θ : Measure PairSpace))
        (ν := (PS : Measure S))
        (X := MeasureTheory.embeddingReal PairSpace)
        (Y := processPath WS)
        (measurable_embeddingReal PairSpace)
        hPathMeas)
  have hsnd : MeasurePreserving Prod.snd (P : Measure Ω) (PS : Measure S) := by
    -- Proof comment: the Brownian coordinate on the product owner is still the second
    -- projection.
    simpa [P] using
      (measurePreserving_snd
        (μ := (θ : Measure PairSpace))
        (ν := (PS : Measure S)))
  have hB : IsBrownianMotion (P : Measure Ω) B := by
    -- Proof comment: pull the restricted Brownian witness back along the measure-preserving
    -- second projection.
    simpa [B] using isBrownianMotion_comp_measurePreserving hsnd hWS
  have hBcont : ∀ ω, Continuous fun t : NNReal ↦ B t ω := by
    intro ω
    simpa [B] using hWScont ω.2
  let rawProcess : NNReal → Ω → PairSpace × ℝ := fun t ω ↦ (ω.1, B t ω)
  let pathTarget : Set (PairSpace × ℝ) :=
    {p | p.2 = (p.1.1 : ℝ)} ∪ {p | p.2 = (p.1.2 : ℝ)}
  have hRawMeas : ∀ t : NNReal, StronglyMeasurable (rawProcess t) := by
    intro t
    have hfst : StronglyMeasurable (fun ω : Ω ↦ ω.1) := measurable_fst.stronglyMeasurable
    simpa [rawProcess] using hfst.prodMk (hB.stronglyMeasurable t)
  have hRawCont : ∀ ω, Continuous fun t : NNReal ↦ rawProcess t ω := by
    rintro ⟨z, η⟩
    show Continuous (fun t : NNReal ↦ (z, B t (z, η)))
    exact continuous_const.prodMk (hBcont (z, η))
  have hPathTargetClosed : IsClosed pathTarget := by
    -- Proof comment: the target is the union of the two closed graphs `x = u` and `x = v`.
    refine
      (isClosed_eq continuous_snd (continuous_subtype_val.comp continuous_fst.fst)).union ?_
    exact isClosed_eq continuous_snd (continuous_subtype_val.comp continuous_fst.snd)
  have hPathTargetNonempty : pathTarget.Nonempty := by
    refine ⟨((⟨(-1 : ℝ), by norm_num⟩, ⟨(0 : ℝ), by simp⟩), (-1 : ℝ)), ?_⟩
    simp [pathTarget]
  let τExact : Ω → ENNReal := hittingAfter rawProcess pathTarget 0
  have hτExact_eq :
      ∀ ω : Ω,
        τExact ω = hittingAfter B ({(ω.1.1 : ℝ), (ω.1.2 : ℝ)} : Set ℝ) 0 ω := by
    classical
    rintro ⟨z, η⟩
    -- Proof comment: for a fixed product point `ω = (z, η)`, the closed target `pathTarget`
    -- records exactly the two boundary equations `B_t = z.1` or `B_t = z.2`.
    unfold τExact
    rw [hittingAfter_def, hittingAfter_def]
    change
      (if ∃ j : NNReal, (0 : NNReal) ≤ j ∧ (z, WS j η) ∈ pathTarget then
          ((sInf {i : NNReal | (0 : NNReal) ≤ i ∧ (z, WS i η) ∈ pathTarget} : NNReal) : ENNReal)
        else ⊤) =
        (if ∃ j : NNReal, (0 : NNReal) ≤ j ∧ WS j η ∈ ({(z.1 : ℝ), (z.2 : ℝ)} : Set ℝ) then
          ((sInf
              {i : NNReal | (0 : NNReal) ≤ i ∧
                WS i η ∈ ({(z.1 : ℝ), (z.2 : ℝ)} : Set ℝ)} : NNReal) : ENNReal)
        else ⊤)
    have hmem :
        ∀ t : NNReal,
          (z, WS t η) ∈ pathTarget ↔
            WS t η ∈ ({(z.1 : ℝ), (z.2 : ℝ)} : Set ℝ) := by
      intro t
      simp [pathTarget, Set.mem_insert_iff, Set.mem_singleton_iff]
    have hExists :
        (∃ j : NNReal, (0 : NNReal) ≤ j ∧ (z, WS j η) ∈ pathTarget) ↔
          ∃ j : NNReal, (0 : NNReal) ≤ j ∧ WS j η ∈ ({(z.1 : ℝ), (z.2 : ℝ)} : Set ℝ) := by
      constructor
      · rintro ⟨j, hj0, hj⟩
        exact ⟨j, hj0, (hmem j).mp hj⟩
      · rintro ⟨j, hj0, hj⟩
        exact ⟨j, hj0, (hmem j).mpr hj⟩
    have hSet :
        {i : NNReal | (0 : NNReal) ≤ i ∧ (z, WS i η) ∈ pathTarget} =
          {i : NNReal | (0 : NNReal) ≤ i ∧
            WS i η ∈ ({(z.1 : ℝ), (z.2 : ℝ)} : Set ℝ)} := by
      ext i
      simp [hmem i]
    by_cases hHit : ∃ j : NNReal, (0 : NNReal) ≤ j ∧ (z, WS j η) ∈ pathTarget
    · have hHit' : ∃ j : NNReal, (0 : NNReal) ≤ j ∧ WS j η ∈ ({(z.1 : ℝ), (z.2 : ℝ)} : Set ℝ) :=
        hExists.mp hHit
      rw [if_pos hHit, if_pos hHit']
      simpa using congrArg (fun s : Set NNReal ↦ ((sInf s : NNReal) : ENNReal)) hSet
    · have hHit' :
          ¬ ∃ j : NNReal, (0 : NNReal) ≤ j ∧ WS j η ∈ ({(z.1 : ℝ), (z.2 : ℝ)} : Set ℝ) := by
        exact mt hExists.mpr hHit
      rw [if_neg hHit, if_neg hHit']
  have hτExact_finite : ∀ ω : Ω, τExact ω ≠ ⊤ := by
    intro ω
    rw [hτExact_eq]
    simpa [B] using
      twoSidedExitFinite_of_memPositiveIntegerHitFullPathSet
        (W := WS) hWScont hWSzero
        (S := (Set.univ : Set S))
        (fun η _ n ↦ by simpa [WS] using hS_hit (η : NNReal → ℝ) η.2 n)
        (ω := ω.2) (by simp) ω.1
  let τ : Ω → NNReal := fun ω ↦ (τExact ω).untop (hτExact_finite ω)
  have hτ_cast : ∀ ω : Ω, ((τ ω : NNReal) : ENNReal) = τExact ω := by
    intro ω
    change ↑((τExact ω).untop (hτExact_finite ω)) = τExact ω
    exact WithTop.coe_untop (τExact ω) (hτExact_finite ω)
  have hτ_fun :
      (fun ω ↦ (τ ω : WithTop NNReal)) = τExact := by
    funext ω
    exact hτ_cast ω
  have hτExact_nat :
      IsStoppingTime (Filtration.natural rawProcess hRawMeas) τExact := by
    -- Proof comment: the exact exit clock is a hitting time of the closed target in the natural
    -- filtration of the paired state process.
    simpa [τExact] using
      hittingClosed_isStoppingTime_of_continuous_natural
        (X := rawProcess) hRawMeas hRawCont hPathTargetClosed hPathTargetNonempty
  have hNatProc :
      Filtration.natural rawProcess hRawMeas ≤ processFiltration rawProcess := by
    exact
      (adapted_iff_natural_le hRawMeas).1
        (adapted_processFiltration_of_measurable
          (X := rawProcess) fun t ↦ (hRawMeas t).measurable)
  have hτExact_proc : IsStoppingTime (processFiltration rawProcess) τExact := by
    exact isStoppingTime_of_filtration_le hNatProc hτExact_nat
  have hτ_stop :
      IsStoppingTime (processFiltration (fun s ω ↦ (Ξ ω, B s ω)))
        (fun ω ↦ (τ ω : WithTop NNReal)) := by
    have hraw_le :
        processFiltration rawProcess ≤ processFiltration (fun s ω ↦ (Ξ ω, B s ω)) := by
      have haux :
          processFiltration
              (fun s : NNReal => fun ω : PairSpace × S ↦
                ((MeasureTheory.measurableEmbedding_embeddingReal PairSpace).invFun (Ξ ω), B s ω)) ≤
            processFiltration (fun s : NNReal => fun ω : PairSpace × S ↦ (Ξ ω, B s ω)) := by
        simpa using
          (decodedPairFiltration_le_codedFiltration_prod (β := S) (B := B))
      have hproc_eq :
          (fun s : NNReal => fun ω : PairSpace × S ↦
              ((MeasureTheory.measurableEmbedding_embeddingReal PairSpace).invFun (Ξ ω), B s ω)) =
            (fun s : NNReal => fun ω : PairSpace × S ↦ (ω.1, B s ω)) := by
        funext s ω
        have hfstEq :
            ((MeasureTheory.measurableEmbedding_embeddingReal PairSpace).invFun (Ξ ω)) = ω.1 := by
          simpa [Ξ, Function.comp] using
            congrArg (fun f : PairSpace × S → PairSpace => f ω)
              (decodeEmbeddingReal_pair_eq_fst_prod (β := S))
        simp [hfstEq]
      change
        processFiltration (fun s : NNReal => fun ω : PairSpace × S ↦ (ω.1, B s ω)) ≤
          processFiltration (fun s : NNReal => fun ω : PairSpace × S ↦ (Ξ ω, B s ω))
      simpa [hproc_eq] using haux
    have hstopExact :
        IsStoppingTime (processFiltration (fun s ω ↦ (Ξ ω, B s ω))) τExact :=
      isStoppingTime_of_filtration_le hraw_le hτExact_proc
    rw [hτ_fun]
    exact hstopExact
  let Y : Ω → ℝ := stoppedValue B (fun ω ↦ (τ ω : WithTop NNReal))
  have hP_comp :
      (P : Measure Ω) = (θ : Measure PairSpace) ⊗ₘ Kernel.const PairSpace (PS : Measure S) := by
    -- Proof comment: the product owner is the composition-product with the constant path kernel.
    change (θ : Measure PairSpace).prod (PS : Measure S) =
      (θ : Measure PairSpace) ⊗ₘ Kernel.const PairSpace (PS : Measure S)
    simpa using
      (Measure.compProd_const
        (μ := (θ : Measure PairSpace))
        (ν := (PS : Measure S))).symm
  have hτExact_meas : Measurable τExact := by
    -- Proof comment: every stopping time is measurable into `WithTop NNReal`, and the stopping
    -- time sigma-algebra sits inside the ambient product sigma-algebra.
    exact (hτExact_proc.measurable).mono hτExact_proc.measurableSpace_le le_rfl
  have hτ_eq_toNNReal : τ = fun ω ↦ (τExact ω).toNNReal := by
    -- Proof comment: the exact clock is everywhere finite on the restricted owner, so its
    -- `NNReal` part is exactly the chosen finite clock.
    funext ω
    exact congrArg ENNReal.toNNReal (hτ_cast ω)
  have hτ_meas : Measurable τ := by
    rw [hτ_eq_toNNReal]
    exact hτExact_meas.ennreal_toNNReal
  have hRawAdapted : Adapted (processFiltration rawProcess) rawProcess :=
    adapted_processFiltration_of_measurable (X := rawProcess) fun t ↦ (hRawMeas t).measurable
  have hRawProg : ProgMeasurable (processFiltration rawProcess) rawProcess :=
    hRawAdapted.stronglyAdapted.progMeasurable_of_continuous hRawCont
  have hStoppedRaw_meas : Measurable (stoppedValue rawProcess τExact) := by
    -- Proof comment: the paired stopped process is measurable because the raw process is adapted
    -- to its own filtration and has continuous paths.
    exact (measurable_stoppedValue hRawProg hτExact_proc).mono hτExact_proc.measurableSpace_le le_rfl
  have hY_eq_raw :
      Y = fun ω ↦ (stoppedValue rawProcess τExact ω).2 := by
    -- Proof comment: the theorem’s stopped value is the second coordinate of the stopped paired
    -- process `(pair, Brownian value)`.
    funext ω
    calc
      Y ω = B ((((τ ω : NNReal) : ENNReal)).untopA) ω := rfl
      _ = B ((τExact ω).untopA) ω := by rw [hτ_cast ω]
      _ = (stoppedValue rawProcess τExact ω).2 := rfl
  have hY_meas : Measurable Y := by
    rw [hY_eq_raw]
    exact measurable_snd.comp hStoppedRaw_meas
  have hτ_section_cast :
      ∀ z : PairSpace, ∀ η : S,
        (((τ (z, η) : NNReal) : ENNReal)) =
          hittingAfter WS ({(z.1 : ℝ), (z.2 : ℝ)} : Set ℝ) 0 η := by
    intro z η
    -- Proof comment: freezing the pair coordinate reduces the product-space clock to the
    -- fixed-barrier Brownian hitting time on the restricted path owner.
    calc
      (((τ (z, η) : NNReal) : ENNReal)) = τExact (z, η) := hτ_cast (z, η)
      _ = hittingAfter B ({(z.1 : ℝ), (z.2 : ℝ)} : Set ℝ) 0 (z, η) := hτExact_eq (ω := (z, η))
      _ = hittingAfter WS ({(z.1 : ℝ), (z.2 : ℝ)} : Set ℝ) 0 η := rfl
  have hY_section_eq :
      ∀ z : PairSpace, ∀ η : S,
        Y (z, η) = stoppedValue WS (hittingAfter WS ({(z.1 : ℝ), (z.2 : ℝ)} : Set ℝ) 0) η := by
    intro z η
    -- Proof comment: after the same section normalization, the stopped value becomes the
    -- textbook two-point stopped value of `WS`.
    calc
      Y (z, η) = B ((((τ (z, η) : NNReal) : ENNReal)).untopA) (z, η) := rfl
      _ = WS ((((τ (z, η) : NNReal) : ENNReal)).untopA) η := rfl
      _ = WS ((hittingAfter WS ({(z.1 : ℝ), (z.2 : ℝ)} : Set ℝ) 0 η).untopA) η := by
            rw [hτ_section_cast z η]
      _ = stoppedValue WS (hittingAfter WS ({(z.1 : ℝ), (z.2 : ℝ)} : Set ℝ) 0) η := rfl
  have hτ_section_toReal :
      ∀ z : PairSpace, ∀ η : S,
        (τ (z, η) : ℝ) =
          ENNReal.toReal (hittingAfter WS ({(z.1 : ℝ), (z.2 : ℝ)} : Set ℝ) 0 η) := by
    intro z η
    -- Proof comment: the finite-clock cast transports the section clock into the `ENNReal`
    -- format used by the Chapter 21 exact-time identities.
    calc
      (τ (z, η) : ℝ) = ENNReal.toReal (((τ (z, η) : NNReal) : ENNReal)) := by simp
      _ = ENNReal.toReal (hittingAfter WS ({(z.1 : ℝ), (z.2 : ℝ)} : Set ℝ) 0 η) := by
            rw [hτ_section_cast z η]
  have restrictedTwoPointExitSectionLaw :
      ∀ z : PairSpace,
        HasLaw (fun η : S ↦ Y (z, η)) (negativeNonnegativeTwoPointKernel z) (PS : Measure S) := by
    intro z
    -- Proof comment: every frozen fiber inherits the fixed-barrier two-point exit law.
    exact
      (brownianTwoPointExit_hasLaw hWS z).congr <|
        Filter.Eventually.of_forall fun η ↦ hY_section_eq z η
  have stoppedValueHasLaw_of_prodFiberHasLaw :
      ∀ {Z : Ω → ℝ}, Measurable Z →
        (∀ z : PairSpace,
          HasLaw (fun η : S ↦ Z (z, η)) (negativeNonnegativeTwoPointKernel z) (PS : Measure S)) →
        HasLaw Z (negativeNonnegativeTwoPointKernel ∘ₘ (θ : Measure PairSpace)) (P : Measure Ω) := by
    intro Z hZ_meas hZ_section
    refine ⟨hZ_meas.aemeasurable, ?_⟩
    refine Measure.ext_of_Iic _ _ fun x ↦ ?_
    rw [Measure.map_apply hZ_meas measurableSet_Iic]
    rw [hP_comp]
    rw [Measure.compProd_apply (hZ_meas measurableSet_Iic)]
    rw [Measure.bind_apply measurableSet_Iic (Kernel.aemeasurable _)]
    refine lintegral_congr_ae <| Filter.Eventually.of_forall fun z ↦ ?_
    have hzLaw := hZ_section z
    -- Proof comment: compare both measures on `Iic x`; each fiber law already identifies the
    -- lower-tail mass with the two-point kernel.
    calc
      Kernel.const PairSpace (PS : Measure S) z (Prod.mk z ⁻¹' (Z ⁻¹' Set.Iic x))
          = (PS : Measure S) {η : S | Z (z, η) ≤ x} := by
              simp [Kernel.const_apply, Set.preimage, Set.mem_Iic]
      _ = ((PS : Measure S).map (fun η : S ↦ Z (z, η))) (Set.Iic x) := by
            rw [Measure.map_apply_of_aemeasurable hzLaw.aemeasurable measurableSet_Iic]
            rfl
      _ = negativeNonnegativeTwoPointKernel z (Set.Iic x) := by
            rw [hzLaw.map_eq]
  have hY_lawMix :
      HasLaw Y (negativeNonnegativeTwoPointKernel ∘ₘ (θ : Measure PairSpace)) (P : Measure Ω) :=
    stoppedValueHasLaw_of_prodFiberHasLaw hY_meas restrictedTwoPointExitSectionLaw
  have hY_law :
      HasLaw Y (μ : Measure ℝ) (P : Measure Ω) := by
    refine ⟨hY_lawMix.aemeasurable, ?_⟩
    rw [hY_lawMix.map_eq, hθ_mix]
  have hYsq_integrable : Integrable (fun ω : Ω ↦ (Y ω) ^ 2) (P : Measure Ω) := by
    have hsq_map : Integrable (fun x : ℝ ↦ x ^ 2) ((P : Measure Ω).map Y) := by
      rw [hY_law.map_eq]
      exact integrable_square_of_memLp_id (μ := μ) hμ_memLp
    -- Proof comment: square-integrability of the target law transports back along the stopped
    -- value law.
    simpa [Function.comp, Y] using hsq_map.comp_aemeasurable hY_law.aemeasurable
  have hYsq_integrable_comp :
      Integrable (fun ω : Ω ↦ (Y ω) ^ 2)
        ((θ : Measure PairSpace) ⊗ₘ Kernel.const PairSpace (PS : Measure S)) := by
    simpa [hP_comp] using hYsq_integrable
  have hYsq_outer_integrable :
      Integrable (fun z : PairSpace ↦ ∫ η, ‖(Y (z, η)) ^ 2‖ ∂(PS : Measure S))
        (θ : Measure PairSpace) := by
    -- Proof comment: the product-space square integrability of `Y` provides the outer Fubini
    -- integrability needed for the clock.
    exact
      ((Measure.integrable_compProd_iff hYsq_integrable_comp.aestronglyMeasurable).mp
        hYsq_integrable_comp).2
  have restrictedTwoPointExitSectionSecondMoment :
      ∀ z : PairSpace,
        ∫ η, (Y (z, η)) ^ 2 ∂(PS : Measure S) =
          ∫ η, (τ (z, η) : ℝ) ∂(PS : Measure S) := by
    intro z
    by_cases hz0 : (z.2 : ℝ) = 0
    · have hhit_zero :
        ∀ η : S, hittingAfter WS ({(z.1 : ℝ), (z.2 : ℝ)} : Set ℝ) 0 η = 0 := by
          intro η
          apply le_antisymm
          · have hmem : WS 0 η ∈ ({(z.1 : ℝ), (z.2 : ℝ)} : Set ℝ) := by
              rw [Set.mem_insert_iff, Set.mem_singleton_iff, hWSzero η]
              exact Or.inr hz0.symm
            exact
              hittingAfter_le_of_mem
                (u := WS) (s := ({(z.1 : ℝ), (z.2 : ℝ)} : Set ℝ))
                (n := 0) (ω := η) (by simp) hmem
          · exact le_hittingAfter (u := WS) (s := ({(z.1 : ℝ), (z.2 : ℝ)} : Set ℝ)) (n := 0) η
      have hτ_zero : ∀ η : S, τ (z, η) = 0 := by
        intro η
        have hcast : (((τ (z, η) : NNReal) : ENNReal)) = 0 := by
          calc
            (((τ (z, η) : NNReal) : ENNReal))
                = hittingAfter WS ({(z.1 : ℝ), (z.2 : ℝ)} : Set ℝ) 0 η := hτ_section_cast z η
            _ = 0 := hhit_zero η
        exact ENNReal.coe_eq_zero.mp hcast
      have hY_zero : ∀ η : S, Y (z, η) = 0 := by
        intro η
        calc
          Y (z, η) = stoppedValue WS (hittingAfter WS ({(z.1 : ℝ), (z.2 : ℝ)} : Set ℝ) 0) η :=
            hY_section_eq z η
          _ = 0 := by
                rw [stoppedValue, hhit_zero η]
                simpa using hWSzero η
      -- Proof comment: when the right barrier is `0`, both the clock and the stopped value are
      -- identically `0` on that section.
      simp [hτ_zero, hY_zero]
    · have hzpos : 0 < (z.2 : ℝ) := by
        exact lt_of_le_of_ne z.2.2 fun h ↦ hz0 h.symm
      have hExact :=
        (twoSidedExitMomentIdentitiesAtExactTime
          (μ := (PS : Measure S)) (B := WS) (hB := hWS)
          (a := (z.1 : ℝ)) (b := (z.2 : ℝ)) z.1.2 hzpos).2
      have hRight :
          ∫ η, (τ (z, η) : ℝ) ∂(PS : Measure S) =
            ∫ η,
              ENNReal.toReal (hittingAfter WS ({(z.1 : ℝ), (z.2 : ℝ)} : Set ℝ) 0 η)
              ∂(PS : Measure S) := by
        refine integral_congr_ae <| Filter.Eventually.of_forall fun η ↦ ?_
        exact hτ_section_toReal z η
      have hLeft :
          ∫ η, (Y (z, η)) ^ 2 ∂(PS : Measure S) =
            ∫ η,
              (stoppedValue WS (hittingAfter WS ({(z.1 : ℝ), (z.2 : ℝ)} : Set ℝ) 0) η) ^ 2
              ∂(PS : Measure S) := by
        refine integral_congr_ae <| Filter.Eventually.of_forall fun η ↦ ?_
        simpa using congrArg (fun y : ℝ ↦ y ^ 2) (hY_section_eq z η)
      -- Proof comment: for positive right barrier, Chapter 21 gives the exact identity between
      -- the clock expectation and the stopped-value second moment.
      calc
        ∫ η, (Y (z, η)) ^ 2 ∂(PS : Measure S)
            = ∫ η,
                (stoppedValue WS (hittingAfter WS ({(z.1 : ℝ), (z.2 : ℝ)} : Set ℝ) 0) η) ^ 2
                ∂(PS : Measure S) := hLeft
        _ = ∫ η,
              ENNReal.toReal (hittingAfter WS ({(z.1 : ℝ), (z.2 : ℝ)} : Set ℝ) 0 η)
              ∂(PS : Measure S) := hExact
        _ = ∫ η, (τ (z, η) : ℝ) ∂(PS : Measure S) := hRight.symm
  have restrictedTwoPointExitSectionIntegrable :
      ∀ z : PairSpace, Integrable (fun η : S ↦ (τ (z, η) : ℝ)) (PS : Measure S) := by
    intro z
    by_cases hz0 : (z.2 : ℝ) = 0
    · have hhit_zero :
        ∀ η : S, hittingAfter WS ({(z.1 : ℝ), (z.2 : ℝ)} : Set ℝ) 0 η = 0 := by
          intro η
          apply le_antisymm
          · have hmem : WS 0 η ∈ ({(z.1 : ℝ), (z.2 : ℝ)} : Set ℝ) := by
              rw [Set.mem_insert_iff, Set.mem_singleton_iff, hWSzero η]
              exact Or.inr hz0.symm
            exact
              hittingAfter_le_of_mem
                (u := WS) (s := ({(z.1 : ℝ), (z.2 : ℝ)} : Set ℝ))
                (n := 0) (ω := η) (by simp) hmem
          · exact le_hittingAfter (u := WS) (s := ({(z.1 : ℝ), (z.2 : ℝ)} : Set ℝ)) (n := 0) η
      have hτ_zero : ∀ η : S, (τ (z, η) : ℝ) = 0 := by
        intro η
        have hcast : (((τ (z, η) : NNReal) : ENNReal)) = 0 := by
          calc
            (((τ (z, η) : NNReal) : ENNReal))
                = hittingAfter WS ({(z.1 : ℝ), (z.2 : ℝ)} : Set ℝ) 0 η := hτ_section_cast z η
            _ = 0 := hhit_zero η
        exact_mod_cast ENNReal.coe_eq_zero.mp hcast
      -- Proof comment: the degenerate `b = 0` fiber has identically zero clock.
      simpa [hτ_zero] using (integrable_zero : Integrable (fun _ : S ↦ (0 : ℝ)) (PS : Measure S))
    · have hzpos : 0 < (z.2 : ℝ) := by
        exact lt_of_le_of_ne z.2.2 fun h ↦ hz0 h.symm
      have hMean :
          ∫ η, (τ (z, η) : ℝ) ∂(PS : Measure S) = -((z.1 : ℝ) * z.2) := by
        calc
          ∫ η, (τ (z, η) : ℝ) ∂(PS : Measure S)
              = ∫ η,
                  ENNReal.toReal (hittingAfter WS ({(z.1 : ℝ), (z.2 : ℝ)} : Set ℝ) 0 η)
                  ∂(PS : Measure S) := by
                    refine integral_congr_ae <| Filter.Eventually.of_forall fun η ↦ ?_
                    exact hτ_section_toReal z η
          _ = -((z.1 : ℝ) * z.2) := brownianTwoPointExitMean_eq_of_pos hWS z hzpos
      have hNonzeroIntegral :
          ∫ η, (τ (z, η) : ℝ) ∂(PS : Measure S) ≠ 0 := by
        rw [hMean]
        have hneg : 0 < -(z.1 : ℝ) := by
          exact neg_pos.mpr z.1.2
        have hmul : 0 < (-(z.1 : ℝ)) * z.2 := mul_pos hneg hzpos
        have hprod_pos : 0 < -((z.1 : ℝ) * z.2) := by
          simpa [neg_mul] using hmul
        exact ne_of_gt hprod_pos
      -- Proof comment: in the nondegenerate case, the Chapter 21 expectation formula is
      -- strictly positive, so the section clock is integrable.
      exact Integrable.of_integral_ne_zero hNonzeroIntegral
  have hτ_outer_integrable :
      Integrable (fun z : PairSpace ↦ ∫ η, ‖(τ (z, η) : ℝ)‖ ∂(PS : Measure S))
        (θ : Measure PairSpace) := by
    -- Proof comment: sectionwise exact-time identities identify the outer clock integral with
    -- the already integrable outer second-moment integral of the stopped value.
    refine hYsq_outer_integrable.congr <| Filter.Eventually.of_forall fun z ↦ ?_
    change (∫ η, ‖(Y (z, η) ^ 2)‖ ∂(PS : Measure S)) =
      ∫ η, ‖(τ (z, η) : ℝ)‖ ∂(PS : Measure S)
    symm
    calc
      ∫ η, ‖(τ (z, η) : ℝ)‖ ∂(PS : Measure S)
          = ∫ η, (τ (z, η) : ℝ) ∂(PS : Measure S) := by
              refine integral_congr_ae <| Filter.Eventually.of_forall fun η ↦ ?_
              exact Real.norm_of_nonneg (show 0 ≤ (τ (z, η) : ℝ) by exact_mod_cast (τ (z, η)).2)
      _ = ∫ η, (Y (z, η)) ^ 2 ∂(PS : Measure S) := (restrictedTwoPointExitSectionSecondMoment z).symm
      _ = ∫ η, ‖(Y (z, η)) ^ 2‖ ∂(PS : Measure S) := by
            refine integral_congr_ae <| Filter.Eventually.of_forall fun η ↦ ?_
            symm
            exact Real.norm_of_nonneg (sq_nonneg (Y (z, η)))
  have hτ_integrable_comp :
      Integrable (fun ω : Ω ↦ (τ ω : ℝ))
        ((θ : Measure PairSpace) ⊗ₘ Kernel.const PairSpace (PS : Measure S)) := by
    have hτReal_meas :
        AEStronglyMeasurable (fun ω : Ω ↦ (τ ω : ℝ))
          ((θ : Measure PairSpace) ⊗ₘ Kernel.const PairSpace (PS : Measure S)) :=
      (measurable_coe_nnreal_real.comp hτ_meas).aestronglyMeasurable
    -- Proof comment: combine fiberwise clock integrability with the outer norm control coming
    -- from the stopped-value second moment.
    exact
      (Measure.integrable_compProd_iff hτReal_meas).2
        ⟨Filter.Eventually.of_forall restrictedTwoPointExitSectionIntegrable, hτ_outer_integrable⟩
  have hτ_integrable : Integrable (fun ω : Ω ↦ (τ ω : ℝ)) (P : Measure Ω) := by
    simpa [hP_comp] using hτ_integrable_comp
  have hτ_eq_secondMoment :
      ∫ ω, (τ ω : ℝ) ∂(P : Measure Ω) =
        ∫ ω, (Y ω) ^ 2 ∂(P : Measure Ω) := by
    rw [hP_comp]
    calc
      ∫ ω, (τ ω : ℝ)
          ∂((θ : Measure PairSpace) ⊗ₘ Kernel.const PairSpace (PS : Measure S))
          = ∫ z, ∫ η, (τ (z, η) : ℝ) ∂(PS : Measure S) ∂(θ : Measure PairSpace) := by
              exact Measure.integral_compProd hτ_integrable_comp
      _ = ∫ z, ∫ η, (Y (z, η)) ^ 2 ∂(PS : Measure S) ∂(θ : Measure PairSpace) := by
            refine integral_congr_ae <| Filter.Eventually.of_forall fun z ↦ ?_
            symm
            exact restrictedTwoPointExitSectionSecondMoment z
      _ = ∫ ω, (Y ω) ^ 2
            ∂((θ : Measure PairSpace) ⊗ₘ Kernel.const PairSpace (PS : Measure S)) := by
              symm
              exact Measure.integral_compProd hYsq_integrable_comp
  have hSecondMoment_eq_var :
      ∫ ω, (Y ω) ^ 2 ∂(P : Measure Ω) = Var[id; (μ : Measure ℝ)] := by
    calc
      ∫ ω, (Y ω) ^ 2 ∂(P : Measure Ω) = ∫ x, x ^ 2 ∂(μ : Measure ℝ) := by
          simpa [Y] using
            hY_law.integral_comp
              ((continuous_id.pow 2).measurable.aestronglyMeasurable)
      _ = Var[id; (μ : Measure ℝ)] := by
            symm
            exact variance_id_eq_secondMoment_of_mean_zero μ hμ_mean_zero hμ_memLp
  -- Route correction: close the theorem on the existing product owner and remove the unstable
  -- `ULift` transport tail entirely.
  have hIndep :
      Ξ ⟂ᵢ[(P : Measure Ω)] (fun ω t ↦ B t ω) := by
    -- Proof comment: `processPath B` is definitionally the same uncurried path map.
    simpa [processPath] using hIndepPath
  have hStoppedLaw :
      HasLaw (stoppedValue B (fun ω ↦ (τ ω : WithTop NNReal))) (μ : Measure ℝ)
        (P : Measure Ω) := by
    -- Proof comment: remove the local alias `Y` to match the theorem statement exactly.
    simpa [Y] using hY_law
  have hτ_eq_var :
      (P : Measure Ω)[fun ω ↦ (τ ω : ℝ)] = Var[id; (μ : Measure ℝ)] := by
    -- Proof comment: the exact clock expectation equals the stopped-value second moment, which
    -- already matches the target variance.
    calc
      (P : Measure Ω)[fun ω ↦ (τ ω : ℝ)] = ∫ ω, (Y ω) ^ 2 ∂(P : Measure Ω) :=
        hτ_eq_secondMoment
      _ = Var[id; (μ : Measure ℝ)] := hSecondMoment_eq_var
  exact ⟨Ω, inferInstance, P, Ξ, B, τ, hIndep, hB, hτ_stop, hStoppedLaw, hτ_eq_var⟩

end ProbabilityTheory
