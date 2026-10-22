/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_4
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_8
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.BrownianStartedAt

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Helper for Theorem 21.11: an ordered Brownian increment has the centered Gaussian law with
variance equal to its time lag. -/
lemma brownianIncrement_hasLaw
    {μ : Measure Ω} {X : NNReal → Ω → ℝ} (hX : IsBrownianMotion μ X)
    {s t : NNReal} (hst : s ≤ t) :
    HasLaw (fun ω ↦ X t ω - X s ω) (gaussianReal 0 (t - s)) μ := by
  letI : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  have hIdent :
      IdentDistrib
        (fun ω ↦ X (((t - s) + s) + 0) ω - X (s + 0) ω)
        (fun ω ↦ X ((t - s) + 0) ω - X 0 ω)
        μ μ :=
    hX.stationaryIncrements.identDistrib_increment (r := 0) (s := t - s) (t := s)
  have hBase :
      HasLaw (fun ω ↦ X ((t - s) + 0) ω - X 0 ω) (gaussianReal 0 (t - s)) μ := by
    by_cases hlag : t - s = 0
    · have hts : t = s := by
        exact le_antisymm (show t ≤ s from (tsub_eq_zero_iff_le).mp hlag) hst
      subst hts
      simpa [gaussianReal_zero_var] using
        (show HasLaw (fun _ : Ω ↦ (0 : ℝ)) (gaussianReal 0 0) μ from
          { aemeasurable := measurable_const.aemeasurable
            map_eq := by simp [gaussianReal_zero_var] })
    · have hlag_pos : 0 < t - s := by
        exact bot_lt_iff_ne_bot.mpr hlag
      have hLaw := hX.gaussian_marginal hlag_pos
      refine hLaw.congr ?_
      exact Filter.Eventually.of_forall fun ω ↦ by simp [hX.zero]
  simpa [tsub_add_cancel_of_le hst] using hIdent.symm.hasLaw hBase

/-- Helper for Theorem 21.11: an ordered increment of a Brownian motion started at `0` has the
centered Gaussian law with variance equal to its time lag. -/
lemma startedAtZeroIncrement_hasLaw
    {μ : Measure Ω} {X : NNReal → Ω → ℝ} (hX : IsBrownianMotionStartedAt μ X 0)
    {s t : NNReal} (hst : s ≤ t) :
    HasLaw (fun ω ↦ X t ω - X s ω) (gaussianReal 0 (t - s)) μ := by
  letI : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  have hIdent :
      IdentDistrib
        (fun ω ↦ X (((t - s) + s) + 0) ω - X (s + 0) ω)
        (fun ω ↦ X ((t - s) + 0) ω - X 0 ω)
        μ μ :=
    hX.stationaryIncrements ((0 : NNReal)) (t - s) s
  have hZeroAe : X 0 =ᵐ[μ] fun _ ↦ 0 :=
    brownianStart_ae_eq_const_of_measurable (hX.stronglyMeasurable 0).measurable hX
  have hBase :
      HasLaw (fun ω ↦ X ((t - s) + 0) ω - X 0 ω) (gaussianReal 0 (t - s)) μ := by
    by_cases hlag : t - s = 0
    · have hts : t = s := by
        exact le_antisymm (show t ≤ s from (tsub_eq_zero_iff_le).mp hlag) hst
      subst hts
      simpa [gaussianReal_zero_var] using
        (show HasLaw (fun _ : Ω ↦ (0 : ℝ)) (gaussianReal 0 0) μ from
          { aemeasurable := measurable_const.aemeasurable
            map_eq := by simp [gaussianReal_zero_var] })
    · have hlag_pos : 0 < t - s := by
        exact bot_lt_iff_ne_bot.mpr hlag
      have hLaw := hX.gaussian_marginal hlag_pos
      refine hLaw.congr ?_
      filter_upwards [hZeroAe] with ω hω
      simp [hω]
  simpa [tsub_add_cancel_of_le hst] using hIdent.symm.hasLaw hBase

/-- Helper for Theorem 21.11: every fixed Brownian marginal belongs to `L²`. -/
lemma brownianEval_memLp_two
    {μ : Measure Ω} {X : NNReal → Ω → ℝ} (hX : IsBrownianMotion μ X) (t : NNReal) :
    MemLp (X t) 2 μ := by
  letI : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  by_cases ht : t = 0
  · -- Proof comment: the time-zero coordinate is the constant zero random variable.
    subst ht
    simp [hX.zero]
  · -- Proof comment: every positive-time Brownian marginal is Gaussian, hence square integrable.
    exact (hX.gaussian_marginal (pos_iff_ne_zero.mpr ht)).hasGaussianLaw.memLp_two

/-- Helper for Theorem 21.11: evaluating a Brownian motion started at `0` along a monotone finite
family of times has a joint Gaussian law. -/
lemma brownianStartedAtZero_hasGaussianLaw_of_monotone
    {μ : Measure Ω} {X : NNReal → Ω → ℝ}
    (hX : IsBrownianMotionStartedAt μ X 0) {n : ℕ} (t : Fin n → NNReal) (ht : Monotone t) :
    HasGaussianLaw (fun ω i ↦ X (t i) ω) μ := by
  letI : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  -- Route correction: work in the monotone `Fin n` normal form, where cumulative sums of
  -- independent Gaussian increments recover the ordered coordinate vector directly.
  let tAux : Fin (n + 1) → NNReal := Fin.cases 0 t
  have htAux : Monotone tAux := Fin.monotone_iff_le_succ.2 fun i => by
    rcases i with ⟨i, hi⟩
    cases i with
    | zero =>
        simp [tAux]
    | succ i =>
        have hi' : i < n := Nat.lt_of_succ_lt hi
        let j : Fin n := ⟨i, hi'⟩
        have hj : j ≤ ⟨i.succ, hi⟩ := Fin.le_iff_val_le_val.2 (Nat.le_succ i)
        change t j ≤ t ⟨i.succ, hi⟩
        exact ht hj
  let Y : Fin n → Ω → ℝ := fun i ω ↦ X (tAux i.succ) ω - X (tAux i.castSucc) ω
  have hY_gauss : ∀ i : Fin n, HasGaussianLaw (Y i) μ := by
    intro i
    exact (startedAtZeroIncrement_hasLaw hX (htAux i.castSucc_le_succ)).hasGaussianLaw
  have hY_indep : iIndepFun Y μ := by
    -- Proof comment: the ordered increment family is independent because Brownian motion has
    -- independent increments on every monotone time mesh.
    simpa [Y] using hX.indepIncrements n tAux htAux
  have hY_joint : HasGaussianLaw (fun ω i ↦ Y i ω) μ :=
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
      ∀ ω i, cumulativeSums (fun j ↦ Y j ω) i = X (t i) ω - X 0 ω := by
    intro ω i
    let f : Fin (n + 1) → ℝ := fun j ↦ X (tAux j) ω
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
    simpa [f, tAux] using hPartial
  have hZeroAe : X 0 =ᵐ[μ] fun _ ↦ 0 :=
    brownianStart_ae_eq_const_of_measurable (hX.stronglyMeasurable 0).measurable hX
  have hRecover :
      (fun ω ↦ cumulativeSums (fun j ↦ Y j ω)) =ᵐ[μ] fun ω i ↦ X (t i) ω := by
    -- Proof comment: the cumulative sums recover `X (t i) - X 0`, and the start value vanishes
    -- almost surely.
    filter_upwards [hZeroAe] with ω hω
    ext i
    simp [hCumulative ω i, hω]
  exact (hY_joint.map cumulativeSums).congr hRecover

/-- Helper for Theorem 21.11: the variance of a centered Gaussian increment with Brownian
covariance equals its time lag, so the increment law is the expected centered Gaussian law. -/
lemma centeredGaussianIncrement_hasLaw_of_brownianCovariance
    {μ : Measure Ω} {X : NNReal → Ω → ℝ} (hgauss : IsGaussianProcess X μ)
    (hmean_zero : ∀ t : NNReal, ∫ ω, X t ω ∂μ = 0)
    (hcov : ∀ s t : NNReal, cov[X s, X t; μ] = ((s ⊓ t : NNReal) : ℝ))
    {s t : NNReal} (hst : s ≤ t) :
    HasLaw (fun ω ↦ X t ω - X s ω) (gaussianReal 0 (t - s)) μ := by
  letI : IsProbabilityMeasure μ := hgauss.isProbabilityMeasure
  let Z : Ω → ℝ := fun ω ↦ X t ω - X s ω
  have hZgauss : HasGaussianLaw Z μ := hgauss.hasGaussianLaw_fun_sub
  have ht_mem : MemLp (X t) 2 μ := (hgauss.hasGaussianLaw_eval t).memLp_two
  have hs_mem : MemLp (X s) 2 μ := (hgauss.hasGaussianLaw_eval s).memLp_two
  have hZ_mem : MemLp Z 2 μ := hZgauss.memLp_two
  have hMean : ∫ ω, Z ω ∂μ = 0 := by
    -- Proof comment: centeredness makes the increment mean vanish by linearity of the integral.
    rw [show Z = fun ω ↦ X t ω - X s ω by rfl]
    rw [integral_sub (ht_mem.integrable (by norm_num)) (hs_mem.integrable (by norm_num))]
    simp [hmean_zero]
  have htt : cov[X t, X t; μ] = (t : ℝ) := by simpa using hcov t t
  have hts : cov[X t, X s; μ] = (s : ℝ) := by
    simpa [inf_eq_right.mpr hst] using hcov t s
  have hst_cov : cov[X s, X t; μ] = (s : ℝ) := by
    simpa [inf_eq_left.mpr hst] using hcov s t
  have hss : cov[X s, X s; μ] = (s : ℝ) := by simpa using hcov s s
  have hVar : Var[Z; μ] = ((t - s : NNReal) : ℝ) := by
    -- Proof comment: expand the increment covariance bilinearly and substitute the Brownian
    -- kernel on the diagonal and off-diagonal terms.
    rw [show Z = fun ω ↦ X t ω - X s ω by rfl]
    rw [← covariance_self hZgauss.aemeasurable, covariance_fun_sub_left ht_mem hs_mem hZ_mem,
      covariance_fun_sub_right ht_mem ht_mem hs_mem,
      covariance_fun_sub_right hs_mem ht_mem hs_mem, htt, hts, hst_cov, hss]
    ring_nf
    simp [NNReal.coe_sub hst]
  refine
    { aemeasurable := hZgauss.aemeasurable
      map_eq := ?_ }
  -- Proof comment: a real Gaussian law is determined by its mean and variance.
  calc
    μ.map Z = gaussianReal (∫ x, x ∂μ.map Z) Var[id; μ.map Z].toNNReal := by
      simpa using
        (IsGaussian.eq_gaussianReal (μ := μ.map Z) hZgauss.isGaussian_map)
    _ = gaussianReal (μ[Z]) Var[id ∘ Z; μ].toNNReal := by
      congr
      · simpa using
          (integral_map (f := id) hZgauss.aemeasurable aestronglyMeasurable_id :
            ∫ x, id x ∂μ.map Z = ∫ ω, id (Z ω) ∂μ)
      · rw [variance_map aemeasurable_id hZgauss.aemeasurable]
    _ = gaussianReal (μ[Z]) Var[Z; μ].toNNReal := by
      simp [Z]
    _ = gaussianReal 0 (t - s) := by
      rw [hMean, hVar]
      simp

/-- Helper for Theorem 21.11: separated increments of a Gaussian process with Brownian covariance
are uncorrelated. -/
lemma covariance_increment_increment_eq_zero_of_brownianCovariance
    {μ : Measure Ω} {X : NNReal → Ω → ℝ} (hgauss : IsGaussianProcess X μ)
    (hcov : ∀ s t : NNReal, cov[X s, X t; μ] = ((s ⊓ t : NNReal) : ℝ))
    {r s t u : NNReal} (hrs : r ≤ s) (hst : s ≤ t) (htu : t ≤ u) :
    cov[fun ω ↦ X s ω - X r ω, fun ω ↦ X u ω - X t ω; μ] = 0 := by
  letI : IsProbabilityMeasure μ := hgauss.isProbabilityMeasure
  have hs_mem : MemLp (X s) 2 μ := (hgauss.hasGaussianLaw_eval s).memLp_two
  have hr_mem : MemLp (X r) 2 μ := (hgauss.hasGaussianLaw_eval r).memLp_two
  have hu_mem : MemLp (X u) 2 μ := (hgauss.hasGaussianLaw_eval u).memLp_two
  have ht_mem : MemLp (X t) 2 μ := (hgauss.hasGaussianLaw_eval t).memLp_two
  have hut_mem : MemLp (fun ω ↦ X u ω - X t ω) 2 μ := (hgauss.hasGaussianLaw_fun_sub
    (s := u) (t := t)).memLp_two
  have hsu : cov[X s, X u; μ] = (s : ℝ) := by
    simpa [inf_eq_left.mpr (le_trans hst htu)] using hcov s u
  have hst_cov : cov[X s, X t; μ] = (s : ℝ) := by
    simpa [inf_eq_left.mpr hst] using hcov s t
  have hru : cov[X r, X u; μ] = (r : ℝ) := by
    simpa [inf_eq_left.mpr (le_trans hrs (le_trans hst htu))] using hcov r u
  have hrt : cov[X r, X t; μ] = (r : ℝ) := by
    simpa [inf_eq_left.mpr (le_trans hrs hst)] using hcov r t
  -- Proof comment: after bilinear expansion, the four Brownian-kernel terms cancel in pairs.
  rw [covariance_fun_sub_left hs_mem hr_mem hut_mem, covariance_fun_sub_right hs_mem hu_mem ht_mem,
    covariance_fun_sub_right hr_mem hu_mem ht_mem, hsu, hst_cov, hru, hrt]
  ring

/-- Helper for Theorem 21.11: Brownian covariance forces independent increments for a centered
Gaussian process. -/
lemma indepIncrements_of_centeredGaussian_brownianCovariance
    {μ : Measure Ω} {X : NNReal → Ω → ℝ} (hgauss : IsGaussianProcess X μ)
    (hcov : ∀ s t : NNReal, cov[X s, X t; μ] = ((s ⊓ t : NNReal) : ℝ)) :
    HasIndepIncrements X μ := by
  letI : IsProbabilityMeasure μ := hgauss.isProbabilityMeasure
  refine HasIndepIncrements.of_nat ?_
  intro t ht _
  let Y : ℕ → Ω → ℝ := fun n ω ↦ X (t (n + 1)) ω - X (t n) ω
  have hY : IsGaussianProcess Y μ := by
    -- Proof comment: each increment is a fixed linear difference of two coordinates of `X`.
    refine hgauss.of_isGaussianProcess ?_
    intro n
    refine
      ⟨{t n, t (n + 1)},
        { toFun := fun x ↦ x ⟨t (n + 1), by simp⟩ - x ⟨t n, by simp⟩
          map_add' := by
            intro x y
            simp [Pi.add_apply]
            ring
          map_smul' := by
            intro c x
            simp [Pi.smul_apply]
            ring
          cont := by
            fun_prop },
        ?_⟩
    -- Proof comment: evaluating the linear map on the coordinate pair recovers the increment.
    intro ω
    simp [Y]
  have hYJoint : IsGaussianProcess (fun (p : Sigma fun _ : ℕ => Unit) ω ↦ Y p.1 ω) μ :=
    hY.comp_right (fun p : Sigma fun _ : ℕ => Unit ↦ p.1)
  have hIndepUnit :
      iIndepFun (fun n ω (_ : Unit) ↦ Y n ω) μ := by
    refine ProbabilityTheory.IsGaussianProcess.iIndepFun_of_covariance_eq_zero hYJoint ?_ ?_
    · intro n _
      exact (hY.hasGaussianLaw_eval n).aemeasurable
    · intro i j hij _ _
      obtain hij_lt | hji_lt := Nat.lt_or_gt_of_ne hij
      · exact covariance_increment_increment_eq_zero_of_brownianCovariance hgauss hcov
          (ht (Nat.le_succ i)) (ht (Nat.succ_le_of_lt hij_lt)) (ht (Nat.le_succ j))
      · rw [covariance_comm]
        exact covariance_increment_increment_eq_zero_of_brownianCovariance hgauss hcov
          (ht (Nat.le_succ j)) (ht (Nat.succ_le_of_lt hji_lt)) (ht (Nat.le_succ i))
  -- Proof comment: evaluate the independent `Unit`-valued family at `()` to recover scalar
  -- increments.
  simpa [Y] using hIndepUnit.comp (fun _ f ↦ f ()) (fun _ ↦ measurable_pi_apply ())

namespace IsBrownianMotionStartedAt

/-- Helper for Theorem 21.11: a Brownian motion started at `0` is a Gaussian process. -/
  theorem isGaussianProcess_zero
    {μ : Measure Ω} {X : NNReal → Ω → ℝ} (hX : IsBrownianMotionStartedAt μ X 0) :
    IsGaussianProcess X μ := by
  letI : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  classical
  -- Proof comment: sort each finite time family once, prove Gaussianity on the monotone `Fin n`
  -- model, and transport that law back to the original finite index set.
  refine ⟨fun I ↦ ?_⟩
  let e : Fin I.card ≃o I := I.orderIsoOfFin rfl
  let eCL : (Fin I.card → ℝ) ≃L[ℝ] (I → ℝ) :=
    (LinearEquiv.funCongrLeft ℝ ℝ e.toEquiv.symm).toContinuousLinearEquivOfContinuous
      (LinearEquiv.funCongrLeft ℝ ℝ e.toEquiv.symm).continuous_of_finiteDimensional
  have hFin :
      HasGaussianLaw (fun ω (i : Fin I.card) ↦ X (e i) ω) μ :=
    brownianStartedAtZero_hasGaussianLaw_of_monotone hX (fun i ↦ (e i : NNReal)) e.monotone
  have hRestrict :
      (fun ω ↦ I.restrict (X · ω)) =
        fun ω ↦
          eCL (fun i : Fin I.card ↦ X (e i) ω) := by
    ext ω i
    simp [eCL, LinearEquiv.funCongrLeft_apply]
  rw [hRestrict]
  exact hFin.map_equiv eCL

end IsBrownianMotionStartedAt

namespace IsBrownianMotion

/-- Every Brownian motion is a Gaussian process. -/
theorem isGaussianProcess
    {μ : Measure Ω} {X : NNReal → Ω → ℝ} (hX : IsBrownianMotion μ X) :
    IsGaussianProcess X μ := by
  letI : IsBrownianMotion μ X := hX
  -- Proof comment: the started-at-zero owner theorem applies immediately through the canonical
  -- instance from standard Brownian motion to Brownian motion started at `0`.
  exact IsBrownianMotionStartedAt.isGaussianProcess_zero (μ := μ) (X := X) inferInstance

/-- Every marginal of a Brownian motion has mean zero. -/
theorem mean_zero
    {μ : Measure Ω} {X : NNReal → Ω → ℝ} (hX : IsBrownianMotion μ X) (t : NNReal) :
    ∫ ω, X t ω ∂μ = 0 := by
  -- Proof comment: for `t = 0` this is the pointwise start value, while for `t > 0` it is the
  -- mean of the prescribed Gaussian marginal.
  by_cases ht : t = 0
  · subst ht
    simp [hX.zero]
  · simpa using (hX.gaussian_marginal (bot_lt_iff_ne_bot.mpr ht)).integral_eq

/-- The covariance kernel of a Brownian motion is `s ∧ t`. -/
theorem covariance_eq
    {μ : Measure Ω} {X : NNReal → Ω → ℝ} (hX : IsBrownianMotion μ X) (s t : NNReal) :
    cov[X s, X t; μ] = ((s ⊓ t : NNReal) : ℝ) := by
  letI : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  -- Proof comment: order the times, split the later value into the past value plus the future
  -- increment, and kill the mixed covariance term by independent increments.
  wlog hst : s ≤ t generalizing s t with hswap
  · rw [covariance_comm, inf_comm]
    exact hswap t s (le_of_not_ge hst)
  have hs_mem : MemLp (X s) 2 μ := brownianEval_memLp_two hX s
  have hIncLaw :
      HasLaw (fun ω ↦ X t ω - X s ω) (gaussianReal 0 (t - s)) μ :=
    brownianIncrement_hasLaw hX hst
  have hInc_mem : MemLp (fun ω ↦ X t ω - X s ω) 2 μ := hIncLaw.hasGaussianLaw.memLp_two
  have hIndep :
      (X s) ⟂ᵢ[μ] (fun ω ↦ X t ω - X s ω) :=
    hX.indepIncrements.indepFun_eval_sub (show (0 : NNReal) ≤ s by simp) hst
      (Filter.Eventually.of_forall fun ω ↦ by simp [hX.zero])
  have hSplit :
      X t = fun ω ↦ X s ω + (X t ω - X s ω) := by
    funext ω
    ring
  have hVarS : Var[X s; μ] = (s : ℝ) := by
    by_cases hs : s = 0
    · subst hs
      simp [hX.zero]
    · simpa using (hX.gaussian_marginal (pos_iff_ne_zero.mpr hs)).variance_eq
  rw [hSplit]
  change cov[X s, X s + (fun ω ↦ X t ω - X s ω); μ] = ((s ⊓ t : NNReal) : ℝ)
  rw [covariance_add_right hs_mem hs_mem hInc_mem, hIndep.covariance_eq_zero hs_mem hInc_mem,
    covariance_self hs_mem.aemeasurable, hVarS]
  simp [inf_eq_left.mpr hst]

end IsBrownianMotion

/-- Helper for Theorem 21.11: a Brownian motion started at `0` has the expected centered
Gaussian marginal at every positive time. -/
lemma startedAtZeroGaussianMarginal
    {μ : Measure Ω} {X : NNReal → Ω → ℝ} (hX : IsBrownianMotionStartedAt μ X 0)
    {t : NNReal} (ht : 0 < t) :
    HasLaw (X t) (gaussianReal 0 t) μ := by
  -- Proof comment: this is exactly the positive-time marginal field of the started-at-zero owner.
  simpa using hX.gaussian_marginal ht

/-- Helper for Theorem 21.11: the covariance kernel of a Brownian motion started at `0` is
`s ∧ t`. -/
lemma startedAtZero_covariance_eq
    {μ : Measure Ω} {X : NNReal → Ω → ℝ} (hX : IsBrownianMotionStartedAt μ X 0) (s t : NNReal) :
    cov[X s, X t; μ] = ((s ⊓ t : NNReal) : ℝ) := by
  letI : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  have hZeroAe : X 0 =ᵐ[μ] fun _ ↦ 0 :=
    brownianStart_ae_eq_const_of_measurable (hX.stronglyMeasurable 0).measurable hX
  -- Proof comment: order the times, split the later value into the earlier value plus the future
  -- increment, and use the almost-sure start value only to justify the independence step at time
  -- `0`.
  wlog hst : s ≤ t generalizing s t with hswap
  · rw [covariance_comm, inf_comm]
    exact hswap t s (le_of_not_ge hst)
  have hs_mem : MemLp (X s) 2 μ := by
    by_cases hs : s = 0
    · subst hs
      have hConst : MemLp (fun _ : Ω ↦ (0 : ℝ)) 2 μ := memLp_const (0 : ℝ)
      exact hConst.congr_norm (hX.stronglyMeasurable 0).aestronglyMeasurable <|
        hZeroAe.mono fun _ hω ↦ by simp [hω]
    · exact (startedAtZeroGaussianMarginal hX (pos_iff_ne_zero.mpr hs)).hasGaussianLaw.memLp_two
  have hIncLaw :
      HasLaw (fun ω ↦ X t ω - X s ω) (gaussianReal 0 (t - s)) μ :=
    startedAtZeroIncrement_hasLaw hX hst
  have hInc_mem : MemLp (fun ω ↦ X t ω - X s ω) 2 μ := hIncLaw.hasGaussianLaw.memLp_two
  have hIndep :
      (X s) ⟂ᵢ[μ] (fun ω ↦ X t ω - X s ω) :=
    hX.indepIncrements.indepFun_eval_sub (show (0 : NNReal) ≤ s by simp) hst hZeroAe
  have hSplit :
      X t = fun ω ↦ X s ω + (X t ω - X s ω) := by
    funext ω
    ring
  have hVarS : Var[X s; μ] = (s : ℝ) := by
    by_cases hs : s = 0
    · subst hs
      have hLaw0 : HasLaw (X 0) (gaussianReal 0 0) μ := by
        -- Proof comment: the time-zero coordinate is almost surely the constant `0`.
        refine
          { aemeasurable := (hX.stronglyMeasurable 0).aemeasurable
            map_eq := ?_ }
        calc
          μ.map (X 0) = μ.map (fun _ : Ω ↦ (0 : ℝ)) := Measure.map_congr hZeroAe
          _ = gaussianReal 0 0 := by simp [gaussianReal_zero_var]
      simpa using hLaw0.variance_eq
    · simpa using (startedAtZeroGaussianMarginal hX (pos_iff_ne_zero.mpr hs)).variance_eq
  rw [hSplit]
  change cov[X s, X s + (fun ω ↦ X t ω - X s ω); μ] = ((s ⊓ t : NNReal) : ℝ)
  rw [covariance_add_right hs_mem hs_mem hInc_mem, hIndep.covariance_eq_zero hs_mem hInc_mem,
    covariance_self hs_mem.aemeasurable, hVarS]
  simp [inf_eq_left.mpr hst]

-- Proof sketch: this is the law-level characterization of Brownian motion started at `0`. For the
-- forward direction, combine the Brownian-motion-started-at-zero axioms with the preceding
-- Gaussianity, centeredness, and covariance lemmas together with the `continuous_paths` field.
-- For the reverse direction, use
-- the centered Gaussian-process characterization from the previous remark: covariance `s ∧ t`
-- yields the Brownian finite-dimensional laws, while the continuity assumption gives the path
-- regularity clause.
/-- A process is Brownian motion started from `0` in the almost-sure sense exactly when it is a
continuous centered Gaussian process with covariance kernel `s ∧ t`. -/
theorem isBrownianMotionStartedAt_zero_iff_isCenteredGaussianProcessWithBrownianCovariance
    (μ : Measure Ω) (X : NNReal → Ω → ℝ) :
    IsBrownianMotionStartedAt μ X 0 ↔
      (∀ t : NNReal, StronglyMeasurable (X t)) ∧
      IsGaussianProcess X μ ∧
        (∀ t : NNReal, ∫ ω, X t ω ∂μ = 0) ∧
        (∀ s t : NNReal, cov[X s, X t; μ] = ((s ⊓ t : NNReal) : ℝ)) ∧
        HasAlmostSurelyContinuousPaths μ X := by
  constructor
  · intro hX
    have hZeroAe : X 0 =ᵐ[μ] fun _ ↦ 0 :=
      brownianStart_ae_eq_const_of_measurable (hX.stronglyMeasurable 0).measurable hX
    -- Route correction: use the Brownian-started-at-zero Gaussian-process theorem directly,
    -- then read off centered marginals and the covariance kernel from the dedicated helpers.
    refine ⟨hX.stronglyMeasurable, hX.isGaussianProcess_zero, ?_, startedAtZero_covariance_eq hX,
      hX.continuous_paths⟩
    intro t
    by_cases ht : t = 0
    · subst ht
      -- Proof comment: the time-zero coordinate is almost surely zero, so its integral vanishes.
      calc
        ∫ ω, X 0 ω ∂μ = ∫ ω, (0 : ℝ) ∂μ := integral_congr_ae hZeroAe
        _ = 0 := by simp
    · -- Proof comment: every positive-time marginal is the centered Gaussian law `N(0,t)`.
      simpa using (startedAtZeroGaussianMarginal hX (pos_iff_ne_zero.mpr ht)).integral_eq
  · rintro ⟨hsm, hgauss, hmean_zero, hcov, hcont⟩
    letI : IsProbabilityMeasure μ := hgauss.isProbabilityMeasure
    have hX0_mem : MemLp (X 0) 2 μ := (hgauss.hasGaussianLaw_eval 0).memLp_two
    have hVar0 : Var[X 0; μ] = 0 := by
      -- Proof comment: the Brownian covariance kernel vanishes at `(0,0)`.
      rw [← covariance_self hX0_mem.aemeasurable, hcov]
      simp
    have hZeroAe : X 0 =ᵐ[μ] fun _ ↦ 0 := by
      -- Proof comment: zero variance forces the time-zero coordinate to equal its mean a.s.
      simpa [hmean_zero 0] using ae_eq_integral_of_variance_eq_zero hX0_mem hVar0
    refine
      { stronglyMeasurable := hsm
        start := ?_
        indepIncrements := indepIncrements_of_centeredGaussian_brownianCovariance hgauss hcov
        stationaryIncrements := ?_
        gaussian_marginal := ?_
        continuous_paths := hcont }
    · -- Proof comment: convert the almost-sure equality `X 0 = 0` into the owner probability
      -- statement.
      exact
        (ae_iff_prob_eq_one ((hsm 0).measurable.eq measurable_const)).mp <| by
          simpa using hZeroAe
    · intro r s t
      have hLeft :
          HasLaw (fun ω ↦ X ((s + t) + r) ω - X (t + r) ω) (gaussianReal 0 s) μ := by
        -- Proof comment: the left increment has lag `s`, so its Gaussian law depends only on `s`.
        have hle : t + r ≤ (s + t) + r := by
          have ht' : t ≤ s + t := by
            simp
          convert add_le_add_left ht' r using 1
        have hLag : ((s + t) + r) - (t + r) = s := by
          convert add_tsub_cancel_left (t + r) s using 1
          simp [add_comm, add_left_comm]
        simpa [hLag] using
          centeredGaussianIncrement_hasLaw_of_brownianCovariance hgauss hmean_zero hcov hle
      have hRight :
          HasLaw (fun ω ↦ X (s + r) ω - X r ω) (gaussianReal 0 s) μ := by
        -- Proof comment: the right increment has the same lag `s`.
        have hle : r ≤ s + r := by
          have hs' : (0 : NNReal) ≤ s := by simp
          convert add_le_add_left hs' r using 1
          simp [add_comm]
        have hLag : (s + r) - r = s := by
          convert add_tsub_cancel_left r s using 1
          simp [add_comm]
        simpa [hLag] using
          centeredGaussianIncrement_hasLaw_of_brownianCovariance hgauss hmean_zero hcov hle
      exact hLeft.identDistrib hRight
    · intro t ht
      -- Proof comment: the positive-time marginal is the `s = 0` increment, and `X 0 = 0` a.s.
      have hInc :
          HasLaw (fun ω ↦ X t ω - X 0 ω) (gaussianReal 0 t) μ := by
        simpa using
          (centeredGaussianIncrement_hasLaw_of_brownianCovariance hgauss hmean_zero hcov
            (s := 0) (t := t) (show (0 : NNReal) ≤ t by simp))
      refine hInc.congr ?_
      filter_upwards [hZeroAe] with ω hω
      simp [hω]

-- Proof sketch: combine the previous almost-sure-start characterization with the additional
-- pointwise initial-value clause `X 0 = 0` required by the standard `IsBrownianMotion` owner.
/-- Theorem 21.11: for a real-valued stochastic process on `[0,∞)`, standard Brownian motion is
equivalent to being a continuous centered Gaussian process with covariance kernel `s ∧ t` together
with the pointwise initial condition `X 0 = 0`. -/
theorem isBrownianMotion_iff_isCenteredGaussianProcessWithBrownianCovariance
    (μ : Measure Ω) (X : NNReal → Ω → ℝ) :
    IsBrownianMotion μ X ↔
      X 0 = 0 ∧
        IsGaussianProcess X μ ∧
          (∀ t : NNReal, ∫ ω, X t ω ∂μ = 0) ∧
          (∀ s t : NNReal, cov[X s, X t; μ] = ((s ⊓ t : NNReal) : ℝ)) ∧
          HasAlmostSurelyContinuousPaths μ X := by
  constructor
  · intro hX
    -- Proof comment: the Brownian owner already stores every field on the right-hand side.
    refine ⟨hX.zero, hX.isGaussianProcess, hX.mean_zero, hX.covariance_eq, hX.continuous_paths⟩
  · rintro ⟨h0, hgauss, hmean_zero, hcov, hcont⟩
    letI : IsProbabilityMeasure μ := hgauss.isProbabilityMeasure
    refine
      { zero := h0
        indepIncrements := indepIncrements_of_centeredGaussian_brownianCovariance hgauss hcov
        stationaryIncrements := ?_
        gaussian_marginal := ?_
        continuous_paths := hcont }
    · intro r s t
      have hLeft :
          HasLaw (fun ω ↦ X ((s + t) + r) ω - X (t + r) ω) (gaussianReal 0 s) μ := by
        -- Proof comment: the left increment has length `s`, so Brownian covariance fixes its law.
        have hle : t + r ≤ (s + t) + r := by
          have ht' : t ≤ s + t := by
            simp
          convert add_le_add_left ht' r using 1
        have hLag : ((s + t) + r) - (t + r) = s := by
          convert add_tsub_cancel_left (t + r) s using 1
          simp [add_comm, add_left_comm]
        simpa [hLag] using
          centeredGaussianIncrement_hasLaw_of_brownianCovariance hgauss hmean_zero hcov hle
      have hRight :
          HasLaw (fun ω ↦ X (s + r) ω - X r ω) (gaussianReal 0 s) μ := by
        -- Proof comment: the reference increment has the same length `s`.
        have hle : r ≤ s + r := by
          have hs' : (0 : NNReal) ≤ s := by simp
          convert add_le_add_left hs' r using 1
          simp [add_comm]
        have hLag : (s + r) - r = s := by
          convert add_tsub_cancel_left r s using 1
          simp [add_comm]
        simpa [hLag] using
          centeredGaussianIncrement_hasLaw_of_brownianCovariance hgauss hmean_zero hcov hle
      exact hLeft.identDistrib hRight
    · intro t ht
      have hInc :
          HasLaw (fun ω ↦ X t ω - X 0 ω) (gaussianReal 0 t) μ := by
        simpa using
          (centeredGaussianIncrement_hasLaw_of_brownianCovariance hgauss hmean_zero hcov
            (s := 0) (t := t) (show (0 : NNReal) ≤ t by simp))
      refine hInc.congr ?_
      exact Filter.Eventually.of_forall fun ω ↦ by simp [h0]

end ProbabilityTheory
