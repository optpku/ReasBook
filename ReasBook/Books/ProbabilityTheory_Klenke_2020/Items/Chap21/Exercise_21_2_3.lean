/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_8
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_11

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

section

variable {μ : Measure Ω} {B : NNReal → Ω → ℝ}

-- Proof sketch: for `s ≤ t`, split the exponent into the time-`s` part and the increment
-- `B_t - B_s`. Brownian independent increments imply that this increment is independent of the
-- natural filtration up to time `s`, while its centered Gaussian law gives expectation
-- `exp ((σ^2 / 2) * (t - s))`. This exactly cancels the compensator, yielding the martingale
-- conditional-expectation identity.
/-- Helper for Exercise 21.2.3: the compensated Brownian exponential is strongly adapted to the
natural filtration of `B`. -/
lemma brownianStochasticExponential_stronglyAdapted
    (hB : IsBrownianMotion μ B) (σ : ℝ) :
    StronglyAdapted
      (Filtration.natural B hB.stronglyMeasurable)
      (fun t ω ↦ Real.exp (σ * B t ω - (σ ^ 2 / 2) * (t : ℝ))) := by
  intro t
  -- Each time slice is a continuous transform of the Brownian evaluation at time `t`.
  have hBt :
      StronglyMeasurable[Filtration.natural B hB.stronglyMeasurable t] (B t) :=
    Filtration.stronglyAdapted_natural (u := B) hB.stronglyMeasurable t
  have hAffine :
      StronglyMeasurable[Filtration.natural B hB.stronglyMeasurable t]
        (fun ω ↦ σ * B t ω - (σ ^ 2 / 2) * (t : ℝ)) :=
    (hBt.const_mul σ).sub stronglyMeasurable_const
  exact Real.continuous_exp.comp_stronglyMeasurable hAffine

/-- Helper for Exercise 21.2.3: the compensated exponential of a Brownian increment has
expectation `1`. -/
lemma brownianIncrementStochasticExponentialIntegral_eq_one
    (hB : IsBrownianMotion μ B) (σ : ℝ) {s t : NNReal} (hst : s ≤ t) :
    ∫ ω, Real.exp (σ * (B t ω - B s ω) - (σ ^ 2 / 2) * ((t - s : NNReal) : ℝ)) ∂μ = 1 := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  let v : NNReal := t - s
  have hLaw : HasLaw (fun ω ↦ B t ω - B s ω) (gaussianReal 0 v) μ := by
    simpa [v] using brownianIncrement_hasLaw hB hst
  have hSm :
      AEStronglyMeasurable
        (fun x : ℝ ↦ Real.exp (σ * x - (σ ^ 2 / 2) * (v : ℝ)))
        (gaussianReal 0 v) := by
    -- The Gaussian integrand is continuous in the increment variable.
    have hCont :
        Continuous (fun x : ℝ ↦ Real.exp (σ * x - (σ ^ 2 / 2) * (v : ℝ))) :=
      Real.continuous_exp.comp ((continuous_const.mul continuous_id).sub continuous_const)
    exact hCont.aestronglyMeasurable
  -- Push the increment law to the Gaussian measure, then evaluate the Gaussian MGF.
  calc
    ∫ ω, Real.exp (σ * (B t ω - B s ω) - (σ ^ 2 / 2) * (v : ℝ)) ∂μ
        = ∫ x, Real.exp (σ * x - (σ ^ 2 / 2) * (v : ℝ)) ∂gaussianReal 0 v := by
            simpa [Function.comp, v] using hLaw.integral_comp hSm
    _ = ∫ x, Real.exp (-(σ ^ 2 / 2) * (v : ℝ)) * Real.exp (σ * x) ∂gaussianReal 0 v := by
          congr 1
          funext x
          rw [show σ * x - (σ ^ 2 / 2) * (v : ℝ) = (-(σ ^ 2 / 2) * (v : ℝ)) + σ * x by ring]
          rw [Real.exp_add]
    _ = Real.exp (-(σ ^ 2 / 2) * (v : ℝ)) *
          ∫ x, Real.exp (σ * x) ∂gaussianReal 0 v := by
          rw [integral_const_mul]
    _ = Real.exp (-(σ ^ 2 / 2) * (v : ℝ)) * ProbabilityTheory.mgf id (gaussianReal 0 v) σ := by
          rfl
    _ = Real.exp (-(σ ^ 2 / 2) * (v : ℝ)) * Real.exp ((v : ℝ) * σ ^ 2 / 2) := by
          rw [ProbabilityTheory.mgf_id_gaussianReal]
          simp
    _ = 1 := by
          rw [← Real.exp_add]
          rw [show -(σ ^ 2 / 2) * (v : ℝ) + (v : ℝ) * σ ^ 2 / 2 = 0 by ring]
          rw [Real.exp_zero]

/-- Helper for Exercise 21.2.3: the compensated exponential of a Brownian increment is integrable.
-/
lemma brownianIncrementStochasticExponential_integrable
    (hB : IsBrownianMotion μ B) (σ : ℝ) {s t : NNReal} (hst : s ≤ t) :
    Integrable
      (fun ω ↦ Real.exp (σ * (B t ω - B s ω) - (σ ^ 2 / 2) * ((t - s : NNReal) : ℝ)))
      μ := by
  let v : NNReal := t - s
  let g : ℝ → ℝ := fun x ↦ Real.exp (σ * x - (σ ^ 2 / 2) * (v : ℝ))
  have hLaw : HasLaw (fun ω ↦ B t ω - B s ω) (gaussianReal 0 v) μ := by
    simpa [v] using brownianIncrement_hasLaw hB hst
  have hgExp :
      Integrable (fun x : ℝ ↦ Real.exp (σ * x)) (gaussianReal 0 v) := by
    simpa using
      (ProbabilityTheory.integrable_exp_mul_gaussianReal (μ := 0) (v := v) σ)
  have hg : Integrable g (gaussianReal 0 v) := by
    -- Proof comment: the centered exponential differs from `exp (σ x)` by a constant factor.
    have hg_eq :
        g = fun x : ℝ ↦ Real.exp (-(σ ^ 2 / 2) * (v : ℝ)) * Real.exp (σ * x) := by
      funext x
      dsimp [g]
      rw [show σ * x - (σ ^ 2 / 2) * (v : ℝ) = (-(σ ^ 2 / 2) * (v : ℝ)) + σ * x by ring]
      rw [Real.exp_add]
    rw [hg_eq]
    exact hgExp.const_mul _
  have hInc_meas : Measurable (fun ω ↦ B t ω - B s ω) := by
    exact (hB.stronglyMeasurable t).measurable.sub (hB.stronglyMeasurable s).measurable
  -- Proof comment: push Gaussian exponential integrability back along the increment law.
  simpa [g, v, Function.comp] using
    (hLaw.measurePreserving hInc_meas).integrable_comp_of_integrable hg

/-- Helper for Exercise 21.2.3: each fixed-time stochastic exponential is integrable. -/
lemma brownianStochasticExponential_integrable
    (hB : IsBrownianMotion μ B) (σ : ℝ) (t : NNReal) :
    Integrable
      (fun ω ↦ Real.exp (σ * B t ω - (σ ^ 2 / 2) * (t : ℝ)))
      μ := by
  -- Proof comment: the time-`t` factor is the increment exponential over `[0,t]`, and Brownian
  -- motion starts at `0`.
  simpa [hB.zero] using
    (brownianIncrementStochasticExponential_integrable (hB := hB) (σ := σ) (s := 0) (t := t)
      (by simp))

/-- Helper for Exercise 21.2.3: the time-`s` natural filtration is exactly the σ-algebra generated
by the full past path `u ↦ B u` on `Set.Iic s`. -/
lemma naturalFiltration_eq_pastPath
    (hB : IsBrownianMotion μ B) (s : NNReal) :
    Filtration.natural B hB.stronglyMeasurable s =
      MeasurableSpace.comap (fun ω (u : Set.Iic s) ↦ B u ω) MeasurableSpace.pi := by
  -- Proof comment: both sides are the supremum of the coordinate σ-algebras from evaluation maps
  -- `B u` with `u ≤ s`, written once by explicit indices and once by a path-space pullback.
  change (⨆ j, ⨆ (_ : j ≤ s), MeasurableSpace.comap (B j) Real.measurableSpace) =
    MeasurableSpace.comap (fun ω (u : Set.Iic s) ↦ B u ω) MeasurableSpace.pi
  rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
  simp only [MeasurableSpace.comap_comp]
  refine le_antisymm ?_ ?_
  · -- Proof comment: each coordinate `B j` with `j ≤ s` is one of the path evaluations.
    refine iSup₂_le ?_
    intro j hj
    exact le_iSup_of_le ⟨j, hj⟩ le_rfl
  · -- Proof comment: every path coordinate comes from some time `u ≤ s`, so it is in the
    -- natural filtration supremum.
    refine iSup_le ?_
    intro u
    exact le_iSup_of_le (u : NNReal) <| le_iSup_of_le u.2 le_rfl

/-- Helper for Exercise 21.2.3: the future Brownian increment is independent of the full past path
up to time `s`. -/
lemma brownianIncrement_indepFun_pastPath
    (hB : IsBrownianMotion μ B) {s t : NNReal} (hst : s ≤ t) :
    IndepFun
      (fun ω (_ : Unit) ↦ B t ω - B s ω)
      (fun ω (u : Set.Iic s) ↦ B u ω)
      μ := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  let hGaussian : IsGaussianProcess B μ := IsBrownianMotion.isGaussianProcess hB
  have hJoint :
      IsGaussianProcess
        (Sum.elim
          (fun _ : Unit => fun ω ↦ B t ω - B s ω)
          (fun u : Set.Iic s => fun ω ↦ B u ω))
        μ := by
    -- Proof comment: each coordinate of the joint family is a continuous linear image of finitely
    -- many Brownian evaluations, so the whole family remains Gaussian.
    refine hGaussian.of_isGaussianProcess ?_
    intro z
    cases z with
    | inl _ =>
        refine ⟨{t, s}, ?_, ?_⟩
        · refine
            { toFun := fun x ↦ x ⟨t, by simp⟩ - x ⟨s, by simp⟩
              map_add' := by
                intro x y
                calc
                  (x + y) ⟨t, by simp⟩ - (x + y) ⟨s, by simp⟩
                      = (x ⟨t, by simp⟩ + y ⟨t, by simp⟩) -
                          (x ⟨s, by simp⟩ + y ⟨s, by simp⟩) := by
                            rfl
                  _ = x ⟨t, by simp⟩ - x ⟨s, by simp⟩ + (y ⟨t, by simp⟩ - y ⟨s, by simp⟩) := by
                        ring
              map_smul' := by
                intro c x
                calc
                  (c • x) ⟨t, by simp⟩ - (c • x) ⟨s, by simp⟩
                      = c * x ⟨t, by simp⟩ - c * x ⟨s, by simp⟩ := by
                          rfl
                  _ = c * (x ⟨t, by simp⟩ - x ⟨s, by simp⟩) := by
                        ring
                  _ = (RingHom.id ℝ) c • (x ⟨t, by simp⟩ - x ⟨s, by simp⟩) := by
                        rfl
              cont := by
                fun_prop }
        · -- Proof comment: evaluate the linear functional on the Brownian path vector.
          intro ω
          simp
    | inr u =>
        refine ⟨{(u : NNReal)}, ?_, ?_⟩
        · refine
            { toFun := fun x ↦ x ⟨(u : NNReal), by simp⟩
              map_add' := by
                intro x y
                simp
              map_smul' := by
                intro c x
                simp
              cont := by
                fun_prop }
        · -- Proof comment: the past-path coordinate is just evaluation at time `u`.
          intro ω
          simp
  -- Proof comment: for a Gaussian family, vanishing covariance against each past coordinate is
  -- enough to upgrade to independence from the whole past path.
  refine ProbabilityTheory.IsGaussianProcess.indepFun_of_covariance_eq_zero hJoint ?_ ?_ ?_
  · intro _
    exact (hB.stronglyMeasurable t).aemeasurable.sub (hB.stronglyMeasurable s).aemeasurable
  · intro u
    exact (hB.stronglyMeasurable u).aemeasurable
  · intro _ u
    have hs_mem : MemLp (B s) 2 μ := brownianEval_memLp_two hB s
    have ht_mem : MemLp (B t) 2 μ := brownianEval_memLp_two hB t
    have hu_mem : MemLp (B u) 2 μ := brownianEval_memLp_two hB u
    have hu_le_s : (u : NNReal) ≤ s := u.2
    have hu_le_t : (u : NNReal) ≤ t := le_trans hu_le_s hst
    have ht_cov : cov[B t, B u; μ] = ((u : NNReal) : ℝ) := by
      simpa [inf_eq_right.mpr hu_le_t] using IsBrownianMotion.covariance_eq hB t u
    have hs_cov : cov[B s, B u; μ] = ((u : NNReal) : ℝ) := by
      simpa [inf_eq_right.mpr hu_le_s] using IsBrownianMotion.covariance_eq hB s u
    -- Proof comment: the increment covariance is the difference of identical Brownian kernels.
    rw [covariance_fun_sub_left ht_mem hs_mem hu_mem, ht_cov, hs_cov]
    ring

/-- Helper for Exercise 21.2.3: the future Brownian increment is independent of the natural
filtration up to the starting time. -/
lemma brownianIncrement_indep_naturalFiltration
    (hB : IsBrownianMotion μ B) {s t : NNReal} (hst : s ≤ t) :
    Indep
      (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) (borel ℝ))
      (Filtration.natural B hB.stronglyMeasurable s)
      μ := by
  let hIndep :
      Indep
        (MeasurableSpace.comap (fun ω (_ : Unit) ↦ B t ω - B s ω) MeasurableSpace.pi)
        (MeasurableSpace.comap (fun ω (u : Set.Iic s) ↦ B u ω) MeasurableSpace.pi)
        μ :=
    (ProbabilityTheory.IndepFun_iff_Indep _ _ _).mp
      (brownianIncrement_indepFun_pastPath hB hst)
  -- Proof comment: rewrite the right σ-algebra as the natural filtration and collapse the
  -- one-point product on the left to the increment σ-algebra itself.
  simpa [naturalFiltration_eq_pastPath hB s, MeasurableSpace.pi] using hIndep

/-- Exercise 21.2.3: for a Brownian motion `B`, the process
`t ↦ exp (σ B_t - (σ^2 / 2) t)` is a martingale with respect to the natural filtration generated
by `B`. -/
theorem brownianStochasticExponential_martingale
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) (σ : ℝ) :
    Martingale
      (fun t ω ↦ Real.exp (σ * B t ω - (σ ^ 2 / 2) * (t : ℝ)))
      (Filtration.natural B hB.stronglyMeasurable)
      μ := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  let ℱB := Filtration.natural B hB.stronglyMeasurable
  let M : NNReal → Ω → ℝ := fun t ω ↦ Real.exp (σ * B t ω - (σ ^ 2 / 2) * (t : ℝ))
  have hAdapted : StronglyAdapted ℱB M := by
    -- Proof comment: each time slice is already strongly measurable in the natural filtration.
    simpa [ℱB, M] using brownianStochasticExponential_stronglyAdapted hB σ
  refine ⟨hAdapted, ?_⟩
  intro s t hst
  let inc : Ω → ℝ := fun ω ↦ B t ω - B s ω
  let Z : Ω → ℝ := fun ω ↦ Real.exp (σ * inc ω - (σ ^ 2 / 2) * ((t - s : NNReal) : ℝ))
  have hSplit : M t = fun ω ↦ M s ω * Z ω := by
    -- Proof comment: split the stochastic exponential into its past factor and future increment.
    funext ω
    dsimp [M, Z, inc]
    rw [NNReal.coe_sub hst, ← Real.exp_add]
    congr 1
    ring
  have hMs_sm : StronglyMeasurable[ℱB s] (M s) := hAdapted s
  have hMt_int : Integrable (M t) μ := by
    simpa [M] using brownianStochasticExponential_integrable hB σ t
  have hZ_int : Integrable Z μ := by
    simpa [Z, inc] using brownianIncrementStochasticExponential_integrable hB σ hst
  have hProd_int : Integrable (fun ω ↦ M s ω * Z ω) μ := by
    -- Proof comment: use the factorization to inherit integrability from the time-`t` slice.
    exact hMt_int.congr (Filter.EventuallyEq.of_eq hSplit)
  have hInc_meas : Measurable inc := by
    exact (hB.stronglyMeasurable t).measurable.sub (hB.stronglyMeasurable s).measurable
  have hInc_sm : StronglyMeasurable[MeasurableSpace.comap inc (borel ℝ)] inc :=
    (comap_measurable inc).stronglyMeasurable
  have hZ_sm : StronglyMeasurable[MeasurableSpace.comap inc (borel ℝ)] Z := by
    -- Proof comment: the future factor depends measurably only on the increment `B_t - B_s`.
    exact Real.continuous_exp.comp_stronglyMeasurable
      ((hInc_sm.const_mul σ).sub stronglyMeasurable_const)
  have hInc_indep :
      Indep (MeasurableSpace.comap inc (borel ℝ)) (ℱB s) μ := by
    simpa [inc, ℱB] using brownianIncrement_indep_naturalFiltration hB hst
  have hZ_mean_one : ∫ ω, Z ω ∂μ = 1 := by
    simpa [Z, inc] using brownianIncrementStochasticExponentialIntegral_eq_one hB σ hst
  have hZ_condExp_one : μ[Z | ℱB s] =ᵐ[μ] fun _ ↦ 1 := by
    -- Proof comment: independence from the past turns the conditional expectation into the mean.
    refine (MeasureTheory.condExp_indep_eq
      (m₁ := MeasurableSpace.comap inc (borel ℝ))
      (m₂ := ℱB s)
      hInc_meas.comap_le
      (ℱB.le s)
      hZ_sm
      hInc_indep).trans ?_
    exact Filter.Eventually.of_forall fun _ ↦ hZ_mean_one
  -- Proof comment: pull the time-`s` factor out of the conditional expectation and normalize the
  -- future increment factor to `1`.
  calc
    μ[M t | ℱB s] =ᵐ[μ] μ[(fun ω ↦ M s ω * Z ω) | ℱB s] := by
      exact condExp_congr_ae (Filter.EventuallyEq.of_eq hSplit)
    _ =ᵐ[μ] M s * μ[Z | ℱB s] := by
      exact condExp_mul_of_stronglyMeasurable_left hMs_sm hProd_int hZ_int
    _ =ᵐ[μ] M s * 1 := by
      filter_upwards [hZ_condExp_one] with ω hω
      simp [hω]
    _ =ᵐ[μ] M s := by
      simp

end

end ProbabilityTheory
