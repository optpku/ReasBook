/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_3
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_12
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Books.ProbabilityTheory_Klenke_2020.Items.Chap22.Theorem_22_5
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_31
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Exercise_21_2_4
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.StandardBrownianMotionVector
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.GeneralizedStrongSolutionAPI
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Remark_26_14
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Theorem_26_8.CoefficientConditions
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Theorem_26_8.StrongMarkovAtStart

open Filter MeasureTheory ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {n m : ℕ}

section GeneralizedStrongSolutions

variable (b : SDEDriftCoeff n) (σ : SDEDiffusionCoeff n m)

/-- Helper for Theorem 26.8: enlarging the coefficient bound to `max |K| 1` preserves the
spatial Lipschitz and linear-growth hypotheses. -/
private theorem inflateLipschitzLinearGrowthBound
    {K : ℝ}
    (hbσ_lipschitz : SDESpaceLipschitzWith K b σ)
    (hbσ_growth : SDELinearGrowthWith K b σ) :
    SDESpaceLipschitzWith (max |K| 1) b σ ∧
      SDELinearGrowthWith (max |K| 1) b σ := by
  refine ⟨?_, ?_⟩
  · intro x x' t
    -- Proof comment: the source Lipschitz estimate remains valid after replacing `K` by the
    -- larger positive constant `max |K| 1`.
    refine le_trans (hbσ_lipschitz x x' t) ?_
    have hK_le : K ≤ max |K| (1 : ℝ) := le_trans (le_abs_self K) (le_max_left _ _)
    exact mul_le_mul_of_nonneg_right hK_le (norm_nonneg _)
  · intro x t
    -- Proof comment: the same monotonicity argument works for the quadratic growth bound because
    -- the factor `1 + ‖x‖ ^ 2` is nonnegative.
    refine le_trans (hbσ_growth x t) ?_
    have hK_sq :
        K ^ 2 ≤ (max |K| (1 : ℝ)) ^ 2 := by
      have hAbs_le : |K| ≤ max |K| (1 : ℝ) := le_max_left _ _
      have hMax_nonneg : 0 ≤ max |K| (1 : ℝ) := le_trans zero_le_one (le_max_right _ _)
      have hAbs_sq : |K| ^ 2 ≤ (max |K| (1 : ℝ)) ^ 2 :=
        (sq_le_sq).2 <| by
          rw [abs_of_nonneg (abs_nonneg K), abs_of_nonneg hMax_nonneg]
          exact hAbs_le
      simpa [sq_abs] using hAbs_sq
    have hFactor_nonneg : 0 ≤ 1 + ‖x‖ ^ 2 := by
      nlinarith [sq_nonneg ‖x‖]
    exact mul_le_mul_of_nonneg_right hK_sq hFactor_nonneg

/-- Helper for Theorem 26.8: a continuous nonnegative function on `[0, T]` that is bounded by a
constant multiple of its own past integral must vanish identically. This is the scalar Gronwall
endgame needed after the SDE difference estimate has been reduced to a Volterra inequality. -/
private theorem zero_of_selfIntervalIntegralBound
    {T C : ℝ}
    (hT_nonneg : 0 ≤ T)
    {f : ℝ → ℝ}
    (hf_cont : ContinuousOn f (Set.Icc 0 T))
    (hf_nonneg : ∀ t ∈ Set.Icc 0 T, 0 ≤ f t)
    (hf_bound : ∀ t ∈ Set.Icc 0 T, f t ≤ C * ∫ s in (0 : ℝ)..t, f s) :
    ∀ t ∈ Set.Icc 0 T, f t = 0 := by
  let g : ℝ → ℝ := fun t ↦ ∫ s in (0 : ℝ)..t, f s
  have hg_cont : ContinuousOn g (Set.Icc 0 T) := by
    -- Proof comment: the primitive of an integrable function is continuous on the interval.
    have hf_int_on : IntegrableOn f (Set.uIcc (0 : ℝ) T) volume := by
      simpa [Set.uIcc_of_le hT_nonneg] using
        (hf_cont.integrableOn_Icc : IntegrableOn f (Set.Icc (0 : ℝ) T) volume)
    simpa [Set.uIcc_of_le hT_nonneg] using
      (intervalIntegral.continuousOn_primitive_interval hf_int_on :
        ContinuousOn (fun t ↦ ∫ s in (0 : ℝ)..t, f s) (Set.uIcc (0 : ℝ) T))
  have hg_nonneg : ∀ t ∈ Set.Icc 0 T, 0 ≤ g t := by
    intro t ht
    -- Proof comment: the primitive is nonnegative because the integrand is nonnegative on
    -- every shorter interval `[0, t]`.
    have hNonnegOn : ∀ s ∈ Set.Icc (0 : ℝ) t, 0 ≤ f s := by
      intro s hs
      exact hf_nonneg s ⟨hs.1, le_trans hs.2 ht.2⟩
    exact intervalIntegral.integral_nonneg ht.1 hNonnegOn
  have hg_deriv :
      ∀ x ∈ Set.Ico (0 : ℝ) T, HasDerivWithinAt g (f x) (Set.Ici x) x := by
    intro x hx
    have hf_cont_left : ContinuousOn f (Set.Icc (0 : ℝ) x) := by
      intro y hy
      exact (hf_cont y ⟨hy.1, le_trans hy.2 hx.2.le⟩).mono <| by
        intro z hz
        exact ⟨hz.1, le_trans hz.2 hx.2.le⟩
    have hf_cont_right_on : ContinuousOn f (Set.Icc x T) := by
      intro y hy
      exact (hf_cont y ⟨le_trans hx.1 hy.1, hy.2⟩).mono <| by
        intro z hz
        exact ⟨le_trans hx.1 hz.1, hz.2⟩
    have hf_int : IntervalIntegrable f volume (0 : ℝ) x :=
      ContinuousOn.intervalIntegrable_of_Icc hx.1 hf_cont_left
    have hderiv_Icc :
        HasDerivWithinAt g (f x) (Set.Icc x T) x := by
      -- Proof comment: on `[x, T]`, the primitive differentiates back to the integrand at the
      -- left endpoint `x`.
      have := Fact.mk (show x ∈ Set.Icc x T from ⟨le_rfl, hx.2.le⟩)
      simpa [g] using
        intervalIntegral.integral_hasDerivWithinAt_right
          hf_int
          (hf_cont_right_on.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc x)
          (hf_cont_right_on.continuousWithinAt ⟨le_rfl, hx.2.le⟩)
    have hIcc_mem : Set.Icc x T ∈ nhdsWithin x (Set.Ici x) := by
      -- Proof comment: near `x`, restricting to `Icc x T` is the same as restricting to the
      -- right-neighborhood `Ici x` together with the ambient bound `y ≤ T`.
      have hInter : Set.Ici x ∩ Set.Iic T ∈ nhdsWithin x (Set.Ici x) :=
        inter_mem_nhdsWithin (Set.Ici x) (Iic_mem_nhds hx.2)
      change Set.Ici x ∩ Set.Iic T ∈ nhdsWithin x (Set.Ici x)
      exact hInter
    exact hderiv_Icc.mono_of_mem_nhdsWithin hIcc_mem
  have hg_zero :
      ∀ t ∈ Set.Icc (0 : ℝ) T, g t = 0 := by
    -- Proof comment: apply Gronwall to the primitive `g`; its derivative is `f`, and the
    -- assumed Volterra bound rewrites as `g' ≤ C * g`.
    refine
      (@eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
        ℝ _ _ g f C 0 T hg_cont hg_deriv ?_ ?_)
    · simp [g]
    · intro x hx
      have hfx_nonneg : 0 ≤ f x := hf_nonneg x ⟨hx.1, hx.2.le⟩
      have hgx_nonneg : 0 ≤ g x := hg_nonneg x ⟨hx.1, hx.2.le⟩
      have hle : f x ≤ C * g x := hf_bound x ⟨hx.1, hx.2.le⟩
      calc
        ‖f x‖ = f x := by simpa [Real.norm_eq_abs, abs_of_nonneg hfx_nonneg]
        _ ≤ C * g x := hle
        _ = C * ‖g x‖ := by simpa [Real.norm_eq_abs, abs_of_nonneg hgx_nonneg]
  intro t ht
  have hft_nonneg : 0 ≤ f t := hf_nonneg t ht
  have hft_le_zero : f t ≤ 0 := by
    -- Proof comment: once the primitive vanishes, the original Volterra bound forces each value
    -- `f t` to be at most `0`.
    simpa [g, hg_zero t ht, mul_zero] using hf_bound t ht
  exact le_antisymm hft_le_zero hft_nonneg

/-- Helper for Theorem 26.8: Gaussian laws pull back along a measure-preserving map without
changing the pushed-forward Gaussian measure. -/
private theorem hasGaussianLaw_comp_measurePreserving
    {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
    {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E] [MeasurableSpace E]
    {μ : Measure β} {ν : Measure α} {f : α → β} {X : β → E}
    (hX : HasGaussianLaw X μ) (hf : MeasurePreserving f ν μ) :
    HasGaussianLaw (X ∘ f) ν := by
  let hLawX : HasLaw X (μ.map X) μ := { map_eq := rfl }
  let hComp : HasLaw (X ∘ f) (μ.map X) ν := HasLaw.comp hLawX hf.hasLaw
  letI : IsGaussian (μ.map X) := hX.isGaussian_map
  -- Proof comment: Gaussianity is determined by the pushed-forward law, and measure preservation
  -- keeps that law unchanged after precomposition.
  exact hComp.hasGaussianLaw

/-- Helper for Theorem 26.8: pulling a scalar Brownian motion back along a measure-preserving map
preserves the Brownian owner. -/
private theorem isBrownianMotion_comp_measurePreserving
    {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
    {ν : Measure α} [IsProbabilityMeasure ν]
    {μ : Measure β} [IsProbabilityMeasure μ]
    {f : α → β}
    (hf : MeasurePreserving f ν μ)
    {B : NNReal → β → ℝ}
    (hB : IsBrownianMotion μ B) :
    IsBrownianMotion ν (fun t x ↦ B t (f x)) := by
  refine
    (isBrownianMotion_iff_isCenteredGaussianProcessWithBrownianCovariance
      ν (fun t x ↦ B t (f x))).2 ?_
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- Proof comment: the deterministic time-zero value survives unchanged after precomposition.
    funext x
    simpa using congrFun hB.zero (f x)
  · refine ⟨fun I ↦ ?_⟩
    -- Proof comment: every finite-dimensional Gaussian law pulls back through the
    -- measure-preserving map.
    simpa [Function.comp_def] using
      hasGaussianLaw_comp_measurePreserving
        (hB.isGaussianProcess.hasGaussianLaw I) hf
  · intro t
    -- Proof comment: centered expectations are preserved because the pullback has the same
    -- pushforward law.
    calc
      ∫ x, B t (f x) ∂ν = ∫ y, B t y ∂μ := by
          simpa [Function.comp_def] using
            (hf.hasLaw.integral_comp
              (hB.stronglyMeasurable t).aestronglyMeasurable)
      _ = 0 := hB.mean_zero t
  · intro s t
    -- Proof comment: the covariance kernel is likewise invariant under measure-preserving
    -- precomposition.
    calc
      cov[(fun x ↦ B s (f x)), (fun x ↦ B t (f x)); ν]
          = cov[(fun y ↦ B s y), (fun y ↦ B t y); μ] := by
              simpa [Function.comp_def] using
                (hf.hasLaw.covariance_comp
                  (hB.stronglyMeasurable s).aemeasurable
                  (hB.stronglyMeasurable t).aemeasurable)
      _ = ((s ⊓ t : NNReal) : ℝ) := hB.covariance_eq s t
  · -- Proof comment: the exceptional null set for path continuity pulls back along the same
    -- measure-preserving map.
    refine (ae_iff.2 ?_)
    have hnull : ν {x | ¬ Continuous (processPath (fun t a ↦ B t (f a)) x)} = 0 := by
      have hnullB : μ {y | ¬ Continuous (processPath B y)} = 0 :=
        (ae_iff.1 hB.continuous_paths)
      simpa [HasAlmostSurelyContinuousPaths, processPath, Function.comp] using
        hf.preimage_null hnullB
    simpa [HasAlmostSurelyContinuousPaths] using hnull

/-- Helper for Theorem 26.8: a continuous Euclidean-valued Brownian vector can be repackaged as a
path-valued Brownian witness on `EuclideanPathSpace`. -/
private theorem pathValuedBrownian_of_continuousStandardBrownianVector
    {Ω0 : Type u} [MeasurableSpace Ω0]
    (μ0 : ProbabilityMeasure Ω0)
    {W0 : NNReal → Ω0 → EuclideanSpace ℝ (Fin m)}
    (hW0 : IsStandardBrownianMotionVector (μ0 : Measure Ω0) W0)
    (hW0cont : ∀ ω, Continuous (fun t : NNReal ↦ W0 t ω)) :
    ∃ Wpath : Ω0 → EuclideanPathSpace m,
      IsBrownianMotionWithFiltration
        (processFiltration (pathProcess Wpath))
        (μ0 : Measure Ω0)
        (pathProcess Wpath) := by
  let Wpath : Ω0 → EuclideanPathSpace m := fun ω ↦
    ⟨fun t ↦ (EuclideanSpace.equiv (Fin m) ℝ) (W0 t ω), by
      -- Proof comment: the Brownian sample path is continuous in Euclidean space, and the
      -- coordinate equivalence transports that continuity to `Fin m → ℝ`.
      simpa using (EuclideanSpace.equiv (Fin m) ℝ).continuous.comp (hW0cont ω)⟩
  refine ⟨Wpath, ?_⟩
  refine ⟨?_, ?_⟩
  · -- Proof comment: converting the path-valued witness back through
    -- `CoordinateProcess.toEuclidean` recovers the original vector Brownian process exactly.
    simpa [ProbabilityTheory.CoordinateProcess.toEuclidean, pathProcess, Wpath] using hW0
  · intro t
    -- Proof comment: every process is adapted to its own natural filtration by construction.
    refine measurable_iff_comap_le.2 ?_
    have hWt_meas : Measurable (pathProcess Wpath t) := by
      exact
        ((EuclideanSpace.equiv (Fin m) ℝ).continuous.measurable).comp
          (IsStandardBrownianMotionVector.stronglyMeasurable hW0 t).measurable
    exact le_inf (Measurable.comap_le hWt_meas) <| by
      refine le_iSup_of_le t ?_
      exact le_iSup_of_le le_rfl le_rfl

/-- Helper for Theorem 26.8: covariance is unchanged after almost-everywhere replacement of both
real-valued coordinates. -/
private theorem covariance_congr_ae_local
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} {X X' Y Y' : Ω → ℝ}
    (hX : X =ᵐ[μ] X') (hY : Y =ᵐ[μ] Y') :
    cov[X, Y; μ] = cov[X', Y'; μ] := by
  have hIntX : ∫ ω, X ω ∂μ = ∫ ω, X' ω ∂μ := integral_congr_ae hX
  have hIntY : ∫ ω, Y ω ∂μ = ∫ ω, Y' ω ∂μ := integral_congr_ae hY
  -- Proof comment: once the expectations agree, the covariance integrands are equal almost
  -- everywhere termwise.
  rw [covariance, covariance]
  refine integral_congr_ae ?_
  filter_upwards [hX, hY] with ω hωX hωY
  simp [hωX, hωY, hIntX, hIntY]

/-- Helper for Theorem 26.8: the everywhere-continuous Brownian modification is still Brownian.
-/
private theorem brownianContinuousVersion_isBrownianMotionLocal
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) :
    IsBrownianMotion μ (brownianContinuousVersion hB) := by
  -- Proof comment: the Brownian characterization is stable under fixed-time almost-everywhere
  -- modification, and the patched process is continuous by construction.
  rw [isBrownianMotion_iff_isCenteredGaussianProcessWithBrownianCovariance]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · funext ω
    by_cases hω : ω ∈ brownianContinuousVersionExceptionSet hB
    · simp [brownianContinuousVersion, hω]
    · simp [brownianContinuousVersion, hω, hB.zero]
  · exact
      (IsBrownianMotion.isGaussianProcess hB).congr
        (fun t ↦ brownianContinuousVersion_areModifications hB t)
  · intro t
    exact
      (integral_congr_ae
        (brownianContinuousVersion_areModifications hB t)).symm.trans
        (IsBrownianMotion.mean_zero hB t)
  · intro s t
    exact
      (covariance_congr_ae_local
        (brownianContinuousVersion_areModifications hB s)
        (brownianContinuousVersion_areModifications hB t)).symm.trans
        (IsBrownianMotion.covariance_eq hB s t)
  · filter_upwards with ω
    simpa [HasAlmostSurelyContinuousPaths, processPath] using
      brownianContinuousVersion_continuous hB ω

/-- Helper for Theorem 26.8: Chapter 22 supplies one scalar Brownian motion, and the public
continuous-version API turns it into an everywhere continuous scalar witness. -/
private theorem scalarContinuousStandardBrownianWitness :
    ∃ (Ω0 : Type) (_ : MeasurableSpace Ω0) (μ0 : ProbabilityMeasure Ω0)
      (B : NNReal → Ω0 → ℝ),
        IsBrownianMotion (μ0 : Measure Ω0) B ∧
          ∀ ω, Continuous (fun t : NNReal ↦ B t ω) := by
  let μstd : ProbabilityMeasure ℝ := ⟨gaussianReal 0 1, inferInstance⟩
  have hμstd_mean_zero : ∫ x, x ∂(μstd : Measure ℝ) = 0 := by
    -- Proof comment: the standard Gaussian used for the embedding is centered.
    simpa [μstd] using ProbabilityTheory.integral_id_gaussianReal
  have hμstd_memLp : MemLp id 2 (μstd : Measure ℝ) := by
    -- Proof comment: the standard Gaussian has finite second moment, so the Skorohod embedding
    -- theorem applies directly.
    simpa [μstd] using
      (ProbabilityTheory.memLp_id_gaussianReal' 2 (by simp))
  rcases exists_skorohod_embedding μstd hμstd_mean_zero hμstd_memLp with
    ⟨Ω0, mΩ0, μ0, _Ξ, B, _τ, _hIndep, hB, _hτ, _hLaw, _hVar⟩
  let Bc : NNReal → Ω0 → ℝ :=
    brownianContinuousVersion hB
  refine ⟨Ω0, mΩ0, μ0, Bc, ?_, ?_⟩
  · -- Proof comment: the continuous-version repair preserves the Brownian owner.
    simpa [Bc] using
      brownianContinuousVersion_isBrownianMotionLocal hB
  · intro ω
    -- Proof comment: by construction the repaired scalar witness has continuous sample paths.
    simpa [Bc] using
      brownianContinuousVersion_continuous hB ω

/-- Helper for Theorem 26.8: taking a finite product of independent scalar continuous Brownian
witnesses yields one continuous standard Brownian vector. -/
private theorem existsContinuousStandardBrownianVectorWitness [NeZero m] :
    ∃ (Ω0 : Type) (_ : MeasurableSpace Ω0) (μ0 : ProbabilityMeasure Ω0)
      (W0 : NNReal → Ω0 → EuclideanSpace ℝ (Fin m)),
        IsStandardBrownianMotionVector (μ0 : Measure Ω0) W0 ∧
          ∀ ω, Continuous (fun t : NNReal ↦ W0 t ω) := by
  rcases scalarContinuousStandardBrownianWitness with
    ⟨Ωs, mΩs, μs, B, hB, hBcont⟩
  let Ω0 : Type := Fin m → Ωs
  let μ0 : ProbabilityMeasure Ω0 := ProbabilityMeasure.pi (fun _ : Fin m ↦ μs)
  let Wscalar : Ωs → NNReal → ℝ := fun ω t ↦ B t ω
  let W0 : NNReal → Ω0 → EuclideanSpace ℝ (Fin m) := fun t ω ↦
    (EuclideanSpace.equiv (Fin m) ℝ).symm (fun i : Fin m ↦ B t (ω i))
  have hWscalar_meas : Measurable Wscalar := by
    refine measurable_pi_lambda _ fun t ↦ ?_
    exact (hB.stronglyMeasurable t).measurable
  have hEvalIndep :
      iIndepFun (Function.eval : Fin m → Ω0 → Ωs) (μ0 : Measure Ω0) := by
    simpa [Ω0, μ0] using
      (iIndepFun_pi (fun _ : Fin m ↦ aemeasurable_id) :
        iIndepFun Function.eval (Measure.pi fun _ : Fin m ↦ (μs : Measure Ωs)))
  have hScalarProcessIndep :
      iIndepFun (fun i : Fin m ↦ fun ω : Ω0 ↦ Wscalar (ω i)) (μ0 : Measure Ω0) := by
    -- Proof comment: the product coordinates stay independent after applying the same measurable
    -- scalar Brownian-path lift to each coordinate.
    simpa [Ω0] using hEvalIndep.comp (fun _ ↦ Wscalar) (fun _ ↦ hWscalar_meas)
  have hW0 : IsStandardBrownianMotionVector (μ0 : Measure Ω0) W0 := by
    refine
      { isBrownianMotion := ?_
        iIndepFun := ?_ }
    · intro i
      let hEval :
          MeasurePreserving (Function.eval i : Ω0 → Ωs)
            (μ0 : Measure Ω0) (μs : Measure Ωs) :=
        measurePreserving_eval (fun _ : Fin m ↦ (μs : Measure Ωs)) i
      -- Proof comment: each vector coordinate is the scalar witness pulled back along the
      -- corresponding product-coordinate projection.
      simpa [W0, Wscalar, Function.comp_def] using
        isBrownianMotion_comp_measurePreserving hEval hB
    · -- Proof comment: the vector coordinates remain independent because they come from the
      -- independent product-coordinate family.
      simpa [W0, Wscalar] using hScalarProcessIndep
  refine ⟨Ω0, inferInstance, μ0, W0, hW0, ?_⟩
  intro ω
  have hcoords : ∀ i : Fin m, Continuous (fun t : NNReal ↦ W0 t ω i) := by
    intro i
    simpa [W0] using hBcont (ω i)
  have hPi : Continuous (fun t : NNReal ↦ fun i : Fin m ↦ W0 t ω i) :=
    continuous_pi hcoords
  -- Proof comment: continuity in `EuclideanSpace ℝ (Fin m)` is equivalent to coordinatewise
  -- continuity through the canonical Euclidean equivalence.
  simpa [W0] using (EuclideanSpace.equiv (Fin m) ℝ).symm.continuous.comp hPi

/-- Helper for Theorem 26.8: there exists one path-valued Brownian witness whose natural
filtration is the ambient filtration for the fixed-start Picard construction. -/
private theorem existsStandardBrownianPathWitness :
    ∃ (Ω0 : Type), ∃ _ : MeasurableSpace Ω0, ∃ μ0 : ProbabilityMeasure Ω0,
      ∃ Wpath : Ω0 → EuclideanPathSpace m,
        IsBrownianMotionWithFiltration
          (processFiltration (pathProcess Wpath))
          (μ0 : Measure Ω0)
          (pathProcess Wpath) := by
  by_cases hm : m = 0
  · subst hm
    let μ0 : ProbabilityMeasure PUnit := ⟨Measure.dirac PUnit.unit, inferInstance⟩
    let W0 : NNReal → PUnit → EuclideanSpace ℝ (Fin 0) := fun _ _ ↦ 0
    have hW0 : IsStandardBrownianMotionVector (μ0 : Measure PUnit) W0 := by
      refine
        { isBrownianMotion := ?_
          iIndepFun := ?_ }
      · intro i
        exact Fin.elim0 i
      · exact iIndepFun.of_subsingleton
    have hW0cont : ∀ ω, Continuous (fun t : NNReal ↦ W0 t ω) := by
      intro ω
      simpa [W0] using
        (continuous_const : Continuous fun _ : NNReal ↦ (0 : EuclideanSpace ℝ (Fin 0)))
    rcases
        (@pathValuedBrownian_of_continuousStandardBrownianVector 0 PUnit _ μ0 W0
          hW0 hW0cont)
      with
      ⟨Wpath, hWpath⟩
    exact ⟨PUnit, inferInstance, μ0, Wpath, hWpath⟩
  · letI : NeZero m := ⟨hm⟩
    rcases (@existsContinuousStandardBrownianVectorWitness m _)
      with
      ⟨Ω0, mΩ0, μ0, W0, hW0, hW0cont⟩
    rcases
        (@pathValuedBrownian_of_continuousStandardBrownianVector m Ω0 _ μ0 W0
          hW0 hW0cont)
      with
      ⟨Wpath, hWpath⟩
    exact ⟨Ω0, mΩ0, μ0, Wpath, hWpath⟩

/-- Helper for Theorem 26.8: a continuous Euclidean path is determined by its rational-time
values. -/
private theorem nnratRestriction_injective_euclideanPath {d : ℕ} :
    Function.Injective
      (fun ω : EuclideanPathSpace d ↦ fun q : ℚ≥0 ↦ ω (q : NNReal)) := by
  intro ω₁ ω₂ hω
  ext t i
  -- Proof comment: equality on the dense rational-time set extends to all times because both
  -- coordinates are continuous.
  have hEq :
      Set.EqOn
        (fun s : NNReal ↦ ω₁ s i)
        (fun s : NNReal ↦ ω₂ s i)
        (Set.range fun q : ℚ≥0 ↦ (q : NNReal)) := by
    rintro _ ⟨q, rfl⟩
    exact congrFun (congrFun hω q) i
  have hDense : Dense (Set.range fun q : ℚ≥0 ↦ (q : NNReal)) := denseRange_nnratCast
  exact
    congrFun
      (Continuous.ext_on
        hDense
        ((continuous_apply i).comp ω₁.continuous)
        ((continuous_apply i).comp ω₂.continuous)
        hEq)
      t

/-- Helper for Theorem 26.8: rational-time restriction measurably embeds path space into a
countable product. -/
private theorem measurableEmbedding_nnratRestriction_euclideanPath (d : ℕ) :
    MeasurableEmbedding
      (fun ω : EuclideanPathSpace d ↦ fun q : ℚ≥0 ↦ ω (q : NNReal)) := by
  have hCont :
      Continuous (fun ω : EuclideanPathSpace d ↦ fun q : ℚ≥0 ↦ ω (q : NNReal)) := by
    refine continuous_pi fun q ↦ ?_
    simpa using (continuous_eval_const (q : NNReal))
  -- Proof comment: continuity together with rational-time injectivity gives the measurable
  -- embedding needed to recover the Borel structure on path space.
  exact hCont.measurableEmbedding nnratRestriction_injective_euclideanPath

/-- Helper for Theorem 26.8: the Borel `σ`-algebra on `EuclideanPathSpace d` is generated by the
rational-time evaluations. -/
private theorem euclideanPathSpace_comap_nnratRestriction_eq_borel (d : ℕ) :
    MeasurableSpace.comap
      (fun ω : EuclideanPathSpace d ↦ fun q : ℚ≥0 ↦ ω (q : NNReal))
      MeasurableSpace.pi =
      borel (EuclideanPathSpace d) := by
  -- Proof comment: rational evaluations already determine a continuous path, so the induced
  -- measurable embedding identifies the Borel structure.
  simpa using (measurableEmbedding_nnratRestriction_euclideanPath d).comap_eq

/-- Helper for Theorem 26.8: a path-valued map is measurable once all rational-time evaluations
are measurable on the source `σ`-algebra. -/
private theorem measurable_euclideanPath_of_rationalEvalFamily
    {Ω' : Type u} [MeasurableSpace Ω']
    {mΩ' : MeasurableSpace Ω'}
    {d : ℕ}
    {Y : Ω' → EuclideanPathSpace d}
    (hY : ∀ q : ℚ≥0, Measurable[mΩ'] (fun ω ↦ Y ω (q : NNReal))) :
    Measurable[mΩ'] Y := by
  refine Measurable.of_comap_le ?_
  change MeasurableSpace.comap Y (borel (EuclideanPathSpace d)) ≤ mΩ'
  rw [← euclideanPathSpace_comap_nnratRestriction_eq_borel d, MeasurableSpace.comap_comp]
  -- Proof comment: after rewriting the path-space Borel structure through rational evaluations,
  -- measurability reduces to the coordinate family supplied by `hY`.
  exact
    (measurable_pi_lambda (fun ω (q : ℚ≥0) ↦ Y ω (q : NNReal)) fun q ↦ hY q).comap_le

/-- Helper for Theorem 26.8: the history `σ`-algebra of a path-valued process up to time `t` is
exactly the pullback of the restriction map to `Set.Iic t`. -/
private theorem generatedFiltrationSpace_eq_pastPathComap
    {ΩW : Type u} [MeasurableSpace ΩW]
    {d : ℕ}
    {Wpath : ΩW → EuclideanPathSpace d}
    (t : NNReal) :
    generatedFiltrationSpace (fun s (ωW : ΩW) ↦ Wpath ωW s) t =
      MeasurableSpace.comap
        (fun ωW (u : Set.Iic t) ↦ Wpath ωW u)
        MeasurableSpace.pi := by
  -- Proof comment: both sigma-algebras are generated by the same deterministic-time evaluations
  -- `ωW ↦ Wpath ωW s` with `s ≤ t`.
  change
      (⨆ j, ⨆ (_ : j ≤ t), MeasurableSpace.comap (fun ωW ↦ Wpath ωW j) inferInstance) =
        MeasurableSpace.comap
          (fun ωW (u : Set.Iic t) ↦ Wpath ωW u)
          MeasurableSpace.pi
  simp_rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
  refine le_antisymm ?_ ?_
  · refine iSup₂_le ?_
    intro j hj
    exact le_iSup_of_le ⟨j, hj⟩ le_rfl
  · refine iSup_le ?_
    intro u
    exact le_iSup_of_le (u : NNReal) <| le_iSup_of_le u.2 le_rfl

/-- Helper for Theorem 26.8: after rewriting the input and output history `σ`-algebras as
restricted-past pullbacks, the operator field `measurable_up_to t` becomes measurability of the
stopped output path against the stopped input path. -/
private theorem measurable_up_to_iff_restrictPastPath
    {Fraw : SDEState n × EuclideanPathSpace m → EuclideanPathSpace n}
    (t : NNReal) :
    Measurable[
      MeasurableSpace.prod inferInstance
        (generatedFiltrationSpace (fun s (ω : EuclideanPathSpace m) ↦ ω s) t),
      generatedFiltrationSpace (fun s (ω : EuclideanPathSpace n) ↦ ω s) t] Fraw ↔
      Measurable[
        MeasurableSpace.prod inferInstance
          (MeasurableSpace.comap
            (fun ω : EuclideanPathSpace m ↦ fun u : Set.Iic t ↦ ω u)
            MeasurableSpace.pi),
        MeasurableSpace.pi]
        (fun xw : SDEState n × EuclideanPathSpace m ↦ fun u : Set.Iic t ↦ Fraw xw u) := by
  have hInputPast :
      generatedFiltrationSpace (fun s (ω : EuclideanPathSpace m) ↦ ω s) t =
        MeasurableSpace.comap
          (fun ω : EuclideanPathSpace m ↦ fun u : Set.Iic t ↦ ω u)
          MeasurableSpace.pi :=
    generatedFiltrationSpace_eq_pastPathComap t
  rw [hInputPast]
  have hOutputPast :
      generatedFiltrationSpace (fun s (ω : EuclideanPathSpace n) ↦ ω s) t =
        MeasurableSpace.comap
          (fun ω : EuclideanPathSpace n ↦ fun u : Set.Iic t ↦ ω u)
          MeasurableSpace.pi :=
    generatedFiltrationSpace_eq_pastPathComap t
  rw [hOutputPast]
  constructor
  · intro h
    -- Proof comment: composing with the codomain restriction map turns the output path into its
    -- stopped past without changing the input history sigma algebra.
    exact
      (comap_measurable (fun ω : EuclideanPathSpace n ↦ fun u : Set.Iic t ↦ ω u)).comp h
  · intro h
    -- Proof comment: conversely, measurability into the pulled-back codomain sigma algebra is
    -- exactly measurability of the stopped output path.
    refine Measurable.of_comap_le ?_
    rw [MeasurableSpace.comap_comp]
    simpa [Function.comp] using h.comap_le

/-- Helper for Theorem 26.8: exact stopped-past factorization already supplies the
nonanticipativity field of a strong-solution operator. -/
private theorem measurableUpTo_of_stoppedPastPathFactors
    (Fraw : SDEState n × EuclideanPathSpace m → EuclideanPathSpace n)
    (hFactor :
      ∀ t : NNReal,
        ∃ Γt : SDEState n × (Set.Iic t → Fin m → ℝ) → (Set.Iic t → SDEState n),
          Measurable Γt ∧
            (fun xw : SDEState n × EuclideanPathSpace m ↦ fun u : Set.Iic t ↦ Fraw xw u) =
              Γt ∘ (fun xw : SDEState n × EuclideanPathSpace m ↦
                (xw.1, fun u : Set.Iic t ↦ xw.2 u))) :
    ∀ t : NNReal,
      Measurable[
        MeasurableSpace.prod inferInstance
          (generatedFiltrationSpace (fun s (ω : EuclideanPathSpace m) ↦ ω s) t),
        generatedFiltrationSpace (fun s (ω : EuclideanPathSpace n) ↦ ω s) t] Fraw := by
  intro t
  rcases hFactor t with ⟨Γt, hΓt_meas, hΓt⟩
  have hRestrict :
      Measurable[
        MeasurableSpace.prod inferInstance
          (MeasurableSpace.comap
            (fun ω : EuclideanPathSpace m ↦ fun u : Set.Iic t ↦ ω u)
            MeasurableSpace.pi),
        MeasurableSpace.prod inferInstance MeasurableSpace.pi]
        (fun xw : SDEState n × EuclideanPathSpace m ↦ (xw.1, fun u : Set.Iic t ↦ xw.2 u)) := by
    -- Proof comment: under the pulled-back input past sigma algebra, restricting the noise path
    -- to `Set.Iic t` is measurable by definition.
    refine measurable_fst.prodMk ?_
    exact
      (comap_measurable (fun ω : EuclideanPathSpace m ↦ fun u : Set.Iic t ↦ ω u)).comp
        measurable_snd
  have hStopped :
      Measurable[
        MeasurableSpace.prod inferInstance
          (MeasurableSpace.comap
            (fun ω : EuclideanPathSpace m ↦ fun u : Set.Iic t ↦ ω u)
            MeasurableSpace.pi),
        MeasurableSpace.pi]
        (fun xw : SDEState n × EuclideanPathSpace m ↦ fun u : Set.Iic t ↦ Fraw xw u) := by
    -- Proof comment: the stopped output path factors measurably through the initial state and
    -- stopped input path by the assumed exact factorization.
    rw [hΓt]
    exact hΓt_meas.comp hRestrict
  -- Proof comment: `measurable_up_to_iff_restrictPastPath` is the normal-form rewrite from the
  -- stopped-path surface back to the operator nonanticipativity field.
  have hRewrite :
      Measurable[
        MeasurableSpace.prod inferInstance
          (generatedFiltrationSpace (fun s (ω : EuclideanPathSpace m) ↦ ω s) t),
        generatedFiltrationSpace (fun s (ω : EuclideanPathSpace n) ↦ ω s) t] Fraw ↔
        Measurable[
          MeasurableSpace.prod inferInstance
            (MeasurableSpace.comap
              (fun ω : EuclideanPathSpace m ↦ fun u : Set.Iic t ↦ ω u)
              MeasurableSpace.pi),
          MeasurableSpace.pi]
          (fun xw : SDEState n × EuclideanPathSpace m ↦ fun u : Set.Iic t ↦ Fraw xw u) :=
    measurable_up_to_iff_restrictPastPath t
  exact hRewrite.2 hStopped

/-- Helper for Theorem 26.8: exact pullback measurability with respect to a pair-valued input map
produces an exact measurable factor through that pair. -/
private theorem existsMeasurableFactor_of_pairComap
    {Ω' : Type u} [MeasurableSpace Ω']
    {α : Type*} [MeasurableSpace α]
    {β : Type*} [MeasurableSpace β]
    {γ : Type*} [MeasurableSpace γ] [Nonempty γ] [StandardBorelSpace γ]
    {f : Ω' → α} {g : Ω' → β} {h : Ω' → γ}
    (hh :
      Measurable[MeasurableSpace.comap (fun ω ↦ (f ω, g ω)) inferInstance] h) :
    ∃ Φ : α × β → γ, Measurable Φ ∧ h = Φ ∘ (fun ω ↦ (f ω, g ω)) := by
  -- Proof comment: this is the exact Doob-Dynkin factorization for the pullback `σ`-algebra
  -- generated by the pair map `ω ↦ (f ω, g ω)`.
  rcases hh.exists_eq_measurable_comp with ⟨Φ, hΦ, hΦeq⟩
  exact ⟨Φ, hΦ, by simpa [Function.comp] using hΦeq⟩

/-- Helper for Theorem 26.8: adaptedness to the natural filtration of the canonical Brownian path
already yields exact full-path and stopped-past factorization through the deterministic-start
input pair. -/
private theorem pathFactorThroughBrownianPath_of_adaptedNatural
    {Ω0 : Type u} [MeasurableSpace Ω0]
    {Wpath : Ω0 → EuclideanPathSpace m}
    {Xpath : Ω0 → EuclideanPathSpace n}
    {x : SDEState n}
    (hAdapt :
      Adapted
        (processFiltration (pathProcess Wpath))
        (pathProcess Xpath)) :
    (∃ Fraw : SDEState n × EuclideanPathSpace m → EuclideanPathSpace n,
      Measurable Fraw ∧
        Xpath = Fraw ∘ (fun ω ↦ (x, Wpath ω))) ∧
      ∀ t : NNReal,
        ∃ Γt : SDEState n × (Set.Iic t → Fin m → ℝ) → (Set.Iic t → SDEState n),
          Measurable Γt ∧
            (fun ω ↦ fun u : Set.Iic t ↦ Xpath ω u) =
              Γt ∘ (fun ω ↦ (x, fun u : Set.Iic t ↦ Wpath ω u)) := by
  let pairMap : Ω0 → SDEState n × EuclideanPathSpace m := fun ω ↦ (x, Wpath ω)
  have hProcessLeFull :
      ∀ q : NNReal,
        processFiltration (pathProcess Wpath) q ≤
          MeasurableSpace.comap pairMap inferInstance := by
    intro q
    have hRestrict :
        Measurable
          (fun xw : SDEState n × EuclideanPathSpace m ↦ fun u : Set.Iic q ↦ xw.2 u) := by
      -- Proof comment: the full input pair measurably restricts to the past noise path on
      -- `[0, q]`.
      exact measurable_pi_lambda _ fun u ↦
        ((continuous_eval_const (u : NNReal)).measurable).comp measurable_snd
    have hPastLe :
        generatedFiltrationSpace (pathProcess Wpath) q ≤
          MeasurableSpace.comap pairMap inferInstance := by
      have hPastEq :
          generatedFiltrationSpace (pathProcess Wpath) q =
            MeasurableSpace.comap
              (fun ω : Ω0 ↦ fun u : Set.Iic q ↦ Wpath ω u)
              MeasurableSpace.pi :=
        generatedFiltrationSpace_eq_pastPathComap q
      rw [hPastEq]
      exact (hRestrict.comp <| comap_measurable pairMap).comap_le
    -- Proof comment: the natural filtration is the ambient measurable space intersected with the
    -- generated past-path sigma algebra, so the generated part is enough here.
    exact le_trans inf_le_right hPastLe
  have hRat :
      ∀ q : ℚ≥0,
        Measurable[MeasurableSpace.comap pairMap inferInstance]
          (fun ω : Ω0 ↦ Xpath ω (q : NNReal)) := by
    intro q
    -- Proof comment: each rational-time state evaluation is adapted and therefore measurable
    -- with respect to the full deterministic-start input pair.
    exact Measurable.mono (hAdapt (q : NNReal)) (hProcessLeFull (q : NNReal)) le_rfl
  have hXpathComap :
      Measurable[MeasurableSpace.comap pairMap inferInstance] Xpath := by
    -- Proof comment: continuity makes the full path measurable once all rational-time
    -- evaluations are measurable for the same pullback sigma algebra.
    exact measurable_euclideanPath_of_rationalEvalFamily hRat
  have hXpathPairComap :
      Measurable[
        MeasurableSpace.comap (fun ω : Ω0 ↦ ((fun _ : Ω0 ↦ x) ω, Wpath ω)) inferInstance] Xpath := by
    simpa [pairMap] using hXpathComap
  rcases existsMeasurableFactor_of_pairComap hXpathPairComap with
    ⟨Fraw, hFraw_meas, hFraw_eq⟩
  refine ⟨⟨Fraw, hFraw_meas, hFraw_eq⟩, ?_⟩
  intro t
  let stoppedPairMap : Ω0 → SDEState n × (Set.Iic t → Fin m → ℝ) :=
    fun ω ↦ (x, fun u : Set.Iic t ↦ Wpath ω u)
  have hProcessLeStopped :
      processFiltration (pathProcess Wpath) t ≤
        MeasurableSpace.comap stoppedPairMap inferInstance := by
    have hRestrict :
        Measurable
          (fun xw : SDEState n × (Set.Iic t → Fin m → ℝ) ↦ xw.2) := measurable_snd
    have hPastLe :
        generatedFiltrationSpace (pathProcess Wpath) t ≤
          MeasurableSpace.comap stoppedPairMap inferInstance := by
      have hPastEq :
          generatedFiltrationSpace (pathProcess Wpath) t =
            MeasurableSpace.comap
              (fun ω : Ω0 ↦ fun u : Set.Iic t ↦ Wpath ω u)
              MeasurableSpace.pi :=
        generatedFiltrationSpace_eq_pastPathComap t
      rw [hPastEq]
      exact (hRestrict.comp <| comap_measurable stoppedPairMap).comap_le
    -- Proof comment: at the horizon `t`, the stopped deterministic-start input pair already sees
    -- the whole natural filtration generated by the Brownian past up to `t`.
    exact le_trans inf_le_right hPastLe
  have hEvalFactors :
      ∀ u : Set.Iic t,
        ∃ φu : SDEState n × (Set.Iic t → Fin m → ℝ) → SDEState n,
          Measurable φu ∧
            (fun ω : Ω0 ↦ Xpath ω u) = φu ∘ stoppedPairMap := by
    intro u
    have hXu :
        Measurable[MeasurableSpace.comap stoppedPairMap inferInstance]
          (fun ω : Ω0 ↦ Xpath ω u) := by
      -- Proof comment: each stopped-time state evaluation is measurable from the same stopped
      -- Brownian input because adaptedness is monotone in the deterministic horizon.
      exact
        Measurable.mono
          (hAdapt (u : NNReal))
          (le_trans ((processFiltration (pathProcess Wpath)).mono u.2) hProcessLeStopped)
          le_rfl
    have hXuPairComap :
        Measurable[
          MeasurableSpace.comap
            (fun ω : Ω0 ↦
              ((fun _ : Ω0 ↦ x) ω, fun v : Set.Iic t ↦ Wpath ω v))
            inferInstance]
          (fun ω : Ω0 ↦ Xpath ω u) := by
      simpa [stoppedPairMap] using hXu
    exact existsMeasurableFactor_of_pairComap hXuPairComap
  classical
  choose φ hφ_meas hφ_eq using hEvalFactors
  let Γt : SDEState n × (Set.Iic t → Fin m → ℝ) → (Set.Iic t → SDEState n) :=
    fun xw u ↦ φ u xw
  have hΓt_meas : Measurable Γt := by
    -- Proof comment: the stopped output path is measurable exactly because every stopped-time
    -- coordinate factor is measurable.
    exact measurable_pi_lambda _ fun u ↦ hφ_meas u
  refine ⟨Γt, hΓt_meas, ?_⟩
  funext ω
  ext u i
  -- Proof comment: evaluating the assembled stopped path at `u` recovers the corresponding
  -- coordinate factor supplied by Doob-Dynkin.
  simpa [Γt, stoppedPairMap, Function.comp] using congrFun (congrFun (hφ_eq u) ω) i

/-- Helper for Theorem 26.8: a path-valued lift that is adapted to `ℱ` is automatically
measurable into the generated path filtration up to each deterministic horizon. -/
private theorem pathLift_measurable_toGeneratedFiltration
    {Ω : Type u} [MeasurableSpace Ω]
    {ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {Wpath : Ω → EuclideanPathSpace m}
    (hWpath : Adapted ℱ (pathProcess Wpath)) (t : NNReal) :
    Measurable[
      ℱ t,
      generatedFiltrationSpace (fun s (ω : EuclideanPathSpace m) ↦ ω s) t] Wpath := by
  -- Proof comment: the path filtration is generated by deterministic-time evaluations, and
  -- adaptedness supplies those evaluations on every earlier slice `s ≤ t`.
  refine Measurable.of_comap_le ?_
  simp_rw [generatedFiltrationSpace, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp,
    Function.comp_def]
  refine iSup₂_le fun s hs ↦ ?_
  exact (Measurable.mono (hWpath s) (ℱ.mono hs) le_rfl).comap_le

/-- Helper for Theorem 26.8: the stopping-time predicate is monotone under filtration inclusion.
This is the exact transfer step needed to move stopping times from the solved-state filtration back
to the Brownian-driver filtration. -/
private theorem isStoppingTime_of_filtration_le
    {Ω : Type u} [MeasurableSpace Ω]
    {ℱ 𝒢 : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    (hle : ℱ ≤ 𝒢) {τ : Ω → WithTop NNReal}
    (hτ : IsStoppingTime ℱ τ) :
    IsStoppingTime 𝒢 τ := by
  -- Proof comment: every time-slice event already measurable for `ℱ` stays measurable for the
  -- larger filtration `𝒢`.
  intro t
  exact hle t _ (hτ t)

/-- Helper for Theorem 26.8: a constant random initial state has Dirac law at its value on every
probability space. -/
private theorem hasLaw_const_dirac_forProbability
    {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (x : SDEState n) :
    HasLaw (fun _ : Ω ↦ x) (Measure.dirac x) P := by
  -- Proof comment: pushing a probability measure forward through a constant map yields the
  -- corresponding Dirac measure.
  refine ⟨measurable_const.aemeasurable, ?_⟩
  simpa using (Measure.map_const P x)

/-- Helper for Theorem 26.8: a random initial state with Dirac law at `x` is almost surely equal
to the constant state `x`. -/
private theorem ae_eq_const_of_hasLaw_dirac
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {ξ : Ω → SDEState n} {x : SDEState n}
    (hξ : HasLaw ξ (Measure.dirac x) P) :
    ξ =ᵐ[P] fun _ ↦ x := by
  change ∀ᵐ ω ∂P, ξ ω = x
  -- Proof comment: the singleton event `{x}` has full `δ_x`-mass, and `HasLaw.ae_iff` transfers
  -- that full-measure statement back to the original space.
  exact
    (hξ.ae_iff (by
      fun_prop : Measurable fun y : SDEState n ↦ y = x)).2 (by simp)

/-- Helper for Theorem 26.8: realizing a strong-solution operator preserves almost-sure equality
of the initial state when the driving path is fixed. -/
private theorem StrongSolutionOperator.realization_congr_left_ae
    (F : StrongSolutionOperator n m)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {ξ ξ' : Ω → SDEState n} {Wpath : Ω → EuclideanPathSpace m}
    (hξ : ξ =ᵐ[P] ξ') :
    F.realization ξ Wpath =ᵐ[P] F.realization ξ' Wpath := by
  -- Proof comment: realization is pointwise application of the same operator to the same path,
  -- so only the initial-state input changes.
  filter_upwards [hξ] with ω hω
  simp [StrongSolutionOperator.realization, hω]

/-- Helper for Theorem 26.8: realizing a strong-solution operator preserves almost-sure equality
of the driving path when the initial state is fixed. -/
private theorem StrongSolutionOperator.realization_congr_right_ae
    (F : StrongSolutionOperator n m)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {ξ : Ω → SDEState n} {Wpath Wpath' : Ω → EuclideanPathSpace m}
    (hW : Wpath =ᵐ[P] Wpath') :
    F.realization ξ Wpath =ᵐ[P] F.realization ξ Wpath' := by
  -- Proof comment: realization is again pointwise application of the same operator, and now
  -- only the driving path varies almost surely.
  filter_upwards [hW] with ω hω
  simp [StrongSolutionOperator.realization, hω]

/-- Helper for Theorem 26.8: if the initial state has Dirac law at `x`, then the realized
strong-solution path is almost surely the same as the realization from the constant initial
state `x`. -/
private theorem strongSolutionOperatorRealization_ae_eq_const_of_hasLaw_dirac
    (F : StrongSolutionOperator n m)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {ξ : Ω → SDEState n} {Wpath : Ω → EuclideanPathSpace m} {x : SDEState n}
    (hLaw : HasLaw ξ (Measure.dirac x) P) :
    F.realization ξ Wpath =ᵐ[P]
      F.realization (fun _ : Ω ↦ x) Wpath := by
  -- Proof comment: a Dirac initial law forces the initial state to be almost surely constant,
  -- and realization respects almost-sure equality in its initial-state slot.
  exact
    StrongSolutionOperator.realization_congr_left_ae F
      (ae_eq_const_of_hasLaw_dirac hLaw)

/-- Helper for Theorem 26.8: once a Dirac-law strong-solution operator is available, the Chapter
26 owner `HasUniqueStrongSolution` is only its existential packaging. -/
private theorem hasUniqueStrongSolution_dirac_of_operator
    {x : SDEState n}
    (F : StrongSolutionOperator n m)
    (hSolves :
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
        (ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω))
        (ξ : Ω → SDEState n) (W : Ω → EuclideanPathSpace m),
        GeneralizedSDEBrownianMotion P ℱ W →
        Measurable[ℱ 0] ξ →
        IndepFun ξ W P →
        HasLaw ξ (Measure.dirac x) P →
        SolvesStrongGeneralizedSDE σ b P ℱ ξ W (F.realization ξ W))
    (hUnique :
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
        (ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω))
        (ξ : Ω → SDEState n) (W : Ω → EuclideanPathSpace m)
        (X : Ω → EuclideanPathSpace n),
        GeneralizedSDEBrownianMotion P ℱ W →
        Measurable[ℱ 0] ξ →
        IndepFun ξ W P →
        HasLaw ξ (Measure.dirac x) P →
        SolvesStrongGeneralizedSDE σ b P ℱ ξ W X →
        X = F.realization ξ W) :
    HasUniqueStrongSolution
      GeneralizedSDEBrownianMotion
      (SolvesStrongGeneralizedSDE σ b)
      (Measure.dirac x) := by
  -- Proof comment: after isolating the operator and its global solve-and-uniqueness clauses, the
  -- `HasUniqueStrongSolution` owner is just Definition 26.4 written out.
  refine ⟨F, ?_⟩
  constructor
  · intro Ω _ P ℱ ξ W hW hξ hIndep hLaw
    -- Proof comment: the first half of the operator witness is exactly the global solve clause.
    exact hSolves P ℱ ξ W hW hξ hIndep hLaw
  · intro Ω _ P ℱ ξ W X hW hξ hIndep hLaw hX
    -- Proof comment: the second half of the operator witness is the exact pathwise uniqueness
    -- clause.
    exact hUnique P ℱ ξ W X hW hξ hIndep hLaw hX

/-- Helper for Theorem 26.8: once the Dirac-law owner is available, specializing it to the
canonical Brownian witness gives the fixed-space deterministic-start realization promised in part
(1). -/
private theorem diracStrongOwner_of_hasUniqueStrongSolution
    {x : SDEState n}
    (hStrong :
      HasUniqueStrongSolution
        GeneralizedSDEBrownianMotion
        (SolvesStrongGeneralizedSDE σ b)
        (Measure.dirac x)) :
    ∃ (Ω : Type), ∃ _ : MeasurableSpace Ω,
      ∃ ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω),
      ∃ P : ProbabilityMeasure Ω,
      ∃ W : Ω → EuclideanPathSpace m,
      ∃ X : Ω → EuclideanPathSpace n,
        StrongSolution n m
          (fun ξ W' X' ↦ SolvesStrongGeneralizedSDE σ b (P : Measure Ω) ℱ ξ W' X')
          (fun _ ↦ x)
          W
          X ∧
      ∀ X' : Ω → EuclideanPathSpace n,
          SolvesStrongGeneralizedSDE σ b (P : Measure Ω) ℱ (fun _ ↦ x) W X' →
          X' =ᵐ[(P : Measure Ω)] X := by
  rcases hStrong with ⟨F, hF⟩
  rcases (@existsStandardBrownianPathWitness m) with
    ⟨Ω0, mΩ0, μ0, Wpath, hWpath⟩
  let ℱ0 := processFiltration (pathProcess Wpath)
  let Xpath : Ω0 → EuclideanPathSpace n := F.realization (fun _ : Ω0 ↦ x) Wpath
  have hBrownianPath :
      GeneralizedSDEBrownianMotion (μ0 : Measure Ω0) ℱ0 Wpath := by
    -- Proof comment: `existsStandardBrownianPathWitness` already gives the canonical path-valued
    -- Brownian motion on its own natural filtration.
    exact ⟨inferInstance, hWpath⟩
  have hConstLaw :
      HasLaw (fun _ : Ω0 ↦ x) (Measure.dirac x) (μ0 : Measure Ω0) :=
    hasLaw_const_dirac_forProbability (μ0 : Measure Ω0) x
  have hSolves :
      SolvesStrongGeneralizedSDE σ b (μ0 : Measure Ω0) ℱ0
        (fun _ : Ω0 ↦ x) Wpath Xpath := by
    -- Proof comment: specialize the global Dirac-law owner to the canonical Brownian witness and
    -- the constant initial state `x`.
    exact
      hF.1
        (μ0 : Measure Ω0)
        ℱ0
        (fun _ : Ω0 ↦ x)
        Wpath
        hBrownianPath
        measurable_const
        (indepFun_const_left x Wpath)
        hConstLaw
  refine ⟨Ω0, mΩ0, ℱ0, μ0, Wpath, Xpath, ?_, ?_⟩
  · -- Proof comment: the fixed-space realization is exactly the canonical operator realization on
    -- the witness Brownian path.
    exact ⟨F, rfl, hSolves⟩
  · intro X' hX'
    have hEq :
        X' = F.realization (fun _ : Ω0 ↦ x) Wpath := by
      -- Proof comment: uniqueness from the global Dirac-law owner specializes to this witness
      -- space verbatim.
      exact
        hF.2
          (μ0 : Measure Ω0)
          ℱ0
          (fun _ : Ω0 ↦ x)
          Wpath
          X'
          hBrownianPath
          measurable_const
          (indepFun_const_left x Wpath)
          hConstLaw
          hX'
    simpa [Xpath] using hEq

/-- Helper for Theorem 26.8: on the canonical Brownian witness, the Picard scheme should produce
one exact path-valued solution started from the deterministic point `x`. -/
private theorem canonicalPicardLimit_solves
    {K : ℝ}
    {Ω0 : Type u} [MeasurableSpace Ω0]
    (μ0 : ProbabilityMeasure Ω0)
    (Wpath : Ω0 → EuclideanPathSpace m)
    (hWpath :
      IsBrownianMotionWithFiltration
        (processFiltration (pathProcess Wpath))
        (μ0 : Measure Ω0)
        (pathProcess Wpath))
    (hbσ_timeMeasurable : SDETimeMeasurable b σ)
    (hK_pos : 0 < K)
    (hbσ_lipschitz : SDESpaceLipschitzWith K b σ)
    (hbσ_growth : SDELinearGrowthWith K b σ)
    (x : SDEState n) :
    ∃ Xpath : Ω0 → EuclideanPathSpace n,
      SolvesStrongGeneralizedSDE
        σ
        b
        (μ0 : Measure Ω0)
        (processFiltration (pathProcess Wpath))
        (fun _ : Ω0 ↦ x)
        Wpath
        Xpath ∧
      Adapted (processFiltration (pathProcess Wpath)) (pathProcess Xpath) := by
  -- Route correction: the actual missing existence step is the deterministic-start Picard limit
  -- on one fixed Brownian witness, not a global Dirac-law owner theorem.
  -- TODO: construct the Picard iterates on `(Ω0, μ0, Wpath)`, prove the finite-horizon `L²`
  -- bounds from the Lipschitz and linear-growth hypotheses, and pass to the exact path-valued
  -- limit solving the generalized SDE together with the adaptedness it naturally carries.
  sorry

/-- Helper for Theorem 26.8: once the deterministic-start path-valued solution is built on the
canonical Brownian witness, it should factor through the Brownian path into a strong-solution
operator. -/
private theorem adaptedDiracSolution_factorizes_throughBrownianPath
    {Ω0 : Type u} [MeasurableSpace Ω0]
    (μ0 : ProbabilityMeasure Ω0)
    {Wpath : Ω0 → EuclideanPathSpace m}
    {Xpath : Ω0 → EuclideanPathSpace n}
    {x : SDEState n}
    (hSolves :
      SolvesStrongGeneralizedSDE
        σ
        b
        (μ0 : Measure Ω0)
        (processFiltration (pathProcess Wpath))
        (fun _ : Ω0 ↦ x)
        Wpath
        Xpath)
    (hAdapt :
      Adapted
        (processFiltration (pathProcess Wpath))
        (pathProcess Xpath)) :
    StrongSolution n m
      (fun ξ W' X' ↦
        SolvesStrongGeneralizedSDE
          σ
          b
          (μ0 : Measure Ω0)
          (processFiltration (pathProcess Wpath))
          ξ
          W'
          X')
      (fun _ : Ω0 ↦ x)
      Wpath
      Xpath := by
  have hFactorization :
      (∃ Fraw : SDEState n × EuclideanPathSpace m → EuclideanPathSpace n,
        Measurable Fraw ∧
          Xpath = Fraw ∘ (fun ω ↦ (x, Wpath ω))) ∧
        ∀ t : NNReal,
          ∃ Γt : SDEState n × (Set.Iic t → Fin m → ℝ) → (Set.Iic t → SDEState n),
            Measurable Γt ∧
              (fun ω ↦ fun u : Set.Iic t ↦ Xpath ω u) =
                Γt ∘ (fun ω ↦ (x, fun u : Set.Iic t ↦ Wpath ω u)) :=
    pathFactorThroughBrownianPath_of_adaptedNatural hAdapt
  rcases hFactorization with
    ⟨⟨Fraw, hFraw_meas, hFraw_eq⟩, hStoppedFactors⟩
  -- Route correction: the witness-space factorization is now established. The remaining gap is
  -- to upgrade the stopped-past factors along the actual canonical input pair to an operator-level
  -- nonanticipativity proof for `Fraw` on arbitrary inputs, so that it can be packaged as a
  -- `StrongSolutionOperator`.
  -- TODO: replace the witness-space factors `hStoppedFactors` by a domain-level factorization
  -- `∀ t, ∃ Γt, (fun xw ↦ fun u ↦ Fraw xw u) = Γt ∘ (fun xw ↦ (xw.1, fun u ↦ xw.2 u))`.
  -- Once that bridge is added, `refine ⟨⟨Fraw, ?_⟩, hFraw_eq, hSolves⟩` closes the theorem via
  -- `measurableUpTo_of_stoppedPastPathFactors`.
  sorry

/-- Helper for Theorem 26.8: two deterministic-start solutions driven by the same Brownian path
agree almost surely under the Lipschitz hypothesis. -/
private theorem solutionsEqual_ae_of_lipschitz_sameDriver_sameConstStart
    {K : ℝ}
    {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω}
    {ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {Wpath : Ω → EuclideanPathSpace m}
    {X X' : Ω → EuclideanPathSpace n}
    (hbσ_lipschitz : SDESpaceLipschitzWith K b σ)
    {x : SDEState n}
    (hX :
      SolvesStrongGeneralizedSDE σ b P ℱ (fun _ : Ω ↦ x) Wpath X)
    (hX' :
      SolvesStrongGeneralizedSDE σ b P ℱ (fun _ : Ω ↦ x) Wpath X') :
    X =ᵐ[P] X' := by
  -- Route correction: the uniqueness frontier is the standard same-driver second-moment estimate,
  -- not the stronger global owner packaging.
  -- TODO: apply Lemma 26.7 to the difference process, use the Lipschitz bound to derive the
  -- Volterra inequality for `E[‖X_t - X'_t‖²]`, and close with
  -- `zero_of_selfIntervalIntegralBound`.
  sorry

/-- Internal bridge packaging a deterministic-start strong solution together with almost-sure
pathwise uniqueness on the same filtered space under the measurable coefficient hypotheses used
internally in Chapter 26. -/
private theorem diracStrongOwner_of_lipschitz_linearGrowth
    {K : ℝ}
    (hbσ_timeMeasurable : SDETimeMeasurable b σ)
    (hK_pos : 0 < K)
    (hbσ_lipschitz : SDESpaceLipschitzWith K b σ)
    (hbσ_growth : SDELinearGrowthWith K b σ) (x : SDEState n) :
    ∃ (Ω : Type), ∃ _ : MeasurableSpace Ω,
      ∃ ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω),
      ∃ P : ProbabilityMeasure Ω,
      ∃ W : Ω → EuclideanPathSpace m,
      ∃ X : Ω → EuclideanPathSpace n,
        StrongSolution n m
          (fun ξ W' X' ↦ SolvesStrongGeneralizedSDE σ b (P : Measure Ω) ℱ ξ W' X')
          (fun _ ↦ x)
          W
          X ∧
      ∀ X' : Ω → EuclideanPathSpace n,
          SolvesStrongGeneralizedSDE σ b (P : Measure Ω) ℱ (fun _ ↦ x) W X' →
          X' =ᵐ[(P : Measure Ω)] X := by
  rcases (@existsStandardBrownianPathWitness m) with
    ⟨Ω0, mΩ0, μ0, Wpath, hWpath⟩
  let ℱ0 := processFiltration (pathProcess Wpath)
  rcases
      canonicalPicardLimit_solves
        (b := b)
        (σ := σ)
        μ0
        Wpath
        hWpath
        hbσ_timeMeasurable
        hK_pos
        hbσ_lipschitz
        hbσ_growth
        x with
    ⟨Xpath, hSolves, hAdapt⟩
  have hStrong :
      StrongSolution n m
        (fun ξ W' X' ↦
          SolvesStrongGeneralizedSDE σ b (μ0 : Measure Ω0) ℱ0 ξ W' X')
        (fun _ : Ω0 ↦ x)
        Wpath
        Xpath := by
    -- Proof comment: once the deterministic-start canonical Picard limit is available on the
    -- Brownian witness space, the earlier factorization bridge packages it as a strong solution.
    exact
      adaptedDiracSolution_factorizes_throughBrownianPath
        (b := b)
        (σ := σ)
        μ0
        hSolves
        hAdapt
  refine ⟨Ω0, mΩ0, ℱ0, μ0, Wpath, Xpath, hStrong, ?_⟩
  intro X' hX'
  -- Proof comment: same-driver deterministic-start uniqueness is exactly the local Lipschitz
  -- uniqueness theorem specialized to the canonical Brownian witness space.
  exact
    solutionsEqual_ae_of_lipschitz_sameDriver_sameConstStart
      (b := b)
      (σ := σ)
      (P := (μ0 : Measure Ω0))
      (ℱ := ℱ0)
      (Wpath := Wpath)
      (X := Xpath)
      (X' := X')
      (x := x)
      hbσ_lipschitz
      hSolves
      hX' |>.symm

/-- Helper for Theorem 26.8: a strong-solution operator realization is adapted once the initial
datum is measurable at time `0` and the path-valued driver is adapted. -/
private theorem StrongSolutionOperator.adaptedPathProcessRealization
    (F : StrongSolutionOperator n m)
    {Ω : Type u} [MeasurableSpace Ω]
    {ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {ξ : Ω → SDEState n} {Wpath : Ω → EuclideanPathSpace m}
    (hξ : Measurable[ℱ 0] ξ)
    (hWpath : Adapted ℱ (pathProcess Wpath)) :
    Adapted ℱ (fun t ω ↦ F.realization ξ Wpath ω t) := by
  intro t
  have hInput :
      Measurable[
        ℱ t,
        MeasurableSpace.prod inferInstance
          (generatedFiltrationSpace (fun s (ω : EuclideanPathSpace m) ↦ ω s) t)
      ] fun ω : Ω ↦ (ξ ω, Wpath ω) := by
    have hξt : Measurable[ℱ t] ξ :=
      Measurable.mono hξ (ℱ.mono (show (0 : NNReal) ≤ t from zero_le t)) le_rfl
    have hWpatht :
        Measurable[
          ℱ t,
          generatedFiltrationSpace (fun s (ω : EuclideanPathSpace m) ↦ ω s) t
        ] Wpath := by
      -- Proof comment: this is exactly the generic path-lift measurability bridge proved above.
      exact pathLift_measurable_toGeneratedFiltration hWpath t
    -- Proof comment: the initial datum is visible at time `0`, while the driver is visible up to
    -- time `t`.
    exact Measurable.prodMk hξt hWpatht
  have hRealization :
      Measurable[
        ℱ t,
        generatedFiltrationSpace (fun s (ω : EuclideanPathSpace n) ↦ ω s) t
      ] fun ω : Ω ↦ F.realization ξ Wpath ω := by
    -- Proof comment: nonanticipativity of `F` is encoded by its `measurable_up_to` field.
    simpa [StrongSolutionOperator.realization] using (F.measurable_up_to t).comp hInput
  have hEval :
      Measurable[
        generatedFiltrationSpace (fun s (ω : EuclideanPathSpace n) ↦ ω s) t
      ] fun ω : EuclideanPathSpace n ↦ ω t := by
    -- Proof comment: deterministic-time evaluation is one of the generators of the path
    -- filtration.
    exact Measurable.of_comap_le <| le_iSup_of_le t <| le_iSup_of_le le_rfl le_rfl
  exact hEval.comp hRealization

/-- Helper for Theorem 26.8: an exact path-valued strong solution packages directly as a
process-valued pathwise strong-solution realization. -/
private theorem hasPathwiseStrongSolutionRealization_of_strongSolution
    {Ω : Type u} [MeasurableSpace Ω]
    {ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    (P : ProbabilityMeasure Ω)
    (x : SDEState n)
    {Wpath : Ω → EuclideanPathSpace m} {Xpath : Ω → EuclideanPathSpace n}
    (hStrong :
      StrongSolution n m
        (fun ξ W' X' ↦ SolvesStrongGeneralizedSDE σ b (P : Measure Ω) ℱ ξ W' X')
        (fun _ ↦ x)
        Wpath
        Xpath) :
    HasPathwiseStrongSolutionRealization
      (IsBrownianMotionWithFiltration ℱ (P : Measure Ω))
      (fun ξ W X ↦ IsGeneralizedNDimensionalDiffusion ℱ (P : Measure Ω) ξ W σ b X)
      ℱ
      (fun _ ↦ x)
      (pathProcess Wpath)
      (pathProcess Xpath) := by
  rcases hStrong with ⟨F, hRealization, hSolves⟩
  rcases hSolves with ⟨_, hDiffusion⟩
  refine ⟨?_, Wpath, rfl, Xpath, rfl, ?_⟩
  · rcases hDiffusion with ⟨hBrownian, N, hIto, hbProg, hbInt, hStateEq⟩
    refine ⟨?_, ?_, hBrownian, ?_⟩
    · intro i
      have hXpathAdapted : Adapted ℱ (fun t ω ↦ Xpath ω t) := by
        -- Proof comment: the exact realization identity lets the operator measurability control
        -- the solved path itself.
        simpa [hRealization] using
          StrongSolutionOperator.adaptedPathProcessRealization
            F
            measurable_const
            hBrownian.2
      have hCoordAdapted : Adapted ℱ (fun t ω ↦ Xpath ω t i) := by
        intro t
        exact (measurable_pi_apply i).comp (hXpathAdapted t)
      -- Proof comment: continuous adapted coordinate processes are progressively measurable.
      exact
        (Adapted.stronglyAdapted hCoordAdapted).progMeasurable_of_continuous
          (fun ω ↦ (continuous_apply i).comp (Xpath ω).continuous)
    · intro i ω
      -- Proof comment: coordinate continuity is inherited from the ambient path continuity.
      exact (continuous_apply i).comp (Xpath ω).continuous
    · -- Proof comment: the strong-solution clause already carries the generalized diffusion
      -- equation in process form once the path lifts are evaluated.
      exact ⟨hBrownian, N, hIto, hbProg, hbInt, hStateEq⟩
  · -- Proof comment: keep the same strong-solution operator witness and only rewrite the ambient
    -- solution relation from path variables to their process evaluations.
    exact ⟨F, hRealization, hDiffusion⟩

/-- Helper for Theorem 26.8: an exact operator realization makes the solved-state history
measurable with respect to the driver history, so the state filtration is contained in the driver
filtration. -/
private theorem processFiltration_le_of_exactPathwiseRealization
    {Ω : Type u} [MeasurableSpace Ω]
    {Wpath : Ω → EuclideanPathSpace m}
    {Xpath : Ω → EuclideanPathSpace n}
    {F : StrongSolutionOperator n m}
    {x : SDEState n}
    (hRealization : Xpath = F.realization (fun _ : Ω ↦ x) Wpath)
    (hWpathTop :
      Adapted
        (⊤ : Filtration NNReal (inferInstance : MeasurableSpace Ω))
        (pathProcess Wpath)) :
    processFiltration (pathProcess Xpath) ≤ processFiltration (pathProcess Wpath) := by
  have hWpathAdapted : Adapted (processFiltration (pathProcess Wpath)) (pathProcess Wpath) := by
    intro t
    refine measurable_iff_comap_le.2 ?_
    exact le_inf (measurable_iff_comap_le.1 (hWpathTop t)) <| by
      refine le_iSup_of_le t ?_
      refine le_iSup_of_le le_rfl ?_
      exact le_rfl
  have hXpathAdapted : Adapted (processFiltration (pathProcess Wpath)) (pathProcess Xpath) := by
    -- Proof comment: once the driver is adapted to its own process filtration, nonanticipativity
    -- of the operator transfers that adaptedness to the solved path.
    simpa [hRealization] using
      StrongSolutionOperator.adaptedPathProcessRealization
        F
        measurable_const
        hWpathAdapted
  intro t
  refine
    (show
      processFiltration (pathProcess Xpath) t ≤ generatedFiltrationSpace (pathProcess Xpath) t
      from inf_le_right).trans ?_
  rw [generatedFiltrationSpace]
  refine iSup₂_le fun s hs ↦ ?_
  exact
    Measurable.comap_le <|
      Measurable.mono (hXpathAdapted s) ((processFiltration (pathProcess Wpath)).mono hs) le_rfl

/-- Helper for Theorem 26.8: exact path lifts let us rewrite stopped-future paths without
changing the underlying process. -/
private theorem futurePathAfterStoppingTime_congr_of_exactStateLift
    {Ω : Type u} [MeasurableSpace Ω]
    {X : NNReal → Ω → SDEState n}
    {Xpath : Ω → EuclideanPathSpace n}
    (hXpath : X = fun t ω ↦ Xpath ω t)
    (τ : Ω → WithTop NNReal) :
    futurePathAfterStoppingTime X τ =
      futurePathAfterStoppingTime (fun t ω ↦ Xpath ω t) τ := by
  -- Proof comment: the stopped-future path depends only on the state process itself, so an exact
  -- path lift only changes the spelling of that process.
  simp [hXpath]

/-- Helper for Theorem 26.8: exact path lifts also rewrite the stopped state value into the
path-valued spelling. -/
private theorem stoppedValue_congr_of_exactStateLift
    {Ω : Type u} [MeasurableSpace Ω]
    {X : NNReal → Ω → SDEState n}
    {Xpath : Ω → EuclideanPathSpace n}
    (hXpath : X = fun t ω ↦ Xpath ω t)
    (τ : Ω → WithTop NNReal) :
    stoppedValue X τ =
      stoppedValue (fun t ω ↦ Xpath ω t) τ := by
  -- Proof comment: `stoppedValue` is functorial under the same exact process identification.
  simp [hXpath]

/-- Helper for Theorem 26.8: translating a continuous state path by a deterministic time still
yields a continuous path. -/
private theorem continuous_shiftedStatePath
    (s : NNReal) (path : EuclideanPathSpace n) :
    Continuous fun t : NNReal ↦ path (s + t) := by
  -- Proof comment: composition with deterministic time translation preserves continuity.
  exact path.continuous.comp (continuous_const.add continuous_id)

/-- Helper for Theorem 26.8: the finite-row future of a continuous state path is again a
continuous path. -/
private def shiftedStatePath
    (s : NNReal) (path : EuclideanPathSpace n) :
    EuclideanPathSpace n :=
  ⟨fun t ↦ path (s + t), continuous_shiftedStatePath s path⟩

/-- Helper for Theorem 26.8: on every finite row, `untopD 0` agrees with the proof-dependent
`untop` spelling of the same `WithTop NNReal` value. -/
private theorem untopD_eq_untop_of_ne_top
    {s : WithTop NNReal} (hs : s ≠ ⊤) :
    s.untopD 0 = s.untop hs := by
  rcases WithTop.ne_top_iff_exists.mp hs with ⟨s0, rfl⟩
  rfl

/-- Helper for Theorem 26.8: on finite stopping-time rows, the raw future path is exactly the
corresponding deterministically shifted continuous path. -/
private theorem futurePathAfterStoppingTime_eq_shiftedStatePath
    {Ω : Type u} [MeasurableSpace Ω]
    {Xpath : Ω → EuclideanPathSpace n}
    {τ : Ω → WithTop NNReal} {ω : Ω}
    (hτω : τ ω ≠ ⊤) :
    futurePathAfterStoppingTime (fun t ω' ↦ Xpath ω' t) τ ω =
      ((shiftedStatePath ((τ ω).untop hτω) (Xpath ω) : EuclideanPathSpace n) :
        NNReal → SDEState n) := by
  funext t
  -- Proof comment: away from the exceptional `⊤` row, the stopped-future path is just the
  -- original continuous path evaluated at the shifted time `τ + t`.
  simpa [shiftedStatePath] using
    futurePathAfterStoppingTime_apply_of_ne_top
      (fun t ω' ↦ Xpath ω' t)
      τ
      ω
      t
      hτω

/-- Helper for Theorem 26.8: a deterministic time shift preserves the measurable, Lipschitz, and
linear-growth coefficient conditions. This is the coefficient-side normalization needed before
comparing restarted paths with a shifted solver. -/
private theorem shiftedCoefficientConditions
    {K : ℝ}
    (s : NNReal)
    (hbσ_timeMeasurable : SDETimeMeasurable b σ)
    (hbσ_lipschitz : SDESpaceLipschitzWith K b σ)
    (hbσ_growth : SDELinearGrowthWith K b σ) :
    SDETimeMeasurable
      (fun t x ↦ b (s + t) x)
      (fun t x ↦ σ (s + t) x) ∧
    SDESpaceLipschitzWith K
      (fun t x ↦ b (s + t) x)
      (fun t x ↦ σ (s + t) x) ∧
    SDELinearGrowthWith K
      (fun t x ↦ b (s + t) x)
      (fun t x ↦ σ (s + t) x) := by
  rcases hbσ_timeMeasurable with ⟨hb_meas, hσ_meas⟩
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro x
      -- Proof comment: the drift time section stays measurable after precomposing with the
      -- deterministic translation `t ↦ s + t`.
      exact (hb_meas x).comp (measurable_const.add measurable_id)
    · intro x
      -- Proof comment: the same deterministic time shift preserves measurability of the
      -- diffusion time section.
      exact (hσ_meas x).comp (measurable_const.add measurable_id)
  · intro x x' t
    -- Proof comment: the spatial Lipschitz estimate is uniform in time, so it survives the
    -- deterministic shift unchanged.
    simpa using hbσ_lipschitz x x' (s + t)
  · intro x t
    -- Proof comment: the linear-growth bound is likewise uniform in time and therefore invariant
    -- under the same shift.
    simpa using hbσ_growth x (s + t)

/-- Helper for Theorem 26.8: after inflating the coefficient constant to a positive bound, all
usable coefficient-side assumptions sit in one bundled normal form. This is the exact hypothesis
package needed by the deterministic-start Picard construction already present in the file. -/
private theorem positiveInflatedCoefficientConditions
    {K : ℝ}
    (hbσ_timeMeasurable : SDETimeMeasurable b σ)
    (hbσ_lipschitz : SDESpaceLipschitzWith K b σ)
    (hbσ_growth : SDELinearGrowthWith K b σ)
    :
    ∃ K' : ℝ,
      0 < K' ∧
        SDETimeMeasurable b σ ∧
        SDESpaceLipschitzWith K' b σ ∧
        SDELinearGrowthWith K' b σ := by
  rcases
      inflateLipschitzLinearGrowthBound
        (b := b)
        (σ := σ)
        hbσ_lipschitz
        hbσ_growth with
    ⟨hLip', hGrow'⟩
  refine ⟨max |K| 1, ?_, hbσ_timeMeasurable, hLip', hGrow'⟩
  -- Proof comment: inflating by `max |K| 1` forces a strictly positive constant without changing
  -- the time-measurability assumption.
  exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)

/-- Theorem 26.8: if `b` and `σ` are globally Lipschitz in the spatial variable and satisfy the
linear-growth condition, then every deterministic initial point `x ∈ ℝ^n` admits a unique strong
solution of the generalized SDE in the canonical deterministic-start owner sense. The realized
Markov and strong-Markov consequences are recorded below as companion bridge theorems. -/
theorem hasUniqueStrongSolution_of_lipschitz_linearGrowth
    {K : ℝ}
    (hbσ_lipschitz : SDESpaceLipschitzWith K b σ)
    (hbσ_growth : SDELinearGrowthWith K b σ) (x : SDEState n) :
    HasUniqueStrongSolution
      GeneralizedSDEBrownianMotion
      (SolvesStrongGeneralizedSDE σ b)
      (Measure.dirac x) := by
  -- Route correction: the local packaging layer is no longer the blocker.
  -- TODO: the statement currently omits the coefficient time-measurability premise needed by the
  -- existing deterministic-start existence bridge; `positiveInflatedCoefficientConditions`
  -- isolates the usable measurable-hypothesis package, but the public theorem still lacks that
  -- premise in its header.
  sorry

/-- Companion to Theorem 26.8: under the same Lipschitz and linear-growth hypotheses, every
deterministic-start pathwise strong realization of the solution is a Markov process. -/
theorem markovRealization_of_lipschitz_linearGrowth
    {K : ℝ} {Ω : Type u} [MeasurableSpace Ω]
    {ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {P : ProbabilityMeasure Ω}
    {W : NNReal → Ω → Fin m → ℝ}
    {X : NNReal → Ω → SDEState n}
    (hbσ_lipschitz : SDESpaceLipschitzWith K b σ)
    (hbσ_growth : SDELinearGrowthWith K b σ)
    (x : SDEState n)
    (hX :
      HasPathwiseStrongSolutionRealization
        (IsBrownianMotionWithFiltration ℱ (P : Measure Ω))
        (fun ξ W' X' ↦ IsGeneralizedNDimensionalDiffusion ℱ (P : Measure Ω) ξ W' σ b X')
        ℱ
        (fun _ ↦ x)
        W
        X) :
    HasMarkovProperty (processFiltration X) (P : Measure Ω) X := by
  -- TODO: once the unique-strong-solution operator is available, rewrite the given pathwise
  -- realization through its exact path lift and use the Brownian future-increment restart kernel
  -- to prove the Chapter 17 Markov conditional-expectation identity.
  sorry

/-- Companion to Theorem 26.8: if the coefficients are time independent, then under the same
Lipschitz and linear-growth hypotheses every deterministic-start pathwise strong realization is
strong Markov in the fixed-start sense. -/
theorem strongMarkovRealization_of_lipschitz_linearGrowth
    {K : ℝ} {Ω : Type u} [MeasurableSpace Ω]
    {ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {P : ProbabilityMeasure Ω}
    {W : NNReal → Ω → Fin m → ℝ}
    {X : NNReal → Ω → SDEState n}
    (hbσ_lipschitz : SDESpaceLipschitzWith K b σ)
    (hbσ_growth : SDELinearGrowthWith K b σ)
    (hcoeff : TimeIndependentCoefficients σ b)
    (x : SDEState n)
    (hX :
      HasPathwiseStrongSolutionRealization
        (IsBrownianMotionWithFiltration ℱ (P : Measure Ω))
        (fun ξ W' X' ↦ IsGeneralizedNDimensionalDiffusion ℱ (P : Measure Ω) ξ W' σ b X')
        ℱ
        (fun _ ↦ x)
        W
        X) :
    ∃ κ : Kernel (SDEState n) (NNReal → SDEState n),
      HasStrongMarkovPropertyAtStartNDim P X κ := by
  -- TODO: package the restarted future-noise law into a state-only restart kernel once the
  -- operator-level unique strong solution theorem supplies the canonical restart solver.
  sorry

end GeneralizedStrongSolutions

end ProbabilityTheory
