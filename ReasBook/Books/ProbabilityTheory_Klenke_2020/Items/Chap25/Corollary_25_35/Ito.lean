/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Corollary_25_35.Regularity
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Corollary_25_35.QuadraticPrimitiveBridge
import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Remark_9_11
import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Remark_9_29
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Exercise_21_2_4
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Exercise_21_10_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_11
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Exercise_25_2_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.StandardBrownianMotionVector
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Theorem_25_21

open Filter MeasureTheory ProbabilityTheory
open Laplacian InnerProductSpace
open scoped BigOperators ENNReal ProbabilityTheory Topology InnerProductSpace

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {d : ℕ}

/-- Helper for `Corollary_25_35::statement_repair::6`: timewise almost-everywhere equality
preserves the martingale property once the target process is already strongly adapted. -/
private lemma martingale_congr_ae_local
    {ℱ : Filtration NNReal mΩ} {M N : NNReal → Ω → ℝ}
    (hM : Martingale M ℱ μ)
    (hN_stronglyAdapted : StronglyAdapted ℱ N)
    (hMN : ∀ t : NNReal, M t =ᵐ[μ] N t) :
    Martingale N ℱ μ := by
  refine ⟨hN_stronglyAdapted, ?_⟩
  intro s t hst
  -- Proof comment: transport the conditional expectation from `N t` back to `M t`, apply the
  -- martingale identity for `M`, and rewrite the time-`s` slice to `N s`.
  exact (condExp_congr_ae (hMN t)).symm.trans ((hM.condExp_ae_eq hst).trans (hMN s))

/-- Helper for `Corollary_25_35::statement_repair::6`: deterministic stopping at time `n` is
just time clipping by `min t n`. -/
private lemma stoppedProcess_constTime_eq_min
    {M : NNReal → Ω → ℝ} (n t : NNReal) :
    stoppedProcess M (fun _ ↦ (n : ENNReal)) t = M (min t n) := by
  ext ω
  -- Proof comment: unfold deterministic stopping and split on whether `t ≤ n` or `n ≤ t`, so
  -- the clipped time simplifies to the correct endpoint.
  rw [stoppedProcess]
  change M ((min (t : ENNReal) n).untopA) ω = M (min t n) ω
  by_cases ht : t ≤ n
  · have hmin : min (t : ENNReal) n = t := by
      exact min_eq_left (by exact_mod_cast ht)
    have htop : (t : ENNReal) ≠ ⊤ := by
      simp
    rw [hmin]
    have hUntop : WithTop.untop (t : ENNReal) htop = t := by
      exact WithTop.coe_inj.mp (WithTop.coe_untop (x := (t : ENNReal)) htop)
    rw [WithTop.untopA_eq_untop htop, hUntop]
    simp [min_eq_left ht]
  · have hnle : n ≤ t := le_of_not_ge ht
    have hmin : min (t : ENNReal) n = n := by
      exact min_eq_right (by exact_mod_cast hnle)
    have htop : (n : ENNReal) ≠ ⊤ := by
      simp
    rw [hmin]
    have hUntop : WithTop.untop (n : ENNReal) htop = n := by
      exact WithTop.coe_inj.mp (WithTop.coe_untop (x := (n : ENNReal)) htop)
    rw [WithTop.untopA_eq_untop htop, hUntop]
    simp [min_eq_right hnle]

/-- Helper for `Corollary_25_35::statement_repair::6`: conditioning the fixed terminal value
`M n` along the clipped filtration `ℱ (t ∧ n)` gives a martingale in the original filtration. -/
private lemma martingale_condExp_constTime
    [IsFiniteMeasure μ] {ℱ : Filtration NNReal mΩ} {M : NNReal → Ω → ℝ}
    (hM : Martingale M ℱ μ) (n : NNReal) :
    Martingale (fun t ω ↦ μ[M n | ℱ (min t n)] ω) ℱ μ := by
  refine ⟨?_, ?_⟩
  · intro t
    -- Proof comment: conditioning onto the smaller σ-algebra `ℱ (t ∧ n)` produces a strongly
    -- measurable representative on `ℱ t`.
    exact stronglyMeasurable_condExp.mono (ℱ.mono (min_le_left t n))
  · intro s t hst
    -- Proof comment: if `s ≤ n`, use the tower property from `ℱ s ≤ ℱ (t ∧ n)`. Once `s ≥ n`,
    -- both clipped times equal `n`, so the process is already constant after conditioning.
    by_cases hs : s ≤ n
    · have hsle : s ≤ min t n := le_min hst hs
      simpa [min_eq_left hs] using
        (condExp_condExp_of_le (ℱ.mono hsle) (ℱ.le (min t n)) :
          μ[μ[M n | ℱ (min t n)] | ℱ s] =ᵐ[μ] μ[M n | ℱ s])
    · have hnle : n ≤ s := le_of_not_ge hs
      have hnt : n ≤ t := hnle.trans hst
      have hnn : μ[M n | ℱ n] = M n :=
        condExp_of_stronglyMeasurable (ℱ.le n) (hM.stronglyMeasurable n) (hM.integrable n)
      have hEqt : (fun ω ↦ μ[M n | ℱ (min t n)] ω) =ᵐ[μ] M n := by
        exact Filter.EventuallyEq.of_eq (by simpa [min_eq_right hnt] using hnn)
      have hEqs : (fun ω ↦ μ[M n | ℱ (min s n)] ω) =ᵐ[μ] M n := by
        exact Filter.EventuallyEq.of_eq (by simpa [min_eq_right hnle] using hnn)
      have hconds : μ[M n | ℱ s] = M n :=
        condExp_of_stronglyMeasurable (ℱ.le s)
          ((hM.stronglyMeasurable n).mono (ℱ.mono hnle)) (hM.integrable n)
      have hleft :
          μ[(fun ω ↦ μ[M n | ℱ (min t n)] ω) | ℱ s] =ᵐ[μ] μ[M n | ℱ s] :=
        condExp_congr_ae hEqt
      have hright :
          μ[M n | ℱ s] =ᵐ[μ] fun ω ↦ μ[M n | ℱ (min s n)] ω := by
        exact (Filter.EventuallyEq.of_eq hconds).trans hEqs.symm
      exact hleft.trans hright

/-- Helper for `Corollary_25_35::statement_repair::6`: the process stopped at deterministic time
`n` agrees almost everywhere with the conditional-expectation martingale built from `M n`. -/
private lemma stoppedProcess_constTime_ae_eq_condExp
    [IsFiniteMeasure μ] {ℱ : Filtration NNReal mΩ} {M : NNReal → Ω → ℝ}
    (hM : Martingale M ℱ μ) (n t : NNReal) :
    stoppedProcess M (fun _ ↦ (n : ENNReal)) t =ᵐ[μ] fun ω ↦ μ[M n | ℱ (min t n)] ω := by
  -- Proof comment: before the deterministic stopping time, use the martingale identity; after the
  -- stopping time, both sides collapse to the fixed terminal slice `M n`.
  by_cases ht : t ≤ n
  · simpa [stoppedProcess_constTime_eq_min, min_eq_left ht] using (hM.condExp_ae_eq ht).symm
  · have hnle : n ≤ t := le_of_not_ge ht
    have hnn : μ[M n | ℱ n] = M n :=
      condExp_of_stronglyMeasurable (ℱ.le n) (hM.stronglyMeasurable n) (hM.integrable n)
    exact Filter.EventuallyEq.of_eq (by
      simpa [stoppedProcess_constTime_eq_min, min_eq_right hnle] using hnn.symm)

/-- Helper for `Corollary_25_35::statement_repair::6`: on a finite measure space, stopping a
martingale at a deterministic time gives a uniformly integrable martingale. -/
private lemma martingale_uniformIntegrable_stoppedProcess_constTime
    [IsFiniteMeasure μ] {ℱ : Filtration NNReal mΩ} {M : NNReal → Ω → ℝ}
    (hM : Martingale M ℱ μ) (n : NNReal) :
    Martingale (stoppedProcess M (fun _ ↦ (n : ENNReal))) ℱ μ ∧
      UniformIntegrable (stoppedProcess M (fun _ ↦ (n : ENNReal))) 1 μ := by
  let N : NNReal → Ω → ℝ := fun t ω ↦ μ[M n | ℱ (min t n)] ω
  have hN_mart : Martingale N ℱ μ := martingale_condExp_constTime hM n
  have hStopped_strong : StronglyAdapted ℱ (stoppedProcess M (fun _ ↦ (n : ENNReal))) := by
    intro t
    -- Proof comment: the stopped slice at time `t` is just the original slice at the clipped
    -- deterministic time `t ∧ n`.
    simpa [N, stoppedProcess_constTime_eq_min] using
      ((hM.stronglyMeasurable (min t n)).mono (ℱ.mono (min_le_left t n)))
  have hStopped_eq :
      ∀ t : NNReal, N t =ᵐ[μ] stoppedProcess M (fun _ ↦ (n : ENNReal)) t := by
    intro t
    exact (stoppedProcess_constTime_ae_eq_condExp hM n t).symm
  have hStopped_mart :
      Martingale (stoppedProcess M (fun _ ↦ (n : ENNReal))) ℱ μ :=
    martingale_congr_ae_local hN_mart hStopped_strong hStopped_eq
  letI : SigmaFinite μ := by
    infer_instance
  have hUI_N : UniformIntegrable N 1 μ := by
    -- Proof comment: a family of conditional expectations of one integrable terminal value is
    -- uniformly integrable on a finite measure space.
    simpa [N] using
      (hM.integrable n).uniformIntegrable_condExp fun t : NNReal ↦ ℱ.le (min t n)
  exact ⟨hStopped_mart, hUI_N.ae_eq hStopped_eq⟩

/-- Helper for `Corollary_25_35::statement_repair::6`: on a finite measure space, deterministic
times localize any martingale. -/
private lemma finiteMeasure_martingale_isLocalMartingale
    [IsFiniteMeasure μ] {ℱ : Filtration NNReal mΩ} {M : NNReal → Ω → ℝ}
    (hM : Martingale M ℱ μ) :
    IsLocalMartingale ℱ μ M := by
  -- Proof comment: deterministic times `τₙ ≡ n` localize every martingale on a finite measure
  -- space once each deterministically stopped process is known to be uniformly integrable.
  refine (isLocalMartingale_iff ℱ μ M).2 ⟨hM.stronglyAdapted.adapted, ?_⟩
  refine ⟨fun n _ ↦ (n : ENNReal), ?_⟩
  refine (isLocalizingSequence_iff ℱ μ M (fun n _ ↦ (n : ENNReal))).2 ?_
  refine ⟨?_, ?_, ?_⟩
  · intro n
    simpa using (isStoppingTime_const ℱ (n : NNReal))
  · refine Filter.Eventually.of_forall fun _ ↦ ?_
    refine ⟨fun a b hab ↦ by
      simpa using (show (a : ENNReal) ≤ (b : ENNReal) by exact_mod_cast hab), ?_⟩
    simpa using ENNReal.tendsto_nat_nhds_top
  · intro n
    simpa using martingale_uniformIntegrable_stoppedProcess_constTime (μ := μ) (ℱ := ℱ) hM
      (n := (n : NNReal))

/-- Helper for `Corollary_25_35::statement_repair::6`: covariance is unchanged by almost-everywhere
replacement of both arguments. -/
private lemma covariance_congr_ae
    {X X' Y Y' : Ω → ℝ}
    (hX : X =ᵐ[μ] X') (hY : Y =ᵐ[μ] Y') :
    cov[X, Y; μ] = cov[X', Y'; μ] := by
  -- Proof comment: rewrite both means by almost-sure equality, then rewrite the centered
  -- covariance integrand pointwise on the common full-measure event.
  have hIntX : μ[X] = μ[X'] := MeasureTheory.integral_congr_ae hX
  have hIntY : μ[Y] = μ[Y'] := MeasureTheory.integral_congr_ae hY
  rw [ProbabilityTheory.covariance, ProbabilityTheory.covariance]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [hX, hY] with ω hωX hωY
  simp [hωX, hωY, hIntX, hIntY]

/-- Helper for `Corollary_25_35::statement_repair::6`: patching a Brownian coordinate on the null
exception set where continuity fails preserves the Brownian owner. -/
private theorem patchedBrownian_isBrownianMotion
    {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) :
    IsBrownianMotion μ (brownianContinuousVersion hB) := by
  -- Proof comment: Brownian motion is stable under fixed-time almost-everywhere modification, and
  -- the canonical patch has continuous sample paths by construction.
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

/-- Helper for `Corollary_25_35::statement_repair::6`: the canonical coordinatewise continuous
version of a standard Brownian motion vector. This is the source-faithful Brownian object used by
the pathwise Itô integral in the repaired corollary statement. -/
noncomputable def standardBrownianMotionVectorContinuousVersion
    {W : NNReal → Ω → EuclideanSpace ℝ (Fin d)}
    (hW : IsStandardBrownianMotionVector μ W) :
    NNReal → Ω → EuclideanSpace ℝ (Fin d) :=
  fun t ω ↦
    WithLp.toLp 2 fun i ↦
      brownianContinuousVersion (hW.isBrownianMotion i) t ω

namespace BrownianVectorContinuousVersion

/-- Helper for `Corollary_25_35::statement_repair::6`: each coordinate of the canonical
continuous Brownian version is strongly measurable at fixed deterministic times. -/
theorem coord_stronglyMeasurable
    {W : NNReal → Ω → EuclideanSpace ℝ (Fin d)}
    (hW : IsStandardBrownianMotionVector μ W)
    (i : Fin d) :
    ∀ t,
      StronglyMeasurable
        (fun ω ↦ (standardBrownianMotionVectorContinuousVersion hW t ω).ofLp i) := by
  intro t
  -- Proof comment: the `i`-th coordinate of the vector patch is exactly the scalar continuous
  -- Brownian patch of the `i`-th coordinate process.
  simpa [standardBrownianMotionVectorContinuousVersion] using
    (patchedBrownian_isBrownianMotion (μ := μ) (B := fun t ω ↦ W t ω i)
      (hW.isBrownianMotion i)).stronglyMeasurable t

/-- Helper for `Corollary_25_35::statement_repair::6`: each coordinate of the canonical
continuous Brownian version supplies the continuous-local-martingale witness used by the canonical
scalar Itô integral process in the repaired corollary statement. -/
theorem coord_isContinuousLocalMartingale
    {W : NNReal → Ω → EuclideanSpace ℝ (Fin d)}
    (hW : IsStandardBrownianMotionVector μ W)
    (i : Fin d) :
    IsContinuousLocalMartingale
      (Filtration.natural
        (fun t ω ↦ (standardBrownianMotionVectorContinuousVersion hW t ω).ofLp i)
        (coord_stronglyMeasurable hW i))
      μ
      (fun t ω ↦ (standardBrownianMotionVectorContinuousVersion hW t ω).ofLp i) := by
  let Bi : NNReal → Ω → ℝ :=
    fun t ω ↦ (standardBrownianMotionVectorContinuousVersion hW t ω).ofLp i
  let hBi : IsBrownianMotion μ Bi := by
    simpa [Bi, standardBrownianMotionVectorContinuousVersion] using
      patchedBrownian_isBrownianMotion (μ := μ) (B := fun t ω ↦ W t ω i)
        (hW.isBrownianMotion i)
  let ℱi := Filtration.natural Bi (coord_stronglyMeasurable hW i)
  have hMart : Martingale Bi ℱi μ := by
    -- Proof comment: once the coordinate patch is recognized as Brownian, it is a martingale in
    -- its natural filtration.
    simpa [Bi, ℱi] using brownianMartingale_natural (μ := μ) (B := Bi) hBi
  refine
    { local_martingale := finiteMeasure_martingale_isLocalMartingale hMart
      continuous := ?_ }
  intro ω
  -- Proof comment: the coordinate path is the scalar continuous Brownian patch, so continuity is
  -- inherited pointwise from that patch.
  simpa [Bi, standardBrownianMotionVectorContinuousVersion] using
    brownianContinuousVersion_continuous (μ := μ) (B := fun t ω ↦ W t ω i)
      (hW.isBrownianMotion i) ω

end BrownianVectorContinuousVersion

/-- Helper for `Corollary_25_35::statement_repair::6`: the `i`-th coordinate of the canonical
continuous version of the Brownian vector `W`. -/
noncomputable def standardBrownianMotionVectorContinuousCoordinate
    {W : NNReal → Ω → EuclideanSpace ℝ (Fin d)}
    (hW : IsStandardBrownianMotionVector μ W) (i : Fin d) :
    NNReal → Ω → ℝ :=
  fun t ω ↦ (standardBrownianMotionVectorContinuousVersion hW t ω).ofLp i

/-- Helper for `Corollary_25_35::statement_repair::6`: the natural filtration of the canonical
continuous version of the `i`-th Brownian coordinate. -/
noncomputable def standardBrownianMotionVectorCoordinateFiltration
    {W : NNReal → Ω → EuclideanSpace ℝ (Fin d)}
    (hW : IsStandardBrownianMotionVector μ W) (i : Fin d) :
    Filtration NNReal mΩ :=
  Filtration.natural
    (standardBrownianMotionVectorContinuousCoordinate hW i)
    (BrownianVectorContinuousVersion.coord_stronglyMeasurable hW i)

/-- Helper for `Corollary_25_35::statement_repair::6`: the continuous Brownian coordinate patch
has deterministic time as a continuous square-variation process. -/
private theorem brownianCoordinate_time_isContinuousSquareVariationProcess
    {W : NNReal → Ω → EuclideanSpace ℝ (Fin d)}
    (hW : IsStandardBrownianMotionVector μ W)
    (i : Fin d) :
    IsContinuousSquareVariationProcess
      (μ := μ)
      (standardBrownianMotionVectorCoordinateFiltration hW i)
      (standardBrownianMotionVectorContinuousCoordinate hW i)
      (fun t : NNReal ↦ fun _ : Ω ↦ (t : ℝ)) := by
  let Bi := standardBrownianMotionVectorContinuousCoordinate hW i
  let hBi : IsBrownianMotion μ Bi := by
    simpa [Bi, standardBrownianMotionVectorContinuousCoordinate,
      standardBrownianMotionVectorContinuousVersion] using
      patchedBrownian_isBrownianMotion (μ := μ) (B := fun t ω ↦ W t ω i)
        (hW.isBrownianMotion i)
  let ℱi := standardBrownianMotionVectorCoordinateFiltration hW i
  have hSqMart : Martingale (fun t ω ↦ Bi t ω ^ 2 - (t : ℝ)) ℱi μ := by
    -- Proof comment: the compensated square of the coordinate Brownian patch is a martingale in
    -- its natural filtration.
    simpa [Bi, ℱi, standardBrownianMotionVectorCoordinateFiltration] using
      brownian_sq_sub_time_martingale (μ := μ) (B := Bi) hBi
  refine
    { zero := by
        funext ω
        simp
      adapted := adapted_const' ℱi (fun t : NNReal ↦ (t : ℝ))
      continuous := ?_
      monotone := ?_
      local_martingale_sq_sub := ?_ }
  · intro ω
    -- Proof comment: the deterministic time clock is continuous on `NNReal`.
    simpa using continuous_subtype_val
  · intro ω s t hst
    exact_mod_cast hst
  · refine
      { local_martingale := finiteMeasure_martingale_isLocalMartingale hSqMart
        continuous := ?_ }
    intro ω
    -- Proof comment: the compensated square is continuous because both the coordinate patch and
    -- the deterministic clock are continuous.
    simpa [Bi, standardBrownianMotionVectorContinuousCoordinate,
      standardBrownianMotionVectorContinuousVersion] using
      ((brownianContinuousVersion_continuous (μ := μ) (B := fun t ω ↦ W t ω i)
        (hW.isBrownianMotion i) ω).pow 2).sub continuous_subtype_val

/-- Helper for `Corollary_25_35::statement_repair::6`: the constant unit bracket density is
progressively measurable for the canonical Brownian coordinate filtration. -/
private theorem brownianCoordinate_unitDensity_progMeasurable
    {W : NNReal → Ω → EuclideanSpace ℝ (Fin d)}
    (hW : IsStandardBrownianMotionVector μ W)
    (i : Fin d) :
    ProgMeasurable
      (standardBrownianMotionVectorCoordinateFiltration hW i)
      (fun _ : NNReal ↦ fun _ : Ω ↦ (1 : ℝ)) := by
  -- Proof comment: progressive measurability is immediate for deterministic constant
  -- coefficients.
  simpa using
    (progMeasurable_const
      (f := standardBrownianMotionVectorCoordinateFiltration hW i)
      (b := (1 : ℝ)))

/-- Helper for `Corollary_25_35::statement_repair::6`: integrating the constant unit bracket
density over `[0,t]` recovers the deterministic clock. -/
private theorem brownianCoordinate_unitDensity_squareVariationEq
    {W : NNReal → Ω → EuclideanSpace ℝ (Fin d)}
    (hW : IsStandardBrownianMotionVector μ W)
    (i : Fin d) :
    ∀ t : NNReal, ∀ ω : Ω,
      (t : ℝ) =
        ∫ s in Set.Icc (0 : ℝ) (t : ℝ), (((1 : NNReal) : ℝ)) := by
  intro t ω
  -- Proof comment: the integral of the constant density `1` over `[0,t]` is the interval length.
  simp [Real.volume_Icc]

/-- Helper for `Corollary_25_35::statement_repair::6`: the canonical continuous version of each
Brownian coordinate has absolutely continuous square variation with deterministic density `1`. -/
noncomputable def brownianCoordinate_hasAbsolutelyContinuousSquareVariation
    {W : NNReal → Ω → EuclideanSpace ℝ (Fin d)}
    (hW : IsStandardBrownianMotionVector μ W)
    (i : Fin d) :
    HasAbsolutelyContinuousSquareVariation
      (standardBrownianMotionVectorContinuousCoordinate hW i)
      (BrownianVectorContinuousVersion.coord_isContinuousLocalMartingale hW i) :=
  { density := fun _ _ ↦ 1
    squareVariation := fun t _ ↦ (t : ℝ)
    squareVariation_owner := brownianCoordinate_time_isContinuousSquareVariationProcess hW i
    density_progMeasurable := brownianCoordinate_unitDensity_progMeasurable hW i
    squareVariation_eq := brownianCoordinate_unitDensity_squareVariationEq hW i }

/-- Helper for `Corollary_25_35::statement_repair::6`: the canonical scalar Itô integral process
of the `i`-th coordinate of the canonical continuous Brownian version against the spatial partial
derivative coefficient `∂[i] F`. -/
noncomputable def standardBrownianMotionVectorCoordinateItoIntegral
    (F : EuclideanSpace ℝ (Fin d) × ℝ → ℝ)
    {W : NNReal → Ω → EuclideanSpace ℝ (Fin d)}
    (hW : IsStandardBrownianMotionVector μ W) (i : Fin d) :
    NNReal → Ω → ℝ :=
  continuousLocalMartingaleItoIntegralProcess
    (BrownianVectorContinuousVersion.coord_isContinuousLocalMartingale hW i)
    (fun t ω ↦
      (∂[i] fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, (t : ℝ)))
        (standardBrownianMotionVectorContinuousVersion hW t ω))

/-- Helper for `Corollary_25_35::statement_repair::6`: the canonical stochastic term in the
displayed formula is definitionally the dyadic pathwise Itô integral along the corresponding
continuous Brownian coordinate path. -/
private theorem standardBrownianMotionVectorCoordinateItoIntegral_apply_eq_pathwise
    (F : EuclideanSpace ℝ (Fin d) × ℝ → ℝ)
    {W : NNReal → Ω → EuclideanSpace ℝ (Fin d)}
    (hW : IsStandardBrownianMotionVector μ W)
    (i : Fin d) (T : NNReal) (ω : Ω) :
    standardBrownianMotionVectorCoordinateItoIntegral F hW i T ω =
      pathwiseItoIntegralAlong
        (fun s : NNReal ↦
          (∂[i] fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, (s : ℝ)))
            (standardBrownianMotionVectorContinuousVersion hW s ω))
        (⟨fun s : NNReal ↦
            (standardBrownianMotionVectorContinuousVersion hW s ω).ofLp i,
          (BrownianVectorContinuousVersion.coord_isContinuousLocalMartingale hW i).continuous ω⟩ :
          C(NNReal, ℝ))
        Definition2158.dyadicPartitionSequence
        T := by
  -- Proof comment: unfold the scalar Itô owner; by definition it is exactly the canonical dyadic
  -- pathwise integral along the `i`-th coordinate path of the continuous Brownian version.
  rfl

/-- Helper for `Corollary_25_35::statement_repair::6`: outside one null event, the canonical
continuous Brownian vector version agrees with the original process at every deterministic time. -/
private theorem standardBrownianContinuousVersion_eq_ae_allTimes
    {W : NNReal → Ω → EuclideanSpace ℝ (Fin d)}
    (hW : IsStandardBrownianMotionVector μ W) :
    ∀ᵐ ω ∂μ, ∀ t : NNReal,
      standardBrownianMotionVectorContinuousVersion hW t ω = W t ω := by
  have hcoords :
      ∀ᵐ ω ∂μ, ∀ i : Fin d, ∀ t : NNReal,
        (standardBrownianMotionVectorContinuousVersion hW t ω).ofLp i = W t ω i := by
    rw [ae_all_iff]
    intro i
    -- Proof comment: each coordinate patch agrees with the original Brownian coordinate at all
    -- deterministic times on a full-measure event.
    simpa [standardBrownianMotionVectorContinuousVersion] using
      (brownianContinuousVersion_ae_eq (μ := μ) (B := fun t ω ↦ W t ω i)
        (hW.isBrownianMotion i))
  filter_upwards [hcoords] with ω hω t
  -- Proof comment: equality in the Euclidean state space is coordinatewise.
  ext i
  exact hω i t

/-- Helper for `Corollary_25_35::statement_repair::6`: each deterministic-time slice of the
canonical continuous Brownian vector version is strongly measurable. This is the ambient
filtration owner used to repair the coordinate Itô approximation route. -/
private theorem brownianContinuousVector_stronglyMeasurable
    {W : NNReal → Ω → EuclideanSpace ℝ (Fin d)}
    (hW : IsStandardBrownianMotionVector μ W)
    (t : NNReal) :
    StronglyMeasurable (standardBrownianMotionVectorContinuousVersion hW t) := by
  let ψ : EuclideanSpace ℝ (Fin d) ≃ᵐ (Fin d → ℝ) :=
    (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm
  rw [stronglyMeasurable_iff_measurable]
  have hcoords :
      Measurable
        (ψ ∘ standardBrownianMotionVectorContinuousVersion hW t) := by
    refine measurable_pi_lambda _ fun i ↦ ?_
    -- Proof comment: after moving to coordinates, each component is the scalar continuous
    -- Brownian patch of the corresponding original Brownian coordinate.
    simpa [standardBrownianMotionVectorContinuousVersion] using
      ((patchedBrownian_isBrownianMotion (μ := μ) (B := fun s ω ↦ W s ω i)
        (hW.isBrownianMotion i)).stronglyMeasurable t).measurable
  exact ψ.measurableEmbedding.measurable_comp_iff.1 hcoords

/-- Helper for `Corollary_25_35::statement_repair::6`: the canonical common-null-set continuous
Brownian vector patch still carries the standard Brownian vector owner. -/
private theorem standardBrownianMotionVectorContinuousVersion_isStandardBrownianMotionVector
    {W : NNReal → Ω → EuclideanSpace ℝ (Fin d)}
    (hW : IsStandardBrownianMotionVector μ W) :
    IsStandardBrownianMotionVector μ (standardBrownianMotionVectorContinuousVersion hW) := by
  refine
    { isBrownianMotion := ?_
      iIndepFun := ?_ }
  · intro i
    -- Proof comment: each coordinate of the patched vector is the scalar continuous Brownian
    -- patch of the corresponding original coordinate.
    simpa [standardBrownianMotionVectorContinuousVersion] using
      patchedBrownian_isBrownianMotion (μ := μ) (B := fun t ω ↦ W t ω i)
        (hW.isBrownianMotion i)
  · have hcoord_eq :
        ∀ i : Fin d,
          (fun ω ↦ fun t : NNReal ↦ W t ω i) =ᵐ[μ]
            (fun ω ↦
              fun t : NNReal ↦ standardBrownianMotionVectorContinuousVersion hW t ω i) := by
        intro i
        filter_upwards [standardBrownianContinuousVersion_eq_ae_allTimes (μ := μ) hW] with ω hω
        funext t
        exact congrArg (fun y : EuclideanSpace ℝ (Fin d) ↦ y i) (hω t).symm
    -- Proof comment: the patch is performed on one common null set, so coordinate-path
    -- independence survives unchanged.
    exact hW.iIndepFun.congr hcoord_eq

/-- Helper for `Corollary_25_35::statement_repair::6`: the natural filtration of one coordinate
of the canonical continuous Brownian vector version is contained in the natural filtration of the
whole continuous Brownian vector. -/
private theorem brownianCoordinateNatural_le_brownianVectorNatural
    {W : NNReal → Ω → EuclideanSpace ℝ (Fin d)}
    (hW : IsStandardBrownianMotionVector μ W)
    (i : Fin d) :
    Filtration.natural
        (standardBrownianMotionVectorContinuousCoordinate hW i)
        (BrownianVectorContinuousVersion.coord_stronglyMeasurable hW i)
      ≤
      Filtration.natural
        (standardBrownianMotionVectorContinuousVersion hW)
        (brownianContinuousVector_stronglyMeasurable (μ := μ) hW) := by
  let Wc := standardBrownianMotionVectorContinuousVersion hW
  let Bi := standardBrownianMotionVectorContinuousCoordinate hW i
  let ℱWc : Filtration NNReal mΩ :=
    Filtration.natural Wc (brownianContinuousVector_stronglyMeasurable (μ := μ) hW)
  have hBi_sm : ∀ t : NNReal, StronglyMeasurable (Bi t) :=
    BrownianVectorContinuousVersion.coord_stronglyMeasurable hW i
  have hBi_adapted : Adapted ℱWc Bi := by
    intro t
    have hslice :
        StronglyMeasurable[ℱWc t] (Wc t) :=
      Filtration.stronglyAdapted_natural
        (u := Wc)
        (brownianContinuousVector_stronglyMeasurable (μ := μ) hW)
        t
    -- Proof comment: each coordinate slice is obtained by applying the continuous coordinate
    -- projection to the ambient vector slice at time `t`.
    simpa [Bi, Wc, standardBrownianMotionVectorContinuousCoordinate] using
      (((EuclideanSpace.proj i).continuous.measurable.comp hslice.measurable).stronglyMeasurable
        : StronglyMeasurable[ℱWc t]
            (fun ω ↦
              (standardBrownianMotionVectorContinuousVersion hW t ω).ofLp i)).measurable
  exact (adapted_iff_natural_le hBi_sm).mp hBi_adapted

/-- Helper for `Corollary_25_35::statement_repair::6`: independence is stable when the right-hand
σ-algebra is replaced by a smaller one. -/
private theorem indep_mono_right_local
    {m₁ m₂ m₃ : MeasurableSpace Ω}
    (h : Indep m₁ m₃ μ)
    (hm : m₂ ≤ m₃) :
    Indep m₁ m₂ μ := by
  -- Proof comment: every `m₂`-measurable event is also `m₃`-measurable, so the defining
  -- factorization for `h` applies unchanged.
  rw [Indep_iff] at h ⊢
  intro s t hs ht
  exact h s t hs (hm _ ht)

/-- Helper for `Corollary_25_35::statement_repair::6`: a standard Euclidean Brownian vector is a
Gaussian process. -/
private theorem standardBrownianVector_isGaussianProcess_local
    {W : NNReal → Ω → EuclideanSpace ℝ (Fin d)}
    (hW : IsStandardBrownianMotionVector μ W) :
    IsGaussianProcess W μ := by
  classical
  letI : IsStandardBrownianMotionVector μ W := hW
  let ψ : EuclideanSpace ℝ (Fin d) ≃L[ℝ] (Fin d → ℝ) :=
    PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d ↦ ℝ)
  refine { hasGaussianLaw := fun I ↦ ?_ }
  let Xi : Fin d → Ω → I → ℝ := fun j ω u ↦ W u ω j
  have hXi_gauss : ∀ j : Fin d, HasGaussianLaw (Xi j) μ := by
    intro j
    let hBj : IsBrownianMotion μ (fun t ω ↦ W t ω j) := inferInstance
    let hGj : IsGaussianProcess (fun t ω ↦ W t ω j) μ :=
      IsBrownianMotion.isGaussianProcess hBj
    -- Proof comment: every coordinate of the Brownian vector is already a scalar Gaussian
    -- process, so finite restrictions have Gaussian law coordinatewise.
    simpa [Xi] using hGj.hasGaussianLaw I
  have hXi_indep : iIndepFun Xi μ := by
    -- Proof comment: coordinate-path independence persists after restricting each path to the
    -- finite time set `I`.
    refine hW.iIndepFun.comp (fun _ f ↦ I.restrict f) ?_
    intro j
    exact measurable_pi_lambda _ fun u ↦ measurable_pi_apply (u : NNReal)
  let L : (Fin d → I → ℝ) →L[ℝ] I → EuclideanSpace ℝ (Fin d) :=
    { toFun := fun x u ↦ ψ.symm (fun j ↦ x j u)
      map_add' := by
        intro x y
        ext u j
        rfl
      map_smul' := by
        intro c x
        ext u j
        rfl
      cont := by
        refine continuous_pi fun u ↦ ?_
        exact ψ.symm.continuous.comp <|
          continuous_pi fun j ↦ (continuous_apply u).comp (continuous_apply j) }
  have hgauss :
      HasGaussianLaw (fun ω ↦ fun j ↦ Xi j ω) μ :=
    ProbabilityTheory.iIndepFun.hasGaussianLaw hXi_gauss hXi_indep
  -- Proof comment: repackaging the independent scalar coordinates through the Euclidean
  -- equivalence reconstructs the Gaussian law of the vector process.
  simpa [Xi] using hgauss.map L

/-- Helper for `Corollary_25_35::statement_repair::6`: a future coordinate increment of the
continuous Brownian vector is independent of the ambient natural filtration up to the start time. -/
private theorem brownianCoordinateIncrement_indep_brownianVectorNatural
    {W : NNReal → Ω → EuclideanSpace ℝ (Fin d)}
    (hW : IsStandardBrownianMotionVector μ W)
    (i : Fin d) {s t : NNReal} (hst : s ≤ t) :
    let Wc := standardBrownianMotionVectorContinuousVersion hW
    let Bi : NNReal → Ω → ℝ := fun u ω ↦ (Wc u ω).ofLp i
    let ℱWc : Filtration NNReal mΩ :=
      Filtration.natural Wc (brownianContinuousVector_stronglyMeasurable (μ := μ) hW)
    Indep
      (MeasurableSpace.comap (fun ω ↦ Bi t ω - Bi s ω) (borel ℝ))
      (ℱWc s)
      μ := by
  let Wc := standardBrownianMotionVectorContinuousVersion hW
  let Bi : NNReal → Ω → ℝ := fun u ω ↦ (Wc u ω).ofLp i
  let ℱWc : Filtration NNReal mΩ :=
    Filtration.natural Wc (brownianContinuousVector_stronglyMeasurable (μ := μ) hW)
  let hWc : IsStandardBrownianMotionVector μ Wc :=
    standardBrownianMotionVectorContinuousVersion_isStandardBrownianMotionVector
      (μ := μ) hW
  have hBi_brownian : IsBrownianMotion μ Bi := hWc.isBrownianMotion i
  let X : Unit → Ω → ℝ := fun _ ω ↦ Bi t ω - Bi s ω
  let Y : Fin d × Set.Iic s → Ω → ℝ := fun ju ω ↦ (Wc ju.2 ω).ofLp ju.1
  have hWG : IsGaussianProcess Wc μ :=
    standardBrownianVector_isGaussianProcess_local hWc
  have hJoint : IsGaussianProcess (Sum.elim X Y) μ := by
    refine hWG.of_isGaussianProcess ?_
    intro z
    cases z with
    | inl _ =>
        let I : Finset NNReal := {t, s}
        have htI : t ∈ I := by simp [I]
        have hsI : s ∈ I := by simp [I]
        refine
          ⟨I,
            ((EuclideanSpace.proj i).comp (ContinuousLinearMap.proj (⟨t, htI⟩ : I))) -
              ((EuclideanSpace.proj i).comp (ContinuousLinearMap.proj (⟨s, hsI⟩ : I))),
            ?_⟩
        -- Proof comment: the increment is the difference of the `i`-th coordinate evaluations at
        -- the two deterministic times `t` and `s`.
        intro ω
        simp [X, Bi, I]
    | inr ju =>
        let I : Finset NNReal := {(ju.2 : NNReal)}
        have huI : (ju.2 : NNReal) ∈ I := by simp [I]
        refine
          ⟨I,
            (EuclideanSpace.proj ju.1).comp
              (ContinuousLinearMap.proj (⟨(ju.2 : NNReal), huI⟩ : I)),
            ?_⟩
        -- Proof comment: each past scalar coordinate is a single coordinate projection of the
        -- vector state at time `u ≤ s`.
        intro ω
        simp [Y, I]
  have hX_meas : ∀ u : Unit, AEMeasurable (X u) μ := by
    intro u
    exact ((BrownianVectorContinuousVersion.coord_stronglyMeasurable hW i t).measurable.sub
      (BrownianVectorContinuousVersion.coord_stronglyMeasurable hW i s).measurable).aemeasurable
  have hY_meas : ∀ ju : Fin d × Set.Iic s, AEMeasurable (Y ju) μ := by
    intro ju
    exact (BrownianVectorContinuousVersion.coord_stronglyMeasurable hW ju.1 ju.2).aemeasurable
  have hIndepFun :
      IndepFun (fun ω (_ : Unit) ↦ X () ω) (fun ω ju ↦ Y ju ω) μ := by
    refine ProbabilityTheory.IsGaussianProcess.indepFun_of_covariance_eq_zero
      hJoint hX_meas hY_meas ?_
    intro _ ju
    have hti_mem : MemLp (Bi t) 2 μ := brownianEval_memLp_two_ofBrownianMotion hBi_brownian t
    have hsi_mem : MemLp (Bi s) 2 μ := brownianEval_memLp_two_ofBrownianMotion hBi_brownian s
    have hu_mem : MemLp (Y ju) 2 μ := by
      simpa [Y] using
        brownianEval_memLp_two_ofBrownianMotion (hWc.isBrownianMotion ju.1) ju.2
    by_cases hij : i = ju.1
    · subst hij
      have htu_cov :
          cov[(fun ω ↦ Bi t ω), (fun ω ↦ Bi ju.2 ω); μ] = ((ju.2 : NNReal) : ℝ) := by
        simpa [inf_eq_right.mpr (ju.2.2.trans hst)] using
          IsBrownianMotion.covariance_eq
            hBi_brownian
            t ju.2
      have hsu_cov :
          cov[(fun ω ↦ Bi s ω), (fun ω ↦ Bi ju.2 ω); μ] = ((ju.2 : NNReal) : ℝ) := by
        simpa [inf_eq_right.mpr ju.2.2] using
          IsBrownianMotion.covariance_eq
            hBi_brownian
            s ju.2
      -- Proof comment: on the same coordinate, Brownian covariance identifies both terms with the
      -- earlier time `u`, so the increment covariance vanishes by subtraction.
      have hcov_sub :
          cov[(fun ω ↦ Bi t ω - Bi s ω), Y ju; μ] = 0 := by
        rw [htu_cov, hsu_cov]
        simpa using covariance_fun_sub_left hti_mem hsi_mem hu_mem
      simpa [X, Y] using hcov_sub
    · have hcoord_indep :
        IndepFun
          (fun ω ↦ Bi t ω - Bi s ω)
          (fun ω ↦ Y ju ω)
          μ := by
        -- Proof comment: distinct coordinates are independent as path processes, so any
        -- deterministic-time increment of coordinate `i` is independent of any past value of
        -- coordinate `ju.1`.
        exact
          (hWc.iIndepFun.indepFun (i := i) (j := ju.1) hij).comp
            ((measurable_pi_apply t).sub (measurable_pi_apply s))
            (measurable_pi_apply (ju.2 : NNReal))
      -- Proof comment: independence of the two scalar functionals forces their covariance to be
      -- zero.
      simpa [X, Y] using hcoord_indep.covariance_eq_zero
        (brownianIncrement_memLp_two hBi_brownian hst)
        hu_mem
  have hIndepBig :
      Indep
        (MeasurableSpace.comap (fun ω ↦ Bi t ω - Bi s ω) (borel ℝ))
        (MeasurableSpace.comap (fun ω ju ↦ Y ju ω) MeasurableSpace.pi)
        μ :=
    (ProbabilityTheory.IndepFun_iff_Indep _ _ _).mp hIndepFun
  have hℱWc_le :
      ℱWc s ≤ MeasurableSpace.comap (fun ω ju ↦ Y ju ω) MeasurableSpace.pi := by
    change
      (⨆ u, ⨆ (_ : u ≤ s), MeasurableSpace.comap (Wc u) inferInstance) ≤
        MeasurableSpace.comap (fun ω ju ↦ Y ju ω) MeasurableSpace.pi
    refine iSup₂_le fun u hu ↦ ?_
    have hWu_meas :
        Measurable[MeasurableSpace.comap (fun ω ju ↦ Y ju ω) MeasurableSpace.pi] (Wc u) := by
      let ψ : EuclideanSpace ℝ (Fin d) ≃ᵐ (Fin d → ℝ) :=
        (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm
      have hcoords :
          Measurable[MeasurableSpace.comap (fun ω ju ↦ Y ju ω) MeasurableSpace.pi] (ψ ∘ Wc u) := by
        refine measurable_pi_lambda _ fun j ↦ ?_
        -- Proof comment: every coordinate of `Wc u` is one of the scalar generators of the past
        -- coordinate family, indexed by `(j, u)`.
        simpa [Y] using
          (measurable_pi_apply (j, (⟨u, hu⟩ : Set.Iic s)) :
            Measurable[MeasurableSpace.comap (fun ω ju ↦ Y ju ω) MeasurableSpace.pi]
              (fun ω ↦ (fun ω ju ↦ Y ju ω) ω (j, (⟨u, hu⟩ : Set.Iic s))))
      exact ψ.measurableEmbedding.measurable_comp_iff.1 hcoords
    exact hWu_meas.comap_le
  -- Proof comment: the coordinate-past family generates a σ-algebra containing the ambient
  -- Brownian natural filtration at time `s`, so the Gaussian independence descends to `ℱWc s`.
  simpa [Bi, ℱWc] using indep_mono_right_local hIndepBig hℱWc_le

/-- Helper for `Corollary_25_35::statement_repair::6`: in the ambient natural filtration of the
continuous Brownian vector, each coordinate is a martingale. -/
private theorem brownianCoordinate_martingale_naturalVector
    {W : NNReal → Ω → EuclideanSpace ℝ (Fin d)}
    (hW : IsStandardBrownianMotionVector μ W)
    (i : Fin d) :
    let Wc := standardBrownianMotionVectorContinuousVersion hW
    let Bi : NNReal → Ω → ℝ := fun t ω ↦ (Wc t ω).ofLp i
    let ℱWc : Filtration NNReal mΩ :=
      Filtration.natural Wc (brownianContinuousVector_stronglyMeasurable (μ := μ) hW)
    Martingale Bi ℱWc μ := by
  let Wc := standardBrownianMotionVectorContinuousVersion hW
  let Bi : NNReal → Ω → ℝ := fun t ω ↦ (Wc t ω).ofLp i
  let ℱWc : Filtration NNReal mΩ :=
    Filtration.natural Wc (brownianContinuousVector_stronglyMeasurable (μ := μ) hW)
  let hWc : IsStandardBrownianMotionVector μ Wc :=
    standardBrownianMotionVectorContinuousVersion_isStandardBrownianMotionVector
      (μ := μ) hW
  have hBi : IsBrownianMotion μ Bi := hWc.isBrownianMotion i
  have hBi_adapted : StronglyAdapted ℱWc Bi := by
    intro t
    have hslice :
        StronglyMeasurable[ℱWc t] (Wc t) :=
      Filtration.stronglyAdapted_natural
        (u := Wc)
        (brownianContinuousVector_stronglyMeasurable (μ := μ) hW)
        t
    -- Proof comment: the ambient vector slice is already `ℱWc t`-measurable, and the `i`-th
    -- coordinate is extracted by the continuous projection.
    simpa [Bi] using
      (((EuclideanSpace.proj i).continuous.measurable.comp hslice.measurable).stronglyMeasurable
        : StronglyMeasurable[ℱWc t] (fun ω ↦ (Wc t ω).ofLp i))
  refine ⟨hBi_adapted, ?_⟩
  intro s t hst
  have hInc_meas : Measurable (fun ω ↦ Bi t ω - Bi s ω) := by
    exact
      (BrownianVectorContinuousVersion.coord_stronglyMeasurable hW i t).measurable.sub
        (BrownianVectorContinuousVersion.coord_stronglyMeasurable hW i s).measurable
  have hInc_sm :
      StronglyMeasurable[
        MeasurableSpace.comap (fun ω ↦ Bi t ω - Bi s ω) (borel ℝ)]
        (fun ω ↦ Bi t ω - Bi s ω) :=
    (comap_measurable (fun ω ↦ Bi t ω - Bi s ω)).stronglyMeasurable
  have hInc_indep :
      Indep
        (MeasurableSpace.comap (fun ω ↦ Bi t ω - Bi s ω) (borel ℝ))
        (ℱWc s)
        μ :=
    brownianCoordinateIncrement_indep_brownianVectorNatural
      (μ := μ) (W := W) hW i hst
  have hInc_mean_zero : ∫ ω, (Bi t ω - Bi s ω) ∂μ = 0 := by
    -- Proof comment: a Brownian increment has centered Gaussian law.
    simpa using (brownianIncrement_hasLaw hBi hst).integral_eq
  have hBs_int : Integrable (Bi s) μ :=
    (brownianEval_memLp_two_ofBrownianMotion hBi s).integrable (by norm_num)
  have hInc_int : Integrable (fun ω ↦ Bi t ω - Bi s ω) μ :=
    (brownianIncrement_memLp_two hBi hst).integrable (by norm_num)
  have hSplit : (fun ω ↦ Bi t ω) = fun ω ↦ Bi s ω + (Bi t ω - Bi s ω) := by
    -- Proof comment: split the future value into its past anchor plus the centered increment.
    funext ω
    ring
  have hInc_condExp_zero :
      μ[(fun ω ↦ Bi t ω - Bi s ω) | ℱWc s] =ᵐ[μ] 0 := by
    refine
      (MeasureTheory.condExp_indep_eq
        hInc_meas.comap_le (ℱWc.le s) hInc_sm hInc_indep).trans ?_
    exact Filter.Eventually.of_forall fun _ ↦ hInc_mean_zero
  -- Proof comment: after conditioning the increment decomposition, the past term is fixed and the
  -- future increment disappears by the ambient independence lemma above.
  calc
    μ[Bi t | ℱWc s]
        =ᵐ[μ] μ[(fun ω ↦ Bi s ω + (Bi t ω - Bi s ω)) | ℱWc s] := by
            exact condExp_congr_ae (Filter.EventuallyEq.of_eq hSplit)
    _ =ᵐ[μ] μ[Bi s | ℱWc s] + μ[(fun ω ↦ Bi t ω - Bi s ω) | ℱWc s] := by
          exact condExp_add hBs_int hInc_int _
    _ =ᵐ[μ] Bi s + 0 := by
          filter_upwards
            [Filter.EventuallyEq.of_eq
              (condExp_of_stronglyMeasurable (ℱWc.le s) (hBi_adapted s) hBs_int),
              hInc_condExp_zero]
            with ω hωs hωinc
          simp [hωs, hωinc]
    _ =ᵐ[μ] Bi s := by
          simp

/-- Helper for `Corollary_25_35::statement_repair::6`: in the ambient natural filtration of the
continuous Brownian vector, the compensated square of each coordinate is a martingale. -/
private theorem brownianCoordinate_sqSubTime_martingale_naturalVector
    {W : NNReal → Ω → EuclideanSpace ℝ (Fin d)}
    (hW : IsStandardBrownianMotionVector μ W)
    (i : Fin d) :
    let Wc := standardBrownianMotionVectorContinuousVersion hW
    let Bi : NNReal → Ω → ℝ := fun t ω ↦ (Wc t ω).ofLp i
    let ℱWc : Filtration NNReal mΩ :=
      Filtration.natural Wc (brownianContinuousVector_stronglyMeasurable (μ := μ) hW)
    Martingale (fun t ω ↦ Bi t ω ^ 2 - (t : ℝ)) ℱWc μ := by
  let Wc := standardBrownianMotionVectorContinuousVersion hW
  let Bi : NNReal → Ω → ℝ := fun t ω ↦ (Wc t ω).ofLp i
  let ℱWc : Filtration NNReal mΩ :=
    Filtration.natural Wc (brownianContinuousVector_stronglyMeasurable (μ := μ) hW)
  let hWc : IsStandardBrownianMotionVector μ Wc :=
    standardBrownianMotionVectorContinuousVersion_isStandardBrownianMotionVector
      (μ := μ) hW
  have hBi : IsBrownianMotion μ Bi := hWc.isBrownianMotion i
  have hAdapted :
      StronglyAdapted ℱWc (fun t ω ↦ Bi t ω ^ 2 - (t : ℝ)) := by
    intro t
    have hBt :
        StronglyMeasurable[ℱWc t] (Bi t) := by
      have hslice :
          StronglyMeasurable[ℱWc t] (Wc t) :=
        Filtration.stronglyAdapted_natural
          (u := Wc)
          (brownianContinuousVector_stronglyMeasurable (μ := μ) hW)
          t
      -- Proof comment: the quadratic process is built from the `ℱWc t`-measurable coordinate
      -- slice of the ambient Brownian vector.
      simpa [Bi] using
        (((EuclideanSpace.proj i).continuous.measurable.comp hslice.measurable).stronglyMeasurable
          : StronglyMeasurable[ℱWc t] (fun ω ↦ (Wc t ω).ofLp i))
    exact (hBt.pow 2).sub stronglyMeasurable_const
  refine ⟨hAdapted, ?_⟩
  intro s t hst
  let inc : Ω → ℝ := fun ω ↦ Bi t ω - Bi s ω
  let incSqComp : Ω → ℝ := fun ω ↦ inc ω ^ 2 - ((t - s : NNReal) : ℝ)
  have hInc_meas : Measurable inc := by
    exact
      (BrownianVectorContinuousVersion.coord_stronglyMeasurable hW i t).measurable.sub
        (BrownianVectorContinuousVersion.coord_stronglyMeasurable hW i s).measurable
  have hBs_mem : MemLp (Bi s) 2 μ := brownianEval_memLp_two_ofBrownianMotion hBi s
  have hInc_mem : MemLp inc 2 μ := brownianIncrement_memLp_two hBi hst
  have hBase_int : Integrable (fun ω ↦ Bi s ω ^ 2 - (s : ℝ)) μ := by
    -- Proof comment: square integrability of `Bi s` gives integrability of the base term.
    exact hBs_mem.integrable_sq.sub (integrable_const _)
  have hInc_int : Integrable inc μ := hInc_mem.integrable (by norm_num)
  have hCross_int : Integrable (fun ω ↦ (2 * Bi s ω) * inc ω) μ := by
    have hFactor_mem : MemLp (fun ω ↦ Bi s ω * 2) 2 μ := by
      simpa [mul_comm] using hBs_mem.const_mul (2 : ℝ)
    have hCross_int' : Integrable (fun ω ↦ inc ω * (Bi s ω * 2)) μ :=
      hInc_mem.integrable_mul hFactor_mem
    -- Proof comment: reorder the two scalar factors to match the normal form used later by the
    -- pull-out conditional expectation lemma.
    refine hCross_int'.congr ?_
    exact Filter.Eventually.of_forall fun ω ↦ by
      dsimp [inc]
      ring
  have hIncSqComp_int : Integrable incSqComp μ := by
    exact hInc_mem.integrable_sq.sub (integrable_const _)
  have hSplit :
      (fun ω ↦ Bi t ω ^ 2 - (t : ℝ)) =
        fun ω ↦ (Bi s ω ^ 2 - (s : ℝ)) + (((2 * Bi s ω) * inc ω) + incSqComp ω) := by
    -- Proof comment: expand `(Bi s + inc)^2` and isolate the centered increment square.
    funext ω
    dsimp [inc, incSqComp]
    rw [NNReal.coe_sub hst]
    ring
  have hCrossFactor_sm :
      StronglyMeasurable[ℱWc s] (fun ω ↦ 2 * Bi s ω) := by
    have hBs_sm :
        StronglyMeasurable[ℱWc s] (Bi s) := by
      have hslice :
          StronglyMeasurable[ℱWc s] (Wc s) :=
        Filtration.stronglyAdapted_natural
          (u := Wc)
          (brownianContinuousVector_stronglyMeasurable (μ := μ) hW)
          s
      simpa [Bi] using
        (((EuclideanSpace.proj i).continuous.measurable.comp hslice.measurable).stronglyMeasurable
          : StronglyMeasurable[ℱWc s] (fun ω ↦ (Wc s ω).ofLp i))
    exact hBs_sm.const_mul (2 : ℝ)
  have hInc_sm :
      StronglyMeasurable[MeasurableSpace.comap inc (borel ℝ)] inc :=
    (comap_measurable inc).stronglyMeasurable
  have hIncSqComp_sm :
      StronglyMeasurable[MeasurableSpace.comap inc (borel ℝ)] incSqComp :=
    (hInc_sm.pow 2).sub stronglyMeasurable_const
  have hInc_indep :
      Indep (MeasurableSpace.comap inc (borel ℝ)) (ℱWc s) μ := by
    simpa [inc] using
      brownianCoordinateIncrement_indep_brownianVectorNatural
        (μ := μ) (W := W) hW i hst
  have hInc_mean_zero : ∫ ω, inc ω ∂μ = 0 := by
    -- Proof comment: the increment remains centered in the ambient filtration proof.
    simpa [inc] using (brownianIncrement_hasLaw hBi hst).integral_eq
  have hInc_condExp_zero :
      μ[inc | ℱWc s] =ᵐ[μ] 0 := by
    refine (MeasureTheory.condExp_indep_eq
      (m₁ := MeasurableSpace.comap inc (borel ℝ))
      (m₂ := ℱWc s)
      hInc_meas.comap_le
      (ℱWc.le s)
      hInc_sm
      hInc_indep).trans ?_
    exact Filter.Eventually.of_forall fun _ ↦ hInc_mean_zero
  have hIncSqComp_mean_zero : ∫ ω, incSqComp ω ∂μ = 0 := by
    -- Proof comment: subtracting the deterministic variance `t - s` centers the squared
    -- increment exactly.
    rw [show incSqComp = fun ω ↦ inc ω ^ 2 - ((t - s : NNReal) : ℝ) by rfl]
    rw [integral_sub hInc_mem.integrable_sq (integrable_const _),
      brownianIncrement_sq_integral_eq_timeLag hBi hst, integral_const, probReal_univ]
    simp
  have hIncSqComp_condExp_zero :
      μ[incSqComp | ℱWc s] =ᵐ[μ] 0 := by
    refine (MeasureTheory.condExp_indep_eq
      (m₁ := MeasurableSpace.comap inc (borel ℝ))
      (m₂ := ℱWc s)
      hInc_meas.comap_le
      (ℱWc.le s)
      hIncSqComp_sm
      hInc_indep).trans ?_
    exact Filter.Eventually.of_forall fun _ ↦ hIncSqComp_mean_zero
  have hCross_condExp_zero :
      μ[(fun ω ↦ (2 * Bi s ω) * inc ω) | ℱWc s] =ᵐ[μ] 0 := by
    -- Proof comment: the past factor is `ℱWc s`-measurable, so the ambient independence again
    -- kills the future increment after pulling it outside the conditional expectation.
    calc
      μ[(fun ω ↦ (2 * Bi s ω) * inc ω) | ℱWc s]
          =ᵐ[μ] (fun ω ↦ 2 * Bi s ω) * μ[inc | ℱWc s] := by
              exact condExp_mul_of_stronglyMeasurable_left hCrossFactor_sm hCross_int hInc_int
      _ =ᵐ[μ] (fun ω ↦ 2 * Bi s ω) * 0 := by
            filter_upwards [hInc_condExp_zero] with ω hω
            simp [hω]
      _ =ᵐ[μ] 0 := by
            simp
  -- Proof comment: conditioning the square expansion in the ambient filtration leaves only the
  -- base term, since both future-increment contributions have conditional expectation `0`.
  calc
    μ[(fun ω ↦ Bi t ω ^ 2 - (t : ℝ)) | ℱWc s]
        =ᵐ[μ]
          μ[(fun ω ↦ (Bi s ω ^ 2 - (s : ℝ)) + (((2 * Bi s ω) * inc ω) + incSqComp ω)) | ℱWc s] := by
            exact condExp_congr_ae (Filter.EventuallyEq.of_eq hSplit)
    _ =ᵐ[μ] μ[(fun ω ↦ Bi s ω ^ 2 - (s : ℝ)) | ℱWc s] +
        μ[(fun ω ↦ (2 * Bi s ω) * inc ω) + incSqComp | ℱWc s] := by
          exact condExp_add hBase_int (hCross_int.add hIncSqComp_int) (ℱWc s)
    _ =ᵐ[μ] μ[(fun ω ↦ Bi s ω ^ 2 - (s : ℝ)) | ℱWc s] +
        (μ[(fun ω ↦ (2 * Bi s ω) * inc ω) | ℱWc s] + μ[incSqComp | ℱWc s]) := by
          exact Filter.EventuallyEq.rfl.add (condExp_add hCross_int hIncSqComp_int (ℱWc s))
    _ =ᵐ[μ] (fun ω ↦ Bi s ω ^ 2 - (s : ℝ)) + (0 + 0) := by
          filter_upwards
            [Filter.EventuallyEq.of_eq
              (condExp_of_stronglyMeasurable (ℱWc.le s) (hAdapted s) hBase_int),
              hCross_condExp_zero, hIncSqComp_condExp_zero]
            with ω hωbase hωcross hωsq
          simp [hωbase, hωcross, hωsq]
    _ =ᵐ[μ] fun ω ↦ Bi s ω ^ 2 - (s : ℝ) := by
          simp

/-- Helper for `Corollary_25_35::statement_repair::6`: in the natural filtration of the
continuous Brownian vector, each coordinate is still a continuous local martingale, and its
square variation is the deterministic clock. -/
private theorem brownianCoordinate_isContinuousLocalMartingale_and_timeBracket_naturalVector
    {W : NNReal → Ω → EuclideanSpace ℝ (Fin d)}
    (hW : IsStandardBrownianMotionVector μ W)
    (i : Fin d) :
    let Wc := standardBrownianMotionVectorContinuousVersion hW
    let Bi : NNReal → Ω → ℝ := fun t ω ↦ (Wc t ω).ofLp i
    let ℱWc : Filtration NNReal mΩ :=
      Filtration.natural Wc (brownianContinuousVector_stronglyMeasurable (μ := μ) hW)
    IsContinuousLocalMartingale ℱWc μ Bi ∧
      IsContinuousSquareVariationProcess
        ℱWc
        μ
        Bi
        (fun t : NNReal ↦ fun _ : Ω ↦ (t : ℝ)) := by
  let Wc := standardBrownianMotionVectorContinuousVersion hW
  let Bi : NNReal → Ω → ℝ := fun t ω ↦ (Wc t ω).ofLp i
  let ℱWc : Filtration NNReal mΩ :=
    Filtration.natural Wc (brownianContinuousVector_stronglyMeasurable (μ := μ) hW)
  let hWc : IsStandardBrownianMotionVector μ Wc :=
    standardBrownianMotionVectorContinuousVersion_isStandardBrownianMotionVector
      (μ := μ) hW
  have hBi : IsBrownianMotion μ Bi := hWc.isBrownianMotion i
  have hBi_adapted : Adapted ℱWc Bi := by
    intro t
    have hslice :
        StronglyMeasurable[ℱWc t] (Wc t) :=
      Filtration.stronglyAdapted_natural
        (u := Wc)
        (brownianContinuousVector_stronglyMeasurable (μ := μ) hW)
        t
    -- Proof comment: the coordinate process is read off from the ambient vector slice by the
    -- continuous coordinate projection.
    simpa [Bi] using
      (((EuclideanSpace.proj i).continuous.measurable.comp hslice.measurable).stronglyMeasurable
        : StronglyMeasurable[ℱWc t] (fun ω ↦ (Wc t ω).ofLp i)).measurable
  have hBiCont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Bi t ω := by
    intro ω
    -- Proof comment: the ambient coordinate path is the scalar continuous Brownian patch.
    simpa [Bi, Wc, standardBrownianMotionVectorContinuousVersion] using
      brownianContinuousVersion_continuous (μ := μ) (B := fun t ω ↦ W t ω i)
        (hW.isBrownianMotion i) ω
  have hBiMart : Martingale Bi ℱWc μ :=
    brownianCoordinate_martingale_naturalVector (W := W) hW i
  have hBiSqMart : Martingale (fun t ω ↦ Bi t ω ^ 2 - (t : ℝ)) ℱWc μ :=
    brownianCoordinate_sqSubTime_martingale_naturalVector (W := W) hW i
  refine
    ⟨{ local_martingale := finiteMeasure_martingale_isLocalMartingale hBiMart
       continuous := hBiCont },
      ?_⟩
  refine
    { zero := by
        funext ω
        simp
      adapted := adapted_const' ℱWc (fun t : NNReal ↦ (t : ℝ))
      continuous := ?_
      monotone := ?_
      local_martingale_sq_sub := ?_ }
  · intro ω
    -- Proof comment: the deterministic clock `t ↦ t` is continuous on `NNReal`.
    simpa using continuous_subtype_val
  · intro ω s t hst
    exact_mod_cast hst
  · refine
      { local_martingale := finiteMeasure_martingale_isLocalMartingale hBiSqMart
        continuous := ?_ }
    intro ω
    -- Proof comment: the compensated square is continuous because both the coordinate path and
    -- the deterministic clock are continuous.
    simpa using (hBiCont ω).pow 2 |>.sub continuous_subtype_val

/-- Helper for `Corollary_25_35::statement_repair::6`: for each spatial coordinate and every
admissible partition sequence, the ambient natural filtration of the continuous Brownian vector
supplies a pathwise subsequence theorem whose limit is the canonical coordinate Itô owner already
used in the target formula. This is the reusable reindexing surface needed for the later
finite-coordinate diagonal argument. -/
private theorem exists_coordinateItoSubsequence_naturalVector_of_partitionSequence
    (F : EuclideanSpace ℝ (Fin d) × ℝ → ℝ)
    (hF : IsTimeSpaceC21 F)
    {W : NNReal → Ω → EuclideanSpace ℝ (Fin d)}
    (hW : IsStandardBrownianMotionVector μ W)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (i : Fin d) :
    ∃ φ : ℕ → ℕ,
      StrictMono φ ∧
        ∀ᵐ ω ∂μ, ∀ T : NNReal,
          Tendsto
            (fun n ↦
              partitionPathwiseItoApproximationUpTo
                (fun t ↦
                  (∂[i] fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, (t : ℝ)))
                    (standardBrownianMotionVectorContinuousVersion hW t ω))
                (⟨fun t ↦
                    (standardBrownianMotionVectorContinuousVersion hW t ω).ofLp i,
                  brownianContinuousCoordinate_continuous_local (μ := μ) hW i ω⟩ :
                  C(NNReal, ℝ))
                P
                T
                (φ n))
            atTop
            (𝓝 (standardBrownianMotionVectorCoordinateItoIntegral F hW i T ω)) := by
  let Wc := standardBrownianMotionVectorContinuousVersion hW
  let Bi : NNReal → Ω → ℝ := fun t ω ↦ (Wc t ω).ofLp i
  let ℱWc : Filtration NNReal mΩ :=
    Filtration.natural Wc (brownianContinuousVector_stronglyMeasurable (μ := μ) hW)
  let hPair :=
    brownianCoordinate_isContinuousLocalMartingale_and_timeBracket_naturalVector
      (W := W) hW i
  let hBi : IsContinuousLocalMartingale ℱWc μ Bi := hPair.1
  let hbr : HasAbsolutelyContinuousSquareVariation Bi hBi :=
    { density := fun _ _ ↦ 1
      squareVariation := fun t _ ↦ (t : ℝ)
      squareVariation_owner := hPair.2
      density_progMeasurable := by
        -- Proof comment: the bracket density is the deterministic constant `1`.
        simpa using (progMeasurable_const (f := ℱWc) (b := (1 : ℝ)))
      squareVariation_eq := brownianCoordinate_unitDensity_squareVariationEq hW i }
  let H : NNReal → Ω → ℝ := fun t ω ↦
    (∂[i] fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, (t : ℝ))) (Wc t ω)
  have hH_prog : ProgMeasurable ℱWc H := by
    have hH_adapted : Adapted ℱWc H := by
      intro t
      have hslice :
          StronglyMeasurable[ℱWc t] (Wc t) :=
        Filtration.stronglyAdapted_natural
          (u := Wc)
          (brownianContinuousVector_stronglyMeasurable (μ := μ) hW)
          t
      -- Proof comment: each deterministic-time coefficient slice is a continuous function of the
      -- ambient Brownian state at time `t`, with the time parameter frozen.
      exact
        (((hF.continuous_spacePartialDeriv i).measurable.comp
          (hslice.measurable.prod_mk measurable_const)).stronglyMeasurable).measurable
    have hH_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ H t ω := by
      intro ω
      have hWcCont : Continuous fun t : NNReal ↦ Wc t ω := by
        refine continuous_pi fun j ↦ ?_
        simpa [Wc, standardBrownianMotionVectorContinuousVersion] using
          brownianContinuousVersion_continuous (μ := μ) (B := fun t ω ↦ W t ω j)
            (hW.isBrownianMotion j) ω
      -- Proof comment: along each sample path, the coefficient is the continuous spatial partial
      -- field of `F` evaluated on the continuous time-state graph `t ↦ (Wc_t, t)`.
      exact (hF.continuous_spacePartialDeriv i).comp (hWcCont.prodMk continuous_subtype_val)
    exact hH_adapted.stronglyAdapted.progMeasurable_of_continuous hH_cont
  have hH_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ H t ω := by
    intro ω
    have hWcCont : Continuous fun t : NNReal ↦ Wc t ω := by
      refine continuous_pi fun j ↦ ?_
      simpa [Wc, standardBrownianMotionVectorContinuousVersion] using
        brownianContinuousVersion_continuous (μ := μ) (B := fun t ω ↦ W t ω j)
          (hW.isBrownianMotion j) ω
    -- Proof comment: the same time-state continuity is reused for the pathwise finite-energy
    -- input needed by Exercise 25.2.1.
    exact (hF.continuous_spacePartialDeriv i).comp (hWcCont.prodMk continuous_subtype_val)
  have hFiniteEnergy : HasFiniteBracketEnergy hbr H := by
    refine ⟨hH_prog, ?_⟩
    intro T
    refine Filter.Eventually.of_forall ?_
    intro ω
    have hHReal : Continuous fun s : ℝ ↦ H s.toNNReal ω := by
      exact (hH_cont ω).comp continuous_real_toNNReal
    -- Proof comment: on each compact interval `[0,T]`, the continuous coefficient has square
    -- integrable sample paths, and the ambient Brownian bracket density is the constant `1`.
    simpa [H, hbr, one_mul] using
      ((hHReal.pow 2).continuousOn.integrableOn_compact
        (μ := volume) (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) (T : ℝ))))
  obtain ⟨φ, hφ, hφae⟩ :=
    exists_partitionSubsequence_with_ae_pathwise_itoApproximation
      (μ := μ) (ℱ := ℱWc) (M := Bi) (H := H) hBi hbr hH_prog hH_cont hFiniteEnergy
      P
  refine ⟨φ, hφ, ?_⟩
  filter_upwards [hφae] with ω hω T
  -- Proof comment: the ambient filtration changes only the bookkeeping, not the underlying path
  -- or coefficient, so the canonical Itô owner is exactly the target coordinate owner.
  simpa [Bi, H, Wc, standardBrownianMotionVectorCoordinateItoIntegral,
    continuousLocalMartingaleItoIntegralProcess] using hω T

/-- Helper for `Corollary_25_35::statement_repair::6`: the previous partition-sequence theorem
specialized to the dyadic sequence used throughout the corollary. -/
private theorem exists_coordinateItoSubsequence_naturalVector
    (F : EuclideanSpace ℝ (Fin d) × ℝ → ℝ)
    (hF : IsTimeSpaceC21 F)
    {W : NNReal → Ω → EuclideanSpace ℝ (Fin d)}
    (hW : IsStandardBrownianMotionVector μ W)
    (i : Fin d) :
    ∃ φ : ℕ → ℕ,
      StrictMono φ ∧
        ∀ᵐ ω ∂μ, ∀ T : NNReal,
          Tendsto
            (fun n ↦
              partitionPathwiseItoApproximationUpTo
                (fun t ↦
                  (∂[i] fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, (t : ℝ)))
                    (standardBrownianMotionVectorContinuousVersion hW t ω))
                (⟨fun t ↦
                    (standardBrownianMotionVectorContinuousVersion hW t ω).ofLp i,
                  brownianContinuousCoordinate_continuous_local (μ := μ) hW i ω⟩ :
                  C(NNReal, ℝ))
                Definition2158.dyadicPartitionSequence
                T
                (φ n))
            atTop
            (𝓝 (standardBrownianMotionVectorCoordinateItoIntegral F hW i T ω)) := by
  -- Proof comment: the general partition-sequence helper is instantiated at the canonical dyadic
  -- sequence used by the Chapter 25 pathwise Itô owners.
  simpa using
    exists_coordinateItoSubsequence_naturalVector_of_partitionSequence
      (μ := μ) F hF hW Definition2158.dyadicPartitionSequence i

/-- Helper for `Corollary_25_35::statement_repair::6`: any finite family of spatial coordinates
admits one common strict-mono dyadic subsequence along which all corresponding coordinate Itô
approximation rows converge almost surely to their canonical owners. -/
private theorem exists_commonCoordinateItoSubsequenceOnFinset
    (F : EuclideanSpace ℝ (Fin d) × ℝ → ℝ)
    (hF : IsTimeSpaceC21 F)
    {W : NNReal → Ω → EuclideanSpace ℝ (Fin d)}
    (hW : IsStandardBrownianMotionVector μ W)
    (s : Finset (Fin d)) :
    ∃ φ : ℕ → ℕ,
      StrictMono φ ∧
        ∀ᵐ ω ∂μ, ∀ i : Fin d, i ∈ s → ∀ T : NNReal,
          Tendsto
            (fun n ↦
              partitionPathwiseItoApproximationUpTo
                (fun t ↦
                  (∂[i] fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, (t : ℝ)))
                    (standardBrownianMotionVectorContinuousVersion hW t ω))
                (⟨fun t ↦
                    (standardBrownianMotionVectorContinuousVersion hW t ω).ofLp i,
                  brownianContinuousCoordinate_continuous_local (μ := μ) hW i ω⟩ :
                  C(NNReal, ℝ))
                Definition2158.dyadicPartitionSequence
                T
                (φ n))
            atTop
            (𝓝 (standardBrownianMotionVectorCoordinateItoIntegral F hW i T ω)) := by
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨fun n ↦ n, ?_, ?_⟩
      · intro m n hmn
        exact hmn
      · refine Filter.Eventually.of_forall ?_
        intro ω i hi
        exact False.elim (by simpa using hi)
  | @insert i s hi hs =>
      rcases hs with ⟨ψ, hψ, hψae⟩
      let Pψ : ℕ → ℕ → NNReal := fun n k ↦ Definition2158.dyadicPartitionSequence (ψ n) k
      letI : IsAdmissiblePartitionSequence Pψ :=
        isAdmissiblePartitionSequence_comp (P := Definition2158.dyadicPartitionSequence) hψ
      obtain ⟨ρ, hρ, hρae⟩ :=
        exists_coordinateItoSubsequence_naturalVector_of_partitionSequence
          (μ := μ) F hF hW Pψ i
      refine ⟨ψ ∘ ρ, hψ.comp hρ, ?_⟩
      filter_upwards [hψae, hρae] with ω hψω hρω
      intro j hj T
      rcases Finset.mem_insert.mp hj with rfl | hj
      · -- Proof comment: the newly inserted coordinate uses the fresh reindexed subsequence
        -- extracted on top of the old one.
        simpa [Pψ, Function.comp] using hρω T
      · -- Proof comment: previously controlled coordinates keep the same limit after passing to
        -- the further strict-mono refinement `ρ`.
        simpa [Function.comp] using (hψω j hj T).comp hρ.tendsto_atTop

/-- Helper for `Corollary_25_35::statement_repair::6`: all spatial coordinate rows admit one
common strict-mono dyadic subsequence with almost-sure convergence to the canonical coordinate Itô
owners. -/
private theorem exists_commonCoordinateItoSubsequence
    (F : EuclideanSpace ℝ (Fin d) × ℝ → ℝ)
    (hF : IsTimeSpaceC21 F)
    {W : NNReal → Ω → EuclideanSpace ℝ (Fin d)}
    (hW : IsStandardBrownianMotionVector μ W) :
    ∃ φ : ℕ → ℕ,
      StrictMono φ ∧
        ∀ᵐ ω ∂μ, ∀ i : Fin d, ∀ T : NNReal,
          Tendsto
            (fun n ↦
              partitionPathwiseItoApproximationUpTo
                (fun t ↦
                  (∂[i] fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, (t : ℝ)))
                    (standardBrownianMotionVectorContinuousVersion hW t ω))
                (⟨fun t ↦
                    (standardBrownianMotionVectorContinuousVersion hW t ω).ofLp i,
                  brownianContinuousCoordinate_continuous_local (μ := μ) hW i ω⟩ :
                  C(NNReal, ℝ))
                Definition2158.dyadicPartitionSequence
                T
                (φ n))
            atTop
            (𝓝 (standardBrownianMotionVectorCoordinateItoIntegral F hW i T ω)) := by
  rcases
      exists_commonCoordinateItoSubsequenceOnFinset
        (μ := μ) F hF hW (Finset.univ : Finset (Fin d)) with
    ⟨φ, hφ, hφae⟩
  refine ⟨φ, hφ, ?_⟩
  filter_upwards [hφae] with ω hω i T
  exact hω i (by simp) T

/-- Helper for `Corollary_25_35::statement_repair::6`: on `[0,T]`, the dyadic predecessor
staircase of a continuous `NNReal`-weight converges pointwise back to the original weight. -/
private theorem tendstoPartitionPredecessorPointDyadicLocal
    (T : NNReal) :
    Tendsto
      (fun n : ℕ ↦
        partitionPredecessorPoint Definition2158.dyadicPartitionSequence n T)
      atTop
      (𝓝 T) := by
  refine Metric.tendsto_atTop.mpr ?_
  intro ε hε
  let ε' : ℝ := ε / 2
  have hε' : 0 < ε' := by
    dsimp [ε']
    linarith
  have hmesh :
      ∀ᶠ n in atTop, partitionMesh Definition2158.dyadicPartitionSequence n ≤ ENNReal.ofReal ε' := by
    rcases
        (ENNReal.tendsto_atTop_zero.mp
          Definition2158.tendsto_partitionMesh_dyadicPartitionSequence)
          (ENNReal.ofReal ε') (ENNReal.ofReal_pos.mpr hε') with
      ⟨N, hN⟩
    exact Filter.eventually_atTop.2 ⟨N, hN⟩
  rcases Filter.eventually_atTop.1 hmesh with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hedist :
      edist
          (partitionPredecessorPoint Definition2158.dyadicPartitionSequence n T)
          T ≤
        ENNReal.ofReal ε' := by
    exact
      (partitionPredecessorPointWithinMesh Definition2158.dyadicPartitionSequence n T).trans
        (hN n hn)
  have hdist :
      dist
          (partitionPredecessorPoint Definition2158.dyadicPartitionSequence n T)
          T ≤
        ε' := by
    exact (ENNReal.ofReal_le_ofReal_iff hε'.le).mp (by simpa [edist_dist] using hedist)
  calc
    dist
        (partitionPredecessorPoint Definition2158.dyadicPartitionSequence n T)
        T ≤
      ε' := hdist
    _ < ε := by
      dsimp [ε']
      linarith

/-- Helper for `Corollary_25_35::statement_repair::6`: on `[0,T]`, the dyadic predecessor
staircase of a continuous `NNReal`-weight converges pointwise back to the original weight. -/
private theorem tendstoCoarseIccStepOfContinuousLocal
    (w : NNReal → ℝ) (hw : Continuous w)
    (T s : NNReal) (hs : s ∈ Set.Icc 0 T) :
    Tendsto
      (fun n : ℕ ↦
        coarseIccStep w Definition2158.dyadicPartitionSequence n T s)
      atTop
      (𝓝 (w s)) := by
  have hpred :
      Tendsto
        (fun n : ℕ ↦
          partitionPredecessorPoint Definition2158.dyadicPartitionSequence n s)
        atTop
        (𝓝 s) :=
    tendstoPartitionPredecessorPointDyadicLocal s
  -- Proof comment: the coarse staircase samples `w` at the predecessor dyadic grid point, and
  -- those predecessor points converge back to the evaluation time `s`.
  refine (hw.continuousAt.tendsto.comp hpred).congr' ?_
  filter_upwards with n
  simpa using
    (coarseIccStep_eq_partitionPredecessorValue
      w
      Definition2158.dyadicPartitionSequence
      n
      T
      s
      hs).symm

/-- Helper for `Corollary_25_35::statement_repair::6`: each dyadic predecessor staircase is
measurable because it is a finite linear combination of interval indicators. -/
private theorem measurableCoarseIccStepLocal
    (w : NNReal → ℝ) (T : NNReal) (n : ℕ) :
    Measurable (coarseIccStep w Definition2158.dyadicPartitionSequence n T) := by
  -- Proof comment: unfolding the staircase leaves only constants, finite sums, and measurable
  -- interval indicators.
  unfold coarseIccStep
  refine measurable_const.add ?_
  refine Finset.measurable_sum _ ?_
  intro i hi
  exact measurable_const.mul (measurable_const.indicator measurableSet_Icc)

/-- Helper for `Corollary_25_35::statement_repair::6`: continuity on the compact interval
`[0,T]` gives one uniform bound for every dyadic predecessor staircase sample. -/
private theorem coarseIccStepAbsLeOfContinuousLocal
    (w : NNReal → ℝ) (hw : Continuous w)
    (T : NNReal) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ n : ℕ, ∀ s ∈ Set.Icc 0 T,
        |coarseIccStep w Definition2158.dyadicPartitionSequence n T s| ≤ C) ∧
      ∀ s ∈ Set.Icc 0 T, |w s| ≤ C := by
  obtain ⟨C, hC⟩ :
      ∃ C : ℝ, ∀ u ∈ Set.Icc (0 : NNReal) T, ‖w u‖ ≤ C :=
    (isCompact_Icc : IsCompact (Set.Icc (0 : NNReal) T)).exists_bound_of_continuousOn
      hw.continuousOn
  have hC_nonneg : 0 ≤ C := by
    have hzero : ‖w 0‖ ≤ C := hC 0 (by simp : (0 : NNReal) ∈ Set.Icc (0 : NNReal) T)
    exact le_trans (by simp) hzero
  refine ⟨C, hC_nonneg, ?_, ?_⟩
  · intro n s hs
    have hpred_mem :
        partitionPredecessorPoint Definition2158.dyadicPartitionSequence n s ∈
          Set.Icc (0 : NNReal) T := by
      exact
        ⟨bot_le,
          le_trans
            (partitionPredecessorPoint_le_time
              Definition2158.dyadicPartitionSequence
              n
              s)
            hs.2⟩
    -- Proof comment: each staircase value is exactly the predecessor-point sample of `w`.
    rw [coarseIccStep_eq_partitionPredecessorValue
      w
      Definition2158.dyadicPartitionSequence
      n
      T
      s
      hs]
    simpa [Real.norm_eq_abs] using hC _ hpred_mem
  · intro s hs
    simpa [Real.norm_eq_abs] using hC s hs

/-- Helper for `Corollary_25_35::statement_repair::6`: integrating the dyadic predecessor
staircases of a continuous weight against a finite measure on `[0,T]` converges to the original
integral. -/
private theorem tendstoSetIntegralCoarseIccStepOfContinuousLocal
    (w : NNReal → ℝ) (hw : Continuous w)
    {ν : Measure NNReal} (T : NNReal)
    (hνFinite : ν (Set.Icc 0 T) < ⊤) :
    Tendsto
      (fun m : ℕ ↦
        ∫ s in Set.Icc 0 T,
          coarseIccStep w Definition2158.dyadicPartitionSequence m T s ∂ν)
      atTop
      (𝓝 (∫ s in Set.Icc 0 T, w s ∂ν)) := by
  let νT : Measure NNReal := ν.restrict (Set.Icc 0 T)
  have hνT_univ_lt_top : νT Set.univ < ⊤ := by
    simpa [νT] using hνFinite
  letI : IsFiniteMeasure νT := ⟨hνT_univ_lt_top⟩
  obtain ⟨C, _hC_nonneg, hbound, _hlimitBound⟩ :=
    coarseIccStepAbsLeOfContinuousLocal w hw T
  have hmeas :
      ∀ n : ℕ,
        AEStronglyMeasurable
          (fun s : NNReal ↦
            coarseIccStep w Definition2158.dyadicPartitionSequence n T s)
          νT := by
    intro n
    exact (measurableCoarseIccStepLocal w T n).aestronglyMeasurable
  have hboundAE :
      ∀ n : ℕ,
        ∀ᵐ s ∂νT,
          ‖coarseIccStep w Definition2158.dyadicPartitionSequence n T s‖ ≤
            (fun _ : NNReal ↦ C) s := by
    intro n
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    simpa [Real.norm_eq_abs] using hbound n s hs
  have hlimAE :
      ∀ᵐ s ∂νT,
        Tendsto
          (fun n : ℕ ↦
            coarseIccStep w Definition2158.dyadicPartitionSequence n T s)
          atTop
          (𝓝 (w s)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact tendstoCoarseIccStepOfContinuousLocal w hw T s hs
  -- Proof comment: after restricting to the finite interval measure, dominated convergence
  -- applies because the staircases are uniformly bounded and converge pointwise on `[0,T]`.
  simpa [νT] using
    (MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun _ : NNReal ↦ C)
      hmeas
      (integrable_const C)
      hboundAE
      hlimAE)

/-- Helper for `Corollary_25_35::statement_repair::6`: pushing a measure on `NNReal` forward to
`ℝ` along coercion preserves interval integrals after rewriting the integrand through
`Real.toNNReal`. -/
private theorem setIntegralMapCoeEqSetIntegralIccLocal
    {ν : Measure NNReal} (H : NNReal → ℝ) (T : NNReal) :
    ∫ s in Set.Icc (0 : ℝ) (T : ℝ), H s.toNNReal ∂(Measure.map ((↑) : NNReal → ℝ) ν) =
      ∫ s in Set.Icc 0 T, H s ∂ν := by
  -- Proof comment: rewrite the real integral as an unrestricted indicator integral, transport it
  -- across `Measure.map`, and simplify the indicator back on `NNReal`.
  calc
    ∫ s in Set.Icc (0 : ℝ) (T : ℝ), H s.toNNReal ∂(Measure.map ((↑) : NNReal → ℝ) ν)
        =
      ∫ s : ℝ,
        Set.indicator (Set.Icc (0 : ℝ) (T : ℝ)) (fun s ↦ H s.toNNReal) s
          ∂(Measure.map ((↑) : NNReal → ℝ) ν) := by
          rw [← MeasureTheory.integral_indicator measurableSet_Icc]
    _ =
      ∫ s : NNReal,
        Set.indicator (Set.Icc (0 : ℝ) (T : ℝ)) (fun s ↦ H s.toNNReal) (s : ℝ) ∂ν := by
          rw [NNReal.isClosedEmbedding_coe.integral_map]
    _ = ∫ s : NNReal, Set.indicator (Set.Icc 0 T) H s ∂ν := by
          refine integral_congr_ae ?_
          filter_upwards with s
          by_cases hsT : s ≤ T
          · simp [Set.indicator, hsT]
          · simp [Set.indicator, hsT]
    _ = ∫ s in Set.Icc 0 T, H s ∂ν := by
          rw [MeasureTheory.integral_indicator measurableSet_Icc]

/-- Helper for `Corollary_25_35::statement_repair::6`: integrating a continuous weight against the
deterministic time path `s ↦ s` is the ordinary interval integral of that weight. -/
private theorem hasPathwiseItoIntegralAlong_timePath_of_continuous
    (w : NNReal → ℝ) (hw : Continuous w) :
    HasPathwiseItoIntegralAlong
      w
      (⟨fun s ↦ (s : ℝ), continuous_subtype_val⟩ : C(NNReal, ℝ))
      Definition2158.dyadicPartitionSequence
      (fun T ↦ ∫ s in Set.Icc (0 : ℝ) (T : ℝ), w s.toNNReal) := by
  intro T
  have hUnitInt :
      IntegrableOn (fun _ : ℝ ↦ (1 : ℝ)) (Set.Icc (0 : ℝ) (T : ℝ)) := by
    exact
      integrableOn_const
        (μ := volume)
        (s := Set.Icc (0 : ℝ) (T : ℝ))
        (C := (1 : ℝ))
        (by simp [Real.volume_Icc])
  let timePrimitive : C(NNReal, ℝ) :=
    indefiniteIntegralPath (Set.indicator (Set.Icc (0 : ℝ) (T : ℝ)) fun _ ↦ (1 : ℝ))
  have htimeEq :
      Set.EqOn
        (fun s : NNReal ↦ (s : ℝ))
        (fun s : NNReal ↦ timePrimitive s)
        (Set.Icc 0 T) := by
    intro s hs
    -- Proof comment: on `[0,T]`, the truncated primitive of the constant density `1` is exactly
    -- the deterministic time path.
    simpa [timePrimitive, Real.volume_Icc] using
      (indefiniteIntegralPath_indicatorIcc_apply
        (f := fun _ ↦ (1 : ℝ))
        (T := T)
        (x := s)
        hUnitInt
        hs.2).symm
  have hRowsEq :
      partitionPathwiseItoApproximationUpTo
          w
          (⟨fun s ↦ (s : ℝ), continuous_subtype_val⟩ : C(NNReal, ℝ))
          Definition2158.dyadicPartitionSequence
          T
        =
      partitionPathwiseItoApproximationUpTo
          w
          timePrimitive
          Definition2158.dyadicPartitionSequence
          T := by
    funext m
    -- Proof comment: every active endpoint of the truncated row lies in `[0,T]`, so replacing
    -- the time path by the truncated primitive does not change the finite partition sum.
    rw [partitionPathwiseItoApproximationUpTo, partitionPathwiseItoApproximationUpTo]
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hk_mem :
        Definition2158.dyadicPartitionSequence m k ∈ Set.Icc 0 T :=
      partitionPoint_mem_Icc_of_lt_partitionBoundIndex
        Definition2158.dyadicPartitionSequence
        m
        k
        T
        (Finset.mem_range.mp hk)
    have hnext_mem :
        partitionNextPointUpTo Definition2158.dyadicPartitionSequence m k T ∈ Set.Icc 0 T := by
      constructor
      · exact bot_le
      · simp [partitionNextPointUpTo]
    rw [htimeEq hk_mem, htimeEq hnext_mem]
  have hRowsIntegral :
      partitionPathwiseItoApproximationUpTo
          w
          (⟨fun s ↦ (s : ℝ), continuous_subtype_val⟩ : C(NNReal, ℝ))
          Definition2158.dyadicPartitionSequence
          T
        =
      fun m : ℕ ↦
        ∫ s in Set.Icc (0 : ℝ) (T : ℝ),
          (1 : ℝ) * coarseIccStep w Definition2158.dyadicPartitionSequence m T s.toNNReal := by
    funext m
    calc
      partitionPathwiseItoApproximationUpTo
          w
          (⟨fun s ↦ (s : ℝ), continuous_subtype_val⟩ : C(NNReal, ℝ))
          Definition2158.dyadicPartitionSequence
          T
          m
          =
        partitionPathwiseItoApproximationUpTo
          w
          timePrimitive
          Definition2158.dyadicPartitionSequence
          T
          m := congrFun hRowsEq m
      _ =
        w (Definition2158.dyadicPartitionSequence m
              (partitionBoundIndex Definition2158.dyadicPartitionSequence m T - 1)) *
            (∫ s in Set.Icc (0 : ℝ) (T : ℝ), (1 : ℝ)) +
          Finset.sum
            (Finset.range
              (partitionBoundIndex Definition2158.dyadicPartitionSequence m T - 1))
            (fun k ↦
              (w (Definition2158.dyadicPartitionSequence m k) -
                  w (Definition2158.dyadicPartitionSequence m (k + 1))) *
                (∫ s in Set.Icc (0 : ℝ)
                    (Definition2158.dyadicPartitionSequence m (k + 1) : ℝ),
                  (1 : ℝ))) := by
            simpa [timePrimitive] using
              (partitionPathwiseItoApproximationUpTo_indicatorIcc_eq_linearCombination_of_prefixIntegral
                (H := w)
                (f := fun _ ↦ (1 : ℝ))
                (T := T)
                hUnitInt
                m)
      _ =
        ∫ s in Set.Icc (0 : ℝ) (T : ℝ),
          (1 : ℝ) * coarseIccStep w Definition2158.dyadicPartitionSequence m T s.toNNReal := by
            symm
            simpa using
              (coarseIccStep_intervalIntegral_eq_linearCombination_of_prefixIntegral
                (H := w)
                (f := fun _ ↦ (1 : ℝ))
                (T := T)
                hUnitInt
                m)
  have hwReal : Continuous fun s : ℝ ↦ w s.toNNReal := by
    exact hw.comp continuous_real_toNNReal
  -- Proof comment: the time-row partition sums are exactly the coarse-staircase interval
  -- integrals, and those converge by the compact-horizon dominated-convergence theorem.
  rw [hRowsIntegral]
  simpa [one_mul] using
    (tendsto_intervalIntegral_mul_coarseIccStep_of_continuous
      (H := w)
      hwReal
      (f := fun _ ↦ (1 : ℝ))
      (T := T)
      hUnitInt)

/-- Helper for `Corollary_25_35::statement_repair::6`: the canonical dyadic Itô integral along the
deterministic time path is the ordinary interval integral of the continuous weight. -/
private theorem pathwiseItoIntegralAlong_timePath_eq_intervalIntegral_of_continuous
    (w : NNReal → ℝ) (hw : Continuous w) :
    pathwiseItoIntegralAlong
        w
        (⟨fun s ↦ (s : ℝ), continuous_subtype_val⟩ : C(NNReal, ℝ))
        Definition2158.dyadicPartitionSequence
      =
      fun T ↦ ∫ s in Set.Icc (0 : ℝ) (T : ℝ), w s.toNNReal :=
  (hasPathwiseItoIntegralAlong_timePath_of_continuous (w := w) hw).eq_pathwiseItoIntegralAlong

/-- Helper for `Corollary_25_35::statement_repair::6`: the time-space function `F(x,t)` viewed on
the `(d+1)`-dimensional Euclidean graph model by using the last coordinate as the time variable. -/
private noncomputable def timeSpaceGraphLift
    (F : EuclideanSpace ℝ (Fin d) × ℝ → ℝ) :
    EuclideanSpace ℝ (Fin (d + 1)) → ℝ :=
  fun z ↦
    F
      (WithLp.toLp 2 (fun i : Fin d ↦ z (Fin.castSucc i)),
        z (Fin.last d))

/-- Helper for `Corollary_25_35::statement_repair::6`: forgetting the last coordinate of the
graph model recovers the spatial `ℝ^d` point. -/
private noncomputable def timeSpaceGraphSpatialPart
    (z : EuclideanSpace ℝ (Fin (d + 1))) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 fun i : Fin d ↦ z (Fin.castSucc i)

/-- Helper for `Corollary_25_35::statement_repair::6`: the spatial projection of the graph model
just reads off the corresponding nonterminal coordinate. -/
private theorem timeSpaceGraphSpatialPart_apply
    (z : EuclideanSpace ℝ (Fin (d + 1))) (i : Fin d) :
    timeSpaceGraphSpatialPart z i = z (Fin.castSucc i) := by
  -- Proof comment: `timeSpaceGraphSpatialPart` is defined by `WithLp.toLp` on the first `d`
  -- coordinates, so evaluating at `i` recovers the `i.castSucc` coordinate of `z`.
  simp [timeSpaceGraphSpatialPart, PiLp.toLp_apply]

/-- Helper for `Corollary_25_35::statement_repair::6`: the graph lift is the original
time-space function evaluated on the split spatial and time coordinates. -/
private theorem timeSpaceGraphLift_eq
    (F : EuclideanSpace ℝ (Fin d) × ℝ → ℝ)
    (z : EuclideanSpace ℝ (Fin (d + 1))) :
    timeSpaceGraphLift F z = F (timeSpaceGraphSpatialPart z, z (Fin.last d)) := by
  -- Proof comment: unfold the graph lift and identify the `WithLp.toLp` term with the dedicated
  -- spatial projection helper.
  simp [timeSpaceGraphLift, timeSpaceGraphSpatialPart]

/-- Helper for `Corollary_25_35::statement_repair::6`: the spatial projection from the graph
model is continuous. -/
private theorem continuous_timeSpaceGraphSpatialPart :
    Continuous (timeSpaceGraphSpatialPart (d := d)) := by
  -- Proof comment: the graph-space projection is `WithLp.toLp` applied to the continuous family
  -- of nonterminal coordinate maps.
  simpa [timeSpaceGraphSpatialPart] using
    (PiLp.continuous_toLp 2 (fun _ : Fin d ↦ ℝ)).comp
      (continuous_pi fun i ↦ continuous_apply (Fin.castSucc i))

/-- Helper for `Corollary_25_35::statement_repair::6`: moving only the `i`-th spatial graph
coordinate corresponds to moving the `i`-th spatial coordinate of `F` while freezing time. -/
private theorem timeSpaceGraphLift_spaceLine_eq
    (F : EuclideanSpace ℝ (Fin d) × ℝ → ℝ)
    (z : EuclideanSpace ℝ (Fin (d + 1))) (i : Fin d) :
    (fun s : ℝ ↦
      timeSpaceGraphLift F
        (z + EuclideanSpace.single (Fin.castSucc i) (s - z (Fin.castSucc i)))) =
      (fun s : ℝ ↦
        F
          (timeSpaceGraphSpatialPart z +
              EuclideanSpace.single i (s - timeSpaceGraphSpatialPart z i),
            z (Fin.last d))) := by
  -- Proof comment: the graph lift only sees the first `d` coordinates through the spatial part,
  -- and a spatial axis update leaves the terminal time coordinate unchanged.
  funext s
  rw [timeSpaceGraphLift_eq]
  congr 1
  · ext j
    by_cases hji : j = i
    · subst hji
      simp [timeSpaceGraphSpatialPart_apply]
    · simp [timeSpaceGraphSpatialPart_apply, EuclideanSpace.single, hji]
  · simp [EuclideanSpace.single, Fin.castSucc_ne_last]

/-- Helper for `Corollary_25_35::statement_repair::6`: moving the last graph coordinate is the
same as moving only the time variable of `F`. -/
private theorem timeSpaceGraphLift_timeLine_eq
    (F : EuclideanSpace ℝ (Fin d) × ℝ → ℝ)
    (z : EuclideanSpace ℝ (Fin (d + 1))) :
    (fun s : ℝ ↦
      timeSpaceGraphLift F
        (z + EuclideanSpace.single (Fin.last d) (s - z (Fin.last d)))) =
      (fun s : ℝ ↦ F (timeSpaceGraphSpatialPart z, s)) := by
  -- Proof comment: updating the distinguished last coordinate changes only the time entry of the
  -- graph lift, while every spatial coordinate stays fixed.
  funext s
  rw [timeSpaceGraphLift_eq]
  congr 1
  · ext i
    simp [timeSpaceGraphSpatialPart_apply, EuclideanSpace.single, Fin.castSucc_ne_last]
  · simp [EuclideanSpace.single]

/-- Helper for `Corollary_25_35::statement_repair::6`: the graph lift inherits the spatial
coordinate-line derivative data of `F`. -/
private theorem timeSpaceGraphLift_hasDerivAt_space
    (F : EuclideanSpace ℝ (Fin d) × ℝ → ℝ)
    (hF : IsTimeSpaceC21 F)
    (i : Fin d) (z : EuclideanSpace ℝ (Fin (d + 1))) :
    HasDerivAt
      (fun s : ℝ ↦
        timeSpaceGraphLift F
          (z + EuclideanSpace.single (Fin.castSucc i) (s - z (Fin.castSucc i))))
      ((∂[i] fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, z (Fin.last d)))
        (timeSpaceGraphSpatialPart z))
      (z (Fin.castSucc i)) := by
  -- Proof comment: after rewriting the graph-axis line to the corresponding spatial line of `F`,
  -- the `C^{2,1}` assumption supplies the derivative directly.
  simpa [timeSpaceGraphLift_spaceLine_eq, timeSpaceGraphSpatialPart_apply] using
    hF.hasDerivAt_space i (timeSpaceGraphSpatialPart z, z (Fin.last d))

/-- Helper for `Corollary_25_35::statement_repair::6`: the spatial partials of the graph lift are
exactly the spatial partials of `F` evaluated at the split graph point. -/
private theorem timeSpaceGraphLift_spacePartialDeriv
    (F : EuclideanSpace ℝ (Fin d) × ℝ → ℝ)
    (hF : IsTimeSpaceC21 F)
    (i : Fin d) (z : EuclideanSpace ℝ (Fin (d + 1))) :
    (∂[Fin.castSucc i] (timeSpaceGraphLift F)) z =
      (∂[i] fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, z (Fin.last d)))
        (timeSpaceGraphSpatialPart z) := by
  -- Proof comment: the previous coordinate-line derivative identifies the derivative value, and
  -- `partialDeriv` is defined from that one-variable derivative.
  exact (timeSpaceGraphLift_hasDerivAt_space F hF i z).deriv

/-- Helper for `Corollary_25_35::statement_repair::6`: the graph lift inherits the time-line
derivative data of `F` along the last coordinate. -/
private theorem timeSpaceGraphLift_hasDerivAt_time
    (F : EuclideanSpace ℝ (Fin d) × ℝ → ℝ)
    (hF : IsTimeSpaceC21 F)
    (z : EuclideanSpace ℝ (Fin (d + 1))) :
    HasDerivAt
      (fun s : ℝ ↦
        timeSpaceGraphLift F
          (z + EuclideanSpace.single (Fin.last d) (s - z (Fin.last d))))
      ((∂ₜ F) (timeSpaceGraphSpatialPart z, z (Fin.last d)))
      (z (Fin.last d)) := by
  -- Proof comment: the last coordinate line of the graph model is exactly the frozen-space time
  -- slice of `F`, so the time derivative field from `IsTimeSpaceC21` applies verbatim.
  simpa [timeSpaceGraphLift_timeLine_eq] using
    hF.hasDerivAt_time (timeSpaceGraphSpatialPart z, z (Fin.last d))

/-- Helper for `Corollary_25_35::statement_repair::6`: the last-coordinate partial derivative of
the graph lift is the time derivative `∂ₜ F`. -/
private theorem timeSpaceGraphLift_timePartialDeriv
    (F : EuclideanSpace ℝ (Fin d) × ℝ → ℝ)
    (hF : IsTimeSpaceC21 F)
    (z : EuclideanSpace ℝ (Fin (d + 1))) :
    (∂[Fin.last d] (timeSpaceGraphLift F)) z =
      (∂ₜ F) (timeSpaceGraphSpatialPart z, z (Fin.last d)) := by
  -- Proof comment: just as for the spatial coordinates, the time partial is recovered from the
  -- one-variable derivative along the distinguished last axis.
  exact (timeSpaceGraphLift_hasDerivAt_time F hF z).deriv

/-- Helper for `Corollary_25_35::statement_repair::6`: the spatial first partial of the graph
lift varies along a second spatial axis exactly like the corresponding frozen-time partial of
`F`. -/
private theorem timeSpaceGraphLift_spacePartialLine_eq
    (F : EuclideanSpace ℝ (Fin d) × ℝ → ℝ)
    (hF : IsTimeSpaceC21 F)
    (i j : Fin d) (z : EuclideanSpace ℝ (Fin (d + 1))) :
    (fun s : ℝ ↦
      (∂[Fin.castSucc i] (timeSpaceGraphLift F))
        (z + EuclideanSpace.single (Fin.castSucc j) (s - z (Fin.castSucc j)))) =
      (fun s : ℝ ↦
        (∂[i] fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, z (Fin.last d)))
          (timeSpaceGraphSpatialPart z +
            EuclideanSpace.single j (s - timeSpaceGraphSpatialPart z j))) := by
  -- Proof comment: the first graph-lift spatial partial already identifies pointwise with the
  -- frozen-time spatial partial of `F`, so moving a second spatial coordinate preserves that
  -- identification.
  funext s
  rw [timeSpaceGraphLift_spacePartialDeriv F hF i
    (z + EuclideanSpace.single (Fin.castSucc j) (s - z (Fin.castSucc j)))]
  congr 1
  · ext k
    by_cases hkj : k = j
    · subst hkj
      simp [timeSpaceGraphSpatialPart_apply]
    · simp [timeSpaceGraphSpatialPart_apply, EuclideanSpace.single, hkj]
  · simp [EuclideanSpace.single, Fin.castSucc_ne_last]

/-- Helper for `Corollary_25_35::statement_repair::6`: the graph lift inherits the second spatial
coordinate-line derivative data of `F`. -/
private theorem timeSpaceGraphLift_hasDerivAt_spaceSecond
    (F : EuclideanSpace ℝ (Fin d) × ℝ → ℝ)
    (hF : IsTimeSpaceC21 F)
    (i j : Fin d) (z : EuclideanSpace ℝ (Fin (d + 1))) :
    HasDerivAt
      (fun s : ℝ ↦
        (∂[Fin.castSucc i] (timeSpaceGraphLift F))
          (z + EuclideanSpace.single (Fin.castSucc j) (s - z (Fin.castSucc j))))
      ((∂²[i, j] fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, z (Fin.last d)))
        (timeSpaceGraphSpatialPart z))
      (z (Fin.castSucc j)) := by
  -- Proof comment: once the first graph-lift partial is rewritten to the frozen-time first
  -- spatial partial of `F`, the `C^{2,1}` assumption supplies the second derivative along the
  -- `j`-th spatial axis.
  simpa [timeSpaceGraphLift_spacePartialLine_eq, timeSpaceGraphSpatialPart_apply] using
    hF.hasDerivAt_spaceSecond i j (timeSpaceGraphSpatialPart z, z (Fin.last d))

/-- Helper for `Corollary_25_35::statement_repair::6`: the graph lift inherits the spatial second
partials of `F` on the nonterminal coordinates. -/
private theorem timeSpaceGraphLift_spaceSecondPartialDeriv
    (F : EuclideanSpace ℝ (Fin d) × ℝ → ℝ)
    (hF : IsTimeSpaceC21 F)
    (i j : Fin d) (z : EuclideanSpace ℝ (Fin (d + 1))) :
    (∂²[Fin.castSucc i, Fin.castSucc j] (timeSpaceGraphLift F)) z =
      (∂²[i, j] fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, z (Fin.last d)))
        (timeSpaceGraphSpatialPart z) := by
  -- Proof comment: the second graph-lift spatial partial is again the derivative value from the
  -- corresponding one-variable coordinate-line computation.
  exact (timeSpaceGraphLift_hasDerivAt_spaceSecond F hF i j z).deriv

/-- Helper for `Corollary_25_35::statement_repair::6`: the graph-lift spatial partial fields are
continuous because they are the frozen-time spatial partial fields of `F` pulled back along the
continuous graph projection. -/
private theorem continuous_timeSpaceGraphLift_spacePartialDeriv
    (F : EuclideanSpace ℝ (Fin d) × ℝ → ℝ)
    (hF : IsTimeSpaceC21 F)
    (i : Fin d) :
    Continuous (fun z : EuclideanSpace ℝ (Fin (d + 1)) ↦
      (∂[Fin.castSucc i] (timeSpaceGraphLift F)) z) := by
  -- Proof comment: rewrite the graph-lift spatial partial to the source-space partial of `F`,
  -- then compose the stored continuity with the spatial/time projection of the graph model.
  have hBase :
      Continuous (fun z : EuclideanSpace ℝ (Fin (d + 1)) ↦
        (∂[i] fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, z (Fin.last d)))
          (timeSpaceGraphSpatialPart z)) := by
    simpa [timeSpaceGraphSpatialPart] using
      (hF.continuous_spacePartialDeriv i).comp
        (continuous_timeSpaceGraphSpatialPart.prodMk (continuous_apply (Fin.last d)))
  -- Proof comment: the explicit pointwise identity from the previous bridge turns this into the
  -- continuity statement for the graph-lift spatial partial itself.
  simpa [funext (timeSpaceGraphLift_spacePartialDeriv F hF i)] using hBase

/-- Helper for `Corollary_25_35::statement_repair::6`: the graph-lift time partial field is
continuous because it is the original time derivative pulled back along the graph projection. -/
private theorem continuous_timeSpaceGraphLift_timePartialDeriv
    (F : EuclideanSpace ℝ (Fin d) × ℝ → ℝ)
    (hF : IsTimeSpaceC21 F) :
    Continuous (fun z : EuclideanSpace ℝ (Fin (d + 1)) ↦
      (∂[Fin.last d] (timeSpaceGraphLift F)) z) := by
  -- Proof comment: compose the stored continuity of `∂ₜ F` with the continuous graph-space split,
  -- then rewrite back to the graph-lift last partial.
  have hBase :
      Continuous (fun z : EuclideanSpace ℝ (Fin (d + 1)) ↦
        (∂ₜ F) (timeSpaceGraphSpatialPart z, z (Fin.last d))) := by
    simpa [timeSpaceGraphSpatialPart] using
      hF.continuous_timePartialDeriv.comp
        (continuous_timeSpaceGraphSpatialPart.prodMk (continuous_apply (Fin.last d)))
  simpa [funext (timeSpaceGraphLift_timePartialDeriv F hF)] using hBase

/-- Helper for `Corollary_25_35::statement_repair::6`: the graph-lift spatial second partial
fields are continuous because they are the frozen-time second partials of `F` pulled back along
the graph projection. -/
private theorem continuous_timeSpaceGraphLift_spaceSecondPartialDeriv
    (F : EuclideanSpace ℝ (Fin d) × ℝ → ℝ)
    (hF : IsTimeSpaceC21 F)
    (i j : Fin d) :
    Continuous (fun z : EuclideanSpace ℝ (Fin (d + 1)) ↦
      (∂²[Fin.castSucc i, Fin.castSucc j] (timeSpaceGraphLift F)) z) := by
  -- Proof comment: this is the same pullback argument as for the first partials, now using the
  -- stored continuity of the second spatial partial field of `F`.
  have hBase :
      Continuous (fun z : EuclideanSpace ℝ (Fin (d + 1)) ↦
        (∂²[i, j] fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, z (Fin.last d)))
          (timeSpaceGraphSpatialPart z)) := by
    simpa [timeSpaceGraphSpatialPart] using
      (hF.continuous_spaceSecondPartialDeriv i j).comp
        (continuous_timeSpaceGraphSpatialPart.prodMk (continuous_apply (Fin.last d)))
  simpa [funext (timeSpaceGraphLift_spaceSecondPartialDeriv F hF i j)] using hBase

/-- Helper for `Corollary_25_35::statement_repair::6`: the graph point `(Wc_t, t)` of the
canonical continuous Brownian version in the `(d+1)`-dimensional Euclidean model. -/
private noncomputable def timeSpaceGraphPoint
    {W : NNReal → Ω → EuclideanSpace ℝ (Fin d)}
    (hW : IsStandardBrownianMotionVector μ W) (t : NNReal) (ω : Ω) :
    EuclideanSpace ℝ (Fin (d + 1)) :=
  WithLp.toLp 2 fun i : Fin (d + 1) ↦
    Fin.lastCases (motive := fun _ ↦ ℝ)
      (t : ℝ)
      (fun j : Fin d ↦ (standardBrownianMotionVectorContinuousVersion hW t ω).ofLp j)
      i

/-- Helper for `Corollary_25_35::statement_repair::6`: the spatial coordinates of the graph path
`(Wc_t, t)` are exactly the coordinates of the canonical continuous Brownian version. -/
private theorem timeSpaceGraphPoint_castSucc
    {W : NNReal → Ω → EuclideanSpace ℝ (Fin d)}
    (hW : IsStandardBrownianMotionVector μ W) (t : NNReal) (ω : Ω) (i : Fin d) :
    timeSpaceGraphPoint (μ := μ) hW t ω (Fin.castSucc i) =
      (standardBrownianMotionVectorContinuousVersion hW t ω).ofLp i := by
  -- Proof comment: evaluating the graph point on a spatial coordinate just selects the matching
  -- Brownian coordinate from the `Fin.lastCases` split.
  simp [timeSpaceGraphPoint]

/-- Helper for `Corollary_25_35::statement_repair::6`: forgetting the last coordinate of the graph
point `(Wc_t, t)` recovers the Brownian state `Wc_t`. -/
private theorem timeSpaceGraphSpatialPart_timeSpaceGraphPoint
    {W : NNReal → Ω → EuclideanSpace ℝ (Fin d)}
    (hW : IsStandardBrownianMotionVector μ W) (t : NNReal) (ω : Ω) :
    timeSpaceGraphSpatialPart (timeSpaceGraphPoint (μ := μ) hW t ω) =
      standardBrownianMotionVectorContinuousVersion hW t ω := by
  -- Proof comment: compare the two state vectors coordinatewise and use the graph-point
  -- coordinate identity on each spatial slot.
  ext i
  simp [timeSpaceGraphSpatialPart_apply, timeSpaceGraphPoint_castSucc]

/-- Helper for `Corollary_25_35::statement_repair::6`: the last coordinate of the graph path
`(Wc_t, t)` is the deterministic time coordinate. -/
private theorem timeSpaceGraphPoint_last
    {W : NNReal → Ω → EuclideanSpace ℝ (Fin d)}
    (hW : IsStandardBrownianMotionVector μ W) (t : NNReal) (ω : Ω) :
    timeSpaceGraphPoint (μ := μ) hW t ω (Fin.last d) = (t : ℝ) := by
  -- Proof comment: on the distinguished last coordinate, `Fin.lastCases` returns the time input.
  simp [timeSpaceGraphPoint]

/-- Helper for `Corollary_25_35::statement_repair::6`: for each sample point `ω`, the graph path
`t ↦ (Wc_t, t)` is continuous. -/
private theorem timeSpaceGraphPath_continuous
    {W : NNReal → Ω → EuclideanSpace ℝ (Fin d)}
    (hW : IsStandardBrownianMotionVector μ W) (ω : Ω) :
    Continuous fun t : NNReal ↦ timeSpaceGraphPoint (μ := μ) hW t ω := by
  -- Proof comment: continuity of the `(d+1)`-dimensional graph path is checked coordinatewise:
  -- each spatial coordinate is a continuous Brownian coordinate path, and the last coordinate is
  -- the continuous deterministic clock.
  have hcoords :
      Continuous
        (fun t : NNReal ↦
          fun i : Fin (d + 1) ↦
            Fin.lastCases (motive := fun _ ↦ ℝ)
              (t : ℝ)
              (fun j : Fin d ↦ (standardBrownianMotionVectorContinuousVersion hW t ω).ofLp j)
              i) := by
    exact continuous_pi fun i ↦
      Fin.lastCases
        (simpa using (continuous_subtype_val : Continuous fun t : NNReal ↦ (t : ℝ)))
        (fun j ↦ by
          simpa using
            (BrownianVectorContinuousVersion.coord_isContinuousLocalMartingale (μ := μ) hW j)
              .continuous ω)
        i
  simpa [timeSpaceGraphPoint] using
    (PiLp.continuous_toLp 2 (fun _ : Fin (d + 1) ↦ ℝ)).comp hcoords

/-- Helper for `Corollary_25_35::statement_repair::6`: bundle the fixed-sample graph
path `t ↦ (Wc_t, t)` as a path in `VectorPathSpace (d + 1)`. -/
private noncomputable def timeSpaceGraphPath
    {W : NNReal → Ω → EuclideanSpace ℝ (Fin d)}
    (hW : IsStandardBrownianMotionVector μ W) (ω : Ω) :
    VectorPathSpace (d + 1) :=
  ⟨fun s ↦ timeSpaceGraphPoint (μ := μ) hW s ω,
    timeSpaceGraphPath_continuous (μ := μ) hW ω⟩

/-- Helper for `Corollary_25_35::statement_repair::6`: each coordinate path of the canonical
continuous Brownian version is continuous. -/
/-- Helper for `Corollary_25_35::statement_repair::6`: each coordinate path of the canonical
continuous Brownian version is continuous. -/
private theorem brownianContinuousCoordinate_continuous_local
    {W : NNReal → Ω → EuclideanSpace ℝ (Fin d)}
    (hW : IsStandardBrownianMotionVector μ W)
    (i : Fin d) (ω : Ω) :
    Continuous fun s ↦ (standardBrownianMotionVectorContinuousVersion hW s ω).ofLp i := by
  -- Proof comment: the coordinate path is exactly the continuous path field from the canonical
  -- continuous-local-martingale witness.
  exact
    (BrownianVectorContinuousVersion.coord_isContinuousLocalMartingale (μ := μ) hW i).continuous ω

/-- Helper for `Corollary_25_35::statement_repair::6`: the graph path components split into the
spatial Brownian coordinate paths and the deterministic time path. -/
private theorem vectorPathComponent_timeSpaceGraph_eq
    {W : NNReal → Ω → EuclideanSpace ℝ (Fin d)}
    (hW : IsStandardBrownianMotionVector μ W) (ω : Ω) :
    (∀ i : Fin d,
      vectorPathComponent
          (⟨fun s ↦ timeSpaceGraphPoint (μ := μ) hW s ω,
            timeSpaceGraphPath_continuous (μ := μ) hW ω⟩ : VectorPathSpace (d + 1))
          (Fin.castSucc i) =
        (⟨fun s ↦ (standardBrownianMotionVectorContinuousVersion hW s ω).ofLp i,
          brownianContinuousCoordinate_continuous_local (μ := μ) hW i ω⟩ : C(NNReal, ℝ))) ∧
      vectorPathComponent
          (⟨fun s ↦ timeSpaceGraphPoint (μ := μ) hW s ω,
            timeSpaceGraphPath_continuous (μ := μ) hW ω⟩ : VectorPathSpace (d + 1))
          (Fin.last d) =
        (⟨fun s ↦ (s : ℝ), continuous_subtype_val⟩ : C(NNReal, ℝ)) := by
  constructor
  · intro i
    -- Proof comment: the spatial graph-path components are definitionally the corresponding
    -- continuous Brownian coordinate paths once the coordinate selection lemma is applied.
    ext s
    simp [vectorPathComponent, timeSpaceGraphPoint_castSucc]
  · -- Proof comment: the last graph-path component is the deterministic time path.
    ext s
    simp [vectorPathComponent, timeSpaceGraphPoint_last]

/-- Helper for `Corollary_25_35::statement_repair::6`: a square-variation witness on the diagonal
is automatically a quadratic-covariation witness with itself. -/
private theorem selfCovariation_of_squareVariation_local
    {Y : C(NNReal, ℝ)} {V : NNReal → ℝ}
    (hY : HasSquareVariationAlong Y V) :
    HasQuadraticCovariationAlong Y Y V := by
  intro T
  -- Proof comment: on the diagonal the dyadic mixed sum is definitionally the dyadic square
  -- variation sum, so the same limit proves self-covariation.
  have hEq :
      partitionQuadraticCovariationSum Definition2158.dyadicPartitionSequence Y Y T =
        partitionPVariationSum Definition2158.dyadicPartitionSequence 2 Y T := by
    funext n
    simp [partitionQuadraticCovariationSum, partitionPVariationSum, sq_abs]
  simpa [dyadic_quadratic_covariation_sum, dyadic_p_variation_sum, hEq] using
    (HasSquareVariationAlong.tendsto_partition_sum hY T)

/-- Helper for `Corollary_25_35::statement_repair::6`: the dyadic mixed quadratic-covariation sum
is bounded by the geometric mean of the two dyadic square-variation sums. -/
private theorem abs_partitionQuadraticCovariationSum_le_sqrt_mul_local
    (F G : C(NNReal, ℝ)) (T : NNReal) (n : ℕ) :
    |partitionQuadraticCovariationSum Definition2158.dyadicPartitionSequence F G T n| ≤
      Real.sqrt (partitionPVariationSum Definition2158.dyadicPartitionSequence 2 F T n) *
        Real.sqrt (partitionPVariationSum Definition2158.dyadicPartitionSequence 2 G T n) := by
  let s := Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n T)
  let ΔF : ℕ → ℝ := fun k ↦
    F (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) -
      F (Definition2158.dyadicPartitionSequence n k)
  let ΔG : ℕ → ℝ := fun k ↦
    G (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) -
      G (Definition2158.dyadicPartitionSequence n k)
  have hAbs :
      |partitionQuadraticCovariationSum Definition2158.dyadicPartitionSequence F G T n| ≤
        Finset.sum s (fun k ↦ |ΔF k| * |ΔG k|) := by
    -- Proof comment: take absolute values termwise in the finite mixed-increment sum.
    simpa [partitionQuadraticCovariationSum, s, ΔF, ΔG, abs_mul] using
      (Finset.abs_sum_le_sum_abs (s := s) (f := fun k ↦ ΔF k * ΔG k))
  have hCS :
      Finset.sum s (fun k ↦ |ΔF k| * |ΔG k|) ≤
        Real.sqrt (Finset.sum s (fun k ↦ |ΔF k| ^ 2)) *
          Real.sqrt (Finset.sum s (fun k ↦ |ΔG k| ^ 2)) := by
    -- Proof comment: Cauchy-Schwarz controls the mixed increment sum by the two square sums.
    exact Real.sum_mul_le_sqrt_mul_sqrt s (fun k ↦ |ΔF k|) (fun k ↦ |ΔG k|)
  calc
    |partitionQuadraticCovariationSum Definition2158.dyadicPartitionSequence F G T n|
        ≤ Finset.sum s (fun k ↦ |ΔF k| * |ΔG k|) := hAbs
    _ ≤ Real.sqrt (Finset.sum s (fun k ↦ |ΔF k| ^ 2)) *
          Real.sqrt (Finset.sum s (fun k ↦ |ΔG k| ^ 2)) := hCS
    _ =
        Real.sqrt (partitionPVariationSum Definition2158.dyadicPartitionSequence 2 F T n) *
          Real.sqrt (partitionPVariationSum Definition2158.dyadicPartitionSequence 2 G T n) := by
          simp [partitionPVariationSum, s, ΔF, ΔG]

/-- Helper for `Corollary_25_35::statement_repair::6`: if the right path has zero square
variation, then the mixed quadratic covariation vanishes. -/
private theorem hasQuadraticCovariationAlong_zero_of_rightZeroSquareVariation_local
    {F G : C(NNReal, ℝ)} {VF : NNReal → ℝ}
    (hVF : HasSquareVariationAlong F VF)
    (hG : HasSquareVariationAlong G 0) :
    HasQuadraticCovariationAlong F G 0 := by
  intro T
  have hFsqrt :
      Tendsto (fun n ↦ Real.sqrt (dyadic_p_variation_sum 2 F T n))
        atTop
        (nhds (Real.sqrt (VF T))) := by
    -- Proof comment: the square-variation limit of `F` passes through continuity of `sqrt`.
    exact
      Real.continuous_sqrt.continuousAt.tendsto.comp
        (HasSquareVariationAlong.tendsto_partition_sum hVF T)
  have hGsqrt :
      Tendsto (fun n ↦ Real.sqrt (dyadic_p_variation_sum 2 G T n))
        atTop
        (nhds 0) := by
    -- Proof comment: the zero square-variation witness forces the right square-root factor to
    -- converge to `0`.
    simpa using
      (Real.continuous_sqrt.continuousAt.tendsto.comp
        (HasSquareVariationAlong.tendsto_partition_sum hG T))
  have hBound :
      Tendsto
        (fun n ↦
          Real.sqrt (dyadic_p_variation_sum 2 F T n) *
            Real.sqrt (dyadic_p_variation_sum 2 G T n))
        atTop
        (nhds 0) := by
    -- Proof comment: the geometric-mean bound tends to `0` because the right factor does.
    simpa [Real.sqrt_zero] using hFsqrt.mul hGsqrt
  exact
    (tendsto_zero_iff_norm_tendsto_zero).2 <| by
      simpa [Real.norm_eq_abs] using
        (squeeze_zero
          (fun n ↦ abs_nonneg _)
          (fun n ↦ abs_partitionQuadraticCovariationSum_le_sqrt_mul_local F G T n)
          hBound)

/-- Helper for `Corollary_25_35::statement_repair::6`: if the left path has zero square
variation, then the mixed quadratic covariation vanishes. -/
private theorem hasQuadraticCovariationAlong_zero_of_leftZeroSquareVariation_local
    {F G : C(NNReal, ℝ)} {VG : NNReal → ℝ}
    (hF : HasSquareVariationAlong F 0)
    (hVG : HasSquareVariationAlong G VG) :
    HasQuadraticCovariationAlong F G 0 := by
  intro T
  have hFsqrt :
      Tendsto (fun n ↦ Real.sqrt (dyadic_p_variation_sum 2 F T n))
        atTop
        (nhds 0) := by
    -- Proof comment: the zero square-variation witness kills the left square-root factor.
    simpa using
      (Real.continuous_sqrt.continuousAt.tendsto.comp
        (HasSquareVariationAlong.tendsto_partition_sum hF T))
  have hGsqrt :
      Tendsto (fun n ↦ Real.sqrt (dyadic_p_variation_sum 2 G T n))
        atTop
        (nhds (Real.sqrt (VG T))) := by
    -- Proof comment: the square-variation limit of `G` again passes through continuity of
    -- `sqrt`.
    exact
      Real.continuous_sqrt.continuousAt.tendsto.comp
        (HasSquareVariationAlong.tendsto_partition_sum hVG T)
  have hBound :
      Tendsto
        (fun n ↦
          Real.sqrt (dyadic_p_variation_sum 2 F T n) *
            Real.sqrt (dyadic_p_variation_sum 2 G T n))
        atTop
        (nhds 0) := by
    -- Proof comment: now the left geometric-mean factor tends to `0`.
    simpa [Real.sqrt_zero] using hFsqrt.mul hGsqrt
  exact
    (tendsto_zero_iff_norm_tendsto_zero).2 <| by
      simpa [Real.norm_eq_abs] using
        (squeeze_zero
          (fun n ↦ abs_nonneg _)
          (fun n ↦ abs_partitionQuadraticCovariationSum_le_sqrt_mul_local F G T n)
          hBound)

/-- Helper for `Corollary_25_35::statement_repair::6`: the deterministic time path has locally
bounded variation on `[0,\infty)`. -/
private theorem deterministicTimePath_locallyBoundedVariation :
    LocallyBoundedVariationOn
      ((⟨fun s ↦ (s : ℝ), continuous_subtype_val⟩ : C(NNReal, ℝ)) : NNReal → ℝ)
      Set.univ := by
  have hmono : MonotoneOn (fun s : NNReal ↦ (s : ℝ)) Set.univ := by
    intro s _ t _ hst
    exact_mod_cast hst
  -- Proof comment: the time path is monotone increasing, hence locally of bounded variation.
  exact hmono.locallyBoundedVariationOn

/-- Helper for `Corollary_25_35::statement_repair::6`: on one almost-sure event, the time-space
graph path `(Wc_t, t)` carries the expected quadratic-covariation family: spatial diagonal entries
have primitive `T ↦ T`, while every mixed or purely time entry vanishes. -/
private theorem timeSpaceGraphCoordinateCovariationFamily_ae
    {W : NNReal → Ω → EuclideanSpace ℝ (Fin d)}
    (hW : IsStandardBrownianMotionVector μ W) :
    let Xω : Ω → VectorPathSpace (d + 1) := fun ω ↦
      ⟨fun s ↦ timeSpaceGraphPoint (μ := μ) hW s ω,
        timeSpaceGraphPath_continuous (μ := μ) hW ω⟩
    ∀ᵐ ω ∂μ,
      (∀ i j : Fin d,
        HasQuadraticCovariationAlong
          (vectorPathComponent (Xω ω) (Fin.castSucc i))
          (vectorPathComponent (Xω ω) (Fin.castSucc j))
          (fun T ↦ if i = j then (T : ℝ) else 0)) ∧
      (∀ i : Fin d,
        HasQuadraticCovariationAlong
          (vectorPathComponent (Xω ω) (Fin.castSucc i))
          (vectorPathComponent (Xω ω) (Fin.last d))
          0) ∧
      (∀ i : Fin d,
        HasQuadraticCovariationAlong
          (vectorPathComponent (Xω ω) (Fin.last d))
          (vectorPathComponent (Xω ω) (Fin.castSucc i))
          0) ∧
      HasQuadraticCovariationAlong
        (vectorPathComponent (Xω ω) (Fin.last d))
        (vectorPathComponent (Xω ω) (Fin.last d))
        0 := by
  let Wc := standardBrownianMotionVectorContinuousVersion hW
  let Xω : Ω → VectorPathSpace (d + 1) := fun ω ↦
    ⟨fun s ↦ timeSpaceGraphPoint (μ := μ) hW s ω,
      timeSpaceGraphPath_continuous (μ := μ) hW ω⟩
  have htimeSq :
      HasSquareVariationAlong
        ((⟨fun s ↦ (s : ℝ), continuous_subtype_val⟩ : C(NNReal, ℝ)))
        0 := by
    -- Proof comment: the deterministic time coordinate has locally bounded variation, so its
    -- quadratic variation vanishes.
    exact
      hasSquareVariationAlong_zero_of_locallyBoundedVariationOn
        deterministicTimePath_locallyBoundedVariation
  have hdiag :
      ∀ i : Fin d,
        ∀ᵐ ω ∂μ,
          HasQuadraticCovariationAlong
            (vectorPathComponent (Xω ω) (Fin.castSucc i))
            (vectorPathComponent (Xω ω) (Fin.castSucc i))
            (fun T ↦ (T : ℝ)) := by
    intro i
    have hsq :
        ∀ᵐ ω ∂μ,
          HasSquareVariationAlong
            ((⟨fun s ↦ (Wc s ω).ofLp i,
              brownianContinuousCoordinate_continuous_local (μ := μ) hW i ω⟩ : C(NNReal, ℝ)))
            (fun T ↦ (T : ℝ)) := by
      -- Proof comment: each spatial graph coordinate is the canonical continuous Brownian
      -- coordinate, whose square variation is the deterministic clock.
      simpa [Wc] using
        (_root_.ProbabilityTheory.ae_hasSquareVariationAlong_continuousSquareVariationProcess
          (BrownianVectorContinuousVersion.coord_isContinuousLocalMartingale (μ := μ) hW i)
          (_root_.ProbabilityTheory.continuousSquareVariationProcess_spec
            (brownianCoordinate_time_isContinuousSquareVariationProcess (μ := μ) hW i)))
    filter_upwards [hsq] with ω hsqω
    have hsplitω := vectorPathComponent_timeSpaceGraph_eq (μ := μ) hW ω
    -- Proof comment: after rewriting the graph coordinate to the continuous Brownian coordinate,
    -- the diagonal covariation is just self-covariation of the square-variation witness.
    simpa [Xω, hsplitω.1 i] using selfCovariation_of_squareVariation_local hsqω
  have hoff :
      ∀ i j : Fin d, i ≠ j →
        ∀ᵐ ω ∂μ,
          HasQuadraticCovariationAlong
            (vectorPathComponent (Xω ω) (Fin.castSucc i))
            (vectorPathComponent (Xω ω) (Fin.castSucc j))
            0 := by
    intro i j hij
    have hraw :
        ∀ᵐ ω ∂μ,
          ∀ hcontω : Continuous fun t : NNReal ↦ W t ω,
            HasQuadraticCovariationAlong
              (⟨fun s ↦ W s ω i, (continuous_apply i).comp hcontω⟩ : C(NNReal, ℝ))
              (⟨fun s ↦ W s ω j, (continuous_apply j).comp hcontω⟩ : C(NNReal, ℝ))
              0 := by
      filter_upwards
        [covariation_ae_eq_zero_of_indep_brownian
          (hW.isBrownianMotion i)
          (hW.isBrownianMotion j)
          (hW.iIndepFun.indepFun hij)] with ω hω hcontω
      -- Proof comment: distinct Brownian coordinates are independent, so their pathwise
      -- quadratic covariation vanishes on the shared full-measure event.
      simpa using hω ((continuous_apply i).comp hcontω) ((continuous_apply j).comp hcontω)
    filter_upwards [hraw, standardBrownianContinuousVersion_eq_ae_allTimes (μ := μ) hW]
        with ω hrawω hEqω
    have hWraw_i :
        (fun s : NNReal ↦ W s ω i) = fun s : NNReal ↦ (Wc s ω).ofLp i := by
      funext s
      simpa [Wc] using congrArg (fun z : EuclideanSpace ℝ (Fin d) ↦ z i) (hEqω s)
    have hWraw_j :
        (fun s : NNReal ↦ W s ω j) = fun s : NNReal ↦ (Wc s ω).ofLp j := by
      funext s
      simpa [Wc] using congrArg (fun z : EuclideanSpace ℝ (Fin d) ↦ z j) (hEqω s)
    have hcontRaw :
        Continuous fun t : NNReal ↦ W t ω := by
      -- Proof comment: the raw Brownian sample path inherits continuity from the canonical
      -- continuous version on the all-times modification event.
      refine continuous_pi fun k ↦ ?_
      have hWraw_k :
          (fun s : NNReal ↦ W s ω k) = fun s : NNReal ↦ (Wc s ω).ofLp k := by
        funext s
        simpa [Wc] using congrArg (fun z : EuclideanSpace ℝ (Fin d) ↦ z k) (hEqω s)
      rw [hWraw_k]
      exact brownianContinuousCoordinate_continuous_local (μ := μ) hW k ω
    have hsplitω := vectorPathComponent_timeSpaceGraph_eq (μ := μ) hW ω
    have hrawEq_i :
        (⟨fun s ↦ W s ω i, (continuous_apply i).comp hcontRaw⟩ : C(NNReal, ℝ)) =
          vectorPathComponent (Xω ω) (Fin.castSucc i) := by
      calc
        (⟨fun s ↦ W s ω i, (continuous_apply i).comp hcontRaw⟩ : C(NNReal, ℝ))
            = (⟨fun s ↦ (Wc s ω).ofLp i,
                brownianContinuousCoordinate_continuous_local (μ := μ) hW i ω⟩ : C(NNReal, ℝ)) := by
                  ext s
                  exact hWraw_i s
        _ = vectorPathComponent (Xω ω) (Fin.castSucc i) := by
            simpa [Xω] using (hsplitω.1 i).symm
    have hrawEq_j :
        (⟨fun s ↦ W s ω j, (continuous_apply j).comp hcontRaw⟩ : C(NNReal, ℝ)) =
          vectorPathComponent (Xω ω) (Fin.castSucc j) := by
      calc
        (⟨fun s ↦ W s ω j, (continuous_apply j).comp hcontRaw⟩ : C(NNReal, ℝ))
            = (⟨fun s ↦ (Wc s ω).ofLp j,
                brownianContinuousCoordinate_continuous_local (μ := μ) hW j ω⟩ : C(NNReal, ℝ)) := by
                  ext s
                  exact hWraw_j s
        _ = vectorPathComponent (Xω ω) (Fin.castSucc j) := by
            simpa [Xω] using (hsplitω.1 j).symm
    -- Proof comment: transfer the raw-coordinate covariation to the graph coordinates along the
    -- all-times equality between `W` and its canonical continuous version.
    simpa [hrawEq_i, hrawEq_j] using hrawω hcontRaw
  have hmixRight :
      ∀ i : Fin d,
        ∀ᵐ ω ∂μ,
          HasQuadraticCovariationAlong
            (vectorPathComponent (Xω ω) (Fin.castSucc i))
            (vectorPathComponent (Xω ω) (Fin.last d))
            0 := by
    intro i
    filter_upwards
      [(_root_.ProbabilityTheory.ae_hasSquareVariationAlong_continuousSquareVariationProcess
        (BrownianVectorContinuousVersion.coord_isContinuousLocalMartingale (μ := μ) hW i)
        (_root_.ProbabilityTheory.continuousSquareVariationProcess_spec
          (brownianCoordinate_time_isContinuousSquareVariationProcess (μ := μ) hW i)))] with ω hsqω
    have hsplitω := vectorPathComponent_timeSpaceGraph_eq (μ := μ) hW ω
    -- Proof comment: the right time coordinate has zero square variation, so every spatial-time
    -- mixed covariation vanishes.
    simpa [Xω, hsplitω.1 i, hsplitω.2] using
      hasQuadraticCovariationAlong_zero_of_rightZeroSquareVariation_local hsqω htimeSq
  have hmixLeft :
      ∀ i : Fin d,
        ∀ᵐ ω ∂μ,
          HasQuadraticCovariationAlong
            (vectorPathComponent (Xω ω) (Fin.last d))
            (vectorPathComponent (Xω ω) (Fin.castSucc i))
            0 := by
    intro i
    filter_upwards
      [(_root_.ProbabilityTheory.ae_hasSquareVariationAlong_continuousSquareVariationProcess
        (BrownianVectorContinuousVersion.coord_isContinuousLocalMartingale (μ := μ) hW i)
        (_root_.ProbabilityTheory.continuousSquareVariationProcess_spec
          (brownianCoordinate_time_isContinuousSquareVariationProcess (μ := μ) hW i)))] with ω hsqω
    have hsplitω := vectorPathComponent_timeSpaceGraph_eq (μ := μ) hW ω
    -- Proof comment: the same zero-square-variation argument also kills the mixed covariation
    -- when the deterministic time path appears on the left.
    simpa [Xω, hsplitω.2, hsplitω.1 i] using
      hasQuadraticCovariationAlong_zero_of_leftZeroSquareVariation_local htimeSq hsqω
  have htimeTime :
      ∀ᵐ ω ∂μ,
        HasQuadraticCovariationAlong
          (vectorPathComponent (Xω ω) (Fin.last d))
          (vectorPathComponent (Xω ω) (Fin.last d))
          0 := by
    refine Filter.Eventually.of_forall ?_
    intro ω
    have hsplitω := vectorPathComponent_timeSpaceGraph_eq (μ := μ) hW ω
    -- Proof comment: the deterministic time coordinate has zero square variation, so its
    -- self-covariation is also zero.
    simpa [Xω, hsplitω.2] using selfCovariation_of_squareVariation_local htimeSq
  have hspatial :
      ∀ᵐ ω ∂μ,
        ∀ i j : Fin d,
          HasQuadraticCovariationAlong
            (vectorPathComponent (Xω ω) (Fin.castSucc i))
            (vectorPathComponent (Xω ω) (Fin.castSucc j))
            (fun T ↦ if i = j then (T : ℝ) else 0) := by
    refine ae_all_iff.2 ?_
    intro i
    refine ae_all_iff.2 ?_
    intro j
    by_cases hij : i = j
    · subst hij
      filter_upwards [hdiag i] with ω hω
      -- Proof comment: on the spatial diagonal the primitive is exactly the deterministic clock.
      simpa using hω
    · filter_upwards [hoff i j hij] with ω hω
      -- Proof comment: distinct spatial coordinates have zero primitive.
      simpa [hij] using hω
  have hmixRightAll :
      ∀ᵐ ω ∂μ,
        ∀ i : Fin d,
          HasQuadraticCovariationAlong
            (vectorPathComponent (Xω ω) (Fin.castSucc i))
            (vectorPathComponent (Xω ω) (Fin.last d))
            0 := by
    exact ae_all_iff.2 hmixRight
  have hmixLeftAll :
      ∀ᵐ ω ∂μ,
        ∀ i : Fin d,
          HasQuadraticCovariationAlong
            (vectorPathComponent (Xω ω) (Fin.last d))
            (vectorPathComponent (Xω ω) (Fin.castSucc i))
            0 := by
    exact ae_all_iff.2 hmixLeft
  filter_upwards [hspatial, hmixRightAll, hmixLeftAll, htimeTime] with ω hspatialω
      hmixRightω hmixLeftω htimeω
  exact ⟨hspatialω, hmixRightω, hmixLeftω, htimeω⟩

/-- Helper for `Corollary_25_35::statement_repair::6`: the full graph-path quadratic-covariation
primitive on `Fin (d + 1)` is the Kronecker clock on spatial coordinates and `0` as soon as the
deterministic time coordinate appears. -/
private noncomputable def timeSpaceGraphCovariationPrimitive
    (i j : Fin (d + 1)) : NNReal → ℝ :=
  Fin.lastCases
    (motive := fun _ ↦ Fin (d + 1) → NNReal → ℝ)
    (fun _ ↦ 0)
    (fun i ↦
      Fin.lastCases
        (motive := fun _ ↦ NNReal → ℝ)
        (fun _ ↦ 0)
        (fun j T ↦ if i = j then (T : ℝ) else 0)
        j)
    i

/-- Helper for `Corollary_25_35::statement_repair::6`: on spatial coordinates the full primitive
reduces to the expected Kronecker clock. -/
private theorem timeSpaceGraphCovariationPrimitive_castSucc_castSucc
    (i j : Fin d) :
    timeSpaceGraphCovariationPrimitive (d := d) (Fin.castSucc i) (Fin.castSucc j) =
      fun T ↦ if i = j then (T : ℝ) else 0 := by
  -- Proof comment: both indices stay in the spatial block, so the nested `Fin.lastCases`
  -- definition reduces to the ordinary Kronecker family.
  funext T
  simp [timeSpaceGraphCovariationPrimitive]

/-- Helper for `Corollary_25_35::statement_repair::6`: if the right coordinate is the time
coordinate, the graph primitive vanishes. -/
private theorem timeSpaceGraphCovariationPrimitive_castSucc_last
    (i : Fin d) :
    timeSpaceGraphCovariationPrimitive (d := d) (Fin.castSucc i) (Fin.last d) = 0 := by
  -- Proof comment: a spatial-time quadratic-covariation primitive is identically zero in the
  -- graph model.
  funext T
  simp [timeSpaceGraphCovariationPrimitive]

/-- Helper for `Corollary_25_35::statement_repair::6`: if the left coordinate is the time
coordinate, the graph primitive vanishes. -/
private theorem timeSpaceGraphCovariationPrimitive_last_castSucc
    (i : Fin d) :
    timeSpaceGraphCovariationPrimitive (d := d) (Fin.last d) (Fin.castSucc i) = 0 := by
  -- Proof comment: the graph primitive is also zero when the deterministic time coordinate sits
  -- on the left.
  funext T
  simp [timeSpaceGraphCovariationPrimitive]

/-- Helper for `Corollary_25_35::statement_repair::6`: the time-time graph primitive is
identically zero. -/
private theorem timeSpaceGraphCovariationPrimitive_last_last :
    timeSpaceGraphCovariationPrimitive (d := d) (Fin.last d) (Fin.last d) = 0 := by
  -- Proof comment: the deterministic time path has zero quadratic variation, so the time-time
  -- primitive vanishes identically.
  funext T
  simp [timeSpaceGraphCovariationPrimitive]

/-- Helper for `Corollary_25_35::statement_repair::6`: on one almost-sure event, every pair of
graph-path coordinates carries the unified full primitive on `Fin (d + 1)`. -/
private theorem timeSpaceGraphCoordinateCovariationFamilyFull_ae
    {W : NNReal → Ω → EuclideanSpace ℝ (Fin d)}
    (hW : IsStandardBrownianMotionVector μ W) :
    let Xω : Ω → VectorPathSpace (d + 1) := fun ω ↦
      ⟨fun s ↦ timeSpaceGraphPoint (μ := μ) hW s ω,
        timeSpaceGraphPath_continuous (μ := μ) hW ω⟩
    ∀ᵐ ω ∂μ, ∀ i j : Fin (d + 1),
      HasQuadraticCovariationAlong
        (vectorPathComponent (Xω ω) i)
        (vectorPathComponent (Xω ω) j)
        (timeSpaceGraphCovariationPrimitive (d := d) i j) := by
  let Xω : Ω → VectorPathSpace (d + 1) := fun ω ↦
    ⟨fun s ↦ timeSpaceGraphPoint (μ := μ) hW s ω,
      timeSpaceGraphPath_continuous (μ := μ) hW ω⟩
  filter_upwards [timeSpaceGraphCoordinateCovariationFamily_ae (μ := μ) hW] with ω hω i j
  -- Proof comment: split the two `Fin (d + 1)` indices into spatial versus time cases and then
  -- dispatch to the already packaged diagonal/off-diagonal/mixed/time owners.
  refine
    Fin.lastCases
      (motive := fun i ↦
        ∀ j : Fin (d + 1),
          HasQuadraticCovariationAlong
            (vectorPathComponent (Xω ω) i)
            (vectorPathComponent (Xω ω) j)
            (timeSpaceGraphCovariationPrimitive (d := d) i j))
      ?_
      ?_
      i
      j
  · refine
      Fin.lastCases
        (motive := fun j ↦
          HasQuadraticCovariationAlong
            (vectorPathComponent (Xω ω) (Fin.last d))
            (vectorPathComponent (Xω ω) j)
            (timeSpaceGraphCovariationPrimitive (d := d) (Fin.last d) j))
        ?_
        ?_
        j
    · simpa [Xω, timeSpaceGraphCovariationPrimitive_last_last (d := d)] using hω.2.2.2
    · intro j
      simpa [Xω, timeSpaceGraphCovariationPrimitive_last_castSucc (d := d) j] using hω.2.2.1 j
  · intro i
    refine
      Fin.lastCases
        (motive := fun j ↦
          HasQuadraticCovariationAlong
            (vectorPathComponent (Xω ω) (Fin.castSucc i))
            (vectorPathComponent (Xω ω) j)
            (timeSpaceGraphCovariationPrimitive (d := d) (Fin.castSucc i) j))
        ?_
        ?_
        j
    · simpa [Xω, timeSpaceGraphCovariationPrimitive_castSucc_last (d := d) i] using hω.2.1 i
    · intro j
      simpa [Xω, timeSpaceGraphCovariationPrimitive_castSucc_castSucc (d := d) i j] using hω.1 i j

/-- Helper for `Corollary_25_35::statement_repair::6`: on one almost-sure event, the graph path
`(Wc_t, t)` belongs to the Chapter 25 quadratic-variation path class `𝒞_qv^(d+1)`. -/
private theorem timeSpaceGraphPath_mem_cqv_ae
    {W : NNReal → Ω → EuclideanSpace ℝ (Fin d)}
    (hW : IsStandardBrownianMotionVector μ W) :
    let Xω : Ω → VectorPathSpace (d + 1) := fun ω ↦
      ⟨fun s ↦ timeSpaceGraphPoint (μ := μ) hW s ω,
        timeSpaceGraphPath_continuous (μ := μ) hW ω⟩
    ∀ᵐ ω ∂μ, Xω ω ∈ (𝒞_qv^(d + 1)) := by
  let Xω : Ω → VectorPathSpace (d + 1) := fun ω ↦
    ⟨fun s ↦ timeSpaceGraphPoint (μ := μ) hW s ω,
      timeSpaceGraphPath_continuous (μ := μ) hW ω⟩
  filter_upwards [timeSpaceGraphCoordinateCovariationFamilyFull_ae (μ := μ) hW] with ω hω
  -- Proof comment: the unified primitive from the previous theorem is exactly the family needed
  -- by `mem_𝒞_qv_d_iff_exists_family`.
  refine (mem_𝒞_qv_d_iff_exists_family (Xω ω)).2 ?_
  refine ⟨fun i j ↦ timeSpaceGraphCovariationPrimitive (d := d) i j, ?_⟩
  intro i j
  exact hω i j

/-- Helper for `Corollary_25_35::statement_repair::6`: a spatial off-diagonal graph bracket term
vanishes because the graph primitive is identically zero away from the spatial diagonal. -/
private theorem timeSpaceGraphSpatialOffDiagonalQuadraticIntegral_eq_zero
    (F : EuclideanSpace ℝ (Fin d) × ℝ → ℝ)
    (hF : IsTimeSpaceC21 F)
    {W : NNReal → Ω → EuclideanSpace ℝ (Fin d)}
    (hW : IsStandardBrownianMotionVector μ W)
    (T : NNReal) (ω : Ω)
    (i j : Fin d) (hij : i ≠ j)
    (hcovω :
      ∀ k l : Fin (d + 1),
        HasQuadraticCovariationAlong
          (vectorPathComponent (timeSpaceGraphPath (μ := μ) hW ω) k)
          (vectorPathComponent (timeSpaceGraphPath (μ := μ) hW ω) l)
          (timeSpaceGraphCovariationPrimitive (d := d) k l)) :
    pathwiseQuadraticCovariationIntegral
        (fun s ↦
          (∂²[Fin.castSucc i, Fin.castSucc j] (timeSpaceGraphLift F))
            (timeSpaceGraphPath (μ := μ) hW ω s))
        (vectorPathComponent (timeSpaceGraphPath (μ := μ) hW ω) (Fin.castSucc i))
        (vectorPathComponent (timeSpaceGraphPath (μ := μ) hW ω) (Fin.castSucc j))
        T =
      0 := by
  let X : VectorPathSpace (d + 1) := timeSpaceGraphPath (μ := μ) hW ω
  have hWeight :
      Continuous fun s : NNReal ↦
        (∂²[Fin.castSucc i, Fin.castSucc j] timeSpaceGraphLift F) (X s) := by
    -- Proof comment: the off-diagonal Hessian entry is continuous on graph space and the graph
    -- sample path itself is continuous, so the composed weight is continuous in time.
    simpa [X] using
      (continuous_timeSpaceGraphLift_spaceSecondPartialDeriv F hF i j).comp X.continuous
  have hDiagLeft :
      HasQuadraticCovariationAlong
        (vectorPathComponent X (Fin.castSucc i))
        (vectorPathComponent X (Fin.castSucc i))
        (fun S ↦ ∫ s in Set.Icc (0 : ℝ) (S : ℝ), (1 : ℝ)) := by
    -- Proof comment: each spatial coordinate has deterministic unit bracket on the diagonal.
    simpa [X, timeSpaceGraphCovariationPrimitive_castSucc_castSucc, Real.volume_Icc] using
      hcovω (Fin.castSucc i) (Fin.castSucc i)
  have hDiagRight :
      HasQuadraticCovariationAlong
        (vectorPathComponent X (Fin.castSucc j))
        (vectorPathComponent X (Fin.castSucc j))
        (fun S ↦ ∫ s in Set.Icc (0 : ℝ) (S : ℝ), (1 : ℝ)) := by
    -- Proof comment: the same unit-bracket normalization applies to the second spatial
    -- coordinate on the diagonal.
    simpa [X, timeSpaceGraphCovariationPrimitive_castSucc_castSucc, Real.volume_Icc] using
      hcovω (Fin.castSucc j) (Fin.castSucc j)
  have hOff :
      HasQuadraticCovariationAlong
        (vectorPathComponent X (Fin.castSucc i))
        (vectorPathComponent X (Fin.castSucc j))
        (fun S ↦ ∫ s in Set.Icc (0 : ℝ) (S : ℝ), (0 : ℝ)) := by
    -- Proof comment: distinct spatial coordinates have zero bracket density in the graph
    -- primitive, so the weighted mixed integral must vanish.
    simpa [X, timeSpaceGraphCovariationPrimitive_castSucc_castSucc, hij, Real.volume_Icc] using
      hcovω (Fin.castSucc i) (Fin.castSucc j)
  have hUnitNat :
      ∀ n : ℕ, IntegrableOn (fun _ : ℝ ↦ (1 : ℝ)) (Set.Icc (0 : ℝ) (n : ℝ)) := by
    intro n
    exact
      integrableOn_const
        (μ := volume)
        (s := Set.Icc (0 : ℝ) (n : ℝ))
        (C := (1 : ℝ))
        (by simp [Real.volume_Icc])
  have hZeroNat :
      ∀ n : ℕ, IntegrableOn (fun _ : ℝ ↦ (0 : ℝ)) (Set.Icc (0 : ℝ) (n : ℝ)) := by
    intro n
    exact
      integrableOn_const
        (μ := volume)
        (s := Set.Icc (0 : ℝ) (n : ℝ))
        (C := (0 : ℝ))
        (by simp [Real.volume_Icc])
  have hZeroInt :
      IntegrableOn (fun _ : ℝ ↦ (0 : ℝ)) (Set.Icc (0 : ℝ) (T : ℝ)) := by
    exact
      integrableOn_const
        (μ := volume)
        (s := Set.Icc (0 : ℝ) (T : ℝ))
        (C := (0 : ℝ))
        (by simp [Real.volume_Icc])
  -- Proof comment: the primitive-to-interval bridge collapses the off-diagonal bracket term to an
  -- integral against the zero density.
  simpa [zero_mul] using
    pathwiseQuadraticCovariationIntegral_eq_intervalIntegral_of_covariationDensity
      (H := fun s ↦
        (∂²[Fin.castSucc i, Fin.castSucc j] timeSpaceGraphLift F) (X s))
      (Yi := vectorPathComponent X (Fin.castSucc i))
      (Yj := vectorPathComponent X (Fin.castSucc j))
      (aii := fun _ ↦ (1 : ℝ))
      (aij := fun _ ↦ (0 : ℝ))
      (ajj := fun _ ↦ (1 : ℝ))
      hDiagLeft
      hDiagRight
      hOff
      hUnitNat
      hZeroNat
      hUnitNat
      hWeight
      T
      hZeroInt

/-- Helper for `Corollary_25_35::statement_repair::6`: a spatial diagonal graph bracket term is
the ordinary time integral of the matching frozen-time second spatial derivative. -/
private theorem timeSpaceGraphSpatialDiagonalQuadraticIntegral_eq_intervalIntegral
    (F : EuclideanSpace ℝ (Fin d) × ℝ → ℝ)
    (hF : IsTimeSpaceC21 F)
    {W : NNReal → Ω → EuclideanSpace ℝ (Fin d)}
    (hW : IsStandardBrownianMotionVector μ W)
    (T : NNReal) (ω : Ω)
    (i : Fin d)
    (hcovω :
      ∀ k l : Fin (d + 1),
        HasQuadraticCovariationAlong
          (vectorPathComponent (timeSpaceGraphPath (μ := μ) hW ω) k)
          (vectorPathComponent (timeSpaceGraphPath (μ := μ) hW ω) l)
          (timeSpaceGraphCovariationPrimitive (d := d) k l)) :
    pathwiseQuadraticCovariationIntegral
        (fun s ↦
          (∂²[Fin.castSucc i, Fin.castSucc i] timeSpaceGraphLift F)
            (timeSpaceGraphPath (μ := μ) hW ω s))
        (vectorPathComponent (timeSpaceGraphPath (μ := μ) hW ω) (Fin.castSucc i))
        (vectorPathComponent (timeSpaceGraphPath (μ := μ) hW ω) (Fin.castSucc i))
        T
      =
        ∫ s in Set.Icc (0 : ℝ) (T : ℝ),
          (∂²[i, i] fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, s))
            (standardBrownianMotionVectorContinuousVersion hW s.toNNReal ω) := by
  let X : VectorPathSpace (d + 1) := timeSpaceGraphPath (μ := μ) hW ω
  have hWeight :
      Continuous fun s : NNReal ↦
        (∂²[Fin.castSucc i, Fin.castSucc i] timeSpaceGraphLift F) (X s) := by
    -- Proof comment: compose the continuous diagonal Hessian field of the graph lift with the
    -- continuous graph sample path.
    simpa [X] using
      (continuous_timeSpaceGraphLift_spaceSecondPartialDeriv F hF i i).comp X.continuous
  have hDiag :
      HasQuadraticCovariationAlong
        (vectorPathComponent X (Fin.castSucc i))
        (vectorPathComponent X (Fin.castSucc i))
        (fun S ↦ ∫ s in Set.Icc (0 : ℝ) (S : ℝ), (1 : ℝ)) := by
    -- Proof comment: the diagonal spatial bracket density is the deterministic unit clock.
    simpa [X, timeSpaceGraphCovariationPrimitive_castSucc_castSucc, Real.volume_Icc] using
      hcovω (Fin.castSucc i) (Fin.castSucc i)
  have hUnitNat :
      ∀ n : ℕ, IntegrableOn (fun _ : ℝ ↦ (1 : ℝ)) (Set.Icc (0 : ℝ) (n : ℝ)) := by
    intro n
    exact
      integrableOn_const
        (μ := volume)
        (s := Set.Icc (0 : ℝ) (n : ℝ))
        (C := (1 : ℝ))
        (by simp [Real.volume_Icc])
  have hUnitInt :
      IntegrableOn (fun _ : ℝ ↦ (1 : ℝ)) (Set.Icc (0 : ℝ) (T : ℝ)) := by
    exact
      integrableOn_const
        (μ := volume)
        (s := Set.Icc (0 : ℝ) (T : ℝ))
        (C := (1 : ℝ))
        (by simp [Real.volume_Icc])
  calc
    pathwiseQuadraticCovariationIntegral
        (fun s ↦
          (∂²[Fin.castSucc i, Fin.castSucc i] timeSpaceGraphLift F) (X s))
        (vectorPathComponent X (Fin.castSucc i))
        (vectorPathComponent X (Fin.castSucc i))
        T
      =
        ∫ s in Set.Icc (0 : ℝ) (T : ℝ),
          (1 : ℝ) *
            (∂²[Fin.castSucc i, Fin.castSucc i] timeSpaceGraphLift F) (X s.toNNReal) := by
          exact
            pathwiseQuadraticCovariationIntegral_eq_intervalIntegral_of_covariationDensity
              (H := fun s ↦
                (∂²[Fin.castSucc i, Fin.castSucc i] timeSpaceGraphLift F) (X s))
              (Yi := vectorPathComponent X (Fin.castSucc i))
              (Yj := vectorPathComponent X (Fin.castSucc i))
              (aii := fun _ ↦ (1 : ℝ))
              (aij := fun _ ↦ (1 : ℝ))
              (ajj := fun _ ↦ (1 : ℝ))
              hDiag
              hDiag
              hDiag
              hUnitNat
              hUnitNat
              hUnitNat
              hWeight
              T
              hUnitInt
    _ =
        ∫ s in Set.Icc (0 : ℝ) (T : ℝ),
          (∂²[i, i] fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, s))
            (standardBrownianMotionVectorContinuousVersion hW s.toNNReal ω) := by
          refine integral_congr_ae ?_
          refine (ae_restrict_iff' measurableSet_Icc).2 <| Filter.Eventually.of_forall ?_
          intro s hs
          change
            (1 : ℝ) *
                (∂²[Fin.castSucc i, Fin.castSucc i] timeSpaceGraphLift F)
                  (timeSpaceGraphPoint (μ := μ) hW s.toNNReal ω) =
              (∂²[i, i] fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, s))
                (standardBrownianMotionVectorContinuousVersion hW s.toNNReal ω)
          rw [one_mul]
          rw [timeSpaceGraphLift_spaceSecondPartialDeriv F hF i i,
            timeSpaceGraphSpatialPart_timeSpaceGraphPoint (μ := μ) hW,
            timeSpaceGraphPoint_last (μ := μ) hW,
            Real.toNNReal_of_nonneg hs.1]

/-- Helper for `Corollary_25_35::statement_repair::6`: the spatial part of the graph quadratic
correction collapses to the sum of the frozen-time diagonal second partial integrals. -/
private theorem timeSpaceGraphSpatialQuadraticCorrection_eq_sumSecondPartials
    (F : EuclideanSpace ℝ (Fin d) × ℝ → ℝ)
    (hF : IsTimeSpaceC21 F)
    {W : NNReal → Ω → EuclideanSpace ℝ (Fin d)}
    (hW : IsStandardBrownianMotionVector μ W)
    (T : NNReal) (ω : Ω)
    (hcovω :
      ∀ k l : Fin (d + 1),
        HasQuadraticCovariationAlong
          (vectorPathComponent (timeSpaceGraphPath (μ := μ) hW ω) k)
          (vectorPathComponent (timeSpaceGraphPath (μ := μ) hW ω) l)
          (timeSpaceGraphCovariationPrimitive (d := d) k l)) :
    ((1 : ℝ) / 2) *
        ∑ i : Fin d, ∑ j : Fin d,
          pathwiseQuadraticCovariationIntegral
            (fun s ↦
              (∂²[Fin.castSucc i, Fin.castSucc j] timeSpaceGraphLift F)
                (timeSpaceGraphPath (μ := μ) hW ω s))
            (vectorPathComponent (timeSpaceGraphPath (μ := μ) hW ω) (Fin.castSucc i))
            (vectorPathComponent (timeSpaceGraphPath (μ := μ) hW ω) (Fin.castSucc j))
            T
      =
        ((1 : ℝ) / 2) *
          ∑ i : Fin d,
            ∫ s in Set.Icc (0 : ℝ) (T : ℝ),
              (∂²[i, i] fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, s))
                (standardBrownianMotionVectorContinuousVersion hW s.toNNReal ω) := by
  -- Proof comment: the full spatial double sum reduces to the diagonal because every off-diagonal
  -- bracket term vanishes under the graph primitive.
  congr 1
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [Finset.sum_eq_single i]
  · exact
      timeSpaceGraphSpatialDiagonalQuadraticIntegral_eq_intervalIntegral
        (μ := μ) F hF hW T ω i hcovω
  · intro j hj hji
    exact
      timeSpaceGraphSpatialOffDiagonalQuadraticIntegral_eq_zero
        (μ := μ) F hF hW T ω i j (by exact fun hijEq ↦ hji hijEq.symm) hcovω
  · intro hi_notin
    exact False.elim (hi_notin (Finset.mem_univ i))

/-- Helper for `Corollary_25_35::statement_repair::6`: the dyadic spatial quadratic-correction
rows along the graph path converge to the diagonal frozen-time second-partial integral surface. -/
private theorem tendsto_timeSpaceGraphSpatialCorrection
    (F : EuclideanSpace ℝ (Fin d) × ℝ → ℝ)
    (hF : IsTimeSpaceC21 F)
    {W : NNReal → Ω → EuclideanSpace ℝ (Fin d)}
    (hW : IsStandardBrownianMotionVector μ W)
    (T : NNReal) (ω : Ω)
    (hcovω :
      ∀ k l : Fin (d + 1),
        HasQuadraticCovariationAlong
          (vectorPathComponent (timeSpaceGraphPath (μ := μ) hW ω) k)
          (vectorPathComponent (timeSpaceGraphPath (μ := μ) hW ω) l)
          (timeSpaceGraphCovariationPrimitive (d := d) k l)) :
    Tendsto
      (fun n ↦
        ((1 : ℝ) / 2) *
          ∑ i : Fin d, ∑ j : Fin d,
            dyadicQuadraticCovariationIntegralApproximationUpTo
              (fun s ↦
                (∂²[Fin.castSucc i, Fin.castSucc j] timeSpaceGraphLift F)
                  (timeSpaceGraphPath (μ := μ) hW ω s))
              (vectorPathComponent (timeSpaceGraphPath (μ := μ) hW ω) (Fin.castSucc i))
              (vectorPathComponent (timeSpaceGraphPath (μ := μ) hW ω) (Fin.castSucc j))
              T
              n)
      atTop
      (𝓝
        (((1 : ℝ) / 2) *
          ∑ i : Fin d,
            ∫ s in Set.Icc (0 : ℝ) (T : ℝ),
              (∂²[i, i] fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, s))
                (standardBrownianMotionVectorContinuousVersion hW s.toNNReal ω))) := by
  let X : VectorPathSpace (d + 1) := timeSpaceGraphPath (μ := μ) hW ω
  have hPair :
      ∀ i j : Fin d,
        Tendsto
          (fun n ↦
            dyadicQuadraticCovariationIntegralApproximationUpTo
              (fun s ↦
                (∂²[Fin.castSucc i, Fin.castSucc j] timeSpaceGraphLift F) (X s))
              (vectorPathComponent X (Fin.castSucc i))
              (vectorPathComponent X (Fin.castSucc j))
              T
              n)
          atTop
          (𝓝
            (pathwiseQuadraticCovariationIntegral
              (fun s ↦
                (∂²[Fin.castSucc i, Fin.castSucc j] timeSpaceGraphLift F) (X s))
              (vectorPathComponent X (Fin.castSucc i))
              (vectorPathComponent X (Fin.castSucc j))
              T)) := by
    intro i j
    have hWeight :
        Continuous fun s : NNReal ↦
          (∂²[Fin.castSucc i, Fin.castSucc j] timeSpaceGraphLift F) (X s) := by
      -- Proof comment: the graph-lift spatial Hessian entry is continuous on graph space, so its
      -- pullback along the fixed graph path is a continuous dyadic weight.
      simpa [X] using
        (continuous_timeSpaceGraphLift_spaceSecondPartialDeriv F hF i j).comp X.continuous
    -- Proof comment: the packaged graph primitive gives the self- and mixed-covariation inputs
    -- required by the pairwise dyadic quadratic-covariation convergence theorem.
    simpa [X] using
      tendsto_dyadicQuadraticCovariationIntegralApproximationUpTo_of_hasQuadraticCovariation
        (fun s ↦
          (∂²[Fin.castSucc i, Fin.castSucc j] timeSpaceGraphLift F) (X s))
        hWeight
        (hcovω (Fin.castSucc i) (Fin.castSucc i))
        (hcovω (Fin.castSucc j) (Fin.castSucc j))
        (hcovω (Fin.castSucc i) (Fin.castSucc j))
        T
  have hSum :
      Tendsto
        (fun n ↦
          ∑ i : Fin d, ∑ j : Fin d,
            dyadicQuadraticCovariationIntegralApproximationUpTo
              (fun s ↦
                (∂²[Fin.castSucc i, Fin.castSucc j] timeSpaceGraphLift F) (X s))
              (vectorPathComponent X (Fin.castSucc i))
              (vectorPathComponent X (Fin.castSucc j))
              T
              n)
        atTop
        (𝓝
          (∑ i : Fin d, ∑ j : Fin d,
            pathwiseQuadraticCovariationIntegral
              (fun s ↦
                (∂²[Fin.castSucc i, Fin.castSucc j] timeSpaceGraphLift F) (X s))
              (vectorPathComponent X (Fin.castSucc i))
              (vectorPathComponent X (Fin.castSucc j))
              T)) := by
    refine tendsto_finset_sum Finset.univ ?_
    intro i hi
    refine tendsto_finset_sum Finset.univ ?_
    intro j hj
    exact hPair i j
  have hScaled :
      Tendsto
        (fun n ↦
          ((1 : ℝ) / 2) *
            ∑ i : Fin d, ∑ j : Fin d,
              dyadicQuadraticCovariationIntegralApproximationUpTo
                (fun s ↦
                  (∂²[Fin.castSucc i, Fin.castSucc j] timeSpaceGraphLift F) (X s))
                (vectorPathComponent X (Fin.castSucc i))
                (vectorPathComponent X (Fin.castSucc j))
                T
                n)
        atTop
        (𝓝
          (((1 : ℝ) / 2) *
            ∑ i : Fin d, ∑ j : Fin d,
              pathwiseQuadraticCovariationIntegral
                (fun s ↦
                  (∂²[Fin.castSucc i, Fin.castSucc j] timeSpaceGraphLift F) (X s))
                (vectorPathComponent X (Fin.castSucc i))
                (vectorPathComponent X (Fin.castSucc j))
                T)) := by
    exact hSum.const_mul ((1 : ℝ) / 2)
  -- Proof comment: after summing the pairwise limits, the previously proved graph-correction
  -- normalization rewrites the limit to the diagonal frozen-time second-partial integral surface.
  convert hScaled using 1
  · ext n
    rfl
  · simpa [X] using
      timeSpaceGraphSpatialQuadraticCorrection_eq_sumSecondPartials
        (μ := μ) F hF hW T ω hcovω

/-- Helper for `Corollary_25_35::statement_repair::6`: expanding the multidimensional dyadic Itô
row gives the finite sum of the scalar coordinate rows. -/
private theorem dyadicMultidimensionalItoApproximationUpTo_eq_sum_coordinateIntegrals_local
    {d' : ℕ}
    (G : EuclideanSpace ℝ (Fin d') → ℝ) (X : VectorPathSpace d')
    (T : NNReal) (n : ℕ) :
    dyadicMultidimensionalItoApproximationUpTo G X T n =
      ∑ k : Fin d',
        partitionPathwiseItoApproximationUpTo
          (fun t ↦ (∂[k] G) (X t))
          (vectorPathComponent X k)
          Definition2158.dyadicPartitionSequence
          T
          n := by
  -- Proof comment: unfold the multidimensional row once, interchange the two finite sums, and
  -- recognize the scalar coordinate rows termwise.
  rw [dyadicMultidimensionalItoApproximationUpTo, Finset.sum_comm]
  simp [partitionPathwiseItoApproximationUpTo]

/-- Helper for `Corollary_25_35::statement_repair::6`: the graph first-order dyadic row splits
exactly into the `d` spatial coordinate rows plus the deterministic time row. -/
private theorem timeSpaceGraphFirstOrder_eq_spatialRows_add_timeRow
    (F : EuclideanSpace ℝ (Fin d) × ℝ → ℝ)
    (hF : IsTimeSpaceC21 F)
    {W : NNReal → Ω → EuclideanSpace ℝ (Fin d)}
    (hW : IsStandardBrownianMotionVector μ W)
    (T : NNReal) (ω : Ω) (n : ℕ) :
    dyadicMultidimensionalItoApproximationUpTo
        (timeSpaceGraphLift F)
        (timeSpaceGraphPath (μ := μ) hW ω)
        T
        n
      =
        (∑ i : Fin d,
          partitionPathwiseItoApproximationUpTo
            (fun t ↦
              (∂[i] fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, (t : ℝ)))
                (standardBrownianMotionVectorContinuousVersion hW t ω))
            (⟨fun t ↦
                (standardBrownianMotionVectorContinuousVersion hW t ω).ofLp i,
              brownianContinuousCoordinate_continuous_local (μ := μ) hW i ω⟩ :
              C(NNReal, ℝ))
            Definition2158.dyadicPartitionSequence
            T
            n) +
          partitionPathwiseItoApproximationUpTo
            (fun t ↦
              (∂ₜ F)
                (standardBrownianMotionVectorContinuousVersion hW t ω, (t : ℝ)))
            (⟨fun t ↦ (t : ℝ), continuous_subtype_val⟩ : C(NNReal, ℝ))
            Definition2158.dyadicPartitionSequence
            T
            n := by
  let X : VectorPathSpace (d + 1) := timeSpaceGraphPath (μ := μ) hW ω
  let Wc := standardBrownianMotionVectorContinuousVersion hW
  have hSplit := vectorPathComponent_timeSpaceGraph_eq (μ := μ) hW ω
    have hSpatialTerm :
      ∀ i : Fin d,
        partitionPathwiseItoApproximationUpTo
            (fun t ↦ (∂[Fin.castSucc i] (timeSpaceGraphLift F)) (X t))
            (vectorPathComponent X (Fin.castSucc i))
            Definition2158.dyadicPartitionSequence
            T
            n
          =
            partitionPathwiseItoApproximationUpTo
              (fun t ↦
                (∂[i] fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, (t : ℝ)))
                  (Wc t ω))
              (⟨fun t ↦ (Wc t ω).ofLp i,
                brownianContinuousCoordinate_continuous_local (μ := μ) hW i ω⟩ :
                C(NNReal, ℝ))
              Definition2158.dyadicPartitionSequence
              T
              n := by
    intro i
    congr
    · funext t
      simp [X, Wc, timeSpaceGraphLift_spacePartialDeriv, timeSpaceGraphPath,
        timeSpaceGraphSpatialPart_timeSpaceGraphPoint, timeSpaceGraphPoint_last]
    · simpa [X, Wc, timeSpaceGraphPath] using hSplit.1 i
  have hTimeTerm :
      partitionPathwiseItoApproximationUpTo
          (fun t ↦ (∂[Fin.last d] (timeSpaceGraphLift F)) (X t))
          (vectorPathComponent X (Fin.last d))
          Definition2158.dyadicPartitionSequence
          T
          n
        =
          partitionPathwiseItoApproximationUpTo
            (fun t ↦ (∂ₜ F) (Wc t ω, (t : ℝ)))
            (⟨fun t ↦ (t : ℝ), continuous_subtype_val⟩ : C(NNReal, ℝ))
            Definition2158.dyadicPartitionSequence
            T
            n := by
    congr
    · funext t
      simp [X, Wc, timeSpaceGraphLift_timePartialDeriv, timeSpaceGraphPath,
        timeSpaceGraphSpatialPart_timeSpaceGraphPoint, timeSpaceGraphPoint_last]
    · simpa [X, Wc, timeSpaceGraphPath] using hSplit.2
  calc
    dyadicMultidimensionalItoApproximationUpTo
        (timeSpaceGraphLift F)
        (timeSpaceGraphPath (μ := μ) hW ω)
        T
        n
      =
        ∑ k : Fin (d + 1),
          partitionPathwiseItoApproximationUpTo
            (fun t ↦ (∂[k] (timeSpaceGraphLift F)) (X t))
            (vectorPathComponent X k)
            Definition2158.dyadicPartitionSequence
            T
            n := by
          simpa [X, timeSpaceGraphPath] using
            dyadicMultidimensionalItoApproximationUpTo_eq_sum_coordinateIntegrals_local
              (G := timeSpaceGraphLift F) X T n
    _ =
        (∑ i : Fin d,
          partitionPathwiseItoApproximationUpTo
            (fun t ↦ (∂[Fin.castSucc i] (timeSpaceGraphLift F)) (X t))
            (vectorPathComponent X (Fin.castSucc i))
            Definition2158.dyadicPartitionSequence
            T
            n) +
          partitionPathwiseItoApproximationUpTo
            (fun t ↦ (∂[Fin.last d] (timeSpaceGraphLift F)) (X t))
            (vectorPathComponent X (Fin.last d))
            Definition2158.dyadicPartitionSequence
            T
            n := by
          rw [Fin.sum_univ_castSucc]
    _ =
        (∑ i : Fin d,
          partitionPathwiseItoApproximationUpTo
            (fun t ↦
              (∂[i] fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, (t : ℝ)))
                (Wc t ω))
            (⟨fun t ↦ (Wc t ω).ofLp i,
              brownianContinuousCoordinate_continuous_local (μ := μ) hW i ω⟩ :
              C(NNReal, ℝ))
            Definition2158.dyadicPartitionSequence
            T
            n) +
          partitionPathwiseItoApproximationUpTo
            (fun t ↦ (∂ₜ F) (Wc t ω, (t : ℝ)))
            (⟨fun t ↦ (t : ℝ), continuous_subtype_val⟩ : C(NNReal, ℝ))
            Definition2158.dyadicPartitionSequence
            T
            n := by
          rw [hTimeTerm]
          refine congrArg (fun z : ℝ ↦ z + _) ?_
          refine Finset.sum_congr rfl ?_
          intro i hi
          exact hSpatialTerm i

/-- Helper for `Corollary_25_35::statement_repair::6`: along a common strict-mono subsequence,
the graph first-order dyadic rows converge to the sum of the canonical coordinate Itô owners and
the deterministic time integral. -/
private theorem tendsto_timeSpaceGraphFirstOrder_alongSubseq
    (F : EuclideanSpace ℝ (Fin d) × ℝ → ℝ)
    (hF : IsTimeSpaceC21 F)
    {W : NNReal → Ω → EuclideanSpace ℝ (Fin d)}
    (hW : IsStandardBrownianMotionVector μ W)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) (ω : Ω) (T : NNReal)
    (hSpatialω :
      ∀ i : Fin d,
        Tendsto
          (fun n ↦
            partitionPathwiseItoApproximationUpTo
              (fun t ↦
                (∂[i] fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, (t : ℝ)))
                  (standardBrownianMotionVectorContinuousVersion hW t ω))
              (⟨fun t ↦
                  (standardBrownianMotionVectorContinuousVersion hW t ω).ofLp i,
                brownianContinuousCoordinate_continuous_local (μ := μ) hW i ω⟩ :
                C(NNReal, ℝ))
              Definition2158.dyadicPartitionSequence
              T
              (φ n))
          atTop
          (𝓝 (standardBrownianMotionVectorCoordinateItoIntegral F hW i T ω))) :
    Tendsto
      (fun n ↦
        dyadicMultidimensionalItoApproximationUpTo
          (timeSpaceGraphLift F)
          (timeSpaceGraphPath (μ := μ) hW ω)
          T
          (φ n))
      atTop
      (𝓝
        ((∑ i : Fin d, standardBrownianMotionVectorCoordinateItoIntegral F hW i T ω) +
          ∫ s in Set.Icc (0 : ℝ) (T : ℝ),
            (∂ₜ F)
              (standardBrownianMotionVectorContinuousVersion hW s.toNNReal ω, s))) := by
  let Wc := standardBrownianMotionVectorContinuousVersion hW
  have hSpatialSum :
      Tendsto
        (fun n ↦
          ∑ i : Fin d,
            partitionPathwiseItoApproximationUpTo
              (fun t ↦
                (∂[i] fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, (t : ℝ)))
                  (Wc t ω))
              (⟨fun t ↦ (Wc t ω).ofLp i,
                brownianContinuousCoordinate_continuous_local (μ := μ) hW i ω⟩ :
                C(NNReal, ℝ))
              Definition2158.dyadicPartitionSequence
              T
              (φ n))
        atTop
        (𝓝 (∑ i : Fin d, standardBrownianMotionVectorCoordinateItoIntegral F hW i T ω)) := by
    refine tendsto_finset_sum Finset.univ ?_
    intro i hi
    exact hSpatialω i
  have hWcCont : Continuous fun t : NNReal ↦ Wc t ω := by
    refine continuous_pi fun i ↦ ?_
    simpa [Wc, standardBrownianMotionVectorContinuousVersion] using
      brownianContinuousVersion_continuous (μ := μ) (B := fun t ω ↦ W t ω i)
        (hW.isBrownianMotion i) ω
  have hTimeWeightCont :
      Continuous fun t : NNReal ↦ (∂ₜ F) (Wc t ω, (t : ℝ)) := by
    -- Proof comment: the time-derivative field is continuous on space-time and the graph path
    -- `t ↦ (Wc_t, t)` is continuous.
    exact hF.continuous_timePartialDeriv.comp (hWcCont.prodMk continuous_subtype_val)
  have hTimeRow :
      Tendsto
        (fun n ↦
          partitionPathwiseItoApproximationUpTo
            (fun t ↦ (∂ₜ F) (Wc t ω, (t : ℝ)))
            (⟨fun t ↦ (t : ℝ), continuous_subtype_val⟩ : C(NNReal, ℝ))
            Definition2158.dyadicPartitionSequence
            T
            (φ n))
        atTop
        (𝓝 (∫ s in Set.Icc (0 : ℝ) (T : ℝ), (∂ₜ F) (Wc s.toNNReal ω, s))) := by
    have hTimeBase :
        Tendsto
          (fun m ↦
            partitionPathwiseItoApproximationUpTo
              (fun t ↦ (∂ₜ F) (Wc t ω, (t : ℝ)))
              (⟨fun t ↦ (t : ℝ), continuous_subtype_val⟩ : C(NNReal, ℝ))
              Definition2158.dyadicPartitionSequence
              T
              m)
          atTop
          (𝓝 (∫ s in Set.Icc (0 : ℝ) (T : ℝ), (∂ₜ F) (Wc s.toNNReal ω, s))) := by
      simpa [pathwiseItoIntegralAlong_timePath_eq_intervalIntegral_of_continuous]
        using
          (hasPathwiseItoIntegralAlong_timePath_of_continuous
            (w := fun t ↦ (∂ₜ F) (Wc t ω, (t : ℝ)))
            hTimeWeightCont).tendsto T
    exact hTimeBase.comp hφ.tendsto_atTop
  have hCombined :
      Tendsto
        (fun n ↦
          (∑ i : Fin d,
            partitionPathwiseItoApproximationUpTo
              (fun t ↦
                (∂[i] fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, (t : ℝ)))
                  (Wc t ω))
              (⟨fun t ↦ (Wc t ω).ofLp i,
                brownianContinuousCoordinate_continuous_local (μ := μ) hW i ω⟩ :
                C(NNReal, ℝ))
              Definition2158.dyadicPartitionSequence
              T
              (φ n)) +
            partitionPathwiseItoApproximationUpTo
              (fun t ↦ (∂ₜ F) (Wc t ω, (t : ℝ)))
              (⟨fun t ↦ (t : ℝ), continuous_subtype_val⟩ : C(NNReal, ℝ))
              Definition2158.dyadicPartitionSequence
              T
              (φ n))
        atTop
        (𝓝
          ((∑ i : Fin d, standardBrownianMotionVectorCoordinateItoIntegral F hW i T ω) +
            ∫ s in Set.Icc (0 : ℝ) (T : ℝ), (∂ₜ F) (Wc s.toNNReal ω, s))) := by
    exact hSpatialSum.add hTimeRow
  convert hCombined using 1
  ext n
  symm
  exact timeSpaceGraphFirstOrder_eq_spatialRows_add_timeRow (μ := μ) F hF hW T ω (φ n)

/-- Helper for `Corollary_25_35::statement_repair::6`: a point on the `k`-th coordinate line
through `x` has `k`-th coordinate equal to the chosen scalar parameter. -/
private theorem pointOnCoordinateLine_apply_local
    (x : EuclideanSpace ℝ (Fin d)) (k : Fin d) (t : ℝ) :
    (x + EuclideanSpace.single k (t - x k)) k = t := by
  -- Proof comment: at the active coordinate, the inserted displacement exactly shifts the
  -- original value `x k` to the target value `t`.
  simp

/-- Helper for `Corollary_25_35::statement_repair::6`: moving twice along the same coordinate line
is the same as moving directly to the final endpoint. -/
private theorem coordinateLine_compose_self_local
    (x : EuclideanSpace ℝ (Fin d)) (k : Fin d) (t u : ℝ) :
    x + EuclideanSpace.single k (t - x k) +
        EuclideanSpace.single k (u - (x + EuclideanSpace.single k (t - x k)) k) =
      x + EuclideanSpace.single k (u - x k) := by
  -- Proof comment: compare coordinates; only the `k`-th coordinate changes, and there the two
  -- successive line moves add up to the single final displacement.
  ext j
  by_cases h : j = k
  · subst h
    simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
      pointOnCoordinateLine_apply_local]
  · simp [h]

/-- Helper for `Corollary 25.35`: summing the clipped increments of an arbitrary scalar row along
one partition level telescopes to the endpoint increment on `[0,T]`. -/
private theorem partitionIncrementSum_eq_endpointIncrement_local
    (G : NNReal → ℝ) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (T : NNReal) (n : ℕ) :
    Finset.sum (Finset.range (partitionBoundIndex P n T)) (fun k ↦
        G (partitionNextPointUpTo P n k T) - G (P n k)) =
      G T - G 0 := by
  let m := partitionBoundIndex P n T
  -- Proof comment: split off the final clipped increment; the earlier cells telescope, and the
  -- last clipped successor is exactly `T`.
  by_cases hm : m = 0
  · have hT0 : T = 0 := by
      have hle : T ≤ P n 0 := by
        simpa [m, hm] using le_partitionBoundIndex_time P n T
      simpa [IsAdmissiblePartitionSequence.zero_eq (P := P) n] using hle
    have hm0 : partitionBoundIndex P n T = 0 := by
      simpa [m] using hm
    rw [hm0, Finset.sum_range_zero, hT0]
    ring
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hm
    have hkm : partitionBoundIndex P n T = k.succ := by
      simpa [m] using hk
    have hsum :
        ∀ r : ℕ,
          Finset.sum (Finset.range r) (fun j ↦ G (P n (j + 1)) - G (P n j)) =
            G (P n r) - G (P n 0) := by
      intro r
      induction r with
      | zero =>
          simp
      | succ r ihr =>
          rw [Finset.sum_range_succ, ihr]
          abel
    rw [hkm, Finset.sum_range_succ]
    have hprefix :
        Finset.sum (Finset.range k)
            (fun j ↦ G (partitionNextPointUpTo P n j T) - G (P n j)) =
          G (P n k) - G (P n 0) := by
      have hraw :
          Finset.sum (Finset.range k)
              (fun j ↦ G (partitionNextPointUpTo P n j T) - G (P n j)) =
            Finset.sum (Finset.range k) (fun j ↦ G (P n (j + 1)) - G (P n j)) := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        have hj_lt : j + 1 < partitionBoundIndex P n T := by
          simpa [hkm, hk] using Nat.succ_lt_succ (Finset.mem_range.mp hj)
        have hnext : partitionNextPointUpTo P n j T = P n (j + 1) := by
          rw [partitionNextPointUpTo, min_eq_left]
          exact le_of_lt (partitionPoint_lt_time_of_lt_partitionBoundIndex P n (j + 1) T hj_lt)
        rw [hnext]
      exact hraw.trans (hsum k)
    have hlast : G (partitionNextPointUpTo P n k T) - G (P n k) = G T - G (P n k) := by
      -- Proof comment: at the final contributing index, the clipped successor is exactly `T`.
      have hnext : partitionNextPointUpTo P n k T = T := by
        rw [partitionNextPointUpTo, min_eq_right]
        simpa [m, hk] using le_partitionBoundIndex_time P n T
      rw [hnext]
    rw [hprefix, hlast]
    simp [IsAdmissiblePartitionSequence.zero_eq (P := P) n]

/-- Helper for `Corollary_25_35::statement_repair::6`: for any frozen-time slice that is already
`C²`, the canonical Laplacian is the sum of the diagonal second coordinate partials. -/
private theorem laplacian_eq_sumSecondPartials_of_contDiff
    (G : EuclideanSpace ℝ (Fin d) → ℝ)
    (hG : ContDiff ℝ 2 G)
    (x : EuclideanSpace ℝ (Fin d)) :
    Δ G x =
      ∑ k : Fin d, (∂²[k, k] G) x := by
  -- Proof comment: this is exactly the chapter-level coordinate-Laplacian bridge already proved
  -- in Theorem 25.33, reused here under the local helper name.
  simpa using laplacian_eq_sum_secondPartialDeriv (d := d) G hG x

/-- Helper for `Corollary_25_35::statement_repair::6`: the dyadic spatial quadratic correction on
the exact graph surface used by the time-dependent Itô proof. -/
private noncomputable def timeSpaceC21SpatialCorrectionApproximationUpTo
    (F : EuclideanSpace ℝ (Fin d) × ℝ → ℝ)
    {W : NNReal → Ω → EuclideanSpace ℝ (Fin d)}
    (hW : IsStandardBrownianMotionVector μ W)
    (T : NNReal) (ω : Ω) (n : ℕ) : ℝ :=
  ((1 : ℝ) / 2) *
    ∑ i : Fin d, ∑ j : Fin d,
      dyadicQuadraticCovariationIntegralApproximationUpTo
        (fun s ↦
          (∂²[Fin.castSucc i, Fin.castSucc j] (timeSpaceGraphLift F))
            (timeSpaceGraphPoint (μ := μ) hW s ω))
        (vectorPathComponent (timeSpaceGraphPath (μ := μ) hW ω) (Fin.castSucc i))
        (vectorPathComponent (timeSpaceGraphPath (μ := μ) hW ω) (Fin.castSucc j))
        T
        n

/-- Helper for `Corollary_25_35::statement_repair::6`: the theorem-local dyadic residual after
subtracting the graph first-order sum and the spatial quadratic correction. -/
private noncomputable def timeSpaceC21Remainder
    (F : EuclideanSpace ℝ (Fin d) × ℝ → ℝ)
    {W : NNReal → Ω → EuclideanSpace ℝ (Fin d)}
    (hW : IsStandardBrownianMotionVector μ W)
    (T : NNReal) (ω : Ω) (n : ℕ) : ℝ :=
  F (standardBrownianMotionVectorContinuousVersion hW T ω, (T : ℝ)) -
    F (standardBrownianMotionVectorContinuousVersion hW 0 ω, 0) -
    dyadicMultidimensionalItoApproximationUpTo
      (timeSpaceGraphLift F)
      (timeSpaceGraphPath (μ := μ) hW ω)
      T
      n -
    timeSpaceC21SpatialCorrectionApproximationUpTo (μ := μ) F hW T ω n

/-- Helper for `Corollary 25.35`: the theorem-local time residual sums the left-point error in the
time variable after freezing the spatial point at the right endpoint of each dyadic cell. -/
private noncomputable def timeSpaceC21TimeResidual
    (F : EuclideanSpace ℝ (Fin d) × ℝ → ℝ)
    {W : NNReal → Ω → EuclideanSpace ℝ (Fin d)}
    (hW : IsStandardBrownianMotionVector μ W)
    (T : NNReal) (ω : Ω) (n : ℕ) : ℝ :=
  let Wc := standardBrownianMotionVectorContinuousVersion hW
  Finset.sum (Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n T)) fun k ↦
    let t0 := Definition2158.dyadicPartitionSequence n k
    let t1 := partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T
    F (Wc t1 ω, (t1 : ℝ)) - F (Wc t1 ω, (t0 : ℝ)) -
      (∂ₜ F) (Wc t0 ω, (t0 : ℝ)) * ((t1 : ℝ) - (t0 : ℝ))

/-- Helper for `Corollary 25.35`: the theorem-local spatial residual is the frozen-time Taylor
error after subtracting the spatial first-order row and the quadratic correction on each dyadic
cell. -/
private noncomputable def timeSpaceC21SpatialResidual
    (F : EuclideanSpace ℝ (Fin d) × ℝ → ℝ)
    {W : NNReal → Ω → EuclideanSpace ℝ (Fin d)}
    (hW : IsStandardBrownianMotionVector μ W)
    (T : NNReal) (ω : Ω) (n : ℕ) : ℝ :=
  let Wc := standardBrownianMotionVectorContinuousVersion hW
  Finset.sum (Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n T)) fun k ↦
    let t0 := Definition2158.dyadicPartitionSequence n k
    let t1 := partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T
    let x0 := Wc t0 ω
    let x1 := Wc t1 ω
    F (x1, (t0 : ℝ)) - F (x0, (t0 : ℝ)) -
      (∑ i : Fin d,
        (∂[i] fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, (t0 : ℝ))) x0 * (x1 i - x0 i)) -
      ((1 : ℝ) / 2) *
        ∑ i : Fin d, ∑ j : Fin d,
          (∂²[i, j] fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, (t0 : ℝ))) x0 *
            (x1 i - x0 i) * (x1 j - x0 j)

/-- Helper for `Corollary_25_35::statement_repair::6`: adding back the theorem-local dyadic
residual recovers the endpoint increment on the graph surface. -/
private theorem timeSpaceC21DyadicDecomposition
    (F : EuclideanSpace ℝ (Fin d) × ℝ → ℝ)
    {W : NNReal → Ω → EuclideanSpace ℝ (Fin d)}
    (hW : IsStandardBrownianMotionVector μ W)
    (T : NNReal) (ω : Ω) (n : ℕ) :
    F (standardBrownianMotionVectorContinuousVersion hW T ω, (T : ℝ)) -
        F (standardBrownianMotionVectorContinuousVersion hW 0 ω, 0) =
      dyadicMultidimensionalItoApproximationUpTo
          (timeSpaceGraphLift F)
          (timeSpaceGraphPath (μ := μ) hW ω)
          T
          n +
        timeSpaceC21SpatialCorrectionApproximationUpTo (μ := μ) F hW T ω n +
        timeSpaceC21Remainder (μ := μ) F hW T ω n := by
  -- Proof comment: after defining the remainder as the algebraic residual, the exact
  -- decomposition is the tautological identity obtained by adding it back.
  rw [timeSpaceC21Remainder]
  ring

/-- Helper for `Corollary 25.35`: the theorem-local remainder is exactly the sum of the
deterministic time residual and the frozen-time spatial Taylor residual. -/
private theorem timeSpaceC21Remainder_eq_timeResidual_add_spatialResidual
    (F : EuclideanSpace ℝ (Fin d) × ℝ → ℝ)
    (hF : IsTimeSpaceC21 F)
    {W : NNReal → Ω → EuclideanSpace ℝ (Fin d)}
    (hW : IsStandardBrownianMotionVector μ W)
    (T : NNReal) (ω : Ω) (n : ℕ) :
    timeSpaceC21Remainder (μ := μ) F hW T ω n =
      timeSpaceC21TimeResidual (μ := μ) F hW T ω n +
        timeSpaceC21SpatialResidual (μ := μ) F hW T ω n := by
  let Wc := standardBrownianMotionVectorContinuousVersion hW
  let G : NNReal → ℝ := fun t ↦ F (Wc t ω, (t : ℝ))
  have hEndpoint :
      Finset.sum (Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n T))
          (fun k ↦
            G (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) -
              G (Definition2158.dyadicPartitionSequence n k)) =
        F (Wc T ω, (T : ℝ)) - F (Wc 0 ω, 0) := by
    -- Proof comment: the endpoint increment is the telescoping sum of the dyadic cell
    -- increments for the scalar graph path `t ↦ F(Wc_t, t)`.
    simpa [G, IsAdmissiblePartitionSequence.zero_eq
      (P := Definition2158.dyadicPartitionSequence) n] using
      partitionIncrementSum_eq_endpointIncrement_local
        (G := G) Definition2158.dyadicPartitionSequence T n
  have hFirstOrder :
      dyadicMultidimensionalItoApproximationUpTo
          (timeSpaceGraphLift F)
          (timeSpaceGraphPath (μ := μ) hW ω)
          T
          n
        =
          (∑ k in Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n T),
            ∑ i : Fin d,
              (∂[i] fun x : EuclideanSpace ℝ (Fin d) ↦
                  F (x, (Definition2158.dyadicPartitionSequence n k : ℝ)))
                (Wc (Definition2158.dyadicPartitionSequence n k) ω) *
                (Wc (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) ω i -
                  Wc (Definition2158.dyadicPartitionSequence n k) ω i)) +
            ∑ k in Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n T),
              (∂ₜ F)
                  (Wc (Definition2158.dyadicPartitionSequence n k) ω,
                    (Definition2158.dyadicPartitionSequence n k : ℝ)) *
                ((partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T : ℝ) -
                  (Definition2158.dyadicPartitionSequence n k : ℝ)) := by
    -- Proof comment: rewrite the graph first-order row as the sum of the spatial coordinate rows
    -- and the deterministic time row, then unfold the scalar partition rows.
    rw [timeSpaceGraphFirstOrder_eq_spatialRows_add_timeRow (μ := μ) F hF hW T ω n]
    simp [partitionPathwiseItoApproximationUpTo]
  have hSpatialCorrection :
      timeSpaceC21SpatialCorrectionApproximationUpTo (μ := μ) F hW T ω n =
        ((1 : ℝ) / 2) *
          ∑ k in Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n T),
            ∑ i : Fin d, ∑ j : Fin d,
              (∂²[i, j] fun x : EuclideanSpace ℝ (Fin d) ↦
                  F (x, (Definition2158.dyadicPartitionSequence n k : ℝ)))
                (Wc (Definition2158.dyadicPartitionSequence n k) ω) *
                (Wc (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) ω i -
                  Wc (Definition2158.dyadicPartitionSequence n k) ω i) *
                (Wc (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) ω j -
                  Wc (Definition2158.dyadicPartitionSequence n k) ω j) := by
    -- Proof comment: unfold the quadratic correction and rewrite the graph second partials and
    -- graph coordinates back to the frozen-time spatial second partials of `F`.
    simp [timeSpaceC21SpatialCorrectionApproximationUpTo,
      dyadicQuadraticCovariationIntegralApproximationUpTo_def, vectorPathComponent_apply,
      timeSpaceGraphLift_spaceSecondPartialDeriv, timeSpaceGraphPath,
      timeSpaceGraphSpatialPart_timeSpaceGraphPoint, timeSpaceGraphPoint_last, Wc]
  rw [timeSpaceC21Remainder, timeSpaceC21TimeResidual, timeSpaceC21SpatialResidual]
  rw [hEndpoint, hFirstOrder, hSpatialCorrection]
  -- Proof comment: after the endpoint, first-order, and quadratic-correction rewrites, each
  -- dyadic cell contribution splits into the stated time and spatial residual pieces.
  ring_nf

/-- Helper for `Corollary 25.35`: the candidate Fréchet derivative of the frozen time slice
`x ↦ F (x, s)` built from the coordinate partials. -/
private noncomputable def frozenSliceFDeriv
    (F : EuclideanSpace ℝ (Fin d) × ℝ → ℝ)
    (s : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ :=
  ∑ i : Fin d,
    (PiLp.proj 2 (fun _ : Fin d ↦ ℝ) i).smulRight
      ((∂[i] fun y : EuclideanSpace ℝ (Fin d) ↦ F (y, s)) x)

/-- Helper for `Corollary 25.35`: evaluating the frozen-slice derivative candidate is the
expected coordinate gradient pairing. -/
private theorem frozenSliceFDeriv_apply
    (F : EuclideanSpace ℝ (Fin d) × ℝ → ℝ)
    (s : ℝ) (x v : EuclideanSpace ℝ (Fin d)) :
    frozenSliceFDeriv F s x v =
      ∑ i : Fin d,
        v i * (∂[i] fun y : EuclideanSpace ℝ (Fin d) ↦ F (y, s)) x := by
  -- Proof comment: expand the finite sum of projected coordinate maps and evaluate each
  -- `smulRight` term on `v`.
  simp [frozenSliceFDeriv, mul_comm, mul_left_comm, mul_assoc]

/-- Helper for `Corollary 25.35`: on the `i`-th Euclidean basis vector, the frozen-slice
derivative candidate evaluates to the stored `i`-th spatial partial derivative. -/
private theorem frozenSliceFDeriv_apply_single
    (F : EuclideanSpace ℝ (Fin d) × ℝ → ℝ)
    (s : ℝ) (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    frozenSliceFDeriv F s x (EuclideanSpace.single i (1 : ℝ)) =
      (∂[i] fun y : EuclideanSpace ℝ (Fin d) ↦ F (y, s)) x := by
  -- Proof comment: in the coordinate-gradient pairing, every basis coefficient vanishes except
  -- the active `i`-th coordinate, where the coefficient is `1`.
  rw [frozenSliceFDeriv_apply]
  simp [EuclideanSpace.single]

/-- Helper for `Corollary 25.35`: the frozen slice has the expected one-variable derivative along
its `i`-th coordinate line, now written using the candidate Fréchet derivative applied to the
standard basis vector. -/
private theorem hasDerivAt_frozenSliceAlongCoordinate
    (F : EuclideanSpace ℝ (Fin d) × ℝ → ℝ)
    (hF : IsTimeSpaceC21 F)
    (s : ℝ) (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    HasDerivAt
      (fun t : ℝ ↦ F (x + EuclideanSpace.single i (t - x i), s))
      (frozenSliceFDeriv F s x (EuclideanSpace.single i (1 : ℝ)))
      (x i) := by
  -- Proof comment: specialize the `C^{2,1}` coordinate-line derivative stored in `hF`, then
  -- rewrite its derivative value through the basis-vector evaluation of `frozenSliceFDeriv`.
  simpa [frozenSliceFDeriv_apply_single] using hF.hasDerivAt_space i (x, s)

/-- Helper for `Corollary 25.35`: the derivative candidate for a frozen-slice partial derivative
uses the second spatial partials as coefficients. -/
private noncomputable def frozenSliceSecondFDeriv
    (F : EuclideanSpace ℝ (Fin d) × ℝ → ℝ)
    (s : ℝ) (i : Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ :=
  ∑ j : Fin d,
    (PiLp.proj 2 (fun _ : Fin d ↦ ℝ) j).smulRight
      ((∂²[i, j] fun y : EuclideanSpace ℝ (Fin d) ↦ F (y, s)) x)

/-- Helper for `Corollary 25.35`: evaluating the derivative candidate of a frozen-slice partial
is the expected Hessian row pairing. -/
private theorem frozenSliceSecondFDeriv_apply
    (F : EuclideanSpace ℝ (Fin d) × ℝ → ℝ)
    (s : ℝ) (i : Fin d) (x v : EuclideanSpace ℝ (Fin d)) :
    frozenSliceSecondFDeriv F s i x v =
      ∑ j : Fin d,
        v j * (∂²[i, j] fun y : EuclideanSpace ℝ (Fin d) ↦ F (y, s)) x := by
  -- Proof comment: unfold the second derivative candidate and evaluate the finite sum termwise.
  simp [frozenSliceSecondFDeriv, mul_comm, mul_left_comm, mul_assoc]

/-- Helper for `Corollary 25.35`: on the `j`-th Euclidean basis vector, the derivative candidate
for the frozen-slice `i`-th partial evaluates to the corresponding stored Hessian entry. -/
private theorem frozenSliceSecondFDeriv_apply_single
    (F : EuclideanSpace ℝ (Fin d) × ℝ → ℝ)
    (s : ℝ) (i : Fin d) (x : EuclideanSpace ℝ (Fin d)) (j : Fin d) :
    frozenSliceSecondFDeriv F s i x (EuclideanSpace.single j (1 : ℝ)) =
      (∂²[i, j] fun y : EuclideanSpace ℝ (Fin d) ↦ F (y, s)) x := by
  -- Proof comment: the Hessian-row pairing again collapses to the unique surviving basis
  -- coefficient on the active `j`-th coordinate.
  rw [frozenSliceSecondFDeriv_apply]
  simp [EuclideanSpace.single]

/-- Helper for `Corollary 25.35`: each frozen-slice spatial partial has the expected derivative
along the `j`-th coordinate line, expressed through the candidate second Fréchet derivative. -/
private theorem hasDerivAt_frozenSlicePartialAlongCoordinate
    (F : EuclideanSpace ℝ (Fin d) × ℝ → ℝ)
    (hF : IsTimeSpaceC21 F)
    (s : ℝ) (i j : Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    HasDerivAt
      (fun t : ℝ ↦
        (∂[i] fun y : EuclideanSpace ℝ (Fin d) ↦ F (y, s))
          (x + EuclideanSpace.single j (t - x j)))
      (frozenSliceSecondFDeriv F s i x (EuclideanSpace.single j (1 : ℝ)))
      (x j) := by
  -- Proof comment: specialize the stored second coordinate-line derivative of `F`, then rewrite
  -- the derivative value through the basis-vector evaluation of `frozenSliceSecondFDeriv`.
  simpa [frozenSliceSecondFDeriv_apply_single] using hF.hasDerivAt_spaceSecond i j (x, s)

/-- Helper for `Corollary 25.35`: for a fixed direction `v`, the frozen-slice derivative
candidate varies continuously in the base point. -/
private theorem continuous_frozenSliceFDeriv_apply
    (F : EuclideanSpace ℝ (Fin d) × ℝ → ℝ)
    (hF : IsTimeSpaceC21 F)
    (s : ℝ) (v : EuclideanSpace ℝ (Fin d)) :
    Continuous fun x : EuclideanSpace ℝ (Fin d) ↦ frozenSliceFDeriv F s x v := by
  -- Proof comment: after expanding the candidate derivative, continuity reduces to the continuity
  -- of the spatial partials supplied by `IsTimeSpaceC21`.
  rw [show (fun x : EuclideanSpace ℝ (Fin d) ↦ frozenSliceFDeriv F s x v) =
      fun x : EuclideanSpace ℝ (Fin d) ↦
        ∑ i : Fin d,
          v i * (∂[i] fun y : EuclideanSpace ℝ (Fin d) ↦ F (y, s)) x by
      funext x
      exact frozenSliceFDeriv_apply F s x v]
  refine continuous_finset_sum _ fun i _ ↦ ?_
  exact continuous_const.mul <|
    (hF.continuous_spacePartialDeriv i).comp (continuous_id.prodMk continuous_const)

/-- Helper for `Corollary 25.35`: for a fixed direction `v`, the derivative candidate of a
frozen-slice partial varies continuously in the base point. -/
private theorem continuous_frozenSliceSecondFDeriv_apply
    (F : EuclideanSpace ℝ (Fin d) × ℝ → ℝ)
    (hF : IsTimeSpaceC21 F)
    (s : ℝ) (i : Fin d) (v : EuclideanSpace ℝ (Fin d)) :
    Continuous fun x : EuclideanSpace ℝ (Fin d) ↦ frozenSliceSecondFDeriv F s i x v := by
  -- Proof comment: the second derivative candidate is a finite Hessian-row sum, so continuity
  -- follows from the continuity of the second spatial partials.
  rw [show (fun x : EuclideanSpace ℝ (Fin d) ↦ frozenSliceSecondFDeriv F s i x v) =
      fun x : EuclideanSpace ℝ (Fin d) ↦
        ∑ j : Fin d,
          v j * (∂²[i, j] fun y : EuclideanSpace ℝ (Fin d) ↦ F (y, s)) x by
      funext x
      exact frozenSliceSecondFDeriv_apply F s i x v]
  refine continuous_finset_sum _ fun j _ ↦ ?_
  exact continuous_const.mul <|
    (hF.continuous_spaceSecondPartialDeriv i j).comp (continuous_id.prodMk continuous_const)

/-- Helper for `Corollary 25.35`: once the frozen slice and its spatial partials have the expected
Fréchet derivatives, the frozen slice is `C²`. -/
private theorem contDiffFrozenSlicePartial_of_bridges
    (F : EuclideanSpace ℝ (Fin d) × ℝ → ℝ)
    (hF : IsTimeSpaceC21 F)
    (s : ℝ) (i : Fin d)
    (hBridge :
      ∀ x : EuclideanSpace ℝ (Fin d),
        HasFDerivAt
          (fun y : EuclideanSpace ℝ (Fin d) ↦
            (∂[i] fun z : EuclideanSpace ℝ (Fin d) ↦ F (z, s)) y)
          (frozenSliceSecondFDeriv F s i x)
          x) :
    ContDiff ℝ 1
      (fun y : EuclideanSpace ℝ (Fin d) ↦
        (∂[i] fun z : EuclideanSpace ℝ (Fin d) ↦ F (z, s)) y) := by
  -- Proof comment: use the finite-dimensional `C¹` criterion, with continuity of every fixed
  -- derivative evaluation supplied by the Hessian-coefficient continuity above.
  refine (contDiff_succ_iff_fderiv_apply
    (𝕜 := ℝ) (D := EuclideanSpace ℝ (Fin d)) (E := ℝ) (n := 0)
    (f := fun y : EuclideanSpace ℝ (Fin d) ↦
      (∂[i] fun z : EuclideanSpace ℝ (Fin d) ↦ F (z, s)) y)).2 ?_
  refine ⟨fun x ↦ (hBridge x).differentiableAt, ?_, ?_⟩
  · intro htop
    cases htop
  · intro v
    rw [contDiff_zero]
    have hEval :
        (fun x : EuclideanSpace ℝ (Fin d) ↦
          (fderiv ℝ
            (fun y : EuclideanSpace ℝ (Fin d) ↦
              (∂[i] fun z : EuclideanSpace ℝ (Fin d) ↦ F (z, s)) y) x) v) =
          fun x : EuclideanSpace ℝ (Fin d) ↦ frozenSliceSecondFDeriv F s i x v := by
      funext x
      exact congrArg (fun L : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ ↦ L v) (hBridge x).fderiv
    rw [hEval]
    exact continuous_frozenSliceSecondFDeriv_apply F hF s i v

/-- Helper for `Corollary 25.35`: the frozen slice is `C²` once the first- and second-order
coordinate-to-Fréchet bridges are available. -/
private theorem contDiffFrozenSlice_of_bridges
    (F : EuclideanSpace ℝ (Fin d) × ℝ → ℝ)
    (hF : IsTimeSpaceC21 F)
    (s : ℝ)
    (hBridge :
      ∀ x : EuclideanSpace ℝ (Fin d),
        HasFDerivAt
          (fun y : EuclideanSpace ℝ (Fin d) ↦ F (y, s))
          (frozenSliceFDeriv F s x)
          x)
    (hBridgePartial :
      ∀ i : Fin d, ∀ x : EuclideanSpace ℝ (Fin d),
        HasFDerivAt
          (fun y : EuclideanSpace ℝ (Fin d) ↦
            (∂[i] fun z : EuclideanSpace ℝ (Fin d) ↦ F (z, s)) y)
          (frozenSliceSecondFDeriv F s i x)
          x) :
    ContDiff ℝ 2 (fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, s)) := by
  have hPart :
      ∀ i : Fin d,
        ContDiff ℝ 1
          (fun y : EuclideanSpace ℝ (Fin d) ↦
            (∂[i] fun z : EuclideanSpace ℝ (Fin d) ↦ F (z, s)) y) := by
    intro i
    exact contDiffFrozenSlicePartial_of_bridges F hF s i (hBridgePartial i)
  -- Proof comment: apply the finite-dimensional `C²` criterion, and rewrite every derivative
  -- evaluation to the already-packaged coordinate gradient pairing.
  refine (contDiff_succ_iff_fderiv_apply
    (𝕜 := ℝ) (D := EuclideanSpace ℝ (Fin d)) (E := ℝ) (n := 1)
    (f := fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, s))).2 ?_
  refine ⟨fun x ↦ (hBridge x).differentiableAt, ?_, ?_⟩
  · intro htop
    cases htop
  · intro v
    have hEval :
        (fun x : EuclideanSpace ℝ (Fin d) ↦
          (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin d) ↦ F (y, s)) x) v) =
          fun x : EuclideanSpace ℝ (Fin d) ↦
            ∑ i : Fin d,
              v i • (∂[i] fun y : EuclideanSpace ℝ (Fin d) ↦ F (y, s)) x := by
      funext x
      rw [show fderiv ℝ (fun y : EuclideanSpace ℝ (Fin d) ↦ F (y, s)) x =
          frozenSliceFDeriv F s x from (hBridge x).fderiv]
      simp [frozenSliceFDeriv_apply, smul_eq_mul]
    rw [hEval]
    simpa using
      (ContDiff.sum (s := Finset.univ) fun i _ ↦ (hPart i).const_smul (v i))

/-- Helper for `Corollary 25.35`: the translated `i`-th coordinate line through `x` is a
continuous affine path. -/
private theorem continuous_coordinateLine_local
    (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    Continuous fun t : ℝ ↦ x + EuclideanSpace.single i (t - x i) := by
  -- Proof comment: every coordinate is constant except the active `i`-th one, where the map is
  -- the affine scalar function `t ↦ t - x i`.
  refine continuous_const.add <| continuous_pi fun j ↦ ?_
  by_cases h : j = i
  · subst h
    simp [EuclideanSpace.single, sub_eq_add_neg]
  · simp [EuclideanSpace.single, h]

/-- Helper for `Corollary 25.35`: the coordinate-line derivative hypothesis can be recentered at
any point on the same coordinate line. -/
private theorem hasDerivAt_coordinateLine_recentered
    (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (f' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
    (hcoord :
      ∀ x : EuclideanSpace ℝ (Fin d), ∀ i : Fin d,
        HasDerivAt
          (fun t : ℝ ↦ f (x + EuclideanSpace.single i (t - x i)))
          (f' x (EuclideanSpace.single i (1 : ℝ)))
          (x i))
    (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) (t : ℝ) :
    HasDerivAt
      (fun u : ℝ ↦ f (x + EuclideanSpace.single i (u - x i)))
      (f' (x + EuclideanSpace.single i (t - x i)) (EuclideanSpace.single i (1 : ℝ)))
      t := by
  -- Proof comment: apply the stored coordinate-line derivative at the shifted base point and use
  -- the coordinate-line composition identity to rewrite it back to the original line.
  simpa [coordinateLine_compose_self_local, pointOnCoordinateLine_apply_local] using
    (hcoord (x + EuclideanSpace.single i (t - x i)) i)

/-- Helper for `Corollary 25.35`: along a coordinate line, the candidate derivative coefficient
for that coordinate varies continuously with the line parameter. -/
private theorem continuous_coordinateLineCoefficient
    (f' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
    (hcont :
      ∀ v : EuclideanSpace ℝ (Fin d),
        Continuous fun x : EuclideanSpace ℝ (Fin d) ↦ f' x v)
    (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    Continuous fun t : ℝ ↦
      f' (x + EuclideanSpace.single i (t - x i)) (EuclideanSpace.single i (1 : ℝ)) := by
  -- Proof comment: this is just the continuity of `x ↦ f' x eᵢ` pulled back along the affine
  -- coordinate line through `x`.
  exact (hcont (EuclideanSpace.single i (1 : ℝ))).comp (continuous_coordinateLine_local x i)

/-- Helper for `Corollary 25.35`: each coordinate of a Euclidean vector is bounded by the ambient
Euclidean norm. -/
private theorem abs_coordinate_le_norm_local
    (h : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    |h i| ≤ ‖h‖ := by
  -- Proof comment: the square of one coordinate is bounded by the full sum of coordinate squares,
  -- and the Euclidean norm is the square root of that sum.
  have hsq :
      (h i) ^ 2 ≤ ∑ j : Fin d, (h j) ^ 2 := by
    simpa using
      (Finset.single_le_sum (fun j _ ↦ sq_nonneg (h j)) (by simp : i ∈ (Finset.univ : Finset (Fin d))) :
        (h i) ^ 2 ≤ ∑ j in (Finset.univ : Finset (Fin d)), (h j) ^ 2)
  rw [← EuclideanSpace.real_norm_sq_eq h] at hsq
  nlinarith [hsq, abs_nonneg (h i), norm_nonneg h]

/-- Helper for `Corollary 25.35`: a finite coordinate partial sum is bounded by its cardinality
times the norm of the full increment vector. -/
private theorem norm_coordinateSum_le_card_mul_norm_local
    (h : EuclideanSpace ℝ (Fin d)) (A : Finset (Fin d)) :
    ‖∑ j in A, EuclideanSpace.single j (h j)‖ ≤ (A.card : ℝ) * ‖h‖ := by
  -- Proof comment: bound the norm of the coordinate sum by the sum of the norms of its terms, and
  -- bound each coordinate term by the ambient norm of `h`.
  calc
    ‖∑ j in A, EuclideanSpace.single j (h j)‖
        ≤ ∑ j in A, ‖EuclideanSpace.single j (h j)‖ := norm_sum_le _ _
    _ = ∑ j in A, |h j| := by simp
    _ ≤ ∑ _j in A, ‖h‖ := by
          refine Finset.sum_le_sum fun j hj ↦ ?_
          exact abs_coordinate_le_norm_local h j
    _ = (A.card : ℝ) * ‖h‖ := by simp

/-- Helper for `Corollary 25.35`: continuous coordinate-line derivatives on
`EuclideanSpace ℝ (Fin d)` assemble into the Fréchet derivative determined by the corresponding
coordinate coefficients. -/
private theorem hasFDerivAt_of_continuousCoordinateLineDerivs
    (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (f' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
    (hcont :
      ∀ v : EuclideanSpace ℝ (Fin d),
        Continuous fun x : EuclideanSpace ℝ (Fin d) ↦ f' x v)
    (hcoord :
      ∀ x : EuclideanSpace ℝ (Fin d), ∀ i : Fin d,
        HasDerivAt
          (fun t : ℝ ↦ f (x + EuclideanSpace.single i (t - x i)))
          (f' x (EuclideanSpace.single i (1 : ℝ)))
          (x i)) :
    ∀ x : EuclideanSpace ℝ (Fin d), HasFDerivAt f (f' x) x := by
  classical
  intro x
  -- Route correction: the old proof hole was hidden inside the frozen-slice `C²` theorem. The
  -- actual unresolved step is this finite-dimensional coordinate-to-Fréchet bridge.
  by_cases hd : d = 0
  · subst hd
    -- Proof comment: in dimension `0`, the domain is a subsingleton, so every map is
    -- automatically Fréchet differentiable.
    exact hasFDerivAt_of_subsingleton f x
  let coeff : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) :=
    fun z i ↦ f' z (EuclideanSpace.single i (1 : ℝ))
  have hcoeffCont : Continuous coeff := by
    -- Proof comment: the coordinate coefficient vector is continuous because each basis-vector
    -- evaluation of `f'` is continuous by assumption.
    refine continuous_pi fun i ↦ ?_
    simpa [coeff] using hcont (EuclideanSpace.single i (1 : ℝ))
  refine HasFDerivAt.of_isLittleO ?_
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  have hdR : 0 < (d : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hd
  let η : ℝ := ε / (d : ℝ)
  have hη : 0 < η := by
    positivity
  obtain ⟨δ, hδpos, hδcoeff⟩ :=
    Metric.mem_nhds_iff.mp (hcoeffCont.continuousAt (Metric.ball_mem_nhds _ hη))
  let ρ : ℝ := δ / (d : ℝ)
  have hρpos : 0 < ρ := by
    positivity
  refine Metric.eventually_nhds_iff.mpr ⟨ρ, hρpos, ?_⟩
  intro y hy
  let h : EuclideanSpace ℝ (Fin d) := y - x
  have hyh : ‖h‖ < ρ := by
    simpa [h, dist_eq_norm] using hy
  have hcoeffBound :
      ∀ z : EuclideanSpace ℝ (Fin d), ‖z - x‖ < δ →
        ∀ i : Fin d,
          |f' z (EuclideanSpace.single i (1 : ℝ)) - f' x (EuclideanSpace.single i (1 : ℝ))| ≤ η := by
    intro z hz i
    have hz' : dist (coeff z) (coeff x) < η := by
      apply hδcoeff
      simpa [dist_eq_norm] using hz
    have hcoordNorm :
        |(coeff z - coeff x) i| ≤ ‖coeff z - coeff x‖ :=
      abs_coordinate_le_norm_local (coeff z - coeff x) i
    have hcoordEq :
        (coeff z - coeff x) i =
          f' z (EuclideanSpace.single i (1 : ℝ)) -
            f' x (EuclideanSpace.single i (1 : ℝ)) := by
      simp [coeff]
    rw [hcoordEq, abs_sub_comm]
    exact hcoordNorm.trans (le_of_lt (by simpa [dist_eq_norm] using hz'))
  let S : Finset (Fin d) → EuclideanSpace ℝ (Fin d) := fun A ↦
    x + ∑ j in A, EuclideanSpace.single j (h j)
  have hprefixBound :
      ∀ A : Finset (Fin d),
        |f (S A) - f x - f' x (∑ j in A, EuclideanSpace.single j (h j))| ≤
          (A.card : ℝ) * η * ‖h‖ := by
    intro A
    refine Finset.induction_on A ?_ ?_
    · -- Proof comment: the empty coordinate set produces no increment and no error.
      simp [S]
    · intro i A hiA hA
      let a : ℝ := (S A) i
      let b : ℝ := a + h i
      let q : ℝ → ℝ := fun t ↦ f (S A + EuclideanSpace.single i (t - a))
      let φ : ℝ →L[ℝ] ℝ :=
        ContinuousLinearMap.toSpanSingleton ℝ (f' x (EuclideanSpace.single i (1 : ℝ)))
      have ha : a = x i := by
        -- Proof comment: before the `i`-th step, the `i`-th coordinate has not moved yet.
        simp [a, S, hiA]
      have hq :
          ∀ t ∈ Set.Icc (min a b) (max a b),
            HasFDerivWithinAt q
              (ContinuousLinearMap.toSpanSingleton ℝ
                (f' (S A + EuclideanSpace.single i (t - a))
                  (EuclideanSpace.single i (1 : ℝ))))
              (Set.Icc (min a b) (max a b))
              t := by
        intro t ht
        -- Proof comment: each cell is exactly a one-variable coordinate line through the current
        -- prefix point, so the recentered coordinate derivative applies directly.
        simpa [q, a] using
          (hasDerivAt_coordinateLine_recentered f f' hcoord (S A) i t).hasFDerivAt.hasFDerivWithinAt
      have hqBound :
          ∀ t ∈ Set.Icc (min a b) (max a b),
            ‖ContinuousLinearMap.toSpanSingleton ℝ
                (f' (S A + EuclideanSpace.single i (t - a))
                    (EuclideanSpace.single i (1 : ℝ))) - φ‖ ≤ η := by
        intro t ht
        have htCoord : |t - a| ≤ ‖h‖ := by
          have htAbs : |t - a| ≤ |h i| := by
            by_cases hhi : 0 ≤ h i
            · have hmin : min a b = a := by
                simp [b, hhi]
              have hmax : max a b = a + h i := by
                simp [b, hhi]
              rw [hmin, hmax] at ht
              nlinarith
            · have hhi' : h i ≤ 0 := le_of_not_ge hhi
              have hmin : min a b = a + h i := by
                simp [b, hhi']
              have hmax : max a b = a := by
                simp [b, hhi']
              rw [hmin, hmax] at ht
              nlinarith
          exact htAbs.trans (abs_coordinate_le_norm_local h i)
        have hzNorm :
            ‖(S A + EuclideanSpace.single i (t - a)) - x‖ ≤ ((A.card : ℝ) + 1) * ‖h‖ := by
          have hzEq :
              (S A + EuclideanSpace.single i (t - a)) - x =
                (∑ j in A, EuclideanSpace.single j (h j)) +
                  EuclideanSpace.single i (t - a) := by
            simp [S, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
          rw [hzEq]
          calc
            ‖(∑ j in A, EuclideanSpace.single j (h j)) + EuclideanSpace.single i (t - a)‖
                ≤ ‖∑ j in A, EuclideanSpace.single j (h j)‖ +
                    ‖EuclideanSpace.single i (t - a)‖ := norm_add_le _ _
            _ ≤ (A.card : ℝ) * ‖h‖ + ‖EuclideanSpace.single i (t - a)‖ := by
                  gcongr
                  exact norm_coordinateSum_le_card_mul_norm_local h A
            _ = (A.card : ℝ) * ‖h‖ + |t - a| := by simp
            _ ≤ (A.card : ℝ) * ‖h‖ + ‖h‖ := by
                  gcongr
            _ = ((A.card : ℝ) + 1) * ‖h‖ := by ring
        have hcard : ((A.card : ℝ) + 1) ≤ (d : ℝ) := by
          have hcardNat : A.card + 1 ≤ d := by
            exact Nat.succ_le_of_lt (Finset.card_lt_univ hiA)
          exact_mod_cast hcardNat
        have hz : ‖(S A + EuclideanSpace.single i (t - a)) - x‖ < δ := by
          have hdMul : (d : ℝ) * ‖h‖ < δ := by
            have : ‖h‖ < δ / (d : ℝ) := by
              simpa [ρ] using hyh
            nlinarith [hdR, this]
          exact lt_of_le_of_lt (hzNorm.trans (by gcongr)) hdMul
        simpa [φ] using
          (show
            ‖ContinuousLinearMap.toSpanSingleton ℝ
                (f' (S A + EuclideanSpace.single i (t - a))
                    (EuclideanSpace.single i (1 : ℝ)) -
                  f' x (EuclideanSpace.single i (1 : ℝ)))‖ ≤ η from by
              simpa using hcoeffBound (S A + EuclideanSpace.single i (t - a)) hz i)
      have hcell :
          |f (S A + EuclideanSpace.single i (h i)) - f (S A) -
              f' x (EuclideanSpace.single i (h i))| ≤
            η * ‖EuclideanSpace.single i (h i)‖ := by
        -- Proof comment: the one-dimensional mean value inequality controls the current cell by
        -- the oscillation of the `i`-th coordinate coefficient on that cell.
        simpa [q, φ, a, b, ContinuousLinearMap.toSpanSingleton_apply, sub_eq_add_neg, add_assoc,
          add_left_comm, add_comm, mul_comm, mul_left_comm, mul_assoc] using
          (convex_Icc (min a b) (max a b)).norm_image_sub_le_of_norm_hasFDerivWithin_le'
            (f := q)
            (f' := fun t ↦
              ContinuousLinearMap.toSpanSingleton ℝ
                (f' (S A + EuclideanSpace.single i (t - a))
                  (EuclideanSpace.single i (1 : ℝ))))
            (φ := φ) (C := η) hq hqBound (by simp) (by simp)
      have hsplit :
          f (S (insert i A)) - f x -
              f' x (∑ j in insert i A, EuclideanSpace.single j (h j)) =
            (f (S A + EuclideanSpace.single i (h i)) - f (S A) -
                f' x (EuclideanSpace.single i (h i))) +
              (f (S A) - f x - f' x (∑ j in A, EuclideanSpace.single j (h j))) := by
        -- Proof comment: split the enlarged prefix error into the new `i`-cell error plus the
        -- previously accumulated prefix error.
        simp [S, hiA, Finset.sum_insert, map_add, sub_eq_add_neg, add_assoc, add_left_comm,
          add_comm]
        ring
      rw [hsplit]
      calc
        |(f (S A + EuclideanSpace.single i (h i)) - f (S A) -
              f' x (EuclideanSpace.single i (h i))) +
            (f (S A) - f x - f' x (∑ j in A, EuclideanSpace.single j (h j)))|
            ≤
              |f (S A + EuclideanSpace.single i (h i)) - f (S A) -
                  f' x (EuclideanSpace.single i (h i))| +
                |f (S A) - f x - f' x (∑ j in A, EuclideanSpace.single j (h j))| := by
                  exact abs_add _ _
        _ ≤ η * ‖EuclideanSpace.single i (h i)‖ + (A.card : ℝ) * η * ‖h‖ := by
              gcongr
        _ = η * |h i| + (A.card : ℝ) * η * ‖h‖ := by simp
        _ ≤ η * ‖h‖ + (A.card : ℝ) * η * ‖h‖ := by
              gcongr
              exact abs_coordinate_le_norm_local h i
        _ = ((A.card + 1 : ℕ) : ℝ) * η * ‖h‖ := by ring
  have hsumAll : ∑ j : Fin d, EuclideanSpace.single j (h j) = h := by
    -- Proof comment: summing all coordinate basis contributions reconstructs the increment
    -- vector `h = y - x`.
    ext j
    simp
  have hS_univ : S (Finset.univ : Finset (Fin d)) = y := by
    -- Proof comment: the full coordinate prefix is the endpoint `y`.
    simp [S, hsumAll, h, add_sub_cancel]
  have hfinal :
      |f y - f x - f' x (y - x)| ≤ ε * ‖y - x‖ := by
    have hfinal' := hprefixBound (Finset.univ : Finset (Fin d))
    have hright : (((Finset.univ : Finset (Fin d)).card : ℝ) * η * ‖h‖) = ε * ‖h‖ := by
      simp [η, hdR.ne']
    rw [hS_univ, hsumAll, hright] at hfinal'
    simpa [h] using hfinal'
  simpa [dist_eq_norm, h] using hfinal

/-- Helper for `Corollary 25.35`: each frozen time slice `x ↦ F (x, s)` is `C²` in the spatial
variable. -/
private theorem contDiffFrozenSlice_of_isTimeSpaceC21
    (F : EuclideanSpace ℝ (Fin d) × ℝ → ℝ)
    (hF : IsTimeSpaceC21 F)
    (s : ℝ) :
    ContDiff ℝ 2 (fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, s)) := by
  -- Proof comment: after isolating the coordinate-to-Fréchet upgrade in one reusable bridge, the
  -- frozen-slice `C²` theorem is just an application of `contDiffFrozenSlice_of_bridges`.
  refine contDiffFrozenSlice_of_bridges F hF s ?_ ?_
  · intro x
    exact
      hasFDerivAt_of_continuousCoordinateLineDerivs
        (f := fun y : EuclideanSpace ℝ (Fin d) ↦ F (y, s))
        (f' := frozenSliceFDeriv F s)
        (hcont := fun v ↦ continuous_frozenSliceFDeriv_apply F hF s v)
        (hcoord := fun x i ↦ hasDerivAt_frozenSliceAlongCoordinate F hF s x i)
        x
  · intro i x
    exact
      hasFDerivAt_of_continuousCoordinateLineDerivs
        (f := fun y : EuclideanSpace ℝ (Fin d) ↦
          (∂[i] fun z : EuclideanSpace ℝ (Fin d) ↦ F (z, s)) y)
        (f' := frozenSliceSecondFDeriv F s i)
        (hcont := fun v ↦ continuous_frozenSliceSecondFDeriv_apply F hF s i v)
        (hcoord := fun x j ↦ hasDerivAt_frozenSlicePartialAlongCoordinate F hF s i j x)
        x

/-- Helper for `Corollary 25.35`: on each frozen time slice, the Laplacian is the sum of the
diagonal second spatial partials. -/
private theorem laplacian_eq_sumSecondPartials_timeSlice
    (F : EuclideanSpace ℝ (Fin d) × ℝ → ℝ)
    (hF : IsTimeSpaceC21 F)
    (s : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    Δ (fun y : EuclideanSpace ℝ (Fin d) ↦ F (y, s)) x =
      ∑ i : Fin d, (∂²[i, i] fun y : EuclideanSpace ℝ (Fin d) ↦ F (y, s)) x := by
  -- Proof comment: once the frozen slice is recognized as `C²`, the diagonal Laplacian formula
  -- is exactly the already-proved `ContDiff`-level lemma above.
  simpa using
    laplacian_eq_sumSecondPartials_of_contDiff
      (G := fun y : EuclideanSpace ℝ (Fin d) ↦ F (y, s))
      (contDiffFrozenSlice_of_isTimeSpaceC21 F hF s)
      x

/-- Helper for `Corollary 25.35`: the deterministic drift written with time derivative plus the
diagonal second spatial partials is the textbook drift with the Laplacian. -/
private theorem timeSpaceDrift_eq_laplacianIntegral
    (F : EuclideanSpace ℝ (Fin d) × ℝ → ℝ)
    {W : NNReal → Ω → EuclideanSpace ℝ (Fin d)}
    (hF : IsTimeSpaceC21 F)
    (hW : IsStandardBrownianMotionVector μ W)
    (T : NNReal) (ω : Ω) :
    (∫ s in Set.Icc (0 : ℝ) (T : ℝ),
        (∂ₜ F) (standardBrownianMotionVectorContinuousVersion hW s.toNNReal ω, s)) +
      ((1 : ℝ) / 2) *
        ∑ i : Fin d,
          ∫ s in Set.Icc (0 : ℝ) (T : ℝ),
            (∂²[i, i] fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, s))
              (standardBrownianMotionVectorContinuousVersion hW s.toNNReal ω)
      =
      ∫ s in Set.Icc (0 : ℝ) (T : ℝ),
        (∂ₜ F) (standardBrownianMotionVectorContinuousVersion hW s.toNNReal ω, s) +
          ((1 : ℝ) / 2) *
            Δ (fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, s))
              (standardBrownianMotionVectorContinuousVersion hW s.toNNReal ω) := by
  let Wc := standardBrownianMotionVectorContinuousVersion hW
  have hWcCont : Continuous fun s : ℝ ↦ Wc s.toNNReal ω := by
    have hcoords :
        Continuous
          (fun s : ℝ ↦ fun i : Fin d ↦ (Wc s.toNNReal ω).ofLp i) := by
      exact continuous_pi fun i ↦
        (brownianContinuousCoordinate_continuous_local (μ := μ) hW i ω).comp
          continuous_real_toNNReal
    simpa [Wc] using
      (PiLp.continuous_toLp 2 (fun _ : Fin d ↦ ℝ)).comp hcoords
  have hTimeCont :
      Continuous fun s : ℝ ↦ (∂ₜ F) (Wc s.toNNReal ω, s) := by
    -- Proof comment: the time derivative field is continuous on space-time, and the frozen graph
    -- path `s ↦ (Wc_s, s)` is continuous on `ℝ`.
    exact hF.continuous_timePartialDeriv.comp (hWcCont.prodMk continuous_id)
  have hSecondCont :
      ∀ i : Fin d,
        Continuous fun s : ℝ ↦
          (∂²[i, i] fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, s))
            (Wc s.toNNReal ω) := by
    intro i
    -- Proof comment: each diagonal spatial second partial is continuous on space-time, so
    -- pulling it back along the continuous Brownian graph gives a continuous scalar weight.
    exact (hF.continuous_spaceSecondPartialDeriv i i).comp (hWcCont.prodMk continuous_id)
  have hDiagSumCont :
      Continuous fun s : ℝ ↦
        ∑ i : Fin d,
          (∂²[i, i] fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, s))
            (Wc s.toNNReal ω) := by
    -- Proof comment: the finite diagonal Hessian sum inherits continuity termwise.
    refine continuous_finset_sum _ fun i _ ↦ ?_
    exact hSecondCont i
  have hScaledLaplacianEq :
      (fun s : ℝ ↦
        ((1 : ℝ) / 2) *
          Δ (fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, s))
            (Wc s.toNNReal ω)) =
      (fun s : ℝ ↦
        ((1 : ℝ) / 2) *
          ∑ i : Fin d,
            (∂²[i, i] fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, s))
              (Wc s.toNNReal ω)) := by
    funext s
    rw [laplacian_eq_sumSecondPartials_timeSlice F hF s (Wc s.toNNReal ω)]
  have hScaledLaplacianCont :
      Continuous fun s : ℝ ↦
        ((1 : ℝ) / 2) *
          Δ (fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, s))
            (Wc s.toNNReal ω) := by
    -- Proof comment: rewrite the Laplacian term to the diagonal second-partial sum and use the
    -- continuity already established for that finite sum.
    rw [hScaledLaplacianEq]
    exact continuous_const.mul hDiagSumCont
  have hTimeInt :
      IntegrableOn
        (fun s : ℝ ↦ (∂ₜ F) (Wc s.toNNReal ω, s))
        (Set.Icc (0 : ℝ) (T : ℝ)) := by
    exact hTimeCont.integrableOn_Icc
  have hSecondInt :
      ∀ i : Fin d,
        IntegrableOn
          (fun s : ℝ ↦
            (∂²[i, i] fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, s))
              (Wc s.toNNReal ω))
          (Set.Icc (0 : ℝ) (T : ℝ)) := by
    intro i
    exact (hSecondCont i).integrableOn_Icc
  have hScaledLaplacianInt :
      IntegrableOn
        (fun s : ℝ ↦
          ((1 : ℝ) / 2) *
            Δ (fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, s))
              (Wc s.toNNReal ω))
        (Set.Icc (0 : ℝ) (T : ℝ)) := by
    exact hScaledLaplacianCont.integrableOn_Icc
  calc
    (∫ s in Set.Icc (0 : ℝ) (T : ℝ), (∂ₜ F) (Wc s.toNNReal ω, s)) +
        ((1 : ℝ) / 2) *
          ∑ i : Fin d,
            ∫ s in Set.Icc (0 : ℝ) (T : ℝ),
              (∂²[i, i] fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, s))
                (Wc s.toNNReal ω)
      =
        (∫ s in Set.Icc (0 : ℝ) (T : ℝ), (∂ₜ F) (Wc s.toNNReal ω, s)) +
          ∫ s in Set.Icc (0 : ℝ) (T : ℝ),
            ((1 : ℝ) / 2) *
              ∑ i : Fin d,
                (∂²[i, i] fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, s))
                  (Wc s.toNNReal ω) := by
          congr 1
          calc
            ((1 : ℝ) / 2) *
                ∑ i : Fin d,
                  ∫ s in Set.Icc (0 : ℝ) (T : ℝ),
                    (∂²[i, i] fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, s))
                      (Wc s.toNNReal ω)
              =
                ((1 : ℝ) / 2) *
                  ∫ s in Set.Icc (0 : ℝ) (T : ℝ),
                    ∑ i : Fin d,
                      (∂²[i, i] fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, s))
                        (Wc s.toNNReal ω) := by
                    congr 1
                    symm
                    exact integral_finset_sum Finset.univ fun i _ ↦ hSecondInt i
            _ =
                ∫ s in Set.Icc (0 : ℝ) (T : ℝ),
                  ((1 : ℝ) / 2) *
                    ∑ i : Fin d,
                      (∂²[i, i] fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, s))
                        (Wc s.toNNReal ω) := by
                    symm
                    exact integral_const_mul ((1 : ℝ) / 2) fun s : ℝ ↦
                      ∑ i : Fin d,
                        (∂²[i, i] fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, s))
                          (Wc s.toNNReal ω)
    _ =
        (∫ s in Set.Icc (0 : ℝ) (T : ℝ), (∂ₜ F) (Wc s.toNNReal ω, s)) +
          ∫ s in Set.Icc (0 : ℝ) (T : ℝ),
            ((1 : ℝ) / 2) *
              Δ (fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, s))
                (Wc s.toNNReal ω) := by
          congr 1
          refine integral_congr_ae ?_
          refine (ae_restrict_iff' measurableSet_Icc).2 <| Filter.Eventually.of_forall ?_
          intro s hs
          rw [laplacian_eq_sumSecondPartials_timeSlice F hF s (Wc s.toNNReal ω)]
    _ =
        ∫ s in Set.Icc (0 : ℝ) (T : ℝ),
          (∂ₜ F) (Wc s.toNNReal ω, s) +
            ((1 : ℝ) / 2) *
              Δ (fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, s))
                (Wc s.toNNReal ω) := by
          symm
          exact integral_add hTimeInt hScaledLaplacianInt

/-- Helper for `Corollary 25.35`: one time-residual cell is the interval integral of the time
derivative error with the spatial point frozen at the right endpoint. -/
private theorem timeSpaceC21TimeResidual_cell_eq_intervalIntegral
    (F : EuclideanSpace ℝ (Fin d) × ℝ → ℝ)
    (hF : IsTimeSpaceC21 F)
    {W : NNReal → Ω → EuclideanSpace ℝ (Fin d)}
    (hW : IsStandardBrownianMotionVector μ W)
    (T : NNReal) (ω : Ω) (n k : ℕ)
    (hk : k < partitionBoundIndex Definition2158.dyadicPartitionSequence n T) :
    let Wc := standardBrownianMotionVectorContinuousVersion hW
    let t0 := Definition2158.dyadicPartitionSequence n k
    let t1 := partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T
    F (Wc t1 ω, (t1 : ℝ)) - F (Wc t1 ω, (t0 : ℝ)) -
        (∂ₜ F) (Wc t0 ω, (t0 : ℝ)) * ((t1 : ℝ) - (t0 : ℝ)) =
      ∫ s in (t0 : ℝ)..(t1 : ℝ),
        (∂ₜ F) (Wc t1 ω, s) - (∂ₜ F) (Wc t0 ω, (t0 : ℝ)) := by
  let Wc := standardBrownianMotionVectorContinuousVersion hW
  let t0 := Definition2158.dyadicPartitionSequence n k
  let t1 := partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T
  have ht0_le_t1 : t0 ≤ t1 := by
    refine le_min ?_ ?_
    · exact le_of_lt ((instStrictMono_of_isAdmissiblePartitionSequence
        (P := Definition2158.dyadicPartitionSequence) n) (Nat.lt_succ_self k))
    · exact
        (partitionPoint_mem_Icc_of_lt_partitionBoundIndex
          Definition2158.dyadicPartitionSequence n k T hk).2
  let c : ℝ := (∂ₜ F) (Wc t0 ω, (t0 : ℝ))
  let g : ℝ → ℝ := fun s ↦ F (Wc t1 ω, s) - c * s
  have hderiv :
      ∀ s ∈ Set.Icc (t0 : ℝ) (t1 : ℝ),
        HasDerivAt g ((∂ₜ F) (Wc t1 ω, s) - c) s := by
    intro s hs
    have htime : HasDerivAt (fun u : ℝ ↦ F (Wc t1 ω, u)) ((∂ₜ F) (Wc t1 ω, s)) s := by
      simpa [Wc, t1] using hF.hasDerivAt_time (Wc t1 ω, s)
    have hlin : HasDerivAt (fun u : ℝ ↦ c * u) c s := by
      simpa [one_mul] using (hasDerivAt_id s).const_mul c
    -- Proof comment: subtract the fixed linear correction so the derivative becomes exactly the
    -- time-derivative error on the current cell.
    simpa [g, c, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using htime.sub hlin
  have hcont :
      ContinuousOn (fun s : ℝ ↦ (∂ₜ F) (Wc t1 ω, s) - c) (Set.Icc (t0 : ℝ) (t1 : ℝ)) := by
    -- Proof comment: along the frozen spatial point `Wc t1 ω`, the time derivative is
    -- continuous, and subtracting the constant left-point coefficient preserves continuity.
    exact
      ((hF.continuous_timePartialDeriv.comp
        (continuous_const.prodMk continuous_id)).sub continuous_const).continuousOn
  have hint :
      IntervalIntegrable (fun s : ℝ ↦ (∂ₜ F) (Wc t1 ω, s) - c) volume (t0 : ℝ) (t1 : ℝ) := by
    exact hcont.intervalIntegrable
  have hFTC :
      ∫ s in (t0 : ℝ)..(t1 : ℝ), ((∂ₜ F) (Wc t1 ω, s) - c) =
        g (t1 : ℝ) - g (t0 : ℝ) := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht0_le_t1 hcont hderiv hint
  -- Proof comment: after the FTC rewrite, expanding the affine correction recovers the stated
  -- cellwise residual identity.
  simpa [g, c, t0, t1, Wc, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm,
    mul_left_comm, mul_assoc] using hFTC.symm

/-- Helper for `Corollary 25.35`: the theorem-local dyadic remainder tends to `0` along the full
dyadic sequence. -/
private theorem tendsto_timeSpaceC21TimeResidual_zero
    (F : EuclideanSpace ℝ (Fin d) × ℝ → ℝ)
    (hF : IsTimeSpaceC21 F)
    {W : NNReal → Ω → EuclideanSpace ℝ (Fin d)}
    (hW : IsStandardBrownianMotionVector μ W)
    (T : NNReal) :
    ∀ᵐ ω ∂μ,
      Tendsto
        (fun n ↦ timeSpaceC21TimeResidual (μ := μ) F hW T ω n)
        atTop
        (𝓝 0) := by
  let Wc := standardBrownianMotionVectorContinuousVersion hW
  have hWcCont : Continuous fun s : ℝ ↦ Wc s.toNNReal ω := by
    have hcoords :
        Continuous
          (fun s : ℝ ↦ fun i : Fin d ↦ (Wc s.toNNReal ω).ofLp i) := by
      exact continuous_pi fun i ↦
        (brownianContinuousCoordinate_continuous_local (μ := μ) hW i ω).comp
          continuous_real_toNNReal
    simpa [Wc] using
      (PiLp.continuous_toLp 2 (fun _ : Fin d ↦ ℝ)).comp hcoords
  refine Filter.Eventually.of_forall ?_
  intro ω
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  let η : ℝ := ε / ((T : ℝ) + 1)
  have hη_pos : 0 < η := by
    dsimp [η]
    positivity
  let q : ℝ × ℝ → ℝ := fun p ↦ (∂ₜ F) (Wc p.1.toNNReal ω, p.2)
  have hqCont : Continuous q := by
    exact hF.continuous_timePartialDeriv.comp
      ((hWcCont.comp continuous_fst).prodMk continuous_snd)
  have hqUC :
      UniformContinuousOn q
        (Set.Icc (0 : ℝ) (T : ℝ) ×ˢ Set.Icc (0 : ℝ) (T : ℝ)) := by
    exact ((isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) (T : ℝ))).prod
      (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) (T : ℝ))))
      .uniformContinuousOn_of_continuous hqCont.continuousOn
  rcases (Metric.uniformContinuousOn_iff_le.mp hqUC) η hη_pos with ⟨δ, hδ_pos, hδ_spec⟩
  have hmesh :
      ∀ᶠ n in atTop,
        partitionMesh Definition2158.dyadicPartitionSequence n ≤ ENNReal.ofReal δ := by
    exact
      (ENNReal.tendsto_atTop_zero.mp
        Definition2158.tendsto_partitionMesh_dyadicPartitionSequence)
        (ENNReal.ofReal δ)
        (ENNReal.ofReal_pos.mpr hδ_pos)
  rcases Filter.eventually_atTop.1 hmesh with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hbound :
      |timeSpaceC21TimeResidual (μ := μ) F hW T ω n| ≤ η * (T : ℝ) := by
    have hsum :
        |timeSpaceC21TimeResidual (μ := μ) F hW T ω n|
          ≤
            Finset.sum
              (Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n T))
              (fun k ↦
                η *
                  ((partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T : ℝ) -
                    (Definition2158.dyadicPartitionSequence n k : ℝ))) := by
      -- Proof comment: each cell is an interval integral of the time-derivative error, and
      -- uniform continuity along the Brownian graph makes that error uniformly small on fine rows.
      calc
        |timeSpaceC21TimeResidual (μ := μ) F hW T ω n|
            =
              |Finset.sum
                  (Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n T))
                  (fun k ↦
                    let t0 := Definition2158.dyadicPartitionSequence n k
                    let t1 := partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T
                    F (Wc t1 ω, (t1 : ℝ)) - F (Wc t1 ω, (t0 : ℝ)) -
                      (∂ₜ F) (Wc t0 ω, (t0 : ℝ)) * ((t1 : ℝ) - (t0 : ℝ))) := by
                simp [timeSpaceC21TimeResidual, Wc]
        _ ≤
            Finset.sum
              (Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n T))
              (fun k ↦
                |
                  let t0 := Definition2158.dyadicPartitionSequence n k
                  let t1 := partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T
                  F (Wc t1 ω, (t1 : ℝ)) - F (Wc t1 ω, (t0 : ℝ)) -
                    (∂ₜ F) (Wc t0 ω, (t0 : ℝ)) * ((t1 : ℝ) - (t0 : ℝ))
                |) := by
                simpa using
                  (Finset.abs_sum_le_sum_abs
                    (fun k : ℕ ↦
                      let t0 := Definition2158.dyadicPartitionSequence n k
                      let t1 := partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T
                      F (Wc t1 ω, (t1 : ℝ)) - F (Wc t1 ω, (t0 : ℝ)) -
                        (∂ₜ F) (Wc t0 ω, (t0 : ℝ)) * ((t1 : ℝ) - (t0 : ℝ)))
                    (Finset.range
                      (partitionBoundIndex Definition2158.dyadicPartitionSequence n T)))
        _ ≤
            Finset.sum
              (Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n T))
              (fun k ↦
                η *
                  ((partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T : ℝ) -
                    (Definition2158.dyadicPartitionSequence n k : ℝ))) := by
                refine Finset.sum_le_sum ?_
                intro k hk
                have hk_lt : k < partitionBoundIndex Definition2158.dyadicPartitionSequence n T :=
                  Finset.mem_range.mp hk
                let t0 := Definition2158.dyadicPartitionSequence n k
                let t1 := partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T
                have ht0_le_t1 : t0 ≤ t1 := by
                  refine le_min ?_ ?_
                  · exact le_of_lt ((instStrictMono_of_isAdmissiblePartitionSequence
                      (P := Definition2158.dyadicPartitionSequence) n) (Nat.lt_succ_self k))
                  · exact
                      (partitionPoint_mem_Icc_of_lt_partitionBoundIndex
                        Definition2158.dyadicPartitionSequence n k T hk_lt).2
                have ht0_mem :
                    (t0 : ℝ) ∈ Set.Icc (0 : ℝ) (T : ℝ) := by
                  exact partitionPoint_mem_Icc_of_lt_partitionBoundIndex
                    Definition2158.dyadicPartitionSequence n k T hk_lt
                have ht1_mem :
                    (t1 : ℝ) ∈ Set.Icc (0 : ℝ) (T : ℝ) := by
                  exact partitionNextPointUpTo_mem_Icc_of_lt_partitionBoundIndex
                    Definition2158.dyadicPartitionSequence n k T hk_lt
                have htDistNN : dist t0 t1 ≤ δ := by
                  have hedist :
                      edist t0 t1 ≤ ENNReal.ofReal δ := by
                    exact
                      (edist_partitionPoint_partitionNextPointUpTo_le_truncationMesh
                        Definition2158.dyadicPartitionSequence n k T hk_lt).trans
                        (hN n hn)
                  exact (edist_le_ofReal (le_of_lt hδ_pos)).1 hedist
                have htDist :
                    dist (t0 : ℝ) (t1 : ℝ) ≤ δ := by
                  simpa [NNReal.dist_eq, Real.dist_eq, abs_of_nonneg ht0_le_t1] using htDistNN
                have hcellEq :=
                  timeSpaceC21TimeResidual_cell_eq_intervalIntegral
                    (μ := μ) F hF hW T ω n k hk_lt
                calc
                  |
                    let t0 := Definition2158.dyadicPartitionSequence n k
                    let t1 := partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T
                    F (Wc t1 ω, (t1 : ℝ)) - F (Wc t1 ω, (t0 : ℝ)) -
                      (∂ₜ F) (Wc t0 ω, (t0 : ℝ)) * ((t1 : ℝ) - (t0 : ℝ))
                  |
                      =
                    |∫ s in (t0 : ℝ)..(t1 : ℝ),
                        (∂ₜ F) (Wc t1 ω, s) - (∂ₜ F) (Wc t0 ω, (t0 : ℝ))| := by
                          simpa [t0, t1, Wc] using congrArg abs hcellEq
                  _ ≤
                      η * |(t1 : ℝ) - (t0 : ℝ)| := by
                        simpa [Real.norm_eq_abs] using
                          (intervalIntegral.norm_integral_le_of_norm_le_const
                            (a := (t0 : ℝ)) (b := (t1 : ℝ))
                            (f := fun s : ℝ ↦
                              (∂ₜ F) (Wc t1 ω, s) - (∂ₜ F) (Wc t0 ω, (t0 : ℝ)))
                            (fun s hs ↦ by
                              have hs_mem : s ∈ Set.Icc (0 : ℝ) (T : ℝ) := by
                                constructor
                                · exact le_trans ht0_mem.1 hs.1
                                · exact le_trans hs.2 ht1_mem.2
                              have hsDist :
                                  dist s (t0 : ℝ) ≤ δ := by
                                rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hs.1)]
                                exact le_trans (by linarith) htDist
                              have hProdDist :
                                  dist ((t1 : ℝ), s) ((t0 : ℝ), (t0 : ℝ)) ≤ δ := by
                                simpa [Prod.dist_eq, dist_self, max_eq_left hsDist] using
                                  max_le htDist hsDist
                              have hqBound :=
                                hδ_spec
                                  ((t1 : ℝ), s)
                                  ⟨ht1_mem, hs_mem⟩
                                  ((t0 : ℝ), (t0 : ℝ))
                                  ⟨ht0_mem, ht0_mem⟩
                                  hProdDist
                              simpa [q, Wc, t0, t1] using hqBound))
                  _ = η * ((t1 : ℝ) - (t0 : ℝ)) := by
                        rw [abs_of_nonneg (sub_nonneg.mpr ht0_le_t1)]
    have hlength :
        Finset.sum
            (Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n T))
            (fun k ↦
              ((partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T : ℝ) -
                (Definition2158.dyadicPartitionSequence n k : ℝ))) =
          (T : ℝ) := by
      simpa [sub_eq_add_neg, IsAdmissiblePartitionSequence.zero_eq
        (P := Definition2158.dyadicPartitionSequence) n] using
        partitionIncrementSum_eq_endpointIncrement_local
          (G := fun t : NNReal ↦ (t : ℝ))
          Definition2158.dyadicPartitionSequence
          T
          n
    calc
      |timeSpaceC21TimeResidual (μ := μ) F hW T ω n|
          ≤
            Finset.sum
              (Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n T))
              (fun k ↦
                η *
                  ((partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T : ℝ) -
                    (Definition2158.dyadicPartitionSequence n k : ℝ))) := hsum
      _ = η *
            Finset.sum
              (Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n T))
              (fun k ↦
                ((partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T : ℝ) -
                  (Definition2158.dyadicPartitionSequence n k : ℝ))) := by
            rw [Finset.mul_sum]
      _ = η * (T : ℝ) := by rw [hlength]
  have hfinal : η * (T : ℝ) < ε := by
    dsimp [η]
    have hT_nonneg : 0 ≤ (T : ℝ) := by positivity
    nlinarith
  exact lt_of_le_of_lt hbound hfinal

/-- Helper for `Corollary 25.35`: a `C²` map has differentiable coordinate partial derivatives. -/
private theorem differentiable_partialDeriv
    (G : EuclideanSpace ℝ (Fin d) → ℝ) (hG : ContDiff ℝ 2 G) (i : Fin d) :
    Differentiable ℝ (∂[i] G) := by
  let ei : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single i (1 : ℝ)
  -- Proof comment: rewrite `∂[i] G` as the Fréchet derivative of `G` evaluated at the basis
  -- vector `eᵢ`, then use the `C²` regularity of `G`.
  have hfd :
      ContDiff ℝ 1 (fun x ↦ (fderiv ℝ G x) ei) := by
    simpa [ei] using
      ((contDiff_succ_iff_fderiv_apply
        (𝕜 := ℝ) (D := EuclideanSpace ℝ (Fin d)) (E := ℝ) (n := 1) (f := G)).mp hG).2.2 ei
  simpa [partialDeriv_eq_fderiv_apply G (hG.differentiable (by norm_num)) i] using
    hfd.differentiable_one

/-- Helper for `Corollary 25.35`: the derivative of an affine line restriction is the coordinate
gradient pairing with the direction vector. -/
private theorem lineDeriv_eq_sum_partialDeriv_mul
    (G : EuclideanSpace ℝ (Fin d) → ℝ)
    (hG : Differentiable ℝ G)
    (x δ : EuclideanSpace ℝ (Fin d)) (s : ℝ) :
    deriv (fun u : ℝ ↦ G (x + u • δ)) s =
      ∑ i : Fin d, (∂[i] G) (x + s • δ) * δ i := by
  let g : ℝ → ℝ := fun u ↦ G (x + u • δ)
  have hshift :
      deriv g s = deriv (fun u : ℝ ↦ G ((x + s • δ) + u • δ)) 0 := by
    -- Proof comment: shift the line derivative to the origin so the standard line-derivative
    -- formula applies directly.
    simpa [g, add_assoc, add_left_comm, add_comm, add_smul] using
      (deriv_comp_const_add (f := g) s 0).symm
  have hline :
      deriv (fun u : ℝ ↦ G ((x + s • δ) + u • δ)) 0 =
        (fderiv ℝ G (x + s • δ)) δ := by
    -- Proof comment: the shifted one-variable derivative is the Fréchet derivative in the
    -- direction `δ`.
    simpa [lineDeriv] using
      ((hG (x + s • δ)).lineDeriv_eq_fderiv (v := δ))
  have hδ :
      δ = ∑ i : Fin d, δ i • EuclideanSpace.single i (1 : ℝ) := by
    -- Proof comment: expand the direction vector in the standard Euclidean basis.
    simpa [EuclideanSpace.basisFun_apply] using
      ((EuclideanSpace.basisFun (Fin d) ℝ).sum_repr δ).symm
  calc
    deriv (fun u : ℝ ↦ G (x + u • δ)) s = (fderiv ℝ G (x + s • δ)) δ := by
      exact hshift.trans hline
    _ =
        (fderiv ℝ G (x + s • δ))
          (∑ i : Fin d, δ i • EuclideanSpace.single i (1 : ℝ)) := by
      exact congrArg (fun v : EuclideanSpace ℝ (Fin d) ↦ (fderiv ℝ G (x + s • δ)) v) hδ
    _ = ∑ i : Fin d,
          (fderiv ℝ G (x + s • δ)) (δ i • EuclideanSpace.single i (1 : ℝ)) := by
      rw [map_sum]
    _ = ∑ i : Fin d, δ i * (fderiv ℝ G (x + s • δ)) (EuclideanSpace.single i (1 : ℝ)) := by
      simp [map_smul, smul_eq_mul]
    _ = ∑ i : Fin d, (∂[i] G) (x + s • δ) * δ i := by
      -- Proof comment: rewrite each Fréchet derivative entry back to the corresponding
      -- coordinate derivative.
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [partialDeriv_eq_fderiv_apply G hG i]
      ring

/-- Helper for `Corollary 25.35`: the second derivative of an affine line restriction is the
coordinate Hessian pairing with the direction vector. -/
private theorem lineSecondDeriv_eq_sum_secondPartialDeriv_mul_mul
    (G : EuclideanSpace ℝ (Fin d) → ℝ) (hG : ContDiff ℝ 2 G)
    (x δ : EuclideanSpace ℝ (Fin d)) (s : ℝ) :
    iteratedDeriv 2 (fun u : ℝ ↦ G (x + u • δ)) s =
      ∑ i : Fin d, ∑ j : Fin d, (∂²[i, j] G) (x + s • δ) * δ i * δ j := by
  have hDiffLine (i : Fin d) :
      DifferentiableAt ℝ (fun u : ℝ ↦ (∂[i] G) (x + u • δ)) s := by
    -- Proof comment: each coordinate partial is differentiable, and composing with the affine
    -- line preserves differentiability.
    exact DifferentiableAt.comp s
      ((differentiable_partialDeriv G hG i) (x + s • δ))
      ((differentiableAt_id.smul_const δ).const_add x)
  have hLinePartial (i : Fin d) :
      deriv (fun u : ℝ ↦ (∂[i] G) (x + u • δ)) s =
        ∑ j : Fin d, (∂²[i, j] G) (x + s • δ) * δ j := by
    -- Proof comment: apply the first line-derivative formula to the partial derivative `∂[i] G`.
    simpa [secondPartialDeriv] using
      (lineDeriv_eq_sum_partialDeriv_mul
        (G := ∂[i] G) (differentiable_partialDeriv G hG i) x δ s)
  calc
    iteratedDeriv 2 (fun u : ℝ ↦ G (x + u • δ)) s =
        deriv (fun u : ℝ ↦ ∑ i : Fin d, (∂[i] G) (x + u • δ) * δ i) s := by
      -- Proof comment: first rewrite the line derivative into the coordinate-gradient expansion.
      rw [iteratedDeriv_succ, iteratedDeriv_one]
      congr 1
      funext u
      exact lineDeriv_eq_sum_partialDeriv_mul G (hG.differentiable (by norm_num)) x δ u
    _ =
        ∑ i : Fin d, deriv (fun u : ℝ ↦ (∂[i] G) (x + u • δ) * δ i) s := by
      -- Proof comment: differentiate the finite sum termwise.
      rw [deriv_fun_sum]
      intro i hi
      exact (hDiffLine i).mul_const (δ i)
    _ =
        ∑ i : Fin d, (∑ j : Fin d, (∂²[i, j] G) (x + s • δ) * δ j) * δ i := by
      -- Proof comment: each summand differentiates by the already-normalized first-order formula.
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [deriv_mul_const (hDiffLine i), hLinePartial i]
    _ = ∑ i : Fin d, ∑ j : Fin d, (∂²[i, j] G) (x + s • δ) * δ i * δ j := by
      -- Proof comment: reassociate the scalar factors into the stated Hessian pairing.
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      intro j hj
      ring

/-- Helper for `Corollary 25.35`: a uniformly bounded coefficient matrix contributes at most `d`
times the diagonal square mass when paired with one increment vector. -/
private theorem abs_sum_mul_mul_le_card_mul_sum_sq
    {ε : ℝ} (hε : 0 ≤ ε)
    (A : Fin d → Fin d → ℝ) (δ : Fin d → ℝ)
    (hA : ∀ i j : Fin d, |A i j| ≤ ε) :
    |∑ i : Fin d, ∑ j : Fin d, A i j * δ i * δ j| ≤
      ε * (d : ℝ) * ∑ i : Fin d, (δ i)^2 := by
  have habs :
      |∑ i : Fin d, ∑ j : Fin d, A i j * δ i * δ j| ≤
        ∑ i : Fin d, ∑ j : Fin d, |A i j * δ i * δ j| := by
    calc
      |∑ i : Fin d, ∑ j : Fin d, A i j * δ i * δ j|
          ≤ ∑ i : Fin d, |∑ j : Fin d, A i j * δ i * δ j| := by
            simpa using
              (Finset.abs_sum_le_sum_abs
                (fun i : Fin d ↦ ∑ j : Fin d, A i j * δ i * δ j)
                (Finset.univ : Finset (Fin d)))
      _ ≤ ∑ i : Fin d, ∑ j : Fin d, |A i j * δ i * δ j| := by
            refine Finset.sum_le_sum ?_
            intro i hi
            simpa using
              (Finset.abs_sum_le_sum_abs
                (fun j : Fin d ↦ A i j * δ i * δ j)
                (Finset.univ : Finset (Fin d)))
  have hcoeff :
      ∑ i : Fin d, ∑ j : Fin d, |A i j * δ i * δ j| ≤
        ∑ i : Fin d, ∑ j : Fin d, ε * |δ i| * |δ j| := by
    refine Finset.sum_le_sum ?_
    intro i hi
    refine Finset.sum_le_sum ?_
    intro j hj
    have hδ_nonneg : 0 ≤ |δ i| * |δ j| := by positivity
    have hmul :
        |A i j| * (|δ i| * |δ j|) ≤ ε * (|δ i| * |δ j|) :=
      mul_le_mul_of_nonneg_right (hA i j) hδ_nonneg
    simpa [abs_mul, mul_assoc, mul_left_comm, mul_comm] using hmul
  have hsum_sq :
      (∑ i : Fin d, |δ i|) ^ 2 ≤ (d : ℝ) * ∑ i : Fin d, (δ i)^2 := by
    simpa [sq_abs] using
      (sq_sum_le_card_mul_sum_sq
        (s := (Finset.univ : Finset (Fin d)))
        (f := fun i : Fin d ↦ |δ i|))
  have hεsum_sq :
      ε * (∑ i : Fin d, |δ i|) ^ 2 ≤ ε * ((d : ℝ) * ∑ i : Fin d, (δ i)^2) :=
    mul_le_mul_of_nonneg_left hsum_sq hε
  calc
    |∑ i : Fin d, ∑ j : Fin d, A i j * δ i * δ j|
        ≤ ∑ i : Fin d, ∑ j : Fin d, |A i j * δ i * δ j| := habs
    _ ≤ ∑ i : Fin d, ∑ j : Fin d, ε * |δ i| * |δ j| := hcoeff
    _ = ε * (∑ i : Fin d, |δ i|) ^ 2 := by
      calc
        ∑ i : Fin d, ∑ j : Fin d, ε * |δ i| * |δ j|
            = ∑ i : Fin d, (ε * |δ i|) * ∑ j : Fin d, |δ j| := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                rw [Finset.mul_sum]
        _ = (∑ i : Fin d, ε * |δ i|) * ∑ j : Fin d, |δ j| := by
              rw [← Finset.sum_mul]
        _ = ε * (∑ i : Fin d, |δ i|) * ∑ j : Fin d, |δ j| := by
              rw [← Finset.mul_sum]
        _ = ε * (∑ i : Fin d, |δ i|) ^ 2 := by
              ring
    _ ≤ ε * ((d : ℝ) * ∑ i : Fin d, (δ i)^2) := hεsum_sq
    _ = ε * (d : ℝ) * ∑ i : Fin d, (δ i)^2 := by ring

/-- Helper for `Corollary 25.35`: once the dyadic mesh is fine enough, every frozen-time Hessian
entry oscillates by at most `2ε` on each Brownian dyadic cell. -/
private theorem eventually_frozenTimeSecondPartialOscillation_onDyadicCells
    (F : EuclideanSpace ℝ (Fin d) × ℝ → ℝ)
    (hF : IsTimeSpaceC21 F)
    {W : NNReal → Ω → EuclideanSpace ℝ (Fin d)}
    (hW : IsStandardBrownianMotionVector μ W)
    (T : NNReal) (ω : Ω) {ε : ℝ} (hε : 0 < ε) :
    let Wc := standardBrownianMotionVectorContinuousVersion hW
    ∀ᶠ n in atTop,
      ∀ i j : Fin d,
        ∀ k ∈ Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n T),
          ∀ u ∈ Set.uIcc (0 : ℝ) 1,
            ∀ v ∈ Set.uIcc (0 : ℝ) 1,
              |(∂²[i, j] fun x : EuclideanSpace ℝ (Fin d) ↦
                    F (x, (Definition2158.dyadicPartitionSequence n k : ℝ)))
                  (Wc (Definition2158.dyadicPartitionSequence n k) ω +
                    u •
                      (Wc (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) ω -
                        Wc (Definition2158.dyadicPartitionSequence n k) ω)) -
                (∂²[i, j] fun x : EuclideanSpace ℝ (Fin d) ↦
                    F (x, (Definition2158.dyadicPartitionSequence n k : ℝ)))
                  (Wc (Definition2158.dyadicPartitionSequence n k) ω +
                    v •
                      (Wc (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) ω -
                        Wc (Definition2158.dyadicPartitionSequence n k) ω))| ≤
                2 * ε := by
  let Wc := standardBrownianMotionVectorContinuousVersion hW
  have hWcCont : Continuous fun t : NNReal ↦ Wc t ω := by
    refine continuous_pi fun i ↦ ?_
    simpa [Wc, standardBrownianMotionVectorContinuousVersion] using
      brownianContinuousVersion_continuous (μ := μ) (B := fun t ω ↦ W t ω i)
        (hW.isBrownianMotion i) ω
  have hpair :
      ∀ i j : Fin d,
        ∀ᶠ n in atTop,
          ∀ k ∈ Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n T),
            ∀ u ∈ Set.uIcc (0 : ℝ) 1,
              ∀ v ∈ Set.uIcc (0 : ℝ) 1,
                |(∂²[i, j] fun x : EuclideanSpace ℝ (Fin d) ↦
                      F (x, (Definition2158.dyadicPartitionSequence n k : ℝ)))
                    (Wc (Definition2158.dyadicPartitionSequence n k) ω +
                      u •
                        (Wc
                            (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T)
                            ω -
                          Wc (Definition2158.dyadicPartitionSequence n k) ω)) -
                  (∂²[i, j] fun x : EuclideanSpace ℝ (Fin d) ↦
                      F (x, (Definition2158.dyadicPartitionSequence n k : ℝ)))
                    (Wc (Definition2158.dyadicPartitionSequence n k) ω +
                      v •
                        (Wc
                            (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T)
                            ω -
                          Wc (Definition2158.dyadicPartitionSequence n k) ω))| ≤
                  2 * ε := by
    intro i j
    obtain ⟨C, hC⟩ :
        ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : NNReal) T, ‖Wc t ω‖ ≤ C :=
      (isCompact_Icc : IsCompact (Set.Icc (0 : NNReal) T)).exists_bound_of_continuousOn
        hWcCont.continuousOn
    have hSecondUC :
        UniformContinuousOn
          (fun xt : EuclideanSpace ℝ (Fin d) × ℝ ↦
            (∂²[i, j] fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, xt.2)) xt.1)
          (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) C ×ˢ Set.Icc (0 : ℝ) (T : ℝ)) := by
      -- Proof comment: the frozen-time Hessian field is uniformly continuous on the compact tube
      -- containing every Brownian dyadic cell segment.
      exact
        ((ProperSpace.isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) C).prod
          (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) (T : ℝ))))
          .uniformContinuousOn_of_continuous
            ((hF.continuous_spaceSecondPartialDeriv i j).continuousOn)
    have hWcUC :
        UniformContinuousOn Wc (Set.Icc (0 : NNReal) T) := by
      -- Proof comment: the Brownian path is uniformly continuous on the compact interval `[0,T]`.
      exact isCompact_Icc.uniformContinuousOn_of_continuous hWcCont.continuousOn
    rcases (Metric.uniformContinuousOn_iff_le.mp hSecondUC) (2 * ε) (by linarith) with
      ⟨δ, hδ_pos, hδ_spec⟩
    rcases (Metric.uniformContinuousOn_iff_le.mp hWcUC) δ hδ_pos with ⟨η, hη_pos, hη_spec⟩
    have hmesh :
        ∀ᶠ n in atTop,
          partitionMesh Definition2158.dyadicPartitionSequence n ≤ ENNReal.ofReal η := by
      -- Proof comment: the dyadic mesh eventually falls below the time modulus coming from the
      -- Brownian path continuity.
      exact
        (ENNReal.tendsto_atTop_zero.mp
          Definition2158.tendsto_partitionMesh_dyadicPartitionSequence)
          (ENNReal.ofReal η)
          (ENNReal.ofReal_pos.mpr hη_pos)
    filter_upwards [hmesh] with n hn k hk u hu v hv
    have hk_lt : k < partitionBoundIndex Definition2158.dyadicPartitionSequence n T :=
      Finset.mem_range.mp hk
    let t0 := Definition2158.dyadicPartitionSequence n k
    let t1 := partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T
    let x : EuclideanSpace ℝ (Fin d) := Wc t0 ω
    let y : EuclideanSpace ℝ (Fin d) := Wc t1 ω
    have ht0_mem : t0 ∈ Set.Icc (0 : NNReal) T :=
      partitionPoint_mem_Icc_of_lt_partitionBoundIndex
        Definition2158.dyadicPartitionSequence n k T hk_lt
    have ht1_mem : t1 ∈ Set.Icc (0 : NNReal) T :=
      partitionNextPointUpTo_mem_Icc_of_lt_partitionBoundIndex
        Definition2158.dyadicPartitionSequence n k T hk_lt
    have ht0_real_mem : (t0 : ℝ) ∈ Set.Icc (0 : ℝ) (T : ℝ) := ht0_mem
    have htime :
        dist x y ≤ δ := by
      have hedist :
          edist t0 t1 ≤ ENNReal.ofReal η := by
        exact
          (edist_partitionPoint_partitionNextPointUpTo_le_truncationMesh
            Definition2158.dyadicPartitionSequence n k T hk_lt).trans hn
      exact hη_spec _ ht0_mem _ ht1_mem (edist_le_ofReal (le_of_lt hη_pos)).1 hedist
    have hsegment_mem :
        ∀ w ∈ Set.Icc (0 : ℝ) 1,
          (x + w • (y - x), (t0 : ℝ)) ∈
            Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) C ×ˢ Set.Icc (0 : ℝ) (T : ℝ) := by
      intro w hw
      have hw0 : 0 ≤ w := hw.1
      have hw1 : w ≤ 1 := hw.2
      have hrewrite : x + w • (y - x) = (1 - w) • x + w • y := by
        ext m
        simp [x, y]
        ring
      have hnorm :
          ‖x + w • (y - x)‖ ≤ C := by
        calc
          ‖x + w • (y - x)‖ = ‖(1 - w) • x + w • y‖ := by
            rw [hrewrite]
          _ ≤ ‖(1 - w) • x‖ + ‖w • y‖ := norm_add_le _ _
          _ = |1 - w| * ‖x‖ + |w| * ‖y‖ := by
            rw [norm_smul, norm_smul]
            simp only [Real.norm_eq_abs]
          _ ≤ (1 - w) * C + w * C := by
            have hw1' : 0 ≤ 1 - w := sub_nonneg.mpr hw1
            rw [abs_of_nonneg hw1', abs_of_nonneg hw0]
            gcongr
            · exact hC _ ht0_mem
            · exact hC _ ht1_mem
          _ = C := by ring
      exact ⟨by simpa [Metric.mem_closedBall, dist_eq_norm] using hnorm, ht0_real_mem⟩
    have huv : |u - v| ≤ 1 := by
      refine abs_le.mpr ?_
      constructor
      · linarith [hu.1, hv.2]
      · linarith [hu.2, hv.1]
    have hdistState :
        dist (x + u • (y - x)) (x + v • (y - x)) ≤ δ := by
      calc
        dist (x + u • (y - x)) (x + v • (y - x))
            = ‖(u - v) • (y - x)‖ := by
                rw [dist_eq_norm]
                congr 1
                ext m
                simp [x, y]
                ring
        _ = |u - v| * ‖y - x‖ := by
              rw [norm_smul]
              simp only [Real.norm_eq_abs]
        _ ≤ 1 * ‖y - x‖ := by
              gcongr
        _ = dist x y := by
              rw [dist_eq_norm, norm_sub_rev]
              simp
        _ ≤ δ := htime
    have hProdDist :
        dist (x + u • (y - x), (t0 : ℝ)) (x + v • (y - x), (t0 : ℝ)) ≤ δ := by
      simpa [Prod.dist_eq, dist_self, max_eq_left (dist_nonneg : 0 ≤ dist (x + u • (y - x)) (x + v • (y - x)))] using
        hdistState
    -- Proof comment: both frozen-time segment points stay in the compact tube, and their
    -- distance is controlled by the Brownian increment size on the dyadic cell.
    simpa [t0, t1, x, y] using
      hδ_spec
        (x + u • (y - x), (t0 : ℝ))
        (hsegment_mem u <| by simpa [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hu)
        (x + v • (y - x), (t0 : ℝ))
        (hsegment_mem v <| by simpa [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hv)
        hProdDist
  choose N hN using fun ij : Fin d × Fin d ↦ Filter.eventually_atTop.1 (hpair ij.1 ij.2)
  let Nmax : ℕ := Finset.univ.sup N
  -- Proof comment: finitely many coordinate pairs are involved, so one common row index works
  -- for all Hessian entries at once.
  refine Filter.eventually_atTop.2 ⟨Nmax, ?_⟩
  intro n hn i j
  exact hN (i, j) n (le_trans (Finset.le_sup (Finset.mem_univ (i, j))) hn)

/-- Helper for `Corollary 25.35`: one frozen-time Brownian dyadic cell is controlled by the
scalar left-point Taylor estimate on the affine line through that cell. -/
private theorem abs_frozenTimeSpatialCellError_le
    (F : EuclideanSpace ℝ (Fin d) × ℝ → ℝ)
    (hF : IsTimeSpaceC21 F)
    {W : NNReal → Ω → EuclideanSpace ℝ (Fin d)}
    (hW : IsStandardBrownianMotionVector μ W)
    (T : NNReal) (ω : Ω) (n k : ℕ) {ε : ℝ}
    (hε : 0 ≤ ε)
    (_hk : k ∈ Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n T))
    (hosc :
      ∀ i j : Fin d,
        ∀ u ∈ Set.uIcc (0 : ℝ) 1,
          ∀ v ∈ Set.uIcc (0 : ℝ) 1,
            |(∂²[i, j] fun x : EuclideanSpace ℝ (Fin d) ↦
                  F (x, (Definition2158.dyadicPartitionSequence n k : ℝ)))
                ((standardBrownianMotionVectorContinuousVersion hW
                      (Definition2158.dyadicPartitionSequence n k) ω) +
                  u •
                    ((standardBrownianMotionVectorContinuousVersion hW
                          (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) ω) -
                      (standardBrownianMotionVectorContinuousVersion hW
                        (Definition2158.dyadicPartitionSequence n k) ω))) -
              (∂²[i, j] fun x : EuclideanSpace ℝ (Fin d) ↦
                  F (x, (Definition2158.dyadicPartitionSequence n k : ℝ)))
                ((standardBrownianMotionVectorContinuousVersion hW
                      (Definition2158.dyadicPartitionSequence n k) ω) +
                  v •
                    ((standardBrownianMotionVectorContinuousVersion hW
                          (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) ω) -
                      (standardBrownianMotionVectorContinuousVersion hW
                        (Definition2158.dyadicPartitionSequence n k) ω)))| ≤
              2 * ε) :
    let Wc := standardBrownianMotionVectorContinuousVersion hW
    let t0 := Definition2158.dyadicPartitionSequence n k
    let t1 := partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T
    let x0 := Wc t0 ω
    let x1 := Wc t1 ω
    |F (x1, (t0 : ℝ)) - F (x0, (t0 : ℝ)) -
        (∑ i : Fin d,
          (∂[i] fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, (t0 : ℝ))) x0 * (x1 i - x0 i)) -
        ((1 : ℝ) / 2) *
          ∑ i : Fin d, ∑ j : Fin d,
            (∂²[i, j] fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, (t0 : ℝ))) x0 *
              (x1 i - x0 i) * (x1 j - x0 j)| ≤
      (2 * ε) * (d : ℝ) * ∑ i : Fin d, (x1 i - x0 i)^2 := by
  let Wc := standardBrownianMotionVectorContinuousVersion hW
  let t0 := Definition2158.dyadicPartitionSequence n k
  let t1 := partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T
  let x0 := Wc t0 ω
  let x1 := Wc t1 ω
  let δ : EuclideanSpace ℝ (Fin d) := x1 - x0
  let G : EuclideanSpace ℝ (Fin d) → ℝ := fun x ↦ F (x, (t0 : ℝ))
  let g : ℝ → ℝ := fun u ↦ G (x0 + u • δ)
  let η : ℝ := (2 * ε) * (d : ℝ) * ∑ i : Fin d, (δ i)^2
  have hG : ContDiff ℝ 2 G := contDiffFrozenSlice_of_isTimeSpaceC21 F hF (t0 : ℝ)
  have hg : ContDiff ℝ 2 g := by
    -- Proof comment: restricting the frozen slice to an affine line preserves `C²` regularity.
    fun_prop
  have hη_nonneg : 0 ≤ η := by
    positivity
  have hlineOsc :
      ∀ u ∈ Set.uIcc (0 : ℝ) 1,
        ∀ v ∈ Set.uIcc (0 : ℝ) 1,
          |iteratedDeriv 2 g u - iteratedDeriv 2 g v| ≤ η := by
    intro u hu v hv
    let A : Fin d → Fin d → ℝ := fun i j ↦
      (∂²[i, j] G) (x0 + u • δ) - (∂²[i, j] G) (x0 + v • δ)
    have hA : ∀ i j : Fin d, |A i j| ≤ 2 * ε := by
      intro i j
      simpa [A, G, x0, δ, Wc, t0, t1] using hosc i j u hu v hv
    calc
      |iteratedDeriv 2 g u - iteratedDeriv 2 g v|
          = |∑ i : Fin d, ∑ j : Fin d, A i j * δ i * δ j| := by
              rw [lineSecondDeriv_eq_sum_secondPartialDeriv_mul_mul G hG x0 δ u,
                lineSecondDeriv_eq_sum_secondPartialDeriv_mul_mul G hG x0 δ v]
              congr 1
              rw [← Finset.sum_sub_distrib]
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [← Finset.sum_sub_distrib]
              refine Finset.sum_congr rfl ?_
              intro j hj
              simp [A]
              ring
      _ ≤ (2 * ε) * (d : ℝ) * ∑ i : Fin d, (δ i)^2 := by
            exact
              abs_sum_mul_mul_le_card_mul_sum_sq
                (d := d) (ε := 2 * ε) (show 0 ≤ 2 * ε by nlinarith) A δ hA
      _ = η := by rfl
  have hTaylor :
      |g 1 - g 0 - deriv g 0 * (1 - 0) -
          ((1 : ℝ) / 2) * iteratedDeriv 2 g 0 * (1 - 0) ^ 2| ≤
        η * (1 - 0) ^ 2 := by
    exact
      leftpointTaylorIncrementError_le g hg (a := 0) (b := 1) (ε := η) (by norm_num)
        hη_nonneg hlineOsc
  have hderiv0 :
      deriv g 0 = ∑ i : Fin d, (∂[i] G) x0 * δ i := by
    simpa [g] using
      lineDeriv_eq_sum_partialDeriv_mul G (hG.differentiable (by norm_num)) x0 δ 0
  have hsecond0 :
      iteratedDeriv 2 g 0 = ∑ i : Fin d, ∑ j : Fin d, (∂²[i, j] G) x0 * δ i * δ j := by
    simpa [g] using lineSecondDeriv_eq_sum_secondPartialDeriv_mul_mul G hG x0 δ 0
  have hzero : x0 + (0 : ℝ) • δ = x0 := by simp
  have hone : x0 + (1 : ℝ) • δ = x1 := by
    ext i
    simp [δ, x0, x1]
  -- Proof comment: rewrite the scalar line estimate back into the endpoint, gradient, and
  -- Hessian data of the current frozen-time Brownian cell.
  rw [hderiv0, hsecond0] at hTaylor
  simpa [G, g, x0, x1, δ, η, Wc, t0, t1, hzero, hone] using hTaylor

/-- Helper for `Corollary 25.35`: if every frozen-time Hessian entry has small oscillation on the
contributing Brownian dyadic cells, then the full spatial residual is controlled by the weighted
coordinate square masses. -/
private theorem abs_timeSpaceC21SpatialResidual_le_weightedSquares
    (F : EuclideanSpace ℝ (Fin d) × ℝ → ℝ)
    (hF : IsTimeSpaceC21 F)
    {W : NNReal → Ω → EuclideanSpace ℝ (Fin d)}
    (hW : IsStandardBrownianMotionVector μ W)
    (T : NNReal) (ω : Ω) (n : ℕ) {ε : ℝ}
    (hε : 0 ≤ ε)
    (hosc :
      ∀ i j : Fin d,
        ∀ k ∈ Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n T),
          ∀ u ∈ Set.uIcc (0 : ℝ) 1,
            ∀ v ∈ Set.uIcc (0 : ℝ) 1,
              |(∂²[i, j] fun x : EuclideanSpace ℝ (Fin d) ↦
                    F (x, (Definition2158.dyadicPartitionSequence n k : ℝ)))
                  ((standardBrownianMotionVectorContinuousVersion hW
                        (Definition2158.dyadicPartitionSequence n k) ω) +
                    u •
                      ((standardBrownianMotionVectorContinuousVersion hW
                            (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T)
                            ω) -
                        (standardBrownianMotionVectorContinuousVersion hW
                          (Definition2158.dyadicPartitionSequence n k) ω))) -
                (∂²[i, j] fun x : EuclideanSpace ℝ (Fin d) ↦
                    F (x, (Definition2158.dyadicPartitionSequence n k : ℝ)))
                  ((standardBrownianMotionVectorContinuousVersion hW
                        (Definition2158.dyadicPartitionSequence n k) ω) +
                    v •
                      ((standardBrownianMotionVectorContinuousVersion hW
                            (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T)
                            ω) -
                        (standardBrownianMotionVectorContinuousVersion hW
                          (Definition2158.dyadicPartitionSequence n k) ω)))| ≤
                2 * ε) :
    let Wc := standardBrownianMotionVectorContinuousVersion hW
    |timeSpaceC21SpatialResidual (μ := μ) F hW T ω n| ≤
      (2 * ε) * (d : ℝ) *
        ∑ i : Fin d,
          pathwiseWeightedPartitionQuadraticVariationApproximationUpTo
            (fun _ ↦ (1 : ℝ))
            (⟨fun s ↦ (Wc s ω).ofLp i,
              brownianContinuousCoordinate_continuous_local (μ := μ) hW i ω⟩ : C(NNReal, ℝ))
            Definition2158.dyadicPartitionSequence
            T
            n := by
  let Wc := standardBrownianMotionVectorContinuousVersion hW
  let N := partitionBoundIndex Definition2158.dyadicPartitionSequence n T
  let inc : ℕ → Fin d → ℝ := fun k i ↦
    Wc (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) ω i -
      Wc (Definition2158.dyadicPartitionSequence n k) ω i
  calc
    |timeSpaceC21SpatialResidual (μ := μ) F hW T ω n|
        = |Finset.sum (Finset.range N) (fun k ↦
            F (Wc (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) ω,
                (Definition2158.dyadicPartitionSequence n k : ℝ)) -
              F (Wc (Definition2158.dyadicPartitionSequence n k) ω,
                (Definition2158.dyadicPartitionSequence n k : ℝ)) -
              (∑ i : Fin d,
                (∂[i] fun x : EuclideanSpace ℝ (Fin d) ↦
                    F (x, (Definition2158.dyadicPartitionSequence n k : ℝ)))
                  (Wc (Definition2158.dyadicPartitionSequence n k) ω) *
                  inc k i) -
              ((1 : ℝ) / 2) *
                ∑ i : Fin d, ∑ j : Fin d,
                  (∂²[i, j] fun x : EuclideanSpace ℝ (Fin d) ↦
                      F (x, (Definition2158.dyadicPartitionSequence n k : ℝ)))
                    (Wc (Definition2158.dyadicPartitionSequence n k) ω) *
                    inc k i * inc k j)| := by
            simp [timeSpaceC21SpatialResidual, Wc, N, inc]
    _ ≤ Finset.sum (Finset.range N) (fun k ↦
          |F (Wc (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) ω,
                (Definition2158.dyadicPartitionSequence n k : ℝ)) -
              F (Wc (Definition2158.dyadicPartitionSequence n k) ω,
                (Definition2158.dyadicPartitionSequence n k : ℝ)) -
              (∑ i : Fin d,
                (∂[i] fun x : EuclideanSpace ℝ (Fin d) ↦
                    F (x, (Definition2158.dyadicPartitionSequence n k : ℝ)))
                  (Wc (Definition2158.dyadicPartitionSequence n k) ω) *
                  inc k i) -
              ((1 : ℝ) / 2) *
                ∑ i : Fin d, ∑ j : Fin d,
                  (∂²[i, j] fun x : EuclideanSpace ℝ (Fin d) ↦
                      F (x, (Definition2158.dyadicPartitionSequence n k : ℝ)))
                    (Wc (Definition2158.dyadicPartitionSequence n k) ω) *
                    inc k i * inc k j|) := by
            simpa using
              (Finset.abs_sum_le_sum_abs
                (fun k : ℕ ↦
                  F (Wc (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) ω,
                        (Definition2158.dyadicPartitionSequence n k : ℝ)) -
                    F (Wc (Definition2158.dyadicPartitionSequence n k) ω,
                      (Definition2158.dyadicPartitionSequence n k : ℝ)) -
                    (∑ i : Fin d,
                      (∂[i] fun x : EuclideanSpace ℝ (Fin d) ↦
                          F (x, (Definition2158.dyadicPartitionSequence n k : ℝ)))
                        (Wc (Definition2158.dyadicPartitionSequence n k) ω) *
                        inc k i) -
                    ((1 : ℝ) / 2) *
                      ∑ i : Fin d, ∑ j : Fin d,
                        (∂²[i, j] fun x : EuclideanSpace ℝ (Fin d) ↦
                            F (x, (Definition2158.dyadicPartitionSequence n k : ℝ)))
                          (Wc (Definition2158.dyadicPartitionSequence n k) ω) *
                          inc k i * inc k j)
                (Finset.range N))
    _ ≤ Finset.sum (Finset.range N) (fun k ↦
          (2 * ε) * (d : ℝ) * ∑ i : Fin d, (inc k i)^2) := by
            refine Finset.sum_le_sum ?_
            intro k hk
            simpa [inc, Wc] using
              abs_frozenTimeSpatialCellError_le (μ := μ) F hF hW T ω n k hε hk
                (fun i j u hu v hv ↦ hosc i j k (by simpa [N] using hk) u hu v hv)
    _ = (2 * ε) * (d : ℝ) *
          ∑ i : Fin d,
            pathwiseWeightedPartitionQuadraticVariationApproximationUpTo
              (fun _ ↦ (1 : ℝ))
              (⟨fun s ↦ (Wc s ω).ofLp i,
                brownianContinuousCoordinate_continuous_local (μ := μ) hW i ω⟩ :
                C(NNReal, ℝ))
              Definition2158.dyadicPartitionSequence
              T
              n := by
            rw [← Finset.mul_sum, Finset.sum_comm]
            congr 1
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [pathwiseWeightedPartitionQuadraticVariationApproximationUpTo_def,
              weightedDyadicSquareVariationSum]
            refine Finset.sum_congr rfl ?_
            intro k hk
            simp [inc]

/-- Helper for `Corollary 25.35`: the frozen-time spatial Taylor residual vanishes along the full
dyadic sequence for almost every Brownian sample. -/
private theorem tendsto_timeSpaceC21SpatialResidual_zero
    (F : EuclideanSpace ℝ (Fin d) × ℝ → ℝ)
    (hF : IsTimeSpaceC21 F)
    {W : NNReal → Ω → EuclideanSpace ℝ (Fin d)}
    (hW : IsStandardBrownianMotionVector μ W)
    (T : NNReal) :
    ∀ᵐ ω ∂μ,
      Tendsto
        (fun n ↦ timeSpaceC21SpatialResidual (μ := μ) F hW T ω n)
        atTop
        (𝓝 0) := by
  let Wc := standardBrownianMotionVectorContinuousVersion hW
  let Xω : Ω → VectorPathSpace (d + 1) := fun ω ↦ timeSpaceGraphPath (μ := μ) hW ω
  have hComponentSplit :
      ∀ ω : Ω,
        (∀ i : Fin d,
          vectorPathComponent (Xω ω) (Fin.castSucc i) =
            (⟨fun s ↦ (Wc s ω).ofLp i,
              brownianContinuousCoordinate_continuous_local (μ := μ) hW i ω⟩ :
              C(NNReal, ℝ))) ∧
          vectorPathComponent (Xω ω) (Fin.last d) =
            (⟨fun s ↦ (s : ℝ), continuous_subtype_val⟩ : C(NNReal, ℝ)) := by
    intro ω
    simpa [Xω, timeSpaceGraphPath, Wc] using vectorPathComponent_timeSpaceGraph_eq (μ := μ) hW ω
  have hGraphCov :
      ∀ᵐ ω ∂μ,
        (∀ i j : Fin d,
          HasQuadraticCovariationAlong
            (vectorPathComponent (Xω ω) (Fin.castSucc i))
            (vectorPathComponent (Xω ω) (Fin.castSucc j))
            (fun S ↦ if i = j then (S : ℝ) else 0)) ∧
        (∀ i : Fin d,
          HasQuadraticCovariationAlong
            (vectorPathComponent (Xω ω) (Fin.castSucc i))
            (vectorPathComponent (Xω ω) (Fin.last d))
            0) ∧
        (∀ i : Fin d,
          HasQuadraticCovariationAlong
            (vectorPathComponent (Xω ω) (Fin.last d))
            (vectorPathComponent (Xω ω) (Fin.castSucc i))
            0) ∧
        HasQuadraticCovariationAlong
          (vectorPathComponent (Xω ω) (Fin.last d))
          (vectorPathComponent (Xω ω) (Fin.last d))
          0 := by
    simpa [Xω, timeSpaceGraphPath] using timeSpaceGraphCoordinateCovariationFamily_ae (μ := μ) hW
  filter_upwards [hGraphCov] with ω hω
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  let M : ℝ := ∑ i : Fin d, (|(T : ℝ)| + 1)
  let B : ℝ := (d : ℝ) * M + 1
  let η : ℝ := ε / (2 * B)
  have hB_pos : 0 < B := by
    dsimp [B, M]
    positivity
  have hη_pos : 0 < η := by
    dsimp [η]
    exact div_pos hε (by positivity)
  have hη_nonneg : 0 ≤ η := hη_pos.le
  have hOsc :
      ∀ᶠ n in atTop,
        ∀ i j : Fin d,
          ∀ k ∈ Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n T),
            ∀ u ∈ Set.uIcc (0 : ℝ) 1,
              ∀ v ∈ Set.uIcc (0 : ℝ) 1,
                |(∂²[i, j] fun x : EuclideanSpace ℝ (Fin d) ↦
                      F (x, (Definition2158.dyadicPartitionSequence n k : ℝ)))
                    (Wc (Definition2158.dyadicPartitionSequence n k) ω +
                      u •
                        (Wc (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) ω -
                          Wc (Definition2158.dyadicPartitionSequence n k) ω)) -
                  (∂²[i, j] fun x : EuclideanSpace ℝ (Fin d) ↦
                      F (x, (Definition2158.dyadicPartitionSequence n k : ℝ)))
                    (Wc (Definition2158.dyadicPartitionSequence n k) ω +
                      v •
                        (Wc (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) ω -
                          Wc (Definition2158.dyadicPartitionSequence n k) ω))| ≤
                  2 * η :=
    eventually_frozenTimeSecondPartialOscillation_onDyadicCells (μ := μ) F hF hW T ω hη_pos
  have hsplitω := hComponentSplit ω
  have hmass_i :
      ∀ i : Fin d,
        ∀ᶠ n in atTop,
          pathwiseWeightedPartitionQuadraticVariationApproximationUpTo
              (fun _ ↦ (1 : ℝ))
              (⟨fun s ↦ (Wc s ω).ofLp i,
                brownianContinuousCoordinate_continuous_local (μ := μ) hW i ω⟩ :
                C(NNReal, ℝ))
              Definition2158.dyadicPartitionSequence
              T
              n ≤
            |(T : ℝ)| + 1 := by
    intro i
    have hsq :
        HasSquareVariationAlong
          (vectorPathComponent (Xω ω) (Fin.castSucc i))
          (fun S ↦ (S : ℝ)) := by
      simpa using
        hasSquareVariationAlong_of_hasQuadraticCovariationAlong_self (hω.1 i i)
    simpa [pathwiseWeightedPartitionQuadraticVariationApproximationUpTo_def,
      weightedDyadicSquareVariationSum, hsplitω.1 i] using
      eventually_le_weightedDyadicSquareVariationSum_one_abs_add_one hsq T
  have hmassAll :
      ∀ᶠ n in atTop,
        ∀ i : Fin d,
          pathwiseWeightedPartitionQuadraticVariationApproximationUpTo
              (fun _ ↦ (1 : ℝ))
              (⟨fun s ↦ (Wc s ω).ofLp i,
                brownianContinuousCoordinate_continuous_local (μ := μ) hW i ω⟩ :
                C(NNReal, ℝ))
              Definition2158.dyadicPartitionSequence
              T
              n ≤
            |(T : ℝ)| + 1 := by
    choose N hN using fun i : Fin d ↦ Filter.eventually_atTop.1 (hmass_i i)
    let Nmax : ℕ := Finset.univ.sup N
    refine Filter.eventually_atTop.2 ⟨Nmax, ?_⟩
    intro n hn i
    exact hN i n (le_trans (Finset.le_sup (Finset.mem_univ i)) hn)
  have hmass :
      ∀ᶠ n in atTop,
        ∑ i : Fin d,
          pathwiseWeightedPartitionQuadraticVariationApproximationUpTo
            (fun _ ↦ (1 : ℝ))
            (⟨fun s ↦ (Wc s ω).ofLp i,
              brownianContinuousCoordinate_continuous_local (μ := μ) hW i ω⟩ :
              C(NNReal, ℝ))
            Definition2158.dyadicPartitionSequence
            T
            n ≤
          M := by
    filter_upwards [hmassAll] with n hn
    dsimp [M]
    exact Finset.sum_le_sum fun i hi ↦ hn i
  have hdMB : (d : ℝ) * M < B := by
    dsimp [B]
    linarith
  have hstrict :
      (2 * η) * (d : ℝ) * M < ε := by
    have hratio : ((d : ℝ) * M) / B < 1 := by
      exact (div_lt_one hB_pos).2 hdMB
    have hmul : ε * (((d : ℝ) * M) / B) < ε := by
      simpa using mul_lt_mul_of_pos_left hratio hε
    simpa [η, B, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using hmul
  have hfactor_nonneg : 0 ≤ (2 * η) * (d : ℝ) := by positivity
  have hfinal :
      ∀ᶠ n in atTop,
        dist (timeSpaceC21SpatialResidual (μ := μ) F hW T ω n) 0 < ε := by
    filter_upwards [hOsc, hmass] with n hnOsc hnMass
    have hbound :=
      abs_timeSpaceC21SpatialResidual_le_weightedSquares (μ := μ) F hF hW T ω n hη_nonneg hnOsc
    have hscaled :
        (2 * η) * (d : ℝ) *
            ∑ i : Fin d,
              pathwiseWeightedPartitionQuadraticVariationApproximationUpTo
                (fun _ ↦ (1 : ℝ))
                (⟨fun s ↦ (Wc s ω).ofLp i,
                  brownianContinuousCoordinate_continuous_local (μ := μ) hW i ω⟩ :
                  C(NNReal, ℝ))
                Definition2158.dyadicPartitionSequence
                T
                n ≤
          (2 * η) * (d : ℝ) * M :=
      mul_le_mul_of_nonneg_left hnMass hfactor_nonneg
    have hlt :
        |timeSpaceC21SpatialResidual (μ := μ) F hW T ω n| < ε :=
      lt_of_le_of_lt hbound (lt_of_le_of_lt hscaled hstrict)
    simpa [Real.dist_eq] using hlt
  simpa using hfinal

/-- Helper for `Corollary 25.35`: the theorem-local dyadic remainder tends to `0` along the full
dyadic sequence. -/
private theorem tendsto_timeSpaceC21Remainder_zero
    (F : EuclideanSpace ℝ (Fin d) × ℝ → ℝ)
    (hF : IsTimeSpaceC21 F)
    {W : NNReal → Ω → EuclideanSpace ℝ (Fin d)}
    (hW : IsStandardBrownianMotionVector μ W)
    (T : NNReal) :
    ∀ᵐ ω ∂μ,
      Tendsto
        (fun n ↦ timeSpaceC21Remainder (μ := μ) F hW T ω n)
        atTop
        (𝓝 0) := by
  have hTimeResidual :
      ∀ᵐ ω ∂μ,
        Tendsto
          (fun n ↦ timeSpaceC21TimeResidual (μ := μ) F hW T ω n)
          atTop
          (𝓝 0) :=
    tendsto_timeSpaceC21TimeResidual_zero (μ := μ) F hF hW T
  have hSpatialResidual :
      ∀ᵐ ω ∂μ,
        Tendsto
          (fun n ↦ timeSpaceC21SpatialResidual (μ := μ) F hW T ω n)
          atTop
          (𝓝 0) :=
    tendsto_timeSpaceC21SpatialResidual_zero (μ := μ) F hF hW T
  filter_upwards [hTimeResidual, hSpatialResidual] with ω hTimeω hSpatialω
  have hSplit :
      ∀ n : ℕ,
        timeSpaceC21Remainder (μ := μ) F hW T ω n =
          timeSpaceC21TimeResidual (μ := μ) F hW T ω n +
            timeSpaceC21SpatialResidual (μ := μ) F hW T ω n := by
    intro n
    exact timeSpaceC21Remainder_eq_timeResidual_add_spatialResidual
      (μ := μ) F hF hW T ω n
  -- Proof comment: the exact algebraic split reduces the full remainder limit to the sum of the
  -- deterministic time residual limit and the frozen-time spatial Taylor residual limit.
  have hAdd := hTimeω.add hSpatialω
  convert hAdd using 1
  funext n
  exact hSplit n

private theorem continuousVersion_timeDependentIto_ae
    (F : EuclideanSpace ℝ (Fin d) × ℝ → ℝ)
    {W : NNReal → Ω → EuclideanSpace ℝ (Fin d)}
    (hF : IsTimeSpaceC21 F)
    (hW : IsStandardBrownianMotionVector μ W)
    (T : NNReal) :
    (fun ω ↦
      F (standardBrownianMotionVectorContinuousVersion hW T ω, (T : ℝ)) -
        F (standardBrownianMotionVectorContinuousVersion hW 0 ω, 0)) =ᵐ[μ]
      (fun ω ↦
        (∑ i : Fin d, standardBrownianMotionVectorCoordinateItoIntegral F hW i T ω) +
          ∫ s in Set.Icc (0 : ℝ) (T : ℝ),
            (∂ₜ F) (standardBrownianMotionVectorContinuousVersion hW s.toNNReal ω, s) +
              ((1 : ℝ) / 2) *
                Δ (fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, s))
                  (standardBrownianMotionVectorContinuousVersion hW s.toNNReal ω)) := by
  -- Route correction: the textbook one-line application of Theorem 25.33 is not directly
  -- executable against the current local API, so the remaining work is isolated to the canonical
  -- continuous Brownian version.
  let Wc := standardBrownianMotionVectorContinuousVersion hW
  let Xω : Ω → VectorPathSpace (d + 1) :=
    fun ω ↦ ⟨fun s ↦ timeSpaceGraphPoint (μ := μ) hW s ω,
      timeSpaceGraphPath_continuous (μ := μ) hW ω⟩
  have hComponentSplit :
      ∀ ω : Ω,
        (∀ i : Fin d,
          vectorPathComponent (Xω ω) (Fin.castSucc i) =
            (⟨fun s ↦ (Wc s ω).ofLp i,
              brownianContinuousCoordinate_continuous_local (μ := μ) hW i ω⟩ : C(NNReal, ℝ))) ∧
          vectorPathComponent (Xω ω) (Fin.last d) =
            (⟨fun s ↦ (s : ℝ), continuous_subtype_val⟩ : C(NNReal, ℝ)) := by
    intro ω
    simpa [Xω, Wc] using vectorPathComponent_timeSpaceGraph_eq (μ := μ) hW ω
  have hGraphCov :
      ∀ᵐ ω ∂μ,
        (∀ i j : Fin d,
          HasQuadraticCovariationAlong
            (vectorPathComponent (Xω ω) (Fin.castSucc i))
            (vectorPathComponent (Xω ω) (Fin.castSucc j))
            (fun T ↦ if i = j then (T : ℝ) else 0)) ∧
        (∀ i : Fin d,
          HasQuadraticCovariationAlong
            (vectorPathComponent (Xω ω) (Fin.castSucc i))
            (vectorPathComponent (Xω ω) (Fin.last d))
            0) ∧
        (∀ i : Fin d,
          HasQuadraticCovariationAlong
            (vectorPathComponent (Xω ω) (Fin.last d))
            (vectorPathComponent (Xω ω) (Fin.castSucc i))
            0) ∧
        HasQuadraticCovariationAlong
          (vectorPathComponent (Xω ω) (Fin.last d))
          (vectorPathComponent (Xω ω) (Fin.last d))
          0 := by
    simpa [Xω] using timeSpaceGraphCoordinateCovariationFamily_ae (μ := μ) hW
  have hGraphCovFull :
      ∀ᵐ ω ∂μ, ∀ i j : Fin (d + 1),
        HasQuadraticCovariationAlong
          (vectorPathComponent (Xω ω) i)
          (vectorPathComponent (Xω ω) j)
          (timeSpaceGraphCovariationPrimitive (d := d) i j) := by
    simpa [Xω] using timeSpaceGraphCoordinateCovariationFamilyFull_ae (μ := μ) hW
  have hXω :
      ∀ᵐ ω ∂μ, Xω ω ∈ (𝒞_qv^(d + 1)) := by
    simpa [Xω] using timeSpaceGraphPath_mem_cqv_ae (μ := μ) hW
  have hSpatialCorrection :
      ∀ᵐ ω ∂μ,
        ((1 : ℝ) / 2) *
            ∑ i : Fin d, ∑ j : Fin d,
              pathwiseQuadraticCovariationIntegral
                (fun s ↦
                  (∂²[Fin.castSucc i, Fin.castSucc j] (timeSpaceGraphLift F))
                    (timeSpaceGraphPoint (μ := μ) hW s ω))
                (vectorPathComponent (Xω ω) (Fin.castSucc i))
                (vectorPathComponent (Xω ω) (Fin.castSucc j))
                T
          =
            ((1 : ℝ) / 2) *
              ∑ i : Fin d,
                ∫ s in Set.Icc (0 : ℝ) (T : ℝ),
                  (∂²[i, i] fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, s))
                    (Wc s.toNNReal ω) := by
    filter_upwards [hGraphCovFull] with ω hω
    -- Proof comment: the new spatial-correction lemma consumes the packaged graph primitive once,
    -- so the remaining proof no longer needs to reopen the spatial bracket normalization.
    simpa [Xω, Wc, timeSpaceGraphPath] using
      timeSpaceGraphSpatialQuadraticCorrection_eq_sumSecondPartials
        (μ := μ) F hF hW T ω hω
  have hCommonCoordinateSubseq :
      ∃ φ : ℕ → ℕ,
        StrictMono φ ∧
          ∀ᵐ ω ∂μ, ∀ i : Fin d, ∀ T : NNReal,
            Tendsto
              (fun n ↦
                partitionPathwiseItoApproximationUpTo
                  (fun t ↦
                    (∂[i] fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, (t : ℝ)))
                      (Wc t ω))
                  (⟨fun t ↦ (Wc t ω).ofLp i,
                    brownianContinuousCoordinate_continuous_local (μ := μ) hW i ω⟩ :
                    C(NNReal, ℝ))
                  Definition2158.dyadicPartitionSequence
                  T
                  (φ n))
              atTop
              (𝓝 (standardBrownianMotionVectorCoordinateItoIntegral F hW i T ω)) := by
    -- Proof comment: the finite-dimensional diagonal argument is now packaged once and for all,
    -- so the remaining assembly can use one common spatial-row subsequence.
    exact exists_commonCoordinateItoSubsequence (μ := μ) F hF hW
  obtain ⟨φ, hφ, hφae⟩ := hCommonCoordinateSubseq
  have hFirstOrderLimit :
      ∀ᵐ ω ∂μ,
        Tendsto
          (fun n ↦
            dyadicMultidimensionalItoApproximationUpTo
              (timeSpaceGraphLift F)
              (Xω ω)
              T
              (φ n))
          atTop
          (𝓝
            ((∑ i : Fin d, standardBrownianMotionVectorCoordinateItoIntegral F hW i T ω) +
              ∫ s in Set.Icc (0 : ℝ) (T : ℝ), (∂ₜ F) (Wc s.toNNReal ω, s))) := by
    filter_upwards [hφae] with ω hω
    -- Proof comment: the new graph first-order normalization lets the common spatial subsequence
    -- and the deterministic time-row theorem combine directly into the first-order limit.
    simpa [Xω, Wc] using
      tendsto_timeSpaceGraphFirstOrder_alongSubseq
        (μ := μ) F hF hW hφ ω T (fun i ↦ hω i T)
  have hSpatialCorrectionLimit :
      ∀ᵐ ω ∂μ,
        Tendsto
          (fun n ↦
            timeSpaceC21SpatialCorrectionApproximationUpTo (μ := μ) F hW T ω n)
          atTop
          (𝓝
            (((1 : ℝ) / 2) *
              ∑ i : Fin d,
                ∫ s in Set.Icc (0 : ℝ) (T : ℝ),
                  (∂²[i, i] fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, s))
                    (Wc s.toNNReal ω))) := by
    filter_upwards [hGraphCovFull] with ω hω
    -- Proof comment: the dyadic spatial correction now has its own standalone convergence theorem,
    -- so the remaining frontier is only the endpoint decomposition and the vanishing remainder.
    simpa [Xω, Wc, timeSpaceGraphPath] using
      tendsto_timeSpaceGraphSpatialCorrection
        (μ := μ) F hF hW T ω hω
  have hRemainderLimit :
      ∀ᵐ ω ∂μ,
        Tendsto
          (fun n ↦ timeSpaceC21Remainder (μ := μ) F hW T ω n)
          atTop
          (𝓝 0) := by
    exact tendsto_timeSpaceC21Remainder_zero (μ := μ) F hF hW T
  filter_upwards [hFirstOrderLimit, hSpatialCorrectionLimit, hRemainderLimit] with
      ω hFirstω hSpatialω hRemainderω
  have hSpatialSubseq :
      Tendsto
        (fun n ↦ timeSpaceC21SpatialCorrectionApproximationUpTo (μ := μ) F hW T ω (φ n))
        atTop
        (𝓝
          (((1 : ℝ) / 2) *
            ∑ i : Fin d,
              ∫ s in Set.Icc (0 : ℝ) (T : ℝ),
                (∂²[i, i] fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, s))
                  (Wc s.toNNReal ω))) :=
    hSpatialω.comp hφ.tendsto_atTop
  have hRemainderSubseq :
      Tendsto
        (fun n ↦ timeSpaceC21Remainder (μ := μ) F hW T ω (φ n))
        atTop
        (𝓝 0) :=
    hRemainderω.comp hφ.tendsto_atTop
  have hApproxLimit :
      Tendsto
        (fun n ↦
          dyadicMultidimensionalItoApproximationUpTo
              (timeSpaceGraphLift F)
              (Xω ω)
              T
              (φ n) +
            timeSpaceC21SpatialCorrectionApproximationUpTo (μ := μ) F hW T ω (φ n) +
            timeSpaceC21Remainder (μ := μ) F hW T ω (φ n))
        atTop
        (𝓝
          (((∑ i : Fin d, standardBrownianMotionVectorCoordinateItoIntegral F hW i T ω) +
              ∫ s in Set.Icc (0 : ℝ) (T : ℝ), (∂ₜ F) (Wc s.toNNReal ω, s)) +
            (((1 : ℝ) / 2) *
              ∑ i : Fin d,
                ∫ s in Set.Icc (0 : ℝ) (T : ℝ),
                  (∂²[i, i] fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, s))
                    (Wc s.toNNReal ω)) +
            0)) := by
    exact (hFirstω.add hSpatialSubseq).add hRemainderSubseq
  have hApproxEq :
      (fun n : ℕ ↦
        F (Wc T ω, (T : ℝ)) - F (Wc 0 ω, 0)) =
      (fun n ↦
        dyadicMultidimensionalItoApproximationUpTo
            (timeSpaceGraphLift F)
            (Xω ω)
            T
            (φ n) +
          timeSpaceC21SpatialCorrectionApproximationUpTo (μ := μ) F hW T ω (φ n) +
          timeSpaceC21Remainder (μ := μ) F hW T ω (φ n)) := by
    funext n
    simpa [Xω, Wc, timeSpaceGraphPath] using
      timeSpaceC21DyadicDecomposition (μ := μ) F hW T ω (φ n)
  have hEndpointLimit :
      Tendsto
        (fun _ : ℕ ↦ F (Wc T ω, (T : ℝ)) - F (Wc 0 ω, 0))
        atTop
        (𝓝
          (((∑ i : Fin d, standardBrownianMotionVectorCoordinateItoIntegral F hW i T ω) +
              ∫ s in Set.Icc (0 : ℝ) (T : ℝ), (∂ₜ F) (Wc s.toNNReal ω, s)) +
            (((1 : ℝ) / 2) *
              ∑ i : Fin d,
                ∫ s in Set.Icc (0 : ℝ) (T : ℝ),
                  (∂²[i, i] fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, s))
                    (Wc s.toNNReal ω)) +
            0)) := by
    rw [hApproxEq]
    exact hApproxLimit
  have hEndpointEq :
      F (Wc T ω, (T : ℝ)) - F (Wc 0 ω, 0) =
        (((∑ i : Fin d, standardBrownianMotionVectorCoordinateItoIntegral F hW i T ω) +
            ∫ s in Set.Icc (0 : ℝ) (T : ℝ), (∂ₜ F) (Wc s.toNNReal ω, s)) +
          (((1 : ℝ) / 2) *
            ∑ i : Fin d,
              ∫ s in Set.Icc (0 : ℝ) (T : ℝ),
                (∂²[i, i] fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, s))
                  (Wc s.toNNReal ω)) +
          0) := by
    exact tendsto_nhds_unique tendsto_const_nhds hEndpointLimit
  -- Proof comment: once the dyadic remainder vanishes, the endpoint identity is the unique limit
  -- of the exact dyadic decomposition. The only remaining deterministic rewrite is the textbook
  -- drift `∂ₜ + (1/2)Δ`.
  calc
    F (Wc T ω, (T : ℝ)) - F (Wc 0 ω, 0)
        =
          (((∑ i : Fin d, standardBrownianMotionVectorCoordinateItoIntegral F hW i T ω) +
              ∫ s in Set.Icc (0 : ℝ) (T : ℝ), (∂ₜ F) (Wc s.toNNReal ω, s)) +
            (((1 : ℝ) / 2) *
              ∑ i : Fin d,
                ∫ s in Set.Icc (0 : ℝ) (T : ℝ),
                  (∂²[i, i] fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, s))
                    (Wc s.toNNReal ω)) +
            0) := hEndpointEq
    _ =
          ((∑ i : Fin d, standardBrownianMotionVectorCoordinateItoIntegral F hW i T ω) +
              ∫ s in Set.Icc (0 : ℝ) (T : ℝ), (∂ₜ F) (Wc s.toNNReal ω, s)) +
            ((1 : ℝ) / 2) *
              ∑ i : Fin d,
                ∫ s in Set.Icc (0 : ℝ) (T : ℝ),
                  (∂²[i, i] fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, s))
                    (Wc s.toNNReal ω) := by
          ring
    _ =
          (∑ i : Fin d, standardBrownianMotionVectorCoordinateItoIntegral F hW i T ω) +
            ((∫ s in Set.Icc (0 : ℝ) (T : ℝ), (∂ₜ F) (Wc s.toNNReal ω, s)) +
              ((1 : ℝ) / 2) *
                ∑ i : Fin d,
                  ∫ s in Set.Icc (0 : ℝ) (T : ℝ),
                    (∂²[i, i] fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, s))
                      (Wc s.toNNReal ω)) := by
          ring
    _ =
          (∑ i : Fin d, standardBrownianMotionVectorCoordinateItoIntegral F hW i T ω) +
            ∫ s in Set.Icc (0 : ℝ) (T : ℝ),
              (∂ₜ F) (Wc s.toNNReal ω, s) +
                ((1 : ℝ) / 2) *
                  Δ (fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, s))
                    (Wc s.toNNReal ω) := by
          rw [timeSpaceDrift_eq_laplacianIntegral (μ := μ) F hF hW T ω]

/-- Helper for `Corollary 25.35`: if two deterministic paths agree at every time, then the
time-dependent Ito drift integral computed along those paths is identical. -/
private lemma timeDependentItoDriftIntegral_congr
    (F : EuclideanSpace ℝ (Fin d) × ℝ → ℝ)
    {V₁ V₂ : NNReal → EuclideanSpace ℝ (Fin d)}
    (T : NNReal)
    (hEq : ∀ t : NNReal, V₁ t = V₂ t) :
    ∫ s in Set.Icc (0 : ℝ) (T : ℝ),
        (∂ₜ F) (V₁ s.toNNReal, s) +
          ((1 : ℝ) / 2) *
            Δ (fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, s))
              (V₁ s.toNNReal) =
      ∫ s in Set.Icc (0 : ℝ) (T : ℝ),
        (∂ₜ F) (V₂ s.toNNReal, s) +
          ((1 : ℝ) / 2) *
            Δ (fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, s))
              (V₂ s.toNNReal) := by
  -- Proof comment: pointwise equality of the two paths identifies the drift integrands on every
  -- time in `[0,T]`, so the interval integrals agree by `integral_congr_ae`.
  refine integral_congr_ae ?_
  refine Filter.Eventually.of_forall ?_
  intro s
  simp [hEq s.toNNReal]

/-- Corollary_25_35::statement_repair::6
Corollary 25.35 (Time-dependent Ito formula): if `F ∈ C^{2,1}(ℝ^d × ℝ)` and `W` is a standard
`d`-dimensional Brownian motion, then for each deterministic horizon `T` the fixed-time identity
for `W` itself holds almost surely, where the stochastic terms are the canonical coordinate Itô
integrals built from the canonical continuous version of `W`. -/
theorem brownian_time_dependent_ito_formula_ae_eq
    (F : EuclideanSpace ℝ (Fin d) × ℝ → ℝ)
    {W : NNReal → Ω → EuclideanSpace ℝ (Fin d)}
    (hF : IsTimeSpaceC21 F)
    (hW : IsStandardBrownianMotionVector μ W)
    (T : NNReal) :
    (fun ω ↦
      F (W T ω, (T : ℝ)) - F (W 0 ω, 0)) =ᵐ[μ]
      (fun ω ↦
        (∑ i : Fin d, standardBrownianMotionVectorCoordinateItoIntegral F hW i T ω) +
          ∫ s in Set.Icc (0 : ℝ) (T : ℝ),
            (∂ₜ F) (W s.toNNReal ω, s) +
              ((1 : ℝ) / 2) *
                Δ (fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, s))
                  (W s.toNNReal ω)) := by
  let Wc := standardBrownianMotionVectorContinuousVersion hW
  filter_upwards
      [continuousVersion_timeDependentIto_ae (μ := μ) F hF hW T,
        standardBrownianContinuousVersion_eq_ae_allTimes (μ := μ) hW] with ω hCore hEq
  have hIntegral :
      ∫ s in Set.Icc (0 : ℝ) (T : ℝ),
          (∂ₜ F) (Wc s.toNNReal ω, s) +
            ((1 : ℝ) / 2) *
              Δ (fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, s))
                (Wc s.toNNReal ω) =
        ∫ s in Set.Icc (0 : ℝ) (T : ℝ),
          (∂ₜ F) (W s.toNNReal ω, s) +
            ((1 : ℝ) / 2) *
              Δ (fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, s))
                (W s.toNNReal ω) := by
    -- Proof comment: the all-times modification event identifies the continuous version path and
    -- the original Brownian path, so the deterministic drift integral rewrites through the helper.
    simpa [Wc] using
      timeDependentItoDriftIntegral_congr
        (F := F)
        (V₁ := fun t ↦ Wc t ω)
        (V₂ := fun t ↦ W t ω)
        T
        hEq
  -- Proof comment: rewrite the terminal values and the deterministic drift along the single
  -- all-times modification event, leaving the stochastic integral terms untouched.
  calc
    F (W T ω, (T : ℝ)) - F (W 0 ω, 0)
        = F (Wc T ω, (T : ℝ)) - F (Wc 0 ω, 0) := by
            simp [Wc, hEq T, hEq 0]
    _ = (∑ i : Fin d, standardBrownianMotionVectorCoordinateItoIntegral F hW i T ω) +
          ∫ s in Set.Icc (0 : ℝ) (T : ℝ),
            (∂ₜ F) (Wc s.toNNReal ω, s) +
              ((1 : ℝ) / 2) *
                Δ (fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, s))
                  (Wc s.toNNReal ω) := hCore
    _ = (∑ i : Fin d, standardBrownianMotionVectorCoordinateItoIntegral F hW i T ω) +
          ∫ s in Set.Icc (0 : ℝ) (T : ℝ),
            (∂ₜ F) (W s.toNNReal ω, s) +
              ((1 : ℝ) / 2) *
                Δ (fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, s))
                  (W s.toNNReal ω) := by
            rw [hIntegral]

end ProbabilityTheory
