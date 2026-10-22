/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_52
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Lemma_21_5
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Remark_21_59
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_66
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_70
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_75

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

local notation "TimeFiltration" => Filtration NNReal mΩ
local notation "PathSpace" => C(NNReal, ℝ)

variable {ℱ : TimeFiltration}

/-- A continuous quadratic-covariation process of continuous local martingales `M` and `N` is a
continuous adapted process `A`, starting at `0` and with almost surely locally finite variation,
such that `MN - A` is a continuous local martingale. -/
structure IsContinuousQuadraticCovariationProcess
    (ℱ : TimeFiltration) (μ : Measure Ω)
    (M N A : NNReal → Ω → ℝ) : Prop where
  /-- The covariation process starts from `0`. -/
  zero : A 0 = 0
  /-- The covariation process is adapted to the ambient filtration. -/
  adapted : Adapted ℱ A
  /-- The covariation process has continuous sample paths. -/
  continuous : ∀ ω : Ω, Continuous (fun t : NNReal ↦ A t ω)
  /-- Almost every sample path of the covariation process has locally finite variation. -/
  locally_finite_variation :
    ∀ᵐ ω ∂μ,
      LocallyBoundedVariationOn
        (⟨fun t ↦ A t ω, continuous ω⟩ : PathSpace) Set.univ
  /-- Subtracting the covariation process from the pointwise product yields a local martingale. -/
  local_martingale_mul_sub :
    IsLocalMartingale ℱ μ (fun t ω ↦ M t ω * N t ω - A t ω)

/-- The mixed partition sum of `M` and `N` on `[0,T]` along the `n`-th row of an admissible
partition sequence. -/
def partitionQuadraticCovariationApproximationUpTo
    (M N : NNReal → Ω → ℝ) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (T : NNReal) (n : ℕ) (ω : Ω) : ℝ :=
  Finset.sum (Finset.range (partitionBoundIndex P n T)) fun k ↦
    (M (partitionNextPointUpTo P n k T) ω - M (P n k) ω) *
      (N (partitionNextPointUpTo P n k T) ω - N (P n k) ω)

-- Proof sketch: unfold `partitionQuadraticCovariationApproximationUpTo`.
/-- Expanding `partitionQuadraticCovariationApproximationUpTo` gives the finite sum of mixed
increments along the truncated partition row. -/
theorem partitionQuadraticCovariationApproximationUpTo_def
    (M N : NNReal → Ω → ℝ) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (T : NNReal) (n : ℕ) (ω : Ω) :
    partitionQuadraticCovariationApproximationUpTo M N P T n ω =
      Finset.sum (Finset.range (partitionBoundIndex P n T)) fun k ↦
        (M (partitionNextPointUpTo P n k T) ω - M (P n k) ω) *
          (N (partitionNextPointUpTo P n k T) ω - N (P n k) ω) := by
  -- Proof comment: the theorem just unfolds the local mixed partition-sum definition.
  rfl

/-- Helper for Corollary 21.73: the nonnegative rationals are dense in `NNReal`. -/
private lemma nnratDense : Dense (Set.range fun q : ℚ≥0 ↦ (q : NNReal)) := by
  -- Proof comment: every open interval in `NNReal` contains a nonnegative rational point.
  refine dense_of_exists_between ?_
  intro a b hab
  rcases NNReal.lt_iff_exists_rat_btwn a b |>.1 hab with ⟨q, hq0, haq, hqb⟩
  let q₀ : ℚ≥0 := ⟨q, hq0⟩
  refine ⟨(q₀ : NNReal), ?_, ?_, ?_⟩
  · exact ⟨q₀, rfl⟩
  · have hq' : (0 : ℝ) ≤ q := Rat.cast_nonneg.mpr hq0
    simpa [q₀, Real.toNNReal_of_nonneg hq'] using haq
  · have hq' : (0 : ℝ) ≤ q := Rat.cast_nonneg.mpr hq0
    simpa [q₀, Real.toNNReal_of_nonneg hq'] using hqb

/-- Helper for Corollary 21.73: a continuous path is determined by its values on `ℚ≥0`. -/
private lemma continuous_eq_const_of_eqOnNNRat
    {f : NNReal → ℝ} (hf : Continuous f) {c : ℝ}
    (hq : ∀ q : ℚ≥0, f q = c) :
    ∀ t : NNReal, f t = c := by
  -- Proof comment: continuity extends the rational-time identity from a dense subset to all times.
  have hEq :
      Set.EqOn f (fun _ : NNReal ↦ c) (Set.range fun q : ℚ≥0 ↦ (q : NNReal)) := by
    intro t ht
    rcases ht with ⟨q, rfl⟩
    simpa using hq q
  intro t
  exact congrFun (Continuous.ext_on nnratDense hf continuous_const hEq) t

/-- Helper for Corollary 21.73: two square-variation realizations of the same path agree. -/
private lemma squareVariation_eq_of_twoRealizations
    {G : PathSpace} {V W : NNReal → ℝ}
    (hV : HasSquareVariationAlong G V)
    (hW : HasSquareVariationAlong G W) :
    V = W := by
  -- Proof comment: compare the two limits of the same dyadic square-sum approximation.
  funext T
  exact tendsto_nhds_unique (hV T) (hW T)

/-- Helper for Corollary 21.73: a continuous path of locally finite variation has identically
vanishing square variation along every chosen square-variation realization. -/
private lemma squareVariation_eq_zero_of_locallyFiniteVariation
    {G : PathSpace} {V : NNReal → ℝ}
    (hV : HasSquareVariationAlong G V)
    (hG : LocallyBoundedVariationOn G Set.univ) :
    V = 0 := by
  -- Proof comment: compare the chosen realization with the canonical zero realization.
  exact squareVariation_eq_of_twoRealizations hV
    (hasSquareVariationAlong_zero_of_locallyBoundedVariationOn hG)

/-- Helper for Corollary 21.73: on `[s, t]`, the variation of a difference of monotone continuous
paths is bounded by the sum of the endpoint increments. -/
private lemma eVariationOn_Icc_sub_le_of_monotone_process
    {G Gplus Gminus : PathSpace} (hG : G = Gplus - Gminus) (hGplus_mono : Monotone Gplus)
    (hGminus_mono : Monotone Gminus) {s t : NNReal} (hst : s ≤ t) :
    eVariationOn G (Set.Icc s t) ≤
      ENNReal.ofReal ((Gplus t - Gplus s) + (Gminus t - Gminus s)) := by
  rw [hG]
  have hGplus_nonneg : 0 ≤ Gplus t - Gplus s := sub_nonneg_of_le (hGplus_mono hst)
  have hGminus_nonneg : 0 ≤ Gminus t - Gminus s := sub_nonneg_of_le (hGminus_mono hst)
  have hGplus_var :
      eVariationOn Gplus (Set.Icc s t) ≤ ENNReal.ofReal (Gplus t - Gplus s) := by
    simpa [Set.univ_inter] using
      (MonotoneOn.eVariationOn_le (f := Gplus) (s := Set.univ) (hGplus_mono.monotoneOn Set.univ)
        (a := s) (b := t) (Set.mem_univ _) (Set.mem_univ _))
  have hGminus_var :
      eVariationOn Gminus (Set.Icc s t) ≤ ENNReal.ofReal (Gminus t - Gminus s) := by
    simpa [Set.univ_inter] using
      (MonotoneOn.eVariationOn_le (f := Gminus) (s := Set.univ)
        (hGminus_mono.monotoneOn Set.univ) (a := s) (b := t) (Set.mem_univ _) (Set.mem_univ _))
  apply iSup_le
  rintro ⟨n, ⟨u, hu, us⟩⟩
  calc
    ∑ i ∈ Finset.range n, edist ((Gplus - Gminus) (u (i + 1))) ((Gplus - Gminus) (u i))
        ≤ ∑ i ∈ Finset.range n,
            (edist (Gplus (u (i + 1))) (Gplus (u i)) +
              edist (Gminus (u (i + 1))) (Gminus (u i))) := by
          refine Finset.sum_le_sum fun i hi => ?_
          simpa [Pi.sub_apply] using
            (edist_vsub_vsub_le (Gplus (u (i + 1))) (Gminus (u (i + 1))) (Gplus (u i))
              (Gminus (u i)))
    _ = (∑ i ∈ Finset.range n, edist (Gplus (u (i + 1))) (Gplus (u i))) +
          ∑ i ∈ Finset.range n, edist (Gminus (u (i + 1))) (Gminus (u i)) := by
      rw [Finset.sum_add_distrib]
    _ ≤ eVariationOn Gplus (Set.Icc s t) + eVariationOn Gminus (Set.Icc s t) := by
      exact add_le_add (eVariationOn.sum_le hu us) (eVariationOn.sum_le hu us)
    _ ≤ ENNReal.ofReal (Gplus t - Gplus s) + ENNReal.ofReal (Gminus t - Gminus s) := by
      exact add_le_add hGplus_var hGminus_var
    _ = ENNReal.ofReal ((Gplus t - Gplus s) + (Gminus t - Gminus s)) := by
      rw [ENNReal.ofReal_add hGplus_nonneg hGminus_nonneg]

/-- Helper for Corollary 21.73: a difference of two continuous monotone increasing paths has
locally bounded variation on `[0, ∞)`. -/
private lemma locallyBoundedVariationOn_univ_of_sub_monotone
    {G Gplus Gminus : PathSpace} (hG : G = Gplus - Gminus) (hGplus_mono : Monotone Gplus)
    (hGminus_mono : Monotone Gminus) :
    LocallyBoundedVariationOn G Set.univ := by
  -- Proof comment: the interval variation bound from the monotone decomposition gives finite
  -- variation on each initial interval `[0, t]`.
  rw [locallyBoundedVariationOn_univ_iff_forall_boundedVariationOn_Icc_zero]
  intro t
  have hbound :=
    eVariationOn_Icc_sub_le_of_monotone_process hG hGplus_mono hGminus_mono (s := 0) (t := t)
      bot_le
  simpa [BoundedVariationOn] using (hbound.trans_lt ENNReal.ofReal_lt_top).ne

/-- Helper for Corollary 21.73: polarizing square-variation witnesses for `M + N` and `M - N`
produces a continuous quadratic-covariation witness for `M` and `N`. -/
private lemma isContinuousQuadraticCovariationProcess_polarization
    {M N Aadd Asub : NNReal → Ω → ℝ}
    (hAdd : IsContinuousSquareVariationProcess ℱ μ (fun t ω ↦ M t ω + N t ω) Aadd)
    (hSub : IsContinuousSquareVariationProcess ℱ μ (fun t ω ↦ M t ω - N t ω) Asub) :
    IsContinuousQuadraticCovariationProcess ℱ μ M N
      (fun t ω ↦ (1 / 4 : ℝ) * (Aadd t ω - Asub t ω)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- Proof comment: both square-variation witnesses start from `0`, so their polarization does
    -- as well.
    funext ω
    simp [hAdd.zero, hSub.zero]
  · -- Proof comment: adaptedness is stable under subtraction and scalar multiplication.
    simpa [Pi.smul_apply] using Adapted.smul (1 / 4 : ℝ) (hAdd.adapted.sub hSub.adapted)
  · -- Proof comment: the polarized path is a scalar multiple of the difference of two continuous
    -- bracket paths.
    intro ω
    simpa [Pi.smul_apply] using
      Continuous.const_mul ((hAdd.continuous ω).sub (hSub.continuous ω)) (1 / 4 : ℝ)
  · -- Proof comment: after scaling the two increasing bracket paths, the local monotone-
    -- difference variation estimate applies pathwise.
    filter_upwards with ω
    let G : PathSpace := ⟨fun t ↦ (1 / 4 : ℝ) * (Aadd t ω - Asub t ω), by
      simpa [Pi.smul_apply] using
        Continuous.const_mul ((hAdd.continuous ω).sub (hSub.continuous ω)) (1 / 4 : ℝ)⟩
    let Gplus : PathSpace := (1 / 4 : ℝ) • ⟨fun t ↦ Aadd t ω, hAdd.continuous ω⟩
    let Gminus : PathSpace := (1 / 4 : ℝ) • ⟨fun t ↦ Asub t ω, hSub.continuous ω⟩
    have hG :
        G = Gplus - Gminus := by
      ext t
      simp [G, Gplus, Gminus]
      ring
    have hGplus_mono : Monotone Gplus := by
      intro s t hst
      exact mul_le_mul_of_nonneg_left (hAdd.monotone ω hst) (by positivity)
    have hGminus_mono : Monotone Gminus := by
      intro s t hst
      exact mul_le_mul_of_nonneg_left (hSub.monotone ω hst) (by positivity)
    exact locallyBoundedVariationOn_univ_of_sub_monotone hG hGplus_mono hGminus_mono
  · -- Proof comment: the mixed product is the quarter-scaled difference of the two square-minus-
    -- bracket local martingales from the polarization identity.
    have hDiffSq :
        IsContinuousLocalMartingale ℱ μ
          (fun t ω ↦
            ((M t ω + N t ω) ^ 2 - Aadd t ω) -
              ((M t ω - N t ω) ^ 2 - Asub t ω)) := by
      simpa using hAdd.local_martingale_sq_sub.sub hSub.local_martingale_sq_sub
    convert (hDiffSq.const_mul (1 / 4 : ℝ)).local_martingale using 1
    funext t ω
    ring

/-- Helper for Corollary 21.73: if a continuous local martingale has almost surely vanishing
square variation, then its square is again a continuous local martingale. -/
private lemma isContinuousLocalMartingale_sq_of_ae_squareVariation_eq_zero
    {X B : NNReal → Ω → ℝ}
    (hX : IsContinuousLocalMartingale ℱ μ X)
    (hB : IsContinuousSquareVariationProcess ℱ μ X B)
    (hzero : ∀ᵐ ω ∂μ, ∀ t : NNReal, B t ω = 0) :
    IsContinuousLocalMartingale ℱ μ (fun t ω ↦ X t ω ^ 2) := by
  have hSquareAdapted : Adapted ℱ (fun t ω ↦ X t ω ^ 2) := by
    simpa [pow_two] using hX.adapted.mul hX.adapted
  have hSquareCont : ∀ ω : Ω, Continuous fun t : NNReal ↦ X t ω ^ 2 := by
    intro ω
    simpa [pow_two] using (hX.continuous ω).mul (hX.continuous ω)
  refine ⟨?_, hSquareCont⟩
  -- Proof comment: `X² - B` is the given square local martingale, and the all-time almost-sure
  -- vanishing of `B` lets us replace it by `X²`.
  exact isLocalMartingale_congr_ae_allTimes hB.local_martingale_sq_sub.local_martingale
    hSquareAdapted hSquareCont <| by
      filter_upwards [hzero] with ω hω t
      simpa using hω t

/-- Helper for Corollary 21.73: if `M` and `M²` are martingales, then the terminal-initial
cross moment equals the initial square moment. -/
private lemma integral_terminal_mul_initial_eq_initial_sq_of_martingale_sq_martingale
    {M : NNReal → Ω → ℝ} (hM : Martingale M ℱ μ)
    (hMsq : Martingale (fun t ω ↦ M t ω ^ 2) ℱ μ) (t : NNReal) :
    μ[fun ω ↦ M t ω * M 0 ω] = μ[fun ω ↦ M 0 ω ^ 2] := by
  have hMt_meas : AEStronglyMeasurable (M t) μ := by
    exact ((hM.stronglyMeasurable t).mono (ℱ.le t)).aestronglyMeasurable
  have hM0_meas : AEStronglyMeasurable (M 0) μ := by
    exact ((hM.stronglyMeasurable 0).mono (ℱ.le 0)).aestronglyMeasurable
  have hMtLp : MemLp (M t) 2 μ :=
    (memLp_two_iff_integrable_sq hMt_meas).2 (hMsq.integrable t)
  have hM0Lp : MemLp (M 0) 2 μ :=
    (memLp_two_iff_integrable_sq hM0_meas).2 (hMsq.integrable 0)
  have hProdInt : Integrable (fun ω ↦ M t ω * M 0 ω) μ := by
    simpa using MemLp.integrable_mul hMtLp hM0Lp
  have hCond :
      μ[(fun ω ↦ M t ω * M 0 ω) | ℱ 0] =ᵐ[μ] fun ω ↦ M 0 ω ^ 2 := by
    -- Proof comment: pull the `ℱ₀`-measurable factor `M 0` outside the conditional expectation
    -- and then use the martingale identity at time `0`.
    refine (condExp_mul_of_stronglyMeasurable_right (hM.stronglyMeasurable 0) hProdInt
      (hM.integrable t)).trans ?_
    refine ((hM.condExp_ae_eq (zero_le t)).mul Filter.EventuallyEq.rfl).trans ?_
    filter_upwards with ω
    simp [pow_two]
  -- Proof comment: integrating the conditional-expectation identity gives the scalar cross-term
  -- formula used in the fixed-time collapse.
  calc
    μ[fun ω ↦ M t ω * M 0 ω] = μ[μ[(fun ω ↦ M t ω * M 0 ω) | ℱ 0]] := by
      symm
      exact integral_condExp (ℱ.le 0)
    _ = μ[fun ω ↦ M 0 ω ^ 2] := by
      exact integral_congr_ae hCond

/-- Helper for Corollary 21.73: once a martingale and its square are martingales, every fixed-time
value agrees almost surely with the initial value. -/
private lemma ae_eq_initial_at_time_of_martingale_sq_martingale
    {M : NNReal → Ω → ℝ} (hM : Martingale M ℱ μ)
    (hMsq : Martingale (fun t ω ↦ M t ω ^ 2) ℱ μ) (t : NNReal) :
    M t =ᵐ[μ] M 0 := by
  let Y : Ω → ℝ := fun ω ↦ M t ω - M 0 ω
  have hMt_meas : AEStronglyMeasurable (M t) μ := by
    exact ((hM.stronglyMeasurable t).mono (ℱ.le t)).aestronglyMeasurable
  have hM0_meas : AEStronglyMeasurable (M 0) μ := by
    exact ((hM.stronglyMeasurable 0).mono (ℱ.le 0)).aestronglyMeasurable
  have hMtLp : MemLp (M t) 2 μ :=
    (memLp_two_iff_integrable_sq hMt_meas).2 (hMsq.integrable t)
  have hM0Lp : MemLp (M 0) 2 μ :=
    (memLp_two_iff_integrable_sq hM0_meas).2 (hMsq.integrable 0)
  have hYLp : MemLp Y 2 μ := by
    simpa [Y] using hMtLp.sub hM0Lp
  have hProdInt : Integrable (fun ω ↦ M t ω * M 0 ω) μ := by
    simpa using MemLp.integrable_mul hMtLp hM0Lp
  have hCrossEq : μ[fun ω ↦ M t ω * M 0 ω] = μ[fun ω ↦ M 0 ω ^ 2] :=
    integral_terminal_mul_initial_eq_initial_sq_of_martingale_sq_martingale hM hMsq t
  have hSqEq : μ[fun ω ↦ M t ω ^ 2] = μ[fun ω ↦ M 0 ω ^ 2] := by
    simpa using (hMsq.setIntegral_eq (zero_le t) (s := Set.univ) MeasurableSet.univ).symm
  have hSecondMomentZero : ∫ ω, Y ω ^ 2 ∂μ = 0 := by
    have hMidInt : Integrable (fun ω ↦ M t ω ^ 2 - 2 * (M t ω * M 0 ω)) μ := by
      exact (hMsq.integrable t).sub (hProdInt.const_mul 2)
    have hSecondMoment :
        ∫ ω, (M t ω - M 0 ω) ^ 2 ∂μ =
          ∫ ω, M t ω ^ 2 ∂μ - 2 * ∫ ω, M t ω * M 0 ω ∂μ + ∫ ω, M 0 ω ^ 2 ∂μ := by
      have hMid :
          ∫ ω, (M t ω ^ 2 - 2 * (M t ω * M 0 ω)) ∂μ =
            ∫ ω, M t ω ^ 2 ∂μ - 2 * ∫ ω, M t ω * M 0 ω ∂μ := by
        calc
          ∫ ω, (M t ω ^ 2 - 2 * (M t ω * M 0 ω)) ∂μ =
              ∫ ω, M t ω ^ 2 ∂μ - ∫ ω, 2 * (M t ω * M 0 ω) ∂μ := by
            simpa using integral_sub' (hMsq.integrable t) (hProdInt.const_mul 2)
          _ = ∫ ω, M t ω ^ 2 ∂μ - 2 * ∫ ω, M t ω * M 0 ω ∂μ := by
            rw [integral_const_mul]
      calc
        ∫ ω, (M t ω - M 0 ω) ^ 2 ∂μ =
            ∫ ω, ((M t ω ^ 2 - 2 * (M t ω * M 0 ω)) + M 0 ω ^ 2) ∂μ := by
              congr 1
              ext ω
              ring
        _ = ∫ ω, (M t ω ^ 2 - 2 * (M t ω * M 0 ω)) ∂μ + ∫ ω, M 0 ω ^ 2 ∂μ := by
              simpa using integral_add hMidInt (hMsq.integrable 0)
        _ = ∫ ω, M t ω ^ 2 ∂μ - 2 * ∫ ω, M t ω * M 0 ω ∂μ + ∫ ω, M 0 ω ^ 2 ∂μ := by
              rw [hMid]
    calc
      ∫ ω, Y ω ^ 2 ∂μ = ∫ ω, (M t ω - M 0 ω) ^ 2 ∂μ := by rfl
      _ = μ[fun ω ↦ M t ω ^ 2] - 2 * μ[fun ω ↦ M t ω * M 0 ω] + μ[fun ω ↦ M 0 ω ^ 2] := by
        simpa using hSecondMoment
      _ = 0 := by
        nlinarith [hCrossEq, hSqEq]
  have hYsqInt : Integrable (fun ω ↦ Y ω ^ 2) μ := hYLp.integrable_sq
  have hYsqNonneg : 0 ≤ᵐ[μ] fun ω ↦ Y ω ^ 2 := Filter.Eventually.of_forall fun ω ↦ sq_nonneg _
  filter_upwards [(integral_eq_zero_iff_of_nonneg_ae hYsqNonneg hYsqInt).1 hSecondMomentZero]
    with ω hω
  -- Proof comment: a nonnegative square can integrate to zero only when the increment itself
  -- vanishes almost surely.
  exact sub_eq_zero.mp <| by
    simpa [Y] using (sq_eq_zero_iff.mp hω)

/-- Helper for Corollary 21.73: squaring a bounded process preserves boundedness. -/
private lemma isBoundedProcess_sq
    {M : NNReal → Ω → ℝ} (hbounded : IsBoundedProcess M) :
    IsBoundedProcess (fun t ω ↦ M t ω ^ 2) := by
  rcases hbounded with ⟨C, hC_nonneg, hC⟩
  refine ⟨C ^ 2, by positivity, ?_⟩
  intro t ω
  have hCω := hC t ω
  -- Proof comment: `|M_t| ≤ C` bounds the square by `C²`.
  have hsq : M t ω ^ 2 ≤ C ^ 2 := by
    have hsq' : |M t ω| ^ 2 ≤ C ^ 2 := by
      exact sq_le_sq.mpr (by simpa [abs_of_nonneg hC_nonneg] using hCω)
    simpa [sq_abs] using hsq'
  have hsq_nonneg : 0 ≤ M t ω ^ 2 := by positivity
  simpa [abs_of_nonneg hsq_nonneg] using hsq

/-- Helper for Corollary 21.73: a bounded stopped process inherits the martingale property for its
square from the square local-martingale owner. -/
private lemma martingale_sq_of_bounded_stoppedProcess
    {M : NNReal → Ω → ℝ}
    (hMsq : IsContinuousLocalMartingale ℱ μ (fun t ω ↦ M t ω ^ 2))
    {τ : Ω → ENNReal} (hτ : IsStoppingTime ℱ τ)
    (hbounded : IsBoundedProcess (stoppedProcess M τ)) :
    Martingale (fun t ω ↦ (stoppedProcess M τ t ω) ^ 2) ℱ μ := by
  have hStoppedSqLocal :
      IsLocalMartingale ℱ μ (stoppedProcess (fun t ω ↦ M t ω ^ 2) τ) := by
    -- Proof comment: stop the square process first; this is the local owner supplied by the
    -- stopped-process bridge.
    exact isLocalMartingale_stoppedProcess hMsq.local_martingale hMsq.continuous hτ
  have hTargetLocal :
      IsLocalMartingale ℱ μ (fun t ω ↦ (stoppedProcess M τ t ω) ^ 2) := by
    -- Proof comment: stopping and squaring commute pointwise because both evaluate `M` at the
    -- clipped time `t ∧ τ(ω)`.
    simpa [stoppedProcess] using hStoppedSqLocal
  -- Proof comment: the deterministic bound on `stoppedProcess M τ` yields the bounded-in-time
  -- hypothesis needed to upgrade the local martingale owner to a genuine martingale.
  exact martingale_of_bounded_local_martingale hTargetLocal
    (boundedInTimeAe_of_boundedProcess (isBoundedProcess_sq hbounded))

/-- Helper for Corollary 21.73: convergence of the localizing stopping times to `∞` forces the
corresponding fixed-time stopped values to converge to the original value. -/
private lemma ae_tendsto_stoppedProcess_at_time_of_stoppingTimeApproximationUpToInfinity
    {M : NNReal → Ω → ℝ} {τSeq : ℕ → Ω → ENNReal}
    (hApprox :
      IsStoppingTimeApproximationUpTo ℱ μ τSeq (fun _ ↦ (∞ : ENNReal))) (u : NNReal) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ stoppedProcess M (τSeq n) u ω) atTop (nhds (M u ω)) := by
  rcases hApprox with ⟨_, _, hlim⟩
  filter_upwards [hlim] with ω hω
  rcases hω with ⟨_, hωtendsto⟩
  -- Proof comment: convergence of `τₙ ω` to `∞` makes the stop inactive for all large `n`.
  have hu_eventually : ∀ᶠ n in atTop, (u : ENNReal) ≤ τSeq n ω :=
    (ENNReal.tendsto_nhds_top_iff_nnreal.1 hωtendsto u).mono fun _ hn ↦ le_of_lt hn
  have hEventuallyEq :
      (fun n ↦ stoppedProcess M (τSeq n) u ω) =ᶠ[atTop] fun _ ↦ M u ω :=
    hu_eventually.mono fun _ hn ↦ stoppedProcess_eq_of_le hn
  exact Tendsto.congr' hEventuallyEq.symm tendsto_const_nhds

/-- Helper for Corollary 21.73: a continuous local martingale whose sample paths have almost
surely locally finite variation is almost surely constant in time. -/
private lemma ae_eq_initial_of_ae_locallyFiniteVariation
    {X : NNReal → Ω → ℝ} (hX : IsContinuousLocalMartingale ℱ μ X)
    (hfv :
      ∀ᵐ ω ∂μ,
        LocallyBoundedVariationOn
          (⟨fun t ↦ X t ω, hX.continuous ω⟩ : PathSpace) Set.univ) :
    ∀ᵐ ω ∂μ, ∀ t : NNReal, X t ω = X 0 ω := by
  rcases existsUnique_continuousSquareVariationProcess (ℱ := ℱ) (μ := μ) hX with
    ⟨B, hB, _⟩
  have hzero :
      ∀ᵐ ω ∂μ, ∀ t : NNReal, B t ω = 0 := by
    filter_upwards [ae_hasSquareVariationAlong_continuousSquareVariationProcess hX hB, hfv]
      with ω hsq hvar
    let bracketPath : PathSpace := ⟨fun t ↦ B t ω, hB.continuous ω⟩
    have hsq' :
        HasSquareVariationAlong
          (⟨fun t ↦ X t ω, hX.continuous ω⟩ : PathSpace) bracketPath := by
      -- Proof comment: repackage the chosen square-variation path as a continuous path to match
      -- the pathwise square-variation API.
      simpa [bracketPath] using hsq
    have hzeroPath : bracketPath = 0 := by
      ext t
      exact congrFun (squareVariation_eq_zero_of_locallyFiniteVariation hsq' hvar) t
    intro t
    simpa [bracketPath] using congrArg (fun f : PathSpace ↦ f t) hzeroPath
  have hX_upToInfinity : IsLocalMartingaleUpTo ℱ μ (fun _ ↦ (∞ : ENNReal)) X := by
    exact (isLocalMartingaleUpTo_iff ℱ μ (fun _ ↦ (∞ : ENNReal)) X).2
      ((isLocalMartingale_iff ℱ μ X).1 hX.local_martingale)
  rcases
      (isLocalMartingaleUpTo_iff_exists_bounded_stopped_martingale_sequence
        (ℱ := ℱ) (μ := μ) (τ := fun _ ↦ (∞ : ENNReal)) (M := X) hX.adapted hX.continuous).1
        hX_upToInfinity with
    ⟨τSeq, hApprox, hMart, hBound⟩
  let hSquareLocal :=
    isContinuousLocalMartingale_sq_of_ae_squareVariation_eq_zero hX hB hzero
  have hRat :
      ∀ᵐ ω ∂μ, ∀ q : ℚ≥0, X (q : NNReal) ω = X 0 ω := by
    rw [ae_all_iff]
    intro q
    have hAllStoppedEq :
        ∀ᵐ ω ∂μ, ∀ n : ℕ, stoppedProcess X (τSeq n) (q : NNReal) ω = X 0 ω := by
      rw [ae_all_iff]
      intro n
      have hSqMart :
          Martingale (fun u ω ↦ (stoppedProcess X (τSeq n) u ω) ^ 2) ℱ μ :=
        martingale_sq_of_bounded_stoppedProcess hSquareLocal (hApprox.2.1 n) (hBound n)
      have hEqStopped :
          stoppedProcess X (τSeq n) (q : NNReal) =ᵐ[μ] stoppedProcess X (τSeq n) 0 :=
        ae_eq_initial_at_time_of_martingale_sq_martingale (hMart n) hSqMart (q : NNReal)
      -- Proof comment: time `0` is never affected by stopping, so the initial value is `X 0`.
      exact hEqStopped.trans <| Filter.Eventually.of_forall fun ω ↦ by
        simp [stoppedProcess]
    have hTendsto :
        ∀ᵐ ω ∂μ,
          Tendsto (fun n ↦ stoppedProcess X (τSeq n) (q : NNReal) ω) atTop
            (nhds (X (q : NNReal) ω)) :=
      ae_tendsto_stoppedProcess_at_time_of_stoppingTimeApproximationUpToInfinity hApprox
        (q : NNReal)
    filter_upwards [hAllStoppedEq, hTendsto] with ω hωEq hωTendsto
    have hEventuallyEq :
        (fun n ↦ stoppedProcess X (τSeq n) (q : NNReal) ω) =ᶠ[atTop] fun _ ↦ X 0 ω :=
      Filter.Eventually.of_forall hωEq
    -- Proof comment: the stopped values converge to `X q ω`, but they are already constantly
    -- equal to `X 0 ω`, so uniqueness of limits gives the rational-time identity.
    exact tendsto_nhds_unique hωTendsto (Tendsto.congr' hEventuallyEq.symm tendsto_const_nhds)
  filter_upwards [hRat] with ω hω t
  -- Proof comment: continuity extends the rational-time identity to every nonnegative time.
  exact continuous_eq_const_of_eqOnNNRat (hX.continuous ω) (fun q ↦ hω q) t

/-- Helper for Corollary 21.73: a continuous local martingale that starts at `0` and has almost
surely locally finite variation is indistinguishable from the zero process. -/
private lemma areIndistinguishable_zero_of_continuousLocalMartingale_zero_initial_ae_locallyFiniteVariation
    {X : NNReal → Ω → ℝ} (hX : IsContinuousLocalMartingale ℱ μ X) (hX0 : X 0 = 0)
    (hfv :
      ∀ᵐ ω ∂μ,
        LocallyBoundedVariationOn
          (⟨fun t ↦ X t ω, hX.continuous ω⟩ : PathSpace) Set.univ) :
    AreIndistinguishable μ X 0 := by
  have hAllZero : ∀ᵐ ω ∂μ, ∀ t : NNReal, X t ω = 0 := by
    filter_upwards [ae_eq_initial_of_ae_locallyFiniteVariation hX hfv] with ω hω t
    simpa using (hω t).trans (congrFun hX0 ω)
  have hRatZero : ∀ q : ℚ≥0, X (q : NNReal) =ᵐ[μ] 0 := by
    intro q
    filter_upwards [hAllZero] with ω hω
    simpa using hω (q : NNReal)
  let N : Set Ω := ⋃ q : ℚ≥0, {ω | X (q : NNReal) ω ≠ 0}
  refine ⟨N, ?_, ?_, ?_⟩
  · -- Proof comment: `N` is a countable union of measurable disagreement sets at rational times.
    refine MeasurableSet.iUnion ?_
    intro q
    exact (((hX.adapted (q : NNReal)).mono (ℱ.le (q : NNReal))).measurable).measurableSet_ne
      measurable_const
  · -- Proof comment: each rational-time disagreement set is null, hence so is their union.
    refine measure_iUnion_null ?_
    intro q
    rw [ae_iff]
    simpa using hRatZero q
  · intro t ω hω
    by_cases hωN : ω ∈ N
    · exact hωN
    · have hRatω : ∀ q : ℚ≥0, X (q : NNReal) ω = 0 := by
        intro q
        by_contra hq
        exact hωN <| Set.mem_iUnion.2 ⟨q, hq⟩
      have hZero : X t ω = 0 := by
        exact continuous_eq_const_of_eqOnNNRat (hX.continuous ω) hRatω t
      exact (hω hZero).elim

/-- Helper for Corollary 21.73: scalar multiplication preserves convergence in measure for real-
valued random functions. -/
private lemma tendstoInMeasure_const_mul
    {ι : Type*} {l : Filter ι} {f : ι → Ω → ℝ} {g : Ω → ℝ} (c : ℝ)
    (hf : TendstoInMeasure μ f l g) :
    TendstoInMeasure μ (fun i ω ↦ c * f i ω) l (fun ω ↦ c * g ω) := by
  rw [MeasureTheory.tendstoInMeasure_iff_measureReal_norm] at hf ⊢
  intro ε hε
  by_cases hc : c = 0
  · -- Proof comment: when `c = 0`, both processes are identically zero, so every deviation set
    -- is empty for `ε > 0`.
    simpa [hc, not_le.mpr hε] using
      (tendsto_const_nhds : Tendsto (fun _ : ι ↦ (0 : ℝ)) l (𝓝 0))
  · have hcabs : 0 < |c| := abs_pos.mpr hc
    have hscaled := hf (ε / |c|) (by positivity)
    have hEq :
        (fun i ↦ μ.real {ω | ε ≤ ‖c * f i ω - c * g ω‖}) =
          fun i ↦ μ.real {ω | ε / |c| ≤ ‖f i ω - g ω‖} := by
      funext i
      congr 1
      ext ω
      change ε ≤ ‖c * f i ω - c * g ω‖ ↔ ε / |c| ≤ ‖f i ω - g ω‖
      rw [show c * f i ω - c * g ω = c * (f i ω - g ω) by ring, norm_mul, Real.norm_eq_abs]
      constructor
      · intro hω
        rw [div_le_iff₀ hcabs]
        simpa [mul_comm] using hω
      · intro hω
        rw [div_le_iff₀ hcabs] at hω
        simpa [mul_comm] using hω
    rw [hEq]
    exact hscaled

/-- Helper for Corollary 21.73: subtraction preserves convergence in measure for real-valued
random functions. -/
private lemma tendstoInMeasure_sub
    {ι : Type*} {l : Filter ι} {f g : ι → Ω → ℝ} {F G : Ω → ℝ}
    (hf : TendstoInMeasure μ f l F) (hg : TendstoInMeasure μ g l G) :
    TendstoInMeasure μ (fun i ω ↦ f i ω - g i ω) l (fun ω ↦ F ω - G ω) := by
  rw [MeasureTheory.tendstoInMeasure_iff_measureReal_norm] at hf hg ⊢
  intro ε hε
  have hε2 : 0 < ε / 2 := by positivity
  have hf' := hf (ε / 2) hε2
  have hg' := hg (ε / 2) hε2
  have hUpper :
      ∀ᶠ i in l,
        μ.real {ω | ε ≤ ‖(f i ω - g i ω) - (F ω - G ω)‖} ≤
          μ.real {ω | ε / 2 ≤ ‖f i ω - F ω‖} +
            μ.real {ω | ε / 2 ≤ ‖g i ω - G ω‖} := by
    refine Filter.Eventually.of_forall ?_
    intro i
    refine (MeasureTheory.measureReal_mono ?_).trans (MeasureTheory.measureReal_union_le _ _)
    intro ω hω
    have htri :
        ‖(f i ω - g i ω) - (F ω - G ω)‖ ≤ ‖f i ω - F ω‖ + ‖g i ω - G ω‖ := by
      rw [show (f i ω - g i ω) - (F ω - G ω) = (f i ω - F ω) - (g i ω - G ω) by ring]
      exact norm_sub_le _ _
    have hsum : ε ≤ ‖f i ω - F ω‖ + ‖g i ω - G ω‖ := le_trans hω htri
    by_cases hleft : ε / 2 ≤ ‖f i ω - F ω‖
    · exact Or.inl hleft
    · have hleft_lt : ‖f i ω - F ω‖ < ε / 2 := lt_of_not_ge hleft
      have hright : ε / 2 ≤ ‖g i ω - G ω‖ := by
        nlinarith
      exact Or.inr hright
  have hSum :
      Tendsto
        (fun i ↦
          μ.real {ω | ε / 2 ≤ ‖f i ω - F ω‖} +
            μ.real {ω | ε / 2 ≤ ‖g i ω - G ω‖})
        l (𝓝 0) := by
    simpa using hf'.add hg'
  -- Proof comment: the bad event for the difference is contained in the union of the two bad
  -- events at scale `ε / 2`, so squeeze by the sum of their measures.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hSum ?_ hUpper
  refine Filter.Eventually.of_forall ?_
  intro i
  exact MeasureTheory.measureReal_nonneg

/-- Helper for Corollary 21.73: the mixed partition sum is the polarization difference of the
quadratic partition sums for `M + N` and `M - N`. -/
private lemma partitionQuadraticCovariationApproximationUpTo_eq_polarization
    {M N : NNReal → Ω → ℝ}
    (hM_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ M t ω)
    (hN_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ N t ω)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P] (T : NNReal) (n : ℕ) :
    partitionQuadraticCovariationApproximationUpTo M N P T n =
      fun ω ↦
        ((weightedPartitionQuadraticVariationApproximationUpTo (fun _ ↦ (1 : ℝ))
            (fun t ↦ M t ω + N t ω) P T n) -
          (weightedPartitionQuadraticVariationApproximationUpTo (fun _ ↦ (1 : ℝ))
            (fun t ↦ M t ω - N t ω) P T n)) / 4 := by
  funext ω
  let F : PathSpace := ⟨fun t ↦ M t ω, hM_cont ω⟩
  let G : PathSpace := ⟨fun t ↦ N t ω, hN_cont ω⟩
  calc
    partitionQuadraticCovariationApproximationUpTo M N P T n ω =
        partitionQuadraticCovariationSum P F G T n := by
          simp [partitionQuadraticCovariationApproximationUpTo, partitionQuadraticCovariationSum,
            F, G]
    _ =
        ((partitionPVariationSum P 2 (F + G) T n) -
          (partitionPVariationSum P 2 (F - G) T n)) / 4 := by
          exact partitionQuadraticCovariationSum_eq_polarization P F G T n
    _ =
        ((weightedPartitionQuadraticVariationApproximationUpTo (fun _ ↦ (1 : ℝ))
            (fun t ↦ M t ω + N t ω) P T n) -
          (weightedPartitionQuadraticVariationApproximationUpTo (fun _ ↦ (1 : ℝ))
            (fun t ↦ M t ω - N t ω) P T n)) / 4 := by
          rw [← weightedPartitionQuadraticVariationApproximationUpTo_one_eq_partitionPVariationSum
              (X := F + G) (P := P) (T := T) (n := n)]
          rw [← weightedPartitionQuadraticVariationApproximationUpTo_one_eq_partitionPVariationSum
              (X := F - G) (P := P) (T := T) (n := n)]
          simp [F, G]

/-- Helper for Corollary 21.73: if the difference process `A - A'` is indistinguishable from `0`,
then `A` and `A'` are indistinguishable. -/
private lemma areIndistinguishable_of_sub_zero
    {A A' : NNReal → Ω → ℝ}
    (h : AreIndistinguishable μ (fun t ω ↦ A t ω - A' t ω) 0) :
    AreIndistinguishable μ A A' := by
  rcases h with ⟨N, hN_meas, hN_zero, hNsub⟩
  refine ⟨N, hN_meas, hN_zero, ?_⟩
  intro t ω hω
  exact hNsub t <| by
    exact sub_ne_zero.mpr hω

-- Proof sketch: apply the square-variation existence theorem to `M + N` and `M - N`, define the
-- mixed bracket by the polarization identity `(1 / 4) * (⟨M + N⟩ - ⟨M - N⟩)`, use that a
-- difference of increasing continuous paths has locally finite variation, and prove uniqueness up
-- to indistinguishability by subtracting two candidates to obtain a continuous local martingale of
-- locally finite variation.
/-- Corollary 21.73: if `M` and `N` are continuous local martingales, then there exists a
continuous adapted process starting at `0`, with almost surely locally finite variation, whose
subtraction from the product process `MN` is again a continuous local martingale; any two such
processes are indistinguishable. This process is the quadratic covariation `⟨M,N⟩`. -/
theorem existsUnique_continuousQuadraticCovariationProcess
    {M N : NNReal → Ω → ℝ} (hM : M ∈ Mlocc ℱ μ) (hN : N ∈ Mlocc ℱ μ) :
    ∃ A : NNReal → Ω → ℝ,
      IsContinuousQuadraticCovariationProcess ℱ μ M N A ∧
        ∀ A' : NNReal → Ω → ℝ,
          IsContinuousQuadraticCovariationProcess ℱ μ M N A' →
            AreIndistinguishable μ A A' := by
  rcases (mem_Mlocc_iff ℱ μ M).1 hM with hMcont
  rcases (mem_Mlocc_iff ℱ μ N).1 hN with hNcont
  have hAdd : IsContinuousLocalMartingale ℱ μ (fun t ω ↦ M t ω + N t ω) := by
    refine ⟨hMcont.local_martingale.add hNcont.local_martingale, ?_⟩
    intro ω
    exact (hMcont.continuous ω).add (hNcont.continuous ω)
  have hSub : IsContinuousLocalMartingale ℱ μ (fun t ω ↦ M t ω - N t ω) := by
    refine ⟨hMcont.local_martingale.sub hNcont.local_martingale, ?_⟩
    intro ω
    exact (hMcont.continuous ω).sub (hNcont.continuous ω)
  rcases existsUnique_continuousSquareVariationProcess (ℱ := ℱ) (μ := μ) hAdd with
    ⟨Aadd, hAadd, _⟩
  rcases existsUnique_continuousSquareVariationProcess (ℱ := ℱ) (μ := μ) hSub with
    ⟨Asub, hAsub, _⟩
  let A : NNReal → Ω → ℝ := fun t ω ↦ (1 / 4 : ℝ) * (Aadd t ω - Asub t ω)
  have hA :
      IsContinuousQuadraticCovariationProcess ℱ μ M N A :=
    isContinuousQuadraticCovariationProcess_polarization hAadd hAsub
  refine ⟨A, hA, ?_⟩
  intro A' hA'
  have hMulSubA :
      IsContinuousLocalMartingale ℱ μ (fun t ω ↦ M t ω * N t ω - A t ω) := by
    refine ⟨hA.local_martingale_mul_sub, ?_⟩
    intro ω
    exact (hMcont.continuous ω).mul (hNcont.continuous ω) |>.sub (hA.continuous ω)
  have hMulSubA' :
      IsContinuousLocalMartingale ℱ μ (fun t ω ↦ M t ω * N t ω - A' t ω) := by
    refine ⟨hA'.local_martingale_mul_sub, ?_⟩
    intro ω
    exact (hMcont.continuous ω).mul (hNcont.continuous ω) |>.sub (hA'.continuous ω)
  have hDiff :
      IsContinuousLocalMartingale ℱ μ (fun t ω ↦ A t ω - A' t ω) := by
    -- Proof comment: subtract the two continuous local martingale realizations of `MN - A`.
    convert hMulSubA'.sub hMulSubA using 1
    funext t ω
    ring
  have hDiff0 : (fun t ω ↦ A t ω - A' t ω) 0 = 0 := by
    funext ω
    simp [A, hA.zero, hA'.zero]
  have hDiffFv :
      ∀ᵐ ω ∂μ,
        LocallyBoundedVariationOn
          (⟨fun t ↦ (A t ω - A' t ω), hDiff.continuous ω⟩ : PathSpace) Set.univ := by
    filter_upwards [hA.locally_finite_variation, hA'.locally_finite_variation] with ω hωA hωA'
    let GA : PathSpace := ⟨fun t ↦ A t ω, hA.continuous ω⟩
    let GA' : PathSpace := ⟨fun t ↦ A' t ω, hA'.continuous ω⟩
    have hGA : GA ∈ continuousVariationSubmodule := by
      exact (mem_continuousVariationSubmodule_iff GA).2 hωA
    have hGA' : GA' ∈ continuousVariationSubmodule := by
      exact (mem_continuousVariationSubmodule_iff GA').2 hωA'
    have hSubMem : GA - GA' ∈ continuousVariationSubmodule := by
      exact Submodule.sub_mem continuousVariationSubmodule hGA hGA'
    simpa [GA, GA'] using (mem_continuousVariationSubmodule_iff (GA - GA')).1 hSubMem
  exact areIndistinguishable_of_sub_zero <|
    areIndistinguishable_zero_of_continuousLocalMartingale_zero_initial_ae_locallyFiniteVariation
      hDiff hDiff0 hDiffFv

-- Proof sketch: write the mixed partition sums as the polarization combination of the quadratic
-- partition sums for `M + N` and `M - N`, invoke Theorem 21.70 (3) for those two square brackets,
-- and pass to the limit in probability through addition, subtraction, and scalar multiplication.
/-- Any continuous quadratic-covariation process `A` is the limit in probability of the mixed
partition sums along every admissible sequence of partitions, matching formula `(21.60)`. -/
theorem tendstoInMeasure_partitionQuadraticCovariationApproximationUpTo
    {M N A : NNReal → Ω → ℝ} (hM : M ∈ Mlocc ℱ μ) (hN : N ∈ Mlocc ℱ μ)
    (hA : IsContinuousQuadraticCovariationProcess ℱ μ M N A) (P : ℕ → ℕ → NNReal)
    [IsAdmissiblePartitionSequence P] (T : NNReal) :
    TendstoInMeasure μ
      (fun n : ℕ ↦ partitionQuadraticCovariationApproximationUpTo M N P T n)
      atTop (A T) := by
  rcases (mem_Mlocc_iff ℱ μ M).1 hM with hMcont
  rcases (mem_Mlocc_iff ℱ μ N).1 hN with hNcont
  have hAdd : IsContinuousLocalMartingale ℱ μ (fun t ω ↦ M t ω + N t ω) := by
    refine ⟨hMcont.local_martingale.add hNcont.local_martingale, ?_⟩
    intro ω
    exact (hMcont.continuous ω).add (hNcont.continuous ω)
  have hSub : IsContinuousLocalMartingale ℱ μ (fun t ω ↦ M t ω - N t ω) := by
    refine ⟨hMcont.local_martingale.sub hNcont.local_martingale, ?_⟩
    intro ω
    exact (hMcont.continuous ω).sub (hNcont.continuous ω)
  rcases existsUnique_continuousSquareVariationProcess (ℱ := ℱ) (μ := μ) hAdd with
    ⟨Aadd, hAadd, _⟩
  rcases existsUnique_continuousSquareVariationProcess (ℱ := ℱ) (μ := μ) hSub with
    ⟨Asub, hAsub, _⟩
  let Apolar : NNReal → Ω → ℝ := fun t ω ↦ (1 / 4 : ℝ) * (Aadd t ω - Asub t ω)
  have hApolar :
      IsContinuousQuadraticCovariationProcess ℱ μ M N Apolar :=
    isContinuousQuadraticCovariationProcess_polarization hAadd hAsub
  have hAddLimit :
      TendstoInMeasure μ
        (fun n : ℕ ↦
          weightedPartitionQuadraticVariationApproximationUpTo (fun _ ↦ (1 : ℝ))
            (fun t ω ↦ M t ω + N t ω) P T n)
        atTop (Aadd T) :=
    tendstoInMeasure_partitionQuadraticVariationApproximationUpTo hAdd hAadd P T
  have hSubLimit :
      TendstoInMeasure μ
        (fun n : ℕ ↦
          weightedPartitionQuadraticVariationApproximationUpTo (fun _ ↦ (1 : ℝ))
            (fun t ω ↦ M t ω - N t ω) P T n)
        atTop (Asub T) :=
    tendstoInMeasure_partitionQuadraticVariationApproximationUpTo hSub hAsub P T
  have hCanonLimit :
      TendstoInMeasure μ (fun n : ℕ ↦ partitionQuadraticCovariationApproximationUpTo M N P T n)
        atTop (Apolar T) := by
    have hPolarLimit :=
      tendstoInMeasure_const_mul (1 / 4 : ℝ) (tendstoInMeasure_sub hAddLimit hSubLimit)
    exact TendstoInMeasure.congr_left
      (fun n ↦ Filter.EventuallyEq.of_eq
        (partitionQuadraticCovariationApproximationUpTo_eq_polarization hMcont.continuous
          hNcont.continuous P T n))
      hPolarLimit
  rcases existsUnique_continuousQuadraticCovariationProcess hM hN with ⟨B, hB, huniq⟩
  have hApolarEq : AreIndistinguishable μ Apolar A := by
    exact areIndistinguishable_trans
      (areIndistinguishable_symm (huniq Apolar hApolar))
      (huniq A hA)
  have hEqT : Apolar T =ᵐ[μ] A T :=
    areModifications_of_areIndistinguishable μ Apolar A hApolarEq T
  -- Proof comment: the canonical polarized witness has the desired limit, and uniqueness up to
  -- indistinguishability identifies its fixed-time value with the given witness `A T`.
  exact TendstoInMeasure.congr_right hEqT hCanonLimit

end ProbabilityTheory
