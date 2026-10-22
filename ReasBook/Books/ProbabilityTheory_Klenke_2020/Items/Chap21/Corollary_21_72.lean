/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Remark_21_59
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Remark_21_68
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Remark_21_71
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_70

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
variable [IsProbabilityMeasure μ]

local notation "TimeFiltration" => Filtration NNReal mΩ
local notation "PathSpace" => C(NNReal, ℝ)
syntax "⟨" term "⟩[" term "]" : term
macro_rules
  | `(⟨$_X⟩[$hX]) => `(continuousSquareVariationProcess $hX)

omit mΩ in
/-- Helper for Corollary 21.72: squaring a bounded process keeps it bounded. -/
lemma isBoundedProcess_sq
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

/-- Helper for Corollary 21.72: the nonnegative rationals are dense in `NNReal`. -/
lemma nnratDense : Dense (Set.range fun q : ℚ≥0 ↦ (q : NNReal)) := by
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

/-- Helper for Corollary 21.72: a continuous path is determined by its values on `ℚ≥0`. -/
lemma continuous_eq_const_of_eqOnNNRat
    {f : NNReal → ℝ} (hf : Continuous f) {c : ℝ}
    (hq : ∀ q : ℚ≥0, f q = c) :
    ∀ t : NNReal, f t = c := by
  -- Proof comment: continuity extends the rational-time identity to the closure of `ℚ≥0`,
  -- namely all of `NNReal`.
  have hEq :
      Set.EqOn f (fun _ : NNReal ↦ c) (Set.range fun q : ℚ≥0 ↦ (q : NNReal)) := by
    intro t ht
    rcases ht with ⟨q, rfl⟩
    simpa using hq q
  intro t
  exact congrFun (Continuous.ext_on nnratDense hf continuous_const hEq) t

omit mΩ in
/-- Helper for Corollary 21.72: two dyadic square-variation realizations of the same continuous
path agree. -/
lemma squareVariation_eq_of_twoRealizations
    {G : PathSpace} {V W : NNReal → ℝ}
    (hV : HasSquareVariationAlong G V)
    (hW : HasSquareVariationAlong G W) :
    V = W := by
  -- Proof comment: both candidates are limits of the same dyadic quadratic-sum sequence.
  funext T
  exact tendsto_nhds_unique (hV T) (hW T)

omit mΩ in
/-- Helper for Corollary 21.72: a continuous path of locally bounded variation has identically
vanishing dyadic square variation. -/
lemma squareVariation_eq_zero_of_locallyBoundedVariationOn
    {G : PathSpace} {V : NNReal → ℝ} (hG : LocallyBoundedVariationOn G Set.univ)
    (hV : HasSquareVariationAlong G V) :
    V = 0 := by
  -- Proof comment: compare the given realization with the canonical zero realization from the
  -- locally-finite-variation square-variation theorem.
  exact squareVariation_eq_of_twoRealizations hV
    (hasSquareVariationAlong_zero_of_locallyBoundedVariationOn hG)

omit mΩ in
/-- Helper for Corollary 21.72: a continuous square-variation path over a locally finite-variation
sample path must vanish identically. -/
lemma continuousSquareVariationPath_eq_zero_of_locallyBoundedVariationOn
    {G V : PathSpace} (hG : LocallyBoundedVariationOn G Set.univ)
    (hV : HasSquareVariationAlong G V) :
    V = 0 := by
  -- Proof comment: this is the path-space specialization of the general vanishing lemma above,
  -- stated in the continuous-path API used by the bracket-path argument below.
  ext t
  exact congrFun
    (squareVariation_eq_zero_of_locallyBoundedVariationOn (G := G) (V := V) hG hV) t

omit [IsProbabilityMeasure μ] in
/-- Helper for Corollary 21.72: convergence of stopping times to `∞` already forces convergence of
the corresponding fixed-time stopped values. -/
lemma ae_tendsto_stoppedProcess_at_time_of_stoppingTimeApproximationUpToInfinity
    {ℱ : TimeFiltration} {M : NNReal → Ω → ℝ} {τSeq : ℕ → Ω → ENNReal}
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

/-- Helper for Corollary 21.72: if the canonical bracket vanishes almost surely, then the square
process is itself a continuous local martingale. -/
lemma isContinuousLocalMartingale_sq_of_ae_squareVariation_eq_zero
    (ℱ : TimeFiltration) {X : NNReal → Ω → ℝ}
    (hX : IsContinuousLocalMartingale ℱ μ X)
    (hzero : ∀ᵐ ω ∂μ, ∀ t : NNReal, (⟨X⟩[hX]) t ω = 0) :
    IsContinuousLocalMartingale ℱ μ (fun t ω ↦ X t ω ^ 2) := by
  let B := continuousSquareVariationProcess hX
  have hBracket : IsContinuousSquareVariationProcess ℱ μ X B :=
    continuousSquareVariationProcess_spec hX
  have hSquareAdapted : Adapted ℱ (fun t ω ↦ X t ω ^ 2) := by
    simpa [pow_two] using hX.adapted.mul hX.adapted
  have hSquareCont : ∀ ω : Ω, Continuous fun t : NNReal ↦ X t ω ^ 2 := by
    intro ω
    simpa [pow_two] using (hX.continuous ω).mul (hX.continuous ω)
  refine ⟨?_, hSquareCont⟩
  -- Proof comment: `X² - ⟨X⟩` is the canonical local martingale from Theorem 21.70, and the
  -- all-time bracket vanishing lets us replace it almost surely by `X²`.
  exact isLocalMartingale_congr_ae_allTimes hBracket.local_martingale_sq_sub.local_martingale
    hSquareAdapted hSquareCont <| by
      filter_upwards [hzero] with ω hω t
      simpa [B] using hω t

/-- Helper for Corollary 21.72: the terminal-initial cross moment collapses to the initial square
moment once both the martingale and its square are genuine martingales. -/
lemma integral_terminal_mul_initial_eq_initial_sq_of_martingale_sq_martingale
    {ℱ : TimeFiltration} {M : NNReal → Ω → ℝ} (hM : Martingale M ℱ μ)
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

/-- Helper for Corollary 21.72: once a martingale and its square are both martingales, every
fixed-time value agrees almost surely with the initial value. -/
lemma ae_eq_initial_at_time_of_martingale_sq_martingale
    {ℱ : TimeFiltration} {M : NNReal → Ω → ℝ} (hM : Martingale M ℱ μ)
    (hMsq : Martingale (fun t ω ↦ M t ω ^ 2) ℱ μ) (t : NNReal) :
    M t =ᵐ[μ] M 0 := by
  -- Route correction: replace the old variance-based closure by a direct
  -- `∫ (M_t - M_0)^2 = 0` argument, which is shorter and avoids the redundant boundedness
  -- hypothesis.
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
      _ = 0 := by nlinarith [hCrossEq, hSqEq]
  have hYsqInt : Integrable (fun ω ↦ Y ω ^ 2) μ := hYLp.integrable_sq
  have hYsqNonneg : 0 ≤ᵐ[μ] fun ω ↦ Y ω ^ 2 := Filter.Eventually.of_forall fun ω ↦ sq_nonneg _
  filter_upwards [(integral_eq_zero_iff_of_nonneg_ae hYsqNonneg hYsqInt).1 hSecondMomentZero]
    with ω hω
  -- Proof comment: a nonnegative square can integrate to zero only when the increment itself
  -- vanishes almost surely.
  exact sub_eq_zero.mp <| by
    simpa [Y] using (sq_eq_zero_iff.mp hω)

/-- Helper for Corollary 21.72: a bounded stopped process inherits the martingale property for its
square from the square local martingale owner. -/
lemma martingale_sq_of_bounded_stoppedProcess
    {ℱ : TimeFiltration} {M : NNReal → Ω → ℝ}
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

/-- Helper for Corollary 21.72: bracket-zero continuous local martingales are constant at a fixed
time almost surely. -/
lemma ae_eq_initial_at_time_of_ae_squareVariation_eq_zero
    (ℱ : TimeFiltration) {X : NNReal → Ω → ℝ}
    (hX : IsContinuousLocalMartingale ℱ μ X)
    (hzero : ∀ᵐ ω ∂μ, ∀ t : NNReal, (⟨X⟩[hX]) t ω = 0)
    (t : NNReal) :
    X t =ᵐ[μ] X 0 := by
  have hX_upToInfinity : IsLocalMartingaleUpTo ℱ μ (fun _ ↦ (∞ : ENNReal)) X := by
    exact (isLocalMartingaleUpTo_iff ℱ μ (fun _ ↦ (∞ : ENNReal)) X).2
      ((isLocalMartingale_iff ℱ μ X).1 hX.local_martingale)
  rcases
      (isLocalMartingaleUpTo_iff_exists_bounded_stopped_martingale_sequence
        (ℱ := ℱ) (μ := μ) (τ := fun _ ↦ (∞ : ENNReal)) (M := X) hX.adapted hX.continuous).1
        hX_upToInfinity with
    ⟨τSeq, hApprox, hStopped⟩
  let hSquareLocal :=
    isContinuousLocalMartingale_sq_of_ae_squareVariation_eq_zero (ℱ := ℱ) (μ := μ) hX hzero
  have hAllStoppedEq :
      ∀ᵐ ω ∂μ, ∀ n : ℕ, stoppedProcess X (τSeq n) t ω = X 0 ω := by
    rw [ae_all_iff]
    intro n
    have hSqMart :
        Martingale (fun u ω ↦ (stoppedProcess X (τSeq n) u ω) ^ 2) ℱ μ :=
      martingale_sq_of_bounded_stoppedProcess (ℱ := ℱ) (μ := μ) hSquareLocal
        (hApprox.2.1 n) (hStopped n).2
    have hEqStopped :
        stoppedProcess X (τSeq n) t =ᵐ[μ] stoppedProcess X (τSeq n) 0 :=
      ae_eq_initial_at_time_of_martingale_sq_martingale (hStopped n).1 hSqMart t
    -- Proof comment: time `0` is never affected by stopping, so the initial value is `X 0`.
    exact hEqStopped.trans <| Filter.Eventually.of_forall fun ω ↦ by
      simp [stoppedProcess]
  have hTendsto :
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ stoppedProcess X (τSeq n) t ω) atTop (nhds (X t ω)) :=
    ae_tendsto_stoppedProcess_at_time_of_stoppingTimeApproximationUpToInfinity hApprox t
  filter_upwards [hAllStoppedEq, hTendsto] with ω hωEq hωTendsto
  have hEventuallyEq :
      (fun n ↦ stoppedProcess X (τSeq n) t ω) =ᶠ[atTop] fun _ ↦ X 0 ω :=
    Filter.Eventually.of_forall hωEq
  -- Proof comment: the stopped values converge to `X t ω`, but they are already constantly
  -- equal to `X 0 ω`, so uniqueness of limits yields the fixed-time identity.
  exact tendsto_nhds_unique hωTendsto (Tendsto.congr' hEventuallyEq.symm tendsto_const_nhds)

-- Proof sketch: apply the continuous local martingale quadratic-variation theorem to the
-- canonical bracket `⟨X⟩[hX]`. If that bracket vanishes almost
-- surely, then `X ^ 2` is a local martingale, and the positivity of `(X_t - X_0)^2` forces all
-- increments to vanish almost surely, simultaneously in `t`.
/-- Corollary 21.72: if a continuous local martingale has almost surely vanishing canonical
square variation, then it is almost surely constant in time. -/
theorem ae_eq_initial_of_ae_squareVariation_eq_zero
    (ℱ : TimeFiltration) {X : NNReal → Ω → ℝ}
    (hX : IsContinuousLocalMartingale ℱ μ X)
    (hzero : ∀ᵐ ω ∂μ, ∀ t : NNReal, (⟨X⟩[hX]) t ω = 0) :
    ∀ᵐ ω ∂μ, ∀ t : NNReal, X t ω = X 0 ω := by
  have hRat :
      ∀ᵐ ω ∂μ, ∀ q : ℚ≥0, X (q : NNReal) ω = X 0 ω := by
    -- Proof comment: gather the fixed-time almost-sure equalities over the countable dense set
    -- `ℚ≥0` into one full-measure event.
    rw [ae_all_iff]
    intro q
    simpa using ae_eq_initial_at_time_of_ae_squareVariation_eq_zero ℱ hX hzero (q : NNReal)
  filter_upwards [hRat] with ω hω t
  -- Proof comment: outside the null set from the rational-time step, continuity extends the
  -- constant value from `ℚ≥0` to every nonnegative real time.
  exact continuous_eq_const_of_eqOnNNRat (hX.continuous ω) (fun q ↦ hω q) t

/-- If almost every sample path of a continuous local martingale has locally finite variation, then
its canonical bracket vanishes almost surely. This is the `bridge/view` step from the source-facing
dyadic square-variation owner to the canonical bracket owner. -/
theorem ae_continuousSquareVariationProcess_eq_zero_of_ae_locallyFiniteVariation
    (ℱ : TimeFiltration) {X : NNReal → Ω → ℝ}
    (hX : IsContinuousLocalMartingale ℱ μ X)
    (hfv :
      ∀ᵐ ω ∂μ,
        LocallyBoundedVariationOn
          (⟨fun t ↦ X t ω, hX.continuous ω⟩ : PathSpace) Set.univ) :
    ∀ᵐ ω ∂μ, ∀ t : NNReal, (⟨X⟩[hX]) t ω = 0 := by
  let B := continuousSquareVariationProcess hX
  have hBracket : IsContinuousSquareVariationProcess ℱ μ X B :=
    continuousSquareVariationProcess_spec hX
  filter_upwards
    [ae_hasSquareVariationAlong_continuousSquareVariationProcess hX hBracket, hfv]
    with ω hsq hvar
  let bracketPath : PathSpace := ⟨fun t ↦ B t ω, hBracket.continuous ω⟩
  have hsq' :
      HasSquareVariationAlong
        (⟨fun t ↦ X t ω, hX.continuous ω⟩ : PathSpace) bracketPath := by
    -- Proof comment: repackage the canonical bracket path as a continuous path to match the
    -- square-variation API for paths of locally finite variation.
    simpa [bracketPath] using hsq
  have hzero : bracketPath = 0 := by
    -- Proof comment: once the bracket is viewed as a pathwise square variation of a
    -- locally-finite-variation sample path, the path-space vanishing lemma applies directly.
    exact continuousSquareVariationPath_eq_zero_of_locallyBoundedVariationOn hvar hsq'
  intro t
  simpa [bracketPath, B] using congrArg (fun f : PathSpace ↦ f t) hzero

-- Proof sketch: first use the owner bridge
-- `ae_hasSquareVariationAlong_continuousSquareVariationProcess` together with Remark 21.59 to
-- show that the canonical bracket vanishes almost surely. Then invoke
-- `ae_eq_initial_of_ae_squareVariation_eq_zero`.
/-- If the sample paths of a continuous local martingale have locally finite variation almost
surely, then the martingale is almost surely constant in time. -/
theorem ae_eq_initial_of_ae_locallyFiniteVariation
    (ℱ : TimeFiltration) {X : NNReal → Ω → ℝ}
    (hX : IsContinuousLocalMartingale ℱ μ X)
    (hfv :
      ∀ᵐ ω ∂μ,
        LocallyBoundedVariationOn
          (⟨fun t ↦ X t ω, hX.continuous ω⟩ : PathSpace) Set.univ) :
    ∀ᵐ ω ∂μ, ∀ t : NNReal, X t ω = X 0 ω :=
  ae_eq_initial_of_ae_squareVariation_eq_zero ℱ hX
    (ae_continuousSquareVariationProcess_eq_zero_of_ae_locallyFiniteVariation ℱ hX hfv)

end ProbabilityTheory
