/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Example_9_13
import Books.ProbabilityTheory_Klenke_2020.Items.Chap10.Definition_10_3
import Books.ProbabilityTheory_Klenke_2020.Items.Chap10.Theorem_10_4

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}

noncomputable section

section

variable {Y : ℕ → Ω → ℝ}
variable (hY_meas : ∀ n, Measurable (Y n))

local notation "S" => partialSum Y

private theorem partialSumStronglyMeasurable
    (hY_meas : ∀ n, Measurable (Y n)) (n : ℕ) : StronglyMeasurable (S n) :=
  (partialSum_measurable Y hY_meas n).stronglyMeasurable

local notation "ℱY" =>
  Filtration.natural S (partialSumStronglyMeasurable hY_meas)

/-- Helper for Example 10.6: consecutive partial sums differ by the next increment. -/
private lemma partialSum_succ_sub (n : ℕ) (ω : Ω) :
    S (n + 1) ω - S n ω = Y n ω := by
  -- Rewrite the tail between consecutive partial sums as the singleton `Ico` block.
  simpa using partialSum_sub_eq_sum_Ico Y (Nat.le_succ n) ω

/-- Helper for Example 10.6: the time-`0` natural filtration of the partial sums is trivial. -/
private lemma partialSumNaturalFiltration_zero :
    ℱY 0 = ⊥ := by
  -- Replace the natural filtration by the equivalent generated filtration and collapse the
  -- constant zeroth partial sum.
  rw [← generatedFiltration_eq_natural S (partialSumStronglyMeasurable hY_meas)]
  rw [generatedFiltration_apply]
  change (⨆ j ≤ 0, MeasurableSpace.comap (S j) (borel ℝ)) = ⊥
  have hconst : MeasurableSpace.comap (S 0) (borel ℝ) = ⊥ := by
    change MeasurableSpace.comap (fun _ : Ω ↦ (0 : ℝ)) (borel ℝ) = ⊥
    exact MeasurableSpace.comap_const 0
  simpa [hconst]

/-- Helper for Example 10.6: after discarding the trivial zeroth coordinate, the natural
filtration of the partial sums agrees with the natural filtration of the increments. -/
private lemma partialSumNaturalFiltration_succ_eq_incrementNatural (n : ℕ) :
    ℱY (n + 1) = Filtration.natural Y (fun k ↦ (hY_meas k).stronglyMeasurable) n := by
  let T : ℕ → Ω → ℝ := fun m ↦ partialSum Y (m + 1)
  have hT_meas : ∀ m, Measurable (T m) := fun m ↦ partialSum_measurable Y hY_meas (m + 1)
  calc
    ℱY (n + 1) = generatedFiltration S (fun m ↦ partialSum_measurable Y hY_meas m) (n + 1) := by
      rw [← generatedFiltration_eq_natural S (partialSumStronglyMeasurable hY_meas)]
    _ = generatedFiltration T hT_meas n := by
      rw [generatedFiltration_apply, generatedFiltration_apply]
      change (⨆ j ≤ n + 1, MeasurableSpace.comap (S j) (borel ℝ)) =
        ⨆ j ≤ n, MeasurableSpace.comap (T j) (borel ℝ)
      refine le_antisymm ?_ ?_
      · refine iSup₂_le ?_
        intro j hj
        cases j with
        | zero =>
            have hconst : MeasurableSpace.comap (S 0) (borel ℝ) = ⊥ := by
              change MeasurableSpace.comap (fun _ : Ω ↦ (0 : ℝ)) (borel ℝ) = ⊥
              exact MeasurableSpace.comap_const 0
            rw [hconst]
            exact bot_le
        | succ k =>
            have hk : k ≤ n := Nat.succ_le_succ_iff.mp hj
            simpa [T] using
              (le_iSup_of_le k <| le_iSup_of_le hk le_rfl :
                MeasurableSpace.comap (T k) (borel ℝ) ≤
                  ⨆ i ≤ n, MeasurableSpace.comap (T i) (borel ℝ))
      · refine iSup₂_le ?_
        intro j hj
        simpa [T] using
          (le_iSup_of_le (j + 1) <| le_iSup_of_le (Nat.succ_le_succ hj) le_rfl :
            MeasurableSpace.comap (S (j + 1)) (borel ℝ) ≤
              ⨆ i ≤ n + 1, MeasurableSpace.comap (S i) (borel ℝ))
    _ = generatedFiltration Y hY_meas n := by
      -- The shifted partial sums generate the same past sigma-algebra as the increments.
      simpa [T] using congrArg (fun ℱ ↦ ℱ n)
        (partialSum_prefix_sigma_eq_increment_prefix_sigma Y hY_meas)
    _ = Filtration.natural Y (fun k ↦ (hY_meas k).stronglyMeasurable) n := by
      rw [generatedFiltration_eq_natural Y (fun k ↦ (hY_meas k).stronglyMeasurable)]

section

variable [IsProbabilityMeasure μ]

/-- Helper for Example 10.6: the conditional expectation of the next partial-sum increment is the
mean of the next independent increment. -/
private lemma condExp_partialSumIncrement_ae_eq_expectation
    (hY_indep : iIndepFun Y μ) :
    ∀ n, μ[S (n + 1) - S n | ℱY n] =ᵐ[μ] fun _ ↦ ∫ ξ, Y n ξ ∂μ := by
  let ℱinc : Filtration ℕ ‹MeasurableSpace Ω› :=
    Filtration.natural Y (fun k ↦ (hY_meas k).stronglyMeasurable)
  intro n
  cases n with
  | zero =>
      have hbot :
          μ[Y 0 | ℱY 0] =ᵐ[μ] fun _ ↦ ∫ ξ, Y 0 ξ ∂μ := by
        -- Conditioning the first increment on the trivial sigma-algebra returns its mean.
        simpa [partialSumNaturalFiltration_zero (Y := Y) (hY_meas := hY_meas)] using
          (EventuallyEq.of_eq (MeasureTheory.condExp_bot (μ := μ) (f := Y 0)) :
            μ[Y 0 | ℱY 0] =ᵐ[μ] fun _ ↦ ∫ ξ, Y 0 ξ ∂μ)
      -- Replace the first partial-sum increment by `Y 0`.
      refine (condExp_congr_ae (Filter.Eventually.of_forall fun ω ↦
        partialSum_succ_sub (Y := Y) 0 ω)).trans hbot
  | succ k =>
      have hnat :
          μ[Y (k + 1) | ℱinc k] =ᵐ[μ] fun _ ↦ ∫ ξ, Y (k + 1) ξ ∂μ := by
        -- The next increment is independent of the past increment filtration.
        simpa [ℱinc] using
          (ProbabilityTheory.iIndepFun.condExp_natural_ae_eq_of_lt
            (f := Y)
            (fun j ↦ (hY_meas j).stronglyMeasurable) hY_indep (Nat.lt_succ_self k))
      -- Transport the independence formula to the natural filtration of the partial sums.
      refine (condExp_congr_ae (Filter.Eventually.of_forall fun ω ↦
        partialSum_succ_sub (Y := Y) (k + 1) ω)).trans ?_
      simpa [ℱinc,
        partialSumNaturalFiltration_succ_eq_incrementNatural (Y := Y) (hY_meas := hY_meas) k] using
        hnat

/-- Helper for Example 10.6: the conditional expectation of the squared next increment is its
deterministic second moment. -/
private lemma condExp_squaredIncrementNatural_ae_eq_secondMoment
    (hY_sq_int : ∀ n, Integrable (fun ω ↦ (Y n ω) ^ 2) μ) (hY_indep : iIndepFun Y μ) :
    ∀ k, μ[(fun ω ↦ (Y (k + 1) ω) ^ 2) |
      Filtration.natural Y (fun j ↦ (hY_meas j).stronglyMeasurable) k] =ᵐ[μ]
        fun _ ↦ ∫ ξ, (Y (k + 1) ξ) ^ 2 ∂μ := by
  intro k
  have hSqMeas :
      StronglyMeasurable[MeasurableSpace.comap (Y (k + 1)) (borel ℝ)]
        (fun ω ↦ (Y (k + 1) ω) ^ 2) := by
    -- The square is measurable with respect to the sigma-algebra generated by the next increment.
    exact ((measurable_id.pow_const 2).comp (comap_measurable (Y (k + 1)))).stronglyMeasurable
  have hIndep :
      Indep (MeasurableSpace.comap (Y (k + 1)) (borel ℝ))
        (Filtration.natural Y (fun j ↦ (hY_meas j).stronglyMeasurable) k) μ :=
    ProbabilityTheory.iIndepFun.indep_comap_natural_of_lt
      (f := Y) (hf := fun j ↦ (hY_meas j).stronglyMeasurable) hY_indep (Nat.lt_succ_self k)
  -- Work on the increment filtration, where the next increment sigma-algebra is independent of
  -- the past, and then observe that the square is measurable with respect to that sigma-algebra.
  simpa using
    (MeasureTheory.condExp_indep_eq
      ((hY_meas (k + 1)).comap_le)
      (Filtration.le _ _)
      hSqMeas hIndep :
        μ[(fun ω ↦ (Y (k + 1) ω) ^ 2) |
          Filtration.natural Y (fun j ↦ (hY_meas j).stronglyMeasurable) k] =ᵐ[μ]
          fun _ ↦ ∫ ξ, (Y (k + 1) ξ) ^ 2 ∂μ)

/-- Helper for Example 10.6: the conditional expectation of the squared next increment is its
deterministic second moment. -/
private lemma condExp_partialSumSqIncrement_ae_eq_secondMoment
    (hY_sq_int : ∀ n, Integrable (fun ω ↦ (Y n ω) ^ 2) μ) (hY_indep : iIndepFun Y μ) :
    ∀ n, μ[(fun ω ↦ (S (n + 1) ω - S n ω) ^ 2) | ℱY n] =ᵐ[μ]
      fun _ ↦ ∫ ξ, (Y n ξ) ^ 2 ∂μ := by
  let ℱinc : Filtration ℕ ‹MeasurableSpace Ω› :=
    Filtration.natural Y (fun k ↦ (hY_meas k).stronglyMeasurable)
  -- Route correction: normalize the squared increment on the increment filtration first, and
  -- only then transport the result back to the partial-sum filtration.
  intro n
  cases n with
  | zero =>
      have hbot :
          μ[(fun ω ↦ (Y 0 ω) ^ 2) | ℱY 0] =ᵐ[μ] fun _ ↦ ∫ ξ, (Y 0 ξ) ^ 2 ∂μ := by
        -- Conditioning on the trivial initial sigma-algebra returns the deterministic mean.
        simpa [partialSumNaturalFiltration_zero (Y := Y) (hY_meas := hY_meas)] using
          (EventuallyEq.of_eq (MeasureTheory.condExp_bot (μ := μ) (f := fun ω ↦ (Y 0 ω) ^ 2)) :
            μ[(fun ω ↦ (Y 0 ω) ^ 2) | ℱY 0] =ᵐ[μ] fun _ ↦ ∫ ξ, (Y 0 ξ) ^ 2 ∂μ)
      -- Replace the first squared partial-sum increment by the square of `Y 0`.
      refine (condExp_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)).trans hbot
      rw [partialSum_succ_sub (Y := Y) 0 ω]
  | succ k =>
      have hnat :
          μ[(fun ω ↦ (Y (k + 1) ω) ^ 2) | ℱinc k] =ᵐ[μ]
            fun _ ↦ ∫ ξ, (Y (k + 1) ξ) ^ 2 ∂μ :=
        condExp_squaredIncrementNatural_ae_eq_secondMoment
          (Y := Y) (μ := μ) (hY_meas := hY_meas) hY_sq_int hY_indep k
      have hsqEq :
          (fun ω ↦ (S (k + 2) ω - S (k + 1) ω) ^ 2) = fun ω ↦ (Y (k + 1) ω) ^ 2 := by
        funext ω
        rw [partialSum_succ_sub (Y := Y) (k + 1) ω]
      -- Rewrite the successor squared increment to the normalized increment-side expression.
      refine (condExp_congr_ae (Filter.EventuallyEq.of_eq hsqEq)).trans ?_
      -- Transport the normalized formula across the one-step filtration identification.
      simpa [ℱinc,
        partialSumNaturalFiltration_succ_eq_incrementNatural (Y := Y) (hY_meas := hY_meas) k] using
        hnat

-- Proof sketch: reuse the upstream cumulative-sum martingale owner theorem for centered
-- independent increments on a probability space, then transport from the increment filtration to
-- the natural filtration of the partial-sum process.
/-- The martingale part of Example 10.6: if `Y₁, Y₂, …` are independent, centered,
integrable real random variables on a probability space, then the partial-sum process
`Xₙ = Y₁ + ⋯ + Yₙ` is a martingale for its natural filtration. In the canonical `0`-based Lean
indexing, the textbook process is `partialSum Y`. -/
theorem independentCenteredPartialSums_martingale
    (hY_int : ∀ n, Integrable (Y n) μ)
    (hY_mean_zero : ∀ n, μ[Y n] = 0) (hY_indep : iIndepFun Y μ) :
    Martingale S ℱY μ := by
  have hS_adapted : StronglyAdapted ℱY S :=
    Filtration.stronglyAdapted_natural (u := S) (hum := partialSumStronglyMeasurable hY_meas)
  have hS_int : ∀ n, Integrable (S n) μ := by
    intro n
    -- Finite sums of integrable increments remain integrable.
    simpa [partialSum] using
      (integrable_finset_sum (Finset.range n) fun i _ ↦ hY_int i)
  have hcond_zero : ∀ n, μ[S (n + 1) - S n | ℱY n] =ᵐ[μ] 0 := by
    intro n
    -- Centered increments turn the one-step conditional expectation into zero.
    refine (condExp_partialSumIncrement_ae_eq_expectation
      (Y := Y) (μ := μ) (hY_meas := hY_meas) hY_indep n).trans ?_
    exact Filter.Eventually.of_forall fun _ ↦ hY_mean_zero n
  -- The natural-filtration one-step criterion closes the martingale proof.
  exact martingale_of_condExp_sub_eq_zero_nat hS_adapted hS_int hcond_zero

end

variable (hY_meas : ∀ n, Measurable (Y n))

/-- Helper for Example 10.6: square-integrable increments define `L²` random variables. -/
private lemma increment_memLp_two
    (hY_meas' : ∀ n, Measurable (Y n))
    (hY_sq_int : ∀ n, Integrable (fun ω ↦ (Y n ω) ^ 2) μ) (n : ℕ) :
    MemLp (Y n) 2 μ := by
  -- Convert integrability of the square into membership in `L²`.
  exact (memLp_two_iff_integrable_sq
    (hY_meas' n).stronglyMeasurable.aestronglyMeasurable).2 (hY_sq_int n)

/-- Helper for Example 10.6: every finite partial sum belongs to `L²` once the increments are
square integrable. -/
private lemma partialSumMemLpTwoOfSquareIntegrableIncrements
    (hY_meas' : ∀ n, Measurable (Y n))
    (hY_sq_int : ∀ n, Integrable (fun ω ↦ (Y n ω) ^ 2) μ) :
    ∀ n, MemLp (partialSum Y n) 2 μ := by
  intro n
  -- Expand the partial sum and sum the `L²` increment bounds over the finite prefix.
  simpa [partialSum] using
    (memLp_finset_sum (Finset.range n) fun i _ ↦
      increment_memLp_two (Y := Y) (μ := μ) hY_meas' hY_sq_int i)

-- Proof sketch: deduce square integrability of each finite partial sum from the square
-- integrability of the increments and the finite-sum expansion of the process.
/-- The square-integrability part of Example 10.6: if the increments are square integrable,
then each partial sum `Xₙ` is square integrable. -/
theorem independentCenteredPartialSums_squareIntegrable
    (hY_meas : ∀ n, Measurable (Y n))
    (hY_sq_int : ∀ n, Integrable (fun ω ↦ (Y n ω) ^ 2) μ) :
    ∀ n, Integrable (fun ω ↦ (S n ω) ^ 2) μ := by
  intro n
  have hMemLp : MemLp (S n) 2 μ :=
    partialSumMemLpTwoOfSquareIntegrableIncrements
      (Y := Y) (μ := μ) hY_meas hY_sq_int n
  -- Package the finite partial sum in `L²`, then read off integrability of its square.
  exact (memLp_two_iff_integrable_sq
    ((partialSum_measurable Y hY_meas n).stronglyMeasurable.aestronglyMeasurable)).1 hMemLp

local notation "A" => fun n ↦ fun _ ↦ ∑ i ∈ Finset.range n, ∫ ξ, (Y i ξ) ^ 2 ∂μ

-- Proof sketch: the variance-sum process is deterministic, so it is adapted one step in advance
-- and hence predictable for the natural filtration of the partial sums; no independence,
-- centeredness, or integrability hypotheses are needed here.
/-- The predictable compensator part of Example 10.6: the deterministic variance-sum process
`Aₙ = ∑_{i=1}^n E[Yᵢ^2]` is predictable for the natural filtration of the partial sums. -/
theorem independentCenteredPartialSums_deterministicSquareVariation_predictable :
    IsPredictable ℱY A := by
  refine isPredictable_of_measurable_add_one measurable_const fun _ ↦ ?_
  exact measurable_const

section

variable [IsProbabilityMeasure μ]

-- Proof sketch: combine the partial-sum martingale statement with the chapter's square-variation
-- owner abstraction, then identify the predictable compensator of the squared process with the
-- deterministic second-moment sum singled out in the example.
/-- Example 10.6: the deterministic variance-sum process
`Aₙ = ∑_{i=1}^n E[Yᵢ^2]` is the square-variation process of the partial-sum martingale. This is
the canonical chapter-level packaging of parts (3) and (4). -/
theorem independentCenteredPartialSums_deterministicSquareVariation_isSquareVariationProcess
    (hY_sq_int : ∀ n, Integrable (fun ω ↦ (Y n ω) ^ 2) μ)
    (hY_mean_zero : ∀ n, μ[Y n] = 0) (hY_indep : iIndepFun Y μ) :
    IsSquareVariationProcess ℱY μ S A := by
  let M : ℕ → Ω → ℝ := fun n ω ↦ (S n ω) ^ 2 - A n ω
  have hY_int : ∀ n, Integrable (Y n) μ := by
    intro n
    -- Square-integrable increments are integrable, so the partial sums form a martingale.
    exact (increment_memLp_two (Y := Y) (μ := μ) hY_meas hY_sq_int n).integrable (by norm_num)
  have hSmg : Martingale S ℱY μ :=
    independentCenteredPartialSums_martingale
      (Y := Y) (μ := μ) (hY_meas := hY_meas) hY_int hY_mean_zero hY_indep
  have hSsq : ∀ n, Integrable (fun ω ↦ (S n ω) ^ 2) μ :=
    independentCenteredPartialSums_squareIntegrable
      (Y := Y) (μ := μ) hY_meas hY_sq_int
  have hSquareAd : StronglyAdapted ℱY (fun n ω ↦ (S n ω) ^ 2) := by
    intro n
    -- Square the martingale coordinates inside the current sigma-algebra.
    simpa [pow_two] using (hSmg.stronglyMeasurable n).mul (hSmg.stronglyMeasurable n)
  have hAad : StronglyAdapted ℱY A := by
    intro n
    -- Each deterministic variance sum is a constant random variable.
    exact stronglyMeasurable_const
  have hMad : StronglyAdapted ℱY M := by
    -- The compensated square process is adapted by stability under subtraction.
    simpa [M] using hSquareAd.sub hAad
  have hMint : ∀ n, Integrable (M n) μ := by
    intro n
    have hAint : Integrable (A n) μ := by
      -- Deterministic variance sums are integrable as constant functions.
      change Integrable (fun _ : Ω ↦ ∑ i ∈ Finset.range n, ∫ ξ, (Y i ξ) ^ 2 ∂μ) μ
      exact integrable_const _
    exact (hSsq n).sub hAint
  have hCondZero : ∀ n, μ[M (n + 1) - M n | ℱY n] =ᵐ[μ] 0 := by
    intro n
    let aStep : Ω → ℝ := fun _ ↦
      (∑ i ∈ Finset.range (n + 1), ∫ ξ, (Y i ξ) ^ 2 ∂μ) -
        ∑ i ∈ Finset.range n, ∫ ξ, (Y i ξ) ^ 2 ∂μ
    have hAdiff : aStep = fun _ ↦ ∫ ξ, (Y n ξ) ^ 2 ∂μ := by
      -- The deterministic compensator gains exactly the next second moment.
      funext ω
      simp [aStep, Finset.sum_range_succ]
    have hSqDiffInt : Integrable (fun ω ↦ (S (n + 1) ω) ^ 2 - (S n ω) ^ 2) μ :=
      (hSsq (n + 1)).sub (hSsq n)
    have hAdiffInt : Integrable aStep μ := by
      rw [hAdiff]
      exact integrable_const _
    have hAdiffMeas : StronglyMeasurable[ℱY n] aStep := by
      rw [hAdiff]
      exact stronglyMeasurable_const
    -- Route correction: first isolate the square-process increment, then replace its
    -- conditional expectation by the deterministic second moment of the next increment.
    calc
      μ[M (n + 1) - M n | ℱY n] =ᵐ[μ]
          μ[(fun ω ↦ ((S (n + 1) ω) ^ 2 - (S n ω) ^ 2) - aStep ω) | ℱY n] := by
            refine condExp_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
            change
              ((S (n + 1) ω) ^ 2 - (∑ i ∈ Finset.range (n + 1), ∫ ξ, (Y i ξ) ^ 2 ∂μ)) -
                  ((S n ω) ^ 2 - (∑ i ∈ Finset.range n, ∫ ξ, (Y i ξ) ^ 2 ∂μ)) =
                ((S (n + 1) ω) ^ 2 - (S n ω) ^ 2) - aStep ω
            rw [show aStep ω =
              (∑ i ∈ Finset.range (n + 1), ∫ ξ, (Y i ξ) ^ 2 ∂μ) -
                ∑ i ∈ Finset.range n, ∫ ξ, (Y i ξ) ^ 2 ∂μ by rfl]
            ring
      _ =ᵐ[μ] μ[(fun ω ↦ (S (n + 1) ω) ^ 2 - (S n ω) ^ 2) | ℱY n] -
            μ[aStep | ℱY n] := by
            exact condExp_sub hSqDiffInt hAdiffInt (ℱY n)
      _ =ᵐ[μ] μ[(fun ω ↦ (S (n + 1) ω - S n ω) ^ 2) | ℱY n] -
            μ[aStep | ℱY n] := by
            exact (condExp_sqMomentDiff_eq_condExp_sqIncrement hSmg hSsq n).sub
              Filter.EventuallyEq.rfl
      _ =ᵐ[μ] (fun _ ↦ ∫ ξ, (Y n ξ) ^ 2 ∂μ) - μ[aStep | ℱY n] := by
            exact (condExp_partialSumSqIncrement_ae_eq_secondMoment
              (Y := Y) (μ := μ) (hY_meas := hY_meas) hY_sq_int hY_indep n).sub
              Filter.EventuallyEq.rfl
      _ =ᵐ[μ] (fun _ ↦ ∫ ξ, (Y n ξ) ^ 2 ∂μ) - fun _ ↦ ∫ ξ, (Y n ξ) ^ 2 ∂μ := by
            have hCondAdiff :
                μ[aStep | ℱY n] = fun _ ↦ ∫ ξ, (Y n ξ) ^ 2 ∂μ := by
              rw [MeasureTheory.condExp_of_stronglyMeasurable
                ((Filtration.natural S (partialSumStronglyMeasurable hY_meas)).le n)
                hAdiffMeas hAdiffInt, hAdiff]
            refine Filter.EventuallyEq.rfl.sub (Filter.EventuallyEq.of_eq hCondAdiff)
      _ =ᵐ[μ] 0 := by
            simp
  -- Assemble the deterministic square variation from its initial value, predictability, and
  -- compensated-square martingale property.
  refine ⟨?_, independentCenteredPartialSums_deterministicSquareVariation_predictable
    (Y := Y) (μ := μ) hY_meas, martingale_of_condExp_sub_eq_zero_nat hMad hMint hCondZero⟩
  ext ω
  change (∑ i ∈ Finset.range 0, ∫ ξ, (Y i ξ) ^ 2 ∂μ) = 0
  simp

-- Proof sketch: read off the compensated-square martingale from the square-variation owner
-- statement for the deterministic compensator `A`.
/-- The compensated-square martingale part of Example 10.6: subtracting the deterministic
variance-sum process from `Xₙ^2` yields a martingale. This is the compensated squared process
from the textbook example. -/
theorem independentCenteredPartialSums_squareMinusDeterministicSquareVariation_martingale
    (hY_sq_int : ∀ n, Integrable (fun ω ↦ (Y n ω) ^ 2) μ)
    (hY_mean_zero : ∀ n, μ[Y n] = 0) (hY_indep : iIndepFun Y μ) :
    Martingale (fun n ω ↦ (S n ω) ^ 2 - A n ω) ℱY μ :=
  (independentCenteredPartialSums_deterministicSquareVariation_isSquareVariationProcess
      hY_meas hY_sq_int hY_mean_zero hY_indep).martingale_sq_sub

-- Proof sketch: apply the uniqueness companion for the square-variation owner object to identify
-- the canonical square variation `⟨S⟩[ℱY, μ]` with the deterministic process `A`; this is the
-- source-facing formula for the predictable part of the squared partial sums.
/-- At each fixed time, the canonical square variation `⟨S⟩[ℱY, μ]` of the squared partial-sum
martingale agrees almost everywhere with the deterministic sum of the second moments of the
increments. This is the explicit `Aₙ` formula singled out in the textbook example. -/
theorem independentCenteredPartialSums_squareVariation_ae_eq_deterministicSquareVariation
    (hY_sq_int : ∀ n, Integrable (fun ω ↦ (Y n ω) ^ 2) μ)
    (hY_mean_zero : ∀ n, μ[Y n] = 0) (hY_indep : iIndepFun Y μ) :
    ∀ n, ⟨S⟩[ℱY, μ] n =ᵐ[μ] A n :=
  IsSquareVariationProcess.predictablePart_sq_ae_eq
    (independentCenteredPartialSums_deterministicSquareVariation_isSquareVariationProcess
      hY_meas hY_sq_int hY_mean_zero hY_indep)
    (independentCenteredPartialSums_squareIntegrable hY_meas hY_sq_int)

end

end
