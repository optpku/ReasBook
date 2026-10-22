/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Example_9_13
import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Definition_9_22
import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Remark_9_11
import Books.ProbabilityTheory_Klenke_2020.Items.Chap10.Theorem_10_11

-- Declarations for this item will be appended below by the statement pipeline.

set_option profiler true

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

universe u

noncomputable section

section

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The exponential martingale process attached to the increment sequence `Y` and parameter `θ`,
with the cumulant generating function `cgf (Y 0) μ` playing the role of the textbook map `ψ`. -/
def cramerLundbergExponentialProcess (Y : ℕ → Ω → ℝ) (μ : Measure Ω) (θ : ℝ) : ℕ → Ω → ℝ :=
  fun n ω ↦
    Real.exp
      (θ * partialSum Y n ω - (n : ℝ) * cgf (Y 0) μ θ)

/-- The textbook process `Z_n^θ` is given pointwise by the exponential tilt of the partial sums. -/
@[simp]
theorem cramerLundbergExponentialProcess_apply (Y : ℕ → Ω → ℝ) (μ : Measure Ω) (θ : ℝ)
    (n : ℕ) (ω : Ω) :
    cramerLundbergExponentialProcess Y μ θ n ω =
      Real.exp (θ * partialSum Y n ω - (n : ℝ) * cgf (Y 0) μ θ) :=
  rfl

/-- The normalized exponential increment factors of the Cramér-Lundberg exponential process. -/
def cramerLundbergExponentialFactorProcess (Y : ℕ → Ω → ℝ) (μ : Measure Ω) (θ : ℝ) :
    ℕ → Ω → ℝ
  | 0 => fun _ ↦ 1
  | n + 1 => fun ω ↦ Real.exp (θ * Y n ω - cgf (Y 0) μ θ)

/-- Helper for Exercise 10.2.2: one step of the Cramér-Lundberg exponential process factors into
the current value and the fresh normalized exponential increment. -/
private theorem cramerLundbergExponentialProcess_succ
    (Y : ℕ → Ω → ℝ) (μ : Measure Ω) (θ : ℝ) (n : ℕ) (ω : Ω) :
    cramerLundbergExponentialProcess Y μ θ (n + 1) ω =
      cramerLundbergExponentialProcess Y μ θ n ω *
        Real.exp (θ * Y n ω - cgf (Y 0) μ θ) := by
  let c : ℝ := cgf (Y 0) μ θ
  have hsum : partialSum Y (n + 1) ω = partialSum Y n ω + Y n ω := by
    rw [partialSum_apply, partialSum_apply]
    simpa using (Finset.sum_range_succ (fun i : ℕ ↦ Y i ω) n)
  -- Rewrite the exponent at time `n + 1` into the past contribution plus the fresh increment.
  rw [cramerLundbergExponentialProcess, cramerLundbergExponentialProcess, hsum, Nat.cast_add,
    Nat.cast_one]
  have hsplit :
      θ * (partialSum Y n ω + Y n ω) - ((n : ℝ) + 1) * c =
        (θ * partialSum Y n ω - (n : ℝ) * c) + (θ * Y n ω - c) := by
    ring
  rw [hsplit, Real.exp_add]

/-- The ruin probability for initial capital `k₀`, written on a probability space as the
probability that the shifted partial-sum process ever becomes negative. -/
def ruinProbability (Y : ℕ → Ω → ℝ) (μ : Measure Ω) [IsProbabilityMeasure μ] (k₀ : ℝ) : ℝ :=
  μ.real {ω | ∃ n : ℕ, partialSum Y n ω + k₀ < 0}

/-- The ruin probability is the real-valued probability of the event that the capital process
crosses below zero. -/
@[simp] theorem ruinProbability_def {μ : Measure Ω} [IsProbabilityMeasure μ]
    (Y : ℕ → Ω → ℝ) (k₀ : ℝ) :
    ruinProbability Y μ k₀ =
      μ.real {ω | ∃ n : ℕ, partialSum Y n ω + k₀ < 0} :=
  rfl

variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {Y : ℕ → Ω → ℝ}
variable (hY_meas : ∀ n, Measurable (Y n))
variable {δ : ℝ}

local notation "S" => partialSum Y

private theorem partialSumStronglyMeasurable
    (hY_meas : ∀ n, Measurable (Y n)) (n : ℕ) : StronglyMeasurable (S n) :=
  (partialSum_measurable Y hY_meas n).stronglyMeasurable

local notation "ℱY" =>
  Filtration.natural S (partialSumStronglyMeasurable hY_meas)

/-- Helper for Exercise 10.2.2: consecutive partial sums differ by the fresh increment. -/
private theorem partialSum_succ_sub (n : ℕ) (ω : Ω) :
    S (n + 1) ω - S n ω = Y n ω := by
  -- Rewrite the difference of neighboring partial sums as the singleton increment block.
  simpa using partialSum_sub_eq_sum_Ico Y (Nat.le_succ n) ω

/-- Helper for Exercise 10.2.2: the initial sigma-algebra of the partial-sum natural filtration is
trivial because `partialSum Y 0` is constant. -/
private theorem partialSumNaturalFiltration_zero :
    ℱY 0 = ⊥ := by
  -- Replace the natural filtration by the generated one and collapse the constant zeroth stage.
  rw [← generatedFiltration_eq_natural S (partialSumStronglyMeasurable hY_meas)]
  rw [generatedFiltration_apply]
  change (⨆ j ≤ 0, MeasurableSpace.comap (S j) (borel ℝ)) = ⊥
  have hconst : MeasurableSpace.comap (S 0) (borel ℝ) = ⊥ := by
    change MeasurableSpace.comap (fun _ : Ω ↦ (0 : ℝ)) (borel ℝ) = ⊥
    exact MeasurableSpace.comap_const 0
  simpa [hconst]

/-- Helper for Exercise 10.2.2: after removing the trivial time-`0` coordinate, the natural
filtration of the partial sums agrees with the natural filtration of the increment sequence. -/
private theorem partialSumNaturalFiltration_succ_eq_incrementNatural (n : ℕ) :
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
      -- The shifted partial sums and the increment prefix carry the same information.
      simpa [T] using congrArg (fun ℱ ↦ ℱ n)
        (partialSum_prefix_sigma_eq_increment_prefix_sigma Y hY_meas)
    _ = Filtration.natural Y (fun k ↦ (hY_meas k).stronglyMeasurable) n := by
      rw [generatedFiltration_eq_natural Y (fun k ↦ (hY_meas k).stronglyMeasurable)]

/-- Helper for Exercise 10.2.2: each stage of the Cramér-Lundberg exponential process is strongly
measurable because it is obtained from the corresponding partial sum by affine transformation and
`Real.exp`. -/
private theorem cramerLundbergExponentialProcessStronglyMeasurable
    (hYmeas : ∀ n, Measurable (Y n)) (θ : ℝ) :
    ∀ n, StronglyMeasurable (cramerLundbergExponentialProcess Y μ θ n) := by
  intro n
  -- The stage `Z_n^θ` is a measurable transform of the partial sum `S n`.
  have hmeas :
      Measurable (fun x : ℝ ↦ Real.exp (θ * x - (n : ℝ) * cgf (Y 0) μ θ)) := by
    fun_prop
  exact (Measurable.comp hmeas (partialSumStronglyMeasurable hYmeas n).measurable).stronglyMeasurable

/-- Helper for Exercise 10.2.2: the exponential moment of the partial sum `partialSum Y n`
factorizes as the exponential of `n * cgf (Y 0) μ a`. -/
private theorem partialSumExpMoment_eq_of_integrable {a : ℝ}
    (hY_meas : ∀ n, Measurable (Y n))
    (hY_indep : iIndepFun Y μ) (hY_ident : ∀ n, IdentDistrib (Y n) (Y 0) μ μ)
    (hY_exp_int : Integrable (fun ω ↦ Real.exp (a * Y 0 ω)) μ)
    (n : ℕ) :
    μ[fun ω ↦ Real.exp (a * partialSum Y n ω)] = Real.exp ((n : ℝ) * cgf (Y 0) μ a) := by
  cases n with
  | zero =>
      -- The empty partial sum is `0`, so the exponential moment is `1 = exp 0`.
      simp [partialSum, ProbabilityTheory.cgf]
  | succ n =>
      have hsum_mgf :
          mgf (partialSum Y (n + 1)) μ a = mgf (Y 0) μ a ^ (Finset.range (n + 1)).card := by
        rw [show partialSum Y (n + 1) = ∑ i ∈ Finset.range (n + 1), Y i by
          ext ω
          simp [partialSum_apply]]
        exact ProbabilityTheory.mgf_sum_of_identDistrib (X := Y) (s := Finset.range (n + 1))
          (j := 0) hY_meas hY_indep
          (by
            intro i hi j hj
            exact (hY_ident i).trans ((hY_ident j).symm))
          (by simp) a
      -- Replace the common mgf by `exp (cgf ...)` and simplify the resulting power.
      calc
        μ[fun ω ↦ Real.exp (a * partialSum Y (n + 1) ω)] = mgf (partialSum Y (n + 1)) μ a := by
          rfl
        _ = mgf (Y 0) μ a ^ (Finset.range (n + 1)).card := hsum_mgf
        _ = (Real.exp (cgf (Y 0) μ a)) ^ (Finset.range (n + 1)).card := by
          rw [ProbabilityTheory.exp_cgf (X := Y 0) (μ := μ) (t := a) (hX := hY_exp_int)]
        _ = Real.exp (((n + 1 : ℕ) : ℝ) * cgf (Y 0) μ a) := by
          rw [Finset.card_range, Real.exp_nat_mul]

/-- Helper for Exercise 10.2.2: each fresh normalized exponential factor has expectation `1`. -/
private theorem cramerLundbergFreshFactor_expectation_one {θ : ℝ}
    (hY_ident : ∀ n, IdentDistrib (Y n) (Y 0) μ μ)
    (hY_exp_int : Integrable (fun ω ↦ Real.exp (θ * Y 0 ω)) μ) :
    ∀ n, μ[fun ω ↦ Real.exp (θ * Y n ω - cgf (Y 0) μ θ)] = 1 := by
  intro n
  calc
    μ[fun ω ↦ Real.exp (θ * Y n ω - cgf (Y 0) μ θ)] =
        Real.exp (-cgf (Y 0) μ θ) * μ[fun ω ↦ Real.exp (θ * Y n ω)] := by
          have hrepr :
              (fun ω ↦ Real.exp (θ * Y n ω - cgf (Y 0) μ θ)) =
                fun ω ↦ Real.exp (-cgf (Y 0) μ θ) * Real.exp (θ * Y n ω) := by
            funext ω
            rw [sub_eq_add_neg, Real.exp_add]
            ring
          rw [hrepr, integral_const_mul]
    _ = Real.exp (-cgf (Y 0) μ θ) * mgf (Y n) μ θ := by
          rfl
    _ = Real.exp (-cgf (Y 0) μ θ) * mgf (Y 0) μ θ := by
          rw [mgf_congr_of_identDistrib (Y n) (Y 0) (hY_ident n) θ]
    _ = 1 := by
          rw [← exp_cgf (X := Y 0) (μ := μ) hY_exp_int, ← Real.exp_add]
          simp

/-- Helper for Exercise 10.2.2: the fresh normalized exponential factor has conditional
expectation `1` with respect to the past partial-sum filtration. -/
private theorem cramerLundbergFreshFactor_condExp_ae_eq_one {θ : ℝ}
    (hY_indep : iIndepFun Y μ) (hY_ident : ∀ n, IdentDistrib (Y n) (Y 0) μ μ)
    (hY_exp_int : Integrable (fun ω ↦ Real.exp (θ * Y 0 ω)) μ) :
    ∀ n, μ[(fun ω ↦ Real.exp (θ * Y n ω - cgf (Y 0) μ θ)) | ℱY n] =ᵐ[μ] fun _ ↦ 1 := by
  let ℱinc : Filtration ℕ ‹MeasurableSpace Ω› :=
    Filtration.natural Y (fun k ↦ (hY_meas k).stronglyMeasurable)
  intro n
  cases n with
  | zero =>
      have hbot :
          μ[(fun ω ↦ Real.exp (θ * Y 0 ω - cgf (Y 0) μ θ)) | ℱY 0] =ᵐ[μ]
            fun _ ↦ μ[fun ω ↦ Real.exp (θ * Y 0 ω - cgf (Y 0) μ θ)] := by
        -- Conditioning the first factor on the trivial initial sigma-algebra returns its mean.
        simpa [partialSumNaturalFiltration_zero (Y := Y) (hY_meas := hY_meas)] using
          (EventuallyEq.of_eq (MeasureTheory.condExp_bot (μ := μ)
            (f := fun ω ↦ Real.exp (θ * Y 0 ω - cgf (Y 0) μ θ))) :
              μ[(fun ω ↦ Real.exp (θ * Y 0 ω - cgf (Y 0) μ θ)) | ℱY 0] =ᵐ[μ]
                fun _ ↦ μ[fun ω ↦ Real.exp (θ * Y 0 ω - cgf (Y 0) μ θ)])
      exact hbot.trans <| Filter.Eventually.of_forall fun _ ↦
        cramerLundbergFreshFactor_expectation_one (Y := Y) (μ := μ) hY_ident hY_exp_int 0
  | succ k =>
      have hFactorSm :
          StronglyMeasurable[MeasurableSpace.comap (Y (k + 1)) (borel ℝ)]
            (fun ω ↦ Real.exp (θ * Y (k + 1) ω - cgf (Y 0) μ θ)) := by
        have hmap : Measurable (fun x : ℝ ↦ Real.exp (θ * x - cgf (Y 0) μ θ)) := by
          fun_prop
        exact (hmap.comp (comap_measurable (Y (k + 1)))).stronglyMeasurable
      have hIndep :
          Indep (MeasurableSpace.comap (Y (k + 1)) (borel ℝ)) (ℱinc k) μ :=
        ProbabilityTheory.iIndepFun.indep_comap_natural_of_lt
          (f := Y) (hf := fun j ↦ (hY_meas j).stronglyMeasurable) hY_indep (Nat.lt_succ_self k)
      have hnat :
          μ[(fun ω ↦ Real.exp (θ * Y (k + 1) ω - cgf (Y 0) μ θ)) | ℱinc k] =ᵐ[μ]
            fun _ ↦ μ[fun ω ↦ Real.exp (θ * Y (k + 1) ω - cgf (Y 0) μ θ)] := by
        simpa [ℱinc] using
          (MeasureTheory.condExp_indep_eq
            ((hY_meas (k + 1)).comap_le)
            (Filtration.le _ _) hFactorSm hIndep :
              μ[(fun ω ↦ Real.exp (θ * Y (k + 1) ω - cgf (Y 0) μ θ)) | ℱinc k] =ᵐ[μ]
                fun _ ↦ μ[fun ω ↦ Real.exp (θ * Y (k + 1) ω - cgf (Y 0) μ θ)])
      have hpast :
          μ[(fun ω ↦ Real.exp (θ * Y (k + 1) ω - cgf (Y 0) μ θ)) | ℱY (k + 1)] =ᵐ[μ]
            fun _ ↦ μ[fun ω ↦ Real.exp (θ * Y (k + 1) ω - cgf (Y 0) μ θ)] := by
        simpa [ℱinc,
          partialSumNaturalFiltration_succ_eq_incrementNatural (Y := Y) (hY_meas := hY_meas) k] using
          hnat
      exact hpast.trans <| Filter.Eventually.of_forall fun _ ↦
        cramerLundbergFreshFactor_expectation_one (Y := Y) (μ := μ) hY_ident hY_exp_int (k + 1)

/-- Helper for Exercise 10.2.2: every stage of the exponential process has expectation `1`. -/
private theorem cramerLundbergExponentialProcess_expectation_one {θ : ℝ}
    (hY_meas : ∀ n, Measurable (Y n))
    (hY_indep : iIndepFun Y μ) (hY_ident : ∀ n, IdentDistrib (Y n) (Y 0) μ μ)
    (hY_exp_int : Integrable (fun ω ↦ Real.exp (θ * Y 0 ω)) μ) :
    ∀ n, μ[cramerLundbergExponentialProcess Y μ θ n] = 1 := by
  intro n
  calc
    μ[cramerLundbergExponentialProcess Y μ θ n] =
        Real.exp (-(n : ℝ) * cgf (Y 0) μ θ) *
          μ[fun ω ↦ Real.exp (θ * partialSum Y n ω)] := by
          have hrepr :
              cramerLundbergExponentialProcess Y μ θ n =
                fun ω ↦
                  Real.exp (-(n : ℝ) * cgf (Y 0) μ θ) *
                    Real.exp (θ * partialSum Y n ω) := by
            funext ω
            rw [cramerLundbergExponentialProcess_apply, sub_eq_add_neg, Real.exp_add]
            ring
          rw [hrepr, integral_const_mul]
    _ = Real.exp (-(n : ℝ) * cgf (Y 0) μ θ) *
          Real.exp ((n : ℝ) * cgf (Y 0) μ θ) := by
          rw [partialSumExpMoment_eq_of_integrable (Y := Y) (μ := μ) hY_meas hY_indep hY_ident
            hY_exp_int n]
    _ = 1 := by
          rw [← Real.exp_add]
          congr 1
          ring
          simp

/-- Helper for Exercise 10.2.2: every stage of the Cramér-Lundberg exponential process is
integrable because its expectation is the finite constant `1`. -/
private theorem cramerLundbergExponentialProcess_integrable {θ : ℝ}
    (hY_meas : ∀ n, Measurable (Y n))
    (hY_indep : iIndepFun Y μ) (hY_ident : ∀ n, IdentDistrib (Y n) (Y 0) μ μ)
    (hY_exp_int : Integrable (fun ω ↦ Real.exp (θ * Y 0 ω)) μ) :
    ∀ n, Integrable (cramerLundbergExponentialProcess Y μ θ n) μ := by
  intro n
  -- The explicit expectation formula shows that `∫ Z_n = 1`, which forces integrability.
  exact integrable_of_integral_eq_one <|
    cramerLundbergExponentialProcess_expectation_one (Y := Y) (μ := μ) hY_meas
      hY_indep hY_ident hY_exp_int n

/-- Helper for Exercise 10.2.2: the one-step conditional expectation of the exponential process
returns the previous stage. -/
private theorem cramerLundbergExponentialProcess_condExp_succ {θ : ℝ}
    (hY_indep : iIndepFun Y μ) (hY_ident : ∀ n, IdentDistrib (Y n) (Y 0) μ μ)
    (hY_exp_int : Integrable (fun ω ↦ Real.exp (θ * Y 0 ω)) μ) :
    ∀ n,
      μ[cramerLundbergExponentialProcess Y μ θ (n + 1) | ℱY n] =ᵐ[μ]
        cramerLundbergExponentialProcess Y μ θ n := by
  have hSadapt : StronglyAdapted ℱY S := by
    exact Filtration.stronglyAdapted_natural (partialSumStronglyMeasurable hY_meas)
  intro n
  have hZmeas :
      StronglyMeasurable[ℱY n] (cramerLundbergExponentialProcess Y μ θ n) := by
    have hSn : Measurable[ℱY n] (S n) := (hSadapt n).measurable
    have hmap :
        Measurable (fun x : ℝ ↦ Real.exp (θ * x - (n : ℝ) * cgf (Y 0) μ θ)) := by
      fun_prop
    -- The time-`n` stage is a measurable transform of the time-`n` partial sum.
    simpa [cramerLundbergExponentialProcess_apply] using
      hmap.stronglyMeasurable.comp_measurable hSn
  have hFactorInt :
      Integrable (fun ω ↦ Real.exp (θ * Y n ω - cgf (Y 0) μ θ)) μ := by
    exact integrable_of_integral_eq_one <|
      cramerLundbergFreshFactor_expectation_one (Y := Y) (μ := μ) hY_ident hY_exp_int n
  have hProdInt :
      Integrable
        (fun ω ↦
          Real.exp (θ * Y n ω - cgf (Y 0) μ θ) *
            cramerLundbergExponentialProcess Y μ θ n ω) μ := by
    have hNextInt :
        Integrable (cramerLundbergExponentialProcess Y μ θ (n + 1)) μ :=
      cramerLundbergExponentialProcess_integrable (Y := Y) (μ := μ) hY_meas hY_indep hY_ident
        hY_exp_int (n + 1)
    -- Rewrite the product as the next stage `Z_{n+1}`.
    refine hNextInt.congr ?_
    exact Filter.Eventually.of_forall fun ω ↦ by
      rw [cramerLundbergExponentialProcess_succ, mul_comm]
  have hFactorCond :
      ∀ n, μ[(fun ω ↦ Real.exp (θ * Y n ω - cgf (Y 0) μ θ)) | ℱY n] =ᵐ[μ] fun _ ↦ 1 :=
    cramerLundbergFreshFactor_condExp_ae_eq_one (Y := Y) (μ := μ) (θ := θ) hY_meas hY_indep
      hY_ident hY_exp_int
  -- Pull the past factor `Z_n` out of the conditional expectation and replace the fresh factor by
  -- its conditional mean `1`.
  calc
    μ[cramerLundbergExponentialProcess Y μ θ (n + 1) | ℱY n] =ᵐ[μ]
        μ[(fun ω ↦
            Real.exp (θ * Y n ω - cgf (Y 0) μ θ) *
              cramerLundbergExponentialProcess Y μ θ n ω) | ℱY n] := by
          refine condExp_congr_ae ?_
          exact Filter.Eventually.of_forall fun ω ↦ by
            rw [cramerLundbergExponentialProcess_succ, mul_comm]
    _ =ᵐ[μ]
        μ[(fun ω ↦ Real.exp (θ * Y n ω - cgf (Y 0) μ θ)) | ℱY n] *
          cramerLundbergExponentialProcess Y μ θ n := by
          exact condExp_mul_of_stronglyMeasurable_right hZmeas hProdInt hFactorInt
    _ =ᵐ[μ]
        (fun _ ↦ (1 : ℝ)) * cramerLundbergExponentialProcess Y μ θ n := by
          exact (hFactorCond n).mul Filter.EventuallyEq.rfl
    _ =ᵐ[μ] cramerLundbergExponentialProcess Y μ θ n := by
          exact Filter.Eventually.of_forall fun _ ↦ by simp

/-- Exercise 10.2.2 (1): for every parameter `θ` in the exponential-moment interval, the process
`Z^θ` built from the partial sums is a martingale with respect to the natural filtration of the
partial-sum process. -/
-- Proof sketch: rewrite `Z_{n + 1}` as `Z_n` times the fresh normalized exponential increment,
-- compute the conditional expectation of that increment against the past partial-sum filtration,
-- and then apply the discrete-time one-step martingale criterion.
theorem cramerLundbergExponentialProcess_martingale {θ : ℝ}
    (hY_indep : iIndepFun Y μ) (hY_ident : ∀ n, IdentDistrib (Y n) (Y 0) μ μ)
    (hY_exp_int : Integrable (fun ω ↦ Real.exp (θ * Y 0 ω)) μ)
    (hθ : θ ∈ Set.Ioo (-δ) δ) :
    Martingale (cramerLundbergExponentialProcess Y μ θ) ℱY μ := by
  have hSadapt : StronglyAdapted ℱY S := by
    exact Filtration.stronglyAdapted_natural (partialSumStronglyMeasurable hY_meas)
  have hZadapt : StronglyAdapted ℱY (cramerLundbergExponentialProcess Y μ θ) := by
    intro n
    have hSn : Measurable[ℱY n] (S n) := (hSadapt n).measurable
    have hmap :
        Measurable (fun x : ℝ ↦ Real.exp (θ * x - (n : ℝ) * cgf (Y 0) μ θ)) := by
      fun_prop
    -- Each stage `Z_n` is a measurable transform of the time-`n` partial sum.
    simpa [cramerLundbergExponentialProcess_apply] using
      hmap.stronglyMeasurable.comp_measurable hSn
  have hZint :
      ∀ n, Integrable (cramerLundbergExponentialProcess Y μ θ n) μ :=
    cramerLundbergExponentialProcess_integrable (Y := Y) (μ := μ) hY_meas
      hY_indep hY_ident hY_exp_int
  have hCondStep :
      ∀ n,
        μ[cramerLundbergExponentialProcess Y μ θ (n + 1) | ℱY n] =ᵐ[μ]
          cramerLundbergExponentialProcess Y μ θ n :=
    cramerLundbergExponentialProcess_condExp_succ (Y := Y) (μ := μ) (θ := θ) hY_meas hY_indep
      hY_ident hY_exp_int
  -- Apply the one-step martingale criterion once the conditional expectation bridge is packaged.
  refine martingale_nat hZadapt hZint ?_
  intro n
  simpa using (hCondStep n).symm

/-- Helper for Exercise 10.2.2: if every exponential moment on `(-δ,δ)` is finite, then every
point of that interval belongs to the interior of `integrableExpSet (Y 0) μ`. -/
private theorem memInterior_integrableExpSet_of_memInterval
    (hY_exp_int : ∀ θ ∈ Set.Ioo (-δ) δ, Integrable (fun ω ↦ Real.exp (θ * Y 0 ω)) μ)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo (-δ) δ) :
    θ ∈ interior (integrableExpSet (Y 0) μ) := by
  -- The open interval itself is contained in the exponential-integrability set.
  rw [mem_interior_iff_mem_nhds]
  refine Filter.mem_of_superset (isOpen_Ioo.mem_nhds hθ) ?_
  intro x hx
  exact hY_exp_int x hx

/-- Exercise 10.2.2 (2): the cumulant generating function of the increment law is strictly convex
on the interval where the exponential moments are finite. -/
-- Proof sketch: apply the strict convexity of the logarithmic moment-generating function on an
-- interval of exponential integrability, and use that the increment law is not almost surely
-- constant to rule out the affine case.
theorem cgf_strictConvexOn_increment_interval
    (hY_not_ae_const : ¬ ∃ c : ℝ, Y 0 =ᵐ[μ] fun _ ↦ c)
    (hY_exp_int : ∀ θ ∈ Set.Ioo (-δ) δ, Integrable (fun ω ↦ Real.exp (θ * Y 0 ω)) μ) :
    StrictConvexOn ℝ (Set.Ioo (-δ) δ) (cgf (Y 0) μ) := by
  -- Route correction: prove strict convexity from positivity of the second derivative.
  have hcont : ContinuousOn (cgf (Y 0) μ) (Set.Ioo (-δ) δ) := by
    refine (ProbabilityTheory.analyticOn_cgf (X := Y 0) (μ := μ)).continuousOn.mono ?_
    intro x hx
    exact memInterior_integrableExpSet_of_memInterval (Y := Y) (μ := μ) hY_exp_int hx
  have hderiv2_pos : ∀ x ∈ Set.Ioo (-δ) δ, 0 < (deriv^[2] (cgf (Y 0) μ)) x := by
    intro x hx
    have hx_int :
        x ∈ interior (integrableExpSet (Y 0) μ) :=
      memInterior_integrableExpSet_of_memInterval (Y := Y) (μ := μ) hY_exp_int hx
    have hmgf_pos : 0 < mgf (Y 0) μ x := ProbabilityTheory.mgf_pos (hY_exp_int x hx)
    have hnonneg :
        0 ≤ᵐ[μ] fun ω ↦
          (Y 0 ω - deriv (cgf (Y 0) μ) x) ^ 2 * Real.exp (x * Y 0 ω) := by
      filter_upwards with ω
      positivity
    have hint1 :
        Integrable (fun ω ↦ Y 0 ω * Real.exp (x * Y 0 ω)) μ := by
      convert ProbabilityTheory.integrable_pow_mul_exp_of_mem_interior_integrableExpSet
        (X := Y 0) (μ := μ) hx_int 1 using 1
      simp
    have hint2 :
        Integrable (fun ω ↦ (Y 0 ω) ^ 2 * Real.exp (x * Y 0 ω)) μ := by
      simpa using ProbabilityTheory.integrable_pow_mul_exp_of_mem_interior_integrableExpSet
        (X := Y 0) (μ := μ) hx_int 2
    have hint0 :
        Integrable (fun ω ↦ Real.exp (x * Y 0 ω)) μ := by
      exact interior_subset (s := integrableExpSet (Y 0) μ) hx_int
    have hint :
        Integrable (fun ω ↦
          (Y 0 ω - deriv (cgf (Y 0) μ) x) ^ 2 * Real.exp (x * Y 0 ω)) μ := by
      -- Expand the square and use the standard exponential-moment integrability lemmas.
      have hterm :
          Integrable (fun ω ↦
            (Y 0 ω) ^ 2 * Real.exp (x * Y 0 ω) -
              (2 * deriv (cgf (Y 0) μ) x) * (Y 0 ω * Real.exp (x * Y 0 ω)) +
              deriv (cgf (Y 0) μ) x ^ 2 * Real.exp (x * Y 0 ω)) μ :=
        (hint2.sub ((hint1.const_mul (2 * deriv (cgf (Y 0) μ) x)))).add
          (hint0.const_mul (deriv (cgf (Y 0) μ) x ^ 2))
      have hexpand :
          (fun ω ↦
            (Y 0 ω - deriv (cgf (Y 0) μ) x) ^ 2 * Real.exp (x * Y 0 ω)) =
          (fun ω ↦
            (Y 0 ω) ^ 2 * Real.exp (x * Y 0 ω) -
              (2 * deriv (cgf (Y 0) μ) x) * (Y 0 ω * Real.exp (x * Y 0 ω)) +
              deriv (cgf (Y 0) μ) x ^ 2 * Real.exp (x * Y 0 ω)) := by
        funext ω
        ring
      simpa [hexpand] using hterm
    have hneq :
        ∫ ω, (Y 0 ω - deriv (cgf (Y 0) μ) x) ^ 2 * Real.exp (x * Y 0 ω) ∂μ ≠ 0 := by
      intro hzero
      have hae_zero :
          (fun ω ↦
            (Y 0 ω - deriv (cgf (Y 0) μ) x) ^ 2 * Real.exp (x * Y 0 ω)) =ᵐ[μ] 0 :=
        (integral_eq_zero_iff_of_nonneg_ae hnonneg hint).mp hzero
      have hconst :
          Y 0 =ᵐ[μ] fun _ ↦ deriv (cgf (Y 0) μ) x := by
        filter_upwards [hae_zero] with ω hω
        have hsquare :
            (Y 0 ω - deriv (cgf (Y 0) μ) x) ^ 2 = 0 := by
          exact (mul_eq_zero.mp hω).resolve_right (by positivity)
        exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero hsquare)
      exact hY_not_ae_const ⟨deriv (cgf (Y 0) μ) x, hconst⟩
    have hderiv2 :
        iteratedDeriv 2 (cgf (Y 0) μ) x =
          μ[fun ω ↦
            (Y 0 ω - deriv (cgf (Y 0) μ) x) ^ 2 * Real.exp (x * Y 0 ω)] / mgf (Y 0) μ x := by
      exact ProbabilityTheory.iteratedDeriv_two_cgf_eq_integral (X := Y 0) (μ := μ) hx_int
    rw [← iteratedDeriv_eq_iterate, hderiv2]
    exact div_pos (lt_of_le_of_ne (integral_nonneg_of_ae hnonneg) (Ne.symm hneq)) hmgf_pos
  exact strictConvexOn_of_deriv2_pos' (convex_Ioo (-δ) δ) hcont hderiv2_pos

/-- Helper for Exercise 10.2.2: the exponential moment of the partial sum `partialSum Y n`
factorizes exactly as the `n`-th power of the common increment mgf, hence as the exponential of
`n * cgf (Y 0) μ a`. -/
private theorem partialSumExpMoment_eq {a : ℝ}
    (hY_meas : ∀ n, Measurable (Y n))
    (hY_indep : iIndepFun Y μ) (hY_ident : ∀ n, IdentDistrib (Y n) (Y 0) μ μ)
    (hY_exp_int : ∀ ϑ ∈ Set.Ioo (-δ) δ, Integrable (fun ω ↦ Real.exp (ϑ * Y 0 ω)) μ)
    (n : ℕ) (ha : a ∈ Set.Ioo (-δ) δ) :
    μ[fun ω ↦ Real.exp (a * partialSum Y n ω)] = Real.exp ((n : ℝ) * cgf (Y 0) μ a) := by
  -- Reuse the fixed-parameter factorization proved earlier.
  exact partialSumExpMoment_eq_of_integrable (Y := Y) (μ := μ) hY_meas hY_indep hY_ident
    (hY_exp_int a ha) n

/-- Helper for Exercise 10.2.2: strict convexity at the midpoint of `0` and `θ` gives the negative
gap needed for geometric decay of `E[√(Z_n^θ)]`. -/
private theorem cgfHalfGap_neg {θ : ℝ}
    (hY_not_ae_const : ¬ ∃ c : ℝ, Y 0 =ᵐ[μ] fun _ ↦ c)
    (hY_exp_int : ∀ ϑ ∈ Set.Ioo (-δ) δ, Integrable (fun ω ↦ Real.exp (ϑ * Y 0 ω)) μ)
    (hθ : θ ∈ Set.Ioo (-δ) δ) (hθ_ne : θ ≠ 0) :
    cgf (Y 0) μ (θ / 2) - cgf (Y 0) μ θ / 2 < 0 := by
  have hzero : (0 : ℝ) ∈ Set.Ioo (-δ) δ := by
    constructor <;> linarith [hθ.1, hθ.2]
  have hsc := cgf_strictConvexOn_increment_interval (Y := Y) (μ := μ) (δ := δ)
    hY_not_ae_const hY_exp_int
  have hmid_lt :
      cgf (Y 0) μ ((1 / 2 : ℝ) * 0 + (1 / 2 : ℝ) * θ) <
        (1 / 2 : ℝ) * cgf (Y 0) μ 0 + (1 / 2 : ℝ) * cgf (Y 0) μ θ := by
    -- Evaluate strict convexity at the midpoint of `0` and `θ`.
    refine hsc.2 hzero hθ ?_ (by norm_num) (by norm_num) (by ring)
    simpa using hθ_ne.symm
  have hzero_cgf : cgf (Y 0) μ 0 = 0 := by
    simp [ProbabilityTheory.cgf]
  have hmid_eq : ((1 / 2 : ℝ) * 0 + (1 / 2 : ℝ) * θ) = θ / 2 := by
    ring
  have hrhs_eq :
      (1 / 2 : ℝ) * cgf (Y 0) μ 0 + (1 / 2 : ℝ) * cgf (Y 0) μ θ =
        cgf (Y 0) μ θ / 2 := by
    rw [hzero_cgf]
    ring
  rw [hmid_eq, hrhs_eq] at hmid_lt
  linarith

/-- Helper for Exercise 10.2.2: the square-root moment of the Cramér-Lundberg process is an
explicit geometric term whose exponent is the strict-convexity gap from the midpoint estimate. -/
private theorem sqrtCramerLundbergExpectation_eq {θ : ℝ}
    (hY_indep : iIndepFun Y μ) (hY_ident : ∀ n, IdentDistrib (Y n) (Y 0) μ μ)
    (hY_exp_int : ∀ ϑ ∈ Set.Ioo (-δ) δ, Integrable (fun ω ↦ Real.exp (ϑ * Y 0 ω)) μ)
    (hθ : θ ∈ Set.Ioo (-δ) δ) (n : ℕ) :
    μ[fun ω ↦ Real.sqrt (cramerLundbergExponentialProcess Y μ θ n ω)] =
      Real.exp ((n : ℝ) * (cgf (Y 0) μ (θ / 2) - cgf (Y 0) μ θ / 2)) := by
  have hhalf : θ / 2 ∈ Set.Ioo (-δ) δ := by
    constructor <;> linarith [hθ.1, hθ.2]
  have hPartial :
      μ[fun ω ↦ Real.exp ((θ / 2) * partialSum Y n ω)] =
        Real.exp ((n : ℝ) * cgf (Y 0) μ (θ / 2)) := by
    let hY_aemeas : ∀ i, AEMeasurable (Y i) μ := fun i ↦ (hY_ident i).aemeasurable_fst
    cases n with
    | zero =>
        simp [partialSum, ProbabilityTheory.cgf]
    | succ n =>
        have hsum_mgf :
            mgf (partialSum Y (n + 1)) μ (θ / 2) =
              mgf (Y 0) μ (θ / 2) ^ (Finset.range (n + 1)).card := by
          rw [show partialSum Y (n + 1) = ∑ i ∈ Finset.range (n + 1), Y i by
            ext ω
            simp [partialSum_apply]]
          exact ProbabilityTheory.mgf_sum_of_identDistrib₀ (X := Y) (s := Finset.range (n + 1))
            (j := 0) hY_aemeas hY_indep
            (by
              intro i hi j hj
              exact (hY_ident i).trans ((hY_ident j).symm))
            (by simp) (θ / 2)
        calc
          μ[fun ω ↦ Real.exp ((θ / 2) * partialSum Y (n + 1) ω)] =
              mgf (partialSum Y (n + 1)) μ (θ / 2) := by
                rfl
          _ = mgf (Y 0) μ (θ / 2) ^ (Finset.range (n + 1)).card := hsum_mgf
          _ = (Real.exp (cgf (Y 0) μ (θ / 2))) ^ (Finset.range (n + 1)).card := by
                rw [ProbabilityTheory.exp_cgf (X := Y 0) (μ := μ) (t := θ / 2)
                  (hX := hY_exp_int (θ / 2) hhalf)]
          _ = Real.exp (((n + 1 : ℕ) : ℝ) * cgf (Y 0) μ (θ / 2)) := by
                rw [Finset.card_range, Real.exp_nat_mul]
  -- Rewrite `√(Z_n^θ)` as the exponential moment of the partial sum at parameter `θ / 2`.
  calc
    μ[fun ω ↦ Real.sqrt (cramerLundbergExponentialProcess Y μ θ n ω)] =
        μ[fun ω ↦ Real.exp ((θ / 2) * partialSum Y n ω - (n : ℝ) * cgf (Y 0) μ θ / 2)] := by
          congr 1
          ext ω
          change Real.sqrt (Real.exp (θ * partialSum Y n ω - (n : ℝ) * cgf (Y 0) μ θ)) =
            Real.exp ((θ / 2) * partialSum Y n ω - (n : ℝ) * cgf (Y 0) μ θ / 2)
          rw [← Real.exp_half]
          congr 1
          ring
    _ = Real.exp ((n : ℝ) * (cgf (Y 0) μ (θ / 2) - cgf (Y 0) μ θ / 2)) := by
          have hconst_factor :
              μ[fun ω ↦ Real.exp ((θ / 2) * partialSum Y n ω - (n : ℝ) * cgf (Y 0) μ θ / 2)] =
                Real.exp (-(n : ℝ) * cgf (Y 0) μ θ / 2) *
                  μ[fun ω ↦ Real.exp ((θ / 2) * partialSum Y n ω)] := by
            have hrepr :
                (fun ω ↦ Real.exp ((θ / 2) * partialSum Y n ω - (n : ℝ) * cgf (Y 0) μ θ / 2)) =
                  fun ω ↦
                    Real.exp (-(n : ℝ) * cgf (Y 0) μ θ / 2) *
                      Real.exp ((θ / 2) * partialSum Y n ω) := by
              funext ω
              rw [sub_eq_add_neg, Real.exp_add]
              ring
            rw [hrepr, integral_const_mul]
          rw [hconst_factor,
            hPartial,
            ← Real.exp_add]
          congr 1
          ring

/-- Exercise 10.2.2 (3): for every nonzero parameter `θ` in the exponential-moment interval, the
expectations `E[√(Z_n^θ)]` decay to `0`. -/
-- Proof sketch: rewrite `√(Z_n^θ)` as an exponential martingale term with parameter `θ / 2`,
-- compute its expectation using independence and identical distribution, and then use strict
-- convexity of the cumulant generating function to obtain exponential decay for `θ ≠ 0`; the
-- interval condition for `θ / 2` is automatic from `hθ`.
theorem expectation_sqrt_cramerLundbergExponentialProcess_tendsto_zero {θ : ℝ}
    (hY_indep : iIndepFun Y μ) (hY_ident : ∀ n, IdentDistrib (Y n) (Y 0) μ μ)
    (hY_not_ae_const : ¬ ∃ c : ℝ, Y 0 =ᵐ[μ] fun _ ↦ c)
    (hY_exp_int : ∀ ϑ ∈ Set.Ioo (-δ) δ, Integrable (fun ω ↦ Real.exp (ϑ * Y 0 ω)) μ)
    (hθ : θ ∈ Set.Ioo (-δ) δ) (hθ_ne : θ ≠ 0) :
    Filter.Tendsto
      (fun n ↦ μ[fun ω ↦ Real.sqrt (cramerLundbergExponentialProcess Y μ θ n ω)])
      Filter.atTop (nhds 0) := by
  have hgap :
      cgf (Y 0) μ (θ / 2) - cgf (Y 0) μ θ / 2 < 0 :=
    cgfHalfGap_neg (Y := Y) (μ := μ) (δ := δ) hY_not_ae_const hY_exp_int hθ hθ_ne
  have hgeom :
      Filter.Tendsto
        (fun n : ℕ ↦ Real.exp ((n : ℝ) * (cgf (Y 0) μ (θ / 2) - cgf (Y 0) μ θ / 2)))
        Filter.atTop (nhds 0) := by
    -- The strict-convexity gap is negative, so the explicit exponential term decays to `0`.
    refine Real.tendsto_exp_atBot.comp ?_
    exact tendsto_natCast_atTop_atTop.atTop_mul_const_of_neg hgap
  -- Rewrite the square-root expectation sequence into the geometric term from the previous helper.
  refine Filter.Tendsto.congr' ?_ hgeom
  exact Filter.Eventually.of_forall fun n ↦
    (sqrtCramerLundbergExpectation_eq (Y := Y) (μ := μ) (δ := δ) hY_indep hY_ident hY_exp_int
      hθ n).symm

-- Exercise 10.2.2 (4): for every nonzero parameter `θ` in the exponential-moment interval, the
-- process `Z_n^θ` converges almost surely to `0`.
/-- Helper for Exercise 10.2.2: because `Z_n^θ` is nonnegative, taking square roots preserves the
threshold events used in Markov's inequality. -/
private theorem cramerLundbergSqrtThresholdEvent_iff {θ ε : ℝ} (n : ℕ) :
    {ω | Real.sqrt ε ≤ Real.sqrt (cramerLundbergExponentialProcess Y μ θ n ω)} =
      {ω | ε ≤ cramerLundbergExponentialProcess Y μ θ n ω} := by
  ext ω
  have hnonneg : 0 ≤ cramerLundbergExponentialProcess Y μ θ n ω := by
    rw [cramerLundbergExponentialProcess_apply]
    positivity
  simpa using
    (Real.sqrt_le_sqrt_iff hnonneg :
      Real.sqrt ε ≤ Real.sqrt (cramerLundbergExponentialProcess Y μ θ n ω) ↔
        ε ≤ cramerLundbergExponentialProcess Y μ θ n ω)

/-- Helper for Exercise 10.2.2: each fixed threshold event for `Z_n^θ` is controlled by Markov's
 inequality applied to `√(Z_n^θ)`, so the decay of the square-root moments gives a geometric upper
 bound on the event probabilities. -/
private theorem cramerLundbergThresholdProbability_le {θ ε : ℝ}
    (hY_indep : iIndepFun Y μ) (hY_ident : ∀ n, IdentDistrib (Y n) (Y 0) μ μ)
    (hY_exp_int : ∀ ϑ ∈ Set.Ioo (-δ) δ, Integrable (fun ω ↦ Real.exp (ϑ * Y 0 ω)) μ)
    (hθ : θ ∈ Set.Ioo (-δ) δ) (hε : 0 < ε) (n : ℕ) :
    μ.real {ω | ε ≤ cramerLundbergExponentialProcess Y μ θ n ω} ≤
      (Real.sqrt ε)⁻¹ *
        Real.exp ((n : ℝ) * (cgf (Y 0) μ (θ / 2) - cgf (Y 0) μ θ / 2)) := by
  have hsqrt_nonneg :
      0 ≤ᵐ[μ] fun ω ↦ Real.sqrt (cramerLundbergExponentialProcess Y μ θ n ω) := by
    filter_upwards with ω
    positivity
  have hsqrt_int :
      Integrable (fun ω ↦ Real.sqrt (cramerLundbergExponentialProcess Y μ θ n ω)) μ := by
    -- Route correction: package the square-root stage itself as the Markov input instead of
    -- repeatedly unfolding it inside the probability estimate.
    refine Integrable.of_integral_ne_zero ?_
    rw [sqrtCramerLundbergExpectation_eq (Y := Y) (μ := μ) (δ := δ) hY_indep hY_ident
      hY_exp_int hθ n]
    exact Real.exp_ne_zero _
  have hsqrt_pos : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have hmarkov :
      Real.sqrt ε *
          μ.real {ω | ε ≤ cramerLundbergExponentialProcess Y μ θ n ω} ≤
        μ[fun ω ↦ Real.sqrt (cramerLundbergExponentialProcess Y μ θ n ω)] := by
    have hset :
        {ω | Real.sqrt ε ≤ Real.sqrt (cramerLundbergExponentialProcess Y μ θ n ω)} =
          {ω | ε ≤ cramerLundbergExponentialProcess Y μ θ n ω} :=
      cramerLundbergSqrtThresholdEvent_iff (Y := Y) (μ := μ) (n := n) (θ := θ) (ε := ε)
    have hmarkovSqrt :
        Real.sqrt ε *
            μ.real {ω | Real.sqrt ε ≤ Real.sqrt (cramerLundbergExponentialProcess Y μ θ n ω)} ≤
          μ[fun ω ↦ Real.sqrt (cramerLundbergExponentialProcess Y μ θ n ω)] :=
      MeasureTheory.mul_meas_ge_le_integral_of_nonneg (μ := μ) hsqrt_nonneg hsqrt_int
        (Real.sqrt ε)
    -- Replace the threshold event by its square-root form and apply Markov's inequality there.
    rw [hset] at hmarkovSqrt
    exact hmarkovSqrt
  have hdiv :
      μ.real {ω | ε ≤ cramerLundbergExponentialProcess Y μ θ n ω} ≤
        μ[fun ω ↦ Real.sqrt (cramerLundbergExponentialProcess Y μ θ n ω)] / Real.sqrt ε := by
    exact (le_div_iff₀ hsqrt_pos).2 <| by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmarkov
  -- Insert the explicit square-root expectation computed in part (3).
  calc
    μ.real {ω | ε ≤ cramerLundbergExponentialProcess Y μ θ n ω} ≤
        μ[fun ω ↦ Real.sqrt (cramerLundbergExponentialProcess Y μ θ n ω)] / Real.sqrt ε := hdiv
    _ =
        (Real.sqrt ε)⁻¹ *
          Real.exp ((n : ℝ) * (cgf (Y 0) μ (θ / 2) - cgf (Y 0) μ θ / 2)) := by
        rw [sqrtCramerLundbergExpectation_eq (Y := Y) (μ := μ) (δ := δ) hY_indep hY_ident
          hY_exp_int hθ n]
        simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

/-- Helper for Exercise 10.2.2: the threshold events for the exponential martingale are summable
for every fixed positive threshold, because the bound from
`cramerLundbergThresholdProbability_le` is geometric in `n`. -/
private theorem cramerLundbergThresholdEventsSummable {θ ε : ℝ}
    (hY_indep : iIndepFun Y μ) (hY_ident : ∀ n, IdentDistrib (Y n) (Y 0) μ μ)
    (hY_not_ae_const : ¬ ∃ c : ℝ, Y 0 =ᵐ[μ] fun _ ↦ c)
    (hY_exp_int : ∀ ϑ ∈ Set.Ioo (-δ) δ, Integrable (fun ω ↦ Real.exp (ϑ * Y 0 ω)) μ)
    (hθ : θ ∈ Set.Ioo (-δ) δ) (hθ_ne : θ ≠ 0) (hε : 0 < ε) :
    (∑' n : ℕ, μ {ω | ε ≤ cramerLundbergExponentialProcess Y μ θ n ω}) ≠ ⊤ := by
  let gap : ℝ := cgf (Y 0) μ (θ / 2) - cgf (Y 0) μ θ / 2
  have hgap : gap < 0 := by
    simpa [gap] using
      cgfHalfGap_neg (Y := Y) (μ := μ) (δ := δ) hY_not_ae_const hY_exp_int hθ hθ_ne
  have hgeom :
      Summable (fun n : ℕ ↦ (Real.sqrt ε)⁻¹ * Real.exp ((n : ℝ) * gap)) := by
    have hr_nonneg : 0 ≤ Real.exp gap := by positivity
    have hr_lt_one : Real.exp gap < 1 := by
      exact Real.exp_lt_one_iff.2 hgap
    have hbase : Summable (fun n : ℕ ↦ Real.exp ((n : ℝ) * gap)) := by
      simpa [Real.exp_nat_mul] using
        (summable_geometric_of_lt_one hr_nonneg hr_lt_one)
    exact hbase.mul_left ((Real.sqrt ε)⁻¹)
  have hreal :
      Summable
        (fun n : ℕ ↦ μ.real {ω | ε ≤ cramerLundbergExponentialProcess Y μ θ n ω}) := by
    -- The Markov bound is geometric because the midpoint convexity gap is negative.
    refine Summable.of_nonneg_of_le (fun n ↦ by positivity) (fun n ↦ ?_) hgeom
    simpa [gap] using
      cramerLundbergThresholdProbability_le (Y := Y) (μ := μ) (δ := δ) hY_indep hY_ident
        hY_exp_int hθ hε n
  -- Convert the real-valued summability back to finiteness of the ENNReal total mass.
  simpa [ENNReal.ofReal_toReal, measure_ne_top] using hreal.tsum_ofReal_ne_top

-- Proof sketch: combine the martingale property and nonnegativity of `Z^θ` with the decay of
-- `E[√(Z_n^θ)]`; convergence of the nonnegative martingale and the vanishing square-root moments
-- force the almost-sure limit to be zero. The midpoint condition for `θ / 2` is derived
-- internally from `hθ`, so it is not part of the public statement.
theorem cramerLundbergExponentialProcess_tendsto_zero_ae {θ : ℝ}
    (hY_indep : iIndepFun Y μ) (hY_ident : ∀ n, IdentDistrib (Y n) (Y 0) μ μ)
    (hY_not_ae_const : ¬ ∃ c : ℝ, Y 0 =ᵐ[μ] fun _ ↦ c)
    (hY_exp_int : ∀ ϑ ∈ Set.Ioo (-δ) δ, Integrable (fun ω ↦ Real.exp (ϑ * Y 0 ω)) μ)
    (hθ : θ ∈ Set.Ioo (-δ) δ) (hθ_ne : θ ≠ 0) :
    ∀ᵐ ω ∂μ, Filter.Tendsto
      (fun n ↦ cramerLundbergExponentialProcess Y μ θ n ω) Filter.atTop (nhds 0) := by
  let threshold : ℕ → ℕ → Set Ω := fun m n ↦
    {ω | (1 / ((m : ℝ) + 1)) ≤ cramerLundbergExponentialProcess Y μ θ n ω}
  have hthreshold_ae :
      ∀ᵐ ω ∂μ, ∀ m : ℕ, ∀ᶠ n in Filter.atTop, ω ∉ threshold m n := by
    rw [ae_all_iff]
    intro m
    -- Each fixed reciprocal threshold belongs to the summable family from the previous helper.
    have hsummable :
        (∑' n : ℕ, μ (threshold m n)) ≠ ⊤ := by
      simpa [threshold] using
        cramerLundbergThresholdEventsSummable (Y := Y) (μ := μ) (δ := δ) hY_indep hY_ident
          hY_not_ae_const hY_exp_int hθ hθ_ne (by positivity : 0 < 1 / ((m : ℝ) + 1))
    simpa [threshold] using
      (MeasureTheory.ae_eventually_notMem (μ := μ) (s := threshold m) hsummable)
  filter_upwards [hthreshold_ae] with ω hω
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  rcases Filter.eventually_atTop.1 (hω m) with ⟨N, hN⟩
  refine ⟨N, fun n hn ↦ ?_⟩
  have hnot_mem : ω ∉ threshold m n := hN n hn
  have hlt :
      cramerLundbergExponentialProcess Y μ θ n ω < 1 / ((m : ℝ) + 1) := by
    by_contra hge
    exact hnot_mem (not_lt.mp hge)
  have hltε : cramerLundbergExponentialProcess Y μ θ n ω < ε := lt_trans hlt hm
  have hnonneg : 0 ≤ cramerLundbergExponentialProcess Y μ θ n ω := by
    rw [cramerLundbergExponentialProcess_apply]
    positivity
  -- The pathwise process is nonnegative, so closeness to `0` is just an upper bound.
  simpa [Real.dist_eq, abs_of_nonneg hnonneg] using hltε

/-- Exercise 10.2.2 (5): if the increment mean is positive and a nonzero root `θ⋆` of the
cumulant generating function exists, then that root is negative. -/
-- Proof sketch: `cgf (Y 0) μ 0 = 0`, the derivative at `0` is the positive mean of `Y_0`, and the
-- strict convexity of `cgf` shows that a second zero cannot lie to the right of `0`; the positive
-- mean together with the nonzero root already excludes the almost surely constant case.
theorem cgf_root_neg_of_mean_pos {θStar : ℝ}
    (hY_exp_int : ∀ θ ∈ Set.Ioo (-δ) δ, Integrable (fun ω ↦ Real.exp (θ * Y 0 ω)) μ)
    (hY_mean_pos : 0 < μ[Y 0]) (hθStar : θStar ∈ Set.Ioo (-δ) δ)
    (hroot : cgf (Y 0) μ θStar = 0) (hθStar_ne : θStar ≠ 0) :
    θStar < 0 := by
  have hY_not_ae_const : ¬ ∃ c : ℝ, Y 0 =ᵐ[μ] fun _ ↦ c := by
    intro hconst
    rcases hconst with ⟨c, hc⟩
    -- A constant increment law would force the cgf root to be at `0`, contradicting the
    -- positive mean hypothesis.
    have hmgf_const : mgf (Y 0) μ θStar = Real.exp (θStar * c) := by
      have hexp_ae :
          (fun ω ↦ Real.exp (θStar * Y 0 ω)) =ᵐ[μ] fun _ ↦ Real.exp (θStar * c) := by
        filter_upwards [hc] with ω hω
        simp [hω]
      calc
        mgf (Y 0) μ θStar = ∫ ω, Real.exp (θStar * c) ∂μ := by
          simpa [ProbabilityTheory.mgf] using integral_congr_ae hexp_ae
        _ = Real.exp (θStar * c) := by
          simp
    have hcgf_const : cgf (Y 0) μ θStar = θStar * c := by
      rw [cgf, hmgf_const, Real.log_exp]
    have hc_zero : c = 0 := by
      have hmul_zero : θStar * c = 0 := by
        linarith [hroot, hcgf_const]
      exact (mul_eq_zero.mp hmul_zero).resolve_left hθStar_ne
    have hmean_eq : μ[Y 0] = c := by
      simpa using integral_congr_ae hc
    linarith
  have hzero_mem : (0 : ℝ) ∈ Set.Ioo (-δ) δ := by
    constructor <;> linarith [hθStar.1, hθStar.2]
  have hzero_int :
      (0 : ℝ) ∈ interior (integrableExpSet (Y 0) μ) :=
    memInterior_integrableExpSet_of_memInterval (Y := Y) (μ := μ) hY_exp_int hzero_mem
  have hdiff : DifferentiableAt ℝ (cgf (Y 0) μ) 0 := by
    exact (ProbabilityTheory.analyticAt_cgf (X := Y 0) (μ := μ) hzero_int).differentiableAt
  have hderiv : deriv (cgf (Y 0) μ) 0 = μ[Y 0] := by
    simpa using ProbabilityTheory.deriv_cgf_zero (X := Y 0) (μ := μ) hzero_int
  have hsc := cgf_strictConvexOn_increment_interval (Y := Y) (μ := μ) (δ := δ)
    hY_not_ae_const hY_exp_int
  have hzero : cgf (Y 0) μ 0 = 0 := by
    simp
  by_contra hneg
  have hnonneg : 0 ≤ θStar := by
    linarith
  have hpos : 0 < θStar := lt_of_le_of_ne hnonneg (Ne.symm hθStar_ne)
  -- Route correction: compare the positive derivative at `0` with the secant slope to the
  -- second zero `θStar`; strict convexity forces that slope to be larger than the derivative.
  have hslope_lt :
      deriv (cgf (Y 0) μ) 0 < slope (cgf (Y 0) μ) 0 θStar :=
    StrictConvexOn.deriv_lt_slope hsc hzero_mem hθStar hpos hdiff
  have hslope_zero : slope (cgf (Y 0) μ) 0 θStar = 0 := by
    simp [slope_def_field, hzero, hroot, hθStar_ne]
  linarith [hY_mean_pos, hderiv, hslope_lt, hslope_zero]

-- Exercise 10.2.2 (6): if `θ⋆` is a nonzero root of the cumulant generating function and the
-- increment mean is positive, then the ruin probability is bounded by `exp (θ⋆ k₀)`.
/-- Helper for Exercise 10.2.2: if ruin occurs by time `N`, then the running maximum of the
 exponential martingale up to time `N` crosses the Cramér-Lundberg threshold
 `exp (-θ⋆ k₀)`. -/
private theorem finiteHorizonRuinEvent_subset_runningMaxThreshold {θStar k₀ : ℝ}
    (hY_exp_int : ∀ θ ∈ Set.Ioo (-δ) δ, Integrable (fun ω ↦ Real.exp (θ * Y 0 ω)) μ)
    (hY_mean_pos : 0 < μ[Y 0]) (hθStar : θStar ∈ Set.Ioo (-δ) δ)
    (hroot : cgf (Y 0) μ θStar = 0) (hθStar_ne : θStar ≠ 0) (N : ℕ) :
    {ω | ∃ n ≤ N, partialSum Y n ω + k₀ < 0} ⊆
      {ω |
        Real.exp (-θStar * k₀) ≤
          (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
            (fun k ↦ cramerLundbergExponentialProcess Y μ θStar k ω)} := by
  have hθStar_neg : θStar < 0 :=
    cgf_root_neg_of_mean_pos (Y := Y) (μ := μ) (δ := δ) hY_exp_int hY_mean_pos
      hθStar hroot hθStar_ne
  intro ω hω
  rcases hω with ⟨n, hnN, hruin⟩
  have hthreshold_lt :
      Real.exp (-θStar * k₀) <
        cramerLundbergExponentialProcess Y μ θStar n ω := by
    have hexp_lt :
        Real.exp (-θStar * k₀) < Real.exp (θStar * partialSum Y n ω) := by
      apply Real.exp_lt_exp.mpr
      -- Route correction: use `θ⋆ < 0` to reverse the ruin inequality into an exponential lower
      -- bound for the martingale stage at the ruin time.
      nlinarith [hruin, hθStar_neg]
    calc
      Real.exp (-θStar * k₀) < Real.exp (θStar * partialSum Y n ω) := hexp_lt
      _ = cramerLundbergExponentialProcess Y μ θStar n ω := by
        rw [cramerLundbergExponentialProcess_apply, hroot]
        simp
  have hle_sup :
      cramerLundbergExponentialProcess Y μ θStar n ω ≤
        (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
          (fun k ↦ cramerLundbergExponentialProcess Y μ θStar k ω) := by
    exact Finset.le_sup' (fun k ↦ cramerLundbergExponentialProcess Y μ θStar k ω) <|
      Finset.mem_range.mpr (Nat.lt_succ_of_le hnN)
  -- Compare the threshold with the ruin-time stage and then with the running maximum.
  exact hthreshold_lt.le.trans hle_sup

/-- Helper for Exercise 10.2.2: Doob's maximal inequality on the positive martingale `Z^{θ⋆}`
gives the finite-horizon Cramér-Lundberg bound. -/
private theorem finiteHorizonRuinProbability_le_exp_cgfRoot {θStar k₀ : ℝ}
    (hY_meas : ∀ n, Measurable (Y n))
    (hY_indep : iIndepFun Y μ) (hY_ident : ∀ n, IdentDistrib (Y n) (Y 0) μ μ)
    (hY_exp_int : ∀ θ ∈ Set.Ioo (-δ) δ, Integrable (fun ω ↦ Real.exp (θ * Y 0 ω)) μ)
    (hY_mean_pos : 0 < μ[Y 0]) (hθStar : θStar ∈ Set.Ioo (-δ) δ)
    (hroot : cgf (Y 0) μ θStar = 0) (hθStar_ne : θStar ≠ 0) (N : ℕ) :
    μ.real {ω | ∃ n ≤ N, partialSum Y n ω + k₀ < 0} ≤ Real.exp (θStar * k₀) := by
  let A : Set Ω := {ω | ∃ n ≤ N, partialSum Y n ω + k₀ < 0}
  let B : Set Ω := {ω |
    Real.exp (-θStar * k₀) ≤
      (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
        (fun k ↦ cramerLundbergExponentialProcess Y μ θStar k ω)}
  have hsubset : A ⊆ B :=
    finiteHorizonRuinEvent_subset_runningMaxThreshold (Y := Y) (μ := μ) (δ := δ)
      hY_exp_int hY_mean_pos hθStar hroot hθStar_ne N
  have hmart :=
    cramerLundbergExponentialProcess_martingale (Y := Y) (μ := μ) (hY_meas := hY_meas)
      (δ := δ) hY_indep hY_ident (hY_exp_int θStar hθStar) hθStar
  have hnonneg : 0 ≤ cramerLundbergExponentialProcess Y μ θStar := by
    intro n ω
    rw [cramerLundbergExponentialProcess_apply]
    positivity
  have hε_nonneg : 0 ≤ Real.exp (-θStar * k₀) := by
    positivity
  let ε : NNReal := ⟨Real.exp (-θStar * k₀), hε_nonneg⟩
  let Bmax : Set Ω := {ω |
    (ε : ℝ) ≤
      (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
        (fun k ↦ cramerLundbergExponentialProcess Y μ θStar k ω)}
  have hB_eq : B = Bmax := by
    ext ω
    simp [B, Bmax, ε]
  have hmax :=
    MeasureTheory.maximal_ineq (μ := μ)
      (f := cramerLundbergExponentialProcess Y μ θStar) hmart.submartingale hnonneg
      (ε := ε) N
  have hsetIntegral_le :
      ∫ ω in B, cramerLundbergExponentialProcess Y μ θStar N ω ∂μ ≤
        ∫ ω, cramerLundbergExponentialProcess Y μ θStar N ω ∂μ := by
    -- The stopped-set integral is bounded by the full expectation because `Z_N^{θ⋆}` is
    -- pointwise nonnegative.
    refine MeasureTheory.setIntegral_le_integral (hfi := hmart.integrable N) ?_
    filter_upwards with ω
    rw [cramerLundbergExponentialProcess_apply]
    positivity
  have hscaled_B :
      ENNReal.ofNNReal ε * μ B ≤ ENNReal.ofReal (1 : ℝ) := by
    -- Replace the restricted integral by the total expectation `E[Z_N^{θ⋆}] = 1`.
    have hmax' :
        ENNReal.ofNNReal ε * μ Bmax ≤
          ENNReal.ofReal
            (∫ ω in Bmax, cramerLundbergExponentialProcess Y μ θStar N ω ∂μ) := by
      simpa [Bmax] using hmax
    rw [hB_eq]
    refine le_trans hmax' ?_
    exact ENNReal.ofReal_le_ofReal <| by
      calc
        ∫ ω in B, cramerLundbergExponentialProcess Y μ θStar N ω ∂μ
            ≤ ∫ ω, cramerLundbergExponentialProcess Y μ θStar N ω ∂μ := hsetIntegral_le
        _ = 1 := cramerLundbergExponentialProcess_expectation_one (Y := Y) (μ := μ) hY_meas
          hY_indep hY_ident (hY_exp_int θStar hθStar) N
  have hscaled_A :
      ENNReal.ofNNReal ε * μ A ≤ ENNReal.ofReal (1 : ℝ) := by
    -- Shrink the maximal-event bound back to the finite ruin event using the pathwise subset.
    calc
      ENNReal.ofNNReal ε * μ A
          ≤ ENNReal.ofNNReal ε * μ B := by
            gcongr
      _ ≤ ENNReal.ofReal (1 : ℝ) := hscaled_B
  have hscaled_A_real : Real.exp (-θStar * k₀) * μ.real A ≤ 1 := by
    -- Convert the ENNReal inequality into a real-valued inequality on probabilities.
    have hscaled_A_toReal :
        (ENNReal.ofNNReal ε * μ A).toReal ≤
          (ENNReal.ofReal (1 : ℝ)).toReal :=
      ENNReal.toReal_mono (by simp) hscaled_A
    have hscaled_A_real' :
        (ENNReal.ofNNReal ε).toReal * μ.real A ≤ 1 := by
      simpa [A, Measure.real_def, ENNReal.toReal_mul] using hscaled_A_toReal
    calc
      Real.exp (-θStar * k₀) * μ.real A =
          (ENNReal.ofNNReal ε).toReal * μ.real A := by
            simp [ε]
      _ ≤ 1 := hscaled_A_real'
  have hthreshold_pos : 0 < Real.exp (-θStar * k₀) := by
    positivity
  have hprob_le_inv : μ.real A ≤ 1 / Real.exp (-θStar * k₀) := by
    exact (le_div_iff₀ hthreshold_pos).2 (by simpa [mul_comm] using hscaled_A_real)
  -- Rewrite the reciprocal threshold back into `exp (θ⋆ k₀)`.
  calc
    μ.real A ≤ 1 / Real.exp (-θStar * k₀) := hprob_le_inv
    _ = Real.exp (θStar * k₀) := by
      rw [show -θStar * k₀ = -(θStar * k₀) by ring, Real.exp_neg]
      simp [one_div]

-- Proof sketch: apply optional stopping to the nonnegative martingale `Z^{θ⋆}` stopped at the
-- ruin time and a deterministic truncation, use `cgf (Y 0) μ θ⋆ = 0` to simplify the stopped
-- process, and then pass to the limit to obtain the Cramér-Lundberg bound.
theorem ruinProbability_le_exp_cgf_root {θStar k₀ : ℝ}
    (hY_meas : ∀ n, Measurable (Y n))
    (hY_indep : iIndepFun Y μ) (hY_ident : ∀ n, IdentDistrib (Y n) (Y 0) μ μ)
    (hY_exp_int : ∀ θ ∈ Set.Ioo (-δ) δ, Integrable (fun ω ↦ Real.exp (θ * Y 0 ω)) μ)
    (hY_mean_pos : 0 < μ[Y 0]) (hθStar : θStar ∈ Set.Ioo (-δ) δ)
    (hroot : cgf (Y 0) μ θStar = 0) (hθStar_ne : θStar ≠ 0) :
    ruinProbability Y μ k₀ ≤ Real.exp (θStar * k₀) := by
  let A : ℕ → Set Ω := fun N ↦ {ω | ∃ n ≤ N, partialSum Y n ω + k₀ < 0}
  have hmono : Monotone A := by
    intro m n hmn ω hω
    rcases hω with ⟨k, hkm, hkruin⟩
    exact ⟨k, Nat.le_trans hkm hmn, hkruin⟩
  have hmeasure_union_le :
      μ (⋃ N, A N) ≤ ENNReal.ofReal (Real.exp (θStar * k₀)) := by
    -- Bound the union measure by the supremum of the uniformly bounded finite-horizon measures.
    rw [hmono.measure_iUnion]
    refine iSup_le fun N ↦ ?_
    rw [← MeasureTheory.ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal <|
      finiteHorizonRuinProbability_le_exp_cgfRoot (Y := Y) (μ := μ) (δ := δ) hY_meas hY_indep
        hY_ident hY_exp_int hY_mean_pos hθStar hroot hθStar_ne N
  have hreal_union_le : μ.real (⋃ N, A N) ≤ Real.exp (θStar * k₀) := by
    -- Convert the increasing-union bound back to the real-valued ruin probability.
    have hmeasure_union_toReal :
        (μ (⋃ N, A N)).toReal ≤ (ENNReal.ofReal (Real.exp (θStar * k₀))).toReal :=
      ENNReal.toReal_mono (by simp) hmeasure_union_le
    have hcoeff :
        (ENNReal.ofReal (Real.exp (θStar * k₀))).toReal = Real.exp (θStar * k₀) := by
      exact ENNReal.toReal_ofReal (by positivity)
    simpa [Measure.real_def, hcoeff] using hmeasure_union_toReal
  have hruin_union :
      {ω | ∃ n : ℕ, partialSum Y n ω + k₀ < 0} = ⋃ N, A N := by
    ext ω
    constructor
    · rintro ⟨n, hruin⟩
      exact Set.mem_iUnion.2 ⟨n, ⟨n, le_rfl, hruin⟩⟩
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨N, hN⟩
      rcases hN with ⟨n, hnN, hruin⟩
      exact ⟨n, hruin⟩
  -- Rewrite the infinite-horizon ruin event as the increasing union of the finite-horizon events.
  rw [ruinProbability_def, hruin_union]
  exact hreal_union_le

/-- Helper for Exercise 10.2.2: along a path whose increments are all `±1`, every partial sum is
an integer-valued real number. -/
private theorem partialSum_integerValued_of_twoPoint {ω : Ω}
    (hω : ∀ n, Y n ω = -1 ∨ Y n ω = 1) :
    ∀ n : ℕ, ∃ z : ℤ, partialSum Y n ω = (z : ℝ) := by
  intro n
  induction n with
  | zero =>
      -- The empty partial sum is the integer `0`.
      refine ⟨0, by simp [partialSum]⟩
  | succ n ih =>
      rcases ih with ⟨z, hz⟩
      have hsucc : partialSum Y (n + 1) ω = partialSum Y n ω + Y n ω := by
        rw [partialSum_apply, partialSum_apply]
        simpa using (Finset.sum_range_succ (fun i : ℕ ↦ Y i ω) n)
      -- The next partial sum changes by exactly one integer step.
      rcases hω n with hstep | hstep
      · refine ⟨z - 1, ?_⟩
        rw [hsucc, hz, hstep]
        simpa [sub_eq_add_neg] using (Int.cast_sub z 1).symm
      · refine ⟨z + 1, ?_⟩
        rw [hsucc, hz, hstep]
        rw [Int.cast_add]
        norm_num

/-- Helper for Exercise 10.2.2: coordinatewise almost-everywhere equality of two increment
processes transports to almost-everywhere equality of all finite partial sums. -/
private theorem partialSum_ae_eq_of_incrementModification {Y1 Y2 : ℕ → Ω → ℝ}
    (hYY : ∀ n, Y1 n =ᵐ[μ] Y2 n) :
    ∀ᵐ ω ∂μ, ∀ n, partialSum Y1 n ω = partialSum Y2 n ω := by
  have hAll : ∀ᵐ ω ∂μ, ∀ n, Y1 n ω = Y2 n ω := by
    simpa using (ae_all_iff.2 hYY)
  filter_upwards [hAll] with ω hω n
  rw [partialSum_apply, partialSum_apply]
  refine Finset.sum_congr rfl ?_
  intro j hj
  exact hω j

/-- Helper for Exercise 10.2.2: coordinatewise almost-everywhere equality of two increment
processes transports the strict-ruin event for a fixed initial capital. -/
private theorem ruinEvent_ae_eq_of_incrementModification {Y1 Y2 : ℕ → Ω → ℝ}
    (hYY : ∀ n, Y1 n =ᵐ[μ] Y2 n) (k₀ : ℝ) :
    {ω | ∃ n : ℕ, partialSum Y1 n ω + k₀ < 0} =ᵐ[μ]
      {ω | ∃ n : ℕ, partialSum Y2 n ω + k₀ < 0} := by
  filter_upwards [partialSum_ae_eq_of_incrementModification (μ := μ) hYY] with ω hω
  -- Rewrite the strict-ruin witness through the a.e. equality of all partial sums.
  apply propext
  constructor
  · rintro ⟨n, hruin⟩
    exact ⟨n, by simpa [hω n] using hruin⟩
  · rintro ⟨n, hruin⟩
    exact ⟨n, by simpa [hω n] using hruin⟩

/-- Helper for Exercise 10.2.2: coordinatewise almost-everywhere equality of two increment
processes preserves the ruin probability for any fixed initial capital. -/
private theorem ruinProbability_eq_of_incrementModification {Y1 Y2 : ℕ → Ω → ℝ}
    (hYY : ∀ n, Y1 n =ᵐ[μ] Y2 n) (k₀ : ℝ) :
    ruinProbability Y1 μ k₀ = ruinProbability Y2 μ k₀ := by
  -- Rewrite the ruin event through the a.e.-equality of all finite partial sums.
  rw [ruinProbability_def, ruinProbability_def, Measure.real_def,
    measure_congr (ruinEvent_ae_eq_of_incrementModification (μ := μ) hYY k₀), Measure.real_def]

/-- Helper for Exercise 10.2.2: almost-everywhere equality preserves the positivity of the mean. -/
private theorem mean_pos_of_ae_eq {X1 X2 : Ω → ℝ} (hXX : X1 =ᵐ[μ] X2)
    (hmean_pos : 0 < μ[X1]) : 0 < μ[X2] := by
  have hmean_eq : μ[X1] = μ[X2] := by
    simpa using integral_congr_ae hXX
  -- Transport the expectation through the a.e. equality before reusing the positivity bound.
  linarith [hmean_pos, hmean_eq]

/-- Helper for Exercise 10.2.2: almost-everywhere equal increments have the same cumulant
generating function at every parameter. -/
private theorem cgf_eq_of_ae_eq {X1 X2 : Ω → ℝ} (hXX : X1 =ᵐ[μ] X2) (θ : ℝ) :
    cgf X1 μ θ = cgf X2 μ θ := by
  have hmgf_eq : mgf X1 μ θ = mgf X2 μ θ := by
    have hexp_eq :
        (fun ω ↦ Real.exp (θ * X1 ω)) =ᵐ[μ] fun ω ↦ Real.exp (θ * X2 ω) := by
      filter_upwards [hXX] with ω hω
      simp [hω]
    -- The moment generating functions agree because their integrands agree almost everywhere.
    simpa [ProbabilityTheory.mgf] using integral_congr_ae hexp_eq
  -- The cumulant generating function is just the logarithm of the matching mgf values.
  simp [ProbabilityTheory.cgf, hmgf_eq]

/-- Helper for Exercise 10.2.2: a coordinatewise almost-everywhere modification preserves the
`±1` support condition. -/
private theorem twoPoint_ae_of_ae_eq {Y1 Y2 : ℕ → Ω → ℝ}
    (hYY : ∀ n, Y1 n =ᵐ[μ] Y2 n)
    (h_two_point : ∀ n, ∀ᵐ ω ∂μ, Y1 n ω = -1 ∨ Y1 n ω = 1) :
    ∀ n, ∀ᵐ ω ∂μ, Y2 n ω = -1 ∨ Y2 n ω = 1 := by
  intro n
  filter_upwards [hYY n, h_two_point n] with ω hω hstep
  -- Replace the modified increment by the original one inside the two-point alternative.
  simpa [hω] using hstep

/-- Helper for Exercise 10.2.2: on a path with `±1` increments, strict ruin by time `N` from
capital `k₀` is equivalent to the shifted capital hitting `0` by time `N`. -/
private theorem finiteRuin_iff_shiftedHitZero_of_twoPoint {ω : Ω} {k₀ N : ℕ}
    (hω : ∀ n, Y n ω = -1 ∨ Y n ω = 1) :
    (∃ n ≤ N, partialSum Y n ω + (k₀ : ℝ) < 0) ↔
      ∃ n ≤ N, partialSum Y n ω + ((k₀ : ℝ) + 1) = 0 := by
  constructor
  · intro hruin
    set n₀ : ℕ := Nat.find hruin with hn₀_def
    have hn₀_le : n₀ ≤ N := (Nat.find_spec hruin).1
    have hn₀_ruin : partialSum Y n₀ ω + (k₀ : ℝ) < 0 := (Nat.find_spec hruin).2
    have hn₀_ne_zero : n₀ ≠ 0 := by
      intro hn₀_zero
      have hnot : ¬ (partialSum Y 0 ω + (k₀ : ℝ) < 0) := by
        simp [partialSum]
      have hruin_zero : partialSum Y 0 ω + (k₀ : ℝ) < 0 := by
        simpa [hn₀_zero] using hn₀_ruin
      exact hnot hruin_zero
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn₀_ne_zero
    have hn₀_le' : m + 1 ≤ N := by
      simpa [hm] using hn₀_le
    have hn₀_ruin' : partialSum Y (m + 1) ω + (k₀ : ℝ) < 0 := by
      simpa [hm] using hn₀_ruin
    have hm_not_ruin : ¬ partialSum Y m ω + (k₀ : ℝ) < 0 := by
      intro hm_ruin
      have hminimal : Nat.find hruin ≤ m :=
        Nat.find_min' hruin ⟨Nat.le_trans (Nat.le_succ m) hn₀_le', hm_ruin⟩
      omega
    have hm_nonneg : 0 ≤ partialSum Y m ω + (k₀ : ℝ) := by
      linarith
    have hsucc : partialSum Y (m + 1) ω = partialSum Y m ω + Y m ω := by
      rw [partialSum_apply, partialSum_apply]
      simpa using (Finset.sum_range_succ (fun i : ℕ ↦ Y i ω) m)
    -- Route correction: use the minimal strict-ruin time and the integer-valued previous capital.
    rcases hω m with hstep | hstep
    · have hm_lt_one : partialSum Y m ω + (k₀ : ℝ) < 1 := by
        rw [hsucc, hstep] at hn₀_ruin'
        linarith
      rcases partialSum_integerValued_of_twoPoint (Y := Y) (ω := ω) hω m with ⟨z, hz⟩
      have hz_nonneg : (0 : ℤ) ≤ z + k₀ := by
        have hreal : (0 : ℝ) ≤ (((z + k₀ : ℤ) : ℝ)) := by
          simpa [hz] using hm_nonneg
        exact_mod_cast hreal
      have hz_lt_one : z + k₀ < 1 := by
        have hreal : (((z + k₀ : ℤ) : ℝ)) < (1 : ℝ) := by
          simpa [hz] using hm_lt_one
        exact_mod_cast hreal
      have hz_zero : z + k₀ = 0 := by
        omega
      have hprev_zero : partialSum Y m ω + (k₀ : ℝ) = 0 := by
        have hreal : (((z + k₀ : ℤ) : ℝ)) = 0 := by
          exact_mod_cast hz_zero
        simpa [hz] using hreal
      refine ⟨m + 1, hn₀_le', ?_⟩
      rw [hsucc, hstep]
      linarith
    · rw [hsucc, hstep] at hn₀_ruin'
      linarith
  · rintro ⟨n, hn, hhit⟩
    refine ⟨n, hn, ?_⟩
    linarith

/-- Helper for Exercise 10.2.2: the shifted capital process used to replace strict ruin by a hit
of `0` in the `±1`-valued case. -/
private def shiftedCapitalProcess (Y : ℕ → Ω → ℝ) (k₀ : ℕ) : ℕ → Ω → ℝ :=
  fun n ω ↦ partialSum Y n ω + ((k₀ : ℝ) + 1)

/-- Helper for Exercise 10.2.2: the exact-hit event of the shifted capital process. -/
private def shiftedHitEvent (Y : ℕ → Ω → ℝ) (k₀ : ℕ) : Set Ω :=
  {ω | ∃ n : ℕ, shiftedCapitalProcess Y k₀ n ω = 0}

/-- Helper for Exercise 10.2.2: the bounded-horizon exact-hit event of the shifted capital
process. -/
private def finiteShiftedHitEvent (Y : ℕ → Ω → ℝ) (k₀ : ℕ) (N : ℕ) : Set Ω :=
  {ω | ∃ n ≤ N, shiftedCapitalProcess Y k₀ n ω = 0}

/-- Helper for Exercise 10.2.2: the exponential transform of the shifted capital process. -/
private def shiftedCapitalExponentialProcess
    (Y : ℕ → Ω → ℝ) (θStar : ℝ) (k₀ : ℕ) : ℕ → Ω → ℝ :=
  fun n ω ↦ Real.exp (θStar * shiftedCapitalProcess Y k₀ n ω)

/-- Helper for Exercise 10.2.2: the no-hit remainder term at finite horizon `N`. -/
private def shiftedExponentialRemainder
    (Y : ℕ → Ω → ℝ) (θStar : ℝ) (k₀ : ℕ) (N : ℕ) : Ω → ℝ :=
  (finiteShiftedHitEvent Y k₀ N)ᶜ.indicator (shiftedCapitalExponentialProcess Y θStar k₀ N)

/-- Helper for Exercise 10.2.2: each stage of the shifted capital process is measurable. -/
private theorem shiftedCapitalProcessMeasurable
    (hY_meas : ∀ n, Measurable (Y n)) {k₀ : ℕ} :
    ∀ n, Measurable (shiftedCapitalProcess Y k₀ n) := by
  intro n
  -- Each shifted capital is the measurable partial sum plus a constant offset.
  simpa [shiftedCapitalProcess] using
    (partialSum_measurable Y hY_meas n).add measurable_const

/-- Helper for Exercise 10.2.2: the shifted capital process is adapted to the natural filtration
of the partial sums. -/
private theorem shiftedCapitalProcessAdapted
    (hY_meas : ∀ n, Measurable (Y n)) {k₀ : ℕ} :
    Adapted ℱY (shiftedCapitalProcess Y k₀) := by
  let hS : Adapted ℱY (partialSum Y) :=
    (Filtration.stronglyAdapted_natural
      (u := partialSum Y) (hum := partialSumStronglyMeasurable hY_meas)).adapted
  intro n
  -- The natural filtration already sees `partialSum Y n`, so the shifted version is adapted too.
  simpa [shiftedCapitalProcess] using (hS n).add measurable_const

/-- Helper for Exercise 10.2.2: the shifted exponential process is a fixed scalar multiple of the
Cramér-Lundberg exponential martingale once `cgf (Y 0) μ θ⋆ = 0`. -/
private theorem shiftedCapitalExponentialProcess_apply {θStar : ℝ} {k₀ : ℕ}
    (hroot : cgf (Y 0) μ θStar = 0) :
    ∀ n ω,
      shiftedCapitalExponentialProcess Y θStar k₀ n ω =
        Real.exp (θStar * ((k₀ : ℝ) + 1)) *
          cramerLundbergExponentialProcess Y μ θStar n ω := by
  intro n ω
  rw [cramerLundbergExponentialProcess_apply, hroot]
  dsimp [shiftedCapitalExponentialProcess, shiftedCapitalProcess]
  have hsplit :
      θStar * (partialSum Y n ω + ((k₀ : ℝ) + 1)) =
        θStar * ((k₀ : ℝ) + 1) + θStar * partialSum Y n ω := by
    ring
  rw [hsplit, Real.exp_add]
  simp

/-- Helper for Exercise 10.2.2: each stage of the shifted exponential process is measurable. -/
private theorem shiftedCapitalExponentialProcessMeasurable
    (hY_meas : ∀ n, Measurable (Y n)) {θStar : ℝ} {k₀ : ℕ} :
    ∀ n, Measurable (shiftedCapitalExponentialProcess Y θStar k₀ n) := by
  intro n
  have hExp : Measurable (fun x : ℝ ↦ Real.exp (θStar * x)) := by
    fun_prop
  -- Compose the shifted capital with the measurable exponential map.
  simpa [shiftedCapitalExponentialProcess] using
    hExp.comp (shiftedCapitalProcessMeasurable (Y := Y) hY_meas (k₀ := k₀) n)

/-- Helper for Exercise 10.2.2: the shifted exponential process is a martingale because it is a
constant multiple of `Z^{θ⋆}`. -/
private theorem shiftedCapitalExponentialProcess_martingale {θStar : ℝ} {k₀ : ℕ}
    (hY_indep : iIndepFun Y μ) (hY_ident : ∀ n, IdentDistrib (Y n) (Y 0) μ μ)
    (hY_exp_int : Integrable (fun ω ↦ Real.exp (θStar * Y 0 ω)) μ)
    (hθStar : θStar ∈ Set.Ioo (-δ) δ) (hroot : cgf (Y 0) μ θStar = 0) :
    Martingale (shiftedCapitalExponentialProcess Y θStar k₀) ℱY μ := by
  let c : ℝ := Real.exp (θStar * ((k₀ : ℝ) + 1))
  have hmart :
      Martingale (cramerLundbergExponentialProcess Y μ θStar) ℱY μ :=
    cramerLundbergExponentialProcess_martingale (Y := Y) (μ := μ) (hY_meas := hY_meas)
      (δ := δ) hY_indep hY_ident hY_exp_int hθStar
  have hshift :
      shiftedCapitalExponentialProcess Y θStar k₀ =
        c • cramerLundbergExponentialProcess Y μ θStar := by
    funext n ω
    simpa [c, Pi.smul_apply] using
      shiftedCapitalExponentialProcess_apply (Y := Y) (μ := μ) (k₀ := k₀) hroot n ω
  -- Rewrite the shifted process as a fixed scalar multiple of the base exponential martingale.
  rw [hshift]
  exact hmart.smul c

/-- Helper for Exercise 10.2.2: the finite-horizon exact-hit event is measurable. -/
private theorem finiteShiftedHitEvent_measurable
    (hY_meas : ∀ n, Measurable (Y n)) {k₀ : ℕ} (N : ℕ) :
    MeasurableSet (finiteShiftedHitEvent Y k₀ N) := by
  induction N with
  | zero =>
      have hset :
          finiteShiftedHitEvent Y k₀ 0 = {ω | shiftedCapitalProcess Y k₀ 0 ω = 0} := by
        ext ω
        constructor
        · rintro ⟨n, hn, hhit⟩
          have hn_zero : n = 0 := Nat.eq_zero_of_le_zero hn
          simpa [hn_zero] using hhit
        · intro hhit
          exact ⟨0, le_rfl, hhit⟩
      rw [hset]
      -- At time `0`, the event is a single measurable preimage of `{0}`.
      change MeasurableSet ((shiftedCapitalProcess Y k₀ 0) ⁻¹' {0})
      exact
        (shiftedCapitalProcessMeasurable (Y := Y) hY_meas (k₀ := k₀) 0)
          (measurableSet_singleton 0)
  | succ N hN =>
      have hset :
          finiteShiftedHitEvent Y k₀ (N + 1) =
            finiteShiftedHitEvent Y k₀ N ∪
              {ω | shiftedCapitalProcess Y k₀ (N + 1) ω = 0} := by
        ext ω
        constructor
        · rintro ⟨n, hn, hhit⟩
          by_cases hle : n ≤ N
          · exact Or.inl ⟨n, hle, hhit⟩
          · have hn_last : n = N + 1 := by
              omega
            exact Or.inr (by simpa [hn_last] using hhit)
        · intro hω
          rcases hω with hω | hω
          · rcases hω with ⟨n, hn, hhit⟩
            exact ⟨n, Nat.le_trans hn (Nat.le_succ N), hhit⟩
          · exact ⟨N + 1, le_rfl, hω⟩
      rw [hset]
      -- Add the new final-time hit slice to the measurable finite-horizon union.
      exact hN.union <| by
        change MeasurableSet ((shiftedCapitalProcess Y k₀ (N + 1)) ⁻¹' {0})
        exact
          (shiftedCapitalProcessMeasurable (Y := Y) hY_meas (k₀ := k₀) (N + 1))
            (measurableSet_singleton 0)

/-- Helper for Exercise 10.2.2: the shifted exponential process converges almost surely to `0`
because it is a constant multiple of `Z^{θ⋆}`. -/
private theorem shiftedCapitalExponentialProcess_tendsto_zero_ae {θStar : ℝ} {k₀ : ℕ}
    (hY_indep : iIndepFun Y μ) (hY_ident : ∀ n, IdentDistrib (Y n) (Y 0) μ μ)
    (hY_not_ae_const : ¬ ∃ c : ℝ, Y 0 =ᵐ[μ] fun _ ↦ c)
    (hY_exp_int : ∀ ϑ ∈ Set.Ioo (-δ) δ, Integrable (fun ω ↦ Real.exp (ϑ * Y 0 ω)) μ)
    (hθStar : θStar ∈ Set.Ioo (-δ) δ) (hθStar_ne : θStar ≠ 0)
    (hroot : cgf (Y 0) μ θStar = 0) :
    ∀ᵐ ω ∂μ, Filter.Tendsto
      (fun n ↦ shiftedCapitalExponentialProcess Y θStar k₀ n ω) Filter.atTop (nhds 0) := by
  let c : ℝ := Real.exp (θStar * ((k₀ : ℝ) + 1))
  filter_upwards
      [cramerLundbergExponentialProcess_tendsto_zero_ae (Y := Y) (μ := μ) (δ := δ)
        hY_indep hY_ident hY_not_ae_const hY_exp_int hθStar hθStar_ne]
      with ω hω
  -- Transport the almost-sure decay through the constant-multiple identity for the shifted process.
  simpa [c, Pi.smul_apply, shiftedCapitalExponentialProcess_apply (Y := Y) (μ := μ) (k₀ := k₀)
    hroot] using hω.const_mul c

/-- Helper for Exercise 10.2.2: stopping the shifted exponential process at the first hit of `0`
before time `N` splits into the hit contribution `1` and the no-hit terminal remainder. -/
private theorem stoppedShiftedCapitalExponential_repr {θStar : ℝ} {k₀ : ℕ} (N : ℕ) :
    let τN : Ω → ℕ := fun ω ↦ hittingBtwn (shiftedCapitalProcess Y k₀) ({0} : Set ℝ) 0 N ω
    stoppedValue (shiftedCapitalExponentialProcess Y θStar k₀)
        (fun ω ↦ (τN ω : ℕ∞)) =
      fun ω ↦
        (finiteShiftedHitEvent Y k₀ N).indicator (fun _ ↦ (1 : ℝ)) ω +
          shiftedExponentialRemainder Y θStar k₀ N ω := by
  let τN : Ω → ℕ := fun ω ↦ hittingBtwn (shiftedCapitalProcess Y k₀) ({0} : Set ℝ) 0 N ω
  have hτN_eval :
      stoppedValue (shiftedCapitalExponentialProcess Y θStar k₀)
        (fun ω ↦ (τN ω : ℕ∞)) =
          fun ω ↦ shiftedCapitalExponentialProcess Y θStar k₀ (τN ω) ω := by
    -- Normalize the finite stopped value into ordinary evaluation at the hitting index.
    simpa [τN] using
      (stoppedValue_coe_eq_eval (shiftedCapitalExponentialProcess Y θStar k₀) τN :
        stoppedValue (shiftedCapitalExponentialProcess Y θStar k₀)
            (fun ω ↦ (τN ω : ℕ∞)) =
          fun ω ↦ shiftedCapitalExponentialProcess Y θStar k₀ (τN ω) ω)
  ext ω
  by_cases hhit : ω ∈ finiteShiftedHitEvent Y k₀ N
  · rcases hhit with ⟨j, hjN, hj0⟩
    have hhit_mem : ω ∈ finiteShiftedHitEvent Y k₀ N := ⟨j, hjN, hj0⟩
    have hhit_exists :
        ∃ i ∈ Set.Icc 0 N, shiftedCapitalProcess Y k₀ i ω ∈ ({0} : Set ℝ) := by
      refine ⟨j, ⟨Nat.zero_le j, hjN⟩, ?_⟩
      simpa [Set.mem_singleton_iff] using hj0
    have hcapital_zero : shiftedCapitalProcess Y k₀ (τN ω) ω = 0 := by
      -- On the hit slice, the bounded hitting time lands exactly on the level `0`.
      simpa [τN, stoppedValue, Set.mem_singleton_iff] using
        (stoppedValue_hittingBtwn_mem (u := shiftedCapitalProcess Y k₀)
          (s := ({0} : Set ℝ)) (n := 0) (m := N) (ω := ω) hhit_exists)
    have hτN_evalω :
        stoppedValue (shiftedCapitalExponentialProcess Y θStar k₀)
            (fun ω ↦ (τN ω : ℕ∞)) ω =
          shiftedCapitalExponentialProcess Y θStar k₀ (τN ω) ω := by
      simpa using congrFun hτN_eval ω
    have hterm :
        stoppedValue (shiftedCapitalExponentialProcess Y θStar k₀)
          (fun ω ↦ (τN ω : ℕ∞)) ω = 1 := by
      -- After rewriting the stopped value as evaluation, the exponential collapses at level `0`.
      calc
        stoppedValue (shiftedCapitalExponentialProcess Y θStar k₀)
            (fun ω ↦ (τN ω : ℕ∞)) ω =
          shiftedCapitalExponentialProcess Y θStar k₀ (τN ω) ω := hτN_evalω
        _ = 1 := by
          dsimp [shiftedCapitalExponentialProcess]
          rw [hcapital_zero]
          simp
    simpa [hhit_mem, shiftedExponentialRemainder] using hterm
  · have hnohit :
      ¬ ∃ j ≤ N, shiftedCapitalProcess Y k₀ j ω = 0 := by
      simpa [finiteShiftedHitEvent] using hhit
    have hτN_eq : τN ω = N := by
      -- On the no-hit slice, the bounded hitting time never finds `0`, so it returns the endpoint.
      dsimp [τN]
      rw [hittingBtwn, if_neg]
      intro hexists
      apply hnohit
      rcases hexists with ⟨j, hj, hj0⟩
      exact ⟨j, hj.2, by simpa [Set.mem_singleton_iff] using hj0⟩
    have hτN_evalω :
        stoppedValue (shiftedCapitalExponentialProcess Y θStar k₀)
            (fun ω ↦ (τN ω : ℕ∞)) ω =
          shiftedCapitalExponentialProcess Y θStar k₀ (τN ω) ω := by
      simpa using congrFun hτN_eval ω
    have hterm :
        stoppedValue (shiftedCapitalExponentialProcess Y θStar k₀)
          (fun ω ↦ (τN ω : ℕ∞)) ω =
          shiftedCapitalExponentialProcess Y θStar k₀ N ω := by
      -- After the no-hit normalization, the stopped process is just the terminal stage `N`.
      simpa [hτN_eq] using hτN_evalω
    simpa [hhit, shiftedExponentialRemainder, hτN_eq] using hterm

/-- Helper for Exercise 10.2.2: optional stopping at the first hit of `0` before time `N`
expresses the bounded-horizon hit probability as the initial exponential capital minus the
no-hit remainder term. -/
private theorem finiteShiftedHitEvent_probability_eq_initial_sub_remainder {θStar : ℝ} {k₀ : ℕ}
    (hY_meas : ∀ n, Measurable (Y n))
    (hY_indep : iIndepFun Y μ) (hY_ident : ∀ n, IdentDistrib (Y n) (Y 0) μ μ)
    (hY_exp_int : ∀ ϑ ∈ Set.Ioo (-δ) δ, Integrable (fun ω ↦ Real.exp (ϑ * Y 0 ω)) μ)
    (hθStar : θStar ∈ Set.Ioo (-δ) δ) (hroot : cgf (Y 0) μ θStar = 0) (N : ℕ) :
    μ.real (finiteShiftedHitEvent Y k₀ N) =
      Real.exp (θStar * ((k₀ : ℝ) + 1)) -
        ∫ ω, shiftedExponentialRemainder Y θStar k₀ N ω ∂μ := by
  let τN : Ω → ℕ := fun ω ↦ hittingBtwn (shiftedCapitalProcess Y k₀) ({0} : Set ℝ) 0 N ω
  let τs : Ω → ℕ∞ := fun ω ↦ (τN ω : ℕ∞)
  let A : Set Ω := finiteShiftedHitEvent Y k₀ N
  let X : ℕ → Ω → ℝ := shiftedCapitalExponentialProcess Y θStar k₀
  let ℱ : Filtration ℕ ‹MeasurableSpace Ω› :=
    Filtration.natural S (partialSumStronglyMeasurable (Y := Y) hY_meas)
  have hA_meas : MeasurableSet A :=
    finiteShiftedHitEvent_measurable (Y := Y) (hY_meas := hY_meas) (k₀ := k₀) N
  have hX_mart : Martingale X ℱ μ := by
    simpa [ℱ, X] using
      shiftedCapitalExponentialProcess_martingale (Y := Y) (μ := μ) (hY_meas := hY_meas)
        (δ := δ) (k₀ := k₀) hY_indep hY_ident (hY_exp_int θStar hθStar) hθStar hroot
  have hX_adapted : Adapted ℱ (shiftedCapitalProcess Y k₀) := by
    let hS : Adapted ℱ (partialSum Y) :=
      (Filtration.stronglyAdapted_natural
        (u := partialSum Y) (hum := partialSumStronglyMeasurable (Y := Y) hY_meas)).adapted
    intro n
    -- Each shifted capital value is the visible partial sum plus a deterministic offset.
    simpa [ℱ, shiftedCapitalProcess] using (hS n).add measurable_const
  have hτ : IsStoppingTime ℱ τs := by
    -- The bounded zero-hitting time is a stopping time because the shifted capital is adapted.
    simpa [τs, τN] using
      hX_adapted.isStoppingTime_hittingBtwn (measurableSet_singleton 0)
  have hτ_le : ∀ ω, τs ω ≤ N := by
    intro ω
    have hω :
        hittingBtwn (shiftedCapitalProcess Y k₀) ({0} : Set ℝ) 0 N ω ≤ N :=
      hittingBtwn_le ω
    -- Convert the nat-valued bounded hitting time into the `ℕ∞` bound required by optional stopping.
    change ((τN ω : ℕ∞) ≤ (N : ℕ∞))
    exact_mod_cast hω
  have hexpected_stopped :
      ∫ ω, stoppedValue X τs ω ∂μ = Real.exp (θStar * ((k₀ : ℝ) + 1)) := by
    -- Route correction: first use bounded optional stopping at `τN`, then collapse the
    -- deterministic time-`0` stopped value to the initial exponential capital.
    calc
      ∫ ω, stoppedValue X τs ω ∂μ =
          ∫ ω, stoppedValue X (fun _ ↦ (0 : ℕ∞)) ω ∂μ := by
            exact martingale_expected_stoppedValue_eq_of_le_of_bounded
              (X := X) (μ := μ) (ℱ := ℱ) hX_mart (isStoppingTime_const ℱ 0) hτ
              (fun ω ↦ by simp [τs]) hτ_le
      _ = Real.exp (θStar * ((k₀ : ℝ) + 1)) := by
        change ∫ ω, X 0 ω ∂μ = Real.exp (θStar * ((k₀ : ℝ) + 1))
        simp [X, shiftedCapitalExponentialProcess, shiftedCapitalProcess, partialSum]
  have hrepr_integral :
      ∫ ω, stoppedValue X τs ω ∂μ =
        μ.real A + ∫ ω, shiftedExponentialRemainder Y θStar k₀ N ω ∂μ := by
    have hrepr :
        stoppedValue X τs =
          fun ω ↦ A.indicator (fun _ ↦ (1 : ℝ)) ω +
            shiftedExponentialRemainder Y θStar k₀ N ω := by
      -- Rewrite the stopped value into the hit indicator plus the terminal no-hit remainder.
      simpa [A, X, τs, τN] using
        (stoppedShiftedCapitalExponential_repr (Y := Y) (θStar := θStar) (k₀ := k₀) N)
    calc
      ∫ ω, stoppedValue X τs ω ∂μ =
          ∫ ω,
            (A.indicator (fun _ ↦ (1 : ℝ)) ω +
              shiftedExponentialRemainder Y θStar k₀ N ω) ∂μ := by
            rw [hrepr]
      _ =
          ∫ ω, A.indicator (fun _ ↦ (1 : ℝ)) ω ∂μ +
            ∫ ω, shiftedExponentialRemainder Y θStar k₀ N ω ∂μ := by
              rw [integral_add]
              · exact (integrable_const (1 : ℝ)).indicator hA_meas
              · simpa [A, X, shiftedExponentialRemainder] using
                  (hX_mart.integrable N).indicator hA_meas.compl
      _ = μ.real A + ∫ ω, shiftedExponentialRemainder Y θStar k₀ N ω ∂μ := by
        rw [integral_indicator_const (1 : ℝ) hA_meas]
        simp [A, smul_eq_mul]
  -- Compare the optional-stopping expectation with the explicit hit/no-hit decomposition.
  linarith [hexpected_stopped, hrepr_integral]

/-- Helper for Exercise 10.2.2: if a nearest-neighbor path has not hit `0` by time `N`, then the
shifted capital at time `N` is at least `1`. -/
private theorem shiftedCapital_one_le_of_noFiniteHit {ω : Ω} {k₀ N : ℕ}
    (hω : ∀ n, Y n ω = -1 ∨ Y n ω = 1)
    (hnohit : ω ∉ finiteShiftedHitEvent Y k₀ N) :
    1 ≤ shiftedCapitalProcess Y k₀ N ω := by
  have hnonneg : 0 ≤ shiftedCapitalProcess Y k₀ N ω := by
    by_contra hneg
    have hruin : ∃ n ≤ N, partialSum Y n ω + (k₀ : ℝ) < 0 := by
      refine ⟨N, le_rfl, ?_⟩
      dsimp [shiftedCapitalProcess] at hneg
      linarith
    rcases
        (finiteRuin_iff_shiftedHitZero_of_twoPoint
          (Y := Y) (ω := ω) (k₀ := k₀) (N := N) hω).1 hruin with
      ⟨n, hn, hzero⟩
    exact hnohit ⟨n, hn, hzero⟩
  have hne_zero : shiftedCapitalProcess Y k₀ N ω ≠ 0 := by
    intro hzero
    exact hnohit ⟨N, le_rfl, hzero⟩
  rcases partialSum_integerValued_of_twoPoint (Y := Y) (ω := ω) hω N with ⟨z, hz⟩
  let m : ℤ := z + (k₀ + 1)
  have hm : shiftedCapitalProcess Y k₀ N ω = (m : ℝ) := by
    dsimp [shiftedCapitalProcess, m]
    rw [hz, Int.cast_add]
    norm_num
  have hm_nonneg : 0 ≤ m := by
    have hm_real : 0 ≤ (m : ℝ) := by
      simpa [hm] using hnonneg
    exact_mod_cast hm_real
  have hm_ne_zero : m ≠ 0 := by
    intro hm_zero
    apply hne_zero
    simpa [hm_zero] using hm
  have hm_pos : 1 ≤ m := by
    omega
  have hm_pos_real : (1 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hm_pos
  simpa [hm] using hm_pos_real

/-- Helper for Exercise 10.2.2: in the measurable nearest-neighbor setting, the no-hit remainder
integrals vanish by dominated convergence. -/
private theorem shiftedExponentialRemainder_tendsto_zero_of_measurable {θStar : ℝ} {k₀ : ℕ}
    (hY_meas : ∀ n, Measurable (Y n))
    (hY_indep : iIndepFun Y μ) (hY_ident : ∀ n, IdentDistrib (Y n) (Y 0) μ μ)
    (hY_mean_pos : 0 < μ[Y 0]) (hθStar : θStar ∈ Set.Ioo (-δ) δ)
    (hroot : cgf (Y 0) μ θStar = 0) (hθStar_ne : θStar ≠ 0)
    (h_two_point : ∀ n, ∀ᵐ ω ∂μ, Y n ω = -1 ∨ Y n ω = 1)
    (hY_exp_int : ∀ ϑ ∈ Set.Ioo (-δ) δ, Integrable (fun ω ↦ Real.exp (ϑ * Y 0 ω)) μ)
    (hY_not_ae_const : ¬ ∃ c : ℝ, Y 0 =ᵐ[μ] fun _ ↦ c) :
    Filter.Tendsto
      (fun N ↦ ∫ ω, shiftedExponentialRemainder Y θStar k₀ N ω ∂μ)
      Filter.atTop (nhds 0) := by
  have hθStar_neg : θStar < 0 :=
    cgf_root_neg_of_mean_pos (Y := Y) (μ := μ) (δ := δ) hY_exp_int hY_mean_pos
      hθStar hroot hθStar_ne
  have hAllSigns : ∀ᵐ ω ∂μ, ∀ n, Y n ω = -1 ∨ Y n ω = 1 := by
    simpa using (ae_all_iff.2 h_two_point)
  have hF_meas :
      ∀ N, AEStronglyMeasurable (shiftedExponentialRemainder Y θStar k₀ N) μ := by
    intro N
    -- The remainder is the indicator of a measurable no-hit slice applied to a measurable stage.
    have hNoHit_meas : MeasurableSet (finiteShiftedHitEvent Y k₀ N)ᶜ :=
      (finiteShiftedHitEvent_measurable (Y := Y) (hY_meas := hY_meas) (k₀ := k₀) N).compl
    have hMeas : Measurable (shiftedExponentialRemainder Y θStar k₀ N) := by
      simpa [shiftedExponentialRemainder] using
        (shiftedCapitalExponentialProcessMeasurable (Y := Y) hY_meas (θStar := θStar)
          (k₀ := k₀) N).indicator hNoHit_meas
    exact hMeas.aestronglyMeasurable
  have hF_bound :
      ∀ N, ∀ᵐ ω ∂μ, ‖shiftedExponentialRemainder Y θStar k₀ N ω‖ ≤ 1 := by
    intro N
    filter_upwards [hAllSigns] with ω hω
    by_cases hhit : ω ∈ finiteShiftedHitEvent Y k₀ N
    · simp [shiftedExponentialRemainder, hhit]
    · have hcap :
          1 ≤ shiftedCapitalProcess Y k₀ N ω :=
        shiftedCapital_one_le_of_noFiniteHit (Y := Y) (ω := ω) (k₀ := k₀) (N := N) hω hhit
      have hexp_le :
          Real.exp (θStar * shiftedCapitalProcess Y k₀ N ω) ≤ 1 := by
        refine Real.exp_le_one_iff.mpr ?_
        nlinarith [hθStar_neg, hcap]
      have hnonneg :
          0 ≤ shiftedExponentialRemainder Y θStar k₀ N ω := by
        simp [shiftedExponentialRemainder, hhit, shiftedCapitalExponentialProcess]
        positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      simpa [shiftedExponentialRemainder, hhit, shiftedCapitalExponentialProcess] using hexp_le
  have hF_tendsto :
      ∀ᵐ ω ∂μ, Filter.Tendsto
        (fun N ↦ shiftedExponentialRemainder Y θStar k₀ N ω) Filter.atTop (nhds 0) := by
    filter_upwards
        [hAllSigns,
          shiftedCapitalExponentialProcess_tendsto_zero_ae (Y := Y) (μ := μ) (δ := δ)
            (k₀ := k₀) hY_indep hY_ident hY_not_ae_const hY_exp_int hθStar hθStar_ne hroot]
        with ω hω hdecay
    by_cases hhit : ω ∈ shiftedHitEvent Y k₀
    · rcases hhit with ⟨M, hM⟩
      have hEventuallyZero :
          (fun N ↦ shiftedExponentialRemainder Y θStar k₀ N ω) =ᶠ[Filter.atTop] fun _ ↦ 0 := by
        refine Filter.eventually_atTop.2 ?_
        refine ⟨M, fun N hMN ↦ ?_⟩
        have hfinite : ω ∈ finiteShiftedHitEvent Y k₀ N := ⟨M, hMN, hM⟩
        simp [shiftedExponentialRemainder, hfinite]
      exact Filter.Tendsto.congr' hEventuallyZero.symm tendsto_const_nhds
    · have hNoFinite : ∀ N, ω ∉ finiteShiftedHitEvent Y k₀ N := by
        intro N hfinite
        rcases hfinite with ⟨n, hn, hzero⟩
        exact hhit ⟨n, hzero⟩
      have hEq :
          (fun N ↦ shiftedExponentialRemainder Y θStar k₀ N ω) =
            fun N ↦ shiftedCapitalExponentialProcess Y θStar k₀ N ω := by
        funext N
        simp [shiftedExponentialRemainder, hNoFinite N]
      exact Filter.Tendsto.congr' (Filter.EventuallyEq.of_eq hEq).symm hdecay
  -- Route correction: do the dominated-convergence step in the measurable world and keep the raw
  -- process out of the final limit computation.
  simpa using
    MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun _ ↦ (1 : ℝ))
      hF_meas
      (integrable_const (1 : ℝ))
      hF_bound
      hF_tendsto

/-- Helper for Exercise 10.2.2: in the measurable nearest-neighbor case, the bounded-horizon
stopping identity and the vanishing remainder assemble into the sharp ruin formula. -/
private theorem ruinProbability_eq_exp_cgf_root_of_two_point_steps_of_measurable {θStar : ℝ}
    {k₀ : ℕ} (hY_meas : ∀ n, Measurable (Y n))
    (hY_indep : iIndepFun Y μ) (hY_ident : ∀ n, IdentDistrib (Y n) (Y 0) μ μ)
    (hY_mean_pos : 0 < μ[Y 0]) (hθStar : θStar ∈ Set.Ioo (-δ) δ)
    (hroot : cgf (Y 0) μ θStar = 0) (hθStar_ne : θStar ≠ 0)
    (h_two_point : ∀ n, ∀ᵐ ω ∂μ, Y n ω = -1 ∨ Y n ω = 1) :
    ruinProbability Y μ k₀ = Real.exp (θStar * ((k₀ : ℝ) + 1)) := by
  have hY_exp_int :
      ∀ ϑ ∈ Set.Ioo (-δ) δ, Integrable (fun ω ↦ Real.exp (ϑ * Y 0 ω)) μ := by
    intro ϑ hϑ
    have hExp_meas : AEStronglyMeasurable (fun ω ↦ Real.exp (ϑ * Y 0 ω)) μ := by
      exact
        (show Measurable (fun ω ↦ Real.exp (ϑ * Y 0 ω)) by
          fun_prop).aestronglyMeasurable
    have hExp_bound :
        ∀ᵐ ω ∂μ, ‖Real.exp (ϑ * Y 0 ω)‖ ≤ max (Real.exp (-ϑ)) (Real.exp ϑ) := by
      filter_upwards [h_two_point 0] with ω hω
      rcases hω with hω | hω
      · simpa [Real.norm_eq_abs, hω] using
          (le_max_left (Real.exp (-ϑ)) (Real.exp ϑ))
      · simpa [Real.norm_eq_abs, hω] using
          (le_max_right (Real.exp (-ϑ)) (Real.exp ϑ))
    -- The `±1` support turns every exponential moment into a bounded measurable function.
    exact Integrable.mono' (integrable_const (max (Real.exp (-ϑ)) (Real.exp ϑ))) hExp_meas
      hExp_bound
  have hY_not_ae_const : ¬ ∃ c : ℝ, Y 0 =ᵐ[μ] fun _ ↦ c := by
    intro hconst
    rcases hconst with ⟨c, hc⟩
    have hmean_eq : μ[Y 0] = c := by
      calc
        μ[Y 0] = ∫ ω, c ∂μ := by
          simpa using integral_congr_ae hc
        _ = c := by
          simp
    have hmgf_const : mgf (Y 0) μ θStar = Real.exp (θStar * c) := by
      have hexp_eq :
          (fun ω ↦ Real.exp (θStar * Y 0 ω)) =ᵐ[μ] fun _ ↦ Real.exp (θStar * c) := by
        filter_upwards [hc] with ω hω
        simp [hω]
      calc
        mgf (Y 0) μ θStar = ∫ ω, Real.exp (θStar * c) ∂μ := by
          simpa [ProbabilityTheory.mgf] using integral_congr_ae hexp_eq
        _ = Real.exp (θStar * c) := by
          simp
    have hcgf_const : cgf (Y 0) μ θStar = θStar * c := by
      rw [ProbabilityTheory.cgf, hmgf_const, Real.log_exp]
    have hc_zero : c = 0 := by
      have hmul_zero : θStar * c = 0 := by
        linarith [hroot, hcgf_const]
      exact (mul_eq_zero.mp hmul_zero).resolve_left hθStar_ne
    linarith [hY_mean_pos, hmean_eq, hc_zero]
  have hHitEvent_eq_iUnion :
      shiftedHitEvent Y k₀ = ⋃ N, finiteShiftedHitEvent Y k₀ N := by
    ext ω
    constructor
    · rintro ⟨n, hzero⟩
      exact Set.mem_iUnion.2 ⟨n, ⟨n, le_rfl, hzero⟩⟩
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨N, hN⟩
      rcases hN with ⟨n, hn, hzero⟩
      exact ⟨n, hzero⟩
  let A : ℕ → Set Ω := fun N ↦ finiteShiftedHitEvent Y k₀ N
  have hA_mono : Monotone A := by
    intro m n hmn ω hω
    rcases hω with ⟨j, hjm, hzero⟩
    exact ⟨j, Nat.le_trans hjm hmn, hzero⟩
  have hHit_finite : μ (shiftedHitEvent Y k₀) < ⊤ := by
    calc
      μ (shiftedHitEvent Y k₀) ≤ μ Set.univ := measure_mono (Set.subset_univ _)
      _ = (1 : ENNReal) := by simp
      _ < ⊤ := by simp
  have hA_tendsto :
      Filter.Tendsto (fun N ↦ μ.real (A N)) Filter.atTop (nhds (μ.real (shiftedHitEvent Y k₀))) := by
    have hμ_tendsto : Filter.Tendsto (μ ∘ A) Filter.atTop (nhds (μ (⋃ N, A N))) :=
      tendsto_measure_iUnion_atTop hA_mono
    rw [← hHitEvent_eq_iUnion] at hμ_tendsto
    change Filter.Tendsto (fun N ↦ μ (A N)) Filter.atTop (nhds (μ (shiftedHitEvent Y k₀))) at hμ_tendsto
    rw [← ENNReal.tendsto_toReal_iff
      (fun N ↦ ne_top_of_le_ne_top hHit_finite.ne
        (measure_mono (show A N ⊆ shiftedHitEvent Y k₀ by
          intro ω hω
          rcases hω with ⟨n, hn, hzero⟩
          exact ⟨n, hzero⟩)))
      hHit_finite.ne] at hμ_tendsto
    simpa [A, Measure.real_def] using hμ_tendsto
  have hRemainder_tendsto :
      Filter.Tendsto
        (fun N ↦ ∫ ω, shiftedExponentialRemainder Y θStar k₀ N ω ∂μ)
        Filter.atTop (nhds 0) :=
    shiftedExponentialRemainder_tendsto_zero_of_measurable (Y := Y) (μ := μ) (δ := δ) hY_meas
      hY_indep hY_ident hY_mean_pos hθStar hroot hθStar_ne h_two_point hY_exp_int
      hY_not_ae_const
  have hA_formula_tendsto :
      Filter.Tendsto (fun N ↦ μ.real (A N)) Filter.atTop
        (nhds (Real.exp (θStar * ((k₀ : ℝ) + 1)))) := by
    have hconst_sub :
        Filter.Tendsto
          (fun N ↦
            Real.exp (θStar * ((k₀ : ℝ) + 1)) -
              ∫ ω, shiftedExponentialRemainder Y θStar k₀ N ω ∂μ)
          Filter.atTop
          (nhds (Real.exp (θStar * ((k₀ : ℝ) + 1)) - 0)) := by
      simpa using (tendsto_const_nhds.sub hRemainder_tendsto)
    have hA_formula :
        (fun N ↦ μ.real (A N)) =
          fun N ↦
            Real.exp (θStar * ((k₀ : ℝ) + 1)) -
              ∫ ω, shiftedExponentialRemainder Y θStar k₀ N ω ∂μ := by
      funext N
      simpa [A] using
        finiteShiftedHitEvent_probability_eq_initial_sub_remainder
          (Y := Y) (μ := μ) (δ := δ) (k₀ := k₀) hY_meas hY_indep hY_ident hY_exp_int
          hθStar hroot N
    -- Compare the finite-horizon hit probabilities with the stopped exponential identity.
    rw [hA_formula]
    simpa using hconst_sub
  have hHit_real :
      μ.real (shiftedHitEvent Y k₀) = Real.exp (θStar * ((k₀ : ℝ) + 1)) := by
    exact tendsto_nhds_unique hA_tendsto hA_formula_tendsto
  have hAllSigns : ∀ᵐ ω ∂μ, ∀ n, Y n ω = -1 ∨ Y n ω = 1 := by
    simpa using (ae_all_iff.2 h_two_point)
  have hRuin_eq :
      {ω | ∃ n : ℕ, partialSum Y n ω + (k₀ : ℝ) < 0} =ᵐ[μ] shiftedHitEvent Y k₀ := by
    filter_upwards [hAllSigns] with ω hω
    apply propext
    constructor
    · rintro ⟨n, hruin⟩
      rcases
          (finiteRuin_iff_shiftedHitZero_of_twoPoint
            (Y := Y) (ω := ω) (k₀ := k₀) (N := n) hω).1 ⟨n, le_rfl, hruin⟩ with
        ⟨m, hm, hzero⟩
      exact ⟨m, hzero⟩
    · rintro ⟨n, hzero⟩
      refine ⟨n, ?_⟩
      dsimp [shiftedCapitalProcess] at hzero
      linarith
  -- Route correction: first identify strict ruin with shifted hit almost surely, then use the
  -- measurable finite-horizon formula and the remainder limit to pass to infinite horizon.
  calc
    ruinProbability Y μ k₀ = μ.real {ω | ∃ n : ℕ, partialSum Y n ω + (k₀ : ℝ) < 0} := by
      rfl
    _ = μ.real (shiftedHitEvent Y k₀) := by
      rw [Measure.real_def, measure_congr hRuin_eq, Measure.real_def]
    _ = Real.exp (θStar * ((k₀ : ℝ) + 1)) := hHit_real

/-- Helper for Exercise 10.2.2: the no-hit remainder term tends to `0` because it is dominated by
`1` and agrees eventually either with `0` or with the shifted exponential process. -/
private theorem shiftedExponentialRemainder_tendsto_zero {θStar : ℝ} {k₀ : ℕ}
    (hY_indep : iIndepFun Y μ) (hY_ident : ∀ n, IdentDistrib (Y n) (Y 0) μ μ)
    (hY_mean_pos : 0 < μ[Y 0]) (hθStar : θStar ∈ Set.Ioo (-δ) δ)
    (hroot : cgf (Y 0) μ θStar = 0) (hθStar_ne : θStar ≠ 0)
    (h_two_point : ∀ n, ∀ᵐ ω ∂μ, Y n ω = -1 ∨ Y n ω = 1)
    (hY_exp_int : ∀ ϑ ∈ Set.Ioo (-δ) δ, Integrable (fun ω ↦ Real.exp (ϑ * Y 0 ω)) μ)
    (hY_not_ae_const : ¬ ∃ c : ℝ, Y 0 =ᵐ[μ] fun _ ↦ c) :
    Filter.Tendsto
      (fun N ↦ ∫ ω, shiftedExponentialRemainder Y θStar k₀ N ω ∂μ)
      Filter.atTop (nhds 0) := by
  let Ym : ℕ → Ω → ℝ := fun n ↦ (hY_ident n).aemeasurable_fst.mk (Y n)
  have hYm_eq : ∀ n, Y n =ᵐ[μ] Ym n := by
    intro n
    simpa [Ym] using (hY_ident n).aemeasurable_fst.ae_eq_mk
  have hYm_meas : ∀ n, Measurable (Ym n) := by
    intro n
    simpa [Ym] using (hY_ident n).aemeasurable_fst.measurable_mk
  have hYm_indep : iIndepFun Ym μ := by
    exact hY_indep.congr hYm_eq
  have hYm_ident : ∀ n, IdentDistrib (Ym n) (Ym 0) μ μ := by
    intro n
    have hYnYm : IdentDistrib (Y n) (Ym n) μ μ := by
      simpa [Ym] using ((hY_ident n).aemeasurable_fst).identDistrib_mk
    have hY0Ym0 : IdentDistrib (Y 0) (Ym 0) μ μ := by
      simpa [Ym] using ((hY_ident 0).aemeasurable_fst).identDistrib_mk
    exact hYnYm.symm.trans ((hY_ident n).trans hY0Ym0)
  have hYm_exp_int :
      ∀ ϑ ∈ Set.Ioo (-δ) δ, Integrable (fun ω ↦ Real.exp (ϑ * Ym 0 ω)) μ := by
    intro ϑ hϑ
    refine (hY_exp_int ϑ hϑ).congr ?_
    filter_upwards [hYm_eq 0] with ω hω
    simp [hω]
  have hYm_not_ae_const : ¬ ∃ c : ℝ, Ym 0 =ᵐ[μ] fun _ ↦ c := by
    intro hconst
    rcases hconst with ⟨c, hc⟩
    exact hY_not_ae_const ⟨c, (hYm_eq 0).trans hc⟩
  have hYm_mean_pos : 0 < μ[Ym 0] := by
    -- The measurable modification does not change the first increment's expectation.
    exact mean_pos_of_ae_eq (μ := μ) (hYm_eq 0) hY_mean_pos
  have hYm_root : cgf (Ym 0) μ θStar = 0 := by
    -- The cgf root is invariant under the a.e. measurable replacement.
    exact (cgf_eq_of_ae_eq (μ := μ) (hYm_eq 0) θStar).symm.trans hroot
  have hYm_two_point : ∀ n, ∀ᵐ ω ∂μ, Ym n ω = -1 ∨ Ym n ω = 1 := by
    -- The `±1` support condition also transports along the measurable modification.
    exact twoPoint_ae_of_ae_eq (μ := μ) hYm_eq h_two_point
  have hpartial_ae :
      ∀ᵐ ω ∂μ, ∀ n, partialSum Y n ω = partialSum Ym n ω :=
    partialSum_ae_eq_of_incrementModification (μ := μ) hYm_eq
  have hRemainder_eq :
      ∀ N, shiftedExponentialRemainder Y θStar k₀ N =ᵐ[μ]
        shiftedExponentialRemainder Ym θStar k₀ N := by
    intro N
    filter_upwards [hpartial_ae] with ω hω
    have hfinite_eq :
        ω ∈ finiteShiftedHitEvent Y k₀ N ↔ ω ∈ finiteShiftedHitEvent Ym k₀ N := by
      constructor
      · rintro ⟨n, hn, hzero⟩
        refine ⟨n, hn, ?_⟩
        simpa [shiftedCapitalProcess, hω n] using hzero
      · rintro ⟨n, hn, hzero⟩
        refine ⟨n, hn, ?_⟩
        simpa [shiftedCapitalProcess, hω n] using hzero
    by_cases hhit : ω ∈ finiteShiftedHitEvent Y k₀ N
    · have hhitYm : ω ∈ finiteShiftedHitEvent Ym k₀ N := hfinite_eq.mp hhit
      simp [shiftedExponentialRemainder, hhit, hhitYm]
    · have hhitYm : ω ∉ finiteShiftedHitEvent Ym k₀ N := by
        intro hmem
        exact hhit (hfinite_eq.mpr hmem)
      simp [shiftedExponentialRemainder, hhit, hhitYm, shiftedCapitalExponentialProcess,
        shiftedCapitalProcess, hω N]
  -- Route correction: move the remainder limit to the measurable modification and transport the
  -- integrals back through the partial-sum a.e. equality.
  have hIntegral_eq :
      (fun N ↦ ∫ ω, shiftedExponentialRemainder Y θStar k₀ N ω ∂μ) =
        fun N ↦ ∫ ω, shiftedExponentialRemainder Ym θStar k₀ N ω ∂μ := by
    funext N
    exact integral_congr_ae (hRemainder_eq N)
  rw [hIntegral_eq]
  exact
    shiftedExponentialRemainder_tendsto_zero_of_measurable (Y := Ym) (μ := μ) (δ := δ)
      (k₀ := k₀) hYm_meas hYm_indep hYm_ident hYm_mean_pos hθStar hYm_root hθStar_ne
      hYm_two_point hYm_exp_int hYm_not_ae_const

/-- Helper for Exercise 10.2.2: choose the measurable representative of each increment provided by
the identical-distribution witness with the reference increment `Y 0`. -/
private def measurableIncrementRepresentative
    (Y : ℕ → Ω → ℝ) (μ : Measure Ω)
    (hY_ident : ∀ n, IdentDistrib (Y n) (Y 0) μ μ) : ℕ → Ω → ℝ :=
  fun n ↦ (hY_ident n).aemeasurable_fst.mk (Y n)

/-- Helper for Exercise 10.2.2: the chosen measurable representative agrees almost everywhere with
the original increment process. -/
private theorem ae_eq_measurableIncrementRepresentative
    (hY_ident : ∀ n, IdentDistrib (Y n) (Y 0) μ μ) :
    ∀ n, Y n =ᵐ[μ] measurableIncrementRepresentative Y μ hY_ident n := by
  intro n
  -- The measurable representative is obtained by modifying only on a null set.
  simpa [measurableIncrementRepresentative] using (hY_ident n).aemeasurable_fst.ae_eq_mk

/-- Helper for Exercise 10.2.2: the chosen representative process is genuinely measurable in each
coordinate. -/
private theorem measurable_measurableIncrementRepresentative
    (hY_ident : ∀ n, IdentDistrib (Y n) (Y 0) μ μ) :
    ∀ n, Measurable (measurableIncrementRepresentative Y μ hY_ident n) := by
  intro n
  -- The representative is built from the measurable version attached to `IdentDistrib`.
  simpa [measurableIncrementRepresentative] using (hY_ident n).aemeasurable_fst.measurable_mk

/-- Helper for Exercise 10.2.2: replacing each increment by the measurable representative keeps
the family identically distributed with the time-`0` representative. -/
private theorem identDistrib_measurableIncrementRepresentative
    (hY_ident : ∀ n, IdentDistrib (Y n) (Y 0) μ μ) :
    ∀ n,
      IdentDistrib
        (measurableIncrementRepresentative Y μ hY_ident n)
        (measurableIncrementRepresentative Y μ hY_ident 0) μ μ := by
  intro n
  have hYnYm :
      IdentDistrib (Y n) (measurableIncrementRepresentative Y μ hY_ident n) μ μ := by
    -- Each representative is still identically distributed with the original increment.
    simpa [measurableIncrementRepresentative] using
      ((hY_ident n).aemeasurable_fst).identDistrib_mk
  have hY0Ym0 :
      IdentDistrib (Y 0) (measurableIncrementRepresentative Y μ hY_ident 0) μ μ := by
    -- Apply the same measurable-representative construction at the reference coordinate `0`.
    simpa [measurableIncrementRepresentative] using
      ((hY_ident 0).aemeasurable_fst).identDistrib_mk
  -- Compare both measurable representatives through the original identical-distribution chain.
  exact hYnYm.symm.trans ((hY_ident n).trans hY0Ym0)

/-- Exercise 10.2.2 (7): in the special `±1`-valued case with integer initial capital, the
Cramér-Lundberg inequality is sharp, recovering the classical exact ruin formula with
`r = exp θ⋆`; because `ruinProbability` here records the event that the capital process becomes
strictly negative, the exact formula carries the expected one-step shift. -/
-- Proof sketch: specialize the stopped-exponential-martingale argument to the nearest-neighbor
-- random walk, where the required exponential moments are automatic, identify the stopped process
-- at ruin exactly, and solve the resulting two-point recursion to turn the upper bound into the
-- exact formula for hitting the negative half-line, equivalently for hit-`0` ruin after shifting
-- the initial capital from `k₀` to `k₀ + 1`.
theorem ruinProbability_eq_exp_cgf_root_of_two_point_steps {θStar : ℝ} {k₀ : ℕ}
    (hY_indep : iIndepFun Y μ) (hY_ident : ∀ n, IdentDistrib (Y n) (Y 0) μ μ)
    (hY_mean_pos : 0 < μ[Y 0]) (hθStar : θStar ∈ Set.Ioo (-δ) δ)
    (hroot : cgf (Y 0) μ θStar = 0) (hθStar_ne : θStar ≠ 0)
    (h_two_point : ∀ n, ∀ᵐ ω ∂μ, Y n ω = -1 ∨ Y n ω = 1) :
    ruinProbability Y μ k₀ = Real.exp (θStar * ((k₀ : ℝ) + 1)) := by
  let Ym : ℕ → Ω → ℝ := measurableIncrementRepresentative Y μ hY_ident
  have hYm_eq : ∀ n, Y n =ᵐ[μ] Ym n := by
    -- The measurable representative changes each increment only on a null set.
    simpa [Ym] using ae_eq_measurableIncrementRepresentative (Y := Y) (μ := μ) hY_ident
  have hYm_meas : ∀ n, Measurable (Ym n) := by
    -- The extracted helper packages measurability of the representative family.
    simpa [Ym] using measurable_measurableIncrementRepresentative (Y := Y) (μ := μ) hY_ident
  have hYm_indep : iIndepFun Ym μ := by
    exact hY_indep.congr hYm_eq
  have hYm_ident : ∀ n, IdentDistrib (Ym n) (Ym 0) μ μ := by
    -- The measurable replacement preserves the common increment law.
    simpa [Ym] using
      identDistrib_measurableIncrementRepresentative (Y := Y) (μ := μ) hY_ident
  have hYm_mean_pos : 0 < μ[Ym 0] := by
    -- The measurable modification leaves the first-step expectation unchanged.
    exact mean_pos_of_ae_eq (μ := μ) (hYm_eq 0) hY_mean_pos
  have hYm_root : cgf (Ym 0) μ θStar = 0 := by
    -- The cgf root survives passage to the measurable representative.
    exact (cgf_eq_of_ae_eq (μ := μ) (hYm_eq 0) θStar).symm.trans hroot
  have hYm_two_point : ∀ n, ∀ᵐ ω ∂μ, Ym n ω = -1 ∨ Ym n ω = 1 := by
    -- The measurable representative still takes only the values `-1` and `1` almost surely.
    exact twoPoint_ae_of_ae_eq (μ := μ) hYm_eq h_two_point
  -- Route correction: prove the sharp formula in the measurable modification and transport only
  -- the strict-ruin event back to the original process by a.e. equality of partial sums.
  calc
    ruinProbability Y μ k₀ = ruinProbability Ym μ k₀ := by
      exact ruinProbability_eq_of_incrementModification (μ := μ) hYm_eq (k₀ := (k₀ : ℝ))
    _ = Real.exp (θStar * ((k₀ : ℝ) + 1)) := by
      exact
        ruinProbability_eq_exp_cgf_root_of_two_point_steps_of_measurable
          (Y := Ym) (μ := μ) (δ := δ) hYm_meas hYm_indep hYm_ident hYm_mean_pos hθStar
          hYm_root hθStar_ne hYm_two_point

end
