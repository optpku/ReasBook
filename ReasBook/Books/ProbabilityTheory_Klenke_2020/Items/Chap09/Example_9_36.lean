/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Example_9_4
import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Definition_9_7
import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Exercise_2_3_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Example_9_13
import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Remark_9_29
import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Theorem_9_35

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

universe u

noncomputable section

variable {Ω : Type u} [MeasurableSpace Ω]

section

variable {P : Measure Ω} {X : ℕ → Ω → ℤ}

local notation "Xℝ" => fun n ω ↦ (X n ω : ℝ)

/-- Helper for Example 9.36: a variable with the symmetric Rademacher law gives mass `1 / 2`
to both singleton atoms `{-1}` and `{1}`. -/
private lemma hasLaw_symmetricRademacher_preimage_singletons
    (P : Measure Ω) (Y : Ω → ℤ) (hY : HasLaw Y symmetricRademacherLaw P) :
    P (Y ⁻¹' {(-1 : ℤ)}) = (2 : ℝ≥0∞)⁻¹ ∧
      P (Y ⁻¹' {(1 : ℤ)}) = (2 : ℝ≥0∞)⁻¹ := by
  constructor
  · -- Proof comment: transport the singleton mass through the pushforward law of `Y`.
    rw [← Measure.map_apply_of_aemeasurable hY.aemeasurable (measurableSet_singleton (-1 : ℤ))]
    rw [hY.map_eq]
    simp [symmetricRademacherLaw, one_div]
  · -- Proof comment: the singleton `{1}` mass is the owner theorem for the symmetric law.
    rw [← Measure.map_apply_of_aemeasurable hY.aemeasurable (measurableSet_singleton (1 : ℤ))]
    rw [hY.map_eq]
    simpa [one_div] using symmetricRademacherLaw_apply_singleton_one

/-- Helper for Example 9.36: the walk position `X n` is the partial sum of its increment process
`ω ↦ X (k + 1) ω - X k ω`. -/
private lemma symmetricSimpleRandomWalk_position_eq_partialSum
    {X : ℕ → Ω → ℤ} (hX_zero : X 0 = 0) :
    ∀ n ω,
      random_walk_partial_sum (fun k ω' ↦ X (k + 1) ω' - X k ω') n ω = X n ω := by
  intro n ω
  induction n with
  | zero =>
      -- Proof comment: the length-`0` partial sum is empty, so it matches the prescribed start.
      simp [random_walk_partial_sum, hX_zero]
  | succ n ih =>
      -- Proof comment: split off the last increment and telescope to recover the next position.
      rw [random_walk_partial_sum, Finset.sum_range_succ]
      have hsum : ∑ x ∈ Finset.range n, (X (x + 1) ω - X x ω) = X n ω := by
        simpa [random_walk_partial_sum] using ih
      rw [hsum]
      omega

/-- Helper for Example 9.36: casting the integer-valued random-walk partial sums to `ℝ` agrees
with the real partial sums of the cast increment family. -/
private lemma partialSum_intCast_eq_randomWalkPartialSum
    (Y : ℕ → Ω → ℤ) :
    ∀ n ω, partialSum (fun k ω' ↦ (Y k ω' : ℝ)) n ω = (random_walk_partial_sum Y n ω : ℝ) := by
  intro n ω
  -- Proof comment: both sides are the same finite sum, written before and after the integer cast.
  rw [partialSum_apply, random_walk_partial_sum]
  exact_mod_cast rfl

section PartialSumFiltration

variable {μ : Measure Ω} {Y : ℕ → Ω → ℝ}
variable (hY_meas : ∀ n, Measurable (Y n))

local notation "S" => partialSum Y

/-- Helper for Example 9.36: each real partial sum is strongly measurable when the increments are
measurable. -/
private theorem partialSumStronglyMeasurable
    (hY_meas : ∀ n, Measurable (Y n)) (n : ℕ) : StronglyMeasurable (S n) :=
  (partialSum_measurable Y hY_meas n).stronglyMeasurable

local notation "ℱY" =>
  Filtration.natural S (partialSumStronglyMeasurable hY_meas)

/-- Helper for Example 9.36: consecutive partial sums differ by the next increment. -/
private lemma partialSum_succ_sub (n : ℕ) (ω : Ω) :
    S (n + 1) ω - S n ω = Y n ω := by
  -- Proof comment: the tail between consecutive partial sums is the singleton `Ico` block.
  simpa using partialSum_sub_eq_sum_Ico Y (Nat.le_succ n) ω

/-- Helper for Example 9.36: the time-`0` natural filtration of the partial sums is trivial. -/
private lemma partialSumNaturalFiltration_zero :
    ℱY 0 = ⊥ := by
  -- Proof comment: rewrite the natural filtration as a generated filtration and use that
  -- `partialSum Y 0` is the constant zero process.
  rw [← generatedFiltration_eq_natural S (partialSumStronglyMeasurable hY_meas)]
  rw [generatedFiltration_apply]
  change (⨆ j ≤ 0, MeasurableSpace.comap (S j) (borel ℝ)) = ⊥
  have hconst : MeasurableSpace.comap (S 0) (borel ℝ) = ⊥ := by
    change MeasurableSpace.comap (fun _ : Ω ↦ (0 : ℝ)) (borel ℝ) = ⊥
    exact MeasurableSpace.comap_const 0
  simpa [hconst]

/-- Helper for Example 9.36: after discarding the trivial zeroth coordinate, the natural
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
      -- Proof comment: shifted partial sums generate the same past sigma-algebra as the increments.
      simpa [T] using congrArg (fun ℱ ↦ ℱ n)
        (partialSum_prefix_sigma_eq_increment_prefix_sigma Y hY_meas)
    _ = Filtration.natural Y (fun k ↦ (hY_meas k).stronglyMeasurable) n := by
      rw [generatedFiltration_eq_natural Y (fun k ↦ (hY_meas k).stronglyMeasurable)]

section

variable [IsProbabilityMeasure μ]

/-- Helper for Example 9.36: the conditional expectation of the next partial-sum increment is the
deterministic mean of the next independent increment. -/
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
        -- Proof comment: conditioning the first increment on the trivial sigma-algebra returns its mean.
        simpa [partialSumNaturalFiltration_zero (Y := Y) (hY_meas := hY_meas)] using
          (EventuallyEq.of_eq (MeasureTheory.condExp_bot (μ := μ) (f := Y 0)) :
            μ[Y 0 | ℱY 0] =ᵐ[μ] fun _ ↦ ∫ ξ, Y 0 ξ ∂μ)
      -- Proof comment: replace the first partial-sum increment by the first increment itself.
      refine (condExp_congr_ae (Filter.Eventually.of_forall fun ω ↦
        partialSum_succ_sub (Y := Y) 0 ω)).trans hbot
  | succ k =>
      have hnat :
          μ[Y (k + 1) | ℱinc k] =ᵐ[μ] fun _ ↦ ∫ ξ, Y (k + 1) ξ ∂μ := by
        -- Proof comment: the next increment is independent of the past increment filtration.
        simpa [ℱinc] using
          (ProbabilityTheory.iIndepFun.condExp_natural_ae_eq_of_lt
            (f := Y)
            (fun j ↦ (hY_meas j).stronglyMeasurable) hY_indep (Nat.lt_succ_self k))
      -- Proof comment: transport the increment-side formula to the natural filtration of partial sums.
      refine (condExp_congr_ae (Filter.Eventually.of_forall fun ω ↦
        partialSum_succ_sub (Y := Y) (k + 1) ω)).trans ?_
      simpa [ℱinc,
        partialSumNaturalFiltration_succ_eq_incrementNatural (Y := Y) (hY_meas := hY_meas) k] using
        hnat

end
end PartialSumFiltration

/-- Helper for Example 9.36: a fair-sign real increment has integrable square. -/
private lemma integrable_stepReal_sq_of_fairSigns
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : ℕ → Ω → ℤ) (hZ_meas : ∀ n, Measurable (Z n))
    (hZ_neg : ∀ n : ℕ, μ ((Z n) ⁻¹' {(-1 : ℤ)}) = (2 : ℝ≥0∞)⁻¹)
    (hZ_pos : ∀ n : ℕ, μ ((Z n) ⁻¹' {(1 : ℤ)}) = (2 : ℝ≥0∞)⁻¹)
    (n : ℕ) :
    Integrable (fun ω ↦ ((((Z n ω : ℤ) : ℝ)) ^ 2)) μ := by
  have hsquare :
      (fun ω ↦ ((((Z n ω : ℤ) : ℝ)) ^ 2)) =ᵐ[μ] fun _ ↦ (1 : ℝ) := by
    filter_upwards
      [ae_eq_negOne_or_eq_one_of_fairSigns (μ := μ) (X := Z) hZ_meas hZ_neg hZ_pos n] with ω hω
    rcases hω with hω | hω <;> simp [hω]
  -- Proof comment: on the fair-sign event, the square is the constant `1`.
  exact (integrable_const (1 : ℝ)).congr hsquare.symm

/-- Helper for Example 9.36: square-integrable increments give `L²` partial sums. -/
private lemma partialSumMemLpTwoOfSquareIntegrableIncrements
    {μ : Measure Ω} {Y : ℕ → Ω → ℝ}
    (hY_meas : ∀ n, Measurable (Y n))
    (hY_sq_int : ∀ n, Integrable (fun ω ↦ (Y n ω) ^ 2) μ) :
    ∀ n, MemLp (partialSum Y n) 2 μ := by
  intro n
  -- Proof comment: expand the partial sum and sum the `L²` bounds over the finite prefix.
  simpa [partialSum] using
    (memLp_finset_sum (Finset.range n) fun i _ ↦
      (memLp_two_iff_integrable_sq
        ((hY_meas i).stronglyMeasurable.aestronglyMeasurable)).2 (hY_sq_int i))

-- Proof sketch: view the integer-valued walk as a real-valued process. The symmetric `±1`
-- increments are centered and bounded, so the walk is a square-integrable martingale for the
-- filtration generated by its past values.
/-- Example 9.36 (1): a symmetric simple random walk on `ℤ`, viewed as a real-valued process,
is a square-integrable martingale with respect to its natural filtration. Here the symmetric
simple-random-walk assumptions are stated directly by `X 0 = 0`, measurability of each time
coordinate, and independent increments having the symmetric `{-1, 1}` law. -/
theorem symmetricSimpleRandomWalk_squareIntegrable_martingale
    (hX_zero : X 0 = 0)
    (hX_meas : ∀ n, Measurable (X n))
    (hX_indep : iIndepFun (fun n ω ↦ X (n + 1) ω - X n ω) P)
    (hX_law : ∀ n,
      HasLaw (fun ω ↦ X (n + 1) ω - X n ω) symmetricRademacherLaw P) :
    IsSquareIntegrableProcess Xℝ P ∧
      Martingale Xℝ
        (Filtration.natural Xℝ
          (fun n ↦
            Int.cast_continuous.comp_stronglyMeasurable
              ((hX_meas n).stronglyMeasurable)))
        P := by
  letI : IsProbabilityMeasure P := (hX_law 0).isProbabilityMeasure
  let Δ : ℕ → Ω → ℤ := fun n ω ↦ X (n + 1) ω - X n ω
  let stepReal : ℕ → Ω → ℝ := fun n ω ↦ (Δ n ω : ℝ)
  let S : ℕ → Ω → ℝ := partialSum stepReal
  let hS_strMeas : ∀ n, StronglyMeasurable (S n) :=
    fun n ↦ (partialSum_measurable stepReal
      (fun k ↦ measurable_stepReal Δ
        (fun m ↦ (hX_meas (m + 1)).sub (hX_meas m)) k) n).stronglyMeasurable
  let ℱS : Filtration ℕ ‹MeasurableSpace Ω› := Filtration.natural S hS_strMeas
  have hΔ_meas : ∀ n, Measurable (Δ n) := by
    intro n
    simpa [Δ] using (hX_meas (n + 1)).sub (hX_meas n)
  have hstep_meas : ∀ n, Measurable (stepReal n) := by
    intro n
    simpa [stepReal] using measurable_stepReal Δ hΔ_meas n
  have hstep_indep : iIndepFun stepReal P := by
    -- Proof comment: independence is preserved by the measurable cast `ℤ → ℝ`.
    have hcast_meas : Measurable (fun z : ℤ ↦ (z : ℝ)) := measurable_of_countable _
    have hstep_indep' : iIndepFun (fun n ω ↦ (Δ n ω : ℝ)) P := by
      simpa using hX_indep.comp (fun _ z ↦ (z : ℝ)) (fun _ ↦ hcast_meas)
    simpa [stepReal] using hstep_indep'
  have hΔ_neg : ∀ n : ℕ, P ((Δ n) ⁻¹' {(-1 : ℤ)}) = (2 : ℝ≥0∞)⁻¹ := by
    intro n
    exact (hasLaw_symmetricRademacher_preimage_singletons P (Δ n) (hX_law n)).1
  have hΔ_pos : ∀ n : ℕ, P ((Δ n) ⁻¹' {(1 : ℤ)}) = (2 : ℝ≥0∞)⁻¹ := by
    intro n
    exact (hasLaw_symmetricRademacher_preimage_singletons P (Δ n) (hX_law n)).2
  have hstep_int : ∀ n, Integrable (stepReal n) P := by
    intro n
    -- Proof comment: each real increment is almost surely bounded by `1`.
    simpa [stepReal] using
      integrable_stepReal_of_fairSigns (μ := P) (X := Δ) hΔ_meas hΔ_neg hΔ_pos n
  have hstep_mean_zero : ∀ n, ∫ ξ, stepReal n ξ ∂P = 0 := by
    intro n
    -- Proof comment: the fair-sign law is symmetric, so each cast increment has mean zero.
    simpa [stepReal] using
      integral_stepReal_eq_zero_of_fairSigns (μ := P) (X := Δ) hΔ_meas hΔ_neg hΔ_pos n
  have hstep_sq_int : ∀ n, Integrable (fun ω ↦ (stepReal n ω) ^ 2) P := by
    intro n
    -- Proof comment: the square of a fair-sign increment is the constant `1`.
    simpa [stepReal] using
      integrable_stepReal_sq_of_fairSigns (μ := P) (Z := Δ) hΔ_meas hΔ_neg hΔ_pos n
  have hS_eq : ∀ n, S n = Xℝ n := by
    intro n
    funext ω
    calc
      S n ω = (random_walk_partial_sum Δ n ω : ℝ) := by
        simpa [S, stepReal] using partialSum_intCast_eq_randomWalkPartialSum Δ n ω
      _ = (X n ω : ℝ) := by
        exact_mod_cast symmetricSimpleRandomWalk_position_eq_partialSum (X := X) hX_zero n ω
  have hS_eq_fun : S = Xℝ := by
    funext n
    exact hS_eq n
  have hS_sq : IsSquareIntegrableProcess S P := by
    intro n
    exact partialSumMemLpTwoOfSquareIntegrableIncrements hstep_meas hstep_sq_int n
  have hS_martingale : Martingale S ℱS P := by
    have hS_adapted : StronglyAdapted ℱS S :=
      Filtration.stronglyAdapted_natural (u := S) (hum := hS_strMeas)
    have hS_int : ∀ n, Integrable (S n) P := by
      intro n
      -- Proof comment: finite sums of integrable increments stay integrable.
      simpa [S, partialSum] using
        (integrable_finset_sum (Finset.range n) fun i _ ↦ hstep_int i)
    have hcond_zero : ∀ n, P[S (n + 1) - S n | ℱS n] =ᵐ[P] 0 := by
      intro n
      -- Proof comment: the next increment is independent of the past and has mean zero.
      refine (condExp_partialSumIncrement_ae_eq_expectation
        (Y := stepReal) (μ := P) (hY_meas := hstep_meas) hstep_indep n).trans ?_
      exact Filter.Eventually.of_forall fun _ ↦ hstep_mean_zero n
    exact martingale_of_condExp_sub_eq_zero_nat hS_adapted hS_int hcond_zero
  let hX_strMeas : ∀ n, StronglyMeasurable (Xℝ n) := fun n ↦
    Int.cast_continuous.comp_stronglyMeasurable ((hX_meas n).stronglyMeasurable)
  have hX_martingale_ℱS : Martingale Xℝ ℱS P := by
    -- Proof comment: the normalized partial-sum model and the original walk agree pathwise.
    simpa [hS_eq_fun] using hS_martingale
  have hX_martingale_nat : Martingale Xℝ (Filtration.natural Xℝ hX_strMeas) P := by
    -- Route correction: instead of forcing equality of the two natural filtrations by hand,
    -- transfer the martingale to `Xℝ` and then restrict to its own natural filtration.
    have hnat := martingale_natural_filtration hX_martingale_ℱS
    have hwitness :
        (fun n ↦ (hX_martingale_ℱS.stronglyAdapted n).mono (ℱS.le n)) = hX_strMeas := by
      funext n
      exact Subsingleton.elim _ _
    simpa [hX_strMeas, hwitness] using hnat
  constructor
  · intro n
    -- Proof comment: transport the `L²` bound from the normalized partial-sum model back to `Xℝ`.
    simpa [hS_eq n] using hS_sq n
  · -- Proof comment: the martingale statement is proved on the normalized partial-sum model `S`
    -- and then lowered to the natural filtration of the original walk.
    exact hX_martingale_nat

-- Proof sketch: apply the preceding square-integrable martingale statement and then use the
-- standard fact that squaring a square-integrable martingale yields a submartingale with respect
-- to the same filtration.
/-- Example 9.36 (2): the squared process `(X_n^2)` of a symmetric simple random walk is a
submartingale for the natural filtration of the walk. -/
theorem symmetricSimpleRandomWalk_sq_submartingale
    (hX_zero : X 0 = 0)
    (hX_meas : ∀ n, Measurable (X n))
    (hX_indep : iIndepFun (fun n ω ↦ X (n + 1) ω - X n ω) P)
    (hX_law : ∀ n,
      HasLaw (fun ω ↦ X (n + 1) ω - X n ω) symmetricRademacherLaw P) :
    Submartingale (fun n ω ↦ Xℝ n ω ^ 2)
      (Filtration.natural Xℝ
        (fun n ↦
          Int.cast_continuous.comp_stronglyMeasurable
            ((hX_meas n).stronglyMeasurable)))
      P := by
  letI : IsProbabilityMeasure P := (hX_law 0).isProbabilityMeasure
  let ℱX : Filtration ℕ ‹MeasurableSpace Ω› :=
    Filtration.natural Xℝ
      (fun n ↦
        Int.cast_continuous.comp_stronglyMeasurable
          ((hX_meas n).stronglyMeasurable))
  obtain ⟨hX_sq, hX_martingale⟩ :=
    symmetricSimpleRandomWalk_squareIntegrable_martingale
      (P := P) (X := X) hX_zero hX_meas hX_indep hX_law
  have hpow_int : ∀ n, Integrable (fun ω ↦ |Xℝ n ω| ^ (2 : ℝ)) P := by
    intro n
    have hsq_int :
        Integrable (fun ω ↦ Xℝ n ω ^ 2) P := by
      exact (memLp_two_iff_integrable_sq
        (Int.cast_continuous.comp_stronglyMeasurable
          ((hX_meas n).stronglyMeasurable)).aestronglyMeasurable).1 (hX_sq n)
    -- Proof comment: for real-valued variables, `|x| ^ 2` is exactly `x ^ 2`.
    simpa [Real.rpow_natCast, sq_abs] using hsq_int
  have habs_sub :
      Submartingale (fun n ω ↦ |Xℝ n ω| ^ (2 : ℝ)) ℱX P := by
    exact submartingale_abs_rpow
      (X := Xℝ) (ℱ := ℱX) (μ := P) hX_martingale (by norm_num) hpow_int
  -- Proof comment: rewrite the absolute-value square back to the ordinary square process.
  simpa [ℱX, Real.rpow_natCast, sq_abs] using habs_sub

end
