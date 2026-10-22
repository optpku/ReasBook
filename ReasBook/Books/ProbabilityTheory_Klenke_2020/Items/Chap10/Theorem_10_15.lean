/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap10.Definition_10_13
import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Remark_9_29

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

universe u

section

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {I : Set ℝ} [Countable I]
variable {μ : Measure Ω} [IsFiniteMeasure μ]

-- The book works in the probability-space setting. Finiteness is the measure-side hypothesis
-- needed by conditional expectation and supplies `SigmaFiniteFiltration μ ℱ` for every filtration.

/-! Theorem 10.15: let `I ⊂ ℝ` be countable, and let `(X_t)_{t ∈ I}` be a martingale,
submartingale, or supermartingale with respect to `ℱ`. If `τ` is a stopping time, then the
stopped process `X^τ` is again a martingale, submartingale, or supermartingale, respectively,
both with respect to `ℱ` and with respect to `ℱ^τ`.

The source theorem is stated below as six atomic clauses rather than one giant conjunction, and
the public bridge `stoppedProcessOn` relates this subtype-indexed surface to
`MeasureTheory.stoppedProcess` whenever `I` is nonempty. -/

/-- The stopped process `X^τ` for a process indexed by a countable subset of `ℝ`.

This is the source-faithful subtype-index version of `MeasureTheory.stoppedProcess`. When
`I` is nonempty, it agrees with the canonical mathlib owner. -/
noncomputable abbrev stoppedProcessOn
    (X : I → Ω → ℝ) (τ : Ω → WithTop I) : I → Ω → ℝ :=
  fun t ω ↦ X ((min (t : WithTop I) (τ ω)).untop (by simp)) ω

/-- On a nonempty index set, the source-facing subtype stopped process agrees with
`MeasureTheory.stoppedProcess`. -/
theorem stoppedProcessOn_eq_stoppedProcess [Nonempty I]
    {X : I → Ω → ℝ} {τ : Ω → WithTop I} :
    stoppedProcessOn X τ = stoppedProcess X τ := by
  ext t ω
  have hne : min (t : WithTop I) (τ ω) ≠ ⊤ := by simp
  rw [stoppedProcessOn, MeasureTheory.stoppedProcess]
  simp [WithTop.untopA_eq_untop, hne]

/-- Helper for Theorem 10.15: for countable subsets of `ℝ`, the stopped process is adapted to the
stopped filtration. -/
lemma stoppedProcess_adapted_stoppedFiltration_countable
    {ℱ : Filtration I mΩ} {X : I → Ω → ℝ} {τ : Ω → WithTop I}
    (hX : Adapted ℱ X) (hτ : IsStoppingTime ℱ τ) :
    Adapted (stoppedFiltration ℱ hτ) (stoppedProcessOn X τ) := by
  classical
  by_cases hI : IsEmpty I
  · letI : IsEmpty I := hI
    intro t
    exact isEmptyElim t
  · letI : Nonempty I := not_isEmpty_iff.mp hI
    intro t
    -- Rewrite the time-`t` slice as the stopped value at the bounded stopping time `τ ∧ t`.
    rw [stoppedFiltration_apply ℱ hτ t]
    let σ : Ω → WithTop I := fun ω ↦ min (τ ω) (t : WithTop I)
    have hσ : IsStoppingTime ℱ σ := hτ.min_const t
    have hslice : stoppedProcessOn X τ t = stoppedValue X σ := by
      ext ω
      have hne : σ ω ≠ ⊤ := by
        simp [σ]
      simp [stoppedProcessOn, stoppedValue, σ, min_comm, WithTop.untopA_eq_untop, hne]
    rw [hslice]
    intro s hs
    -- Decompose the stopped value along the countably many atoms `{σ = i}`.
    have hpreimage :
        stoppedValue X σ ⁻¹' s = ⋃ i : I, (X i ⁻¹' s ∩ {ω | σ ω = i}) := by
      ext ω
      constructor
      · intro hω
        let i : I := (σ ω).untop (by simp [σ])
        refine Set.mem_iUnion.2 ⟨i, ?_⟩
        have hωi : σ ω = i := by
          simp [i, σ]
        have hωuntop : (σ ω).untopA = i := by
          rw [hωi]
          simp
        refine ⟨?_, hωi⟩
        simpa [stoppedValue, hωuntop]
          using hω
      · intro hω
        rcases Set.mem_iUnion.1 hω with ⟨i, hi⟩
        rcases hi with ⟨hiX, hωi⟩
        have hωuntop : (σ ω).untopA = i := by
          rw [hωi]
          simp
        simpa [stoppedValue, hωuntop]
          using hiX
    rw [hpreimage]
    refine MeasurableSet.iUnion fun i ↦ ?_
    have hXi : MeasurableSet[ℱ i] (X i ⁻¹' s ∩ {ω | σ ω = i}) :=
      (hX i hs).inter (hσ.measurableSet_eq_of_countable_range (Set.to_countable _) i)
    exact (hσ.measurableSet_inter_eq_iff (X i ⁻¹' s) i).2 hXi

/-- Helper for Theorem 10.15: the stopped filtration is pointwise smaller than the original
filtration. -/
lemma stoppedFiltration_le
    {ℱ : Filtration I mΩ} {τ : Ω → WithTop I} (hτ : IsStoppingTime ℱ τ) :
    stoppedFiltration ℱ hτ ≤ ℱ := by
  intro t
  simpa [stoppedFiltration] using
    (show (Filtration.const I hτ.measurableSpace hτ.measurableSpace_le ⊓ ℱ) t ≤ ℱ t from
      inf_le_right)

/-- Helper for Theorem 10.15: stopping commutes with pointwise negation. -/
lemma stoppedProcess_neg
    {X : I → Ω → ℝ} {τ : Ω → WithTop I} :
    -(stoppedProcessOn (-X) τ) = stoppedProcessOn X τ := by
  -- Stopping only changes the time index, so pointwise negation commutes with stopping.
  ext t ω
  simp [stoppedProcessOn]

/-- Helper for Theorem 10.15: for countable subsets of `ℝ`, the stopped process is strongly
adapted to the original filtration. -/
lemma stoppedProcess_stronglyAdapted_originalFiltration_countable
    {ℱ : Filtration I mΩ} {X : I → Ω → ℝ} {τ : Ω → WithTop I}
    (hX : StronglyAdapted ℱ X) (hτ : IsStoppingTime ℱ τ) :
    StronglyAdapted ℱ (stoppedProcessOn X τ) := by
  let hStoppedAdapted :
      Adapted (stoppedFiltration ℱ hτ) (stoppedProcessOn X τ) :=
    stoppedProcess_adapted_stoppedFiltration_countable hX.adapted hτ
  let hStoppedStrong :
      StronglyAdapted (stoppedFiltration ℱ hτ) (stoppedProcessOn X τ) :=
    hStoppedAdapted.stronglyAdapted
  intro t
  -- First measure the stopped slice in the smaller stopped filtration, then enlarge to `ℱ t`.
  exact (hStoppedStrong t).mono ((stoppedFiltration_le hτ) t)

/-- Helper for Theorem 10.15: on `{τ ≤ s}`, the stopped values at times `s` and `t` already
agree. -/
private lemma stoppedValue_min_const_eq_on_le [Nonempty I]
    {X : I → Ω → ℝ} {τ : Ω → WithTop I} {s t : I} (hst : s ≤ t) :
    Set.EqOn (stoppedValue X fun ω ↦ min (s : WithTop I) (τ ω))
      (stoppedValue X fun ω ↦ min (t : WithTop I) (τ ω))
      {ω | τ ω ≤ s} := by
  intro ω hω
  -- On this event both bounded stopping times reduce to the same random time `τ`.
  have hs : min (s : WithTop I) (τ ω) = τ ω := min_eq_right hω
  have hstTop : (s : WithTop I) ≤ (t : WithTop I) := by exact_mod_cast hst
  have ht : min (t : WithTop I) (τ ω) = τ ω := min_eq_right (hω.trans hstTop)
  simp [stoppedValue, hs, ht]

/-- Helper for Theorem 10.15: on `{s < τ}`, the `s`-stopped value is just `X s`. -/
private lemma stoppedValue_min_const_eq_time_on_lt [Nonempty I]
    {X : I → Ω → ℝ} {τ : Ω → WithTop I} {s : I} :
    Set.EqOn (stoppedValue X fun ω ↦ min (s : WithTop I) (τ ω)) (X s)
      {ω | (s : WithTop I) < τ ω} := by
  intro ω hω
  -- Before the stopping time has arrived, the minimum is the deterministic time `s`.
  have hs : min (s : WithTop I) (τ ω) = s := min_eq_left (le_of_lt hω)
  simp [stoppedValue, hs]

/-- Helper for Theorem 10.15: the `{τ ≤ s}` piece contributes the same set integral at times `s`
and `t`. -/
private lemma setIntegral_stoppedValue_min_const_eq_on_le [Nonempty I]
    {X : I → Ω → ℝ} {τ : Ω → WithTop I} {s t : I} (hst : s ≤ t)
    {A : Set Ω} (hA : MeasurableSet A) (hAτ : A ⊆ {ω | τ ω ≤ s}) :
    ∫ ω in A, stoppedValue X (fun ω ↦ min (s : WithTop I) (τ ω)) ω ∂μ
      = ∫ ω in A, stoppedValue X (fun ω ↦ min (t : WithTop I) (τ ω)) ω ∂μ := by
  -- The first split piece is handled by pointwise equality of the two stopped values.
  refine setIntegral_congr_fun hA fun ω hω ↦ ?_
  exact stoppedValue_min_const_eq_on_le (X := X) (τ := τ) hst (hAτ hω)

/-- Helper for Theorem 10.15: on a set contained in `{s < τ}`, the `s`-stopped value integrates
exactly like `X s`. -/
private lemma setIntegral_stoppedValue_min_const_eq_time_on_lt [Nonempty I]
    {X : I → Ω → ℝ} {τ : Ω → WithTop I} {s : I}
    {A : Set Ω} (hA : MeasurableSet A) (hAτ : A ⊆ {ω | (s : WithTop I) < τ ω}) :
    ∫ ω in A, stoppedValue X (fun ω ↦ min (s : WithTop I) (τ ω)) ω ∂μ
      = ∫ ω in A, X s ω ∂μ := by
  -- The second split piece collapses the bounded stopped value to the deterministic slice.
  refine setIntegral_congr_fun hA fun ω hω ↦ ?_
  exact stoppedValue_min_const_eq_time_on_lt (X := X) (τ := τ) (hAτ hω)

/-- Helper for Theorem 10.15: an `ℱ s`-measurable set that lies entirely before a stopping time is
measurable in the stopping-time σ-algebra. -/
private lemma measurableSet_stoppingTime_of_subset_gt
    {ℱ : Filtration I mΩ} {σ : Ω → WithTop I} (hσ : IsStoppingTime ℱ σ)
    {s : I} {A : Set Ω} (hA : MeasurableSet[ℱ s] A)
    (hAσ : A ⊆ {ω | (s : WithTop I) < σ ω}) :
    MeasurableSet[hσ.measurableSpace] A := by
  -- Proof comment: before the deterministic time `s`, the set is disjoint from `{σ ≤ i}`; after
  -- time `s`, both factors are already measurable in `ℱ i`.
  rw [IsStoppingTime.measurableSet]
  refine ⟨(ℱ.le s) _ hA, fun i ↦ ?_⟩
  by_cases hsi : s ≤ i
  · exact ((ℱ.mono hsi) _ hA).inter (hσ.measurableSet_le i)
  · have hEmpty : A ∩ {ω | σ ω ≤ i} = ∅ := by
      ext ω
      constructor
      · intro hω
        rcases hω with ⟨hωA, hωi⟩
        have hslt : (s : WithTop I) < σ ω := hAσ hωA
        exact (not_le_of_gt hslt) <|
          le_trans hωi (show (i : WithTop I) ≤ s by exact_mod_cast le_of_not_ge hsi)
      · intro hω
        exact False.elim hω
    simpa [hEmpty]

/-- Helper for Theorem 10.15: on a deterministic test set contained in `{s < σ}`, integrating a
conditional expectation over the stopping-time σ-algebra is the same as integrating the original
function. -/
private lemma setIntegral_condExp_of_subset_gt
    {ℱ : Filtration I mΩ} {σ : Ω → WithTop I} (hσ : IsStoppingTime ℱ σ)
    {s : I} {A : Set Ω} (hA : MeasurableSet[ℱ s] A)
    (hAσ : A ⊆ {ω | (s : WithTop I) < σ ω}) {f : Ω → ℝ} (hf : Integrable f μ) :
    ∫ ω in A, μ[f | hσ.measurableSpace] ω ∂μ = ∫ ω in A, f ω ∂μ := by
  -- Proof comment: the previous lemma upgrades the post-hit test set from `ℱ s` to the
  -- stopping-time σ-algebra, so the owner `setIntegral_condExp` identity applies directly.
  rw [MeasureTheory.setIntegral_condExp hσ.measurableSpace_le hf
    (measurableSet_stoppingTime_of_subset_gt (ℱ := ℱ) (σ := σ) hσ hA hAσ)]

/-- Helper for Theorem 10.15: on the atom `{σ = i}`, conditioning `X t` to `hσ.measurableSpace`
agrees with conditioning it to the deterministic-time `σ`-algebra `ℱ i`. -/
private lemma condExp_eq_condExp_on_stoppingAtom [Nonempty I]
    {ℱ : Filtration I mΩ} {X : I → Ω → ℝ} {σ : Ω → WithTop I} {i t : I}
    (hσ : IsStoppingTime ℱ σ) (hσ_le : ∀ ω, σ ω ≤ t)
    (hXt : StronglyMeasurable[ℱ t] (X t)) (hXt_int : Integrable (X t) μ) :
    μ[X t | hσ.measurableSpace] =ᵐ[μ.restrict {ω | σ ω = i}] μ[X t | ℱ i] := by
  -- Proof comment: this is exactly the owner conditional-expectation restriction lemma on a
  -- stopping-time atom, so no further local unfolding is needed here.
  simpa using
    (MeasureTheory.condExp_stopping_time_ae_eq_restrict_eq_of_countable
      (μ := μ) (ℱ := ℱ) (τ := σ) (f := X t) (i := i) hσ)

/-- Helper for Theorem 10.15: a bounded stopped value is pointwise dominated by the conditional
expectation of the later deterministic slice with respect to the stopping-time `σ`-algebra. -/
private lemma stoppedValue_ae_le_condExp_of_le_const [Nonempty I]
    {ℱ : Filtration I mΩ} {X : I → Ω → ℝ} {σ : Ω → WithTop I} {t : I}
    (hσ : IsStoppingTime ℱ σ) (hσ_le : ∀ ω, σ ω ≤ t) (hX : Submartingale X ℱ μ) :
    stoppedValue X σ ≤ᵐ[μ] μ[X t | hσ.measurableSpace] := by
  let Y : I → Ω → ℝ := fun i ω ↦ μ[X t | ℱ i] ω
  have hY : Martingale Y ℱ μ := by
    -- Proof comment: the deterministic terminal slice generates a canonical martingale by
    -- conditioning along the filtration.
    simpa [Y] using (MeasureTheory.martingale_condExp (X t) ℱ μ)
  have hYt :
      Y t =ᵐ[μ] X t := by
    -- Proof comment: at time `t`, conditioning the `ℱ t`-measurable slice back to `ℱ t` does
    -- nothing.
    exact Filter.EventuallyEq.of_eq <|
      condExp_of_stronglyMeasurable (ℱ.le t) (hX.stronglyAdapted t) (hX.integrable t)
  have hYstop :
      stoppedValue Y σ =ᵐ[μ] μ[X t | hσ.measurableSpace] := by
    -- Proof comment: instead of using the topological optional-sampling owner theorem, decompose
    -- along the countably many atoms `{σ = i}` and apply the stopping-atom restriction identity.
    have hRestr :
        stoppedValue Y σ =ᵐ[μ.restrict (⋃ i ∈ (Set.univ : Set I), {ω | σ ω = i})]
          μ[X t | hσ.measurableSpace] := by
      rw [MeasureTheory.ae_eq_restrict_biUnion_iff (μ := μ)
        (s := fun i : I ↦ {ω | σ ω = i}) (t := (Set.univ : Set I)) (ht := Set.to_countable _)]
      intro i _
      have hStoppedY :
          stoppedValue Y σ =ᵐ[μ.restrict {ω | σ ω = i}] Y i := by
        -- Proof comment: on the atom `{σ = i}`, the sampled martingale `Y` reduces to its
        -- deterministic slice at `i`.
        exact
          (show Set.EqOn (stoppedValue Y σ) (Y i) {ω | σ ω = i} from
            fun ω hω ↦ by
              rw [Set.mem_setOf_eq] at hω
              simp [stoppedValue, Y, hω]).aeEq_restrict
            ((ℱ.le i) _ (hσ.measurableSet_eq_of_countable_range (Set.to_countable _) i))
      exact hStoppedY.trans <| by
        simpa [Y] using
          (condExp_eq_condExp_on_stoppingAtom
            (ℱ := ℱ) (X := X) (σ := σ) (i := i) (t := t)
            hσ hσ_le (hX.stronglyAdapted t) (hX.integrable t)).symm
    have hCover :
        (⋃ i ∈ (Set.univ : Set I), {ω | σ ω = i}) = (Set.univ : Set Ω) := by
      ext ω
      constructor
      · intro _
        simp
      · intro _
        have hTop : σ ω ≠ ⊤ := by
          exact fun hTop ↦ by simpa [hTop] using hσ_le ω
        refine Set.mem_iUnion.2 ⟨(σ ω).untop hTop, ?_⟩
        refine Set.mem_iUnion.2 ⟨by simp, ?_⟩
        simpa [Set.mem_setOf_eq] using (WithTop.coe_untop (σ ω) hTop)
    have hRestr' := hRestr
    rw [hCover, Measure.restrict_univ] at hRestr'
    exact hRestr'
  have hAtomLe :
      ∀ i : I, ∀ᵐ ω ∂μ.restrict {ω | σ ω = i}, stoppedValue X σ ω ≤ stoppedValue Y σ ω := by
    intro i
    by_cases hi : i ≤ t
    · have hXi :
          X i ≤ᵐ[μ] Y i := by
        -- Proof comment: on each deterministic time `i ≤ t`, the submartingale inequality gives
        -- the comparison with the conditional-expectation martingale `Y`.
        simpa [Y] using (hX.ae_le_condExp (i := i) (j := t) hi)
      have hXi_restrict :
          X i ≤ᵐ[μ.restrict {ω | σ ω = i}] Y i :=
        ae_restrict_of_ae hXi
      have hStoppedX :
          stoppedValue X σ =ᵐ[μ.restrict {ω | σ ω = i}] X i := by
        -- Proof comment: on the atom `{σ = i}`, the stopped value really is the deterministic
        -- slice `X i`.
        exact
          (show Set.EqOn (stoppedValue X σ) (X i) {ω | σ ω = i} from
            fun ω hω ↦ by
              rw [Set.mem_setOf_eq] at hω
              simp [stoppedValue, hω]).aeEq_restrict
            ((ℱ.le i) _ (hσ.measurableSet_eq_of_countable_range (Set.to_countable _) i))
      have hStoppedY :
          stoppedValue Y σ =ᵐ[μ.restrict {ω | σ ω = i}] Y i := by
        -- Proof comment: the same atomwise normalization applies to the auxiliary martingale `Y`.
        exact
          (show Set.EqOn (stoppedValue Y σ) (Y i) {ω | σ ω = i} from
            fun ω hω ↦ by
              rw [Set.mem_setOf_eq] at hω
              simp [stoppedValue, Y, hω]).aeEq_restrict
            ((ℱ.le i) _ (hσ.measurableSet_eq_of_countable_range (Set.to_countable _) i))
      filter_upwards [hStoppedX, hXi_restrict, hStoppedY] with ω hωX hωXY hωY
      simpa [hωX, hωY] using hωXY
    · have hEmpty : {ω | σ ω = i} = ∅ := by
        -- Proof comment: if `i` is above the deterministic bound `t`, the atom `{σ = i}` is empty.
        ext ω
        constructor
        · intro hω
          rw [Set.mem_setOf_eq] at hω
          exact (hi <| by simpa [hω] using hσ_le ω).elim
        · intro hω
          exact False.elim hω
      simpa [hEmpty]
  have hStopLe :
      stoppedValue X σ ≤ᵐ[μ] stoppedValue Y σ := by
    -- Proof comment: glue the atomwise deterministic inequalities back over the countable
    -- partition `Ω = ⋃ i, {σ = i}`.
    have hRestr :
        ∀ᵐ ω ∂μ.restrict (⋃ i ∈ (Set.univ : Set I), {ω | σ ω = i}),
          stoppedValue X σ ω ≤ stoppedValue Y σ ω := by
      rw [MeasureTheory.ae_restrict_biUnion_iff (μ := μ)
        (s := fun i : I ↦ {ω | σ ω = i}) (t := (Set.univ : Set I)) (ht := Set.to_countable _)]
      intro i _
      exact hAtomLe i
    have hCover :
        (⋃ i ∈ (Set.univ : Set I), {ω | σ ω = i}) = (Set.univ : Set Ω) := by
      ext ω
      constructor
      · intro _
        simp
      · intro _
        have hTop : σ ω ≠ ⊤ := by
          exact fun hTop ↦ by simpa [hTop] using hσ_le ω
        refine Set.mem_iUnion.2 ⟨(σ ω).untop hTop, ?_⟩
        refine Set.mem_iUnion.2 ⟨by simp, ?_⟩
        simpa [Set.mem_setOf_eq] using (WithTop.coe_untop (σ ω) hTop)
    have hRestr' := hRestr
    rw [hCover, Measure.restrict_univ] at hRestr'
    exact hRestr'
  filter_upwards [hStopLe, hYstop] with ω hωLe hωEq
  simpa [hωEq] using hωLe

/-- Helper for Theorem 10.15: the original-filtration submartingale clause is the only remaining
structural blocker, so the other two original-filtration clauses can reduce to it. -/
-- The finite-measure assumption now supplies `SigmaFiniteFiltration μ ℱ`; the remaining proof
-- obligation is the countable-order optional-stopping argument itself.
private theorem submartingale_stoppedProcess_originalFiltration
    [Nonempty I]
    {ℱ : Filtration I mΩ} {X : I → Ω → ℝ} {τ : Ω → WithTop I}
    (hτ : IsStoppingTime ℱ τ) (hX : Submartingale X ℱ μ) :
    Submartingale (stoppedProcess X τ) ℱ μ := by
  -- TODO: the remaining step is the bounded optional-sampling inequality
  -- `X s ≤ μ[stoppedValue X (fun ω ↦ min (t : WithTop I) (τ ω)) | ℱ s]` on `{s < τ}`.
  -- The new helper `stoppedValue_ae_le_condExp_of_le_const` closes the deterministic-time bridge,
  -- but the proof still needs the later stopped-value comparison to finish the set-integral route.
  sorry

/-- Theorem 10.15 (1): if `(X_t)_{t ∈ I}` is a martingale with respect to `ℱ` and `τ` is a
stopping time, then the stopped process `X^τ` is again a martingale with respect to `ℱ`. -/
theorem stoppedProcess_preserves_martingale
    {ℱ : Filtration I mΩ} {X : I → Ω → ℝ} {τ : Ω → WithTop I}
    (hτ : IsStoppingTime ℱ τ) (hX : Martingale X ℱ μ) :
    Martingale (stoppedProcessOn X τ) ℱ μ := by
  -- Route correction: reduce the martingale case to the already separated sub/super cases.
  rw [martingale_iff]
  refine ⟨?_, ?_⟩
  · -- The supermartingale half comes from applying the submartingale backbone to `-X`.
    have hSubNeg : Submartingale (stoppedProcessOn (-X) τ) ℱ μ := by
      classical
      by_cases hI : IsEmpty I
      · letI : Subsingleton I := ⟨fun a b ↦ isEmptyElim a⟩
        have hproc : stoppedProcessOn (-X) τ = -X := Subsingleton.elim _ _
        simpa [hproc] using hX.supermartingale.neg
      · letI : Nonempty I := not_isEmpty_iff.mp hI
        simpa [stoppedProcessOn_eq_stoppedProcess] using
          submartingale_stoppedProcess_originalFiltration
            (I := I) (μ := μ) hτ hX.supermartingale.neg
    simpa [stoppedProcess_neg] using hSubNeg.neg
  · classical
    by_cases hI : IsEmpty I
    · letI : Subsingleton I := ⟨fun a b ↦ isEmptyElim a⟩
      have hproc : stoppedProcessOn X τ = X := Subsingleton.elim _ _
      simpa [hproc] using hX.submartingale
    · letI : Nonempty I := not_isEmpty_iff.mp hI
      simpa [stoppedProcessOn_eq_stoppedProcess] using
        submartingale_stoppedProcess_originalFiltration (I := I) (μ := μ) hτ hX.submartingale

/-- Clause (2): if `(X_t)_{t ∈ I}` is a martingale with respect to `ℱ` and `τ` is a
stopping time, then the stopped process `X^τ` is again a martingale with respect to `ℱ^τ`. -/
-- The finite-measure instance supplies the conditional-expectation transport used below.
theorem stoppedProcess_preserves_martingale_stoppedFiltration
    {ℱ : Filtration I mΩ} {X : I → Ω → ℝ} {τ : Ω → WithTop I}
    (hτ : IsStoppingTime ℱ τ) (hX : Martingale X ℱ μ) :
    Martingale (stoppedProcessOn X τ) (stoppedFiltration ℱ hτ) μ := by
  exact martingale_of_le_filtration (stoppedFiltration_le hτ)
    (stoppedProcess_preserves_martingale hτ hX)
    (stoppedProcess_adapted_stoppedFiltration_countable hX.stronglyAdapted.adapted hτ)

/-- Clause (3): if `(X_t)_{t ∈ I}` is a submartingale with respect to `ℱ` and `τ` is a
stopping time, then the stopped process `X^τ` is again a submartingale with respect to `ℱ`. -/
theorem stoppedProcess_preserves_submartingale
    {ℱ : Filtration I mΩ} {X : I → Ω → ℝ} {τ : Ω → WithTop I}
    (hτ : IsStoppingTime ℱ τ) (hX : Submartingale X ℱ μ) :
    Submartingale (stoppedProcessOn X τ) ℱ μ := by
  classical
  by_cases hI : IsEmpty I
  · letI : Subsingleton I := ⟨fun a b ↦ isEmptyElim a⟩
    have hproc : stoppedProcessOn X τ = X := Subsingleton.elim _ _
    -- In the empty-index case, every process is definitionally the same.
    simpa [hproc] using hX
  · letI : Nonempty I := not_isEmpty_iff.mp hI
    -- In the nonempty case, transport the private owner-level theorem back to `stoppedProcessOn`.
    simpa [stoppedProcessOn_eq_stoppedProcess] using
      submartingale_stoppedProcess_originalFiltration (I := I) (μ := μ) hτ hX

/-- Clause (4): if `(X_t)_{t ∈ I}` is a submartingale with respect to `ℱ` and `τ` is a
stopping time, then the stopped process `X^τ` is again a submartingale with respect to
`ℱ^τ`. -/
-- Route correction: this clause depends on the same smaller-filtration bridge as clause (2), so
-- the missing finiteness premise blocks it before any further local decomposition helps.
theorem stoppedProcess_preserves_submartingale_stoppedFiltration
    {ℱ : Filtration I mΩ} {X : I → Ω → ℝ} {τ : Ω → WithTop I}
    (hτ : IsStoppingTime ℱ τ) (hX : Submartingale X ℱ μ) :
    Submartingale (stoppedProcessOn X τ) (stoppedFiltration ℱ hτ) μ := by
  exact submartingale_of_le_filtration (stoppedFiltration_le hτ)
    (stoppedProcess_preserves_submartingale hτ hX)
    (stoppedProcess_adapted_stoppedFiltration_countable hX.stronglyAdapted.adapted hτ)

/-- Clause (5): if `(X_t)_{t ∈ I}` is a supermartingale with respect to `ℱ` and `τ` is a
stopping time, then the stopped process `X^τ` is again a supermartingale with respect to `ℱ`. -/
theorem stoppedProcess_preserves_supermartingale
    {ℱ : Filtration I mΩ} {X : I → Ω → ℝ} {τ : Ω → WithTop I}
    (hτ : IsStoppingTime ℱ τ) (hX : Supermartingale X ℱ μ) :
    Supermartingale (stoppedProcessOn X τ) ℱ μ := by
  -- Route correction: the supermartingale case is the negated submartingale case.
  have hSubNeg : Submartingale (stoppedProcessOn (-X) τ) ℱ μ :=
    stoppedProcess_preserves_submartingale hτ hX.neg
  have hSuperNeg : Supermartingale (-(stoppedProcessOn (-X) τ)) ℱ μ :=
    hSubNeg.neg
  simpa [stoppedProcess_neg] using hSuperNeg

/-- Clause (6): if `(X_t)_{t ∈ I}` is a supermartingale with respect to `ℱ` and `τ` is a
stopping time, then the stopped process `X^τ` is again a supermartingale with respect to
`ℱ^τ`. -/
-- Route correction: once the stopped-filtration submartingale statement is premise-corrected,
-- this clause again reduces to the negated submartingale route.
theorem stoppedProcess_preserves_supermartingale_stoppedFiltration
    {ℱ : Filtration I mΩ} {X : I → Ω → ℝ} {τ : Ω → WithTop I}
    (hτ : IsStoppingTime ℱ τ) (hX : Supermartingale X ℱ μ) :
    Supermartingale (stoppedProcessOn X τ) (stoppedFiltration ℱ hτ) μ := by
  exact supermartingale_of_le_filtration (stoppedFiltration_le hτ)
    (stoppedProcess_preserves_supermartingale hτ hX)
    (stoppedProcess_adapted_stoppedFiltration_countable hX.stronglyAdapted.adapted hτ)

end
