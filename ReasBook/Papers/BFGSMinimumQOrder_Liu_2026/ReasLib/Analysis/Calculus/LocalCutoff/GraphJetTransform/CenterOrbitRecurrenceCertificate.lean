module

public import ReasLib.Analysis.Calculus.LocalCutoff.GraphJetTransform

public section

universe u v

namespace LocalCutoff.GraphTransform

/-- Helper for Infrastructure I.16: a compact-domain error decomposition keeps
the center-orbit transport explicit while isolating the forcing term. -/
structure CenterOrbitRecurrenceCertificate
    (Θ : Type u) (E : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Set Θ) where
  step : Θ → Θ
  defect : Θ → E
  filtered : Θ → E
  contraction : ℝ
  budget : ℝ
  forcing : Θ → E
  contraction_nonneg : 0 ≤ contraction
  contraction_lt_one : contraction < 1
  step_mem : ∀ u, u ∈ K → step u ∈ K
  bounded : ∃ M : ℝ, ∀ u ∈ K, ‖defect u - filtered u‖ ≤ M
  decomposition : ∀ u ∈ K,
    defect u - filtered u =
      contraction • (defect (step u) - filtered (step u)) + forcing u
  forcing_norm_le : ∀ u ∈ K, ‖forcing u‖ ≤ (1 - contraction) * budget

/-- Helper for Infrastructure I.16: a bounded compact-domain norm recurrence
absorbs its contracted successor error into a uniform budget. -/
theorem norm_le_of_bounded_centerOrbit_recurrence
    {Θ : Type u} {E : Type v} [NormedAddCommGroup E]
    {K : Set Θ} (step : Θ → Θ) (defect filtered : Θ → E)
    (contraction budget forcingBound : ℝ)
    (contraction_nonneg : 0 ≤ contraction)
    (contraction_lt_one : contraction < 1)
    (forcingBound_le : forcingBound ≤ (1 - contraction) * budget)
    (step_mem : ∀ u, u ∈ K → step u ∈ K)
    (bounded : ∃ M : ℝ, ∀ u ∈ K, ‖defect u - filtered u‖ ≤ M)
    (recurrence : ∀ u ∈ K,
      ‖defect u - filtered u‖ ≤
        contraction * ‖defect (step u) - filtered (step u)‖ +
          forcingBound)
    (hK : K.Nonempty) :
    ∀ u ∈ K, ‖defect u - filtered u‖ ≤ budget := by
  obtain ⟨M, hM⟩ := bounded
  let errors : Set ℝ := Set.range fun u : K ↦
    ‖defect u - filtered u‖
  have herrors_nonempty : errors.Nonempty := by
    obtain ⟨u, hu⟩ := hK
    exact ⟨‖defect u - filtered u‖, ⟨⟨u, hu⟩, rfl⟩⟩
  have herrors_bdd : BddAbove errors := by
    refine ⟨M, ?_⟩
    rintro _ ⟨u, rfl⟩
    exact hM u.1 u.2
  have hsuccessor_le (u : K) :
      ‖defect (step u) - filtered (step u)‖ ≤ sSup errors := by
    apply le_csSup herrors_bdd
    exact ⟨⟨step u, step_mem u.1 u.2⟩, rfl⟩
  have hrecurrence (u : K) :
      ‖defect u - filtered u‖ ≤
        contraction * sSup errors + (1 - contraction) * budget := by
    exact (recurrence u.1 u.2).trans <| add_le_add
      (mul_le_mul_of_nonneg_left (hsuccessor_le u) contraction_nonneg)
      forcingBound_le
  have hsup_le :
      sSup errors ≤ contraction * sSup errors + (1 - contraction) * budget := by
    apply csSup_le herrors_nonempty
    rintro _ ⟨u, rfl⟩
    exact hrecurrence u
  have hsup_budget : sSup errors ≤ budget := by
    nlinarith [hsup_le, contraction_lt_one]
  intro u hu
  exact (le_csSup herrors_bdd ⟨⟨u, hu⟩, rfl⟩).trans hsup_budget

/-- Infrastructure I.16: a bounded compact-domain center-orbit recurrence
absorbs its contracted successor error and bounds the live defect minus its
filtered branch by the supplied budget. -/
theorem CenterOrbitRecurrenceCertificate.error_norm_le
    {Θ : Type u} {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set Θ} (certificate : CenterOrbitRecurrenceCertificate Θ E K)
    (hK : K.Nonempty) :
    ∀ u ∈ K, ‖certificate.defect u - certificate.filtered u‖ ≤
      certificate.budget := by
  have hrecurrence : ∀ u ∈ K,
      ‖certificate.defect u - certificate.filtered u‖ ≤
        certificate.contraction *
            ‖certificate.defect (certificate.step u) -
              certificate.filtered (certificate.step u)‖ +
          (1 - certificate.contraction) * certificate.budget := by
    intro u hu
    rw [certificate.decomposition u hu]
    calc
      ‖certificate.contraction •
            (certificate.defect (certificate.step u) -
              certificate.filtered (certificate.step u)) +
          certificate.forcing u‖ ≤
          ‖certificate.contraction •
              (certificate.defect (certificate.step u) -
                certificate.filtered (certificate.step u))‖ +
            ‖certificate.forcing u‖ := norm_add_le _ _
      _ = |certificate.contraction| *
            ‖certificate.defect (certificate.step u) -
              certificate.filtered (certificate.step u)‖ +
            ‖certificate.forcing u‖ := by
        rw [norm_smul, Real.norm_eq_abs]
      _ ≤ certificate.contraction *
            ‖certificate.defect (certificate.step u) -
              certificate.filtered (certificate.step u)‖ +
            (1 - certificate.contraction) * certificate.budget := by
        rw [abs_of_nonneg certificate.contraction_nonneg]
        exact add_le_add le_rfl (certificate.forcing_norm_le u hu)
  exact norm_le_of_bounded_centerOrbit_recurrence
    certificate.step certificate.defect certificate.filtered certificate.contraction
    certificate.budget ((1 - certificate.contraction) * certificate.budget)
    certificate.contraction_nonneg certificate.contraction_lt_one le_rfl
    certificate.step_mem certificate.bounded hrecurrence hK

/-- Helper for Infrastructure I.16: compact and exterior forcing estimates
combine into the global forcing bound consumed by a center-orbit recurrence. -/
theorem forcing_norm_le_of_mem_or_not_mem
    {Θ : Type u} {E : Type v} [NormedAddCommGroup E]
    (K : Set Θ) (forcing : Θ → E) (forcingBound : ℝ)
    (hcompact : ∀ u ∈ K, ‖forcing u‖ ≤ forcingBound)
    (hexterior : ∀ u ∉ K, ‖forcing u‖ ≤ forcingBound) :
    ∀ u, ‖forcing u‖ ≤ forcingBound := by
  intro u
  by_cases hu : u ∈ K
  · exact hcompact u hu
  · exact hexterior u hu

/-- Helper for Infrastructure I.16: a finite transported-increment orbit keeps
the terminal error and the weighted forcing budget explicit. -/
structure FiniteCenterOrbitRecurrenceCertificate
    (Θ : Type u) (E : Type v) [NormedAddCommGroup E] (K : Set Θ) where
  step : Θ → Θ
  error : Θ → E
  contraction : ℝ
  forcingBound : ℝ
  budget : ℝ
  steps : ℕ
  contraction_nonneg : 0 ≤ contraction
  step_mem : ∀ u, u ∈ K → step u ∈ K
  recurrence : ∀ u ∈ K,
    ‖error u‖ ≤ contraction * ‖error (step u)‖ + forcingBound
  terminalBound : ℝ
  terminal_norm_le : ∀ u ∈ K,
    ‖error ((step^[steps]) u)‖ ≤ terminalBound
  weighted_budget_le :
    contraction ^ steps * terminalBound +
        (∑ j ∈ Finset.range steps, contraction ^ j) * forcingBound ≤ budget

/-- Infrastructure I.16: finite orbit iteration bounds a transported error
without requiring a uniform bound at every intermediate increment. -/
theorem FiniteCenterOrbitRecurrenceCertificate.error_norm_le
    {Θ : Type u} {E : Type v} [NormedAddCommGroup E]
    {K : Set Θ}
    (certificate : FiniteCenterOrbitRecurrenceCertificate Θ E K)
    {u : Θ} (hu : u ∈ K) : ‖certificate.error u‖ ≤ certificate.budget := by
  have hstep_mem : ∀ n : ℕ, ∀ u, u ∈ K →
      (certificate.step^[n]) u ∈ K := by
    intro n
    induction n with
    | zero =>
        intro u hu
        exact hu
    | succ n ih =>
        intro u hu
        rw [Function.iterate_succ_apply']
        exact certificate.step_mem _ (ih u hu)
  have hiterate : ∀ n : ℕ, ∀ u ∈ K,
      ‖certificate.error u‖ ≤
        certificate.contraction ^ n *
            ‖certificate.error ((certificate.step^[n]) u)‖ +
          ∑ j ∈ Finset.range n, certificate.contraction ^ j *
            certificate.forcingBound := by
    intro n
    induction n with
    | zero =>
        intro u hu
        simp
    | succ n ih =>
        intro u hu
        have hprev := ih u hu
        have hiterate_mem : (certificate.step^[n]) u ∈ K := hstep_mem n u hu
        have hstep := certificate.recurrence ((certificate.step^[n]) u)
          hiterate_mem
        have hscaled := mul_le_mul_of_nonneg_left hstep
          (pow_nonneg certificate.contraction_nonneg n)
        calc
          ‖certificate.error u‖ ≤
              certificate.contraction ^ n *
                  ‖certificate.error ((certificate.step^[n]) u)‖ +
                ∑ j ∈ Finset.range n, certificate.contraction ^ j *
                  certificate.forcingBound := hprev
          _ ≤ certificate.contraction ^ n *
                (certificate.contraction *
                    ‖certificate.error (certificate.step ((certificate.step^[n]) u))‖ +
                  certificate.forcingBound) +
                ∑ j ∈ Finset.range n, certificate.contraction ^ j *
                  certificate.forcingBound := by
            exact add_le_add_left hscaled _
          _ = certificate.contraction ^ (n + 1) *
                ‖certificate.error ((certificate.step^[n + 1]) u)‖ +
                ∑ j ∈ Finset.range (n + 1), certificate.contraction ^ j *
                  certificate.forcingBound := by
            rw [Finset.sum_range_succ, Function.iterate_succ_apply', pow_succ]
            ring_nf
  have hbound := hiterate certificate.steps u hu
  calc
    ‖certificate.error u‖ ≤ certificate.contraction ^ certificate.steps *
          ‖certificate.error ((certificate.step^[certificate.steps]) u)‖ +
        ∑ j ∈ Finset.range certificate.steps, certificate.contraction ^ j *
          certificate.forcingBound := hbound
    _ ≤ certificate.contraction ^ certificate.steps * certificate.terminalBound +
        ∑ j ∈ Finset.range certificate.steps, certificate.contraction ^ j *
          certificate.forcingBound := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (certificate.terminal_norm_le u hu)
          (pow_nonneg certificate.contraction_nonneg _)) le_rfl
    _ = certificate.contraction ^ certificate.steps * certificate.terminalBound +
        (∑ j ∈ Finset.range certificate.steps, certificate.contraction ^ j) *
          certificate.forcingBound := by
      rw [Finset.sum_mul]
    _ ≤ certificate.budget := certificate.weighted_budget_le

end LocalCutoff.GraphTransform
