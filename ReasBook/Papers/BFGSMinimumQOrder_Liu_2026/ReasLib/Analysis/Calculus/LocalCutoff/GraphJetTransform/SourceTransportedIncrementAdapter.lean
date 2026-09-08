module

public import ReasLib.Analysis.Calculus.LocalCutoff.GraphJetTransform.TransportedIncrementRecurrence

public section

open scoped BigOperators

universe u

namespace LocalCutoff.GraphTransform

/-!
This file is a source-facing view of the generic transported-increment
certificate.  The graph-transform source writes a state as `(u, t)`, while the
generic recurrence API writes it as an element of `TransportedIncrementState`.
The lemmas below only normalize that notation; all recurrence, terminal, and
budget hypotheses remain fields of the existing certificates.
-/

/-- Helper for Infrastructure I.16a: the center projection of a transported
increment state written as `(u, t)` is its source center `u`. -/
theorem transportedIncrementState_fst_pair {Θ : Type u} (x : Θ) (t : ℝ) :
    ((x, t) : TransportedIncrementState Θ).1 = x := by
  rfl

/-- Helper for Infrastructure I.16a: the increment projection of a transported
increment state written as `(u, t)` is its source increment `t`. -/
theorem transportedIncrementState_snd_pair {Θ : Type u} (x : Θ) (t : ℝ) :
    ((x, t) : TransportedIncrementState Θ).2 = t := by
  rfl

/-- Helper for Infrastructure I.16a: a generic transported recurrence can be
read directly at the source pair `(u, t)` without changing its hypotheses. -/
theorem TransportedIncrementRecurrenceData.recurrence_at_pair
    {Θ : Type u} {K : Set (TransportedIncrementState Θ)}
    (data : TransportedIncrementRecurrenceData Θ K)
    {u : Θ} {t : ℝ} (hstate : (u, t) ∈ K) :
    data.error (u, t) ≤
      data.contraction * data.error (data.step (u, t)) + data.forcing * ‖t‖ := by
  exact data.recurrence (u, t) hstate

/-- Helper for Infrastructure I.16a: the transported increment estimate at a
source pair exposes the second projection needed by the graph-transform proof. -/
theorem TransportedIncrementRecurrenceData.increment_norm_le_at_pair
    {Θ : Type u} {K : Set (TransportedIncrementState Θ)}
    (data : TransportedIncrementRecurrenceData Θ K)
    {u : Θ} {t : ℝ} (hstate : (u, t) ∈ K) :
    ‖(data.step (u, t)).2‖ ≤ data.transport * ‖t‖ := by
  exact data.increment_norm_le (u, t) hstate

/-- Helper for Infrastructure I.16a: recurrence iteration at `(u, t)` keeps
the terminal state and the geometric forcing factor in source notation. -/
theorem TransportedIncrementRecurrenceData.iterate_at_pair
    {Θ : Type u} {K : Set (TransportedIncrementState Θ)}
    (data : TransportedIncrementRecurrenceData Θ K)
    {u : Θ} {t : ℝ} (hstate : (u, t) ∈ K) (n : ℕ) :
    data.error (u, t) ≤
      data.contraction ^ n * data.error ((data.step^[n]) (u, t)) +
        data.forcing * ‖t‖ *
          ∑ j ∈ Finset.range n, (data.contraction * data.transport) ^ j := by
  exact data.iterate hstate n

/-- Helper for Infrastructure I.16a: a finite transported-increment budget
certificate exposes its terminal estimate at the source pair `(u, t)`. -/
theorem FiniteTransportedIncrementBudgetCertificate.terminal_error_le_at_pair
    {Θ : Type u} {K : Set (TransportedIncrementState Θ)}
    (certificate : FiniteTransportedIncrementBudgetCertificate Θ K)
    {u : Θ} {t : ℝ} (hstate : (u, t) ∈ K) :
    certificate.recurrenceData.error
        ((certificate.recurrenceData.step^[certificate.steps]) (u, t)) ≤
      certificate.terminalBound := by
  exact certificate.terminal_error_le (u, t) hstate

/-- Helper for Infrastructure I.16a: the source increment radius and weighted
forcing budget are the explicit terminal data consumed by the finite estimate. -/
theorem FiniteTransportedIncrementBudgetCertificate.source_budget_interface
    {Θ : Type u} {K : Set (TransportedIncrementState Θ)}
    (certificate : FiniteTransportedIncrementBudgetCertificate Θ K)
    {u : Θ} {t : ℝ} (hstate : (u, t) ∈ K) :
    ‖t‖ ≤ certificate.radius ∧
      certificate.recurrenceData.error
          ((certificate.recurrenceData.step^[certificate.steps]) (u, t)) ≤
        certificate.terminalBound ∧
      certificate.recurrenceData.contraction ^ certificate.steps *
            certificate.terminalBound +
          certificate.recurrenceData.forcing * certificate.radius *
            ∑ j ∈ Finset.range certificate.steps,
              (certificate.recurrenceData.contraction *
                certificate.recurrenceData.transport) ^ j ≤ certificate.budget ∧
      certificate.recurrenceData.error (u, t) ≤ certificate.budget := by
  exact ⟨certificate.increment_norm_le (u, t) hstate,
    certificate.terminal_error_le (u, t) hstate,
    certificate.weighted_budget_le,
    certificate.error_le_budget hstate⟩

/-- Infrastructure I.16a: explicit source recurrence, terminal, and forcing
fields assemble through the existing finite certificate and bound the error at
the source pair `(u, t)`. -/
theorem transportedIncrementError_le_of_source_fields
    {Θ : Type u} {K : Set (TransportedIncrementState Θ)}
    (data : TransportedIncrementRecurrenceData Θ K)
    (radius : ℝ) (radius_nonneg : 0 ≤ radius) (steps : ℕ)
    (terminalBound budget : ℝ)
    (increment_norm_le : ∀ s ∈ K, ‖s.2‖ ≤ radius)
    (terminal_error_le : ∀ s ∈ K,
      data.error ((data.step^[steps]) s) ≤ terminalBound)
    (weighted_budget_le :
      data.contraction ^ steps * terminalBound +
          data.forcing * radius *
            ∑ j ∈ Finset.range steps,
              (data.contraction * data.transport) ^ j ≤ budget)
    {u : Θ} {t : ℝ} (hstate : (u, t) ∈ K) :
    data.error (u, t) ≤ budget := by
  let certificate : FiniteTransportedIncrementBudgetCertificate Θ K :=
    { recurrenceData := data
      radius := radius
      radius_nonneg := radius_nonneg
      steps := steps
      terminalBound := terminalBound
      budget := budget
      increment_norm_le := increment_norm_le
      terminal_error_le := terminal_error_le
      weighted_budget_le := weighted_budget_le }
  exact certificate.error_le_budget hstate

end LocalCutoff.GraphTransform
