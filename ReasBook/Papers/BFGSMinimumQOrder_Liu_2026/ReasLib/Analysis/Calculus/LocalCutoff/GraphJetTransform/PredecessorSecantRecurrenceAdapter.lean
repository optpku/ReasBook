module

public import ReasLib.Analysis.Calculus.LocalCutoff.GraphJetTransform.SourceTransportedIncrementAdapter

public section

open scoped BigOperators

universe u

namespace LocalCutoff.GraphTransform

/-!
This file gives the source-facing interface for the two-point predecessor
comparison used by the graph-jet top coefficient.  The generic transported
increment certificate remains the iteration engine; this adapter only names
the inverse-center successor and the norm of the source predecessor defect.
-/

/-- Helper for Infrastructure I.16a: the inverse-center successor of a source
pair `(u, t)` keeps the forward center and transports its increment through
the inverse coordinate. -/
def predecessorSecantStep
    (forward inverse : ℝ → ℝ) (s : ℝ × ℝ) : ℝ × ℝ :=
  (inverse (forward s.1), inverse (s.1 + s.2) - inverse s.1)

/-- Helper for Infrastructure I.16a: a source predecessor defect is measured
by its norm at the pair `(u, t)`. -/
def predecessorSecantError
    {E : Type u} [NormedAddCommGroup E]
    (defect : ℝ → ℝ → E) (s : ℝ × ℝ) : ℝ :=
  ‖defect s.1 s.2‖

/-- Helper for Infrastructure I.16a: the named predecessor successor unfolds
at a source pair without exposing any generic state representation. -/
theorem predecessorSecantStep_pair
    (forward inverse : ℝ → ℝ) (u t : ℝ) :
    predecessorSecantStep forward inverse (u, t) =
      (inverse (forward u), inverse (u + t) - inverse u) := by
  rfl

/-- Helper for Infrastructure I.16a: a source predecessor adapter identifies
the exact `(u, t)` successor and defect while reusing an existing transported
increment recurrence certificate. -/
structure PredecessorSecantRecurrenceInterface
    (E : Type u) [NormedAddCommGroup E]
    (K : Set (ℝ × ℝ)) where
  defect : ℝ → ℝ → E
  forward : ℝ → ℝ
  inverse : ℝ → ℝ
  data : TransportedIncrementRecurrenceData ℝ K
  step_eq : data.step = predecessorSecantStep forward inverse
  error_eq : data.error = predecessorSecantError defect

/-- Helper for Infrastructure I.16a: the source recurrence is available at a
pair `(u, t)` with the inverse-center successor displayed explicitly. -/
theorem PredecessorSecantRecurrenceInterface.recurrence_at_pair
    {E : Type u} [NormedAddCommGroup E]
    {K : Set (ℝ × ℝ)}
    (certificate : PredecessorSecantRecurrenceInterface E K)
    {u t : ℝ} (hstate : (u, t) ∈ K) :
    predecessorSecantError certificate.defect (u, t) ≤
      certificate.data.contraction * predecessorSecantError certificate.defect
        (certificate.inverse (certificate.forward u),
          certificate.inverse (u + t) - certificate.inverse u) +
      certificate.data.forcing * ‖t‖ := by
  have hrec := certificate.data.recurrence (u, t) hstate
  simpa only [certificate.error_eq, certificate.step_eq,
    predecessorSecantStep_pair] using hrec

/-- Helper for Infrastructure I.16a: the inverse-center successor remains in
the declared source state set. -/
theorem PredecessorSecantRecurrenceInterface.step_mem_at_pair
    {E : Type u} [NormedAddCommGroup E]
    {K : Set (ℝ × ℝ)}
    (certificate : PredecessorSecantRecurrenceInterface E K)
    {u t : ℝ} (hstate : (u, t) ∈ K) :
    (certificate.inverse (certificate.forward u),
      certificate.inverse (u + t) - certificate.inverse u) ∈ K := by
  simpa only [certificate.step_eq, predecessorSecantStep_pair] using
    certificate.data.step_mem (u, t) hstate

/-- Helper for Infrastructure I.16a: the transported increment at a source
pair satisfies the declared scalar transport estimate. -/
theorem PredecessorSecantRecurrenceInterface.increment_norm_le_at_pair
    {E : Type u} [NormedAddCommGroup E]
    {K : Set (ℝ × ℝ)}
    (certificate : PredecessorSecantRecurrenceInterface E K)
    {u t : ℝ} (hstate : (u, t) ∈ K) :
    ‖certificate.inverse (u + t) - certificate.inverse u‖ ≤
      certificate.data.transport * ‖t‖ := by
  simpa only [certificate.step_eq, predecessorSecantStep_pair] using
    certificate.data.increment_norm_le (u, t) hstate

/-- Helper for Infrastructure I.16a: the existing transported-increment data
has the same iterated successor as the source predecessor step. -/
theorem PredecessorSecantRecurrenceInterface.step_iterate_eq
    {E : Type u} [NormedAddCommGroup E]
    {K : Set (ℝ × ℝ)}
    (certificate : PredecessorSecantRecurrenceInterface E K)
    (n : ℕ) (s : ℝ × ℝ) :
    (certificate.data.step^[n]) s =
      ((predecessorSecantStep certificate.forward certificate.inverse)^[n]) s := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simpa only [Function.iterate_succ_apply', certificate.step_eq, ih]

/-- Infrastructure I.16a: explicit terminal, radius, and weighted forcing
hypotheses bound the raw predecessor defect at a source pair. -/
theorem predecessorSecantError_le_of_terminal_forcing
    {E : Type u} [NormedAddCommGroup E]
    {K : Set (ℝ × ℝ)}
    (certificate : PredecessorSecantRecurrenceInterface E K)
    (radius : ℝ) (radius_nonneg : 0 ≤ radius) (steps : ℕ)
    (terminalBound budget : ℝ)
    (increment_norm_le : ∀ s ∈ K, ‖s.2‖ ≤ radius)
    (terminal_error_le : ∀ s ∈ K,
      predecessorSecantError certificate.defect
        ((predecessorSecantStep certificate.forward certificate.inverse)^[steps] s) ≤
      terminalBound)
    (weighted_budget_le :
      certificate.data.contraction ^ steps * terminalBound +
          certificate.data.forcing * radius *
            ∑ j ∈ Finset.range steps,
              (certificate.data.contraction * certificate.data.transport) ^ j ≤ budget)
    {u t : ℝ} (hstate : (u, t) ∈ K) :
    predecessorSecantError certificate.defect (u, t) ≤ budget := by
  have hterminal : ∀ s ∈ K,
      certificate.data.error ((certificate.data.step^[steps]) s) ≤ terminalBound := by
    intro s hs
    simpa only [certificate.error_eq, certificate.step_iterate_eq] using
      terminal_error_le s hs
  simpa only [certificate.error_eq] using
    (transportedIncrementError_le_of_source_fields
      certificate.data radius radius_nonneg steps terminalBound budget
      increment_norm_le hterminal weighted_budget_le hstate)

end LocalCutoff.GraphTransform
