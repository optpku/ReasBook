module

public import ReasLib.Analysis.Calculus.LocalCutoff.GraphJetTransform.CenterOrbitRecurrenceCertificate

public section

open scoped BigOperators

universe u

namespace LocalCutoff.GraphTransform

/-!
This file records the two-point recurrence interface used by the finite-order
graph-jet argument.  The state keeps both a center parameter and the increment
transported by that parameter; source-specific composition identities only need
to provide the fields of the certificate.
-/

/-- A transported-increment state consists of a base parameter and a scalar
increment carried from that parameter. -/
abbrev TransportedIncrementState (Θ : Type u) := Θ × ℝ

/-- Infrastructure I.16a: recurrence data for a transported two-point error,
including the contraction factor, increment transport factor, and forcing scale. -/
structure TransportedIncrementRecurrenceData
    (Θ : Type u) (K : Set (TransportedIncrementState Θ)) where
  step : TransportedIncrementState Θ → TransportedIncrementState Θ
  error : TransportedIncrementState Θ → ℝ
  contraction : ℝ
  transport : ℝ
  forcing : ℝ
  contraction_nonneg : 0 ≤ contraction
  transport_nonneg : 0 ≤ transport
  forcing_nonneg : 0 ≤ forcing
  step_mem : ∀ s, s ∈ K → step s ∈ K
  recurrence : ∀ s ∈ K,
    error s ≤ contraction * error (step s) + forcing * ‖s.2‖
  increment_norm_le : ∀ s ∈ K,
    ‖(step s).2‖ ≤ transport * ‖s.2‖

/-- Infrastructure I.16a: iterating a transported-increment recurrence exposes
the terminal error and the geometric forcing budget at the original increment. -/
theorem TransportedIncrementRecurrenceData.iterate
    {Θ : Type u} {K : Set (TransportedIncrementState Θ)}
    (data : TransportedIncrementRecurrenceData Θ K)
    {s : TransportedIncrementState Θ} (hs : s ∈ K) (n : ℕ) :
    data.error s ≤
      data.contraction ^ n * data.error ((data.step^[n]) s) +
        data.forcing * ‖s.2‖ *
          ∑ j ∈ Finset.range n,
            (data.contraction * data.transport) ^ j := by
  have hstep_mem : ∀ n : ℕ, (data.step^[n]) s ∈ K := by
    intro m
    induction m with
    | zero =>
        simpa using hs
    | succ m ihm =>
        rw [Function.iterate_succ_apply']
        exact data.step_mem _ ihm
  have hincrement : ∀ m : ℕ,
      ‖((data.step^[m]) s).2‖ ≤
        data.transport ^ m * ‖s.2‖ := by
    intro m
    induction m with
    | zero =>
        simp
    | succ m ihm =>
        rw [Function.iterate_succ_apply']
        have hstep := data.increment_norm_le ((data.step^[m]) s) (hstep_mem m)
        have hscaled := mul_le_mul_of_nonneg_left ihm data.transport_nonneg
        calc
          ‖(data.step ((data.step^[m]) s)).2‖ ≤
              data.transport * ‖((data.step^[m]) s).2‖ := hstep
          _ ≤ data.transport * (data.transport ^ m * ‖s.2‖) :=
            hscaled
          _ = data.transport ^ (m + 1) * ‖s.2‖ := by
            rw [pow_succ]
            ring
  have hiterate : ∀ m : ℕ,
      data.error s ≤
        data.contraction ^ m * data.error ((data.step^[m]) s) +
          data.forcing * ‖s.2‖ *
            ∑ j ∈ Finset.range m,
              (data.contraction * data.transport) ^ j := by
    intro m
    induction m with
    | zero =>
        simp
    | succ m ihm =>
        have hrec := data.recurrence ((data.step^[m]) s) (hstep_mem m)
        have hscaled := mul_le_mul_of_nonneg_left hrec
          (pow_nonneg data.contraction_nonneg m)
        have hforcing :
            data.forcing * ‖((data.step^[m]) s).2‖ ≤
              data.forcing * (data.transport ^ m * ‖s.2‖) := by
          exact mul_le_mul_of_nonneg_left (hincrement m) data.forcing_nonneg
        calc
          data.error s ≤
              data.contraction ^ m * data.error ((data.step^[m]) s) +
                data.forcing * ‖s.2‖ *
                  ∑ j ∈ Finset.range m,
                    (data.contraction * data.transport) ^ j := ihm
          _ ≤ data.contraction ^ m *
                (data.contraction *
                    data.error (data.step ((data.step^[m]) s)) +
                  data.forcing * ‖((data.step^[m]) s).2‖) +
                data.forcing * ‖s.2‖ *
                  ∑ j ∈ Finset.range m,
                    (data.contraction * data.transport) ^ j := by
            exact add_le_add_left hscaled _
          _ ≤ data.contraction ^ m *
                (data.contraction *
                    data.error (data.step ((data.step^[m]) s)) +
                  data.forcing * (data.transport ^ m * ‖s.2‖)) +
            data.forcing * ‖s.2‖ *
                  ∑ j ∈ Finset.range m,
                    (data.contraction * data.transport) ^ j := by
            have hinner :
                data.contraction *
                    data.error (data.step ((data.step^[m]) s)) +
                    data.forcing * ‖((data.step^[m]) s).2‖ ≤
                  data.contraction *
                    data.error (data.step ((data.step^[m]) s)) +
                    data.forcing * (data.transport ^ m * ‖s.2‖) :=
              add_le_add_right hforcing _
            have hmul := mul_le_mul_of_nonneg_left hinner
              (pow_nonneg data.contraction_nonneg m)
            exact add_le_add_left hmul _
          _ = data.contraction ^ (m + 1) *
                data.error ((data.step^[m + 1]) s) +
                data.forcing * ‖s.2‖ *
                  ∑ j ∈ Finset.range (m + 1),
                    (data.contraction * data.transport) ^ j := by
            rw [Finset.sum_range_succ, Function.iterate_succ_apply', pow_succ]
            ring_nf
  exact hiterate n

/-- Infrastructure I.16a: a finite transported-increment certificate packages
the terminal estimate, radius envelope, and weighted budget consumed by the
graph-transform residual bound. -/
structure FiniteTransportedIncrementBudgetCertificate
    (Θ : Type u) (K : Set (TransportedIncrementState Θ)) where
  recurrenceData : TransportedIncrementRecurrenceData Θ K
  radius : ℝ
  radius_nonneg : 0 ≤ radius
  steps : ℕ
  terminalBound : ℝ
  budget : ℝ
  increment_norm_le : ∀ s ∈ K, ‖s.2‖ ≤ radius
  terminal_error_le : ∀ s ∈ K,
    recurrenceData.error ((recurrenceData.step^[steps]) s) ≤ terminalBound
  weighted_budget_le :
    recurrenceData.contraction ^ steps * terminalBound +
        recurrenceData.forcing * radius *
          ∑ j ∈ Finset.range steps,
            (recurrenceData.contraction * recurrenceData.transport) ^ j ≤ budget

/-- Infrastructure I.16a: the finite transported-increment certificate bounds
the initial error by its declared terminal-plus-forcing budget. -/
theorem FiniteTransportedIncrementBudgetCertificate.error_le_budget
    {Θ : Type u} {K : Set (TransportedIncrementState Θ)}
    (certificate : FiniteTransportedIncrementBudgetCertificate Θ K)
    {s : TransportedIncrementState Θ} (hs : s ∈ K) :
    certificate.recurrenceData.error s ≤ certificate.budget := by
  have hiter := certificate.recurrenceData.iterate hs certificate.steps
  have hterminal := certificate.terminal_error_le s hs
  have hincrement := certificate.increment_norm_le s hs
  calc
    certificate.recurrenceData.error s ≤
        certificate.recurrenceData.contraction ^ certificate.steps *
            certificate.recurrenceData.error
              ((certificate.recurrenceData.step^[certificate.steps]) s) +
          certificate.recurrenceData.forcing * ‖s.2‖ *
            ∑ j ∈ Finset.range certificate.steps,
              (certificate.recurrenceData.contraction *
                certificate.recurrenceData.transport) ^ j := hiter
    _ ≤ certificate.recurrenceData.contraction ^ certificate.steps * certificate.terminalBound +
          certificate.recurrenceData.forcing * certificate.radius *
            ∑ j ∈ Finset.range certificate.steps,
              (certificate.recurrenceData.contraction *
                certificate.recurrenceData.transport) ^ j := by
      have hpow : 0 ≤ certificate.recurrenceData.contraction ^ certificate.steps :=
        pow_nonneg certificate.recurrenceData.contraction_nonneg _
      have hsum : 0 ≤ ∑ j ∈ Finset.range certificate.steps,
          (certificate.recurrenceData.contraction *
            certificate.recurrenceData.transport) ^ j := by
        apply Finset.sum_nonneg
        intro j hj
        exact pow_nonneg
          (mul_nonneg certificate.recurrenceData.contraction_nonneg
            certificate.recurrenceData.transport_nonneg) _
      have hterm :
          certificate.recurrenceData.contraction ^ certificate.steps *
              certificate.recurrenceData.error
                ((certificate.recurrenceData.step^[certificate.steps]) s) ≤
            certificate.recurrenceData.contraction ^ certificate.steps *
              certificate.terminalBound :=
        mul_le_mul_of_nonneg_left hterminal hpow
      have hforce :
          certificate.recurrenceData.forcing * ‖s.2‖ *
              ∑ j ∈ Finset.range certificate.steps,
                (certificate.recurrenceData.contraction *
                  certificate.recurrenceData.transport) ^ j ≤
            certificate.recurrenceData.forcing * certificate.radius *
              ∑ j ∈ Finset.range certificate.steps,
                (certificate.recurrenceData.contraction *
                  certificate.recurrenceData.transport) ^ j := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hincrement
            certificate.recurrenceData.forcing_nonneg) hsum
      exact add_le_add hterm hforce
    _ ≤ certificate.budget := certificate.weighted_budget_le

end LocalCutoff.GraphTransform
