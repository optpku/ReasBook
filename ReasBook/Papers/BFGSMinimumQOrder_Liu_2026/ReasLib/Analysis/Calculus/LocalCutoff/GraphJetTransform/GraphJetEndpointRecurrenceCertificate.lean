module

public import ReasLib.Analysis.Calculus.LocalCutoff.GraphJetTransform.AllOnesBranchTransportCertificate
public import ReasLib.Analysis.Calculus.LocalCutoff.GraphJetTransform.PredecessorSecantRecurrenceAdapter
public import ReasLib.Analysis.Calculus.LocalCutoff.GraphJetTransform.SourceTransportedIncrementAdapter
public import ReasLib.Analysis.Calculus.LocalCutoff.GraphJetTransform.FixedSectionDerivativeBridge

public section

open scoped BigOperators Topology

universe u v

namespace LocalCutoff.GraphTransform

/-!
This module is the source-facing endpoint bridge for the orderwise graph-jet
recurrence.  It keeps the center and increment as the pair `(u, t)`, records
the all-ones and filtered branches separately, and delegates finite iteration
to `FiniteTransportedIncrementBudgetCertificate`.
-/

/-- Infrastructure I.16a: a graph-jet endpoint certificate records the
all-ones transport identity, the filtered finite-branch decomposition, an
existing finite transported-increment budget, and the source-local
arbitrary-forcing endpoint recurrence on the state space `(u, t)`. -/
structure GraphJetEndpointRecurrenceCertificate
    (ι : Type u) (E : Type v)
    [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Set (ℝ × ℝ)) where
  budgetCertificate : FiniteTransportedIncrementBudgetCertificate ℝ K
  defect : ℝ → ℝ → E
  forward : ℝ → ℝ
  inverse : ℝ → ℝ
  stepEq : budgetCertificate.recurrenceData.step =
    predecessorSecantStep forward inverse
  errorEq : budgetCertificate.recurrenceData.error =
    fun s : ℝ × ℝ ↦ ‖defect s.1 s.2‖
  predecessorErrorEq : budgetCertificate.recurrenceData.error =
    predecessorSecantError defect
  distinguished : ι
  live : ℝ × ℝ → E
  allOnes : AllOnesBranchTransportCertificate ℝ E
  filtered : ℝ × ℝ → E
  branches : ι → ℝ × ℝ → E
  liveEqDefect : ∀ s, live s = defect s.1 s.2
  liveEqAllOnesAddFiltered : ∀ s,
    live s = allOnes.principal s.1 s.2 + filtered s
  filteredEqNonDistinguished : ∀ s,
    filtered s = ∑ i, if i = distinguished then 0 else branches i s
  transportedEqSuccessor : ∀ s,
    allOnes.transported s.1 s.2 =
      budgetCertificate.recurrenceData.contraction •
        defect (budgetCertificate.recurrenceData.step s).1
          (budgetCertificate.recurrenceData.step s).2
  branchScale : ℝ
  branchNormLe : ∀ i, i ≠ distinguished → ∀ s ∈ K,
    ‖branches i s‖ ≤ branchScale * ‖s.2‖
  branchBudgetLe :
    ((Fintype.card ι : ℝ) - 1) * branchScale ≤
      budgetCertificate.recurrenceData.forcing
  sourceEndpointRecurrence : ∀ η : ℝ, 0 < η →
    ∃ δ > 0, ∀ u s : ℝ, s ≠ 0 → ‖s‖ < δ →
      ‖defect u s‖ ≤
        budgetCertificate.recurrenceData.contraction *
            ‖defect (inverse u) (inverse (u + s) - inverse u)‖ +
          η * ‖s‖

/-- Helper for Infrastructure I.16a: the endpoint certificate exposes the existing
`PredecessorSecantRecurrenceInterface` without changing its `(u, t)` state. -/
def GraphJetEndpointRecurrenceCertificate.toPredecessorInterface
    {ι : Type u} {E : Type v}
    [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set (ℝ × ℝ)}
    (certificate : GraphJetEndpointRecurrenceCertificate ι E K) :
    PredecessorSecantRecurrenceInterface E K :=
  { defect := certificate.defect
    forward := certificate.forward
    inverse := certificate.inverse
    data := certificate.budgetCertificate.recurrenceData
    step_eq := certificate.stepEq
    error_eq := certificate.predecessorErrorEq }

/-- Helper for Infrastructure I.16a: the stored recurrence step has the concrete source
normal form `(inverse (forward u), inverse (u + t) - inverse u)`. -/
theorem GraphJetEndpointRecurrenceCertificate.step_at_pair
    {ι : Type u} {E : Type v}
    [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set (ℝ × ℝ)}
    (certificate : GraphJetEndpointRecurrenceCertificate ι E K)
    (u t : ℝ) :
    certificate.budgetCertificate.recurrenceData.step (u, t) =
      (certificate.inverse (certificate.forward u),
        certificate.inverse (u + t) - certificate.inverse u) := by
  have hstep := congrFun certificate.stepEq (u, t)
  simpa only [predecessorSecantStep_pair] using hstep

/-- Helper for Infrastructure I.16a: the stored scalar error is exactly the norm of the
source defect at `(u, t)`. -/
theorem GraphJetEndpointRecurrenceCertificate.error_at_pair
    {ι : Type u} {E : Type v}
    [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set (ℝ × ℝ)}
    (certificate : GraphJetEndpointRecurrenceCertificate ι E K)
    (u t : ℝ) :
    certificate.budgetCertificate.recurrenceData.error (u, t) =
      ‖certificate.defect u t‖ := by
  exact congrFun certificate.errorEq (u, t)

/-- Helper for Infrastructure I.16a: the all-ones branch is transported to the exact
successor defect, with no fixed-radius substitution. -/
theorem GraphJetEndpointRecurrenceCertificate.allOnes_transport_at_pair
    {ι : Type u} {E : Type v}
    [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set (ℝ × ℝ)}
    (certificate : GraphJetEndpointRecurrenceCertificate ι E K)
    (u t : ℝ) :
    certificate.allOnes.transported u t =
      certificate.budgetCertificate.recurrenceData.contraction •
        certificate.defect (certificate.inverse (certificate.forward u))
          (certificate.inverse (u + t) - certificate.inverse u) := by
  have htransport := certificate.transportedEqSuccessor (u, t)
  rw [certificate.step_at_pair] at htransport
  exact htransport

/-- Helper for Infrastructure I.16a: the all-ones principal branch has the same explicit
successor normal form after applying its transport certificate. -/
theorem GraphJetEndpointRecurrenceCertificate.allOnes_principal_at_pair
    {ι : Type u} {E : Type v}
    [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set (ℝ × ℝ)}
    (certificate : GraphJetEndpointRecurrenceCertificate ι E K)
    (u t : ℝ) :
    certificate.allOnes.principal u t =
      certificate.budgetCertificate.recurrenceData.contraction •
        certificate.defect (certificate.inverse (certificate.forward u))
          (certificate.inverse (u + t) - certificate.inverse u) := by
  rw [certificate.allOnes.principal_eq_transported]
  exact certificate.allOnes_transport_at_pair u t

/-- Helper for Infrastructure I.16a: the finite non-ones branches satisfy the aggregate
forcing estimate required by the transported recurrence. -/
theorem GraphJetEndpointRecurrenceCertificate.filtered_norm_le_at_pair
    {ι : Type u} {E : Type v}
    [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set (ℝ × ℝ)}
    (certificate : GraphJetEndpointRecurrenceCertificate ι E K)
    {u t : ℝ} (hstate : (u, t) ∈ K) :
    ‖certificate.filtered (u, t)‖ ≤
      certificate.budgetCertificate.recurrenceData.forcing * ‖t‖ := by
  rw [certificate.filteredEqNonDistinguished]
  have hbudget := mul_le_mul_of_nonneg_right certificate.branchBudgetLe
    (norm_nonneg t)
  have hbudget' :
      ((Fintype.card ι : ℝ) - 1) *
          (certificate.branchScale * ‖t‖) ≤
        certificate.budgetCertificate.recurrenceData.forcing * ‖t‖ := by
    calc
      ((Fintype.card ι : ℝ) - 1) *
          (certificate.branchScale * ‖t‖) =
          (((Fintype.card ι : ℝ) - 1) * certificate.branchScale) * ‖t‖ := by
            ring
      _ ≤ certificate.budgetCertificate.recurrenceData.forcing * ‖t‖ := hbudget
  exact norm_sum_if_eq_zero_le
    (fun i ↦ certificate.branches i (u, t)) certificate.distinguished
    (certificate.branchScale * ‖t‖)
    (certificate.budgetCertificate.recurrenceData.forcing * ‖t‖)
    (fun i hi ↦ certificate.branchNormLe i hi (u, t) hstate) hbudget'

/-- Helper for Infrastructure I.16a: the all-ones and filtered branch identities yield
the source recurrence at a concrete `(u, t)` state. -/
theorem GraphJetEndpointRecurrenceCertificate.branch_recurrence_at_pair
    {ι : Type u} {E : Type v}
    [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set (ℝ × ℝ)}
    (certificate : GraphJetEndpointRecurrenceCertificate ι E K)
    {u t : ℝ} (hstate : (u, t) ∈ K) :
    ‖certificate.defect u t‖ ≤
      certificate.budgetCertificate.recurrenceData.contraction *
          ‖certificate.defect
            (certificate.budgetCertificate.recurrenceData.step (u, t)).1
            (certificate.budgetCertificate.recurrenceData.step (u, t)).2‖ +
        certificate.budgetCertificate.recurrenceData.forcing * ‖t‖ := by
  have hfiltered := certificate.filtered_norm_le_at_pair hstate
  have hprincipal :
      ‖certificate.allOnes.principal u t‖ ≤
        certificate.budgetCertificate.recurrenceData.contraction *
          ‖certificate.defect
            (certificate.budgetCertificate.recurrenceData.step (u, t)).1
            (certificate.budgetCertificate.recurrenceData.step (u, t)).2‖ := by
    calc
      ‖certificate.allOnes.principal u t‖ =
          ‖certificate.allOnes.transported u t‖ := by
        rw [certificate.allOnes.principal_eq_transported u t]
      _ = ‖certificate.budgetCertificate.recurrenceData.contraction •
            certificate.defect (certificate.inverse (certificate.forward u))
              (certificate.inverse (u + t) - certificate.inverse u)‖ := by
        rw [certificate.allOnes_transport_at_pair]
      _ = certificate.budgetCertificate.recurrenceData.contraction *
            ‖certificate.defect (certificate.inverse (certificate.forward u))
              (certificate.inverse (u + t) - certificate.inverse u)‖ := by
        rw [norm_smul, Real.norm_eq_abs,
          abs_of_nonneg certificate.budgetCertificate.recurrenceData.contraction_nonneg]
      _ ≤ certificate.budgetCertificate.recurrenceData.contraction *
            ‖certificate.defect
              (certificate.budgetCertificate.recurrenceData.step (u, t)).1
              (certificate.budgetCertificate.recurrenceData.step (u, t)).2‖ := by
        rw [certificate.step_at_pair]
  calc
    ‖certificate.defect u t‖ = ‖certificate.live (u, t)‖ := by
      rw [certificate.liveEqDefect]
    _ = ‖certificate.allOnes.principal u t + certificate.filtered (u, t)‖ := by
      rw [certificate.liveEqAllOnesAddFiltered]
    _ ≤ ‖certificate.allOnes.principal u t‖ +
          ‖certificate.filtered (u, t)‖ := norm_add_le _ _
    _ ≤ certificate.budgetCertificate.recurrenceData.contraction *
          ‖certificate.defect
            (certificate.budgetCertificate.recurrenceData.step (u, t)).1
            (certificate.budgetCertificate.recurrenceData.step (u, t)).2‖ +
          certificate.budgetCertificate.recurrenceData.forcing * ‖t‖ :=
      add_le_add hprincipal hfiltered

/-- Helper for Infrastructure I.16a: the source recurrence is available with the inverse
center step written explicitly, through the existing predecessor adapter. -/
theorem GraphJetEndpointRecurrenceCertificate.recurrence_at_pair
    {ι : Type u} {E : Type v}
    [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set (ℝ × ℝ)}
    (certificate : GraphJetEndpointRecurrenceCertificate ι E K)
    {u t : ℝ} (hstate : (u, t) ∈ K) :
    ‖certificate.defect u t‖ ≤
      certificate.budgetCertificate.recurrenceData.contraction *
          ‖certificate.defect
            (certificate.inverse (certificate.forward u))
            (certificate.inverse (u + t) - certificate.inverse u)‖ +
        certificate.budgetCertificate.recurrenceData.forcing * ‖t‖ := by
  have hrec := certificate.budgetCertificate.recurrenceData.recurrence
    (u, t) hstate
  rw [certificate.errorEq, certificate.step_at_pair] at hrec
  exact hrec

/-- Helper for Infrastructure I.16a: the branch decomposition supplies the recurrence in
the exact error/step shape expected by `TransportedIncrementRecurrenceData`. -/
theorem GraphJetEndpointRecurrenceCertificate.branch_recurrence_data
    {ι : Type u} {E : Type v}
    [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set (ℝ × ℝ)}
    (certificate : GraphJetEndpointRecurrenceCertificate ι E K) :
    ∀ s ∈ K,
      certificate.budgetCertificate.recurrenceData.error s ≤
        certificate.budgetCertificate.recurrenceData.contraction *
            certificate.budgetCertificate.recurrenceData.error
              (certificate.budgetCertificate.recurrenceData.step s) +
          certificate.budgetCertificate.recurrenceData.forcing * ‖s.2‖ := by
  intro s hs
  rcases s with ⟨u, t⟩
  have hbranch := certificate.branch_recurrence_at_pair hs
  rw [certificate.errorEq, certificate.step_at_pair]
  rw [certificate.step_at_pair] at hbranch
  simpa only [Prod.fst, Prod.snd] using hbranch

/-- Helper for Infrastructure I.16a: a genuine predecessor recurrence and the
left-inverse identity for the center map give the parent-facing forward
endpoint recurrence without changing the transported `(u, t)` state. -/
theorem forwardEndpointRecurrenceOfTransport
    {E : Type u} [NormedAddCommGroup E]
    (defect : ℝ → ℝ → E) (forward inverse : ℝ → ℝ)
    (p η : ℝ)
    (hrec : ∃ δ > 0, ∀ u s : ℝ, s ≠ 0 → ‖s‖ < δ →
      ‖defect u s‖ ≤
        p * ‖defect (inverse u) (inverse (u + s) - inverse u)‖ +
          η * ‖s‖)
    (hleft : ∀ v, inverse (forward v) = v) :
    ∃ δ > 0, ∀ v s : ℝ, s ≠ 0 → ‖s‖ < δ →
      ‖defect (forward v) s‖ ≤
        p * ‖defect v (inverse (forward v + s) - v)‖ +
          η * ‖s‖ := by
  obtain ⟨δ, hδ, hrec⟩ := hrec
  refine ⟨δ, hδ, ?_⟩
  intro v s hs hsδ
  have hforward := hrec (forward v) s hs hsδ
  rw [hleft v] at hforward
  exact hforward

/-- Helper for Infrastructure I.16a: the endpoint certificate transfers its
source-local arbitrary-forcing recurrence to the forward center coordinate. -/
theorem GraphJetEndpointRecurrenceCertificate.forwardEndpointRecurrence
    {ι : Type u} {E : Type v}
    [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set (ℝ × ℝ)}
    (certificate : GraphJetEndpointRecurrenceCertificate ι E K)
    (hleft : ∀ v, certificate.inverse (certificate.forward v) = v)
    (η : ℝ) (hη : 0 < η) :
    ∃ δ > 0, ∀ v s : ℝ, s ≠ 0 → ‖s‖ < δ →
      ‖certificate.defect (certificate.forward v) s‖ ≤
        certificate.budgetCertificate.recurrenceData.contraction *
            ‖certificate.defect v
              (certificate.inverse (certificate.forward v + s) - v)‖ +
          η * ‖s‖ := by
  exact forwardEndpointRecurrenceOfTransport
    certificate.defect certificate.forward certificate.inverse
    certificate.budgetCertificate.recurrenceData.contraction η
    (certificate.sourceEndpointRecurrence η hη) hleft

/-- Helper for Infrastructure I.16a: a uniformly sublinear successor defect is
absorbed by the strict endpoint contraction and yields a little-o estimate at
each forward center. -/
theorem GraphJetEndpointRecurrenceCertificate.isLittleOForwardOfSublinearSuccessor
    {ι : Type u} {E : Type v}
    [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set (ℝ × ℝ)}
    (certificate : GraphJetEndpointRecurrenceCertificate ι E K)
    (hleft : ∀ v, certificate.inverse (certificate.forward v) = v)
    (hcontraction : certificate.budgetCertificate.recurrenceData.contraction < 1)
    (hdefect_zero : ∀ v, certificate.defect v 0 = 0)
    (hsuccessor : ∀ ε : ℝ, 0 < ε →
      ∃ δ > 0, ∀ v s : ℝ, s ≠ 0 → ‖s‖ < δ →
        ‖certificate.defect v
          (certificate.inverse (certificate.forward v + s) - v)‖ ≤
          ε * ‖s‖) :
    ∀ v : ℝ,
      (fun h : ℝ ↦ certificate.defect (certificate.forward v) h) =o[𝓝 0]
        (fun h : ℝ ↦ h) := by
  intro v
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  obtain ⟨δrec, hδrec, hrec⟩ :=
    certificate.forwardEndpointRecurrence hleft (ε / 2) hhalf
  obtain ⟨δsucc, hδsucc, hsucc⟩ := hsuccessor (ε / 2) hhalf
  let δ := min δrec δsucc
  have hδ : 0 < δ := lt_min hδrec hδsucc
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with h hh
  have hhδ : ‖h‖ < δ := by
    simpa only [Metric.mem_ball, dist_zero_right] using hh
  by_cases hzero : h = 0
  · subst h
    rw [hdefect_zero]
    simp
  · have hhrec : ‖h‖ < δrec :=
      lt_of_lt_of_le hhδ (min_le_left _ _)
    have hhsucc : ‖h‖ < δsucc :=
      lt_of_lt_of_le hhδ (min_le_right _ _)
    have hrec' := hrec v h hzero hhrec
    have hsucc' := hsucc v h hzero hhsucc
    have hsucc_mul := mul_le_mul_of_nonneg_left hsucc'
      certificate.budgetCertificate.recurrenceData.contraction_nonneg
    have hsum := add_le_add_left hsucc_mul ((ε / 2) * ‖h‖)
    have hp_le : certificate.budgetCertificate.recurrenceData.contraction ≤ 1 :=
      le_of_lt hcontraction
    have hhalf_nonneg : 0 ≤ ε / 2 := hhalf.le
    have hfactor_nonneg : 0 ≤ (ε / 2) * ‖h‖ :=
      mul_nonneg hhalf_nonneg (norm_nonneg h)
    have hpterm :
        certificate.budgetCertificate.recurrenceData.contraction *
            ((ε / 2) * ‖h‖) ≤
          1 * ((ε / 2) * ‖h‖) :=
      mul_le_mul_of_nonneg_right hp_le hfactor_nonneg
    calc
      ‖certificate.defect (certificate.forward v) h‖ ≤
          certificate.budgetCertificate.recurrenceData.contraction *
              ‖certificate.defect v
                (certificate.inverse (certificate.forward v + h) - v)‖ +
            (ε / 2) * ‖h‖ := hrec'
      _ ≤ certificate.budgetCertificate.recurrenceData.contraction *
            ((ε / 2) * ‖h‖) + (ε / 2) * ‖h‖ := hsum
      _ ≤ 1 * ((ε / 2) * ‖h‖) + (ε / 2) * ‖h‖ :=
        add_le_add_left hpterm _
      _ = ε * ‖h‖ := by ring

/-- Helper for Infrastructure I.16a: an endpoint defect representation turns the
sublinear-successor estimate into the predecessor derivative equation. -/
theorem GraphJetEndpointRecurrenceCertificate.hasFDerivAt_of_sublinearSuccessor
    {ι : Type u} {E : Type v}
    [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set (ℝ × ℝ)}
    (certificate : GraphJetEndpointRecurrenceCertificate ι E K)
    (hleft : ∀ v, certificate.inverse (certificate.forward v) = v)
    (hcontraction : certificate.budgetCertificate.recurrenceData.contraction < 1)
    (hdefect_zero : ∀ v, certificate.defect v 0 = 0)
    (hsuccessor : ∀ ε : ℝ, 0 < ε →
      ∃ δ > 0, ∀ v s : ℝ, s ≠ 0 → ‖s‖ < δ →
        ‖certificate.defect v
          (certificate.inverse (certificate.forward v + s) - v)‖ ≤
          ε * ‖s‖)
    (p : ℝ → E) (A : ℝ →L[ℝ] E)
    (hrepresentation : ∀ v h : ℝ,
      certificate.defect (certificate.forward v) h =
        p (v + h) - p v - A h) :
    ∀ v, HasFDerivAt p A v := by
  intro v
  have hlittle := certificate.isLittleOForwardOfSublinearSuccessor hleft
    hcontraction hdefect_zero hsuccessor v
  have hrem :
      (fun h : ℝ ↦ p (v + h) - p v - A h) =o[𝓝 0] (fun h : ℝ ↦ h) := by
    exact hlittle.congr_left (fun h ↦ hrepresentation v h)
  exact hasFDerivAt_of_isLittleO_shift_bridge p v A hrem

/-- Helper for Infrastructure I.16a: the inverse-center successor remains in the source
state set, preserving the step-membership field needed by iteration. -/
theorem GraphJetEndpointRecurrenceCertificate.step_mem_at_pair
    {ι : Type u} {E : Type v}
    [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set (ℝ × ℝ)}
    (certificate : GraphJetEndpointRecurrenceCertificate ι E K)
    {u t : ℝ} (hstate : (u, t) ∈ K) :
    (certificate.inverse (certificate.forward u),
      certificate.inverse (u + t) - certificate.inverse u) ∈ K := by
  exact certificate.toPredecessorInterface.step_mem_at_pair hstate

/-- Helper for Infrastructure I.16a: the transported increment has the declared norm
factor at a concrete source pair. -/
theorem GraphJetEndpointRecurrenceCertificate.increment_norm_le_at_pair
    {ι : Type u} {E : Type v}
    [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set (ℝ × ℝ)}
    (certificate : GraphJetEndpointRecurrenceCertificate ι E K)
    {u t : ℝ} (hstate : (u, t) ∈ K) :
    ‖certificate.inverse (u + t) - certificate.inverse u‖ ≤
      certificate.budgetCertificate.recurrenceData.transport * ‖t‖ := by
  exact certificate.toPredecessorInterface.increment_norm_le_at_pair hstate

/-- Helper for Infrastructure I.16a: the finite budget certificate exposes its terminal
error and weighted forcing fields at `(u, t)`, while retaining the source
defect notation. -/
theorem GraphJetEndpointRecurrenceCertificate.source_budget_interface
    {ι : Type u} {E : Type v}
    [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set (ℝ × ℝ)}
    (certificate : GraphJetEndpointRecurrenceCertificate ι E K)
    {u t : ℝ} (hstate : (u, t) ∈ K) :
    ‖t‖ ≤ certificate.budgetCertificate.radius ∧
      ‖certificate.defect
          ((certificate.budgetCertificate.recurrenceData.step^[
            certificate.budgetCertificate.steps]) (u, t)).1
          ((certificate.budgetCertificate.recurrenceData.step^[
            certificate.budgetCertificate.steps]) (u, t)).2‖ ≤
        certificate.budgetCertificate.terminalBound ∧
      certificate.budgetCertificate.recurrenceData.contraction ^
            certificate.budgetCertificate.steps *
          certificate.budgetCertificate.terminalBound +
        certificate.budgetCertificate.recurrenceData.forcing *
            certificate.budgetCertificate.radius *
          ∑ j ∈ Finset.range certificate.budgetCertificate.steps,
            (certificate.budgetCertificate.recurrenceData.contraction *
              certificate.budgetCertificate.recurrenceData.transport) ^ j ≤
        certificate.budgetCertificate.budget ∧
      ‖certificate.defect u t‖ ≤ certificate.budgetCertificate.budget := by
  obtain ⟨hincrement, hterminal, hweighted, herror⟩ :=
    certificate.budgetCertificate.source_budget_interface hstate
  have hterminal' :
      ‖certificate.defect
          ((certificate.budgetCertificate.recurrenceData.step^[
            certificate.budgetCertificate.steps]) (u, t)).1
          ((certificate.budgetCertificate.recurrenceData.step^[
            certificate.budgetCertificate.steps]) (u, t)).2‖ ≤
        certificate.budgetCertificate.terminalBound := by
    rw [certificate.errorEq] at hterminal
    exact hterminal
  have herror' : ‖certificate.defect u t‖ ≤ certificate.budgetCertificate.budget := by
    rw [certificate.errorEq] at herror
    exact herror
  exact ⟨hincrement, hterminal', hweighted, herror'⟩

/-- Helper for Infrastructure I.16a: the stored finite transported-increment certificate
already is the budget projection consumed by the generic iteration theorem. -/
def GraphJetEndpointRecurrenceCertificate.to_finite_budget
    {ι : Type u} {E : Type v}
    [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set (ℝ × ℝ)}
    (certificate : GraphJetEndpointRecurrenceCertificate ι E K) :
    FiniteTransportedIncrementBudgetCertificate ℝ K :=
  certificate.budgetCertificate

/-- Helper for Infrastructure I.16a: the endpoint live branch is bounded by the existing
finite transported-increment budget, with no replacement of the `(u, t)` state. -/
theorem GraphJetEndpointRecurrenceCertificate.live_norm_le_budget
    {ι : Type u} {E : Type v}
    [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set (ℝ × ℝ)}
    (certificate : GraphJetEndpointRecurrenceCertificate ι E K)
    {u t : ℝ} (hstate : (u, t) ∈ K) :
    ‖certificate.live (u, t)‖ ≤ certificate.budgetCertificate.budget := by
  have herror := certificate.budgetCertificate.error_le_budget hstate
  rw [certificate.errorEq] at herror
  rw [certificate.liveEqDefect]
  exact herror

end LocalCutoff.GraphTransform
