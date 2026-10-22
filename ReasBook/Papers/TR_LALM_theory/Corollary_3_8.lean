/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import Mathlib.Algebra.Order.Floor.Div
public import Mathlib.Probability.Process.HittingTime
public import TR_LALM_theory.Theorem_3_6.OperationalTrace
public import TR_LALM_theory.Theorem_3_7
public import TR_LALM_theory.Corollary_3_8.CanonicalStoppedAttempt
public import TR_LALM_theory.Corollary_3_8.FiniteStoppedSemantics
public import TR_LALM_theory.Corollary_3_8.FiniteStoppedEnergy
public import TR_LALM_theory.Corollary_3_8.FiniteStoppedPrefixInvariant
public import TR_LALM_theory.Corollary_3_8.FiniteStoppedEnergyRecursion
public import TR_LALM_theory.Corollary_3_8.FiniteStoppedPath
public import TR_LALM_theory.Corollary_3_8.FiniteStoppedPathRealization
public import TR_LALM_theory.Corollary_3_8.FiniteStoppedSchedule
public import TR_LALM_theory.Corollary_3_8.FiniteStoppedLocalization
public import TR_LALM_theory.Corollary_3_8.FiniteStoppedExitGeometry
public import TR_LALM_theory.Corollary_3_8.FiniteStoppedCanonicalPath
public import TR_LALM_theory.Corollary_3_8.FiniteStoppedResidual
public import TR_LALM_theory.Corollary_3_8.FiniteStoppedCertificate
public import TR_LALM_theory.Corollary_3_8.FiniteStoppedOutput
public import TR_LALM_theory.Corollary_3_8.FiniteStoppedRestart
public import TR_LALM_theory.Corollary_3_8.FiniteStoppedRestartProbability
public import TR_LALM_theory.Corollary_3_8.FiniteStoppedRestartAccounting
public import TR_LALM_theory.Corollary_3_8.FiniteStoppedCertifiedRestart
public import TR_LALM_theory.Corollary_3_8.FiniteStoppedRestartResidualLaw
public import TR_LALM_theory.Corollary_3_8.FiniteStoppedRestartResidual
public import TR_LALM_theory.Corollary_3_8.FiniteStoppedCanonicalRestart
public import TR_LALM_theory.Corollary_3_8.FiniteStoppedCorollary
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Probability.Independence.Integration
import TR_LALM_theory.Theorem_3_7

/-!
# Full-tail restart coupling

This module uses complete stochastic-run witnesses as an exact-real coupling.
Its public success event, returned output, and accounting definitions inspect
only the finite prefix through the first localization exit; they do not assert
that the latent tail is evaluated after exit.  A literal absorbing state record
is therefore unnecessary for the base theorem.  The dedicated `Stopped*`
modules provide that stronger representation for the optional corrected
transition.  The base `Corollary_3_8.CanonicalStoppedAttempt` import additionally
exposes a finite absorbing construction and its canonical product realization.
The finite stopped path module derives the analytic prefix certificate directly
from the safe-parameter and clipped-gradient assumptions.
-/

public section

open MeasureTheory
open LALM.StochasticRun.UniformOutput
open scoped BigOperators ENNReal NNReal

namespace LALM

open StochasticRun.Localization

universe u v

variable {n m : ℕ}
variable {Ξ : Type u} [MeasurableSpace Ξ] {ν : Measure Ξ} [IsProbabilityMeasure ν]
variable {Ω : Type v} [MeasurableSpace Ω] {ℙ : Measure Ω} [IsProbabilityMeasure ℙ]
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
variable {x₀ : EuclideanSpace ℝ (Fin n)}
variable {multiplier₀ : EuclideanSpace ℝ (Fin m)}
variable {h : EqualityConstrained.Regularity f c}
variable {oracle : EqualityConstrained.StochasticOracle f h.region ν}
variable {params : LALM.Parameters h x₀ multiplier₀}

/-- A full-tail coupling wrapper carrying independent scheduled attempts and
uniform output selectors.  The scheduled attempts are complete probability
witnesses; the theorem-facing API observes and charges only their finite
localization-safe prefixes. -/
structure SafeguardedRestart
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (ℙ : Measure Ω) [IsProbabilityMeasure ℙ]
    (x₀ : EuclideanSpace ℝ (Fin n))
    (multiplier₀ : EuclideanSpace ℝ (Fin m))
    (params : LALM.Parameters h x₀ multiplier₀)
    (K : ℕ) (hK : 2 ≤ K)
    (X : Set (EuclideanSpace ℝ (Fin n))) where
  /-- The complete stochastic NR-LALM witness attached to each restart attempt.
  Values after a localization exit are retained by this coupling structure and
  must not be read as additional executed oracle calls. -/
  attempt (i : ℕ) : SPIDER.ScheduledRun h oracle ℙ x₀ multiplier₀ params K
  /-- The independent uniform selector used to return an iterate from each attempt. -/
  outputIndex (i : ℕ) (ω : Ω) : ℕ
  /-- Every selector is uniform on the indices `1, …, K - 1`. -/
  outputIndex_hasLaw (i : ℕ) :
    ProbabilityTheory.HasLaw (outputIndex i) (indexLaw K hK).toMeasure ℙ
  /-- Within an attempt, the selector is independent of the complete trajectory. -/
  outputIndex_indep_attempt (i : ℕ) :
    ProbabilityTheory.IndepFun (outputIndex i)
      (fun ω ↦
        (fun k j ↦ (attempt i).sample k j ω,
          fun k ↦ (attempt i).point k ω,
          fun k ↦ (attempt i).multiplier k ω,
          fun k ↦ (attempt i).step k ω)) ℙ
  /-- Complete attempt observables, including their selectors, are mutually independent. -/
  independent_attempt : ProbabilityTheory.iIndepFun
    (fun i ω ↦
      (outputIndex i ω,
        fun k j ↦ (attempt i).sample k j ω,
        fun k ↦ (attempt i).point k ω,
        fun k ↦ (attempt i).multiplier k ω,
        fun k ↦ (attempt i).step k ω)) ℙ

namespace SafeguardedRestart

variable {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}

/-- Helper for Corollary 3.8: classical membership decisions reflect
membership in the safeguard set. -/
private lemma classicalMembershipDecision_eq_true
    (x : EuclideanSpace ℝ (Fin n)) :
    @decide (x ∈ X) (Classical.propDecidable _) = true ↔ x ∈ X := by
  simp only [decide_eq_true_eq]

/-- The classical logical indicator that the full-tail witness survives all
`K` safeguard membership tests.  It is a prefix mask and does not provide an
executable membership oracle or claim that the witness tail was evaluated. -/
noncomputable def completionIndicator
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) (ω : Ω) : Bool :=
  (List.range K).all (fun k ↦
    @decide ((restart.attempt i).point (k + 1) ω ∈ X)
      (Classical.propDecidable _))

/-- An attempt completes exactly when all one-based iterates pass the safeguard. -/
theorem completionIndicator_eq_true
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) (ω : Ω) :
    restart.completionIndicator i ω = true ↔
      ∀ j ∈ Finset.Icc 1 K, (restart.attempt i).point j ω ∈ X := by
  -- Reindex the zero-based Boolean list by the one-based iteration interval.
  simp only [completionIndicator, List.all_eq_true, List.mem_range]
  constructor
  · intro hall j hj
    have hjBounds := Finset.mem_Icc.mp hj
    have hkBound : j - 1 < K := by omega
    have hindex : j - 1 + 1 = j := Nat.sub_add_cancel hjBounds.1
    have hpoint : (restart.attempt i).point (j - 1 + 1) ω ∈ X := by
      exact (classicalMembershipDecision_eq_true
        ((restart.attempt i).point (j - 1 + 1) ω)).mp (hall (j - 1) hkBound)
    simpa only [hindex] using hpoint
  · intro hall k hk
    have hmem : k + 1 ∈ Finset.Icc 1 K := by
      simp only [Finset.mem_Icc]
      omega
    exact (classicalMembershipDecision_eq_true
      ((restart.attempt i).point (k + 1) ω)).mpr (hall (k + 1) hmem)

/-- The event that attempt `i` completes all safeguarded iterations. -/
def successEvent
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) : Set Ω :=
  {ω | restart.completionIndicator i ω = true}

/-- The restart success event is the localization survival event of its run. -/
theorem successEvent_eq_survivalEvent
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) :
    restart.successEvent i = survivalEvent (restart.attempt i) X K := by
  -- Both events require the same one-based finite point prefix.
  ext ω
  simp only [successEvent, Set.mem_setOf_eq, completionIndicator_eq_true,
    mem_survivalEvent, Finset.mem_Icc, Set.mem_Icc]

/-- Helper for Corollary 3.8: the coupled success event is exactly the event
that the full-tail witness's first localization exit occurs strictly after the
charged horizon. -/
theorem successEvent_eq_firstExitSurvival
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) :
    restart.successEvent i =
      {ω | (K : WithTop ℕ) <
        StochasticRun.Localization.exitTime (restart.attempt i) X ω} := by
  rw [restart.successEvent_eq_survivalEvent]
  ext ω
  rw [StochasticRun.Localization.mem_survivalEvent]
  simp only [Set.mem_setOf_eq, ← not_le,
    StochasticRun.Localization.exitTime_le_iff]
  simp

/-- Helper for Corollary 3.8: pointwise form of the first-exit interpretation
of the coupled success event. -/
theorem mem_successEvent_iff_firstExit
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) (ω : Ω) :
    ω ∈ restart.successEvent i ↔
      (K : WithTop ℕ) <
        StochasticRun.Localization.exitTime (restart.attempt i) X ω := by
  rw [restart.successEvent_eq_firstExitSurvival]
  simp only [Set.mem_setOf_eq]

/-- The zero-based index of the first successful attempt, or `⊤`. -/
noncomputable def firstAccepted
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X) :
    Ω → WithTop ℕ :=
  MeasureTheory.hittingAfter restart.completionIndicator {true} 0

/-- The first accepted index is `⊤` exactly when every attempt fails. -/
theorem firstAccepted_eq_top_iff
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (ω : Ω) :
    restart.firstAccepted ω = ⊤ ↔ ∀ i, ω ∉ restart.successEvent i := by
  -- Apply the hitting-time characterization without crossing the `ENat` wrapper.
  rw [firstAccepted, MeasureTheory.hittingAfter_eq_top_iff]
  simp only [Nat.zero_le, true_imp_iff, successEvent, Set.mem_setOf_eq,
    Set.mem_singleton_iff]

/-- A finite first accepted index belongs to its success event. -/
theorem firstAccepted_mem_successEvent
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (ω : Ω) (htermination : restart.firstAccepted ω ≠ ⊤) :
    ω ∈ restart.successEvent ((restart.firstAccepted ω).untop htermination) := by
  -- The finite hitting time belongs to the target singleton.
  have hmem : restart.completionIndicator
      (restart.firstAccepted ω).untopA ω ∈ ({true} : Set Bool) := by
    simpa only [firstAccepted] using
      (MeasureTheory.hittingAfter_mem_set_of_ne_top
        (u := restart.completionIndicator) (s := ({true} : Set Bool))
        (n := 0) (ω := ω) htermination)
  have hindex : (restart.firstAccepted ω).untopA =
      (restart.firstAccepted ω).untop htermination := by
    exact WithTop.untopA_eq_untop htermination
  rw [hindex] at hmem
  simpa only [successEvent, Set.mem_setOf_eq, Set.mem_singleton_iff] using hmem

/-- Helper for Corollary 3.8: a finite first accepted index is characterized
by success there and failure at every earlier index. -/
theorem firstAccepted_eq_coe_iff
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) (ω : Ω) :
    restart.firstAccepted ω = (i : WithTop ℕ) ↔
      ω ∈ restart.successEvent i ∧ ∀ j < i, ω ∉ restart.successEvent j := by
  -- Use hitting-time minimality in both directions.
  constructor
  · intro hfirst
    have htermination : restart.firstAccepted ω ≠ ⊤ := by
      rw [hfirst]
      exact WithTop.coe_ne_top
    constructor
    · have hsuccess := restart.firstAccepted_mem_successEvent ω htermination
      have hindex : (restart.firstAccepted ω).untop htermination = i := by
        apply WithTop.coe_injective
        calc
          ((restart.firstAccepted ω).untop htermination : WithTop ℕ) =
              restart.firstAccepted ω := WithTop.coe_untop _ _
          _ = (i : WithTop ℕ) := hfirst
      rwa [hindex] at hsuccess
    · intro j hji
      have hjlt : (j : WithTop ℕ) < restart.firstAccepted ω := by
        rw [hfirst]
        exact_mod_cast hji
      have hjltHitting : (j : WithTop ℕ) < MeasureTheory.hittingAfter
          restart.completionIndicator ({true} : Set Bool) 0 ω := hjlt
      have hnotMem := MeasureTheory.notMem_of_lt_hittingAfter
        (u := restart.completionIndicator) (s := ({true} : Set Bool))
        (n := 0) (k := j) (ω := ω) hjltHitting (Nat.zero_le j)
      simpa only [successEvent, Set.mem_setOf_eq, Set.mem_singleton_iff] using hnotMem
  · rintro ⟨hiSuccess, hprior⟩
    have hiMem : restart.completionIndicator i ω ∈ ({true} : Set Bool) := by
      simpa only [successEvent, Set.mem_setOf_eq, Set.mem_singleton_iff] using hiSuccess
    have hleHitting :=
      MeasureTheory.hittingAfter_le_of_mem (u := restart.completionIndicator)
        (s := ({true} : Set Bool)) (n := 0) (ω := ω) (Nat.zero_le i) hiMem
    have hle : restart.firstAccepted ω ≤ (i : WithTop ℕ) := hleHitting
    have hge : (i : WithTop ℕ) ≤ restart.firstAccepted ω := by
      apply le_of_not_gt
      intro hlt
      have htermination : restart.firstAccepted ω ≠ ⊤ :=
        ne_top_of_lt (hlt.trans (WithTop.coe_lt_top i))
      have hjlt : (restart.firstAccepted ω).untop htermination < i := by
        exact (WithTop.untop_lt_iff htermination).mpr hlt
      apply hprior ((restart.firstAccepted ω).untop htermination) hjlt
      exact restart.firstAccepted_mem_successEvent ω htermination
    exact le_antisymm hle hge

/-- The one-based number of attempted runs, represented as an extended natural. -/
noncomputable def attemptCount
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (ω : Ω) : ℕ∞ :=
  (restart.firstAccepted ω).recTopCoe ⊤ (fun i ↦ (i + 1 : ℕ))

/-- The attempt count is infinite exactly when no attempt succeeds. -/
theorem attemptCount_eq_top_iff
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (ω : Ω) :
    restart.attemptCount ω = ⊤ ↔ restart.firstAccepted ω = ⊤ := by
  -- Eliminate the finite-or-infinite first-acceptance index.
  cases hfirst : restart.firstAccepted ω using WithTop.recTopCoe with
  | top => simp only [attemptCount, hfirst, WithTop.recTopCoe_top]
  | coe i =>
      simp only [attemptCount, hfirst, WithTop.recTopCoe_coe,
        ENat.coe_ne_top, WithTop.coe_ne_top]

/-- The returned primal point selected from the first successful attempt. -/
noncomputable def returnedPoint
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (ω : Ω) : EuclideanSpace ℝ (Fin n) :=
  let i := (restart.firstAccepted ω).untopD 0
  (restart.attempt i).point (restart.outputIndex i ω + 1) ω

/-- The returned point has its explicit first-accepted-index formula. -/
theorem returnedPoint_apply
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (ω : Ω) :
    restart.returnedPoint ω =
      (restart.attempt ((restart.firstAccepted ω).untopD 0)).point
        (restart.outputIndex ((restart.firstAccepted ω).untopD 0) ω + 1) ω := by
  rfl

/-- The returned multiplier selected from the first successful attempt. -/
noncomputable def returnedMultiplier
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (ω : Ω) : EuclideanSpace ℝ (Fin m) :=
  let i := (restart.firstAccepted ω).untopD 0
  (restart.attempt i).multiplier (restart.outputIndex i ω + 1) ω

/-- The returned multiplier has its explicit first-accepted-index formula. -/
theorem returnedMultiplier_apply
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (ω : Ω) :
    restart.returnedMultiplier ω =
      (restart.attempt ((restart.firstAccepted ω).untopD 0)).multiplier
        (restart.outputIndex ((restart.firstAccepted ω).untopD 0) ω + 1) ω := by
  rfl

/-- The expected squared KKT residual of the pair returned by the wrapper. -/
noncomputable def residualMeanSquare
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X) : ℝ≥0∞ :=
  KKT.Stochastic.residualMeanSquare ℙ f c restart.returnedPoint restart.returnedMultiplier

/-- The restart residual is the canonical stochastic KKT residual. -/
theorem residualMeanSquare_def
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X) :
    restart.residualMeanSquare =
      KKT.Stochastic.residualMeanSquare ℙ f c
        restart.returnedPoint restart.returnedMultiplier := by
  rfl

/-- Helper for Corollary 3.8: the complete observable type stored for one attempt. -/
private abbrev AttemptObservable (Ξ : Type u) (n m : ℕ) :=
  ℕ × ((ℕ → ℕ → Ξ) ×
    (ℕ → EuclideanSpace ℝ (Fin n)) ×
    (ℕ → EuclideanSpace ℝ (Fin m)) ×
    (ℕ → EuclideanSpace ℝ (Fin n)))

/-- Helper for Corollary 3.8: records whose point trajectory fails a safeguard test. -/
private def attemptFailureRecords
    (K : ℕ) (X : Set (EuclideanSpace ℝ (Fin n))) :
    Set (AttemptObservable Ξ n m) :=
  {z | ∀ j ∈ Finset.Icc 1 K, z.2.2.1 j ∈ X}ᶜ

/-- Helper for Corollary 3.8: the record-level failure event is measurable. -/
private lemma measurableSet_attemptFailureRecords
    (K : ℕ) (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X) :
    MeasurableSet (attemptFailureRecords (Ξ := Ξ) (m := m) K X) := by
  -- Build the finite success event coordinatewise, then take its complement.
  have hcoordinate (j : ℕ) : MeasurableSet
      {z : AttemptObservable Ξ n m | z.2.2.1 j ∈ X} :=
    hX.preimage (measurable_pi_apply j |>.comp measurable_snd.snd.fst)
  have hsuccess : MeasurableSet
      {z : AttemptObservable Ξ n m | ∀ j ∈ Finset.Icc 1 K, z.2.2.1 j ∈ X} := by
    induction Finset.Icc 1 K using Finset.induction with
    | empty =>
        simp only [Finset.notMem_empty, IsEmpty.forall_iff, implies_true,
          Set.setOf_true, MeasurableSet.univ]
    | insert a s ha hs =>
        simpa only [Finset.forall_mem_insert, Set.setOf_and] using
          (hcoordinate a).inter hs
  exact hsuccess.compl

/-- Helper for Corollary 3.8: pulling back record failure gives attempt failure. -/
private lemma attemptFailureRecords_preimage
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) :
    (fun ω ↦
      (restart.outputIndex i ω,
        fun k j ↦ (restart.attempt i).sample k j ω,
        fun k ↦ (restart.attempt i).point k ω,
        fun k ↦ (restart.attempt i).multiplier k ω,
        fun k ↦ (restart.attempt i).step k ω)) ⁻¹'
        attemptFailureRecords (Ξ := Ξ) (m := m) K X =
      (restart.successEvent i)ᶜ := by
  -- The record condition is exactly the negation of the completion theorem.
  ext ω
  simp only [Set.mem_preimage, attemptFailureRecords, Set.mem_compl_iff,
    Set.mem_setOf_eq, successEvent, completionIndicator_eq_true]

/-- Helper for Corollary 3.8: the attempt-count tail is the intersection of
the first `t` failure events. -/
private lemma attemptCount_tail_eq_failureInter
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (t : ℕ) :
    {ω | t < restart.attemptCount ω} =
      ⋂ i ∈ Finset.range t, (restart.successEvent i)ᶜ := by
  -- Split on the finite first-success index and compare it with `t`.
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_range,
    Set.mem_compl_iff]
  cases hfirst : restart.firstAccepted ω using WithTop.recTopCoe with
  | top =>
      have hall := (restart.firstAccepted_eq_top_iff ω).mp hfirst
      simp only [attemptCount, hfirst, WithTop.recTopCoe_top, ENat.coe_lt_top,
        true_iff]
      exact fun i _hi ↦ hall i
  | coe a =>
      have hcharacterization :=
        (restart.firstAccepted_eq_coe_iff a ω).mp hfirst
      simp only [attemptCount, hfirst, WithTop.recTopCoe_coe, ENat.coe_lt_coe]
      constructor
      · intro ht i hit
        apply hcharacterization.2 i
        omega
      · intro hall
        have hta : t ≤ a := by
          by_contra hnot
          have hat : a < t := Nat.lt_of_not_ge hnot
          exact hall a hat hcharacterization.1
        omega

/-- The attempt-count tail is dominated by independent failure probabilities. -/
theorem attemptCount_tail_le
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (confidence : ℝ)
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1)
    (hX : MeasurableSet X) (initial_mem : x₀ ∈ X)
    (h_region : RegionCondition h oracle params confidence X) (t : ℕ) :
    ℙ {ω | t < restart.attemptCount ω} ≤ ENNReal.ofReal confidence ^ t := by
  -- Each attempt fails with probability at most `confidence`.
  have hfailure (i : ℕ) :
      ℙ (restart.successEvent i)ᶜ ≤ ENNReal.ofReal confidence := by
    have hsuccessNull : NullMeasurableSet (restart.successEvent i) ℙ := by
      rw [restart.successEvent_eq_survivalEvent]
      exact nullMeasurableSet_survivalEvent (restart.attempt i) X hX K
    have hsuccessLower : ENNReal.ofReal (1 - confidence) ≤
        ℙ (restart.successEvent i) := by
      rw [restart.successEvent_eq_survivalEvent]
      exact survivalProbability_ge K hK confidence confidence_pos X hX initial_mem
        (restart.attempt i) h_region
    have hconfidence : ENNReal.ofReal confidence ≤ 1 := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal confidence_lt_one.le
    calc
      ℙ (restart.successEvent i)ᶜ = 1 - ℙ (restart.successEvent i) :=
        prob_compl_eq_one_sub₀ hsuccessNull
      _ ≤ 1 - ENNReal.ofReal (1 - confidence) :=
        tsub_le_tsub_left hsuccessLower 1
      _ = ENNReal.ofReal confidence := by
        rw [ENNReal.ofReal_sub 1 confidence_pos.le, ENNReal.ofReal_one,
          ENNReal.sub_sub_cancel ENNReal.one_ne_top hconfidence]
  -- Mutual independence factors the finite intersection of failures.
  have hfactor := restart.independent_attempt.measure_inter_preimage_eq_mul
    (Finset.range t)
    (sets := fun _ ↦ attemptFailureRecords (Ξ := Ξ) (m := m) K X)
    (fun _ _ ↦ measurableSet_attemptFailureRecords K X hX)
  rw [restart.attemptCount_tail_eq_failureInter t]
  calc
    ℙ (⋂ i ∈ Finset.range t, (restart.successEvent i)ᶜ) =
        ∏ i ∈ Finset.range t, ℙ (restart.successEvent i)ᶜ := by
      simpa only [attemptFailureRecords_preimage] using hfactor
    _ ≤ ∏ _i ∈ Finset.range t, ENNReal.ofReal confidence :=
      Finset.prod_le_prod' fun i _hi ↦ hfailure i
    _ = ENNReal.ofReal confidence ^ t := by simp

end SafeguardedRestart

namespace RestartAccounting

/-- Helper for Corollary 3.8: the charged number of prefix iterations before a
horizon, truncated at the first localization exit. -/
noncomputable def truncatedIterations (K : ℕ) (exitTime : ℕ∞) : ℕ :=
  min K (exitTime.untopD K)

/-- A horizon-truncated iteration count never exceeds the horizon. -/
theorem truncatedIterations_le (K : ℕ) (exitTime : ℕ∞) :
    truncatedIterations K exitTime ≤ K := by
  exact min_le_left K (exitTime.untopD K)

/-- The accumulated cost of finitely many attempts, or `⊤` on nontermination. -/
noncomputable def accumulatedCost (count : ℕ∞) (cost : ℕ → ℕ) : ℕ∞ :=
  if hcount : count = ⊤ then ⊤
  else (∑ i ∈ Finset.range (count.untop hcount), cost i : ℕ)

/-- Helper for Corollary 3.8: a positive uniform per-attempt budget bounds
the accumulated extended-natural cost. -/
theorem accumulatedCost_le_mul (count : ℕ∞) (cost : ℕ → ℕ) (budget : ℕ)
    (hbudget : 0 < budget) (hcost : ∀ i, cost i ≤ budget) :
    accumulatedCost count cost ≤ count * budget := by
  -- The infinite case is absorbing; the finite case is a bounded finite sum.
  cases count using ENat.recTopCoe with
  | top =>
      have hbudgetNe : (budget : ℕ∞) ≠ 0 := by exact_mod_cast hbudget.ne'
      simp only [accumulatedCost, ↓reduceDIte, ENat.top_mul', hbudgetNe, if_false,
        le_rfl]
  | coe count =>
      have hsum :
        ∑ i ∈ Finset.range count, cost i ≤
            count * budget := by
        calc
          ∑ i ∈ Finset.range count, cost i ≤
              ∑ _i ∈ Finset.range count, budget :=
            Finset.sum_le_sum fun i _hi ↦ hcost i
          _ = count * budget := by
            simp only [Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul]
      simp only [accumulatedCost, ENat.coe_ne_top, ↓reduceDIte]
      exact_mod_cast hsum

end RestartAccounting

namespace SafeguardedRestart

variable {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}

/-- The charged prefix length of attempt `i`, truncated at localization exit.
The underlying `attempt` is still a full-tail witness; only this prefix is
interpreted as executed work. -/
noncomputable def attemptIterations
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) (ω : Ω) : ℕ :=
  RestartAccounting.truncatedIterations K
    (StochasticRun.Localization.exitTime (restart.attempt i) X ω)

/-- No restart attempt is charged more than `K` prefix iterations. -/
theorem attemptIterations_le
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) (ω : Ω) : restart.attemptIterations i ω ≤ K := by
  exact RestartAccounting.truncatedIterations_le K _

/-- Helper for Corollary 3.8: the charged iterations are the first-exit-
truncated prefix length. -/
theorem attemptIterations_eq_firstExitCharge
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) (ω : Ω) :
    restart.attemptIterations i ω =
      RestartAccounting.truncatedIterations K
        (StochasticRun.Localization.exitTime (restart.attempt i) X ω) := by
  rfl

/-- The accumulated cost of all attempted runs. -/
noncomputable def accumulatedCost
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (cost : ℕ → Ω → ℕ) (ω : Ω) : ℕ∞ :=
  RestartAccounting.accumulatedCost (restart.attemptCount ω) (fun i ↦ cost i ω)

/-- The total number of transitions charged through the accepted prefix.  The
latent full-tail witness is not an execution trace after its first exit. -/
noncomputable def totalIterations
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (ω : Ω) : ℕ∞ :=
  restart.accumulatedCost restart.attemptIterations ω

/-- Total work is at most `K` times the number of attempted runs. -/
theorem totalIterations_le_attemptCount_mul
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (ω : Ω) :
    restart.totalIterations ω ≤ restart.attemptCount ω * K := by
  -- Transfer the pointwise horizon bound through accumulated cost.
  exact RestartAccounting.accumulatedCost_le_mul _ _ K (by omega)
    (fun i ↦ restart.attemptIterations_le i ω)

/-- Helper for Corollary 3.8: at most `K ⌈/⌉ q` indices below a prefix of
length at most `K` are divisible by positive `q`. -/
private lemma refreshIndexCard_le_ceilDiv
    (L K q : ℕ) (hq : 0 < q) (hLK : L ≤ K) :
    ((Finset.range L).filter (fun k ↦ k % q = 0)).card ≤ K ⌈/⌉ q := by
  have hKq : K ≤ (K ⌈/⌉ q) * q := by
    simpa only [mul_comm] using (ceilDiv_le_iff_le_mul hq).mp (le_refl (K ⌈/⌉ q))
  have hcard : ((Finset.range L).filter (fun k ↦ k % q = 0)).card ≤
      (Finset.range (K ⌈/⌉ q)).card := by
    apply Finset.card_le_card_of_injOn (fun k ↦ k / q)
    · intro k hk
      have hk' := Finset.mem_filter.mp hk
      apply Finset.mem_range.mpr
      rw [Nat.div_lt_iff_lt_mul hq]
      exact lt_of_lt_of_le (lt_of_lt_of_le (Finset.mem_range.mp hk'.1) hLK) hKq
    · intro a ha b hb hab
      change a / q = b / q at hab
      have ha' := Finset.mem_filter.mp ha
      have hb' := Finset.mem_filter.mp hb
      have harepr := Nat.div_add_mod a q
      have hbrepr := Nat.div_add_mod b q
      calc
        a = q * (a / q) + a % q := harepr.symm
        _ = q * (a / q) := by rw [ha'.2, Nat.add_zero]
        _ = q * (b / q) := by rw [hab]
        _ = q * (b / q) + b % q := by rw [hb'.2, Nat.add_zero]
        _ = b := hbrepr
  simpa only [Finset.card_range] using hcard

/-- The stochastic-gradient evaluations charged to one truncated SPIDER
prefix. -/
noncomputable def attemptGradientEvaluationCount
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) (ω : Ω) : ℕ :=
  (restart.attempt i).gradientEvaluationCount (restart.attemptIterations i ω)

/-- One attempt uses at most the prescribed full-run SPIDER gradient budget. -/
theorem attemptGradientEvaluationCount_le
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) (ω : Ω) :
    restart.attemptGradientEvaluationCount i ω ≤
      (K ⌈/⌉ (SPIDER.refreshPeriod K : ℕ)) * (SPIDER.refreshBatchSize K : ℕ) +
        2 * K * (SPIDER.innerBatchSize h oracle params K : ℕ) := by
  -- Count refresh indices and bound all recursive updates by the prefix length.
  let L := restart.attemptIterations i ω
  have hL : L ≤ K := restart.attemptIterations_le i ω
  have hq : 0 < (SPIDER.refreshPeriod K : ℕ) := (SPIDER.refreshPeriod K).pos
  have hrefresh := refreshIndexCard_le_ceilDiv L K
    (SPIDER.refreshPeriod K : ℕ) hq hL
  unfold attemptGradientEvaluationCount
  rw [(restart.attempt i).gradientEvaluationCount_spec]
  calc
    (∑ k ∈ Finset.range L,
        if k % (SPIDER.refreshPeriod K : ℕ) = 0 then
          (SPIDER.refreshBatchSize K : ℕ)
        else 2 * (SPIDER.innerBatchSize h oracle params K : ℕ)) ≤
        ∑ k ∈ Finset.range L,
          ((if k % (SPIDER.refreshPeriod K : ℕ) = 0 then
              (SPIDER.refreshBatchSize K : ℕ) else 0) +
            2 * (SPIDER.innerBatchSize h oracle params K : ℕ)) := by
      apply Finset.sum_le_sum
      intro k hk
      split <;> omega
    _ = ((Finset.range L).filter
          (fun k ↦ k % (SPIDER.refreshPeriod K : ℕ) = 0)).card *
          (SPIDER.refreshBatchSize K : ℕ) +
        L * (2 * (SPIDER.innerBatchSize h oracle params K : ℕ)) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_range, Nat.cast_id]
    _ ≤ (K ⌈/⌉ (SPIDER.refreshPeriod K : ℕ)) *
          (SPIDER.refreshBatchSize K : ℕ) +
        K * (2 * (SPIDER.innerBatchSize h oracle params K : ℕ)) :=
      add_le_add (Nat.mul_le_mul_right _ hrefresh) (Nat.mul_le_mul_right _ hL)
    _ = (K ⌈/⌉ (SPIDER.refreshPeriod K : ℕ)) *
          (SPIDER.refreshBatchSize K : ℕ) +
        2 * K * (SPIDER.innerBatchSize h oracle params K : ℕ) := by ring

/-- The total stochastic-gradient evaluation count across all attempts. -/
noncomputable def gradientEvaluationCount
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (ω : Ω) : ℕ∞ :=
  restart.accumulatedCost restart.attemptGradientEvaluationCount ω

/-- The total gradient count is bounded by the per-attempt budget times attempts. -/
theorem gradientEvaluationCount_le
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (ω : Ω) :
    restart.gradientEvaluationCount ω ≤ restart.attemptCount ω *
      ((K ⌈/⌉ (SPIDER.refreshPeriod K : ℕ)) * (SPIDER.refreshBatchSize K : ℕ) +
        2 * K * (SPIDER.innerBatchSize h oracle params K : ℕ)) := by
  -- Transfer the fixed SPIDER budget through accumulated cost.
  have hbudget : 0 <
      (K ⌈/⌉ (SPIDER.refreshPeriod K : ℕ)) * (SPIDER.refreshBatchSize K : ℕ) +
        2 * K * (SPIDER.innerBatchSize h oracle params K : ℕ) := by
    have hinner := (SPIDER.innerBatchSize h oracle params K).pos
    have hsecond : 0 < 2 * K * (SPIDER.innerBatchSize h oracle params K : ℕ) := by
      positivity
    exact lt_of_lt_of_le hsecond (Nat.le_add_left _ _)
  exact RestartAccounting.accumulatedCost_le_mul _ _ _ hbudget
    (fun i ↦ restart.attemptGradientEvaluationCount_le i ω)

/-- The logical constraint-evaluation count, one per transition. -/
noncomputable def constraintEvaluationCount
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (ω : Ω) : ℕ∞ :=
  restart.totalIterations ω

/-- The constraint counter equals the executed-transition count. -/
theorem constraintEvaluationCount_eq_totalIterations
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (ω : Ω) : restart.constraintEvaluationCount ω = restart.totalIterations ω := by
  rfl

/-- The logical Jacobian-evaluation count, one per transition. -/
noncomputable def jacobianEvaluationCount
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (ω : Ω) : ℕ∞ :=
  restart.totalIterations ω

/-- The Jacobian counter equals the executed-transition count. -/
theorem jacobianEvaluationCount_eq_totalIterations
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (ω : Ω) : restart.jacobianEvaluationCount ω = restart.totalIterations ω := by
  rfl

/-- The logical linear-system solve count, one per transition. -/
noncomputable def linearSystemSolveCount
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (ω : Ω) : ℕ∞ :=
  restart.totalIterations ω

/-- The linear-system solve counter equals the transition count. -/
theorem linearSystemSolveCount_eq_totalIterations
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (ω : Ω) : restart.linearSystemSolveCount ω = restart.totalIterations ω := by
  rfl

/-- The abstract localization-membership cost model, charging one logical test per
transition. It is an accounting specification, not an executable membership oracle. -/
noncomputable def membershipTestCount
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (ω : Ω) : ℕ∞ :=
  restart.totalIterations ω

/-- The membership-test counter equals the transition count. -/
theorem membershipTestCount_eq_totalIterations
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (ω : Ω) : restart.membershipTestCount ω = restart.totalIterations ω := by
  rfl

end SafeguardedRestart

end LALM

namespace LALM.SafeguardedRestart

open StochasticRun.Localization

universe u v

variable {n m : ℕ}
variable {Ξ : Type u} [MeasurableSpace Ξ] {ν : Measure Ξ} [IsProbabilityMeasure ν]
variable {Ω : Type v} [MeasurableSpace Ω] {ℙ : Measure Ω} [IsProbabilityMeasure ℙ]
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
variable {x₀ : EuclideanSpace ℝ (Fin n)}
variable {multiplier₀ : EuclideanSpace ℝ (Fin m)}
variable {h : EqualityConstrained.Regularity f c}
variable {oracle : EqualityConstrained.StochasticOracle f h.region ν}
variable {params : LALM.Parameters h x₀ multiplier₀}

/-- Helper for Corollary 3.8: an extended natural number is the sum of the
indicators of its strict natural lower bounds. -/
private lemma enatToENNReal_eq_tsum_lt (a : ℕ∞) :
    (a : ℝ≥0∞) = ∑' t : ℕ, if (t : ℕ∞) < a then 1 else 0 := by
  -- Separate the infinite count from a finite initial segment.
  cases a using ENat.recTopCoe with
  | top =>
      simp only [ENat.toENNReal_top, lt_top_iff_ne_top]
      exact (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero).symm
  | coe a =>
      simp only [ENat.toENNReal_coe, ENat.coe_lt_coe]
      calc
        (a : ℝ≥0∞) = ∑ t ∈ Finset.range a, (1 : ℝ≥0∞) := by
          rw [Finset.sum_const, nsmul_one, Finset.card_range]
        _ = ∑' t : ℕ, if t < a then 1 else 0 := by
          rw [tsum_eq_sum (s := Finset.range a)]
          · apply Finset.sum_congr rfl
            intro t ht
            rw [if_pos (Finset.mem_range.mp ht)]
          · intro t ht
            rw [if_neg]
            simpa only [Finset.mem_range] using ht

omit [IsProbabilityMeasure ℙ] in
/-- Helper for Corollary 3.8: the lower integral of an extended-natural
random variable is bounded by the sum of its outer tail probabilities. -/
private lemma lintegralENat_le_tsum_tail (count : Ω → ℕ∞) :
    ∫⁻ ω, (count ω : ℝ≥0∞) ∂ℙ ≤ ∑' t : ℕ, ℙ {ω | t < count ω} := by
  -- Route correction: `firstAccepted` is opaque outside its owner module, so
  -- measurable hulls provide the tail interface without unfolding it.
  have hpoint (ω : Ω) : (count ω : ℝ≥0∞) ≤
      ∑' t : ℕ, (toMeasurable ℙ {ω | t < count ω}).indicator (fun _ ↦ 1) ω := by
    rw [enatToENNReal_eq_tsum_lt]
    apply ENNReal.tsum_le_tsum
    intro t
    by_cases ht : (t : ℕ∞) < count ω
    · have hmem : ω ∈ toMeasurable ℙ {ω | t < count ω} :=
        subset_toMeasurable ℙ _ ht
      simp only [ht, if_true, Set.indicator_of_mem hmem]
      exact le_rfl
    · simp only [ht, if_false, zero_le]
  -- Integrate the measurable hull indicators and preserve their outer measures.
  calc
    (∫⁻ ω, (count ω : ℝ≥0∞) ∂ℙ) ≤
        ∫⁻ ω, ∑' t : ℕ,
          (toMeasurable ℙ {ω | t < count ω}).indicator (fun _ ↦ 1) ω ∂ℙ :=
      lintegral_mono hpoint
    _ = ∑' t : ℕ, ∫⁻ ω,
        (toMeasurable ℙ {ω | t < count ω}).indicator (fun _ ↦ 1) ω ∂ℙ := by
      rw [lintegral_tsum]
      intro t
      exact (measurable_const.indicator
        (measurableSet_toMeasurable ℙ {ω | t < count ω})).aemeasurable
    _ = ∑' t : ℕ, ℙ {ω | t < count ω} := by
      apply tsum_congr
      intro t
      calc
        (∫⁻ ω, (toMeasurable ℙ {ω | t < count ω}).indicator
            (fun _ ↦ 1) ω ∂ℙ) = ℙ (toMeasurable ℙ {ω | t < count ω}) :=
          lintegral_indicator_one (measurableSet_toMeasurable ℙ _)
        _ = ℙ {ω | t < count ω} := measure_toMeasurable _

/-- Helper for Corollary 3.8: a pointwise per-attempt budget bounds the
expected accumulated extended-natural cost. -/
private lemma lintegralCost_le_attemptCount_mul
    (K : ℕ) (hK : 2 ≤ K) (X : Set (EuclideanSpace ℝ (Fin n)))
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (cost : Ω → ℕ∞) (budget : ℕ)
    (hcost : ∀ ω, cost ω ≤ restart.attemptCount ω * budget) :
    ∫⁻ ω, (cost ω : ℝ≥0∞) ∂ℙ ≤
      (∫⁻ ω, (restart.attemptCount ω : ℝ≥0∞) ∂ℙ) * budget := by
  -- Coerce the pointwise accounting inequality and pull out the finite budget.
  have hcoerced (ω : Ω) :
      (cost ω : ℝ≥0∞) ≤ (restart.attemptCount ω : ℝ≥0∞) * budget := by
    simpa only [ENat.toENNReal_mul, ENat.toENNReal_coe] using
      ENat.toENNReal_mono (hcost ω)
  calc
    (∫⁻ ω, (cost ω : ℝ≥0∞) ∂ℙ) ≤
        ∫⁻ ω, (restart.attemptCount ω : ℝ≥0∞) * budget ∂ℙ :=
      lintegral_mono hcoerced
    _ = (∫⁻ ω, (restart.attemptCount ω : ℝ≥0∞) ∂ℙ) * budget := by
      rw [lintegral_mul_const']
      exact ENNReal.natCast_ne_top budget

/-- Corollary 3.8 (1): independent safeguarded restarts terminate almost surely. -/
theorem terminatesAE
    (K : ℕ) (hK : 2 ≤ K) (confidence : ℝ)
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (h_region : RegionCondition h oracle params confidence X) :
    ∀ᵐ ω ∂ℙ, restart.firstAccepted ω ≠ ⊤ := by
  -- The nontermination event lies in every geometric attempt-count tail.
  rw [ae_iff]
  simp only [not_ne_iff]
  refine ENNReal.eq_zero_of_le_mul_pow (ε := 1)
    (ENNReal.ofReal_lt_one.mpr confidence_lt_one) ?_
  intro t
  calc
    ℙ {ω | restart.firstAccepted ω = ⊤} ≤
        ℙ {ω | t < restart.attemptCount ω} := by
      apply measure_mono
      intro ω hω
      have hcount : restart.attemptCount ω = ⊤ :=
        (restart.attemptCount_eq_top_iff ω).2 hω
      simp only [Set.mem_setOf_eq, hcount, ENat.coe_lt_top]
    _ ≤ ENNReal.ofReal confidence ^ t :=
      restart.attemptCount_tail_le confidence confidence_pos confidence_lt_one
        hX initial_mem h_region t
    _ = (1 : ℝ≥0) * ENNReal.ofReal confidence ^ t := by simp

/-- Companion to Corollary 3.8 (2): the expected number of attempts is at most
`1 / (1 - confidence)`. -/
theorem expectedAttemptCount_le
    (K : ℕ) (hK : 2 ≤ K) (confidence : ℝ)
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (h_region : RegionCondition h oracle params confidence X) :
    ∫⁻ ω, (restart.attemptCount ω : ℝ≥0∞) ∂ℙ ≤
      ENNReal.ofReal (1 / (1 - confidence)) := by
  -- Sum the geometric tail bound and normalize its closed form in `ℝ≥0∞`.
  calc
    (∫⁻ ω, (restart.attemptCount ω : ℝ≥0∞) ∂ℙ) ≤
        ∑' t : ℕ, ℙ {ω | t < restart.attemptCount ω} :=
      lintegralENat_le_tsum_tail restart.attemptCount
    _ ≤
        ∑' t : ℕ, ENNReal.ofReal confidence ^ t :=
      ENNReal.tsum_le_tsum fun t ↦
        restart.attemptCount_tail_le confidence confidence_pos confidence_lt_one
          hX initial_mem h_region t
    _ = (1 - ENNReal.ofReal confidence)⁻¹ := ENNReal.tsum_geometric _
    _ = ENNReal.ofReal (1 / (1 - confidence)) := by
      rw [ENNReal.ofReal_div_of_pos (sub_pos.mpr confidence_lt_one),
        ENNReal.ofReal_one, ENNReal.ofReal_sub 1 confidence_pos.le,
        ENNReal.ofReal_one, one_div]

/-- Helper for Corollary 3.8: coercing a positive-denominator geometric budget
commutes with multiplication by its finite natural cost. -/
private lemma geometricBudget_ofReal
    (confidence : ℝ) (confidence_lt_one : confidence < 1) (budget : ℕ) :
    ENNReal.ofReal (1 / (1 - confidence)) * budget =
      ENNReal.ofReal ((budget : ℝ) / (1 - confidence)) := by
  -- Move the finite budget into `ofReal`, then commute the real factors.
  have honeMinusConfidence : 0 < 1 - confidence := sub_pos.mpr confidence_lt_one
  calc
    ENNReal.ofReal (1 / (1 - confidence)) * budget =
        ENNReal.ofReal (1 / (1 - confidence)) *
          ENNReal.ofReal (budget : ℝ) := by
      rw [ENNReal.ofReal_natCast]
    _ = ENNReal.ofReal ((1 / (1 - confidence)) * (budget : ℝ)) :=
      (ENNReal.ofReal_mul (one_div_nonneg.mpr honeMinusConfidence.le)).symm
    _ = ENNReal.ofReal ((budget : ℝ) / (1 - confidence)) := by
      rw [one_div, div_eq_mul_inv, mul_comm]

/-- Helper for Corollary 3.8: a deterministic per-attempt budget inherits the
geometric expected-attempt factor. -/
private lemma expectedCost_le
    (K : ℕ) (hK : 2 ≤ K) (confidence : ℝ)
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (h_region : RegionCondition h oracle params confidence X)
    (cost : Ω → ℕ∞) (budget : ℕ)
    (hcost : ∀ ω, cost ω ≤ restart.attemptCount ω * budget) :
    ∫⁻ ω, (cost ω : ℝ≥0∞) ∂ℙ ≤
      ENNReal.ofReal ((budget : ℝ) / (1 - confidence)) := by
  -- First transfer the pointwise budget, then insert the geometric attempt bound.
  calc
    (∫⁻ ω, (cost ω : ℝ≥0∞) ∂ℙ) ≤
        (∫⁻ ω, (restart.attemptCount ω : ℝ≥0∞) ∂ℙ) * budget :=
      lintegralCost_le_attemptCount_mul K hK X restart cost budget hcost
    _ ≤ ENNReal.ofReal (1 / (1 - confidence)) * budget :=
      mul_le_mul_left (expectedAttemptCount_le K hK confidence confidence_pos
        confidence_lt_one X hX initial_mem restart h_region) budget
    _ = ENNReal.ofReal ((budget : ℝ) / (1 - confidence)) :=
      geometricBudget_ofReal confidence confidence_lt_one budget

/-- Helper for Corollary 3.8: expected executed iterations are at most the
horizon times the geometric expected-attempt factor. -/
private lemma expectedTotalIterations_le
    (K : ℕ) (hK : 2 ≤ K) (confidence : ℝ)
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (h_region : RegionCondition h oracle params confidence X) :
    ∫⁻ ω, (restart.totalIterations ω : ℝ≥0∞) ∂ℙ ≤
      ENNReal.ofReal ((K : ℝ) / (1 - confidence)) := by
  -- Apply the generic transfer to the public per-attempt iteration bound.
  exact expectedCost_le K hK confidence confidence_pos confidence_lt_one X hX
    initial_mem restart h_region restart.totalIterations K
      restart.totalIterations_le_attemptCount_mul

/-- Helper for Corollary 3.8: the squared residual selected within one fixed
restart attempt. -/
private noncomputable def selectedAttemptResidualSq
    {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) (ω : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal
    (KKT.residual f c
      ((restart.attempt i).point (restart.outputIndex i ω + 1) ω)
      ((restart.attempt i).multiplier (restart.outputIndex i ω + 1) ω) ^ 2)

omit [IsProbabilityMeasure ℙ] in
/-- Helper for Corollary 3.8: countably many almost-everywhere measurable
sections assemble into a product-space function. -/
private lemma aemeasurableIndexedProduct
    {E : Type*} [MeasurableSpace E] (μ : Measure ℕ)
    (g : ℕ → Ω → E) (hg : ∀ k, AEMeasurable (g k) ℙ) :
    AEMeasurable (fun output : ℕ × Ω ↦ g output.1 output.2) (μ.prod ℙ) := by
  -- Replace every section by a measurable version before assembling them.
  let g' : ℕ → Ω → E := fun k ↦ (hg k).mk (g k)
  have hg'Measurable (k : ℕ) : Measurable (g' k) :=
    (hg k).measurable_mk
  have hglobalMeasurable :
      Measurable (fun output : ℕ × Ω ↦ g' output.1 output.2) :=
    measurable_from_prod_countable_right hg'Measurable
  have hsections : ∀ᵐ ω ∂ℙ, ∀ k, g' k ω = g k ω := by
    apply ae_all_iff.mpr
    intro k
    exact (hg k).ae_eq_mk.symm
  have hlifted :
      ∀ᵐ output ∂μ.prod ℙ, ∀ k, g' k output.2 = g k output.2 :=
    (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ℙ)).ae hsections
  have hglobalAE :
      (fun output : ℕ × Ω ↦ g' output.1 output.2) =ᵐ[μ.prod ℙ]
        fun output ↦ g output.1 output.2 := by
    filter_upwards [hlifted] with output houtput
    exact houtput output.1
  exact hglobalMeasurable.aemeasurable.congr hglobalAE

/-- Helper for Corollary 3.8: the point and multiplier trajectories are the
components of an attempt needed by the residual calculation. -/
private def pointMultiplierObservable
    {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) (ω : Ω) :
    (ℕ → EuclideanSpace ℝ (Fin n)) × (ℕ → EuclideanSpace ℝ (Fin m)) :=
  (fun k ↦ (restart.attempt i).point k ω,
    fun k ↦ (restart.attempt i).multiplier k ω)

/-- Helper for Corollary 3.8: each point-multiplier trajectory observable is
almost-everywhere measurable. -/
private lemma aemeasurablePointMultiplierObservable
    {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) : AEMeasurable (pointMultiplierObservable restart i) ℙ := by
  -- Assemble the two trajectories coordinatewise from the scheduled-run API.
  exact (aemeasurable_pi_lambda _ fun k ↦
    (restart.attempt i).aemeasurable_point k).prodMk
      (aemeasurable_pi_lambda _ fun k ↦
        (restart.attempt i).aemeasurable_multiplier k)

/-- Helper for Corollary 3.8: the uniform selector is independent of the point
and multiplier trajectories of its attempt. -/
private lemma outputIndex_indep_pointMultiplierObservable
    {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) : ProbabilityTheory.IndepFun (restart.outputIndex i)
      (pointMultiplierObservable restart i) ℙ := by
  -- Project the required pair from the certified complete-attempt observable.
  have hprojection : Measurable
      (fun z :
        (ℕ → ℕ → Ξ) ×
          (ℕ → EuclideanSpace ℝ (Fin n)) ×
          (ℕ → EuclideanSpace ℝ (Fin m)) ×
          (ℕ → EuclideanSpace ℝ (Fin n)) ↦
        (z.2.1, z.2.2.1)) :=
    measurable_snd.fst.prodMk measurable_snd.snd.fst
  unfold pointMultiplierObservable
  simpa only [Function.comp_def, id_eq] using
    (restart.outputIndex_indep_attempt i).comp measurable_id hprojection

/-- Helper for Corollary 3.8: an attempt selector lies almost surely in the
finite support of its prescribed uniform law. -/
private lemma outputIndex_mem_uniformRange
    {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) :
    ∀ᵐ ω ∂ℙ, restart.outputIndex i ω ∈ Finset.Icc 1 (K - 1) := by
  let p := StochasticRun.UniformOutput.indexLaw K hK
  let s := Finset.Icc 1 (K - 1)
  have hpSupport : ∀ᵐ k ∂p.toMeasure, k ∈ s := by
    rw [ae_iff_of_countable]
    intro k hkMeasure
    by_contra hk
    have hk' : k ∉ Finset.Icc 1 (K - 1) := by
      simpa only [s] using hk
    have hpZero : p k = 0 := by
      simp only [p, StochasticRun.UniformOutput.indexLaw,
        PMF.uniformOfFinset_apply, if_neg hk']
    have hsingleton : p.toMeasure {k} = p k :=
      PMF.toMeasure_apply_singleton p k (MeasurableSet.singleton k)
    exact hkMeasure (hsingleton.trans hpZero)
  have hpSupport' :
      ∀ᵐ k ∂(StochasticRun.UniformOutput.indexLaw K hK).toMeasure,
        k ∈ Finset.Icc 1 (K - 1) := by
    simpa only [p, s] using hpSupport
  exact ((restart.outputIndex_hasLaw i).ae_iff (measurable_of_countable _)).mpr
    hpSupport'

/-- Helper for Corollary 3.8: the success-restricted residual as a measurable
function of an output index and point-multiplier trajectory. -/
private noncomputable def restrictedTrajectoryResidualSq
    (h : EqualityConstrained.Regularity f c)
    (K : ℕ) (X : Set (EuclideanSpace ℝ (Fin n)))
    (output : ℕ ×
      ((ℕ → EuclideanSpace ℝ (Fin n)) ×
        (ℕ → EuclideanSpace ℝ (Fin m)))) : ℝ≥0∞ :=
  {output | output.1 ∈ Finset.Icc 1 (K - 1) ∧
      ∀ j ∈ Finset.Icc 1 K, output.2.1 j ∈ X}.indicator
    (fun output ↦ ENNReal.ofReal
      (KKT.residualExtension h
        (output.2.1 (output.1 + 1), output.2.2 (output.1 + 1)) ^ 2)) output

/-- Helper for Corollary 3.8: the trajectory-form success-restricted residual
is measurable. -/
private lemma measurableRestrictedTrajectoryResidualSq
    (h : EqualityConstrained.Regularity f c)
    (K : ℕ) (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X) :
    Measurable (restrictedTrajectoryResidualSq h K X) := by
  -- The finite success condition is an intersection of measurable coordinates.
  have hcoordinate (j : ℕ) : MeasurableSet
      {output : ℕ ×
        ((ℕ → EuclideanSpace ℝ (Fin n)) ×
          (ℕ → EuclideanSpace ℝ (Fin m))) | output.2.1 j ∈ X} :=
    hX.preimage ((measurable_pi_apply j).comp measurable_snd.fst)
  have hsuccess : MeasurableSet
      {output : ℕ ×
        ((ℕ → EuclideanSpace ℝ (Fin n)) ×
          (ℕ → EuclideanSpace ℝ (Fin m))) |
        ∀ j ∈ Finset.Icc 1 K, output.2.1 j ∈ X} := by
    have hfinite (s : Finset ℕ) : MeasurableSet
        {output : ℕ ×
          ((ℕ → EuclideanSpace ℝ (Fin n)) ×
            (ℕ → EuclideanSpace ℝ (Fin m))) |
          ∀ j ∈ s, output.2.1 j ∈ X} := by
      induction s using Finset.induction with
      | empty =>
          simp only [Finset.notMem_empty, IsEmpty.forall_iff, implies_true,
            Set.setOf_true, MeasurableSet.univ]
      | insert a s ha hs =>
          simpa only [Finset.forall_mem_insert, Set.setOf_and] using
            (hcoordinate a).inter hs
    exact hfinite (Finset.Icc 1 K)
  -- Variable-index evaluation is measurable because the index is countable.
  have hpoint : Measurable
      (fun output : ℕ ×
        ((ℕ → EuclideanSpace ℝ (Fin n)) ×
          (ℕ → EuclideanSpace ℝ (Fin m))) ↦
        output.2.1 (output.1 + 1)) := by
    apply measurable_from_prod_countable_right
    intro k
    exact (measurable_pi_apply (k + 1)).comp measurable_fst
  have hmultiplier : Measurable
      (fun output : ℕ ×
        ((ℕ → EuclideanSpace ℝ (Fin n)) ×
          (ℕ → EuclideanSpace ℝ (Fin m))) ↦
        output.2.2 (output.1 + 1)) := by
    apply measurable_from_prod_countable_right
    intro k
    exact (measurable_pi_apply (k + 1)).comp measurable_snd
  have hindex : MeasurableSet
      {output : ℕ ×
        ((ℕ → EuclideanSpace ℝ (Fin n)) ×
          (ℕ → EuclideanSpace ℝ (Fin m))) |
        output.1 ∈ Finset.Icc 1 (K - 1)} :=
    (Finset.Icc 1 (K - 1)).measurableSet.preimage measurable_fst
  have hresidual :=
    (KKT.measurable_residualExtension h).comp (hpoint.prodMk hmultiplier)
  unfold restrictedTrajectoryResidualSq
  exact (hresidual.pow_const 2).ennreal_ofReal.indicator (hindex.inter hsuccess)

/-- Helper for Corollary 3.8: evaluating the trajectory normal form on an
actual attempt gives its success-restricted selected residual almost surely. -/
private lemma restrictedTrajectoryResidualSq_actual
    {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}
    (hXregion : X ⊆ h.region)
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) :
    (fun ω ↦ restrictedTrajectoryResidualSq h K X
        (restart.outputIndex i ω, pointMultiplierObservable restart i ω)) =ᵐ[ℙ]
      fun ω ↦ (restart.successEvent i).indicator
        (selectedAttemptResidualSq restart i) ω := by
  filter_upwards [outputIndex_mem_uniformRange restart i] with ω hindex
  have hsuccess :
      (∀ j ∈ Finset.Icc 1 K, (restart.attempt i).point j ω ∈ X) ↔
        ω ∈ restart.successEvent i := by
    rw [restart.successEvent_eq_survivalEvent,
      StochasticRun.Localization.mem_survivalEvent]
    simp only [Finset.mem_Icc, Set.mem_Icc]
  by_cases hω : ω ∈ restart.successEvent i
  · have hall := hsuccess.mpr hω
    have hselectedIndex : restart.outputIndex i ω + 1 ∈ Finset.Icc 1 K := by
      have hindexBounds := Finset.mem_Icc.mp hindex
      simp only [Finset.mem_Icc]
      omega
    have hselectedRegion :
        (restart.attempt i).point (restart.outputIndex i ω + 1) ω ∈ h.region :=
      hXregion (hall _ hselectedIndex)
    have hpair :
        (restart.outputIndex i ω, pointMultiplierObservable restart i ω) ∈
          {output : ℕ ×
            ((ℕ → EuclideanSpace ℝ (Fin n)) ×
              (ℕ → EuclideanSpace ℝ (Fin m))) |
            output.1 ∈ Finset.Icc 1 (K - 1) ∧
              ∀ j ∈ Finset.Icc 1 K, output.2.1 j ∈ X} := by
      simpa only [Set.mem_setOf_eq, pointMultiplierObservable] using ⟨hindex, hall⟩
    have hextension := KKT.residualExtension_eq h
      (z := ((restart.attempt i).point (restart.outputIndex i ω + 1) ω,
        (restart.attempt i).multiplier (restart.outputIndex i ω + 1) ω))
      hselectedRegion
    unfold restrictedTrajectoryResidualSq
    rw [Set.indicator_of_mem hpair, Set.indicator_of_mem hω]
    unfold pointMultiplierObservable selectedAttemptResidualSq
    rw [hextension]
  · have hpair :
        (restart.outputIndex i ω, pointMultiplierObservable restart i ω) ∉
          {output : ℕ ×
            ((ℕ → EuclideanSpace ℝ (Fin n)) ×
              (ℕ → EuclideanSpace ℝ (Fin m))) |
            output.1 ∈ Finset.Icc 1 (K - 1) ∧
              ∀ j ∈ Finset.Icc 1 K, output.2.1 j ∈ X} := by
      intro hpair
      apply hω
      apply hsuccess.mp
      simpa only [Set.mem_setOf_eq, pointMultiplierObservable] using hpair.2
    unfold restrictedTrajectoryResidualSq
    rw [Set.indicator_of_notMem hpair, Set.indicator_of_notMem hω]

/-- Helper for Corollary 3.8: the indicator that a point-multiplier trajectory
completes all safeguarded iterations. -/
private noncomputable def trajectorySuccessWeight
    (K : ℕ) (X : Set (EuclideanSpace ℝ (Fin n)))
    (output : ℕ ×
      ((ℕ → EuclideanSpace ℝ (Fin n)) ×
        (ℕ → EuclideanSpace ℝ (Fin m)))) : ℝ≥0∞ :=
  {z | ∀ j ∈ Finset.Icc 1 K, z.2.1 j ∈ X}.indicator (fun _ ↦ 1) output

/-- Helper for Corollary 3.8: the trajectory success indicator is measurable. -/
private lemma measurableTrajectorySuccessWeight
    (K : ℕ) (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X) :
    Measurable (trajectorySuccessWeight (n := n) (m := m) K X) := by
  -- Express completion as a finite intersection of measurable coordinate
  -- membership events, then take its constant indicator.
  have hcoordinate (j : ℕ) : MeasurableSet
      {output : ℕ ×
        ((ℕ → EuclideanSpace ℝ (Fin n)) ×
          (ℕ → EuclideanSpace ℝ (Fin m))) | output.2.1 j ∈ X} :=
    hX.preimage ((measurable_pi_apply j).comp measurable_snd.fst)
  have hsuccess : MeasurableSet
      {output : ℕ ×
        ((ℕ → EuclideanSpace ℝ (Fin n)) ×
          (ℕ → EuclideanSpace ℝ (Fin m))) |
        ∀ j ∈ Finset.Icc 1 K, output.2.1 j ∈ X} := by
    induction Finset.Icc 1 K using Finset.induction with
    | empty =>
        simp only [Finset.notMem_empty, IsEmpty.forall_iff, implies_true,
          Set.setOf_true, MeasurableSet.univ]
    | insert a s ha hs =>
        simpa only [Finset.forall_mem_insert, Set.setOf_and] using
          (hcoordinate a).inter hs
  unfold trajectorySuccessWeight
  exact measurable_const.indicator hsuccess

/-- Helper for Corollary 3.8: on an actual attempt, trajectory completion is
the indicator of that attempt's success event. -/
private lemma trajectorySuccessWeight_actual
    {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) (ω : Ω) :
    trajectorySuccessWeight (n := n) (m := m) K X
        (restart.outputIndex i ω, pointMultiplierObservable restart i ω) =
      (restart.successEvent i).indicator (fun _ ↦ (1 : ℝ≥0∞)) ω := by
  -- The owner completion theorem identifies the same finite point-membership
  -- condition used by the trajectory indicator.
  have hsuccess :
      (∀ j ∈ Finset.Icc 1 K, (restart.attempt i).point j ω ∈ X) ↔
        ω ∈ restart.successEvent i := by
    rw [restart.successEvent_eq_survivalEvent,
      StochasticRun.Localization.mem_survivalEvent]
    simp only [Finset.mem_Icc, Set.mem_Icc]
  by_cases hω : ω ∈ restart.successEvent i
  · have htrajectory :
        (restart.outputIndex i ω, pointMultiplierObservable restart i ω) ∈
          {z : ℕ ×
            ((ℕ → EuclideanSpace ℝ (Fin n)) ×
              (ℕ → EuclideanSpace ℝ (Fin m))) |
            ∀ j ∈ Finset.Icc 1 K, z.2.1 j ∈ X} := by
      simpa only [Set.mem_setOf_eq, pointMultiplierObservable] using
        hsuccess.mpr hω
    unfold trajectorySuccessWeight
    rw [Set.indicator_of_mem htrajectory, Set.indicator_of_mem hω]
  · have htrajectory :
        (restart.outputIndex i ω, pointMultiplierObservable restart i ω) ∉
          {z : ℕ ×
            ((ℕ → EuclideanSpace ℝ (Fin n)) ×
              (ℕ → EuclideanSpace ℝ (Fin m))) |
            ∀ j ∈ Finset.Icc 1 K, z.2.1 j ∈ X} := by
      intro htrajectory
      apply hω
      apply hsuccess.mp
      simpa only [Set.mem_setOf_eq, pointMultiplierObservable] using
        htrajectory
    unfold trajectorySuccessWeight
    rw [Set.indicator_of_notMem htrajectory, Set.indicator_of_notMem hω]

/-- Helper for Corollary 3.8: each attempt exposes its success weight together
with its success-restricted selected residual. -/
private noncomputable def successResidualObservable
    {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) (ω : Ω) : ℝ≥0∞ × ℝ≥0∞ :=
  ((restart.successEvent i).indicator (fun _ ↦ 1) ω,
    (restart.successEvent i).indicator (selectedAttemptResidualSq restart i) ω)

/-- Helper for Corollary 3.8: every success-residual attempt observable is
almost-everywhere measurable. -/
private lemma aemeasurableSuccessResidualObservable
    {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}
    (hX : MeasurableSet X)
    (hXregion : X ⊆ h.region)
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) : AEMeasurable (successResidualObservable restart i) ℙ := by
  -- Measurability of the first coordinate comes from the null-measurable
  -- success event; the trajectory normal form supplies the second coordinate.
  have hsuccess : NullMeasurableSet (restart.successEvent i) ℙ := by
    rw [restart.successEvent_eq_survivalEvent]
    exact StochasticRun.Localization.nullMeasurableSet_survivalEvent
      (restart.attempt i) X hX K
  have hjoint : AEMeasurable
      (fun ω ↦ (restart.outputIndex i ω,
        pointMultiplierObservable restart i ω)) ℙ :=
    (restart.outputIndex_hasLaw i).aemeasurable.prodMk
      (aemeasurablePointMultiplierObservable restart i)
  have hrestricted : AEMeasurable
      (fun ω ↦ (restart.successEvent i).indicator
        (selectedAttemptResidualSq restart i) ω) ℙ :=
    ((measurableRestrictedTrajectoryResidualSq h K X hX).comp_aemeasurable
      hjoint).congr (restrictedTrajectoryResidualSq_actual hXregion restart i)
  unfold successResidualObservable
  exact (aemeasurable_const.indicator₀ hsuccess).prodMk hrestricted

/-- Helper for Corollary 3.8: the attemptwise success-residual observables are
mutually independent. -/
private lemma iIndepFun_successResidualObservable
    {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}
    (hX : MeasurableSet X)
    (hXregion : X ⊆ h.region)
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X) :
    ProbabilityTheory.iIndepFun (fun i ↦ successResidualObservable restart i) ℙ := by
  -- Project each large complete-attempt record to the trajectory data used by
  -- the two-coordinate observable, keeping the record construction opaque.
  let projectAttempt := fun z :
      ℕ ×
        ((ℕ → ℕ → Ξ) ×
          (ℕ → EuclideanSpace ℝ (Fin n)) ×
          (ℕ → EuclideanSpace ℝ (Fin m)) ×
          (ℕ → EuclideanSpace ℝ (Fin n))) ↦
    (z.1, (z.2.2.1, z.2.2.2.1))
  let summarizeAttempt := fun z :
      ℕ ×
        ((ℕ → EuclideanSpace ℝ (Fin n)) ×
          (ℕ → EuclideanSpace ℝ (Fin m))) ↦
    (trajectorySuccessWeight (n := n) (m := m) K X z,
      restrictedTrajectoryResidualSq h K X z)
  have hproject : Measurable projectAttempt :=
    measurable_fst.prodMk
      (measurable_snd.snd.fst.prodMk measurable_snd.snd.snd.fst)
  have hsummarize : Measurable summarizeAttempt :=
    (measurableTrajectorySuccessWeight K X hX).prodMk
      (measurableRestrictedTrajectoryResidualSq h K X hX)
  have hindependent := restart.independent_attempt.comp
    (fun _ ↦ summarizeAttempt ∘ projectAttempt)
    (fun _ ↦ hsummarize.comp hproject)
  refine hindependent.congr fun i ↦ ?_
  filter_upwards [restrictedTrajectoryResidualSq_actual hXregion restart i] with ω hresidual
  -- The two trajectory computation lemmas identify the projected record with
  -- the public attempt observable pointwise.
  simp only [Function.comp_apply, projectAttempt, summarizeAttempt]
  apply Prod.ext
  · exact trajectorySuccessWeight_actual restart i ω
  · exact hresidual

/-- Helper for Corollary 3.8: evaluating the trajectory normal form on the
uniform product space gives Theorem 3.7's survival-restricted residual almost surely. -/
private lemma restrictedTrajectoryResidualSq_reference
    (K : ℕ) (hK : 2 ≤ K) (X : Set (EuclideanSpace ℝ (Fin n)))
    (hXregion : X ⊆ h.region)
    (run : SPIDER.ScheduledRun h oracle ℙ x₀ multiplier₀ params K) :
    (fun output : ℕ × Ω ↦ restrictedTrajectoryResidualSq h K X
        (output.1,
          (fun k ↦ run.point k output.2, fun k ↦ run.multiplier k output.2))) =ᵐ[
        StochasticRun.UniformOutput.measure K hK ℙ]
      fun output ↦
        (Set.univ ×ˢ StochasticRun.Localization.survivalEvent run X K).indicator
        (fun output ↦ ENNReal.ofReal
          (KKT.residual f c
            (StochasticRun.UniformOutput.point run output)
            (StochasticRun.UniformOutput.multiplier run output) ^ 2)) output := by
  let p := StochasticRun.UniformOutput.indexLaw K hK
  have hpSupport : ∀ᵐ k ∂p.toMeasure, k ∈ Finset.Icc 1 (K - 1) := by
    rw [ae_iff_of_countable]
    intro k hkMeasure
    by_contra hk
    have hpZero : p k = 0 := by
      simp only [p, StochasticRun.UniformOutput.indexLaw,
        PMF.uniformOfFinset_apply, if_neg hk]
    have hsingleton : p.toMeasure {k} = p k :=
      PMF.toMeasure_apply_singleton p k (MeasurableSet.singleton k)
    exact hkMeasure (hsingleton.trans hpZero)
  have hpSupportLifted :
      ∀ᵐ output ∂p.toMeasure.prod ℙ, output.1 ∈ Finset.Icc 1 (K - 1) :=
    (Measure.quasiMeasurePreserving_fst (μ := p.toMeasure) (ν := ℙ)).ae hpSupport
  change _ =ᵐ[p.toMeasure.prod ℙ] _
  filter_upwards [hpSupportLifted] with output hindex
  have hsuccess :
      (∀ j ∈ Finset.Icc 1 K, run.point j output.2 ∈ X) ↔
        output.2 ∈ StochasticRun.Localization.survivalEvent run X K := by
    rw [StochasticRun.Localization.mem_survivalEvent]
    simp only [Finset.mem_Icc, Set.mem_Icc]
  by_cases hω : output.2 ∈ StochasticRun.Localization.survivalEvent run X K
  · have hall := hsuccess.mpr hω
    have hselectedIndex : output.1 + 1 ∈ Finset.Icc 1 K := by
      have hindexBounds := Finset.mem_Icc.mp hindex
      simp only [Finset.mem_Icc]
      omega
    have hselectedRegion : run.point (output.1 + 1) output.2 ∈ h.region :=
      hXregion (hall _ hselectedIndex)
    have htrajectory :
        (output.1,
          (fun k ↦ run.point k output.2, fun k ↦ run.multiplier k output.2)) ∈
          {z : ℕ ×
            ((ℕ → EuclideanSpace ℝ (Fin n)) ×
              (ℕ → EuclideanSpace ℝ (Fin m))) |
            z.1 ∈ Finset.Icc 1 (K - 1) ∧
              ∀ j ∈ Finset.Icc 1 K, z.2.1 j ∈ X} := by
      simpa only [Set.mem_setOf_eq] using ⟨hindex, hall⟩
    have hproduct :
        output ∈ Set.univ ×ˢ StochasticRun.Localization.survivalEvent run X K :=
      ⟨Set.mem_univ _, hω⟩
    have hextension := KKT.residualExtension_eq h
      (z := (run.point (output.1 + 1) output.2,
        run.multiplier (output.1 + 1) output.2)) hselectedRegion
    unfold restrictedTrajectoryResidualSq
    rw [Set.indicator_of_mem htrajectory, Set.indicator_of_mem hproduct,
      StochasticRun.UniformOutput.point_apply,
      StochasticRun.UniformOutput.multiplier_apply, hextension]
  · have htrajectory :
        (output.1,
          (fun k ↦ run.point k output.2, fun k ↦ run.multiplier k output.2)) ∉
          {z : ℕ ×
            ((ℕ → EuclideanSpace ℝ (Fin n)) ×
              (ℕ → EuclideanSpace ℝ (Fin m))) |
            z.1 ∈ Finset.Icc 1 (K - 1) ∧
              ∀ j ∈ Finset.Icc 1 K, z.2.1 j ∈ X} := by
      intro htrajectory
      apply hω
      apply hsuccess.mp
      exact htrajectory.2
    have hproduct :
        output ∉ Set.univ ×ˢ StochasticRun.Localization.survivalEvent run X K := by
      intro houtput
      exact hω houtput.2
    unfold restrictedTrajectoryResidualSq
    rw [Set.indicator_of_notMem htrajectory, Set.indicator_of_notMem hproduct]

/-- Helper for Corollary 3.8: mapping the right coordinate of a product measure
commutes with integrating a measurable nonnegative function. -/
private lemma lintegral_prod_map_right
    {E : Type*} [MeasurableSpace E]
    (μ : Measure ℕ) (g : Ω → E) (hg : AEMeasurable g ℙ)
    (F : ℕ × E → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z, F z ∂μ.prod (ℙ.map g)) =
      ∫⁻ z, F (z.1, g z.2) ∂μ.prod ℙ := by
  -- Apply Tonelli on both sides and transport each measurable section by `g`.
  have hsection (k : ℕ) :
      AEMeasurable (fun y : E ↦ F (k, y)) (ℙ.map g) :=
    (hF.comp (measurable_const.prodMk measurable_id)).aemeasurable
  have hcomposedSection (k : ℕ) :
      AEMeasurable (fun ω ↦ F (k, g ω)) ℙ :=
    (hsection k).comp_aemeasurable hg
  have hcomposed : AEMeasurable
      (fun z : ℕ × Ω ↦ F (z.1, g z.2)) (μ.prod ℙ) :=
    aemeasurableIndexedProduct μ (fun k ω ↦ F (k, g ω)) hcomposedSection
  calc
    (∫⁻ z, F z ∂μ.prod (ℙ.map g)) =
        ∫⁻ k, ∫⁻ y, F (k, y) ∂ℙ.map g ∂μ :=
      lintegral_prod F hF.aemeasurable
    _ = ∫⁻ k, ∫⁻ ω, F (k, g ω) ∂ℙ ∂μ := by
      apply lintegral_congr
      intro k
      exact lintegral_map' (hsection k) hg
    _ = ∫⁻ z, F (z.1, g z.2) ∂μ.prod ℙ :=
      (lintegral_prod _ hcomposed).symm

/-- Helper for Corollary 3.8: a fixed attempt's success-restricted selected
residual has the same integral as the canonical uniform product output. -/
private lemma successRestrictedSelectedResidual_eq
    (K : ℕ) (hK : 2 ≤ K) (X : Set (EuclideanSpace ℝ (Fin n)))
    (hX : MeasurableSet X)
    (hXregion : X ⊆ h.region)
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) :
    (∫⁻ ω in restart.successEvent i,
        selectedAttemptResidualSq restart i ω ∂ℙ) =
      ∫⁻ output in
          Set.univ ×ˢ StochasticRun.Localization.survivalEvent
            (restart.attempt i) X K,
        ENNReal.ofReal
          (KKT.residual f c
            (StochasticRun.UniformOutput.point (restart.attempt i) output)
            (StochasticRun.UniformOutput.multiplier (restart.attempt i) output) ^ 2)
        ∂StochasticRun.UniformOutput.measure K hK ℙ := by
  -- Name the shared trajectory map and its integrand once for the law transport.
  let μindex := (StochasticRun.UniformOutput.indexLaw K hK).toMeasure
  let trajectory := pointMultiplierObservable restart i
  let integrand := restrictedTrajectoryResidualSq h K X
  have htrajectory : AEMeasurable trajectory ℙ :=
    aemeasurablePointMultiplierObservable restart i
  have hintegrand : Measurable integrand :=
    measurableRestrictedTrajectoryResidualSq h K X hX
  have htrajectoryLaw : ProbabilityTheory.HasLaw trajectory (ℙ.map trajectory) ℙ :=
    ⟨htrajectory, rfl⟩
  have hjointLaw : ProbabilityTheory.HasLaw
      (fun ω ↦ (restart.outputIndex i ω, trajectory ω))
      (μindex.prod (ℙ.map trajectory)) ℙ :=
    (outputIndex_indep_pointMultiplierObservable restart i).hasLaw_prod
      (restart.outputIndex_hasLaw i) htrajectoryLaw
  have hsuccess : NullMeasurableSet (restart.successEvent i) ℙ := by
    rw [restart.successEvent_eq_survivalEvent]
    exact StochasticRun.Localization.nullMeasurableSet_survivalEvent
      (restart.attempt i) X hX K
  have hreferenceSuccess : NullMeasurableSet
      (Set.univ ×ˢ StochasticRun.Localization.survivalEvent
        (restart.attempt i) X K) (μindex.prod ℙ) :=
    MeasurableSet.univ.nullMeasurableSet.prod
      (StochasticRun.Localization.nullMeasurableSet_survivalEvent
        (restart.attempt i) X hX K)
  -- Transport the common integrand through the joint law and the right-coordinate map.
  calc
    (∫⁻ ω in restart.successEvent i,
        selectedAttemptResidualSq restart i ω ∂ℙ) =
        ∫⁻ ω, (restart.successEvent i).indicator
          (selectedAttemptResidualSq restart i) ω ∂ℙ :=
      (lintegral_indicator₀ hsuccess _).symm
    _ = ∫⁻ ω, integrand (restart.outputIndex i ω, trajectory ω) ∂ℙ := by
      apply lintegral_congr_ae
      exact (restrictedTrajectoryResidualSq_actual hXregion restart i).symm
    _ = ∫⁻ z, integrand z ∂μindex.prod (ℙ.map trajectory) :=
      hjointLaw.lintegral_comp hintegrand.aemeasurable
    _ = ∫⁻ z, integrand (z.1, trajectory z.2) ∂μindex.prod ℙ :=
      lintegral_prod_map_right μindex trajectory htrajectory integrand hintegrand
    _ = ∫⁻ output,
        (Set.univ ×ˢ StochasticRun.Localization.survivalEvent
          (restart.attempt i) X K).indicator
          (fun output ↦ ENNReal.ofReal
            (KKT.residual f c
              (StochasticRun.UniformOutput.point (restart.attempt i) output)
              (StochasticRun.UniformOutput.multiplier (restart.attempt i) output) ^ 2))
          output ∂μindex.prod ℙ := by
      apply lintegral_congr_ae
      exact restrictedTrajectoryResidualSq_reference K hK X hXregion
        (restart.attempt i)
    _ = ∫⁻ output in
        Set.univ ×ˢ StochasticRun.Localization.survivalEvent
          (restart.attempt i) X K,
        ENNReal.ofReal
          (KKT.residual f c
            (StochasticRun.UniformOutput.point (restart.attempt i) output)
            (StochasticRun.UniformOutput.multiplier (restart.attempt i) output) ^ 2)
        ∂μindex.prod ℙ :=
      lintegral_indicator₀ hreferenceSuccess _
    _ = ∫⁻ output in
        Set.univ ×ˢ StochasticRun.Localization.survivalEvent
          (restart.attempt i) X K,
        ENNReal.ofReal
          (KKT.residual f c
            (StochasticRun.UniformOutput.point (restart.attempt i) output)
            (StochasticRun.UniformOutput.multiplier (restart.attempt i) output) ^ 2)
        ∂StochasticRun.UniformOutput.measure K hK ℙ := by
      rfl

/-- Helper for Corollary 3.8: every fixed attempt satisfies the required
success-restricted residual numerator bound. -/
private lemma successRestrictedSelectedResidual_le
    (K : ℕ) (hK : 2 ≤ K) (confidence : ℝ)
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (h_region : RegionCondition h oracle params confidence X) (i : ℕ) :
    (∫⁻ ω in restart.successEvent i,
        selectedAttemptResidualSq restart i ω ∂ℙ) ≤
      ℙ (restart.successEvent i) *
        ENNReal.ofReal (StochasticRun.complexityConstant h oracle params /
          ((1 - confidence) * ((K : ℝ) - 1))) := by
  -- Use the fixed-attempt law bridge, then undo conditioning by its positive mass.
  let run := restart.attempt i
  let S := StochasticRun.Localization.survivalEvent run X K
  let numerator := ∫⁻ output in Set.univ ×ˢ S,
    ENNReal.ofReal
      (KKT.residual f c
        (StochasticRun.UniformOutput.point run output)
        (StochasticRun.UniformOutput.multiplier run output) ^ 2)
      ∂StochasticRun.UniformOutput.measure K hK ℙ
  let bound := ENNReal.ofReal (StochasticRun.complexityConstant h oracle params /
    ((1 - confidence) * ((K : ℝ) - 1)))
  have htransport :
      (∫⁻ ω in restart.successEvent i,
          selectedAttemptResidualSq restart i ω ∂ℙ) = numerator := by
    have hXregion : X ⊆ h.region := fun x hx ↦
      h_region.thickening_subset (Metric.self_subset_cthickening X hx)
    exact successRestrictedSelectedResidual_eq K hK X hX hXregion restart i
  have hconditional :
      StochasticRun.UniformOutput.conditionalResidualMeanSquare run K hK X ≤ bound :=
    StochasticRun.UniformOutput.conditionalResidualMeanSquare_le K hK confidence
      confidence_pos confidence_lt_one X hX initial_mem run h_region
  have hsurvival : ENNReal.ofReal (1 - confidence) ≤ ℙ S :=
    StochasticRun.Localization.survivalProbability_ge K hK confidence confidence_pos
      X hX initial_mem run h_region
  have hsurvivalPos : ℙ S ≠ 0 := by
    apply ne_of_gt
    exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr confidence_lt_one)).trans_le hsurvival
  have hsurvivalFinite : ℙ S ≠ ⊤ := measure_ne_top ℙ S
  have hnumerator :
      numerator = ℙ S *
        StochasticRun.UniformOutput.conditionalResidualMeanSquare run K hK X := by
    calc
      numerator = 1 * numerator := (one_mul numerator).symm
      _ = (ℙ S * (ℙ S)⁻¹) * numerator := by
        rw [ENNReal.mul_inv_cancel hsurvivalPos hsurvivalFinite]
      _ = ℙ S * ((ℙ S)⁻¹ * numerator) := mul_assoc _ _ _
      _ = ℙ S *
          StochasticRun.UniformOutput.conditionalResidualMeanSquare run K hK X := by
        rw [StochasticRun.UniformOutput.conditionalResidualMeanSquare_eq_inv_mul_setLIntegral]
  calc
    (∫⁻ ω in restart.successEvent i,
        selectedAttemptResidualSq restart i ω ∂ℙ) = numerator := htransport
    _ = ℙ S *
        StochasticRun.UniformOutput.conditionalResidualMeanSquare run K hK X :=
      hnumerator
    _ ≤ ℙ S * bound := mul_le_mul_right hconditional (ℙ S)
    _ = ℙ (restart.successEvent i) * bound := by
      rw [restart.successEvent_eq_survivalEvent]

/-- Helper for Corollary 3.8: a finite extended natural has the same value
under defaulted and proof-indexed removal of `⊤`. -/
private lemma enatUntopD_eq_untop (a : ℕ∞) (d : ℕ) (ha : a ≠ ⊤) :
    a.untopD d = a.untop ha := by
  -- The finite case is definitional, while the top case contradicts `ha`.
  cases a using ENat.recTopCoe with
  | top => exact False.elim (ha rfl)
  | coe k => rfl

/-- Helper for Corollary 3.8: the returned squared residual is the residual
selected inside the stored first-accepted attempt. -/
private lemma returnedResidualSq_eq_selectedAttempt
    {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (ω : Ω) :
    ENNReal.ofReal
        (KKT.residual f c (restart.returnedPoint ω)
          (restart.returnedMultiplier ω) ^ 2) =
      selectedAttemptResidualSq restart ((restart.firstAccepted ω).untopD 0) ω := by
  -- Rewrite only through the public projections of the returned pair.
  rw [restart.returnedPoint_apply, restart.returnedMultiplier_apply]
  rfl

/-- Helper for Corollary 3.8: on termination, the defaulted selected attempt
belongs to its success event. -/
private lemma selectedAttempt_mem_successEvent
    {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (ω : Ω) (htermination : restart.firstAccepted ω ≠ ⊤) :
    ω ∈ restart.successEvent ((restart.firstAccepted ω).untopD 0) := by
  -- Replace the defaulted index by the finite index used by the owner theorem.
  rw [enatUntopD_eq_untop _ 0 htermination]
  exact restart.firstAccepted_mem_successEvent ω htermination

/-- Helper for Corollary 3.8: the event that every attempt before `i` fails. -/
private def priorFailureEvent
    {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) : Set Ω :=
  ⋂ j ∈ Finset.range i, (restart.successEvent j)ᶜ

/-- Helper for Corollary 3.8: a finite first-acceptance fiber is the
intersection of all prior failures with current success. -/
private lemma firstAcceptedFiber_eq
    {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) :
    { ω | restart.firstAccepted ω = (i : WithTop ℕ) } =
      priorFailureEvent restart i ∩ restart.successEvent i := by
  -- Convert the pointwise hitting-time characterization into the finite
  -- intersection normal form used by the measure-theoretic proof.
  ext ω
  rw [Set.mem_setOf_eq, restart.firstAccepted_eq_coe_iff]
  simp only [priorFailureEvent, Set.mem_inter_iff, Set.mem_iInter,
    Set.mem_compl_iff, Finset.mem_range]
  tauto

/-- Helper for Corollary 3.8: the event that all first coordinates in a finite
family vanish, represented by its `ℝ≥0∞` indicator. -/
private noncomputable def allFirstCoordinatesZeroWeight
    {ι : Type*} (z : ι → ℝ≥0∞ × ℝ≥0∞) : ℝ≥0∞ :=
  {z | ∀ j, (z j).1 = 0}.indicator (fun _ ↦ 1) z

/-- Helper for Corollary 3.8: the finite all-zero weight is measurable. -/
private lemma measurableAllFirstCoordinatesZeroWeight
    {ι : Type*} [Finite ι] :
    Measurable (allFirstCoordinatesZeroWeight (ι := ι)) := by
  -- The all-zero locus is a finite intersection of measurable coordinate fibers.
  have hcoordinate (j : ι) : Measurable
      (fun z : ι → ℝ≥0∞ × ℝ≥0∞ ↦ (z j).1) :=
    measurable_fst.comp (measurable_pi_apply j)
  unfold allFirstCoordinatesZeroWeight
  apply measurable_const.indicator
  rw [Set.setOf_forall]
  exact MeasurableSet.iInter fun j ↦
    (measurableSet_singleton (0 : ℝ≥0∞)).preimage
      (hcoordinate j)

/-- Helper for Corollary 3.8: the indicator of failure of every attempt before
`i`. -/
private noncomputable def priorFailureWeight
    {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) (ω : Ω) : ℝ≥0∞ :=
  (priorFailureEvent restart i).indicator (fun _ ↦ 1) ω

/-- Helper for Corollary 3.8: the finite tuple all-zero weight agrees with the
public prior-failure indicator. -/
private lemma allFirstCoordinatesZeroWeight_attempts
    {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) (ω : Ω) :
    allFirstCoordinatesZeroWeight
        (fun j : ↑(Finset.range i) ↦ successResidualObservable restart j ω) =
      priorFailureWeight restart i ω := by
  -- Compare both indicators through the same statement that every earlier
  -- success weight is zero.
  classical
  by_cases hprior : ω ∈ priorFailureEvent restart i
  · have hfail : ∀ j ∈ Finset.range i, ω ∉ restart.successEvent j := by
      simpa only [priorFailureEvent, Set.mem_iInter, Set.mem_compl_iff] using hprior
    have hsummary :
        (fun j : ↑(Finset.range i) ↦ successResidualObservable restart j ω) ∈
          {z | ∀ j, (z j).1 = 0} := by
      intro j
      unfold successResidualObservable
      change (restart.successEvent j).indicator (fun _ ↦ (1 : ℝ≥0∞)) ω = 0
      rw [Set.indicator_of_notMem (hfail j j.property)]
    unfold allFirstCoordinatesZeroWeight priorFailureWeight
    rw [Set.indicator_of_mem hsummary, Set.indicator_of_mem hprior]
  · have hsummary :
        (fun j : ↑(Finset.range i) ↦ successResidualObservable restart j ω) ∉
          {z | ∀ j, (z j).1 = 0} := by
      intro hall
      apply hprior
      simp only [priorFailureEvent, Set.mem_iInter, Set.mem_compl_iff]
      intro j hj hsuccess
      have hzero := hall ⟨j, hj⟩
      unfold successResidualObservable at hzero
      change (restart.successEvent j).indicator (fun _ ↦ (1 : ℝ≥0∞)) ω = 0 at hzero
      rw [Set.indicator_of_mem hsuccess] at hzero
      exact one_ne_zero hzero
    unfold allFirstCoordinatesZeroWeight priorFailureWeight
    rw [Set.indicator_of_notMem hsummary, Set.indicator_of_notMem hprior]

/-- Helper for Corollary 3.8: the prior-failure indicator is independent of
the current attempt's success-residual observable. -/
private lemma priorFailureWeight_indep_successResidualObservable
    {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}
    (hX : MeasurableSet X)
    (hXregion : X ⊆ h.region)
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) : ProbabilityTheory.IndepFun (priorFailureWeight restart i)
      (successResidualObservable restart i) ℙ := by
  -- Split the independent attempt family into the strict prefix and the
  -- singleton current attempt, then apply measurable coordinate summaries.
  classical
  have hrangeSingletonDisjoint : Disjoint (Finset.range i) {i} := by
    simp
  have htuple :=
    (iIndepFun_successResidualObservable hX hXregion restart).indepFun_finset₀
    (Finset.range i) {i} hrangeSingletonDisjoint
      (aemeasurableSuccessResidualObservable hX hXregion restart)
  have hprojected := htuple.comp
    measurableAllFirstCoordinatesZeroWeight
    (measurable_pi_apply ⟨i, Finset.mem_singleton_self i⟩)
  refine hprojected.congr ?_ ?_
  · exact Filter.Eventually.of_forall fun ω ↦
      allFirstCoordinatesZeroWeight_attempts restart i ω
  · exact Filter.Eventually.of_forall fun _ ↦ rfl

/-- Helper for Corollary 3.8: the event of prior failure is null-measurable. -/
private lemma nullMeasurableSetPriorFailureEvent
    {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}
    (hX : MeasurableSet X)
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) : NullMeasurableSet (priorFailureEvent restart i) ℙ := by
  -- Each earlier failure is the complement of a localization survival event.
  unfold priorFailureEvent
  apply (Finset.range i).nullMeasurableSet_biInter
  intro j hj
  rw [restart.successEvent_eq_survivalEvent]
  exact (StochasticRun.Localization.nullMeasurableSet_survivalEvent
    (restart.attempt j) X hX K).compl

/-- Helper for Corollary 3.8: every finite first-acceptance fiber is
null-measurable. -/
private lemma nullMeasurableSetFirstAcceptedFiber
    {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}
    (hX : MeasurableSet X)
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) :
    NullMeasurableSet {ω | restart.firstAccepted ω = (i : WithTop ℕ)} ℙ := by
  -- Use the finite-intersection normal form and the public survival-event API.
  rw [firstAcceptedFiber_eq restart i]
  refine (nullMeasurableSetPriorFailureEvent hX restart i).inter ?_
  rw [restart.successEvent_eq_survivalEvent]
  exact StochasticRun.Localization.nullMeasurableSet_survivalEvent
    (restart.attempt i) X hX K

/-- Helper for Corollary 3.8: on a finite first-acceptance fiber, the returned
residual is the residual selected in that fixed attempt. -/
private lemma returnedResidualSq_eq_selectedAttempt_onFiber
    {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) (ω : Ω) (hfirst : restart.firstAccepted ω = (i : WithTop ℕ)) :
    ENNReal.ofReal
        (KKT.residual f c (restart.returnedPoint ω)
          (restart.returnedMultiplier ω) ^ 2) =
      selectedAttemptResidualSq restart i ω := by
  -- First expose the stored selected attempt, then normalize its finite index.
  calc
    ENNReal.ofReal
        (KKT.residual f c (restart.returnedPoint ω)
          (restart.returnedMultiplier ω) ^ 2) =
        selectedAttemptResidualSq restart
          ((restart.firstAccepted ω).untopD 0) ω :=
      returnedResidualSq_eq_selectedAttempt restart ω
    _ = selectedAttemptResidualSq restart i ω := by
      have hindex : (restart.firstAccepted ω).untopD 0 = i := by
        rw [hfirst]
        rfl
      rw [hindex]

/-- Helper for Corollary 3.8: multiplying prior failure by current success is
the indicator of the corresponding finite first-acceptance fiber. -/
private lemma priorFailureWeight_mul_successWeight
    {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) (ω : Ω) :
    priorFailureWeight restart i ω *
        (successResidualObservable restart i ω).1 =
      {ω | restart.firstAccepted ω = (i : WithTop ℕ)}.indicator
        (fun _ ↦ (1 : ℝ≥0∞)) ω := by
  -- Resolve the two event indicators; their conjunction is exactly the fiber.
  change priorFailureWeight restart i ω *
      (restart.successEvent i).indicator (fun _ ↦ (1 : ℝ≥0∞)) ω = _
  by_cases hprior : ω ∈ priorFailureEvent restart i
  · by_cases hsuccess : ω ∈ restart.successEvent i
    · have hfiber : ω ∈ {ω | restart.firstAccepted ω = (i : WithTop ℕ)} := by
        rw [firstAcceptedFiber_eq restart i]
        exact ⟨hprior, hsuccess⟩
      unfold priorFailureWeight
      rw [Set.indicator_of_mem hprior, Set.indicator_of_mem hsuccess,
        Set.indicator_of_mem hfiber, one_mul]
    · have hnotFiber : ω ∉ {ω | restart.firstAccepted ω = (i : WithTop ℕ)} := by
        rw [firstAcceptedFiber_eq restart i]
        exact fun hfiber ↦ hsuccess hfiber.2
      unfold priorFailureWeight
      rw [Set.indicator_of_mem hprior, Set.indicator_of_notMem hsuccess,
        Set.indicator_of_notMem hnotFiber, mul_zero]
  · have hnotFiber : ω ∉ {ω | restart.firstAccepted ω = (i : WithTop ℕ)} := by
      rw [firstAcceptedFiber_eq restart i]
      exact fun hfiber ↦ hprior hfiber.1
    unfold priorFailureWeight
    rw [Set.indicator_of_notMem hprior, Set.indicator_of_notMem hnotFiber,
      zero_mul]

/-- Helper for Corollary 3.8: multiplying prior failure by the current
success-restricted residual is the returned residual restricted to that fiber. -/
private lemma priorFailureWeight_mul_successResidual
    {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) (ω : Ω) :
    priorFailureWeight restart i ω *
        (successResidualObservable restart i ω).2 =
      {ω | restart.firstAccepted ω = (i : WithTop ℕ)}.indicator
        (fun ω ↦ ENNReal.ofReal
          (KKT.residual f c (restart.returnedPoint ω)
            (restart.returnedMultiplier ω) ^ 2)) ω := by
  -- On the conjunction, identify the returned attempt; off it, one factor is zero.
  change priorFailureWeight restart i ω *
      (restart.successEvent i).indicator
        (selectedAttemptResidualSq restart i) ω = _
  by_cases hprior : ω ∈ priorFailureEvent restart i
  · by_cases hsuccess : ω ∈ restart.successEvent i
    · have hfiber : ω ∈ {ω | restart.firstAccepted ω = (i : WithTop ℕ)} := by
        rw [firstAcceptedFiber_eq restart i]
        exact ⟨hprior, hsuccess⟩
      unfold priorFailureWeight
      rw [Set.indicator_of_mem hprior, Set.indicator_of_mem hsuccess,
        Set.indicator_of_mem hfiber, one_mul]
      exact (returnedResidualSq_eq_selectedAttempt_onFiber restart i ω hfiber).symm
    · have hnotFiber : ω ∉ {ω | restart.firstAccepted ω = (i : WithTop ℕ)} := by
        rw [firstAcceptedFiber_eq restart i]
        exact fun hfiber ↦ hsuccess hfiber.2
      unfold priorFailureWeight
      rw [Set.indicator_of_mem hprior, Set.indicator_of_notMem hsuccess,
        Set.indicator_of_notMem hnotFiber, mul_zero]
  · have hnotFiber : ω ∉ {ω | restart.firstAccepted ω = (i : WithTop ℕ)} := by
      rw [firstAcceptedFiber_eq restart i]
      exact fun hfiber ↦ hprior hfiber.1
    unfold priorFailureWeight
    rw [Set.indicator_of_notMem hprior, Set.indicator_of_notMem hnotFiber,
      zero_mul]

/-- Helper for Corollary 3.8: a success-restricted bound for one attempt
transfers to the corresponding first-acceptance fiber. -/
private lemma firstAcceptedFiberResidual_le
    {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}
    (hX : MeasurableSet X)
    (hXregion : X ⊆ h.region)
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) (bound : ℝ≥0∞)
    (hfixed :
      (∫⁻ ω in restart.successEvent i,
          selectedAttemptResidualSq restart i ω ∂ℙ) ≤
        ℙ (restart.successEvent i) * bound) :
    (∫⁻ ω in {ω | restart.firstAccepted ω = (i : WithTop ℕ)},
        ENNReal.ofReal
          (KKT.residual f c (restart.returnedPoint ω)
            (restart.returnedMultiplier ω) ^ 2) ∂ℙ) ≤
      ℙ {ω | restart.firstAccepted ω = (i : WithTop ℕ)} * bound := by
  -- Record measurability once, then factor the prefix weight from each current
  -- coordinate using independence of the strict prefix and singleton attempt.
  have hpriorNull := nullMeasurableSetPriorFailureEvent hX restart i
  have hfiberNull := nullMeasurableSetFirstAcceptedFiber hX restart i
  have hsuccessNull : NullMeasurableSet (restart.successEvent i) ℙ := by
    rw [restart.successEvent_eq_survivalEvent]
    exact StochasticRun.Localization.nullMeasurableSet_survivalEvent
      (restart.attempt i) X hX K
  have hpriorMeas : AEMeasurable (priorFailureWeight restart i) ℙ := by
    unfold priorFailureWeight
    exact aemeasurable_const.indicator₀ hpriorNull
  have hcurrentMeas :=
    aemeasurableSuccessResidualObservable hX hXregion restart i
  have hindependent :=
    priorFailureWeight_indep_successResidualObservable hX hXregion restart i
  have hfactorResidual :
      (∫⁻ ω, priorFailureWeight restart i ω *
          (successResidualObservable restart i ω).2 ∂ℙ) =
        (∫⁻ ω, priorFailureWeight restart i ω ∂ℙ) *
          ∫⁻ ω, (successResidualObservable restart i ω).2 ∂ℙ :=
    ProbabilityTheory.lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun''
      hpriorMeas hcurrentMeas.snd
        (hindependent.comp measurable_id measurable_snd)
  have hfactorSuccess :
      (∫⁻ ω, priorFailureWeight restart i ω *
          (successResidualObservable restart i ω).1 ∂ℙ) =
        (∫⁻ ω, priorFailureWeight restart i ω ∂ℙ) *
          ∫⁻ ω, (successResidualObservable restart i ω).1 ∂ℙ :=
    ProbabilityTheory.lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun''
      hpriorMeas hcurrentMeas.fst
        (hindependent.comp measurable_id measurable_fst)
  have hcurrentResidualIntegral :
      (∫⁻ ω, (successResidualObservable restart i ω).2 ∂ℙ) =
        ∫⁻ ω in restart.successEvent i,
          selectedAttemptResidualSq restart i ω ∂ℙ := by
    unfold successResidualObservable
    exact lintegral_indicator₀ hsuccessNull _
  have hcurrentSuccessIntegral :
      (∫⁻ ω, (successResidualObservable restart i ω).1 ∂ℙ) =
        ℙ (restart.successEvent i) := by
    unfold successResidualObservable
    exact lintegral_indicator_one₀ hsuccessNull
  -- Factor the fiber probability through the same prefix integral.
  have hmeasureFiber :
      ℙ {ω | restart.firstAccepted ω = (i : WithTop ℕ)} =
        (∫⁻ ω, priorFailureWeight restart i ω ∂ℙ) *
          ℙ (restart.successEvent i) := by
    calc
      ℙ {ω | restart.firstAccepted ω = (i : WithTop ℕ)} =
          ∫⁻ ω, {ω | restart.firstAccepted ω = (i : WithTop ℕ)}.indicator
            (fun _ ↦ (1 : ℝ≥0∞)) ω ∂ℙ :=
        (lintegral_indicator_one₀ hfiberNull).symm
      _ = ∫⁻ ω, priorFailureWeight restart i ω *
          (successResidualObservable restart i ω).1 ∂ℙ := by
        apply lintegral_congr
        intro ω
        exact (priorFailureWeight_mul_successWeight restart i ω).symm
      _ = (∫⁻ ω, priorFailureWeight restart i ω ∂ℙ) *
          ∫⁻ ω, (successResidualObservable restart i ω).1 ∂ℙ :=
        hfactorSuccess
      _ = (∫⁻ ω, priorFailureWeight restart i ω ∂ℙ) *
          ℙ (restart.successEvent i) := by
        rw [hcurrentSuccessIntegral]
  -- Apply the fixed-attempt numerator estimate between the two factorizations.
  calc
    (∫⁻ ω in {ω | restart.firstAccepted ω = (i : WithTop ℕ)},
        ENNReal.ofReal
          (KKT.residual f c (restart.returnedPoint ω)
            (restart.returnedMultiplier ω) ^ 2) ∂ℙ) =
        ∫⁻ ω, {ω | restart.firstAccepted ω = (i : WithTop ℕ)}.indicator
          (fun ω ↦ ENNReal.ofReal
            (KKT.residual f c (restart.returnedPoint ω)
              (restart.returnedMultiplier ω) ^ 2)) ω ∂ℙ :=
      (lintegral_indicator₀ hfiberNull _).symm
    _ = ∫⁻ ω, priorFailureWeight restart i ω *
        (successResidualObservable restart i ω).2 ∂ℙ := by
      apply lintegral_congr
      intro ω
      exact (priorFailureWeight_mul_successResidual restart i ω).symm
    _ = (∫⁻ ω, priorFailureWeight restart i ω ∂ℙ) *
        ∫⁻ ω, (successResidualObservable restart i ω).2 ∂ℙ :=
      hfactorResidual
    _ = (∫⁻ ω, priorFailureWeight restart i ω ∂ℙ) *
        (∫⁻ ω in restart.successEvent i,
          selectedAttemptResidualSq restart i ω ∂ℙ) := by
      rw [hcurrentResidualIntegral]
    _ ≤ (∫⁻ ω, priorFailureWeight restart i ω ∂ℙ) *
        (ℙ (restart.successEvent i) * bound) :=
      mul_le_mul_right hfixed _
    _ = ((∫⁻ ω, priorFailureWeight restart i ω ∂ℙ) *
        ℙ (restart.successEvent i)) * bound :=
      (mul_assoc _ _ _).symm
    _ = ℙ {ω | restart.firstAccepted ω = (i : WithTop ℕ)} * bound := by
      rw [← hmeasureFiber]

/-- Helper for Corollary 3.8: uniform success-restricted attempt bounds pass
through an almost-surely terminating first-success mixture. -/
private lemma residualMeanSquare_le_of_successRestricted
    {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}
    (hX : MeasurableSet X)
    (hXregion : X ⊆ h.region)
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (bound : ℝ≥0∞)
    (htermination : ∀ᵐ ω ∂ℙ, restart.firstAccepted ω ≠ ⊤)
    (hfixed : ∀ i,
      (∫⁻ ω in restart.successEvent i,
          selectedAttemptResidualSq restart i ω ∂ℙ) ≤
        ℙ (restart.successEvent i) * bound) :
    restart.residualMeanSquare ≤ bound := by
  -- Distinct finite values of `firstAccepted` give pairwise disjoint fibers.
  have hdisjoint : Pairwise fun i j : ℕ ↦
      Disjoint {ω | restart.firstAccepted ω = (i : WithTop ℕ)}
        {ω | restart.firstAccepted ω = (j : WithTop ℕ)} := by
    intro i j hij
    rw [Set.disjoint_left]
    intro ω hi hj
    apply hij
    apply ENat.coe_inj.mp
    exact hi.symm.trans hj
  have haedisjoint : Pairwise fun i j : ℕ ↦
      AEDisjoint ℙ {ω | restart.firstAccepted ω = (i : WithTop ℕ)}
        {ω | restart.firstAccepted ω = (j : WithTop ℕ)} :=
    hdisjoint.aedisjoint
  have hfiberNull (i : ℕ) :
      NullMeasurableSet {ω | restart.firstAccepted ω = (i : WithTop ℕ)} ℙ :=
    nullMeasurableSetFirstAcceptedFiber hX restart i
  -- Almost-sure termination says that the countable union of finite fibers
  -- has full measure.
  have hunionAE : ∀ᵐ ω ∂ℙ,
      ω ∈ ⋃ i : ℕ, {ω | restart.firstAccepted ω = (i : WithTop ℕ)} := by
    filter_upwards [htermination] with ω hfinite
    obtain ⟨i, hi⟩ : ∃ i : ℕ, restart.firstAccepted ω = (i : WithTop ℕ) := by
      cases hvalue : restart.firstAccepted ω using WithTop.recTopCoe with
      | top => exact False.elim (hfinite hvalue)
      | coe i => exact ⟨i, rfl⟩
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  have hunionMeasure :
      ℙ (⋃ i : ℕ, {ω | restart.firstAccepted ω = (i : WithTop ℕ)}) = 1 := by
    calc
      ℙ (⋃ i : ℕ, {ω | restart.firstAccepted ω = (i : WithTop ℕ)}) =
          ℙ Set.univ :=
        measure_congr (Filter.eventuallyEq_univ.mpr hunionAE)
      _ = 1 := measure_univ
  -- Decompose over the full-measure disjoint union and sum the fiber bounds.
  calc
    restart.residualMeanSquare =
        ∫⁻ ω, ENNReal.ofReal
          (KKT.residual f c (restart.returnedPoint ω)
            (restart.returnedMultiplier ω) ^ 2) ∂ℙ := by
      rw [restart.residualMeanSquare_def,
        KKT.Stochastic.residualMeanSquare_def]
    _ = ∫⁻ ω in
          ⋃ i : ℕ, {ω | restart.firstAccepted ω = (i : WithTop ℕ)},
        ENNReal.ofReal
          (KKT.residual f c (restart.returnedPoint ω)
            (restart.returnedMultiplier ω) ^ 2) ∂ℙ := by
      rw [Measure.restrict_eq_self_of_ae_mem hunionAE]
    _ = ∑' i : ℕ,
        ∫⁻ ω in {ω | restart.firstAccepted ω = (i : WithTop ℕ)},
          ENNReal.ofReal
            (KKT.residual f c (restart.returnedPoint ω)
              (restart.returnedMultiplier ω) ^ 2) ∂ℙ :=
      lintegral_iUnion₀ hfiberNull haedisjoint _
    _ ≤ ∑' i : ℕ,
        ℙ {ω | restart.firstAccepted ω = (i : WithTop ℕ)} * bound :=
      ENNReal.tsum_le_tsum fun i ↦
        firstAcceptedFiberResidual_le hX hXregion restart i bound (hfixed i)
    _ = (∑' i : ℕ,
        ℙ {ω | restart.firstAccepted ω = (i : WithTop ℕ)}) * bound :=
      ENNReal.tsum_mul_right
    _ = ℙ (⋃ i : ℕ,
        {ω | restart.firstAccepted ω = (i : WithTop ℕ)}) * bound := by
      rw [measure_iUnion₀ haedisjoint hfiberNull]
    _ = 1 * bound := by rw [hunionMeasure]
    _ = bound := one_mul bound

/-- Companion to Corollary 3.8 (3): the returned pair inherits the conditional stochastic
residual bound of a successful attempt. -/
theorem residualMeanSquare_le
    (K : ℕ) (hK : 2 ≤ K) (confidence : ℝ)
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (h_region : RegionCondition h oracle params confidence X) :
    restart.residualMeanSquare ≤
      ENNReal.ofReal (StochasticRun.complexityConstant h oracle params /
        ((1 - confidence) * ((K : ℝ) - 1))) := by
  -- First establish the global termination fact and the uniform numerator
  -- estimate that will feed the first-success mixture.
  have htermination :=
    terminatesAE K hK confidence confidence_pos confidence_lt_one X hX initial_mem
      restart h_region
  have hfixed (i : ℕ) :=
    successRestrictedSelectedResidual_le K hK confidence confidence_pos
      confidence_lt_one X hX initial_mem restart h_region i
  have hXregion : X ⊆ h.region := fun x hx ↦
    h_region.thickening_subset (Metric.self_subset_cthickening X hx)
  -- Route correction: after isolating the opaque owner normalization in
  -- `firstAccepted_eq_coe_iff`, sum the verified independent fiber bounds.
  exact residualMeanSquare_le_of_successRestricted hX hXregion restart
    (ENNReal.ofReal (StochasticRun.complexityConstant h oracle params /
      ((1 - confidence) * ((K : ℝ) - 1)))) htermination hfixed

/-- Helper for Corollary 3.8: the primal point selected inside one fixed
restart attempt. -/
private noncomputable def selectedAttemptPoint
    {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) (ω : Ω) : EuclideanSpace ℝ (Fin n) :=
  (restart.attempt i).point (restart.outputIndex i ω + 1) ω

/-- Helper for Corollary 3.8: the multiplier selected inside one fixed
restart attempt. -/
private noncomputable def selectedAttemptMultiplier
    {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) (ω : Ω) : EuclideanSpace ℝ (Fin m) :=
  (restart.attempt i).multiplier (restart.outputIndex i ω + 1) ω

/-- Helper for Corollary 3.8: the selected primal point from a fixed attempt
is almost-everywhere measurable. -/
private lemma aemeasurableSelectedAttemptPoint
    {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) : AEMeasurable (selectedAttemptPoint restart i) ℙ := by
  have hjoint : AEMeasurable
      (fun ω ↦ (restart.outputIndex i ω,
        pointMultiplierObservable restart i ω)) ℙ :=
    (restart.outputIndex_hasLaw i).aemeasurable.prodMk
      (aemeasurablePointMultiplierObservable restart i)
  have hevaluate : Measurable
      (fun output : ℕ ×
        ((ℕ → EuclideanSpace ℝ (Fin n)) ×
          (ℕ → EuclideanSpace ℝ (Fin m))) ↦
        output.2.1 (output.1 + 1)) := by
    apply measurable_from_prod_countable_right
    intro k
    exact (measurable_pi_apply (k + 1)).comp measurable_fst
  unfold selectedAttemptPoint
  exact hevaluate.comp_aemeasurable hjoint

/-- Helper for Corollary 3.8: the selected multiplier from a fixed attempt
is almost-everywhere measurable. -/
private lemma aemeasurableSelectedAttemptMultiplier
    {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) : AEMeasurable (selectedAttemptMultiplier restart i) ℙ := by
  have hjoint : AEMeasurable
      (fun ω ↦ (restart.outputIndex i ω,
        pointMultiplierObservable restart i ω)) ℙ :=
    (restart.outputIndex_hasLaw i).aemeasurable.prodMk
      (aemeasurablePointMultiplierObservable restart i)
  have hevaluate : Measurable
      (fun output : ℕ ×
        ((ℕ → EuclideanSpace ℝ (Fin n)) ×
          (ℕ → EuclideanSpace ℝ (Fin m))) ↦
        output.2.2 (output.1 + 1)) := by
    apply measurable_from_prod_countable_right
    intro k
    exact (measurable_pi_apply (k + 1)).comp measurable_snd
  unfold selectedAttemptMultiplier
  exact hevaluate.comp_aemeasurable hjoint

omit [IsProbabilityMeasure ℙ] in
/-- Helper for Corollary 3.8: almost-everywhere measurable functions on a
countable null-measurable conull partition glue to a global function. -/
private lemma aemeasurable_of_eq_on_countable_partition
    {E : Type*} [MeasurableSpace E]
    (sets : ℕ → Set Ω) (hsets : ∀ i, NullMeasurableSet (sets i) ℙ)
    (hcover : ∀ᵐ ω ∂ℙ, ω ∈ ⋃ i, sets i)
    (selected : ℕ → Ω → E) (returned : Ω → E)
    (hselected : ∀ i, AEMeasurable (selected i) ℙ)
    (heq : ∀ i ω, ω ∈ sets i → returned ω = selected i ω) :
    AEMeasurable returned ℙ := by
  have hrestricted : AEMeasurable returned (ℙ.restrict (⋃ i, sets i)) := by
    rw [aemeasurable_iUnion_iff]
    intro i
    have hselectedRestricted :
        AEMeasurable (selected i) (ℙ.restrict (sets i)) :=
      (hselected i).mono_measure Measure.restrict_le_self
    have heqAE : selected i =ᵐ[ℙ.restrict (sets i)] returned :=
      (ae_restrict_mem₀ (hsets i)).mono fun ω hω ↦
        (heq i ω hω).symm
    exact hselectedRestricted.congr heqAE
  have hmeasure : ℙ.restrict (⋃ i, sets i) = ℙ :=
    Measure.restrict_eq_self_of_ae_mem hcover
  rwa [hmeasure] at hrestricted

/-- Helper for Corollary 3.8: almost-sure termination makes the union of all
finite first-acceptance fibers conull. -/
private lemma firstAcceptedFiberUnion_ae
    {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (htermination : ∀ᵐ ω ∂ℙ, restart.firstAccepted ω ≠ ⊤) :
    ∀ᵐ ω ∂ℙ,
      ω ∈ ⋃ i : ℕ, {ω | restart.firstAccepted ω = (i : WithTop ℕ)} := by
  filter_upwards [htermination] with ω hfinite
  cases hvalue : restart.firstAccepted ω using WithTop.recTopCoe with
  | top => exact False.elim (hfinite hvalue)
  | coe i => exact Set.mem_iUnion.mpr ⟨i, hvalue⟩

/-- Helper for Corollary 3.8: the returned primal point is almost-everywhere
measurable under almost-sure termination. -/
private lemma aemeasurableReturnedPoint
    {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}
    (hX : MeasurableSet X)
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (htermination : ∀ᵐ ω ∂ℙ, restart.firstAccepted ω ≠ ⊤) :
    AEMeasurable restart.returnedPoint ℙ := by
  let sets : ℕ → Set Ω := fun i ↦
    {ω | restart.firstAccepted ω = (i : WithTop ℕ)}
  have hsets (i : ℕ) : NullMeasurableSet (sets i) ℙ :=
    nullMeasurableSetFirstAcceptedFiber hX restart i
  have hcover : ∀ᵐ ω ∂ℙ, ω ∈ ⋃ i, sets i :=
    firstAcceptedFiberUnion_ae restart htermination
  have heq (i : ℕ) (ω : Ω) (hω : ω ∈ sets i) :
      restart.returnedPoint ω = selectedAttemptPoint restart i ω := by
    have hindex : (restart.firstAccepted ω).untopD 0 = i := by
      rw [hω]
      rfl
    rw [restart.returnedPoint_apply]
    unfold selectedAttemptPoint
    rw [hindex]
  exact aemeasurable_of_eq_on_countable_partition sets hsets hcover
    (selectedAttemptPoint restart) restart.returnedPoint
    (aemeasurableSelectedAttemptPoint restart) heq

/-- Helper for Corollary 3.8: the returned multiplier is almost-everywhere
measurable under almost-sure termination. -/
private lemma aemeasurableReturnedMultiplier
    {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}
    (hX : MeasurableSet X)
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (htermination : ∀ᵐ ω ∂ℙ, restart.firstAccepted ω ≠ ⊤) :
    AEMeasurable restart.returnedMultiplier ℙ := by
  let sets : ℕ → Set Ω := fun i ↦
    {ω | restart.firstAccepted ω = (i : WithTop ℕ)}
  have hsets (i : ℕ) : NullMeasurableSet (sets i) ℙ :=
    nullMeasurableSetFirstAcceptedFiber hX restart i
  have hcover : ∀ᵐ ω ∂ℙ, ω ∈ ⋃ i, sets i :=
    firstAcceptedFiberUnion_ae restart htermination
  have heq (i : ℕ) (ω : Ω) (hω : ω ∈ sets i) :
      restart.returnedMultiplier ω = selectedAttemptMultiplier restart i ω := by
    have hindex : (restart.firstAccepted ω).untopD 0 = i := by
      rw [hω]
      rfl
    rw [restart.returnedMultiplier_apply]
    unfold selectedAttemptMultiplier
    rw [hindex]
  exact aemeasurable_of_eq_on_countable_partition sets hsets hcover
    (selectedAttemptMultiplier restart) restart.returnedMultiplier
    (aemeasurableSelectedAttemptMultiplier restart) heq

/-- Companion to Corollary 3.8: the first accepted pair is measurable and
inherits the uniform successful-attempt residual bound. -/
theorem returnedPairResidualBounds
    (K : ℕ) (hK : 2 ≤ K) (confidence : ℝ)
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (h_region : RegionCondition h oracle params confidence X) :
    AEMeasurable restart.returnedPoint ℙ ∧
      AEMeasurable restart.returnedMultiplier ℙ ∧
      KKT.Stochastic.residualMeanSquare ℙ f c
          restart.returnedPoint restart.returnedMultiplier ≤
        ENNReal.ofReal (StochasticRun.complexityConstant h oracle params /
          ((1 - confidence) * ((K : ℝ) - 1))) := by
  have htermination :=
    terminatesAE K hK confidence confidence_pos confidence_lt_one X hX initial_mem
      restart h_region
  have hpoint := aemeasurableReturnedPoint hX restart htermination
  have hmultiplier := aemeasurableReturnedMultiplier hX restart htermination
  have hresidual := residualMeanSquare_le K hK confidence confidence_pos
    confidence_lt_one X hX initial_mem restart h_region
  exact ⟨hpoint, hmultiplier, hresidual⟩

/-- Corollary 3.8: at the safeguarded iteration threshold, the returned
pair is stochastic `ε`-KKT. -/
theorem isApproximatePair_of_iterationBound
    (K : ℕ) (hK : 2 ≤ K) (confidence : ℝ)
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (h_region : RegionCondition h oracle params confidence X)
    (ε : ℝ≥0) (ε_pos : 0 < ε)
    (h_iterations : StochasticRun.complexityConstant h oracle params * ε⁻¹ ^ 2 ≤
      (1 - confidence) * ((K : ℝ) - 1)) :
    KKT.Stochastic.IsApproximatePair ℙ f c ε
      restart.returnedPoint restart.returnedMultiplier := by
  have hreturned := returnedPairResidualBounds K hK confidence confidence_pos
    confidence_lt_one X hX initial_mem restart h_region
  have hε : 0 < (ε : ℝ) := by
    exact_mod_cast ε_pos
  have hεne : (ε : ℝ) ≠ 0 := hε.ne'
  have hKnat : 1 < K := by omega
  have hKreal : (1 : ℝ) < (K : ℝ) := by
    exact_mod_cast hKnat
  have hdenominator : 0 < (1 - confidence) * ((K : ℝ) - 1) :=
    mul_pos (sub_pos.mpr confidence_lt_one) (sub_pos.mpr hKreal)
  have hrealRate :
      StochasticRun.complexityConstant h oracle params /
          ((1 - confidence) * ((K : ℝ) - 1)) ≤
        (ε : ℝ) ^ 2 := by
    apply (div_le_iff₀ hdenominator).2
    calc
      StochasticRun.complexityConstant h oracle params =
          (StochasticRun.complexityConstant h oracle params * (ε : ℝ)⁻¹ ^ 2) *
            (ε : ℝ) ^ 2 := by
        field_simp [hεne]
      _ ≤ ((1 - confidence) * ((K : ℝ) - 1)) * (ε : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right h_iterations (sq_nonneg (ε : ℝ))
      _ = (ε : ℝ) ^ 2 * ((1 - confidence) * ((K : ℝ) - 1)) := by
        ring
  have hresidual :
      KKT.Stochastic.residualMeanSquare ℙ f c
          restart.returnedPoint restart.returnedMultiplier ≤
        (ε : ℝ≥0∞) ^ 2 := by
    calc
      KKT.Stochastic.residualMeanSquare ℙ f c
          restart.returnedPoint restart.returnedMultiplier ≤
          ENNReal.ofReal (StochasticRun.complexityConstant h oracle params /
            ((1 - confidence) * ((K : ℝ) - 1))) := hreturned.2.2
      _ ≤ ENNReal.ofReal ((ε : ℝ) ^ 2) :=
        ENNReal.ofReal_le_ofReal hrealRate
      _ = (ε : ℝ≥0∞) ^ 2 := by
        rw [ENNReal.ofReal_pow (NNReal.coe_nonneg ε),
          ENNReal.ofReal_coe_nnreal]
  exact KKT.Stochastic.IsApproximatePair.of_residualMeanSquare_le
    hreturned.1 hreturned.2.1 hresidual

/-- Companion to Corollary 3.8 (4): the expected stochastic-gradient count is the full-run
SPIDER budget multiplied by at most `1 / (1 - confidence)`. -/
theorem expectedGradientEvaluationCount_le
    (K : ℕ) (hK : 2 ≤ K) (confidence : ℝ)
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (h_region : RegionCondition h oracle params confidence X) :
    ∫⁻ ω, (restart.gradientEvaluationCount ω : ℝ≥0∞) ∂ℙ ≤
      ENNReal.ofReal
        (((((K ⌈/⌉ (SPIDER.refreshPeriod K : ℕ)) *
          (SPIDER.refreshBatchSize K : ℕ) +
          2 * K * (SPIDER.innerBatchSize h oracle params K : ℕ) : ℕ) : ℝ)) /
            (1 - confidence)) := by
  -- Transfer the full-run SPIDER budget through the expected attempt count.
  simpa only using expectedCost_le K hK confidence confidence_pos
    confidence_lt_one X hX initial_mem restart h_region
      restart.gradientEvaluationCount
      ((K ⌈/⌉ (SPIDER.refreshPeriod K : ℕ)) *
        (SPIDER.refreshBatchSize K : ℕ) +
        2 * K * (SPIDER.innerBatchSize h oracle params K : ℕ))
      restart.gradientEvaluationCount_le

/-- Companion to Corollary 3.8 (5): the expected logical constraint-evaluation count is at
most `K / (1 - confidence)`. -/
theorem expectedConstraintEvaluationCount_le
    (K : ℕ) (hK : 2 ≤ K) (confidence : ℝ)
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (h_region : RegionCondition h oracle params confidence X) :
    ∫⁻ ω, (restart.constraintEvaluationCount ω : ℝ≥0∞) ∂ℙ ≤
      ENNReal.ofReal ((K : ℝ) / (1 - confidence)) := by
  -- Replace the logical counter by the shared executed-iteration counter.
  simpa only [constraintEvaluationCount_eq_totalIterations] using
    expectedTotalIterations_le K hK confidence confidence_pos confidence_lt_one
      X hX initial_mem restart h_region

/-- Companion to Corollary 3.8 (6): the expected logical Jacobian-evaluation count is at
most `K / (1 - confidence)`. -/
theorem expectedJacobianEvaluationCount_le
    (K : ℕ) (hK : 2 ≤ K) (confidence : ℝ)
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (h_region : RegionCondition h oracle params confidence X) :
    ∫⁻ ω, (restart.jacobianEvaluationCount ω : ℝ≥0∞) ∂ℙ ≤
      ENNReal.ofReal ((K : ℝ) / (1 - confidence)) := by
  -- Replace the logical counter by the shared executed-iteration counter.
  simpa only [jacobianEvaluationCount_eq_totalIterations] using
    expectedTotalIterations_le K hK confidence confidence_pos confidence_lt_one
      X hX initial_mem restart h_region

/-- Companion to Corollary 3.8 (7): the expected logical linear-system solve count is at
most `K / (1 - confidence)`. -/
theorem expectedLinearSystemSolveCount_le
    (K : ℕ) (hK : 2 ≤ K) (confidence : ℝ)
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (h_region : RegionCondition h oracle params confidence X) :
    ∫⁻ ω, (restart.linearSystemSolveCount ω : ℝ≥0∞) ∂ℙ ≤
      ENNReal.ofReal ((K : ℝ) / (1 - confidence)) := by
  -- Replace the logical counter by the shared executed-iteration counter.
  simpa only [linearSystemSolveCount_eq_totalIterations] using
    expectedTotalIterations_le K hK confidence confidence_pos confidence_lt_one
      X hX initial_mem restart h_region

/-- Companion to Corollary 3.8 (8): the expected localization-membership test count is at
most `K / (1 - confidence)`. -/
theorem expectedMembershipTestCount_le
    (K : ℕ) (hK : 2 ≤ K) (confidence : ℝ)
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (h_region : RegionCondition h oracle params confidence X) :
    ∫⁻ ω, (restart.membershipTestCount ω : ℝ≥0∞) ∂ℙ ≤
      ENNReal.ofReal ((K : ℝ) / (1 - confidence)) := by
  -- Replace the membership-test counter by the executed-iteration counter.
  simpa only [membershipTestCount_eq_totalIterations] using
    expectedTotalIterations_le K hK confidence confidence_pos confidence_lt_one
      X hX initial_mem restart h_region

end LALM.SafeguardedRestart


end
