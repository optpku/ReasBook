/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import Mathlib.Probability.Process.HittingTime
public import TR_LALM_theory.Corollary_4_2.Stochastic
public import TR_LALM_theory.Theorem_3_6.UniformOutput

/-!
# Legacy corrected full-tail restart compatibility

This module keeps the earlier corrected `ScheduledRun` restart witness for
compatibility.  Its completion and accounting predicates inspect a finite
localization prefix, but the stored trajectory remains a full tail.  The
absorbing execution semantics matching the current TeX are provided by the
`StoppedScheduledAttempt` and `StoppedRestart` modules.
-/

public section

open MeasureTheory
open LALM.StochasticRun.UniformOutput
open scoped ENNReal NNReal

namespace LALM.Correction

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
variable {params : Parameters h x₀ multiplier₀}

/-- A legacy full-tail safeguarded restart for corrected SPIDER-LALM attempts
with independent uniform output selectors.  Prefix predicates below do not
assert evaluation of the stored tail after localization exit. -/
structure SafeguardedRestart
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (ℙ : Measure Ω) [IsProbabilityMeasure ℙ]
    (x₀ : EuclideanSpace ℝ (Fin n))
    (multiplier₀ : EuclideanSpace ℝ (Fin m))
    (params : Parameters h x₀ multiplier₀)
    (K : ℕ) (hK : 2 ≤ K) (X : Set (EuclideanSpace ℝ (Fin n))) where
  /-- The complete corrected stochastic run witnessing each attempt. -/
  attempt : ℕ → SPIDER.Correction.ScheduledRun h oracle ℙ x₀ multiplier₀ params K
  /-- The independent uniform selector used in each attempt. -/
  outputIndex : ℕ → Ω → ℕ
  /-- Every selector is uniform on the output index range. -/
  outputIndex_hasLaw : ∀ i,
    ProbabilityTheory.HasLaw (outputIndex i)
      (indexLaw K hK).toMeasure ℙ
  /-- Each selector is independent of its complete corrected attempt. -/
  outputIndex_indep_attempt : ∀ i,
    ProbabilityTheory.IndepFun (outputIndex i)
      (fun ω ↦
        (fun k j ↦ (attempt i).sample k j ω,
          fun k ↦ (attempt i).point k ω,
          fun k ↦ (attempt i).multiplier k ω,
          fun k ↦ (attempt i).baseStep k ω)) ℙ
  /-- Complete corrected attempts, including selectors, are mutually independent. -/
  independent_attempt : ProbabilityTheory.iIndepFun
    (fun i ω ↦
      (outputIndex i ω,
        fun k j ↦ (attempt i).sample k j ω,
        fun k ↦ (attempt i).point k ω,
        fun k ↦ (attempt i).multiplier k ω,
        fun k ↦ (attempt i).baseStep k ω)) ℙ

namespace SafeguardedRestart

variable {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}

/-- Helper for Corollary 4.2: a localization decision returns true exactly for
points in the localization set. -/
private lemma decidableResult_eq_true {p : Prop} (decision : Decidable p) :
    @decide p decision = true ↔ p := by
  -- Reflect the explicit decision through the canonical Boolean API.
  simp only [decide_eq_true_eq]

/-- Construct a corrected safeguarded restart from explicit attempts and selectors. -/
def ofAttempts
    (K : ℕ) (hK : 2 ≤ K) (X : Set (EuclideanSpace ℝ (Fin n)))
    (attempt : ℕ → SPIDER.Correction.ScheduledRun h oracle ℙ x₀ multiplier₀ params K)
    (outputIndex : ℕ → Ω → ℕ)
    (outputIndex_hasLaw : ∀ i,
      ProbabilityTheory.HasLaw (outputIndex i)
        (indexLaw K hK).toMeasure ℙ)
    (outputIndex_indep_attempt : ∀ i,
      ProbabilityTheory.IndepFun (outputIndex i)
        (fun ω ↦
          (fun k j ↦ (attempt i).sample k j ω,
            fun k ↦ (attempt i).point k ω,
            fun k ↦ (attempt i).multiplier k ω,
            fun k ↦ (attempt i).baseStep k ω)) ℙ)
    (independent_attempt : ProbabilityTheory.iIndepFun
      (fun i ω ↦
        (outputIndex i ω,
          fun k j ↦ (attempt i).sample k j ω,
          fun k ↦ (attempt i).point k ω,
          fun k ↦ (attempt i).multiplier k ω,
          fun k ↦ (attempt i).baseStep k ω)) ℙ) :
    SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X :=
  { attempt
    outputIndex
    outputIndex_hasLaw
    outputIndex_indep_attempt
    independent_attempt }

/-- The Boolean prefix indicator that one corrected full-tail attempt remains
in the localization set through the prescribed horizon. -/
noncomputable def completionIndicator
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) (ω : Ω) : Bool :=
  (List.range K).all (fun k ↦
    @decide ((restart.attempt i).point (k + 1) ω ∈ X)
      (Classical.propDecidable _))

/-- A corrected attempt completes exactly when all positive-index iterates pass
the localization test. -/
theorem completionIndicator_eq_true
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) (ω : Ω) :
    restart.completionIndicator i ω = true ↔
      ∀ j ∈ Finset.Icc 1 K, (restart.attempt i).point j ω ∈ X := by
  -- Reindex the zero-based Boolean list after reflecting classical membership.
  simp only [completionIndicator, List.all_eq_true, List.mem_range,
    decidableResult_eq_true]
  constructor
  · intro hall j hj
    have hjBounds := Finset.mem_Icc.mp hj
    have hkBound : j - 1 < K := by omega
    have hindex : j - 1 + 1 = j := Nat.sub_add_cancel hjBounds.1
    have hpoint : (restart.attempt i).point (j - 1 + 1) ω ∈ X :=
      hall (j - 1) hkBound
    simpa only [hindex] using hpoint
  · intro hall k hk
    have hmem : k + 1 ∈ Finset.Icc 1 K := by
      simp only [Finset.mem_Icc]
      omega
    exact hall (k + 1) hmem

/-- A corrected safeguarded restart exposes its selector laws, independent
attempts, and completion semantics. -/
theorem spec
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X) :
    ((∀ i, ProbabilityTheory.HasLaw (restart.outputIndex i)
        (indexLaw K hK).toMeasure ℙ) ∧
      ∀ i, ProbabilityTheory.IndepFun (restart.outputIndex i)
        (fun ω ↦
          (fun k j ↦ (restart.attempt i).sample k j ω,
            fun k ↦ (restart.attempt i).point k ω,
            fun k ↦ (restart.attempt i).multiplier k ω,
            fun k ↦ (restart.attempt i).baseStep k ω)) ℙ) ∧
    (ProbabilityTheory.iIndepFun
      (fun i ω ↦
        (restart.outputIndex i ω,
          fun k j ↦ (restart.attempt i).sample k j ω,
          fun k ↦ (restart.attempt i).point k ω,
          fun k ↦ (restart.attempt i).multiplier k ω,
          fun k ↦ (restart.attempt i).baseStep k ω)) ℙ ∧
      ∀ i ω, restart.completionIndicator i ω = true ↔
        ∀ j ∈ Finset.Icc 1 K, (restart.attempt i).point j ω ∈ X) := by
  -- Package the stored laws together with the proved completion semantics.
  exact ⟨⟨restart.outputIndex_hasLaw, restart.outputIndex_indep_attempt⟩,
    restart.independent_attempt, restart.completionIndicator_eq_true⟩

/-- The zero-based first accepted corrected attempt, or `⊤` if none succeeds. -/
noncomputable def firstAccepted
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X) :
    Ω → ℕ∞ :=
  MeasureTheory.hittingAfter restart.completionIndicator {true} 0

/-- Helper for Corollary 4.2: the corrected first accepted index is infinite
exactly when every Boolean completion indicator is false. -/
theorem firstAccepted_eq_top_iff_completion
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (ω : Ω) :
    restart.firstAccepted ω = ⊤ ↔
      ∀ i, restart.completionIndicator i ω ≠ true := by
  -- Normalize the opaque index through the hitting-time top characterization.
  change (MeasureTheory.hittingAfter restart.completionIndicator {true} 0 ω =
    (⊤ : WithTop ℕ) ↔ ∀ i, restart.completionIndicator i ω ≠ true)
  rw [MeasureTheory.hittingAfter_eq_top_iff]
  simp only [Nat.zero_le, true_imp_iff, Set.mem_singleton_iff]

/-- Helper for Corollary 4.2: the Boolean completion indicator is true at
every finite corrected first accepted index. -/
theorem firstAccepted_completion
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (ω : Ω) (htermination : restart.firstAccepted ω ≠ ⊤) :
    restart.completionIndicator
      ((restart.firstAccepted ω).untop htermination) ω = true := by
  -- Membership of a finite hitting time gives Boolean completion there.
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
  simpa only [Set.mem_singleton_iff] using hmem

/-- Helper for Corollary 4.2: a finite corrected first accepted index is
the first index whose Boolean completion indicator is true. -/
theorem firstAccepted_eq_coe_iff_completion
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) (ω : Ω) :
    restart.firstAccepted ω = (i : ℕ∞) ↔
      restart.completionIndicator i ω = true ∧
        ∀ j < i, restart.completionIndicator j ω ≠ true := by
  -- Use hitting-time membership and minimality in both directions.
  constructor
  · intro hfirst
    have htermination : restart.firstAccepted ω ≠ ⊤ := by
      rw [hfirst]
      exact ENat.coe_ne_top i
    constructor
    · have hsuccess := restart.firstAccepted_completion ω htermination
      have hindex : (restart.firstAccepted ω).untop htermination = i := by
        apply WithTop.coe_injective
        calc
          ((restart.firstAccepted ω).untop htermination : ℕ∞) =
              restart.firstAccepted ω := WithTop.coe_untop _ _
          _ = (i : ℕ∞) := hfirst
      rwa [hindex] at hsuccess
    · intro j hji
      have hfirstHitting :
          MeasureTheory.hittingAfter restart.completionIndicator {true} 0 ω =
            (i : WithTop ℕ) := hfirst
      have hjlt : (j : WithTop ℕ) < MeasureTheory.hittingAfter
          restart.completionIndicator ({true} : Set Bool) 0 ω := by
        rw [hfirstHitting]
        exact WithTop.coe_lt_coe.mpr hji
      have hnotMem := MeasureTheory.notMem_of_lt_hittingAfter
        (u := restart.completionIndicator) (s := ({true} : Set Bool))
        (n := 0) (k := j) (ω := ω) hjlt (Nat.zero_le j)
      simpa only [Set.mem_singleton_iff] using hnotMem
  · rintro ⟨hiSuccess, hprior⟩
    have hiMem : restart.completionIndicator i ω ∈ ({true} : Set Bool) := by
      simpa only [Set.mem_singleton_iff] using hiSuccess
    have hle :=
      MeasureTheory.hittingAfter_le_of_mem (u := restart.completionIndicator)
        (s := ({true} : Set Bool)) (n := 0) (ω := ω) (Nat.zero_le i) hiMem
    have hge : (i : ℕ∞) ≤ restart.firstAccepted ω := by
      apply le_of_not_gt
      intro hlt
      have htermination : restart.firstAccepted ω ≠ ⊤ :=
        ne_top_of_lt (hlt.trans (WithTop.coe_lt_top i))
      have hjlt : (restart.firstAccepted ω).untop htermination < i := by
        exact (WithTop.untop_lt_iff htermination).mpr hlt
      apply hprior ((restart.firstAccepted ω).untop htermination) hjlt
      exact restart.firstAccepted_completion ω htermination
    exact le_antisymm hle hge

/-- The one-based number of corrected attempts, equal to `⊤` on nontermination. -/
noncomputable def attemptCount
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (ω : Ω) : ℕ∞ :=
  restart.firstAccepted ω + 1

/-- The corrected attempt count is one plus the first accepted index. -/
theorem attemptCount_eq
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (ω : Ω) :
    restart.attemptCount ω = restart.firstAccepted ω + 1 := by
  rfl

/-- The corrected attempt count is infinite exactly when no attempt succeeds. -/
theorem attemptCount_eq_top_iff
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (ω : Ω) :
    restart.attemptCount ω = ⊤ ↔ restart.firstAccepted ω = ⊤ := by
  -- Adding the finite offset one preserves precisely the infinite case.
  simp only [attemptCount, ENat.add_eq_top, ENat.one_ne_top, or_false]

/-- The returned corrected primal point from the first accepted attempt. -/
noncomputable def returnedPoint
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (ω : Ω) : EuclideanSpace ℝ (Fin n) :=
  let i := (restart.firstAccepted ω).untopD 0
  (restart.attempt i).point (restart.outputIndex i ω + 1) ω

/-- The returned classical multiplier from the first accepted corrected attempt. -/
noncomputable def returnedMultiplier
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (ω : Ω) : EuclideanSpace ℝ (Fin m) :=
  let i := (restart.firstAccepted ω).untopD 0
  (restart.attempt i).multiplier (restart.outputIndex i ω + 1) ω

/-- The returned point is selected using the index of the first accepted attempt,
with the default index `0` when no attempt is accepted. -/
theorem returnedPoint_apply
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (ω : Ω) :
    restart.returnedPoint ω =
      (restart.attempt ((restart.firstAccepted ω).untopD 0)).point
        (restart.outputIndex ((restart.firstAccepted ω).untopD 0) ω + 1) ω := by
  -- Unfold the selected attempt index once.
  rfl

/-- The returned multiplier is selected using the index of the first accepted attempt,
with the default index `0` when no attempt is accepted. -/
theorem returnedMultiplier_apply
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (ω : Ω) :
    restart.returnedMultiplier ω =
      (restart.attempt ((restart.firstAccepted ω).untopD 0)).multiplier
        (restart.outputIndex ((restart.firstAccepted ω).untopD 0) ω + 1) ω := by
  -- Unfold the selected attempt index once.
  rfl

end SafeguardedRestart

end LALM.Correction

end
