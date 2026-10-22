/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Corollary_4_2.Restart
public import TR_LALM_theory.Corollary_4_2.StoppedProcess

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LALM.Correction

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
variable {params : Parameters h x₀ multiplier₀}

namespace SafeguardedRestart

variable {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}

/-- Helper for Corollary 4.2: the event that a corrected restart attempt
passes every localization test through its horizon. -/
def successEvent
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) : Set Ω :=
  {ω | restart.completionIndicator i ω = true}

/-- Helper for Corollary 4.2: corrected restart success is exactly survival
of the corresponding corrected stochastic run through the horizon. -/
theorem successEvent_eq_survivalEvent
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) :
    restart.successEvent i = survivalEvent (restart.attempt i) X K := by
  -- Compare the two events through their common one-based point prefix.
  ext ω
  simp only [successEvent, Set.mem_setOf_eq, completionIndicator_eq_true,
    mem_survivalEvent, Finset.mem_Icc, Set.mem_Icc]

/-- Helper for Corollary 4.2: the corrected first accepted index is infinite
exactly when every restart attempt fails. -/
theorem firstAccepted_eq_top_iff
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (ω : Ω) :
    restart.firstAccepted ω = ⊤ ↔ ∀ i, ω ∉ restart.successEvent i := by
  -- Route correction: use owner normal forms because imported hitting times are opaque.
  -- Repackage the owner-side Boolean top characterization as event failure.
  simpa only [successEvent, Set.mem_setOf_eq] using
    restart.firstAccepted_eq_top_iff_completion ω

/-- Helper for Corollary 4.2: a finite corrected first accepted index belongs
to its success event. -/
theorem firstAccepted_mem_successEvent
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (ω : Ω) (htermination : restart.firstAccepted ω ≠ ⊤) :
    ω ∈ restart.successEvent ((restart.firstAccepted ω).untop htermination) := by
  -- Repackage owner-side Boolean completion as success-event membership.
  simpa only [successEvent, Set.mem_setOf_eq] using
    restart.firstAccepted_completion ω htermination

/-- Helper for Corollary 4.2: a finite corrected first accepted index is
characterized by success there and failure at every earlier index. -/
theorem firstAccepted_eq_coe_iff
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) (ω : Ω) :
    restart.firstAccepted ω = (i : ℕ∞) ↔
      ω ∈ restart.successEvent i ∧ ∀ j < i, ω ∉ restart.successEvent j := by
  -- Translate the owner-side finite hitting-time normal form to event notation.
  simpa only [successEvent, Set.mem_setOf_eq] using
    restart.firstAccepted_eq_coe_iff_completion i ω

/-- Helper for Corollary 4.2: exceeding `t` corrected attempts is exactly
failure of each of the first `t` attempts. -/
private lemma attemptCount_tail_eq_failureInter
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (t : ℕ) :
    {ω | (t : ℕ∞) < restart.attemptCount ω} =
      ⋂ i ∈ Finset.range t, (restart.successEvent i)ᶜ := by
  -- Split once on the finite-or-infinite first success, then compare indices.
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_range,
    Set.mem_compl_iff]
  cases hfirst : restart.firstAccepted ω using ENat.recTopCoe with
  | top =>
      have hall := (restart.firstAccepted_eq_top_iff ω).mp hfirst
      simp only [restart.attemptCount_eq, hfirst, top_add, ENat.coe_lt_top,
        true_iff]
      exact fun i _hi ↦ hall i
  | coe a =>
      have hcharacterization :=
        (restart.firstAccepted_eq_coe_iff a ω).mp hfirst
      simp only [restart.attemptCount_eq, hfirst, ← ENat.coe_one,
        ← ENat.coe_add, ENat.coe_lt_coe]
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

end SafeguardedRestart

end LALM.Correction

end
