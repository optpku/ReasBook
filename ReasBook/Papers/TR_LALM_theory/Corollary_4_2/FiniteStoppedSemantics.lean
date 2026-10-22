/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Corollary_4_2.StoppedScheduledAttempt
import all TR_LALM_theory.Corollary_4_2.StoppedScheduledAttempt

public section

namespace LALM.Correction

universe u v

variable {n m : ℕ}
variable {Ξ : Type u} [MeasurableSpace Ξ] {ν : MeasureTheory.Measure Ξ}
  [MeasureTheory.IsProbabilityMeasure ν]
variable {Ω : Type v} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
  [MeasureTheory.IsProbabilityMeasure P]
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
variable {x₀ : EuclideanSpace ℝ (Fin n)}
variable {multiplier₀ : EuclideanSpace ℝ (Fin m)}
variable {h : EqualityConstrained.Regularity f c}
variable {oracle : EqualityConstrained.StochasticOracle f h.region ν}
variable {params : Parameters h x₀ multiplier₀}

namespace StoppedAttempt

variable {Q B b : ℕ+} {confidence : ℝ} {K : ℕ}
variable {X : Set (EuclideanSpace ℝ (Fin n))}

/-- Helper for Corollary 4.2: when a finite stopped path has an endpoint
outside `X`, `leastExitEndpointOf` selects the least such positive endpoint. -/
noncomputable def leastExitEndpointOf
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X) (omega : Ω)
    (hExit : ∃ j : ℕ,
      1 ≤ j ∧ j ≤ K ∧ point attempt j omega ∉ X) : ℕ :=
  @Nat.find
    (fun j : ℕ ↦ 1 ≤ j ∧ j ≤ K ∧ point attempt j omega ∉ X)
    (Classical.decPred _) hExit

/-- Helper for Corollary 4.2: the selected least exit endpoint satisfies the
positive-index, horizon, and localization-failure conditions. -/
theorem leastExitEndpointOf_spec
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X) (omega : Ω)
    (hExit : ∃ j : ℕ,
      1 ≤ j ∧ j ≤ K ∧ point attempt j omega ∉ X) :
    1 ≤ leastExitEndpointOf attempt omega hExit ∧
      leastExitEndpointOf attempt omega hExit ≤ K ∧
      point attempt (leastExitEndpointOf attempt omega hExit) omega ∉ X := by
  unfold leastExitEndpointOf
  exact @Nat.find_spec _ (Classical.decPred _) hExit

/-- Helper for Corollary 4.2: the selected exit endpoint is no later than any
other positive endpoint through `K` that lies outside `X`. -/
theorem leastExitEndpointOf_le
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X) (omega : Ω)
    (hExit : ∃ j : ℕ,
      1 ≤ j ∧ j ≤ K ∧ point attempt j omega ∉ X)
    {j : ℕ} (hj : 1 ≤ j ∧ j ≤ K ∧ point attempt j omega ∉ X) :
    leastExitEndpointOf attempt omega hExit ≤ j := by
  unfold leastExitEndpointOf
  exact @Nat.find_min'
    (fun q : ℕ ↦ 1 ≤ q ∧ q ≤ K ∧ point attempt q omega ∉ X)
    (Classical.decPred _) hExit j hj

/-- Corollary 4.2: `firstExitEndpoint attempt ω` is the least positive
endpoint at which the finite stopped path leaves `X`; its value is `K + 1`
when no endpoint through `K` leaves `X`. -/
noncomputable def firstExitEndpoint
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X) (omega : Ω) : ℕ :=
  @dite ℕ
    (∃ j : ℕ, 1 ≤ j ∧ j ≤ K ∧ point attempt j omega ∉ X)
    (Classical.propDecidable _)
    (fun hExit ↦ leastExitEndpointOf attempt omega hExit)
    (fun _ ↦ K + 1)

/-- Helper for Corollary 4.2: the finite first-exit endpoint never exceeds
the no-exit sentinel `K + 1`. -/
theorem firstExitEndpoint_le_succ
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X) (omega : Ω) :
    firstExitEndpoint attempt omega ≤ K + 1 := by
  classical
  by_cases hExit : ∃ j : ℕ,
      1 ≤ j ∧ j ≤ K ∧ point attempt j omega ∉ X
  · rw [firstExitEndpoint, dif_pos hExit]
    exact Nat.le_trans (leastExitEndpointOf_spec attempt omega hExit).2.1
      (Nat.le_succ K)
  · rw [firstExitEndpoint, dif_neg hExit]

/-- Helper for Corollary 4.2: before the finite first-exit endpoint, every
positive-index endpoint remains in `X`. -/
theorem point_mem_of_lt_firstExitEndpoint
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X) (omega : Ω) (j : ℕ) (hjPositive : 1 ≤ j)
    (hjExit : j < firstExitEndpoint attempt omega) :
    point attempt j omega ∈ X := by
  classical
  by_contra hjOutside
  by_cases hExit : ∃ q : ℕ,
      1 ≤ q ∧ q ≤ K ∧ point attempt q omega ∉ X
  · rw [firstExitEndpoint, dif_pos hExit] at hjExit
    have hfirstBound : leastExitEndpointOf attempt omega hExit ≤ K :=
      (leastExitEndpointOf_spec attempt omega hExit).2.1
    have hjBound : j ≤ K := Nat.le_trans (Nat.le_of_lt hjExit) hfirstBound
    have hminimal : leastExitEndpointOf attempt omega hExit ≤ j :=
      leastExitEndpointOf_le attempt omega hExit
        ⟨hjPositive, hjBound, hjOutside⟩
    exact (Nat.not_le_of_gt hjExit) hminimal
  · exact hExit ⟨j, hjPositive, by
      rw [firstExitEndpoint, dif_neg hExit] at hjExit
      omega, hjOutside⟩

/-- Helper for Corollary 4.2: an actual finite exit endpoint is positive,
lies at or before `K`, and is outside `X`. -/
theorem firstExitEndpoint_spec_of_failure
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X) (omega : Ω)
    (hfailure : omega ∉ successEvent attempt) :
    1 ≤ firstExitEndpoint attempt omega ∧
      firstExitEndpoint attempt omega ≤ K ∧
      point attempt (firstExitEndpoint attempt omega) omega ∉ X := by
  classical
  have hExit : ∃ j : ℕ,
      1 ≤ j ∧ j ≤ K ∧ point attempt j omega ∉ X := by
    by_contra hNoExit
    apply hfailure
    apply (mem_successEvent_iff_points_mem attempt omega).mpr
    intro j hjPositive hjBound
    by_contra hjOutside
    exact hNoExit ⟨j, hjPositive, hjBound, hjOutside⟩
  rw [firstExitEndpoint, dif_pos hExit]
  exact leastExitEndpointOf_spec attempt omega hExit

/-- Corollary 4.2: activity of the padded finite stopped path is exactly the
strict prefix below its first exit endpoint, including all natural indices. -/
theorem activeAt_iff_lt_firstExitEndpoint
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X) (omega : Ω) (k : ℕ) :
    activeAt attempt k omega ↔ k < firstExitEndpoint attempt omega := by
  classical
  by_cases hk : k ≤ K
  · constructor
    · intro hactive
      by_cases hExit : ∃ j : ℕ,
          1 ≤ j ∧ j ≤ K ∧ point attempt j omega ∉ X
      · rw [firstExitEndpoint, dif_pos hExit]
        by_contra hnotBefore
        have hfirstAtMost : leastExitEndpointOf attempt omega hExit ≤ k := by
          omega
        have hpoints := (activeAt_iff_points_mem attempt k omega hk).mp hactive
        exact (leastExitEndpointOf_spec attempt omega hExit).2.2
          (hpoints (leastExitEndpointOf attempt omega hExit)
            (leastExitEndpointOf_spec attempt omega hExit).1 hfirstAtMost)
      · rw [firstExitEndpoint, dif_neg hExit]
        omega
    · intro hkExit
      apply (activeAt_iff_points_mem attempt k omega hk).mpr
      intro j hjPositive hjBound
      exact point_mem_of_lt_firstExitEndpoint attempt omega j hjPositive
        (Nat.lt_of_le_of_lt hjBound hkExit)
  · constructor
    · intro hactive
      exact (not_activeAt_of_horizon_lt attempt k
        (Nat.lt_of_not_ge hk) omega hactive).elim
    · intro hkExit
      have hupper := firstExitEndpoint_le_succ attempt omega
      omega

/-- Helper for Corollary 4.2: inactivity is equivalent to being at or after
the finite first-exit endpoint. -/
theorem not_activeAt_iff_firstExitEndpoint_le
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X) (omega : Ω) (k : ℕ) :
    ¬ activeAt attempt k omega ↔ firstExitEndpoint attempt omega ≤ k := by
  rw [activeAt_iff_lt_firstExitEndpoint]
  exact Nat.not_lt

/-- Helper for Corollary 4.2: once the finite stopped path is inactive, it
remains inactive at every later natural index. -/
theorem not_activeAt_of_le
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X) (omega : Ω) (j k : ℕ) (hjk : j ≤ k)
    (hinactive : ¬ activeAt attempt j omega) :
    ¬ activeAt attempt k omega := by
  rw [not_activeAt_iff_firstExitEndpoint_le] at hinactive ⊢
  exact Nat.le_trans hinactive hjk

/-- Corollary 4.2: terminal success is equivalent to the absence of an exit
endpoint through `K`, represented exactly by the sentinel value `K + 1`. -/
theorem mem_successEvent_iff_firstExitEndpoint_eq_succ
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X) (omega : Ω) :
    omega ∈ successEvent attempt ↔
      firstExitEndpoint attempt omega = K + 1 := by
  simp only [successEvent, Set.mem_setOf_eq]
  rw [activeAt_iff_lt_firstExitEndpoint]
  have hupper := firstExitEndpoint_le_succ attempt omega
  omega

/-- Helper for Corollary 4.2: finite-horizon failure is equivalent to the
first exit endpoint occurring at or before the terminal endpoint `K`. -/
theorem not_mem_successEvent_iff_firstExitEndpoint_le
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X) (omega : Ω) :
    omega ∉ successEvent attempt ↔
      firstExitEndpoint attempt omega ≤ K := by
  constructor
  · intro hfailure
    exact (firstExitEndpoint_spec_of_failure attempt omega hfailure).2.1
  · intro hExit hsuccess
    have hsentinel :=
      (mem_successEvent_iff_firstExitEndpoint_eq_succ attempt omega).mp
        hsuccess
    omega

/-- Corollary 4.2: failure has a unique semantic first-exit transition.  That
transition is still active, produces the first endpoint outside `X`, and every
state from that endpoint onward is inactive. -/
theorem not_mem_successEvent_iff_exists_firstExit
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X) (omega : Ω) :
    omega ∉ successEvent attempt ↔
      ∃ k : ℕ, k < K ∧
        firstExitEndpoint attempt omega = k + 1 ∧
        activeAt attempt k omega ∧
        point attempt (k + 1) omega ∉ X ∧
        ∀ j : ℕ, k + 1 ≤ j → ¬ activeAt attempt j omega := by
  constructor
  · intro hfailure
    have hspec := firstExitEndpoint_spec_of_failure attempt omega hfailure
    let k := firstExitEndpoint attempt omega - 1
    have hendpoint : firstExitEndpoint attempt omega = k + 1 := by
      dsimp only [k]
      omega
    have hkBound : k < K := by
      dsimp only [k]
      omega
    have hkActive : activeAt attempt k omega := by
      rw [activeAt_iff_lt_firstExitEndpoint]
      dsimp only [k]
      omega
    refine ⟨k, hkBound, hendpoint, hkActive, ?_, ?_⟩
    · rw [← hendpoint]
      exact hspec.2.2
    · intro j hj
      rw [not_activeAt_iff_firstExitEndpoint_le]
      rwa [hendpoint]
  · rintro ⟨k, hkBound, hendpoint, hkActive, hpointOutside, hinactive⟩
    intro hsuccess
    have hpointInside :=
      (mem_successEvent_iff_points_mem attempt omega).mp hsuccess
        (k + 1) (by omega) (by omega)
    exact hpointOutside hpointInside

/-- Helper for Corollary 4.2: the executed finite transition indices are
exactly the initial range cut off by the first exit endpoint. -/
theorem executedIndexSet_eq_range_min_firstExitEndpoint
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X) (omega : Ω) :
    executedIndexSet attempt omega =
      Finset.range (min K (firstExitEndpoint attempt omega)) := by
  classical
  ext k
  rw [mem_executedIndexSet_iff]
  simp only [Finset.mem_range]
  rw [activeAt_iff_lt_firstExitEndpoint]
  omega

/-- Helper for Corollary 4.2: the number of executed finite transitions is
the horizon clipped by the first exit endpoint. -/
theorem executedIterations_eq_min_firstExitEndpoint
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X) (omega : Ω) :
    executedIterations attempt omega =
      min K (firstExitEndpoint attempt omega) := by
  change (executedIndexSet attempt omega).card =
    min K (firstExitEndpoint attempt omega)
  rw [executedIndexSet_eq_range_min_firstExitEndpoint]
  exact Finset.card_range _

end StoppedAttempt

end LALM.Correction
