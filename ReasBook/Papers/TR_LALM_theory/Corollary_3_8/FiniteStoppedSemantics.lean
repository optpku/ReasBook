/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Corollary_3_8.StoppedScheduledAttempt
import all TR_LALM_theory.Corollary_3_8.StoppedScheduledAttempt

public section

open MeasureTheory

namespace LALM.FiniteStopped.StoppedAttempt

universe u v

variable {n m : ℕ}
variable {Ξ : Type u} [MeasurableSpace Ξ] {ν : Measure Ξ} [IsProbabilityMeasure ν]
variable {Ω : Type v} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
variable {x₀ : EuclideanSpace ℝ (Fin n)}
variable {multiplier₀ : EuclideanSpace ℝ (Fin m)}
variable {h : EqualityConstrained.Regularity f c}
variable {oracle : EqualityConstrained.StochasticOracle f h.region ν}
variable {params : LALM.Parameters h x₀ multiplier₀}
variable {Q B b : ℕ+} {confidence : ℝ} {K : ℕ}
variable {X : Set (EuclideanSpace ℝ (Fin n))}

/-- Helper for Theorem 3.7: activity of a finite stopped base trajectory
propagates to every earlier in-horizon state. -/
theorem activeAt_of_le
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (omega : Ω) (j k : ℕ) (hjk : j ≤ k) (hk : k ≤ K)
    (hactive : attempt.activeAt ⟨k, Nat.lt_succ_iff.mpr hk⟩ omega) :
    attempt.activeAt ⟨j, Nat.lt_succ_iff.mpr (hjk.trans hk)⟩ omega := by
  induction k generalizing j with
  | zero =>
      have hj : j = 0 := Nat.eq_zero_of_le_zero hjk
      simpa only [hj] using hactive
  | succ k ih =>
      have hklt : k < K := Nat.lt_of_succ_le hk
      have hactiveSucc : attempt.activeAt (⟨k, hklt⟩ : Fin K).succ omega := by
        simpa only [Fin.succ_mk] using hactive
      have hactivePrevious :
          attempt.activeAt (⟨k, hklt⟩ : Fin K).castSucc omega :=
        ((attempt.activeAt_succ_iff ⟨k, hklt⟩ omega).mp hactiveSucc).1
      have hactivePrevious' :
          attempt.activeAt ⟨k, Nat.lt_succ_of_lt hklt⟩ omega := by
        simpa only [Fin.castSucc_mk] using hactivePrevious
      by_cases hlast : j = k + 1
      · simpa only [hlast, Fin.succ_mk] using hactiveSucc
      · exact ih (j := j) (by omega) (Nat.le_of_lt hklt) hactivePrevious'

/-- Helper for Theorem 3.7: once a finite stopped base trajectory is inactive,
every later state through the horizon is inactive. -/
theorem not_activeAt_of_le
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (omega : Ω) (j k : ℕ) (hjk : j ≤ k) (hk : k ≤ K)
    (hinactive : ¬ attempt.activeAt ⟨j, Nat.lt_succ_iff.mpr (hjk.trans hk)⟩ omega) :
    ¬ attempt.activeAt ⟨k, Nat.lt_succ_iff.mpr hk⟩ omega := by
  intro hactive
  exact hinactive (attempt.activeAt_of_le omega j k hjk hk hactive)

/-- Theorem 3.7: terminal finite success is equivalent to activity at every
state through the prescribed horizon. -/
theorem mem_successEvent_iff_all_active
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (omega : Ω) :
    omega ∈ attempt.successEvent ↔
      ∀ j : ℕ, (hj : j ≤ K) →
        attempt.activeAt ⟨j, Nat.lt_succ_iff.mpr hj⟩ omega := by
  constructor
  · intro hsuccess j hj
    have hterminal :
        attempt.activeAt ⟨K, Nat.lt_succ_iff.mpr (Nat.le_refl K)⟩ omega := by
      change attempt.activeAt (Fin.last K) omega at hsuccess
      convert hsuccess using 1 <;> apply Fin.ext <;> rfl
    exact attempt.activeAt_of_le omega j K hj (Nat.le_refl K) hterminal
  · intro hall
    have hterminal := hall K (Nat.le_refl K)
    change attempt.activeAt (Fin.last K) omega
    convert hterminal using 1 <;> apply Fin.ext <;> rfl

/-- Theorem 3.7: a finite stopped base attempt succeeds exactly when every
computed endpoint from iteration `1` through `K` remains in `X`. -/
theorem mem_successEvent_iff_points_mem
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (omega : Ω) :
    omega ∈ attempt.successEvent ↔
      ∀ k : Fin K, attempt.point k.succ omega ∈ X := by
  constructor
  · intro hsuccess k
    have hall := (attempt.mem_successEvent_iff_all_active omega).mp hsuccess
    have hprevious : attempt.activeAt k.castSucc omega := by
      have h := hall k.1 (Nat.le_of_lt k.isLt)
      convert h using 1 <;> apply Fin.ext <;> rfl
    have hnext : attempt.activeAt k.succ omega := by
      have h := hall (k.1 + 1) k.isLt
      convert h using 1 <;> apply Fin.ext <;> rfl
    have hmembership := ((attempt.activeAt_succ_iff k omega).mp hnext).2
    rw [attempt.point_succ_of_active k omega hprevious]
    exact hmembership
  · intro hpoints
    apply (attempt.mem_successEvent_iff_all_active omega).mpr
    intro j hj
    induction j with
    | zero => exact attempt.activeAt_zero omega
    | succ j ih =>
        have hjlt : j < K := Nat.lt_of_succ_le hj
        let k : Fin K := ⟨j, hjlt⟩
        have hprevious' := ih (Nat.le_of_lt hjlt)
        have hprevious : attempt.activeAt k.castSucc omega := by
          simpa only [k, Fin.castSucc_mk] using hprevious'
        apply (attempt.activeAt_succ_iff k omega).mpr
        refine ⟨hprevious, ?_⟩
        rw [← attempt.point_succ_of_active k omega hprevious]
        exact hpoints k

/-- Theorem 3.7: finite failure is equivalent to an actually executed active
transition whose stored endpoint lies outside the localization set. -/
theorem not_mem_successEvent_iff_exists_active_exit
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (omega : Ω) :
    omega ∉ attempt.successEvent ↔
      ∃ k : Fin K,
        attempt.activeAt k.castSucc omega ∧ attempt.point k.succ omega ∉ X := by
  constructor
  · intro hfailure
    have hterminal :
        ¬ attempt.activeAt ⟨K, Nat.lt_succ_iff.mpr (Nat.le_refl K)⟩ omega := by
      change ¬ attempt.activeAt (Fin.last K) omega at hfailure
      intro hterminal
      apply hfailure
      convert hterminal using 1 <;> apply Fin.ext <;> rfl
    have hexitBefore (j : ℕ) (hj : j ≤ K)
        (hinactive : ¬ attempt.activeAt ⟨j, Nat.lt_succ_iff.mpr hj⟩ omega) :
        ∃ k : Fin K, k.1 < j ∧ attempt.activeAt k.castSucc omega ∧
          ¬ attempt.activeAt k.succ omega := by
      induction j with
      | zero => exact (hinactive (attempt.activeAt_zero omega)).elim
      | succ j ih =>
          have hjlt : j < K := Nat.lt_of_succ_le hj
          by_cases hprevious :
              attempt.activeAt ⟨j, Nat.lt_succ_of_lt hjlt⟩ omega
          · let k : Fin K := ⟨j, hjlt⟩
            refine ⟨k, Nat.lt_succ_self j, ?_, ?_⟩
            · convert hprevious using 1 <;> apply Fin.ext <;> rfl
            · have hidx :
                  (⟨j + 1, Nat.lt_succ_iff.mpr hj⟩ : Fin (K + 1)) = k.succ := by
                apply Fin.ext
                rfl
              rw [← hidx]
              exact hinactive
          · obtain ⟨k, hk, hactive, hnext⟩ :=
              ih (Nat.le_of_lt hjlt) hprevious
            exact ⟨k, hk.trans (Nat.lt_succ_self j), hactive, hnext⟩
    obtain ⟨k, hk, hactive, hnext⟩ :=
      hexitBefore K (Nat.le_refl K) hterminal
    have houtside : nextPointAt h oracle params Q B b k
        (attempt.state k.castSucc omega, attempt.batch k omega) ∉ X := by
      intro hmem
      exact hnext ((attempt.activeAt_succ_iff k omega).mpr
        ⟨hactive, hmem⟩)
    refine ⟨k, hactive, ?_⟩
    rw [attempt.point_succ_of_active k omega hactive]
    exact houtside
  · rintro ⟨k, _hactive, houtside⟩ hsuccess
    exact houtside ((attempt.mem_successEvent_iff_points_mem omega).mp hsuccess k)

/-! The following interface records the finite first-exit convention used in
the TeX proof.  A transition has index `k < K` and produces endpoint `k + 1`,
so the no-exit sentinel is `K + 1`. -/

/-- Helper for Theorem 3.7: extend finite activity to natural indices, with
all indices after the prescribed horizon inactive. -/
def activeAtNat
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) (omega : Ω) : Prop :=
  if hk : k ≤ K then
    attempt.activeAt ⟨k, Nat.lt_succ_iff.mpr hk⟩ omega
  else False

/-- Helper for Theorem 3.7: on the finite horizon, natural-index activity is
the original `Fin (K + 1)` activity predicate. -/
theorem activeAtNat_of_le
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (omega : Ω) (k : ℕ) (hk : k ≤ K) :
    attempt.activeAtNat k omega ↔
      attempt.activeAt ⟨k, Nat.lt_succ_iff.mpr hk⟩ omega := by
  unfold activeAtNat
  rw [dif_pos hk]

/-- Helper for Theorem 3.7: natural-index activity is false beyond the
finite horizon. -/
theorem not_activeAtNat_of_horizon_lt
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (omega : Ω) (k : ℕ) (hk : K < k) :
    ¬ attempt.activeAtNat k omega := by
  unfold activeAtNat
  rw [dif_neg (Nat.not_le_of_lt hk)]
  simp

/-- Helper for Theorem 3.7: the finite point at a bounded natural endpoint.
The bound is explicit so that the endpoint/transition off-by-one remains
visible in downstream statements. -/
def pointAtNat
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) (hk : k ≤ K) (omega : Ω) : EuclideanSpace ℝ (Fin n) :=
  attempt.point ⟨k, Nat.lt_succ_iff.mpr hk⟩ omega

/-- Helper for Theorem 3.7: the least positive inactive endpoint through
`K`; this is an auxiliary interface for the sentinel definition below. -/
noncomputable def leastExitEndpointOf
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (omega : Ω)
    (hExit : ∃ j : ℕ, 1 ≤ j ∧ j ≤ K ∧ ¬ attempt.activeAtNat j omega) : ℕ :=
  @Nat.find
    (fun j : ℕ ↦ 1 ≤ j ∧ j ≤ K ∧ ¬ attempt.activeAtNat j omega)
    (Classical.decPred _) hExit

/-- Helper for Theorem 3.7: the selected least inactive endpoint satisfies
its positivity, horizon, and inactivity conditions. -/
theorem leastExitEndpointOf_spec
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (omega : Ω)
    (hExit : ∃ j : ℕ, 1 ≤ j ∧ j ≤ K ∧ ¬ attempt.activeAtNat j omega) :
    1 ≤ leastExitEndpointOf attempt omega hExit ∧
      leastExitEndpointOf attempt omega hExit ≤ K ∧
      ¬ attempt.activeAtNat (leastExitEndpointOf attempt omega hExit) omega := by
  unfold leastExitEndpointOf
  exact @Nat.find_spec
    (fun j : ℕ ↦ 1 ≤ j ∧ j ≤ K ∧ ¬ attempt.activeAtNat j omega)
    (Classical.decPred _) hExit

/-- Helper for Theorem 3.7: the least inactive endpoint is no later than any
other positive inactive endpoint through `K`. -/
theorem leastExitEndpointOf_le
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (omega : Ω)
    (hExit : ∃ j : ℕ, 1 ≤ j ∧ j ≤ K ∧ ¬ attempt.activeAtNat j omega)
    {j : ℕ} (hj : 1 ≤ j ∧ j ≤ K ∧ ¬ attempt.activeAtNat j omega) :
    leastExitEndpointOf attempt omega hExit ≤ j := by
  unfold leastExitEndpointOf
  exact @Nat.find_min'
    (fun q : ℕ ↦ 1 ≤ q ∧ q ≤ K ∧ ¬ attempt.activeAtNat q omega)
    (Classical.decPred _) hExit j hj

/-- Theorem 3.7: the first finite exit endpoint, using `K + 1` as the
no-exit sentinel. -/
noncomputable def firstExitEndpoint
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (omega : Ω) : ℕ :=
  @dite ℕ
    (∃ j : ℕ, 1 ≤ j ∧ j ≤ K ∧ ¬ attempt.activeAtNat j omega)
    (Classical.propDecidable _)
    (fun hExit ↦ leastExitEndpointOf attempt omega hExit)
    (fun _ ↦ K + 1)

/-- Helper for Theorem 3.7: the first finite exit endpoint is bounded by the
sentinel `K + 1`. -/
theorem firstExitEndpoint_le_succ
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (omega : Ω) : firstExitEndpoint attempt omega ≤ K + 1 := by
  classical
  by_cases hExit : ∃ j : ℕ, 1 ≤ j ∧ j ≤ K ∧ ¬ attempt.activeAtNat j omega
  · rw [firstExitEndpoint, dif_pos hExit]
    exact Nat.le_trans (leastExitEndpointOf_spec attempt omega hExit).2.1
      (Nat.le_succ K)
  · rw [firstExitEndpoint, dif_neg hExit]

/-- Helper for Theorem 3.7: every positive natural endpoint strictly before
the first exit is active. -/
theorem activeAtNat_of_lt_firstExitEndpoint
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (omega : Ω) (j : ℕ) (hjPositive : 1 ≤ j)
    (hjExit : j < firstExitEndpoint attempt omega) :
    attempt.activeAtNat j omega := by
  classical
  by_contra hjInactive
  by_cases hExit : ∃ q : ℕ, 1 ≤ q ∧ q ≤ K ∧ ¬ attempt.activeAtNat q omega
  · have hjBound : j ≤ K := by
      have hfirstBound := (leastExitEndpointOf_spec attempt omega hExit).2.1
      rw [firstExitEndpoint, dif_pos hExit] at hjExit
      omega
    have hleast := leastExitEndpointOf_le attempt omega hExit (j := j)
      ⟨hjPositive, hjBound, hjInactive⟩
    have hEq : firstExitEndpoint attempt omega =
        leastExitEndpointOf attempt omega hExit := by
      rw [firstExitEndpoint, dif_pos hExit]
    rw [← hEq] at hleast
    exact (Nat.not_le_of_gt hjExit) hleast
  · have hjBound : j ≤ K := by
      rw [firstExitEndpoint, dif_neg hExit] at hjExit
      omega
    exact hExit ⟨j, hjPositive, hjBound, hjInactive⟩

/-- Helper for Theorem 3.7: failure supplies a positive inactive endpoint
through the prescribed horizon. -/
theorem exists_inactiveEndpoint_of_not_mem_successEvent
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (omega : Ω) (hfailure : omega ∉ attempt.successEvent) :
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ K ∧ ¬ attempt.activeAtNat j omega := by
  by_cases hK : K = 0
  · subst K
    have hsuccess : omega ∈ attempt.successEvent := by
      change attempt.activeAt (Fin.last 0) omega
      convert attempt.activeAt_zero omega using 1 <;> apply Fin.ext <;> rfl
    exact (hfailure hsuccess).elim
  · have hKpos : 1 ≤ K := Nat.one_le_iff_ne_zero.mpr hK
    have hterminal :
        ¬ attempt.activeAt ⟨K, Nat.lt_succ_iff.mpr (Nat.le_refl K)⟩ omega := by
      change ¬ attempt.activeAt (Fin.last K) omega at hfailure
      exact hfailure
    refine ⟨K, hKpos, Nat.le_refl K, ?_⟩
    rw [activeAtNat_of_le attempt omega K (Nat.le_refl K)]
    exact hterminal

/-- Helper for Theorem 3.7: a failed attempt has a genuine first exit
endpoint, rather than the no-exit sentinel. -/
theorem firstExitEndpoint_spec_of_failure
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (omega : Ω) (hfailure : omega ∉ attempt.successEvent) :
    1 ≤ firstExitEndpoint attempt omega ∧
      firstExitEndpoint attempt omega ≤ K ∧
      ¬ attempt.activeAtNat (firstExitEndpoint attempt omega) omega := by
  have hExit := exists_inactiveEndpoint_of_not_mem_successEvent attempt omega hfailure
  have hEq : firstExitEndpoint attempt omega =
      leastExitEndpointOf attempt omega hExit := by
    rw [firstExitEndpoint, dif_pos hExit]
  rw [hEq]
  exact leastExitEndpointOf_spec attempt omega hExit

/-- Theorem 3.7: finite activity is exactly the strict prefix below the
first exit endpoint.  A state at index `k` is the endpoint created by the
transition at index `k - 1`, while the charged transition indices satisfy
`k < K`; this makes the TeX off-by-one explicit. -/
theorem activeAt_iff_lt_firstExitEndpoint
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (omega : Ω) (k : Fin (K + 1)) :
    attempt.activeAt k omega ↔ k.1 < firstExitEndpoint attempt omega := by
  classical
  have hk : k.1 ≤ K := Nat.le_of_lt_succ k.isLt
  constructor
  · intro hactive
    by_cases hkzero : k.1 = 0
    · have hτpos : 1 ≤ firstExitEndpoint attempt omega := by
        by_cases hExit :
            ∃ j : ℕ, 1 ≤ j ∧ j ≤ K ∧ ¬ attempt.activeAtNat j omega
        · have hEq : firstExitEndpoint attempt omega =
              leastExitEndpointOf attempt omega hExit := by
            rw [firstExitEndpoint, dif_pos hExit]
          rw [hEq]
          exact (leastExitEndpointOf_spec attempt omega hExit).1
        · rw [firstExitEndpoint, dif_neg hExit]
          omega
      omega
    · by_contra hnot
      have hτle : firstExitEndpoint attempt omega ≤ k.1 :=
        Nat.le_of_not_gt hnot
      by_cases hExit :
          ∃ j : ℕ, 1 ≤ j ∧ j ≤ K ∧ ¬ attempt.activeAtNat j omega
      · have hspec := leastExitEndpointOf_spec attempt omega hExit
        have hτeq : firstExitEndpoint attempt omega =
            leastExitEndpointOf attempt omega hExit := by
          rw [firstExitEndpoint, dif_pos hExit]
        have hτbound : firstExitEndpoint attempt omega ≤ K := by
          rw [hτeq]
          exact hspec.2.1
        have hτinactive :
            ¬ attempt.activeAtNat (firstExitEndpoint attempt omega) omega := by
          rw [hτeq]
          exact hspec.2.2
        have hτactiveFin :
            attempt.activeAt
              ⟨firstExitEndpoint attempt omega,
                Nat.lt_succ_iff.mpr hτbound⟩ omega :=
          attempt.activeAt_of_le omega (firstExitEndpoint attempt omega) k.1
            hτle hk hactive
        exact hτinactive ((activeAtNat_of_le attempt omega _ hτbound).mpr hτactiveFin)
      · rw [firstExitEndpoint, dif_neg hExit] at hτle
        omega
  · intro hbefore
    by_cases hkzero : k.1 = 0
    · have hk_eq : k = (⟨0, Nat.zero_lt_succ K⟩ : Fin (K + 1)) := by
        apply Fin.ext
        exact hkzero
      rw [hk_eq]
      exact attempt.activeAt_zero omega
    · have hpositive : 1 ≤ k.1 := Nat.one_le_iff_ne_zero.mpr hkzero
      have hnat := activeAtNat_of_lt_firstExitEndpoint attempt omega k.1
        hpositive hbefore
      have hfin := (activeAtNat_of_le attempt omega k.1 hk).mp hnat
      simpa only [Fin.ext_iff] using hfin

/-- Helper for Theorem 3.7: the natural-index activity adapter has the same
strict-prefix characterization, including indices beyond the horizon. -/
theorem activeAtNat_iff_lt_firstExitEndpoint
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (omega : Ω) (k : ℕ) :
    attempt.activeAtNat k omega ↔ k < firstExitEndpoint attempt omega := by
  classical
  by_cases hk : k ≤ K
  · rw [activeAtNat_of_le attempt omega k hk]
    exact activeAt_iff_lt_firstExitEndpoint attempt omega
      (⟨k, Nat.lt_succ_iff.mpr hk⟩ : Fin (K + 1))
  · constructor
    · intro hactive
      exact (not_activeAtNat_of_horizon_lt attempt omega k
        (Nat.lt_of_not_ge hk) hactive).elim
    · intro hbefore
      have hupper := firstExitEndpoint_le_succ attempt omega
      omega

/-- Theorem 3.7: terminal success is equivalent to the sentinel endpoint
`K + 1`. -/
theorem mem_successEvent_iff_firstExitEndpoint_eq_succ
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (omega : Ω) :
    omega ∈ attempt.successEvent ↔ firstExitEndpoint attempt omega = K + 1 := by
  change attempt.activeAt (Fin.last K) omega ↔ _
  rw [activeAt_iff_lt_firstExitEndpoint]
  have hupper := firstExitEndpoint_le_succ attempt omega
  change K < firstExitEndpoint attempt omega ↔ _
  omega

/-- Theorem 3.7: finite failure is equivalent to the first exit endpoint
occurring at or before `K`. -/
theorem not_mem_successEvent_iff_firstExitEndpoint_le
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (omega : Ω) :
    omega ∉ attempt.successEvent ↔ firstExitEndpoint attempt omega ≤ K := by
  constructor
  · intro hfailure
    have hExit := exists_inactiveEndpoint_of_not_mem_successEvent attempt omega hfailure
    rw [firstExitEndpoint, dif_pos hExit]
    exact (leastExitEndpointOf_spec attempt omega hExit).2.1
  · intro hle hsuccess
    have hsentinel :=
      (mem_successEvent_iff_firstExitEndpoint_eq_succ attempt omega).mp hsuccess
    omega

/-- Helper for Theorem 3.7: at a failed attempt, the first exit endpoint is
outside the localization set. -/
theorem firstExitEndpoint_point_not_mem_of_failure
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (omega : Ω) (hfailure : omega ∉ attempt.successEvent) :
    point attempt
        ⟨firstExitEndpoint attempt omega,
          Nat.lt_succ_iff.mpr
            ((not_mem_successEvent_iff_firstExitEndpoint_le attempt omega).mp
              hfailure)⟩ omega ∉ X := by
  have hspec := firstExitEndpoint_spec_of_failure attempt omega hfailure
  let tau := firstExitEndpoint attempt omega
  have htauPos : 1 ≤ tau := by
    simpa only [tau] using hspec.1
  have htauBound : tau ≤ K := by
    simpa only [tau] using hspec.2.1
  let k : Fin K := ⟨tau - 1, by omega⟩
  have hkprevNat : attempt.activeAtNat (tau - 1) omega := by
    by_cases hτone : tau = 1
    · have hzero := attempt.activeAt_zero omega
      rw [hτone]
      apply (activeAtNat_of_le attempt omega 0 (by omega)).mpr
      exact hzero
    · exact activeAtNat_of_lt_firstExitEndpoint attempt omega (tau - 1)
        (by omega) (by omega)
  have hkprev : attempt.activeAt k.castSucc omega := by
    have hfin :=
      (activeAtNat_of_le attempt omega (tau - 1) (by omega)).mp hkprevNat
    convert hfin using 1 <;> apply Fin.ext <;> rfl
  have hidx :
      k.succ =
        (⟨tau, Nat.lt_succ_iff.mpr htauBound⟩ : Fin (K + 1)) := by
    apply Fin.ext
    dsimp [k]
    omega
  have htauInactive :
      ¬ attempt.activeAt (⟨tau, Nat.lt_succ_iff.mpr htauBound⟩ : Fin (K + 1)) omega := by
    intro hactive
    apply (by simpa only [tau] using hspec.2.2)
    exact (activeAtNat_of_le attempt omega tau htauBound).mpr hactive
  have hpoint : attempt.point k.succ omega ∉ X := by
    intro hmem
    apply htauInactive
    rw [← hidx]
    have hmodel := attempt.point_succ_of_active k omega hkprev
    apply (attempt.activeAt_succ_iff k omega).mpr
    refine ⟨hkprev, ?_⟩
    rw [← hmodel]
    exact hmem
  have hpoint' :
      attempt.point (⟨tau, Nat.lt_succ_iff.mpr htauBound⟩ : Fin (K + 1)) omega ∉ X := by
    simpa only [hidx] using hpoint
  simpa only [tau] using hpoint'

/-- Helper for Theorem 3.7: the finite transition indices that are actually
executed form a finite set of natural numbers. -/
noncomputable def executedIndexSet
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (omega : Ω) : Finset ℕ :=
  @Finset.filter ℕ (fun k : ℕ ↦ attempt.activeAtNat k omega)
    (Classical.decPred _) (Finset.range K)

/-- Helper for Theorem 3.7: membership in `executedIndexSet` exposes both
the horizon bound and the active-prefix condition. -/
theorem mem_executedIndexSet_iff
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (omega : Ω) (k : ℕ) :
    k ∈ attempt.executedIndexSet omega ↔
      k < K ∧ attempt.activeAtNat k omega := by
  classical
  simp only [executedIndexSet, Finset.mem_filter, Finset.mem_range]

/-- Helper for Theorem 3.7: the number of executed finite transitions. -/
noncomputable def executedIterations
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (omega : Ω) : ℕ :=
  (attempt.executedIndexSet omega).card

/-- Theorem 3.7: executed transition indices are exactly the range clipped
by `min K τ_ex`. -/
theorem executedIndexSet_eq_range_min_firstExitEndpoint
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (omega : Ω) :
    attempt.executedIndexSet omega =
      Finset.range (min K (firstExitEndpoint attempt omega)) := by
  classical
  ext k
  rw [mem_executedIndexSet_iff]
  rw [activeAtNat_iff_lt_firstExitEndpoint]
  simp only [Finset.mem_range]
  omega

/-- Theorem 3.7: the number of executed transitions is `min K τ_ex`; the
transition at index `k` produces endpoint `k + 1`. -/
theorem executedIterations_eq_min_firstExitEndpoint
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (omega : Ω) :
    attempt.executedIterations omega =
      min K (firstExitEndpoint attempt omega) := by
  change (attempt.executedIndexSet omega).card = _
  rw [executedIndexSet_eq_range_min_firstExitEndpoint]
  exact Finset.card_range _

end LALM.FiniteStopped.StoppedAttempt

end
