/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Corollary_4_2.LocalizedEstimatorState
public import TR_LALM_theory.Theorem_3_6.CanonicalRun

public section

open MeasureTheory
open scoped BigOperators NNReal

namespace LALM.Correction

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
variable {params : Parameters h x₀ multiplier₀}

open StochasticRun.Localization

/-- Corollary 4.2: a finite corrected stochastic attempt keeps an infinite iid
sample supply but applies algorithmic transitions only through its prescribed
horizon, becoming inactive after the first failed localization test. -/
structure StoppedAttempt
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (x₀ : EuclideanSpace ℝ (Fin n))
    (multiplier₀ : EuclideanSpace ℝ (Fin m))
    (params : Parameters h x₀ multiplier₀) (Q B b : ℕ+)
    (confidence : ℝ) (K : ℕ) (X : Set (EuclideanSpace ℝ (Fin n))) where
  /-- The localization predicate is measurable; membership is used
  propositionally in the exact-real stopped transition. -/
  measurableSet_localization : MeasurableSet X
  /-- The initial point starts inside the localization set. -/
  initial_mem : x₀ ∈ X
  /-- The localization set has the regularity buffer required by active steps. -/
  region_condition : RegionCondition h oracle params confidence X
  /-- The latent iid oracle-sample array, including coordinates never read after exit. -/
  sample : ℕ → ℕ → Ω → Ξ
  /-- Every latent sample coordinate is measurable. -/
  measurable_sample (k i : ℕ) : Measurable (sample k i)
  /-- Every latent sample coordinate has the oracle law. -/
  hasLaw_sample (k i : ℕ) : ProbabilityTheory.HasLaw (sample k i) ν P
  /-- All latent sample coordinates are mutually independent. -/
  independent_sample :
    ProbabilityTheory.iIndepFun (fun ki : ℕ × ℕ ↦ sample ki.1 ki.2) P
  /-- The stopped state before each batch up to the terminal horizon. -/
  state : Fin (K + 1) → Ω → LocalizedPreBatchState h params X
  /-- Every finite stopped state is measurable. -/
  measurable_state (k : Fin (K + 1)) : Measurable (state k)
  /-- A pre-batch stopped state is independent of its fresh latent sample row. -/
  independent_state_sample (k : Fin K) :
    ProbabilityTheory.IndepFun (state k.castSucc)
      (fun omega i ↦ sample k i omega) P
  /-- The finite stopped state starts from the active initialized package. -/
  state_zero (omega : Ω) :
    state ⟨0, Nat.zero_lt_succ K⟩ omega =
      Sum.inr (initialActivePreBatchState initial_mem region_condition)
  /-- Every in-horizon successor is the absorbing localized transition. -/
  state_succ (k : Fin K) (omega : Ω) :
    state k.succ omega =
      canonicalLocalizedTransition h oracle params Q B b X region_condition k
        (state k.castSucc omega, fun i ↦ sample k i omega)

namespace StoppedAttempt

variable {Q B b : ℕ+} {confidence : ℝ} {K : ℕ}
variable {X : Set (EuclideanSpace ℝ (Fin n))}

/-- Helper for Corollary 4.2: the fresh latent row paired with a stopped state
is the batch available at that iteration. -/
def batch
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X) (k : ℕ) (omega : Ω) : ℕ → Ξ :=
  fun i ↦ attempt.sample k i omega

/-- Helper for Corollary 4.2: every stopped batch is measurable as a function
into the countable product of sample spaces. -/
theorem measurable_batch
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X) (k : ℕ) :
    Measurable (attempt.batch k) := by
  apply measurable_pi_lambda
  intro i
  exact attempt.measurable_sample k i

/-- Helper for Corollary 4.2: a localized state records whether its numerical
iteration is still active. -/
def localizedActiveFlag : LocalizedPreBatchState h params X → Bool :=
  Sum.elim (fun _ ↦ false) (fun _ ↦ true)

/-- Helper for Corollary 4.2: the localized active flag is measurable. -/
theorem measurable_localizedActiveFlag :
    Measurable (localizedActiveFlag
      (h := h) (params := params) (X := X)) := by
  exact measurable_const.sumElim measurable_const

/-- Helper for Corollary 4.2: the active flag is true exactly on the right
summand of the localized state. -/
theorem localizedActiveFlag_eq_true_iff
    (s : LocalizedPreBatchState h params X) :
    localizedActiveFlag s = true ↔ ∃ a : ActivePreBatchState h params X,
      s = Sum.inr a := by
  cases s with
  | inl u => simp [localizedActiveFlag]
  | inr a => simp [localizedActiveFlag]

/-- Helper for Corollary 4.2: the padded active indicator is false beyond the
finite horizon and otherwise reads the corresponding stopped state. -/
noncomputable def activeIndicator
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X) (k : ℕ) (omega : Ω) : Bool :=
  if hk : k ≤ K then
    localizedActiveFlag (attempt.state ⟨k, Nat.lt_succ_iff.mpr hk⟩ omega)
  else false

/-- Helper for Corollary 4.2: an iteration is active exactly when its padded
active indicator is true. -/
def activeAt
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X) (k : ℕ) (omega : Ω) : Prop :=
  attempt.activeIndicator k omega = true

/-- Helper for Corollary 4.2: an in-horizon active indicator is equivalent to
the corresponding stopped state carrying an active package. -/
theorem activeAt_iff_state
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X) (k : ℕ) (omega : Ω) (hk : k ≤ K) :
    activeAt attempt k omega ↔
      ∃ a : ActivePreBatchState h params X,
        attempt.state ⟨k, Nat.lt_succ_iff.mpr hk⟩ omega = Sum.inr a := by
  unfold activeAt activeIndicator
  rw [dif_pos hk, localizedActiveFlag_eq_true_iff]

/-- Helper for Corollary 4.2: after the finite horizon every padded indicator
is inactive. -/
theorem not_activeAt_of_horizon_lt
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X) (k : ℕ) (hk : K < k) (omega : Ω) :
    ¬ activeAt attempt k omega := by
  unfold activeAt activeIndicator
  rw [dif_neg (Nat.not_le_of_lt hk)]
  simp

/-- Helper for Corollary 4.2: an active successor state comes from an active
predecessor whose corrected point remains in the localization set. -/
theorem activeSuccessor_data
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X) (k : Fin K) (omega : Ω)
    (aNext : ActivePreBatchState h params X)
    (hnextState : attempt.state k.succ omega = Sum.inr aNext) :
    ∃ a : ActivePreBatchState h params X,
      attempt.state k.castSucc omega = Sum.inr a ∧
      canonicalActiveNextPointAt h oracle params Q B b k.1
          (a, attempt.batch k.1 omega) ∈ X ∧
      aNext.1 = canonicalActiveNextDataAt h oracle params Q B b k.1
          (a, attempt.batch k.1 omega) := by
  have hstate := attempt.state_succ k omega
  cases hprev : attempt.state k.castSucc omega with
  | inl u =>
      rw [hprev] at hstate
      have hbatch : (fun i ↦ attempt.sample k.1 i omega) =
          attempt.batch k.1 omega := by
        rfl
      rw [hbatch] at hstate
      have hstate' : attempt.state k.succ omega =
          canonicalLocalizedTransition h oracle params Q B b X
            attempt.region_condition k.1 (Sum.inl u, attempt.batch k.1 omega) := by
        exact hstate
      rw [canonicalLocalizedTransition_inactive X attempt.region_condition
        k.1 (attempt.batch k.1 omega)] at hstate'
      rw [hstate'] at hnextState
      cases hnextState
  | inr a =>
      by_cases hmem : canonicalActiveNextPointAt h oracle params Q B b k.1
          (a, attempt.batch k.1 omega) ∈ X
      · have htransition := canonicalLocalizedTransition_active_of_mem X
          attempt.region_condition k.1 a (attempt.batch k.1 omega) hmem
        rw [hprev] at hstate
        have hbatch : (fun i ↦ attempt.sample k.1 i omega) =
            attempt.batch k.1 omega := by
          rfl
        rw [hbatch] at hstate
        have hstate' : attempt.state k.succ omega =
            canonicalLocalizedTransition h oracle params Q B b X
              attempt.region_condition k.1 (Sum.inr a, attempt.batch k.1 omega) := by
          exact hstate
        rw [htransition] at hstate'
        rw [hstate'] at hnextState
        have haNext : aNext =
            ⟨canonicalActiveNextDataAt h oracle params Q B b k.1
              (a, attempt.batch k.1 omega),
              canonicalActiveNextDataAt_invariant attempt.region_condition k.1
                (a, attempt.batch k.1 omega) hmem⟩ :=
          (Sum.inr.inj hnextState).symm
        refine ⟨a, rfl, hmem, ?_⟩
        exact congrArg Subtype.val haNext
      · have htransition := canonicalLocalizedTransition_active_of_not_mem X
          attempt.region_condition k.1 a (attempt.batch k.1 omega) hmem
        rw [hprev] at hstate
        have hbatch : (fun i ↦ attempt.sample k.1 i omega) =
            attempt.batch k.1 omega := by
          rfl
        rw [hbatch] at hstate
        have hstate' : attempt.state k.succ omega =
            canonicalLocalizedTransition h oracle params Q B b X
              attempt.region_condition k.1 (Sum.inr a, attempt.batch k.1 omega) := by
          exact hstate
        rw [htransition] at hstate'
        rw [hstate'] at hnextState
        cases hnextState

/-- Helper for Corollary 4.2: the padded point transition freezes an inactive
point and otherwise records the newly computed corrected endpoint. -/
noncomputable def paddedPointTransition
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : Parameters h x₀ multiplier₀) (Q B b : ℕ+)
    {X : Set (EuclideanSpace ℝ (Fin n))} (k : ℕ) :
    LocalizedPreBatchState h params X ×
        (EuclideanSpace ℝ (Fin n) × (ℕ → Ξ)) →
      EuclideanSpace ℝ (Fin n) :=
  Sum.elim
      (fun z : Unit × (EuclideanSpace ℝ (Fin n) × (ℕ → Ξ)) ↦ z.2.1)
      (fun z : ActivePreBatchState h params X ×
          (EuclideanSpace ℝ (Fin n) × (ℕ → Ξ)) ↦
        canonicalActiveNextPointAt h oracle params Q B b k (z.1, z.2.2)) ∘
    MeasurableEquiv.sumProdDistrib Unit (ActivePreBatchState h params X)
      (EuclideanSpace ℝ (Fin n) × (ℕ → Ξ))

/-- Helper for Corollary 4.2: the padded multiplier transition freezes an
inactive multiplier and otherwise records the newly computed multiplier. -/
noncomputable def paddedMultiplierTransition
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : Parameters h x₀ multiplier₀) (Q B b : ℕ+)
    {X : Set (EuclideanSpace ℝ (Fin n))} (k : ℕ) :
    LocalizedPreBatchState h params X ×
        (EuclideanSpace ℝ (Fin m) × (ℕ → Ξ)) →
      EuclideanSpace ℝ (Fin m) :=
  Sum.elim
      (fun z : Unit × (EuclideanSpace ℝ (Fin m) × (ℕ → Ξ)) ↦ z.2.1)
      (fun z : ActivePreBatchState h params X ×
          (EuclideanSpace ℝ (Fin m) × (ℕ → Ξ)) ↦
        canonicalActiveNextMultiplierAt h oracle params Q B b k (z.1, z.2.2)) ∘
    MeasurableEquiv.sumProdDistrib Unit (ActivePreBatchState h params X)
      (EuclideanSpace ℝ (Fin m) × (ℕ → Ξ))

/-- Helper for Corollary 4.2: the padded base-step transition is zero on the
inactive summand and the canonical base step on the active summand. -/
noncomputable def paddedBaseStepTransition
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : Parameters h x₀ multiplier₀) (Q B b : ℕ+)
    {X : Set (EuclideanSpace ℝ (Fin n))} (k : ℕ) :
    LocalizedPreBatchState h params X × (ℕ → Ξ) →
      EuclideanSpace ℝ (Fin n) :=
  Sum.elim
      (fun _z : Unit × (ℕ → Ξ) ↦ (0 : EuclideanSpace ℝ (Fin n)))
      (fun z : ActivePreBatchState h params X × (ℕ → Ξ) ↦
        canonicalActiveBaseStepAt h oracle params Q B b k (z.1, z.2)) ∘
    MeasurableEquiv.sumProdDistrib Unit (ActivePreBatchState h params X)
      (ℕ → Ξ)

/-- Helper for Corollary 4.2: the padded primal transition is measurable in the
localized state, previous point, and fresh batch. -/
theorem measurable_paddedPointTransition
    (X : Set (EuclideanSpace ℝ (Fin n))) (_hX : MeasurableSet X)
    (h_region : RegionCondition h oracle params confidence X) (k : ℕ) :
    Measurable (paddedPointTransition h oracle params Q B b (X := X) k) := by
  unfold paddedPointTransition
  have hinactive : Measurable (fun z : Unit ×
      (EuclideanSpace ℝ (Fin n) × (ℕ → Ξ)) ↦ z.2.1) := by
    exact measurable_fst.comp measurable_snd
  have hactive : Measurable (fun z : ActivePreBatchState h params X ×
      (EuclideanSpace ℝ (Fin n) × (ℕ → Ξ)) ↦
      canonicalActiveNextPointAt h oracle params Q B b k (z.1, z.2.2)) := by
    exact (measurable_canonicalActiveNextPointAt h_region k).comp
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  exact (hinactive.sumElim hactive).comp
    (MeasurableEquiv.sumProdDistrib Unit (ActivePreBatchState h params X)
      (EuclideanSpace ℝ (Fin n) × (ℕ → Ξ))).measurable

/-- Helper for Corollary 4.2: the padded multiplier transition is measurable in
the localized state, previous multiplier, and fresh batch. -/
theorem measurable_paddedMultiplierTransition
    (X : Set (EuclideanSpace ℝ (Fin n))) (_hX : MeasurableSet X)
    (h_region : RegionCondition h oracle params confidence X) (k : ℕ) :
    Measurable (paddedMultiplierTransition h oracle params Q B b (X := X) k) := by
  unfold paddedMultiplierTransition
  have hinactive : Measurable (fun z : Unit ×
      (EuclideanSpace ℝ (Fin m) × (ℕ → Ξ)) ↦ z.2.1) := by
    exact measurable_fst.comp measurable_snd
  have hactive : Measurable (fun z : ActivePreBatchState h params X ×
      (EuclideanSpace ℝ (Fin m) × (ℕ → Ξ)) ↦
      canonicalActiveNextMultiplierAt h oracle params Q B b k (z.1, z.2.2)) := by
    exact (measurable_canonicalActiveNextMultiplierAt h_region k).comp
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  exact (hinactive.sumElim hactive).comp
    (MeasurableEquiv.sumProdDistrib Unit (ActivePreBatchState h params X)
      (EuclideanSpace ℝ (Fin m) × (ℕ → Ξ))).measurable

/-- Helper for Corollary 4.2: the padded base-step transition is measurable in
the localized state and fresh batch. -/
theorem measurable_paddedBaseStepTransition
    (X : Set (EuclideanSpace ℝ (Fin n)))
    (h_region : RegionCondition h oracle params confidence X) (k : ℕ) :
    Measurable (paddedBaseStepTransition h oracle params Q B b (X := X) k) := by
  unfold paddedBaseStepTransition
  have hinactive : Measurable
      (fun _z : Unit × (ℕ → Ξ) ↦ (0 : EuclideanSpace ℝ (Fin n))) :=
    measurable_const
  have hactive : Measurable
      (fun z : ActivePreBatchState h params X × (ℕ → Ξ) ↦
        canonicalActiveBaseStepAt h oracle params Q B b k (z.1, z.2)) := by
    exact (measurable_canonicalActiveBaseStepAt h_region k).comp
      measurable_id
  exact (hinactive.sumElim hactive).comp
    (MeasurableEquiv.sumProdDistrib Unit (ActivePreBatchState h params X)
      (ℕ → Ξ)).measurable

/-- Helper for Corollary 4.2: the padded primal path stores every computed
endpoint through the horizon and freezes after inactivity or the horizon. -/
noncomputable def point
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X) : ℕ → Ω → EuclideanSpace ℝ (Fin n)
  | 0, _ => x₀
  | k + 1, omega =>
      if hk : k < K then
        paddedPointTransition h oracle params Q B b k
          (attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩ omega,
            point attempt k omega, attempt.batch k omega)
      else point attempt k omega

/-- Helper for Corollary 4.2: the padded multiplier path stores every computed
active update and freezes after inactivity or the horizon. -/
noncomputable def multiplier
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X) : ℕ → Ω → EuclideanSpace ℝ (Fin m)
  | 0, _ => multiplier₀
  | k + 1, omega =>
      if hk : k < K then
        paddedMultiplierTransition h oracle params Q B b k
          (attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩ omega,
            multiplier attempt k omega, attempt.batch k omega)
      else multiplier attempt k omega

/-- Helper for Corollary 4.2: every padded primal path coordinate is
measurable. -/
theorem measurable_point
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X) (k : ℕ) : Measurable (attempt.point k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
      by_cases hk : k < K
      · simp only [point, dif_pos hk]
        exact (measurable_paddedPointTransition X
          attempt.measurableSet_localization attempt.region_condition k).comp
          ((attempt.measurable_state ⟨k, Nat.lt_succ_of_lt hk⟩).prodMk
            (ih.prodMk (measurable_batch attempt k)))
      · simp only [point, dif_neg hk]
        exact ih

/-- Helper for Corollary 4.2: every padded multiplier path coordinate is
measurable. -/
theorem measurable_multiplier
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X) (k : ℕ) : Measurable (attempt.multiplier k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
      by_cases hk : k < K
      · simp only [multiplier, dif_pos hk]
        exact (measurable_paddedMultiplierTransition X
          attempt.measurableSet_localization attempt.region_condition k).comp
          ((attempt.measurable_state ⟨k, Nat.lt_succ_of_lt hk⟩).prodMk
            (ih.prodMk (measurable_batch attempt k)))
      · simp only [multiplier, dif_neg hk]
        exact ih

/-- Helper for Corollary 4.2: the padded active indicator is measurable. -/
theorem measurable_activeIndicator
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X) (k : ℕ) :
    Measurable (attempt.activeIndicator k) := by
  by_cases hk : k ≤ K
  · have heq : attempt.activeIndicator k =
        (fun omega => localizedActiveFlag
          (attempt.state ⟨k, Nat.lt_succ_iff.mpr hk⟩ omega)) := by
      funext omega
      unfold activeIndicator
      simp [hk]
    rw [heq]
    exact measurable_localizedActiveFlag.comp
      (attempt.measurable_state ⟨k, Nat.lt_succ_iff.mpr hk⟩)
  · have heq : attempt.activeIndicator k = (fun _ : Ω => false) := by
      funext omega
      unfold activeIndicator
      simp [hk]
    rw [heq]
    exact measurable_const

/-- Helper for Corollary 4.2: the padded activity event is measurable. -/
theorem measurableSet_activeAt
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X) (k : ℕ) : MeasurableSet {omega | activeAt attempt k omega} := by
  change MeasurableSet
    ((fun omega => attempt.activeIndicator k omega) ⁻¹' ({true} : Set Bool))
  exact (measurableSet_singleton true).preimage (measurable_activeIndicator attempt k)

/-- Helper for Corollary 4.2: whenever a stopped state is active, its current
point agrees with the padded primal path. -/
theorem activeState_current_eq_point
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X) (k : ℕ) (omega : Ω) (hk : k ≤ K)
    (a : ActivePreBatchState h params X)
    (ha : attempt.state ⟨k, Nat.lt_succ_iff.mpr hk⟩ omega = Sum.inr a) :
    a.1.1 = attempt.point k omega := by
  induction k generalizing a with
  | zero =>
      have hz := attempt.state_zero omega
      have haeq : initialActivePreBatchState attempt.initial_mem
          attempt.region_condition = a := Sum.inr.inj (hz.symm.trans ha)
      rw [← haeq]
      rw [initialActivePreBatchState_current]
      rfl
  | succ k ih =>
      have hklt : k < K := Nat.lt_of_succ_le hk
      have ha' : attempt.state ⟨k + 1, Nat.lt_succ_iff.mpr hk⟩ omega = Sum.inr a := by
        simpa only [Fin.succ_mk] using ha
      obtain ⟨aPrev, hprev, hmem, hdata⟩ :=
        activeSuccessor_data attempt ⟨k, hklt⟩ omega a ha'
      have hprev' : attempt.state ⟨k, Nat.lt_succ_of_lt hklt⟩ omega =
          Sum.inr aPrev := by
        simpa only [Fin.castSucc_mk] using hprev
      have hprevMem : k ≤ K := Nat.le_of_lt hklt
      have hpointPrev : aPrev.1.1 = attempt.point k omega :=
        ih hprevMem aPrev hprev'
      rw [point, dif_pos hklt]
      rw [hprev']
      change a.1.1 = canonicalActiveNextPointAt h oracle params Q B b k
        (aPrev, attempt.batch k omega)
      rw [← canonicalActiveNextDataAt_current (h := h) (oracle := oracle)
        (params := params) (Q := Q) (B := B) (b := b) aPrev
        (attempt.batch k omega) k, ← hdata]

/-- Helper for Corollary 4.2: whenever a stopped state is active, its
multiplier agrees with the padded multiplier path. -/
theorem activeState_multiplier_eq_multiplier
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X) (k : ℕ) (omega : Ω) (hk : k ≤ K)
    (a : ActivePreBatchState h params X)
    (ha : attempt.state ⟨k, Nat.lt_succ_iff.mpr hk⟩ omega = Sum.inr a) :
    a.1.2.2.1 = attempt.multiplier k omega := by
  induction k generalizing a with
  | zero =>
      have hz := attempt.state_zero omega
      have haeq : initialActivePreBatchState attempt.initial_mem
          attempt.region_condition = a := Sum.inr.inj (hz.symm.trans ha)
      rw [← haeq]
      rw [initialActivePreBatchState_multiplier]
      rfl
  | succ k ih =>
      have hklt : k < K := Nat.lt_of_succ_le hk
      have ha' : attempt.state ⟨k + 1, Nat.lt_succ_iff.mpr hk⟩ omega = Sum.inr a := by
        simpa only [Fin.succ_mk] using ha
      obtain ⟨aPrev, hprev, hmem, hdata⟩ :=
        activeSuccessor_data attempt ⟨k, hklt⟩ omega a ha'
      have hprev' : attempt.state ⟨k, Nat.lt_succ_of_lt hklt⟩ omega =
          Sum.inr aPrev := by
        simpa only [Fin.castSucc_mk] using hprev
      have hprevMem : k ≤ K := Nat.le_of_lt hklt
      have hmultPrev : aPrev.1.2.2.1 = attempt.multiplier k omega :=
        ih hprevMem aPrev hprev'
      rw [multiplier, dif_pos hklt]
      rw [hprev']
      change a.1.2.2.1 = canonicalActiveNextMultiplierAt h oracle params Q B b k
        (aPrev, attempt.batch k omega)
      rw [← canonicalActiveNextDataAt_multiplier (h := h) (oracle := oracle)
        (params := params) (Q := Q) (B := B) (b := b) aPrev
        (attempt.batch k omega) k, ← hdata]

/-- Helper for Corollary 4.2: an active state's preceding point is the padded
point at the preceding natural index. -/
theorem activeState_previous_eq_point
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X) (k : ℕ) (omega : Ω) (hk : k ≤ K)
    (a : ActivePreBatchState h params X)
    (ha : attempt.state ⟨k, Nat.lt_succ_iff.mpr hk⟩ omega = Sum.inr a) :
    a.1.2.1 = attempt.point (k - 1) omega := by
  induction k generalizing a with
  | zero =>
      have hz := attempt.state_zero omega
      have haeq : initialActivePreBatchState attempt.initial_mem
          attempt.region_condition = a := Sum.inr.inj (hz.symm.trans ha)
      rw [← haeq, initialActivePreBatchState_previous]
      rfl
  | succ k ih =>
      have hklt : k < K := Nat.lt_of_succ_le hk
      have ha' : attempt.state ⟨k + 1, Nat.lt_succ_iff.mpr hk⟩ omega = Sum.inr a := by
        simpa only [Fin.succ_mk] using ha
      obtain ⟨aPrev, hprev, hmem, hdata⟩ :=
        activeSuccessor_data attempt ⟨k, hklt⟩ omega a ha'
      have hprev' : attempt.state ⟨k, Nat.lt_succ_of_lt hklt⟩ omega =
          Sum.inr aPrev := by
        simpa only [Fin.castSucc_mk] using hprev
      have hpointPrev : aPrev.1.1 = attempt.point k omega :=
        activeState_current_eq_point attempt k omega (Nat.le_of_lt hklt)
          aPrev hprev'
      change a.1.2.1 = attempt.point (k + 1 - 1) omega
      rw [hdata]
      rw [canonicalActiveNextDataAt_previous (h := h) (oracle := oracle)
        (params := params) (Q := Q) (B := B) (b := b) aPrev
        (attempt.batch k omega) k]
      simpa only [Nat.succ_sub_one] using hpointPrev

/-- Helper for Corollary 4.2: within the horizon, activity at the next index
is equivalent to prior activity and localization of the new padded point. -/
theorem activeAt_succ_iff
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X) (k : Fin K) (omega : Ω) :
    activeAt attempt (k.1 + 1) omega ↔
      activeAt attempt k.1 omega ∧ point attempt (k.1 + 1) omega ∈ X := by
  have hkBound : k.1 ≤ K := Nat.le_of_lt k.isLt
  have hsuccBound : k.1 + 1 ≤ K := Nat.succ_le_of_lt k.isLt
  constructor
  · intro hnextActive
    obtain ⟨aNext, hnextState⟩ :=
      (activeAt_iff_state attempt (k.1 + 1) omega hsuccBound).mp hnextActive
    have hnextState' : attempt.state k.succ omega = Sum.inr aNext := by
      have hindex :
          (⟨k.1 + 1, Nat.lt_succ_iff.mpr hsuccBound⟩ : Fin (K + 1)) = k.succ := by
        apply Fin.ext
        rfl
      rw [← hindex]
      exact hnextState
    obtain ⟨aPrev, hprev, hmem, hdata⟩ :=
      activeSuccessor_data attempt k omega aNext hnextState'
    have hprevActive : activeAt attempt k.1 omega :=
      (activeAt_iff_state attempt k.1 omega hkBound).mpr ⟨aPrev, hprev⟩
    have hpoint :
        canonicalActiveNextPointAt h oracle params Q B b k.1
            (aPrev, attempt.batch k.1 omega) = point attempt (k.1 + 1) omega := by
      have hpointState := activeState_current_eq_point attempt (k.1 + 1) omega
        hsuccBound aNext hnextState
      rw [hdata] at hpointState
      rw [canonicalActiveNextDataAt_current (h := h) (oracle := oracle)
        (params := params) (Q := Q) (B := B) (b := b) aPrev
        (attempt.batch k.1 omega) k.1] at hpointState
      exact hpointState
    exact ⟨hprevActive, hpoint ▸ hmem⟩
  · rintro ⟨hprevActive, hpointMem⟩
    obtain ⟨aPrev, hprev⟩ :=
      (activeAt_iff_state attempt k.1 omega hkBound).mp hprevActive
    have hprev' : attempt.state k.castSucc omega = Sum.inr aPrev := by
      have hindex :
          (⟨k.1, Nat.lt_succ_iff.mpr hkBound⟩ : Fin (K + 1)) = k.castSucc := by
        apply Fin.ext
        rfl
      rw [← hindex]
      exact hprev
    have hnextMem :
        canonicalActiveNextPointAt h oracle params Q B b k.1
            (aPrev, attempt.batch k.1 omega) ∈ X := by
      have hpointDef : point attempt (k.1 + 1) omega =
          canonicalActiveNextPointAt h oracle params Q B b k.1
            (aPrev, attempt.batch k.1 omega) := by
        rw [point, dif_pos k.isLt, hprev]
        rfl
      rw [← hpointDef]
      exact hpointMem
    have hstate := attempt.state_succ k omega
    rw [hprev'] at hstate
    have hbatch : (fun i ↦ attempt.sample k.1 i omega) =
        attempt.batch k.1 omega := by
      rfl
    rw [hbatch] at hstate
    rw [canonicalLocalizedTransition_active_of_mem X attempt.region_condition
      k.1 aPrev (attempt.batch k.1 omega) hnextMem] at hstate
    apply (activeAt_iff_state attempt (k.1 + 1) omega hsuccBound).mpr
    let aNext : ActivePreBatchState h params X :=
      ⟨canonicalActiveNextDataAt h oracle params Q B b k.1
          (aPrev, attempt.batch k.1 omega),
        canonicalActiveNextDataAt_invariant attempt.region_condition k.1
          (aPrev, attempt.batch k.1 omega) hnextMem⟩
    refine ⟨aNext, ?_⟩
    dsimp [aNext]
    have hindex :
        (⟨k.1 + 1, Nat.lt_succ_iff.mpr hsuccBound⟩ : Fin (K + 1)) = k.succ := by
      apply Fin.ext
      rfl
    rw [hindex]
    exact hstate

/-- Helper for Corollary 4.2: the initialized stopped state is active at
horizon zero. -/
theorem activeAt_zero
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X) (omega : Ω) :
    activeAt attempt 0 omega := by
  apply (activeAt_iff_state attempt 0 omega (Nat.zero_le K)).mpr
  refine ⟨initialActivePreBatchState attempt.initial_mem
    attempt.region_condition, ?_⟩
  exact attempt.state_zero omega

/-- Helper for Corollary 4.2: activity through a horizon is equivalent to
localization of every positive-index padded point through that horizon. -/
theorem activeAt_iff_points_mem
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X) (k : ℕ) (omega : Ω) (hk : k ≤ K) :
    activeAt attempt k omega ↔
      ∀ j : ℕ, 1 ≤ j → j ≤ k → point attempt j omega ∈ X := by
  induction k with
  | zero =>
      constructor
      · intro _ j hjOne hjZero
        omega
      · intro _
        exact activeAt_zero attempt omega
  | succ k ih =>
      have hklt : k < K := Nat.lt_of_succ_le hk
      rw [activeAt_succ_iff attempt ⟨k, hklt⟩ omega]
      constructor
      · rintro ⟨hprev, hpoint⟩ j hjOne hjTop
        by_cases hjLast : j = k + 1
        · simpa only [hjLast] using hpoint
        · have hjPrev : j ≤ k := by omega
          exact (ih (Nat.le_of_lt hklt)).mp hprev j hjOne hjPrev
      · intro hall
        constructor
        · apply (ih (Nat.le_of_lt hklt)).mpr
          intro j hjOne hjPrev
          exact hall j hjOne (Nat.le_trans hjPrev (Nat.le_succ k))
        · exact hall (k + 1) (by omega) le_rfl

/-- Helper for Corollary 4.2: the success event is the event that the padded
run remains localized through its terminal horizon. -/
def successEvent
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X) : Set Ω :=
  {omega | activeAt attempt K omega}

/-- Helper for Corollary 4.2: the terminal success event of a stopped
attempt is measurable. -/
theorem measurableSet_successEvent
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X) : MeasurableSet (successEvent attempt) := by
  unfold successEvent
  exact measurableSet_activeAt attempt K

/-- Helper for Corollary 4.2: membership in the success event is equivalent to
all positive-index padded points lying in the localization set. -/
theorem mem_successEvent_iff_points_mem
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X) (omega : Ω) :
    omega ∈ successEvent attempt ↔
      ∀ j : ℕ, 1 ≤ j → j ≤ K → point attempt j omega ∈ X := by
  unfold successEvent
  exact activeAt_iff_points_mem attempt K omega le_rfl

/-- Helper for Corollary 4.2: success is equivalent to activity at every
pre-batch horizon below the terminal one. -/
theorem mem_successEvent_iff_all_active
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X) (omega : Ω) :
    omega ∈ successEvent attempt ↔
      ∀ j : ℕ, j ≤ K → activeAt attempt j omega := by
  constructor
  · intro hsuccess j hj
    unfold successEvent at hsuccess
    induction j with
    | zero => exact activeAt_zero attempt omega
    | succ j ih =>
        have hjlt : j < K := Nat.lt_of_succ_le hj
        rw [activeAt_succ_iff attempt ⟨j, hjlt⟩ omega]
        exact ⟨ih (Nat.le_of_lt hjlt),
          (mem_successEvent_iff_points_mem attempt omega).mp hsuccess (j + 1)
            (by omega) hj⟩
  · intro hall
    exact hall K le_rfl

/-- Helper for Corollary 4.2: success propagates activity backwards through
the whole finite pre-batch prefix. -/
theorem activeAt_of_mem_successEvent
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X) (omega : Ω) (hsuccess : omega ∈ successEvent attempt)
    (k : ℕ) (hk : k ≤ K) : activeAt attempt k omega :=
  (mem_successEvent_iff_all_active attempt omega).mp hsuccess k hk

/-- Helper for Corollary 4.2: the executed index set records exactly the
active in-horizon iterations, including the first iteration that exits only
after its active transition has been computed. -/
noncomputable def executedIndexSet
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
  confidence K X) (omega : Ω) : Finset ℕ :=
  (Finset.range K).filter (fun k => attempt.activeIndicator k omega = true)

/-- Helper for Corollary 4.2: membership in the executed index set exposes the
horizon bound and active indicator. -/
theorem mem_executedIndexSet_iff
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
  confidence K X) (omega : Ω) (k : ℕ) :
    k ∈ executedIndexSet attempt omega ↔ k < K ∧ activeAt attempt k omega := by
  unfold executedIndexSet
  simp only [Finset.mem_filter, Finset.mem_range, activeAt]

/-- Helper for Corollary 4.2: a successful stopped attempt has the full
initial active block as its executed index set. -/
theorem executedIndexSet_eq_range_of_mem_successEvent
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X) (omega : Ω)
    (hsuccess : omega ∈ successEvent attempt) :
    executedIndexSet attempt omega = Finset.range K := by
  classical
  have hall : ∀ j : ℕ, j ≤ K → activeAt attempt j omega :=
    (mem_successEvent_iff_all_active attempt omega).mp hsuccess
  ext k
  simp only [mem_executedIndexSet_iff, Finset.mem_range]
  constructor
  · exact And.left
  · intro hk
    exact ⟨hk, hall k (Nat.le_of_lt hk)⟩

/-- Helper for Corollary 4.2: the number of executed iterations is the
cardinality of the active in-horizon index set. -/
noncomputable def executedIterations
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X) (omega : Ω) : ℕ :=
  (executedIndexSet attempt omega).card

/-- Helper for Corollary 4.2: the executed iteration count is bounded by the
prescribed finite horizon. -/
theorem executedIterations_le
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X) (omega : Ω) :
    executedIterations attempt omega ≤ K := by
  classical
  unfold executedIterations executedIndexSet
  have hsub :
      (Finset.range K).filter
          (fun k : ℕ => attempt.activeIndicator k omega = true) ⊆
        Finset.range K :=
    Finset.filter_subset (p := fun k : ℕ =>
      attempt.activeIndicator k omega = true) (Finset.range K)
  simpa only [Finset.card_range] using Finset.card_le_card hsub

/-- Helper for Corollary 4.2: a successful stopped attempt executes every
scheduled transition. -/
theorem executedIterations_eq_of_mem_successEvent
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X) (omega : Ω)
    (hsuccess : omega ∈ successEvent attempt) :
    executedIterations attempt omega = K := by
  unfold executedIterations
  rw [executedIndexSet_eq_range_of_mem_successEvent attempt omega hsuccess]
  exact Finset.card_range K

/-- Helper for Corollary 4.2: the padded base step is the true canonical step
on active in-horizon iterations and zero otherwise. -/
noncomputable def baseStep
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X) (k : ℕ) (omega : Ω) : EuclideanSpace ℝ (Fin n) :=
  if hk : k < K then
    Sum.elim (fun _ : Unit ↦ 0)
      (fun s ↦ canonicalActiveBaseStepAt h oracle params Q B b k
        (s, attempt.batch k omega))
      (attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩ omega)
  else 0

/-- Helper for Corollary 4.2: on an active in-horizon state, the padded base
step is the canonical active base step. -/
theorem activeState_baseStep_eq_baseStep
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X) (k : ℕ) (omega : Ω) (hk : k < K)
    (a : ActivePreBatchState h params X)
    (ha : attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩ omega = Sum.inr a) :
    baseStep attempt k omega =
      canonicalActiveBaseStepAt h oracle params Q B b k
        (a, attempt.batch k omega) := by
  rw [baseStep, dif_pos hk, ha]
  rfl

/-- Helper for Corollary 4.2: every padded base-step coordinate is
measurable, including the absorbing zero branch after a stopped exit. -/
theorem measurable_baseStep
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X) (k : ℕ) : Measurable (attempt.baseStep k) := by
  by_cases hk : k < K
  · have hdef : attempt.baseStep k =
        (fun omega ↦
          paddedBaseStepTransition h oracle params Q B b k
            (attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩ omega,
              attempt.batch k omega)) := by
      funext omega
      unfold baseStep
      simp only [dif_pos hk, paddedBaseStepTransition]
      cases hstate : attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩ omega with
      | inl u => simp [MeasurableEquiv.sumProdDistrib]
      | inr a => simp [MeasurableEquiv.sumProdDistrib]
    rw [hdef]
    exact (measurable_paddedBaseStepTransition X
      attempt.region_condition k).comp
      ((attempt.measurable_state ⟨k, Nat.lt_succ_of_lt hk⟩).prodMk
        (measurable_batch attempt k))
  · have hdef : attempt.baseStep k = (fun _ : Ω ↦ 0) := by
      funext omega
      unfold baseStep
      simp only [dif_neg hk]
    rw [hdef]
    exact measurable_const

/-- Helper for Corollary 4.2: the padded raw estimate is formed on active
in-horizon iterations and is zero after stopping. -/
noncomputable def rawEstimate
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X) (k : ℕ) (omega : Ω) : EuclideanSpace ℝ (Fin n) :=
  if hk : k < K then
    Sum.elim (fun _ : Unit ↦ 0)
      (fun s ↦ canonicalRawEstimateAt oracle Q B b k s.1
        (attempt.batch k omega))
      (attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩ omega)
  else 0

/-- Helper for Corollary 4.2: on an active in-horizon state, the padded raw
estimate is the canonical raw transition for its fresh batch. -/
theorem activeState_rawEstimate_at
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X) (k : ℕ) (omega : Ω) (hk : k < K)
    (a : ActivePreBatchState h params X)
    (ha : attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩ omega = Sum.inr a) :
    rawEstimate attempt k omega =
      canonicalRawEstimateAt oracle Q B b k a.1 (attempt.batch k omega) := by
  rw [rawEstimate, dif_pos hk, ha]
  rfl

/-- Helper for Corollary 4.2: an active state's stored raw estimate is the
padded raw estimate from the preceding batch. -/
theorem activeState_rawEstimate_eq_rawEstimate
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X) (k : ℕ) (omega : Ω) (hk : k ≤ K)
    (a : ActivePreBatchState h params X)
    (ha : attempt.state ⟨k, Nat.lt_succ_iff.mpr hk⟩ omega = Sum.inr a) :
    a.1.2.2.2 = if k = 0 then 0 else rawEstimate attempt (k - 1) omega := by
  induction k generalizing a with
  | zero =>
      have hz := attempt.state_zero omega
      have haeq : initialActivePreBatchState attempt.initial_mem
          attempt.region_condition = a := Sum.inr.inj (hz.symm.trans ha)
      rw [← haeq, initialActivePreBatchState_rawEstimate]
      simp
  | succ k ih =>
      have hklt : k < K := Nat.lt_of_succ_le hk
      have ha' : attempt.state ⟨k + 1, Nat.lt_succ_iff.mpr hk⟩ omega = Sum.inr a := by
        simpa only [Fin.succ_mk] using ha
      obtain ⟨aPrev, hprev, hmem, hdata⟩ :=
        activeSuccessor_data attempt ⟨k, hklt⟩ omega a ha'
      have hprev' : attempt.state ⟨k, Nat.lt_succ_of_lt hklt⟩ omega =
          Sum.inr aPrev := by
        simpa only [Fin.castSucc_mk] using hprev
      rw [if_neg (Nat.succ_ne_zero k)]
      change a.1.2.2.2 = rawEstimate attempt k omega
      rw [hdata]
      rw [canonicalActiveNextDataAt_rawEstimate (h := h) (oracle := oracle)
        (params := params) (Q := Q) (B := B) (b := b) aPrev
        (attempt.batch k omega) k]
      rw [rawEstimate, dif_pos hklt, hprev']
      rfl

/-- Helper for Corollary 4.2: the projected estimate is the clipped padded raw
estimate. -/
noncomputable def gradientEstimate
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X) (k : ℕ) (omega : Ω) : EuclideanSpace ℝ (Fin n) :=
  SPIDER.clip h.gradientBound (attempt.rawEstimate k omega)

end StoppedAttempt

end LALM.Correction

end
