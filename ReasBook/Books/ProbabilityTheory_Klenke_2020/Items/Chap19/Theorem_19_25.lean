/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_30
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_42
import Books.ProbabilityTheory_Klenke_2020.Items.Chap19.Definition_19_11
import Books.ProbabilityTheory_Klenke_2020.Items.Chap19.Definition_19_23
import Books.ProbabilityTheory_Klenke_2020.Items.Chap19.Lemma_19_24
import Mathlib

open MeasureTheory
open scoped ENNReal symmDiff

noncomputable section

universe u v

namespace ProbabilityTheory

attribute [local instance] Classical.propDecidable

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]
variable {Ω : Type v} [MeasurableSpace Ω]
variable {p C : E → E → ℝ≥0∞}
variable {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E} {x₁ : E}
variable [IsRandomWalkWithWeights p C]
variable [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]

/- Layering for Theorem 19.25:
- `source-facing`: `escapeProbability`, recurrence of `x₁`, and the conductance/resistance
  criteria from the textbook statement.
- `core/canonical`: `conductance`, `effectiveConductanceToInfinity`, and the Chapter 17 recurrence
  predicate `IsRecurrentState`.
- `bridge/view`: the missing step is the limit comparison from Lemma 19.24 to the no-return event
  formula for `escapeProbability`. -/

/-- Helper for Theorem 19.25: in this item, the effective resistance to infinity is the reciprocal
of the effective conductance to infinity. -/
def effectiveResistanceToInfinity
    (C : E → E → ℝ≥0∞) (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (x : E) : ℝ≥0∞ :=
  (effectiveConductanceToInfinity C P X x)⁻¹

/-- Helper for Theorem 19.25: the positive-time reachable hull from `x` is the set of states
carrying positive singleton mass in some positive-time law of the walk. -/
private def positiveTimeReachable (p : E → E → ℝ≥0∞) (x : E) : Set E :=
  {y | ∃ n : ℕ, 0 < n ∧ 0 < ((discreteMatrixKernel p ^ n) x) ({y} : Set E)}

/-- Helper for Theorem 19.25: an `n`-step law started from `x₁` has only countably many states
with positive singleton mass. -/
private theorem positiveLawSupport_countable
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    [IsMarkovProcessRealization (fun m : ℕ ↦ discreteMatrixKernel p ^ m) P X]
    (x : E) (n : ℕ) :
    {y : E | 0 < ((discreteMatrixKernel p ^ n) x) ({y} : Set E)}.Countable := by
  let μ : Measure E := (discreteMatrixKernel p ^ n) x
  let hReal : IsMarkovProcessRealization (fun m : ℕ ↦ discreteMatrixKernel p ^ m) P X :=
    inferInstance
  letI : IsMarkovKernel ((fun m : ℕ ↦ discreteMatrixKernel p ^ m) n) :=
    hReal.semigroup.isMarkovKernel n
  have hμ_ne_top : μ Set.univ ≠ ⊤ := by
    have hμ_univ : μ Set.univ = 1 := by
      simpa [μ] using
        ((inferInstance : IsMarkovKernel ((fun m : ℕ ↦ discreteMatrixKernel p ^ m) n))
          .isProbabilityMeasure x).measure_univ
    simpa [hμ_univ]
  have hiUnion_singletons : (⋃ y : E, ({y} : Set E)) = Set.univ := by
    ext y
    simp
  have hμ_ne_top_iUnion : μ (⋃ y : E, ({y} : Set E)) ≠ ⊤ := by
    simpa [hiUnion_singletons] using hμ_ne_top
  -- Proof comment: every `n`-step law is a probability measure, so only countably many
  -- singletons can carry positive mass.
  simpa [μ] using
    (Measure.countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top μ
      (As_mble := fun y : E ↦ MeasurableSet.singleton y)
      (As_disj := fun y z hyz ↦ Set.disjoint_singleton.2 hyz)
      hμ_ne_top_iUnion)

/-- Helper for Theorem 19.25: an `n`-step law started from `x₁` has only countably many states
with positive singleton mass. -/
private theorem positiveTimeLawSupport_countable
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    [IsMarkovProcessRealization (fun m : ℕ ↦ discreteMatrixKernel p ^ m) P X]
    (x₁ : E) (n : ℕ) :
    {y : E | 0 < ((discreteMatrixKernel p ^ n) x₁) ({y} : Set E)}.Countable := by
  -- Proof comment: this is the arbitrary-start support lemma specialized to the distinguished
  -- start state `x₁`.
  simpa using positiveLawSupport_countable (p := p) P X x₁ n

/-- Helper for Theorem 19.25: the positive-time reachable hull from `x₁` is countable. -/
private theorem positiveTimeReachable_countable
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    [IsMarkovProcessRealization (fun m : ℕ ↦ discreteMatrixKernel p ^ m) P X]
    (x₁ : E) :
    (positiveTimeReachable p x₁).Countable := by
  have hsubset :
      positiveTimeReachable p x₁ ⊆
        ⋃ n : ℕ, {y : E | 0 < ((discreteMatrixKernel p ^ n) x₁) ({y} : Set E)} := by
    intro y hy
    rcases hy with ⟨n, -, hyn⟩
    exact Set.mem_iUnion.mpr ⟨n, hyn⟩
  -- Proof comment: positive-time reachability is the countable union of the singleton supports of
  -- the `n`-step laws.
  exact Set.Countable.mono hsubset <|
    Set.countable_iUnion fun n ↦ positiveTimeLawSupport_countable (p := p) P X x₁ n

/-- Helper for Theorem 19.25: adjoining the start state keeps the reachable hull countable. -/
private theorem positiveTimeReachableWithStart_countable
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    [IsMarkovProcessRealization (fun m : ℕ ↦ discreteMatrixKernel p ^ m) P X]
    (x₁ : E) :
    (insert x₁ (positiveTimeReachable p x₁)).Countable := by
  -- Proof comment: the reachable hull is already countable, and adding one distinguished state
  -- preserves countability.
  exact (positiveTimeReachable_countable (p := p) P X x₁).insert x₁

/-- Helper for Theorem 19.25: the reachable hull with the start state admits a monotone finite
exhaustion. -/
private def positiveTimeReachableExhaustion :
    (insert x₁ (positiveTimeReachable p x₁)).FiniteExhaustion :=
  (positiveTimeReachableWithStart_countable (p := p) P X x₁).finiteExhaustion

/-- Helper for Theorem 19.25: every finite subset of `insert x₁ (positiveTimeReachable p x₁)` is
eventually contained in one inserted exhaustion stage. -/
private theorem finiteSubset_insertReachable_eventually_subset_stage
    {K : Set E} (hKfin : K.Finite)
    (hKsub : K ⊆ insert x₁ (positiveTimeReachable p x₁)) :
    ∃ n : ℕ,
      K ⊆ insert x₁
        (positiveTimeReachableExhaustion (p := p) (P := P) (X := X) (x₁ := x₁) n) := by
  classical
  let L : Finset E := hKfin.toFinset
  have hstage :
      ∀ y ∈ K, ∃ n : ℕ,
        y ∈ positiveTimeReachableExhaustion (p := p) (P := P) (X := X) (x₁ := x₁) n := by
    intro y hyK
    have hyUnion :
        y ∈
          ⋃ n : ℕ,
            positiveTimeReachableExhaustion (p := p) (P := P) (X := X) (x₁ := x₁) n := by
      rw [(positiveTimeReachableExhaustion (p := p) (P := P) (X := X) (x₁ := x₁)).iUnion_eq]
      exact hKsub hyK
    exact Set.mem_iUnion.mp hyUnion
  let witness : E → ℕ := fun y ↦
    if hyK : y ∈ K then Nat.find (hstage y hyK) else 0
  let N : ℕ := L.sup witness
  refine ⟨N, ?_⟩
  intro y hyK
  have hyL : y ∈ L := by
    simpa [L, hKfin.mem_toFinset] using hyK
  have hw_eq : witness y = Nat.find (hstage y hyK) := by
    simp [witness, hyK]
  have hw_le : witness y ≤ N := Finset.le_sup hyL
  have hyStage :
      y ∈ positiveTimeReachableExhaustion (p := p) (P := P) (X := X) (x₁ := x₁) (witness y) := by
    rw [hw_eq]
    exact Nat.find_spec (hstage y hyK)
  -- Proof comment: once every point in the finite set is assigned a stage, the finite supremum
  -- of those indices places the whole set in one common inserted stage.
  exact Or.inr <|
    (positiveTimeReachableExhaustion (p := p) (P := P) (X := X) (x₁ := x₁)).mono hw_le hyStage

/-- Helper for Theorem 19.25: the conductance at any state is nonzero because each transition row
is stochastic. -/
private theorem conductance_ne_zero_at
    (p C : E → E → ℝ≥0∞) [IsRandomWalkWithWeights p C] (x : E) :
    conductance C x ≠ 0 := by
  let hWalk : IsRandomWalkWithWeights p C := inferInstance
  intro hzero
  have hC_zero : ∀ y : E, C x y = 0 := by
    intro y
    exact (ENNReal.tsum_eq_zero.mp hzero) y
  have hp_zero : ∀ y : E, p x y = 0 := by
    intro y
    rw [hWalk.transition_eq, hC_zero y]
    simp
  have hsum_zero : ∑' y : E, p x y = 0 := by
    simp [hp_zero]
  have hstochastic := hWalk.isStochastic x
  -- Proof comment: if the conductance vanished, every transition mass out of `x` would vanish,
  -- contradicting that the stochastic row sum is `1`.
  rw [hsum_zero] at hstochastic
  simp at hstochastic

/-- Helper for Theorem 19.25: the weighted random-walk kernel satisfies singleton detailed balance
at one step. -/
private theorem oneStepSingletonBalance (x y : E) :
    conductance C x * ((discreteMatrixKernel p) x ({y} : Set E)) =
      conductance C y * ((discreteMatrixKernel p) y ({x} : Set E)) := by
  let hWalk : IsRandomWalkWithWeights p C := inferInstance
  have hx_ne_zero : conductance C x ≠ 0 := conductance_ne_zero_at (p := p) (C := C) x
  have hy_ne_zero : conductance C y ≠ 0 := conductance_ne_zero_at (p := p) (C := C) y
  have hx_ne_top : conductance C x ≠ ∞ := (hWalk.conductance_lt_top x).ne
  have hy_ne_top : conductance C y ≠ ∞ := (hWalk.conductance_lt_top y).ne
  -- Proof comment: both sides reduce to the same edge conductance `C x y` by the defining
  -- normalization formula and symmetry of the weight family.
  calc
    conductance C x * ((discreteMatrixKernel p) x ({y} : Set E))
        = conductance C x * p x y := by
            rw [discreteMatrixKernel_apply_singleton]
    _ = conductance C x * (C x y / conductance C x) := by rw [hWalk.transition_eq]
    _ = C x y := by
          rw [ENNReal.mul_div_cancel'
            (fun hzero ↦ False.elim (hx_ne_zero hzero))
            (fun htop ↦ False.elim (hx_ne_top htop))]
    _ = C y x := hWalk.symmetric x y
    _ = conductance C y * (C y x / conductance C y) := by
          rw [ENNReal.mul_div_cancel'
            (fun hzero ↦ False.elim (hy_ne_zero hzero))
            (fun htop ↦ False.elim (hy_ne_top htop))]
    _ = conductance C y * p y x := by rw [hWalk.transition_eq]
    _ = conductance C y * ((discreteMatrixKernel p) y ({x} : Set E)) := by
          rw [discreteMatrixKernel_apply_singleton]

/-- Helper for Theorem 19.25: positive singleton masses compose across kernel powers. -/
private theorem positiveSingletonComp
    {κ : Kernel E E} {m n : ℕ} {x y z : E}
    (hxy : 0 < (κ ^ m) x ({y} : Set E))
    (hyz : 0 < (κ ^ n) y ({z} : Set E)) :
    0 < (κ ^ (m + n)) x ({z} : Set E) := by
  -- Proof comment: expand the Chapman-Kolmogorov integral and keep the positive contribution from
  -- the intermediate singleton `{y}`.
  rw [Kernel.pow_add_apply_eq_lintegral κ m n x (measurableSet_singleton z)]
  have hsingleton :
      0 < ∫⁻ b in ({y} : Set E), (κ ^ n) b ({z} : Set E) ∂((κ ^ m) x) := by
    rw [MeasureTheory.lintegral_singleton]
    exact ENNReal.mul_pos hyz.ne' hxy.ne'
  have hmono :
      ∫⁻ b in ({y} : Set E), (κ ^ n) b ({z} : Set E) ∂((κ ^ m) x) ≤
        ∫⁻ b in Set.univ, (κ ^ n) b ({z} : Set E) ∂((κ ^ m) x) :=
    MeasureTheory.lintegral_mono_set (show ({y} : Set E) ⊆ Set.univ from Set.subset_univ _)
  exact lt_of_lt_of_le hsingleton (by simpa [Measure.restrict_univ] using hmono)

/-- Helper for Theorem 19.25: if every singleton in `A` has zero one-step mass from `x`, then the
whole one-step row mass of `A` vanishes. -/
private theorem discreteMatrixKernel_apply_eq_zero_of_singleton_zero
    (x : E) {A : Set E}
    (hA : ∀ y ∈ A, (discreteMatrixKernel p) x ({y} : Set E) = 0) :
    (discreteMatrixKernel p) x A = 0 := by
  rw [discreteMatrixKernel_apply, Measure.sum_apply _ (DiscreteMeasurableSpace.forall_measurableSet _)]
  refine ENNReal.tsum_eq_zero.mpr ?_
  intro y
  by_cases hyA : y ∈ A
  · have hy_zero : p x y = 0 := by
      have hy_mass_zero : (discreteMatrixKernel p) x ({y} : Set E) = 0 := hA y hyA
      rw [discreteMatrixKernel_apply_singleton] at hy_mass_zero
      exact hy_mass_zero
    simp [hyA, hy_zero]
  · simp [hyA]

/-- Helper for Theorem 19.25: if every singleton in `A` has zero `n`-step mass from `x`, then the
whole `n`-step law of `A` vanishes. -/
private theorem kernelPow_apply_eq_zero_of_singleton_zero
    (n : ℕ) (x : E) {A : Set E}
    (hA : ∀ y ∈ A, ((discreteMatrixKernel p ^ n) x) ({y} : Set E) = 0) :
    ((discreteMatrixKernel p ^ n) x) A = 0 := by
  induction n generalizing x with
  | zero =>
      by_cases hxA : x ∈ A
      · have hx_zero : ((discreteMatrixKernel p ^ 0) x) ({x} : Set E) = 0 := hA x hxA
        have hx_one : ((discreteMatrixKernel p ^ 0) x) ({x} : Set E) = 1 := by
          change (Measure.dirac x) ({x} : Set E) = 1
          rw [Measure.dirac_apply' _ (measurableSet_singleton x)]
          simp
        exact False.elim (zero_ne_one (hx_zero.symm.trans hx_one))
      · -- Proof comment: at time `0` the kernel row is the Dirac mass at `x`, so avoiding `x`
        -- inside `A` already forces the whole set mass to vanish.
        change (Measure.dirac x) A = 0
        rw [Measure.dirac_apply' _ (DiscreteMeasurableSpace.forall_measurableSet _)]
        simp [hxA]
  | succ n ih =>
      rw [show n + 1 = 1 + n by simp [Nat.add_comm]]
      rw [Kernel.pow_add_apply_eq_lintegral (discreteMatrixKernel p) 1 n x
        (DiscreteMeasurableSpace.forall_measurableSet _)]
      rw [pow_one, discreteMatrixKernel_apply, lintegral_sum_measure]
      refine ENNReal.tsum_eq_zero.mpr ?_
      intro y
      rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
      by_cases hxy : p x y = 0
      · simp [hxy]
      · have hyA :
            ∀ z ∈ A, ((discreteMatrixKernel p ^ n) y) ({z} : Set E) = 0 := by
          intro z hzA
          by_contra hzy
          have hxy_pos : 0 < ((discreteMatrixKernel p ^ 1) x) ({y} : Set E) := by
            refine bot_lt_iff_ne_bot.mpr ?_
            rw [pow_one, discreteMatrixKernel_apply_singleton]
            exact hxy
          have hzy_pos : 0 < ((discreteMatrixKernel p ^ n) y) ({z} : Set E) :=
            bot_lt_iff_ne_bot.mpr hzy
          have hcomp :
              0 < ((discreteMatrixKernel p ^ (1 + n)) x) ({z} : Set E) :=
            positiveSingletonComp
              (κ := discreteMatrixKernel p) (m := 1) (n := n) hxy_pos hzy_pos
          have hz_zero :
              ((discreteMatrixKernel p ^ (Nat.succ n)) x) ({z} : Set E) = 0 :=
            hA z hzA
          exact hcomp.ne' (by simpa [Nat.add_comm] using hz_zero)
        have hy_zero : ((discreteMatrixKernel p ^ n) y) A = 0 :=
          ih y hyA
        -- Proof comment: a positive first step from `x` to `y` would transport any positive
        -- `n`-step mass from `y` into `A` to a positive `(n + 1)`-step mass from `x`, so the
        -- induction hypothesis annihilates every row that contributes to the Chapman--Kolmogorov
        -- series.
        simp [hxy, hy_zero]

/-- Helper for Theorem 19.25: positive-time marginals assign zero mass to sets outside the
positive-time reachable hull from `x₁`. -/
private theorem positiveTimeLaw_null_outsideReachable
    {A : Set E} {n : ℕ} (hn : 0 < n)
    (hA : A ⊆ (positiveTimeReachable p x₁)ᶜ) :
    (P x₁ : Measure Ω) {ω | X n ω ∈ A} = 0 := by
  let hReal : IsMarkovProcessRealization (fun m : ℕ ↦ discreteMatrixKernel p ^ m) P X :=
    inferInstance
  have hsingle_zero :
      ∀ y ∈ A, ((discreteMatrixKernel p ^ n) x₁) ({y} : Set E) = 0 := by
    intro y hyA
    by_cases hyn : 0 < ((discreteMatrixKernel p ^ n) x₁) ({y} : Set E)
    · have hyReach : y ∈ positiveTimeReachable p x₁ := ⟨n, hn, hyn⟩
      exact False.elim ((hA hyA) hyReach)
    · exact bot_unique (not_lt.mp hyn)
  have hpreimage :
      {ω | X n ω ∈ A} = X n ⁻¹' A := by
    ext ω
    simp
  -- Proof comment: rewrite the time-`n` marginal through the realization law and then kill the
  -- target set using the singleton-zero bridge for the `n`-step kernel row.
  rw [hpreimage]
  rw [← Measure.map_apply (hReal.measurable_process n) (DiscreteMeasurableSpace.forall_measurableSet _)]
  rw [hReal.transition_eq x₁ n]
  exact kernelPow_apply_eq_zero_of_singleton_zero (p := p) n x₁ hsingle_zero

/-- Helper for Theorem 19.25: the escape-to-set probability only depends on the intersection of
the target with the positive-time reachable hull from `x₁`. -/
private theorem escapeToSetProbability_eq_inter_positiveTimeReachable
    (A : Set E) :
    escapeToSetProbability P X x₁ A =
      escapeToSetProbability P X x₁ (A ∩ positiveTimeReachable p x₁) := by
  let Reach : Set E := positiveTimeReachable p x₁
  let μ : Measure Ω := P x₁
  let EA : Set Ω := {ω |
    ∃ n : ℕ, 0 < n ∧ X n ω ∈ A ∧
      ∀ m : ℕ, 0 < m → m ≤ n → X m ω ≠ x₁}
  let ER : Set Ω := {ω |
    ∃ n : ℕ, 0 < n ∧ X n ω ∈ A ∩ Reach ∧
      ∀ m : ℕ, 0 < m → m ≤ n → X m ω ≠ x₁}
  let Bad : Set Ω := ⋃ n : ℕ, {ω | 0 < n ∧ X n ω ∈ A \ Reach}
  rw [escapeToSetProbability_def, escapeToSetProbability_def]
  change μ EA = μ ER
  have hER_subset : ER ⊆ EA := by
    intro ω hω
    rcases hω with ⟨n, hn, hnA, hnoReturn⟩
    exact ⟨n, hn, hnA.1, hnoReturn⟩
  have hEA_subset : EA ⊆ ER ∪ Bad := by
    intro ω hω
    rcases hω with ⟨n, hn, hnA, hnoReturn⟩
    by_cases hReach : X n ω ∈ Reach
    · exact Or.inl ⟨n, hn, ⟨hnA, hReach⟩, hnoReturn⟩
    · exact Or.inr <| Set.mem_iUnion.mpr ⟨n, ⟨hn, hnA, hReach⟩⟩
  have hBad_zero : μ Bad = 0 := by
    unfold Bad
    refine measure_iUnion_null ?_
    intro n
    by_cases hn : 0 < n
    · have hnull :
          μ {ω | X n ω ∈ A \ Reach} = 0 :=
        positiveTimeLaw_null_outsideReachable (p := p) (P := P) (X := X) (x₁ := x₁)
          (A := A \ Reach) hn (by
            intro y hy
            exact hy.2)
      simpa [μ, hn, Set.mem_diff, Reach] using hnull
    · simp [μ, hn]
  refine le_antisymm ?_ (measure_mono hER_subset)
  calc
    μ EA ≤ μ (ER ∪ Bad) := measure_mono hEA_subset
    _ ≤ μ ER + μ Bad := measure_union_le _ _
    _ = μ ER := by simp [hBad_zero]

/-- Helper for Theorem 19.25: `effectiveConductanceToInfinity` is the conductance factor times the
infimum over complements of the inserted reachable-hull exhaustion stages. -/
private theorem effectiveConductanceToInfinity_eq_iInf_reachableExhaustion :
    effectiveConductanceToInfinity C P X x₁ =
      conductance C x₁ * ⨅ n : ℕ,
        escapeToSetProbability P X x₁
          ((insert x₁
              (positiveTimeReachableExhaustion (p := p) (P := P) (X := X) (x₁ := x₁) n))ᶜ) := by
  let Reach : Set E := positiveTimeReachable p x₁
  let A₀ : ℕ → Set E := fun n ↦
    (insert x₁
      (positiveTimeReachableExhaustion (p := p) (P := P) (X := X) (x₁ := x₁) n))ᶜ
  rw [effectiveConductanceToInfinity_def]
  congr 1
  refine le_antisymm ?_ ?_
  · refine le_iInf ?_
    intro n
    refine sInf_le ?_
    refine ⟨A₀ n, ?_, ?_, rfl⟩
    · dsimp [A₀]
      simpa using
        (Set.Finite.insert x₁
          ((positiveTimeReachableExhaustion (p := p) (P := P) (X := X) (x₁ := x₁)).finite n))
    · dsimp [A₀]
      simp
  · refine le_sInf ?_
    rintro r ⟨B, hBfin, hx₁B, rfl⟩
    let K : Set E := insert x₁ (Reach \ B)
    have hKfin : K.Finite := by
      refine Set.Finite.insert x₁ ?_
      exact hBfin.subset fun y hy ↦ hy.2
    have hKsub : K ⊆ insert x₁ Reach := by
      intro y hy
      rcases hy with rfl | hy
      · exact Set.mem_insert _ _
      · exact Or.inr hy.1
    obtain ⟨n, hnK⟩ :=
      finiteSubset_insertReachable_eventually_subset_stage
        (p := p) (P := P) (X := X) (x₁ := x₁) hKfin hKsub
    have hstage_subset : A₀ n ∩ Reach ⊆ B ∩ Reach := by
      intro y hy
      have hyNotStage :
          y ∉ insert x₁
            (positiveTimeReachableExhaustion (p := p) (P := P) (X := X) (x₁ := x₁) n) :=
        hy.1
      have hyReach : y ∈ Reach := hy.2
      have hyB : y ∈ B := by
        by_contra hyB
        have hyK : y ∈ K := by
          right
          exact ⟨hyReach, hyB⟩
        exact hyNotStage (hnK hyK)
      exact ⟨hyB, hyReach⟩
    -- Proof comment: after discarding unreachable targets, every admissible cofinite set dominates
    -- one complement of the inserted reachable exhaustion, so the cofinite infimum is an `iInf`.
    calc
      ⨅ n : ℕ, escapeToSetProbability P X x₁ (A₀ n)
        ≤ escapeToSetProbability P X x₁ (A₀ n) := iInf_le _ n
      _ = escapeToSetProbability P X x₁ (A₀ n ∩ Reach) :=
          escapeToSetProbability_eq_inter_positiveTimeReachable
            (p := p) (P := P) (X := X) (x₁ := x₁) (A := A₀ n)
      _ ≤ escapeToSetProbability P X x₁ (B ∩ Reach) :=
          escapeToSetProbability_mono P X x₁ hstage_subset
      _ = escapeToSetProbability P X x₁ B := by
          symm
          exact escapeToSetProbability_eq_inter_positiveTimeReachable
            (p := p) (P := P) (X := X) (x₁ := x₁) (A := B)

/-- Helper for Theorem 19.25: the positive-time reachable hull from `x₁` is forward-closed under
positive one-step transitions. -/
private theorem positiveTimeReachable_closed_under_oneStep
    {y z : E} (hy : y ∈ positiveTimeReachable p x₁)
    (hyz : 0 < (discreteMatrixKernel p) y ({z} : Set E)) :
    z ∈ positiveTimeReachable p x₁ := by
  rcases hy with ⟨n, hn_pos, hxy⟩
  -- Proof comment: append the positive one-step transition `y ↝ z` to the existing positive path
  -- from `x₁` to `y`.
  refine ⟨n + 1, Nat.succ_pos _, ?_⟩
  simpa [pow_one, Nat.add_comm] using
    positiveSingletonComp (κ := discreteMatrixKernel p) (m := n) (n := 1) hxy
      (by simpa [pow_one] using hyz)

/-- Helper for Theorem 19.25: for a fixed target state `y`, only countably many states can jump
to `y` in one step. -/
private theorem positiveOneStepReverse
    {C : E → E → ℝ≥0∞} [IsRandomWalkWithWeights p C]
    {x y : E}
    (hxy : 0 < (discreteMatrixKernel p) x ({y} : Set E)) :
    0 < (discreteMatrixKernel p) y ({x} : Set E) := by
  rw [discreteMatrixKernel_apply_singleton] at hxy
  have hbalance := oneStepSingletonBalance (p := p) (C := C) x y
  rw [discreteMatrixKernel_apply_singleton, discreteMatrixKernel_apply_singleton] at hbalance
  have hleft_pos :
      0 < conductance C x * p x y := by
    -- Proof comment: the detailed-balance identity has a strictly positive left-hand side because
    -- both the conductance and the forward singleton mass are positive.
    exact ENNReal.mul_pos (conductance_ne_zero_at (p := p) (C := C) x) hxy.ne'
  by_contra hyx
  rw [discreteMatrixKernel_apply_singleton] at hyx
  have hyx_zero : p y x = 0 := bot_unique (not_lt.mp hyx)
  have hleft_zero :
      conductance C x * p x y = 0 := by
    simpa [hyx_zero] using hbalance
  exact hleft_pos.ne' hleft_zero

/-- Helper for Theorem 19.25: for a fixed target state `y`, only countably many states can jump
to `y` in one step. -/
private theorem oneStepPredecessor_countable
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    [IsMarkovProcessRealization (fun m : ℕ ↦ discreteMatrixKernel p ^ m) P X]
    {C : E → E → ℝ≥0∞} [IsRandomWalkWithWeights p C] (y : E) :
    {z : E | 0 < (discreteMatrixKernel p) z ({y} : Set E)}.Countable := by
  have hsubset :
      {z : E | 0 < (discreteMatrixKernel p) z ({y} : Set E)} ⊆
        {z : E | 0 < (discreteMatrixKernel p) y ({z} : Set E)} := by
    intro z hz
    exact positiveOneStepReverse (p := p) (C := C) hz
  -- Proof comment: reversibility turns every positive predecessor of `y` into a positive
  -- successor from `y`, and one-step laws have countable positive support.
  exact Set.Countable.mono hsubset <|
    by simpa [pow_one] using positiveLawSupport_countable (p := p) P X y 1

/-- Helper for Theorem 19.25: a positive `(n + 1)`-step singleton mass factors through an
intermediate state carrying both positive `n`-step mass from the start and a positive final
one-step jump to the target. -/
private theorem existsIntermediate_of_positivePowSingletonMass
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    [IsMarkovProcessRealization (fun m : ℕ ↦ discreteMatrixKernel p ^ m) P X]
    {C : E → E → ℝ≥0∞} [IsRandomWalkWithWeights p C]
    {n : ℕ} {x y : E}
    (hxy : 0 < ((discreteMatrixKernel p ^ (n + 1)) x) ({y} : Set E)) :
    ∃ z : E, 0 < ((discreteMatrixKernel p ^ n) x) ({z} : Set E) ∧
      0 < (discreteMatrixKernel p) z ({y} : Set E) := by
  let S : Set E := {z : E | 0 < (discreteMatrixKernel p) z ({y} : Set E)}
  let μ : Measure E := ((discreteMatrixKernel p ^ n) x)
  let f : E → ℝ≥0∞ := fun z ↦ (discreteMatrixKernel p) z ({y} : Set E)
  have hS_countable : S.Countable :=
    oneStepPredecessor_countable (p := p) P X (C := C) y
  have hS_indicator : S.indicator f = f := by
    funext z
    by_cases hz : z ∈ S
    · simp [S, f]
    · simp [S, f]
  rw [Kernel.pow_succ_apply_eq_lintegral (discreteMatrixKernel p) n x (measurableSet_singleton y)] at hxy
  have hIntegral_pos :
      0 < ∫⁻ z in S, f z ∂ μ := by
    have hAll_pos : 0 < ∫⁻ z, f z ∂ μ := by
      simpa [μ, f] using hxy
    -- Proof comment: outside the predecessor set `S`, the one-step singleton mass to `y`
    -- vanishes, so the positive integral is already concentrated on `S`.
    have hIntegral_eq :
        ∫⁻ z in S, f z ∂ μ = ∫⁻ z, f z ∂ μ := by
      rw [← MeasureTheory.lintegral_indicator
        (DiscreteMeasurableSpace.forall_measurableSet S), hS_indicator]
    rw [hIntegral_eq]
    exact hAll_pos
  have htsum_pos :
      0 < ∑' z : S, f z * μ ({(z : E)} : Set E) := by
    rw [MeasureTheory.lintegral_countable (μ := μ) f hS_countable] at hIntegral_pos
    simpa [f, μ, mul_comm] using hIntegral_pos
  by_contra hmid
  have hterm_zero :
      ∀ z : S, f z * μ ({(z : E)} : Set E) = 0 := by
    intro z
    have hz_pos : 0 < f z := z.2
    have hμ_not_pos : ¬ 0 < μ ({(z : E)} : Set E) := by
      intro hμ_pos
      exact hmid ⟨z, by simpa [μ] using hμ_pos, by simpa [f] using hz_pos⟩
    have hμ_zero : μ ({(z : E)} : Set E) = 0 := bot_unique (not_lt.mp hμ_not_pos)
    simp [f, μ, hμ_zero]
  have htsum_zero :
      ∑' z : S, f z * μ ({(z : E)} : Set E) = 0 :=
    ENNReal.tsum_eq_zero.mpr hterm_zero
  exact htsum_pos.ne' htsum_zero

/-- Helper for Theorem 19.25: a positive `n`-step singleton mass can be reversed to a positive
`n`-step singleton mass in the opposite direction. -/
private theorem positivePowSingletonMass_reverse
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    [IsMarkovProcessRealization (fun m : ℕ ↦ discreteMatrixKernel p ^ m) P X]
    {C : E → E → ℝ≥0∞} [IsRandomWalkWithWeights p C]
    {n : ℕ} {x y : E}
    (hn : 0 < n)
    (hxy : 0 < ((discreteMatrixKernel p ^ n) x) ({y} : Set E)) :
    0 < ((discreteMatrixKernel p ^ n) y) ({x} : Set E) := by
  induction n generalizing x y with
  | zero =>
      cases Nat.not_lt_zero _ hn
  | succ n ih =>
      cases n with
      | zero =>
          -- Proof comment: at one step, the reversibility bridge is exactly
          -- `positiveOneStepReverse`.
          have hxy' : 0 < (discreteMatrixKernel p) x ({y} : Set E) := by
            simpa [pow_one] using hxy
          have hyx' : 0 < (discreteMatrixKernel p) y ({x} : Set E) :=
            positiveOneStepReverse (p := p) (C := C) hxy'
          simpa [pow_one] using hyx'
      | succ n =>
          obtain ⟨z, hxz, hzy⟩ :=
            existsIntermediate_of_positivePowSingletonMass
              (p := p) P X (C := C) (n := n + 1) (x := x) (y := y) hxy
          have hyz : 0 < (discreteMatrixKernel p) y ({z} : Set E) :=
            positiveOneStepReverse (p := p) (C := C) hzy
          have hyz' : 0 < ((discreteMatrixKernel p ^ 1) y) ({z} : Set E) := by
            simpa [pow_one] using hyz
          have hzx : 0 < ((discreteMatrixKernel p ^ (n + 1)) z) ({x} : Set E) :=
            ih (Nat.succ_pos _) hxz
          -- Proof comment: reverse the last step and the initial `(n + 1)`-step prefix
          -- separately, then compose them into a positive path from `y` back to `x`.
          have hcomp :
              0 < ((discreteMatrixKernel p ^ (1 + (n + 1))) y) ({x} : Set E) :=
            positiveSingletonComp
              (κ := discreteMatrixKernel p) (m := 1) (n := n + 1) hyz' hzx
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcomp

/-- Helper for Theorem 19.25: every positive-time reachable state returns to `x₁` with positive
mass at some positive deterministic time. -/
private theorem positiveTimeReachable_has_positiveReturnMass
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    [IsMarkovProcessRealization (fun m : ℕ ↦ discreteMatrixKernel p ^ m) P X]
    {C : E → E → ℝ≥0∞} [IsRandomWalkWithWeights p C]
    {y : E} (hy : y ∈ positiveTimeReachable p x₁) :
    ∃ m : ℕ, 0 < m ∧ 0 < ((discreteMatrixKernel p ^ m) y) ({x₁} : Set E) := by
  rcases hy with ⟨m, hm_pos, hmass⟩
  -- Proof comment: the reachable witness already provides a positive path from `x₁` to `y`;
  -- reversing that path gives the desired deterministic return mass.
  exact ⟨m, hm_pos,
    positivePowSingletonMass_reverse
      (p := p) P X (C := C) hm_pos hmass⟩

/-- Helper for Theorem 19.25: finitely many positive return witnesses admit one common time bound
and one uniform positive lower mass bound. -/
private theorem finiteReturnWitness_uniformization
    {C : E → E → ℝ≥0∞} [IsRandomWalkWithWeights p C]
    (L : Finset E)
    (hL : ∀ y ∈ L, ∃ m : ℕ, 0 < m ∧ 0 < ((discreteMatrixKernel p ^ m) y) ({x₁} : Set E)) :
    ∃ N : ℕ, 0 < N ∧ ∃ δ : ℝ≥0∞, 0 < δ ∧
      ∀ y ∈ L,
        ∃ m : ℕ, 0 < m ∧ m ≤ N ∧ δ ≤ ((discreteMatrixKernel p ^ m) y) ({x₁} : Set E) := by
  classical
  by_cases hLempty : L = ∅
  · refine ⟨1, by simp, 1, by simp, ?_⟩
    intro y hy
    simpa [hLempty] using hy
  · have hLne : L.Nonempty := Finset.nonempty_iff_ne_empty.mpr hLempty
    choose witnessTime hwitnessTime_pos hwitnessMass_pos using hL
    let time : E → ℕ := fun y ↦ if hy : y ∈ L then witnessTime y hy else 1
    let mass : E → ℝ≥0∞ := fun y ↦
      if hy : y ∈ L then ((discreteMatrixKernel p ^ time y) y) ({x₁} : Set E) else 1
    let N : ℕ := L.sup time
    have hMassImage_nonempty : (L.image mass).Nonempty := by
      rcases hLne with ⟨y, hy⟩
      exact ⟨mass y, Finset.mem_image.mpr ⟨y, hy, rfl⟩⟩
    let δ : ℝ≥0∞ := (L.image mass).min' hMassImage_nonempty
    have hδ_pos : 0 < δ := by
      have hδ_mem : δ ∈ L.image mass := Finset.min'_mem _ hMassImage_nonempty
      rcases Finset.mem_image.mp hδ_mem with ⟨y, hy, hyδ⟩
      have hyMass : 0 < mass y := by
        simpa [mass, time, hy] using hwitnessMass_pos y hy
      simpa [δ, hyδ] using hyMass
    refine ⟨N, ?_, δ, hδ_pos, ?_⟩
    · rcases hLne with ⟨y, hy⟩
      have hyTime : 0 < time y := by
        simpa [time, hy] using hwitnessTime_pos y hy
      exact lt_of_lt_of_le hyTime (Finset.le_sup hy)
    · intro y hy
      refine ⟨time y, ?_, Finset.le_sup hy, ?_⟩
      · simpa [time, hy] using hwitnessTime_pos y hy
      · have hyMass_mem : mass y ∈ L.image mass := Finset.mem_image.mpr ⟨y, hy, rfl⟩
        simpa [δ, mass, time, hy] using
          (Finset.min'_le (L.image mass) (mass y) hyMass_mem)

/-- Helper for Theorem 19.25: a finite reachable hull admits one common return window and one
uniform positive lower bound for deterministic returns to `x₁`. -/
private theorem finiteReachableHull_uniformReturnData
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    [IsMarkovProcessRealization (fun m : ℕ ↦ discreteMatrixKernel p ^ m) P X]
    {C : E → E → ℝ≥0∞} [IsRandomWalkWithWeights p C]
    {K : Set E} (hKfin : K.Finite) (hx₁K : x₁ ∈ K)
    (hKsub : K ⊆ insert x₁ (positiveTimeReachable p x₁)) :
    ∃ N : ℕ, 0 < N ∧ ∃ δ : ℝ≥0∞, 0 < δ ∧
      ∀ y ∈ K, y ≠ x₁ →
        ∃ m : ℕ, 0 < m ∧ m ≤ N ∧ δ ≤ ((discreteMatrixKernel p ^ m) y) ({x₁} : Set E) := by
  classical
  let L : Finset E := hKfin.toFinset.erase x₁
  have hL :
      ∀ y ∈ L, ∃ m : ℕ, 0 < m ∧ 0 < ((discreteMatrixKernel p ^ m) y) ({x₁} : Set E) := by
    intro y hy
    have hyK : y ∈ K := by
      exact hKfin.mem_toFinset.mp (Finset.mem_erase.mp hy).2
    have hy_ne : y ≠ x₁ := (Finset.mem_erase.mp hy).1
    have hyReach : y ∈ positiveTimeReachable p x₁ := by
      rcases hKsub hyK with rfl | hyReach
      · exact False.elim (hy_ne rfl)
      · exact hyReach
    -- Proof comment: every non-start state in the finite reachable hull already has a positive
    -- return witness by reversing one positive path from `x₁`.
    exact positiveTimeReachable_has_positiveReturnMass
      (p := p) P X (x₁ := x₁) (C := C) hyReach
  obtain ⟨N, hN, δ, hδ, huniform⟩ :=
    finiteReturnWitness_uniformization (p := p) (x₁ := x₁) (C := C) L hL
  refine ⟨N, hN, δ, hδ, ?_⟩
  intro y hyK hy_ne
  have hyL : y ∈ L := by
    refine Finset.mem_erase.mpr ?_
    exact ⟨hy_ne, hKfin.mem_toFinset.mpr hyK⟩
  -- Proof comment: the finset-level package on `K \\ {x₁}` is exactly the set-level uniform return
  -- data needed later in the finite-hull trap argument.
  exact huniform y hyL

/-- Helper for Theorem 19.25: the generated history filtration is monotone along natural times. -/
private theorem generatedFiltrationSpace_monoLocal
    (Y : ℕ → Ω → E) {s t : ℕ} (hst : s ≤ t) :
    generatedFiltrationSpace Y s ≤ generatedFiltrationSpace Y t := by
  -- Proof comment: every generator used up to time `s` also appears in the larger history up to
  -- time `t`.
  refine iSup₂_le fun r hr ↦ ?_
  exact le_iSup_of_le r <| le_iSup_of_le (hr.trans hst) le_rfl

/-- Helper for Theorem 19.25: every generated history filtration is a sub-σ-algebra of the
ambient measurable space. -/
private theorem generatedFiltrationSpace_le_ambientLocal
    (P : E → ProbabilityMeasure Ω)
    [IsMarkovProcessRealization (fun m : ℕ ↦ discreteMatrixKernel p ^ m) P X]
    (n : ℕ) :
    generatedFiltrationSpace X n ≤ ‹MeasurableSpace Ω› := by
  let hReal : IsMarkovProcessRealization (fun m : ℕ ↦ discreteMatrixKernel p ^ m) P X :=
    inferInstance
  -- Proof comment: every coordinate used in the generated history is ambient measurable under the
  -- realization hypothesis, so the generated σ-algebra sits below the ambient one.
  refine iSup₂_le fun k hk ↦ ?_
  exact (hReal.measurable_process k).comap_le

/-- Helper for Theorem 19.25: the shifted finite-hull survival event records that every positive
time up to the horizon `1 + k * N` stays inside `K` and avoids the start state `x₁`. -/
private def shiftedStayInFiniteReachableHull (K : Set E) (N k : ℕ) : Set Ω :=
  {ω | ∀ m : ℕ, 0 < m → m ≤ 1 + k * N → X m ω ∈ K ∧ X m ω ≠ x₁}

/-- Helper for Theorem 19.25: the shifted finite-hull survival event is measurable with respect to
the history up to its terminal time. -/
private theorem shiftedStayInFiniteReachableHull_measurable
    (P : E → ProbabilityMeasure Ω)
    [IsMarkovProcessRealization (fun m : ℕ ↦ discreteMatrixKernel p ^ m) P X]
    (K : Set E) (N k : ℕ) :
    MeasurableSet[generatedFiltrationSpace X (1 + k * N)]
      (shiftedStayInFiniteReachableHull (X := X) (x₁ := x₁) K N k) := by
  let T : ℕ := 1 + k * N
  have hEq :
      shiftedStayInFiniteReachableHull (X := X) (x₁ := x₁) K N k =
        ⋂ m : ℕ, ⋂ (_hmPos : 0 < m), ⋂ (_hmLe : m ≤ T),
          X m ⁻¹' (K ∩ ({x₁} : Set E)ᶜ) := by
    ext ω
    simp [shiftedStayInFiniteReachableHull, T, Set.mem_inter_iff]
  rw [hEq]
  refine MeasurableSet.iInter fun m ↦ ?_
  refine MeasurableSet.iInter fun hmPos ↦ ?_
  refine MeasurableSet.iInter fun hmLe ↦ ?_
  letI : MeasurableSpace Ω := generatedFiltrationSpace X T
  have hXm : Measurable (X m) := by
    -- Proof comment: the coordinate `X m` is measurable for the terminal filtration because
    -- `m ≤ T` keeps it inside the generated history window.
    refine Measurable.of_comap_le ?_
    exact le_iSup_of_le m <| le_iSup_of_le hmLe le_rfl
  -- Proof comment: each bounded-time slice is the preimage of the fixed state-space event
  -- `K ∩ {x₁}ᶜ`, so the whole shifted event is a countable intersection of such slices.
  exact hXm (DiscreteMeasurableSpace.forall_measurableSet _)

/-- Helper for Theorem 19.25: enlarging the block index only strengthens the shifted finite-hull
survival requirement. -/
private theorem shiftedStayInFiniteReachableHull_antitone
    (K : Set E) (N : ℕ) :
    Antitone (shiftedStayInFiniteReachableHull (X := X) (x₁ := x₁) K N) := by
  intro k l hkl ω hω m hm_pos hm_le
  have hHorizon :
      1 + k * N ≤ 1 + l * N := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      Nat.add_le_add_left (Nat.mul_le_mul_right N hkl) 1
  -- Proof comment: a path that survives up to the larger horizon also survives up to any smaller
  -- horizon.
  exact hω m hm_pos (hm_le.trans hHorizon)

/-- Helper for Theorem 19.25: membership in the shifted survival event forces the state at the
terminal time `1 + k * N` to lie in `K \\ {x₁}`. -/
private theorem mem_shiftedStayInFiniteReachableHull_horizon
    {K : Set E} {N k : ℕ} {ω : Ω}
    (hω : ω ∈ shiftedStayInFiniteReachableHull (X := X) (x₁ := x₁) K N k) :
    X (1 + k * N) ω ∈ K ∧ X (1 + k * N) ω ≠ x₁ := by
  -- Proof comment: the horizon time itself is one of the positive times constrained by the
  -- shifted event definition.
  exact hω (1 + k * N) (by simpa using Nat.succ_pos (k * N)) le_rfl

/-- Helper for Theorem 19.25: the event of staying forever in a finite hull while avoiding `x₁`
is the decreasing intersection of the shifted survival events. -/
private theorem stayInFiniteReachableHull_eq_iInter_shifted
    {K : Set E} {N : ℕ} (hN : 0 < N) :
    {ω | (∀ n : ℕ, 0 < n → X n ω ∈ K) ∧ (∀ n : ℕ, 0 < n → X n ω ≠ x₁)} =
      ⋂ k : ℕ, shiftedStayInFiniteReachableHull (X := X) (x₁ := x₁) K N k := by
  ext ω
  constructor
  · intro hω
    refine Set.mem_iInter.mpr ?_
    intro k
    intro m hm_pos hm_le
    -- Proof comment: a path that stays in `K` and avoids `x₁` at every positive time satisfies
    -- every bounded-horizon version of the same requirement.
    exact ⟨hω.1 m hm_pos, hω.2 m hm_pos⟩
  · intro hω
    refine ⟨?_, ?_⟩
    · intro m hm_pos
      have hm_bound : m ≤ 1 + m * N := by
        have hOne : 1 ≤ N := Nat.succ_le_of_lt hN
        calc
          m = m * 1 := by simp
          _ ≤ m * N := Nat.mul_le_mul_left _ hOne
          _ ≤ m * N + 1 := Nat.le_add_right _ _
          _ = 1 + m * N := by simp [Nat.add_comm]
      have hmStage := Set.mem_iInter.mp hω m
      exact (hmStage m hm_pos hm_bound).1
    · intro m hm_pos
      have hm_bound : m ≤ 1 + m * N := by
        have hOne : 1 ≤ N := Nat.succ_le_of_lt hN
        calc
          m = m * 1 := by simp
          _ ≤ m * N := Nat.mul_le_mul_left _ hOne
          _ ≤ m * N + 1 := Nat.le_add_right _ _
          _ = 1 + m * N := by simp [Nat.add_comm]
      have hmStage := Set.mem_iInter.mp hω m
      -- Proof comment: choosing the block index `k = m` gives a horizon that already contains the
      -- queried positive time `m`.
      exact (hmStage m hm_pos hm_bound).2

/-- Helper for Theorem 19.25: positive-time visits outside the reachable hull have zero total
probability under the law started from `x₁`. -/
private theorem positiveTimeVisitsOutsideReachable_null :
    (P x₁ : Measure Ω)
      (⋃ n : ℕ, {ω | 0 < n ∧ X n ω ∈ (positiveTimeReachable p x₁)ᶜ}) = 0 := by
  refine measure_iUnion_null ?_
  intro n
  by_cases hn : 0 < n
  · -- Proof comment: each fixed positive time has zero mass outside the positive-time reachable
    -- hull, and the countable union preserves nullity.
    simpa [hn] using
      positiveTimeLaw_null_outsideReachable (p := p) (P := P) (X := X) (x₁ := x₁)
        (A := (positiveTimeReachable p x₁)ᶜ) hn (by intro y hy; exact hy)
  · simp [hn]

/-- Helper for Theorem 19.25: after a history event fixes `X n = y`, the mass of the later
singleton event `X (n + m) = z` factors through the deterministic-time Markov restart law. -/
private theorem measure_inter_prefix_stepEvent_eq_mul
    {x y z : E} {A : Set Ω} {n m : ℕ}
    (hA_meas : MeasurableSet[generatedFiltrationSpace X n] A)
    (hA_sub : A ⊆ {ω | X n ω = y}) :
    (P x : Measure Ω).real (A ∩ {ω | X (n + m) ω = z}) =
      (((discreteMatrixKernel p ^ m) y) ({z} : Set E)).toReal * (P x : Measure Ω).real A := by
  let μ : Measure Ω := P x
  let hReal : IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X :=
    inferInstance
  let B : Set Ω := X (n + m) ⁻¹' ({z} : Set E)
  have hB_meas : MeasurableSet B := by
    simpa [B] using (hReal.measurable_process (n + m)) (MeasurableSet.singleton z)
  have hFiltration_le : generatedFiltrationSpace X n ≤ ‹MeasurableSpace Ω› := by
    refine iSup₂_le fun k hk ↦ ?_
    exact (hReal.measurable_process k).comap_le
  have hA_measAmbient : MeasurableSet A := by
    -- Proof comment: history-measurable events are ambient measurable because the generated
    -- filtration is a sub-σ-algebra of the ambient measurable space.
    dsimp [LE.le] at hFiltration_le
    exact hFiltration_le (s := A) hA_meas
  have hMarkovGenerated :
      μ⟦B | generatedFiltrationSpace X n⟧ =ᵐ[μ]
        fun ω ↦ (((discreteMatrixKernel p ^ m) (X n ω)) : Measure E).real ({z} : Set E) := by
    simpa [μ, B, add_comm] using
      hReal.markov_property x (A := ({z} : Set E)) (MeasurableSet.singleton z) n m
  have hIndicatorIntegrable : Integrable (B.indicator (fun _ ↦ (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hB_meas
  -- Proof comment: integrate the Markov conditional expectation over the history event `A`, then
  -- freeze the present state to `y` because `A` already determines `X n`.
  calc
    μ.real (A ∩ {ω | X (n + m) ω = z}) =
        ∫ ω in A, (μ⟦B | generatedFiltrationSpace X n⟧) ω ∂ μ := by
          rw [MeasureTheory.setIntegral_condExp hFiltration_le hIndicatorIntegrable hA_meas,
            ← MeasureTheory.integral_indicator hA_measAmbient]
          symm
          simpa [B, Set.indicator_indicator, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm,
            smul_eq_mul] using
            MeasureTheory.integral_indicator_const (μ := μ) (1 : ℝ)
              (hA_measAmbient.inter hB_meas)
    _ = ∫ ω in A, (((discreteMatrixKernel p ^ m) (X n ω)) : Measure E).real ({z} : Set E) ∂ μ := by
          exact MeasureTheory.integral_congr_ae hMarkovGenerated.restrict
    _ = ∫ _ in A, (((discreteMatrixKernel p ^ m) y) ({z} : Set E)).toReal ∂ μ := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards [MeasureTheory.self_mem_ae_restrict (μ := μ) (s := A) hA_measAmbient]
            with ω hω
          have hω : X n ω = y := hA_sub hω
          rw [hω]
          simp [MeasureTheory.Measure.real_def]
    _ = (((discreteMatrixKernel p ^ m) y) ({z} : Set E)).toReal * μ.real A := by
          rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_comm]

/-- Helper for Theorem 19.25: the deterministic-time restart factorization is cleaner in raw
`Measure` (`ℝ≥0∞`) form. -/
private theorem measure_inter_prefix_stepEvent_eq_mul_ennreal
    {x y z : E} {A : Set Ω} {n m : ℕ}
    (hA_meas : MeasurableSet[generatedFiltrationSpace X n] A)
    (hA_sub : A ⊆ {ω | X n ω = y}) :
    (P x : Measure Ω) (A ∩ {ω | X (n + m) ω = z}) =
      (((discreteMatrixKernel p ^ m) y) ({z} : Set E)) * (P x : Measure Ω) A := by
  have hstep :
      (P x : Measure Ω).real (A ∩ {ω | X (n + m) ω = z}) =
        (((discreteMatrixKernel p ^ m) y) ({z} : Set E)).toReal * (P x : Measure Ω).real A :=
    measure_inter_prefix_stepEvent_eq_mul (p := p) (P := P) (X := X) hA_meas hA_sub
  have hleft_ne_top :
      (P x : Measure Ω) (A ∩ {ω | X (n + m) ω = z}) ≠ ⊤ :=
    measure_ne_top _ _
  letI : IsMarkovKernel ((fun k : ℕ ↦ discreteMatrixKernel p ^ k) m) :=
    (inferInstance :
      IsMarkovProcessRealization (fun k : ℕ ↦ discreteMatrixKernel p ^ k) P X).semigroup.isMarkovKernel m
  have hright_ne_top :
      (((discreteMatrixKernel p ^ m) y) ({z} : Set E)) * (P x : Measure Ω) A ≠ ⊤ := by
    have hkernel_ne_top : (((discreteMatrixKernel p ^ m) y) ({z} : Set E)) ≠ ⊤ :=
      measure_ne_top _ _
    exact ENNReal.mul_ne_top hkernel_ne_top (measure_ne_top _ _)
  -- Proof comment: both event masses are finite, so equality of their `toReal` values upgrades
  -- back to equality in `ℝ≥0∞`.
  exact (ENNReal.toReal_eq_toReal_iff' hleft_ne_top hright_ne_top).mp <| by
    simpa [MeasureTheory.Measure.real_def, ENNReal.toReal_mul, measure_ne_top _ _, measure_ne_top _ _]
      using hstep

/-- Helper for Theorem 19.25: after a history event fixes `X n = y`, the mass of any later
state-set event factors through the deterministic-time Markov restart law. -/
private theorem measure_inter_prefix_stateEvent_eq_mul
    {x y : E} {B : Set E} {A : Set Ω} {n m : ℕ}
    (hB_meas : MeasurableSet B)
    (hA_meas : MeasurableSet[generatedFiltrationSpace X n] A)
    (hA_sub : A ⊆ {ω | X n ω = y}) :
    (P x : Measure Ω).real (A ∩ {ω | X (n + m) ω ∈ B}) =
      (((discreteMatrixKernel p ^ m) y) B).toReal * (P x : Measure Ω).real A := by
  let μ : Measure Ω := P x
  let hReal : IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X :=
    inferInstance
  let C : Set Ω := X (n + m) ⁻¹' B
  have hC_meas : MeasurableSet C := by
    simpa [C] using (hReal.measurable_process (n + m)) hB_meas
  have hFiltration_le :
      generatedFiltrationSpace X n ≤ ‹MeasurableSpace Ω› :=
    generatedFiltrationSpace_le_ambientLocal (p := p) (P := P) (X := X) n
  have hA_measAmbient : MeasurableSet A := by
    -- Proof comment: generated-history measurability upgrades to ambient measurability through the
    -- realization's coordinate measurability.
    dsimp [LE.le] at hFiltration_le
    exact hFiltration_le (s := A) hA_meas
  have hMarkovGenerated :
      μ⟦C | generatedFiltrationSpace X n⟧ =ᵐ[μ]
        fun ω ↦ (((discreteMatrixKernel p ^ m) (X n ω)) : Measure E).real B := by
    simpa [μ, C, add_comm] using
      hReal.markov_property x (A := B) hB_meas n m
  have hIndicatorIntegrable : Integrable (C.indicator (fun _ ↦ (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hC_meas
  -- Proof comment: integrate the deterministic-time Markov identity over the history event `A`,
  -- then freeze the present state to `y` because `A` already pins down `X n`.
  calc
    μ.real (A ∩ {ω | X (n + m) ω ∈ B}) =
        ∫ ω in A, (μ⟦C | generatedFiltrationSpace X n⟧) ω ∂ μ := by
          rw [MeasureTheory.setIntegral_condExp hFiltration_le hIndicatorIntegrable hA_meas,
            ← MeasureTheory.integral_indicator hA_measAmbient]
          symm
          simpa [C, Set.indicator_indicator, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm,
            smul_eq_mul] using
            MeasureTheory.integral_indicator_const (μ := μ) (1 : ℝ)
              (hA_measAmbient.inter hC_meas)
    _ = ∫ ω in A, (((discreteMatrixKernel p ^ m) (X n ω)) : Measure E).real B ∂ μ := by
          exact MeasureTheory.integral_congr_ae hMarkovGenerated.restrict
    _ = ∫ _ in A, (((discreteMatrixKernel p ^ m) y) B).toReal ∂ μ := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards [MeasureTheory.self_mem_ae_restrict (μ := μ) (s := A) hA_measAmbient]
            with ω hω
          have hω : X n ω = y := hA_sub hω
          rw [hω]
          simp [MeasureTheory.Measure.real_def]
    _ = (((discreteMatrixKernel p ^ m) y) B).toReal * μ.real A := by
          rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_comm]

/-- Helper for Theorem 19.25: the deterministic-time restart factorization also holds for general
future state-set events in raw `Measure` (`ℝ≥0∞`) form. -/
private theorem measure_inter_prefix_stateEvent_eq_mul_ennreal
    {x y : E} {B : Set E} {A : Set Ω} {n m : ℕ}
    (hB_meas : MeasurableSet B)
    (hA_meas : MeasurableSet[generatedFiltrationSpace X n] A)
    (hA_sub : A ⊆ {ω | X n ω = y}) :
    (P x : Measure Ω) (A ∩ {ω | X (n + m) ω ∈ B}) =
      (((discreteMatrixKernel p ^ m) y) B) * (P x : Measure Ω) A := by
  have hstep :
      (P x : Measure Ω).real (A ∩ {ω | X (n + m) ω ∈ B}) =
        (((discreteMatrixKernel p ^ m) y) B).toReal * (P x : Measure Ω).real A :=
    measure_inter_prefix_stateEvent_eq_mul
      (p := p) (P := P) (X := X) hB_meas hA_meas hA_sub
  have hleft_ne_top :
      (P x : Measure Ω) (A ∩ {ω | X (n + m) ω ∈ B}) ≠ ⊤ :=
    measure_ne_top _ _
  letI : IsMarkovKernel ((fun k : ℕ ↦ discreteMatrixKernel p ^ k) m) :=
    (inferInstance :
      IsMarkovProcessRealization (fun k : ℕ ↦ discreteMatrixKernel p ^ k) P X).semigroup.isMarkovKernel m
  have hright_ne_top :
      (((discreteMatrixKernel p ^ m) y) B) * (P x : Measure Ω) A ≠ ⊤ := by
    have hkernel_ne_top : (((discreteMatrixKernel p ^ m) y) B) ≠ ⊤ :=
      measure_ne_top _ _
    exact ENNReal.mul_ne_top hkernel_ne_top (measure_ne_top _ _)
  -- Proof comment: finiteness of both sides lets us lift the already-proved `toReal` identity
  -- back to `ℝ≥0∞`.
  exact (ENNReal.toReal_eq_toReal_iff' hleft_ne_top hright_ne_top).mp <| by
    simpa [MeasureTheory.Measure.real_def, ENNReal.toReal_mul, measure_ne_top _ _, measure_ne_top _ _]
      using hstep

/-- Helper for Theorem 19.25: the explicit reachable-hull escape targets are the complements of
the inserted finite exhaustion stages. -/
private def reachableExhaustionTarget (n : ℕ) : Set E :=
  (insert x₁
    (positiveTimeReachableExhaustion (p := p) (P := P) (X := X) (x₁ := x₁) n))ᶜ

/-- Helper for Theorem 19.25: the `n`th reachable-hull escape event is hitting the `n`th target
before any positive-time return to `x₁`. -/
private def reachableExhaustionEscapeEvent (n : ℕ) : Set Ω :=
  {ω | ∃ m : ℕ, 0 < m ∧ X m ω ∈ reachableExhaustionTarget (p := p) (P := P) (X := X) (x₁ := x₁) n ∧
    ∀ j : ℕ, 0 < j → j ≤ m → X j ω ≠ x₁}

/-- Helper for Theorem 19.25: `noReturnEvent` is the event of never making a positive-time return
to `x₁`. -/
private def noReturnEvent : Set Ω :=
  {ω | ∀ j : ℕ, 0 < j → X j ω ≠ x₁}

/-- Helper for Theorem 19.25: uniform positive deterministic return data on a finite reachable hull
forces geometric decay of the shifted finite-hull survival events. -/
private theorem shiftedStayInFiniteReachableHull_contracts_of_uniformReturn
    {K : Set E} {N : ℕ} {δ : ℝ≥0∞}
    (hKfin : K.Finite) (hN : 0 < N) (hδ : 0 < δ) (hδ_le_one : δ ≤ 1)
    (hreturn :
      ∀ y ∈ K, y ≠ x₁ →
        ∃ m : ℕ, 0 < m ∧ m ≤ N ∧ δ ≤ ((discreteMatrixKernel p ^ m) y) ({x₁} : Set E)) :
    ∀ k : ℕ,
      (P x₁ : Measure Ω)
        (shiftedStayInFiniteReachableHull (X := X) (x₁ := x₁) K N (k + 1)) ≤
        (1 - δ) * (P x₁ : Measure Ω)
          (shiftedStayInFiniteReachableHull (X := X) (x₁ := x₁) K N k) := by
  classical
  intro k
  let μ : Measure Ω := P x₁
  let L : Finset E := hKfin.toFinset.erase x₁
  let horizon : ℕ := 1 + k * N
  let S : ℕ → Set Ω := shiftedStayInFiniteReachableHull (X := X) (x₁ := x₁) K N
  let Slice : E → Set Ω := fun y ↦ S k ∩ {ω | X horizon ω = y}
  let NextSlice : E → Set Ω := fun y ↦ S (k + 1) ∩ Slice y
  have hState_meas :
      ∀ y : E,
        MeasurableSet[generatedFiltrationSpace X horizon] ({ω | X horizon ω = y} : Set Ω) := by
    intro y
    letI : MeasurableSpace Ω := generatedFiltrationSpace X horizon
    have hXh : Measurable (X horizon) := by
      refine Measurable.of_comap_le ?_
      exact le_iSup_of_le horizon <| le_iSup_of_le le_rfl le_rfl
    show MeasurableSet (X horizon ⁻¹' ({y} : Set E))
    exact hXh (MeasurableSet.singleton y)
  have hSlice_hist :
      ∀ y ∈ L, MeasurableSet[generatedFiltrationSpace X horizon] (Slice y) := by
    intro y hyL
    -- Proof comment: each slice is the shifted survival history intersected with one fixed
    -- horizon-state cylinder.
    exact
      (shiftedStayInFiniteReachableHull_measurable
        (p := p) (P := P) (X := X) (x₁ := x₁) K N k).inter
        (hState_meas y)
  have hAmbient_le_horizon :
      generatedFiltrationSpace X horizon ≤ ‹MeasurableSpace Ω› :=
    generatedFiltrationSpace_le_ambientLocal (p := p) (P := P) (X := X) horizon
  have hSlice_meas :
      ∀ y ∈ L, MeasurableSet (Slice y) := by
    intro y hyL
    have hSlice := hSlice_hist y hyL
    dsimp [LE.le] at hAmbient_le_horizon
    exact hAmbient_le_horizon (s := Slice y) hSlice
  have hSlice_disj : Set.PairwiseDisjoint (↑L : Set E) Slice := by
    intro y hy z hz hyz
    refine Set.disjoint_left.2 ?_
    intro ω hωy hωz
    have hyEq : X horizon ω = y := by simpa [Slice, horizon] using hωy.2
    have hzEq : X horizon ω = z := by simpa [Slice, horizon] using hωz.2
    exact hyz (hyEq.symm.trans hzEq)
  have hSlice_union : S k = ⋃ y ∈ L, Slice y := by
    ext ω
    constructor
    · intro hω
      have hω_horizon :
          X horizon ω ∈ K ∧ X horizon ω ≠ x₁ :=
        mem_shiftedStayInFiniteReachableHull_horizon (X := X) (x₁ := x₁) hω
      have hyL : X horizon ω ∈ L := by
        refine Finset.mem_erase.mpr ?_
        exact ⟨hω_horizon.2, hKfin.mem_toFinset.mpr hω_horizon.1⟩
      refine Set.mem_iUnion.2 ⟨X horizon ω, ?_⟩
      refine Set.mem_iUnion.2 ⟨hyL, ?_⟩
      exact ⟨hω, by simp [Slice, horizon]⟩
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨y, hyω⟩
      rcases Set.mem_iUnion.1 hyω with ⟨hyL, hyω⟩
      exact hyω.1
  have hS_succ_subset : S (k + 1) ⊆ S k := by
    exact shiftedStayInFiniteReachableHull_antitone (X := X) (x₁ := x₁) K N (Nat.le_succ k)
  have hNext_union : S (k + 1) = ⋃ y ∈ L, NextSlice y := by
    ext ω
    constructor
    · intro hω
      have hωk : ω ∈ S k := hS_succ_subset hω
      have hωSlices : ω ∈ ⋃ y ∈ L, Slice y := by rwa [← hSlice_union]
      rcases Set.mem_iUnion.1 hωSlices with ⟨y, hyω⟩
      rcases Set.mem_iUnion.1 hyω with ⟨hyL, hyω⟩
      refine Set.mem_iUnion.2 ⟨y, ?_⟩
      refine Set.mem_iUnion.2 ⟨hyL, ?_⟩
      exact ⟨hω, hyω⟩
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨y, hyω⟩
      rcases Set.mem_iUnion.1 hyω with ⟨hyL, hyω⟩
      exact hyω.1
  have hNext_meas :
      ∀ y ∈ L, MeasurableSet (NextSlice y) := by
    intro y hyL
    let hAmbient_le_succ :=
      generatedFiltrationSpace_le_ambientLocal (p := p) (P := P) (X := X) (1 + (k + 1) * N)
    have hSuccMeas :
        MeasurableSet
          (shiftedStayInFiniteReachableHull (X := X) (x₁ := x₁) K N (k + 1)) := by
      have hMeas :=
        shiftedStayInFiniteReachableHull_measurable
          (p := p) (P := P) (X := X) (x₁ := x₁) K N (k + 1)
      dsimp [LE.le] at hAmbient_le_succ
      exact hAmbient_le_succ (s := S (k + 1)) hMeas
    exact hSuccMeas.inter (hSlice_meas y hyL)
  have hNext_disj : Set.PairwiseDisjoint (↑L : Set E) NextSlice := by
    intro y hy z hz hyz
    refine Set.disjoint_left.2 ?_
    intro ω hωy hωz
    have hyEq : X horizon ω = y := by simpa [NextSlice, Slice, horizon] using hωy.2.2
    have hzEq : X horizon ω = z := by simpa [NextSlice, Slice, horizon] using hωz.2.2
    exact hyz (hyEq.symm.trans hzEq)
  have hSlice_bound :
      ∀ y ∈ L, μ (NextSlice y) ≤ (1 - δ) * μ (Slice y) := by
    intro y hyL
    have hyK : y ∈ K := by
      exact hKfin.mem_toFinset.mp (Finset.mem_erase.mp hyL).2
    have hy_ne : y ≠ x₁ := (Finset.mem_erase.mp hyL).1
    rcases hreturn y hyK hy_ne with ⟨m, hm_pos, hm_le, hδy⟩
    have hNext_subset :
        NextSlice y ⊆ Slice y ∩ {ω | X (horizon + m) ω ∈ ({x₁} : Set E)ᶜ} := by
      intro ω hω
      refine ⟨hω.2, ?_⟩
      have hωsucc : ω ∈ S (k + 1) := hω.1
      have htime_le : horizon + m ≤ 1 + (k + 1) * N := by
        calc
          horizon + m ≤ horizon + N := Nat.add_le_add_left hm_le horizon
          _ = 1 + (k + 1) * N := by
            dsimp [horizon]
            rw [Nat.succ_mul, Nat.add_assoc]
      have htime_pos : 0 < horizon + m := by
        have hhor_pos : 0 < horizon := by
          simpa [horizon, Nat.succ_eq_add_one, Nat.add_comm, Nat.add_left_comm,
            Nat.add_assoc] using Nat.succ_pos (k * N)
        exact lt_of_lt_of_le hhor_pos (Nat.le_add_right horizon m)
      have hωtime :
          X (horizon + m) ω ∈ K ∧ X (horizon + m) ω ≠ x₁ :=
        hωsucc (horizon + m) htime_pos htime_le
      simpa using hωtime.2
    have hSlice_sub :
        Slice y ⊆ {ω | X horizon ω = y} := by
      intro ω hω
      exact hω.2
    have hMarkov :
        μ (Slice y ∩ {ω | X (horizon + m) ω ∈ ({x₁} : Set E)ᶜ}) =
          (((discreteMatrixKernel p ^ m) y) ({x₁} : Set E)ᶜ) * μ (Slice y) := by
      exact measure_inter_prefix_stateEvent_eq_mul_ennreal
        (p := p) (P := P) (X := X) (x := x₁) (y := y)
        (B := ({x₁} : Set E)ᶜ) (A := Slice y) (n := horizon) (m := m)
        (by simpa using (measurableSet_singleton x₁).compl)
        (hSlice_hist y hyL) hSlice_sub
    have hcompl_le :
        (((discreteMatrixKernel p ^ m) y) ({x₁} : Set E)ᶜ) ≤ 1 - δ := by
      let hRealPow : IsMarkovProcessRealization (fun k : ℕ ↦ discreteMatrixKernel p ^ k) P X :=
        inferInstance
      letI : IsMarkovKernel ((fun k : ℕ ↦ discreteMatrixKernel p ^ k) m) :=
        hRealPow.semigroup.isMarkovKernel m
      have hcompl_eq :
          (((discreteMatrixKernel p ^ m) y) ({x₁} : Set E)ᶜ) =
            1 - ((discreteMatrixKernel p ^ m) y) ({x₁} : Set E) := by
        simpa using
          (MeasureTheory.prob_compl_eq_one_sub
            (μ := ((discreteMatrixKernel p ^ m) y))
            (s := ({x₁} : Set E)) (measurableSet_singleton x₁))
      rw [hcompl_eq]
      exact tsub_le_tsub_left hδy 1
    -- Proof comment: on each horizon slice, surviving the next block forces the specific return
    -- time `m` to miss `x₁`, and the restart factorization bounds that miss-event by `1 - δ`.
    calc
      μ (NextSlice y)
        ≤ μ (Slice y ∩ {ω | X (horizon + m) ω ∈ ({x₁} : Set E)ᶜ}) := by
            exact measure_mono hNext_subset
      _ = (((discreteMatrixKernel p ^ m) y) ({x₁} : Set E)ᶜ) * μ (Slice y) := hMarkov
      _ ≤ (1 - δ) * μ (Slice y) := by
            exact mul_le_mul_right' hcompl_le (μ (Slice y))
  -- Proof comment: partition the current horizon event by the horizon state, apply the slice-wise
  -- contraction estimate, and recombine the disjoint finite union.
  calc
    μ (S (k + 1))
      = Finset.sum L (fun y ↦ μ (NextSlice y)) := by
          rw [hNext_union]
          exact MeasureTheory.measure_biUnion_finset hNext_disj hNext_meas
    _ ≤ Finset.sum L (fun y ↦ (1 - δ) * μ (Slice y)) := by
          exact Finset.sum_le_sum hSlice_bound
    _ = (1 - δ) * Finset.sum L (fun y ↦ μ (Slice y)) := by
          rw [Finset.mul_sum]
    _ = (1 - δ) * μ (S k) := by
          congr 1
          symm
          rw [hSlice_union]
          exact MeasureTheory.measure_biUnion_finset hSlice_disj hSlice_meas

/-- Helper for Theorem 19.25: a path that avoids `x₁` forever cannot stay forever inside one fixed
finite reachable hull with positive probability. -/
private theorem stayInFiniteReachableHull_avoidStart_null
    {C : E → E → ℝ≥0∞} [IsRandomWalkWithWeights p C]
    {K : Set E} (hKfin : K.Finite) (hx₁K : x₁ ∈ K)
    (hKsub : K ⊆ insert x₁ (positiveTimeReachable p x₁)) :
    (P x₁ : Measure Ω)
      {ω | (∀ n : ℕ, 0 < n → X n ω ∈ K) ∧ (∀ n : ℕ, 0 < n → X n ω ≠ x₁)} = 0 := by
  classical
  let μ : Measure Ω := P x₁
  let Trap : Set Ω :=
    {ω | (∀ n : ℕ, 0 < n → X n ω ∈ K) ∧ (∀ n : ℕ, 0 < n → X n ω ≠ x₁)}
  by_cases hLempty : hKfin.toFinset.erase x₁ = ∅
  · have hTrap_empty : Trap = (∅ : Set Ω) := by
      ext ω
      constructor
      · intro hω
        have hX1K : X 1 ω ∈ K := hω.1 1 (by simp)
        have hX1ne : X 1 ω ≠ x₁ := hω.2 1 (by simp)
        have hX1eq : X 1 ω = x₁ := by
          by_contra hneq
          have hmem : X 1 ω ∈ hKfin.toFinset.erase x₁ := by
            exact Finset.mem_erase.mpr ⟨hneq, hKfin.mem_toFinset.mpr hX1K⟩
          simpa [hLempty] using hmem
        exact (hX1ne hX1eq).elim
      · simp
    simpa [μ, Trap, hTrap_empty]
  · obtain ⟨N, hN, δ, hδ, huniform⟩ :=
      finiteReachableHull_uniformReturnData
        (p := p) (P := P) (X := X) (x₁ := x₁) (C := C) hKfin hx₁K hKsub
    let hRealPow :
        IsMarkovProcessRealization (fun k : ℕ ↦ discreteMatrixKernel p ^ k) P X :=
      inferInstance
    have hδ_le_one : δ ≤ 1 := by
      rcases Finset.nonempty_iff_ne_empty.mpr hLempty with ⟨y, hyL⟩
      have hyK : y ∈ K := by
        exact hKfin.mem_toFinset.mp (Finset.mem_erase.mp hyL).2
      have hy_ne : y ≠ x₁ := (Finset.mem_erase.mp hyL).1
      rcases huniform y hyK hy_ne with ⟨m, hm_pos, hm_le, hδy⟩
      letI : IsMarkovKernel ((fun k : ℕ ↦ discreteMatrixKernel p ^ k) m) :=
        hRealPow.semigroup.isMarkovKernel m
      have hmass_le :
          ((discreteMatrixKernel p ^ m) y) ({x₁} : Set E) ≤ 1 := by
        have huniv :
            ((discreteMatrixKernel p ^ m) y) Set.univ = 1 := by
          simpa using
            ((inferInstance :
              IsMarkovKernel ((fun k : ℕ ↦ discreteMatrixKernel p ^ k) m))
                .isProbabilityMeasure y).measure_univ
        rw [← huniv]
        exact measure_mono (Set.singleton_subset_iff.mpr (Set.mem_univ x₁))
      exact le_trans hδy hmass_le
    let S : ℕ → Set Ω := shiftedStayInFiniteReachableHull (X := X) (x₁ := x₁) K N
    have hS_meas : ∀ k : ℕ, MeasurableSet (S k) := by
      intro k
      let hAmbient_le :=
        generatedFiltrationSpace_le_ambientLocal (p := p) (P := P) (X := X) (1 + k * N)
      have hMeas :=
        shiftedStayInFiniteReachableHull_measurable
          (p := p) (P := P) (X := X) (x₁ := x₁) K N k
      dsimp [LE.le] at hAmbient_le
      exact hAmbient_le (s := S k) hMeas
    have hSTendsto :
        Filter.Tendsto (fun k ↦ μ (S k)) Filter.atTop (nhds (μ Trap)) := by
      have hInter :
          Trap = ⋂ k : ℕ, S k :=
        stayInFiniteReachableHull_eq_iInter_shifted (X := X) (x₁ := x₁) (K := K) (N := N) hN
      simpa [μ, Trap, S, hInter] using
        tendsto_measure_iInter_atTop (μ := μ)
          (fun k ↦ (hS_meas k).nullMeasurableSet)
          (shiftedStayInFiniteReachableHull_antitone (X := X) (x₁ := x₁) K N)
          ⟨0, measure_ne_top _ _⟩
    have hBound :
        ∀ k : ℕ, μ (S k) ≤ (1 - δ) ^ k := by
      intro k
      induction k with
      | zero =>
          calc
            μ (S 0) ≤ μ Set.univ := by
              exact measure_mono (Set.subset_univ _)
            _ = 1 := by simp [μ]
            _ = (1 - δ) ^ 0 := by simp
      | succ k ih =>
          calc
            μ (S (k + 1)) ≤ (1 - δ) * μ (S k) := by
              exact shiftedStayInFiniteReachableHull_contracts_of_uniformReturn
                (p := p) (P := P) (X := X) (x₁ := x₁)
                hKfin hN hδ hδ_le_one huniform k
            _ ≤ (1 - δ) * (1 - δ) ^ k := by
              exact mul_right_mono ih
            _ = (1 - δ) ^ (k + 1) := by
              rw [pow_succ, mul_comm]
    have hPowTendsto :
        Filter.Tendsto (fun k : ℕ ↦ (1 - δ) ^ k) Filter.atTop (nhds 0) := by
      have hsub_lt_one : 1 - δ < 1 := by
        exact ENNReal.sub_lt_self (by simp) (by simp) hδ.ne'
      exact ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hsub_lt_one
    have hZeroTendsto :
        Filter.Tendsto (fun k : ℕ ↦ μ (S k)) Filter.atTop (nhds 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le
        tendsto_const_nhds hPowTendsto ?_ ?_
      · intro k
        simp
      · intro k
        exact hBound k
    -- Proof comment: continuity from above identifies the tail event with the decreasing
    -- intersection, and the geometric block bound drives that limit to `0`.
    exact tendsto_nhds_unique hSTendsto hZeroTendsto

/-- Helper for Theorem 19.25: the decreasing reachable-exhaustion escape events coincide almost
everywhere with the no-return event. -/
private theorem reachableExhaustionEscapeEvents_ae_eq_noReturn
    {C : E → E → ℝ≥0∞} [IsRandomWalkWithWeights p C] :
    (⋂ n : ℕ,
        reachableExhaustionEscapeEvent (p := p) (P := P) (X := X) (x₁ := x₁) n)
      =ᵐ[(P x₁ : Measure Ω)]
        noReturnEvent (X := X) (x₁ := x₁) := by
  classical
  let μ : Measure Ω := P x₁
  let BadReach : Set Ω :=
    ⋃ n : ℕ, {ω | 0 < n ∧ X n ω ∈ (positiveTimeReachable p x₁)ᶜ}
  have hBadReach_zero : μ BadReach = 0 := by
    simpa [μ, BadReach] using
      positiveTimeVisitsOutsideReachable_null (p := p) (P := P) (X := X) (x₁ := x₁)
  have hLeft_zero :
      μ
        ((⋂ n : ℕ,
            reachableExhaustionEscapeEvent (p := p) (P := P) (X := X) (x₁ := x₁) n) \
          noReturnEvent (X := X) (x₁ := x₁)) = 0 := by
    have hSubset :
        ((⋂ n : ℕ,
            reachableExhaustionEscapeEvent (p := p) (P := P) (X := X) (x₁ := x₁) n) \
          noReturnEvent (X := X) (x₁ := x₁)) ⊆ BadReach := by
      intro ω hω
      by_contra hωBad
      have hωInter :
          ω ∈ ⋂ n : ℕ, reachableExhaustionEscapeEvent (p := p) (P := P) (X := X) (x₁ := x₁) n :=
        hω.1
      have hωReturn : ∃ r : ℕ, 0 < r ∧ X r ω = x₁ := by
        by_contra hNoReturn
        apply hω.2
        intro j hj
        by_contra hjEq
        exact hNoReturn ⟨j, hj, hjEq⟩
      rcases hωReturn with ⟨r, hr_pos, hr_eq⟩
      let Kω : Set E := ↑((Finset.Icc 1 r).image fun m ↦ X m ω)
      have hKωfin : Kω.Finite := by
        exact ((Finset.Icc 1 r).image fun m ↦ X m ω).finite_toSet
      have hKωsub : Kω ⊆ insert x₁ (positiveTimeReachable p x₁) := by
        intro y hyK
        have hyFin : y ∈ (Finset.Icc 1 r).image fun m ↦ X m ω := by
          simpa [Kω] using hyK
        rcases Finset.mem_image.mp hyFin with ⟨m, hm, rfl⟩
        have hm_pos : 0 < m := (Finset.mem_Icc.mp hm).1
        have hmReach : X m ω ∈ positiveTimeReachable p x₁ := by
          by_contra hmNotReach
          exact hωBad <| Set.mem_iUnion.mpr ⟨m, ⟨hm_pos, hmNotReach⟩⟩
        exact Or.inr hmReach
      obtain ⟨n, hnStage⟩ :=
        finiteSubset_insertReachable_eventually_subset_stage
          (p := p) (P := P) (X := X) (x₁ := x₁) hKωfin hKωsub
      have hNotEscape :
          ω ∉ reachableExhaustionEscapeEvent (p := p) (P := P) (X := X) (x₁ := x₁) n := by
        intro hEscape
        rcases hEscape with ⟨m, hm_pos, hmTarget, hmNoReturn⟩
        by_cases hmr : m ≤ r
        · have hmKω : X m ω ∈ Kω := by
            refine Finset.mem_coe.mpr ?_
            exact Finset.mem_image.mpr ⟨m, Finset.mem_Icc.mpr ⟨hm_pos, hmr⟩, rfl⟩
          have hmStage :
              X m ω ∈
                insert x₁
                  (positiveTimeReachableExhaustion (p := p) (P := P) (X := X) (x₁ := x₁) n) :=
            hnStage hmKω
          exact hmTarget hmStage
        · have hr_le_m : r ≤ m := Nat.le_of_lt (Nat.lt_of_not_ge hmr)
          exact (hmNoReturn r hr_pos hr_le_m hr_eq).elim
      exact hNotEscape <| Set.mem_iInter.mp hωInter n
    exact measure_mono_null hSubset hBadReach_zero
  have hRight_zero :
      μ
        (noReturnEvent (X := X) (x₁ := x₁) \
          ⋂ n : ℕ,
            reachableExhaustionEscapeEvent (p := p) (P := P) (X := X) (x₁ := x₁) n) = 0 := by
    let Trap : ℕ → Set Ω := fun n ↦
      {ω |
        (∀ m : ℕ, 0 < m →
          X m ω ∈
            insert x₁
              (positiveTimeReachableExhaustion (p := p) (P := P) (X := X) (x₁ := x₁) n)) ∧
        (∀ m : ℕ, 0 < m → X m ω ≠ x₁)}
    have hTrap_zero :
        ∀ n : ℕ, μ (Trap n) = 0 := by
      intro n
      have hStageSub :
          insert x₁
              (positiveTimeReachableExhaustion
                (p := p) (P := P) (X := X) (x₁ := x₁) n) ⊆
            insert x₁ (positiveTimeReachable p x₁) := by
        intro y hy
        rcases hy with rfl | hy
        · exact Or.inl rfl
        · have hyUnion :
              y ∈
                ⋃ n : ℕ,
                  positiveTimeReachableExhaustion
                    (p := p) (P := P) (X := X) (x₁ := x₁) n := by
            exact Set.mem_iUnion.mpr ⟨n, hy⟩
          rwa [(positiveTimeReachableExhaustion
            (p := p) (P := P) (X := X) (x₁ := x₁)).iUnion_eq] at hyUnion
      -- Proof comment: each fixed exhaustion stage is a finite reachable hull, so the
      -- previously proved finite-hull null lemma applies directly.
      simpa [μ, Trap] using
        (stayInFiniteReachableHull_avoidStart_null
          (p := p) (P := P) (X := X) (x₁ := x₁) (C := C)
          (K := insert x₁
            (positiveTimeReachableExhaustion (p := p) (P := P) (X := X) (x₁ := x₁) n))
          (Set.Finite.insert x₁
            ((positiveTimeReachableExhaustion (p := p) (P := P) (X := X) (x₁ := x₁)).finite n))
          (by simp) hStageSub)
    have hSubset :
        noReturnEvent (X := X) (x₁ := x₁) \
            ⋂ n : ℕ,
              reachableExhaustionEscapeEvent (p := p) (P := P) (X := X) (x₁ := x₁) n
          ⊆ ⋃ n : ℕ, Trap n := by
      intro ω hω
      have hωNoReturn : ω ∈ noReturnEvent (X := X) (x₁ := x₁) := hω.1
      have hωNotInter :
          ω ∉ ⋂ n : ℕ,
            reachableExhaustionEscapeEvent (p := p) (P := P) (X := X) (x₁ := x₁) n := hω.2
      have hωNotInter' :
          ¬ ∀ n : ℕ,
            ω ∈ reachableExhaustionEscapeEvent (p := p) (P := P) (X := X) (x₁ := x₁) n := by
        simpa [Set.mem_iInter] using hωNotInter
      push Not at hωNotInter'
      rcases hωNotInter' with ⟨n, hnNot⟩
      refine Set.mem_iUnion.mpr ⟨n, ?_⟩
      refine ⟨?_, ?_⟩
      · intro m hm_pos
        by_contra hmTarget
        exact hnNot ⟨m, hm_pos, hmTarget, fun j hjpos hjle ↦ hωNoReturn j hjpos⟩
      · exact hωNoReturn
    have hUnion_zero : μ (⋃ n : ℕ, Trap n) = 0 := by
      refine measure_iUnion_null ?_
      intro n
      exact hTrap_zero n
    exact measure_mono_null hSubset hUnion_zero
  -- Proof comment: the decreasing escape events and the no-return event differ only by the null
  -- outside-reachable paths and the null finite-hull trap events.
  have hSymmDiff_zero :
      μ
        (((⋂ n : ℕ,
            reachableExhaustionEscapeEvent (p := p) (P := P) (X := X) (x₁ := x₁) n) ∆
          noReturnEvent (X := X) (x₁ := x₁))) = 0 := by
    rw [Set.symmDiff_def]
    refine le_antisymm ?_ bot_le
    calc
      μ
          (((⋂ n : ℕ,
              reachableExhaustionEscapeEvent (p := p) (P := P) (X := X) (x₁ := x₁) n) \
            noReturnEvent (X := X) (x₁ := x₁)) ∪
            (noReturnEvent (X := X) (x₁ := x₁) \
              ⋂ n : ℕ,
                reachableExhaustionEscapeEvent (p := p) (P := P) (X := X) (x₁ := x₁) n))
        ≤ μ
            ((⋂ n : ℕ,
                reachableExhaustionEscapeEvent (p := p) (P := P) (X := X) (x₁ := x₁) n) \
              noReturnEvent (X := X) (x₁ := x₁)) +
            μ
              (noReturnEvent (X := X) (x₁ := x₁) \
                ⋂ n : ℕ,
                  reachableExhaustionEscapeEvent (p := p) (P := P) (X := X) (x₁ := x₁) n) := by
          exact measure_union_le _ _
      _ = 0 := by rw [hLeft_zero, hRight_zero, zero_add]
  exact (measure_symmDiff_eq_zero_iff.mp hSymmDiff_zero)

omit [MeasurableSpace E] [DiscreteMeasurableSpace E] in
/-- Helper for Theorem 19.25: vanishing effective conductance is equivalent to infinite effective
resistance. -/
theorem effectiveConductanceToInfinity_eq_zero_iff_effectiveResistanceToInfinity_eq_top :
    effectiveConductanceToInfinity C P X x₁ = 0 ↔
      effectiveResistanceToInfinity C P X x₁ = ∞ := by
  -- Proof comment: the local resistance notation is just reciprocal conductance, and `a⁻¹ = ∞`
  -- in `ℝ≥0∞` is equivalent to `a = 0`.
  simp [effectiveResistanceToInfinity, ENNReal.inv_eq_top]

-- Proof sketch: choose a decreasing cofinite exhaustion away from `x₁`; Lemma 19.24 identifies
-- the limit of `conductance C x₁ * escapeToSetProbability P X x₁ (A₀ n)` with
-- `effectiveConductanceToInfinity C P X x₁`, while `escapeProbability_eq_prob_no_return`
-- identifies the same limit with `conductance C x₁ * escapeProbability P X x₁`.
/-- Helper for Theorem 19.25: the reachable-hull escape probabilities converge to the no-return
probability. -/
private theorem escapeToSetProbability_tendsto_reachableExhaustion
    {C : E → E → ℝ≥0∞} [IsRandomWalkWithWeights p C] :
    Filter.Tendsto
      (fun n ↦
        escapeToSetProbability P X x₁
          ((insert x₁
              (positiveTimeReachableExhaustion (p := p) (P := P) (X := X) (x₁ := x₁) n))ᶜ))
      Filter.atTop (nhds (escapeProbability P X x₁)) := by
  let μ : Measure Ω := P x₁
  let hReal : IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X :=
    inferInstance
  have hEscape_eq :
      ∀ n : ℕ,
        escapeToSetProbability P X x₁
            (reachableExhaustionTarget (p := p) (P := P) (X := X) (x₁ := x₁) n) =
          μ (reachableExhaustionEscapeEvent (p := p) (P := P) (X := X) (x₁ := x₁) n) := by
    intro n
    rw [escapeToSetProbability_def]
    rfl
  have hNoReturn_eq :
      escapeProbability P X x₁ = μ (noReturnEvent (X := X) (x₁ := x₁)) := by
    rw [escapeProbability_eq_prob_no_return P X x₁ (fun n ↦ hReal.measurable_process n)]
    rfl
  have hEscape_antitone :
      Antitone
        (reachableExhaustionEscapeEvent (p := p) (P := P) (X := X) (x₁ := x₁)) := by
    intro m n hmn ω hω
    rcases hω with ⟨k, hk_pos, hkTarget, hkNoReturn⟩
    have htarget :
        reachableExhaustionTarget (p := p) (P := P) (X := X) (x₁ := x₁) n ⊆
          reachableExhaustionTarget (p := p) (P := P) (X := X) (x₁ := x₁) m := by
      exact Set.compl_subset_compl.mpr <|
        by
          intro y hy
          rcases hy with rfl | hy
          · exact Or.inl rfl
          · exact Or.inr <|
              (positiveTimeReachableExhaustion (p := p) (P := P) (X := X) (x₁ := x₁)).mono hmn hy
    exact ⟨k, hk_pos, htarget hkTarget, hkNoReturn⟩
  have hEscape_meas :
      ∀ n : ℕ,
        MeasurableSet
          (reachableExhaustionEscapeEvent (p := p) (P := P) (X := X) (x₁ := x₁) n) := by
    intro n
    have hUnion :
        reachableExhaustionEscapeEvent (p := p) (P := P) (X := X) (x₁ := x₁) n =
          ⋃ m : ℕ,
            {ω |
              0 < m ∧
                X m ω ∈ reachableExhaustionTarget (p := p) (P := P) (X := X) (x₁ := x₁) n ∧
                ∀ j : ℕ, 0 < j → j ≤ m → X j ω ≠ x₁} := by
      ext ω
      simp [reachableExhaustionEscapeEvent]
    rw [hUnion]
    refine MeasurableSet.iUnion ?_
    intro m
    by_cases hm : 0 < m
    · have hEvent_eq :
          {ω |
              0 < m ∧
                X m ω ∈ reachableExhaustionTarget (p := p) (P := P) (X := X) (x₁ := x₁) n ∧
                ∀ j : ℕ, 0 < j → j ≤ m → X j ω ≠ x₁} =
            X m ⁻¹'
                reachableExhaustionTarget (p := p) (P := P) (X := X) (x₁ := x₁) n ∩
              (⋂ j ∈ (↑(Finset.Icc 1 m) : Set ℕ), X j ⁻¹' ({x₁} : Set E)ᶜ) := by
        ext ω
        constructor
        · intro hω
          refine ⟨hω.2.1, ?_⟩
          refine Set.mem_biInter ?_
          intro j hj
          have hj' : j ∈ Finset.Icc 1 m := Finset.mem_coe.mp hj
          exact hω.2.2 j (by simpa using (Finset.mem_Icc.mp hj').1) (Finset.mem_Icc.mp hj').2
        · intro hω
          refine ⟨hm, hω.1, ?_⟩
          intro j hjpos hjm
          have hj : j ∈ (↑(Finset.Icc 1 m) : Set ℕ) :=
            Finset.mem_coe.mpr <| Finset.mem_Icc.mpr ⟨by simpa using hjpos, hjm⟩
          exact Set.mem_iInter₂.mp hω.2 j hj
      rw [hEvent_eq]
      refine ((hReal.measurable_process m)
        (DiscreteMeasurableSpace.forall_measurableSet _)).inter ?_
      refine MeasurableSet.biInter (Finset.countable_toSet _) ?_
      intro j hj
      simpa using (hReal.measurable_process j) (measurableSet_singleton x₁).compl
    · have hEmpty :
          {ω |
              0 < m ∧
                X m ω ∈ reachableExhaustionTarget (p := p) (P := P) (X := X) (x₁ := x₁) n ∧
                ∀ j : ℕ, 0 < j → j ≤ m → X j ω ≠ x₁} = (∅ : Set Ω) := by
        ext ω
        simp [hm]
      rw [hEmpty]
      simp
  have hMeasure_tendsto :
      Filter.Tendsto
        (fun n : ℕ ↦
          μ (reachableExhaustionEscapeEvent (p := p) (P := P) (X := X) (x₁ := x₁) n))
        Filter.atTop
        (nhds
          (μ
            (⋂ n : ℕ,
              reachableExhaustionEscapeEvent (p := p) (P := P) (X := X) (x₁ := x₁) n))) := by
    exact tendsto_measure_iInter_atTop (μ := μ)
      (fun n ↦ (hEscape_meas n).nullMeasurableSet)
      hEscape_antitone
      ⟨0, measure_ne_top _ _⟩
  have hInter_eq :
      μ
          (⋂ n : ℕ,
            reachableExhaustionEscapeEvent (p := p) (P := P) (X := X) (x₁ := x₁) n) =
        μ (noReturnEvent (X := X) (x₁ := x₁)) := by
    exact measure_congr <|
      reachableExhaustionEscapeEvents_ae_eq_noReturn
        (p := p) (P := P) (X := X) (x₁ := x₁) (C := C)
  have hMeasure_tendsto_noReturn :
      Filter.Tendsto
        (fun n : ℕ ↦
          μ (reachableExhaustionEscapeEvent (p := p) (P := P) (X := X) (x₁ := x₁) n))
        Filter.atTop (nhds (μ (noReturnEvent (X := X) (x₁ := x₁)))) := by
    simpa [hInter_eq] using hMeasure_tendsto
  -- Proof comment: continuity from above gives the limit of the decreasing escape-event masses,
  -- and the AE comparison replaces that limit event with the no-return event.
  simpa [reachableExhaustionTarget, hNoReturn_eq] using
    hMeasure_tendsto_noReturn.congr' <|
      Filter.Eventually.of_forall fun n ↦ (hEscape_eq n).symm

/-- Theorem 19.25: the escape probability from `x₁` equals the conductance-normalized effective
conductance to infinity. -/
theorem escapeProbability_eq_conductance_inv_mul_effectiveConductanceToInfinity
    {p : E → E → ℝ≥0∞}
    [IsRandomWalkWithWeights p C]
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X] :
    escapeProbability P X x₁ =
      (conductance C x₁)⁻¹ * effectiveConductanceToInfinity C P X x₁
    := by
  let hWalk : IsRandomWalkWithWeights p C := inferInstance
  let A₀ : ℕ → Set E := fun n ↦
    (insert x₁
      (positiveTimeReachableExhaustion (p := p) (P := P) (X := X) (x₁ := x₁) n))ᶜ
  let f : ℕ → ℝ≥0∞ := fun n ↦ escapeToSetProbability P X x₁ (A₀ n)
  have hf_anti : Antitone f := by
    intro m n hmn
    have hstage :
        insert x₁
            (positiveTimeReachableExhaustion (p := p) (P := P) (X := X) (x₁ := x₁) m) ⊆
          insert x₁
            (positiveTimeReachableExhaustion (p := p) (P := P) (X := X) (x₁ := x₁) n) := by
      intro y hy
      rcases hy with rfl | hy
      · exact Or.inl rfl
      · exact Or.inr <|
          (positiveTimeReachableExhaustion (p := p) (P := P) (X := X) (x₁ := x₁)).mono hmn hy
    -- Proof comment: the finite exhaustion is increasing, so its complements form the decreasing
    -- target family that drives the limiting escape probabilities.
    exact
      escapeToSetProbability_mono P X x₁ (Set.compl_subset_compl.mpr hstage)
  have hlimit_iInf : Filter.Tendsto f Filter.atTop (nhds (⨅ n : ℕ, f n)) :=
    tendsto_atTop_iInf hf_anti
  have hiInf_eq : (⨅ n : ℕ, f n) = escapeProbability P X x₁ :=
    tendsto_nhds_unique hlimit_iInf
      (escapeToSetProbability_tendsto_reachableExhaustion
        (p := p) (P := P) (X := X) (x₁ := x₁) (C := C))
  have hconductance_mul :
      effectiveConductanceToInfinity C P X x₁ =
        conductance C x₁ * escapeProbability P X x₁ := by
    rw [effectiveConductanceToInfinity_eq_iInf_reachableExhaustion
      (p := p) (C := C) (P := P) (X := X) (x₁ := x₁), hiInf_eq]
  have hconductance_ne_zero : conductance C x₁ ≠ 0 :=
    conductance_ne_zero_at (p := p) (C := C) x₁
  have hconductance_ne_top : conductance C x₁ ≠ ∞ :=
    (hWalk.conductance_lt_top x₁).ne
  -- Proof comment: once the reachable-exhaustion limit is identified with `escapeProbability`,
  -- the theorem is just cancellation of the nonzero finite conductance factor.
  calc
    escapeProbability P X x₁ =
        (conductance C x₁)⁻¹ * (conductance C x₁ * escapeProbability P X x₁) := by
          symm
          rw [← mul_assoc, ENNReal.inv_mul_cancel hconductance_ne_zero hconductance_ne_top,
            one_mul]
    _ = (conductance C x₁)⁻¹ * effectiveConductanceToInfinity C P X x₁ := by
          rw [hconductance_mul]

/-- Helper for Theorem 19.25: the conductance at the starting state is nonzero because the
transition row at `x₁` is stochastic. -/
private theorem conductance_ne_zero
    (p : E → E → ℝ≥0∞) (C : E → E → ℝ≥0∞) [IsRandomWalkWithWeights p C] (x₁ : E) :
    conductance C x₁ ≠ 0 := by
  exact conductance_ne_zero_at (p := p) (C := C) x₁

/-- Helper for Theorem 19.25: recurrence of `x₁` is equivalent to vanishing effective
conductance to infinity. -/
theorem isRecurrentState_iff_effectiveConductanceToInfinity_eq_zero
    {p : E → E → ℝ≥0∞} [IsRandomWalkWithWeights p C]
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X] :
    IsRecurrentState P X x₁ ↔ effectiveConductanceToInfinity C P X x₁ = 0 := by
  let hWalk : IsRandomWalkWithWeights p C := inferInstance
  have hconductance_ne_top : conductance C x₁ ≠ ∞ :=
    (hWalk.conductance_lt_top x₁).ne
  have hconductance_inv_ne_zero : (conductance C x₁)⁻¹ ≠ 0 := by
    intro hinv
    exact hconductance_ne_top (ENNReal.inv_eq_zero.mp hinv)
  rw [IsRecurrentState, isRecurrentState_iff_escapeProbability_eq_zero P X x₁]
  rw [escapeProbability_eq_conductance_inv_mul_effectiveConductanceToInfinity
    (p := p) (C := C) (P := P) (X := X) (x₁ := x₁)]
  constructor
  · intro hzero
    rcases mul_eq_zero.mp hzero with hinv | hconductance
    · exact False.elim (hconductance_inv_ne_zero hinv)
    · exact hconductance
  · intro hzero
    -- Proof comment: once the effective conductance vanishes, the normalized escape probability
    -- vanishes by the main identity.
    simp [hzero]

/-- Helper for Theorem 19.25: recurrence of `x₁` is equivalent to infinite effective resistance
to infinity. -/
theorem isRecurrentState_iff_effectiveResistanceToInfinity_eq_top
    {p : E → E → ℝ≥0∞} [IsRandomWalkWithWeights p C]
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X] :
    IsRecurrentState P X x₁ ↔ effectiveResistanceToInfinity C P X x₁ = ∞ := by
  -- Proof comment: combine the conductance criterion with the reciprocal bridge for
  -- `effectiveResistanceToInfinity`.
  rw [isRecurrentState_iff_effectiveConductanceToInfinity_eq_zero
    (p := p) (C := C) (P := P) (X := X) (x₁ := x₁)]
  rw [effectiveConductanceToInfinity_eq_zero_iff_effectiveResistanceToInfinity_eq_top
    (C := C) (P := P) (X := X) (x₁ := x₁)]

end ProbabilityTheory
