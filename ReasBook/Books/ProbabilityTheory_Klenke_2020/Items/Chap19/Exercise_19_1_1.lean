/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap08.Example_8_27
import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Definition_9_10
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Definition_14_40
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_3
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.MarkovProcessRealization
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_42
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

open Classical

attribute [local instance] Classical.propDecidable

variable {E : Type u} {Ω : Type v}

section EntranceTime

variable [MeasurableSpace Ω]

/-- The chain started from every state outside `A` hits `A` almost surely at the first entrance
time `τ_A = hittingAfter X A 1`. -/
def HitsSetAlmostSurely (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (A : Set E) : Prop :=
  ∀ x : E, x ∉ A → (P x : Measure Ω) {ω | hittingAfter X A 1 ω < ⊤} = 1

-- Proof sketch: unfold `HitsSetAlmostSurely`; this is exactly the pointwise almost-sure finiteness
-- of the first entrance time into `A` from every starting state outside `A`.
/-- Hitting `A` almost surely means that `τ_A` is finite with probability `1` from every state in
`E \ A`. -/
theorem hitsSetAlmostSurely_iff (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (A : Set E) :
    HitsSetAlmostSurely P X A ↔
      ∀ x : E, x ∉ A → (P x : Measure Ω) {ω | hittingAfter X A 1 ω < ⊤} = 1 :=
  Iff.rfl

end EntranceTime

section KilledGreenFunction

variable [MeasurableSpace Ω]

/- Layering for Exercise 19.1.1:
- `source-facing`: `killedVisitCount` and `killedGreenFunction`, the intrinsic visit-count and
  Green-function objects for the chain killed on first entrance into `A`.
- `core/canonical`: `hittingAfter`, `stoppedValue`, and the Chapter 17 Green-function framework
  around expected visit counts.
- `bridge/view`: the finite-state real matrices below, obtained from the owner kernel
  `discreteMatrixKernel p` and from `killedGreenFunction` by taking singleton masses and
  `ENNReal.toReal`. -/

/-- The pathwise visit count of the chain killed on entering `A`. If the initial state `x` already
lies in `A`, only the time-`0` visit survives; if `x ∉ A` and `y ∈ A`, the only possible visit is
the entrance hit at time `hittingAfter X A 1`; if `x, y ∉ A`, this counts visits to `y` strictly
before the first entrance into `A`. -/
def killedVisitCount (X : ℕ → Ω → E) (A : Set E) (x y : E) (ω : Ω) : ℝ≥0∞ :=
  if x ∈ A then
    if x = y then 1 else 0
  else if y ∈ A then
    if hittingAfter X A 1 ω < ⊤ ∧ stoppedValue X (hittingAfter X A 1) ω = y then 1 else 0
  else
    Measure.count {n : ℕ | (n : ℕ∞) < hittingAfter X A 1 ω ∧ X n ω = y}

/-- The intrinsic Green function of the chain killed on first entrance into `A`, defined as the
expected value of `killedVisitCount`. -/
def killedGreenFunction
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (A : Set E) (x y : E) : ℝ≥0∞ :=
  ∫⁻ ω, killedVisitCount X A x y ω ∂(P x : Measure Ω)

-- Proof sketch: if `x ∈ A`, then `killedVisitCount` is definitionally the constant Kronecker-delta
-- pathwise count, so its expectation is the same delta value.
/-- If the chain starts inside `A`, the killed Green function is the Kronecker delta at the
starting point. -/
theorem killedGreenFunction_eq_kroneckerDelta_of_mem
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (A : Set E) {x y : E} (hx : x ∈ A) :
    killedGreenFunction P X A x y = if x = y then 1 else 0 := by
  -- Proof comment: once the starting point lies in `A`, the pathwise killed visit count is the
  -- constant Kronecker delta, so its expectation is the same constant.
  rw [killedGreenFunction]
  simp [killedVisitCount, hx]

-- Proof sketch: for `x ∉ A` and `y ∈ A`, the definition of `killedVisitCount` reduces pointwise
-- to the indicator of the event that the first entrance into `A` occurs at `y`; integrating that
-- indicator gives the corresponding entrance distribution.
/-- Helper for Exercise 19.1.1: the event that the first entrance into `A` occurs at `y` is
measurable. -/
private lemma killedFirstEntranceEvent_measurable
    [MeasurableSpace E] [DiscreteMeasurableSpace E]
    (X : ℕ → Ω → E) (A : Set E) (y : E) (hX : ∀ n : ℕ, Measurable (X n)) :
    MeasurableSet
      {ω | hittingAfter X A 1 ω < ⊤ ∧
          stoppedValue X (hittingAfter X A 1) ω = y} := by
  let τ : Ω → ℕ∞ := hittingAfter X A 1
  have hτ_le_meas : ∀ k : ℕ, MeasurableSet {ω | τ ω ≤ k} := by
    intro k
    -- Proof comment: `τ ≤ k` means that some time between `1` and `k` already lies in `A`, so
    -- this set is a countable union of measurable coordinate preimages.
    have hEq : {ω | τ ω ≤ k} = ⋃ j, ⋃ _ : j ∈ Set.Icc 1 k, X j ⁻¹' A := by
      ext ω
      simpa [τ] using
        (hittingAfter_le_iff (u := X) (s := A) (n := 1) (ω := ω) (i := k))
    simpa [hEq] using MeasurableSet.iUnion fun j =>
      MeasurableSet.iUnion fun _ =>
        (hX j) (show MeasurableSet A from MeasurableSet.of_discrete)
  let slice : ℕ → Set Ω := fun n ↦ {ω | τ ω = n + 1 ∧ X (n + 1) ω = y}
  have hslice_meas : ∀ n : ℕ, MeasurableSet (slice n) := by
    intro n
    have hτ_eq_meas : MeasurableSet {ω | τ ω = n + 1} := by
      -- Proof comment: in `ℕ∞`, equality with `n + 1` is the difference between the two lower
      -- sets `{τ ≤ n + 1}` and `{τ ≤ n}`.
      have hEq :
          {ω | τ ω = n + 1} = {ω | τ ω ≤ n + 1} \ {ω | τ ω ≤ n} := by
        ext ω
        constructor
        · intro hω
          have hω' : τ ω = n + 1 := by simpa using hω
          refine ⟨?_, ?_⟩
          · show τ ω ≤ n + 1
            simpa [hω']
          have hnot : ¬ ((n + 1 : ℕ∞) ≤ n) := by
            exact_mod_cast Nat.not_succ_le_self n
          · show ¬ τ ω ≤ n
            simpa [hω'] using hnot
        · intro hω
          by_cases htop : τ ω = ⊤
          · exfalso
            have hnot_top : ((n : ℕ∞) + 1) ≠ ⊤ := by
              intro h
              cases h
            exact hnot_top (by simpa [Set.mem_setOf_eq, htop] using hω.1)
          · lift τ ω to ℕ using htop with m hm
            have hm_le : m ≤ n + 1 := by
              have hm_le' : ((m : ℕ) : ℕ∞) ≤ n + 1 := by
                simpa [Set.mem_setOf_eq, hm] using hω.1
              exact_mod_cast hm_le'
            have hm_nle : ¬ m ≤ n := by
              have hm_nle' : ¬ (((m : ℕ) : ℕ∞) ≤ n) := by
                simpa [Set.mem_setOf_eq, hm] using hω.2
              exact_mod_cast hm_nle'
            have hm_eq : m = n + 1 := by omega
            simpa [hm_eq] using hm.symm
      rw [hEq]
      exact (hτ_le_meas (n + 1)).diff (hτ_le_meas n)
    -- Proof comment: each exact first-hit slice also records the value `X (n + 1)`, so the slice
    -- event is an intersection of two measurable sets.
    refine hτ_eq_meas.inter ?_
    change MeasurableSet (X (n + 1) ⁻¹' ({y} : Set E))
    exact (hX (n + 1)) (by simp)
  have hEq :
      {ω | τ ω < ⊤ ∧ stoppedValue X τ ω = y} = ⋃ n : ℕ, slice n := by
    ext ω
    constructor
    · intro hω
      have hτ_ne_top : τ ω ≠ ⊤ := ne_of_lt hω.1
      lift τ ω to ℕ using hτ_ne_top with m hm
      have hm_pos : 0 < m := by
        have hle : (1 : ℕ∞) ≤ τ ω := by
          simpa [τ] using (le_hittingAfter (u := X) (s := A) (n := 1) ω)
        have hm_one : 1 ≤ m := by
          have hm_one' : (1 : ℕ∞) ≤ m := by
            simpa [hm] using hle
          exact_mod_cast hm_one'
        exact Nat.succ_le_iff.mp hm_one
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm_pos.ne'
      have hτ_eq : τ ω = n + 1 := by
        simpa using hm.symm
      refine Set.mem_iUnion.2 ⟨n, ?_⟩
      refine ⟨hτ_eq, ?_⟩
      calc
        X (n + 1) ω = X (((n : ℕ∞) + 1).untopA) ω := by
          rfl
        _ = stoppedValue X τ ω := by
          simp [stoppedValue, hτ_eq]
        _ = y := hω.2
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨n, hn⟩
      refine ⟨?_, ?_⟩
      · rw [hn.1]
        simp
      · calc
          stoppedValue X τ ω = X (n + 1) ω := by
            rw [stoppedValue, hn.1]
            rfl
          _ = y := hn.2
  change MeasurableSet {ω | τ ω < ⊤ ∧ stoppedValue X τ ω = y}
  rw [hEq]
  exact MeasurableSet.iUnion hslice_meas

/-- If `x ∉ A` and `y ∈ A`, the killed Green function at `(x, y)` is the probability that the
first entrance into `A` occurs at `y`. -/
theorem killedGreenFunction_eq_firstEntranceMeasure
    [MeasurableSpace E] [DiscreteMeasurableSpace E]
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (A : Set E)
    {x y : E} (hX : ∀ n : ℕ, Measurable (X n)) (hx : x ∉ A) (hy : y ∈ A) :
    killedGreenFunction P X A x y =
      (P x : Measure Ω)
        {ω | hittingAfter X A 1 ω < ⊤ ∧
            stoppedValue X (hittingAfter X A 1) ω = y} := by
  have hmeas :
      MeasurableSet
        {ω | hittingAfter X A 1 ω < ⊤ ∧
            stoppedValue X (hittingAfter X A 1) ω = y} :=
    killedFirstEntranceEvent_measurable (X := X) (A := A) y hX
  -- Proof comment: for `x ∉ A` and `y ∈ A`, the killed visit count is exactly the indicator of
  -- the first-entrance event at `y`, so its lower integral is the measure of that event.
  rw [killedGreenFunction]
  simpa [killedVisitCount, hx, hy, Set.indicator] using
    (lintegral_indicator_one
      (μ := (P x : Measure Ω))
      (s := {ω | hittingAfter X A 1 ω < ⊤ ∧
        stoppedValue X (hittingAfter X A 1) ω = y}) hmeas)

end KilledGreenFunction

section MatrixBridge

variable [MeasurableSpace E] [DiscreteMeasurableSpace E]

/-- Bridge/view: the finite-state real matrix obtained from the owner kernel
`discreteMatrixKernel p` by killing rows indexed by `A`. -/
def killedKernelMatrixView (p : E → E → ℝ≥0∞) (A : Set E) : Matrix E E ℝ :=
  fun x y ↦ if x ∈ A then 0 else (((discreteMatrixKernel p) x) ({y} : Set E)).toReal

/-- Bridge/view: the real matrix of the owner kernel `discreteMatrixKernel p` restricted to the
state space `E \ A`. -/
def restrictedKernelMatrixView (p : E → E → ℝ≥0∞) (A : Set E) :
    Matrix (↥(Aᶜ)) (↥(Aᶜ)) ℝ :=
  fun x y ↦ (((discreteMatrixKernel p) x) ({(y : E)} : Set E)).toReal

-- Proof sketch: evaluate the kernel `discreteMatrixKernel p` on the singleton `{y}`; on a
-- discrete state space this singleton mass is exactly `p x y`, and the extra `if` kills the rows
-- indexed by `A`.
/-- Evaluating `killedKernelMatrixView` recovers the row-killed transition formula in finite-state
real-matrix coordinates. -/
theorem killedKernelMatrixView_apply
    (p : E → E → ℝ≥0∞) (A : Set E) (x y : E) :
    killedKernelMatrixView p A x y = if x ∈ A then 0 else (p x y).toReal := by
  -- Proof comment: the only extra structure in `killedKernelMatrixView` is the row-killing `if`;
  -- outside `A`, singleton evaluation of `discreteMatrixKernel p` gives the matrix entry.
  by_cases hx : x ∈ A
  · simp [killedKernelMatrixView, hx]
  · rw [killedKernelMatrixView, if_neg hx, if_neg hx]
    simpa using
      congrArg ENNReal.toReal
        (discreteMatrixKernel_apply_singleton (p := p) (x := y) (y := x))

-- Proof sketch: on `Aᶜ` there is no row-killing term, and the singleton mass of
-- `discreteMatrixKernel p` is exactly the original transition weight `p x y`.
/-- On the restricted state space `E \ A`, `restrictedKernelMatrixView` is the original transition
matrix written in real-valued coordinates. -/
theorem restrictedKernelMatrixView_apply
    (p : E → E → ℝ≥0∞) (A : Set E) (x y : ↥(Aᶜ)) :
    restrictedKernelMatrixView p A x y = (p x y).toReal := by
  -- Proof comment: on the restricted state space there is no killed-row branch, so singleton
  -- evaluation of the owner kernel directly returns the original transition weight.
  rw [restrictedKernelMatrixView]
  simpa using
    congrArg ENNReal.toReal
      (discreteMatrixKernel_apply_singleton (p := p) (x := (y : E)) (y := (x : E)))

end MatrixBridge

section

variable [MeasurableSpace E] [DiscreteMeasurableSpace E]
variable [Fintype E]
variable [MeasurableSpace Ω]
variable {p : E → E → ℝ≥0∞} {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
variable [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]

/-- Helper for Exercise 19.1.1: a one-step matrix realized by a Markov-process realization is
stochastic. -/
private lemma isStochasticMatrix_of_realization
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X] :
    IsStochasticMatrix p := by
  let hrealization := (inferInstance :
    IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X)
  letI : IsMarkovKernel ((fun n : ℕ ↦ discreteMatrixKernel p ^ n) 1) :=
    hrealization.semigroup.isMarkovKernel 1
  intro x
  -- Proof comment: the time-`1` marginal kernel of the realization is Markov, so its row mass on
  -- the full state space is `1`, and that full mass is exactly the row sum of `p`.
  calc
    ∑' y : E, p x y = discreteMatrixKernel p x Set.univ := by
      symm
      rw [discreteMatrixKernel_univ]
    _ = ((fun n : ℕ ↦ discreteMatrixKernel p ^ n) 1) x Set.univ := by
      simp
    _ = 1 := by
      simpa using (measure_univ : ((fun n : ℕ ↦ discreteMatrixKernel p ^ n) 1) x Set.univ = 1)

/-- Bridge/view: the finite-state real matrix obtained from the intrinsic killed Green function by
taking `ENNReal.toReal` entrywise. -/
def killedGreenMatrixView (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (A : Set E) :
    Matrix E E ℝ :=
  fun x y ↦ (killedGreenFunction P X A x y).toReal

/-- Helper for Exercise 19.1.1: rows indexed by `A` in the killed Green matrix bridge are already
the Kronecker delta rows. -/
private lemma killedGreenMatrixView_eq_kroneckerDelta_of_mem_local
    (A : Set E) {x y : E} (hx : x ∈ A) :
    killedGreenMatrixView P X A x y = if x = y then 1 else 0 := by
  -- Proof comment: the matrix bridge is defined entrywise from `killedGreenFunction`, so the
  -- boundary-row normalization transports directly through `ENNReal.toReal`.
  rw [killedGreenMatrixView,
    killedGreenFunction_eq_kroneckerDelta_of_mem (P := P) (X := X) (A := A) hx]
  split_ifs <;> simp

/-- Helper for Exercise 19.1.1: integrating a real-valued observable of `X n` under `P x`
matches the `n`-step kernel row of the local realization interface. -/
private lemma localMarkovRealization_integral_comp_transition_eq
    {g : E → ℝ} (x : E) (n : ℕ) :
    (P x : Measure Ω)[fun ω ↦ g (X n ω)] =
      ∫ z, g z ∂((discreteMatrixKernel p ^ n) x) := by
  let hReal :
      IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  have hXn : Measurable (X n) := hReal.measurable_process n
  -- Proof comment: rewrite the time-`n` marginal through the realization field `transition_eq`.
  rw [← hReal.transition_eq x n, integral_map]
  · exact hXn.aemeasurable
  · exact (Measurable.of_discrete : Measurable g).aestronglyMeasurable

/-- Helper for Exercise 19.1.1: if a deterministic-time history event already forces the current
state to be `y`, then intersecting it with a future singleton event factors through the
corresponding `m`-step transition mass from `y`. -/
private lemma measure_inter_prefix_stepEvent_eq_mul
    {x y z : E} {A : Set Ω} {n m : ℕ}
    (hA_meas : MeasurableSet[generatedFiltrationSpace X n] A)
    (hA_sub : A ⊆ {ω | X n ω = y}) :
    (P x : Measure Ω).real (A ∩ {ω | X (n + m) ω = z}) =
      (((discreteMatrixKernel p) ^ m) y ({z} : Set E)).toReal * (P x : Measure Ω).real A := by
  let μ : Measure Ω := P x
  let hReal :
      IsMarkovProcessRealization (fun k : ℕ ↦ discreteMatrixKernel p ^ k) P X := inferInstance
  let B : Set Ω := X (n + m) ⁻¹' ({z} : Set E)
  have hB_meas : MeasurableSet B := by
    simpa [B] using (hReal.measurable_process (n + m)) (MeasurableSet.singleton z)
  have hFiltration_le : generatedFiltrationSpace X n ≤ ‹MeasurableSpace Ω› := by
    refine iSup₂_le fun k hk ↦ ?_
    exact (hReal.measurable_process k).comap_le
  have hA_measAmbient : MeasurableSet A := by
    -- Proof comment: the deterministic history sigma-algebra up to time `n` sits inside the
    -- ambient measurable space, so the same event is ambient measurable.
    exact hFiltration_le _ hA_meas
  have hMarkovGenerated :
      μ⟦B | generatedFiltrationSpace X n⟧ =ᵐ[μ]
        fun ω ↦ (((discreteMatrixKernel p) ^ m) (X n ω)).real ({z} : Set E) := by
    simpa [μ, B, add_comm] using
      hReal.markov_property x (A := ({z} : Set E)) (MeasurableSet.singleton z) n m
  have hIndicatorIntegrable : Integrable (B.indicator (fun _ ↦ (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hB_meas
  -- Proof comment: integrate the Markov conditional-expectation identity over `A`, then freeze
  -- the transition row because `A` already pins down the state at time `n`.
  calc
    μ.real (A ∩ {ω | X (n + m) ω = z}) =
        ∫ ω in A, (μ⟦B | generatedFiltrationSpace X n⟧) ω ∂ μ := by
          rw [setIntegral_condExp hFiltration_le hIndicatorIntegrable hA_meas,
            ← integral_indicator hA_measAmbient]
          symm
          simpa [B, Set.indicator_indicator, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm,
            smul_eq_mul] using integral_indicator_const (1 : ℝ) (hA_measAmbient.inter hB_meas)
    _ = ∫ ω in A, (((discreteMatrixKernel p) ^ m) (X n ω)).real ({z} : Set E) ∂ μ := by
          exact integral_congr_ae hMarkovGenerated.restrict
    _ = ∫ _ in A, (((discreteMatrixKernel p) ^ m) y ({z} : Set E)).toReal ∂ μ := by
          refine integral_congr_ae ?_
          filter_upwards [self_mem_ae_restrict (μ := μ) (s := A) hA_measAmbient] with ω hω
          have hω : X n ω = y := hA_sub hω
          rw [hω]
          simp [Measure.real_def]
    _ = (((discreteMatrixKernel p) ^ m) y ({z} : Set E)).toReal * μ.real A := by
          rw [setIntegral_const, smul_eq_mul, mul_comm]

/-- Helper for Exercise 19.1.1: the deterministic-time prefix factorization is often more stable
in raw `Measure` form when the downstream event algebra still lives in `ℝ≥0∞`. -/
private lemma measure_inter_prefix_stepEvent_eq_mul_ennreal
    {x y z : E} {A : Set Ω} {n m : ℕ}
    (hA_meas : MeasurableSet[generatedFiltrationSpace X n] A)
    (hA_sub : A ⊆ {ω | X n ω = y}) :
    (P x : Measure Ω) (A ∩ {ω | X (n + m) ω = z}) =
      (((discreteMatrixKernel p) ^ m) y ({z} : Set E)) * (P x : Measure Ω) A := by
  have hstep :
      (P x : Measure Ω).real (A ∩ {ω | X (n + m) ω = z}) =
        (((discreteMatrixKernel p) ^ m) y ({z} : Set E)).toReal * (P x : Measure Ω).real A :=
    measure_inter_prefix_stepEvent_eq_mul (p := p) (P := P) (X := X) hA_meas hA_sub
  have hleft_ne_top :
      (P x : Measure Ω) (A ∩ {ω | X (n + m) ω = z}) ≠ ⊤ :=
    measure_ne_top _ _
  let hReal :
      IsMarkovProcessRealization (fun k : ℕ ↦ discreteMatrixKernel p ^ k) P X := inferInstance
  letI : IsMarkovKernel ((fun k : ℕ ↦ discreteMatrixKernel p ^ k) m) :=
    hReal.semigroup.isMarkovKernel m
  have hright_ne_top :
      (((discreteMatrixKernel p) ^ m) y ({z} : Set E)) * (P x : Measure Ω) A ≠ ⊤ := by
    exact ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
  -- Proof comment: both event masses are finite, so equality of their `toReal` values upgrades
  -- directly to equality in `ℝ≥0∞`.
  exact (ENNReal.toReal_eq_toReal_iff' hleft_ne_top hright_ne_top).mp <| by
    simpa [MeasureTheory.Measure.real_def, ENNReal.toReal_mul, measure_ne_top _ _, measure_ne_top _ _]
      using hstep

/-- Helper for Exercise 19.1.1: under `P x`, the time-`0` law of the realization is concentrated
at the start state `x`. -/
private lemma initialState_prob_eq_one_local
    (p : E → E → ℝ≥0∞)
    (hReal : IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X)
    (x : E) :
    (P x : Measure Ω) (X 0 ⁻¹' ({x} : Set E)) = 1 := by
  -- Proof comment: this is the singleton evaluation of the realization field `initial_eq`.
  have hInit := congrArg (fun ν : Measure E ↦ ν ({x} : Set E)) (hReal.initial_eq x)
  simpa [Measure.map_apply (hReal.measurable_process 0) (measurableSet_singleton x)] using hInit

/-- Helper for Exercise 19.1.1: under `P x`, the realized chain starts from `x` almost surely. -/
private lemma initialState_ae_eq_start_local (x : E)
    (hReal : IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance) :
    ∀ᵐ ω ∂(P x : Measure Ω), X 0 ω = x := by
  have hprob : (P x : Measure Ω) (X 0 ⁻¹' ({x} : Set E)) = 1 := by
    exact initialState_prob_eq_one_local (p := p) (P := P) (X := X) (hReal := hReal) x
  have hmeas : MeasurableSet (X 0 ⁻¹' ({x} : Set E)) := by
    simpa using (hReal.measurable_process 0) (measurableSet_singleton x)
  exact (mem_ae_iff_prob_eq_one hmeas).2 hprob

/-- Helper for Exercise 19.1.1: if the realized trajectory starts outside `A`, then the first
entrance time searched from `0` agrees with the first entrance time searched from `1`. -/
private lemma hittingAfter_zero_eq_one_of_not_mem_initial_local
    {A : Set E} {ω : Ω} (h0 : X 0 ω ∉ A) :
    hittingAfter X A 0 ω = hittingAfter X A 1 ω := by
  -- Proof comment: the time-`0` search cannot stop immediately once `X 0 ω ∉ A`.
  refine le_antisymm (hittingAfter_apply_mono (u := X) (s := A) (ω := ω) (by simp)) ?_
  by_cases htop : hittingAfter X A 0 ω = ⊤
  · have hle :
        hittingAfter X A 0 ω ≤ hittingAfter X A 1 ω :=
      hittingAfter_apply_mono (u := X) (s := A) (ω := ω) (by simp)
    simpa [htop] using hle
  · lift hittingAfter X A 0 ω to ℕ using htop with n hn
    have hn_ne_top : hittingAfter X A 0 ω ≠ ⊤ := by
      rw [← hn]
      simp
    have hidx : (hittingAfter X A 0 ω).untopA = n := by
      rw [← hn, WithTop.untopA_eq_untop (by simp)]
      exact (WithTop.untop_eq_iff (by simp)).2 rfl
    have hmem : X n ω ∈ A := by
      -- Proof comment: a finite first entrance time always lands inside the target set.
      simpa [hidx] using
        hittingAfter_mem_set_of_ne_top (u := X) (s := A) (n := 0) (ω := ω) hn_ne_top
    have hn_pos : 1 ≤ n := by
      by_contra hn_pos
      have hn_zero : n = 0 := by omega
      exact h0 (hn_zero ▸ hmem)
    simpa [hn] using
      hittingAfter_le_of_mem (u := X) (s := A) (n := 1) (ω := ω) hn_pos hmem

/-- Helper for Exercise 19.1.1: the discrete-time future path of `X` after `k` steps. -/
private def shiftedFuturePath (Y : ℕ → Ω → E) (k : ℕ) : Ω → ℕ → E :=
  fun ω n ↦ Y (n + k) ω

/-- Helper for Exercise 19.1.1: the canonical path-law kernel attached to the realization
`(P, X)`. -/
private def realizationPathKernel : Kernel E (ℕ → E) :=
  Kernel.ofFunOfCountable fun z ↦
    (P z : Measure Ω).map (fun ω : Ω ↦ fun n : ℕ ↦ X n ω)

/-- Helper for Exercise 19.1.1: the path-kernel time-`n` marginal is exactly the original
`n`-step transition row. -/
private lemma realizationPathKernel_transition
    (x : E) (n : ℕ) :
    transitionKernel (realizationPathKernel (P := P) (X := X)) n x = (discreteMatrixKernel p ^ n) x := by
  let hReal :
      IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  -- Proof comment: expand the explicit path-law kernel and read off the time-`n` marginal from
  -- the realization field `transition_eq`.
  rw [transitionKernel_apply]
  change
    Measure.map (fun ξ : ℕ → E ↦ ξ n)
      ((P x : Measure Ω).map (fun ω : Ω ↦ fun m : ℕ ↦ X m ω)) =
        (discreteMatrixKernel p ^ n) x
  rw [Measure.map_map]
  · simpa using hReal.transition_eq x n
  · exact measurable_pi_apply n
  · exact measurable_pi_lambda _ fun m ↦ hReal.measurable_process m

/-- Helper for Exercise 19.1.1: the canonical path-law kernel makes the realization into a
time-homogeneous Markov process on path space. -/
private lemma realizationPathKernel_isTimeHomogeneousMarkovProcess
    (hReal : IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance) :
    IsTimeHomogeneousMarkovProcess X P (realizationPathKernel (P := P) (X := X)) := by
  refine
    { measurable_process := hReal.measurable_process
      initial_state :=
        initialState_prob_eq_one_local (p := p) (P := P) (X := X) (hReal := hReal)
      path_law := ?_
      markov_property := ?_ }
  · intro x
    rfl
  · intro x A hA s t
    -- Proof comment: rewrite the owner transition kernel in the Markov property through the
    -- explicit path-law marginal just proved above.
    refine (hReal.markov_property x hA s t).trans ?_
    filter_upwards with ω
    rw [realizationPathKernel_transition (p := p) (P := P) (X := X) (x := X s ω) t]

/-- Helper for Exercise 19.1.1: the first `n` coordinates of the realized path started from time
`0`. -/
private def realizedTupleFromZero (Y : ℕ → Ω → E) (n : ℕ) : Ω → Fin n → E :=
  fun ω i ↦ Y i ω

/-- Helper for Exercise 19.1.1: the first `n` coordinates of the realized path started from time
`1`. -/
private def realizedTupleFromStep (Y : ℕ → Ω → E) (n : ℕ) : Ω → Fin n → E :=
  fun ω i ↦ Y (i + 1) ω

/-- Helper for Exercise 19.1.1: fixing a zero-start tuple of length `n + 2` is the same as
fixing the initial state together with the shifted tail tuple of length `n + 1`. -/
private lemma realizedTupleFromZero_preimage_singleton_eq_start_inter_stepTail
    (n : ℕ) (t : Fin (n + 2) → E) :
    (realizedTupleFromZero X (n + 2)) ⁻¹' ({t} : Set (Fin (n + 2) → E)) =
      X 0 ⁻¹' ({t 0} : Set E) ∩
        (realizedTupleFromStep X (n + 1)) ⁻¹'
          ({fun i : Fin (n + 1) ↦ t i.succ} : Set (Fin (n + 1) → E)) := by
  ext ω
  constructor
  · intro hω
    refine ⟨?_, ?_⟩
    · simpa [realizedTupleFromZero, Set.mem_preimage] using congrFun hω 0
    · change realizedTupleFromStep X (n + 1) ω = fun i : Fin (n + 1) ↦ t i.succ
      funext i
      simpa [realizedTupleFromZero, realizedTupleFromStep] using congrFun hω i.succ
  · rintro ⟨h0, htail⟩
    change realizedTupleFromZero X (n + 2) ω = t
    funext i
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
    · simpa [realizedTupleFromZero, Set.mem_preimage] using h0
    · simpa [realizedTupleFromStep] using congrFun htail j

/-- Helper for Exercise 19.1.1: under the start law `P (t 0)`, the zero-start tuple singleton
mass equals the shifted-tail tuple singleton mass because the initial state is pinned almost
surely. -/
private lemma zeroTupleSingletonMeasure_eq_stepTailMeasure
    (n : ℕ) (t : Fin (n + 2) → E)
    (hReal : IsMarkovProcessRealization (fun k : ℕ ↦ discreteMatrixKernel p ^ k) P X := inferInstance) :
    (P (t 0) : Measure Ω) ((realizedTupleFromZero X (n + 2)) ⁻¹' ({t} : Set (Fin (n + 2) → E))) =
      (P (t 0) : Measure Ω)
        ((realizedTupleFromStep X (n + 1)) ⁻¹'
          ({fun i : Fin (n + 1) ↦ t i.succ} : Set (Fin (n + 1) → E))) := by
  let startEvent : Set Ω := X 0 ⁻¹' ({t 0} : Set E)
  let tailEvent : Set Ω :=
    (realizedTupleFromStep X (n + 1)) ⁻¹'
      ({fun i : Fin (n + 1) ↦ t i.succ} : Set (Fin (n + 1) → E))
  have hsplit :
      (realizedTupleFromZero X (n + 2)) ⁻¹' ({t} : Set (Fin (n + 2) → E)) =
        startEvent ∩ tailEvent := by
    simpa [startEvent, tailEvent] using
      realizedTupleFromZero_preimage_singleton_eq_start_inter_stepTail
        (X := X) n t
  have hstart_ae : ∀ᵐ ω ∂(P (t 0) : Measure Ω), ω ∈ startEvent := by
    simpa [startEvent, Set.mem_preimage] using
      initialState_ae_eq_start_local (p := p) (P := P) (X := X) (x := t 0) (hReal := hReal)
  have htail_ae :
      (startEvent ∩ tailEvent : Set Ω) =ᵐ[(P (t 0) : Measure Ω)] tailEvent := by
    -- Proof comment: the start event has full measure under `P (t 0)`, so intersecting with it
    -- does not change the tail-tuple event.
    filter_upwards [hstart_ae] with ω hω
    apply propext
    constructor
    · intro hω'
      exact hω'.2
    · intro hω'
      exact ⟨hω, hω'⟩
  rw [hsplit]
  exact measure_congr htail_ae

/-- Helper for Exercise 19.1.1: the time-`1, ..., n` tuple is measurable on the history through
time `n`. -/
private lemma measurable_realizedTupleFromStep_filtration
    (n : ℕ) :
    Measurable[generatedFiltrationSpace X n] (realizedTupleFromStep X n) := by
  rw [@measurable_pi_iff]
  intro i
  refine Measurable.of_comap_le ?_
  exact
    le_iSup_of_le (i + 1) <|
      le_iSup_of_le (by exact_mod_cast i.2) le_rfl

/-- Helper for Exercise 19.1.1: the time-`0, ..., n` tuple is measurable on the history through
time `n`. -/
private lemma measurable_realizedTupleFromZero_filtration
    (n : ℕ) :
    Measurable[generatedFiltrationSpace X n] (realizedTupleFromZero X (n + 1)) := by
  rw [@measurable_pi_iff]
  intro i
  refine Measurable.of_comap_le ?_
  -- Proof comment: the `i`-th coordinate of the length-`n + 1` prefix occurs no later than time
  -- `n`, so it belongs to the generated history filtration at time `n`.
  exact
    le_iSup_of_le i <|
      le_iSup_of_le (Nat.le_of_lt_succ i.2) le_rfl

/-- Helper for Exercise 19.1.1: a shifted tuple singleton factors through its final one-step
transition once the earlier shifted prefix is fixed. -/
private lemma shiftedTupleSingletonMeasure_lastStepFactor
    (x : E) (n : ℕ) (t : Fin (n + 2) → E)
    (hReal : IsMarkovProcessRealization (fun k : ℕ ↦ discreteMatrixKernel p ^ k) P X := inferInstance) :
    (P x : Measure Ω) ((realizedTupleFromStep X (n + 2)) ⁻¹' ({t} : Set (Fin (n + 2) → E))) =
      p (t (Fin.castSucc (Fin.last n))) (t (Fin.last (n + 1))) *
        (P x : Measure Ω)
          ((realizedTupleFromStep X (n + 1)) ⁻¹'
            ({fun i : Fin (n + 1) ↦ t i.castSucc} : Set (Fin (n + 1) → E))) := by
  let prefixEvent : Set Ω :=
    (realizedTupleFromStep X (n + 1)) ⁻¹'
      ({fun i : Fin (n + 1) ↦ t i.castSucc} : Set (Fin (n + 1) → E))
  have hprefix_meas :
      MeasurableSet[generatedFiltrationSpace X (n + 1)] prefixEvent := by
    -- Proof comment: the shifted prefix event is a singleton fiber of the measurable
    -- `(X 1, ..., X (n + 1))` tuple map.
    simpa [prefixEvent] using
      (measurable_realizedTupleFromStep_filtration (X := X) (n := n + 1))
        (measurableSet_singleton (fun i : Fin (n + 1) ↦ t i.castSucc))
  have hprefix_sub :
      prefixEvent ⊆ {ω | X (n + 1) ω = t (Fin.castSucc (Fin.last n))} := by
    intro ω hω
    have hprefix :
        realizedTupleFromStep X (n + 1) ω = fun i : Fin (n + 1) ↦ t i.castSucc := by
      simpa [prefixEvent, Set.mem_preimage] using hω
    -- Proof comment: on the prefix singleton, the final coordinate of the prefix is prescribed.
    simpa [realizedTupleFromStep] using congrFun hprefix (Fin.last n)
  have hsplit :
      (realizedTupleFromStep X (n + 2)) ⁻¹' ({t} : Set (Fin (n + 2) → E)) =
        prefixEvent ∩ {ω | X (n + 2) ω = t (Fin.last (n + 1))} := by
    ext ω
    constructor
    · intro hω
      refine ⟨?_, ?_⟩
      · change realizedTupleFromStep X (n + 1) ω = fun i : Fin (n + 1) ↦ t i.castSucc
        funext i
        simpa [realizedTupleFromStep] using congrFun hω i.castSucc
      · simpa [realizedTupleFromStep, Set.mem_preimage] using congrFun hω (Fin.last (n + 1))
    · rintro ⟨hprefix, hlast⟩
      change realizedTupleFromStep X (n + 2) ω = t
      funext i
      cases i using Fin.lastCases with
      | last =>
          simpa [realizedTupleFromStep, Set.mem_preimage] using hlast
      | cast j =>
          have hprefix' :
              realizedTupleFromStep X (n + 1) ω = fun i : Fin (n + 1) ↦ t i.castSucc := by
            simpa [prefixEvent, Set.mem_preimage] using hprefix
          simpa [realizedTupleFromStep] using congrFun hprefix' j
  -- Proof comment: after normalizing the full tuple singleton into a history event at time
  -- `n + 1` plus the last coordinate, the one-step Markov factorization applies directly.
  calc
    (P x : Measure Ω) ((realizedTupleFromStep X (n + 2)) ⁻¹' ({t} : Set (Fin (n + 2) → E)))
        = (P x : Measure Ω)
            (prefixEvent ∩ {ω | X (n + 2) ω = t (Fin.last (n + 1))}) := by
              rw [hsplit]
    _ = (((discreteMatrixKernel p) ^ 1) (t (Fin.castSucc (Fin.last n)))
          ({t (Fin.last (n + 1))} : Set E)) * (P x : Measure Ω) prefixEvent := by
            exact
              measure_inter_prefix_stepEvent_eq_mul_ennreal
                (p := p) (P := P) (X := X)
                (A := prefixEvent) (x := x)
                (y := t (Fin.castSucc (Fin.last n)))
                (z := t (Fin.last (n + 1)))
                (n := n + 1) (m := 1) hprefix_meas hprefix_sub
    _ = (discreteMatrixKernel p) (t (Fin.castSucc (Fin.last n)))
          ({t (Fin.last (n + 1))} : Set E) * (P x : Measure Ω) prefixEvent := by
          simp
    _ = p (t (Fin.castSucc (Fin.last n))) (t (Fin.last (n + 1))) * (P x : Measure Ω) prefixEvent := by
          rw [discreteMatrixKernel_apply_singleton]
    _ = p (t (Fin.castSucc (Fin.last n))) (t (Fin.last (n + 1))) *
          (P x : Measure Ω)
            ((realizedTupleFromStep X (n + 1)) ⁻¹'
              ({fun i : Fin (n + 1) ↦ t i.castSucc} : Set (Fin (n + 1) → E))) := by
          rfl

/-- Helper for Exercise 19.1.1: the length-one shifted tuple singleton is just the first-step
transition mass out of the start state. -/
private lemma shiftedTupleSingletonMeasure_base
    (x : E) (t : Fin 1 → E)
    (hReal : IsMarkovProcessRealization (fun k : ℕ ↦ discreteMatrixKernel p ^ k) P X := inferInstance) :
    (P x : Measure Ω) ((realizedTupleFromStep X 1) ⁻¹' ({t} : Set (Fin 1 → E))) =
      p x (t 0) * (P (t 0) : Measure Ω)
        ((realizedTupleFromZero X 1) ⁻¹' ({t} : Set (Fin 1 → E))) := by
  let stepEvent : Set Ω := {ω | X 1 ω = t 0}
  let startEvent : Set Ω := X 0 ⁻¹' ({t 0} : Set E)
  have hstep :
      (realizedTupleFromStep X 1) ⁻¹' ({t} : Set (Fin 1 → E)) = stepEvent := by
    ext ω
    constructor
    · intro hω
      simpa [stepEvent, realizedTupleFromStep, Set.mem_preimage] using congrFun hω 0
    · intro hω
      change realizedTupleFromStep X 1 ω = t
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      simpa [stepEvent, realizedTupleFromStep, Set.mem_preimage] using hω
  have hzero :
      (realizedTupleFromZero X 1) ⁻¹' ({t} : Set (Fin 1 → E)) = startEvent := by
    ext ω
    constructor
    · intro hω
      simpa [startEvent, realizedTupleFromZero, Set.mem_preimage] using congrFun hω 0
    · intro hω
      change realizedTupleFromZero X 1 ω = t
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      simpa [startEvent, realizedTupleFromZero, Set.mem_preimage] using hω
  have htrans :
      (P x : Measure Ω) stepEvent = p x (t 0) := by
    have hstepLaw := congrArg (fun ν : Measure E ↦ ν ({t 0} : Set E)) (hReal.transition_eq x 1)
    calc
      (P x : Measure Ω) stepEvent
          = ((P x : Measure Ω).map (X 1)) ({t 0} : Set E) := by
              symm
              rw [Measure.map_apply (hReal.measurable_process 1) (measurableSet_singleton (t 0))]
              rfl
      _ = ((discreteMatrixKernel p ^ 1) x) ({t 0} : Set E) := hstepLaw
      _ = (discreteMatrixKernel p) x ({t 0} : Set E) := by simp
      _ = p x (t 0) := by rw [discreteMatrixKernel_apply_singleton]
  have hstart :
      (P (t 0) : Measure Ω) startEvent = 1 := by
    simpa [startEvent] using
      initialState_prob_eq_one_local (p := p) (P := P) (X := X) (hReal := hReal) (t 0)
  -- Proof comment: for a one-coordinate shifted tuple, the left-hand side is exactly the first
  -- transition probability, and the restarted zero tuple has mass `1` because the start is fixed.
  calc
    (P x : Measure Ω) ((realizedTupleFromStep X 1) ⁻¹' ({t} : Set (Fin 1 → E)))
        = (P x : Measure Ω) stepEvent := by rw [hstep]
    _ = p x (t 0) := htrans
    _ = p x (t 0) * 1 := by simp
    _ = p x (t 0) * (P (t 0) : Measure Ω) startEvent := by rw [hstart]
    _ = p x (t 0) * (P (t 0) : Measure Ω)
          ((realizedTupleFromZero X 1) ⁻¹' ({t} : Set (Fin 1 → E))) := by
            rw [hzero]

/-- Helper for Exercise 19.1.1: a shifted tuple singleton factors into the first-step transition
mass and the restarted zero-start tuple singleton mass. -/
private lemma shiftedTupleSingletonMeasure_eq_mul_restartMass
    (x : E) :
    ∀ n : ℕ, ∀ t : Fin (n + 1) → E,
      (P x : Measure Ω) ((realizedTupleFromStep X (n + 1)) ⁻¹' ({t} : Set (Fin (n + 1) → E))) =
        p x (t 0) * (P (t 0) : Measure Ω)
          ((realizedTupleFromZero X (n + 1)) ⁻¹' ({t} : Set (Fin (n + 1) → E))) := by
  have hReal :
      IsMarkovProcessRealization (fun k : ℕ ↦ discreteMatrixKernel p ^ k) P X := inferInstance
  intro n
  induction n with
  | zero =>
      intro t
      -- Proof comment: the length-one tuple is exactly the already isolated base case.
      simpa using
        shiftedTupleSingletonMeasure_base
          (p := p) (P := P) (X := X) (x := x) t
  | succ n ih =>
      intro t
      set prefixTuple : Fin (n + 1) → E := fun i ↦ t i.castSucc
      have hstepFactor :
          (P x : Measure Ω) ((realizedTupleFromStep X (n + 2)) ⁻¹' ({t} : Set (Fin (n + 2) → E))) =
            p (t (Fin.castSucc (Fin.last n))) (t (Fin.last (n + 1))) *
              (P x : Measure Ω)
                ((realizedTupleFromStep X (n + 1)) ⁻¹' ({prefixTuple} : Set (Fin (n + 1) → E))) := by
        simpa [prefixTuple] using
          shiftedTupleSingletonMeasure_lastStepFactor
            (p := p) (P := P) (X := X) (x := x) (n := n) t
      have hprefix :
          (P x : Measure Ω) ((realizedTupleFromStep X (n + 1)) ⁻¹' ({prefixTuple} : Set (Fin (n + 1) → E))) =
            p x (t 0) * (P (t 0) : Measure Ω)
              ((realizedTupleFromZero X (n + 1)) ⁻¹' ({prefixTuple} : Set (Fin (n + 1) → E))) := by
        simpa [prefixTuple] using ih prefixTuple
      have hrestart :
          (P (t 0) : Measure Ω) ((realizedTupleFromZero X (n + 2)) ⁻¹' ({t} : Set (Fin (n + 2) → E))) =
            p (t (Fin.castSucc (Fin.last n))) (t (Fin.last (n + 1))) *
              (P (t 0) : Measure Ω)
                ((realizedTupleFromZero X (n + 1)) ⁻¹' ({prefixTuple} : Set (Fin (n + 1) → E))) := by
        cases n with
        | zero =>
            set tail : Fin 1 → E := fun i ↦ t i.succ
            have hfull :
                (P (t 0) : Measure Ω)
                    ((realizedTupleFromZero X 2) ⁻¹' ({t} : Set (Fin 2 → E))) =
                  (P (t 0) : Measure Ω)
                    ((realizedTupleFromStep X 1) ⁻¹' ({tail} : Set (Fin 1 → E))) := by
              simpa [tail] using
                zeroTupleSingletonMeasure_eq_stepTailMeasure
                  (p := p) (P := P) (X := X) (n := 0) t
            have htail :
                (P (t 0) : Measure Ω)
                    ((realizedTupleFromStep X 1) ⁻¹' ({tail} : Set (Fin 1 → E))) =
                  p (t 0) (t 1) * (P (t 1) : Measure Ω)
                    ((realizedTupleFromZero X 1) ⁻¹' ({tail} : Set (Fin 1 → E))) := by
              simpa [tail] using
                shiftedTupleSingletonMeasure_base
                  (p := p) (P := P) (X := X) (x := t 0) tail
            have htailZero :
                (realizedTupleFromZero X 1) ⁻¹' ({tail} : Set (Fin 1 → E)) =
                  X 0 ⁻¹' ({t 1} : Set E) := by
              ext ω
              constructor
              · intro hω
                simpa [tail, realizedTupleFromZero, Set.mem_preimage] using congrFun hω 0
              · intro hω
                change realizedTupleFromZero X 1 ω = tail
                funext i
                have hi : i = 0 := Subsingleton.elim _ _
                subst hi
                simpa [tail, realizedTupleFromZero, Set.mem_preimage] using hω
            have htailStart :
                (P (t 1) : Measure Ω)
                    ((realizedTupleFromZero X 1) ⁻¹' ({tail} : Set (Fin 1 → E))) = 1 := by
              rw [htailZero]
              simpa using
                initialState_prob_eq_one_local
                  (p := p) (P := P) (X := X) (hReal := hReal) (t 1)
            have hprefixZero :
                (realizedTupleFromZero X 1) ⁻¹' ({prefixTuple} : Set (Fin 1 → E)) =
                  X 0 ⁻¹' ({t 0} : Set E) := by
              ext ω
              constructor
              · intro hω
                simpa [prefixTuple, realizedTupleFromZero, Set.mem_preimage] using congrFun hω 0
              · intro hω
                change realizedTupleFromZero X 1 ω = prefixTuple
                funext i
                have hi : i = 0 := Subsingleton.elim _ _
                subst hi
                simpa [prefixTuple, realizedTupleFromZero, Set.mem_preimage] using hω
            have hprefixStart :
                (P (t 0) : Measure Ω)
                    ((realizedTupleFromZero X 1) ⁻¹' ({prefixTuple} : Set (Fin 1 → E))) = 1 := by
              rw [hprefixZero]
              simpa using
                initialState_prob_eq_one_local
                  (p := p) (P := P) (X := X) (hReal := hReal) (t 0)
            -- Proof comment: for tuples of length two, pin the restarted start state and reduce
            -- the full zero tuple to the one-step tail singleton.
            calc
              (P (t 0) : Measure Ω)
                  ((realizedTupleFromZero X 2) ⁻¹' ({t} : Set (Fin 2 → E)))
                  =
                  (P (t 0) : Measure Ω)
                    ((realizedTupleFromStep X 1) ⁻¹' ({tail} : Set (Fin 1 → E))) := hfull
              _ = p (t 0) (t 1) * (P (t 1) : Measure Ω)
                    ((realizedTupleFromZero X 1) ⁻¹' ({tail} : Set (Fin 1 → E))) := htail
              _ = p (t 0) (t 1) * 1 := by rw [htailStart]
              _ = p (t 0) (t 1) * (P (t 0) : Measure Ω)
                    ((realizedTupleFromZero X 1) ⁻¹' ({prefixTuple} : Set (Fin 1 → E))) := by
                      rw [hprefixStart]
        | succ m =>
            set tail : Fin (m + 2) → E := fun i ↦ t i.succ
            set tailPrefixTuple : Fin (m + 1) → E := fun i ↦ prefixTuple i.succ
            have hfull :
                (P (t 0) : Measure Ω)
                    ((realizedTupleFromZero X (m + 3)) ⁻¹' ({t} : Set (Fin (m + 3) → E))) =
                  (P (t 0) : Measure Ω)
                    ((realizedTupleFromStep X (m + 2)) ⁻¹' ({tail} : Set (Fin (m + 2) → E))) := by
              simpa [tail] using
                zeroTupleSingletonMeasure_eq_stepTailMeasure
                  (p := p) (P := P) (X := X) (n := m + 1) t
            have htailStep :
                (P (t 0) : Measure Ω)
                    ((realizedTupleFromStep X (m + 2)) ⁻¹' ({tail} : Set (Fin (m + 2) → E))) =
                  p (t (Fin.castSucc (Fin.last (m + 1)))) (t (Fin.last (m + 2))) *
                    (P (t 0) : Measure Ω)
                      ((realizedTupleFromStep X (m + 1)) ⁻¹'
                        ({tailPrefixTuple} : Set (Fin (m + 1) → E))) := by
              simpa [tail, tailPrefixTuple] using
                shiftedTupleSingletonMeasure_lastStepFactor
                  (p := p) (P := P) (X := X) (x := t 0) (n := m) tail
            have hprefixZero :
                (P (t 0) : Measure Ω)
                    ((realizedTupleFromZero X (m + 2)) ⁻¹' ({prefixTuple} : Set (Fin (m + 2) → E))) =
                  (P (t 0) : Measure Ω)
                    ((realizedTupleFromStep X (m + 1)) ⁻¹'
                      ({tailPrefixTuple} : Set (Fin (m + 1) → E))) := by
              simpa [prefixTuple, tailPrefixTuple] using
                zeroTupleSingletonMeasure_eq_stepTailMeasure
                  (p := p) (P := P) (X := X) (n := m) prefixTuple
            -- Proof comment: for longer tuples, reduce both the full restarted tuple and the
            -- restarted prefix to the same shifted tail-prefix singleton, then compare the common
            -- last-step factor.
            calc
              (P (t 0) : Measure Ω)
                  ((realizedTupleFromZero X (m + 3)) ⁻¹' ({t} : Set (Fin (m + 3) → E)))
                  =
                  (P (t 0) : Measure Ω)
                    ((realizedTupleFromStep X (m + 2)) ⁻¹' ({tail} : Set (Fin (m + 2) → E))) := hfull
              _ = p (t (Fin.castSucc (Fin.last (m + 1)))) (t (Fin.last (m + 2))) *
                    (P (t 0) : Measure Ω)
                      ((realizedTupleFromStep X (m + 1)) ⁻¹'
                        ({tailPrefixTuple} : Set (Fin (m + 1) → E))) := htailStep
              _ = p (t (Fin.castSucc (Fin.last (m + 1)))) (t (Fin.last (m + 2))) *
                    (P (t 0) : Measure Ω)
                      ((realizedTupleFromZero X (m + 2)) ⁻¹' ({prefixTuple} : Set (Fin (m + 2) → E))) := by
                        rw [hprefixZero]
      -- Proof comment: factor the original shifted tuple through its last step, apply the
      -- induction hypothesis to the shifted prefix, and identify the restarted zero tuple by the
      -- matching restarted recursion.
      calc
        (P x : Measure Ω) ((realizedTupleFromStep X (n + 2)) ⁻¹' ({t} : Set (Fin (n + 2) → E)))
            =
            p (t (Fin.castSucc (Fin.last n))) (t (Fin.last (n + 1))) *
              (P x : Measure Ω)
                ((realizedTupleFromStep X (n + 1)) ⁻¹' ({prefixTuple} : Set (Fin (n + 1) → E))) := hstepFactor
        _ =
            p (t (Fin.castSucc (Fin.last n))) (t (Fin.last (n + 1))) *
              (p x (t 0) * (P (t 0) : Measure Ω)
                ((realizedTupleFromZero X (n + 1)) ⁻¹' ({prefixTuple} : Set (Fin (n + 1) → E)))) := by
                  rw [hprefix]
        _ =
            p x (t 0) *
              (p (t (Fin.castSucc (Fin.last n))) (t (Fin.last (n + 1))) *
                (P (t 0) : Measure Ω)
                  ((realizedTupleFromZero X (n + 1)) ⁻¹' ({prefixTuple} : Set (Fin (n + 1) → E)))) := by
                    ring_nf
        _ =
            p x (t 0) * (P (t 0) : Measure Ω)
              ((realizedTupleFromZero X (n + 2)) ⁻¹' ({t} : Set (Fin (n + 2) → E))) := by
                rw [hrestart]

/-- Helper for Exercise 19.1.1: the path-space event that the coordinate process first enters `A`
from time `0` at the state `y`. -/
private def firstEntrancePathEventFromZero (A : Set E) (y : E) : Set (ℕ → E) :=
  {ξ | y ∈ A ∧ ∃ n : ℕ, (∀ m < n, ξ m ∉ A) ∧ ξ n = y}

/-- Helper for Exercise 19.1.1: a finite prefix-avoidance condition on path space is measurable. -/
private lemma avoidBeforePathEvent_measurable
    (A : Set E) :
    ∀ n : ℕ, MeasurableSet {ξ : ℕ → E | ∀ m < n, ξ m ∉ A}
  | 0 => by
      simp
  | n + 1 => by
      have hEq :
          {ξ : ℕ → E | ∀ m < n + 1, ξ m ∉ A} =
            {ξ : ℕ → E | ∀ m < n, ξ m ∉ A} ∩ {ξ : ℕ → E | ξ n ∉ A} := by
        ext ξ
        constructor
        · intro hξ
          refine ⟨?_, ?_⟩
          · intro m hm
            exact hξ m (Nat.lt_succ_of_lt hm)
          · exact hξ n (Nat.lt_succ_self n)
        · intro hξ m hm
          rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hm | rfl
          · exact hξ.1 m hm
          · exact hξ.2
      -- Proof comment: split the length-`n + 1` avoidance event into the length-`n` prefix
      -- avoidance and the single coordinate condition at time `n`.
      rw [hEq]
      refine (avoidBeforePathEvent_measurable A n).inter ?_
      change MeasurableSet (((fun ξ : ℕ → E ↦ ξ n) ⁻¹' Aᶜ))
      exact (measurable_pi_apply n) (by simpa using (MeasurableSet.of_discrete : MeasurableSet A))

/-- Helper for Exercise 19.1.1: a finite outside-`A` prefix through time `n` is measurable. -/
private lemma avoidThroughPathEvent_measurable
    (A : Set E) (n : ℕ) :
    MeasurableSet {ξ : ℕ → E | ∀ m ≤ n, ξ m ∉ A} := by
  have hEq :
      {ξ : ℕ → E | ∀ m ≤ n, ξ m ∉ A} = {ξ : ℕ → E | ∀ m < n + 1, ξ m ∉ A} := by
    ext ξ
    simp
  -- Proof comment: rewrite the closed prefix condition as the strict prefix of length `n + 1`.
  rw [hEq]
  exact avoidBeforePathEvent_measurable (A := A) (n + 1)

/-- Helper for Exercise 19.1.1: the first-entrance path event is exactly the finite-coordinate
description "stay outside `A` before time `n` and equal `y` at time `n`". -/
private lemma firstEntrancePathEventFromZero_coordSpec
    (A : Set E) (y : E) {ξ : ℕ → E} :
    ξ ∈ firstEntrancePathEventFromZero (A := A) y ↔
      y ∈ A ∧ ∃ n : ℕ, (∀ m < n, ξ m ∉ A) ∧ ξ n = y :=
  Iff.rfl

/-- Helper for Exercise 19.1.1: the shifted first-entrance event on path space is measurable. -/
private lemma firstEntrancePathEventFromZero_measurable
    (A : Set E) (y : E) :
    MeasurableSet (firstEntrancePathEventFromZero (A := A) y) := by
  by_cases hy : y ∈ A
  · have hEq :
        firstEntrancePathEventFromZero (A := A) y =
          ⋃ n : ℕ, ({ξ : ℕ → E | ∀ m < n, ξ m ∉ A} ∩ {ξ : ℕ → E | ξ n = y}) := by
        ext ξ
        simp [firstEntrancePathEventFromZero, hy, and_left_comm, and_assoc]
    -- Proof comment: when `y ∈ A`, the first-entrance event is a countable union of finite
    -- coordinate conditions.
    rw [hEq]
    refine MeasurableSet.iUnion fun n ↦ ?_
    refine (avoidBeforePathEvent_measurable (A := A) n).inter ?_
    change MeasurableSet (((fun ξ : ℕ → E ↦ ξ n) ⁻¹' ({y} : Set E)))
    exact (measurable_pi_apply n) (measurableSet_singleton y)
  · have hEq : firstEntrancePathEventFromZero (A := A) y = ∅ := by
      ext ξ
      simp [firstEntrancePathEventFromZero, hy]
    rw [hEq]
    simp

/-- Helper for Exercise 19.1.1: shifting the path by one step turns the first-entrance event from
time `0` on path space into the original first-entrance event from time `1`. -/
private lemma futurePath_mem_firstEntrancePathEventFromZero_iff
    (A : Set E) {y : E} {ω : Ω} :
    shiftedFuturePath X 1 ω ∈ firstEntrancePathEventFromZero (A := A) y ↔
      hittingAfter X A 1 ω < ⊤ ∧ stoppedValue X (hittingAfter X A 1) ω = y := by
  constructor
  · intro hω
    rcases hω with ⟨hyA, n, havoid, hxy⟩
    have hxy' : X (n + 1) ω = y := by
      simpa [shiftedFuturePath] using hxy
    have hXhit : X (n + 1) ω ∈ A := by
      simpa [hxy'] using hyA
    have hτ_le : hittingAfter X A 1 ω ≤ n + 1 := by
      exact
        hittingAfter_le_of_mem (u := X) (s := A) (n := 1) (ω := ω)
          (Nat.succ_le_succ (Nat.zero_le n)) hXhit
    have hτ_ge : n + 1 ≤ hittingAfter X A 1 ω := by
      by_contra hlt
      have hlt' : hittingAfter X A 1 ω < n + 1 := lt_of_not_ge hlt
      rcases (hittingAfter_lt_iff (u := X) (s := A) (n := 1) (ω := ω) (i := n + 1)).1 hlt' with
        ⟨j, hj, hjA⟩
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hj.1)
      have hk_lt : k < n := by
        simpa using hj.2
      have hk_not_mem : X (k + 1) ω ∉ A := by
        simpa [shiftedFuturePath] using havoid k hk_lt
      exact hk_not_mem hjA
    have hτ_eq : hittingAfter X A 1 ω = n + 1 := le_antisymm hτ_le hτ_ge
    have hτ_idx : (hittingAfter X A 1 ω).untopA = n + 1 := by
      rw [hτ_eq, WithTop.untopA_eq_untop (by simp)]
      exact (WithTop.untop_eq_iff (by simp)).2 rfl
    refine ⟨lt_of_le_of_lt hτ_le (by simp), ?_⟩
    -- Proof comment: once the first positive hit time is identified with `n + 1`, the stopped
    -- value is the corresponding coordinate `X (n + 1) ω`.
    rw [stoppedValue, hτ_idx]
    exact hxy
  · rintro ⟨hτ_fin, hstop⟩
    have hτ_ne_top : hittingAfter X A 1 ω ≠ ⊤ := hτ_fin.ne
    lift hittingAfter X A 1 ω to ℕ using hτ_ne_top with m hm
    have hm_pos : 0 < m := by
      have hτ_ge : (1 : ℕ∞) ≤ hittingAfter X A 1 ω :=
        le_hittingAfter (u := X) (s := A) (n := 1) ω
      have hm_ge_one : 1 ≤ m := by
        have hge_m : (1 : ℕ∞) ≤ (m : ℕ∞) := by
          exact le_of_le_of_eq hτ_ge hm.symm
        exact_mod_cast hge_m
      exact Nat.succ_le_iff.mp hm_ge_one
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm_pos.ne'
    have hτ_eq : hittingAfter X A 1 ω = n + 1 := by
      simpa using hm.symm
    have hτ_idx : (hittingAfter X A 1 ω).untopA = n + 1 := by
      rw [hτ_eq, WithTop.untopA_eq_untop (by simp)]
      exact (WithTop.untop_eq_iff (by simp)).2 rfl
    have hyA : y ∈ A := by
      have hτ_ne_top' : hittingAfter X A 1 ω ≠ ⊤ := by
        rw [hτ_eq]
        simp
      have hhit_mem : X (n + 1) ω ∈ A := by
        simpa [hτ_eq, hτ_idx] using
          hittingAfter_mem_set_of_ne_top (u := X) (s := A) (n := 1) (ω := ω) hτ_ne_top'
      have hxy : X (n + 1) ω = y := by
        calc
          X (n + 1) ω = stoppedValue X (hittingAfter X A 1) ω := by
            rw [stoppedValue, hτ_idx]
          _ = y := hstop
      exact hxy ▸ hhit_mem
    refine ⟨hyA, n, ?_, ?_⟩
    · intro k hk
      have hk_lt_τ : (k + 1 : ℕ∞) < hittingAfter X A 1 ω := by
        rw [hτ_eq]
        change ((k : ℕ∞) + 1) < ((n : ℕ∞) + 1)
        simpa [Nat.cast_add] using
          (WithTop.coe_lt_coe.2 (Nat.succ_lt_succ hk))
      -- Proof comment: every earlier positive-time coordinate lies strictly before the first hit,
      -- so it must stay outside `A`.
      exact
        notMem_of_lt_hittingAfter (u := X) (s := A) (n := 1) (ω := ω) (k := k + 1) hk_lt_τ
          (by simp)
    · rw [← hstop, stoppedValue, hτ_idx]
      simp [shiftedFuturePath]

/-- Helper for Exercise 19.1.1: if the realized path starts inside `A`, then the path-space
first-entrance event from time `0` reduces to the time-`0` singleton event. -/
private lemma realizationPath_firstEntrancePathEventFromZero_ae_eq_startEq_of_mem
    (A : Set E) {z y : E} (hy : y ∈ A) (hz : z ∈ A)
    (hstart : ∀ᵐ ω ∂(P z : Measure Ω), X 0 ω = z) :
    let ν : Measure Ω := (P z : Measure Ω)
    (fun ω : Ω ↦ fun m : ℕ ↦ X m ω) ⁻¹' firstEntrancePathEventFromZero (A := A) y =ᵐ[ν]
      X 0 ⁻¹' ({y} : Set E) := by
  intro ν
  have hstart' : ∀ᵐ ω ∂ν, X 0 ω = z := by
    simpa [ν] using hstart
  -- Proof comment: once the start state already lies in `A`, the only admissible first entrance
  -- on the full path occurs at time `0`, so the path event becomes the singleton start event.
  filter_upwards [hstart'] with ω hω
  apply propext
  constructor
  · intro hpath
    rcases hpath with ⟨-, n, havoid, hxy⟩
    cases n with
    | zero =>
        simpa [Set.mem_preimage] using hxy
    | succ n =>
        have hnotA : X 0 ω ∉ A := havoid 0 (Nat.succ_pos _)
        have hmemA : X 0 ω ∈ A := by
          simpa [hω] using hz
        exact False.elim (hnotA hmemA)
  · intro hxy
    refine ⟨hy, 0, ?_, ?_⟩
    · intro m hm
      exact False.elim (Nat.not_lt_zero _ hm)
    · simpa [Set.mem_preimage] using hxy

/-- Helper for Exercise 19.1.1: if the realized path starts outside `A`, then the path-space
first-entrance event from time `0` agrees with the original first-entrance event from time `1`. -/
private lemma realizationPath_firstEntrancePathEventFromZero_ae_eq_firstEntranceEvent_of_not_mem
    (A : Set E) {z y : E} (hz : z ∉ A)
    (hstart : ∀ᵐ ω ∂(P z : Measure Ω), X 0 ω = z) :
    let ν : Measure Ω := (P z : Measure Ω)
    (fun ω : Ω ↦ fun m : ℕ ↦ X m ω) ⁻¹' firstEntrancePathEventFromZero (A := A) y =ᵐ[ν]
      {ω | hittingAfter X A 1 ω < ⊤ ∧ stoppedValue X (hittingAfter X A 1) ω = y} := by
  intro ν
  have hstart' : ∀ᵐ ω ∂ν, X 0 ω = z := by
    simpa [ν] using hstart
  -- Proof comment: when the path starts outside `A`, deleting the time-`0` coordinate converts
  -- the full-path first-entrance event into the positive-time first-entrance event already
  -- encoded by `futurePath_mem_firstEntrancePathEventFromZero_iff`.
  filter_upwards [hstart'] with ω hω
  have h0notA : X 0 ω ∉ A := by
    simpa [hω] using hz
  have hshift :
      (fun m : ℕ ↦ X m ω) ∈ firstEntrancePathEventFromZero (A := A) y ↔
        shiftedFuturePath X 1 ω ∈ firstEntrancePathEventFromZero (A := A) y := by
    constructor
    · intro hpath
      rcases hpath with ⟨hy, n, havoid, hxy⟩
      have hn_ne_zero : n ≠ 0 := by
        intro hn0
        have hxy0 : X 0 ω = y := by
          simpa [hn0] using hxy
        have h0mem : X 0 ω ∈ A := by
          exact hxy0 ▸ hy
        exact h0notA h0mem
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn_ne_zero
      refine ⟨hy, k, ?_, ?_⟩
      · intro m hm
        exact havoid (m + 1) (Nat.succ_lt_succ hm)
      · simpa [shiftedFuturePath] using hxy
    · intro hpath
      rcases hpath with ⟨hy, n, havoid, hxy⟩
      refine ⟨hy, n + 1, ?_, ?_⟩
      · intro m hm
        cases m with
        | zero =>
            simpa using h0notA
        | succ m =>
            have hm' : m < n := Nat.lt_of_succ_lt_succ hm
            simpa [shiftedFuturePath] using havoid m hm'
      · simpa [shiftedFuturePath] using hxy
  exact propext <|
    hshift.trans <|
      futurePath_mem_firstEntrancePathEventFromZero_iff
        (X := X) (A := A) (y := y) (ω := ω)

/-- Helper for Exercise 19.1.1: for a boundary target `y ∈ A`, integrating the indicator of the
path-space first-entrance event against the realized path law from `z` recovers the killed Green
matrix entry at `(z, y)`. -/
private lemma firstEntrancePathIndicator_integral_eq_killedGreenMatrixView
    (p : E → E → ℝ≥0∞)
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    (A : Set E) {z y : E} (hy : y ∈ A) :
    let B : Set (ℕ → E) := firstEntrancePathEventFromZero (A := A) y
    let f : (ℕ → E) → ℝ := Set.indicator B (fun _ ↦ (1 : ℝ))
    ∫ ξ, f ξ ∂(realizationPathKernel (P := P) (X := X) z) =
      killedGreenMatrixView P X A z y := by
  intro B f
  let hReal :
      IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  let path : Ω → ℕ → E := fun ω m ↦ X m ω
  have hB_meas : MeasurableSet B := firstEntrancePathEventFromZero_measurable (A := A) y
  have hpath_meas : Measurable path := by
    refine measurable_pi_lambda _ fun m ↦ ?_
    simpa [path] using hReal.measurable_process m
  have hinner :
      ∫ ξ, f ξ ∂(realizationPathKernel (P := P) (X := X) z) =
        ((P z : Measure Ω) (path ⁻¹' B)).toReal := by
    -- Proof comment: the explicit path kernel is the pushforward of `P z` along the full path
    -- map, so the indicator integral is exactly the real mass of the pulled-back path event.
    calc
      ∫ ξ, f ξ ∂(realizationPathKernel (P := P) (X := X) z)
          = (realizationPathKernel (P := P) (X := X) z).real B := by
              simpa [f] using
                (MeasureTheory.integral_indicator_one
                  (μ := realizationPathKernel (P := P) (X := X) z) (s := B) hB_meas)
      _ = (((P z : Measure Ω).map path).real B) := by
            rfl
      _ = ((P z : Measure Ω) (path ⁻¹' B)).toReal := by
            simpa [MeasureTheory.Measure.real_def, path] using
              (MeasureTheory.map_measureReal_apply
                (μ := (P z : Measure Ω)) (f := path) hpath_meas hB_meas)
  have hstart : ∀ᵐ ω ∂(P z : Measure Ω), X 0 ω = z :=
    initialState_ae_eq_start_local (p := p) (P := P) (X := X) z
  by_cases hz : z ∈ A
  · have hpre_ae :
        path ⁻¹' B =ᵐ[(P z : Measure Ω)] X 0 ⁻¹' ({y} : Set E) := by
      simpa [path, B] using
        realizationPath_firstEntrancePathEventFromZero_ae_eq_startEq_of_mem
          (P := P) (X := X) (A := A) (y := y) hy hz hstart
    have hmassMeasure :
        (P z : Measure Ω) (X 0 ⁻¹' ({y} : Set E)) = if z = y then 1 else 0 := by
      have hinit := congrArg (fun ν : Measure E ↦ ν ({y} : Set E)) (hReal.initial_eq z)
      by_cases hzy : z = y
      · subst hzy
        simpa [Measure.map_apply (hReal.measurable_process 0) (measurableSet_singleton z)]
          using hinit
      · simpa [Measure.map_apply (hReal.measurable_process 0) (measurableSet_singleton y), hzy]
          using hinit
    have hmass :
        ((P z : Measure Ω) (X 0 ⁻¹' ({y} : Set E))).toReal = if z = y then 1 else 0 := by
      rw [hmassMeasure]
      split_ifs <;> simp
    calc
      ∫ ξ, f ξ ∂(realizationPathKernel (P := P) (X := X) z)
          = ((P z : Measure Ω) (path ⁻¹' B)).toReal := hinner
      _ = ((P z : Measure Ω) (X 0 ⁻¹' ({y} : Set E))).toReal := by
            rw [measure_congr hpre_ae]
      _ = if z = y then 1 else 0 := hmass
      _ = killedGreenMatrixView P X A z y := by
            symm
            simpa using
              killedGreenMatrixView_eq_kroneckerDelta_of_mem_local
                (P := P) (X := X) (A := A) (x := z) (y := y) hz
  · have hpre_ae :
        path ⁻¹' B =ᵐ[(P z : Measure Ω)]
          {ω | hittingAfter X A 1 ω < ⊤ ∧
              stoppedValue X (hittingAfter X A 1) ω = y} := by
      simpa [path, B] using
        realizationPath_firstEntrancePathEventFromZero_ae_eq_firstEntranceEvent_of_not_mem
          (P := P) (X := X) (A := A) (z := z) (y := y) hz hstart
    calc
      ∫ ξ, f ξ ∂(realizationPathKernel (P := P) (X := X) z)
          = ((P z : Measure Ω) (path ⁻¹' B)).toReal := hinner
      _ = ((P z : Measure Ω)
            {ω | hittingAfter X A 1 ω < ⊤ ∧
                stoppedValue X (hittingAfter X A 1) ω = y}).toReal := by
              rw [measure_congr hpre_ae]
      _ = killedGreenMatrixView P X A z y := by
            rw [killedGreenMatrixView,
              killedGreenFunction_eq_firstEntranceMeasure
                (P := P) (X := X) (A := A) (x := z) (y := y) hReal.measurable_process hz hy]

/-- Helper for Exercise 19.1.1: the path-space event that the shifted chain is still outside `A`
through time `n` and is at `y` at time `n`. -/
private def preHitStatePathEvent (A : Set E) (y : E) (n : ℕ) : Set (ℕ → E) :=
  {ξ | ξ n = y ∧ ∀ m ≤ n, ξ m ∉ A}

/-- Helper for Exercise 19.1.1: the pre-hit path event is exactly the finite-coordinate
description "equal `y` at time `n` and stay outside `A` through time `n`". -/
private lemma preHitStatePathEvent_coordSpec
    (A : Set E) (y : E) (n : ℕ) {ξ : ℕ → E} :
    ξ ∈ preHitStatePathEvent (A := A) y n ↔
      ξ n = y ∧ ∀ m ≤ n, ξ m ∉ A :=
  Iff.rfl

/-- Helper for Exercise 19.1.1: the bounded pre-hit time-`n` path event is measurable. -/
private lemma preHitStatePathEvent_measurable
    (A : Set E) (y : E) (n : ℕ) :
    MeasurableSet (preHitStatePathEvent (A := A) y n) := by
  -- Proof comment: the pre-hit slice is the intersection of one coordinate singleton event with
  -- the finite prefix-avoidance event through time `n`.
  exact
    ((measurable_pi_apply n) (measurableSet_singleton y)).inter
      (avoidThroughPathEvent_measurable (A := A) n)

/-- Helper for Exercise 19.1.1: shifting the trajectory by one step turns the pre-hit path event
on path space into the corresponding positive-time pre-hit slice of the original chain. -/
private lemma futurePath_mem_preHitStatePathEvent_iff
    (A : Set E) (y : E) (n : ℕ) {ω : Ω} :
    shiftedFuturePath X 1 ω ∈ preHitStatePathEvent (A := A) y n ↔
      ((((n + 1 : ℕ) : ℕ∞) < hittingAfter X A 1 ω) ∧ X (n + 1) ω = y) := by
  constructor
  · intro hω
    rcases (preHitStatePathEvent_coordSpec (A := A) (y := y) (n := n)).1 hω with ⟨hxy, havoid⟩
    refine ⟨?_, hxy⟩
    by_contra hnot
    have hle : hittingAfter X A 1 ω ≤ n + 1 := le_of_not_gt hnot
    rcases (hittingAfter_le_iff (u := X) (s := A) (n := 1) (ω := ω) (i := n + 1)).1 hle with
      ⟨j, hj, hjA⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hj.1)
    have hk_le : k ≤ n := by
      simpa using hj.2
    have hk_not_mem : X (k + 1) ω ∉ A := by
      simpa [shiftedFuturePath] using havoid k hk_le
    exact hk_not_mem hjA
  · rintro ⟨hτ, hxy⟩
    refine (preHitStatePathEvent_coordSpec (A := A) (y := y) (n := n)).2 ⟨hxy, ?_⟩
    intro m hm
    have hm_lt_τ : (m + 1 : ℕ∞) < hittingAfter X A 1 ω := by
      exact lt_of_le_of_lt (by exact_mod_cast Nat.succ_le_succ hm) hτ
    -- Proof comment: every coordinate up to time `n` on the shifted path still lies before the
    -- first positive hit of `A`.
    simpa [shiftedFuturePath] using
      notMem_of_lt_hittingAfter (u := X) (s := A) (n := 1) (ω := ω) (k := m + 1) hm_lt_τ
        (by simp)

/-- Helper for Exercise 19.1.1: from a starting state in `A`, the pre-hit path event is empty
under the realized path law. -/
private lemma realizationPath_preHitStatePathEvent_ae_eq_empty_of_mem
    (A : Set E) {z y : E} (hz : z ∈ A)
    (hstart : ∀ᵐ ω ∂(P z : Measure Ω), X 0 ω = z) (n : ℕ) :
    let ν : Measure Ω := (P z : Measure Ω)
    (fun ω : Ω ↦ fun m : ℕ ↦ X m ω) ⁻¹' preHitStatePathEvent (A := A) y n =ᵐ[ν]
      (∅ : Set Ω) := by
  intro ν
  have hstart' : ∀ᵐ ω ∂ν, X 0 ω = z := by
    simpa [ν] using hstart
  -- Proof comment: on the almost-sure event `X 0 = z ∈ A`, the full-path pre-hit event is
  -- impossible because its time-`0` coordinate is required to lie outside `A`.
  filter_upwards [hstart'] with ω hω
  apply propext
  constructor
  · intro hpre
    have hcoord :=
      (preHitStatePathEvent_coordSpec (A := A) (y := y) (n := n)
        (ξ := fun m : ℕ ↦ X m ω)).1 hpre
    have h0mem : X 0 ω ∈ A := by
      simpa [hω] using hz
    have : False := (hcoord.2 0 (Nat.zero_le n)) h0mem
    simpa using this
  · intro hfalse
    exact False.elim hfalse

/-- Helper for Exercise 19.1.1: from a starting state outside `A`, the pre-hit path event under
the realized path law is exactly the corresponding pre-hit state slice. -/
private lemma realizationPath_preHitStatePathEvent_ae_eq_preHitSlice_of_not_mem
    (A : Set E) {z y : E} (hz : z ∉ A)
    (hstart : ∀ᵐ ω ∂(P z : Measure Ω), X 0 ω = z) (n : ℕ) :
    let ν : Measure Ω := (P z : Measure Ω)
    (fun ω : Ω ↦ fun m : ℕ ↦ X m ω) ⁻¹' preHitStatePathEvent (A := A) y n =ᵐ[ν]
      {ω | ((n : ℕ∞) < hittingAfter X A 1 ω) ∧ X n ω = y} := by
  intro ν
  have hstart' : ∀ᵐ ω ∂ν, X 0 ω = z := by
    simpa [ν] using hstart
  -- Proof comment: once `X 0 = z ∉ A`, the path-space pre-hit event is equivalent to saying that
  -- the first `n + 1` coordinates stay before the first hit, together with the time-`n` value.
  filter_upwards [hstart'] with ω hω
  apply propext
  constructor
  · intro hpre
    have hcoord :=
      (preHitStatePathEvent_coordSpec (A := A) (y := y) (n := n)
        (ξ := fun m : ℕ ↦ X m ω)).1 hpre
    have h0notA : X 0 ω ∉ A := by
      simpa [hω] using hz
    have hτ01 :
        hittingAfter X A 0 ω = hittingAfter X A 1 ω :=
      hittingAfter_zero_eq_one_of_not_mem_initial_local (X := X) (A := A) (ω := ω) h0notA
    have hlt0 : (n : ℕ∞) < hittingAfter X A 0 ω := by
      by_contra hnot
      have hle : hittingAfter X A 0 ω ≤ n := le_of_not_gt hnot
      rcases (hittingAfter_le_iff (u := X) (s := A) (n := 0) (ω := ω) (i := n)).1 hle with
        ⟨j, hj, hjA⟩
      exact (hcoord.2 j hj.2) hjA
    exact ⟨by simpa [hτ01] using hlt0, hcoord.1⟩
  · rintro ⟨hτ, hxy⟩
    have h0notA : X 0 ω ∉ A := by
      simpa [hω] using hz
    have hτ01 :
        hittingAfter X A 0 ω = hittingAfter X A 1 ω :=
      hittingAfter_zero_eq_one_of_not_mem_initial_local (X := X) (A := A) (ω := ω) h0notA
    have hlt0 : (n : ℕ∞) < hittingAfter X A 0 ω := by
      simpa [hτ01] using hτ
    refine (preHitStatePathEvent_coordSpec (A := A) (y := y) (n := n)
      (ξ := fun m : ℕ ↦ X m ω)).2 ⟨hxy, ?_⟩
    intro m hm
    have hm_lt0 : (m : ℕ∞) < hittingAfter X A 0 ω := by
      exact lt_of_le_of_lt (by exact_mod_cast hm) hlt0
    exact
      notMem_of_lt_hittingAfter (u := X) (s := A) (n := 0) (ω := ω) (k := m) hm_lt0
        (by simp)

/-- Helper for Exercise 19.1.1: a fixed first-step branch of the successor pre-hit slice is the
finite union of the shifted tuple singletons whose coordinates stay outside `A`, start at `z`,
and end at `y`. -/
private lemma preHitSuccessorBranch_eq_biUnion_shiftedTupleSingletons
    (A : Set E) (y z : E) (n : ℕ) :
    ({ω | X 1 ω = z} ∩
      {ω | (((n + 1 : ℕ) : ℕ∞) < hittingAfter X A 1 ω) ∧ X (n + 1) ω = y}) =
        ⋃ t ∈ (Finset.univ.filter fun t : Fin (n + 1) → E ↦
          t 0 = z ∧ t (Fin.last n) = y ∧ ∀ i : Fin (n + 1), t i ∉ A),
          (realizedTupleFromStep X (n + 1)) ⁻¹' ({t} : Set (Fin (n + 1) → E)) := by
  ext ω
  simp only [Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
    Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨hstep, hslice⟩
    let t : Fin (n + 1) → E := realizedTupleFromStep X (n + 1) ω
    refine ⟨t, ?_, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa [t, realizedTupleFromStep] using hstep
    · simpa [t, realizedTupleFromStep] using hslice.2
    · intro i
      have hi_lt :
          (((i : ℕ) + 1 : ℕ∞) < hittingAfter X A 1 ω) := by
        have hi_le_nat : (i : ℕ) + 1 ≤ n + 1 :=
          Nat.succ_le_succ (Nat.le_of_lt_succ i.2)
        exact
          lt_of_le_of_lt
            (by exact_mod_cast hi_le_nat)
            hslice.1
      -- Proof comment: every coordinate of the shifted tuple lies strictly before the first hit.
      simpa [t, realizedTupleFromStep] using
        notMem_of_lt_hittingAfter
          (u := X) (s := A) (n := 1) (ω := ω) (k := (i : ℕ) + 1) hi_lt (by simp)
  · rintro ⟨t, ht, htup⟩
    rcases ht with ⟨ht0, hty, havoid⟩
    refine ⟨?_, ?_⟩
    · simpa [realizedTupleFromStep, ht0] using congrFun htup 0
    · refine ⟨?_, ?_⟩
      · by_contra hnot
        have hle : hittingAfter X A 1 ω ≤ n + 1 := le_of_not_gt hnot
        rcases (hittingAfter_le_iff (u := X) (s := A) (n := 1) (ω := ω) (i := n + 1)).1 hle with
          ⟨j, hj, hjA⟩
        obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hj.1)
        have hk_le : k ≤ n := by
          simpa using hj.2
        let i : Fin (n + 1) := ⟨k, Nat.lt_succ_of_le hk_le⟩
        have hcoord : X (k + 1) ω = t i := by
          simpa [realizedTupleFromStep, i] using congrFun htup i
        exact havoid i (hcoord.symm ▸ hjA)
      · simpa [realizedTupleFromStep, hty] using congrFun htup (Fin.last n)

/-- Helper for Exercise 19.1.1: every pre-hit state slice is measurable. -/
private lemma preHitStateSlice_measurable_generated
    (A : Set E) (y : E) (n : ℕ) :
    MeasurableSet[generatedFiltrationSpace X n]
      {ω | ((n : ℕ∞) < hittingAfter X A 1 ω) ∧ X n ω = y} := by
  have htail :
      MeasurableSet[generatedFiltrationSpace X n] {ω | ((n : ℕ∞) < hittingAfter X A 1 ω)} := by
    have hEq :
        {ω | ((n : ℕ∞) < hittingAfter X A 1 ω)} = {ω | hittingAfter X A 1 ω ≤ n}ᶜ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff]
      constructor
      · intro hω
        exact not_le_of_gt hω
      · intro hω
        exact lt_of_not_ge hω
    rw [hEq]
    have hle :
        MeasurableSet[generatedFiltrationSpace X n] {ω | hittingAfter X A 1 ω ≤ n} := by
      have hUnion :
          {ω | hittingAfter X A 1 ω ≤ n} =
            ⋃ j ∈ ((Finset.Icc 1 n : Finset ℕ) : Set ℕ), X j ⁻¹' A := by
        ext ω
        simpa using
          (hittingAfter_le_iff (u := X) (s := A) (n := 1) (ω := ω) (i := n))
      rw [hUnion]
      refine MeasurableSet.biUnion (Set.to_countable _) ?_
      intro j hj
      have hjn : j ≤ n := (Finset.mem_Icc.mp hj).2
      have hXj_meas : Measurable[generatedFiltrationSpace X n] (X j) := by
        refine Measurable.of_comap_le ?_
        exact le_iSup₂_of_le j hjn le_rfl
      exact hXj_meas (show MeasurableSet A from MeasurableSet.of_discrete)
    exact hle.compl
  have hXn_meas : Measurable[generatedFiltrationSpace X n] (X n) := by
    refine Measurable.of_comap_le ?_
    exact le_iSup₂_of_le n le_rfl le_rfl
  have hstate :
      MeasurableSet[generatedFiltrationSpace X n] (X n ⁻¹' ({y} : Set E)) := by
    simpa using hXn_meas (measurableSet_singleton y)
  have hEq :
      {ω | ((n : ℕ∞) < hittingAfter X A 1 ω) ∧ X n ω = y} =
        {ω | ((n : ℕ∞) < hittingAfter X A 1 ω)} ∩ X n ⁻¹' ({y} : Set E) := by
    ext ω
    simp [Set.mem_preimage]
  -- Proof comment: the time-`n` pre-hit slice is the intersection of the history tail event and
  -- the measurable singleton fiber of `X n`, both already visible in the time-`n` filtration.
  rw [hEq]
  exact htail.inter hstate

/-- Helper for Exercise 19.1.1: every pre-hit state slice is measurable. -/
private lemma preHitStateSlice_measurable
    (A : Set E) (y : E) (n : ℕ) (hX : ∀ m : ℕ, Measurable (X m)) :
    MeasurableSet {ω | ((n : ℕ∞) < hittingAfter X A 1 ω) ∧ X n ω = y} := by
  have hFiltration_le : generatedFiltrationSpace X n ≤ ‹MeasurableSpace Ω› := by
    refine iSup₂_le fun k hk ↦ ?_
    exact (hX k).comap_le
  -- Proof comment: the deterministic-time slice is already measurable in the generated
  -- filtration, and that history sigma-algebra sits inside the ambient measurable space.
  exact
    hFiltration_le _
      (preHitStateSlice_measurable_generated (X := X) (A := A) y n)

/-- Helper for Exercise 19.1.1: if the pinned time-`n` state already lies in `A`, then the
corresponding pre-hit slice has zero mass under a start state outside `A`. -/
private lemma preHitStateSlice_measure_eq_zero_of_mem
    (p : E → E → ℝ≥0∞)
    [IsMarkovProcessRealization (fun k : ℕ ↦ discreteMatrixKernel p ^ k) P X]
    (A : Set E) {x z : E} (hx : x ∉ A) (hz : z ∈ A) (n : ℕ) :
    (P x : Measure Ω) {ω | ((n : ℕ∞) < hittingAfter X A 1 ω) ∧ X n ω = z} = 0 := by
  let hReal :
      IsMarkovProcessRealization (fun k : ℕ ↦ discreteMatrixKernel p ^ k) P X := inferInstance
  cases n with
  | zero =>
      have hxz : x ≠ z := by
        intro hxz
        exact hx (hxz ▸ hz)
      have hEq :
          {ω | ((0 : ℕ∞) < hittingAfter X A 1 ω) ∧ X 0 ω = z} = X 0 ⁻¹' ({z} : Set E) := by
        ext ω
        constructor
        · intro hω
          simpa [Set.mem_preimage] using hω.2
        · intro hω
          refine ⟨?_, ?_⟩
          · exact lt_of_lt_of_le (by simp : (0 : ℕ∞) < 1)
              (le_hittingAfter (u := X) (s := A) (n := 1) ω)
          · simpa [Set.mem_preimage] using hω
      have hstart :=
        congrArg (fun ν : Measure E ↦ ν ({z} : Set E)) (hReal.initial_eq x)
      have hmassMap : (Measure.map (X 0) (P x : Measure Ω)) ({z} : Set E) = 0 := by
        simpa [hxz] using hstart
      have hmass :
          (P x : Measure Ω) (X 0 ⁻¹' ({z} : Set E)) = 0 := by
        rw [← Measure.map_apply (hReal.measurable_process 0) (measurableSet_singleton z)]
        exact hmassMap
      simpa [hEq] using hmass
  | succ n =>
      have hEq :
          {ω | ((((n + 1 : ℕ) : ℕ∞) < hittingAfter X A 1 ω) ∧ X (n + 1) ω = z)} =
            (∅ : Set Ω) := by
        ext ω
        constructor
        · intro hω
          have hnotA :
              X (n + 1) ω ∉ A :=
            notMem_of_lt_hittingAfter
              (u := X) (s := A) (n := 1) (ω := ω) (k := n + 1) hω.1 (by simp)
          exact False.elim (hnotA (hω.2.symm ▸ hz))
        · simp
      rw [hEq]
      simp

/-- Helper for Exercise 19.1.1: each first-step branch of a positive-time pre-hit slice is
ambient measurable. -/
private lemma preHitStateSlice_firstStepBranch_measurable
    (A : Set E) (y z : E) (n : ℕ) (hX : ∀ m : ℕ, Measurable (X m)) :
    MeasurableSet
      ({ω | X 1 ω = z} ∩
        {ω | (((n + 1 : ℕ) : ℕ∞) < hittingAfter X A 1 ω) ∧ X (n + 1) ω = y}) := by
  -- Proof comment: a first-step branch is the intersection of the time-`1` singleton event with
  -- the ambient positive-time slice event at time `n + 1`.
  refine (hX 1 (measurableSet_singleton z)).inter ?_
  exact preHitStateSlice_measurable (X := X) (A := A) y (n + 1) hX

/-- Helper for Exercise 19.1.1: if the first step lands in `A`, then the positive-time pre-hit
slice is empty on that branch. -/
private lemma preHitStateSlice_firstStepBranch_eq_empty_of_mem
    (A : Set E) {y z : E} (hz : z ∈ A) (n : ℕ) :
    ({ω | X 1 ω = z} ∩
      {ω | (((n + 1 : ℕ) : ℕ∞) < hittingAfter X A 1 ω) ∧ X (n + 1) ω = y}) =
        (∅ : Set Ω) := by
  ext ω
  constructor
  · intro hω
    have hlt : (1 : ℕ∞) < hittingAfter X A 1 ω := by
      exact lt_of_le_of_lt (by simp) hω.2.1
    have hnotA :
        X 1 ω ∉ A :=
      notMem_of_lt_hittingAfter
        (u := X) (s := A) (n := 1) (ω := ω) (k := 1) hlt (by simp)
    have hmem : X 1 ω ∈ A := by
      exact hω.1.symm ▸ hz
    exact False.elim (hnotA hmem)
  · intro hω
    simpa using hω

/-- Helper for Exercise 19.1.1: distinct first-step branches of the same positive-time pre-hit
slice are disjoint. -/
private lemma preHitStateSlice_firstStepBranch_pairwiseDisjoint
    (A : Set E) (y : E) (n : ℕ) :
    (Set.univ : Set E).PairwiseDisjoint fun z : E ↦
      ({ω | X 1 ω = z} ∩
        {ω | (((n + 1 : ℕ) : ℕ∞) < hittingAfter X A 1 ω) ∧ X (n + 1) ω = y}) := by
  intro z _ w _ hzw
  -- Proof comment: two distinct branches cannot meet because they prescribe different values for
  -- the same first-step coordinate `X 1`.
  refine Set.disjoint_left.2 ?_
  intro ω hz hw
  exact hzw (hz.1.symm.trans hw.1)

/-- Helper for Exercise 19.1.1: a positive-time pre-hit slice is the finite union of its
first-step branches over states outside `A`. -/
private lemma preHitStateSlice_eq_biUnion_firstStepOutside
    (A : Set E) (y : E) (n : ℕ) :
    {ω | (((n + 1 : ℕ) : ℕ∞) < hittingAfter X A 1 ω) ∧ X (n + 1) ω = y} =
      ⋃ z ∈ (Finset.univ.filter fun z : E ↦ z ∉ A),
        ({ω | X 1 ω = z} ∩
          {ω | (((n + 1 : ℕ) : ℕ∞) < hittingAfter X A 1 ω) ∧ X (n + 1) ω = y}) := by
  ext ω
  simp only [Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
    Set.mem_iUnion, exists_prop]
  constructor
  · intro hω
    have hlt : (1 : ℕ∞) < hittingAfter X A 1 ω := by
      exact lt_of_le_of_lt (by simp) hω.1
    have hnotA :
        X 1 ω ∉ A :=
      notMem_of_lt_hittingAfter
        (u := X) (s := A) (n := 1) (ω := ω) (k := 1) hlt (by simp)
    -- Proof comment: on a positive-time pre-hit slice, the first step is itself an outside-`A`
    -- branch witness.
    exact ⟨X 1 ω, hnotA, rfl, hω⟩
  · intro hω
    rcases hω with ⟨z, -, -, hzω⟩
    exact hzω

/-- Helper for Exercise 19.1.1: the real mass of a positive-time pre-hit slice is the finite sum
of the real masses of its first-step branches outside `A`. -/
private lemma preHitStateSlice_eq_sum_firstStepBranches_toReal
    (A : Set E) (x y : E) (n : ℕ) (hX : ∀ m : ℕ, Measurable (X m)) :
    ((P x : Measure Ω)
      {ω | (((n + 1 : ℕ) : ℕ∞) < hittingAfter X A 1 ω) ∧ X (n + 1) ω = y}).toReal =
        Finset.sum (Finset.univ.filter fun z : E ↦ z ∉ A) fun z ↦
          ((P x : Measure Ω)
            ({ω | X 1 ω = z} ∩
              {ω | (((n + 1 : ℕ) : ℕ∞) < hittingAfter X A 1 ω) ∧ X (n + 1) ω = y})).toReal := by
  let branch : E → Set Ω := fun z ↦
    {ω | X 1 ω = z} ∩
      {ω | (((n + 1 : ℕ) : ℕ∞) < hittingAfter X A 1 ω) ∧ X (n + 1) ω = y}
  have hEq :
      {ω | (((n + 1 : ℕ) : ℕ∞) < hittingAfter X A 1 ω) ∧ X (n + 1) ω = y} =
        ⋃ z ∈ (Finset.univ.filter fun z : E ↦ z ∉ A), branch z := by
    simpa [branch] using preHitStateSlice_eq_biUnion_firstStepOutside (X := X) (A := A) y n
  have hdisj : (Set.univ : Set E).PairwiseDisjoint branch := by
    simpa [branch] using
      preHitStateSlice_firstStepBranch_pairwiseDisjoint (X := X) (A := A) y n
  have hmeas : ∀ z : E, MeasurableSet (branch z) := by
    intro z
    simpa [branch] using
      preHitStateSlice_firstStepBranch_measurable (X := X) (A := A) y z n
        hX
  have hdisjOutside :
      {z : E | z ∉ A}.PairwiseDisjoint branch := by
    intro z hz w hw hzw
    exact hdisj (by simp) (by simp) hzw
  -- Proof comment: after partitioning by the first step, the slice mass is the real measure of a
  -- disjoint finite union, so `measureReal_biUnion_finset` turns it into a finite sum.
  have hmass :
      ((P x : Measure Ω) (⋃ z ∈ (Finset.univ.filter fun z : E ↦ z ∉ A), branch z)).toReal =
        Finset.sum (Finset.univ.filter fun z : E ↦ z ∉ A) fun z ↦
          ((P x : Measure Ω) (branch z)).toReal := by
    simpa [measureReal_def, branch] using
      (measureReal_biUnion_finset (μ := (P x : Measure Ω))
        (s := (Finset.univ.filter fun z : E ↦ z ∉ A)) (f := branch)
        (by simpa using hdisjOutside) (fun z _ ↦ hmeas z))
  calc
    ((P x : Measure Ω)
      {ω | (((n + 1 : ℕ) : ℕ∞) < hittingAfter X A 1 ω) ∧ X (n + 1) ω = y}).toReal
        = ((P x : Measure Ω) (⋃ z ∈ (Finset.univ.filter fun z : E ↦ z ∉ A), branch z)).toReal := by
            rw [hEq]
    _ = Finset.sum (Finset.univ.filter fun z : E ↦ z ∉ A) fun z ↦
          ((P x : Measure Ω) (branch z)).toReal := hmass

/-- Helper for Exercise 19.1.1: the first-step partition can be written as a full row sum by
inserting zero branches on `A`. -/
private lemma preHitStateSlice_eq_sum_firstStepBranches_all_toReal
    (A : Set E) (x y : E) (n : ℕ) (hX : ∀ m : ℕ, Measurable (X m)) :
    ((P x : Measure Ω)
      {ω | (((n + 1 : ℕ) : ℕ∞) < hittingAfter X A 1 ω) ∧ X (n + 1) ω = y}).toReal =
        ∑ z : E, if z ∈ A then 0 else
          ((P x : Measure Ω)
            ({ω | X 1 ω = z} ∩
              {ω | (((n + 1 : ℕ) : ℕ∞) < hittingAfter X A 1 ω) ∧ X (n + 1) ω = y})).toReal := by
  let branch : E → Set Ω := fun z ↦
    {ω | X 1 ω = z} ∩
      {ω | (((n + 1 : ℕ) : ℕ∞) < hittingAfter X A 1 ω) ∧ X (n + 1) ω = y}
  rw [preHitStateSlice_eq_sum_firstStepBranches_toReal (P := P) (X := X) (A := A) x y n hX]
  -- Proof comment: replace the filtered outside-`A` sum by a full finite sum, using the zero
  -- contribution of branches indexed by `A`.
  simpa [branch] using
    (Finset.sum_filter (s := Finset.univ) (p := fun z : E ↦ z ∉ A)
      (f := fun z ↦ ((P x : Measure Ω) (branch z)).toReal))

/-- Helper for Exercise 19.1.1: when the restarted chain starts from `z ∉ A`, the finite union of
zero-start tuple singletons encoding a length-`n` pre-hit slice is exactly the event that the
start state is `z` and the chain is still outside `A` through time `n` while sitting at `y` at
time `n`. -/
private lemma preHitRestartedZeroTupleUnion_eq_startInterSlice
    (A : Set E) {z y : E} (hz : z ∉ A) (n : ℕ) :
    (⋃ t ∈ (Finset.univ.filter fun t : Fin (n + 1) → E ↦
      t 0 = z ∧ t (Fin.last n) = y ∧ ∀ i : Fin (n + 1), t i ∉ A),
      (realizedTupleFromZero X (n + 1)) ⁻¹' ({t} : Set (Fin (n + 1) → E))) =
        X 0 ⁻¹' ({z} : Set E) ∩
          {ω | ((n : ℕ∞) < hittingAfter X A 1 ω) ∧ X n ω = y} := by
  ext ω
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_iUnion, exists_prop,
    Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage]
  constructor
  · rintro ⟨t, ⟨ht0, hty, havoid⟩, htup⟩
    refine ⟨?_, ?_⟩
    · simpa [realizedTupleFromZero, ht0] using congrFun htup 0
    · refine ⟨?_, ?_⟩
      · by_contra hnot
        have hle : hittingAfter X A 1 ω ≤ n := le_of_not_gt hnot
        rcases (hittingAfter_le_iff (u := X) (s := A) (n := 1) (ω := ω) (i := n)).1 hle with
          ⟨j, hj, hjA⟩
        let i : Fin (n + 1) := ⟨j, Nat.lt_succ_of_le hj.2⟩
        have hcoord : X j ω = t i := by
          simpa [realizedTupleFromZero, i] using congrFun htup i
        exact havoid i (hcoord.symm ▸ hjA)
      · simpa [realizedTupleFromZero, hty] using congrFun htup (Fin.last n)
  · rintro ⟨hstart, hslice⟩
    let t : Fin (n + 1) → E := realizedTupleFromZero X (n + 1) ω
    refine ⟨t, ?_, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa [t, realizedTupleFromZero] using hstart
    · simpa [t, realizedTupleFromZero] using hslice.2
    · intro i
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
      · have hstartEq : X 0 ω = z := by
          simpa [Set.mem_preimage] using hstart
        have h0notA : X 0 ω ∉ A := by
          simpa [hstartEq] using hz
        simpa [t, realizedTupleFromZero] using h0notA
      · have hj_lt :
            (((j : ℕ) + 1 : ℕ∞) < hittingAfter X A 1 ω) := by
          have hj_le : j.1 + 1 ≤ n := Nat.succ_le_of_lt j.2
          exact lt_of_le_of_lt (by exact_mod_cast hj_le) hslice.1
        -- Proof comment: every positive coordinate in the restarted tuple lies strictly before
        -- the first entrance time, so it stays outside `A`.
        simpa [t, realizedTupleFromZero] using
          notMem_of_lt_hittingAfter
            (u := X) (s := A) (n := 1) (ω := ω) (k := (j : ℕ) + 1) hj_lt (by simp)

/-- Helper for Exercise 19.1.1: one fixed first-step branch of the successor pre-hit slice has
mass `(p x z)` times the restarted pre-hit slice mass from `z`, with the `z ∈ A` branch already
collapsed to `0`. -/
private lemma preHitStateSliceFirstStepBranch_eq_mul_restartSlice_toReal
    (A : Set E) (x y z : E) (n : ℕ) :
    ((P x : Measure Ω)
      ({ω | X 1 ω = z} ∩
        {ω | (((n + 1 : ℕ) : ℕ∞) < hittingAfter X A 1 ω) ∧ X (n + 1) ω = y})).toReal =
      (p x z).toReal * (if z ∈ A then 0 else
        ((P z : Measure Ω) {ω | ((n : ℕ∞) < hittingAfter X A 1 ω) ∧ X n ω = y}).toReal) := by
  let s : Finset (Fin (n + 1) → E) :=
    Finset.univ.filter fun t : Fin (n + 1) → E ↦
      t 0 = z ∧ t (Fin.last n) = y ∧ ∀ i : Fin (n + 1), t i ∉ A
  by_cases hz : z ∈ A
  · rw [preHitStateSlice_firstStepBranch_eq_empty_of_mem (X := X) (A := A) (y := y) hz n]
    simp [hz]
  · have hReal :
        IsMarkovProcessRealization (fun k : ℕ ↦ discreteMatrixKernel p ^ k) P X := inferInstance
    have hstep_meas : Measurable (realizedTupleFromStep X (n + 1)) := by
      refine measurable_pi_lambda _ fun i ↦ ?_
      simpa [realizedTupleFromStep] using hReal.measurable_process ((i : ℕ) + 1)
    have hzero_meas : Measurable (realizedTupleFromZero X (n + 1)) := by
      refine measurable_pi_lambda _ fun i ↦ ?_
      simpa [realizedTupleFromZero] using hReal.measurable_process (i : ℕ)
    have hdisjStep :
        (s : Set (Fin (n + 1) → E)).PairwiseDisjoint fun t ↦
          (realizedTupleFromStep X (n + 1)) ⁻¹' ({t} : Set (Fin (n + 1) → E)) := by
      intro t ht u hu htu
      refine Set.disjoint_left.2 ?_
      intro ω hωt hωu
      exact htu (hωt.symm.trans hωu)
    have hdisjZero :
        (s : Set (Fin (n + 1) → E)).PairwiseDisjoint fun t ↦
          (realizedTupleFromZero X (n + 1)) ⁻¹' ({t} : Set (Fin (n + 1) → E)) := by
      intro t ht u hu htu
      refine Set.disjoint_left.2 ?_
      intro ω hωt hωu
      exact htu (hωt.symm.trans hωu)
    have hstepMass :
        ((P x : Measure Ω)
          (⋃ t ∈ s,
            (realizedTupleFromStep X (n + 1)) ⁻¹' ({t} : Set (Fin (n + 1) → E)))).toReal =
          Finset.sum s fun t ↦
            ((P x : Measure Ω)
              ((realizedTupleFromStep X (n + 1)) ⁻¹' ({t} : Set (Fin (n + 1) → E)))).toReal := by
      simpa [measureReal_def] using
        (measureReal_biUnion_finset (μ := (P x : Measure Ω)) (s := s)
          (f := fun t ↦ (realizedTupleFromStep X (n + 1)) ⁻¹' ({t} : Set (Fin (n + 1) → E)))
          hdisjStep
          (fun t _ ↦ hstep_meas (measurableSet_singleton t)))
    have hzeroMass :
        ((P z : Measure Ω)
          (⋃ t ∈ s,
            (realizedTupleFromZero X (n + 1)) ⁻¹' ({t} : Set (Fin (n + 1) → E)))).toReal =
          Finset.sum s fun t ↦
            ((P z : Measure Ω)
              ((realizedTupleFromZero X (n + 1)) ⁻¹' ({t} : Set (Fin (n + 1) → E)))).toReal := by
      simpa [measureReal_def] using
        (measureReal_biUnion_finset (μ := (P z : Measure Ω)) (s := s)
          (f := fun t ↦ (realizedTupleFromZero X (n + 1)) ⁻¹' ({t} : Set (Fin (n + 1) → E)))
          hdisjZero
          (fun t _ ↦ hzero_meas (measurableSet_singleton t)))
    let startSlice : Set Ω :=
      X 0 ⁻¹' ({z} : Set E) ∩ {ω | ((n : ℕ∞) < hittingAfter X A 1 ω) ∧ X n ω = y}
    have hstart_ae :
        startSlice =ᵐ[(P z : Measure Ω)] {ω | ((n : ℕ∞) < hittingAfter X A 1 ω) ∧ X n ω = y} := by
      filter_upwards [initialState_ae_eq_start_local (p := p) (P := P) (X := X) z] with ω hω
      apply propext
      constructor
      · intro hω'
        exact hω'.2
      · intro hω'
        exact ⟨by simpa [Set.mem_preimage] using hω, hω'⟩
    -- Proof comment: replace the branch by its finite shifted-tuple decomposition, factor each
    -- singleton branch through the restarted zero-start tuple, then reassemble the restarted
    -- tuple family into the pre-hit slice from `z`.
    calc
      ((P x : Measure Ω)
        ({ω | X 1 ω = z} ∩
          {ω | (((n + 1 : ℕ) : ℕ∞) < hittingAfter X A 1 ω) ∧ X (n + 1) ω = y})).toReal
          =
            ((P x : Measure Ω)
              (⋃ t ∈ s,
                (realizedTupleFromStep X (n + 1)) ⁻¹' ({t} : Set (Fin (n + 1) → E)))).toReal := by
              rw [preHitSuccessorBranch_eq_biUnion_shiftedTupleSingletons (X := X) (A := A) y z n]
      _ = Finset.sum s fun t ↦
            ((P x : Measure Ω)
              ((realizedTupleFromStep X (n + 1)) ⁻¹' ({t} : Set (Fin (n + 1) → E)))).toReal := hstepMass
      _ = Finset.sum s fun t ↦
            (p x z).toReal *
              ((P z : Measure Ω)
                ((realizedTupleFromZero X (n + 1)) ⁻¹' ({t} : Set (Fin (n + 1) → E)))).toReal := by
              refine Finset.sum_congr rfl fun t ht ↦ ?_
              have ht0 : t 0 = z := (Finset.mem_filter.mp ht).2.1
              have hp : IsStochasticMatrix p :=
                isStochasticMatrix_of_realization (p := p) (P := P) (X := X)
              have hpxz_ne_top : p x z ≠ ⊤ := by
                apply ne_of_lt
                have hle : p x z ≤ ∑' w : E, p x w := ENNReal.le_tsum z
                have hrow : ∑' w : E, p x w = 1 := hp x
                rw [hrow] at hle
                exact lt_of_le_of_lt hle (by simp)
              have hfactor :=
                congrArg ENNReal.toReal
                  (shiftedTupleSingletonMeasure_eq_mul_restartMass
                    (p := p) (P := P) (X := X) (x := x) (n := n) t)
              simpa [ht0, ENNReal.toReal_mul, hpxz_ne_top, measure_ne_top _ _] using hfactor
      _ = (p x z).toReal *
            Finset.sum s fun t ↦
              ((P z : Measure Ω)
                ((realizedTupleFromZero X (n + 1)) ⁻¹' ({t} : Set (Fin (n + 1) → E)))).toReal := by
              symm
              rw [Finset.mul_sum]
      _ = (p x z).toReal *
            ((P z : Measure Ω)
              (⋃ t ∈ s,
                (realizedTupleFromZero X (n + 1)) ⁻¹' ({t} : Set (Fin (n + 1) → E)))).toReal := by
              rw [hzeroMass]
      _ = (p x z).toReal *
            ((P z : Measure Ω)
              (X 0 ⁻¹' ({z} : Set E) ∩
                {ω | ((n : ℕ∞) < hittingAfter X A 1 ω) ∧ X n ω = y})).toReal := by
              rw [preHitRestartedZeroTupleUnion_eq_startInterSlice (X := X) (A := A) hz n]
      _ = (p x z).toReal *
            ((P z : Measure Ω)
              {ω | ((n : ℕ∞) < hittingAfter X A 1 ω) ∧ X n ω = y}).toReal := by
              have hslice_eq :
                  (P z : Measure Ω)
                    (X 0 ⁻¹' ({z} : Set E) ∩
                      {ω | ((n : ℕ∞) < hittingAfter X A 1 ω) ∧ X n ω = y}) =
                    (P z : Measure Ω)
                      {ω | ((n : ℕ∞) < hittingAfter X A 1 ω) ∧ X n ω = y} :=
                measure_congr hstart_ae
              rw [hslice_eq]
      _ = (p x z).toReal * (if z ∈ A then 0 else
            ((P z : Measure Ω) {ω | ((n : ℕ∞) < hittingAfter X A 1 ω) ∧ X n ω = y}).toReal) := by
              simp [hz]

/-- Helper for Exercise 19.1.1: one positive-time pre-hit slice is the one-step kernel average of
the preceding pre-hit slice. -/
private lemma preHitStateSlice_succ_eq_kernelAverage_toReal
    (A : Set E) {x y : E} (hx : x ∉ A) (n : ℕ) :
    ((P x : Measure Ω)
      {ω | ((((n + 1 : ℕ) : ℕ∞) < hittingAfter X A 1 ω) ∧ X (n + 1) ω = y)}).toReal =
        ∫ z, (if z ∈ A then 0 else
          ((P z : Measure Ω) {ω | ((n : ℕ∞) < hittingAfter X A 1 ω) ∧ X n ω = y}).toReal)
          ∂discreteMatrixKernel p x := by
  let hReal :
      IsMarkovProcessRealization (fun k : ℕ ↦ discreteMatrixKernel p ^ k) P X := inferInstance
  have hX : ∀ m : ℕ, Measurable (X m) := hReal.measurable_process
  let f : E → ℝ := fun z ↦ if z ∈ A then 0 else
    ((P z : Measure Ω) {ω | ((n : ℕ∞) < hittingAfter X A 1 ω) ∧ X n ω = y}).toReal
  let hp : IsStochasticMatrix p := isStochasticMatrix_of_realization (p := p) (P := P) (X := X)
  have hsum : Summable (fun z : E ↦ (p x z).toReal * ‖f z‖) := Summable.of_finite
  calc
    ((P x : Measure Ω)
      {ω | ((((n + 1 : ℕ) : ℕ∞) < hittingAfter X A 1 ω) ∧ X (n + 1) ω = y)}).toReal =
        ∑ z : E, if z ∈ A then 0 else
          ((P x : Measure Ω)
            ({ω | X 1 ω = z} ∩
              {ω | (((n + 1 : ℕ) : ℕ∞) < hittingAfter X A 1 ω) ∧ X (n + 1) ω = y})).toReal := by
              simpa using
                preHitStateSlice_eq_sum_firstStepBranches_all_toReal
                  (P := P) (X := X) (A := A) x y n hX
    _ = ∑ z : E, (p x z).toReal * f z := by
            refine Finset.sum_congr rfl fun z _ ↦ ?_
            by_cases hz : z ∈ A
            · simp [f, hz]
            · have hbranch :=
                preHitStateSliceFirstStepBranch_eq_mul_restartSlice_toReal
                  (p := p) (P := P) (X := X) A x y z n
              simpa [f, hz] using hbranch
    _ = ∫ z, f z ∂discreteMatrixKernel p x := by
          symm
          simpa [f] using integral_discreteMatrixKernel_eq_tsum p hp f x hsum

/-- Helper for Exercise 19.1.1: the pre-hit survival event is measurable because it is the union
of its state slices. -/
private lemma preHitTailEvent_measurable
    (A : Set E) (n : ℕ) (hX : ∀ m : ℕ, Measurable (X m)) :
    MeasurableSet {ω | ((n : ℕ∞) < hittingAfter X A 1 ω)} := by
  have hEq :
      {ω | ((n : ℕ∞) < hittingAfter X A 1 ω)} =
        ⋃ y : E, {ω | ((n : ℕ∞) < hittingAfter X A 1 ω) ∧ X n ω = y} := by
    ext ω
    constructor
    · intro hω
      refine Set.mem_iUnion.2 ⟨X n ω, ?_⟩
      exact ⟨hω, rfl⟩
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨y, hy⟩
      exact hy.1
  rw [hEq]
  exact MeasurableSet.iUnion fun y ↦ preHitStateSlice_measurable (A := A) y n hX

/-- Helper for Exercise 19.1.1: the pre-hit survival probability is the finite sum of the masses
of the corresponding state slices. -/
private lemma preHitTailMass_eq_sum_preHitStateSlices
    (A : Set E) (z : E) (n : ℕ) (hX : ∀ m : ℕ, Measurable (X m)) :
    ((P z : Measure Ω) {ω | ((n : ℕ∞) < hittingAfter X A 1 ω)}).toReal =
      ∑ y : E, ((P z : Measure Ω)
        {ω | ((n : ℕ∞) < hittingAfter X A 1 ω) ∧ X n ω = y}).toReal := by
  let slice : E → Set Ω :=
    fun y ↦ {ω | ((n : ℕ∞) < hittingAfter X A 1 ω) ∧ X n ω = y}
  have hEq :
      {ω | ((n : ℕ∞) < hittingAfter X A 1 ω)} =
        ⋃ y ∈ (Finset.univ : Finset E), slice y := by
    ext ω
    simp [slice]
  have hdisj : (Set.univ : Set E).PairwiseDisjoint slice := by
    intro y _ w _ hyw
    refine Set.disjoint_left.2 ?_
    intro ω hωy hωw
    exact hyw (hωy.2.symm.trans hωw.2)
  -- Proof comment: the survival event is the disjoint finite union of its time-`n` state slices,
  -- so its real measure is the sum of the real measures of those slices.
  simpa [measureReal_def, hEq, slice] using
    (measureReal_biUnion_finset (μ := (P z : Measure Ω)) (s := (Finset.univ : Finset E))
      (f := slice) (by simpa using hdisj)
      (fun y hy ↦ preHitStateSlice_measurable (A := A) y n hX))

/-- Helper for Exercise 19.1.1: the pre-hit survival tail satisfies the same one-step averaging
recursion as the state slices after summing over the state space. -/
private lemma preHitTailMass_succ_eq_kernelAverage_toReal
    (A : Set E) {x : E} (hx : x ∉ A) (n : ℕ) :
    (((P x : Measure Ω) {ω | (((n + 1 : ℕ) : ℕ∞) < hittingAfter X A 1 ω)}).toReal) =
      ∫ z, (if z ∈ A then 0 else
        (((P z : Measure Ω) {ω | ((n : ℕ∞) < hittingAfter X A 1 ω)}).toReal))
        ∂discreteMatrixKernel p x := by
  let hReal :
      IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  have hX : ∀ m : ℕ, Measurable (X m) := hReal.measurable_process
  have hp : IsStochasticMatrix p := isStochasticMatrix_of_realization (p := p) (P := P) (X := X)
  have hrowSum :
      ∀ g : E → ℝ, ∫ z, g z ∂discreteMatrixKernel p x = ∑ z : E, (p x z).toReal * g z := by
    intro g
    have hsum : Summable (fun z : E ↦ (p x z).toReal * ‖g z‖) := Summable.of_finite
    simpa using integral_discreteMatrixKernel_eq_tsum p hp g x hsum
  -- Proof comment: sum the repaired slice recursion over the current state `y`, commute the two
  -- finite sums, and collapse the inner sum back to the survival tail at the restarted state.
  calc
    (((P x : Measure Ω) {ω | (((n + 1 : ℕ) : ℕ∞) < hittingAfter X A 1 ω)}).toReal) =
        ∑ y : E, ((P x : Measure Ω)
          {ω | (((n + 1 : ℕ) : ℕ∞) < hittingAfter X A 1 ω) ∧ X (n + 1) ω = y}).toReal := by
            simpa using
              preHitTailMass_eq_sum_preHitStateSlices (P := P) (X := X) (A := A) x (n + 1) hX
    _ = ∑ y : E, ∫ z, (if z ∈ A then 0 else
          ((P z : Measure Ω) {ω | ((n : ℕ∞) < hittingAfter X A 1 ω) ∧ X n ω = y}).toReal)
          ∂discreteMatrixKernel p x := by
            refine Finset.sum_congr rfl fun y _ ↦ ?_
            exact
              preHitStateSlice_succ_eq_kernelAverage_toReal
                (p := p) (P := P) (X := X) (A := A) (x := x) (y := y) hx n
    _ = ∑ y : E, ∑ z : E, (p x z).toReal * (if z ∈ A then 0 else
          ((P z : Measure Ω) {ω | ((n : ℕ∞) < hittingAfter X A 1 ω) ∧ X n ω = y}).toReal) := by
            refine Finset.sum_congr rfl fun y _ ↦ ?_
            simpa using
              (hrowSum
                (fun z ↦ if z ∈ A then 0 else
                  ((P z : Measure Ω)
                    {ω | ((n : ℕ∞) < hittingAfter X A 1 ω) ∧ X n ω = y}).toReal))
    _ = ∑ z : E, (p x z).toReal * ∑ y : E, (if z ∈ A then 0 else
          ((P z : Measure Ω) {ω | ((n : ℕ∞) < hittingAfter X A 1 ω) ∧ X n ω = y}).toReal) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun z _ ↦ ?_
            rw [Finset.mul_sum]
    _ = ∑ z : E, (p x z).toReal * (if z ∈ A then 0 else
          (((P z : Measure Ω) {ω | ((n : ℕ∞) < hittingAfter X A 1 ω)}).toReal)) := by
            refine Finset.sum_congr rfl fun z _ ↦ ?_
            by_cases hz : z ∈ A
            · simp [hz]
            · simp [hz, preHitTailMass_eq_sum_preHitStateSlices (P := P) (X := X) (A := A) z n hX]
    _ = ∫ z, (if z ∈ A then 0 else
          (((P z : Measure Ω) {ω | ((n : ℕ∞) < hittingAfter X A 1 ω)}).toReal))
          ∂discreteMatrixKernel p x := by
            symm
            simpa using
              (hrowSum
                (fun z ↦ if z ∈ A then 0 else
                  (((P z : Measure Ω) {ω | ((n : ℕ∞) < hittingAfter X A 1 ω)}).toReal)))


/-- Helper for Exercise 19.1.1: almost-sure entrance into `A` on the finite outside state space
improves to a uniform positive lower bound on some bounded entrance window. -/
private lemma uniformHittingWindowForSummableTail
    (p : E → E → ℝ≥0∞)
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    (A : Set E) (hhit : HitsSetAlmostSurely P X A) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ z : E, z ∉ A →
        ε ≤ ((P z : Measure Ω) {ω | hittingAfter X A 1 ω ≤ N}).toReal := by
  let hitWithin : ℕ → Set Ω := fun N ↦ {ω | hittingAfter X A 1 ω ≤ N}
  have hmono : Monotone hitWithin := by
    intro N M hNM ω hω
    exact
      show hittingAfter X A 1 ω ≤ (M : ℕ∞) from
        le_trans (by simpa [hitWithin] using hω)
          (show (N : ℕ∞) ≤ (M : ℕ∞) by exact_mod_cast hNM)
  have hUnion :
      {ω | hittingAfter X A 1 ω < ⊤} = ⋃ N : ℕ, hitWithin N := by
    ext ω
    constructor
    · intro hω
      have hne_top : hittingAfter X A 1 ω ≠ ⊤ := lt_top_iff_ne_top.mp hω
      lift hittingAfter X A 1 ω to ℕ using hne_top with m hm
      refine Set.mem_iUnion.2 ⟨m, ?_⟩
      simpa [hitWithin] using (le_of_eq hm.symm)
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨N, hN⟩
      exact lt_of_le_of_lt (by simpa [hitWithin] using hN : hittingAfter X A 1 ω ≤ (N : ℕ∞))
        (show ((N : ℕ∞) < ⊤) by simp)
  have hexistsWindow :
      ∀ z : {z : E // z ∉ A}, ∃ N : ℕ,
        ((1 / 2 : ℝ≥0∞) < (P z.1 : Measure Ω) (hitWithin N)) := by
    intro z
    have hmeasure_iUnion :
        (P z.1 : Measure Ω) (⋃ N : ℕ, hitWithin N) =
          ⨆ N : ℕ, (P z.1 : Measure Ω) (hitWithin N) := by
      exact hmono.measure_iUnion
    have hhit_union : (P z.1 : Measure Ω) (⋃ N : ℕ, hitWithin N) = 1 := by
      simpa [hUnion] using hhit z.1 z.2
    by_contra hnot
    have hle : (⨆ N : ℕ, (P z.1 : Measure Ω) (hitWithin N)) ≤ (1 / 2 : ℝ≥0∞) := by
      refine iSup_le fun N ↦ ?_
      exact le_of_not_gt (by
        intro hgt
        exact hnot ⟨N, hgt⟩)
    have hle_real :
        ((⨆ N : ℕ, (P z.1 : Measure Ω) (hitWithin N))).toReal ≤ (1 / 2 : ℝ≥0∞).toReal := by
      exact ENNReal.toReal_mono (by simp) hle
    have hiSup_toReal : ((⨆ N : ℕ, (P z.1 : Measure Ω) (hitWithin N))).toReal = 1 := by
      rw [← hmeasure_iUnion, hhit_union]
      simp
    have hone_le_half : (1 : ℝ) ≤ 1 / 2 := by
      calc
        (1 : ℝ) = ((⨆ N : ℕ, (P z.1 : Measure Ω) (hitWithin N))).toReal := by
          symm
          exact hiSup_toReal
        _ ≤ (1 / 2 : ℝ≥0∞).toReal := hle_real
        _ = 1 / 2 := by norm_num
    linarith
  choose N0 hN0 using hexistsWindow
  let Nsup : ℕ := Finset.univ.sup N0
  refine ⟨max 1 Nsup, le_max_left _ _, 1 / 2, by norm_num, ?_⟩
  intro z hz
  let zA : {z : E // z ∉ A} := ⟨z, hz⟩
  have hN0_le : N0 zA ≤ Nsup := by
    exact Finset.le_sup (Finset.mem_univ zA)
  have hsubset : hitWithin (N0 zA) ⊆ hitWithin (max 1 Nsup) := by
    exact hmono (le_trans hN0_le (le_max_right _ _))
  have hmeasure_mono :
      (P z : Measure Ω) (hitWithin (N0 zA)) ≤
        (P z : Measure Ω) (hitWithin (max 1 Nsup)) := by
    exact measure_mono hsubset
  have hhalf_lt :
      (1 / 2 : ℝ≥0∞) < (P z : Measure Ω) (hitWithin (max 1 Nsup)) := by
    exact lt_of_lt_of_le (hN0 zA) hmeasure_mono
  have htoReal :
      (1 / 2 : ℝ) < ((P z : Measure Ω) (hitWithin (max 1 Nsup))).toReal := by
    simpa using
      (ENNReal.toReal_lt_toReal (by simp) (measure_ne_top _ _)).2 hhalf_lt
  -- Proof comment: a single finite window with mass `> 1 / 2` for every outside state gives the
  -- uniform lower bound with the fixed choice `ε = 1 / 2`.
  simpa [hitWithin] using le_of_lt htoReal

/-- Helper for Exercise 19.1.1: almost-sure entrance into `A` gives a geometric block bound for
the pre-hit survival tail, so the full real tail series is summable. -/
private lemma summablePreHitTailMass_of_hitsSetAlmostSurely
    (p : E → E → ℝ≥0∞)
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    (A : Set E) (hhit : HitsSetAlmostSurely P X A) {x : E} (hx : x ∉ A) :
    Summable (fun n : ℕ => ((P x : Measure Ω) {ω | ((n : ℕ∞) < hittingAfter X A 1 ω)}).toReal) := by
  let hReal :
      IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  have hX : ∀ m : ℕ, Measurable (X m) := hReal.measurable_process
  obtain ⟨N, hN, ε, hε_pos, hwindow⟩ :=
    uniformHittingWindowForSummableTail (p := p) (P := P) (X := X) (A := A) hhit
  let tailAt : E → ℕ → ℝ := fun z n ↦
    ((P z : Measure Ω) {ω | ((n : ℕ∞) < hittingAfter X A 1 ω)}).toReal
  let q : ℝ := 1 - ε
  have hε_le_one : ε ≤ 1 := by
    have hle_window : ε ≤ ((P x : Measure Ω) {ω | hittingAfter X A 1 ω ≤ N}).toReal := hwindow x hx
    have hhit_le_one :
        ((P x : Measure Ω) {ω | hittingAfter X A 1 ω ≤ N}).toReal ≤ 1 := by
      simpa using
        (ENNReal.toReal_mono (by simp)
          (prob_le_one :
            (P x : Measure Ω) {ω | hittingAfter X A 1 ω ≤ N} ≤ 1))
    linarith
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    linarith
  have hq_lt_one : q < 1 := by
    dsimp [q]
    linarith
  have htail_zero : ∀ z : E, tailAt z 0 = 1 := by
    intro z
    have hEq : {ω | ((0 : ℕ∞) < hittingAfter X A 1 ω)} = (Set.univ : Set Ω) := by
      ext ω
      constructor
      · intro _
        simp
      · intro _
        exact lt_of_lt_of_le (by simp : (0 : ℕ∞) < 1)
          (le_hittingAfter (u := X) (s := A) (n := 1) ω)
    -- Proof comment: positive-time hitting starts at time `1`, so the zero-tail event is all of
    -- `Ω`, hence every start state has survival mass `1` at time `0`.
    simp [tailAt, hEq]
  have htail_antitone : Antitone (tailAt x) := by
    intro n m hnm
    refine ENNReal.toReal_mono (measure_ne_top _ _) ?_
    exact measure_mono fun ω hω ↦
      show ((n : ℕ∞) < hittingAfter X A 1 ω) from
        lt_of_le_of_lt (by exact_mod_cast hnm) hω
  have hbase :
      ∀ z : E, z ∉ A → tailAt z N ≤ q * tailAt z 0 := by
    intro z hz
    let hitWithin : Set Ω := {ω | hittingAfter X A 1 ω ≤ N}
    have hhit_meas : MeasurableSet hitWithin :=
      by
        have hEq :
            hitWithin = ⋃ j, ⋃ _ : j ∈ Set.Icc 1 N, X j ⁻¹' A := by
          ext ω
          simpa [hitWithin] using
            (hittingAfter_le_iff (u := X) (s := A) (n := 1) (ω := ω) (i := N))
        rw [hEq]
        refine MeasurableSet.iUnion fun j ↦ ?_
        refine MeasurableSet.iUnion fun _ ↦ ?_
        exact hX j (show MeasurableSet A from MeasurableSet.of_discrete)
    have hcomp :
        {ω | ((N : ℕ∞) < hittingAfter X A 1 ω)} = hitWithinᶜ := by
      ext ω
      constructor <;> intro h <;> simpa [hitWithin] using h
    have htail_eq :
        tailAt z N = 1 - ((P z : Measure Ω) hitWithin).toReal := by
      dsimp [tailAt]
      rw [hcomp]
      have hmeasure_compl :
          (P z : Measure Ω) hitWithinᶜ = 1 - (P z : Measure Ω) hitWithin := by
        simpa [hitWithin] using measure_compl (μ := (P z : Measure Ω)) hhit_meas
      rw [hmeasure_compl]
      have hle : (P z : Measure Ω) hitWithin ≤ 1 := prob_le_one
      simpa using ENNReal.toReal_sub_of_le hle (by simp : (1 : ℝ≥0∞) ≠ ∞)
    have hwindow_z : ε ≤ ((P z : Measure Ω) hitWithin).toReal := hwindow z hz
    have htail_le_q : tailAt z N ≤ q := by
      rw [htail_eq]
      dsimp [q]
      linarith
    simpa [htail_zero z] using htail_le_q
  have hp : IsStochasticMatrix p := isStochasticMatrix_of_realization (p := p) (P := P) (X := X)
  have hrowSum :
      ∀ z : E, ∀ g : E → ℝ,
        ∫ w, g w ∂discreteMatrixKernel p z = ∑ w : E, (p z w).toReal * g w := by
    intro z g
    have hsum : Summable (fun w : E ↦ (p z w).toReal * ‖g w‖) := Summable.of_finite
    simpa using integral_discreteMatrixKernel_eq_tsum p hp g z hsum
  have hblock :
      ∀ n : ℕ, ∀ z : E, z ∉ A → tailAt z (n + N) ≤ q * tailAt z n := by
    intro n
    induction n with
    | zero =>
        simpa using hbase
    | succ n ihn =>
        intro z hz
        -- Proof comment: push the fixed-window contraction through one more killed-kernel step
        -- and use the induction hypothesis statewise inside the finite row sum.
        calc
          tailAt z (n.succ + N)
              = tailAt z ((n + N) + 1) := by
                  simp [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          _ = ∫ w, (if w ∈ A then 0 else tailAt w (n + N)) ∂discreteMatrixKernel p z := by
                simpa [tailAt] using
                  preHitTailMass_succ_eq_kernelAverage_toReal
                    (p := p) (P := P) (X := X) (A := A) (x := z) hz (n + N)
          _ = ∑ w : E, (p z w).toReal * (if w ∈ A then 0 else tailAt w (n + N)) := by
                exact hrowSum z (fun w ↦ if w ∈ A then 0 else tailAt w (n + N))
          _ ≤ ∑ w : E, (p z w).toReal * (if w ∈ A then 0 else q * tailAt w n) := by
                refine Finset.sum_le_sum fun w _ ↦ ?_
                by_cases hw : w ∈ A
                · simp [hw]
                · exact mul_le_mul_of_nonneg_left (by simpa [hw] using ihn w hw)
                    ENNReal.toReal_nonneg
          _ = ∑ w : E, q * ((p z w).toReal * (if w ∈ A then 0 else tailAt w n)) := by
                refine Finset.sum_congr rfl fun w _ ↦ ?_
                by_cases hw : w ∈ A
                · simp [hw]
                · simp [hw, mul_assoc, mul_left_comm, mul_comm]
          _ = q * ∑ w : E, (p z w).toReal * (if w ∈ A then 0 else tailAt w n) := by
                rw [Finset.mul_sum]
          _ = q * ∫ w, (if w ∈ A then 0 else tailAt w n) ∂discreteMatrixKernel p z := by
                congr 1
                symm
                exact hrowSum z (fun w ↦ if w ∈ A then 0 else tailAt w n)
          _ = q * tailAt z (n + 1) := by
                congr 1
                symm
                simpa [tailAt] using
                  preHitTailMass_succ_eq_kernelAverage_toReal
                    (p := p) (P := P) (X := X) (A := A) (x := z) hz n
  have hmultiples_le : ∀ k : ℕ, tailAt x (N * k) ≤ q ^ k := by
    intro k
    induction k with
    | zero =>
        simp [htail_zero, tailAt]
    | succ k ih =>
        have hstep := hblock (N * k) x hx
        have hqpow : q * q ^ k = q ^ k.succ := by
          simp [pow_succ, mul_comm, mul_left_comm, mul_assoc]
        calc
          tailAt x (N * k.succ) = tailAt x (N * k + N) := by
            rw [Nat.mul_succ]
          _ ≤ q * tailAt x (N * k) := hstep
          _ ≤ q * q ^ k := mul_le_mul_of_nonneg_left ih hq_nonneg
          _ = q ^ k.succ := hqpow
  have hmultiples_summable : Summable (fun k : ℕ ↦ tailAt x (N * k)) := by
    refine Summable.of_nonneg_of_le (fun k ↦ by positivity) hmultiples_le ?_
    exact summable_geometric_of_lt_one hq_nonneg hq_lt_one
  letI : NeZero N := ⟨by
    have hpos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one hN
    exact Nat.ne_of_gt hpos⟩
  have hindicator_summable :
      Summable ({n : ℕ | (n : ZMod N) = 0}.indicator (tailAt x)) := by
    simpa [Nat.zero_add] using
      (summable_indicator_mod_iff_summable (m := N) (k := 0) (f := tailAt x)).2
        hmultiples_summable
  -- Proof comment: the survival tail is decreasing, so summability on the `0 mod N` residue
  -- class upgrades to summability of the full tail sequence.
  exact
    (summable_indicator_mod_iff (m := N) (f := tailAt x) htail_antitone 0).1
      hindicator_summable

/-- Helper for Exercise 19.1.1: pathwise, the pre-hit visit-count indicator series is the counting
measure of the corresponding visit-index set. -/
private lemma tsum_preHitStateSliceIndicators_eq_count
    (A : Set E) (y : E) (ω : Ω) :
    (∑' n : ℕ,
      Set.indicator
        {ω' | ((n : ℕ∞) < hittingAfter X A 1 ω' ∧ X n ω' = y)}
        (fun _ ↦ (1 : ℝ≥0∞)) ω) =
      Measure.count {n : ℕ | ((n : ℕ∞) < hittingAfter X A 1 ω ∧ X n ω = y)} := by
  rw [Measure.count_apply MeasurableSet.of_discrete]
  -- Proof comment: rewrite the ambient indicator series as the counting sum over the subtype of
  -- valid visit times, then evaluate the constant-one series as the encard of that subtype.
  calc
    (∑' n : ℕ,
      Set.indicator
        {ω' | ((n : ℕ∞) < hittingAfter X A 1 ω' ∧ X n ω' = y)}
        (fun _ ↦ (1 : ℝ≥0∞)) ω)
        = ∑' _ : {n : ℕ | ((n : ℕ∞) < hittingAfter X A 1 ω ∧ X n ω = y)}, (1 : ℝ≥0∞) := by
            symm
            simpa [Set.indicator_apply] using
              (tsum_subtype
                (s := {n : ℕ | ((n : ℕ∞) < hittingAfter X A 1 ω ∧ X n ω = y)})
                (f := fun _ : ℕ ↦ (1 : ℝ≥0∞)))
    _ = ({n : ℕ | ((n : ℕ∞) < hittingAfter X A 1 ω ∧ X n ω = y)}).encard := ENNReal.tsum_one

/-- Helper for Exercise 19.1.1: each fixed-target pre-hit slice series is summable because every
slice mass is bounded by the corresponding survival tail. -/
private lemma summablePreHitStateSliceMasses_of_hitsSetAlmostSurely
    (p : E → E → ℝ≥0∞)
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    (A : Set E) (hhit : HitsSetAlmostSurely P X A) {x y : E} (hx : x ∉ A) :
    Summable (fun n : ℕ =>
      ((P x : Measure Ω) {ω | ((n : ℕ∞) < hittingAfter X A 1 ω) ∧ X n ω = y}).toReal) := by
  have htail :
      Summable (fun n : ℕ =>
        ((P x : Measure Ω) {ω | ((n : ℕ∞) < hittingAfter X A 1 ω)}).toReal) :=
    summablePreHitTailMass_of_hitsSetAlmostSurely (p := p) (P := P) (X := X) (A := A) hhit hx
  -- Proof comment: each state slice sits inside the full survival tail at the same time, so the
  -- repaired tail summability immediately dominates the slice series termwise.
  refine Summable.of_nonneg_of_le (fun n ↦ by positivity) ?_ htail
  intro n
  refine ENNReal.toReal_mono (measure_ne_top _ _) ?_
  exact measure_mono fun ω hω ↦ hω.1

/-- Helper for Exercise 19.1.1: in the interior branch, the killed Green function is the
`ℝ≥0∞` series of its pre-hit state-slice masses. -/
private lemma killedGreenFunction_eq_tsum_preHitStateSliceMasses_of_not_mem
    (p : E → E → ℝ≥0∞)
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    (A : Set E) {x y : E} (hx : x ∉ A) (hy : y ∉ A) :
    killedGreenFunction P X A x y =
      ∑' n : ℕ, (P x : Measure Ω)
        {ω | ((n : ℕ∞) < hittingAfter X A 1 ω) ∧ X n ω = y} := by
  let hReal :
      IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  have hX : ∀ n : ℕ, Measurable (X n) := hReal.measurable_process
  -- Proof comment: in the interior branch the pathwise killed visit count is exactly the counting
  -- measure of the pre-hit visit-index set, so Tonelli rewrites its expectation as the slice
  -- mass series.
  calc
    killedGreenFunction P X A x y =
        ∫⁻ ω,
          Measure.count {n : ℕ | ((n : ℕ∞) < hittingAfter X A 1 ω) ∧ X n ω = y}
          ∂(P x : Measure Ω) := by
            rw [killedGreenFunction]
            refine lintegral_congr_ae <| Filter.Eventually.of_forall fun ω ↦ ?_
            simp [killedVisitCount, hx, hy]
    _ =
        ∫⁻ ω,
          ∑' n : ℕ,
            Set.indicator
              {ω' | ((n : ℕ∞) < hittingAfter X A 1 ω' ∧ X n ω' = y)}
              (fun _ ↦ (1 : ℝ≥0∞)) ω
          ∂(P x : Measure Ω) := by
            refine lintegral_congr_ae <| Filter.Eventually.of_forall fun ω ↦ ?_
            symm
            exact tsum_preHitStateSliceIndicators_eq_count (X := X) (A := A) y ω
    _ =
        ∑' n : ℕ,
          ∫⁻ ω,
            Set.indicator
              {ω' | ((n : ℕ∞) < hittingAfter X A 1 ω' ∧ X n ω' = y)}
              (fun _ ↦ (1 : ℝ≥0∞)) ω
            ∂(P x : Measure Ω) := by
              rw [lintegral_tsum fun n ↦
                (measurable_const.indicator
                  (preHitStateSlice_measurable (X := X) (A := A) y n hX)).aemeasurable]
    _ =
        ∑' n : ℕ, (P x : Measure Ω)
          {ω | ((n : ℕ∞) < hittingAfter X A 1 ω) ∧ X n ω = y} := by
            refine tsum_congr fun n ↦ ?_
            simpa using
              (lintegral_indicator_one
                (μ := (P x : Measure Ω))
                (s := {ω | ((n : ℕ∞) < hittingAfter X A 1 ω) ∧ X n ω = y})
                (preHitStateSlice_measurable (X := X) (A := A) y n hX))

/-- Helper for Exercise 19.1.1: in the interior branch, the time-`0` part of the killed Green
series is the Kronecker term and the rest is the positive-time pre-hit slice series. -/
private lemma killedGreenFunction_eq_kroneckerDelta_add_tsum_preHitStateSliceMasses_of_not_mem
    (p : E → E → ℝ≥0∞)
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    (A : Set E) {x y : E} (hx : x ∉ A) (hy : y ∉ A) :
    killedGreenFunction P X A x y =
      (if x = y then 1 else 0) +
        ∑' n : ℕ, (P x : Measure Ω)
          {ω | (((n + 1 : ℕ) : ℕ∞) < hittingAfter X A 1 ω) ∧ X (n + 1) ω = y} := by
  let hReal :
      IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  have hzero :
      (P x : Measure Ω) {ω | ((0 : ℕ∞) < hittingAfter X A 1 ω) ∧ X 0 ω = y} =
        if x = y then 1 else 0 := by
    have hEq :
        {ω | ((0 : ℕ∞) < hittingAfter X A 1 ω) ∧ X 0 ω = y} = X 0 ⁻¹' ({y} : Set E) := by
      ext ω
      constructor
      · intro hω
        simpa [Set.mem_preimage] using hω.2
      · intro hω
        refine ⟨?_, ?_⟩
        · exact lt_of_lt_of_le (by simp : (0 : ℕ∞) < 1)
            (le_hittingAfter (u := X) (s := A) (n := 1) ω)
        · simpa [Set.mem_preimage] using hω
    have hinit :
        (P x : Measure Ω) (X 0 ⁻¹' ({y} : Set E)) = if x = y then 1 else 0 := by
      have hstart :=
        congrArg (fun ν : Measure E ↦ ν ({y} : Set E)) (hReal.initial_eq x)
      by_cases hxy : x = y
      · subst hxy
        simpa [Measure.map_apply (hReal.measurable_process 0) (measurableSet_singleton x)]
          using hstart
      · simpa [Measure.map_apply (hReal.measurable_process 0) (measurableSet_singleton y), hxy]
          using hstart
    rw [hEq, hinit]
  -- Proof comment: first rewrite the killed Green function as the full pre-hit slice series, then
  -- split off the time-`0` slice and identify it with the initial-state Kronecker term.
  calc
    killedGreenFunction P X A x y =
        ∑' n : ℕ, (P x : Measure Ω)
          {ω | ((n : ℕ∞) < hittingAfter X A 1 ω) ∧ X n ω = y} := by
            exact
              killedGreenFunction_eq_tsum_preHitStateSliceMasses_of_not_mem
                (p := p) (P := P) (X := X) (A := A) hx hy
    _ = (P x : Measure Ω) {ω | ((0 : ℕ∞) < hittingAfter X A 1 ω) ∧ X 0 ω = y} +
          ∑' n : ℕ, (P x : Measure Ω)
            {ω | (((n + 1 : ℕ) : ℕ∞) < hittingAfter X A 1 ω) ∧ X (n + 1) ω = y} := by
              simpa using
                (tsum_eq_zero_add' ENNReal.summable
                  (f := fun n : ℕ ↦ (P x : Measure Ω)
                    {ω | ((n : ℕ∞) < hittingAfter X A 1 ω) ∧ X n ω = y}))
    _ = (if x = y then 1 else 0) +
          ∑' n : ℕ, (P x : Measure Ω)
            {ω | (((n + 1 : ℕ) : ℕ∞) < hittingAfter X A 1 ω) ∧ X (n + 1) ω = y} := by
              rw [hzero]

/-- Helper for Exercise 19.1.1: in the interior branch, taking `toReal` transports the full
pre-hit slice series of the killed Green function to the matrix entry. -/
private lemma killedGreenMatrixView_eq_tsum_preHitStateSliceMasses_of_not_mem
    (p : E → E → ℝ≥0∞)
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    (A : Set E) {x y : E} (hx : x ∉ A) (hy : y ∉ A) :
    killedGreenMatrixView P X A x y =
      ∑' n : ℕ, ((P x : Measure Ω)
        {ω | ((n : ℕ∞) < hittingAfter X A 1 ω) ∧ X n ω = y}).toReal := by
  -- Proof comment: the interior killed Green entry is the `toReal` of the `ℝ≥0∞` slice series,
  -- and every slice mass is finite because it is a probability event.
  rw [killedGreenMatrixView]
  rw [killedGreenFunction_eq_tsum_preHitStateSliceMasses_of_not_mem
    (p := p) (P := P) (X := X) (A := A) hx hy]
  simpa using
    (ENNReal.tsum_toReal_eq
      (f := fun n : ℕ ↦ (P x : Measure Ω)
        {ω | ((n : ℕ∞) < hittingAfter X A 1 ω) ∧ X n ω = y})
      (fun _ ↦ measure_ne_top _ _))

/-- Helper for Exercise 19.1.1: hitting `A` from time `1` is the union of the positive-time
coordinate hits of `A`. -/
private lemma hittingAfter_one_lt_top_event_eq_iUnion_timeSlices
    (A : Set E) :
    {ω | hittingAfter X A 1 ω < ⊤} = ⋃ n : ℕ, X n.succ ⁻¹' A := by
  ext ω
  constructor
  · intro hω
    have hne_top : hittingAfter X A 1 ω ≠ ⊤ := lt_top_iff_ne_top.mp hω
    lift hittingAfter X A 1 ω to ℕ using hne_top with m hm
    have hm_ne_top : hittingAfter X A 1 ω ≠ ⊤ := by
      rw [← hm]
      simp
    have hm_idx : (hittingAfter X A 1 ω).untopA = m := by
      rw [← hm, WithTop.untopA_eq_untop (by simp)]
      exact (WithTop.untop_eq_iff (by simp)).2 rfl
    have hm_mem : X m ω ∈ A := by
      -- Proof comment: a finite first positive hit lands in `A`.
      simpa [hm_idx] using
        hittingAfter_mem_set_of_ne_top (u := X) (s := A) (n := 1) (ω := ω) hm_ne_top
    have hm_ne_zero : m ≠ 0 := by
      intro hm_zero
      have hτ_ge : (1 : ℕ∞) ≤ hittingAfter X A 1 ω :=
        le_hittingAfter (u := X) (s := A) (n := 1) ω
      have hm_zero_top : hittingAfter X A 1 ω = 0 := by
        symm
        simpa [hm_zero] using hm
      have habsurd : (1 : ℕ∞) ≤ (0 : ℕ∞) := hm_zero_top ▸ hτ_ge
      simp at habsurd
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm_ne_zero
    exact Set.mem_iUnion.2 ⟨n, by simpa [Set.mem_preimage] using hm_mem⟩
  · intro hω
    rcases Set.mem_iUnion.1 hω with ⟨n, hn⟩
    have hn_mem : X n.succ ω ∈ A := by
      simpa [Set.mem_preimage] using hn
    have hle : hittingAfter X A 1 ω ≤ n.succ := by
      exact
        hittingAfter_le_of_mem (u := X) (s := A) (n := 1) (ω := ω)
          (Nat.succ_le_succ (Nat.zero_le n)) hn_mem
    exact lt_of_le_of_lt hle (by simp)

/-- Helper for Exercise 19.1.1: the bounded entrance event `{τ_A ≤ N}` is measurable. -/
private lemma hittingAfter_one_le_event_measurable
    (A : Set E) (N : ℕ) (hX : ∀ m : ℕ, Measurable (X m)) :
    MeasurableSet {ω | hittingAfter X A 1 ω ≤ N} := by
  have hEq :
      {ω | hittingAfter X A 1 ω ≤ N} = ⋃ j, ⋃ _ : j ∈ Set.Icc 1 N, X j ⁻¹' A := by
    ext ω
    simpa using
      (hittingAfter_le_iff (u := X) (s := A) (n := 1) (ω := ω) (i := N))
  -- Proof comment: a bounded positive-time hit means that one of the coordinates `1, ..., N`
  -- already lies in `A`, so the event is a countable union of measurable coordinate preimages.
  rw [hEq]
  refine MeasurableSet.iUnion fun j ↦ ?_
  refine MeasurableSet.iUnion fun _ ↦ ?_
  exact hX j (show MeasurableSet A from MeasurableSet.of_discrete)

/-- Helper for Exercise 19.1.1: avoiding `A` during the first `n` positive times is a measurable
history event. -/
private def avoidFirstPositiveTimesEvent (A : Set E) (n : ℕ) : Set Ω :=
  {ω | ∀ m < n, X (m + 1) ω ∉ A}

/-- Helper for Exercise 19.1.1: the positive-time avoidance event is measurable. -/
private lemma avoidFirstPositiveTimesEvent_measurable
    (A : Set E) (hX : ∀ m : ℕ, Measurable (X m)) :
    ∀ n : ℕ, MeasurableSet (avoidFirstPositiveTimesEvent (X := X) A n)
  | 0 => by
      simp [avoidFirstPositiveTimesEvent]
  | n + 1 => by
      have hprev : MeasurableSet (avoidFirstPositiveTimesEvent (X := X) A n) :=
        avoidFirstPositiveTimesEvent_measurable A hX n
      have hstep : MeasurableSet {ω | X (n + 1) ω ∉ A} := by
        change MeasurableSet (X (n + 1) ⁻¹' Aᶜ)
        exact
          (hX (n + 1))
            (show MeasurableSet Aᶜ from (MeasurableSet.of_discrete : MeasurableSet A).compl)
      have hEq :
          avoidFirstPositiveTimesEvent (X := X) A (n + 1) =
            avoidFirstPositiveTimesEvent (X := X) A n ∩ {ω | X (n + 1) ω ∉ A} := by
        ext ω
        constructor
        · intro hω
          refine ⟨?_, ?_⟩
          · intro m hm
            exact hω m (Nat.lt_succ_of_lt hm)
          · exact hω n (Nat.lt_succ_self n)
        · rintro ⟨hω, hn⟩ m hm
          rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hm' | rfl
          · exact hω m hm'
          · exact hn
      rw [hEq]
      exact hprev.inter hstep

/-- Helper for Exercise 19.1.1: the exact first-entrance slice at time `n + 1` is the event that
the chain avoids `A` during the first `n` positive times and lands in `y` at time `n + 1`. -/
private def firstEntranceSliceEvent (A : Set E) (y : E) (n : ℕ) : Set Ω :=
  avoidFirstPositiveTimesEvent (X := X) A n ∩ {ω | X (n + 1) ω = y}

/-- Helper for Exercise 19.1.1: exact first-entrance slices are measurable. -/
private lemma firstEntranceSliceEvent_measurable
    (A : Set E) (y : E) (n : ℕ) (hX : ∀ m : ℕ, Measurable (X m)) :
    MeasurableSet (firstEntranceSliceEvent (X := X) A y n) := by
  rw [firstEntranceSliceEvent]
  refine (avoidFirstPositiveTimesEvent_measurable (X := X) A hX n).inter ?_
  change MeasurableSet (X (n + 1) ⁻¹' ({y} : Set E))
  exact (hX (n + 1)) (measurableSet_singleton y)

/-- Helper for Exercise 19.1.1: for a boundary target `y ∈ A`, the exact slice at time `n + 1`
is exactly the event that the first positive entrance time equals `n + 1` and lands at `y`. -/
private lemma mem_firstEntranceSliceEvent_iff
    (A : Set E) {y : E} (hy : y ∈ A) (n : ℕ) {ω : Ω} :
    ω ∈ firstEntranceSliceEvent (X := X) A y n ↔
      hittingAfter X A 1 ω = n + 1 ∧
        stoppedValue X (hittingAfter X A 1) ω = y := by
  rw [firstEntranceSliceEvent]
  constructor
  · rintro ⟨havoid, hxy⟩
    have hmem : X (n + 1) ω ∈ A := by
      exact hxy.symm ▸ hy
    have hτ_le : hittingAfter X A 1 ω ≤ n + 1 := by
      exact
        hittingAfter_le_of_mem (u := X) (s := A) (n := 1) (ω := ω)
          (Nat.succ_le_succ (Nat.zero_le n)) hmem
    have hτ_ge : n + 1 ≤ hittingAfter X A 1 ω := by
      by_contra hlt
      have hlt' : hittingAfter X A 1 ω < n + 1 := lt_of_not_ge hlt
      rcases (hittingAfter_lt_iff (u := X) (s := A) (n := 1) (ω := ω) (i := n + 1)).1 hlt' with
        ⟨j, hj, hjA⟩
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hj.1)
      have hk_lt : k < n := by
        simpa using hj.2
      exact (havoid k hk_lt) hjA
    have hτ_eq : hittingAfter X A 1 ω = n + 1 := le_antisymm hτ_le hτ_ge
    have hτ_idx : (hittingAfter X A 1 ω).untopA = n + 1 := by
      rw [hτ_eq, WithTop.untopA_eq_untop (by simp)]
      exact (WithTop.untop_eq_iff (by simp)).2 rfl
    refine ⟨hτ_eq, ?_⟩
    -- Proof comment: after identifying the first entrance time, `stoppedValue` is the same
    -- coordinate `X (n + 1)`.
    rw [stoppedValue, hτ_idx]
    exact hxy
  · rintro ⟨hτ_eq, hstop⟩
    refine ⟨?_, ?_⟩
    · intro m hm
      have hm_lt_τ : (m + 1 : ℕ∞) < hittingAfter X A 1 ω := by
        rw [hτ_eq]
        change ((m : ℕ∞) + 1) < ((n : ℕ∞) + 1)
        simpa [Nat.cast_add] using (WithTop.coe_lt_coe.2 (Nat.succ_lt_succ hm))
      -- Proof comment: every earlier positive-time coordinate lies strictly before the first
      -- entrance time, so it stays outside `A`.
      exact
        notMem_of_lt_hittingAfter (u := X) (s := A) (n := 1) (ω := ω) (k := m + 1) hm_lt_τ
          (by simp)
    · have hτ_idx : (hittingAfter X A 1 ω).untopA = n + 1 := by
        rw [hτ_eq, WithTop.untopA_eq_untop (by simp)]
        exact (WithTop.untop_eq_iff (by simp)).2 rfl
      calc
        X (n + 1) ω = stoppedValue X (hittingAfter X A 1) ω := by
          rw [stoppedValue, hτ_idx]
        _ = y := hstop

/-- Helper for Exercise 19.1.1: a fixed first-step branch of a successor exact entrance slice is
the finite union of shifted tuple singletons whose first `n + 1` coordinates stay outside `A`,
start at `z`, and end at `y`. -/
private lemma firstEntranceSuccessorBranch_eq_biUnion_shiftedTupleSingletons
    (A : Set E) (y z : E) (n : ℕ) :
    ({ω | X 1 ω = z} ∩ firstEntranceSliceEvent (X := X) A y (n + 1)) =
      ⋃ t ∈ (Finset.univ.filter fun t : Fin (n + 2) → E ↦
        t 0 = z ∧ t (Fin.last (n + 1)) = y ∧
          ∀ i : Fin (n + 1), t i.castSucc ∉ A),
        (realizedTupleFromStep X (n + 2)) ⁻¹' ({t} : Set (Fin (n + 2) → E)) := by
  ext ω
  simp only [firstEntranceSliceEvent, avoidFirstPositiveTimesEvent, Set.mem_setOf_eq,
    Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨hstep, havoid, hfinal⟩
    let t : Fin (n + 2) → E := realizedTupleFromStep X (n + 2) ω
    refine ⟨t, ?_, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa [t, realizedTupleFromStep] using hstep
    · simpa [t, realizedTupleFromStep] using hfinal
    · intro i
      -- Proof comment: the exact entrance slice records that the first `n + 1` positive-time
      -- coordinates avoid `A`, which is exactly the shifted tuple prefix condition.
      simpa [t, realizedTupleFromStep] using havoid (i : ℕ) i.2
  · rintro ⟨t, ht, htup⟩
    rcases ht with ⟨ht0, hty, havoid⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa [realizedTupleFromStep, ht0] using congrFun htup 0
    · intro m hm
      let i : Fin (n + 1) := ⟨m, hm⟩
      have hcoord : X (m + 1) ω = t i.castSucc := by
        simpa [realizedTupleFromStep, i] using congrFun htup i.castSucc
      simpa [hcoord] using havoid i
    · simpa [realizedTupleFromStep, hty] using congrFun htup (Fin.last (n + 1))

/-- Helper for Exercise 19.1.1: each first-step branch of a successor exact entrance slice is
ambient measurable. -/
private lemma firstEntranceSlice_firstStepBranch_measurable
    (A : Set E) (y z : E) (n : ℕ) (hX : ∀ m : ℕ, Measurable (X m)) :
    MeasurableSet
      ({ω | X 1 ω = z} ∩ firstEntranceSliceEvent (X := X) A y (n + 1)) := by
  -- Proof comment: a first-step branch is the intersection of the time-`1` singleton event with
  -- the successor exact-entrance slice.
  refine (hX 1 (measurableSet_singleton z)).inter ?_
  exact firstEntranceSliceEvent_measurable (X := X) (A := A) y (n + 1) hX

/-- Helper for Exercise 19.1.1: if the first step lands in `A`, then the successor exact
entrance slice is empty on that branch. -/
private lemma firstEntranceSlice_firstStepBranch_eq_empty_of_mem
    (A : Set E) {y z : E} (hz : z ∈ A) (n : ℕ) :
    ({ω | X 1 ω = z} ∩ firstEntranceSliceEvent (X := X) A y (n + 1)) = (∅ : Set Ω) := by
  ext ω
  constructor
  · rintro ⟨hstep, hslice⟩
    have hnotA : X 1 ω ∉ A := by
      exact hslice.1 0 (Nat.zero_lt_succ n)
    exact False.elim (hnotA (hstep.symm ▸ hz))
  · intro hω
    simpa using hω

/-- Helper for Exercise 19.1.1: distinct first-step branches of the same successor exact entrance
slice are disjoint. -/
private lemma firstEntranceSlice_firstStepBranch_pairwiseDisjoint
    (A : Set E) (y : E) (n : ℕ) :
    (Set.univ : Set E).PairwiseDisjoint fun z : E ↦
      ({ω | X 1 ω = z} ∩ firstEntranceSliceEvent (X := X) A y (n + 1)) := by
  intro z _ w _ hzw
  -- Proof comment: two different first-step branches prescribe different values for `X 1`.
  refine Set.disjoint_left.2 ?_
  intro ω hz hw
  exact hzw (hz.1.symm.trans hw.1)

/-- Helper for Exercise 19.1.1: a successor exact entrance slice is the finite union of its
first-step branches over states outside `A`. -/
private lemma firstEntranceSlice_eq_biUnion_firstStepOutside
    (A : Set E) (y : E) (n : ℕ) :
    firstEntranceSliceEvent (X := X) A y (n + 1) =
      ⋃ z ∈ (Finset.univ.filter fun z : E ↦ z ∉ A),
        ({ω | X 1 ω = z} ∩ firstEntranceSliceEvent (X := X) A y (n + 1)) := by
  ext ω
  simp only [firstEntranceSliceEvent, avoidFirstPositiveTimesEvent, Finset.mem_filter,
    Finset.mem_univ, true_and, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
  constructor
  · intro hω
    have hnotA : X 1 ω ∉ A := hω.1 0 (Nat.zero_lt_succ n)
    -- Proof comment: on a successor exact slice, the first step is itself an outside-`A`
    -- branch witness.
    exact ⟨X 1 ω, hnotA, rfl, hω⟩
  · intro hω
    rcases hω with ⟨z, -, -, hzω⟩
    exact hzω

/-- Helper for Exercise 19.1.1: the real mass of a successor exact entrance slice is the finite
sum of the real masses of its first-step branches outside `A`. -/
private lemma firstEntranceSlice_eq_sum_firstStepBranches_toReal
    (A : Set E) (x y : E) (n : ℕ) (hX : ∀ m : ℕ, Measurable (X m)) :
    ((P x : Measure Ω) (firstEntranceSliceEvent (X := X) A y (n + 1))).toReal =
      Finset.sum (Finset.univ.filter fun z : E ↦ z ∉ A) fun z ↦
        ((P x : Measure Ω)
          ({ω | X 1 ω = z} ∩ firstEntranceSliceEvent (X := X) A y (n + 1))).toReal := by
  let branch : E → Set Ω := fun z ↦
    {ω | X 1 ω = z} ∩ firstEntranceSliceEvent (X := X) A y (n + 1)
  have hEq :
      firstEntranceSliceEvent (X := X) A y (n + 1) =
        ⋃ z ∈ (Finset.univ.filter fun z : E ↦ z ∉ A), branch z := by
    simpa [branch] using firstEntranceSlice_eq_biUnion_firstStepOutside (X := X) (A := A) y n
  have hdisj : (Set.univ : Set E).PairwiseDisjoint branch := by
    simpa [branch] using
      firstEntranceSlice_firstStepBranch_pairwiseDisjoint (X := X) (A := A) y n
  have hmeas : ∀ z : E, MeasurableSet (branch z) := by
    intro z
    simpa [branch] using
      firstEntranceSlice_firstStepBranch_measurable (X := X) (A := A) y z n hX
  have hdisjOutside :
      {z : E | z ∉ A}.PairwiseDisjoint branch := by
    intro z hz w hw hzw
    exact hdisj (by simp) (by simp) hzw
  -- Proof comment: after partitioning by the first step, the slice mass is the real measure of
  -- a disjoint finite union.
  have hmass :
      ((P x : Measure Ω) (⋃ z ∈ (Finset.univ.filter fun z : E ↦ z ∉ A), branch z)).toReal =
        Finset.sum (Finset.univ.filter fun z : E ↦ z ∉ A) fun z ↦
          ((P x : Measure Ω) (branch z)).toReal := by
    simpa [measureReal_def, branch] using
      (measureReal_biUnion_finset (μ := (P x : Measure Ω))
        (s := Finset.univ.filter fun z : E ↦ z ∉ A) (f := branch)
        (by simpa using hdisjOutside) (fun z _ ↦ hmeas z))
  calc
    ((P x : Measure Ω) (firstEntranceSliceEvent (X := X) A y (n + 1))).toReal =
        ((P x : Measure Ω) (⋃ z ∈ (Finset.univ.filter fun z : E ↦ z ∉ A), branch z)).toReal := by
          rw [hEq]
    _ = Finset.sum (Finset.univ.filter fun z : E ↦ z ∉ A) fun z ↦
          ((P x : Measure Ω) (branch z)).toReal := hmass

/-- Helper for Exercise 19.1.1: the first-step partition of a successor exact entrance slice can
be written as a full finite row sum by inserting zero branches on `A`. -/
private lemma firstEntranceSlice_eq_sum_firstStepBranches_all_toReal
    (A : Set E) (x y : E) (n : ℕ) (hX : ∀ m : ℕ, Measurable (X m)) :
    ((P x : Measure Ω) (firstEntranceSliceEvent (X := X) A y (n + 1))).toReal =
      ∑ z : E, if z ∈ A then 0 else
        ((P x : Measure Ω)
          ({ω | X 1 ω = z} ∩ firstEntranceSliceEvent (X := X) A y (n + 1))).toReal := by
  let branch : E → Set Ω := fun z ↦
    {ω | X 1 ω = z} ∩ firstEntranceSliceEvent (X := X) A y (n + 1)
  rw [firstEntranceSlice_eq_sum_firstStepBranches_toReal (P := P) (X := X) (A := A) x y n hX]
  -- Proof comment: replace the filtered outside-`A` sum by a full finite sum and use the zero
  -- contribution of branches indexed by `A`.
  simpa [branch] using
    (Finset.sum_filter (s := Finset.univ) (p := fun z : E ↦ z ∉ A)
      (f := fun z ↦ ((P x : Measure Ω) (branch z)).toReal))

/-- Helper for Exercise 19.1.1: when the restarted chain starts from `z ∉ A`, the finite union of
zero-start tuple singletons encoding a length-`n` exact entrance slice is exactly the event that
the start state is `z` and the chain first enters `A` at `y` after `n + 1` steps. -/
private lemma firstEntranceRestartedZeroTupleUnion_eq_startInterSlice
    (A : Set E) {z y : E} (hz : z ∉ A) (n : ℕ) :
    (⋃ t ∈ (Finset.univ.filter fun t : Fin (n + 2) → E ↦
      t 0 = z ∧ t (Fin.last (n + 1)) = y ∧
        ∀ i : Fin (n + 1), t i.castSucc ∉ A),
      (realizedTupleFromZero X (n + 2)) ⁻¹' ({t} : Set (Fin (n + 2) → E))) =
        X 0 ⁻¹' ({z} : Set E) ∩ firstEntranceSliceEvent (X := X) A y n := by
  ext ω
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_iUnion, exists_prop,
    Set.mem_inter_iff, Set.mem_preimage]
  constructor
  · rintro ⟨t, ⟨ht0, hty, havoid⟩, htup⟩
    refine ⟨?_, ?_⟩
    · simpa [realizedTupleFromZero, ht0] using congrFun htup 0
    · rw [firstEntranceSliceEvent]
      refine ⟨?_, ?_⟩
      · intro m hm
        let i : Fin (n + 1) := ⟨m + 1, Nat.succ_lt_succ hm⟩
        have hcoord : X (m + 1) ω = t i.castSucc := by
          simpa [realizedTupleFromZero, i] using congrFun htup i.castSucc
        simpa [hcoord] using havoid i
      · simpa [realizedTupleFromZero, hty] using congrFun htup (Fin.last (n + 1))
  · rintro ⟨hstart, hslice⟩
    rw [firstEntranceSliceEvent] at hslice
    let t : Fin (n + 2) → E := realizedTupleFromZero X (n + 2) ω
    refine ⟨t, ?_, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa [t, realizedTupleFromZero] using hstart
    · simpa [t, realizedTupleFromZero] using hslice.2
    · intro i
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
      · have hstartEq : X 0 ω = z := by
          simpa [Set.mem_preimage] using hstart
        have h0notA : X 0 ω ∉ A := by
          simpa [hstartEq] using hz
        simpa [t, realizedTupleFromZero] using h0notA
      · simpa [t, realizedTupleFromZero] using hslice.1 (j : ℕ) j.2

/-- Helper for Exercise 19.1.1: one fixed first-step branch of the successor exact entrance slice
has mass `(p x z)` times the restarted exact entrance slice mass from `z`, with the `z ∈ A`
branch already collapsed to `0`. -/
private lemma firstEntranceSliceFirstStepBranch_eq_mul_restartSlice_toReal
    (A : Set E) (x y z : E) (n : ℕ) :
    ((P x : Measure Ω)
      ({ω | X 1 ω = z} ∩ firstEntranceSliceEvent (X := X) A y (n + 1))).toReal =
      (p x z).toReal * (if z ∈ A then 0 else
        ((P z : Measure Ω) (firstEntranceSliceEvent (X := X) A y n)).toReal) := by
  let s : Finset (Fin (n + 2) → E) :=
    Finset.univ.filter fun t : Fin (n + 2) → E ↦
      t 0 = z ∧ t (Fin.last (n + 1)) = y ∧
        ∀ i : Fin (n + 1), t i.castSucc ∉ A
  by_cases hz : z ∈ A
  · rw [firstEntranceSlice_firstStepBranch_eq_empty_of_mem (X := X) (A := A) (y := y) hz n]
    simp [hz]
  · have hReal :
        IsMarkovProcessRealization (fun k : ℕ ↦ discreteMatrixKernel p ^ k) P X := inferInstance
    letI : IsMarkovKernel ((fun k : ℕ ↦ discreteMatrixKernel p ^ k) 1) :=
      hReal.semigroup.isMarkovKernel 1
    have hstep_meas : Measurable (realizedTupleFromStep X (n + 2)) := by
      refine measurable_pi_lambda _ fun i ↦ ?_
      simpa [realizedTupleFromStep] using hReal.measurable_process ((i : ℕ) + 1)
    have hzero_meas : Measurable (realizedTupleFromZero X (n + 2)) := by
      refine measurable_pi_lambda _ fun i ↦ ?_
      simpa [realizedTupleFromZero] using hReal.measurable_process (i : ℕ)
    have hdisjStep :
        (s : Set (Fin (n + 2) → E)).PairwiseDisjoint fun t ↦
          (realizedTupleFromStep X (n + 2)) ⁻¹' ({t} : Set (Fin (n + 2) → E)) := by
      intro t ht u hu htu
      refine Set.disjoint_left.2 ?_
      intro ω hωt hωu
      exact htu (hωt.symm.trans hωu)
    have hdisjZero :
        (s : Set (Fin (n + 2) → E)).PairwiseDisjoint fun t ↦
          (realizedTupleFromZero X (n + 2)) ⁻¹' ({t} : Set (Fin (n + 2) → E)) := by
      intro t ht u hu htu
      refine Set.disjoint_left.2 ?_
      intro ω hωt hωu
      exact htu (hωt.symm.trans hωu)
    have hstepMass :
        ((P x : Measure Ω)
          (⋃ t ∈ s,
            (realizedTupleFromStep X (n + 2)) ⁻¹' ({t} : Set (Fin (n + 2) → E)))).toReal =
          Finset.sum s fun t ↦
            ((P x : Measure Ω)
              ((realizedTupleFromStep X (n + 2)) ⁻¹' ({t} : Set (Fin (n + 2) → E)))).toReal := by
      simpa [measureReal_def] using
        (measureReal_biUnion_finset (μ := (P x : Measure Ω)) (s := s)
          (f := fun t ↦ (realizedTupleFromStep X (n + 2)) ⁻¹' ({t} : Set (Fin (n + 2) → E)))
          hdisjStep (fun t _ ↦ hstep_meas (measurableSet_singleton t)))
    have hzeroMass :
        ((P z : Measure Ω)
          (⋃ t ∈ s,
            (realizedTupleFromZero X (n + 2)) ⁻¹' ({t} : Set (Fin (n + 2) → E)))).toReal =
          Finset.sum s fun t ↦
            ((P z : Measure Ω)
              ((realizedTupleFromZero X (n + 2)) ⁻¹' ({t} : Set (Fin (n + 2) → E)))).toReal := by
      simpa [measureReal_def] using
        (measureReal_biUnion_finset (μ := (P z : Measure Ω)) (s := s)
          (f := fun t ↦ (realizedTupleFromZero X (n + 2)) ⁻¹' ({t} : Set (Fin (n + 2) → E)))
          hdisjZero (fun t _ ↦ hzero_meas (measurableSet_singleton t)))
    let startSlice : Set Ω := X 0 ⁻¹' ({z} : Set E) ∩ firstEntranceSliceEvent (X := X) A y n
    have hstart_ae :
        startSlice =ᵐ[(P z : Measure Ω)] firstEntranceSliceEvent (X := X) A y n := by
      filter_upwards [initialState_ae_eq_start_local (p := p) (P := P) (X := X) z] with ω hω
      apply propext
      constructor
      · intro hω'
        exact hω'.2
      · intro hω'
        exact ⟨by simpa [Set.mem_preimage] using hω, hω'⟩
    -- Proof comment: replace the branch by its finite shifted-tuple decomposition, factor each
    -- tuple singleton through the restarted zero-start tuple, and then reassemble the restarted
    -- tuple family into the exact entrance slice from `z`.
    calc
      ((P x : Measure Ω)
        ({ω | X 1 ω = z} ∩ firstEntranceSliceEvent (X := X) A y (n + 1))).toReal =
          ((P x : Measure Ω)
            (⋃ t ∈ s,
              (realizedTupleFromStep X (n + 2)) ⁻¹' ({t} : Set (Fin (n + 2) → E)))).toReal := by
            rw [firstEntranceSuccessorBranch_eq_biUnion_shiftedTupleSingletons
              (X := X) (A := A) y z n]
      _ = Finset.sum s fun t ↦
            ((P x : Measure Ω)
              ((realizedTupleFromStep X (n + 2)) ⁻¹' ({t} : Set (Fin (n + 2) → E)))).toReal :=
            hstepMass
      _ = Finset.sum s fun t ↦
            (p x z).toReal *
              ((P z : Measure Ω)
                ((realizedTupleFromZero X (n + 2)) ⁻¹' ({t} : Set (Fin (n + 2) → E)))).toReal := by
            refine Finset.sum_congr rfl fun t ht ↦ ?_
            have ht0 : t 0 = z := (Finset.mem_filter.mp ht).2.1
            have hp : IsStochasticMatrix p :=
              isStochasticMatrix_of_realization (p := p) (P := P) (X := X)
            have hpxz_ne_top : p x z ≠ ⊤ := by
              apply ne_of_lt
              have hle : p x z ≤ ∑' w : E, p x w := ENNReal.le_tsum z
              have hrow : ∑' w : E, p x w = 1 := hp x
              rw [hrow] at hle
              exact lt_of_le_of_lt hle (by simp)
            have hfactor :=
              congrArg ENNReal.toReal
                (shiftedTupleSingletonMeasure_eq_mul_restartMass
                  (p := p) (P := P) (X := X) (x := x) (n := n + 1) t)
            simpa [ht0, ENNReal.toReal_mul, hpxz_ne_top, measure_ne_top _ _] using hfactor
      _ = (p x z).toReal *
            Finset.sum s fun t ↦
              ((P z : Measure Ω)
                ((realizedTupleFromZero X (n + 2)) ⁻¹' ({t} : Set (Fin (n + 2) → E)))).toReal := by
            symm
            rw [Finset.mul_sum]
      _ = (p x z).toReal *
            ((P z : Measure Ω)
              (⋃ t ∈ s,
                (realizedTupleFromZero X (n + 2)) ⁻¹' ({t} : Set (Fin (n + 2) → E)))).toReal := by
            rw [hzeroMass]
      _ = (p x z).toReal *
            ((P z : Measure Ω)
              (X 0 ⁻¹' ({z} : Set E) ∩ firstEntranceSliceEvent (X := X) A y n)).toReal := by
            rw [firstEntranceRestartedZeroTupleUnion_eq_startInterSlice (X := X) (A := A) hz n]
      _ = (p x z).toReal *
            ((P z : Measure Ω) (firstEntranceSliceEvent (X := X) A y n)).toReal := by
            have hslice_eq :
                (P z : Measure Ω)
                  (X 0 ⁻¹' ({z} : Set E) ∩ firstEntranceSliceEvent (X := X) A y n) =
                (P z : Measure Ω) (firstEntranceSliceEvent (X := X) A y n) :=
              measure_congr hstart_ae
            rw [hslice_eq]
      _ = (p x z).toReal * (if z ∈ A then 0 else
            ((P z : Measure Ω) (firstEntranceSliceEvent (X := X) A y n)).toReal) := by
            simp [hz]

/-- Helper for Exercise 19.1.1: one successor exact entrance slice is the one-step kernel average
of the preceding exact entrance slice. -/
private lemma firstEntranceSlice_succ_eq_kernelAverage_toReal
    (A : Set E) {x y : E} (hx : x ∉ A) (n : ℕ) :
    ((P x : Measure Ω) (firstEntranceSliceEvent (X := X) A y (n + 1))).toReal =
      ∫ z, (if z ∈ A then 0 else
        ((P z : Measure Ω) (firstEntranceSliceEvent (X := X) A y n)).toReal)
        ∂discreteMatrixKernel p x := by
  let hReal :
      IsMarkovProcessRealization (fun k : ℕ ↦ discreteMatrixKernel p ^ k) P X := inferInstance
  have hX : ∀ m : ℕ, Measurable (X m) := hReal.measurable_process
  let f : E → ℝ := fun z ↦ if z ∈ A then 0 else
    ((P z : Measure Ω) (firstEntranceSliceEvent (X := X) A y n)).toReal
  let hp : IsStochasticMatrix p := isStochasticMatrix_of_realization (p := p) (P := P) (X := X)
  have hsum : Summable (fun z : E ↦ (p x z).toReal * ‖f z‖) := Summable.of_finite
  -- Proof comment: partition the successor slice by its first step, replace each branch by the
  -- restarted exact-slice mass, and then repackage the finite row sum as an integral.
  calc
    ((P x : Measure Ω) (firstEntranceSliceEvent (X := X) A y (n + 1))).toReal =
        ∑ z : E, if z ∈ A then 0 else
          ((P x : Measure Ω)
            ({ω | X 1 ω = z} ∩ firstEntranceSliceEvent (X := X) A y (n + 1))).toReal := by
              simpa using
                firstEntranceSlice_eq_sum_firstStepBranches_all_toReal
                  (P := P) (X := X) (A := A) x y n hX
    _ = ∑ z : E, (p x z).toReal * f z := by
          refine Finset.sum_congr rfl fun z _ ↦ ?_
          by_cases hz : z ∈ A
          · simp [f, hz]
          · have hbranch :=
              firstEntranceSliceFirstStepBranch_eq_mul_restartSlice_toReal
                (p := p) (P := P) (X := X) A x y z n
            simpa [f, hz] using hbranch
    _ = ∫ z, f z ∂discreteMatrixKernel p x := by
          symm
          simpa [f] using integral_discreteMatrixKernel_eq_tsum p hp f x hsum

/-- Helper for Exercise 19.1.1: for a boundary target `y ∈ A`, the first-entrance event is the
disjoint union of the exact entrance slices. -/
private lemma firstEntranceMeasure_eq_tsum_exactSlices
    (p : E → E → ℝ≥0∞)
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    (A : Set E) {x y : E} (hy : y ∈ A) :
    (P x : Measure Ω)
      {ω | hittingAfter X A 1 ω < ⊤ ∧
          stoppedValue X (hittingAfter X A 1) ω = y} =
        ∑' n : ℕ, (P x : Measure Ω) (firstEntranceSliceEvent (X := X) A y n) := by
  let hReal :
      IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  let event : Set Ω :=
    {ω | hittingAfter X A 1 ω < ⊤ ∧
        stoppedValue X (hittingAfter X A 1) ω = y}
  have hUnion : event = ⋃ n : ℕ, firstEntranceSliceEvent (X := X) A y n := by
    ext ω
    constructor
    · intro hω
      have hne_top : hittingAfter X A 1 ω ≠ ⊤ := hω.1.ne
      lift hittingAfter X A 1 ω to ℕ using hne_top with m hm
      have hm_pos : 0 < m := by
        have hτ_ge : (1 : ℕ∞) ≤ hittingAfter X A 1 ω :=
          le_hittingAfter (u := X) (s := A) (n := 1) ω
        have hm_ge_one : 1 ≤ m := by
          have hge_m : (1 : ℕ∞) ≤ (m : ℕ∞) := by
            exact le_of_le_of_eq hτ_ge hm.symm
          exact_mod_cast hge_m
        exact Nat.succ_le_iff.mp hm_ge_one
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm_pos.ne'
      refine Set.mem_iUnion.2 ⟨n, ?_⟩
      exact (mem_firstEntranceSliceEvent_iff (X := X) (A := A) hy n).2 ⟨by simpa using hm.symm, hω.2⟩
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨n, hn⟩
      rcases (mem_firstEntranceSliceEvent_iff (X := X) (A := A) hy n).1 hn with ⟨hτ_eq, hstop⟩
      refine ⟨?_, hstop⟩
      rw [hτ_eq]
      simp
  have hPairwise :
      Pairwise (fun n m : ℕ ↦
        Disjoint (firstEntranceSliceEvent (X := X) A y n)
          (firstEntranceSliceEvent (X := X) A y m)) := by
    intro n m hnm
    refine Set.disjoint_left.2 ?_
    intro ω hωn hωm
    rcases (mem_firstEntranceSliceEvent_iff (X := X) (A := A) hy n).1 hωn with ⟨hnτ, -⟩
    rcases (mem_firstEntranceSliceEvent_iff (X := X) (A := A) hy m).1 hωm with ⟨hmτ, -⟩
    have hEq : (n + 1 : ℕ∞) = m + 1 := hnτ.symm.trans hmτ
    have hEqNat : n + 1 = m + 1 := by
      exact_mod_cast hEq
    exact hnm (Nat.succ.inj hEqNat)
  have hMeas :
      ∀ n : ℕ, MeasurableSet (firstEntranceSliceEvent (X := X) A y n) := by
    intro n
    exact firstEntranceSliceEvent_measurable (X := X) (A := A) y n hReal.measurable_process
  -- Proof comment: the boundary entrance event is the disjoint countable union of the exact
  -- entrance slices, so its measure is the corresponding `tsum`.
  change (P x : Measure Ω) event = ∑' n : ℕ, (P x : Measure Ω) (firstEntranceSliceEvent (X := X) A y n)
  rw [hUnion]
  exact measure_iUnion hPairwise hMeas

/-- Helper for Exercise 19.1.1: for a boundary target, the exact first-entrance slice masses are
dominated by the corresponding pre-hit survival tail, hence form a summable real series from any
starting state outside `A`. -/
private lemma summableFirstEntranceSliceMasses_of_hitsSetAlmostSurely
    (p : E → E → ℝ≥0∞)
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    (A : Set E) (hhit : HitsSetAlmostSurely P X A)
    {z y : E} (hy : y ∈ A) (hz : z ∉ A) :
    Summable (fun n : ℕ =>
      ((P z : Measure Ω) (firstEntranceSliceEvent (X := X) A y n)).toReal) := by
  have htail :
      Summable (fun n : ℕ =>
        ((P z : Measure Ω) {ω | ((n : ℕ∞) < hittingAfter X A 1 ω)}).toReal) :=
    summablePreHitTailMass_of_hitsSetAlmostSurely (p := p) (P := P) (X := X) (A := A) hhit hz
  -- Proof comment: the exact entrance slice at time `n + 1` can only occur while the chain is
  -- still outside `A` through the first `n` positive times, so each slice is dominated by the
  -- corresponding pre-hit tail event.
  refine Summable.of_nonneg_of_le (fun n ↦ by positivity) ?_ htail
  intro n
  refine ENNReal.toReal_mono (measure_ne_top _ _) ?_
  refine measure_mono fun ω hω ↦ ?_
  have hslice :=
    (mem_firstEntranceSliceEvent_iff (X := X) (A := A) hy n).1 hω
  show (n : ℕ∞) < hittingAfter X A 1 ω
  rw [hslice.1]
  simpa [Nat.cast_add] using (WithTop.coe_lt_coe.2 (Nat.lt_succ_self n))

/-- Helper for Exercise 19.1.1: in the boundary branch, taking `toReal` transports the exact
first-entrance slice series of the killed Green function to the matrix entry. -/
private lemma killedGreenMatrixView_eq_tsum_firstEntranceSliceMasses_of_not_mem
    (p : E → E → ℝ≥0∞)
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    (A : Set E) {x y : E} (hx : x ∉ A) (hy : y ∈ A) :
    killedGreenMatrixView P X A x y =
      ∑' n : ℕ, ((P x : Measure Ω) (firstEntranceSliceEvent (X := X) A y n)).toReal := by
  let hReal :
      IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  have hX : ∀ n : ℕ, Measurable (X n) := hReal.measurable_process
  -- Proof comment: the boundary killed Green entry is the `toReal` of the exact entrance-measure
  -- series, and every slice mass is finite because it is the mass of a probability event.
  rw [killedGreenMatrixView]
  rw [killedGreenFunction_eq_firstEntranceMeasure
    (P := P) (X := X) (A := A) (x := x) (y := y) hX hx hy]
  rw [firstEntranceMeasure_eq_tsum_exactSlices
    (p := p) (P := P) (X := X) (A := A) (x := x) hy]
  simpa using
    (ENNReal.tsum_toReal_eq
      (f := fun n : ℕ ↦ (P x : Measure Ω) (firstEntranceSliceEvent (X := X) A y n))
      (fun _ ↦ measure_ne_top _ _))

/-- Helper for Exercise 19.1.1: almost-sure entrance into `A` on the finite outside state space
improves to a uniform positive lower bound on some bounded entrance window. -/
private lemma uniformHittingWindow_of_hitsSetAlmostSurely
    (p : E → E → ℝ≥0∞)
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    (A : Set E) (hhit : HitsSetAlmostSurely P X A) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ z : E, z ∉ A →
        ε ≤ ((P z : Measure Ω) {ω | hittingAfter X A 1 ω ≤ N}).toReal := by
  exact uniformHittingWindowForSummableTail (p := p) (P := P) (X := X) (A := A) hhit

/-- Helper for Exercise 19.1.1: the stochastic row `p x` defines a PMF whose measure is exactly
the row measure `discreteMatrixKernel p x`. -/
private lemma rowPmfToMeasure_eq_discreteMatrixKernel
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    (x : E) :
    let q : PMF E := ⟨fun y : E ↦ p x y, ENNReal.summable.hasSum_iff.2
      (isStochasticMatrix_of_realization (p := p) (P := P) (X := X) x)⟩
    discreteMatrixKernel p x = q.toMeasure := by
  let hp : IsStochasticMatrix p := isStochasticMatrix_of_realization (p := p) (P := P) (X := X)
  let q : PMF E := ⟨fun y : E ↦ p x y, ENNReal.summable.hasSum_iff.2 (hp x)⟩
  ext s hs
  -- Proof comment: rewrite both measures on `s` into the same singleton-indicator normal form.
  rw [discreteMatrixKernel_apply, Measure.sum_apply _ hs]
  change ∑' y : E, (p x y • Measure.dirac y) s = q.toMeasure s
  calc
    ∑' y : E, (p x y • Measure.dirac y) s
      = ∑' y : E, s.indicator (fun z : E ↦ p x z) y := by
          refine tsum_congr fun y => ?_
          by_cases hy : y ∈ s
          · simp [Measure.smul_apply, hy]
          · simp [Measure.smul_apply, hy]
    _ = q.toMeasure s := by
        rw [PMF.toMeasure_apply_eq_tsum]
        change
          ∑' y : E, s.indicator (fun z : E ↦ p x z) y =
            ∑' y : E, s.indicator (fun z : E ↦ p x z) y
        rfl

/-- Helper for Exercise 19.1.1: on the finite state space, a one-step average against
`discreteMatrixKernel p x` is the explicit finite row sum. -/
private lemma integral_discreteMatrixKernel_eq_rowSum
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    (x : E) (f : E → ℝ) :
    ∫ z, f z ∂discreteMatrixKernel p x = ∑ z : E, (p x z).toReal * f z := by
  let hp : IsStochasticMatrix p := isStochasticMatrix_of_realization (p := p) P X
  let q : PMF E := ⟨fun y : E ↦ p x y, ENNReal.summable.hasSum_iff.2 (hp x)⟩
  have hrow : discreteMatrixKernel p x = q.toMeasure := by
    simpa [q] using rowPmfToMeasure_eq_discreteMatrixKernel (p := p) P X x
  -- Proof comment: once the row measure is identified with a PMF on the finite state space, the
  -- integral is exactly the PMF expectation formula.
  rw [hrow]
  simpa [q, smul_eq_mul] using (PMF.integral_eq_sum (p := q) (f := f))

/-- Helper for Exercise 19.1.1: on the finite state space, a `tsum` over time commutes with the
finite state sum once each state column is summable. -/
private lemma tsum_sum_fintype_eq_sum_tsum
    (a : ℕ → E → ℝ)
    (hSummable : ∀ z : E, Summable (fun n : ℕ ↦ a n z)) :
    (∑' n : ℕ, ∑ z : E, a n z) = ∑ z : E, ∑' n : ℕ, a n z := by
  classical
  let s : Finset E := Finset.univ
  change (∑' n : ℕ, Finset.sum s (fun z ↦ a n z)) =
    Finset.sum s (fun z ↦ ∑' n : ℕ, a n z)
  clear_value s
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert z s hz ih =>
      have hsummSum : Summable (fun n : ℕ ↦ Finset.sum s (fun w ↦ a n w)) := by
        refine Finset.induction_on s ?_ ?_
        · simpa using summable_zero
        · intro w t hwt iht
          simpa [Finset.sum_insert, hwt] using (hSummable w).add iht
      -- Proof comment: peel off one state `z`, commute `tsum` with the finite sum on the
      -- remaining states by induction, and use `Summable.tsum_mul_left`/`tsum_add` only on the
      -- now one-dimensional summable columns.
      calc
        (∑' n : ℕ, Finset.sum (insert z s) (fun w ↦ a n w))
            = ∑' n : ℕ, (a n z + Finset.sum s (fun w ↦ a n w)) := by
                simp [Finset.sum_insert, hz]
        _ = (∑' n : ℕ, a n z) + ∑' n : ℕ, Finset.sum s (fun w ↦ a n w) := by
              simpa using (hSummable z).tsum_add hsummSum
        _ = Finset.sum (insert z s) (fun w ↦ ∑' n : ℕ, a n w) := by
              simp [Finset.sum_insert, hz, ih]

/-- Helper for Exercise 19.1.1: for `x ∉ A`, the killed Green matrix entry satisfies the
first-step resolvent identity once the positive-time tail is rewritten as a one-step average. -/
private lemma killedGreenMatrixView_resolvent_apply_of_not_mem_local
    (A : Set E) (hhit : HitsSetAlmostSurely P X A) {x y : E} (hx : x ∉ A) :
    killedGreenMatrixView P X A x y =
      (if x = y then 1 else 0) +
        ∑ z : E, killedKernelMatrixView p A x z * killedGreenMatrixView P X A z y := by
  let hReal :
      IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  have hX : ∀ n : ℕ, Measurable (X n) := hReal.measurable_process
  have hkx : ∀ z : E, killedKernelMatrixView p A x z = (p x z).toReal := by
    intro z
    simpa [hx] using killedKernelMatrixView_apply (p := p) A x z
  by_cases hy : y ∈ A
  · let slice : E → ℕ → ℝ := fun z n ↦
      ((P z : Measure Ω) (firstEntranceSliceEvent (X := X) A y n)).toReal
    have hxy : x ≠ y := by
      intro hxy
      exact hx (hxy ▸ hy)
    have hsummX :
        Summable (fun n : ℕ ↦ slice x n) :=
      summableFirstEntranceSliceMasses_of_hitsSetAlmostSurely
        (p := p) (P := P) (X := X) (A := A) hhit hy hx
    have hzero :
        slice x 0 = (p x y).toReal := by
      have hstepLaw := congrArg (fun ν : Measure E ↦ ν ({y} : Set E)) (hReal.transition_eq x 1)
      have hsliceEq :
          firstEntranceSliceEvent (X := X) A y 0 = X 1 ⁻¹' ({y} : Set E) := by
        ext ω
        simp [firstEntranceSliceEvent, avoidFirstPositiveTimesEvent]
      -- Proof comment: the time-`1` exact entrance slice is just the singleton event `X 1 = y`.
      calc
        slice x 0 = ((P x : Measure Ω) (X 1 ⁻¹' ({y} : Set E))).toReal := by
            simp [slice, hsliceEq]
        _ = (((discreteMatrixKernel p ^ 1) x) ({y} : Set E)).toReal := by
            simpa [Measure.map_apply (hX 1) (measurableSet_singleton y)] using
              congrArg ENNReal.toReal hstepLaw
        _ = (p x y).toReal := by
            calc
              (((discreteMatrixKernel p ^ 1) x) ({y} : Set E)).toReal =
                  (((discreteMatrixKernel p) x) ({y} : Set E)).toReal := by
                    simp
              _ = (p x y).toReal := by
                    simpa using congrArg ENNReal.toReal
                      (discreteMatrixKernel_apply_singleton (p := p) (x := y) (y := x))
    have hseries :
        killedGreenMatrixView P X A x y = slice x 0 + ∑' n : ℕ, slice x (n + 1) := by
      -- Proof comment: split the boundary exact-entrance series into the base slice `n = 0` and
      -- the positive-time tail.
      calc
        killedGreenMatrixView P X A x y = ∑' n : ℕ, slice x n := by
          simpa [slice] using
            killedGreenMatrixView_eq_tsum_firstEntranceSliceMasses_of_not_mem
              (p := p) (A := A) hx hy
        _ = slice x 0 + ∑' n : ℕ, slice x (n + 1) := by
              simpa using hsummX.tsum_eq_zero_add
    have hsummCols :
        ∀ z : E, Summable (fun n : ℕ ↦ (p x z).toReal * (if z ∈ A then 0 else slice z n)) := by
      intro z
      by_cases hz : z ∈ A
      · simpa [hz] using summable_zero
      · simpa [hz] using
          (summableFirstEntranceSliceMasses_of_hitsSetAlmostSurely
            (p := p) (P := P) (X := X) (A := A) (z := z) (y := y) hhit hy hz).mul_left
            ((p x z).toReal)
    have htail :
        ∑' n : ℕ, slice x (n + 1) =
          ∑ z : E, killedKernelMatrixView p A x z *
            (if z ∈ A then 0 else killedGreenMatrixView P X A z y) := by
      -- Proof comment: rewrite each successor exact slice by the one-step recursion, commute the
      -- time `tsum` with the finite state sum, and identify each outside column with the killed
      -- Green matrix entry.
      calc
        ∑' n : ℕ, slice x (n + 1) =
            ∑' n : ℕ,
              ∫ z, (if z ∈ A then 0 else slice z n) ∂discreteMatrixKernel p x := by
                refine tsum_congr fun n ↦ ?_
                simpa [slice] using
                  firstEntranceSlice_succ_eq_kernelAverage_toReal
                    (p := p) (P := P) (X := X) (A := A) (x := x) (y := y) hx n
        _ = ∑' n : ℕ, ∑ z : E, (p x z).toReal * (if z ∈ A then 0 else slice z n) := by
              refine tsum_congr fun n ↦ ?_
              simpa using
                integral_discreteMatrixKernel_eq_rowSum
                  (p := p) (P := P) (X := X) x
                  (fun z ↦ if z ∈ A then 0 else slice z n)
        _ = ∑ z : E, ∑' n : ℕ, (p x z).toReal * (if z ∈ A then 0 else slice z n) := by
              exact tsum_sum_fintype_eq_sum_tsum
                (a := fun n z ↦ (p x z).toReal * (if z ∈ A then 0 else slice z n))
                hsummCols
        _ = ∑ z : E, (p x z).toReal * (if z ∈ A then 0 else ∑' n : ℕ, slice z n) := by
              refine Finset.sum_congr rfl fun z _ ↦ ?_
              by_cases hz : z ∈ A
              · simp [hz]
              · simp [hz, tsum_mul_left]
        _ = ∑ z : E, killedKernelMatrixView p A x z *
              (if z ∈ A then 0 else killedGreenMatrixView P X A z y) := by
              refine Finset.sum_congr rfl fun z _ ↦ ?_
              by_cases hz : z ∈ A
              · simp [hz, hkx z]
              · calc
                  (p x z).toReal * (if z ∈ A then 0 else ∑' n : ℕ, slice z n) =
                      (p x z).toReal * ∑' n : ℕ, slice z n := by
                        simp [hz]
                  _ = (p x z).toReal * killedGreenMatrixView P X A z y := by
                        rw [killedGreenMatrixView_eq_tsum_firstEntranceSliceMasses_of_not_mem
                          (p := p) (A := A) (x := z) hz hy]
                  _ = killedKernelMatrixView p A x z *
                        (if z ∈ A then 0 else killedGreenMatrixView P X A z y) := by
                        simp [hz, hkx z]
    have hbaseSum :
        ∑ z : E, killedKernelMatrixView p A x z *
          (if z ∈ A then killedGreenMatrixView P X A z y else 0) = (p x y).toReal := by
      -- Proof comment: the boundary rows of the killed Green matrix are Kronecker deltas, so the
      -- inside-`A` contribution collapses to the single branch `z = y`.
      calc
        ∑ z : E, killedKernelMatrixView p A x z *
            (if z ∈ A then killedGreenMatrixView P X A z y else 0) =
            ∑ z : E, (p x z).toReal *
              (if z ∈ A then killedGreenMatrixView P X A z y else 0) := by
                refine Finset.sum_congr rfl fun z _ ↦ by rw [hkx z]
        _ = ∑ z : E, if z = y then (p x y).toReal else 0 := by
              refine Finset.sum_congr rfl fun z _ ↦ ?_
              by_cases hz : z ∈ A
              · rw [killedGreenMatrixView_eq_kroneckerDelta_of_mem_local
                  (P := P) (X := X) (A := A) (x := z) (y := y) hz]
                by_cases hzy : z = y
                · subst hzy
                  simp [hy]
                · simp [hz, hzy]
              · have hzy : z ≠ y := by
                  intro hzy
                  exact hz (hzy ▸ hy)
                simp [hz, hzy]
        _ = (p x y).toReal := by
              classical
              simp
    have hbase :
        slice x 0 =
          ∑ z : E, killedKernelMatrixView p A x z *
            (if z ∈ A then killedGreenMatrixView P X A z y else 0) := by
      exact hzero.trans hbaseSum.symm
    calc
      killedGreenMatrixView P X A x y = slice x 0 + ∑' n : ℕ, slice x (n + 1) := hseries
      _ =
          (∑ z : E, killedKernelMatrixView p A x z *
            (if z ∈ A then killedGreenMatrixView P X A z y else 0)) +
          ∑ z : E, killedKernelMatrixView p A x z *
            (if z ∈ A then 0 else killedGreenMatrixView P X A z y) := by
              rw [hbase, htail]
      _ =
          ∑ z : E,
            (killedKernelMatrixView p A x z *
                (if z ∈ A then killedGreenMatrixView P X A z y else 0) +
              killedKernelMatrixView p A x z *
                (if z ∈ A then 0 else killedGreenMatrixView P X A z y)) := by
              rw [← Finset.sum_add_distrib]
      _ = ∑ z : E, killedKernelMatrixView p A x z * killedGreenMatrixView P X A z y := by
            refine Finset.sum_congr rfl fun z _ ↦ ?_
            by_cases hz : z ∈ A <;> simp [hz]
      _ = (if x = y then 1 else 0) +
            ∑ z : E, killedKernelMatrixView p A x z * killedGreenMatrixView P X A z y := by
              simp [hxy]
  · let slice : E → ℕ → ℝ := fun z n ↦
      ((P z : Measure Ω) {ω | ((n : ℕ∞) < hittingAfter X A 1 ω) ∧ X n ω = y}).toReal
    have hsummX :
        Summable (fun n : ℕ ↦ slice x n) :=
      summablePreHitStateSliceMasses_of_hitsSetAlmostSurely
        (p := p) (P := P) (X := X) (A := A) hhit hx
    have hzero :
        slice x 0 = if x = y then 1 else 0 := by
      have hEq :
          {ω | ((0 : ℕ∞) < hittingAfter X A 1 ω) ∧ X 0 ω = y} = X 0 ⁻¹' ({y} : Set E) := by
        ext ω
        constructor
        · intro hω
          simpa [Set.mem_preimage] using hω.2
        · intro hω
          refine ⟨?_, ?_⟩
          · exact lt_of_lt_of_le (by simp : (0 : ℕ∞) < 1)
              (le_hittingAfter (u := X) (s := A) (n := 1) ω)
          · simpa [Set.mem_preimage] using hω
      have hinit :
          (P x : Measure Ω) (X 0 ⁻¹' ({y} : Set E)) = if x = y then 1 else 0 := by
        have hstart := congrArg (fun ν : Measure E ↦ ν ({y} : Set E)) (hReal.initial_eq x)
        by_cases hxy : x = y
        · subst hxy
          simpa [Measure.map_apply (hX 0) (measurableSet_singleton x)] using hstart
        · simpa [Measure.map_apply (hX 0) (measurableSet_singleton y), hxy] using hstart
      have hsliceEq :
          slice x 0 = ((P x : Measure Ω) (X 0 ⁻¹' ({y} : Set E))).toReal := by
        simpa [slice, hEq]
      rw [hsliceEq, hinit]
      split_ifs <;> simp
    have hseries :
        killedGreenMatrixView P X A x y =
          (if x = y then 1 else 0) +
            ∑' n : ℕ, slice x (n + 1) := by
      -- Proof comment: in the interior branch, split the full slice series into its time-`0`
      -- term and the positive-time tail.
      calc
        killedGreenMatrixView P X A x y = ∑' n : ℕ, slice x n := by
          simpa [slice] using
            killedGreenMatrixView_eq_tsum_preHitStateSliceMasses_of_not_mem
              (p := p) (P := P) (X := X) (A := A) hx hy
        _ = slice x 0 + ∑' n : ℕ, slice x (n + 1) := by
              simpa using hsummX.tsum_eq_zero_add
        _ = (if x = y then 1 else 0) + ∑' n : ℕ, slice x (n + 1) := by
              rw [hzero]
    have hsummCols :
        ∀ z : E, Summable (fun n : ℕ ↦ (p x z).toReal * (if z ∈ A then 0 else slice z n)) := by
      intro z
      by_cases hz : z ∈ A
      · simpa [hz] using summable_zero
      · simpa [hz] using
          (summablePreHitStateSliceMasses_of_hitsSetAlmostSurely
            (p := p) (P := P) (X := X) (A := A) (x := z) (y := y) hhit hz).mul_left
            ((p x z).toReal)
    have hpositive :
        ∑' n : ℕ, slice x (n + 1) =
          ∑ z : E, killedKernelMatrixView p A x z * killedGreenMatrixView P X A z y := by
      calc
        ∑' n : ℕ, slice x (n + 1)
            = ∑' n : ℕ,
                ∫ z, (if z ∈ A then 0 else slice z n) ∂discreteMatrixKernel p x := by
                  refine tsum_congr fun n ↦ ?_
                  simpa [slice] using
                    preHitStateSlice_succ_eq_kernelAverage_toReal
                      (p := p) (P := P) (X := X) (A := A) (x := x) (y := y) hx n
        _ = ∑' n : ℕ, ∑ z : E, (p x z).toReal * (if z ∈ A then 0 else slice z n) := by
              refine tsum_congr fun n ↦ ?_
              simpa using
                integral_discreteMatrixKernel_eq_rowSum
                  (p := p) (P := P) (X := X) x
                  (fun z ↦ if z ∈ A then 0 else slice z n)
        _ = ∑ z : E, ∑' n : ℕ, (p x z).toReal * (if z ∈ A then 0 else slice z n) := by
              exact tsum_sum_fintype_eq_sum_tsum
                (a := fun n z ↦ (p x z).toReal * (if z ∈ A then 0 else slice z n))
                hsummCols
        _ = ∑ z : E, killedKernelMatrixView p A x z * killedGreenMatrixView P X A z y := by
              refine Finset.sum_congr rfl fun z _ ↦ ?_
              by_cases hz : z ∈ A
              · have hzy : z ≠ y := by
                  intro hzy
                  exact hy (hzy ▸ hz)
                have hGzero : killedGreenMatrixView P X A z y = 0 := by
                  rw [killedGreenMatrixView_eq_kroneckerDelta_of_mem_local
                    (P := P) (X := X) (A := A) (x := z) (y := y) hz]
                  simp [hzy]
                have hsumzero :
                    ∑' n : ℕ, (p x z).toReal * (if z ∈ A then 0 else slice z n) = 0 := by
                  simp [hz]
                rw [hsumzero, hGzero]
                simp
              · calc
                  ∑' n : ℕ, (p x z).toReal * (if z ∈ A then 0 else slice z n)
                      = (p x z).toReal * ∑' n : ℕ, slice z n := by
                          simp [hz, tsum_mul_left]
                  _ = (p x z).toReal * killedGreenMatrixView P X A z y := by
                        rw [killedGreenMatrixView_eq_tsum_preHitStateSliceMasses_of_not_mem
                          (p := p) (P := P) (X := X) (A := A) (x := z) (y := y) hz hy]
                  _ = killedKernelMatrixView p A x z * killedGreenMatrixView P X A z y := by
                        rw [hkx z]
    exact hseries.trans <| by rw [hpositive]

/-- Exercise 19.1.1: for `x ∉ A`, the killed Green matrix entry satisfies the first-step
resolvent identity once the positive-time tail is rewritten as a one-step average. -/
theorem killedGreenMatrixView_resolvent_apply_of_not_mem
    (A : Set E) (hhit : HitsSetAlmostSurely P X A) {x y : E} (hx : x ∉ A) :
    killedGreenMatrixView P X A x y =
      (if x = y then 1 else 0) +
        ∑ z : E, killedKernelMatrixView p A x z * killedGreenMatrixView P X A z y := by
  -- Proof comment: expose the stabilized interior resolvent identity under the item-level
  -- declaration name that the proof pipeline expects for this exercise.
  exact killedGreenMatrixView_resolvent_apply_of_not_mem_local
    (p := p) (P := P) (X := X) (A := A) hhit hx

/-- Helper for Exercise 19.1.1: the killed Green matrix is a right inverse of
`1 - killedKernelMatrixView p A`. -/
private lemma one_sub_killedKernelMatrixView_mul_killedGreenMatrixView_eq_one
    (A : Set E) (hhit : HitsSetAlmostSurely P X A) :
    (1 - killedKernelMatrixView p A) * killedGreenMatrixView P X A = 1 := by
  -- Proof comment: evaluate entrywise. On rows indexed by `A`, the killed kernel row vanishes;
  -- on rows outside `A`, the claimed identity is exactly the rearranged resolvent formula.
  ext x y
  by_cases hx : x ∈ A
  · -- Proof comment: the killed row is zero on `A`, so only the boundary Kronecker row remains.
    calc
      (((1 - killedKernelMatrixView p A) * killedGreenMatrixView P X A) x y)
          = (((1 : Matrix E E ℝ) * killedGreenMatrixView P X A) -
              killedKernelMatrixView p A * killedGreenMatrixView P X A) x y := by
                simp [sub_mul]
      _ = killedGreenMatrixView P X A x y -
            ∑ z : E,
              killedKernelMatrixView p A x z * killedGreenMatrixView P X A z y := by
                simp [Matrix.mul_apply]
      _ = if x = y then 1 else 0 := by
            simp [hx, killedKernelMatrixView_apply,
              killedGreenMatrixView_eq_kroneckerDelta_of_mem_local
                (P := P) (X := X) (A := A) hx]
      _ = (1 : Matrix E E ℝ) x y := by
            simp [Matrix.one_apply]
  · have hres :=
        killedGreenMatrixView_resolvent_apply_of_not_mem
          (p := p) (P := P) (X := X) (A := A) hhit (x := x) (y := y) hx
    -- Proof comment: outside `A`, subtract the one-step average from the rowwise resolvent
    -- identity to recover the Kronecker delta.
    calc
      (((1 - killedKernelMatrixView p A) * killedGreenMatrixView P X A) x y)
          = (((1 : Matrix E E ℝ) * killedGreenMatrixView P X A) -
              killedKernelMatrixView p A * killedGreenMatrixView P X A) x y := by
                simp [sub_mul]
      _ = killedGreenMatrixView P X A x y -
            ∑ z : E,
              killedKernelMatrixView p A x z * killedGreenMatrixView P X A z y := by
                simp [Matrix.mul_apply]
      _ = if x = y then 1 else 0 := by
            rw [hres]
            ring
      _ = (1 : Matrix E E ℝ) x y := by
            simp [Matrix.one_apply]

-- Proof sketch: use the almost-sure finiteness of the first entrance time into `A` to identify
-- the Neumann series of the killed kernel matrix with the intrinsic killed Green function; this
-- produces a two-sided inverse for `1 - killedKernelMatrixView p A`.
/-- Part (1) of Exercise 19.1.1: if the chain started from every state outside `A` enters `A` almost
surely, then the finite-state bridge matrix `1 - \bar p` is invertible. -/
theorem one_sub_killedKernelMatrixView_isUnit
    (A : Set E) (hhit : HitsSetAlmostSurely P X A) :
    IsUnit (1 - killedKernelMatrixView p A) := by
  -- Proof comment: once the explicit killed Green matrix is a right inverse, invertibility is a
  -- direct matrix-algebra corollary.
  exact IsUnit.of_mul_eq_one _
    (one_sub_killedKernelMatrixView_mul_killedGreenMatrixView_eq_one
      (p := p) (P := P) (X := X) (A := A) hhit)

-- Proof sketch: identify `(1 - killedKernelMatrixView p A)⁻¹` with the intrinsic killed Green
-- function by comparing both with the expected killed visit counts.
/-- The inverse of the killed kernel matrix bridge is the matrix representation of the intrinsic
killed Green function. -/
theorem inv_one_sub_killedKernelMatrixView_eq_killedGreenMatrixView
    (A : Set E) (hhit : HitsSetAlmostSurely P X A) :
    (1 - killedKernelMatrixView p A)⁻¹ = killedGreenMatrixView P X A :=
  -- Proof comment: the explicit right inverse is unique, so the matrix inverse must equal the
  -- killed Green matrix bridge.
  Matrix.inv_eq_right_inv
    (one_sub_killedKernelMatrixView_mul_killedGreenMatrixView_eq_one
      (p := p) (P := P) (X := X) (A := A) hhit)

/-- Helper for Exercise 19.1.1: after reindexing `E` as `A ⊕ Aᶜ`, the matrix
`1 - killedKernelMatrixView p A` becomes lower block-triangular with identity on the `A` block and
`1 - restrictedKernelMatrixView p A` on the `Aᶜ` block. -/
private lemma reindexOneSubKilledKernelMatrixView_eq_fromBlocks
    (A : Set E) :
    Matrix.reindex (Equiv.sumCompl (fun z : E ↦ z ∈ A)).symm
      (Equiv.sumCompl (fun z : E ↦ z ∈ A)).symm
      (1 - killedKernelMatrixView p A) =
      Matrix.fromBlocks
        (1 : Matrix {z : E // z ∈ A} {z : E // z ∈ A} ℝ)
        0
        (Matrix.toBlock (1 - killedKernelMatrixView p A)
          (fun z : E ↦ z ∉ A) (fun z : E ↦ z ∈ A))
        (1 - restrictedKernelMatrixView p A) := by
  -- Proof comment: reindex along `E ≃ A ⊕ Aᶜ`, split into the four sum-type cases, and then
  -- identify the diagonal blocks by the explicit formulas for the killed and restricted kernels.
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp only [Matrix.reindex_apply, Matrix.toBlock_apply, Equiv.symm_symm,
      Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.submatrix_apply]
  · -- Proof comment: the `A × A` block is the identity because killed rows vanish on `A`.
    simp [killedKernelMatrixView_apply, i.2, Matrix.one_apply, Subtype.ext_iff]
  · -- Proof comment: the `A × Aᶜ` block vanishes for the same killed-row reason.
    have hij : (↑i : E) ≠ ↑j := by
      intro h
      exact j.2 (h ▸ i.2)
    simp [killedKernelMatrixView_apply, i.2, Matrix.one_apply, hij]
  · -- Proof comment: the lower-left block is exactly the corresponding `toBlock` entry.
    -- Proof comment: after expanding the lower-right entry of the block matrix, both sides are
    -- the same Kronecker-delta term minus the same restricted kernel entry.
    change
      ((1 : Matrix E E ℝ) ↑i ↑j - killedKernelMatrixView p A ↑i ↑j) =
        ((1 : Matrix ↥(Aᶜ) ↥(Aᶜ) ℝ) i j - restrictedKernelMatrixView p A i j)
    rw [killedKernelMatrixView_apply, restrictedKernelMatrixView_apply]
    simp [i.2, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij
      have hone : ((1 : Matrix ↥(Aᶜ) ↥(Aᶜ) ℝ) i i) = 1 := by
        simpa using
          (show ((1 : Matrix ↥(Aᶜ) ↥(Aᶜ) ℝ) i i) = if i = i then 1 else 0 from Matrix.one_apply)
      simpa using hone.symm
    · have hcoe : (↑i : E) ≠ ↑j := by
        intro h
        apply hij
        exact Subtype.ext h
      have hone : ((1 : Matrix ↥(Aᶜ) ↥(Aᶜ) ℝ) i j) = 0 := by
        simpa [hij] using
          (show ((1 : Matrix ↥(Aᶜ) ↥(Aᶜ) ℝ) i j) = if i = j then 1 else 0 from Matrix.one_apply)
      simpa [hcoe] using hone.symm

-- Proof sketch: after decomposing the state space as `A ⊔ (E \ A)`, the block on `A` is the
-- identity, so the restriction of the inverse to `Aᶜ` agrees with the inverse of the restricted
-- kernel matrix.
/-- Part (2) of Exercise 19.1.1: on `E \ A`, the matrix representation of the intrinsic killed Green
function agrees with the inverse of `1 - \tilde p` for the restricted chain. -/
theorem killedGreenMatrixView_eq_restrictedKernelMatrixView_inv
    (A : Set E) (hhit : HitsSetAlmostSurely P X A) (x y : ↥(Aᶜ)) :
    killedGreenMatrixView P X A x y = ((1 - restrictedKernelMatrixView p A)⁻¹) x y := by
  let e : E ≃ ({z : E // z ∈ A} ⊕ ↥(Aᶜ)) := (Equiv.sumCompl fun z : E ↦ z ∈ A).symm
  let lowerLeft :
      Matrix ↥(Aᶜ) {z : E // z ∈ A} ℝ :=
    Matrix.toBlock (1 - killedKernelMatrixView p A)
      (fun z : E ↦ z ∉ A) (fun z : E ↦ z ∈ A)
  have hblock :
      Matrix.reindex e e (1 - killedKernelMatrixView p A) =
        Matrix.fromBlocks
          (1 : Matrix {z : E // z ∈ A} {z : E // z ∈ A} ℝ)
          0
          lowerLeft
          (1 - restrictedKernelMatrixView p A) := by
    -- Proof comment: this is the block decomposition of the killed kernel matrix with respect to
    -- the partition `E = A ⊔ Aᶜ`.
    simpa [e, lowerLeft] using
      reindexOneSubKilledKernelMatrixView_eq_fromBlocks (p := p) (A := A)
  have hunit :
      IsUnit (Matrix.reindex e e (1 - killedKernelMatrixView p A)) := by
    -- Proof comment: reindexing is an algebra equivalence, so it preserves invertibility.
    exact (isUnit_map_iff (Matrix.reindexAlgEquiv ℝ ℝ e) _).2
      (one_sub_killedKernelMatrixView_isUnit (P := P) (X := X) (A := A) hhit)
  have hrestrictedUnit : IsUnit (1 - restrictedKernelMatrixView p A) := by
    -- Proof comment: the lower-right diagonal block of an invertible lower block-triangular matrix
    -- is itself invertible.
    have hblockUnit :
        IsUnit
          (Matrix.fromBlocks
            (1 : Matrix {z : E // z ∈ A} {z : E // z ∈ A} ℝ)
            0
            lowerLeft
            (1 - restrictedKernelMatrixView p A)) := by
      simpa [hblock] using hunit
    exact (Matrix.isUnit_fromBlocks_zero₁₂.mp hblockUnit).2
  have hdiag :
      IsUnit (1 : Matrix {z : E // z ∈ A} {z : E // z ∈ A} ℝ) ↔
        IsUnit (1 - restrictedKernelMatrixView p A) := by
    constructor
    · intro _
      exact hrestrictedUnit
    · intro _
      simpa using
        (show IsUnit (1 : Matrix {z : E // z ∈ A} {z : E // z ∈ A} ℝ) from isUnit_one)
  have hInv :
      Matrix.reindex e e ((1 - killedKernelMatrixView p A)⁻¹) =
        Matrix.fromBlocks
          (1 : Matrix {z : E // z ∈ A} {z : E // z ∈ A} ℝ)
          0
          (-( (1 - restrictedKernelMatrixView p A)⁻¹ * lowerLeft))
          ((1 - restrictedKernelMatrixView p A)⁻¹) := by
    -- Proof comment: apply the standard lower block-triangular inverse formula and then move back
    -- from the reindexed matrix inverse to the reindex of the original inverse.
    calc
      Matrix.reindex e e ((1 - killedKernelMatrixView p A)⁻¹)
          = (Matrix.reindex e e (1 - killedKernelMatrixView p A))⁻¹ := by
              symm
              simpa [e] using
                (Matrix.inv_reindex e e (1 - killedKernelMatrixView p A))
      _ = (Matrix.fromBlocks
            (1 : Matrix {z : E // z ∈ A} {z : E // z ∈ A} ℝ)
            0
            lowerLeft
            (1 - restrictedKernelMatrixView p A))⁻¹ := by
              rw [hblock]
      _ = Matrix.fromBlocks
            (1 : Matrix {z : E // z ∈ A} {z : E // z ∈ A} ℝ)
            0
            (-( (1 - restrictedKernelMatrixView p A)⁻¹ * lowerLeft))
            ((1 - restrictedKernelMatrixView p A)⁻¹) := by
              simpa [Matrix.one_mul] using
                Matrix.inv_fromBlocks_zero₁₂_of_isUnit_iff
                  (1 : Matrix {z : E // z ∈ A} {z : E // z ∈ A} ℝ)
                  lowerLeft
                  (1 - restrictedKernelMatrixView p A)
                  hdiag
  have hentry :
      (1 - killedKernelMatrixView p A)⁻¹ x y =
        ((1 - restrictedKernelMatrixView p A)⁻¹) x y := by
    -- Proof comment: reading the lower-right block of the inverse identifies the `Aᶜ × Aᶜ`
    -- entries of the full inverse with the inverse of the restricted block.
    have := congrArg (fun M ↦ M (Sum.inr x) (Sum.inr y)) hInv
    simpa [Matrix.reindex_apply, e] using this
  rw [inv_one_sub_killedKernelMatrixView_eq_killedGreenMatrixView
    (P := P) (X := X) (A := A) hhit] at hentry
  exact hentry

-- Proof sketch: if `x ∈ A`, the intrinsic killed Green function is already the Kronecker delta
-- row, and `killedGreenMatrixView` is its real-valued finite-state presentation.
/-- Part (3) of Exercise 19.1.1: if `x ∈ A`, then the row of the killed Green matrix bridge at `x` is the
Kronecker delta row. -/
theorem killedGreenMatrixView_eq_kroneckerDelta_of_mem
    (A : Set E) (hhit : HitsSetAlmostSurely P X A) {x y : E} (hx : x ∈ A) :
    killedGreenMatrixView P X A x y = if x = y then 1 else 0 := by
  -- Proof comment: this is exactly the earlier boundary-row normalization helper.
  simpa using
    killedGreenMatrixView_eq_kroneckerDelta_of_mem_local
      (P := P) (X := X) (A := A) hx

-- Proof sketch: for `x ∉ A` and `y ∈ A`, the intrinsic killed Green function is the first
-- entrance distribution of `A` at `y`; `killedGreenMatrixView` is its real-valued matrix bridge.
/-- Part (4) of Exercise 19.1.1: for `x ∈ E \ A` and `y ∈ A`, the boundary entry of the killed Green
matrix bridge is the probability that the chain first enters `A` at the point `y`. -/
theorem killedGreenMatrixView_eq_firstEntranceDistribution
    (p : E → E → ℝ≥0∞)
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    (A : Set E) (hhit : HitsSetAlmostSurely P X A)
    {x y : E} (hx : x ∉ A) (hy : y ∈ A) :
    killedGreenMatrixView P X A x y =
      (P x : Measure Ω).real
        {ω | hittingAfter X A 1 ω < ⊤ ∧
            stoppedValue X (hittingAfter X A 1) ω = y} := by
  -- Route correction: the theorem-local kernel parameter must line up with the realization
  -- instance, and the needed measurability is exactly the realization field.
  let hrealization := (inferInstance :
    IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X)
  have hX : ∀ n : ℕ, Measurable (X n) := hrealization.measurable_process
  rw [killedGreenMatrixView]
  rw [killedGreenFunction_eq_firstEntranceMeasure
    (P := P) (X := X) (A := A) (x := x) (y := y) hX hx hy]
  simp [Measure.real_def]

end

end ProbabilityTheory
