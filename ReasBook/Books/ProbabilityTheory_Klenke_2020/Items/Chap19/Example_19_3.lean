/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap08.Example_8_27
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Lemma_14_27
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_33
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_30
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_16
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_36
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_42
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_17
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_29
import Books.ProbabilityTheory_Klenke_2020.Items.Chap19.Definition_19_1
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]
variable {Ω : Type v} [MeasurableSpace Ω]

/-- Helper for Example 19.3: `ℕ+` is used as a discrete counting index for iterated entrance
times. -/
local instance : MeasurableSpace ℕ+ := ⊤

/-- Helper for Example 19.3: the measurable structure on `ℕ+` is discrete. -/
local instance : DiscreteMeasurableSpace ℕ+ where
  forall_measurableSet := by
    intro s
    trivial

/-- Helper for Example 19.3: the finite-prefix counting arguments use classical equality on the
state space. -/
local instance instDecidableEqState : DecidableEq E := Classical.decEq E

/-- Helper for Example 19.3: any one-step transition matrix realized by `X` is stochastic. -/
private lemma stochasticMatrix_of_realization
    (p : E → E → ℝ≥0∞) (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X] :
    IsStochasticMatrix p := by
  let hReal : IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  letI : IsMarkovKernel ((fun n : ℕ ↦ discreteMatrixKernel p ^ n) 1) :=
    hReal.semigroup.isMarkovKernel 1
  intro x
  -- Proof comment: the realized time-`1` kernel is Markov, so its row mass is `1`; for
  -- `discreteMatrixKernel p` that row mass is exactly `∑' y, p x y`.
  calc
    ∑' y : E, p x y = discreteMatrixKernel p x Set.univ := by
      symm
      rw [discreteMatrixKernel_univ]
    _ = ((fun n : ℕ ↦ discreteMatrixKernel p ^ n) 1) x Set.univ := by
      simp
    _ = 1 := by
      simpa using
        (measure_univ :
          ((fun n : ℕ ↦ discreteMatrixKernel p ^ n) 1) x Set.univ = 1)

/-- Helper for Example 19.3: away from the pole `a`, removing the time-`0` Green summand does
nothing. -/
private lemma greenFunctionFrom_one_eq_greenFunction_offTarget
    (p : E → E → ℝ≥0∞) (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel p ^ n) P X]
    {x a : E} (hx : x ≠ a) :
    (G[P, X; 1]) x a = (G[P, X]) x a := by
  let hReal : IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  let hX : IsStochasticProcess X := fun n ↦ hReal.measurable_process n
  have hzero :
      (P x : Measure Ω) {ω | X 0 ω = a} = 0 := by
    -- Proof comment: under `P x`, the chain starts at `x`, so the time-`0` event `{X₀ = a}` is
    -- empty when `x ≠ a`.
    have hpreimage : {ω | X 0 ω = a} = X 0 ⁻¹' ({a} : Set E) := by
      ext ω
      simp
    calc
      (P x : Measure Ω) {ω | X 0 ω = a}
        = ((P x : Measure Ω).map (X 0)) ({a} : Set E) := by
            rw [hpreimage]
            rw [← Measure.map_apply (hReal.measurable_process 0) (MeasurableSet.singleton a)]
      _ = Measure.dirac x ({a} : Set E) := by
            rw [hReal.initial_eq x]
      _ = 0 := by
            simp [hx]
  -- Proof comment: split the full Green series into the `n = 0` term and the positive-time tail;
  -- the time-`0` term vanishes off the diagonal.
  symm
  calc
    (G[P, X]) x a = ∑' n : ℕ, (P x : Measure Ω) {ω | X n ω = a} := by
      rw [greenFunction_eq_tsum_stateProbabilities P X hX x a]
    _ = (P x : Measure Ω) {ω | X 0 ω = a} +
        ∑' n : ℕ, ite (n = 0) 0 ((P x : Measure Ω) {ω | X n ω = a}) := by
          classical
          have hsplit :
              ∑' n : ℕ, (P x : Measure Ω) {ω | X n ω = a} =
                (P x : Measure Ω) {ω | X 0 ω = a} +
                  ∑' n : ℕ,
                    @ite ℝ≥0∞ (n = 0) (Classical.propDecidable (n = 0)) 0
                      ((P x : Measure Ω) {ω | X n ω = a}) := by
            exact ENNReal.tsum_eq_add_tsum_ite
              (f := fun n : ℕ ↦ (P x : Measure Ω) {ω | X n ω = a}) 0
          calc
            ∑' n : ℕ, (P x : Measure Ω) {ω | X n ω = a} =
                (P x : Measure Ω) {ω | X 0 ω = a} +
                  ∑' n : ℕ,
                    @ite ℝ≥0∞ (n = 0) (Classical.propDecidable (n = 0)) 0
                      ((P x : Measure Ω) {ω | X n ω = a}) := hsplit
            _ = (P x : Measure Ω) {ω | X 0 ω = a} +
                  ∑' n : ℕ, ite (n = 0) 0 ((P x : Measure Ω) {ω | X n ω = a}) := by
                    congr 1
                    refine tsum_congr fun n => ?_
                    by_cases hn : n = 0
                    · simp [hn]
                    · simp [hn]
    _ = 0 + ∑' n : ℕ, ite (n = 0) 0 ((P x : Measure Ω) {ω | X n ω = a}) := by
          simp [hzero]
    _ = ∑' n : ℕ, (P x : Measure Ω) {ω | 0 < n ∧ X n ω = a} := by
          refine (zero_add _).trans ?_
          refine tsum_congr fun n => ?_
          by_cases hn : n = 0
          · subst hn
            simp
          · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
            simp [hn, hnpos]
    _ = (G[P, X; 1]) x a := by
          rw [greenFunctionFrom_one_eq_tsum_positiveStateProbabilities P X hX x a]

/-- Helper for Example 19.3: averaging the fixed-target Green potential over one step gives the
positive-time Green function. -/
private lemma greenFunctionSelf_eq_one_add_greenFunctionFromOneSelf
    (p : E → E → ℝ≥0∞) (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel p ^ n) P X]
    (a : E) :
    (G[P, X]) a a = 1 + (G[P, X; 1]) a a := by
  let hReal : IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  let hX : IsStochasticProcess X := fun n ↦ hReal.measurable_process n
  have hzero :
      (P a : Measure Ω) {ω | X 0 ω = a} = 1 := by
    -- Proof comment: under `P a`, the chain starts from `a` at time `0`.
    have hpreimage : {ω | X 0 ω = a} = X 0 ⁻¹' ({a} : Set E) := by
      ext ω
      simp
    calc
      (P a : Measure Ω) {ω | X 0 ω = a}
        = ((P a : Measure Ω).map (X 0)) ({a} : Set E) := by
            rw [hpreimage]
            rw [← Measure.map_apply (hReal.measurable_process 0) (MeasurableSet.singleton a)]
      _ = Measure.dirac a ({a} : Set E) := by
            rw [hReal.initial_eq a]
      _ = 1 := by
            simp
  -- Proof comment: separate the `n = 0` summand in the diagonal Green series and recognize the
  -- remaining shifted series as the positive-time Green function.
  calc
    (G[P, X]) a a = ∑' n : ℕ, (P a : Measure Ω) {ω | X n ω = a} := by
      rw [greenFunction_eq_tsum_stateProbabilities P X hX a a]
    _ = (P a : Measure Ω) {ω | X 0 ω = a} +
        ∑' n : ℕ, ite (n = 0) 0 ((P a : Measure Ω) {ω | X n ω = a}) := by
          classical
          have hsplit :
              ∑' n : ℕ, (P a : Measure Ω) {ω | X n ω = a} =
                (P a : Measure Ω) {ω | X 0 ω = a} +
                  ∑' n : ℕ,
                    @ite ℝ≥0∞ (n = 0) (Classical.propDecidable (n = 0)) 0
                      ((P a : Measure Ω) {ω | X n ω = a}) := by
            exact ENNReal.tsum_eq_add_tsum_ite
              (f := fun n : ℕ ↦ (P a : Measure Ω) {ω | X n ω = a}) 0
          calc
            ∑' n : ℕ, (P a : Measure Ω) {ω | X n ω = a} =
                (P a : Measure Ω) {ω | X 0 ω = a} +
                  ∑' n : ℕ,
                    @ite ℝ≥0∞ (n = 0) (Classical.propDecidable (n = 0)) 0
                      ((P a : Measure Ω) {ω | X n ω = a}) := hsplit
            _ = (P a : Measure Ω) {ω | X 0 ω = a} +
                  ∑' n : ℕ, ite (n = 0) 0 ((P a : Measure Ω) {ω | X n ω = a}) := by
                    congr 1
                    refine tsum_congr fun n => ?_
                    by_cases hn : n = 0
                    · simp [hn]
                    · simp [hn]
    _ = 1 + ∑' n : ℕ, ite (n = 0) 0 ((P a : Measure Ω) {ω | X n ω = a}) := by
          simp [hzero]
    _ = 1 + ∑' n : ℕ, (P a : Measure Ω) {ω | 0 < n ∧ X n ω = a} := by
          congr 1
          refine tsum_congr fun n => ?_
          by_cases hn : n = 0
          · subst hn
            simp
          · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
            simp [hn, hnpos]
    _ = 1 + (G[P, X; 1]) a a := by
          rw [greenFunctionFrom_one_eq_tsum_positiveStateProbabilities P X hX a a]

/-- Helper for Example 19.3: integrating a nonnegative function against one row of
`discreteMatrixKernel p` expands to the corresponding weighted `tsum`. -/
private lemma lintegral_discreteMatrixKernel_eq_tsum
    (p : E → E → ℝ≥0∞) (x : E) (f : E → ℝ≥0∞) :
    ∫⁻ y, f y ∂discreteMatrixKernel p x = ∑' y : E, p x y * f y := by
  -- Proof comment: expand the discrete row into weighted Dirac masses and evaluate the Dirac
  -- integrals termwise.
  rw [discreteMatrixKernel_apply, lintegral_sum_measure]
  refine tsum_congr fun y => ?_
  rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]

/-- Helper for Example 19.3: singleton masses of the realized `n`-step kernel are exactly the
time-`n` state probabilities. -/
private lemma transitionPowSingleton_eq_stateProbability
    (p : E → E → ℝ≥0∞) (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel p ^ n) P X]
    (y a : E) (n : ℕ) :
    ((discreteMatrixKernel p ^ n) y) ({a} : Set E) =
      (P y : Measure Ω) {ω | X n ω = a} := by
  let hReal : IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  -- Proof comment: rewrite the singleton mass of the `n`-step kernel as the pushforward mass of
  -- `X n` under `P y`, then evaluate that pushforward on the singleton `{a}`.
  calc
    ((discreteMatrixKernel p ^ n) y) ({a} : Set E)
      = ((P y : Measure Ω).map (X n)) ({a} : Set E) := by
          rw [hReal.transition_eq y n]
    _ = (P y : Measure Ω) (X n ⁻¹' ({a} : Set E)) := by
          rw [Measure.map_apply (hReal.measurable_process n) (MeasurableSet.singleton a)]
    _ = (P y : Measure Ω) {ω | X n ω = a} := by
          rfl

/-- Helper for Example 19.3: the `(n + 1)`-step state probability is the one-step convolution of
the `n`-step state probabilities. -/
private lemma stateProbabilitySucc_eq_tsum_stepMass_mul_stateProbability
    (p : E → E → ℝ≥0∞) (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel p ^ n) P X]
    (x a : E) (n : ℕ) :
    (P x : Measure Ω) {ω | X (n + 1) ω = a} =
      ∑' y : E, p x y * (P y : Measure Ω) {ω | X n ω = a} := by
  let hReal : IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  have hpow :
      (discreteMatrixKernel p ^ n) ∘ₖ discreteMatrixKernel p =
        discreteMatrixKernel p ^ (n + 1) := by
    -- Proof comment: the realized kernel powers satisfy Chapman--Kolmogorov, and time `1` is the
    -- original discrete transition kernel.
    simpa [pow_one, Nat.succ_eq_add_one, Nat.add_comm] using hReal.semigroup.comp_eq 1 n
  -- Proof comment: evaluate the `(n + 1)`-step singleton mass through the kernel composition and
  -- expand the resulting one-step row integral into the discrete weighted series.
  calc
    (P x : Measure Ω) {ω | X (n + 1) ω = a}
      = ((discreteMatrixKernel p ^ (n + 1)) x) ({a} : Set E) := by
          symm
          exact transitionPowSingleton_eq_stateProbability p P X x a (n + 1)
    _ = (((discreteMatrixKernel p ^ n) ∘ₖ discreteMatrixKernel p) x) ({a} : Set E) := by
          rw [hpow]
    _ = ∫⁻ y, ((discreteMatrixKernel p ^ n) y) ({a} : Set E) ∂discreteMatrixKernel p x := by
          rw [Kernel.comp_apply' _ _ _ (MeasurableSet.singleton a)]
    _ = ∑' y : E, p x y * ((discreteMatrixKernel p ^ n) y) ({a} : Set E) := by
          rw [lintegral_discreteMatrixKernel_eq_tsum]
    _ = ∑' y : E, p x y * (P y : Measure Ω) {ω | X n ω = a} := by
          refine tsum_congr fun y => ?_
          rw [transitionPowSingleton_eq_stateProbability p P X y a n]

/-- Helper for Example 19.3: the positive-time Green function is the series of the successor-time
state probabilities. -/
private lemma greenFunctionFrom_one_eq_tsum_succStateProbabilities
    (p : E → E → ℝ≥0∞) (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel p ^ n) P X]
    (x a : E) :
    (G[P, X; 1]) x a = ∑' n : ℕ, (P x : Measure Ω) {ω | X (n + 1) ω = a} := by
  let hReal : IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  let hX : IsStochasticProcess X := fun n ↦ hReal.measurable_process n
  -- Proof comment: split the positive-time series into its time-`0` term and shifted tail; the
  -- time-`0` term is empty, so only the successor-time probabilities remain.
  calc
    (G[P, X; 1]) x a = ∑' n : ℕ, (P x : Measure Ω) {ω | 0 < n ∧ X n ω = a} := by
      rw [greenFunctionFrom_one_eq_tsum_positiveStateProbabilities P X hX x a]
    _ = (P x : Measure Ω) {ω | 0 < 0 ∧ X 0 ω = a} +
          ∑' n : ℕ, (P x : Measure Ω) {ω | 0 < (n + 1) ∧ X (n + 1) ω = a} := by
            rw [tsum_eq_zero_add' ENNReal.summable]
    _ = ∑' n : ℕ, (P x : Measure Ω) {ω | X (n + 1) ω = a} := by
          simp

/-- Helper for Example 19.3: the positive-time Green function is the one-step convolution of the
full Green function against the transition matrix. -/
private lemma greenFunctionFrom_one_eq_tsum_stepMass_mul_greenFunction
    (p : E → E → ℝ≥0∞) (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel p ^ n) P X]
    (x a : E) :
    (G[P, X; 1]) x a = ∑' y : E, p x y * (G[P, X]) y a := by
  let hReal : IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  let hX : IsStochasticProcess X := fun n ↦ hReal.measurable_process n
  -- Proof comment: normalize `G[P, X; 1]` to the successor-time state-probability series and
  -- replace each term by the one-step Chapman--Kolmogorov convolution formula.
  calc
    (G[P, X; 1]) x a = ∑' n : ℕ, (P x : Measure Ω) {ω | X (n + 1) ω = a} := by
      rw [greenFunctionFrom_one_eq_tsum_succStateProbabilities p P X x a]
    _ = ∑' n : ℕ, ∑' y : E, p x y * (P y : Measure Ω) {ω | X n ω = a} := by
          refine tsum_congr fun n => ?_
          rw [stateProbabilitySucc_eq_tsum_stepMass_mul_stateProbability p P X x a n]
    _ = ∑' y : E, ∑' n : ℕ, p x y * (P y : Measure Ω) {ω | X n ω = a} := by
          rw [ENNReal.tsum_comm]
    _ = ∑' y : E, p x y * ∑' n : ℕ, (P y : Measure Ω) {ω | X n ω = a} := by
          refine tsum_congr fun y => ?_
          rw [ENNReal.tsum_mul_left]
    _ = ∑' y : E, p x y * (G[P, X]) y a := by
          refine tsum_congr fun y => ?_
          rw [greenFunction_eq_tsum_stateProbabilities P X hX y a]

/-- Helper for Example 19.3: a bound on the infimum of a set of natural times in `ℕ∞` is
equivalent to a bounded witness in that set. -/
private lemma sInf_natImage_le_iff {S : Set ℕ} {N : ℕ} :
    sInf ((fun n : ℕ ↦ (n : ℕ∞)) '' S) ≤ N ↔ ∃ n ∈ S, n ≤ N := by
  by_cases hS : S.Nonempty
  · have hsInf :
        sInf ((fun n : ℕ ↦ (n : ℕ∞)) '' S) = (((sInf S : ℕ) : ℕ∞)) := by
      simpa using (WithTop.coe_sInf' hS (OrderBot.bddBelow S)).symm
    constructor
    · intro h
      refine ⟨sInf S, Nat.sInf_mem hS, ?_⟩
      have hsInf_leN : (((sInf S : ℕ) : ℕ∞)) ≤ N := by
        simpa [hsInf] using h
      exact_mod_cast hsInf_leN
    · rintro ⟨n, hnS, hnN⟩
      have hsInf_le_nat : (sInf S : ℕ) ≤ n := Nat.sInf_le hnS
      have hsInf_leN_nat : (sInf S : ℕ) ≤ N := hsInf_le_nat.trans hnN
      have hsInf_leN : (((sInf S : ℕ) : ℕ∞)) ≤ N := by
        exact_mod_cast hsInf_leN_nat
      simpa [hsInf] using hsInf_leN
  · have hS_empty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
    subst hS_empty
    simp

/-- Helper for Example 19.3: the successor entrance time is bounded by `N` exactly when there is
some visit to `a` by time `N` strictly after the previous entrance. -/
private lemma iteratedEntranceTime_succ_le_iff_existsHitAfter
    (X : ℕ → Ω → E) (a : E) (ω : Ω) (k : ℕ+) (N : ℕ) :
    (τ_[X, a]^(k + 1)) ω ≤ N ↔ ∃ n : ℕ, (τ_[X, a]^k) ω < n ∧ n ≤ N ∧ X n ω = a := by
  -- Proof comment: unfold the recursive successor step and replace the `sInf` bound by the
  -- existence of one bounded future hit.
  rw [iteratedEntranceTime_succ]
  rw [sInf_natImage_le_iff]
  constructor
  · rintro ⟨n, hn, hnN⟩
    exact ⟨n, hn.1, hnN, hn.2⟩
  · rintro ⟨n, hτ, hnN, ha⟩
    exact ⟨n, ⟨hτ, ha⟩, hnN⟩

/-- Helper for Example 19.3: the generated history filtration is monotone in the time index. -/
private lemma generatedFiltrationSpace_mono
    (X : ℕ → Ω → E) {m n : ℕ} (hmn : m ≤ n) :
    generatedFiltrationSpace X m ≤ generatedFiltrationSpace X n := by
  -- Proof comment: increasing the terminal time only enlarges the available history sigma-algebra.
  refine iSup₂_le fun r hr ↦ ?_
  exact le_iSup_of_le r <| le_iSup_of_le (hr.trans hmn) le_rfl

/-- Helper for Example 19.3: every coordinate `X i` is measurable with respect to the generated
history filtration at any later time `n ≥ i`. -/
private lemma measurable_process_generated
    (X : ℕ → Ω → E) {i n : ℕ} (hi : i ≤ n) :
    @Measurable Ω E (generatedFiltrationSpace X n) _ (X i) := by
  -- Proof comment: the coordinate sigma-algebra at time `i` already appears among the generators
  -- of the history filtration at every later time `n`.
  exact Measurable.of_comap_le <|
    le_iSup_of_le i <| le_iSup_of_le hi le_rfl

/-- Helper for Example 19.3: state events are measurable in every generated filtration that
already contains the relevant coordinate. -/
private lemma measurableSet_stateEvent_generated
    (X : ℕ → Ω → E) (a : E) {i n : ℕ} (hi : i ≤ n) :
    MeasurableSet[generatedFiltrationSpace X n] {ω | X i ω = a} := by
  let hXi : @Measurable Ω E (generatedFiltrationSpace X n) _ (X i) :=
    measurable_process_generated (X := X) hi
  change MeasurableSet[generatedFiltrationSpace X n] ((X i) ⁻¹' ({a} : Set E))
  exact hXi (MeasurableSet.singleton a)

/-- Helper for Example 19.3: the bounded entrance event `{τ_[X, a]^k ≤ N}` is measurable with
respect to the history sigma-algebra at time `N`. -/
private lemma iteratedEntranceTime_le_measurable_generated
    (X : ℕ → Ω → E) (a : E) :
    ∀ (k : ℕ+) (N : ℕ),
      MeasurableSet[generatedFiltrationSpace X N] {ω | (τ_[X, a]^k) ω ≤ N} := by
  intro k N
  induction k using PNat.recOn generalizing N with
  | one =>
      have hEq :
          {ω | (τ_[X, a]^1) ω ≤ N} =
            ⋃ j ∈ ((Finset.Icc 1 N : Finset ℕ) : Set ℕ), {ω | X j ω = a} := by
        ext ω
        simpa [iteratedEntranceTime_one, Set.mem_singleton_iff] using
          (MeasureTheory.hittingAfter_le_iff
            (u := X) (s := ({a} : Set E)) (n := 1) (ω := ω) (i := N))
      rw [hEq]
      refine MeasurableSet.biUnion (Set.to_countable _) ?_
      intro j hj
      exact measurableSet_stateEvent_generated
        (X := X) a (hi := (Finset.mem_Icc.mp hj).2)
  | succ k ih =>
      let slice : ℕ → Set Ω := fun j =>
        {ω | (τ_[X, a]^k) ω < j} ∩ {ω | X j ω = a}
      have hEq :
          {ω | (τ_[X, a]^(k + 1)) ω ≤ N} =
            ⋃ j ∈ ((Finset.Icc 1 N : Finset ℕ) : Set ℕ), slice j := by
        ext ω
        constructor
        · intro hω
          rcases (iteratedEntranceTime_succ_le_iff_existsHitAfter X a ω k N).1 hω with
            ⟨j, hτj, hjN, hja⟩
          have hj_pos : 0 < j := by
            cases j with
            | zero => simpa using hτj
            | succ j => exact Nat.succ_pos j
          exact Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨Finset.mem_Icc.mpr ⟨hj_pos, hjN⟩,
            ⟨hτj, hja⟩⟩⟩
        · intro hω
          rcases Set.mem_iUnion.1 hω with ⟨j, hω⟩
          rcases Set.mem_iUnion.1 hω with ⟨hj, hslice⟩
          exact (iteratedEntranceTime_succ_le_iff_existsHitAfter X a ω k N).2
            ⟨j, hslice.1, (Finset.mem_Icc.mp hj).2, hslice.2⟩
      rw [hEq]
      refine MeasurableSet.biUnion (Set.to_countable _) ?_
      intro j hj
      have hj_le : j ≤ N := (Finset.mem_Icc.mp hj).2
      have hlt_N :
          MeasurableSet[generatedFiltrationSpace X N] {ω | (τ_[X, a]^k) ω < j} := by
        cases j with
        | zero =>
            have hj_false : ¬ 0 ∈ (Finset.Icc 1 N : Finset ℕ) := by
              simpa using hj
            exact False.elim (hj_false hj)
        | succ j =>
            have hle_j :
                MeasurableSet[generatedFiltrationSpace X j]
                  {ω | (τ_[X, a]^k) ω ≤ j} :=
              ih j
            have hle_N :
                MeasurableSet[generatedFiltrationSpace X N]
                  {ω | (τ_[X, a]^k) ω ≤ j} := by
              have hmono := generatedFiltrationSpace_mono
                (X := X) (Nat.le_trans (Nat.le_succ j) hj_le)
              exact hmono (s := {ω | (τ_[X, a]^k) ω ≤ j}) hle_j
            simpa [ENat.lt_coe_add_one_iff] using hle_N
      exact hlt_N.inter (measurableSet_stateEvent_generated (X := X) a (hi := hj_le))

/-- Helper for Example 19.3: the strict bounded entrance event `{τ_[X, a]^k < N}` is measurable
with respect to the history sigma-algebra at time `N`. -/
private lemma iteratedEntranceTime_lt_measurable_generated
    (X : ℕ → Ω → E) (a : E) (k : ℕ+) :
    ∀ N : ℕ,
      MeasurableSet[generatedFiltrationSpace X N] {ω | (τ_[X, a]^k) ω < N} := by
  intro N
  cases N with
  | zero =>
      simpa using (MeasurableSet.empty : MeasurableSet (∅ : Set Ω))
  | succ N =>
      have hle_N :
          MeasurableSet[generatedFiltrationSpace X (N + 1)] {ω | (τ_[X, a]^k) ω ≤ N} := by
        have hle_N_base :
            MeasurableSet[generatedFiltrationSpace X N] {ω | (τ_[X, a]^k) ω ≤ N} :=
          iteratedEntranceTime_le_measurable_generated (X := X) a k N
        have hmono := generatedFiltrationSpace_mono (X := X) (Nat.le_succ N)
        exact hmono (s := {ω | (τ_[X, a]^k) ω ≤ N}) hle_N_base
      simpa [ENat.lt_coe_add_one_iff] using hle_N

/-- Helper for Example 19.3: the exact-time slice of the `k`th entrance into `a`. -/
private def entranceSlice (X : ℕ → Ω → E) (a : E) (k : ℕ+) (n : ℕ) : Set Ω :=
  {ω | (τ_[X, a]^k) ω = n}

/-- Helper for Example 19.3: exact entrance slices are measurable in the generated history
filtration at their terminal time. -/
private lemma entranceSlice_measurable_generated
    (X : ℕ → Ω → E) (a : E) (k : ℕ+) (n : ℕ) :
    MeasurableSet[generatedFiltrationSpace X n] (entranceSlice X a k n) := by
  have hEq :
      entranceSlice X a k n =
        {ω | (τ_[X, a]^k) ω ≤ n} \ {ω | (τ_[X, a]^k) ω < n} := by
    ext ω
    constructor
    · intro hω
      have hτ : (τ_[X, a]^k) ω = n := by
        simpa [entranceSlice] using hω
      constructor
      · simpa [hτ]
      · simpa [hτ]
    · intro hω
      simp [entranceSlice, le_antisymm_iff, not_lt] at hω ⊢
      exact hω
  rw [hEq]
  exact (iteratedEntranceTime_le_measurable_generated (X := X) a k n).diff
    (iteratedEntranceTime_lt_measurable_generated (X := X) a k n)

/-- Helper for Example 19.3: the finite entrance event is the union of its exact-time slices. -/
private lemma finiteEntranceEvent_eq_iUnion_entranceSlice
    (X : ℕ → Ω → E) (a : E) (k : ℕ+) :
    {ω | (τ_[X, a]^k) ω < ⊤} = ⋃ n : ℕ, entranceSlice X a k n := by
  ext ω
  constructor
  · intro hω
    refine Set.mem_iUnion.2 ⟨ENat.toNat ((τ_[X, a]^k) ω), ?_⟩
    have hne : (τ_[X, a]^k) ω ≠ ⊤ := ne_of_lt hω
    simp [entranceSlice, ENat.coe_toNat hne]
  · intro hω
    rcases Set.mem_iUnion.mp hω with ⟨n, hn⟩
    simp [entranceSlice] at hn
    simpa [hn]

/-- Helper for Example 19.3: exact entrance slices are measurable in the ambient sigma-algebra. -/
private lemma entranceSlice_measurable
    (p : E → E → ℝ≥0∞) (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel p ^ n) P X]
    (a : E) (k : ℕ+) (n : ℕ) :
    MeasurableSet (entranceSlice X a k n) := by
  let hReal : IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  have hslice_meas_gen :
      MeasurableSet[generatedFiltrationSpace X n] (entranceSlice X a k n) :=
    entranceSlice_measurable_generated (X := X) (a := a) (k := k) (n := n)
  exact (generatedFiltrationSpace_le_ambient (X := X)
    hReal.measurable_process n) _ hslice_meas_gen

/-- Helper for Example 19.3: finite iterated-entrance events are measurable. -/
private lemma measurableSet_iteratedEntranceTime_lt_top
    (p : E → E → ℝ≥0∞) (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel p ^ n) P X]
    (a : E) (k : ℕ+) :
    MeasurableSet {ω | (τ_[X, a]^k) ω < ⊤} := by
  rw [finiteEntranceEvent_eq_iUnion_entranceSlice (X := X) (a := a) k]
  exact MeasurableSet.iUnion fun n =>
    entranceSlice_measurable (p := p) (P := P) (X := X) a k n

/-- Helper for Example 19.3: pathwise, the indicator series of finite iterated entrance times is
the counting measure of the finite-entrance index set. -/
private lemma tsum_iteratedEntranceIndicators_eq_countFiniteIteratedEntrances
    (X : ℕ → Ω → E) (a : E) (ω : Ω) :
    (∑' k : ℕ+,
      Set.indicator {ω' | (τ_[X, a]^k) ω' < ⊤} (fun _ ↦ (1 : ℝ≥0∞)) ω) =
      Measure.count {k : ℕ+ | (τ_[X, a]^k) ω < ⊤} := by
  rw [Measure.count_apply MeasurableSet.of_discrete]
  calc
    (∑' k : ℕ+, Set.indicator {ω' | (τ_[X, a]^k) ω' < ⊤} (fun _ ↦ (1 : ℝ≥0∞)) ω)
        = ∑' _ : {k : ℕ+ | (τ_[X, a]^k) ω < ⊤}, (1 : ℝ≥0∞) := by
            symm
            simpa [Set.indicator_apply] using
              (tsum_subtype
                (s := {k : ℕ+ | (τ_[X, a]^k) ω < ⊤})
                (f := fun _ : ℕ+ ↦ (1 : ℝ≥0∞)))
    _ = ({k : ℕ+ | (τ_[X, a]^k) ω < ⊤}).encard := ENNReal.tsum_one

/-- Helper for Example 19.3: the strictly positive visit times of the path `ω` at the state
`a`. -/
private def positiveVisitSet (Y : ℕ → Ω → E) (a : E) (ω : Ω) : Set ℕ :=
  {n : ℕ | 1 ≤ n ∧ Y n ω = a}

/-- Helper for Example 19.3: `prefixHasIteratedReturn a k m f` records `k` strictly positive
visits to `a` inside the finite prefix `f : Fin m → E`. -/
private def prefixHasIteratedReturn (a : E) : ℕ+ → ∀ m : ℕ, (Fin m → E) → Prop :=
  fun k =>
    PNat.recOn k
      (fun m f => ∃ i : Fin m, 0 < (i : ℕ) ∧ f i = a)
      (fun _ ih m f =>
        ∃ i : Fin m, 0 < (i : ℕ) ∧ f i = a ∧
          ih i (fun j : Fin i ↦ f ⟨j, Nat.lt_trans j.2 i.2⟩))

/-- Helper for Example 19.3: unfold `prefixHasIteratedReturn` at the first positive index. -/
private lemma prefixHasIteratedReturn_one_iff
    (a : E) (m : ℕ) (f : Fin m → E) :
    prefixHasIteratedReturn a 1 m f ↔ ∃ i : Fin m, 0 < (i : ℕ) ∧ f i = a := by
  simp [prefixHasIteratedReturn]

/-- Helper for Example 19.3: unfold `prefixHasIteratedReturn` at a successor positive index. -/
private lemma prefixHasIteratedReturn_succ_iff
    (a : E) (k : ℕ+) (m : ℕ) (f : Fin m → E) :
    prefixHasIteratedReturn a (k + 1) m f ↔
      ∃ i : Fin m, 0 < (i : ℕ) ∧ f i = a ∧
        prefixHasIteratedReturn a k i (fun j : Fin i ↦ f ⟨j, Nat.lt_trans j.2 i.2⟩) := by
  simp [prefixHasIteratedReturn]

/-- Helper for Example 19.3: the bounded event `τ_[Y,a]^k < m` is exactly the recursive
finite-prefix predicate on the first `m` coordinates of the path. -/
private lemma iteratedEntranceTime_lt_iff_prefixHasIteratedReturn
    (Y : ℕ → Ω → E) (a : E) (ω : Ω) :
    ∀ (k : ℕ+) (m : ℕ),
      (τ_[Y, a]^k) ω < m ↔
        prefixHasIteratedReturn a k m (fun i : Fin m ↦ Y i ω) := by
  intro k
  induction k using PNat.recOn with
  | one =>
      intro m
      cases m with
      | zero =>
          -- Proof comment: there is no strictly positive time inside the empty prefix.
          constructor
          · intro h
            simpa using h
          · intro h
            rcases h with ⟨i, _, _⟩
            exact Fin.elim0 i
      | succ m =>
          -- Proof comment: the first entrance time is the usual positive-time hitting time, so
          -- the finite-prefix description is exactly `hittingAfter_lt_iff` specialized to `{a}`.
          constructor
          · intro h
            have hhit :
                hittingAfter Y ({a} : Set E) 1 ω < ↑(m + 1) := by
              simpa [iteratedEntranceTime_one] using h
            rcases (MeasureTheory.hittingAfter_lt_iff
              (u := Y) (s := ({a} : Set E)) (n := 1) (ω := ω) (i := m + 1)).1 hhit with
              ⟨n, hn_mem, hn_eq⟩
            exact (prefixHasIteratedReturn_one_iff a (m + 1) (fun i : Fin (m + 1) ↦ Y i ω)).2
              ⟨⟨n, hn_mem.2⟩, by simpa using hn_mem.1,
                by simpa [Set.mem_singleton_iff] using hn_eq⟩
          · intro h
            rcases (prefixHasIteratedReturn_one_iff a (m + 1) (fun i : Fin (m + 1) ↦ Y i ω)).1 h with
              ⟨i, hi_pos, hi_eq⟩
            have hhit :
                hittingAfter Y ({a} : Set E) 1 ω < ↑(m + 1) := by
              exact (MeasureTheory.hittingAfter_lt_iff
                (u := Y) (s := ({a} : Set E)) (n := 1) (ω := ω) (i := m + 1)).2
                ⟨i, ⟨by simpa using hi_pos, i.2⟩, by simpa [Set.mem_singleton_iff] using hi_eq⟩
            simpa [iteratedEntranceTime_one] using hhit
  | succ k ih =>
      intro m
      cases m with
      | zero =>
          -- Proof comment: a nontrivial iterated return cannot occur inside an empty prefix.
          constructor
          · intro h
            simpa using h
          · intro h
            rcases (prefixHasIteratedReturn_succ_iff a k 0 (fun i : Fin 0 ↦ Y i ω)).1 h with
              ⟨i, _, _, _⟩
            exact Fin.elim0 i
      | succ m =>
          -- Proof comment: the last positive visit in the prefix is the witness that converts the
          -- successor entrance-time bound into the recursive prefix predicate, and conversely.
          have hbound :
              (τ_[Y, a]^(k + 1)) ω < ↑(m + 1) ↔ (τ_[Y, a]^(k + 1)) ω ≤ m := by
            simpa using
              (ENat.lt_coe_add_one_iff (m := (τ_[Y, a]^(k + 1)) ω) (n := m))
          constructor
          · intro h
            have hle : (τ_[Y, a]^(k + 1)) ω ≤ m := hbound.mp h
            rcases (iteratedEntranceTime_succ_le_iff_existsHitAfter
              (X := Y) (a := a) (ω := ω) (k := k) (N := m)).1 hle with
              ⟨n, hτn, hn_le, hn_eq⟩
            have hn_pos : 0 < n := by
              by_contra hn_zero
              have hn_eq_zero : n = 0 := Nat.eq_zero_of_not_pos hn_zero
              have : ¬ (τ_[Y, a]^k) ω < (0 : ℕ) := by simp
              exact this (by simpa [hn_eq_zero] using hτn)
            exact (prefixHasIteratedReturn_succ_iff a k (m + 1)
              (fun i : Fin (m + 1) ↦ Y i ω)).2
              ⟨⟨n, Nat.lt_succ_iff.mpr hn_le⟩, by simpa using hn_pos,
                by simpa using hn_eq,
                (ih n).1 hτn⟩
          · intro h
            rcases (prefixHasIteratedReturn_succ_iff a k (m + 1)
              (fun i : Fin (m + 1) ↦ Y i ω)).1 h with
              ⟨i, hi_pos, hi_eq, hi_prefix⟩
            have hle : (τ_[Y, a]^(k + 1)) ω ≤ m := by
              exact (iteratedEntranceTime_succ_le_iff_existsHitAfter
                (X := Y) (a := a) (ω := ω) (k := k) (N := m)).2
                ⟨i, (ih i).2 hi_prefix, Nat.le_of_lt_succ i.2, by simpa using hi_eq⟩
            exact hbound.mpr hle

/-- Helper for Example 19.3: the recursive finite-prefix witness forces at least the
corresponding number of positive visits in that prefix. -/
private lemma prefixHasIteratedReturn_le_card
    (a : E) :
    ∀ {k : ℕ+} {m : ℕ} {f : Fin m → E},
      prefixHasIteratedReturn a k m f →
        (k : ℕ) ≤ (Finset.univ.filter fun i : Fin m ↦ 0 < (i : ℕ) ∧ f i = a).card := by
  intro k
  induction k using PNat.recOn with
  | one =>
      intro m f h
      -- Proof comment: the first-return witness already belongs to the filtered prefix set.
      rcases (prefixHasIteratedReturn_one_iff a m f).1 h with ⟨i, hi_pos, hi_eq⟩
      have hone : 1 ≤ (Finset.univ.filter fun j : Fin m ↦ 0 < (j : ℕ) ∧ f j = a).card := by
        rw [Finset.one_le_card]
        exact ⟨i, by simp [hi_pos, hi_eq]⟩
      simpa using hone
  | succ k ih =>
      intro m f h
      -- Proof comment: remove the last witnessed visit; the recursive witness gives `k` earlier
      -- visits, and they inject into the remaining filtered prefix.
      rcases (prefixHasIteratedReturn_succ_iff a k m f).1 h with ⟨i, hi_pos, hi_eq, hi_prefix⟩
      let s : Finset (Fin m) := Finset.univ.filter fun j : Fin m ↦ 0 < (j : ℕ) ∧ f j = a
      let t : Finset (Fin i) := Finset.univ.filter fun j : Fin i ↦
        0 < (j : ℕ) ∧ f ⟨j, Nat.lt_trans j.2 i.2⟩ = a
      have hi_mem : i ∈ s := by
        simp [s, hi_pos, hi_eq]
      have hk_le_t : (k : ℕ) ≤ t.card := ih hi_prefix
      have ht_le_erase : t.card ≤ (s.erase i).card := by
        refine Finset.card_le_card_of_injOn
          (fun j : Fin i ↦ (⟨(j : ℕ), Nat.lt_trans j.2 i.2⟩ : Fin m)) ?_ ?_
        · intro j hj
          have hj_props : 0 < (j : ℕ) ∧ f ⟨j, Nat.lt_trans j.2 i.2⟩ = a := by
            simpa [t] using hj
          refine Finset.mem_erase.2 ⟨?_, ?_⟩
          · intro hji
            exact (ne_of_lt j.2) (Fin.ext_iff.mp hji)
          · simp [s, hj_props]
        · intro a₁ ha₁ b hb hEq
          exact Fin.ext (congrArg (fun z : Fin m ↦ (z : ℕ)) hEq)
      have hk_le_erase : (k : ℕ) ≤ (s.erase i).card := le_trans hk_le_t ht_le_erase
      have hs_card : (s.erase i).card + 1 = s.card := Finset.card_erase_add_one hi_mem
      have hs_succ : (k : ℕ) + 1 ≤ s.card := by
        rw [← hs_card]
        exact Nat.succ_le_succ hk_le_erase
      simpa [s] using hs_succ

/-- Helper for Example 19.3: inside a finite prefix, at least `k` positive visits force the
recursive Chapter 17 prefix witness for the `k`th iterated return. -/
private lemma prefixHasIteratedReturn_of_le_card
    (a : E) :
    ∀ {k : ℕ+} {m : ℕ} {f : Fin m → E},
      (k : ℕ) ≤ (Finset.univ.filter fun i : Fin m ↦ 0 < (i : ℕ) ∧ f i = a).card →
        prefixHasIteratedReturn a k m f := by
  intro k
  induction k using PNat.recOn with
  | one =>
      intro m f h
      -- Proof comment: if the filtered hit set has cardinality at least `1`, it already supplies
      -- the witness needed for the base case.
      have h' : 1 ≤ (Finset.univ.filter fun i : Fin m ↦ 0 < (i : ℕ) ∧ f i = a).card := by
        simpa using h
      rw [Finset.one_le_card] at h'
      rcases h' with ⟨i, hi_mem⟩
      have hi_props : 0 < (i : ℕ) ∧ f i = a := by
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hi_mem
      exact (prefixHasIteratedReturn_one_iff a m f).2 ⟨i, hi_props.1, hi_props.2⟩
  | succ k ih =>
      intro m f h
      -- Proof comment: choose the last positive visit in the filtered prefix, erase it, and
      -- recurse on the remaining earlier visits transported into the shorter prefix.
      let s : Finset (Fin m) := Finset.univ.filter fun i : Fin m ↦ 0 < (i : ℕ) ∧ f i = a
      have hs_card_pos : 0 < s.card := by
        have hk_pos : 0 < ((k + 1 : ℕ+) : ℕ) := PNat.pos (k + 1)
        exact lt_of_lt_of_le hk_pos (by simpa [s] using h)
      have hs_nonempty : s.Nonempty := Finset.card_pos.mp hs_card_pos
      let i : Fin m := s.max' hs_nonempty
      have hi_mem : i ∈ s := Finset.max'_mem s hs_nonempty
      have hi_props : 0 < (i : ℕ) ∧ f i = a := by
        simpa only [s, Finset.mem_filter, Finset.mem_univ, true_and] using hi_mem
      let toInitialSegment : Fin m → Fin i :=
        fun j ↦ if hj : (j : ℕ) < i then ⟨(j : ℕ), hj⟩ else ⟨0, hi_props.1⟩
      let t : Finset (Fin i) := Finset.univ.filter fun j : Fin i ↦
        0 < (j : ℕ) ∧ f ⟨j, Nat.lt_trans j.2 i.2⟩ = a
      have hk_le_erase : (k : ℕ) ≤ (s.erase i).card := by
        have hk_succ : (k : ℕ) + 1 ≤ s.card := by
          simpa [s, Nat.succ_eq_add_one] using h
        have hs_card : (s.erase i).card + 1 = s.card := Finset.card_erase_add_one hi_mem
        have hk_succ' : Nat.succ (k : ℕ) ≤ Nat.succ (s.erase i).card := by
          simpa [hs_card, Nat.succ_eq_add_one] using hk_succ
        exact Nat.succ_le_succ_iff.mp hk_succ'
      have herase_le_t : (s.erase i).card ≤ t.card := by
        refine Finset.card_le_card_of_injOn toInitialSegment ?_ ?_
        · intro j hj
          have hj_ne : j ≠ i := (Finset.mem_erase.mp hj).1
          have hj_mem : j ∈ s := (Finset.mem_erase.mp hj).2
          have hj_props : 0 < (j : ℕ) ∧ f j = a := by
            simpa only [s, Finset.mem_filter, Finset.mem_univ, true_and] using hj_mem
          have hj_le : j ≤ i := Finset.le_max' s j hj_mem
          have hj_lt : (j : ℕ) < i := by
            exact show (j : ℕ) < (i : ℕ) from
              lt_of_le_of_ne hj_le (fun hji ↦ hj_ne (Fin.ext hji))
          have hsegment : toInitialSegment j = ⟨(j : ℕ), hj_lt⟩ := by
            -- Route correction: pick the strict-inequality branch first, then compare values.
            have hji : (j : ℕ) < i := hj_lt
            change
              (if h : (j : ℕ) < i then (⟨(j : ℕ), h⟩ : Fin i) else ⟨0, hi_props.1⟩) =
                ⟨(j : ℕ), hj_lt⟩
            rw [dif_pos hji]
          simp [t, hsegment, hj_props]
        · intro a₁ ha₁ b hb hEq
          have ha_ne : a₁ ≠ i := (Finset.mem_erase.mp ha₁).1
          have hb_ne : b ≠ i := (Finset.mem_erase.mp hb).1
          have ha_mem : a₁ ∈ s := (Finset.mem_erase.mp ha₁).2
          have hb_mem : b ∈ s := (Finset.mem_erase.mp hb).2
          have ha_le : a₁ ≤ i := Finset.le_max' s a₁ ha_mem
          have hb_le : b ≤ i := Finset.le_max' s b hb_mem
          have ha_lt : (a₁ : ℕ) < i := by
            exact show (a₁ : ℕ) < (i : ℕ) from
              lt_of_le_of_ne ha_le (fun hai ↦ ha_ne (Fin.ext hai))
          have hb_lt : (b : ℕ) < i := by
            exact show (b : ℕ) < (i : ℕ) from
              lt_of_le_of_ne hb_le (fun hbi ↦ hb_ne (Fin.ext hbi))
          have ha_seg : toInitialSegment a₁ = ⟨(a₁ : ℕ), ha_lt⟩ := by
            -- Route correction: rewrite to the true branch and close by extensionality on `Fin`.
            have ha' : (a₁ : ℕ) < i := ha_lt
            change
              (if h : (a₁ : ℕ) < i then (⟨(a₁ : ℕ), h⟩ : Fin i) else ⟨0, hi_props.1⟩) =
                ⟨(a₁ : ℕ), ha_lt⟩
            rw [dif_pos ha']
          have hb_seg : toInitialSegment b = ⟨(b : ℕ), hb_lt⟩ := by
            -- Route correction: the second image uses the same branch normalization.
            have hb' : (b : ℕ) < i := hb_lt
            change
              (if h : (b : ℕ) < i then (⟨(b : ℕ), h⟩ : Fin i) else ⟨0, hi_props.1⟩) =
                ⟨(b : ℕ), hb_lt⟩
            rw [dif_pos hb']
          have himage_eq : (⟨(a₁ : ℕ), ha_lt⟩ : Fin i) = ⟨(b : ℕ), hb_lt⟩ := by
            calc
              (⟨(a₁ : ℕ), ha_lt⟩ : Fin i) = toInitialSegment a₁ := by
                simpa using ha_seg.symm
              _ = toInitialSegment b := hEq
              _ = (⟨(b : ℕ), hb_lt⟩ : Fin i) := by
                simpa using hb_seg
          have hab_val : (a₁ : ℕ) = (b : ℕ) := by
            exact congrArg (fun z : Fin i ↦ (z : ℕ)) himage_eq
          exact Fin.ext hab_val
      have hk_le_t : (k : ℕ) ≤ t.card := le_trans hk_le_erase herase_le_t
      exact (prefixHasIteratedReturn_succ_iff a k m f).2 ⟨i, hi_props.1, hi_props.2, ih hk_le_t⟩

/-- Helper for Example 19.3: the recursive finite-prefix witness is equivalent to asking for at
least `k` positive visits to `a` in that prefix. -/
private lemma prefixHasIteratedReturn_iff_prefixVisitCountAtLeast
    (a : E) {k : ℕ+} {m : ℕ} {f : Fin m → E} :
    prefixHasIteratedReturn a k m f ↔
      (k : ℕ) ≤ (Finset.univ.filter fun i : Fin m ↦ 0 < (i : ℕ) ∧ f i = a).card :=
  by
    -- Proof comment: the recursive prefix predicate and the cardinality condition encode the same
    -- finite-prefix notion of the `k`th positive return to `a`.
    constructor
    · exact prefixHasIteratedReturn_le_card a
    · exact prefixHasIteratedReturn_of_le_card a

/-- Helper for Example 19.3: the event `τ_[Y,a]^k < m` is equivalent to having at least `k`
positive visits to `a` in the first `m` coordinates of the path. -/
private lemma iteratedEntranceTime_lt_iff_prefixVisitCountAtLeast
    (Y : ℕ → Ω → E) (a : E) (ω : Ω) :
    ∀ (k : ℕ+) (m : ℕ),
      (τ_[Y, a]^k) ω < m ↔
        (k : ℕ) ≤ (Finset.univ.filter fun i : Fin m ↦ 0 < (i : ℕ) ∧ Y i ω = a).card
  | k, m => by
      -- Proof comment: collapse the recursive finite-prefix criterion to the measurable
      -- visit-count normal form.
      rw [iteratedEntranceTime_lt_iff_prefixHasIteratedReturn,
        prefixHasIteratedReturn_iff_prefixVisitCountAtLeast]

/-- Helper for Example 19.3: the event `τ_[Y,a]^k ≤ N` is equivalent to having at least `k`
positive visits to `a` in the first `N + 1` coordinates of the path. -/
private lemma iteratedEntranceTime_le_iff_prefixVisitCountAtLeast
    (Y : ℕ → Ω → E) (a : E) (ω : Ω) :
    ∀ (k : ℕ+) (N : ℕ),
      (τ_[Y, a]^k) ω ≤ N ↔
        (k : ℕ) ≤
          (Finset.univ.filter fun i : Fin (N + 1) ↦ 0 < (i : ℕ) ∧ Y i ω = a).card
  | k, N => by
      -- Proof comment: on `ℕ∞`, the bound `≤ N` is the same as strict inequality below `N + 1`.
      have hbound :
          (τ_[Y, a]^k) ω ≤ N ↔ (τ_[Y, a]^k) ω < N + 1 := by
        simpa using
          (ENat.lt_coe_add_one_iff (m := (τ_[Y, a]^k) ω) (n := N)).symm
      constructor
      · intro h
        exact (iteratedEntranceTime_lt_iff_prefixVisitCountAtLeast Y a ω k (N + 1)).1
          (hbound.mp h)
      · intro h
        exact hbound.mpr
          ((iteratedEntranceTime_lt_iff_prefixVisitCountAtLeast Y a ω k (N + 1)).2 h)

/-- Helper for Example 19.3: every bounded prefix count of visits to `a` injects into the full
set of positive visit times, so its cardinality is bounded by the total positive-visit encard. -/
private lemma prefixHitCount_le_positiveVisitEncard
    (Y : ℕ → Ω → E) (a : E) (ω : Ω) (N : ℕ) :
    ((Finset.univ.filter fun i : Fin (N + 1) ↦ 0 < (i : ℕ) ∧ Y i ω = a).card : ℕ∞) ≤
      (positiveVisitSet Y a ω).encard := by
  classical
  let s : Set (Fin (N + 1)) := {i : Fin (N + 1) | 0 < (i : ℕ) ∧ Y i ω = a}
  have hs_subset : (fun i : Fin (N + 1) ↦ (i : ℕ)) '' s ⊆ positiveVisitSet Y a ω := by
    intro n hn
    rcases hn with ⟨i, hi, rfl⟩
    exact ⟨Nat.succ_le_of_lt hi.1, hi.2⟩
  -- Proof comment: identify the filtered prefix finset with its image inside the full positive
  -- visit set and compare the resulting encards by monotonicity.
  calc
    ((Finset.univ.filter fun i : Fin (N + 1) ↦ 0 < (i : ℕ) ∧ Y i ω = a).card : ℕ∞)
        = s.encard := by
          calc
            ((Finset.univ.filter fun i : Fin (N + 1) ↦ 0 < (i : ℕ) ∧ Y i ω = a).card : ℕ∞)
              = s.toFinset.card := by
                  simp [s]
            _ = s.encard := by
                  symm
                  exact Set.encard_eq_coe_toFinset_card s
    _ = ((fun i : Fin (N + 1) ↦ (i : ℕ)) '' s).encard := by
      symm
      exact Fin.val_injective.encard_image s
    _ ≤ (positiveVisitSet Y a ω).encard := Set.encard_mono hs_subset

/-- Helper for Example 19.3: among positive integers, exactly `m` indices satisfy `k ≤ m`. -/
private lemma count_pnat_le_eq (m : ℕ) :
    Measure.count {k : ℕ+ | (k : ℕ) ≤ m} = m :=
  by
    let s : Set ℕ+ := {k : ℕ+ | (k : ℕ) ≤ m}
    have himage : Equiv.pnatEquivNat '' s = {n : ℕ | n < m} := by
      ext n
      constructor
      · rintro ⟨k, hk, rfl⟩
        have hk' : k.natPred + 1 ≤ m := by
          simpa [s, PNat.natPred_add_one] using hk
        exact lt_of_lt_of_le (Nat.lt_succ_self k.natPred) hk'
      · intro hn
        refine ⟨n.succPNat, ?_, by simp [Equiv.pnatEquivNat]⟩
        simpa [s] using Nat.succ_le_of_lt hn
    -- Proof comment: transport the positive-natural counting problem to the ordinary initial
    -- segment `{n : ℕ | n < m}`, whose counting measure is the standard `range m` cardinality.
    calc
      Measure.count s = Measure.count (Equiv.pnatEquivNat '' s) := by
        symm
        exact Measure.count_injective_image Equiv.pnatEquivNat.injective s
      _ = Measure.count {n : ℕ | n < m} := by
        rw [himage]
      _ = ({n : ℕ | n < m}).encard := by
        rw [Measure.count_apply MeasurableSet.of_discrete]
      _ = (m : ℝ≥0∞) := by
        exact_mod_cast (Set.Nat.encard_range m)

/-- Helper for Example 19.3: counting positive integers bounded by an `ℕ∞` value recovers that
bound. -/
private lemma count_pnat_le_enat_eq (t : ℕ∞) :
    Measure.count {k : ℕ+ | (k : ℕ∞) ≤ t} = t :=
  by
    by_cases ht : t = ⊤
    · subst ht
      simpa [ENat.card_eq_top_of_infinite] using
        (Measure.count_univ : Measure.count (Set.univ : Set ℕ+) = ENat.card ℕ+)
    · -- Proof comment: in the finite case, replace the `ℕ∞` bound by `ENat.toNat t` and reuse
      -- the explicit `ℕ+` counting lemma above.
      calc
        Measure.count {k : ℕ+ | (k : ℕ∞) ≤ t}
          = Measure.count {k : ℕ+ | (k : ℕ) ≤ ENat.toNat t} := by
              congr 1
              ext k
              constructor
              · intro hk
                simpa using ENat.toNat_le_toNat hk ht
              · intro hk
                have hk' : ((k : ℕ) : ℕ∞) ≤ (ENat.toNat t : ℕ∞) := by
                  exact (ENat.coe_le_coe).2 hk
                simpa [ENat.coe_toNat ht] using hk'
        _ = ENat.toNat t := by
              simpa using count_pnat_le_eq (ENat.toNat t)
        _ = (t : ℝ≥0∞) := by
              exact_mod_cast ENat.coe_toNat ht

/-- Helper for Example 19.3: a finite iterated entrance time is equivalent to having at least `k`
positive visits to `a`; the right-hand side is expressed through the full positive-visit encard. -/
private lemma iteratedEntranceTime_lt_top_iff_le_positiveVisitEncard
    (Y : ℕ → Ω → E) (a : E) (ω : Ω) (k : ℕ+) :
    (τ_[Y, a]^k) ω < ⊤ ↔ (k : ℕ∞) ≤ (positiveVisitSet Y a ω).encard :=
  by
    constructor
    · intro hτ
      let N : ℕ := ENat.toNat ((τ_[Y, a]^k) ω)
      have hτ_ne_top : (τ_[Y, a]^k) ω ≠ ⊤ := ne_of_lt hτ
      have hτ_le : (τ_[Y, a]^k) ω ≤ N := by
        simp [N, ENat.coe_toNat hτ_ne_top]
      have hk_le_prefix :
          (k : ℕ∞) ≤
            ((Finset.univ.filter fun i : Fin (N + 1) ↦ 0 < (i : ℕ) ∧ Y i ω = a).card : ℕ∞) := by
        exact_mod_cast (iteratedEntranceTime_le_iff_prefixVisitCountAtLeast Y a ω k N).1 hτ_le
      -- Proof comment: a finite `k`th entrance time yields a bounded prefix with at least `k`
      -- positive visits, and every bounded prefix injects into the full visit set.
      exact hk_le_prefix.trans (prefixHitCount_le_positiveVisitEncard Y a ω N)
    · intro hk
      obtain ⟨t, ht_subset, ht_card⟩ :=
        Set.exists_subset_encard_eq (s := positiveVisitSet Y a ω) hk
      have ht_finite : t.Finite := Set.finite_of_encard_eq_coe (by simpa using ht_card)
      let tfin : Finset ℕ := ht_finite.toFinset
      have htfin_card_enat : (tfin.card : ℕ∞) = (k : ℕ∞) := by
        rw [← ht_finite.encard_eq_coe_toFinset_card]
        simpa [tfin] using ht_card
      have htfin_card : tfin.card = (k : ℕ) := ENat.coe_inj.mp htfin_card_enat
      have htfin_nonempty : tfin.Nonempty := by
        apply Finset.card_pos.mp
        rw [htfin_card]
        exact k.2
      let N : ℕ := tfin.max' htfin_nonempty
      let toPrefix : ℕ → Fin (N + 1) :=
        fun n ↦
          if hn : n ∈ tfin then
            ⟨n, Nat.lt_succ_of_le (Finset.le_max' tfin n hn)⟩
          else 0
      have hk_le_prefix :
          (k : ℕ) ≤ (Finset.univ.filter fun i : Fin (N + 1) ↦ 0 < (i : ℕ) ∧ Y i ω = a).card := by
        have hcard_le :
            tfin.card ≤ (Finset.univ.filter fun i : Fin (N + 1) ↦ 0 < (i : ℕ) ∧ Y i ω = a).card := by
          refine Finset.card_le_card_of_injOn toPrefix ?_ ?_
          · intro n hn
            have hn_t : n ∈ t := by
              simpa [tfin] using hn
            have hn_props : 1 ≤ n ∧ Y n ω = a := ht_subset hn_t
            have htoPrefix : toPrefix n = ⟨n, Nat.lt_succ_of_le (Finset.le_max' tfin n hn)⟩ := by
              by_cases hmem : n ∈ tfin
              · simp [toPrefix, hmem]
              · exact (hmem hn).elim
            have hprefix_val : ((toPrefix n : Fin (N + 1)) : ℕ) = n := by
              rw [htoPrefix]
            have hpos : 0 < ((toPrefix n : Fin (N + 1)) : ℕ) := by
              simpa [hprefix_val] using Nat.succ_le_iff.mp hn_props.1
            have hstate : Y (toPrefix n) ω = a := by
              simpa [hprefix_val] using hn_props.2
            refine Finset.mem_filter.mpr ?_
            refine ⟨by simp, ?_⟩
            exact ⟨show (0 : Fin (N + 1)) < toPrefix n from hpos, hstate⟩
          · intro n₁ hn₁ n₂ hn₂ hEq
            have hvals :
                ((toPrefix n₁ : Fin (N + 1)) : ℕ) = ((toPrefix n₂ : Fin (N + 1)) : ℕ) := by
              exact congrArg (fun i : Fin (N + 1) ↦ (i : ℕ)) hEq
            have hn₁_val : ((toPrefix n₁ : Fin (N + 1)) : ℕ) = n₁ := by
              have htoPrefix :
                  toPrefix n₁ = ⟨n₁, Nat.lt_succ_of_le (Finset.le_max' tfin n₁ hn₁)⟩ := by
                by_cases hmem : n₁ ∈ tfin
                · simp [toPrefix, hmem]
                · exact (hmem hn₁).elim
              rw [htoPrefix]
            have hn₂_val : ((toPrefix n₂ : Fin (N + 1)) : ℕ) = n₂ := by
              have htoPrefix :
                  toPrefix n₂ = ⟨n₂, Nat.lt_succ_of_le (Finset.le_max' tfin n₂ hn₂)⟩ := by
                by_cases hmem : n₂ ∈ tfin
                · simp [toPrefix, hmem]
                · exact (hmem hn₂).elim
              rw [htoPrefix]
            calc
              n₁ = ((toPrefix n₁ : Fin (N + 1)) : ℕ) := hn₁_val.symm
              _ = ((toPrefix n₂ : Fin (N + 1)) : ℕ) := hvals
              _ = n₂ := hn₂_val
        rw [htfin_card] at hcard_le
        exact hcard_le
      -- Proof comment: a concrete `k`-element subset of positive visits is bounded by its maximal
      -- time, so the bounded-prefix criterion gives a finite `k`th entrance time.
      have hτ_le : (τ_[Y, a]^k) ω ≤ N :=
        (iteratedEntranceTime_le_iff_prefixVisitCountAtLeast Y a ω k N).2 hk_le_prefix
      exact lt_of_le_of_lt hτ_le (by simp)

/-- Helper for Example 19.3: pathwise, the positive-time visit count equals the number of finite
iterated entrances into `a`. -/
private lemma totalVisitsFromOne_eq_countFiniteIteratedEntrances
    (X : ℕ → Ω → E) (a : E) (ω : Ω) :
    totalVisitsFrom X a 1 ω = Measure.count {k : ℕ+ | (τ_[X, a]^k) ω < ⊤} :=
  by
    -- Proof comment: rewrite the positive visit count as the encard of the positive-visit set and
    -- then identify that encard with the counting measure of the finite entrance-time index set.
    calc
      totalVisitsFrom X a 1 ω = Measure.count {n : ℕ | 1 ≤ n ∧ X n ω = a} := by
        rw [totalVisitsFrom_eq_count]
      _ = (positiveVisitSet X a ω).encard := by
        rw [Measure.count_apply MeasurableSet.of_discrete]
        simp [positiveVisitSet]
      _ = Measure.count {k : ℕ+ | (k : ℕ∞) ≤ (positiveVisitSet X a ω).encard} := by
        symm
        exact count_pnat_le_enat_eq ((positiveVisitSet X a ω).encard)
      _ = Measure.count {k : ℕ+ | (τ_[X, a]^k) ω < ⊤} := by
        congr 1
        ext k
        simpa using
          (iteratedEntranceTime_lt_top_iff_le_positiveVisitEncard X a ω k).symm

-- Helper for Example 19.3: pathwise, the positive visit count at `a` equals the number of finite
-- iterated entrance times into `a`.
-- Route correction: the normalization of `G[P, X; 1]` is already reduced to a pure Chapter 17
-- owner statement. The remaining missing API is the pathwise identification of positive visits
-- with finite iterated entrances.
/-- Helper for Example 19.3: rewrite the positive-time Green function as the series of finite
iterated-entrance probabilities. -/
-- Route correction: normalize `G[P, X; 1]` at the entrance-time owner before any real-valued
-- transport. The remaining blocker is the pathwise equality between the positive visit count and
-- the number of finite iterated entrance times.
private lemma greenFunctionFrom_one_eq_tsum_iteratedEntranceProbabilities
    (p : E → E → ℝ≥0∞) (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel p ^ n) P X]
    (y a : E) :
    (G[P, X; 1]) y a =
      ∑' k : ℕ+, ENNReal.ofReal ((P y : Measure Ω).real {ω | (τ_[X, a]^k) ω < ⊤}) := by
  have hτ_meas : ∀ k : ℕ+, MeasurableSet {ω | (τ_[X, a]^k) ω < ⊤} := by
    intro k
    exact measurableSet_iteratedEntranceTime_lt_top (p := p) (P := P) (X := X) a k
  -- Proof comment: rewrite `G[P, X; 1]` as the expected positive visit count, replace that count
  -- by the finite-entrance count, expand it as an indicator series, and integrate termwise.
  calc
    (G[P, X; 1]) y a = ∫⁻ ω, totalVisitsFrom X a 1 ω ∂(P y : Measure Ω) := by
      rw [greenFunctionFrom_eq_lintegral_totalVisitsFrom]
    _ = ∫⁻ ω, Measure.count {k : ℕ+ | (τ_[X, a]^k) ω < ⊤} ∂(P y : Measure Ω) := by
          refine lintegral_congr_ae ?_
          filter_upwards [] with ω
          rw [totalVisitsFromOne_eq_countFiniteIteratedEntrances]
    _ = ∫⁻ ω,
          ∑' k : ℕ+,
            Set.indicator {ω' | (τ_[X, a]^k) ω' < ⊤} (fun _ ↦ (1 : ℝ≥0∞)) ω
          ∂(P y : Measure Ω) := by
            refine lintegral_congr_ae ?_
            filter_upwards [] with ω
            symm
            exact tsum_iteratedEntranceIndicators_eq_countFiniteIteratedEntrances X a ω
    _ = ∑' k : ℕ+,
          ∫⁻ ω,
            Set.indicator {ω' | (τ_[X, a]^k) ω' < ⊤} (fun _ ↦ (1 : ℝ≥0∞)) ω
          ∂(P y : Measure Ω) := by
            rw [lintegral_tsum fun k ↦
              (measurable_const.indicator (hτ_meas k)).aemeasurable]
    _ = ∑' k : ℕ+, (P y : Measure Ω) {ω | (τ_[X, a]^k) ω < ⊤} := by
          refine tsum_congr fun k ↦ ?_
          simpa using
            (lintegral_indicator_one (μ := (P y : Measure Ω))
              (s := {ω | (τ_[X, a]^k) ω < ⊤}) (hτ_meas k))
    _ = ∑' k : ℕ+, ENNReal.ofReal ((P y : Measure Ω).real {ω | (τ_[X, a]^k) ω < ⊤}) := by
          refine tsum_congr fun k ↦ ?_
          simp [MeasureTheory.measureReal_def]

/-- Helper for Example 19.3: Theorem 17.29 turns the positive-time Green function into a geometric
series governed by the return probability at `a`. -/
private lemma greenFunctionFrom_one_eq_tsum_everHits_mul_selfPowers
    (p : E → E → ℝ≥0∞) (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel p ^ n) P X]
    (y a : E) :
    (G[P, X; 1]) y a =
      ∑' n : ℕ, ENNReal.ofReal (((F[P, X]) y a) * (F[P, X]) a a ^ n) := by
  -- Proof comment: first rewrite the positive-time Green function as the entrance-probability
  -- series, then specialize Theorem 17.29 termwise and reindex `ℕ+` by `ℕ`.
  calc
    (G[P, X; 1]) y a =
        ∑' k : ℕ+, ENNReal.ofReal ((P y : Measure Ω).real {ω | (τ_[X, a]^k) ω < ⊤}) := by
          rw [greenFunctionFrom_one_eq_tsum_iteratedEntranceProbabilities (p := p) (P := P)
            (X := X) y a]
    _ = ∑' k : ℕ+, ENNReal.ofReal ((F[P, X]) y a * (F[P, X]) a a ^ k.natPred) := by
          refine tsum_congr fun k => ?_
          rw [iteratedEntranceTime_finite_probability_eq_everHitsProbability_mul_selfPow
            (P := P) (X := X) y a k]
    _ = ∑' n : ℕ, ENNReal.ofReal ((F[P, X]) y a * (F[P, X]) a a ^ n) := by
          simpa using
            (Equiv.tsum_eq Equiv.pnatEquivNat
              (fun n : ℕ ↦ ENNReal.ofReal ((F[P, X]) y a * (F[P, X]) a a ^ n)))

/-- Helper for Example 19.3: a geometric series of `ENNReal` casts is finite whenever the ratio
lies in `[0, 1)`. -/
private lemma ennrealOfReal_tsum_geometric_lt_top {q : ℝ}
    (hq_nonneg : 0 ≤ q) (hq_lt_one : q < 1) :
    ∑' n : ℕ, ENNReal.ofReal (q ^ n) < ⊤ := by
  have hsum : Summable (fun n : ℕ ↦ q ^ n) :=
    summable_geometric_of_lt_one hq_nonneg hq_lt_one
  -- Proof comment: summability of the nonnegative real geometric series survives the termwise
  -- cast to `ℝ≥0∞`.
  calc
    ∑' n : ℕ, ENNReal.ofReal (q ^ n) = ENNReal.ofReal (∑' n : ℕ, q ^ n) := by
      rw [ENNReal.ofReal_tsum_of_nonneg]
      · intro n
        exact pow_nonneg hq_nonneg n
      · exact hsum
    _ < ⊤ := by
      simp

/-- Helper for Example 19.3: the positive-time Green function aimed at a transient state is
finite from every start state. -/
private lemma greenFunctionFrom_one_lt_top_of_transientState
    (p : E → E → ℝ≥0∞) (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel p ^ n) P X]
    {a : E} (ha : IsTransientState P X a) (y : E) :
    (G[P, X; 1]) y a < ⊤ := by
  have haa_nonneg : 0 ≤ (F[P, X]) a a := measureReal_nonneg
  have hya_le_one : (F[P, X]) y a ≤ 1 := by
    rw [everHitsProbability_def]
    exact measureReal_le_one
  have hgeom_lt_top :
      ∑' n : ℕ, ENNReal.ofReal ((F[P, X]) a a ^ n) < ⊤ :=
    ennrealOfReal_tsum_geometric_lt_top haa_nonneg ha
  -- Proof comment: Theorem 17.29 rewrites `G[P, X; 1] y a` as a geometric series with leading
  -- factor `F(y, a) ≤ 1`, so it is dominated by the full geometric series of `F(a, a)`.
  calc
    (G[P, X; 1]) y a =
        ∑' n : ℕ, ENNReal.ofReal (((F[P, X]) y a) * (F[P, X]) a a ^ n) := by
          rw [greenFunctionFrom_one_eq_tsum_everHits_mul_selfPowers (p := p) (P := P) (X := X)
            y a]
    _ ≤ ∑' n : ℕ, ENNReal.ofReal ((F[P, X]) a a ^ n) := by
          refine ENNReal.tsum_le_tsum fun n => ?_
          apply ENNReal.ofReal_le_ofReal
          have hpow_nonneg : 0 ≤ (F[P, X]) a a ^ n := pow_nonneg haa_nonneg n
          calc
            (F[P, X]) y a * (F[P, X]) a a ^ n ≤ 1 * (F[P, X]) a a ^ n := by
              exact mul_le_mul_of_nonneg_right hya_le_one hpow_nonneg
            _ = (F[P, X]) a a ^ n := by simp
    _ < ⊤ := hgeom_lt_top

/-- Helper for Example 19.3: transientness of the target state implies finiteness of the entire
fixed-target Green column. -/
private lemma greenFunction_fixedTarget_lt_top_of_transientState
    (p : E → E → ℝ≥0∞) (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel p ^ n) P X]
    {a : E} (ha : IsTransientState P X a) :
    ∀ y : E, (G[P, X]) y a < ⊤ := by
  intro y
  by_cases hya : y = a
  · subst y
    have hfrom :
        (G[P, X; 1]) a a < ⊤ :=
      greenFunctionFrom_one_lt_top_of_transientState (p := p) (P := P) (X := X) ha a
    -- Proof comment: split the diagonal Green function into the deterministic initial visit and
    -- the positive-time tail, then use finiteness of that tail.
    rw [greenFunctionSelf_eq_one_add_greenFunctionFromOneSelf (p := p) (P := P) (X := X) a]
    exact ENNReal.add_lt_top.2 ⟨by simp, hfrom⟩
  · -- Proof comment: away from the pole, the time-`0` Green summand vanishes, so finiteness of
    -- the full Green function is exactly the finiteness of the positive-time Green function.
    simpa [greenFunctionFrom_one_eq_greenFunction_offTarget (p := p) (P := P) (X := X) hya] using
      greenFunctionFrom_one_lt_top_of_transientState (p := p) (P := P) (X := X) ha y

/-- Helper for Example 19.3: finiteness of the full fixed-target Green column already implies
finiteness of the positive-time Green column. -/
private lemma greenFunctionFrom_one_lt_top_of_greenFinite
    (p : E → E → ℝ≥0∞) (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel p ^ n) P X]
    {a : E} (hgreenFinite : ∀ y : E, (G[P, X]) y a < ⊤) (x : E) :
    (G[P, X; 1]) x a < ⊤ := by
  by_cases hxa : x = a
  · subst x
    have hdiag : (G[P, X]) a a < ⊤ := hgreenFinite a
    -- Proof comment: on the diagonal, the full Green function splits into the deterministic first
    -- visit plus the positive-time tail.
    rw [greenFunctionSelf_eq_one_add_greenFunctionFromOneSelf (p := p) (P := P) (X := X) a] at hdiag
    exact (ENNReal.add_lt_top.mp hdiag).2
  · -- Proof comment: off the pole, the positive-time and full Green functions coincide.
    simpa [greenFunctionFrom_one_eq_greenFunction_offTarget (p := p) (P := P) (X := X) hxa] using
      hgreenFinite x

/-- Helper for Example 19.3: a finite Green convolution row gives an absolutely summable real row
for the fixed-target Green potential. -/
private lemma greenPotentialRowSummable_of_greenFinite
    (p : E → E → ℝ≥0∞) (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel p ^ n) P X]
    {a : E} (hgreenFinite : ∀ y : E, (G[P, X]) y a < ⊤) (x : E) :
    Summable (fun y : E ↦ (p x y).toReal * ‖((G[P, X]) y a).toReal‖) := by
  have hrow_ne_top : (∑' y : E, p x y * (G[P, X]) y a) ≠ ⊤ := by
    rw [← greenFunctionFrom_one_eq_tsum_stepMass_mul_greenFunction (p := p) (P := P) (X := X) x a]
    exact (greenFunctionFrom_one_lt_top_of_greenFinite
      (p := p) (P := P) (X := X) hgreenFinite x).ne
  have hrow_toReal :
      Summable (fun y : E ↦ (p x y * (G[P, X]) y a).toReal) :=
    ENNReal.summable_toReal hrow_ne_top
  -- Proof comment: the ENNReal row is nonnegative termwise, so taking `toReal` turns it into the
  -- absolute-value weighted real row needed for the Bochner integral theorem.
  simpa
    [ENNReal.toReal_mul, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    using hrow_toReal

/-- Helper for Example 19.3: the real weighted row sum of the Green potential is the positive-time
Green function. -/
private lemma greenPotentialRowTsum_eq_greenFunctionFromOne_toReal
    (p : E → E → ℝ≥0∞) (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel p ^ n) P X]
    {a : E} (hgreenFinite : ∀ y : E, (G[P, X]) y a < ⊤) (x : E) :
    (∑' y : E, (p x y).toReal * ((G[P, X]) y a).toReal) = ((G[P, X; 1]) x a).toReal := by
  have hp : IsStochasticMatrix p :=
    stochasticMatrix_of_realization (p := p) (P := P) (X := X)
  have hrow_ne_top : (∑' y : E, p x y * (G[P, X]) y a) ≠ ⊤ := by
    rw [← greenFunctionFrom_one_eq_tsum_stepMass_mul_greenFunction (p := p) (P := P) (X := X) x a]
    exact (greenFunctionFrom_one_lt_top_of_greenFinite
      (p := p) (P := P) (X := X) hgreenFinite x).ne
  have hterm_ne_top : ∀ y : E, p x y * (G[P, X]) y a ≠ ⊤ := by
    intro y
    have hentry_le_one : p x y ≤ 1 := by
      calc
        p x y ≤ ∑' z : E, p x z := ENNReal.le_tsum y
        _ = 1 := hp x
    have hentry_ne_top : p x y ≠ ⊤ :=
      (lt_of_le_of_lt hentry_le_one ENNReal.one_lt_top).ne
    exact ENNReal.mul_ne_top hentry_ne_top (hgreenFinite y).ne
  -- Proof comment: apply `ENNReal.tsum_toReal_eq` to the finite convolution series and rewrite
  -- each term through `ENNReal.toReal_mul`.
  calc
    ∑' y : E, (p x y).toReal * ((G[P, X]) y a).toReal
        = ∑' y : E, (p x y * (G[P, X]) y a).toReal := by
            refine tsum_congr fun y => ?_
            rw [ENNReal.toReal_mul]
    _ = (∑' y : E, p x y * (G[P, X]) y a).toReal := by
          symm
          exact ENNReal.tsum_toReal_eq hterm_ne_top
    _ = ((G[P, X; 1]) x a).toReal := by
          rw [greenFunctionFrom_one_eq_tsum_stepMass_mul_greenFunction (p := p) (P := P) (X := X)]

/-- Helper for Example 19.3: once the fixed-target Green column is finite, the one-step average
of the real-valued Green potential is exactly the positive-time Green value. -/
-- Route correction: the earlier proof converted the kernel average back from a finite `lintegral`.
-- The refactored route below first packages the Green row as an absolutely summable real series
-- and then applies the public discrete-kernel integral theorem directly.
private lemma greenPotential_stepAverage_eq_greenFunctionFromOne_of_greenFinite
    (p : E → E → ℝ≥0∞) (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel p ^ n) P X]
    {a : E} (hgreenFinite : ∀ y : E, (G[P, X]) y a < ⊤) (x : E) :
    Integrable (fun y ↦ ((G[P, X]) y a).toReal) (discreteMatrixKernel p x) ∧
      ∫ y, ((G[P, X]) y a).toReal ∂discreteMatrixKernel p x = ((G[P, X; 1]) x a).toReal := by
  have hp : IsStochasticMatrix p :=
    stochasticMatrix_of_realization (p := p) (P := P) (X := X)
  let g : E → ℝ≥0∞ := fun y ↦ (G[P, X]) y a
  have hgreenFromFinite : (G[P, X; 1]) x a < ⊤ :=
    greenFunctionFrom_one_lt_top_of_greenFinite
      (p := p) (P := P) (X := X) hgreenFinite x
  have hrowSummable :
      Summable (fun y : E ↦ (p x y).toReal * ‖((G[P, X]) y a).toReal‖) :=
    greenPotentialRowSummable_of_greenFinite
      (p := p) (P := P) (X := X) hgreenFinite x
  have hgMeas : Measurable g := Measurable.of_discrete
  have hlintegral :
      ∫⁻ y, g y ∂discreteMatrixKernel p x = (G[P, X; 1]) x a := by
    -- Proof comment: expand the one-step row integral into the weighted Green series and use the
    -- discrete Chapman--Kolmogorov identity already proved for `G[P, X; 1]`.
    rw [lintegral_discreteMatrixKernel_eq_tsum]
    symm
    exact greenFunctionFrom_one_eq_tsum_stepMass_mul_greenFunction
      (p := p) (P := P) (X := X) x a
  have hlintegral_ne_top :
      ∫⁻ y, g y ∂discreteMatrixKernel p x ≠ ⊤ := by
    rw [hlintegral]
    exact hgreenFromFinite.ne
  have hgIntegrable :
      Integrable (fun y ↦ (g y).toReal) (discreteMatrixKernel p x) := by
    exact integrable_toReal_of_lintegral_ne_top hgMeas.aemeasurable hlintegral_ne_top
  have hgFiniteAe :
      ∀ᵐ y ∂discreteMatrixKernel p x, g y < ⊤ :=
    ae_lt_top hgMeas hlintegral_ne_top
  refine ⟨hgIntegrable, ?_⟩
  -- Proof comment: with absolute row summability available, the public discrete-kernel integral
  -- theorem turns the one-step average into the real Green convolution series, which the previous
  -- helper identifies with `((G[P, X; 1]) x a).toReal`.
  calc
    ∫ y, ((G[P, X]) y a).toReal ∂discreteMatrixKernel p x
        = ∑' y : E, (p x y).toReal * ((G[P, X]) y a).toReal := by
            simpa [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg] using
              (integral_discreteMatrixKernel_eq_tsum
                p hp (fun y ↦ ((G[P, X]) y a).toReal) x hrowSummable)
    _ = ((G[P, X; 1]) x a).toReal := by
          exact greenPotentialRowTsum_eq_greenFunctionFromOne_toReal
            (p := p) (P := P) (X := X) hgreenFinite x

/-- Helper for Example 19.3: averaging the fixed-target Green potential over one step gives the
positive-time Green function. -/
private lemma greenPotential_stepAverage_eq_greenFunctionFromOne
    (p : E → E → ℝ≥0∞) (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel p ^ n) P X]
    {a : E} (ha : IsTransientState P X a) (x : E) :
    Integrable (fun y ↦ ((G[P, X]) y a).toReal) (discreteMatrixKernel p x) ∧
      ∫ y, ((G[P, X]) y a).toReal ∂discreteMatrixKernel p x = ((G[P, X; 1]) x a).toReal :=
  greenPotential_stepAverage_eq_greenFunctionFromOne_of_greenFinite
    (p := p) (P := P) (X := X)
    (greenFunction_fixedTarget_lt_top_of_transientState (p := p) (P := P) (X := X) ha) x

/-- Helper for Example 19.3: in a transient chain, a nonabsorbing state cannot be recurrent, so
it is transient in the Chapter 17 state sense. -/
private lemma nonabsorbing_isTransientState_of_isTransientMarkovChain
    (p : E → E → ℝ≥0∞) (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel p ^ n) P X]
    (htransient : IsTransientMarkovChain p P X) {a : E}
    (ha : ¬ IsAbsorbingState p a) :
    IsTransientState P X a := by
  by_contra hnot
  have hnot_transient : ¬ (F[P, X]) a a < 1 := by
    simpa [IsTransientState] using hnot
  have hle : (F[P, X]) a a ≤ 1 := by
    -- Proof comment: `F[P, X] a a` is the probability of a measurable event under `P a`.
    rw [everHitsProbability_def]
    exact measureReal_le_one
  have hrec : IsRecurrentState P X a := by
    -- Proof comment: a real probability bounded above by `1` and not strictly below `1` must
    -- equal `1`.
    rw [IsRecurrentState]
    refine le_antisymm hle ?_
    exact le_of_not_gt hnot_transient
  exact ha (htransient a hrec)

-- Proof sketch: if `a` is transient in the Chapter 17 owner sense, then the Green function is
-- finite at `a`, so the source-facing potential is the real-valued function
-- `x ↦ ((G[P, X]) x a).toReal`. Expand `G[P, X]` by
-- `greenFunction_eq_tsum_stateProbabilities`, rewrite the one-step average against
-- `discreteMatrixKernel p` using the Markov realization, and shift the visit-probability series.
-- Outside `{a}` the missing `n = 0` term is `0`, so the shifted series recovers `G(x, a)`,
-- yielding the Chapter 19 harmonicity predicate on `E \ {a}`.
/- Example 19.3 is `source-facing`: the distinguished state is assumed transient via the Chapter 17
owner predicate `IsTransientState P X a`. The chain-level notion `IsTransientMarkovChain p P X`
and the concrete condition `¬ IsAbsorbingState p a` remain only a `bridge/view` reformulation. -/
/-- Example 19.3: for a discrete-time Markov chain with transition matrix `p`, if `a` is
transient, then the real-valued Green potential
`x ↦ ((G[P, X]) x a).toReal` is harmonic on `E \ {a}`. -/
theorem greenFunction_harmonic_off_transient_state
    (p : E → E → ℝ≥0∞) (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel p ^ n) P X]
    {a : E} (ha : IsTransientState P X a) :
    IsHarmonicOutside (discreteMatrixKernel p) ({a} : Set E)
      (fun x ↦ ((G[P, X]) x a).toReal) := by
  intro x hx
  have hxa : x ≠ a := by
    simpa using hx
  have hstep :=
    greenPotential_stepAverage_eq_greenFunctionFromOne (p := p) (P := P) (X := X) ha x
  refine ⟨hstep.1, ?_⟩
  -- Proof comment: the one-step average is the positive-time Green term, and away from `a` that
  -- already equals the full Green function.
  calc
    ((G[P, X]) x a).toReal = ((G[P, X; 1]) x a).toReal := by
      rw [greenFunctionFrom_one_eq_greenFunction_offTarget (p := p) (P := P) (X := X) hxa]
    _ = ∫ y, ((G[P, X]) y a).toReal ∂discreteMatrixKernel p x := by
      symm
      exact hstep.2

-- Proof sketch: under `IsTransientMarkovChain p P X`, a nonabsorbing state cannot be recurrent;
-- since `F[P, X] a a` is a probability, this forces `F[P, X] a a < 1`, i.e. `a` is transient.
-- Apply the source-facing harmonicity theorem above.
/-- Bridge reformulation: in a transient chain, every nonabsorbing state has harmonic Green
potential off the singleton `{a}`. -/
theorem greenFunction_harmonic_off_nonabsorbing_state
    (p : E → E → ℝ≥0∞) (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel p ^ n) P X]
    (htransient : IsTransientMarkovChain p P X) {a : E}
    (ha : ¬ IsAbsorbingState p a) :
    IsHarmonicOutside (discreteMatrixKernel p) ({a} : Set E)
      (fun x ↦ ((G[P, X]) x a).toReal) := by
  -- Proof comment: first convert the nonabsorbing hypothesis into the Chapter 17 transient-state
  -- predicate, then invoke the source-facing harmonicity theorem.
  have haTransient :
      IsTransientState P X a :=
    nonabsorbing_isTransientState_of_isTransientMarkovChain
      (p := p) (P := P) (X := X) htransient ha
  exact greenFunction_harmonic_off_transient_state (p := p) (P := P) (X := X) haTransient

end ProbabilityTheory
