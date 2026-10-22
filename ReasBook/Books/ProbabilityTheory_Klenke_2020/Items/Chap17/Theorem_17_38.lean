/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Lemma_14_27
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_28
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_30
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_33
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_36
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_29
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_17
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_38.PositiveVisitNormalization
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]
variable {Ω : Type v} [MeasurableSpace Ω]

section FiniteStateSpace

variable [Finite E]
attribute [local instance] Fintype.ofFinite
variable (p : E → E → ℝ≥0∞) (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
variable [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel p ^ n) P X]

include p P X

/-- Helper for Theorem 17.38: `ℕ+` is used as a discrete counting index for iterated entrance
times. -/
local instance : MeasurableSpace ℕ+ := ⊤

/-- Helper for Theorem 17.38: the measurable structure on `ℕ+` is discrete. -/
local instance : DiscreteMeasurableSpace ℕ+ where
  forall_measurableSet := by
    intro s
    trivial

/-- Helper for Theorem 17.38: the finite state space is used classically inside the entrance-count
normalization lemmas. -/
local instance : DecidableEq E := Classical.decEq E

/-- Helper for Theorem 17.38: at a fixed time `n`, the state probabilities of the realized chain
sum to `1` over the finite state space. -/
private lemma stateProbabilitySum_eq_one (x : E) (n : ℕ) :
    ∑ y : E, (P x : Measure Ω) {ω | X n ω = y} = 1 := by
  let hReal : IsMarkovProcessRealization (fun m ↦ discreteMatrixKernel p ^ m) P X := inferInstance
  let μ : Measure E := (P x : Measure Ω).map (X n)
  have hsum :
      ∑ y : E, μ {y} = 1 := by
    calc
      ∑ y : E, μ {y} = ∑' y : E, μ {y} := by
        symm
        exact tsum_eq_sum (s := Finset.univ) (by
          intro y hy
          simp at hy)
      _ = μ Set.univ := by
        simpa using μ.tsum_indicator_apply_singleton Set.univ MeasurableSet.univ
      _ = 1 := by
        dsimp [μ]
        rw [Measure.map_apply (hReal.measurable_process n) MeasurableSet.univ]
        simp
  -- Proof comment: rewrite each time-`n` event as the singleton mass of the mapped law.
  calc
    ∑ y : E, (P x : Measure Ω) {ω | X n ω = y}
      = ∑ y : E, μ {y} := by
          congr with y
          have hpreimage : {ω | X n ω = y} = X n ⁻¹' ({y} : Set E) := by
            ext ω
            simp
          rw [hpreimage]
          rw [← Measure.map_apply (hReal.measurable_process n) (MeasurableSet.singleton y)]
    _ = 1 := hsum

/-- Helper for Theorem 17.38: every Green row has infinite total mass on a finite state space. -/
private lemma greenFunctionRowSum_eq_top (x : E) :
    ∑ y : E, (G[P, X]) x y = ⊤ := by
  let hReal : IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  let hX : IsStochasticProcess X := fun n ↦ hReal.measurable_process n
  -- Proof comment: expand `G[P, X]` into the time-slice series, commute the finite state sum with
  -- the time sum, and collapse each time slice to `1`.
  calc
    ∑ y : E, (G[P, X]) x y
      = ∑ y : E, ∑' n : ℕ, (P x : Measure Ω) {ω | X n ω = y} := by
          congr with y
          rw [greenFunction_eq_tsum_stateProbabilities P X hX x y]
    _ = ∑' y : E, ∑' n : ℕ, (P x : Measure Ω) {ω | X n ω = y} := by
          rw [tsum_fintype]
    _ = ∑' n : ℕ, ∑' y : E, (P x : Measure Ω) {ω | X n ω = y} := by
          simpa using
            (ENNReal.tsum_comm
              (f := fun y : E ↦ fun n : ℕ ↦ (P x : Measure Ω) {ω | X n ω = y}))
    _ = ∑' n : ℕ, ∑ y : E, (P x : Measure Ω) {ω | X n ω = y} := by
          refine tsum_congr fun n => ?_
          rw [tsum_fintype]
    _ = ∑' _n : ℕ, (1 : ℝ≥0∞) := by
          refine tsum_congr fun n => ?_
          exact stateProbabilitySum_eq_one (p := p) (P := P) (X := X) x n
    _ = ⊤ := by
          exact ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero

/-- Helper for Theorem 17.38: if a finite Green row sums to `⊤`, then one entry in that row is
already `⊤`. -/
private lemma exists_greenFunction_eq_top_of_rowSum_eq_top (x : E)
    (hrow : ∑ y : E, (G[P, X]) x y = ⊤) :
    ∃ y : E, (G[P, X]) x y = ⊤ := by
  by_contra hnone
  have hlt : ∑ y : E, (G[P, X]) x y < ⊤ := by
    refine ENNReal.sum_lt_top.2 ?_
    intro y hy
    exact lt_top_iff_ne_top.2 fun hy_top ↦ hnone ⟨y, hy_top⟩
  exact hlt.ne hrow

/-- Helper for Theorem 17.38: composing two singleton transition masses gives a lower bound on the
singleton mass after the combined time. -/
private lemma singletonStepMass_mul_singletonStepMass_le_stepMass
    (a b c : E) (m n : ℕ) :
    (((discreteMatrixKernel p ^ m) a) ({b} : Set E)) *
        (((discreteMatrixKernel p ^ n) b) ({c} : Set E)) ≤
      (((discreteMatrixKernel p ^ (m + n)) a) ({c} : Set E)) := by
  let hReal : IsMarkovProcessRealization (fun k ↦ discreteMatrixKernel p ^ k) P X := inferInstance
  -- Proof comment: expand the composed kernel at the singleton `{c}` and keep only the
  -- intermediate state `b` in the resulting finite sum.
  calc
    (((discreteMatrixKernel p ^ m) a) ({b} : Set E)) *
        (((discreteMatrixKernel p ^ n) b) ({c} : Set E))
      = (((discreteMatrixKernel p ^ n) b) ({c} : Set E)) *
          (((discreteMatrixKernel p ^ m) a) ({b} : Set E)) := by
            rw [mul_comm]
    _ ≤ ∑' z : E, (((discreteMatrixKernel p ^ n) z) ({c} : Set E)) *
          (((discreteMatrixKernel p ^ m) a) ({z} : Set E)) := by
            exact ENNReal.le_tsum b
    _ = (((discreteMatrixKernel p ^ (m + n)) a) ({c} : Set E)) := by
          rw [← hReal.semigroup.comp_eq m n]
          rw [Kernel.comp_apply' _ _ _ (MeasurableSet.singleton c)]
          rw [MeasureTheory.lintegral_fintype]
          simp [mul_comm]

/-- Helper for Theorem 17.38: a positive `k`-step path from `y` back to `x` turns an infinite
Green mass from `x` to `y` into an infinite diagonal Green mass at `x`. -/
private lemma greenFunctionSelf_eq_top_of_greenFunctionTop_andStepMass
    (x y : E) {k : ℕ}
    (hxy_top : (G[P, X]) x y = ⊤)
    (hkx : 0 < ((discreteMatrixKernel p ^ k) y) ({x} : Set E)) :
    (G[P, X]) x x = ⊤ := by
  let hReal : IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  let hX : IsStochasticProcess X := fun n ↦ hReal.measurable_process n
  let c : ℝ≥0∞ := ((discreteMatrixKernel p ^ k) y) ({x} : Set E)
  have hc_ne_zero : c ≠ 0 := hkx.ne'
  have hy_series :
      ∑' n : ℕ, (P x : Measure Ω) {ω | X n ω = y} = ⊤ := by
    simpa [greenFunction_eq_tsum_stateProbabilities P X hX x y] using hxy_top
  have hterm_le :
      ∀ n : ℕ,
        (P x : Measure Ω) {ω | X n ω = y} * c ≤
          (P x : Measure Ω) {ω | X (n + k) ω = x} := by
    intro n
    have hpreimage_y : {ω | X n ω = y} = X n ⁻¹' ({y} : Set E) := by
      ext ω
      simp
    have hpreimage_x : {ω | X (n + k) ω = x} = X (n + k) ⁻¹' ({x} : Set E) := by
      ext ω
      simp
    -- Proof comment: the cross mass at time `n` followed by the positive `k`-step path from `y`
    -- back to `x` yields a lower bound on the diagonal mass at time `n + k`.
    calc
      (P x : Measure Ω) {ω | X n ω = y} * c
        = ((discreteMatrixKernel p ^ n) x) ({y} : Set E) * c := by
            rw [hpreimage_y]
            rw [← Measure.map_apply (hReal.measurable_process n) (MeasurableSet.singleton y)]
            rw [hReal.transition_eq x n]
      _ = ((discreteMatrixKernel p ^ n) x) ({y} : Set E) *
            ((discreteMatrixKernel p ^ k) y) ({x} : Set E) := by
            simp [c]
      _ ≤ ((discreteMatrixKernel p ^ (n + k)) x) ({x} : Set E) := by
            simpa using
              singletonStepMass_mul_singletonStepMass_le_stepMass
                (p := p) (P := P) (X := X) x y x n k
      _ = (P x : Measure Ω) {ω | X (n + k) ω = x} := by
            rw [hpreimage_x]
            rw [← Measure.map_apply (hReal.measurable_process (n + k))
              (MeasurableSet.singleton x)]
            rw [hReal.transition_eq x (n + k)]
  have hscaled_top :
      ∑' n : ℕ, (P x : Measure Ω) {ω | X n ω = y} * c = ⊤ := by
    calc
      ∑' n : ℕ, (P x : Measure Ω) {ω | X n ω = y} * c
        = (∑' n : ℕ, (P x : Measure Ω) {ω | X n ω = y}) * c := by
            rw [ENNReal.tsum_mul_right]
      _ = ⊤ := by
            simpa [hy_series, hc_ne_zero] using
              congrArg (fun t : ℝ≥0∞ ↦ t * c) hy_series
  have htail_top :
      ∑' n : ℕ, (P x : Measure Ω) {ω | X (n + k) ω = x} = ⊤ := by
    apply top_unique
    rw [← hscaled_top]
    exact ENNReal.tsum_le_tsum hterm_le
  by_contra hxx_ne_top
  have hdiag_series_ne_top :
      ∑' n : ℕ, (P x : Measure Ω) {ω | X n ω = x} ≠ ⊤ := by
    simpa [greenFunction_eq_tsum_stateProbabilities P X hX x x] using hxx_ne_top
  have hdiag_lt_top :
      ∑' n : ℕ, (P x : Measure Ω) {ω | X n ω = x} < ⊤ :=
    lt_top_iff_ne_top.2 hdiag_series_ne_top
  have htail_le :
      ∑' n : ℕ, (P x : Measure Ω) {ω | X (n + k) ω = x} ≤
        ∑' n : ℕ, (P x : Measure Ω) {ω | X n ω = x} := by
    exact
      (ENNReal.summable.tsum_le_tsum_of_inj (fun n : ℕ ↦ n + k)
        (by
          intro a b hab
          exact Nat.add_right_cancel hab)
        (fun _ _ ↦ zero_le _) (fun _ ↦ le_rfl)) ENNReal.summable
  have htail_ne_top :
      ∑' n : ℕ, (P x : Measure Ω) {ω | X (n + k) ω = x} ≠ ⊤ := by
    exact lt_top_iff_ne_top.1 (lt_of_le_of_lt htail_le hdiag_lt_top)
  exact htail_ne_top htail_top

/-- Helper for Theorem 17.38: the full diagonal Green value splits into the deterministic
time-`0` visit and the strictly positive-time diagonal Green tail. -/
private lemma greenFunctionSelf_eq_one_add_greenFunctionFromOneSelf (x : E) :
    (G[P, X]) x x = 1 + (G[P, X; 1]) x x := by
  let hReal : IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  let hX : IsStochasticProcess X := fun n ↦ hReal.measurable_process n
  have hzero :
      (P x : Measure Ω) {ω | X 0 ω = x} = 1 := by
    have hpreimage : {ω | X 0 ω = x} = X 0 ⁻¹' ({x} : Set E) := by
      ext ω
      simp
    -- Proof comment: under `P x`, the chain starts at `x` with probability one at time `0`.
    calc
      (P x : Measure Ω) {ω | X 0 ω = x}
        = ((P x : Measure Ω).map (X 0)) ({x} : Set E) := by
            rw [hpreimage]
            rw [← Measure.map_apply (hReal.measurable_process 0) (MeasurableSet.singleton x)]
      _ = Measure.dirac x ({x} : Set E) := by
            rw [hReal.initial_eq x]
      _ = 1 := by
            simp
  -- Proof comment: isolate the time-`0` term in the full Green series and rewrite the rest as
  -- the positive-time Green function.
  calc
    (G[P, X]) x x = ∑' n : ℕ, (P x : Measure Ω) {ω | X n ω = x} := by
      rw [greenFunction_eq_tsum_stateProbabilities P X hX x x]
    _ = (P x : Measure Ω) {ω | X 0 ω = x} +
        ∑' n : ℕ, ite (n = 0) 0 ((P x : Measure Ω) {ω | X n ω = x}) := by
          classical
          have hsplit :
              ∑' n : ℕ, (P x : Measure Ω) {ω | X n ω = x} =
                (P x : Measure Ω) {ω | X 0 ω = x} +
                  ∑' n : ℕ,
                    @ite ℝ≥0∞ (n = 0) (Classical.propDecidable (n = 0)) 0
                      ((P x : Measure Ω) {ω | X n ω = x}) := by
            exact ENNReal.tsum_eq_add_tsum_ite
              (f := fun n : ℕ ↦ (P x : Measure Ω) {ω | X n ω = x}) 0
          calc
            ∑' n : ℕ, (P x : Measure Ω) {ω | X n ω = x} =
                (P x : Measure Ω) {ω | X 0 ω = x} +
                  ∑' n : ℕ,
                    @ite ℝ≥0∞ (n = 0) (Classical.propDecidable (n = 0)) 0
                      ((P x : Measure Ω) {ω | X n ω = x}) := hsplit
            _ = (P x : Measure Ω) {ω | X 0 ω = x} +
                  ∑' n : ℕ, ite (n = 0) 0 ((P x : Measure Ω) {ω | X n ω = x}) := by
                    congr 1
                    refine tsum_congr fun n ↦ ?_
                    by_cases hn : n = 0
                    · simp [hn]
                    · simp [hn]
    _ = 1 + ∑' n : ℕ, ite (n = 0) 0 ((P x : Measure Ω) {ω | X n ω = x}) := by
          simp [hzero]
    _ = 1 + ∑' n : ℕ, (P x : Measure Ω) {ω | 0 < n ∧ X n ω = x} := by
          congr 1
          refine tsum_congr fun n ↦ ?_
          by_cases hn : n = 0
          · subst hn
            simp
          · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
            simp [hn, hnpos]
    _ = 1 + (G[P, X; 1]) x x := by
          rw [greenFunctionFrom_one_eq_tsum_positiveStateProbabilities P X hX x x]

section PathwiseNormalization

omit p P X

/-- Helper for Theorem 17.38: a shifted geometric series of `ℝ≥0∞`-casts is finite whenever the
ratio lies in `[0, 1)`. -/
private lemma ennrealOfRealTsumGeometricSucc_lt_top {q : ℝ}
    (hq_nonneg : 0 ≤ q) (hq_lt_one : q < 1) :
    ∑' n : ℕ, ENNReal.ofReal (q ^ (n + 1)) < ⊤ := by
  have hsum : Summable (fun n : ℕ ↦ q ^ (n + 1)) :=
    (_root_.summable_nat_add_iff 1).2 (summable_geometric_of_lt_one hq_nonneg hq_lt_one)
  -- Proof comment: summability in `ℝ` keeps the nonnegative `ℝ≥0∞` casts finite termwise.
  calc
    ∑' n : ℕ, ENNReal.ofReal (q ^ (n + 1))
      = ENNReal.ofReal (∑' n : ℕ, q ^ (n + 1)) := by
          rw [ENNReal.ofReal_tsum_of_nonneg]
          · intro n
            exact pow_nonneg hq_nonneg _
          · exact hsum
    _ < ⊤ := by
          simp

end PathwiseNormalization

/-- Helper for Theorem 17.38: Theorem 17.29 specialized to `(x, x)` turns the iterated entrance
probability series into the shifted power series of `F(x, x)`. -/
private lemma iteratedEntranceProbabilitySeries_eq_selfPowerSeries
    (x : E) :
    (∑' k : ℕ+, ENNReal.ofReal ((P x : Measure Ω).real {ω | (τ_[X, x]^k) ω < ⊤})) =
      ∑' n : ℕ, ENNReal.ofReal (((F[P, X]) x x) ^ (n + 1)) := by
  let κ : ℕ → Kernel E E := fun n ↦ discreteMatrixKernel p ^ n
  let _ : IsMarkovProcessRealization κ P X := inferInstance
  -- Proof comment: replace each entrance probability by the Theorem 17.29 formula, then reindex
  -- the `ℕ+`-sum along `Equiv.pnatEquivNat`.
  calc
    (∑' k : ℕ+, ENNReal.ofReal ((P x : Measure Ω).real {ω | (τ_[X, x]^k) ω < ⊤})) =
        ∑' k : ℕ+, ENNReal.ofReal ((F[P, X]) x x * (F[P, X]) x x ^ k.natPred) := by
          refine tsum_congr fun k ↦ ?_
          simpa using congrArg ENNReal.ofReal
            (iteratedEntranceTime_finite_probability_eq_everHitsProbability_mul_selfPow
              (κ := κ) (P := P) (X := X) x x k)
    _ = ∑' n : ℕ, ENNReal.ofReal ((F[P, X]) x x * (F[P, X]) x x ^ n) := by
          simpa using
            (Equiv.tsum_eq Equiv.pnatEquivNat
              (fun n : ℕ ↦ ENNReal.ofReal ((F[P, X]) x x * (F[P, X]) x x ^ n)))
    _ = ∑' n : ℕ, ENNReal.ofReal (((F[P, X]) x x) ^ (n + 1)) := by
          refine tsum_congr fun n ↦ ?_
          rw [pow_succ, mul_comm]

/-- Helper for Theorem 17.38: the positive-time diagonal Green function is the shifted power
series of the return probability. -/
private lemma greenFunctionFromOneSelf_eq_tsum_selfPowers
    (x : E) :
    (G[P, X; 1]) x x =
      ∑' n : ℕ, ENNReal.ofReal (((F[P, X]) x x) ^ (n + 1)) := by
  -- Proof comment: combine the pathwise entrance-count normalization with the `ℕ+`-to-`ℕ`
  -- reindexing from Theorem 17.29.
  exact
    (greenFunctionFromOneSelf_eq_tsum_iteratedEntranceProbabilities
      (κ := fun n ↦ discreteMatrixKernel p ^ n) (P := P) (X := X) x).trans
      (iteratedEntranceProbabilitySeries_eq_selfPowerSeries
        (p := p) (P := P) (X := X) x)

/-- Helper for Theorem 17.38: an infinite diagonal Green value forces recurrence. -/
private lemma isRecurrentState_of_greenFunctionSelf_eq_top (x : E)
    (hx : (G[P, X]) x x = ⊤) :
    IsRecurrentState P X x := by
  have hq_nonneg : 0 ≤ (F[P, X]) x x := measureReal_nonneg
  have hq_le_one : (F[P, X]) x x ≤ 1 := by
    rw [everHitsProbability_def]
    exact measureReal_le_one
  -- Route correction: instead of unfolding `G[P, X]` directly, normalize the positive-time
  -- diagonal Green tail to the shifted power series in `F(x, x)` and close by a geometric
  -- contradiction.
  by_contra htrans
  have hq_lt_one : (F[P, X]) x x < 1 := by
    rw [IsRecurrentState] at htrans
    exact lt_of_le_of_ne hq_le_one (by simpa [eq_comm] using htrans)
  have htail_lt_top :
      ∑' n : ℕ, ENNReal.ofReal (((F[P, X]) x x) ^ (n + 1)) < ⊤ :=
    ennrealOfRealTsumGeometricSucc_lt_top hq_nonneg hq_lt_one
  have hgreen_lt_top : (G[P, X]) x x < ⊤ := by
    calc
      (G[P, X]) x x = 1 + (G[P, X; 1]) x x := by
        rw [greenFunctionSelf_eq_one_add_greenFunctionFromOneSelf (p := p) (P := P) (X := X)]
      _ = 1 + ∑' n : ℕ, ENNReal.ofReal (((F[P, X]) x x) ^ (n + 1)) := by
        rw [greenFunctionFromOneSelf_eq_tsum_selfPowers (p := p) (P := P) (X := X)]
      _ < ⊤ := by
        exact ENNReal.add_lt_top.2 ⟨by simp, htail_lt_top⟩
  exact (ne_of_lt hgreen_lt_top) hx

/-- Helper for Theorem 17.38: kernel irreducibility of `discreteMatrixKernel p` yields the
Chapter 17 irreducibility predicate for the realized chain. -/
private lemma isIrreducibleMarkovChain_of_discreteMatrixKernelIsIrreducible
    [Kernel.IsIrreducible (Measure.count : Measure E) (discreteMatrixKernel p)] :
    IsIrreducibleMarkovChain P X := by
  have hgreen :
      ∀ ⦃x y : E⦄, x ≠ y → 0 < (G[P, X; 1]) x y := by
    intro x y hxy
    have hy_pos : 0 < (Measure.count : Measure E) ({y} : Set E) := by
      simp
    rcases (inferInstance : Kernel.IsIrreducible (Measure.count : Measure E)
        (discreteMatrixKernel p)).irreducible
        (A := ({y} : Set E)) (MeasurableSet.singleton y) hy_pos x with ⟨n, hn⟩
    have hnpos : 0 < n := by
      by_contra hnpos
      have hnzero : n = 0 := Nat.eq_zero_of_not_pos hnpos
      subst hnzero
      have hzero : ((discreteMatrixKernel p ^ 0) x) ({y} : Set E) = 0 := by
        change (Kernel.id x) ({y} : Set E) = 0
        simp [Kernel.id_apply, hxy]
      rw [hzero] at hn
      exact lt_irrefl _ hn
    exact greenFunctionFrom_one_pos_of_posStepMass
      (κ := fun m ↦ discreteMatrixKernel p ^ m) P X hnpos hn
  exact
    (isIrreducibleMarkovChain_iff_greenFunctionFrom_one_pos_offDiagonal
      (κ := fun n ↦ discreteMatrixKernel p ^ n) P X).2 hgreen

-- Proof sketch: apply the source-facing row-sum argument to get some state `y` with
-- `G(x, y) = ⊤`, then use irreducibility to find a positive path from `y` back to `x`.
-- The remaining blocked endpoint is the standard Chapter 17 implication `G(x, x) = ⊤ -> recurrent`.
/-- Theorem 17.38: if the discrete state space `E` is finite and the realized chain with
transition matrix `p` is irreducible in the Chapter 17 sense, then the chain is recurrent. -/
theorem finite_irreducibleMarkovChain_isRecurrent
    (hirr : IsIrreducibleMarkovChain P X) :
    IsRecurrentMarkovChain P X := by
  classical
  intro x
  have hrow : ∑ y : E, (G[P, X]) x y = ⊤ :=
    greenFunctionRowSum_eq_top (p := p) (P := P) (X := X) x
  obtain ⟨y, hy_top⟩ :=
    exists_greenFunction_eq_top_of_rowSum_eq_top (p := p) (P := P) (X := X) x hrow
  have hxx_top : (G[P, X]) x x = ⊤ := by
    by_cases hyx : y = x
    · simpa [hyx] using hy_top
    · have hyx_greenFrom :
        0 < (G[P, X; 1]) y x := by
          exact
            (isIrreducibleMarkovChain_iff_greenFunctionFrom_one_pos_offDiagonal
              (κ := fun n ↦ discreteMatrixKernel p ^ n) P X).1 hirr hyx
      rcases existsPosStepMass_of_greenFunctionFrom_one_pos
          (κ := fun n ↦ discreteMatrixKernel p ^ n) P X hyx_greenFrom with
        ⟨k, hkpos, hkx⟩
      exact greenFunctionSelf_eq_top_of_greenFunctionTop_andStepMass
        (p := p) (P := P) (X := X) x y hy_top hkx
  exact isRecurrentState_of_greenFunctionSelf_eq_top (p := p) (P := P) (X := X) x hxx_top

-- Proof sketch: pass from the discrete-kernel irreducibility of `discreteMatrixKernel p` to the
-- source-facing Chapter 17 predicate `IsIrreducibleMarkovChain P X`, then apply Theorem 17.38.
/-- Kernel-style specialization of Theorem 17.38 for realizations of a stochastic matrix. -/
theorem finite_irreducibleMarkovChain_isRecurrent_of_discreteMatrixKernel_isIrreducible
    [Kernel.IsIrreducible (Measure.count : Measure E) (discreteMatrixKernel p)] :
    IsRecurrentMarkovChain P X := by
  apply finite_irreducibleMarkovChain_isRecurrent (p := p) (P := P) (X := X)
  exact isIrreducibleMarkovChain_of_discreteMatrixKernelIsIrreducible
    (p := p) (P := P) (X := X)

end FiniteStateSpace

end ProbabilityTheory
