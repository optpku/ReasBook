/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Lemma_14_27
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_16
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_28
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_30
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_33
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_43
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.MarkovProcessRealization
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_29
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_38.PositiveVisitNormalization
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Example_17_18
import Books.ProbabilityTheory_Klenke_2020.Items.Chap10.Example_10_6
import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Theorem_5_11
import Mathlib

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Helper for Theorem 17.40: a bound on the infimum of a set of natural times in `ℕ∞` is
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

/-- Helper for Theorem 17.40: the successor entrance time is bounded by `N` exactly when there is
some visit to `y` by time `N` that occurs strictly after the previous entrance. -/
private lemma iteratedEntranceTime_succ_le_iff_existsHitAfter
    {Ω' E : Type*} (Y : ℕ → Ω' → E) (y : E) (ω : Ω') (k : ℕ+) (N : ℕ) :
    (τ_[Y, y]^(k + 1)) ω ≤ N ↔ ∃ n : ℕ, (τ_[Y, y]^k) ω < n ∧ n ≤ N ∧ Y n ω = y := by
  -- Proof comment: unfold the recursive successor step and replace the `sInf` bound by a witness.
  rw [iteratedEntranceTime_succ]
  rw [sInf_natImage_le_iff]
  constructor
  · rintro ⟨n, hn, hnN⟩
    exact ⟨n, hn.1, hnN, hn.2⟩
  · rintro ⟨n, hτ, hnN, hy⟩
    exact ⟨n, ⟨hτ, hy⟩, hnN⟩

/-- Helper for Theorem 17.40: every iterated entrance time is at least its positive index. -/
private lemma iteratedEntranceTime_index_le
    {Ω' E : Type*} (Y : ℕ → Ω' → E) (y : E) (ω : Ω') :
    ∀ k : ℕ+, ((k : ℕ) : ℕ∞) ≤ (τ_[Y, y]^k) ω := by
  intro k
  induction k using PNat.recOn with
  | one =>
      -- Proof comment: the first entrance time starts searching at time `1`.
      simpa [iteratedEntranceTime_one] using
        (le_hittingAfter (u := Y) (s := ({y} : Set E)) (n := 1) ω)
  | succ k ih =>
      by_cases htop : (τ_[Y, y]^(k + 1)) ω = ⊤
      · simp [htop]
      · have hnot_le_k : ¬ (τ_[Y, y]^(k + 1)) ω ≤ (k : ℕ) := by
          intro hle
          rcases (iteratedEntranceTime_succ_le_iff_existsHitAfter Y y ω k k).1 hle with
            ⟨n, hnτ, hnk, _⟩
          have hk_le_n : ((k : ℕ) : ℕ∞) < n := lt_of_le_of_lt ih hnτ
          have hk_le_n_nat : (k : ℕ) < n := by
            exact_mod_cast hk_le_n
          exact (Nat.not_lt_of_ge hnk) hk_le_n_nat
        have hk_toNat_lt : (k : ℕ) < ENat.toNat ((τ_[Y, y]^(k + 1)) ω) := by
          by_contra hk_toNat
          have htoNat_le : ENat.toNat ((τ_[Y, y]^(k + 1)) ω) ≤ (k : ℕ) :=
            Nat.not_lt.mp hk_toNat
          have hle : (τ_[Y, y]^(k + 1)) ω ≤ (k : ℕ) := by
            rw [← ENat.coe_toNat htop]
            exact_mod_cast htoNat_le
          exact hnot_le_k hle
        rw [← ENat.coe_toNat htop]
        exact_mod_cast Nat.succ_le_of_lt hk_toNat_lt

/-- Helper for Theorem 17.40: the generated history filtration is monotone in the time index. -/
private lemma generatedFiltrationSpace_mono
    {Ω' E : Type*} [MeasurableSpace E] (Y : ℕ → Ω' → E) {m n : ℕ} (hmn : m ≤ n) :
    generatedFiltrationSpace Y m ≤ generatedFiltrationSpace Y n := by
  -- Proof comment: enlarging the time horizon only adds more coordinate sigma-algebras.
  refine iSup₂_le fun r hr ↦ ?_
  exact le_iSup_of_le r <| le_iSup_of_le (hr.trans hmn) le_rfl

/-- Helper for Theorem 17.40: every coordinate is measurable with respect to any later generated
history filtration. -/
private lemma measurable_process_generated
    {Ω' E : Type*} [MeasurableSpace E] (Y : ℕ → Ω' → E) {i n : ℕ} (hi : i ≤ n) :
    @Measurable Ω' E (generatedFiltrationSpace Y n) _ (Y i) := by
  -- Proof comment: the coordinate sigma-algebra at time `i` is one of the generators of the
  -- history filtration at every later time `n`.
  exact Measurable.of_comap_le <|
    le_iSup_of_le i <| le_iSup_of_le hi le_rfl

/-- Helper for Theorem 17.40: singleton state events are measurable in every generated filtration
that already sees the corresponding coordinate. -/
private lemma measurableSet_stateEvent_generated
    {Ω' E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E]
    (Y : ℕ → Ω' → E) (x : E) {i n : ℕ} (hi : i ≤ n) :
    MeasurableSet[generatedFiltrationSpace Y n] {ω | Y i ω = x} := by
  -- Proof comment: this event is the singleton preimage of the coordinate map `Y i`.
  let hYi : @Measurable Ω' E (generatedFiltrationSpace Y n) _ (Y i) :=
    measurable_process_generated (Y := Y) hi
  change MeasurableSet[generatedFiltrationSpace Y n] ((Y i) ⁻¹' ({x} : Set E))
  exact hYi (MeasurableSet.singleton x)

/-- Helper for Theorem 17.40: bounded iterated-entrance events are measurable in the generated
history filtration at the same horizon. -/
private lemma iteratedEntranceTime_le_measurable_generated
    {Ω' E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E]
    (Y : ℕ → Ω' → E) (x : E) :
    ∀ (k : ℕ+) (N : ℕ),
      MeasurableSet[generatedFiltrationSpace Y N] {ω | (τ_[Y, x]^k) ω ≤ N} := by
  intro k N
  induction k using PNat.recOn generalizing N with
  | one =>
      -- Proof comment: the first entrance event is a bounded union of singleton coordinate hits.
      have hEq :
          {ω | (τ_[Y, x]^1) ω ≤ N} =
            ⋃ j ∈ ((Finset.Icc 1 N : Finset ℕ) : Set ℕ), {ω | Y j ω = x} := by
        ext ω
        simpa [iteratedEntranceTime_one, Set.mem_singleton_iff] using
          (MeasureTheory.hittingAfter_le_iff
            (u := Y) (s := ({x} : Set E)) (n := 1) (ω := ω) (i := N))
      rw [hEq]
      refine MeasurableSet.biUnion (Set.to_countable _) ?_
      intro j hj
      exact measurableSet_stateEvent_generated
        (Y := Y) x (hi := (Finset.mem_Icc.mp hj).2)
  | succ k ih =>
      let slice : ℕ → Set Ω' := fun j =>
        {ω | (τ_[Y, x]^k) ω < j} ∩ {ω | Y j ω = x}
      -- Proof comment: the successor entrance happens by time `N` iff some hit by time `N`
      -- occurs strictly after the previous entrance time.
      have hEq :
          {ω | (τ_[Y, x]^(k + 1)) ω ≤ N} =
            ⋃ j ∈ ((Finset.Icc 1 N : Finset ℕ) : Set ℕ), slice j := by
        ext ω
        constructor
        · intro hω
          rcases (iteratedEntranceTime_succ_le_iff_existsHitAfter Y x ω k N).1 hω with
            ⟨j, hτj, hjN, hjx⟩
          have hj_pos : 0 < j := by
            cases j with
            | zero =>
                simp at hτj
            | succ j => exact Nat.succ_pos j
          exact Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨Finset.mem_Icc.mpr ⟨hj_pos, hjN⟩,
            ⟨hτj, hjx⟩⟩⟩
        · intro hω
          rcases Set.mem_iUnion.1 hω with ⟨j, hω⟩
          rcases Set.mem_iUnion.1 hω with ⟨hj, hslice⟩
          exact (iteratedEntranceTime_succ_le_iff_existsHitAfter Y x ω k N).2
            ⟨j, hslice.1, (Finset.mem_Icc.mp hj).2, hslice.2⟩
      rw [hEq]
      refine MeasurableSet.biUnion (Set.to_countable _) ?_
      intro j hj
      have hj_le : j ≤ N := (Finset.mem_Icc.mp hj).2
      have hlt_N :
          MeasurableSet[generatedFiltrationSpace Y N] {ω | (τ_[Y, x]^k) ω < j} := by
        cases j with
        | zero =>
            have hj_false : ¬ 0 ∈ (Finset.Icc 1 N : Finset ℕ) := by
              simp
            exact False.elim (hj_false hj)
        | succ j =>
            have hle_j :
                MeasurableSet[generatedFiltrationSpace Y j]
                  {ω | (τ_[Y, x]^k) ω ≤ j} :=
              ih j
            have hle_N :
                MeasurableSet[generatedFiltrationSpace Y N]
                  {ω | (τ_[Y, x]^k) ω ≤ j} := by
              have hmono := generatedFiltrationSpace_mono
                (Y := Y) (Nat.le_trans (Nat.le_succ j) hj_le)
              exact hmono (s := {ω | (τ_[Y, x]^k) ω ≤ j}) hle_j
            simpa [ENat.lt_coe_add_one_iff] using hle_N
      exact hlt_N.inter (measurableSet_stateEvent_generated (Y := Y) x (hi := hj_le))

/-- Helper for Theorem 17.40: finite iterated-entrance events are measurable. -/
lemma iteratedEntranceTimeFiniteEvent_measurable
    {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E]
    {κ : ℕ → Kernel E E} {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    [IsMarkovProcessRealization κ P X] (x : E) (k : ℕ+) :
    MeasurableSet {ω | (τ_[X, x]^k) ω < ⊤} := by
  let hReal : IsMarkovProcessRealization κ P X := inferInstance
  have hEq :
      {ω | (τ_[X, x]^k) ω < ⊤} = ⋃ N : ℕ, {ω | (τ_[X, x]^k) ω ≤ N} := by
    ext ω
    constructor
    · intro hω
      let N : ℕ := ENat.toNat ((τ_[X, x]^k) ω)
      have hne : (τ_[X, x]^k) ω ≠ ⊤ := ne_of_lt hω
      refine Set.mem_iUnion.2 ⟨N, ?_⟩
      simp [N, ENat.coe_toNat hne]
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨N, hN⟩
      have hτ_le : (τ_[X, x]^k) ω ≤ N := by
        simpa using hN
      exact lt_of_le_of_lt hτ_le (by simp)
  rw [hEq]
  refine MeasurableSet.iUnion fun N ↦ ?_
  have hbounded :
      MeasurableSet[generatedFiltrationSpace X N] {ω | (τ_[X, x]^k) ω ≤ N} :=
    iteratedEntranceTime_le_measurable_generated (Y := X) x k N
  exact (generatedFiltrationSpace_le_ambient (X := X) hReal.measurable_process N) _ hbounded

/-- Helper for Theorem 17.40: the singleton-mass step matrix extracted from the convolution kernel
`dirac_convolution_kernel (ν : Measure ℤ)`. -/
def convolutionStepMatrix (ν : ProbabilityMeasure ℤ) : ℤ → ℤ → ℝ≥0∞ :=
  fun x y ↦ dirac_convolution_kernel (ν : Measure ℤ) x {y}

/-- Helper for Theorem 17.40: the discrete matrix kernel of `convolutionStepMatrix ν` is exactly
the convolution kernel generated by `ν`. -/
lemma convolutionStepMatrixKernel_eq (ν : ProbabilityMeasure ℤ) :
    discreteMatrixKernel (convolutionStepMatrix ν) =
      dirac_convolution_kernel (ν : Measure ℤ) := by
  ext x s hs
  have hrow :
      discreteMatrixKernel (convolutionStepMatrix ν) x =
        dirac_convolution_kernel (ν : Measure ℤ) x := by
    refine Measure.ext_of_singleton ?_
    intro y
    -- Proof comment: on the discrete state space `ℤ`, equality of row measures is determined by
    -- singleton masses.
    rw [discreteMatrixKernel_apply, Measure.sum_apply _ (measurableSet_singleton y)]
    rw [tsum_eq_single y]
    · simp [convolutionStepMatrix]
    · intro z hz
      simp [convolutionStepMatrix, Measure.smul_apply, Measure.dirac_apply', hz]
  -- Proof comment: evaluate the row equality on the target measurable set.
  exact congrArg (fun μ ↦ μ s) hrow

/-- Helper for Theorem 17.40: the singleton-mass step matrix associated with `ν` is stochastic. -/
lemma convolutionStepMatrix_isStochastic (ν : ProbabilityMeasure ℤ) :
    IsStochasticMatrix (convolutionStepMatrix ν) := by
  intro x
  -- Proof comment: the row sum is the total mass of the corresponding convolution-kernel row.
  calc
    ∑' y : ℤ, convolutionStepMatrix ν x y =
        discreteMatrixKernel (convolutionStepMatrix ν) x Set.univ := by
          exact (discreteMatrixKernel_univ (K := convolutionStepMatrix ν) x).symm
    _ = dirac_convolution_kernel (ν : Measure ℤ) x Set.univ := by
          rw [convolutionStepMatrixKernel_eq]
    _ = 1 := by
          rw [dirac_convolution_kernel_apply, Measure.dirac_conv]
          rw [Measure.map_apply (by fun_prop) MeasurableSet.univ]
          simp

/-- Helper for Theorem 17.40: the singleton-mass step matrix associated with `ν` is translation
invariant. -/
lemma convolutionStepMatrix_isTranslationInvariant (ν : ProbabilityMeasure ℤ) :
    IsTranslationInvariantStepMatrix (convolutionStepMatrix ν) := by
  intro x y
  -- Proof comment: both singleton masses are the value of `ν` at the common increment `y - x`.
  change dirac_convolution_kernel (ν : Measure ℤ) x ({y} : Set ℤ) =
    dirac_convolution_kernel (ν : Measure ℤ) 0 ({y - x} : Set ℤ)
  rw [dirac_convolution_kernel_apply, Measure.dirac_conv]
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton y)]
  have hpreimage :
      (fun z : ℤ ↦ x + z) ⁻¹' ({y} : Set ℤ) = {y - x} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hz
      exact eq_sub_iff_add_eq.mpr (by simpa [add_comm] using hz)
    · intro hz
      exact by simpa [add_comm] using (eq_sub_iff_add_eq.mp hz)
  rw [hpreimage]
  rw [dirac_convolution_kernel_apply, Measure.dirac_conv]
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton (y - x))]
  simp

/-- Helper for Theorem 17.40: the origin row of `convolutionStepMatrix ν` is the step law `ν`
itself. -/
lemma convolutionStepMatrix_originRow_eq (ν : ProbabilityMeasure ℤ) :
    discreteMatrixKernel (convolutionStepMatrix ν) 0 = (ν : Measure ℤ) := by
  -- Proof comment: at the origin, the convolution kernel reduces to the untranslated step law.
  calc
    discreteMatrixKernel (convolutionStepMatrix ν) 0 =
        dirac_convolution_kernel (ν : Measure ℤ) 0 := by
          simpa using congrArg (fun κ : Kernel ℤ ℤ ↦ κ 0) (convolutionStepMatrixKernel_eq ν)
    _ = (ν : Measure ℤ) := by
      rw [dirac_convolution_kernel_apply, Measure.dirac_conv]
      refine Measure.ext_of_singleton fun y ↦ ?_
      rw [Measure.map_apply (by fun_prop) (measurableSet_singleton y)]
      simp

section DiagonalGreen

variable {P : ℤ → ProbabilityMeasure Ω} {X : ℕ → Ω → ℤ}

/-- Helper for Theorem 17.40: Theorem 17.29 specialized to `(x, x)` turns the iterated-entrance
probability series into the shifted power series of `F(x, x)`. -/
private lemma iteratedEntranceProbabilitySeries_eq_selfPowerSeries
    {κ : ℕ → Kernel ℤ ℤ} [IsMarkovProcessRealization κ P X] (x : ℤ) :
    (∑' k : ℕ+, ENNReal.ofReal ((P x : Measure Ω).real {ω | (τ_[X, x]^k) ω < ⊤})) =
      ∑' n : ℕ, ENNReal.ofReal (((F[P, X]) x x) ^ (n + 1)) := by
  -- Proof comment: replace each iterated-entrance probability by the Theorem 17.29 formula, then
  -- reindex the `ℕ+`-series along `Equiv.pnatEquivNat`.
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

/-- Helper for Theorem 17.40: the positive-time diagonal Green function is the shifted geometric
series of successive return probabilities. -/
private lemma greenFunctionFromOneSelf_eq_tsum_selfPowers
    {κ : ℕ → Kernel ℤ ℤ} [IsMarkovProcessRealization κ P X] (x : ℤ) :
    (G[P, X; 1]) x x =
      ∑' n : ℕ, ENNReal.ofReal (((F[P, X]) x x) ^ (n + 1)) := by
  -- Proof comment: rewrite the positive-time Green function as the iterated-entrance series, then
  -- reindex that series along `ℕ+ ≃ ℕ`.
  exact
    (greenFunctionFromOneSelf_eq_tsum_iteratedEntranceProbabilities
      (P := P) (X := X) (κ := κ) x).trans
      (iteratedEntranceProbabilitySeries_eq_selfPowerSeries (P := P) (X := X) (κ := κ) x)

/-- Helper for Theorem 17.40: the full diagonal Green function splits into the deterministic
time-`0` visit and the strictly positive-time diagonal Green tail. -/
private lemma greenFunctionSelf_eq_one_add_greenFunctionFromOneSelf
    {κ : ℕ → Kernel ℤ ℤ} [IsMarkovProcessRealization κ P X] (x : ℤ) :
    (G[P, X]) x x = 1 + (G[P, X; 1]) x x := by
  let hReal : IsMarkovProcessRealization κ P X := inferInstance
  let hX : IsStochasticProcess X := fun n ↦ hReal.measurable_process n
  have hzero :
      (P x : Measure Ω) {ω | X 0 ω = x} = 1 := by
    have hpreimage : {ω | X 0 ω = x} = X 0 ⁻¹' ({x} : Set ℤ) := by
      ext ω
      simp
    -- Proof comment: under `P x`, the chain starts at `x` with probability one at time `0`.
    calc
      (P x : Measure Ω) {ω | X 0 ω = x}
        = ((P x : Measure Ω).map (X 0)) ({x} : Set ℤ) := by
            simpa [hpreimage] using
              (Measure.map_apply
                (μ := (P x : Measure Ω))
                (f := X 0)
                (s := ({x} : Set ℤ))
                (hReal.measurable_process 0)
                (MeasurableSet.singleton x)).symm
      _ = Measure.dirac x ({x} : Set ℤ) := by
            simpa using
              congrArg (fun μ : Measure ℤ ↦ μ ({x} : Set ℤ)) (hReal.initial_eq x)
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

/-- Helper for Theorem 17.40: a shifted geometric series of `ℝ≥0∞`-casts is finite whenever the
ratio lies in `[0, 1)`. -/
private lemma ennrealOfRealTsumGeometricSucc_lt_top {q : ℝ}
    (hq_nonneg : 0 ≤ q) (hq_lt_one : q < 1) :
    ∑' n : ℕ, ENNReal.ofReal (q ^ (n + 1)) < ⊤ := by
  have hsum : Summable (fun n : ℕ ↦ q ^ (n + 1)) :=
    (_root_.summable_nat_add_iff 1).2 (summable_geometric_of_lt_one hq_nonneg hq_lt_one)
  -- Proof comment: summability in `ℝ` keeps the pointwise `ℝ≥0∞` casts finite because all terms
  -- are nonnegative.
  calc
    ∑' n : ℕ, ENNReal.ofReal (q ^ (n + 1))
      = ENNReal.ofReal (∑' n : ℕ, q ^ (n + 1)) := by
          rw [ENNReal.ofReal_tsum_of_nonneg]
          · intro n
            exact pow_nonneg hq_nonneg _
          · exact hsum
    _ < ⊤ := by
          simp

/-- Helper for Theorem 17.40: an infinite diagonal Green value forces recurrence. -/
lemma isRecurrentState_of_greenFunctionSelf_eq_top
    {κ : ℕ → Kernel ℤ ℤ} [IsMarkovProcessRealization κ P X]
    (x : ℤ) (hx : (G[P, X]) x x = ⊤) :
    IsRecurrentState P X x := by
  have hq_nonneg : 0 ≤ (F[P, X]) x x := measureReal_nonneg
  have hq_le_one : (F[P, X]) x x ≤ 1 := by
    rw [everHitsProbability_def]
    exact measureReal_le_one
  -- Proof comment: normalize the positive-time diagonal tail to the shifted power series in
  -- `F(x, x)` and then close by a geometric contradiction.
  by_contra htrans
  have hneq : (F[P, X]) x x ≠ 1 := by
    rw [IsRecurrentState] at htrans
    simpa [eq_comm] using htrans
  have hq_lt_one : (F[P, X]) x x < 1 :=
    lt_of_le_of_ne hq_le_one hneq
  have htail_lt_top :
      ∑' n : ℕ, ENNReal.ofReal (((F[P, X]) x x) ^ (n + 1)) < ⊤ :=
    ennrealOfRealTsumGeometricSucc_lt_top hq_nonneg hq_lt_one
  have hone_lt_top : (1 : ℝ≥0∞) < ⊤ := by
    simp
  have hgreen_lt_top : (G[P, X]) x x < ⊤ := by
    calc
      (G[P, X]) x x = 1 + (G[P, X; 1]) x x := by
        rw [greenFunctionSelf_eq_one_add_greenFunctionFromOneSelf (P := P) (X := X) (κ := κ)]
      _ = 1 + ∑' n : ℕ, ENNReal.ofReal (((F[P, X]) x x) ^ (n + 1)) := by
          rw [greenFunctionFromOneSelf_eq_tsum_selfPowers (P := P) (X := X) (κ := κ)]
      _ < ⊤ := by
          exact ENNReal.add_lt_top.2 ⟨hone_lt_top, htail_lt_top⟩
  exact (ne_of_lt hgreen_lt_top) hx

/-- Helper for Theorem 17.40: recurrence forces the diagonal Green value to be infinite. -/
lemma greenFunctionSelf_eq_top_of_isRecurrentState
    {κ : ℕ → Kernel ℤ ℤ} [IsMarkovProcessRealization κ P X]
    (x : ℤ) (hx : IsRecurrentState P X x) :
    (G[P, X]) x x = ⊤ := by
  have htail :
      (G[P, X; 1]) x x = ∑' n : ℕ, (1 : ℝ≥0∞) := by
    -- Proof comment: recurrence makes every return-probability power equal to `1`, so the
    -- positive-time Green tail is the divergent series of ones.
    calc
      (G[P, X; 1]) x x = ∑' n : ℕ, ENNReal.ofReal (((F[P, X]) x x) ^ (n + 1)) := by
        rw [greenFunctionFromOneSelf_eq_tsum_selfPowers (P := P) (X := X) (κ := κ)]
      _ = ∑' n : ℕ, ENNReal.ofReal (1 ^ (n + 1 : ℕ)) := by
            refine tsum_congr fun n ↦ ?_
            rw [IsRecurrentState] at hx
            simp [hx]
      _ = ∑' n : ℕ, (1 : ℝ≥0∞) := by
            refine tsum_congr fun n ↦ ?_
            simp
  -- Proof comment: add the deterministic time-`0` visit to the already divergent positive-time
  -- tail.
  calc
    (G[P, X]) x x = 1 + (G[P, X; 1]) x x := by
      rw [greenFunctionSelf_eq_one_add_greenFunctionFromOneSelf (P := P) (X := X) (κ := κ)]
    _ = 1 + ∑' n : ℕ, (1 : ℝ≥0∞) := by
          rw [htail]
    _ = ⊤ := by
          simp

/-- Helper for Theorem 17.40: the diagonal Green value at the origin is the common origin-mass
series of the convolution kernel. -/
lemma integerWalk_greenFunction_zero_zero_eq_tsum_originMass
    (ν : ProbabilityMeasure ℤ)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ dirac_convolution_kernel (ν : Measure ℤ) ^ n) P X] :
    (G[P, X]) (0 : ℤ) 0 =
      ∑' n : ℕ, ((dirac_convolution_kernel (ν : Measure ℤ) ^ n) (0 : ℤ)) ({0} : Set ℤ) := by
  let hReal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ dirac_convolution_kernel (ν : Measure ℤ) ^ n) P X := inferInstance
  let hX : IsStochasticProcess X := fun n ↦ hReal.measurable_process n
  -- Proof comment: rewrite each time-`n` visit probability at the origin through the realization
  -- identity for the convolution kernel.
  rw [greenFunction_eq_tsum_stateProbabilities P X hX 0 0]
  refine tsum_congr fun n ↦ ?_
  have htransition :=
    congrArg (fun ρ : Measure ℤ ↦ ρ ({0} : Set ℤ)) (hReal.transition_eq (0 : ℤ) n)
  simpa [Measure.map_apply (hReal.measurable_process n) (measurableSet_singleton (0 : ℤ))] using
    htransition

end DiagonalGreen

/-- Helper for Theorem 17.40: recurrence at a state should force all iterated entrance times to be
finite almost surely. -/
lemma recurrentState_ae_allIteratedEntranceTimes_finite
    {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E]
    {κ : ℕ → Kernel E E} {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    [IsMarkovProcessRealization κ P X] (x : E) (hx : IsRecurrentState P X x) :
    ∀ᵐ ω ∂(P x : Measure Ω), ∀ k : ℕ+, (τ_[X, x]^k) ω < ⊤ := by
  have hrec : (F[P, X]) x x = 1 := by
    simpa [IsRecurrentState] using hx
  -- Route correction: use the bounded-event measurability recursion from Theorem 17.29, then turn
  -- each probability-one finite-entrance event into an `ae` statement and package the family.
  refine ae_all_iff.2 fun k ↦ ?_
  have hfinite_meas :
      MeasurableSet {ω | (τ_[X, x]^k) ω < ⊤} :=
    iteratedEntranceTimeFiniteEvent_measurable (κ := κ) (P := P) (X := X) x k
  change {ω | (τ_[X, x]^k) ω < ⊤} ∈ ae (P x : Measure Ω)
  refine (mem_ae_iff_prob_eq_one hfinite_meas).2 ?_
  rw [← ENNReal.toReal_eq_one_iff]
  calc
    (P x : Measure Ω).real {ω | (τ_[X, x]^k) ω < ⊤}
      = (F[P, X]) x x * (F[P, X]) x x ^ k.natPred := by
          simpa using
            (iteratedEntranceTime_finite_probability_eq_everHitsProbability_mul_selfPow
              (κ := κ) (P := P) (X := X) x x k)
    _ = 1 := by
          simp [hrec]

/-- Helper for Theorem 17.40: finitely many iterated origin returns are incompatible with a
nonzero asymptotic velocity. -/
lemma allIteratedOriginReturns_finite_not_tendsto_nonzero
    {Ω' : Type*} (Y : ℕ → Ω' → ℤ) (ω : Ω') (m : ℝ) (hm : m ≠ 0)
    (hfinite : ∀ k : ℕ+, (τ_[Y, 0]^k) ω < ⊤) :
    ¬ Tendsto (fun n : ℕ ↦ (Y n ω : ℝ) / n) atTop (nhds m) := by
  intro htend
  have hEventuallyNonzero :
      ∀ᶠ n : ℕ in atTop, (Y n ω : ℝ) / n ≠ 0 := by
    have hneigh : {r : ℝ | r ≠ 0} ∈ nhds m :=
      isOpen_ne.mem_nhds hm
    exact htend hneigh
  rcases Filter.mem_atTop_sets.1 hEventuallyNonzero with ⟨N, hN⟩
  let k : ℕ+ := ⟨N + 1, Nat.succ_pos N⟩
  have hkfinite : (τ_[Y, 0]^(k + 1)) ω < ⊤ := hfinite (k + 1)
  have hle :
      (τ_[Y, 0]^(k + 1)) ω ≤ ENat.toNat ((τ_[Y, 0]^(k + 1)) ω) := by
    rw [← ENat.coe_toNat (ne_of_lt hkfinite)]
    simp
  rcases (iteratedEntranceTime_succ_le_iff_existsHitAfter
      Y 0 ω k (ENat.toNat ((τ_[Y, 0]^(k + 1)) ω))).1 hle with
    ⟨n, hnτ, -, hnzero⟩
  have hk_le_prev : ((k : ℕ) : ℕ∞) ≤ (τ_[Y, 0]^k) ω :=
    iteratedEntranceTime_index_le Y 0 ω k
  have hk_lt_n : ((k : ℕ) : ℕ∞) < n := lt_of_le_of_lt hk_le_prev hnτ
  have hk_lt_n_nat : (k : ℕ) < n := by
    exact_mod_cast hk_lt_n
  have hN_lt_n : N < n := by
    exact lt_trans (Nat.lt_succ_self N) (by simpa [k] using hk_lt_n_nat)
  have hq_nonzero : (Y n ω : ℝ) / n ≠ 0 := hN n hN_lt_n.le
  have hq_zero : (Y n ω : ℝ) / n = 0 := by
    simp [hnzero]
  exact hq_nonzero hq_zero

/-- Helper for Theorem 17.40: the real-valued partial sums of the increment family agree with the
cast integer random walk. -/
private lemma randomWalkProcess_real_apply
    {Ω' : Type*} [MeasurableSpace Ω'] (Z : ℕ → Ω' → ℤ) (n : ℕ) (ω : Ω') :
    (∑ i ∈ Finset.range n, (Z i ω : ℝ)) = (randomWalkProcess Z n ω : ℝ) := by
  -- Proof comment: `randomWalkProcess` is exactly this finite integer sum, viewed after casting
  -- to `ℝ`.
  rw [randomWalkProcess_apply]
  exact_mod_cast rfl

/-- Helper for Theorem 17.40: the strong law for an i.i.d. increment family rewrites directly
into the random-walk notation. -/
private lemma randomWalkProcess_ae_tendsto_stepMean
    {Ω' : Type*} [MeasurableSpace Ω'] (ν : ProbabilityMeasure ℤ)
    (Q : ProbabilityMeasure Ω') (Z : ℕ → Ω' → ℤ)
    (hfirstMoment : Integrable (fun z : ℤ ↦ (z : ℝ)) (ν : Measure ℤ))
    (hZ_indep : iIndepFun Z (Q : Measure Ω'))
    (hZ_law : ∀ n : ℕ, HasLaw (Z n) (ν : Measure ℤ) (Q : Measure Ω')) :
    ∀ᵐ ω ∂(Q : Measure Ω'),
      Tendsto (fun n : ℕ ↦ (randomWalkProcess Z n ω : ℝ) / n) atTop
        (nhds (∫ z, (z : ℝ) ∂(ν : Measure ℤ))) := by
  have hstep_integrable : Integrable (fun ω ↦ (Z 0 ω : ℝ)) (Q : Measure Ω') := by
    -- Proof comment: the first-moment assumption on `ν` transports across the law of `Z 0`.
    have hcast_integrable :
        Integrable (fun z : ℤ ↦ (z : ℝ)) (Measure.map (Z 0) (Q : Measure Ω')) := by
      simpa [(hZ_law 0).map_eq] using hfirstMoment
    simpa [Function.comp] using hcast_integrable.comp_aemeasurable (hZ_law 0).aemeasurable
  have hZ_pairwise :
      Pairwise fun i j ↦ (fun ω ↦ (Z i ω : ℝ)) ⟂ᵢ[(Q : Measure Ω')]
        (fun ω ↦ (Z j ω : ℝ)) := by
    -- Proof comment: pairwise independence follows by composing the integer-valued family with
    -- the measurable cast `ℤ → ℝ`.
    intro i j hij
    exact (hZ_indep.comp₀ (fun _ ↦ ((↑) : ℤ → ℝ))
      (fun n ↦ (hZ_law n).aemeasurable)
      (fun _ ↦ (measurable_of_countable ((↑) : ℤ → ℝ)).aemeasurable)).indepFun hij
  have hZ_ident :
      ∀ n : ℕ, IdentDistrib (fun ω ↦ (Z n ω : ℝ)) (fun ω ↦ (Z 0 ω : ℝ))
        (Q : Measure Ω') (Q : Measure Ω') := by
    -- Proof comment: every increment has the same law `ν`, so their real-valued casts are
    -- identically distributed.
    intro n
    have hcast_meas : Measurable ((↑) : ℤ → ℝ) := by
      exact measurable_of_countable ((↑) : ℤ → ℝ)
    have hcast_n :
        HasLaw (fun ω ↦ (Z n ω : ℝ))
          (Measure.map ((↑) : ℤ → ℝ) (ν : Measure ℤ)) (Q : Measure Ω') := by
      refine ⟨hcast_meas.aemeasurable.comp_aemeasurable (hZ_law n).aemeasurable, ?_⟩
      calc
        Measure.map (fun ω ↦ (Z n ω : ℝ)) (Q : Measure Ω')
          = Measure.map ((↑) : ℤ → ℝ) (Measure.map (Z n) (Q : Measure Ω')) := by
              symm
              exact AEMeasurable.map_map_of_aemeasurable hcast_meas.aemeasurable
                (hZ_law n).aemeasurable
        _ = Measure.map ((↑) : ℤ → ℝ) (ν : Measure ℤ) := by
              rw [(hZ_law n).map_eq]
    have hcast_0 :
        HasLaw (fun ω ↦ (Z 0 ω : ℝ))
          (Measure.map ((↑) : ℤ → ℝ) (ν : Measure ℤ)) (Q : Measure Ω') := by
      refine ⟨hcast_meas.aemeasurable.comp_aemeasurable (hZ_law 0).aemeasurable, ?_⟩
      calc
        Measure.map (fun ω ↦ (Z 0 ω : ℝ)) (Q : Measure Ω')
          = Measure.map ((↑) : ℤ → ℝ) (Measure.map (Z 0) (Q : Measure Ω')) := by
              symm
              exact AEMeasurable.map_map_of_aemeasurable hcast_meas.aemeasurable
                (hZ_law 0).aemeasurable
        _ = Measure.map ((↑) : ℤ → ℝ) (ν : Measure ℤ) := by
              rw [(hZ_law 0).map_eq]
    exact hcast_n.identDistrib hcast_0
  have hmean_eq :
      (Q : Measure Ω')[fun ω ↦ (Z 0 ω : ℝ)] = ∫ z, (z : ℝ) ∂(ν : Measure ℤ) := by
    -- Proof comment: the expectation of the first increment is the mean of the common step law.
    simpa using
      (hZ_law 0).integral_comp ((measurable_of_countable ((↑) : ℤ → ℝ)).aestronglyMeasurable)
  have hstrongLaw :
      ∀ᵐ ω ∂(Q : Measure Ω'),
        Tendsto (fun n : ℕ ↦ (∑ i ∈ Finset.range n, (Z i ω : ℝ)) / n) atTop
          (nhds ((Q : Measure Ω')[fun ω ↦ (Z 0 ω : ℝ)])) := by
    -- Proof comment: this is the real-valued strong law for pairwise independent, identically
    -- distributed increments with finite first moment.
    exact ProbabilityTheory.strong_law_ae_real (fun n ω ↦ (Z n ω : ℝ))
      hstep_integrable hZ_pairwise hZ_ident
  -- Proof comment: rewrite the partial sums from the strong law into `randomWalkProcess`.
  filter_upwards [hstrongLaw] with ω hω
  simpa [hmean_eq, randomWalkProcess_real_apply] using hω

/-- Helper for Theorem 17.40: a one-dimensional integer random walk with nonzero drift is not
recurrent. -/
lemma integerRandomWalk_not_recurrent_of_integrable_mean_ne_zero
    (ν : ProbabilityMeasure ℤ)
    (hfirstMoment : Integrable (fun z : ℤ ↦ (z : ℝ)) (ν : Measure ℤ))
    (hmean_ne_zero : ∫ z, (z : ℝ) ∂(ν : Measure ℤ) ≠ 0)
    (P : ℤ → ProbabilityMeasure Ω) (X : ℕ → Ω → ℤ)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ dirac_convolution_kernel (ν : Measure ℤ) ^ n) P X] :
    ¬ IsRecurrentMarkovChain P X := by
  intro hrec
  have hseries_top :
      ∑' n : ℕ, ((dirac_convolution_kernel (ν : Measure ℤ) ^ n) (0 : ℤ)) ({0} : Set ℤ) = ⊤ := by
    -- Proof comment: recurrence of the origin forces the diagonal Green value to diverge.
    calc
      ∑' n : ℕ, ((dirac_convolution_kernel (ν : Measure ℤ) ^ n) (0 : ℤ)) ({0} : Set ℤ)
        = (G[P, X]) (0 : ℤ) 0 := by
            symm
            exact integerWalk_greenFunction_zero_zero_eq_tsum_originMass (ν := ν) (P := P) (X := X)
      _ = ⊤ := by
            exact greenFunctionSelf_eq_top_of_isRecurrentState
              (κ := fun n : ℕ ↦ dirac_convolution_kernel (ν : Measure ℤ) ^ n)
              (P := P) (X := X) 0 (hrec 0)
  let p : ℤ → ℤ → ℝ≥0∞ := convolutionStepMatrix ν
  have hp_stochastic : IsStochasticMatrix p :=
    convolutionStepMatrix_isStochastic ν
  have hp_translation : IsTranslationInvariantStepMatrix p :=
    convolutionStepMatrix_isTranslationInvariant ν
  have horiginRow : discreteMatrixKernel p 0 = (ν : Measure ℤ) :=
    convolutionStepMatrix_originRow_eq ν
  let _ : IsMarkovKernel (discreteMatrixKernel p) :=
    discreteMatrixKernel_isMarkovKernel p hp_stochastic
  obtain ⟨Ω', hΩ', Q, Zlift, hZ_meas, hZ_law, hZ_indep, hQ_prob⟩ :
      ∃ Ω' : Type, ∃ _ : MeasurableSpace Ω', ∃ Q : Measure Ω', ∃ Zlift : ULift ℕ → Ω' → ℤ,
        (∀ i : ULift ℕ, Measurable (Zlift i)) ∧
          (∀ i : ULift ℕ, HasLaw (Zlift i) (ν : Measure ℤ) Q) ∧
          iIndepFun Zlift Q ∧ IsProbabilityMeasure Q := by
    simpa using ProbabilityTheory.exists_iid (ULift ℕ) (ν : Measure ℤ)
  let Qprob : ProbabilityMeasure Ω' := ⟨Q, hQ_prob⟩
  let Z : ℕ → Ω' → ℤ := fun n ω ↦ Zlift ⟨n⟩ ω
  have hZ_meas' : ∀ n : ℕ, Measurable (Z n) := by
    intro n
    simpa [Z] using hZ_meas ⟨n⟩
  have hZ_law' : ∀ n : ℕ, HasLaw (Z n) (discreteMatrixKernel p 0) (Qprob : Measure Ω') := by
    intro n
    simpa [Z, Qprob, horiginRow] using hZ_law ⟨n⟩
  have hZ_indep' : iIndepFun Z (Qprob : Measure Ω') := by
    simpa [Z, Qprob] using
      hZ_indep.precomp (g := fun n : ℕ ↦ (⟨n⟩ : ULift ℕ)) (by
        intro i j hij
        simpa using congrArg ULift.down hij)
  have hZ_law_nu : ∀ n : ℕ, HasLaw (Z n) (ν : Measure ℤ) (Qprob : Measure Ω') := by
    intro n
    simpa [Z, Qprob] using hZ_law ⟨n⟩
  let hdisc :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel p ^ n)
        (productStartRandomWalkMeasure Qprob)
        (productStartRandomWalk Z) :=
    productStartRandomWalk_isMarkovProcessRealization
      p hp_stochastic hp_translation Qprob Z hZ_meas' hZ_indep' hZ_law'
  let hconv :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ dirac_convolution_kernel (ν : Measure ℤ) ^ n)
        (productStartRandomWalkMeasure Qprob)
        (productStartRandomWalk Z) := by
    simpa [p, convolutionStepMatrixKernel_eq ν] using hdisc
  letI :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ dirac_convolution_kernel (ν : Measure ℤ) ^ n)
        (productStartRandomWalkMeasure Qprob)
        (productStartRandomWalk Z) := hconv
  have hgreen_top_aux :
      (G[productStartRandomWalkMeasure Qprob, productStartRandomWalk Z]) (0 : ℤ) 0 = ⊤ := by
    -- Proof comment: both realizations have the same origin Green series, so recurrence transfers.
    calc
      (G[productStartRandomWalkMeasure Qprob, productStartRandomWalk Z]) (0 : ℤ) 0
        = ∑' n : ℕ, ((dirac_convolution_kernel (ν : Measure ℤ) ^ n) (0 : ℤ)) ({0} : Set ℤ) := by
            exact integerWalk_greenFunction_zero_zero_eq_tsum_originMass
              (ν := ν) (P := productStartRandomWalkMeasure Qprob) (X := productStartRandomWalk Z)
      _ = ⊤ := hseries_top
  have hrec0_aux :
      IsRecurrentState (productStartRandomWalkMeasure Qprob) (productStartRandomWalk Z) 0 :=
    isRecurrentState_of_greenFunctionSelf_eq_top
      (κ := fun n : ℕ ↦ dirac_convolution_kernel (ν : Measure ℤ) ^ n)
      (P := productStartRandomWalkMeasure Qprob)
      (X := productStartRandomWalk Z)
      0 hgreen_top_aux
  have hreturns_ae :
      ∀ᵐ s ∂(productStartRandomWalkMeasure Qprob 0 : Measure (ℤ × Ω')),
        ∀ k : ℕ+, (τ_[productStartRandomWalk Z, 0]^k) s < ⊤ :=
    recurrentState_ae_allIteratedEntranceTimes_finite
      (κ := fun n : ℕ ↦ dirac_convolution_kernel (ν : Measure ℤ) ^ n)
      (P := productStartRandomWalkMeasure Qprob)
      (X := productStartRandomWalk Z)
      0 hrec0_aux
  have hlimit_ae_base :
      ∀ᵐ ω ∂(Qprob : Measure Ω'),
        Tendsto (fun n : ℕ ↦ (randomWalkProcess Z n ω : ℝ) / n) atTop
          (nhds (∫ z, (z : ℝ) ∂(ν : Measure ℤ))) :=
    randomWalkProcess_ae_tendsto_stepMean ν Qprob Z hfirstMoment hZ_indep' hZ_law_nu
  have hstart_measure :
      (productStartRandomWalkMeasure Qprob 0 : Measure (ℤ × Ω')) =
        (Qprob : Measure Ω').map (fun ω ↦ ((0 : ℤ), ω)) := by
    change ((Measure.dirac (0 : ℤ)).prod (Qprob : Measure Ω')) =
      (Qprob : Measure Ω').map (fun ω ↦ ((0 : ℤ), ω))
    rw [Measure.dirac_prod]
  have hlimit_ae :
      ∀ᵐ s ∂(productStartRandomWalkMeasure Qprob 0 : Measure (ℤ × Ω')),
        Tendsto (fun n : ℕ ↦ (productStartRandomWalk Z n s : ℝ) / n) atTop
          (nhds (∫ z, (z : ℝ) ∂(ν : Measure ℤ))) := by
    let hprodMk : MeasurableEmbedding (fun ω : Ω' ↦ ((0 : ℤ), ω)) :=
      MeasurableEmbedding.prodMk_left (x := (0 : ℤ)) (f := id) MeasurableEmbedding.id
    rw [hstart_measure]
    rw [hprodMk.ae_map_iff]
    filter_upwards [hlimit_ae_base] with ω hω
    have hpath :
        (fun n : ℕ ↦ (productStartRandomWalk Z n ((0 : ℤ), ω) : ℝ) / n) =
          fun n : ℕ ↦ (randomWalkProcess Z n ω : ℝ) / n := by
      funext n
      have hstep :
          productStartRandomWalk Z n ((0 : ℤ), ω) = 0 + randomWalkProcess Z n ω := by
        simpa using congrFun (productStartRandomWalk_comp_prodMk Z 0 n) ω
      rw [hstep]
      simp
    simpa [hpath] using hω
  have hFalseAE :
      ∀ᵐ s ∂(productStartRandomWalkMeasure Qprob 0 : Measure (ℤ × Ω')), False := by
    filter_upwards [hlimit_ae, hreturns_ae] with s hsLimit hsReturns
    exact
      (allIteratedOriginReturns_finite_not_tendsto_nonzero
        (Y := productStartRandomWalk Z) (ω := s)
        (m := ∫ z, (z : ℝ) ∂(ν : Measure ℤ))
        hmean_ne_zero hsReturns) hsLimit
  have huniv_zero :
      (productStartRandomWalkMeasure Qprob 0 : Measure (ℤ × Ω')) Set.univ = 0 := by
    have hFalseAE'' :
        (productStartRandomWalkMeasure Qprob 0 : Measure (ℤ × Ω')) Set.univ = 0 := by
      have hFalseAE' := hFalseAE
      simp [ae_iff] at hFalseAE'
    exact hFalseAE''
  have huniv_one :
      (productStartRandomWalkMeasure Qprob 0 : Measure (ℤ × Ω')) Set.univ = 1 := by
    simp [productStartRandomWalkMeasure]
  exact one_ne_zero (huniv_one.symm.trans huniv_zero)

/-- Helper for Theorem 17.40: composing a translation convolution kernel with a measure is just
measure convolution by the common step law. -/
private lemma diracConvolutionKernel_comp_measure_eq_conv
    (μ ν : Measure ℤ) [SFinite μ] [SFinite ν] :
    dirac_convolution_kernel ν ∘ₘ μ = μ ∗ ν := by
  have hconst :=
    congrArg
      (fun κ : Kernel ℤ ℤ ↦ κ (0 : ℤ))
      (dirac_convolution_kernel_comp_const_eq_const_conv (μ := μ) (ν := ν))
  simpa [Kernel.comp_apply] using hconst

/-- Helper for Theorem 17.40: after `n` steps, the row of a translation convolution kernel is the
translate of the origin-started `n`-step law. -/
private lemma diracConvolutionKernel_pow_apply_eq_diracConv_origin
    (μ : Measure ℤ) :
    ∀ n : ℕ, ∀ x : ℤ,
      ((dirac_convolution_kernel μ ^ n) x) =
        (Measure.dirac x) ∗ ((dirac_convolution_kernel μ ^ n) (0 : ℤ))
  | 0, x => by
      -- Proof comment: the zero-step law is exactly the starting Dirac mass.
      change Measure.dirac x = Measure.dirac x ∗ Measure.dirac (0 : ℤ)
      simp
  | n + 1, x => by
      let κ : Kernel ℤ ℤ := dirac_convolution_kernel μ
      have hpow : κ ^ (n + 1) = κ ∘ₖ (κ ^ n) := by
        simpa [pow_one, Nat.one_add] using (ProbabilityTheory.Kernel.pow_add κ 1 n)
      -- Proof comment: evolve the translated `n`-step law by one more convolution step and
      -- reassociate the resulting convolution product.
      calc
        (κ ^ (n + 1)) x = κ ∘ₘ ((κ ^ n) x) := by
          rw [hpow, Kernel.comp_apply]
        _ = ((κ ^ n) x) ∗ μ := by
          simpa [κ] using
            (diracConvolutionKernel_comp_measure_eq_conv
              (μ := (κ ^ n) x) (ν := μ))
        _ = (Measure.dirac x ∗ ((κ ^ n) (0 : ℤ))) ∗ μ := by
          rw [diracConvolutionKernel_pow_apply_eq_diracConv_origin μ n x]
        _ = Measure.dirac x ∗ (((κ ^ n) (0 : ℤ)) ∗ μ) := by
          rw [Measure.conv_assoc]
        _ = Measure.dirac x ∗ ((κ ^ (n + 1)) (0 : ℤ)) := by
          congr 1
          calc
            ((κ ^ n) (0 : ℤ)) ∗ μ = κ ∘ₘ ((κ ^ n) (0 : ℤ)) := by
              symm
              simpa [κ] using
                (diracConvolutionKernel_comp_measure_eq_conv
                  (μ := (κ ^ n) (0 : ℤ)) (ν := μ))
            _ = (κ ∘ₖ (κ ^ n)) (0 : ℤ) := by
              rw [Kernel.comp_apply]
            _ = (κ ^ (n + 1)) (0 : ℤ) := by
              rw [← hpow]

/-- Helper for Theorem 17.40: the diagonal singleton mass of the `n`-step convolution kernel is
the common origin mass. -/
private lemma diracConvolutionKernelPow_apply_self_eq_originMass
    (ν : ProbabilityMeasure ℤ) (n : ℕ) (x : ℤ) :
    ((dirac_convolution_kernel (ν : Measure ℤ) ^ n) x) ({x} : Set ℤ) =
      ((dirac_convolution_kernel (ν : Measure ℤ) ^ n) (0 : ℤ)) ({0} : Set ℤ) := by
  -- Proof comment: rewrite the `x`-row as the translate of the origin row and compute the
  -- singleton mass at the unchanged displacement `x - x = 0`.
  rw [diracConvolutionKernel_pow_apply_eq_diracConv_origin (ν : Measure ℤ) n x]
  rw [Measure.dirac_conv]
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton x)]
  have hpreimage :
      (fun z : ℤ ↦ x + z) ⁻¹' ({x} : Set ℤ) = ({0} : Set ℤ) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hz
      linarith
    · intro hz
      linarith
  rw [hpreimage]

/-- Helper for Theorem 17.40: once the origin diagonal Green value is infinite, translation
invariance of the convolution kernel makes every state recurrent. -/
private theorem integerRandomWalk_recurrentState_of_origin
    (ν : ProbabilityMeasure ℤ)
    (P : ℤ → ProbabilityMeasure Ω) (X : ℕ → Ω → ℤ)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ dirac_convolution_kernel (ν : Measure ℤ) ^ n) P X]
    (hgreen0 : (G[P, X]) (0 : ℤ) 0 = ⊤) :
    ∀ x : ℤ, IsRecurrentState P X x := by
  intro x
  let hReal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ dirac_convolution_kernel (ν : Measure ℤ) ^ n)
        P X := inferInstance
  let hX : IsStochasticProcess X := fun n ↦ hReal.measurable_process n
  have hgreenx : (G[P, X]) x x = ⊤ := by
    -- Route correction: compare the diagonal Green series through the `n`-step kernel rows,
    -- rather than transporting realized marginals directly.
    calc
      (G[P, X]) x x =
          ∑' n : ℕ, ((dirac_convolution_kernel (ν : Measure ℤ) ^ n) x) ({x} : Set ℤ) := by
            rw [greenFunction_eq_tsum_stateProbabilities P X hX x x]
            refine tsum_congr fun n ↦ ?_
            have htransition :=
              congrArg
                (fun μ : Measure ℤ ↦ μ ({x} : Set ℤ))
                (hReal.transition_eq x n)
            simpa [Measure.map_apply (hReal.measurable_process n)
              (measurableSet_singleton x)] using htransition
      _ = ∑' n : ℕ, ((dirac_convolution_kernel (ν : Measure ℤ) ^ n) (0 : ℤ)) ({0} : Set ℤ) := by
            refine tsum_congr fun n ↦ ?_
            simpa using diracConvolutionKernelPow_apply_self_eq_originMass (ν := ν) n x
      _ = (G[P, X]) (0 : ℤ) 0 := by
            symm
            exact integerWalk_greenFunction_zero_zero_eq_tsum_originMass (ν := ν) (P := P) (X := X)
      _ = ⊤ := hgreen0
  exact
    isRecurrentState_of_greenFunctionSelf_eq_top
      (κ := fun n : ℕ ↦ dirac_convolution_kernel (ν : Measure ℤ) ^ n)
      (P := P) (X := X) x hgreenx

/-- Helper for Theorem 17.40: if a time-`n` history event already forces `X n = z`, then
intersecting it with the time-`n + m` singleton event factors through the `m`-step transition
mass from `z`. -/
private lemma measure_inter_prefix_stepEvent_eq_mulLocal
    {κ : ℕ → Kernel ℤ ℤ} {P : ℤ → ProbabilityMeasure Ω}
    [IsMarkovProcessRealization κ P X]
    {s z y : ℤ} {A : Set Ω} {n m : ℕ}
    (hA_meas : MeasurableSet[generatedFiltrationSpace X n] A)
    (hA_sub : A ⊆ {ω | X n ω = z}) :
    (P s : Measure Ω) (A ∩ {ω | X (n + m) ω = y}) =
      ((κ m) z ({y} : Set ℤ)) * (P s : Measure Ω) A := by
  let μ : Measure Ω := P s
  let hReal : IsMarkovProcessRealization κ P X := inferInstance
  let B : Set Ω := X (n + m) ⁻¹' ({y} : Set ℤ)
  have hB_meas : MeasurableSet B := by
    simpa [B] using (hReal.measurable_process (n + m)) (MeasurableSet.singleton y)
  have hA_measAmbient : MeasurableSet A := by
    exact (generatedFiltrationSpace_le_ambient X hReal.measurable_process n) _ hA_meas
  have hMarkovGenerated :
      μ⟦B | generatedFiltrationSpace X n⟧ =ᵐ[μ]
        fun ω ↦ (((κ m) (X n ω)).real ({y} : Set ℤ)) := by
    -- Proof comment: this is the deterministic-time Markov property specialized to the
    -- singleton future event `{y}` at gap `m`.
    simpa [μ, B, add_comm] using
      hReal.markov_property s (A := ({y} : Set ℤ)) (MeasurableSet.singleton y) n m
  have hIndicatorIntegrable : Integrable (B.indicator (fun _ ↦ (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hB_meas
  have hstep :
      μ.real (A ∩ {ω | X (n + m) ω = y}) =
        (((κ m) z ({y} : Set ℤ)).toReal) * μ.real A := by
    -- Proof comment: integrate the Markov conditional expectation over `A`, then freeze the
    -- transition row at `z` because `A` already pins down the time-`n` state.
    calc
      μ.real (A ∩ {ω | X (n + m) ω = y}) =
          ∫ ω in A, (μ⟦B | generatedFiltrationSpace X n⟧) ω ∂ μ := by
            rw [setIntegral_condExp
              (generatedFiltrationSpace_le_ambient X hReal.measurable_process n)
              hIndicatorIntegrable hA_meas, ← integral_indicator hA_measAmbient]
            symm
            simpa [B, Set.indicator_indicator, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm,
              smul_eq_mul] using integral_indicator_const (μ := μ) (1 : ℝ)
                (hA_measAmbient.inter hB_meas)
      _ = ∫ ω in A, (((κ m) (X n ω)).real ({y} : Set ℤ)) ∂ μ := by
            exact integral_congr_ae hMarkovGenerated.restrict
      _ = ∫ _ in A, (((κ m) z ({y} : Set ℤ)).toReal) ∂ μ := by
            refine integral_congr_ae ?_
            filter_upwards [self_mem_ae_restrict (μ := μ) (s := A) hA_measAmbient] with ω hω
            have hω : X n ω = z := hA_sub hω
            rw [hω]
            rfl
      _ = (((κ m) z ({y} : Set ℤ)).toReal) * μ.real A := by
            rw [setIntegral_const, smul_eq_mul, mul_comm]
  have hleft_ne_top :
      (P s : Measure Ω) (A ∩ {ω | X (n + m) ω = y}) ≠ ⊤ :=
    measure_ne_top _ _
  letI : IsMarkovKernel (κ m) := hReal.semigroup.isMarkovKernel m
  have hkernel_ne_top : ((κ m) z ({y} : Set ℤ)) ≠ ⊤ :=
    measure_ne_top _ _
  have hA_ne_top : (P s : Measure Ω) A ≠ ⊤ :=
    measure_ne_top _ _
  have hkernel_toReal_nonneg : 0 ≤ (((κ m) z ({y} : Set ℤ)).toReal) :=
    ENNReal.toReal_nonneg
  -- Proof comment: transport the real-valued factorization back to `ℝ≥0∞`.
  calc
    (P s : Measure Ω) (A ∩ {ω | X (n + m) ω = y}) =
        ENNReal.ofReal ((P s : Measure Ω).real (A ∩ {ω | X (n + m) ω = y})) := by
          symm
          exact ENNReal.ofReal_toReal hleft_ne_top
    _ = ENNReal.ofReal
        ((((κ m) z ({y} : Set ℤ)).toReal) * (P s : Measure Ω).real A) := by
          rw [hstep]
    _ = ((κ m) z ({y} : Set ℤ)) * (P s : Measure Ω) A := by
          rw [ENNReal.ofReal_mul hkernel_toReal_nonneg, ENNReal.ofReal_toReal hkernel_ne_top,
            Measure.real_def, ENNReal.ofReal_toReal hA_ne_top]

/-- Helper for Theorem 17.40: `firstPositiveHitEvent X y n` is the event that the path first hits
`y` at the positive time `n`. -/
private def firstPositiveHitEvent (Y : ℕ → Ω → ℤ) (y : ℤ) (n : ℕ) : Set Ω :=
  {ω | Y n ω = y ∧ ∀ j : ℕ, 1 ≤ j → j ≤ n - 1 → Y j ω ≠ y}

/-- Helper for Theorem 17.40: the exact first-positive-hit event is measurable. -/
private lemma firstPositiveHitEvent_measurable
    (Y : ℕ → Ω → ℤ) (hY_meas : ∀ n : ℕ, Measurable (Y n)) (y : ℤ) (n : ℕ) :
    MeasurableSet (firstPositiveHitEvent Y y n) := by
  -- Proof comment: the event is a finite intersection of singleton state events and their
  -- complements.
  have hEq :
      firstPositiveHitEvent Y y n =
        {ω | Y n ω = y} ∩ ⋂ j ∈ Finset.Icc 1 (n - 1), {ω | Y j ω ≠ y} := by
    ext ω
    simp [firstPositiveHitEvent]
  rw [hEq]
  refine ((hY_meas n) (MeasurableSet.singleton y)).inter ?_
  classical
  refine MeasurableSet.iInter fun j ↦ ?_
  refine MeasurableSet.iInter fun _ ↦ ?_
  exact ((hY_meas j) (MeasurableSet.singleton y)).compl

/-- Helper for Theorem 17.40: every exact first-positive-hit event is contained in the
corresponding state event. -/
private lemma firstPositiveHitEvent_subset_state
    {Ω' : Type*} (Y : ℕ → Ω' → ℤ) (y : ℤ) (n : ℕ) :
    firstPositiveHitEvent Y y n ⊆ {ω | Y n ω = y} :=
  fun _ hω ↦ hω.1

/-- Helper for Theorem 17.40: exact first-positive-hit events at distinct positive times are
pairwise disjoint. -/
private lemma firstPositiveHitEvent_disjoint
    {Ω' : Type*} (Y : ℕ → Ω' → ℤ) (y : ℤ) {m n : ℕ}
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hmn : m ≠ n) :
    Disjoint (firstPositiveHitEvent Y y m) (firstPositiveHitEvent Y y n) := by
  refine Set.disjoint_left.2 ?_
  intro ω hωm hωn
  rcases lt_or_gt_of_ne hmn with hmn_lt | hnm_lt
  · have hm_mem : m ∈ Finset.Icc 1 (n - 1) := by
      exact Finset.mem_Icc.mpr ⟨hm, Nat.le_pred_of_lt hmn_lt⟩
    have hm_bounds : 1 ≤ m ∧ m ≤ n - 1 := Finset.mem_Icc.mp hm_mem
    have hstate : Y m ω = y := (firstPositiveHitEvent_subset_state Y y m) hωm
    have havoid : Y m ω ≠ y := hωn.2 m hm_bounds.1 hm_bounds.2
    exact havoid hstate
  · have hn_mem : n ∈ Finset.Icc 1 (m - 1) := by
      exact Finset.mem_Icc.mpr ⟨hn, Nat.le_pred_of_lt hnm_lt⟩
    have hn_bounds : 1 ≤ n ∧ n ≤ m - 1 := Finset.mem_Icc.mp hn_mem
    have hstate : Y n ω = y := (firstPositiveHitEvent_subset_state Y y n) hωn
    have havoid : Y n ω ≠ y := hωm.2 n hn_bounds.1 hn_bounds.2
    exact havoid hstate

/-- Helper for Theorem 17.40: at a fixed positive time `k`, the state event `{X k = y}` splits
as the union over the exact first positive hit time of `y`. -/
private lemma firstPositiveHitEvent_partition_stateEvent
    {Ω' : Type*} (Y : ℕ → Ω' → ℤ) (y : ℤ) {k : ℕ} (hk : 1 ≤ k) :
    {ω | Y k ω = y} =
      ⋃ n ∈ Finset.Icc 1 k, firstPositiveHitEvent Y y n ∩ {ω | Y k ω = y} := by
  ext ω
  constructor
  · intro hω
    let hits : Finset ℕ := (Finset.Icc 1 k).filter fun n ↦ Y n ω = y
    have hhits_nonempty : hits.Nonempty := by
      refine ⟨k, ?_⟩
      simpa [hits, hk] using hω
    let n : ℕ := hits.min' hhits_nonempty
    have hn_mem : n ∈ hits := Finset.min'_mem hits hhits_nonempty
    have hn_Icc : n ∈ Finset.Icc 1 k := by
      simpa [hits] using (Finset.mem_filter.mp hn_mem).1
    have hn_state : Y n ω = y := by
      simpa [hits] using (Finset.mem_filter.mp hn_mem).2
    have hfirst : ω ∈ firstPositiveHitEvent Y y n := by
      refine ⟨hn_state, ?_⟩
      intro j hj_pos hj_le hj_state
      have hn_pos : 1 ≤ n := (Finset.mem_Icc.mp hn_Icc).1
      have hj_lt_n : j < n := by
        omega
      have hj_le_k : j ≤ k := le_trans (Nat.le_of_lt hj_lt_n) (Finset.mem_Icc.mp hn_Icc).2
      have hj_hits : j ∈ hits := by
        simp [hits, hj_pos, hj_le_k, hj_state]
      have hn_le_j : n ≤ j := Finset.min'_le hits j hj_hits
      exact (not_lt_of_ge hn_le_j) hj_lt_n
    exact Set.mem_iUnion.2 ⟨n, Set.mem_iUnion.2 ⟨hn_Icc, ⟨hfirst, hω⟩⟩⟩
  · intro hω
    rcases Set.mem_iUnion.mp hω with ⟨n, hω⟩
    rcases Set.mem_iUnion.mp hω with ⟨hn, hω⟩
    exact hω.2

/-- Helper for Theorem 17.40: the exact first-positive-hit event is already measurable in the
time-`n` history filtration. -/
private lemma firstPositiveHitEvent_measurableInFiltration
    {Ω' : Type*} (Y : ℕ → Ω' → ℤ) (y : ℤ) (n : ℕ) :
    MeasurableSet[generatedFiltrationSpace Y n] (firstPositiveHitEvent Y y n) := by
  have hEq :
      firstPositiveHitEvent Y y n =
        {ω | Y n ω = y} ∩ ⋂ j ∈ Finset.Icc 1 (n - 1), {ω | Y j ω ≠ y} := by
    ext ω
    simp [firstPositiveHitEvent]
  rw [hEq]
  have hYn :
      Measurable[generatedFiltrationSpace Y n] (Y n) := by
    refine Measurable.of_comap_le ?_
    exact le_iSup_of_le n <| le_iSup_of_le le_rfl le_rfl
  refine (hYn (MeasurableSet.singleton y)).inter ?_
  refine MeasurableSet.iInter fun j ↦ ?_
  refine MeasurableSet.iInter fun hj ↦ ?_
  have hj_le : j ≤ n := le_trans (Finset.mem_Icc.mp hj).2 (Nat.sub_le _ _)
  have hYj :
      Measurable[generatedFiltrationSpace Y n] (Y j) := by
    refine Measurable.of_comap_le ?_
    exact le_iSup_of_le j <| le_iSup_of_le hj_le le_rfl
  exact (hYj (MeasurableSet.singleton y)).compl

/-- Helper for Theorem 17.40: in any realized one-dimensional walk, the finite Green window at an
off-diagonal target is bounded by the corresponding diagonal window at that target. -/
private lemma truncatedGreen_offDiagonal_le_self
    {κ : ℕ → Kernel ℤ ℤ} {P : ℤ → ProbabilityMeasure Ω}
    [IsMarkovProcessRealization κ P X]
    (N : ℕ) (y : ℤ) :
    (∑ k ∈ Finset.range (N + 1), (P 0 : Measure Ω) {ω | X k ω = y}) ≤
      (∑ k ∈ Finset.range (N + 1), (P y : Measure Ω) {ω | X k ω = y}) := by
  by_cases hy : y = 0
  · simp [hy]
  let hReal : IsMarkovProcessRealization κ P X := inferInstance
  let hitMass : ℕ → ℝ≥0∞ := fun n ↦ (P 0 : Measure Ω) (firstPositiveHitEvent X y n)
  let selfMass : ℕ → ℝ≥0∞ := fun n ↦ (P y : Measure Ω) {ω | X n ω = y}
  let GselfN : ℝ≥0∞ := ∑ k ∈ Finset.range (N + 1), selfMass k
  have hselfMass :
      ∀ m : ℕ, ((κ m) y ({y} : Set ℤ)) = selfMass m := by
    intro m
    have hpreimage : {ω | X m ω = y} = X m ⁻¹' ({y} : Set ℤ) := by
      ext ω
      simp
    dsimp [selfMass]
    rw [hpreimage, ← Measure.map_apply (hReal.measurable_process m)
      (measurableSet_singleton y), hReal.transition_eq y m]
  have htimeZero :
      (P 0 : Measure Ω) {ω | X 0 ω = y} = 0 := by
    have hpreimage : {ω | X 0 ω = y} = X 0 ⁻¹' ({y} : Set ℤ) := by
      ext ω
      simp
    rw [hpreimage, ← Measure.map_apply (hReal.measurable_process 0) (measurableSet_singleton y),
      hReal.initial_eq 0]
    simp [hy]
  have hhit_disjoint :
      Set.PairwiseDisjoint (↑(Finset.Ico 1 (N + 1)) : Set ℕ)
        (fun n ↦ firstPositiveHitEvent X y n) := by
    intro n hn m hm hnm
    exact firstPositiveHitEvent_disjoint
      (Y := X) y (hm := (Finset.mem_Ico.mp hn).1) (hn := (Finset.mem_Ico.mp hm).1) hnm
  have hhit_meas :
      ∀ n ∈ Finset.Ico 1 (N + 1), MeasurableSet (firstPositiveHitEvent X y n) := by
    intro n hn
    exact firstPositiveHitEvent_measurable X (fun m ↦ hReal.measurable_process m) y n
  have hhit_sum_le_one :
      ∑ n ∈ Finset.Ico 1 (N + 1), hitMass n ≤ 1 := by
    let U : Set Ω := ⋃ n ∈ Finset.Ico 1 (N + 1), firstPositiveHitEvent X y n
    have hsum :
        ∑ n ∈ Finset.Ico 1 (N + 1), hitMass n = (P 0 : Measure Ω) U := by
      symm
      simpa [hitMass, U] using MeasureTheory.measure_biUnion_finset hhit_disjoint hhit_meas
    calc
      ∑ n ∈ Finset.Ico 1 (N + 1), hitMass n = (P 0 : Measure Ω) U := hsum
      _ ≤ (P 0 : Measure Ω) Set.univ := by
        exact measure_mono (Set.subset_univ U)
      _ = 1 := by simp
  have hstate_decomp :
      ∀ k ∈ Finset.Ico 1 (N + 1),
        (P 0 : Measure Ω) {ω | X k ω = y} =
          ∑ n ∈ Finset.Ico 1 (k + 1), selfMass (k - n) * hitMass n := by
    intro k hk
    have hk_pos : 1 ≤ k := (Finset.mem_Ico.mp hk).1
    have hIccIco : Finset.Icc 1 k = Finset.Ico 1 (k + 1) := by
      ext n
      simp
    have hUnion :
        {ω | X k ω = y} =
          ⋃ n ∈ Finset.Ico 1 (k + 1), firstPositiveHitEvent X y n ∩ {ω | X k ω = y} := by
        simpa [hIccIco] using firstPositiveHitEvent_partition_stateEvent (Y := X) y hk_pos
    have hDisjoint :
        Set.PairwiseDisjoint (↑(Finset.Ico 1 (k + 1)) : Set ℕ)
          (fun n ↦ firstPositiveHitEvent X y n ∩ {ω | X k ω = y}) := by
      intro n hn m hm hnm
      refine Set.disjoint_left.2 ?_
      intro ω hωn hωm
      exact
        Set.disjoint_left.mp
          (firstPositiveHitEvent_disjoint
            (Y := X) y
            (hm := (Finset.mem_Ico.mp hn).1)
            (hn := (Finset.mem_Ico.mp hm).1) hnm) hωn.1 hωm.1
    have hMeas :
        ∀ n ∈ Finset.Ico 1 (k + 1),
          MeasurableSet (firstPositiveHitEvent X y n ∩ {ω | X k ω = y}) := by
      intro n hn
      have hstateMeas : MeasurableSet {ω | X k ω = y} := by
        simpa [Set.preimage] using (hReal.measurable_process k) (MeasurableSet.singleton y)
      exact
        (firstPositiveHitEvent_measurable X (fun m ↦ hReal.measurable_process m) y n).inter
          hstateMeas
    calc
      (P 0 : Measure Ω) {ω | X k ω = y}
          = (P 0 : Measure Ω)
              (⋃ n ∈ Finset.Ico 1 (k + 1), firstPositiveHitEvent X y n ∩ {ω | X k ω = y}) := by
              exact congrArg (fun s : Set Ω ↦ (P 0 : Measure Ω) s) hUnion
      _ = ∑ n ∈ Finset.Ico 1 (k + 1),
            (P 0 : Measure Ω) (firstPositiveHitEvent X y n ∩ {ω | X k ω = y}) := by
              exact MeasureTheory.measure_biUnion_finset hDisjoint hMeas
      _ = ∑ n ∈ Finset.Ico 1 (k + 1), selfMass (k - n) * hitMass n := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            have hn_le_k : n ≤ k := Nat.le_of_lt_succ (Finset.mem_Ico.mp hn).2
            have hslice :
                (P 0 : Measure Ω) (firstPositiveHitEvent X y n ∩ {ω | X (n + (k - n)) ω = y}) =
                  ((κ (k - n)) y ({y} : Set ℤ)) *
                    (P 0 : Measure Ω) (firstPositiveHitEvent X y n) :=
              measure_inter_prefix_stepEvent_eq_mulLocal
                (κ := κ) (P := P) (X := X)
                (s := 0) (z := y) (y := y)
                (A := firstPositiveHitEvent X y n)
                (n := n) (m := k - n)
                (firstPositiveHitEvent_measurableInFiltration (Y := X) y n)
                (firstPositiveHitEvent_subset_state X y n)
            simpa [Nat.add_sub_of_le hn_le_k, hitMass, selfMass, hselfMass (k - n)] using hslice
  have hinner_le :
      ∀ n ∈ Finset.Ico 1 (N + 1),
        ∑ k ∈ Finset.Ico n (N + 1), selfMass (k - n) ≤ GselfN := by
    intro n hn
    calc
      ∑ k ∈ Finset.Ico n (N + 1), selfMass (k - n)
          = ∑ m ∈ Finset.range (N + 1 - n), selfMass m := by
              rw [Finset.sum_Ico_eq_sum_range]
              refine Finset.sum_congr rfl ?_
              intro m hm
              rw [Nat.add_sub_cancel_left]
      _ ≤ ∑ m ∈ Finset.range (N + 1), selfMass m := by
            exact Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.range_subset_range.2 (Nat.sub_le _ _))
              (fun _ _ _ ↦ bot_le)
      _ = GselfN := by rfl
  calc
    ∑ k ∈ Finset.range (N + 1), (P 0 : Measure Ω) {ω | X k ω = y}
        = ∑ k ∈ Finset.range 1, (P 0 : Measure Ω) {ω | X k ω = y} +
            ∑ k ∈ Finset.Ico 1 (N + 1), (P 0 : Measure Ω) {ω | X k ω = y} := by
            simpa using
              (Finset.sum_range_eq_add_Ico
                (fun k ↦ (P 0 : Measure Ω) {ω | X k ω = y}) (by omega))
    _ = ∑ k ∈ Finset.Ico 1 (N + 1), (P 0 : Measure Ω) {ω | X k ω = y} := by
            rw [Finset.sum_range_one, htimeZero, zero_add]
    _ = ∑ k ∈ Finset.Ico 1 (N + 1),
          ∑ n ∈ Finset.Ico 1 (k + 1), selfMass (k - n) * hitMass n := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            exact hstate_decomp k hk
    _ = ∑ n ∈ Finset.Ico 1 (N + 1),
          ∑ k ∈ Finset.Ico n (N + 1), selfMass (k - n) * hitMass n := by
            symm
            exact Finset.sum_Ico_Ico_comm 1 (N + 1)
              (fun n k ↦ selfMass (k - n) * hitMass n)
    _ = ∑ n ∈ Finset.Ico 1 (N + 1), hitMass n *
          ∑ k ∈ Finset.Ico n (N + 1), selfMass (k - n) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            calc
              ∑ k ∈ Finset.Ico n (N + 1), selfMass (k - n) * hitMass n =
                  (∑ k ∈ Finset.Ico n (N + 1), selfMass (k - n)) * hitMass n := by
                    symm
                    exact Finset.sum_mul (Finset.Ico n (N + 1)) (fun k ↦ selfMass (k - n))
                      (hitMass n)
              _ = hitMass n * ∑ k ∈ Finset.Ico n (N + 1), selfMass (k - n) := by
                    rw [mul_comm]
    _ ≤ ∑ n ∈ Finset.Ico 1 (N + 1), hitMass n * GselfN := by
            refine Finset.sum_le_sum ?_
            intro n hn
            simpa [mul_comm] using mul_le_mul_right (hinner_le n hn) (hitMass n)
    _ = (∑ n ∈ Finset.Ico 1 (N + 1), hitMass n) * GselfN := by
            rw [Finset.sum_mul]
    _ = GselfN * (∑ n ∈ Finset.Ico 1 (N + 1), hitMass n) := by
            rw [mul_comm]
    _ ≤ GselfN * 1 := by
            exact mul_le_mul_right hhit_sum_le_one GselfN
    _ = GselfN := by simp
    _ = ∑ k ∈ Finset.range (N + 1), (P y : Measure Ω) {ω | X k ω = y} := by
            rfl

/-- Helper for Theorem 17.40: on the canonical one-dimensional convolution walk, summing the
finite off-diagonal Green-window bound over the interval `[-L, L]` yields the source proof's
finite-window averaging inequality. -/
private lemma intervalMass_sum_le_card_mul_truncatedGreenSelf
    (ν : ProbabilityMeasure ℤ)
    {Ω' : Type*} [MeasurableSpace Ω'] (Qprob : ProbabilityMeasure Ω') (Z : ℕ → Ω' → ℤ)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ dirac_convolution_kernel (ν : Measure ℤ) ^ n)
      (productStartRandomWalkMeasure Qprob)
      (productStartRandomWalk Z)]
    (N L : ℕ) :
    (∑ k ∈ Finset.range (N + 1),
      ((dirac_convolution_kernel (ν : Measure ℤ) ^ k) (0 : ℤ))
        ((Finset.Icc (-(L : ℤ)) L : Finset ℤ) : Set ℤ)) ≤
      (2 * L + 1 : ℝ≥0∞) *
        ∑ k ∈ Finset.range (N + 1),
          ((dirac_convolution_kernel (ν : Measure ℤ) ^ k) (0 : ℤ)) ({0} : Set ℤ) := by
  let window : Finset ℤ := Finset.Icc (-(L : ℤ)) L
  let hReal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ dirac_convolution_kernel (ν : Measure ℤ) ^ n)
        (productStartRandomWalkMeasure Qprob)
        (productStartRandomWalk Z) := inferInstance
  let originWindow : ℝ≥0∞ :=
    ∑ k ∈ Finset.range (N + 1),
      ((dirac_convolution_kernel (ν : Measure ℤ) ^ k) (0 : ℤ)) ({0} : Set ℤ)
  have hstateMass :
      ∀ x y : ℤ, ∀ k : ℕ,
        (productStartRandomWalkMeasure Qprob x : Measure (ℤ × Ω'))
            {s | productStartRandomWalk Z k s = y} =
          ((dirac_convolution_kernel (ν : Measure ℤ) ^ k) x) ({y} : Set ℤ) := by
    intro x y k
    have hpreimage :
        {s | productStartRandomWalk Z k s = y} =
          productStartRandomWalk Z k ⁻¹' ({y} : Set ℤ) := by
      ext s
      simp
    rw [hpreimage, ← Measure.map_apply (hReal.measurable_process k)
      (measurableSet_singleton y), hReal.transition_eq x k]
  have hintervalSplit :
      ∑ k ∈ Finset.range (N + 1),
          ((dirac_convolution_kernel (ν : Measure ℤ) ^ k) (0 : ℤ)) (window : Set ℤ) =
        ∑ y ∈ window, ∑ k ∈ Finset.range (N + 1),
          ((dirac_convolution_kernel (ν : Measure ℤ) ^ k) (0 : ℤ)) ({y} : Set ℤ) := by
    calc
      ∑ k ∈ Finset.range (N + 1),
          ((dirac_convolution_kernel (ν : Measure ℤ) ^ k) (0 : ℤ)) (window : Set ℤ) =
        ∑ k ∈ Finset.range (N + 1), ∑ y ∈ window,
          ((dirac_convolution_kernel (ν : Measure ℤ) ^ k) (0 : ℤ)) ({y} : Set ℤ) := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            symm
            exact MeasureTheory.sum_measure_singleton
              (μ := ((dirac_convolution_kernel (ν : Measure ℤ) ^ k) (0 : ℤ))) (s := window)
      _ = ∑ y ∈ window, ∑ k ∈ Finset.range (N + 1),
            ((dirac_convolution_kernel (ν : Measure ℤ) ^ k) (0 : ℤ)) ({y} : Set ℤ) := by
            rw [Finset.sum_comm]
  have hpointwise :
      ∀ y ∈ window,
        ∑ k ∈ Finset.range (N + 1),
            ((dirac_convolution_kernel (ν : Measure ℤ) ^ k) (0 : ℤ)) ({y} : Set ℤ) ≤
          originWindow := by
    intro y hy
    calc
      ∑ k ∈ Finset.range (N + 1),
          ((dirac_convolution_kernel (ν : Measure ℤ) ^ k) (0 : ℤ)) ({y} : Set ℤ) =
        ∑ k ∈ Finset.range (N + 1),
          (productStartRandomWalkMeasure Qprob 0 : Measure (ℤ × Ω'))
            {s | productStartRandomWalk Z k s = y} := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            symm
            simpa using hstateMass (x := 0) (y := y) (k := k)
      _ ≤ ∑ k ∈ Finset.range (N + 1),
            (productStartRandomWalkMeasure Qprob y : Measure (ℤ × Ω'))
              {s | productStartRandomWalk Z k s = y} := by
            exact truncatedGreen_offDiagonal_le_self
              (κ := fun n : ℕ ↦ dirac_convolution_kernel (ν : Measure ℤ) ^ n)
              (P := productStartRandomWalkMeasure Qprob)
              (X := productStartRandomWalk Z)
              N y
      _ = originWindow := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            rw [hstateMass (x := y) (y := y) (k := k)]
            simpa [originWindow] using
              diracConvolutionKernelPow_apply_self_eq_originMass (ν := ν) k y
  have hcardNat : window.card = 2 * L + 1 := by
    have hcardInt : ((window.card : ℕ) : ℤ) = (2 * L + 1 : ℤ) := by
      dsimp [window]
      rw [Int.card_Icc]
      omega
    exact_mod_cast hcardInt
  have hcardENN : (window.card : ℝ≥0∞) = (2 * L + 1 : ℝ≥0∞) := by
    exact_mod_cast hcardNat
  calc
    (∑ k ∈ Finset.range (N + 1),
      ((dirac_convolution_kernel (ν : Measure ℤ) ^ k) (0 : ℤ))
        ((Finset.Icc (-(L : ℤ)) L : Finset ℤ) : Set ℤ)) =
      ∑ y ∈ window, ∑ k ∈ Finset.range (N + 1),
        ((dirac_convolution_kernel (ν : Measure ℤ) ^ k) (0 : ℤ)) ({y} : Set ℤ) := by
          simpa [window] using hintervalSplit
    _ ≤ ∑ y ∈ window, originWindow := by
          refine Finset.sum_le_sum ?_
          intro y hy
          exact hpointwise y hy
    _ = window.card • originWindow := by
          simp [originWindow]
    _ = (2 * L + 1 : ℝ≥0∞) * originWindow := by
          rw [nsmul_eq_mul, hcardENN]
    _ =
        (2 * L + 1 : ℝ≥0∞) *
          ∑ k ∈ Finset.range (N + 1),
            ((dirac_convolution_kernel (ν : Measure ℤ) ^ k) (0 : ℤ)) ({0} : Set ℤ) := by
          rfl

/-- Helper for Theorem 17.40: if the normalized position is at most `1 / m` and `k ≤ m * L`,
then the walk position lies in the fixed window `[-L, L]`. -/
private lemma smallDeviationEvent_subset_fixedWindow
    {Ω' : Type*} [MeasurableSpace Ω'] (Z : ℕ → Ω' → ℤ)
    {m : ℕ+} {k L : ℕ} (hk : k ≤ m * L) :
    {s | |(productStartRandomWalk Z k s : ℝ)| ≤ (k : ℝ) / m} ⊆
      {s | productStartRandomWalk Z k s ∈ (Finset.Icc (-(L : ℤ)) L : Finset ℤ)} := by
  intro s hs
  have hm_pos : 0 < (m : ℝ) := by
    exact_mod_cast m.pos
  have hk_real : (k : ℝ) ≤ (m : ℝ) * L := by
    exact_mod_cast hk
  have hdiv : (k : ℝ) / m ≤ L := by
    rw [div_le_iff₀ hm_pos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hk_real
  have habs : |(productStartRandomWalk Z k s : ℝ)| ≤ L :=
    le_trans hs hdiv
  have hbounds :
      (-(L : ℝ) ≤ (productStartRandomWalk Z k s : ℝ)) ∧
        ((productStartRandomWalk Z k s : ℝ) ≤ L) := by
    simpa [abs_le] using habs
  have hlow : -(L : ℤ) ≤ productStartRandomWalk Z k s := by
    exact_mod_cast hbounds.1
  have hupp : productStartRandomWalk Z k s ≤ L := by
    exact_mod_cast hbounds.2
  exact Finset.mem_Icc.mpr ⟨hlow, hupp⟩

/-- Helper for Theorem 17.40: the normalized canonical walk `X_k / k` converges to `0` in
measure under the zero-drift hypotheses. -/
private lemma canonicalWalk_normalizedPosition_tendstoInMeasure_zero
    (ν : ProbabilityMeasure ℤ)
    (hν_integrable : Integrable (fun z : ℤ ↦ (z : ℝ)) (ν : Measure ℤ))
    (hν_mean_zero : ∫ z, (z : ℝ) ∂(ν : Measure ℤ) = 0)
    {Ω' : Type*} [MeasurableSpace Ω'] (Qprob : ProbabilityMeasure Ω') (Z : ℕ → Ω' → ℤ)
    (hZ_meas : ∀ n : ℕ, Measurable (Z n))
    (hZ_indep : iIndepFun Z (Qprob : Measure Ω'))
    (hZ_law : ∀ n : ℕ, HasLaw (Z n) (ν : Measure ℤ) (Qprob : Measure Ω')) :
    TendstoInMeasure
      (productStartRandomWalkMeasure Qprob 0 : Measure (ℤ × Ω'))
      (fun k s ↦ (productStartRandomWalk Z k s : ℝ) / k) atTop (fun _ ↦ (0 : ℝ)) := by
  let μ0 : Measure (ℤ × Ω') := (productStartRandomWalkMeasure Qprob 0 : Measure (ℤ × Ω'))
  letI : IsProbabilityMeasure μ0 := by
    change IsProbabilityMeasure ((productStartRandomWalkMeasure Qprob 0 : Measure (ℤ × Ω')))
    infer_instance
  have hlimit_ae_base :
      ∀ᵐ ω ∂(Qprob : Measure Ω'),
        Tendsto (fun n : ℕ ↦ (randomWalkProcess Z n ω : ℝ) / n) atTop
          (nhds (∫ z, (z : ℝ) ∂(ν : Measure ℤ))) :=
    randomWalkProcess_ae_tendsto_stepMean ν Qprob Z hν_integrable hZ_indep hZ_law
  have hlimit_ae :
      ∀ᵐ s ∂(productStartRandomWalkMeasure Qprob 0 : Measure (ℤ × Ω')),
        Tendsto (fun n : ℕ ↦ (productStartRandomWalk Z n s : ℝ) / n) atTop
          (nhds (∫ z, (z : ℝ) ∂(ν : Measure ℤ))) := by
    let hprodMk : MeasurableEmbedding (fun ω : Ω' ↦ ((0 : ℤ), ω)) :=
      MeasurableEmbedding.prodMk_left (x := (0 : ℤ)) (f := id) MeasurableEmbedding.id
    have hstart_measure :
        (productStartRandomWalkMeasure Qprob 0 : Measure (ℤ × Ω')) =
          (Qprob : Measure Ω').map (fun ω ↦ ((0 : ℤ), ω)) := by
      change ((Measure.dirac (0 : ℤ)).prod (Qprob : Measure Ω')) =
        (Qprob : Measure Ω').map (fun ω ↦ ((0 : ℤ), ω))
      rw [Measure.dirac_prod]
    rw [hstart_measure]
    rw [hprodMk.ae_map_iff]
    filter_upwards [hlimit_ae_base] with ω hω
    have hpath :
        (fun n : ℕ ↦ (productStartRandomWalk Z n ((0 : ℤ), ω) : ℝ) / n) =
          fun n : ℕ ↦ (randomWalkProcess Z n ω : ℝ) / n := by
      funext n
      have hstep :
          productStartRandomWalk Z n ((0 : ℤ), ω) = 0 + randomWalkProcess Z n ω := by
        simpa using congrFun (productStartRandomWalk_comp_prodMk Z 0 n) ω
      rw [hstep]
      simp
    simpa [hpath] using hω
  have hmeas :
      ∀ k : ℕ,
        AEStronglyMeasurable (fun s ↦ (productStartRandomWalk Z k s : ℝ) / k) μ0 := by
    intro k
    have hcast_meas : Measurable fun z : ℤ ↦ (z : ℝ) :=
      measurable_of_countable (fun z : ℤ ↦ (z : ℝ))
    have hmeas_k :
        Measurable (fun s ↦ (productStartRandomWalk Z k s : ℝ) / k) :=
      (hcast_meas.comp (measurable_productStartRandomWalk Z hZ_meas k)).div_const k
    exact hmeas_k.aestronglyMeasurable
  simpa [hν_mean_zero] using MeasureTheory.tendstoInMeasure_of_tendsto_ae hmeas hlimit_ae

/-- Helper for Theorem 17.40: on the canonical product-start walk, the small-deviation event
`|X_k| ≤ k / m` eventually has probability at least `1 / 2`. -/
private lemma canonicalWalk_smallDeviation_measure_eventually_ge_half
    (ν : ProbabilityMeasure ℤ)
    (hν_integrable : Integrable (fun z : ℤ ↦ (z : ℝ)) (ν : Measure ℤ))
    (hν_mean_zero : ∫ z, (z : ℝ) ∂(ν : Measure ℤ) = 0)
    {Ω' : Type*} [MeasurableSpace Ω'] (Qprob : ProbabilityMeasure Ω') (Z : ℕ → Ω' → ℤ)
    (hZ_meas : ∀ n : ℕ, Measurable (Z n))
    (hZ_indep : iIndepFun Z (Qprob : Measure Ω'))
    (hZ_law : ∀ n : ℕ, HasLaw (Z n) (ν : Measure ℤ) (Qprob : Measure Ω'))
    (m : ℕ+) :
    ∀ᶠ k in atTop,
      (1 / 2 : ℝ) ≤
        (productStartRandomWalkMeasure Qprob 0 : Measure (ℤ × Ω')).real
          {s | |(productStartRandomWalk Z k s : ℝ)| ≤ (k : ℝ) / m} := by
  let μ0 : Measure (ℤ × Ω') := (productStartRandomWalkMeasure Qprob 0 : Measure (ℤ × Ω'))
  let goodEvent : ℕ → Set (ℤ × Ω') := fun k ↦
    {s | |(productStartRandomWalk Z k s : ℝ)| ≤ (k : ℝ) / m}
  let badEvent : ℕ → Set (ℤ × Ω') := fun k ↦
    {s | (1 / m : ℝ) ≤ ‖(productStartRandomWalk Z k s : ℝ) / k‖}
  letI : IsProbabilityMeasure μ0 := by
    change IsProbabilityMeasure ((productStartRandomWalkMeasure Qprob 0 : Measure (ℤ × Ω')))
    infer_instance
  have hmeasure :
      TendstoInMeasure μ0
        (fun k s ↦ (productStartRandomWalk Z k s : ℝ) / k) atTop (fun _ ↦ (0 : ℝ)) :=
    canonicalWalk_normalizedPosition_tendstoInMeasure_zero
      (ν := ν) hν_integrable hν_mean_zero Qprob Z hZ_meas hZ_indep hZ_law
  have hm_pos : 0 < (m : ℝ) := by
    exact_mod_cast m.pos
  have hbad_tendsto :
      Tendsto (fun k ↦ μ0.real (badEvent k)) atTop (nhds 0) := by
    have hnorm :=
      (MeasureTheory.tendstoInMeasure_iff_measureReal_norm (μ := μ0)).1 hmeasure
    simpa [badEvent] using hnorm (1 / m) (one_div_pos.2 hm_pos)
  have hbad_lt_half :
      ∀ᶠ k in atTop, μ0.real (badEvent k) < (1 / 2 : ℝ) :=
    hbad_tendsto (Iio_mem_nhds (by norm_num))
  have hbad_meas :
      ∀ k : ℕ, MeasurableSet (badEvent k) := by
    intro k
    have hcast_meas : Measurable fun z : ℤ ↦ (z : ℝ) :=
      measurable_of_countable (fun z : ℤ ↦ (z : ℝ))
    have hmeas_k :
        Measurable (fun s ↦ (productStartRandomWalk Z k s : ℝ) / k) :=
      (hcast_meas.comp (measurable_productStartRandomWalk Z hZ_meas k)).div_const k
    exact (hmeas_k.norm measurableSet_Ici)
  filter_upwards [eventually_ge_atTop 1, hbad_lt_half] with k hk hbad
  have hk_pos : 0 < (k : ℝ) := by
    exact_mod_cast hk
  have hsubset : (badEvent k)ᶜ ⊆ goodEvent k := by
    intro s hs
    have hsbad : ¬ (1 / m : ℝ) ≤ ‖(productStartRandomWalk Z k s : ℝ) / k‖ := by
      simpa [badEvent] using hs
    have hnorm_lt : ‖(productStartRandomWalk Z k s : ℝ) / k‖ < (1 / m : ℝ) :=
      lt_of_not_ge hsbad
    have habs_div :
        |(productStartRandomWalk Z k s : ℝ)| / k < (1 / m : ℝ) := by
      simpa [Real.norm_eq_abs, abs_div, abs_of_nonneg (le_of_lt hk_pos)] using hnorm_lt
    have habs_lt :
        |(productStartRandomWalk Z k s : ℝ)| < (k : ℝ) / m := by
      have hmul := (div_lt_iff₀ hk_pos).mp habs_div
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
    exact le_of_lt habs_lt
  have hcompl :
      μ0.real ((badEvent k)ᶜ) = 1 - μ0.real (badEvent k) := by
    rw [MeasureTheory.measureReal_compl (μ := μ0) (hbad_meas k), MeasureTheory.probReal_univ]
  have hmono :
      1 - μ0.real (badEvent k) ≤ μ0.real (goodEvent k) := by
    simpa [hcompl] using MeasureTheory.measureReal_mono (μ := μ0) hsubset
  have hhalf : (1 / 2 : ℝ) ≤ 1 - μ0.real (badEvent k) := by
    linarith
  exact le_trans hhalf hmono

/-- Helper for Theorem 17.40: realized window-event probabilities on the canonical product-start
walk agree with the corresponding kernel masses after taking `toReal`. -/
private lemma canonicalWalk_windowEvent_measureReal_eq_kernelMass
    (ν : ProbabilityMeasure ℤ)
    {Ω' : Type*} [MeasurableSpace Ω'] (Qprob : ProbabilityMeasure Ω') (Z : ℕ → Ω' → ℤ)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ dirac_convolution_kernel (ν : Measure ℤ) ^ n)
      (productStartRandomWalkMeasure Qprob)
      (productStartRandomWalk Z)]
    (k : ℕ) {S : Set ℤ} (hS : MeasurableSet S) :
    (productStartRandomWalkMeasure Qprob 0 : Measure (ℤ × Ω')).real
      {s | productStartRandomWalk Z k s ∈ S} =
      (((dirac_convolution_kernel (ν : Measure ℤ) ^ k) (0 : ℤ)) S).toReal := by
  let hReal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ dirac_convolution_kernel (ν : Measure ℤ) ^ n)
        (productStartRandomWalkMeasure Qprob)
        (productStartRandomWalk Z) := inferInstance
  have hpreimage :
      {s | productStartRandomWalk Z k s ∈ S} = productStartRandomWalk Z k ⁻¹' S := by
    ext s
    simp
  rw [hpreimage, Measure.real, ← Measure.map_apply (hReal.measurable_process k) hS,
    hReal.transition_eq (0 : ℤ) k]

/-- Helper for Theorem 17.40: a uniform `1 / 2` lower bound on the small-deviation events forces
the fixed interval `[-L, L]` to capture linearly many visits up to time `m * L`. -/
private lemma intervalMass_real_lowerBound_of_smallDeviation
    (ν : ProbabilityMeasure ℤ)
    {Ω' : Type*} [MeasurableSpace Ω'] (Qprob : ProbabilityMeasure Ω') (Z : ℕ → Ω' → ℤ)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ dirac_convolution_kernel (ν : Measure ℤ) ^ n)
      (productStartRandomWalkMeasure Qprob)
      (productStartRandomWalk Z)]
    (m : ℕ+) (K L : ℕ)
    (hK :
      ∀ k ≥ K,
        (1 / 2 : ℝ) ≤
          (productStartRandomWalkMeasure Qprob 0 : Measure (ℤ × Ω')).real
            {s | |(productStartRandomWalk Z k s : ℝ)| ≤ (k : ℝ) / m})
    (hKL : K ≤ m * L) :
    ((m * L + 1 - K : ℝ) / 2) ≤
      (∑ k ∈ Finset.range (m * L + 1),
        ((dirac_convolution_kernel (ν : Measure ℤ) ^ k) (0 : ℤ))
          ((Finset.Icc (-(L : ℤ)) L : Finset ℤ) : Set ℤ)).toReal := by
  let window : Set ℤ := ((Finset.Icc (-(L : ℤ)) L : Finset ℤ) : Set ℤ)
  let windowMass : ℕ → ℝ≥0∞ := fun k ↦
    ((dirac_convolution_kernel (ν : Measure ℤ) ^ k) (0 : ℤ)) window
  have hwindow_meas : MeasurableSet window := by
    simp [window]
  have htail_pointwise :
      ∀ k ∈ Finset.Icc K (m * L), (1 / 2 : ℝ) ≤ (windowMass k).toReal := by
    intro k hk
    have hk_ge : K ≤ k := Finset.mem_Icc.mp hk |>.1
    have hk_le : k ≤ m * L := Finset.mem_Icc.mp hk |>.2
    have hsmall :
        (1 / 2 : ℝ) ≤
          (productStartRandomWalkMeasure Qprob 0 : Measure (ℤ × Ω')).real
            {s | |(productStartRandomWalk Z k s : ℝ)| ≤ (k : ℝ) / m} :=
      hK k hk_ge
    have hsubset :
        {s | |(productStartRandomWalk Z k s : ℝ)| ≤ (k : ℝ) / m} ⊆
          {s | productStartRandomWalk Z k s ∈ (Finset.Icc (-(L : ℤ)) L : Finset ℤ)} :=
      smallDeviationEvent_subset_fixedWindow (Z := Z) (m := m) (k := k) (L := L) hk_le
    have hmono :
        (productStartRandomWalkMeasure Qprob 0 : Measure (ℤ × Ω')).real
            {s | |(productStartRandomWalk Z k s : ℝ)| ≤ (k : ℝ) / m} ≤
          (productStartRandomWalkMeasure Qprob 0 : Measure (ℤ × Ω')).real
            {s | productStartRandomWalk Z k s ∈ (Finset.Icc (-(L : ℤ)) L : Finset ℤ)} :=
      MeasureTheory.measureReal_mono
        (μ := (productStartRandomWalkMeasure Qprob 0 : Measure (ℤ × Ω'))) hsubset
    calc
      (1 / 2 : ℝ) ≤
          (productStartRandomWalkMeasure Qprob 0 : Measure (ℤ × Ω')).real
            {s | |(productStartRandomWalk Z k s : ℝ)| ≤ (k : ℝ) / m} := hsmall
      _ ≤
          (productStartRandomWalkMeasure Qprob 0 : Measure (ℤ × Ω')).real
            {s | productStartRandomWalk Z k s ∈ (Finset.Icc (-(L : ℤ)) L : Finset ℤ)} := hmono
      _ = (windowMass k).toReal := by
            simpa [window, windowMass] using
              canonicalWalk_windowEvent_measureReal_eq_kernelMass
                (ν := ν) (Qprob := Qprob) (Z := Z) (k := k) hwindow_meas
  have hcard :
      (Finset.Icc K (m * L)).card = m * L + 1 - K := by
    simp
  have htail_sum :
      ((m * L + 1 - K : ℝ) / 2) ≤
        ∑ k ∈ Finset.Icc K (m * L), (windowMass k).toReal := by
    calc
      ((m * L + 1 - K : ℝ) / 2)
          = ∑ k ∈ Finset.Icc K (m * L), (1 / 2 : ℝ) := by
              rw [Finset.sum_const, hcard, nsmul_eq_mul]
              have hKL_succ : K ≤ m * L + 1 := Nat.le_succ_of_le hKL
              rw [Nat.cast_sub hKL_succ, Nat.cast_add, Nat.cast_mul]
              ring
      _ ≤ ∑ k ∈ Finset.Icc K (m * L), (windowMass k).toReal := by
            exact Finset.sum_le_sum htail_pointwise
  have hsubset_range : Finset.Icc K (m * L) ⊆ Finset.range (m * L + 1) := by
    intro k hk
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Icc.mp hk |>.2))
  have hsum_le :
      ∑ k ∈ Finset.Icc K (m * L), (windowMass k).toReal ≤
        ∑ k ∈ Finset.range (m * L + 1), (windowMass k).toReal := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset_range <|
      fun _ _ _ ↦ MeasureTheory.measureReal_nonneg
  let hReal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ dirac_convolution_kernel (ν : Measure ℤ) ^ n)
        (productStartRandomWalkMeasure Qprob)
        (productStartRandomWalk Z) := inferInstance
  have htoReal_sum :
      (∑ k ∈ Finset.range (m * L + 1), windowMass k).toReal =
        ∑ k ∈ Finset.range (m * L + 1), (windowMass k).toReal := by
    exact ENNReal.toReal_sum fun k hk ↦ by
      have hle :
          ((dirac_convolution_kernel (ν : Measure ℤ) ^ k) (0 : ℤ)) window ≤
            ((dirac_convolution_kernel (ν : Measure ℤ) ^ k) (0 : ℤ)) Set.univ :=
        measure_mono (Set.subset_univ window)
      have huniv_ne_top :
          ((dirac_convolution_kernel (ν : Measure ℤ) ^ k) (0 : ℤ)) Set.univ ≠ ⊤ := by
        have huniv_eq_one :
            ((dirac_convolution_kernel (ν : Measure ℤ) ^ k) (0 : ℤ)) Set.univ = 1 := by
          letI : IsMarkovKernel ((fun n : ℕ ↦ dirac_convolution_kernel (ν : Measure ℤ) ^ n) k) :=
            hReal.semigroup.isMarkovKernel k
          simp
        rw [huniv_eq_one]
        simp
      exact ne_top_of_le_ne_top huniv_ne_top (by simpa [windowMass] using hle)
  calc
    ((m * L + 1 - K : ℝ) / 2) ≤ ∑ k ∈ Finset.Icc K (m * L), (windowMass k).toReal := htail_sum
    _ ≤ ∑ k ∈ Finset.range (m * L + 1), (windowMass k).toReal := hsum_le
    _ = (∑ k ∈ Finset.range (m * L + 1), windowMass k).toReal := htoReal_sum.symm
    _ =
        (∑ k ∈ Finset.range (m * L + 1),
          ((dirac_convolution_kernel (ν : Measure ℤ) ^ k) (0 : ℤ))
            ((Finset.Icc (-(L : ℤ)) L : Finset ℤ) : Set ℤ)).toReal := by
          rfl

/-- Helper for Theorem 17.40: the exit time from the centered interval `(-(m : ℤ), m)` for an
integer-valued path. Using `Int.natAbs` keeps the later pathwise prefix bound purely arithmetic. -/
private def intervalExitTime {Ω' : Type*} (Y : ℕ → Ω' → ℤ) (m : ℕ+) : Ω' → ℕ∞ :=
  fun ω ↦ MeasureTheory.hittingAfter Y {z : ℤ | m ≤ Int.natAbs z} 0 ω

/-- Helper for Theorem 17.40: the direct increment-space event that the partial-sum walk returns
to `0` before leaving `(-(m : ℤ), m)`. -/
private def directFirstReturnBeforeExitEvent {Ω' : Type*} [MeasurableSpace Ω']
    (Z : ℕ → Ω' → ℤ) (m : ℕ+) : Set Ω' :=
  {ω |
    MeasureTheory.hittingAfter (fun n ω' ↦ randomWalkProcess Z n ω') ({0} : Set ℤ) 1 ω <
      MeasureTheory.hittingAfter (fun n ω' ↦ randomWalkProcess Z n ω')
        {z : ℤ | m ≤ Int.natAbs z} 0 ω}

/-- Helper for Theorem 17.40: starting the auxiliary walk deterministically from `0` is the
pushforward of the increment law by `ω ↦ (0, ω)`. -/
private lemma productStartRandomWalkMeasure_zero_eq_map
    {Ω' : Type*} [MeasurableSpace Ω'] (Qprob : ProbabilityMeasure Ω') :
    (productStartRandomWalkMeasure Qprob 0 : Measure (ℤ × Ω')) =
      (Qprob : Measure Ω').map (fun ω ↦ ((0 : ℤ), ω)) := by
  -- Proof comment: the first coordinate is fixed by the Dirac mass, so only the increment sample
  -- remains random.
  change ((Measure.dirac (0 : ℤ)).prod (Qprob : Measure Ω')) =
    (Qprob : Measure Ω').map (fun ω ↦ ((0 : ℤ), ω))
  rw [Measure.dirac_prod]

/-- Helper for Theorem 17.40: if two integer-valued paths agree pointwise at one sample, their
hitting times into the same target set agree at that sample. -/
private lemma hittingAfter_eq_of_pointwise_eq
    {Ω' : Type*} [MeasurableSpace Ω']
    {u v : ℕ → Ω' → ℤ} {S : Set ℤ} {n : ℕ} {ω : Ω'}
    (hω : ∀ k : ℕ, u k ω = v k ω) :
    MeasureTheory.hittingAfter u S n ω = MeasureTheory.hittingAfter v S n ω := by
  by_cases hu : ∃ j, n ≤ j ∧ u j ω ∈ S
  · have hv : ∃ j, n ≤ j ∧ v j ω ∈ S := by
      rcases hu with ⟨j, hjn, hjs⟩
      exact ⟨j, hjn, by simpa [hω j] using hjs⟩
    rw [MeasureTheory.hittingAfter_def, MeasureTheory.hittingAfter_def]
    simp only
    rw [if_pos hu, if_pos hv]
    have hset :
        {i : ℕ | n ≤ i ∧ u i ω ∈ S} = {i : ℕ | n ≤ i ∧ v i ω ∈ S} := by
      ext i
      constructor
      · intro hi
        exact ⟨hi.1, by simpa [hω i] using hi.2⟩
      · intro hi
        exact ⟨hi.1, by simpa [hω i] using hi.2⟩
    have hsInf :
        sInf {i : ℕ | n ≤ i ∧ u i ω ∈ S} = sInf {i : ℕ | n ≤ i ∧ v i ω ∈ S} := by
      rw [hset]
    exact congrArg (fun m : ℕ ↦ (m : ℕ∞)) hsInf
  · have hv : ¬ ∃ j, n ≤ j ∧ v j ω ∈ S := by
      intro hv
      apply hu
      rcases hv with ⟨j, hjn, hjs⟩
      exact ⟨j, hjn, by simpa [hω j] using hjs⟩
    rw [MeasureTheory.hittingAfter_def, MeasureTheory.hittingAfter_def]
    simp only
    rw [if_neg hu, if_neg hv]

/-- Helper for Theorem 17.40: coordinatewise `ae` equality of increment families gives `ae`
equality of the associated partial-sum walks. -/
private lemma randomWalkProcess_ae_eq_of_ae_eq
    {Ω' : Type*} [MeasurableSpace Ω'] {μ : Measure Ω'}
    {Y Ym : ℕ → Ω' → ℤ}
    (hEq : ∀ n : ℕ, Y n =ᵐ[μ] Ym n) :
    ∀ᵐ ω ∂μ, ∀ n : ℕ, randomWalkProcess Y n ω = randomWalkProcess Ym n ω := by
  have hAll : ∀ᵐ ω ∂μ, ∀ n : ℕ, Y n ω = Ym n ω := by
    simpa [Filter.EventuallyEq] using (ae_all_iff.2 hEq)
  -- Proof comment: once the increments agree at every coordinate of a sample, the finite partial
  -- sums agree term-by-term as well.
  filter_upwards [hAll] with ω hω n
  rw [randomWalkProcess_apply, randomWalkProcess_apply]
  refine Finset.sum_congr rfl ?_
  intro j hj
  exact hω j

/-- Helper for Theorem 17.40: fixing the deterministic start `0` rewrites the canonical bounded
first-return event to the direct partial-sum event on the increment space. -/
private lemma canonicalFirstReturnBeforeExit_event_comp_prodMk
    {Ω' : Type*} [MeasurableSpace Ω'] (Z : ℕ → Ω' → ℤ) (m : ℕ+) (ω : Ω') :
    (τ_[productStartRandomWalk Z, 0]^1) ((0 : ℤ), ω) <
        intervalExitTime (productStartRandomWalk Z) m ((0 : ℤ), ω) ↔
      MeasureTheory.hittingAfter (fun n ω' ↦ randomWalkProcess Z n ω') ({0} : Set ℤ) 1 ω <
        MeasureTheory.hittingAfter (fun n ω' ↦ randomWalkProcess Z n ω')
          {z : ℤ | m ≤ Int.natAbs z} 0 ω := by
  let directProcess : ℕ → (ℤ × Ω') → ℤ := fun n s ↦ randomWalkProcess Z n s.2
  have hpath : ∀ n : ℕ,
      productStartRandomWalk Z n ((0 : ℤ), ω) = directProcess n ((0 : ℤ), ω) := by
    intro n
    simpa [directProcess] using congrFun (productStartRandomWalk_comp_prodMk Z 0 n) ω
  have hreturn :
      MeasureTheory.hittingAfter (productStartRandomWalk Z) ({0} : Set ℤ) 1 ((0 : ℤ), ω) =
        MeasureTheory.hittingAfter directProcess ({0} : Set ℤ) 1 ((0 : ℤ), ω) :=
    hittingAfter_eq_of_pointwise_eq (u := productStartRandomWalk Z) (v := directProcess)
      (S := ({0} : Set ℤ)) (n := 1) (ω := ((0 : ℤ), ω)) hpath
  have hexit :
      MeasureTheory.hittingAfter (productStartRandomWalk Z) {z : ℤ | m ≤ Int.natAbs z} 0
          ((0 : ℤ), ω) =
        MeasureTheory.hittingAfter directProcess {z : ℤ | m ≤ Int.natAbs z} 0 ((0 : ℤ), ω) :=
    hittingAfter_eq_of_pointwise_eq (u := productStartRandomWalk Z) (v := directProcess)
      (S := {z : ℤ | m ≤ Int.natAbs z}) (n := 0) (ω := ((0 : ℤ), ω)) hpath
  -- Proof comment: replace the auxiliary process by the direct partial-sum process at the fixed
  -- start `(0, ω)`, then unfold the direct process back to `randomWalkProcess`.
  simpa [iteratedEntranceTime_one, intervalExitTime, directProcess] using
    (show MeasureTheory.hittingAfter (productStartRandomWalk Z) ({0} : Set ℤ) 1 ((0 : ℤ), ω) <
        MeasureTheory.hittingAfter (productStartRandomWalk Z) {z : ℤ | m ≤ Int.natAbs z} 0
          ((0 : ℤ), ω) ↔
      MeasureTheory.hittingAfter directProcess ({0} : Set ℤ) 1 ((0 : ℤ), ω) <
      MeasureTheory.hittingAfter directProcess {z : ℤ | m ≤ Int.natAbs z} 0
        ((0 : ℤ), ω) from by
      rw [hreturn, hexit])

/-- Helper for Theorem 17.40: pulling the product-start first-return event back along
`ω ↦ (0, ω)` yields the direct increment-space event. -/
private lemma directFirstReturnBeforeExitEvent_preimage_prodMk
    {Ω' : Type*} [MeasurableSpace Ω'] (Z : ℕ → Ω' → ℤ) (m : ℕ+) :
    (fun ω : Ω' ↦ ((0 : ℤ), ω)) ⁻¹'
        {s | (τ_[productStartRandomWalk Z, 0]^1) s <
            intervalExitTime (productStartRandomWalk Z) m s} =
      directFirstReturnBeforeExitEvent Z m := by
  ext ω
  exact canonicalFirstReturnBeforeExit_event_comp_prodMk (Z := Z) (m := m) (ω := ω)

/-- Helper for Theorem 17.40: under the deterministic start `0`, the product-start probability of
the bounded first-return event is exactly the direct-event probability on the increment space. -/
private lemma productStartRandomWalkMeasure_real_firstReturnBeforeExit_eq_direct
    {Ω' : Type*} [MeasurableSpace Ω'] (Qprob : ProbabilityMeasure Ω') (Z : ℕ → Ω' → ℤ) (m : ℕ+) :
    (productStartRandomWalkMeasure Qprob 0 : Measure (ℤ × Ω')).real
        {s | (τ_[productStartRandomWalk Z, 0]^1) s <
            intervalExitTime (productStartRandomWalk Z) m s} =
      (Qprob : Measure Ω').real (directFirstReturnBeforeExitEvent Z m) := by
  let hprodMk : MeasurableEmbedding (fun ω : Ω' ↦ ((0 : ℤ), ω)) :=
    MeasurableEmbedding.prodMk_left (x := (0 : ℤ)) (f := id) MeasurableEmbedding.id
  -- Proof comment: the deterministic-start product law is the pushforward along
  -- `ω ↦ (0, ω)`, so the bounded first-return event is measured on the increment space by
  -- pulling it back through that embedding.
  rw [productStartRandomWalkMeasure_zero_eq_map Qprob, Measure.real_def, Measure.real_def,
    MeasurableEmbedding.map_apply hprodMk (Qprob : Measure Ω')
      {s | (τ_[productStartRandomWalk Z, 0]^1) s <
          intervalExitTime (productStartRandomWalk Z) m s}]
  exact congrArg ENNReal.toReal
    (congrArg ((Qprob : Measure Ω'))
      (directFirstReturnBeforeExitEvent_preimage_prodMk (Z := Z) (m := m)))

/-- Helper for Theorem 17.40: returning to `0` before leaving `(-(m : ℤ), m)` forces the first
increment to stay inside that interval. -/
private lemma canonicalFirstReturnBeforeExit_implies_firstIncrement_natAbs_lt
    {Ω' : Type*} [MeasurableSpace Ω'] (Z : ℕ → Ω' → ℤ) (m : ℕ+) (ω : Ω')
    (hω : (τ_[productStartRandomWalk Z, 0]^1) ((0 : ℤ), ω) <
      intervalExitTime (productStartRandomWalk Z) m ((0 : ℤ), ω)) :
    Int.natAbs (Z 0 ω) < m := by
  have hτ_ge : (1 : ℕ∞) ≤ (τ_[productStartRandomWalk Z, 0]^1) ((0 : ℤ), ω) := by
    simpa [iteratedEntranceTime_one] using
      (le_hittingAfter (u := productStartRandomWalk Z) (s := ({0} : Set ℤ)) (n := 1)
        ((0 : ℤ), ω))
  by_contra hstep
  have hstep_mem : m ≤ Int.natAbs (Z 0 ω) := Nat.le_of_not_lt hstep
  have hExit_le_one :
      intervalExitTime (productStartRandomWalk Z) m ((0 : ℤ), ω) ≤ 1 := by
    -- Proof comment: if the first increment already lands outside the interval, the exit time is
    -- at most `1`.
    refine MeasureTheory.hittingAfter_le_of_mem
      (u := productStartRandomWalk Z) (s := {z : ℤ | m ≤ Int.natAbs z})
      (n := 0) (i := 1) (ω := ((0 : ℤ), ω)) (by simp) ?_
    simpa [productStartRandomWalk_succ, productStartRandomWalk_zero] using hstep_mem
  exact (not_lt_of_ge (hExit_le_one.trans hτ_ge)) hω

/-- Helper for Theorem 17.40: the direct increment-space first-return event also forces the first
increment to stay inside `(-(m : ℤ), m)`. -/
private lemma directFirstReturnBeforeExitEvent_subset_smallFirstIncrement
    {Ω' : Type*} [MeasurableSpace Ω'] (Z : ℕ → Ω' → ℤ) (m : ℕ+) :
    directFirstReturnBeforeExitEvent Z m ⊆ {ω | Int.natAbs (Z 0 ω) < m} := by
  intro ω hω
  -- Proof comment: transport the direct event to the product-start realization at `(0, ω)` and
  -- apply the already proved first-step restriction there.
  exact canonicalFirstReturnBeforeExit_implies_firstIncrement_natAbs_lt
    (Z := Z) (m := m) (ω := ω)
    ((canonicalFirstReturnBeforeExit_event_comp_prodMk (Z := Z) (m := m) (ω := ω)).2 hω)

/-- Helper for Theorem 17.40: a single increment leaves `(-(m : ℤ), m)` with probability at most
its first absolute moment divided by `m`. -/
private lemma firstIncrementLeavesInterval_prob_le_meanAbs_div
    (ν : ProbabilityMeasure ℤ)
    (hν_integrable : Integrable (fun z : ℤ ↦ (z : ℝ)) (ν : Measure ℤ))
    {Ω' : Type*} [MeasurableSpace Ω'] (Qprob : ProbabilityMeasure Ω') (Z : ℕ → Ω' → ℤ)
    (hZ_law : ∀ n : ℕ, HasLaw (Z n) (ν : Measure ℤ) (Qprob : Measure Ω'))
    (m : ℕ+) :
    (Qprob : Measure Ω').real {ω | m ≤ Int.natAbs (Z 0 ω)} ≤
      (∫ z, |(z : ℝ)| ∂(ν : Measure ℤ)) / m := by
  have hm_pos : 0 < (m : ℝ) := by
    exact_mod_cast m.pos
  have habs_integrable : Integrable (fun z : ℤ ↦ |(z : ℝ)|) (ν : Measure ℤ) :=
    hν_integrable.norm
  have habs_nonneg :
      0 ≤ᵐ[(ν : Measure ℤ)] fun z : ℤ ↦ |(z : ℝ)| := by
    exact Filter.Eventually.of_forall fun _ ↦ abs_nonneg _
  have hmarkov :
      (ν : Measure ℤ) {z : ℤ | (m : ℝ) ≤ |(z : ℝ)|} ≤
        (∫⁻ z, ENNReal.ofReal |(z : ℝ)| ∂(ν : Measure ℤ)) / ENNReal.ofReal (m : ℝ) := by
    -- Proof comment: this is Markov's inequality for the nonnegative random variable `|Z₀|`.
    have hmarkov0 :
        (ν : Measure ℤ) {z : ℤ | (m : NNReal) ≤ ‖(z : ℝ)‖₊} ≤
          (∫⁻ z, (((‖(z : ℝ)‖₊ : NNReal) : ℝ≥0∞)) ∂(ν : Measure ℤ)) /
            ((m : NNReal) : ℝ≥0∞) := by
      exact
        markov_inequality_of_monotone
          (μ := (ν : Measure ℤ))
          (X := fun z : ℤ ↦ (z : ℝ))
          (f := fun x : NNReal ↦ x)
          (ε := (m : NNReal))
          (hX := measurable_of_countable (fun z : ℤ ↦ (z : ℝ)))
          (hf := fun ⦃a b⦄ hab ↦ hab)
          (hfε := by
            change (0 : NNReal) < (m : NNReal)
            exact_mod_cast m.pos)
    calc
      (ν : Measure ℤ) {z : ℤ | (m : ℝ) ≤ |(z : ℝ)|}
          = (ν : Measure ℤ) {z : ℤ | (m : NNReal) ≤ ‖(z : ℝ)‖₊} := by
            refine congrArg (fun s : Set ℤ ↦ (ν : Measure ℤ) s) ?_
            ext z
            constructor <;> intro hz
            · change ((m : NNReal) : ℝ) ≤ ((‖(z : ℝ)‖₊ : NNReal) : ℝ)
              simpa [Real.norm_eq_abs] using hz
            · change ((m : NNReal) : ℝ) ≤ ((‖(z : ℝ)‖₊ : NNReal) : ℝ) at hz
              simpa [Real.norm_eq_abs] using hz
      _ ≤
          (∫⁻ z, (((‖(z : ℝ)‖₊ : NNReal) : ℝ≥0∞)) ∂(ν : Measure ℤ)) /
            ((m : NNReal) : ℝ≥0∞) := hmarkov0
      _ =
          (∫⁻ z, ENNReal.ofReal |(z : ℝ)| ∂(ν : Measure ℤ)) / ENNReal.ofReal (m : ℝ) := by
            have hlintegral :
                (∫⁻ z, (((‖(z : ℝ)‖₊ : NNReal) : ℝ≥0∞)) ∂(ν : Measure ℤ)) =
                  ∫⁻ z, ENNReal.ofReal |(z : ℝ)| ∂(ν : Measure ℤ) := by
              refine lintegral_congr_ae ?_
              exact Filter.Eventually.of_forall fun z ↦ by
                simpa [Real.norm_eq_abs] using (ofReal_norm_eq_enorm (z : ℝ)).symm
            rw [hlintegral]
            simp
  have hpush :
      (Qprob : Measure Ω') {ω | (m : ℝ) ≤ |(Z 0 ω : ℝ)|} =
        (ν : Measure ℤ) {z : ℤ | (m : ℝ) ≤ |(z : ℝ)|} := by
    -- Proof comment: push the threshold event through the law of `Z 0`.
    calc
      (Qprob : Measure Ω') {ω | (m : ℝ) ≤ |(Z 0 ω : ℝ)|} =
          Measure.map (Z 0) (Qprob : Measure Ω') {z : ℤ | (m : ℝ) ≤ |(z : ℝ)|} := by
            symm
            simpa using
              (Measure.map_apply_of_aemeasurable
                ((hZ_law 0).aemeasurable) (measurableSet_setOf.2 <| by fun_prop))
      _ = (ν : Measure ℤ) {z : ℤ | (m : ℝ) ≤ |(z : ℝ)|} := by
            rw [(hZ_law 0).map_eq]
  have hbound :
      (Qprob : Measure Ω') {ω | (m : ℝ) ≤ |(Z 0 ω : ℝ)|} ≤
        ENNReal.ofReal ((∫ z, |(z : ℝ)| ∂(ν : Measure ℤ)) / m) := by
    calc
      (Qprob : Measure Ω') {ω | (m : ℝ) ≤ |(Z 0 ω : ℝ)|}
          = (ν : Measure ℤ) {z : ℤ | (m : ℝ) ≤ |(z : ℝ)|} := hpush
      _ ≤ (∫⁻ z, ENNReal.ofReal |(z : ℝ)| ∂(ν : Measure ℤ)) / ENNReal.ofReal (m : ℝ) := hmarkov
      _ = ENNReal.ofReal ((∫ z, |(z : ℝ)| ∂(ν : Measure ℤ)) / m) := by
            rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal habs_integrable habs_nonneg,
              ENNReal.ofReal_div_of_pos hm_pos]
  -- Proof comment: convert the `ℝ≥0∞` tail bound back to the real-valued probability notation.
  rw [Measure.real_def]
  have hratio_nonneg : 0 ≤ (∫ z, |(z : ℝ)| ∂(ν : Measure ℤ)) / m := by
    exact div_nonneg (integral_nonneg fun _ ↦ abs_nonneg _) hm_pos.le
  refine
    (show ((Qprob : Measure Ω') {ω | m ≤ Int.natAbs (Z 0 ω)}).toReal ≤
        (∫ z, |(z : ℝ)| ∂(ν : Measure ℤ)) / m from ?_)
  have hevent :
      ((Qprob : Measure Ω') {ω | m ≤ Int.natAbs (Z 0 ω)}).toReal =
        ((Qprob : Measure Ω') {ω | (m : ℝ) ≤ |(Z 0 ω : ℝ)|}).toReal := by
    refine congrArg ENNReal.toReal ?_
    congr
    ext ω
    have hω :
        m ≤ Int.natAbs (Z 0 ω) ↔
          (m : ℝ) ≤ (((Z 0 ω).natAbs : ℕ) : ℝ) := by
      exact_mod_cast (show m ≤ Int.natAbs (Z 0 ω) ↔ m ≤ Int.natAbs (Z 0 ω) by rfl)
    simpa [Nat.cast_natAbs, Int.cast_abs] using hω
  rw [hevent]
  refine ENNReal.toReal_le_of_le_ofReal hratio_nonneg ?_
  exact hbound

/-- Helper for Theorem 17.40: equivalently, the first increment stays inside `(-(m : ℤ), m)`
with probability at least `1 - (∫ |z| dν) / m`. -/
private lemma firstIncrementStaysInInterval_prob_ge_one_sub_meanAbs_div
    (ν : ProbabilityMeasure ℤ)
    (hν_integrable : Integrable (fun z : ℤ ↦ (z : ℝ)) (ν : Measure ℤ))
    {Ω' : Type*} [MeasurableSpace Ω'] (Qprob : ProbabilityMeasure Ω') (Z : ℕ → Ω' → ℤ)
    (hZ_law : ∀ n : ℕ, HasLaw (Z n) (ν : Measure ℤ) (Qprob : Measure Ω'))
    (m : ℕ+) :
    1 - (∫ z, |(z : ℝ)| ∂(ν : Measure ℤ)) / m ≤
      (Qprob : Measure Ω').real {ω | Int.natAbs (Z 0 ω) < m} := by
  have hlargeStep :
      (Qprob : Measure Ω').real {ω | m ≤ Int.natAbs (Z 0 ω)} ≤
        (∫ z, |(z : ℝ)| ∂(ν : Measure ℤ)) / m :=
    firstIncrementLeavesInterval_prob_le_meanAbs_div
      (ν := ν) hν_integrable Qprob Z hZ_law m
  let A : Set Ω' := {ω | (m : ℝ) ≤ |(Z 0 ω : ℝ)|}
  have hlarge_eq : {ω | m ≤ Int.natAbs (Z 0 ω)} = A := by
    ext ω
    have hω :
        m ≤ Int.natAbs (Z 0 ω) ↔
          (m : ℝ) ≤ (((Z 0 ω).natAbs : ℕ) : ℝ) := by
      exact_mod_cast
        (show m ≤ Int.natAbs (Z 0 ω) ↔ m ≤ Int.natAbs (Z 0 ω) by rfl)
    simpa [A, Nat.cast_natAbs, Int.cast_abs] using hω
  have hsmall_eq : {ω | Int.natAbs (Z 0 ω) < m} = Aᶜ := by
    ext ω
    have hω :
        m ≤ Int.natAbs (Z 0 ω) ↔
          (m : ℝ) ≤ (((Z 0 ω).natAbs : ℕ) : ℝ) := by
      exact_mod_cast
        (show m ≤ Int.natAbs (Z 0 ω) ↔ m ≤ Int.natAbs (Z 0 ω) by rfl)
    simpa [A, Nat.not_le, Nat.cast_natAbs, Int.cast_abs] using (not_congr hω)
  have hcast_aemeas :
      AEMeasurable (fun ω ↦ (Z 0 ω : ℝ)) (Qprob : Measure Ω') := by
    exact
      ((measurable_of_countable (f := fun z : ℤ ↦ (z : ℝ))).aemeasurable).comp_aemeasurable
        (hZ_law 0).aemeasurable
  have hA_null : NullMeasurableSet A (Qprob : Measure Ω') :=
    nullMeasurableSet_le aemeasurable_const hcast_aemeas.abs
  have hlargeStepA :
      (Qprob : Measure Ω').real A ≤ (∫ z, |(z : ℝ)| ∂(ν : Measure ℤ)) / m := by
    simpa [hlarge_eq] using hlargeStep
  have hcompl :
      (Qprob : Measure Ω').real {ω | Int.natAbs (Z 0 ω) < m} =
        1 - (Qprob : Measure Ω').real A := by
    rw [hsmall_eq, MeasureTheory.measureReal_compl₀ (μ := (Qprob : Measure Ω')) hA_null,
      probReal_univ]
  linarith

/-- Helper for Theorem 17.40: the real-cast integer walk agrees with the partial sums of the
real-cast increments. -/
private lemma partialSum_intCast_eq_randomWalkProcess
    {Ω' : Type*} [MeasurableSpace Ω'] (Z : ℕ → Ω' → ℤ) :
    ∀ n ω, partialSum (fun k ω' ↦ (Z k ω' : ℝ)) n ω = (randomWalkProcess Z n ω : ℝ) := by
  intro n ω
  -- Proof comment: both sides are the same finite sum; the right-hand side is just written in
  -- the integer-walk notation before casting to `ℝ`.
  rw [partialSum_apply, randomWalkProcess_apply]
  exact_mod_cast rfl

/-- Helper for Theorem 17.40: Example 10.6 turns centered i.i.d. real-cast increments into a
martingale for their partial-sum filtration. -/
private lemma canonicalDirectWalk_martingale
    (ν : ProbabilityMeasure ℤ)
    (hν_integrable : Integrable (fun z : ℤ ↦ (z : ℝ)) (ν : Measure ℤ))
    (hν_mean_zero : ∫ z, (z : ℝ) ∂(ν : Measure ℤ) = 0)
    {Ω' : Type*} [MeasurableSpace Ω'] (Qprob : ProbabilityMeasure Ω') (Z : ℕ → Ω' → ℤ)
    (hZ_meas : ∀ n : ℕ, Measurable (Z n))
    (hZ_indep : iIndepFun Z (Qprob : Measure Ω'))
    (hZ_law : ∀ n : ℕ, HasLaw (Z n) (ν : Measure ℤ) (Qprob : Measure Ω')) :
    let stepReal : ℕ → Ω' → ℝ := fun n ω ↦ (Z n ω : ℝ)
    let S : ℕ → Ω' → ℝ := partialSum stepReal
    let hS_strMeas :
        ∀ n, StronglyMeasurable (S n) :=
      fun n ↦ (partialSum_measurable stepReal
        (fun k ↦ (measurable_of_countable (f := fun z : ℤ ↦ (z : ℝ))).comp (hZ_meas k))
        n).stronglyMeasurable
    let ℱS : Filtration ℕ ‹MeasurableSpace Ω'› := Filtration.natural S hS_strMeas
    Martingale S ℱS (Qprob : Measure Ω') := by
  let stepReal : ℕ → Ω' → ℝ := fun n ω ↦ (Z n ω : ℝ)
  let S : ℕ → Ω' → ℝ := partialSum stepReal
  let hS_strMeas :
      ∀ n, StronglyMeasurable (S n) :=
    fun n ↦ (partialSum_measurable stepReal
      (fun k ↦ (measurable_of_countable (f := fun z : ℤ ↦ (z : ℝ))).comp (hZ_meas k))
      n).stronglyMeasurable
  let ℱS : Filtration ℕ ‹MeasurableSpace Ω'› := Filtration.natural S hS_strMeas
  have hcast_meas : Measurable (fun z : ℤ ↦ (z : ℝ)) :=
    measurable_of_countable (f := fun z : ℤ ↦ (z : ℝ))
  have hstepReal_meas : ∀ n, Measurable (stepReal n) := by
    intro n
    -- Proof comment: the increment coordinate is measurable after composing the measurable cast
    -- `ℤ → ℝ` with the countable-valued increment.
    exact hcast_meas.comp (hZ_meas n)
  have hstepReal_indep : iIndepFun stepReal (Qprob : Measure Ω') := by
    -- Proof comment: independence survives the measurable cast from `ℤ` to `ℝ`.
    simpa [stepReal] using hZ_indep.comp (fun _ z ↦ (z : ℝ)) (fun _ ↦ hcast_meas)
  have hstepReal_int : ∀ n, Integrable (stepReal n) (Qprob : Measure Ω') := by
    intro n
    -- Proof comment: the step law `ν` already has finite first moment, so the real-cast increment
    -- is integrable under the increment measure as well.
    have hmap_int :
        Integrable (fun z : ℤ ↦ (z : ℝ)) (Measure.map (Z n) (Qprob : Measure Ω')) := by
      simpa [(hZ_law n).map_eq] using hν_integrable
    exact
      (MeasureTheory.integrable_map_measure
        (μ := (Qprob : Measure Ω'))
        (f := Z n)
        (g := fun z : ℤ ↦ (z : ℝ))
        hcast_meas.aestronglyMeasurable
        (hZ_law n).aemeasurable).1 hmap_int
  have hstepReal_mean_zero : ∀ n, (Qprob : Measure Ω')[stepReal n] = 0 := by
    intro n
    -- Proof comment: `HasLaw.integral_comp` rewrites the increment expectation to the mean of
    -- `ν`, which vanishes by hypothesis.
    calc
      (Qprob : Measure Ω')[stepReal n] = ∫ z, (z : ℝ) ∂(ν : Measure ℤ) := by
        simpa [stepReal, Function.comp] using
          (hZ_law n).integral_comp (f := fun z : ℤ ↦ (z : ℝ))
            hcast_meas.aestronglyMeasurable
      _ = 0 := hν_mean_zero
  -- Proof comment: Example 10.6 closes the martingale proof once the cast increments are
  -- measurable, integrable, centered, and independent.
  simpa [stepReal, S, ℱS, hS_strMeas] using
    (independentCenteredPartialSums_martingale
      (Y := stepReal) (μ := (Qprob : Measure Ω')) (hY_meas := hstepReal_meas)
      hstepReal_int hstepReal_mean_zero hstepReal_indep)

/-- Helper for Theorem 17.40: a one-dimensional zero-drift walk with finite first moment has
infinite diagonal Green value at the origin. -/
private lemma integerRandomWalk_greenFunction_zero_zero_eq_top_of_integrable_mean_zero
    (ν : ProbabilityMeasure ℤ)
    (hν_integrable : Integrable (fun z : ℤ ↦ (z : ℝ)) (ν : Measure ℤ))
    (hν_mean_zero : ∫ z, (z : ℝ) ∂(ν : Measure ℤ) = 0)
    {P : ℤ → ProbabilityMeasure Ω} {X : ℕ → Ω → ℤ}
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ dirac_convolution_kernel (ν : Measure ℤ) ^ n) P X] :
    (G[P, X]) (0 : ℤ) 0 = ⊤ := by
  let p : ℤ → ℤ → ℝ≥0∞ := convolutionStepMatrix ν
  have hp_stochastic : IsStochasticMatrix p :=
    convolutionStepMatrix_isStochastic ν
  have hp_translation : IsTranslationInvariantStepMatrix p :=
    convolutionStepMatrix_isTranslationInvariant ν
  have horiginRow : discreteMatrixKernel p 0 = (ν : Measure ℤ) :=
    convolutionStepMatrix_originRow_eq ν
  let _ : IsMarkovKernel (discreteMatrixKernel p) :=
    discreteMatrixKernel_isMarkovKernel p hp_stochastic
  obtain ⟨Ω', hΩ', Q, Zlift, hZ_meas, hZ_law, hZ_indep, hQ_prob⟩ :
      ∃ Ω' : Type, ∃ _ : MeasurableSpace Ω', ∃ Q : Measure Ω', ∃ Zlift : ULift ℕ → Ω' → ℤ,
        (∀ i : ULift ℕ, Measurable (Zlift i)) ∧
          (∀ i : ULift ℕ, HasLaw (Zlift i) (ν : Measure ℤ) Q) ∧
          iIndepFun Zlift Q ∧ IsProbabilityMeasure Q := by
    simpa using ProbabilityTheory.exists_iid (ULift ℕ) (ν : Measure ℤ)
  let Qprob : ProbabilityMeasure Ω' := ⟨Q, hQ_prob⟩
  let Z : ℕ → Ω' → ℤ := fun n ω ↦ Zlift ⟨n⟩ ω
  have hZ_meas' : ∀ n : ℕ, Measurable (Z n) := by
    intro n
    simpa [Z] using hZ_meas ⟨n⟩
  have hZ_law' : ∀ n : ℕ, HasLaw (Z n) (discreteMatrixKernel p 0) (Qprob : Measure Ω') := by
    intro n
    simpa [Z, Qprob, horiginRow] using hZ_law ⟨n⟩
  have hZ_indep' : iIndepFun Z (Qprob : Measure Ω') := by
    simpa [Z, Qprob] using
      hZ_indep.precomp (g := fun n : ℕ ↦ (⟨n⟩ : ULift ℕ)) (by
        intro i j hij
        simpa using congrArg ULift.down hij)
  have hZ_law_nu : ∀ n : ℕ, HasLaw (Z n) (ν : Measure ℤ) (Qprob : Measure Ω') := by
    intro n
    simpa [Z, Qprob] using hZ_law ⟨n⟩
  let hdisc :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel p ^ n)
        (productStartRandomWalkMeasure Qprob)
        (productStartRandomWalk Z) :=
    productStartRandomWalk_isMarkovProcessRealization
      p hp_stochastic hp_translation Qprob Z hZ_meas' hZ_indep' hZ_law'
  let hconv :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ dirac_convolution_kernel (ν : Measure ℤ) ^ n)
        (productStartRandomWalkMeasure Qprob)
        (productStartRandomWalk Z) := by
    simpa [p, convolutionStepMatrixKernel_eq ν] using hdisc
  letI :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ dirac_convolution_kernel (ν : Measure ℤ) ^ n)
        (productStartRandomWalkMeasure Qprob)
        (productStartRandomWalk Z) := hconv
  have hintervalSum :
      ∀ N L : ℕ,
        (∑ k ∈ Finset.range (N + 1),
          ((dirac_convolution_kernel (ν : Measure ℤ) ^ k) (0 : ℤ))
            ((Finset.Icc (-(L : ℤ)) L : Finset ℤ) : Set ℤ)) ≤
          (2 * L + 1 : ℝ≥0∞) *
            ∑ k ∈ Finset.range (N + 1),
              ((dirac_convolution_kernel (ν : Measure ℤ) ^ k) (0 : ℤ)) ({0} : Set ℤ) := by
    intro N L
    -- Proof comment: this is the finite-window averaging inequality from the source proof, now
    -- packaged in canonical kernel language for the product-start walk.
    exact intervalMass_sum_le_card_mul_truncatedGreenSelf
      (ν := ν) Qprob Z N L
  let originMass : ℕ → ℝ≥0∞ :=
    fun k ↦ ((dirac_convolution_kernel (ν : Measure ℤ) ^ k) (0 : ℤ)) ({0} : Set ℤ)
  -- Proof comment: rewrite the diagonal Green value as the origin singleton-mass series and argue
  -- by contradiction from a hypothetical finite total mass.
  rw [integerWalk_greenFunction_zero_zero_eq_tsum_originMass (ν := ν) (P := P) (X := X)]
  by_contra htsum_ne_top
  obtain ⟨M, hM⟩ := ENNReal.exists_nat_gt htsum_ne_top
  let m : ℕ+ := ⟨8 * M + 1, by positivity⟩
  have hm_nat : (m : ℕ) = 8 * M + 1 := rfl
  have hsmall_eventually :
      ∀ᶠ k in atTop,
        (1 / 2 : ℝ) ≤
          (productStartRandomWalkMeasure Qprob 0 : Measure (ℤ × Ω')).real
            {s | |(productStartRandomWalk Z k s : ℝ)| ≤ (k : ℝ) / m} :=
    canonicalWalk_smallDeviation_measure_eventually_ge_half
      (ν := ν) hν_integrable hν_mean_zero Qprob Z hZ_meas' hZ_indep' hZ_law_nu m
  rcases Filter.mem_atTop_sets.1 hsmall_eventually with ⟨K, hK⟩
  let L : ℕ := K + 2 * M
  have hL_def : L = K + 2 * M := rfl
  have hKL : K ≤ m * L := by
    change K ≤ (m : ℕ) * L
    have hK_le_L : K ≤ L := by
      rw [hL_def]
      omega
    have hm_ge_one : 1 ≤ (m : ℕ) := by
      rw [hm_nat]
      omega
    exact hK_le_L.trans <| by
      simpa using (Nat.mul_le_mul_right L hm_ge_one)
  let partialWindow : ℝ≥0∞ :=
    ∑ k ∈ Finset.range (m * L + 1),
      ((dirac_convolution_kernel (ν : Measure ℤ) ^ k) (0 : ℤ))
        ((Finset.Icc (-(L : ℤ)) L : Finset ℤ) : Set ℤ)
  let partialOrigin : ℝ≥0∞ :=
    ∑ k ∈ Finset.range (m * L + 1), originMass k
  have hwindowLower :
      ((m * L + 1 - K : ℝ) / 2) ≤ partialWindow.toReal := by
    -- Proof comment: the small-deviation tail contributes at least `1 / 2` on each of the tail
    -- times `K, …, mL`, and each such event lies inside the fixed interval window.
    simpa [partialWindow] using
      intervalMass_real_lowerBound_of_smallDeviation
        (ν := ν) (Qprob := Qprob) (Z := Z) (m := m) (K := K) (L := L) hK hKL
  have hwindowUpper :
      partialWindow ≤ (2 * L + 1 : ℝ≥0∞) * partialOrigin := by
    -- Proof comment: this is the finite-window averaging inequality specialized to the same time
    -- horizon `mL`.
    simpa [partialWindow, partialOrigin, originMass] using hintervalSum (m * L) L
  have hpartial_le_tsum : partialOrigin ≤ ∑' n : ℕ, originMass n := by
    dsimp [partialOrigin]
    exact ENNReal.sum_le_tsum (Finset.range (m * L + 1))
  have hpartial_ne_top : partialOrigin ≠ ⊤ :=
    ne_top_of_le_ne_top htsum_ne_top hpartial_le_tsum
  have htsum_real_lt_M : (∑' n : ℕ, originMass n).toReal < M := by
    simpa using
      (ENNReal.toReal_lt_toReal htsum_ne_top (by simp : (M : ℝ≥0∞) ≠ ⊤)).mpr hM
  have hpartial_real_lt_M : partialOrigin.toReal < M := by
    exact lt_of_le_of_lt (ENNReal.toReal_mono htsum_ne_top hpartial_le_tsum) htsum_real_lt_M
  have hwindowUpperReal :
      partialWindow.toReal ≤ (2 * L + 1 : ℝ) * partialOrigin.toReal := by
    have hcoeff_ne_top : (2 * L + 1 : ℝ≥0∞) ≠ ⊤ := by
      simpa using ENNReal.natCast_ne_top (2 * L + 1)
    have hupperReal :=
      ENNReal.toReal_mono (ENNReal.mul_ne_top hcoeff_ne_top hpartial_ne_top) hwindowUpper
    have hcoeff_toReal : ((2 * L + 1 : ℝ≥0∞)).toReal = (2 * L + 1 : ℝ) := by
      simpa using ENNReal.toReal_natCast (2 * L + 1)
    calc
      partialWindow.toReal ≤ (((2 * L + 1 : ℝ≥0∞) * partialOrigin)).toReal := hupperReal
      _ = ((2 * L + 1 : ℝ≥0∞)).toReal * partialOrigin.toReal := by
            rw [ENNReal.toReal_mul]
      _ = (2 * L + 1 : ℝ) * partialOrigin.toReal := by
            rw [hcoeff_toReal]
  have hcoeff_pos : 0 < (2 * L + 1 : ℝ) := by
    positivity
  have hwindow_lt_bound :
      partialWindow.toReal < (2 * L + 1 : ℝ) * M := by
    exact lt_of_le_of_lt hwindowUpperReal (mul_lt_mul_of_pos_left hpartial_real_lt_M hcoeff_pos)
  have hstrict_bound :
      ((2 * L + 1 : ℝ) * M) < ((m * L + 1 - K : ℝ) / 2) := by
    rw [hm_nat, hL_def]
    have hdiff :
        (((((8 * M + 1 : ℕ) : ℝ) * ↑(K + 2 * M) + 1 - ↑K) / 2) -
            ((2 * ↑(K + 2 * M) + 1 : ℝ) * M)) =
          (1 / 2 : ℝ) + 2 * (M : ℝ) * K + 4 * (M : ℝ) ^ 2 := by
      norm_num [Nat.cast_add, Nat.cast_mul]
      ring
    have haux :
        0 <
          ((((8 * M + 1 : ℕ) : ℝ) * ↑(K + 2 * M) + 1 - ↑K) / 2) -
            ((2 * ↑(K + 2 * M) + 1 : ℝ) * M) := by
      rw [hdiff]
      positivity
    exact sub_pos.mp haux
  -- Proof comment: the lower window estimate and the averaging upper bound now force the same
  -- real quantity to be simultaneously larger and smaller than `(2L + 1) M`.
  have : ((2 * L + 1 : ℝ) * M) < ((2 * L + 1 : ℝ) * M) := by
    exact lt_trans hstrict_bound (lt_of_le_of_lt hwindowLower hwindow_lt_bound)
  exact (lt_irrefl ((2 * L + 1 : ℝ) * M)) this

/-- Helper for Theorem 17.40: a one-dimensional random walk on `ℤ` with finite first moment and
mean-zero increment law is recurrent. -/
private theorem integerRandomWalk_recurrent_of_integrable_mean_zero
    (ν : ProbabilityMeasure ℤ)
    (hν_integrable : Integrable (fun z : ℤ ↦ (z : ℝ)) (ν : Measure ℤ))
    (hν_mean_zero : ∫ z, (z : ℝ) ∂(ν : Measure ℤ) = 0)
    {P : ℤ → ProbabilityMeasure Ω} {X : ℕ → Ω → ℤ}
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ dirac_convolution_kernel (ν : Measure ℤ) ^ n) P X] :
    IsRecurrentMarkovChain P X := by
  have hgreen0 :
      (G[P, X]) (0 : ℤ) 0 = ⊤ :=
    integerRandomWalk_greenFunction_zero_zero_eq_top_of_integrable_mean_zero
      (P := P) (X := X) (ν := ν) hν_integrable hν_mean_zero
  -- Proof comment: once the origin Green function diverges, translation invariance propagates
  -- recurrence from `0` to every state.
  exact integerRandomWalk_recurrentState_of_origin (ν := ν) (P := P) (X := X) hgreen0

/-- Theorem 17.40: a one-dimensional random walk on `ℤ` with step law `ν` and finite first moment
is recurrent exactly when the drift of `ν` vanishes. -/
theorem integerRandomWalk_recurrent_iff_zero_stepLawMean
    (ν : ProbabilityMeasure ℤ) (P : ℤ → ProbabilityMeasure Ω) (X : ℕ → Ω → ℤ)
    (hfirstMoment : Integrable (fun z : ℤ ↦ (z : ℝ)) (ν : Measure ℤ))
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ dirac_convolution_kernel (ν : Measure ℤ) ^ n) P X] :
    IsRecurrentMarkovChain P X ↔ ∫ z, (z : ℝ) ∂(ν : Measure ℤ) = 0 := by
  constructor
  · intro hrec
    by_contra hmean_ne_zero
    exact
      (integerRandomWalk_not_recurrent_of_integrable_mean_ne_zero
        (ν := ν) hfirstMoment hmean_ne_zero P X) hrec
  · intro hmean_zero
    exact integerRandomWalk_recurrent_of_integrable_mean_zero
      (P := P) (X := X) (ν := ν) hfirstMoment hmean_zero

end ProbabilityTheory
