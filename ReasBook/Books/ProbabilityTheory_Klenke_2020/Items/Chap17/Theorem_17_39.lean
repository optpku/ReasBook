/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Lemma_2_40
import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Exercise_2_2_3
import Books.ProbabilityTheory_Klenke_2020.Items.Chap03.Example_3_4
import Books.ProbabilityTheory_Klenke_2020.Items.Chap03.Lemma_3_5
import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Example_5_9
import Books.ProbabilityTheory_Klenke_2020.Items.Chap07.Exercise_7_4_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Definition_9_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Example_9_8
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Lemma_14_27
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_16
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_30
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_33
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_42
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Example_17_18
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Exercise_17_5_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_17
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_29
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_38
import Mathlib

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory unitInterval

noncomputable section

universe u v

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

section LatticeWalk

variable (D : ℕ) (P : LatticePoint D → ProbabilityMeasure Ω) (X : ℕ → Ω → LatticePoint D)

/-- Helper for Theorem 17.39: composing a lattice translation kernel with a measure is the same
as convolving that measure with the common step law. -/
private lemma latticeDiracConvolutionKernel_comp_measure_eq_conv
    (μ ν : Measure (LatticePoint D)) [SFinite μ] [SFinite ν] :
    dirac_convolution_kernel ν ∘ₘ μ = μ ∗ ν := by
  have hconst :=
    congrArg
      (fun κ : Kernel (LatticePoint D) (LatticePoint D) ↦ κ (0 : LatticePoint D))
      (dirac_convolution_kernel_comp_const_eq_const_conv (μ := μ) (ν := ν))
  simpa [Kernel.comp_apply] using hconst

/-- Helper for Theorem 17.39: after `n` steps, the row of a lattice convolution kernel is the
translate of the origin-started `n`-step law. -/
lemma latticeKernelPow_apply_eq_diracConv_originLaw
    (ν : PMF (LatticePoint D)) (n : ℕ) (x : LatticePoint D) :
    ((dirac_convolution_kernel ν.toMeasure ^ n) x) =
      Measure.dirac x ∗
        ((dirac_convolution_kernel ν.toMeasure ^ n) (0 : LatticePoint D)) := by
  induction n with
  | zero =>
      -- Proof comment: at time `0`, the kernel row is the starting Dirac mass.
      change Measure.dirac x = Measure.dirac x ∗ Measure.dirac (0 : LatticePoint D)
      simp
  | succ n ih =>
      let κ : Kernel (LatticePoint D) (LatticePoint D) := dirac_convolution_kernel ν.toMeasure
      have hpow : κ ^ (n + 1) = κ ∘ₖ (κ ^ n) := by
        simpa [pow_one, Nat.one_add] using (ProbabilityTheory.Kernel.pow_add κ 1 n)
      -- Proof comment: evolve the translated `n`-step origin law by one more convolution step
      -- and reassociate the resulting convolution product.
      calc
        (κ ^ (n + 1)) x = κ ∘ₘ ((κ ^ n) x) := by
          rw [hpow, Kernel.comp_apply]
        _ = ((κ ^ n) x) ∗ ν.toMeasure := by
          simpa [κ] using
            (latticeDiracConvolutionKernel_comp_measure_eq_conv
              (μ := (κ ^ n) x) (ν := ν.toMeasure))
        _ = (Measure.dirac x ∗ ((κ ^ n) (0 : LatticePoint D))) ∗ ν.toMeasure := by
          rw [ih]
        _ = Measure.dirac x ∗ (((κ ^ n) (0 : LatticePoint D)) ∗ ν.toMeasure) := by
          rw [Measure.conv_assoc]
        _ = Measure.dirac x ∗ ((κ ^ (n + 1)) (0 : LatticePoint D)) := by
          congr 1
          calc
            ((κ ^ n) (0 : LatticePoint D)) ∗ ν.toMeasure = κ ∘ₘ ((κ ^ n) (0 : LatticePoint D)) := by
              symm
              simpa [κ] using
                (latticeDiracConvolutionKernel_comp_measure_eq_conv
                  (μ := (κ ^ n) (0 : LatticePoint D)) (ν := ν.toMeasure))
            _ = (κ ∘ₖ (κ ^ n)) (0 : LatticePoint D) := by
              rw [Kernel.comp_apply]
            _ = (κ ^ (n + 1)) (0 : LatticePoint D) := by
              rw [← hpow]

/-- Helper for Theorem 17.39: the `n`-step return mass at a lattice point equals the origin
return mass for the same convolution-kernel walk. -/
lemma latticeKernelPow_apply_singleton_self_eq_originMass
    (ν : PMF (LatticePoint D)) (n : ℕ) (x : LatticePoint D) :
    ((dirac_convolution_kernel ν.toMeasure ^ n) x) ({x} : Set (LatticePoint D)) =
      ((dirac_convolution_kernel ν.toMeasure ^ n) (0 : LatticePoint D))
        ({0} : Set (LatticePoint D)) := by
  -- Proof comment: rewrite the `x`-row as a translated origin law and evaluate the translated
  -- singleton at displacement `x - x = 0`.
  rw [latticeKernelPow_apply_eq_diracConv_originLaw (ν := ν) (n := n) (x := x)]
  rw [Measure.dirac_conv]
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton x)]
  have hpreimage :
      (fun z : LatticePoint D ↦ x + z) ⁻¹' ({x} : Set (LatticePoint D)) =
        ({0} : Set (LatticePoint D)) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hz
      have hz' : x + z - x = x - x := by
        exact congrArg (fun w : LatticePoint D ↦ w - x) hz
      simpa using hz'
    · intro hz
      simpa [hz]
  rw [hpreimage]

/-- Helper for Theorem 17.39: the origin diagonal Green value is the origin-mass series of the
canonical lattice convolution walk. -/
lemma latticeWalk_greenFunction_zero_zero_eq_tsum_originMass
    (ν : PMF (LatticePoint D))
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ dirac_convolution_kernel ν.toMeasure ^ n) P X] :
    (G[P, X]) (0 : LatticePoint D) 0 =
      ∑' n : ℕ, ((dirac_convolution_kernel ν.toMeasure ^ n) (0 : LatticePoint D))
        ({0} : Set (LatticePoint D)) := by
  let hReal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ dirac_convolution_kernel ν.toMeasure ^ n) P X := inferInstance
  let hX : IsStochasticProcess X := fun n ↦ hReal.measurable_process n
  -- Proof comment: rewrite each time-`n` visit probability at the origin through the canonical
  -- kernel transition identity.
  rw [greenFunction_eq_tsum_stateProbabilities P X hX 0 0]
  refine tsum_congr fun n ↦ ?_
  have htransition :=
    congrArg
      (fun μ : Measure (LatticePoint D) ↦ μ ({0} : Set (LatticePoint D)))
      (hReal.transition_eq (0 : LatticePoint D) n)
  simpa [Measure.map_apply (hReal.measurable_process n) (measurableSet_singleton (0 : LatticePoint D))] using
    htransition

/-- Helper for Theorem 17.39: for a canonical lattice convolution walk, the diagonal Green value
is translation invariant. -/
lemma latticeWalk_greenFunction_self_eq_origin
    (ν : PMF (LatticePoint D))
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ dirac_convolution_kernel ν.toMeasure ^ n) P X]
    (x : LatticePoint D) :
    (G[P, X]) x x = (G[P, X]) (0 : LatticePoint D) 0 := by
  let hReal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ dirac_convolution_kernel ν.toMeasure ^ n) P X := inferInstance
  let hX : IsStochasticProcess X := fun n ↦ hReal.measurable_process n
  -- Proof comment: expand both diagonal Green values into the visit-probability series and then
  -- identify each time-`n` diagonal mass with the common origin mass.
  calc
    (G[P, X]) x x =
        ∑' n : ℕ, ((dirac_convolution_kernel ν.toMeasure ^ n) x) ({x} : Set (LatticePoint D)) := by
          rw [greenFunction_eq_tsum_stateProbabilities P X hX x x]
          refine tsum_congr fun n ↦ ?_
          have htransition :=
            congrArg
              (fun μ : Measure (LatticePoint D) ↦ μ ({x} : Set (LatticePoint D)))
              (hReal.transition_eq x n)
          simpa [Measure.map_apply (hReal.measurable_process n) (measurableSet_singleton x)] using
            htransition
    _ = ∑' n : ℕ, ((dirac_convolution_kernel ν.toMeasure ^ n) (0 : LatticePoint D))
          ({0} : Set (LatticePoint D)) := by
          refine tsum_congr fun n ↦ ?_
          exact latticeKernelPow_apply_singleton_self_eq_originMass (ν := ν) (n := n) (x := x)
    _ = (G[P, X]) (0 : LatticePoint D) 0 := by
          symm
          exact latticeWalk_greenFunction_zero_zero_eq_tsum_originMass
            (ν := ν) (P := P) (X := X)

section DiagonalGreen

/-- Helper for Theorem 17.39: the positive-time diagonal Green function is the shifted power
series of the return probability on `ℤ^D`. -/
private lemma latticeWalk_greenFunctionFromOneSelf_eq_tsum_selfPowers
    {κ : ℕ → Kernel (LatticePoint D) (LatticePoint D)}
    [IsMarkovProcessRealization κ P X]
    (x : LatticePoint D) :
    (G[P, X; 1]) x x =
      ∑' n : ℕ, ENNReal.ofReal (((F[P, X]) x x) ^ (n + 1)) := by
  -- Proof comment: rewrite the iterated entrance probabilities with Theorem 17.29 and reindex
  -- the `ℕ+`-series along `Equiv.pnatEquivNat`.
  calc
    (G[P, X; 1]) x x =
        ∑' k : ℕ+, ENNReal.ofReal ((P x : Measure Ω).real {ω | (τ_[X, x]^k) ω < ⊤}) := by
          exact greenFunctionFromOneSelf_eq_tsum_iteratedEntranceProbabilities
            (P := P) (X := X) (κ := κ) x
    _ =
        ∑' k : ℕ+, ENNReal.ofReal ((F[P, X]) x x * (F[P, X]) x x ^ k.natPred) := by
          refine tsum_congr fun k ↦ ?_
          simpa using congrArg ENNReal.ofReal
            (iteratedEntranceTime_finite_probability_eq_everHitsProbability_mul_selfPow
              (κ := κ) (P := P) (X := X) x x k)
    _ =
        ∑' n : ℕ, ENNReal.ofReal ((F[P, X]) x x * (F[P, X]) x x ^ n) := by
          simpa using
            (Equiv.tsum_eq Equiv.pnatEquivNat
              (fun n : ℕ ↦ ENNReal.ofReal ((F[P, X]) x x * (F[P, X]) x x ^ n)))
    _ = ∑' n : ℕ, ENNReal.ofReal (((F[P, X]) x x) ^ (n + 1)) := by
          refine tsum_congr fun n ↦ ?_
          rw [pow_succ, mul_comm]

/-- Helper for Theorem 17.39: the full diagonal Green value splits into the deterministic
time-`0` visit and the strictly positive-time diagonal Green tail on `ℤ^D`. -/
private lemma latticeWalk_greenFunctionSelf_eq_one_add_greenFunctionFromOneSelf
    {κ : ℕ → Kernel (LatticePoint D) (LatticePoint D)}
    [IsMarkovProcessRealization κ P X]
    (x : LatticePoint D) :
    (G[P, X]) x x = 1 + (G[P, X; 1]) x x := by
  let hReal : IsMarkovProcessRealization κ P X := inferInstance
  let hX : IsStochasticProcess X := fun n ↦ hReal.measurable_process n
  have hzero :
      (P x : Measure Ω) {ω | X 0 ω = x} = 1 := by
    have hpreimage : {ω | X 0 ω = x} = X 0 ⁻¹' ({x} : Set (LatticePoint D)) := by
      ext ω
      simp
    -- Proof comment: under `P x`, the process starts at `x` almost surely at time `0`.
    calc
      (P x : Measure Ω) {ω | X 0 ω = x}
        = ((P x : Measure Ω).map (X 0)) ({x} : Set (LatticePoint D)) := by
            simpa [hpreimage] using
              (Measure.map_apply
                (μ := (P x : Measure Ω))
                (f := X 0)
                (s := ({x} : Set (LatticePoint D)))
                (hReal.measurable_process 0)
                (MeasurableSet.singleton x)).symm
      _ = Measure.dirac x ({x} : Set (LatticePoint D)) := by
            simpa using
              congrArg (fun μ : Measure (LatticePoint D) ↦ μ ({x} : Set (LatticePoint D)))
                (hReal.initial_eq x)
      _ = 1 := by
            simp
  -- Proof comment: isolate the time-`0` term in the Green series and rewrite the remainder as
  -- the positive-time diagonal Green function.
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
                    by_cases hn : n = 0 <;> simp [hn]
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

/-- Helper for Theorem 17.39: a shifted geometric series of `ℝ≥0∞`-casts is finite whenever the
ratio lies in `[0, 1)`. -/
private lemma latticeWalk_ennrealOfRealTsumGeometricSucc_lt_top {q : ℝ}
    (hq_nonneg : 0 ≤ q) (hq_lt_one : q < 1) :
    ∑' n : ℕ, ENNReal.ofReal (q ^ (n + 1)) < ⊤ := by
  have hsum : Summable (fun n : ℕ ↦ q ^ (n + 1)) :=
    (_root_.summable_nat_add_iff 1).2 (summable_geometric_of_lt_one hq_nonneg hq_lt_one)
  -- Proof comment: a summable nonnegative real series remains finite after termwise casting to
  -- `ℝ≥0∞`.
  calc
    ∑' n : ℕ, ENNReal.ofReal (q ^ (n + 1))
      = ENNReal.ofReal (∑' n : ℕ, q ^ (n + 1)) := by
          rw [ENNReal.ofReal_tsum_of_nonneg]
          · intro n
            exact pow_nonneg hq_nonneg _
          · exact hsum
    _ < ⊤ := by
          simp

/-- Helper for Theorem 17.39: an infinite diagonal Green value forces recurrence on `ℤ^D`. -/
private lemma latticeWalk_isRecurrentState_of_greenFunctionSelf_eq_top
    {κ : ℕ → Kernel (LatticePoint D) (LatticePoint D)}
    [IsMarkovProcessRealization κ P X]
    (x : LatticePoint D) (hx : (G[P, X]) x x = ⊤) :
    IsRecurrentState P X x := by
  have hq_nonneg : 0 ≤ (F[P, X]) x x := measureReal_nonneg
  have hq_le_one : (F[P, X]) x x ≤ 1 := by
    rw [everHitsProbability_def]
    exact measureReal_le_one
  -- Proof comment: normalize the positive-time diagonal Green tail to the shifted power series in
  -- `F(x, x)` and close by contradiction with the geometric-series bound.
  by_contra htrans
  have hq_lt_one : (F[P, X]) x x < 1 := by
    rw [IsRecurrentState] at htrans
    exact lt_of_le_of_ne hq_le_one (by simpa [eq_comm] using htrans)
  have htail_lt_top :
      ∑' n : ℕ, ENNReal.ofReal (((F[P, X]) x x) ^ (n + 1)) < ⊤ :=
    latticeWalk_ennrealOfRealTsumGeometricSucc_lt_top hq_nonneg hq_lt_one
  have hgreen_lt_top : (G[P, X]) x x < ⊤ := by
    calc
      (G[P, X]) x x = 1 + (G[P, X; 1]) x x := by
        rw [latticeWalk_greenFunctionSelf_eq_one_add_greenFunctionFromOneSelf
          (P := P) (X := X) (κ := κ)]
      _ = 1 + ∑' n : ℕ, ENNReal.ofReal (((F[P, X]) x x) ^ (n + 1)) := by
        rw [latticeWalk_greenFunctionFromOneSelf_eq_tsum_selfPowers (P := P) (X := X) (κ := κ)]
      _ < ⊤ := by
        exact ENNReal.add_lt_top.2 ⟨by simp, htail_lt_top⟩
  exact (ne_of_lt hgreen_lt_top) hx

/-- Helper for Theorem 17.39: recurrence forces the diagonal Green value to be infinite on
`ℤ^D`. -/
private lemma latticeWalk_greenFunctionSelf_eq_top_of_isRecurrentState
    {κ : ℕ → Kernel (LatticePoint D) (LatticePoint D)}
    [IsMarkovProcessRealization κ P X]
    (x : LatticePoint D) (hx : IsRecurrentState P X x) :
    (G[P, X]) x x = ⊤ := by
  have htail :
      (G[P, X; 1]) x x = ∑' n : ℕ, (1 : ℝ≥0∞) := by
    -- Proof comment: recurrence makes every return-probability power equal to `1`, so the
    -- positive-time Green tail is already the divergent series of ones.
    calc
      (G[P, X; 1]) x x = ∑' n : ℕ, ENNReal.ofReal (((F[P, X]) x x) ^ (n + 1)) := by
        rw [latticeWalk_greenFunctionFromOneSelf_eq_tsum_selfPowers (P := P) (X := X) (κ := κ)]
      _ = ∑' n : ℕ, ENNReal.ofReal (1 ^ (n + 1 : ℕ)) := by
            refine tsum_congr fun n ↦ ?_
            rw [IsRecurrentState] at hx
            simpa [hx]
      _ = ∑' n : ℕ, (1 : ℝ≥0∞) := by
            refine tsum_congr fun n ↦ ?_
            simp
  -- Proof comment: add the deterministic time-`0` visit to the already divergent positive-time
  -- diagonal tail.
  calc
    (G[P, X]) x x = 1 + (G[P, X; 1]) x x := by
      rw [latticeWalk_greenFunctionSelf_eq_one_add_greenFunctionFromOneSelf
        (P := P) (X := X) (κ := κ)]
    _ = 1 + ∑' n : ℕ, (1 : ℝ≥0∞) := by
          rw [htail]
    _ = ⊤ := by
          simp

end DiagonalGreen

/-- Helper for Theorem 17.39: for a canonical lattice convolution walk, recurrence is equivalent
to the origin diagonal Green value being infinite. -/
lemma latticeWalk_isRecurrent_iff_originGreen_eq_top
    (ν : PMF (LatticePoint D))
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ dirac_convolution_kernel ν.toMeasure ^ n) P X] :
    IsRecurrentMarkovChain P X ↔ (G[P, X]) (0 : LatticePoint D) 0 = ⊤ := by
  constructor
  · intro hrec
    -- Proof comment: recurrence at the origin forces the diagonal Green value at the origin to
    -- diverge.
    exact latticeWalk_greenFunctionSelf_eq_top_of_isRecurrentState
      (D := D) (P := P) (X := X)
      (κ := fun n : ℕ ↦ dirac_convolution_kernel ν.toMeasure ^ n)
      (x := (0 : LatticePoint D)) (hx := hrec 0)
  · intro hgreen0
    intro x
    -- Proof comment: translation invariance identifies the diagonal Green value at every state
    -- with the origin value, so recurrence propagates from `0` to all states.
    refine latticeWalk_isRecurrentState_of_greenFunctionSelf_eq_top
      (D := D) (P := P) (X := X)
      (κ := fun n : ℕ ↦ dirac_convolution_kernel ν.toMeasure ^ n) (x := x) ?_
    rw [latticeWalk_greenFunction_self_eq_origin
      (D := D) (ν := ν) (P := P) (X := X) (x := x)]
    exact hgreen0

/-- Helper for Theorem 17.39: the convolution kernel generated by the symmetric simple random-walk
step law is Markov. -/
private lemma symmetricSimpleRandomWalkKernel_isMarkov [NeZero D] :
    IsMarkovKernel (dirac_convolution_kernel (symmetricSimpleRandomWalkStepPMF D).toMeasure) := by
  refine ⟨?_⟩
  intro x
  rw [dirac_convolution_kernel_apply]
  infer_instance

/-- Helper for Theorem 17.39: every power of the symmetric simple random-walk convolution kernel
is again Markov. -/
private lemma symmetricSimpleRandomWalkKernelPow_isMarkov [NeZero D] (n : ℕ) :
    IsMarkovKernel (dirac_convolution_kernel (symmetricSimpleRandomWalkStepPMF D).toMeasure ^ n) := by
  let κ : Kernel (LatticePoint D) (LatticePoint D) :=
    dirac_convolution_kernel (symmetricSimpleRandomWalkStepPMF D).toMeasure
  letI : IsMarkovKernel κ := symmetricSimpleRandomWalkKernel_isMarkov (D := D)
  induction n with
  | zero =>
      simpa [κ] using (inferInstance : IsMarkovKernel (Kernel.id : Kernel (LatticePoint D) (LatticePoint D)))
  | succ n ih =>
      letI : IsMarkovKernel (κ ^ n) := by simpa [κ] using ih
      simpa [κ, pow_succ] using (inferInstance : IsMarkovKernel ((κ ^ n) ∘ₖ κ))

/-- Helper for Theorem 17.39: the lattice parity homomorphism records the parity of the coordinate
sum in `ZMod 2`. -/
private def latticePointParity (D : ℕ) : LatticePoint D →+ ZMod 2 where
  toFun := fun x ↦ ∑ i : Fin D, (x i : ZMod 2)
  map_zero' := by
    simp
  map_add' x y := by
    -- Proof comment: coordinatewise addition turns the parity of the sum into the sum of the
    -- coordinate parities.
    simp [Finset.sum_add_distrib]

/-- Helper for Theorem 17.39: every signed unit step of the symmetric walk has odd lattice parity.
-/
private lemma latticePointParity_signedUnitStep
    (b : Bool) (i : Fin D) :
    latticePointParity D
      (if b then Pi.single i (1 : ℤ) else Pi.single i (-1)) =
      (1 : ZMod 2) := by
  -- Proof comment: only the chosen coordinate contributes, and both `1` and `-1` reduce to the
  -- odd residue class in `ZMod 2`.
  cases b
  · change ∑ j : Fin D, (((((Pi.single i (-1 : ℤ) : LatticePoint D) j) : ℤ) : ZMod 2)) =
        (1 : ZMod 2)
    simp [Pi.single_apply]
  · change ∑ j : Fin D, (((((Pi.single i (1 : ℤ) : LatticePoint D) j) : ℤ) : ZMod 2)) =
        (1 : ZMod 2)
    simp [Pi.single_apply]

/-- Helper for Theorem 17.39: pushing the symmetric one-step law through lattice parity collapses
it to the deterministic odd class. -/
private lemma symmetricSimpleRandomWalkStepPMF_map_latticePointParity
    [NeZero D] :
    (symmetricSimpleRandomWalkStepPMF D).map (latticePointParity D) =
      PMF.pure (1 : ZMod 2) := by
  let step : Bool × Fin D → LatticePoint D :=
    fun s ↦ if s.1 then Pi.single s.2 (1 : ℤ) else Pi.single s.2 (-1)
  have hconst : (latticePointParity D) ∘ step = Function.const _ (1 : ZMod 2) := by
    funext s
    rcases s with ⟨b, i⟩
    simpa [step] using latticePointParity_signedUnitStep (D := D) b i
  -- Proof comment: the step sampler already chooses a signed unit vector uniformly, and lattice
  -- parity sends every such vector to the constant odd class.
  calc
    (symmetricSimpleRandomWalkStepPMF D).map (latticePointParity D)
      = ((PMF.uniformOfFintype (Bool × Fin D)).map step).map (latticePointParity D) := by
          rfl
    _ = (PMF.uniformOfFintype (Bool × Fin D)).map ((latticePointParity D) ∘ step) := by
          rw [PMF.map_comp]
    _ = (PMF.uniformOfFintype (Bool × Fin D)).map (Function.const _ (1 : ZMod 2)) := by
          rw [hconst]
    _ = PMF.pure (1 : ZMod 2) := by
          simpa using (PMF.map_const (p := PMF.uniformOfFintype (Bool × Fin D)) (b := (1 : ZMod 2)))

/-- Helper for Theorem 17.39: the parity pushforward of the symmetric `n`-step origin law is the
Dirac mass at the parity class of `n`. -/
private lemma symmetricSimpleRandomWalkOriginLaw_map_latticePointParity
    [NeZero D] (n : ℕ) :
    Measure.map (latticePointParity D)
      ((dirac_convolution_kernel (symmetricSimpleRandomWalkStepPMF D).toMeasure ^ n)
        (0 : LatticePoint D)) =
      Measure.dirac (n : ZMod 2) := by
  induction n with
  | zero =>
      -- Proof comment: at time `0`, the walk is still at the origin, whose parity class is `0`.
      change Measure.map (latticePointParity D) (Measure.dirac (0 : LatticePoint D)) =
        Measure.dirac (0 : ZMod 2)
      rw [Measure.map_dirac]
      simp [latticePointParity]
  | succ n ih =>
      let κ : Kernel (LatticePoint D) (LatticePoint D) :=
        dirac_convolution_kernel (symmetricSimpleRandomWalkStepPMF D).toMeasure
      have hpow : κ ^ (n + 1) = κ ∘ₖ (κ ^ n) := by
        simpa [pow_one, Nat.one_add] using (ProbabilityTheory.Kernel.pow_add κ 1 n)
      have hstepMeasure :
          Measure.map (latticePointParity D) (symmetricSimpleRandomWalkStepPMF D).toMeasure =
            Measure.dirac (1 : ZMod 2) := by
        rw [PMF.toMeasure_map (p := symmetricSimpleRandomWalkStepPMF D)
          (f := latticePointParity D) (hf := measurable_of_countable (latticePointParity D))]
        have hpmf :
            (symmetricSimpleRandomWalkStepPMF D).map (latticePointParity D) =
              PMF.pure (1 : ZMod 2) :=
          symmetricSimpleRandomWalkStepPMF_map_latticePointParity (D := D)
        simpa [PMF.toMeasure_pure] using congrArg PMF.toMeasure hpmf
      -- Proof comment: one more step convolves the `n`-step origin law with the one-step law, and
      -- parity turns that convolution into addition in `ZMod 2`.
      calc
        Measure.map (latticePointParity D) ((κ ^ (n + 1)) (0 : LatticePoint D))
          = Measure.map (latticePointParity D) (κ ∘ₘ ((κ ^ n) (0 : LatticePoint D))) := by
              rw [hpow, Kernel.comp_apply]
        _ = Measure.map (latticePointParity D)
              (((κ ^ n) (0 : LatticePoint D)) ∗ (symmetricSimpleRandomWalkStepPMF D).toMeasure) := by
              rw [show κ ∘ₘ ((κ ^ n) (0 : LatticePoint D)) =
                (((κ ^ n) (0 : LatticePoint D)) ∗ (symmetricSimpleRandomWalkStepPMF D).toMeasure) by
                  simpa [κ] using
                    (latticeDiracConvolutionKernel_comp_measure_eq_conv
                      (μ := ((κ ^ n) (0 : LatticePoint D)))
                      (ν := (symmetricSimpleRandomWalkStepPMF D).toMeasure))]
        _ = Measure.map (latticePointParity D) ((κ ^ n) (0 : LatticePoint D)) ∗
              Measure.map (latticePointParity D) (symmetricSimpleRandomWalkStepPMF D).toMeasure := by
              simpa using
                (Measure.map_conv_addMonoidHom
                  (μ := ((κ ^ n) (0 : LatticePoint D)))
                  (ν := (symmetricSimpleRandomWalkStepPMF D).toMeasure)
                  (latticePointParity D)
                  (measurable_of_countable (latticePointParity D)))
        _ = Measure.dirac (n : ZMod 2) ∗ Measure.dirac (1 : ZMod 2) := by
              rw [ih, hstepMeasure]
        _ = Measure.dirac ((n : ZMod 2) + 1) := by
              simpa using Measure.dirac_conv_dirac (n : ZMod 2) (1 : ZMod 2)
        _ = Measure.dirac ((n + 1 : ℕ) : ZMod 2) := by
              simp

/-- Helper for Theorem 17.39: odd-time origin masses of the canonical symmetric walk vanish by
the parity invariant. -/
private lemma symmetricSimpleRandomWalk_originMass_odd_eq_zero
    [NeZero D] (n : ℕ) :
    ((dirac_convolution_kernel (symmetricSimpleRandomWalkStepPMF D).toMeasure ^ (2 * n + 1))
      (0 : LatticePoint D))
      ({0} : Set (LatticePoint D)) = 0 := by
  let μ : Measure (LatticePoint D) :=
    ((dirac_convolution_kernel (symmetricSimpleRandomWalkStepPMF D).toMeasure ^ (2 * n + 1))
      (0 : LatticePoint D))
  have hparity :
      Measure.map (latticePointParity D) μ = Measure.dirac (1 : ZMod 2) := by
    -- Proof comment: the `2n + 1`-step law lives entirely in the odd parity class.
    have hodd : ((2 * n + 1 : ℕ) : ZMod 2) = (1 : ZMod 2) := by
      exact (ZMod.natCast_eq_one_iff_odd (n := 2 * n + 1)).2 ⟨n, rfl⟩
    simpa [μ, hodd] using
      symmetricSimpleRandomWalkOriginLaw_map_latticePointParity (D := D) (n := 2 * n + 1)
  have hsubset :
      ({0} : Set (LatticePoint D)) ⊆
        (latticePointParity D) ⁻¹' ({0} : Set (ZMod 2)) := by
    intro x hx
    have hx0 : x = 0 := by
      simpa using hx
    simp [hx0, latticePointParity]
  have hzero :
      μ ((latticePointParity D) ⁻¹' ({0} : Set (ZMod 2))) = 0 := by
    -- Proof comment: mapping the law through parity turns the even-parity event into the
    -- singleton `{0}` in `ZMod 2`, which has zero mass under `Dirac 1`.
    rw [← Measure.map_apply (μ := μ) (f := latticePointParity D)
      (s := ({0} : Set (ZMod 2)))
      (measurable_of_countable (latticePointParity D)) (MeasurableSet.singleton 0)]
    rw [hparity]
    simp
  change μ ({0} : Set (LatticePoint D)) = 0
  exact measure_mono_null hsubset hzero

/-- Helper for Theorem 17.39: the symmetric point `1 / 2` packaged as an element of `I`. -/
private def halfUnitInterval : I := ⟨(1 / 2 : ℝ), by
  constructor <;> norm_num⟩

/-- Helper for Theorem 17.39: the one-dimensional symmetric nearest-neighbor step law on `ℤ`. -/
private def oneDimSymmetricIntegerStepPMF : PMF ℤ :=
  (PMF.uniformOfFintype Bool).map fun b ↦ if b then (1 : ℤ) else -1

/-- Helper for Theorem 17.39: after `n` one-dimensional steps, choosing `k` positive signs gives
displacement `2 * k - n`. -/
private def oneDimSymmetricDisplacement (n : ℕ) : ℕ → ℤ :=
  fun k ↦ (2 : ℤ) * k - n

/-- Helper for Theorem 17.39: convolving two pushforwards from `ℕ` is the same as pushing
forward the product law by the summed displacements. -/
private lemma oneDimMapConv_eq_mapProdSum
    (μ ν : Measure ℕ) (f g : ℕ → ℤ) (hf : Measurable f) (hg : Measurable g) :
    Measure.map f μ ∗ Measure.map g ν =
      Measure.map (fun s : ℕ × ℕ ↦ f s.1 + g s.2) (μ.prod ν) := by
  -- Proof comment: unfold convolution and collapse the two transported coordinates into one map
  -- on the product measure.
  rw [Measure.conv]
  rw [Measure.map_prod_map μ ν hf hg]
  have hsumMap :
      ((fun x : ℤ × ℤ ↦ x.1 + x.2) ∘ Prod.map f g) =
        (fun s : ℕ × ℕ ↦ f s.1 + g s.2) := by
    funext s
    cases s
    rfl
  simpa [hsumMap] using
    (Measure.map_map
      (μ := μ.prod ν)
      (g := fun x : ℤ × ℤ ↦ x.1 + x.2)
      (f := Prod.map f g)
      (by fun_prop)
      (by fun_prop))

/-- Helper for Theorem 17.39: appending one more one-dimensional step adds the corresponding
displacements. -/
private lemma oneDimSymmetricDisplacement_add (n : ℕ) :
    (fun s : ℕ × ℕ ↦
      oneDimSymmetricDisplacement n s.1 + oneDimSymmetricDisplacement 1 s.2) =
      fun s : ℕ × ℕ ↦ oneDimSymmetricDisplacement (n + 1) (s.1 + s.2) := by
  -- Proof comment: both sides expand to the same affine expression in the two binomial counts.
  ext s
  simp [oneDimSymmetricDisplacement]
  ring

/-- Helper for Theorem 17.39: the singleton masses of `Bin(n, p)` are the usual binomial
weights, now viewed in `ℝ≥0∞`. -/
private lemma oneDimBinomial_apply_singleton (n k : ℕ) (p : I) :
    Bin(n, p) ({k} : Set ℕ) =
      ENNReal.ofReal ((Nat.choose n k : ℝ) * (p : ℝ) ^ k * (1 - (p : ℝ)) ^ (n - k)) := by
  -- Proof comment: convert the already-formalized real-valued singleton formula through
  -- `ENNReal.ofReal_toReal`.
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  simpa using congrArg ENNReal.ofReal (binomial_apply_singleton_toReal n k p)

/-- Helper for Theorem 17.39: the fixed symmetric one-step law on `ℤ` is the pushforward of
`Bin(1, 1 / 2)` under the displacement map. -/
private lemma oneDimSymmetricStepLaw_eq_binomialPushforward :
    Measure.map (oneDimSymmetricDisplacement 1) (Bin(1, halfUnitInterval)) =
      oneDimSymmetricIntegerStepPMF.toMeasure := by
  refine Measure.ext_of_singleton fun y ↦ ?_
  have hmeasDisp : Measurable (oneDimSymmetricDisplacement 1) := measurable_of_countable _
  by_cases hy1 : y = 1
  · subst hy1
    rw [Measure.map_apply hmeasDisp (measurableSet_singleton (1 : ℤ))]
    have hpreimage :
        oneDimSymmetricDisplacement 1 ⁻¹' ({(1 : ℤ)} : Set ℤ) = ({1} : Set ℕ) := by
      ext k
      simp [oneDimSymmetricDisplacement]
      omega
    rw [hpreimage, oneDimBinomial_apply_singleton]
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton (1 : ℤ))]
    simp [oneDimSymmetricIntegerStepPMF, halfUnitInterval]
  · by_cases hyNeg : y = -1
    · subst hyNeg
      rw [Measure.map_apply hmeasDisp (measurableSet_singleton (-1 : ℤ))]
      have hpreimage :
          oneDimSymmetricDisplacement 1 ⁻¹' ({(-1 : ℤ)} : Set ℤ) = ({0} : Set ℕ) := by
        ext k
        simp [oneDimSymmetricDisplacement]
      rw [hpreimage, oneDimBinomial_apply_singleton]
      rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton (-1 : ℤ))]
      have hleft :
          ENNReal.ofReal
              ((Nat.choose 1 0 : ℝ) * ((halfUnitInterval : I) : ℝ) ^ 0 *
                (1 - ((halfUnitInterval : I) : ℝ)) ^ (1 - 0)) =
            ENNReal.ofReal (1 / (2 : ℝ)) := by
        norm_num [halfUnitInterval]
      have hright : oneDimSymmetricIntegerStepPMF (-1) = ((2 : ℝ≥0∞)⁻¹) := by
        simp [oneDimSymmetricIntegerStepPMF]
      rw [hleft, hright]
      have htwo : ((2 : ℝ≥0∞)⁻¹) = (1 / 2 : ℝ≥0∞) := by
        norm_num
      have hrealHalf : ENNReal.ofReal (1 / (2 : ℝ)) = (1 / 2 : ℝ≥0∞) := by
        simpa using
          (ENNReal.ofReal_eq_coe_nnreal (show 0 ≤ (1 / (2 : ℝ)) by positivity)).symm
      calc
        ENNReal.ofReal (1 / (2 : ℝ)) = (1 / 2 : ℝ≥0∞) := hrealHalf
        _ = ((2 : ℝ≥0∞)⁻¹) := htwo.symm
    · rw [Measure.map_apply hmeasDisp (measurableSet_singleton y)]
      have hsupport :
          ∀ᵐ k : ℕ ∂Bin(1, halfUnitInterval), k ≤ 1 := by
        simpa using
          (ProbabilityTheory.ae_le_of_hasLaw_binomial
            (n := 1)
            (p := halfUnitInterval)
            (X := id)
            (P := Bin(1, halfUnitInterval))
            (ProbabilityTheory.HasLaw.id (μ := Bin(1, halfUnitInterval))))
      have hleft :
          Bin(1, halfUnitInterval) (oneDimSymmetricDisplacement 1 ⁻¹' ({y} : Set ℤ)) = 0 := by
        rw [measure_eq_zero_iff_ae_notMem]
        filter_upwards [hsupport] with k hk
        simp [Set.mem_preimage, Set.mem_singleton_iff]
        intro hky
        have hEq : (2 : ℤ) * k - 1 = y := by
          simpa [oneDimSymmetricDisplacement] using hky
        have hk_gt : 1 < k := by
          omega
        exact (not_lt_of_ge hk) hk_gt
      rw [hleft]
      rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton y)]
      simp [oneDimSymmetricIntegerStepPMF, hy1, hyNeg]

/-- Helper for Theorem 17.39: one more origin-started symmetric step on `ℤ` convolves the current
origin law with the one-step law. -/
private lemma oneDimSymmetricOriginLawIterateSucc (n : ℕ) :
    (((dirac_convolution_kernel oneDimSymmetricIntegerStepPMF.toMeasure) ^ (n + 1)) (0 : ℤ)) =
      (((dirac_convolution_kernel oneDimSymmetricIntegerStepPMF.toMeasure) ^ n) (0 : ℤ)) ∗
        oneDimSymmetricIntegerStepPMF.toMeasure := by
  let κ : Kernel ℤ ℤ := dirac_convolution_kernel oneDimSymmetricIntegerStepPMF.toMeasure
  have hpow : κ ^ (n + 1) = κ ∘ₖ (κ ^ n) := by
    simpa [pow_one, Nat.one_add] using (ProbabilityTheory.Kernel.pow_add κ 1 n)
  have hcomp :
      κ ∘ₘ ((κ ^ n) (0 : ℤ)) =
        ((κ ^ n) (0 : ℤ)) ∗ oneDimSymmetricIntegerStepPMF.toMeasure := by
    have hconst :=
      congrArg
        (fun K : Kernel ℤ ℤ ↦ K (0 : ℤ))
        (dirac_convolution_kernel_comp_const_eq_const_conv
          (μ := ((κ ^ n) (0 : ℤ)))
          (ν := oneDimSymmetricIntegerStepPMF.toMeasure))
    simpa [Kernel.comp_apply, κ] using hconst
  -- Proof comment: rewrite the successor power as one kernel composition and evaluate it at the
  -- origin.
  calc
    (κ ^ (n + 1)) (0 : ℤ) = κ ∘ₘ ((κ ^ n) (0 : ℤ)) := by
      rw [hpow, Kernel.comp_apply]
    _ = ((κ ^ n) (0 : ℤ)) ∗ oneDimSymmetricIntegerStepPMF.toMeasure := hcomp

/-- Helper for Theorem 17.39: the origin-started `n`-step law of the one-dimensional symmetric
walk on `ℤ` is the pushforward of `Bin(n, 1 / 2)` by the displacement map. -/
private lemma oneDimSymmetricOriginLaw_eq_binomialPushforward :
    ∀ n : ℕ,
      ((dirac_convolution_kernel oneDimSymmetricIntegerStepPMF.toMeasure ^ n) (0 : ℤ)) =
        Measure.map (oneDimSymmetricDisplacement n) (Bin(n, halfUnitInterval))
  | 0 => by
      have hzero :
          ((dirac_convolution_kernel oneDimSymmetricIntegerStepPMF.toMeasure ^ 0) (0 : ℤ)) =
            Measure.dirac (0 : ℤ) := by
        simpa [pow_zero] using (Kernel.id_apply (0 : ℤ))
      -- Proof comment: at time `0`, both laws are the Dirac mass at the origin.
      rw [hzero, binomial_zero_left]
      have hmeasDisp : Measurable (oneDimSymmetricDisplacement 0) := measurable_of_countable _
      rw [Measure.map_dirac]
      simp [oneDimSymmetricDisplacement]
  | n + 1 => by
      have hmeasSum :
          Measurable (fun s : ℕ × ℕ ↦ s.1 + s.2) := measurable_fst.add measurable_snd
      have hmeasDisp : Measurable (oneDimSymmetricDisplacement (n + 1)) := measurable_of_countable _
      have hmap :
          Measure.map
              (fun s : ℕ × ℕ ↦ oneDimSymmetricDisplacement (n + 1) (s.1 + s.2))
              (Bin(n, halfUnitInterval).prod Bin(1, halfUnitInterval)) =
            Measure.map (oneDimSymmetricDisplacement (n + 1))
              (Measure.map (fun s : ℕ × ℕ ↦ s.1 + s.2)
                (Bin(n, halfUnitInterval).prod Bin(1, halfUnitInterval))) := by
        -- Proof comment: factor the displacement through addition before using the binomial
        -- convolution theorem.
        symm
        simpa using
          (Measure.map_map
            (μ := Bin(n, halfUnitInterval).prod Bin(1, halfUnitInterval))
            (g := oneDimSymmetricDisplacement (n + 1))
            (f := fun s : ℕ × ℕ ↦ s.1 + s.2)
            hmeasDisp
            hmeasSum)
      have hmeasDispN : Measurable (oneDimSymmetricDisplacement n) := measurable_of_countable _
      have hmeasDisp1 : Measurable (oneDimSymmetricDisplacement 1) := measurable_of_countable _
      calc
        ((dirac_convolution_kernel oneDimSymmetricIntegerStepPMF.toMeasure ^ (n + 1))
            (0 : ℤ))
            =
            ((dirac_convolution_kernel oneDimSymmetricIntegerStepPMF.toMeasure ^ n)
              (0 : ℤ)) ∗
              oneDimSymmetricIntegerStepPMF.toMeasure := by
                simpa using oneDimSymmetricOriginLawIterateSucc n
        _ = Measure.map (oneDimSymmetricDisplacement n) (Bin(n, halfUnitInterval)) ∗
              oneDimSymmetricIntegerStepPMF.toMeasure := by
                rw [oneDimSymmetricOriginLaw_eq_binomialPushforward n]
        _ = Measure.map (oneDimSymmetricDisplacement n) (Bin(n, halfUnitInterval)) ∗
              Measure.map (oneDimSymmetricDisplacement 1) (Bin(1, halfUnitInterval)) := by
                rw [oneDimSymmetricStepLaw_eq_binomialPushforward]
        _ = Measure.map
              (fun s : ℕ × ℕ ↦
                oneDimSymmetricDisplacement n s.1 +
                  oneDimSymmetricDisplacement 1 s.2)
              (Bin(n, halfUnitInterval).prod Bin(1, halfUnitInterval)) := by
                exact oneDimMapConv_eq_mapProdSum
                  (μ := Bin(n, halfUnitInterval))
                  (ν := Bin(1, halfUnitInterval))
                  (f := oneDimSymmetricDisplacement n)
                  (g := oneDimSymmetricDisplacement 1)
                  hmeasDispN
                  hmeasDisp1
        _ = Measure.map
              (fun s : ℕ × ℕ ↦ oneDimSymmetricDisplacement (n + 1) (s.1 + s.2))
              (Bin(n, halfUnitInterval).prod Bin(1, halfUnitInterval)) := by
                rw [oneDimSymmetricDisplacement_add n]
        _ = Measure.map (oneDimSymmetricDisplacement (n + 1))
              (Measure.map (fun s : ℕ × ℕ ↦ s.1 + s.2)
                (Bin(n, halfUnitInterval).prod Bin(1, halfUnitInterval))) := hmap
        _ = Measure.map (oneDimSymmetricDisplacement (n + 1))
              (Bin(n, halfUnitInterval) ∗ Bin(1, halfUnitInterval)) := by
                rw [Measure.conv]
        _ = Measure.map (oneDimSymmetricDisplacement (n + 1))
              (Bin(n + 1, halfUnitInterval)) := by
                simpa [Nat.add_comm] using
                  congrArg (Measure.map (oneDimSymmetricDisplacement (n + 1)))
                    (example_3_4_binomial_conv n 1 halfUnitInterval)

/-- Helper for Theorem 17.39: the even return mass of the one-dimensional symmetric walk on `ℤ`
is the normalized central-binomial term. -/
private lemma oneDimSymmetricOriginMass_even (n : ℕ) :
    ((dirac_convolution_kernel oneDimSymmetricIntegerStepPMF.toMeasure ^ (2 * n))
      (0 : ℤ))
      ({0} : Set ℤ) =
      ENNReal.ofReal ((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n) := by
  rw [oneDimSymmetricOriginLaw_eq_binomialPushforward (n := 2 * n)]
  have hmeasDisp : Measurable (oneDimSymmetricDisplacement (2 * n)) := measurable_of_countable _
  rw [Measure.map_apply hmeasDisp (measurableSet_singleton (0 : ℤ))]
  have hpreimage :
      oneDimSymmetricDisplacement (2 * n) ⁻¹' ({(0 : ℤ)} : Set ℤ) = ({n} : Set ℕ) := by
    ext k
    simp [oneDimSymmetricDisplacement]
    omega
  rw [hpreimage, oneDimBinomial_apply_singleton]
  have hhalf : ((halfUnitInterval : I) : ℝ) = 1 / 2 := rfl
  have hpq : ((halfUnitInterval : I) : ℝ) * (1 - ((halfUnitInterval : I) : ℝ)) = 1 / 4 := by
    nlinarith [hhalf]
  have hsub : 2 * n - n = n := by
    omega
  congr 1
  rw [hsub]
  have hpow :
      (((halfUnitInterval : I) : ℝ) ^ n) * (1 - ((halfUnitInterval : I) : ℝ)) ^ n =
        ((4 : ℝ) ^ n)⁻¹ := by
    rw [← mul_pow, hpq]
    simp [one_div, inv_pow]
  calc
    (Nat.choose (2 * n) n : ℝ) * (((halfUnitInterval : I) : ℝ) ^ n) *
        (1 - ((halfUnitInterval : I) : ℝ)) ^ n
      = (Nat.choose (2 * n) n : ℝ) *
          ((((halfUnitInterval : I) : ℝ) ^ n) * (1 - ((halfUnitInterval : I) : ℝ)) ^ n) := by
            ring
    _ = (Nat.choose (2 * n) n : ℝ) * ((4 : ℝ) ^ n)⁻¹ := by
          rw [hpow]
    _ = (Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n := by
          rw [div_eq_mul_inv]

/-- Helper for Theorem 17.39: reading off the unique coordinate identifies `LatticePoint 1` with
the one-dimensional walk on `ℤ`. -/
private def latticePointOneCoord : LatticePoint 1 →+ ℤ where
  toFun := fun x ↦ x 0
  map_zero' := by
    simp
  map_add' x y := by
    simp

/-- Helper for Theorem 17.39: pushing the one-dimensional lattice step law through the unique
coordinate map gives the symmetric nearest-neighbor law on `ℤ`. -/
private lemma symmetricSimpleRandomWalkStepPMF_one_map_latticePointOneCoord :
    Measure.map latticePointOneCoord (symmetricSimpleRandomWalkStepPMF 1).toMeasure =
      oneDimSymmetricIntegerStepPMF.toMeasure := by
  have hfirst :
      (PMF.uniformOfFintype (Bool × Fin 1)).map Prod.fst = PMF.uniformOfFintype Bool := by
    ext b
    cases b
    · rw [PMF.map_apply, PMF.uniformOfFintype_apply]
      rw [tsum_eq_single (false, (0 : Fin 1))]
      · simp
      · intro a ha
        rcases a with ⟨a, i⟩
        cases a
        · fin_cases i
          exact (ha rfl).elim
        · fin_cases i
          simp
    · rw [PMF.map_apply, PMF.uniformOfFintype_apply]
      rw [tsum_eq_single (true, (0 : Fin 1))]
      · simp
      · intro a ha
        rcases a with ⟨a, i⟩
        cases a
        · fin_cases i
          simp
        · fin_cases i
          exact (ha rfl).elim
  have hcoord :
      (symmetricSimpleRandomWalkStepPMF 1).map latticePointOneCoord =
        ((PMF.uniformOfFintype (Bool × Fin 1)).map Prod.fst).map
          (fun b ↦ if b then (1 : ℤ) else -1) := by
    rw [symmetricSimpleRandomWalkStepPMF, PMF.map_comp]
    symm
    rw [PMF.map_comp]
    congr 1
    funext s
    rcases s with ⟨b, i⟩
    fin_cases i
    cases b <;> simp [latticePointOneCoord]
  rw [PMF.toMeasure_map (p := symmetricSimpleRandomWalkStepPMF 1)
    (f := latticePointOneCoord) (hf := measurable_of_countable latticePointOneCoord)]
  rw [hcoord, hfirst]
  rfl

/-- Helper for Theorem 17.39: after pushing the origin-started one-dimensional lattice walk
through the coordinate map, one gets the corresponding symmetric walk on `ℤ`. -/
private lemma symmetricSimpleRandomWalkOriginLaw_one_map_latticePointOneCoord (n : ℕ) :
    Measure.map latticePointOneCoord
      ((dirac_convolution_kernel (symmetricSimpleRandomWalkStepPMF 1).toMeasure ^ n)
        (0 : LatticePoint 1)) =
      ((dirac_convolution_kernel oneDimSymmetricIntegerStepPMF.toMeasure ^ n) (0 : ℤ)) := by
  induction n with
  | zero =>
      -- Proof comment: at time `0`, both origin laws are the Dirac mass at the origin.
      change Measure.map latticePointOneCoord (Measure.dirac (0 : LatticePoint 1)) = Measure.dirac (0 : ℤ)
      rw [Measure.map_dirac]
      simp [latticePointOneCoord]
  | succ n ih =>
      let κL : Kernel (LatticePoint 1) (LatticePoint 1) :=
        dirac_convolution_kernel (symmetricSimpleRandomWalkStepPMF 1).toMeasure
      let κZ : Kernel ℤ ℤ := dirac_convolution_kernel oneDimSymmetricIntegerStepPMF.toMeasure
      have hpowL : κL ^ (n + 1) = κL ∘ₖ (κL ^ n) := by
        simpa [pow_one, Nat.one_add] using (ProbabilityTheory.Kernel.pow_add κL 1 n)
      have hpowZ : κZ ^ (n + 1) = κZ ∘ₖ (κZ ^ n) := by
        simpa [pow_one, Nat.one_add] using (ProbabilityTheory.Kernel.pow_add κZ 1 n)
      have hmeasCoord : Measurable latticePointOneCoord := measurable_of_countable latticePointOneCoord
      have hconvMap :
          Measure.map latticePointOneCoord
              (((κL ^ n) (0 : LatticePoint 1)) ∗ (symmetricSimpleRandomWalkStepPMF 1).toMeasure) =
            Measure.map latticePointOneCoord ((κL ^ n) (0 : LatticePoint 1)) ∗
              Measure.map latticePointOneCoord (symmetricSimpleRandomWalkStepPMF 1).toMeasure := by
        simpa using
          (Measure.map_conv_addMonoidHom
            (μ := ((κL ^ n) (0 : LatticePoint 1)))
            (ν := (symmetricSimpleRandomWalkStepPMF 1).toMeasure)
            latticePointOneCoord
            hmeasCoord)
      -- Proof comment: one more lattice step becomes one more integer step after applying the
      -- additive coordinate map.
      calc
        Measure.map latticePointOneCoord ((κL ^ (n + 1)) (0 : LatticePoint 1))
            = Measure.map latticePointOneCoord (κL ∘ₘ ((κL ^ n) (0 : LatticePoint 1))) := by
                rw [hpowL, Kernel.comp_apply]
        _ = Measure.map latticePointOneCoord
              ((((κL ^ n) (0 : LatticePoint 1)) ∗ (symmetricSimpleRandomWalkStepPMF 1).toMeasure)) := by
                have hcomp :=
                  latticeDiracConvolutionKernel_comp_measure_eq_conv
                    (D := 1)
                    (μ := ((κL ^ n) (0 : LatticePoint 1)))
                    (ν := (symmetricSimpleRandomWalkStepPMF 1).toMeasure)
                rw [hcomp]
        _ = Measure.map latticePointOneCoord ((κL ^ n) (0 : LatticePoint 1)) ∗
              Measure.map latticePointOneCoord (symmetricSimpleRandomWalkStepPMF 1).toMeasure := hconvMap
        _ = ((κZ ^ n) (0 : ℤ)) ∗ oneDimSymmetricIntegerStepPMF.toMeasure := by
              rw [ih, symmetricSimpleRandomWalkStepPMF_one_map_latticePointOneCoord]
        _ = (κZ ^ (n + 1)) (0 : ℤ) := by
              simpa [κZ] using (oneDimSymmetricOriginLawIterateSucc n).symm

/-- Helper for Theorem 17.39: the even origin mass of the one-dimensional lattice walk is the
normalized central-binomial term. -/
private lemma symmetricSimpleRandomWalkOriginMass_even_dimOne (n : ℕ) :
    ((dirac_convolution_kernel (symmetricSimpleRandomWalkStepPMF 1).toMeasure ^ (2 * n))
      (0 : LatticePoint 1))
      ({0} : Set (LatticePoint 1)) =
      ENNReal.ofReal ((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n) := by
  let μ : Measure (LatticePoint 1) :=
    ((dirac_convolution_kernel (symmetricSimpleRandomWalkStepPMF 1).toMeasure ^ (2 * n))
      (0 : LatticePoint 1))
  have hmapMeasure :
      Measure.map latticePointOneCoord μ =
        ((dirac_convolution_kernel oneDimSymmetricIntegerStepPMF.toMeasure ^ (2 * n)) (0 : ℤ)) := by
    simpa [μ] using symmetricSimpleRandomWalkOriginLaw_one_map_latticePointOneCoord (n := 2 * n)
  have hmap :=
    congrArg (fun ν : Measure ℤ ↦ ν ({0} : Set ℤ)) hmapMeasure
  have hmeasCoord : Measurable latticePointOneCoord := measurable_of_countable latticePointOneCoord
  have hpreimage :
      latticePointOneCoord ⁻¹' ({(0 : ℤ)} : Set ℤ) = ({0} : Set (LatticePoint 1)) := by
    ext x
    constructor
    · intro hx
      ext i
      fin_cases i
      simpa [latticePointOneCoord] using hx
    · intro hx
      have hx0 : x = 0 := by
        simpa using hx
      simpa [latticePointOneCoord, hx0]
  have hleft :
      (Measure.map latticePointOneCoord μ) ({0} : Set ℤ) = μ ({0} : Set (LatticePoint 1)) := by
    rw [Measure.map_apply hmeasCoord (measurableSet_singleton (0 : ℤ)), hpreimage]
  calc
    μ ({0} : Set (LatticePoint 1))
      = (Measure.map latticePointOneCoord μ) ({0} : Set ℤ) := by
          exact hleft.symm
    _ = ((dirac_convolution_kernel oneDimSymmetricIntegerStepPMF.toMeasure ^ (2 * n))
          (0 : ℤ))
          ({0} : Set ℤ) := hmap
    _ = ENNReal.ofReal ((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n) := by
          exact oneDimSymmetricOriginMass_even n

/-- Helper for Theorem 17.39: the one-dimensional normalized central-binomial masses dominate a
shifted harmonic tail. -/
private lemma centralBinomialReturnMass_dimOne_ge_harmonic (n : ℕ) :
    ENNReal.ofReal (1 / (n + 4 : ℝ)) ≤
      ENNReal.ofReal ((Nat.choose (2 * (n + 4)) (n + 4) : ℝ) / (4 : ℝ) ^ (n + 4)) := by
  have hnat :
      4 ^ (n + 4) < (n + 4) * Nat.centralBinom (n + 4) := by
    exact Nat.four_pow_lt_mul_centralBinom (n + 4) (by omega)
  have hreal :
      (4 : ℝ) ^ (n + 4) < (n + 4 : ℝ) * (Nat.centralBinom (n + 4) : ℝ) := by
    exact_mod_cast hnat
  have hpow_pos : 0 < (4 : ℝ) ^ (n + 4) := by
    positivity
  have hnat_pos : 0 < (n + 4 : ℝ) := by
    positivity
  have hineq :
      1 / (n + 4 : ℝ) <
        (Nat.centralBinom (n + 4) : ℝ) / (4 : ℝ) ^ (n + 4) := by
    have htmp :
        (4 : ℝ) ^ (n + 4) / (n + 4 : ℝ) < (Nat.centralBinom (n + 4) : ℝ) := by
      rw [div_lt_iff₀ hnat_pos]
      simpa [Nat.centralBinom, mul_assoc, mul_comm, mul_left_comm] using hreal
    have hdiv :
        ((4 : ℝ) ^ (n + 4) / (n + 4 : ℝ)) / (4 : ℝ) ^ (n + 4) <
          (Nat.centralBinom (n + 4) : ℝ) / (4 : ℝ) ^ (n + 4) :=
      div_lt_div_of_pos_right htmp hpow_pos
    have hleft :
        ((4 : ℝ) ^ (n + 4) / (n + 4 : ℝ)) / (4 : ℝ) ^ (n + 4) = 1 / (n + 4 : ℝ) := by
      field_simp [hpow_pos.ne', hnat_pos.ne']
    rw [hleft] at hdiv
    exact hdiv
  exact ENNReal.ofReal_le_ofReal hineq.le

/-- Helper for Theorem 17.39: the shifted harmonic series diverges in `ℝ≥0∞`. -/
private lemma shiftedHarmonicOfReal_tsum_eq_top_dimOne :
    (∑' n : ℕ, ENNReal.ofReal (1 / (n + 4 : ℝ))) = ∞ := by
  by_contra hfinite
  have hsummable :
      Summable (fun n : ℕ ↦ (ENNReal.ofReal (1 / (n + 4 : ℝ))).toReal) :=
    ENNReal.summable_toReal (f := fun n : ℕ ↦ ENNReal.ofReal (1 / (n + 4 : ℝ))) <| by
      simpa using hfinite
  have hshift :
      Summable (fun n : ℕ ↦ 1 / (n + 4 : ℝ)) := by
    -- Proof comment: finiteness of the `ℝ≥0∞` series would force summability of the real tail.
    refine hsummable.congr ?_
    intro n
    rw [ENNReal.toReal_ofReal]
    positivity
  have hnot : ¬ Summable (fun n : ℕ ↦ 1 / (n + 4 : ℝ)) := by
    simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm] using
      mt ((_root_.summable_nat_add_iff (f := fun n : ℕ ↦ 1 / (n : ℝ)) 4).1)
        Real.not_summable_one_div_natCast
  exact hnot hshift

/-- Helper for Theorem 17.39: the normalized central-binomial term has the exact Wallis-product
representation used later in the planar and high-dimensional estimates. -/
private lemma centralBinomialReturnProbability_sq_eq_wallis (n : ℕ) :
    (((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n) ^ 2) =
      1 / ((((2 * n + 1 : ℕ) : ℝ) * Real.Wallis.W n) : ℝ) := by
  have hChoose :
      (Nat.choose (2 * n) n : ℝ) =
        (Nat.factorial (2 * n) : ℝ) /
          ((Nat.factorial n : ℝ) * (Nat.factorial n : ℝ)) := by
    have hFact :
        ((Nat.factorial n : ℝ) * (Nat.factorial n : ℝ)) ≠ 0 := by
      positivity
    apply (eq_div_iff hFact).2
    have hChooseNat :
        ((n + n).choose n : ℝ) * (Nat.factorial n : ℝ) * (Nat.factorial n : ℝ) =
          (Nat.factorial (n + n) : ℝ) := by
      exact_mod_cast Nat.add_choose_mul_factorial_mul_factorial n n
    ring_nf at hChooseNat ⊢
    simpa [two_mul] using hChooseNat
  have hPow :
      ((4 : ℝ) ^ n) ^ (2 : ℕ) = (2 : ℝ) ^ (4 * n) := by
    calc
      ((4 : ℝ) ^ n) ^ (2 : ℕ) = (4 : ℝ) ^ (n * 2) := by
        rw [pow_mul]
      _ = (4 : ℝ) ^ (2 * n) := by
        congr 1
        ring
      _ = ((4 : ℝ) ^ (2 : ℕ)) ^ n := by
        rw [pow_mul]
      _ = (2 : ℝ) ^ (4 * n) := by
        norm_num [pow_mul]
  -- Proof comment: rewrite the central binomial coefficient through factorials and then compare
  -- the result with the closed Wallis factorial formula.
  rw [pow_two, hChoose, Real.Wallis.W_eq_factorial_ratio]
  field_simp
  rw [← hPow]
  have hNat : (((2 * n + 1 : ℕ) : ℝ)) = 2 * (n : ℝ) + 1 := by
    norm_num
  rw [hNat]
  simp [mul_comm]

/-- Helper for Theorem 17.39: the normalized central-binomial coefficients converge to
`1 / √π`. -/
private lemma centralBinomialReturnProbability_tendsto :
    Tendsto
      (fun n : ℕ ↦
        (n : ℝ) ^ ((1 : ℝ) / 2) * ((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n))
      atTop
      (nhds (1 / Real.sqrt Real.pi)) := by
  let a : ℕ → ℝ := fun n ↦
    (n : ℝ) ^ ((1 : ℝ) / 2) * ((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n)
  have hsqEq :
      ∀ n : ℕ, (a n) ^ (2 : ℕ) = (n : ℝ) / ((((2 * n + 1 : ℕ) : ℝ) * Real.Wallis.W n)) := by
    intro n
    dsimp [a]
    rw [mul_pow]
    rw [show (((n : ℝ) ^ ((1 : ℝ) / 2)) ^ (2 : ℕ)) = (n : ℝ) by
      rw [← Real.sqrt_eq_rpow]
      simp [Real.sq_sqrt (Nat.cast_nonneg n)]]
    rw [centralBinomialReturnProbability_sq_eq_wallis]
    ring
  have hsqWallis :
      Tendsto
        (fun n : ℕ ↦ (n : ℝ) / ((((2 * n + 1 : ℕ) : ℝ) * Real.Wallis.W n)))
        atTop
        (nhds (1 / Real.pi)) := by
    have hWallisInv :
        Tendsto (fun n : ℕ ↦ (Real.Wallis.W n)⁻¹) atTop (nhds ((Real.pi / 2)⁻¹)) := by
      exact Real.Wallis.tendsto_W_nhds_pi_div_two.inv₀ (by positivity)
    have hRatio :
        Tendsto (fun n : ℕ ↦ (n : ℝ) / (2 * (n : ℝ) + 1)) atTop (nhds (1 / 2)) := by
      simpa using Stirling.tendsto_self_div_two_mul_self_add_one
    convert hRatio.mul hWallisInv using 1
    · ext n
      field_simp [ne_of_gt (Real.Wallis.W_pos n)]
      congr 1
      simpa [mul_comm]
    · field_simp [Real.pi_ne_zero]
  have hsq :
      Tendsto (fun n : ℕ ↦ (a n) ^ (2 : ℕ)) atTop (nhds (1 / Real.pi)) := by
    simpa [hsqEq] using hsqWallis
  have hnonneg : ∀ n : ℕ, 0 ≤ a n := by
    intro n
    dsimp [a]
    refine mul_nonneg ?_ ?_
    · exact Real.rpow_nonneg (Nat.cast_nonneg n) _
    · refine div_nonneg ?_ ?_
      · positivity
      · positivity
  -- Proof comment: all terms are nonnegative, so continuity of `Real.sqrt` transfers the limit
  -- from the squared sequence to the original normalized central-binomial term.
  have hsqrt :
      Tendsto (fun n : ℕ ↦ Real.sqrt ((a n) ^ (2 : ℕ))) atTop (nhds (Real.sqrt (1 / Real.pi))) :=
    Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  have hsqrtEq : (fun n : ℕ ↦ Real.sqrt ((a n) ^ (2 : ℕ))) = a := by
    funext n
    rw [show (a n) ^ (2 : ℕ) = (a n) ^ 2 by norm_num]
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (hnonneg n)]
  have hsqrtPi : Real.sqrt (1 / Real.pi) = 1 / Real.sqrt Real.pi := by
    rw [Real.sqrt_div (by positivity)]
    simp
  rw [hsqrtEq] at hsqrt
  simpa [a, hsqrtPi] using hsqrt

/-- Helper for Theorem 17.39: the square of the normalized central-binomial term dominates a
shifted harmonic tail through the upper Wallis bound. -/
private lemma centralBinomialReturnProbability_sq_ge_piInv_div_succ (n : ℕ) :
    1 / (Real.pi * (n + 1 : ℝ)) ≤
      (((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n) ^ 2) := by
  have hden_pos :
      0 < (((2 * n + 1 : ℕ) : ℝ) * Real.Wallis.W n) := by
    exact mul_pos (by positivity) (Real.Wallis.W_pos n)
  have hden_le :
      (((2 * n + 1 : ℕ) : ℝ) * Real.Wallis.W n) ≤ Real.pi * (n + 1 : ℝ) := by
    have hhalf_le : (((2 * n + 1 : ℕ) : ℝ) / 2) ≤ (n + 1 : ℝ) := by
      have hnat :
          (((2 * n + 1 : ℕ) : ℝ)) ≤ 2 * (n + 1 : ℝ) := by
        exact_mod_cast (show 2 * n + 1 ≤ 2 * (n + 1) by omega)
      linarith
    calc
      (((2 * n + 1 : ℕ) : ℝ) * Real.Wallis.W n)
          ≤ (((2 * n + 1 : ℕ) : ℝ) * (Real.pi / 2)) := by
            gcongr
            exact Real.Wallis.W_le n
      _ ≤ Real.pi * (n + 1 : ℝ) := by
            nlinarith [hhalf_le, Real.pi_pos]
  -- Proof comment: the Wallis upper bound puts a linear upper bound on the denominator in the
  -- exact square formula, so reciprocals give the harmonic lower bound.
  calc
    1 / (Real.pi * (n + 1 : ℝ))
      ≤ 1 / ((((2 * n + 1 : ℕ) : ℝ) * Real.Wallis.W n)) := by
          exact one_div_le_one_div_of_le hden_pos hden_le
    _ = (((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n) ^ 2) := by
          rw [centralBinomialReturnProbability_sq_eq_wallis]

/-- Helper for Theorem 17.39: the square of the normalized central-binomial term has the uniform
`(n + 1)⁻¹` upper bound coming from the lower Wallis estimate. -/
private lemma centralBinomialReturnProbability_sq_le_fourPiInv_div_succ (n : ℕ) :
    (((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n) ^ 2) ≤
      4 / (Real.pi * (n + 1 : ℝ)) := by
  have hWallisLower :
      Real.pi / 4 ≤ Real.Wallis.W n := by
    have hratio :
        (1 / 2 : ℝ) ≤ (((2 : ℝ) * n + 1) / (2 * n + 2)) := by
      have hden_pos : 0 < ((2 : ℝ) * n + 2) := by positivity
      field_simp [hden_pos.ne']
      nlinarith
    have hquarter :
        Real.pi / 4 ≤ (((2 : ℝ) * n + 1) / (2 * n + 2)) * (Real.pi / 2) := by
      have hpi_half_nonneg : 0 ≤ Real.pi / 2 := by positivity
      calc
        Real.pi / 4 = (1 / 2 : ℝ) * (Real.pi / 2) := by ring
        _ ≤ (((2 : ℝ) * n + 1) / (2 * n + 2)) * (Real.pi / 2) := by
              exact mul_le_mul_of_nonneg_right hratio hpi_half_nonneg
    exact hquarter.trans (Real.Wallis.le_W n)
  have hden_lower :
      Real.pi * (n + 1 : ℝ) / 4 ≤
        (((2 * n + 1 : ℕ) : ℝ) * Real.Wallis.W n) := by
    have hsucc_le : (n + 1 : ℝ) ≤ (((2 * n + 1 : ℕ) : ℝ)) := by
      exact_mod_cast (show n + 1 ≤ 2 * n + 1 by omega)
    calc
      Real.pi * (n + 1 : ℝ) / 4
          ≤ (((2 * n + 1 : ℕ) : ℝ) * (Real.pi / 4)) := by
            nlinarith [hsucc_le, Real.pi_pos]
      _ ≤ (((2 * n + 1 : ℕ) : ℝ) * Real.Wallis.W n) := by
            gcongr
  have hrecip :
      1 / ((((2 * n + 1 : ℕ) : ℝ) * Real.Wallis.W n)) ≤
        1 / (Real.pi * (n + 1 : ℝ) / 4) := by
    have hpos : 0 < Real.pi * (n + 1 : ℝ) / 4 := by
      positivity
    exact one_div_le_one_div_of_le hpos hden_lower
  -- Proof comment: the lower Wallis bound gives a linear lower bound on the denominator in the
  -- exact square formula, hence a global `1 / (n + 1)` majorant after reciprocation.
  calc
    (((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n) ^ 2)
      = 1 / ((((2 * n + 1 : ℕ) : ℝ) * Real.Wallis.W n)) := by
          rw [centralBinomialReturnProbability_sq_eq_wallis]
    _ ≤ 1 / (Real.pi * (n + 1 : ℝ) / 4) := hrecip
    _ = 4 / (Real.pi * (n + 1 : ℝ)) := by
          field_simp [Real.pi_ne_zero]

/-
/-- Helper for Theorem 17.39: the real-valued even return mass of the canonical symmetric walk. -/
private def symmetricSimpleRandomWalkEvenOriginMassToReal (D n : ℕ) [NeZero D] : ℝ :=
  ((((dirac_convolution_kernel (symmetricSimpleRandomWalkStepPMF D).toMeasure ^ (2 * n))
    (0 : LatticePoint D))
    ({0} : Set (LatticePoint D))).toReal)

/-- Helper for Theorem 17.39: the signed coordinate step attached to a sample in
`Bool × Fin D`. -/
private def signedCoordinateStep (D : ℕ) (s : Bool × Fin D) : LatticePoint D :=
  if s.1 then Pi.single s.2 (1 : ℤ) else Pi.single s.2 (-1)

/-- Helper for Theorem 17.39: the total lattice displacement carried by a finite signed word. -/
private def signedStepWordSum (D : ℕ) {n : ℕ} (w : Fin n → Bool × Fin D) : LatticePoint D :=
  ∑ j, signedCoordinateStep D (w j)

/-- Helper for Theorem 17.39: convolving two pushforwards into `LatticePoint D` is the same as
pushing the product law through the sum of the transported coordinates. -/
private lemma latticeMapConv_eq_mapProdSum {D : ℕ} {α : Type*} {β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    [SFinite μ] [SFinite ν]
    (μ : Measure α) (ν : Measure β) (f : α → LatticePoint D) (g : β → LatticePoint D)
    (hf : Measurable f) (hg : Measurable g) :
    Measure.map f μ ∗ Measure.map g ν =
      Measure.map (fun s : α × β ↦ f s.1 + g s.2) (μ.prod ν) := by
  -- Proof comment: unfold convolution and collapse the two transported coordinates into one map
  -- on the product source space.
  rw [Measure.conv]
  rw [Measure.map_prod_map μ ν hf hg]
  have hsumMap :
      ((fun x : LatticePoint D × LatticePoint D ↦ x.1 + x.2) ∘ Prod.map f g) =
        (fun s : α × β ↦ f s.1 + g s.2) := by
    funext s
    cases s
    rfl
  simpa [hsumMap] using
    (Measure.map_map
      (μ := μ.prod ν)
      (g := fun x : LatticePoint D × LatticePoint D ↦ x.1 + x.2)
      (f := Prod.map f g)
      (by fun_prop)
      (by fun_prop))

/-- Helper for Theorem 17.39: the one-step lattice law is the pushforward of the uniform signed
step sampler. -/
private lemma symmetricSimpleRandomWalkStepMeasure_eq_signedCoordinateStepMap
    [NeZero D] :
    (symmetricSimpleRandomWalkStepPMF D).toMeasure =
      Measure.map (signedCoordinateStep D) ((PMF.uniformOfFintype (Bool × Fin D)).toMeasure) := by
  -- Proof comment: this is the defining `PMF.map` presentation of the symmetric step law,
  -- rewritten on the measure surface once.
  simpa [symmetricSimpleRandomWalkStepPMF, signedCoordinateStep] using
    (PMF.toMeasure_map
    (p := PMF.uniformOfFintype (Bool × Fin D))
    (f := signedCoordinateStep D)
    (hf := measurable_of_countable _))

/-- Helper for Theorem 17.39: the finite product of the uniform signed-step marginals is the
uniform measure on the finite word space. -/
private lemma uniformSignedWordPi_eq_uniformMeasure (D m : ℕ) [NeZero D] :
    Measure.pi (fun _ : Fin m ↦ ((PMF.uniformOfFintype (Bool × Fin D)).toMeasure)) =
      (PMF.uniformOfFintype (Fin m → Bool × Fin D)).toMeasure := by
  -- Proof comment: both finite measures assign the same mass to every singleton word.
  refine Measure.ext_of_singleton ?_
  intro w
  rw [Measure.pi_singleton]
  simp [PMF.uniformOfFintype_apply, ENNReal.inv_pow]

/-- Helper for Theorem 17.39: the `m`-step origin law of the symmetric walk is the pushforward of
the iid signed-word product measure by the word-sum map. -/
private lemma symmetricSimpleRandomWalkOriginLaw_eq_signedWordPiMap [NeZero D] :
    ∀ m : ℕ,
      ((dirac_convolution_kernel (symmetricSimpleRandomWalkStepPMF D).toMeasure ^ m)
        (0 : LatticePoint D)) =
        Measure.map (signedStepWordSum D)
          (Measure.pi fun _ : Fin m ↦ ((PMF.uniformOfFintype (Bool × Fin D)).toMeasure))
  | 0 => by
      let cube0 : Measure (Fin 0 → Bool × Fin D) :=
        Measure.pi fun _ : Fin 0 ↦ ((PMF.uniformOfFintype (Bool × Fin D)).toMeasure)
      have hcube0 :
          cube0 = Measure.dirac (Fin.elim0 : Fin 0 → Bool × Fin D) := by
        -- Proof comment: the zero-length word space has a unique point, so its product law is
        -- the corresponding Dirac mass.
        refine Measure.ext_of_singleton ?_
        intro w
        have hw : w = (Fin.elim0 : Fin 0 → Bool × Fin D) := by
          funext i
          exact Fin.elim0 i
        subst hw
        rw [Measure.pi_singleton]
        simp
      change Measure.dirac (0 : LatticePoint D) =
        Measure.map (signedStepWordSum D) cube0
      rw [hcube0, Measure.map_dirac]
      simp [signedStepWordSum]
  | n + 1 => by
      let stepMeasure : Measure (Bool × Fin D) :=
        ((PMF.uniformOfFintype (Bool × Fin D)).toMeasure)
      let cube : (m : ℕ) → Measure (Fin m → Bool × Fin D) :=
        fun m ↦ Measure.pi fun _ : Fin m ↦ stepMeasure
      let κ : Kernel (LatticePoint D) (LatticePoint D) :=
        dirac_convolution_kernel (symmetricSimpleRandomWalkStepPMF D).toMeasure
      let split :
          MeasurableEquiv (Fin (n + 1) → Bool × Fin D)
            ((Bool × Fin D) × (Fin n → Bool × Fin D)) :=
        MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ Bool × Fin D) 0
      have hpow : κ ^ (n + 1) = κ ∘ₖ (κ ^ n) := by
        simpa [pow_one, Nat.one_add] using (ProbabilityTheory.Kernel.pow_add κ 1 n)
      have hsplit :
          (cube (n + 1)).map split = stepMeasure.prod (cube n) := by
        -- Proof comment: `piFinSuccAbove` separates the fresh head step from the old tail word.
        simpa [cube, stepMeasure, Fin.zero_succAbove] using
          (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ stepMeasure) 0).map_eq
      calc
        (κ ^ (n + 1)) (0 : LatticePoint D) = κ ∘ₘ ((κ ^ n) (0 : LatticePoint D)) := by
          rw [hpow, Kernel.comp_apply]
        _ = ((κ ^ n) (0 : LatticePoint D)) ∗ (symmetricSimpleRandomWalkStepPMF D).toMeasure := by
          simpa [κ] using
            (latticeDiracConvolutionKernel_comp_measure_eq_conv
              (D := D)
              (μ := ((κ ^ n) (0 : LatticePoint D)))
              (ν := (symmetricSimpleRandomWalkStepPMF D).toMeasure))
        _ = Measure.map (signedStepWordSum D) (cube n) ∗
              Measure.map (signedCoordinateStep D) stepMeasure := by
              rw [symmetricSimpleRandomWalkOriginLaw_eq_signedWordPiMap n,
                symmetricSimpleRandomWalkStepMeasure_eq_signedCoordinateStepMap (D := D)]
        _ = Measure.map (signedCoordinateStep D) stepMeasure ∗
              Measure.map (signedStepWordSum D) (cube n) := by
              rw [Measure.conv_comm]
        _ = Measure.map
              (fun s : (Bool × Fin D) × (Fin n → Bool × Fin D) ↦
                signedCoordinateStep D s.1 + signedStepWordSum D s.2)
              (stepMeasure.prod (cube n)) := by
              exact latticeMapConv_eq_mapProdSum
                (D := D)
                (μ := stepMeasure)
                (ν := cube n)
                (f := signedCoordinateStep D)
                (g := signedStepWordSum D)
                (measurable_of_countable _)
                (measurable_of_countable _)
        _ = Measure.map
              (fun s : (Bool × Fin D) × (Fin n → Bool × Fin D) ↦
                signedCoordinateStep D s.1 + signedStepWordSum D s.2)
              ((cube (n + 1)).map split) := by
              rw [hsplit]
        _ = Measure.map
              ((fun s : (Bool × Fin D) × (Fin n → Bool × Fin D) ↦
                  signedCoordinateStep D s.1 + signedStepWordSum D s.2) ∘ split)
              (cube (n + 1)) := by
              rw [Measure.map_map (by fun_prop) split.measurable]
        _ = Measure.map (signedStepWordSum D) (cube (n + 1)) := by
              congr 1
              funext w
              -- Proof comment: splitting off the first coordinate rewrites the `(n+1)`-word sum
              -- into the head step plus the old tail-word sum.
              simpa [split, signedStepWordSum] using
                (Fin.sum_univ_succAbove
                  (f := fun j : Fin (n + 1) ↦ signedCoordinateStep D (w j))
                  0).symm

/-- Helper for Theorem 17.39: the `m`-step origin law of the symmetric walk is the pushforward of
the uniform signed-word measure by the word-sum map. -/
private lemma symmetricSimpleRandomWalkOriginLaw_eq_signedWordUniformMeasure [NeZero D]
    (m : ℕ) :
    ((dirac_convolution_kernel (symmetricSimpleRandomWalkStepPMF D).toMeasure ^ m)
      (0 : LatticePoint D)) =
      Measure.map (signedStepWordSum D)
        ((PMF.uniformOfFintype (Fin m → Bool × Fin D)).toMeasure) := by
  -- Proof comment: after identifying the iid product law with the finite uniform word law, the
  -- origin law is exactly the pushforward of that uniform word measure.
  rw [symmetricSimpleRandomWalkOriginLaw_eq_signedWordPiMap (D := D) (m := m)]
  congr 1
  exact uniformSignedWordPi_eq_uniformMeasure D m

/-- Helper for Theorem 17.39: evaluating one signed coordinate step at a fixed coordinate detects
whether that step is the positive or negative move in that coordinate. -/
private lemma signedCoordinateStep_apply (D : ℕ) (s : Bool × Fin D) (i : Fin D) :
    signedCoordinateStep D s i =
      if s = (true, i) then (1 : ℤ) else if s = (false, i) then -1 else 0 := by
  rcases s with ⟨b, j⟩
  by_cases hji : j = i
  · subst hji
    cases b <;> simp [signedCoordinateStep, Prod.mk.injEq]
  · cases b <;> simp [signedCoordinateStep, Prod.mk.injEq, hji]

/-- Helper for Theorem 17.39: the `i`th coordinate of a signed-word sum is the excess of positive
`i`-steps over negative `i`-steps. -/
private lemma signedCoordinateWordSum_apply {D n : ℕ}
    (w : Fin n → Bool × Fin D) (i : Fin D) :
    (∑ j, signedCoordinateStep D (w j)) i =
      ((Finset.univ.filter fun j : Fin n ↦ w j = (true, i)).card : ℤ) -
        ((Finset.univ.filter fun j : Fin n ↦ w j = (false, i)).card : ℤ) := by
  have hcardPos :
      ((Finset.univ.filter fun j : Fin n ↦ w j = (true, i)).card : ℤ) =
        ∑ j : Fin n, if w j = (true, i) then (1 : ℤ) else 0 := by
    exact_mod_cast
      (Finset.card_filter (s := Finset.univ) (p := fun j : Fin n ↦ w j = (true, i)))
  have hcardNeg :
      ((Finset.univ.filter fun j : Fin n ↦ w j = (false, i)).card : ℤ) =
        ∑ j : Fin n, if w j = (false, i) then (1 : ℤ) else 0 := by
    exact_mod_cast
      (Finset.card_filter (s := Finset.univ) (p := fun j : Fin n ↦ w j = (false, i)))
  calc
    (∑ j, signedCoordinateStep D (w j)) i
      = ∑ j : Fin n, (signedCoordinateStep D (w j)) i := by
          simp
    _ = ∑ j : Fin n,
          (if w j = (true, i) then (1 : ℤ) else if w j = (false, i) then -1 else 0) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          rw [signedCoordinateStep_apply]
    _ = ∑ j : Fin n,
          ((if w j = (true, i) then (1 : ℤ) else 0) -
            (if w j = (false, i) then (1 : ℤ) else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          by_cases hpos : w j = (true, i)
          · simp [hpos]
          · by_cases hneg : w j = (false, i)
            · simp [hneg]
            · simp [hneg, hpos]
    _ = (∑ j : Fin n, if w j = (true, i) then (1 : ℤ) else 0) -
          ∑ j : Fin n, if w j = (false, i) then (1 : ℤ) else 0 := by
          rw [Finset.sum_sub_distrib]
    _ = ((Finset.univ.filter fun j : Fin n ↦ w j = (true, i)).card : ℤ) -
          ((Finset.univ.filter fun j : Fin n ↦ w j = (false, i)).card : ℤ) := by
          rw [← hcardPos, ← hcardNeg]

/-- Helper for Theorem 17.39: a signed word returns to the origin exactly when each coordinate is
used equally often with positive and negative sign. -/
private lemma signedStepWordSum_zero_iff_balancedCounts {D n : ℕ}
    (w : Fin n → Bool × Fin D) :
    (∑ j, signedCoordinateStep D (w j)) = 0 ↔
      ∀ i : Fin D,
        (Finset.univ.filter fun j : Fin n ↦ w j = (true, i)).card =
          (Finset.univ.filter fun j : Fin n ↦ w j = (false, i)).card := by
  constructor
  · intro hsum i
    have hcoord := congrFun hsum i
    change (((∑ j, signedCoordinateStep D (w j)) i : ℤ) = 0) at hcoord
    rw [signedCoordinateWordSum_apply] at hcoord
    omega
  · intro hbalance
    ext i
    change (((∑ j, signedCoordinateStep D (w j)) i : ℤ) = 0)
    rw [signedCoordinateWordSum_apply]
    have hEq := hbalance i
    omega

/-- Helper for Theorem 17.39: one planar axis-count summand factors into the square
central-binomial profile. -/
private lemma planarAxisCount_choose_identity (n k : ℕ) :
    Nat.choose (2 * n) (2 * k) * Nat.choose (2 * k) k *
        Nat.choose (2 * n - 2 * k) (n - k) =
      Nat.choose (2 * n) n * Nat.choose n k ^ 2 := by
  by_cases hk : k ≤ n
  · have hsplit :
        Nat.choose (2 * n) (2 * k) * Nat.choose (2 * k) k =
          Nat.choose (2 * n) k * Nat.choose (2 * n - k) k := by
      -- Proof comment: first peel the `2k`-choice into a `k`-choice inside the chosen block.
      simpa [two_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
        (Nat.choose_mul (n := 2 * n) (k := 2 * k) (s := k) (by omega))
    have hmiddle :
        Nat.choose (2 * n - k) k * Nat.choose (2 * n - 2 * k) (n - k) =
          Nat.choose (2 * n - k) n * Nat.choose n k := by
      -- Proof comment: then identify the remaining two factors as another Chu-Vandermonde
      -- instance with `n` total selected positions and `k` of them prescribed.
      have htmp :
          Nat.choose (2 * n - k) n * Nat.choose n k =
            Nat.choose (2 * n - k) k * Nat.choose (2 * n - k - k) (n - k) := by
        simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
          (Nat.choose_mul (n := 2 * n - k) (k := n) (s := k) hk)
      have hsub : 2 * n - k - k = 2 * n - 2 * k := by
        omega
      simpa [hsub] using htmp.symm
    have hcombine :
        Nat.choose (2 * n) k * Nat.choose (2 * n - k) n =
          Nat.choose (2 * n) n * Nat.choose n k := by
      -- Proof comment: the outer and middle choices collapse to the central binomial factor and
      -- one remaining `n.choose k`.
      have hsymm : Nat.choose (2 * n - k) (n - k) = Nat.choose (2 * n - k) n := by
        have htmp := Nat.choose_symm (n := 2 * n - k) (k := n) (by omega)
        have hsub : (2 * n - k) - n = n - k := by
          omega
        simpa [hsub] using htmp
      calc
        Nat.choose (2 * n) k * Nat.choose (2 * n - k) n =
            Nat.choose (2 * n) k * Nat.choose (2 * n - k) (n - k) := by
              rw [← hsymm]
        _ = Nat.choose (2 * n) n * Nat.choose n k := by
              symm
              simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
                (Nat.choose_mul (n := 2 * n) (k := n) (s := k) hk)
    -- Proof comment: chaining the two binomial-factor identities leaves exactly the square
    -- central-binomial profile.
    calc
      Nat.choose (2 * n) (2 * k) * Nat.choose (2 * k) k *
          Nat.choose (2 * n - 2 * k) (n - k)
        = (Nat.choose (2 * n) k * Nat.choose (2 * n - k) k) *
            Nat.choose (2 * n - 2 * k) (n - k) := by
              rw [hsplit]
      _ = Nat.choose (2 * n) k *
            (Nat.choose (2 * n - k) k * Nat.choose (2 * n - 2 * k) (n - k)) := by
              ring
      _ = Nat.choose (2 * n) k * (Nat.choose (2 * n - k) n * Nat.choose n k) := by
              rw [hmiddle]
      _ = (Nat.choose (2 * n) k * Nat.choose (2 * n - k) n) * Nat.choose n k := by
              ring
      _ = (Nat.choose (2 * n) n * Nat.choose n k) * Nat.choose n k := by
              rw [hcombine]
      _ = Nat.choose (2 * n) n * Nat.choose n k ^ 2 := by
              ring
  · have hlt : n < k := Nat.lt_of_not_ge hk
    -- Proof comment: outside `0 ≤ k ≤ n`, the first binomial factor already vanishes.
    have hzero : Nat.choose (2 * n) (2 * k) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have hzero' : Nat.choose n k = 0 := Nat.choose_eq_zero_of_lt hlt
    simp [hzero, hzero']

/-- Helper for Theorem 17.39: once the planar even return mass is written as the axis-count
sum, Vandermonde collapses it to the square central-binomial term. -/
private lemma planarAxisCount_sum_eq_centralBinomialSquare (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        (((Nat.choose (2 * n) (2 * k) * Nat.choose (2 * k) k *
            Nat.choose (2 * n - 2 * k) (n - k) : ℕ) : ℝ) / (4 : ℝ) ^ (2 * n)) =
      (((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n) ^ 2) := by
  calc
    ∑ k ∈ Finset.range (n + 1),
        (((Nat.choose (2 * n) (2 * k) * Nat.choose (2 * k) k *
            Nat.choose (2 * n - 2 * k) (n - k) : ℕ) : ℝ) / (4 : ℝ) ^ (2 * n))
      =
        ∑ k ∈ Finset.range (n + 1),
          (((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n) *
            ((Nat.choose n k : ℝ) ^ 2 / (4 : ℝ) ^ n)) := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            -- Proof comment: replace the triple binomial product with the factorized identity
            -- proved above, then pull the common denominator through.
            have hfactor :
                (((Nat.choose (2 * n) (2 * k) * Nat.choose (2 * k) k *
                    Nat.choose (2 * n - 2 * k) (n - k) : ℕ) : ℝ) / (4 : ℝ) ^ (2 * n)) =
                  ((((Nat.choose (2 * n) n * Nat.choose n k ^ 2 : ℕ) : ℝ) /
                    (4 : ℝ) ^ (2 * n))) := by
              exact congrArg (fun x : ℝ => x / (4 : ℝ) ^ (2 * n)) <|
                congrArg (fun x : ℕ => (x : ℝ)) (planarAxisCount_choose_identity n k)
            have hcast :
                (((Nat.choose (2 * n) n * Nat.choose n k ^ 2 : ℕ) : ℝ)) =
                  ((Nat.choose (2 * n) n : ℝ) * (Nat.choose n k : ℝ) ^ 2) := by
              norm_num
            calc
              (((Nat.choose (2 * n) (2 * k) * Nat.choose (2 * k) k *
                  Nat.choose (2 * n - 2 * k) (n - k) : ℕ) : ℝ) / (4 : ℝ) ^ (2 * n))
                = ((((Nat.choose (2 * n) n * Nat.choose n k ^ 2 : ℕ) : ℝ) /
                    (4 : ℝ) ^ (2 * n))) :=
                    hfactor
              _ = (((Nat.choose (2 * n) n : ℝ) * (Nat.choose n k : ℝ) ^ 2) /
                    (4 : ℝ) ^ (2 * n)) := by
                    rw [hcast]
              _ = (((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n) *
                    ((Nat.choose n k : ℝ) ^ 2 / (4 : ℝ) ^ n)) := by
                    ring
    _ = (((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n) *
          ∑ k ∈ Finset.range (n + 1), ((Nat.choose n k : ℝ) ^ 2 / (4 : ℝ) ^ n)) := by
            rw [Finset.mul_sum]
    _ = (((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n) *
          ((∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℝ) ^ 2) / (4 : ℝ) ^ n)) := by
            congr 1
            rw [div_eq_mul_inv, ← Finset.sum_mul]
    _ = (((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n) *
          ((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n)) := by
            congr 1
            have hsum_choose_sq :
                (∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℝ) ^ 2) =
                  (Nat.choose (2 * n) n : ℝ) := by
              exact_mod_cast Nat.sum_range_choose_sq n
            rw [hsum_choose_sq]
    _ = (((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n) ^ 2) := by
            ring

/-- Helper for Theorem 17.39: duplicating an occupancy profile across both signs factors the
resulting `Bool × Fin D` multinomial coefficient into a central-binomial term times the square of
the underlying `Fin D` multinomial coefficient. -/
private lemma signedOccupancyProfile_multinomial {D n : ℕ} (η : Fin D → ℕ)
    (hη : ∑ i : Fin D, η i = n) :
    Nat.multinomial (Finset.univ : Finset (Bool × Fin D)) (fun s ↦ η s.2) =
      Nat.choose (2 * n) n * Nat.multinomial (Finset.univ : Finset (Fin D)) η ^ 2 := by
  let p : ℕ := ∏ i : Fin D, Nat.factorial (η i)
  have hp_pos : 0 < p := by
    dsimp [p]
    exact Finset.prod_pos fun i _ ↦ Nat.factorial_pos (η i)
  have hprod :
      (∏ s : Bool × Fin D, Nat.factorial (η s.2)) = p ^ 2 := by
    calc
      (∏ s : Bool × Fin D, Nat.factorial (η s.2))
        = ∏ b : Bool, ∏ i : Fin D, Nat.factorial (η i) := by
            simp
      _ = p * p := by
            simp [p]
      _ = p ^ 2 := by
            rw [pow_two]
  have hsum :
      (∑ s : Bool × Fin D, η s.2) = 2 * n := by
    calc
      (∑ s : Bool × Fin D, η s.2) = ∑ b : Bool, ∑ i : Fin D, η i := by
            simp
      _ = n + n := by
            simp [hη]
      _ = 2 * n := by
            omega
  have hbase :
      p * Nat.multinomial (Finset.univ : Finset (Fin D)) η = Nat.factorial n := by
    simpa [p, hη] using
      (Nat.multinomial_spec (s := (Finset.univ : Finset (Fin D))) (f := η))
  have hleft :
      p ^ 2 * Nat.multinomial (Finset.univ : Finset (Bool × Fin D)) (fun s ↦ η s.2) =
        Nat.factorial (2 * n) := by
    simpa [hprod, hsum] using
      (Nat.multinomial_spec
        (s := (Finset.univ : Finset (Bool × Fin D)))
        (f := fun s ↦ η s.2))
  have hright :
      p ^ 2 *
          (Nat.choose (2 * n) n * Nat.multinomial (Finset.univ : Finset (Fin D)) η ^ 2) =
        Nat.factorial (2 * n) := by
    calc
      p ^ 2 *
          (Nat.choose (2 * n) n * Nat.multinomial (Finset.univ : Finset (Fin D)) η ^ 2)
        = Nat.choose (2 * n) n * (p * Nat.multinomial (Finset.univ : Finset (Fin D)) η) ^ 2 := by
            dsimp [p]
            ring
      _ = Nat.choose (2 * n) n * (Nat.factorial n) ^ 2 := by
            rw [hbase]
      _ = Nat.choose (2 * n) n * Nat.factorial n * Nat.factorial n := by
            simp [pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      _ = Nat.factorial (2 * n) := by
            simpa [two_mul] using Nat.add_choose_mul_factorial_mul_factorial n n
  have hp2_pos : 0 < p ^ 2 := by
    exact pow_pos hp_pos 2
  exact Nat.eq_of_mul_eq_mul_left hp2_pos (hleft.trans hright.symm)

/-- Helper for Theorem 17.39: encoding a finite alphabet by `Fintype.equivFin` transports the
multinomial coefficient without changing its value. -/
private lemma multinomial_equivFin {S : Type*} [Fintype S] (k : S → ℕ) :
    Nat.multinomial (Finset.univ : Finset (Fin (Fintype.card S)))
        (fun i ↦ k ((Fintype.equivFin S).symm i)) =
      Nat.multinomial (Finset.univ : Finset S) k := by
  classical
  let e : S ≃ Fin (Fintype.card S) := Fintype.equivFin S
  have hsum :
      (∑ i : Fin (Fintype.card S), k (e.symm i)) = ∑ s : S, k s := by
    simpa [e] using
      (Fintype.sum_equiv e.symm
        (fun i : Fin (Fintype.card S) ↦ k (e.symm i))
        (fun s : S ↦ k s)
        (fun i ↦ by simp))
  have hprod :
      (∏ i : Fin (Fintype.card S), Nat.factorial (k (e.symm i))) =
        ∏ s : S, Nat.factorial (k s) := by
    simpa [e] using
      (Fintype.prod_equiv e.symm
        (fun i : Fin (Fintype.card S) ↦ Nat.factorial (k (e.symm i)))
        (fun s : S ↦ Nat.factorial (k s))
        (fun i ↦ by simp))
  have hleft :
      (∏ s : S, Nat.factorial (k s)) *
          Nat.multinomial (Finset.univ : Finset (Fin (Fintype.card S)))
            (fun i ↦ k (e.symm i)) =
        Nat.factorial (∑ s : S, k s) := by
    calc
      (∏ s : S, Nat.factorial (k s)) *
          Nat.multinomial (Finset.univ : Finset (Fin (Fintype.card S)))
            (fun i ↦ k (e.symm i))
        = (∏ i : Fin (Fintype.card S), Nat.factorial (k (e.symm i))) *
            Nat.multinomial (Finset.univ : Finset (Fin (Fintype.card S)))
              (fun i ↦ k (e.symm i)) := by
              rw [hprod]
      _ = Nat.factorial (∑ i : Fin (Fintype.card S), k (e.symm i)) := by
            simpa using
              (Nat.multinomial_spec
                (s := (Finset.univ : Finset (Fin (Fintype.card S))))
                (f := fun i ↦ k (e.symm i)))
      _ = Nat.factorial (∑ s : S, k s) := by
            rw [hsum]
  have hright :
      (∏ s : S, Nat.factorial (k s)) *
          Nat.multinomial (Finset.univ : Finset S) k =
        Nat.factorial (∑ s : S, k s) := by
    simpa using (Nat.multinomial_spec (s := (Finset.univ : Finset S)) (f := k))
  have hpos : 0 < ∏ s : S, Nat.factorial (k s) := by
    refine Finset.prod_pos ?_
    intro s hs
    exact Nat.factorial_pos (k s)
  exact Nat.eq_of_mul_eq_mul_left hpos (hleft.trans hright.symm)

/-- Helper for Theorem 17.39: under the product law of uniform finite letters, the encoded
coordinates are independent and each coordinate is uniformly distributed on `Fin (card S)`. -/
private lemma encodedUniformProductCoordinateHasLaw
    {S : Type*} [Fintype S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (m : ℕ) :
    let P : Measure (Fin m → S) :=
      Measure.pi fun _ : Fin m ↦ ((PMF.uniformOfFintype S).toMeasure)
    let e : S → Fin (Fintype.card S) := Fintype.equivFin S
    iIndepFun (fun j : Fin m ↦ fun ω : Fin m → S ↦ e (ω j)) P ∧
      ∀ j : Fin m,
        HasLaw
          (fun ω : Fin m → S ↦ e (ω j))
          (((PMF.uniformOfFintype S).map e).toMeasure)
          P := by
  classical
  let P : Measure (Fin m → S) :=
    Measure.pi fun _ : Fin m ↦ ((PMF.uniformOfFintype S).toMeasure)
  let e : S → Fin (Fintype.card S) := Fintype.equivFin S
  have he_meas : Measurable e := measurable_of_finite e
  constructor
  · -- Proof comment: the product coordinates are independent, and composing them with a fixed
    -- encoding map preserves that independence.
    simpa [P, e] using
      (iIndepFun_pi
        (μ := fun _ : Fin m ↦ ((PMF.uniformOfFintype S).toMeasure))
        (X := fun _ : Fin m ↦ e)
        (fun _ ↦ he_meas.aemeasurable))
  · intro j
    have hEval :
        HasLaw (Function.eval j) ((PMF.uniformOfFintype S).toMeasure) P := by
      -- Proof comment: under the product law, every coordinate evaluation recovers the common
      -- one-letter marginal.
      simpa [P] using
        (MeasurePreserving.hasLaw
          (measurePreserving_eval
            (μ := fun _ : Fin m ↦ ((PMF.uniformOfFintype S).toMeasure)) j))
    have hEncode :
        HasLaw e (((PMF.uniformOfFintype S).map e).toMeasure)
          ((PMF.uniformOfFintype S).toMeasure) := by
      refine ⟨he_meas.aemeasurable, ?_⟩
      rw [← PMF.toMeasure_map (p := PMF.uniformOfFintype S) (f := e) he_meas]
    simpa [P, e, Function.comp] using (HasLaw.comp hEncode hEval)

/-- Helper for Theorem 17.39: the duplicated signed profile associated with `η` after encoding the
alphabet `Bool × Fin D` by `Fintype.equivFin`. -/
private def encodedDuplicatedProfile (D : ℕ) (η : Fin D → ℕ) :
    Fin (Fintype.card (Bool × Fin D)) → ℕ :=
  fun i ↦ η ((Fintype.equivFin (Bool × Fin D)).symm i).2

/-- Helper for Theorem 17.39: the encoded duplicated-profile map remembers `η` from the `true`
signed coordinates, so it is injective. -/
private lemma encodedDuplicatedProfile_injective (D : ℕ) :
    Function.Injective (encodedDuplicatedProfile D) := by
  intro η ξ hηξ
  ext i
  have hcoord := congrFun hηξ ((Fintype.equivFin (Bool × Fin D)) (true, i))
  simpa [encodedDuplicatedProfile] using hcoord

/-- Helper for Theorem 17.39: if `η` has total mass `n`, then its duplicated encoded profile on
`Bool × Fin D` has total mass `2 * n`. -/
private lemma sum_encodedDuplicatedProfile {D n : ℕ} (η : Fin D → ℕ)
    (hη : ∑ i : Fin D, η i = n) :
    ∑ i : Fin (Fintype.card (Bool × Fin D)), encodedDuplicatedProfile D η i = 2 * n := by
  let e : Bool × Fin D ≃ Fin (Fintype.card (Bool × Fin D)) := Fintype.equivFin (Bool × Fin D)
  calc
    ∑ i : Fin (Fintype.card (Bool × Fin D)), encodedDuplicatedProfile D η i
      = ∑ s : Bool × Fin D, η s.2 := by
          simpa [encodedDuplicatedProfile, e] using
            (Fintype.sum_equiv e.symm
              (fun i : Fin (Fintype.card (Bool × Fin D)) ↦ encodedDuplicatedProfile D η i)
              (fun s : Bool × Fin D ↦ η s.2)
              (fun i ↦ by simp [encodedDuplicatedProfile, e]))
    _ = n + n := by
          simp [hη]
    _ = 2 * n := by
          ring

/-- Helper for Theorem 17.39: among encoded histograms of length `2 * n`, the balanced ones are
exactly the duplicated profiles coming from `Finset.piAntidiag univ n`. -/
private lemma signedStepWordSum_zero_iff_multinomialCount_memEncodedBalancedProfiles
    {D n : ℕ} [NeZero D] (w : Fin (2 * n) → Bool × Fin D) :
    signedStepWordSum D w = 0 ↔
      multinomialCount
          (fun j : Fin (2 * n) ↦
            fun ω : Fin (2 * n) → Bool × Fin D ↦
              (Fintype.equivFin (Bool × Fin D)) (ω j))
          w ∈
        (Finset.piAntidiag (Finset.univ : Finset (Fin D)) n).image (encodedDuplicatedProfile D) := by
  classical
  let e : Bool × Fin D → Fin (Fintype.card (Bool × Fin D)) := Fintype.equivFin (Bool × Fin D)
  let X :
      Fin (2 * n) → (Fin (2 * n) → Bool × Fin D) → Fin (Fintype.card (Bool × Fin D)) :=
    fun j ω ↦ e (ω j)
  let k : Fin (Fintype.card (Bool × Fin D)) → ℕ := multinomialCount X w
  have hk_eval (s : Bool × Fin D) :
      k (e s) = (Finset.univ.filter fun j : Fin (2 * n) ↦ w j = s).card := by
    -- Proof comment: evaluating the encoded multinomial count at `e s` is exactly the raw
    -- occurrence count of the letter `s`.
    simp [k, X, e, multinomialCount]
  constructor
  · intro hzero
    have hbalance :
        ∀ i : Fin D,
          (Finset.univ.filter fun j : Fin (2 * n) ↦ w j = (true, i)).card =
            (Finset.univ.filter fun j : Fin (2 * n) ↦ w j = (false, i)).card :=
      (signedStepWordSum_zero_iff_balancedCounts (D := D) (w := w)).1 hzero
    let η : Fin D → ℕ := fun i ↦ k (e (true, i))
    have hsumk : ∑ i : Fin (Fintype.card (Bool × Fin D)), k i = 2 * n := by
      simpa [k, X] using
        (sum_multinomialCount (X := X) w)
    have hηsum : ∑ i : Fin D, η i = n := by
      have hsplit :
          ∑ i : Fin (Fintype.card (Bool × Fin D)), k i =
            ∑ s : Bool × Fin D, k (e s) := by
              simpa [e] using
                (Fintype.sum_equiv e
                  (fun i : Fin (Fintype.card (Bool × Fin D)) ↦ k i)
                  (fun s : Bool × Fin D ↦ k (e s))
                  (fun s ↦ by simp))
      calc
        2 * n = ∑ i : Fin (Fintype.card (Bool × Fin D)), k i := hsumk.symm
        _ = ∑ s : Bool × Fin D, k (e s) := hsplit.symm
        _ = ∑ b : Bool, ∑ i : Fin D, k (e (b, i)) := by
              simp
        _ = (∑ i : Fin D, η i) + ∑ i : Fin D, η i := by
              simp [η, hbalance, hk_eval]
        _ = 2 * ∑ i : Fin D, η i := by
              ring
      omega
    have hkshape : k = encodedDuplicatedProfile D η := by
      ext i
      let s : Bool × Fin D := (Fintype.equivFin (Bool × Fin D)).symm i
      rcases s with ⟨b, j⟩
      cases b <;> simp [s, η, encodedDuplicatedProfile, hk_eval, hbalance]
    refine Finset.mem_image.mpr ?_
    refine ⟨η, ?_, hkshape.symm⟩
    simpa [Finset.mem_piAntidiag] using hηsum
  · intro hk
    rcases Finset.mem_image.mp hk with ⟨η, hηmem, hkshape⟩
    have hbalance :
        ∀ i : Fin D,
          (Finset.univ.filter fun j : Fin (2 * n) ↦ w j = (true, i)).card =
            (Finset.univ.filter fun j : Fin (2 * n) ↦ w j = (false, i)).card := by
      intro i
      have htrue := congrFun hkshape ((Fintype.equivFin (Bool × Fin D)) (true, i))
      have hfalse := congrFun hkshape ((Fintype.equivFin (Bool × Fin D)) (false, i))
      simpa [encodedDuplicatedProfile, hk_eval] using htrue.trans hfalse.symm
    exact (signedStepWordSum_zero_iff_balancedCounts (D := D) (w := w)).2 hbalance

/-- Helper for Theorem 17.39: under the histogram law of a uniform signed word of length `2 * n`,
the duplicated profile `encodedDuplicatedProfile D η` has the expected central-binomial
multinomial mass. -/
private lemma encodedDuplicatedProfileHistogramMass_toReal
    {D n : ℕ} [NeZero D] (η : Fin D → ℕ)
    (hη : η ∈ Finset.piAntidiag (Finset.univ : Finset (Fin D)) n) :
    ((((PMF.uniformOfFintype (Fin (2 * n) → Bool × Fin D)).map
        (multinomialCount
          (fun j : Fin (2 * n) ↦
            fun ω : Fin (2 * n) → Bool × Fin D ↦
              (Fintype.equivFin (Bool × Fin D)) (ω j)))
      (encodedDuplicatedProfile D η)).toReal) =
      ((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n) *
        (((Nat.multinomial Finset.univ η : ℝ) / (D : ℝ) ^ n) ^ 2) := by
  classical
  let α : Type := Fin (2 * n) → Bool × Fin D
  let e : Bool × Fin D → Fin (Fintype.card (Bool × Fin D)) := Fintype.equivFin (Bool × Fin D)
  let X : Fin (2 * n) → α → Fin (Fintype.card (Bool × Fin D)) :=
    fun j ω ↦ e (ω j)
  let p : PMF (Fin (Fintype.card (Bool × Fin D))) := (PMF.uniformOfFintype (Bool × Fin D)).map e
  have hηsum : ∑ i : Fin D, η i = n := by
    simpa [Finset.mem_piAntidiag] using hη
  have hp : p = PMF.uniformOfFintype (Fin (Fintype.card (Bool × Fin D))) := by
    ext i
    rw [p, PMF.map_apply]
    refine (tsum_eq_single (e.symm i) ?_).trans ?_
    · intro s hs
      have his : i ≠ e s := by
        intro hi
        apply hs
        simpa using (congrArg e.symm hi).symm
      simp [his]
    · simp [PMF.uniformOfFintype_apply]
  have hmass :
      (((PMF.uniformOfFintype α).map (multinomialCount X)).toMeasure)
          ({encodedDuplicatedProfile D η} :
            Set (Fin (Fintype.card (Bool × Fin D)) → ℕ)) =
        (Nat.multinomial (Finset.univ : Finset (Fin (Fintype.card (Bool × Fin D))))
            (encodedDuplicatedProfile D η) : ENNReal) *
          ∏ i : Fin (Fintype.card (Bool × Fin D)),
            (p i) ^ encodedDuplicatedProfile D η i := by
    rcases encodedUniformProductCoordinateHasLaw (S := Bool × Fin D) (m := 2 * n) with
      ⟨hIndep, hLaw⟩
    rw [PMF.toMeasure_map (p := PMF.uniformOfFintype α) (f := multinomialCount X)
      (hf := measurable_of_countable _)]
    rw [← uniformSignedWordPi_eq_uniformMeasure (D := D) (m := 2 * n)]
    rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
    simpa [X, p] using
      (multinomialCount_preimage_singleton_eq_multinomial_of_sum_eq
        (p := p)
        (X := X)
        hIndep
        hLaw
        (encodedDuplicatedProfile D η)
        (sum_encodedDuplicatedProfile (η := η) hηsum))
  have hprod :
      (∏ i : Fin (Fintype.card (Bool × Fin D)), (p i) ^ encodedDuplicatedProfile D η i) =
        ((2 * D : ℝ≥0∞)⁻¹) ^ (2 * n) := by
    -- Proof comment: the pushed-forward uniform law is still uniform on the encoded alphabet, so
    -- the profile weight is a single constant raised to the total encoded mass `2 * n`.
    rw [Finset.prod_congr rfl]
    · rw [Finset.prod_pow_eq_pow_sum]
      congr 1
      exact sum_encodedDuplicatedProfile (η := η) hηsum
    · intro i hi
      rw [hp]
      simp [PMF.uniformOfFintype_apply]
  have hmult :
      (Nat.multinomial (Finset.univ : Finset (Fin (Fintype.card (Bool × Fin D))))
          (encodedDuplicatedProfile D η) : ℝ) =
        (Nat.choose (2 * n) n : ℝ) * (Nat.multinomial Finset.univ η : ℝ) ^ 2 := by
    have hnat :
        Nat.multinomial (Finset.univ : Finset (Fin (Fintype.card (Bool × Fin D))))
            (encodedDuplicatedProfile D η) =
          Nat.choose (2 * n) n * Nat.multinomial Finset.univ η ^ 2 := by
      calc
        Nat.multinomial (Finset.univ : Finset (Fin (Fintype.card (Bool × Fin D))))
            (encodedDuplicatedProfile D η)
          = Nat.multinomial (Finset.univ : Finset (Bool × Fin D)) (fun s ↦ η s.2) := by
              simpa [encodedDuplicatedProfile] using
                (multinomial_equivFin (k := fun s : Bool × Fin D ↦ η s.2))
        _ = Nat.choose (2 * n) n * Nat.multinomial Finset.univ η ^ 2 := by
              simpa using signedOccupancyProfile_multinomial (η := η) hηsum
    exact_mod_cast hnat
  have hD_ne_zero : (D : ℝ) ≠ 0 := by
    exact_mod_cast (NeZero.ne D)
  have hpowTwo : (2 : ℝ) ^ (2 * n) = (4 : ℝ) ^ n := by
    calc
      (2 : ℝ) ^ (2 * n) = ((2 : ℝ) ^ 2) ^ n := by rw [pow_mul]
      _ = (4 : ℝ) ^ n := by norm_num
  -- Proof comment: convert the multinomial singleton mass to real numbers, factor the encoded
  -- multinomial coefficient, and rewrite the uniform weight `(2D)^{-2n}` as the product of the
  -- central-binomial and occupancy normalizations.
  rw [← PMF.toMeasure_apply_singleton
    (p := (PMF.uniformOfFintype α).map (multinomialCount X))
    (a := encodedDuplicatedProfile D η)
    (h := measurableSet_singleton _)]
  rw [hmass, ENNReal.toReal_mul, hprod, hmult, ENNReal.toReal_pow, ENNReal.toReal_inv]
  simp only [ENNReal.toReal_natCast, ENNReal.toReal_ofNat]
  calc
    (Nat.choose (2 * n) n : ℝ) * (Nat.multinomial Finset.univ η : ℝ) ^ 2 *
        (((2 * D : ℝ≥0∞)⁻¹) ^ (2 * n)).toReal
      = (Nat.choose (2 * n) n : ℝ) * (Nat.multinomial Finset.univ η : ℝ) ^ 2 *
          ((2 * D : ℝ)⁻¹) ^ (2 * n) := by
            simp
    _ = (Nat.choose (2 * n) n : ℝ) * (Nat.multinomial Finset.univ η : ℝ) ^ 2 /
          ((2 * D : ℝ) ^ (2 * n)) := by
            rw [div_eq_mul_inv, inv_pow]
    _ = (Nat.choose (2 * n) n : ℝ) * (Nat.multinomial Finset.univ η : ℝ) ^ 2 /
          ((4 : ℝ) ^ n * (D : ℝ) ^ (2 * n)) := by
            rw [show (2 * D : ℝ) = (2 : ℝ) * D by norm_num, mul_pow, hpowTwo]
    _ = ((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n) *
          (((Nat.multinomial Finset.univ η : ℝ) / (D : ℝ) ^ n) ^ 2) := by
            field_simp [hD_ne_zero]
            ring

/-- Helper for Theorem 17.39: the even origin mass factors into the central-binomial return term
times the collision probability of the uniform `D`-box occupancy profile. -/
private lemma symmetricSimpleRandomWalkEvenOriginMassToReal_eq_centralBinomial_mulOccupancyCollision
    [NeZero D] (n : ℕ) :
    symmetricSimpleRandomWalkEvenOriginMassToReal D n =
      ((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n) *
        ∑ η ∈ Finset.piAntidiag (Finset.univ : Finset (Fin D)) n,
          (((Nat.multinomial Finset.univ η : ℝ) / (D : ℝ) ^ n) ^ 2) := by
  classical
  let α : Type := Fin (2 * n) → Bool × Fin D
  let e : Bool × Fin D → Fin (Fintype.card (Bool × Fin D)) := Fintype.equivFin (Bool × Fin D)
  let X : Fin (2 * n) → α → Fin (Fintype.card (Bool × Fin D)) :=
    fun j ω ↦ e (ω j)
  let A : Finset (Fin (Fintype.card (Bool × Fin D)) → ℕ) :=
    (Finset.piAntidiag (Finset.univ : Finset (Fin D)) n).image (encodedDuplicatedProfile D)
  -- Proof comment: rewrite the even origin event as the encoded balanced-histogram event under
  -- the uniform signed-word law.
  rw [symmetricSimpleRandomWalkEvenOriginMassToReal]
  rw [symmetricSimpleRandomWalkOriginLaw_eq_signedWordUniformMeasure (D := D) (m := 2 * n)]
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton (0 : LatticePoint D))]
  have hzeroEvent :
      signedStepWordSum D ⁻¹' ({0} : Set (LatticePoint D)) =
        multinomialCount X ⁻¹' (A : Set (Fin (Fintype.card (Bool × Fin D)) → ℕ)) := by
    ext w
    simpa [A, X, e] using
      (signedStepWordSum_zero_iff_multinomialCount_memEncodedBalancedProfiles
        (D := D) (n := n) (w := w))
  rw [hzeroEvent]
  -- Proof comment: push the uniform signed-word law through the encoded histogram map and sum
  -- the singleton masses over the injective image of the duplicated profiles.
  rw [← Measure.map_apply (μ := (PMF.uniformOfFintype α).toMeasure)
    (f := multinomialCount X)
    (s := (A : Set (Fin (Fintype.card (Bool × Fin D)) → ℕ)))
    (measurable_of_countable _)
    A.measurableSet]
  rw [← PMF.toMeasure_map (p := PMF.uniformOfFintype α) (f := multinomialCount X)
    (hf := measurable_of_countable _)]
  rw [PMF.toMeasure_apply_finset, ENNReal.toReal_sum]
  · rw [Finset.sum_image]
    · calc
        ∑ η ∈ Finset.piAntidiag (Finset.univ : Finset (Fin D)) n,
            (((PMF.uniformOfFintype α).map (multinomialCount X))
              (encodedDuplicatedProfile D η)).toReal
          = ∑ η ∈ Finset.piAntidiag (Finset.univ : Finset (Fin D)) n,
              ((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n) *
                (((Nat.multinomial Finset.univ η : ℝ) / (D : ℝ) ^ n) ^ 2) := by
                  refine Finset.sum_congr rfl ?_
                  intro η hη
                  simpa [X, e] using
                    (encodedDuplicatedProfileHistogramMass_toReal
                      (D := D) (n := n) (η := η) hη)
        _ = ((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n) *
              ∑ η ∈ Finset.piAntidiag (Finset.univ : Finset (Fin D)) n,
                (((Nat.multinomial Finset.univ η : ℝ) / (D : ℝ) ^ n) ^ 2) := by
                  rw [Finset.mul_sum]
    · intro η hη ξ hξ hEq
      exact (encodedDuplicatedProfile_injective D) hEq
  · intro k hk
    exact ((PMF.uniformOfFintype α).map (multinomialCount X)).apply_ne_top k

/-- Helper for Theorem 17.39: the planar occupancy-collision sum collapses to the normalized
central-binomial term. -/
private lemma occupancyCollision_dimTwo_eq_centralBinomialRatio (n : ℕ) :
    ∑ η ∈ Finset.piAntidiag (Finset.univ : Finset (Fin 2)) n,
        (((Nat.multinomial Finset.univ η : ℝ) / (2 : ℝ) ^ n) ^ 2) =
      ((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n) := by
  calc
    ∑ η ∈ Finset.piAntidiag (Finset.univ : Finset (Fin 2)) n,
        (((Nat.multinomial Finset.univ η : ℝ) / (2 : ℝ) ^ n) ^ 2)
      = ∑ η ∈ Finset.Nat.antidiagonalTuple 2 n,
          (((Nat.multinomial Finset.univ η : ℝ) / (2 : ℝ) ^ n) ^ 2) := by
            rw [Finset.piAntidiag_univ_fin_eq_antidiagonalTuple n 2]
    _ = ∑ ab ∈ Finset.antidiagonal n,
          (((Nat.choose n ab.1 : ℝ) / (2 : ℝ) ^ n) ^ 2) := by
            rw [Finset.Nat.antidiagonalTuple_two]
            rw [Finset.sum_map]
            · refine Finset.sum_congr rfl ?_
              intro ab hab
              have hab_sum : ab.1 + ab.2 = n := Finset.mem_antidiagonal.mp hab
              have hmult :
                  Nat.multinomial (Finset.univ : Finset (Fin 2)) ![ab.1, ab.2] =
                    Nat.choose n ab.1 := by
                calc
                  Nat.multinomial (Finset.univ : Finset (Fin 2)) ![ab.1, ab.2]
                    = Nat.choose (ab.1 + ab.2) ab.2 := by
                        rw [Nat.multinomial_univ_two, Nat.add_choose]
                  _ = Nat.choose n ab.2 := by rw [hab_sum]
                  _ = Nat.choose n ab.1 := by
                        rw [Nat.choose_symm]
                        omega
              simp [hmult]
            · intro a _ b _ hab
              simpa using congrArg (piFinTwoEquiv fun _ ↦ ℕ) hab
    _ = ∑ k ∈ Finset.range (n + 1),
          (((Nat.choose n k : ℝ) / (2 : ℝ) ^ n) ^ 2) := by
            rw [Finset.Nat.antidiagonal_eq_image]
            rw [Finset.sum_image]
            · refine Finset.sum_congr rfl ?_
              intro k hk
              simp
            · intro a _ b _ hab
              exact Prod.mk.inj_1 hab
    _ = ∑ k ∈ Finset.range (n + 1), ((Nat.choose n k : ℝ) ^ 2 / (4 : ℝ) ^ n) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          have hpow : (((2 : ℝ) ^ n) ^ 2) = (4 : ℝ) ^ n := by
            calc
              (((2 : ℝ) ^ n) ^ 2) = (2 : ℝ) ^ (n * 2) := by
                rw [pow_mul]
              _ = (2 : ℝ) ^ (2 * n) := by
                congr 1
                omega
              _ = ((2 : ℝ) ^ 2) ^ n := by
                rw [pow_mul]
              _ = (4 : ℝ) ^ n := by
                norm_num
          calc
            (((Nat.choose n k : ℝ) / (2 : ℝ) ^ n) ^ 2)
              = ((Nat.choose n k : ℝ) ^ 2) / (((2 : ℝ) ^ n) ^ 2) := by
                  ring
            _ = ((Nat.choose n k : ℝ) ^ 2) / (4 : ℝ) ^ n := by
                  rw [hpow]
    _ = (∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℝ) ^ 2) / (4 : ℝ) ^ n := by
          rw [div_eq_mul_inv, Finset.sum_mul]
    _ = ((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n) := by
          have hsum_choose_sq :
              (∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℝ) ^ 2) =
                (Nat.choose (2 * n) n : ℝ) := by
            exact_mod_cast Nat.sum_range_choose_sq n
          rw [hsum_choose_sq]
          ring

/-- Helper for Theorem 17.39: splitting the first coordinate of a `Fin (m + 1)` multinomial
coefficient produces the expected binomial head factor and the tail multinomial coefficient. -/
private lemma multinomialFinSuccSplit (m n r : ℕ) (k : Fin m → ℕ)
    (hk : r + ∑ i : Fin m, k i = n) :
    Nat.multinomial Finset.univ (Fin.cons r k) = n.choose r * Nat.multinomial Finset.univ k := by
  let k' : Fin (m + 1) → ℕ := Fin.cons r k
  let p : ℕ := ∏ i : Fin m, Nat.factorial (k i)
  have hp_pos : 0 < Nat.factorial r * p := by
    -- Proof comment: factorials are positive, so the common denominator can be cancelled.
    refine Nat.mul_pos (Nat.factorial_pos _) ?_
    refine Finset.prod_pos ?_
    intro i _
    exact Nat.factorial_pos _
  have hprod :
      (∏ i : Fin (m + 1), Nat.factorial (k' i)) = Nat.factorial r * p := by
    -- Proof comment: the factorial product splits into the head factor and the tail product.
    simp [k', p, Fin.prod_univ_succ]
  have hsum : ∑ i : Fin (m + 1), k' i = n := by
    -- Proof comment: the total mass is the head count plus the tail total.
    simpa [k', Fin.sum_univ_succ] using hk
  have htailSpec :
      Nat.factorial (∑ i : Fin m, k i) = p * Nat.multinomial Finset.univ k := by
    -- Proof comment: rewrite the tail multinomial coefficient with the shared denominator `p`.
    simpa [p, mul_comm, mul_left_comm, mul_assoc] using
      (Nat.multinomial_spec (s := Finset.univ) (f := k)).symm
  apply Nat.mul_left_cancel hp_pos
  -- Proof comment: rewrite both multinomial coefficients via factorials and isolate the common
  -- binomial factor `n.choose r`.
  calc
    (Nat.factorial r * p) * Nat.multinomial Finset.univ (Fin.cons r k)
        = (∏ i : Fin (m + 1), Nat.factorial (k' i)) *
            Nat.multinomial Finset.univ (Fin.cons r k) := by
            rw [hprod]
    _ = Nat.factorial (∑ i : Fin (m + 1), k' i) := by
          simpa [k'] using (Nat.multinomial_spec (s := Finset.univ) (f := k'))
    _ = Nat.factorial n := by
          rw [hsum]
    _ = n.choose r * (Nat.factorial (∑ i : Fin m, k i) * Nat.factorial r) := by
          simpa [hk, add_comm, add_left_comm, add_assoc, mul_assoc, mul_comm, mul_left_comm] using
            (Nat.add_choose_mul_factorial_mul_factorial (∑ i : Fin m, k i) r).symm
    _ = n.choose r * (Nat.factorial r * (p * Nat.multinomial Finset.univ k)) := by
          rw [htailSpec]
          dsimp [p]
          ac_rfl
    _ = (Nat.factorial r * p) * (n.choose r * Nat.multinomial Finset.univ k) := by
          ac_rfl

/-- Helper for Theorem 17.39: the normalized occupancy atom on `Fin (D + 1)` factors into the
binomial head-count mass and the normalized tail occupancy atom on `Fin D`. -/
private lemma multinomialOccupancyAtom_split_head [NeZero D]
    (n k : ℕ) (ξ : Fin D → ℕ) (hk : k + ∑ i : Fin D, ξ i = n) :
    ((Nat.multinomial Finset.univ (Fin.cons k ξ) : ℝ) / ((D + 1 : ℝ) ^ n)) =
      ((Nat.choose n k : ℝ) * ((1 : ℝ) / (D + 1 : ℝ)) ^ k *
          ((D : ℝ) / (D + 1 : ℝ)) ^ (n - k)) *
        ((Nat.multinomial Finset.univ ξ : ℝ) / (D : ℝ) ^ (n - k)) := by
  have hk_le : k ≤ n := by
    omega
  have hsplit :
      (Nat.multinomial Finset.univ (Fin.cons k ξ) : ℝ) =
        (n.choose k : ℝ) * (Nat.multinomial Finset.univ ξ : ℝ) := by
    exact_mod_cast multinomialFinSuccSplit (m := D) (n := n) (r := k) (k := ξ) hk
  have hD_ne_zero : (D : ℝ) ≠ 0 := by
    exact_mod_cast (NeZero.ne D)
  have hDs_ne_zero : ((D + 1 : ℝ)) ≠ 0 := by
    positivity
  have hpow :
      ((D + 1 : ℝ) ^ n) = ((D + 1 : ℝ) ^ k) * ((D + 1 : ℝ) ^ (n - k)) := by
    rw [← pow_add]
    congr 1
    omega
  -- Proof comment: after factoring the multinomial coefficient, the remaining normalization is
  -- exactly the head binomial mass times the normalized tail occupancy atom.
  calc
    ((Nat.multinomial Finset.univ (Fin.cons k ξ) : ℝ) / ((D + 1 : ℝ) ^ n))
      = (((n.choose k : ℝ) * (Nat.multinomial Finset.univ ξ : ℝ)) /
          (((D + 1 : ℝ) ^ k) * ((D + 1 : ℝ) ^ (n - k))) := by
            rw [hsplit, hpow]
    _ =
        ((Nat.choose n k : ℝ) * ((1 : ℝ) / (D + 1 : ℝ)) ^ k *
            ((D : ℝ) / (D + 1 : ℝ)) ^ (n - k)) *
          ((Nat.multinomial Finset.univ ξ : ℝ) / (D : ℝ) ^ (n - k)) := by
            field_simp [hD_ne_zero, hDs_ne_zero]
            ring

/-- Helper for Theorem 17.39: the planar even return mass is exactly the square of the normalized
central-binomial term. -/
private lemma symmetricSimpleRandomWalkOriginMass_even_dimTwo_toReal (n : ℕ) :
    symmetricSimpleRandomWalkEvenOriginMassToReal 2 n =
      (((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n) ^ 2) := by
  -- Proof comment: the exact histogram bridge reduces the planar return mass to the occupancy
  -- collision sum, and the already-proved two-box identity closes that collision term.
  rw [symmetricSimpleRandomWalkEvenOriginMassToReal_eq_centralBinomial_mulOccupancyCollision
    (D := 2) (n := n)]
  rw [occupancyCollision_dimTwo_eq_centralBinomialRatio]
  ring

/-- Helper for Theorem 17.39: the normalized central-binomial term has the uniform
`(n + 1)^(-1/2)` upper bound needed in the transient branch. -/
private lemma centralBinomialReturnProbability_le_two_mul_rpow (n : ℕ) :
    ((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n) ≤
      2 * (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) := by
  let x : ℝ := ((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n)
  let y : ℝ := 2 * (n + 1 : ℝ) ^ (-(1 / 2 : ℝ))
  have hx_nonneg : 0 ≤ x := by
    dsimp [x]
    positivity
  have hy_nonneg : 0 ≤ y := by
    dsimp [y]
    positivity
  have hsq : x ^ 2 ≤ y ^ 2 := by
    have hsq_raw :
        x ^ 2 ≤ 4 / (Real.pi * (n + 1 : ℝ)) := by
      simpa [x] using centralBinomialReturnProbability_sq_le_fourPiInv_div_succ n
    have hpi : (1 : ℝ) ≤ Real.pi := by
      linarith [Real.pi_gt_three]
    have hden :
        4 / (Real.pi * (n + 1 : ℝ)) ≤ 4 / (n + 1 : ℝ) := by
      have hpos : 0 < (n + 1 : ℝ) := by
        positivity
      have hmul : (n + 1 : ℝ) ≤ Real.pi * (n + 1 : ℝ) := by
        nlinarith
      have hrecip : 1 / (Real.pi * (n + 1 : ℝ)) ≤ 1 / (n + 1 : ℝ) := by
        exact one_div_le_one_div_of_le (by positivity) hmul
      exact mul_le_mul_of_nonneg_left hrecip (by positivity)
    have hy_sq :
        y ^ 2 = 4 / (n + 1 : ℝ) := by
      have hpow_sqrt :
          (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt (n + 1 : ℝ) := by
        rw [Real.rpow_neg (by positivity)]
        rw [show (n + 1 : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt (n + 1 : ℝ) by
          rw [Real.sqrt_eq_rpow]
          positivity]
      rw [hpow_sqrt]
      field_simp [Real.sqrt_ne_zero'.mpr (by positivity)]
      ring
    exact hsq_raw.trans (by simpa [hy_sq])
  -- Proof comment: nonnegativity lets us pass from the squared upper bound to the linear one.
  have hxy : x ≤ y := by
    nlinarith
  simpa [x, y] using hxy

/-- Helper for Theorem 17.39: the planar occupancy collision already has the expected
`(n + 1)^(-1/2)` decay. -/
private lemma uniformOccupancyCollision_dimTwo_le_const_rpow :
    ∃ C > 0, ∀ n : ℕ,
      ∑ η ∈ Finset.piAntidiag (Finset.univ : Finset (Fin 2)) n,
        (((Nat.multinomial Finset.univ η : ℝ) / (2 : ℝ) ^ n) ^ 2) ≤
          C * (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) := by
  refine ⟨2, by positivity, ?_⟩
  intro n
  -- Proof comment: the two-box collision sum is exactly the central-binomial return term, so the
  -- dedicated `n^(-1/2)` estimate closes the base case.
  rw [occupancyCollision_dimTwo_eq_centralBinomialRatio]
  exact centralBinomialReturnProbability_le_two_mul_rpow n

/-- Helper for Theorem 17.39: the central-binomial return factor also has the matching
lower `(n + 1)^(-1/2)` bound needed to recover the occupancy collision from the exact bridge. -/
private lemma centralBinomialReturnProbability_ge_piInvSqrt_mul_rpow (n : ℕ) :
    (1 / Real.sqrt Real.pi) * (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) ≤
      ((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n) := by
  let x : ℝ := ((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n)
  let y : ℝ := (1 / Real.sqrt Real.pi) * (n + 1 : ℝ) ^ (-(1 / 2 : ℝ))
  have hx_nonneg : 0 ≤ x := by
    dsimp [x]
    positivity
  have hy_nonneg : 0 ≤ y := by
    dsimp [y]
    positivity
  have hy_sq : y ^ 2 = 1 / (Real.pi * (n + 1 : ℝ)) := by
    have hsqrt_pi :
        (1 / Real.sqrt Real.pi) ^ 2 = 1 / Real.pi := by
      field_simp [Real.sqrt_ne_zero'.mpr Real.pi_pos]
      ring
    have hpow_sqrt :
        (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt (n + 1 : ℝ) := by
      rw [Real.rpow_neg (by positivity)]
      rw [show (n + 1 : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt (n + 1 : ℝ) by
        rw [Real.sqrt_eq_rpow]
        positivity]
    rw [show y = (1 / Real.sqrt Real.pi) * (1 / Real.sqrt (n + 1 : ℝ)) by
      simp [y, hpow_sqrt]]
    rw [mul_pow, hsqrt_pi]
    field_simp [Real.sqrt_ne_zero'.mpr (by positivity)]
    ring
  have hsq : y ^ 2 ≤ x ^ 2 := by
    simpa [x, hy_sq] using centralBinomialReturnProbability_sq_ge_piInv_div_succ n
  have hxy : y ≤ x := by
    nlinarith
  simpa [x, y] using hxy

/-- Helper for Theorem 17.39: summing over `Fin (m + 1)` occupancy profiles can be reindexed by
the head count and the tail profile on `Fin m`. -/
private lemma sumPiAntidiagFinSucc {α : Type*} [AddCommMonoid α]
    (m n : ℕ) (F : (Fin (m + 1) → ℕ) → α) :
    ∑ η ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (m + 1))) n, F η =
      ∑ ab ∈ Finset.antidiagonal n,
        ∑ ξ ∈ Finset.piAntidiag (Finset.univ : Finset (Fin m)) ab.2,
          F (Fin.cons ab.1 ξ) := by
  have hpi :
      Finset.piAntidiag (Finset.univ : Finset (Fin (m + 1))) n =
        Finset.finAntidiagonal (m + 1) n := by
    ext η
    simp [Finset.mem_finAntidiagonal]
  have hpiTailAux :
      ∀ r : ℕ,
        (↑(Finset.finAntidiagonal.aux m r) : Finset (Fin m → ℕ)) =
          Finset.piAntidiag (Finset.univ : Finset (Fin m)) r := by
    intro r
    ext ξ
    constructor
    · intro hξ
      have hξ' : ξ ∈ Finset.finAntidiagonal m r := by
        simpa [Finset.finAntidiagonal] using hξ
      simpa [Finset.mem_finAntidiagonal] using hξ'
    · intro hξ
      have hξ' : ξ ∈ Finset.finAntidiagonal m r := by
        simpa [Finset.mem_finAntidiagonal] using hξ
      simpa [Finset.finAntidiagonal] using hξ'
  rw [hpi]
  -- Proof comment: `finAntidiagonal` on `Fin (m + 1)` unfolds by splitting the head coordinate
  -- and ranging the tail over the corresponding lower-dimensional antidiagonal.
  simp only [Finset.finAntidiagonal, Finset.finAntidiagonal.aux]
  rw [Finset.sum_disjiUnion]
  refine Finset.sum_congr rfl ?_
  intro ab hab
  rw [Finset.sum_map]
  rw [hpiTailAux ab.2]
  refine Finset.sum_congr rfl ?_
  intro ξ hξ
  rfl

/-- Helper for Theorem 17.39: the normalized occupancy masses on `D` boxes form a probability
distribution on `Finset.piAntidiag univ n`. -/
private lemma uniformOccupancyMass_sum_eq_one [NeZero D] (n : ℕ) :
    ∑ η ∈ Finset.piAntidiag (Finset.univ : Finset (Fin D)) n,
      ((Nat.multinomial Finset.univ η : ℝ) / (D : ℝ) ^ n) = 1 := by
  have hsum :
      ((D : ℝ) ^ n) =
        ∑ η ∈ Finset.piAntidiag (Finset.univ : Finset (Fin D)) n,
          (Nat.multinomial Finset.univ η : ℝ) := by
    -- Proof comment: this is the multinomial theorem specialized to the constant function `1`.
    simpa using
      (Finset.sum_pow_eq_sum_piAntidiag
        (s := (Finset.univ : Finset (Fin D)))
        (f := fun _ : Fin D ↦ (1 : ℝ))
        n)
  have hD_ne_zero : (D : ℝ) ≠ 0 := by
    exact_mod_cast (NeZero.ne D)
  -- Proof comment: divide the multinomial identity by the common normalization factor `D ^ n`.
  calc
    ∑ η ∈ Finset.piAntidiag (Finset.univ : Finset (Fin D)) n,
        ((Nat.multinomial Finset.univ η : ℝ) / (D : ℝ) ^ n)
      = ∑ η ∈ Finset.piAntidiag (Finset.univ : Finset (Fin D)) n,
          (Nat.multinomial Finset.univ η : ℝ) * ((D : ℝ) ^ n)⁻¹ := by
            refine Finset.sum_congr rfl ?_
            intro η hη
            rw [div_eq_mul_inv]
    _ = (∑ η ∈ Finset.piAntidiag (Finset.univ : Finset (Fin D)) n,
            (Nat.multinomial Finset.univ η : ℝ)) * ((D : ℝ) ^ n)⁻¹ := by
          rw [Finset.sum_mul]
    _ = ((D : ℝ) ^ n) / (D : ℝ) ^ n := by
          rw [hsum, div_eq_mul_inv]
    _ = 1 := by
          field_simp [hD_ne_zero]

/-- Helper for Theorem 17.39: every occupancy collision sum is at most `1`, since it is the
`L²`-norm square of a finite probability mass function. -/
private lemma uniformOccupancyCollision_le_one [NeZero D] (n : ℕ) :
    ∑ η ∈ Finset.piAntidiag (Finset.univ : Finset (Fin D)) n,
      (((Nat.multinomial Finset.univ η : ℝ) / (D : ℝ) ^ n) ^ 2) ≤ 1 := by
  let p : (Fin D → ℕ) → ℝ :=
    fun η ↦ ((Nat.multinomial Finset.univ η : ℝ) / (D : ℝ) ^ n)
  have hp_nonneg :
      ∀ η : Fin D → ℕ, 0 ≤ p η := by
    intro η
    dsimp [p]
    positivity
  have hp_le_one :
      ∀ η ∈ Finset.piAntidiag (Finset.univ : Finset (Fin D)) n, p η ≤ 1 := by
    intro η hη
    have hsingle :
        p η ≤
          ∑ ξ ∈ Finset.piAntidiag (Finset.univ : Finset (Fin D)) n, p ξ := by
      exact Finset.single_le_sum (fun ξ hξ ↦ hp_nonneg ξ) hη
    simpa [p, uniformOccupancyMass_sum_eq_one (D := D) n] using hsingle
  -- Proof comment: on each atom, `p η ∈ [0, 1]`, so `p η ^ 2 ≤ p η`; summing preserves that bound.
  calc
    ∑ η ∈ Finset.piAntidiag (Finset.univ : Finset (Fin D)) n, (p η) ^ 2
      ≤ ∑ η ∈ Finset.piAntidiag (Finset.univ : Finset (Fin D)) n, p η := by
          refine Finset.sum_le_sum ?_
          intro η hη
          nlinarith [hp_nonneg η, hp_le_one η hη]
    _ = 1 := uniformOccupancyMass_sum_eq_one (D := D) n

/-- Helper for Theorem 17.39: after splitting off the head box, the `(D + 1)`-box occupancy
collision sum becomes a head-binomial square times the `D`-box tail collision sum. -/
private lemma uniformOccupancyCollisionSucc_eq_headWeightedSum [NeZero D] (n : ℕ) :
    ∑ η ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (D + 1))) n,
      (((Nat.multinomial Finset.univ η : ℝ) / ((D + 1 : ℝ) ^ n)) ^ 2) =
      ∑ ab ∈ Finset.antidiagonal n,
        (((Nat.choose n ab.1 : ℝ) * ((1 : ℝ) / (D + 1 : ℝ)) ^ ab.1 *
            ((D : ℝ) / (D + 1 : ℝ)) ^ ab.2) ^ 2) *
          ∑ ξ ∈ Finset.piAntidiag (Finset.univ : Finset (Fin D)) ab.2,
            (((Nat.multinomial Finset.univ ξ : ℝ) / (D : ℝ) ^ ab.2) ^ 2) := by
  -- Proof comment: reindex the `Fin (D + 1)` antidiagonal by the head count and the tail profile,
  -- then apply the exact factorization of each normalized occupancy atom.
  rw [sumPiAntidiagFinSucc (m := D) (n := n) (F := fun η ↦
    (((Nat.multinomial Finset.univ η : ℝ) / ((D + 1 : ℝ) ^ n)) ^ 2))]
  refine Finset.sum_congr rfl ?_
  intro ab hab
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro ξ hξ
  have hab_sum : ab.1 + ab.2 = n := Finset.mem_antidiagonal.mp hab
  have hξsum : ∑ i : Fin D, ξ i = ab.2 := by
    simpa [Finset.mem_piAntidiag] using hξ
  have hsplit : ab.1 + ∑ i : Fin D, ξ i = n := by
    omega
  have htail : n - ab.1 = ab.2 := by
    omega
  rw [multinomialOccupancyAtom_split_head (D := D) (n := n) (k := ab.1) (ξ := ξ) hsplit]
  rw [htail]
  ring

/-- Helper for Theorem 17.39: a uniform `L∞` bound on normalized occupancy atoms controls the
collision sum by `L² ≤ L∞ · L¹`. -/
private lemma occupancyCollision_le_of_atomBound [NeZero D] {B : ℕ → ℝ}
    (hB : ∀ n η, η ∈ Finset.piAntidiag (Finset.univ : Finset (Fin D)) n →
      ((Nat.multinomial Finset.univ η : ℝ) / (D : ℝ) ^ n) ≤ B n) :
    ∀ n : ℕ,
      ∑ η ∈ Finset.piAntidiag (Finset.univ : Finset (Fin D)) n,
        (((Nat.multinomial Finset.univ η : ℝ) / (D : ℝ) ^ n) ^ 2) ≤ B n := by
  intro n
  let p : (Fin D → ℕ) → ℝ :=
    fun η ↦ ((Nat.multinomial Finset.univ η : ℝ) / (D : ℝ) ^ n)
  have hp_nonneg : ∀ η : Fin D → ℕ, 0 ≤ p η := by
    intro η
    dsimp [p]
    positivity
  have hp_sq_le :
      ∀ η ∈ Finset.piAntidiag (Finset.univ : Finset (Fin D)) n, (p η) ^ 2 ≤ B n * p η := by
    intro η hη
    have hpB : p η ≤ B n := hB n η hη
    -- Proof comment: each atom is nonnegative, so the pointwise majorant `p η ≤ B n` upgrades
    -- directly to `p η ^ 2 ≤ B n * p η`.
    nlinarith [hp_nonneg η, hpB]
  -- Proof comment: sum the pointwise `L² ≤ L∞ · L¹` estimate and collapse the `L¹` term with the
  -- normalized occupancy-mass identity.
  calc
    ∑ η ∈ Finset.piAntidiag (Finset.univ : Finset (Fin D)) n, (p η) ^ 2
      ≤ ∑ η ∈ Finset.piAntidiag (Finset.univ : Finset (Fin D)) n, B n * p η := by
          refine Finset.sum_le_sum ?_
          intro η hη
          exact hp_sq_le η hη
    _ = B n * ∑ η ∈ Finset.piAntidiag (Finset.univ : Finset (Fin D)) n, p η := by
          rw [← Finset.mul_sum]
    _ = B n * ∑ η ∈ Finset.piAntidiag (Finset.univ : Finset (Fin D)) n,
          ((Nat.multinomial Finset.univ η : ℝ) / (D : ℝ) ^ n) := by
          rfl
    _ = B n := by
          rw [uniformOccupancyMass_sum_eq_one (D := D) n]
          ring

/-- Helper for Theorem 17.39: permuting the boxes of an occupancy profile preserves the
multinomial coefficient. -/
private lemma multinomialOccupancyAtom_reindex {D : ℕ}
    (e : Fin D ≃ Fin D) (η : Fin D → ℕ) :
    (Nat.multinomial Finset.univ (η ∘ e) : ℝ) = (Nat.multinomial Finset.univ η : ℝ) := by
  -- Proof comment: the multinomial coefficient depends only on the multiset of occupation
  -- counts, so reindexing by a finite permutation leaves both the total sum and factorial product
  -- unchanged.
  have hnat :
      Nat.multinomial (Finset.univ : Finset (Fin D)) (η ∘ e) =
        Nat.multinomial (Finset.univ : Finset (Fin D)) η := by
    have hsum : (∑ i : Fin D, η (e i)) = ∑ i : Fin D, η i := by
      simpa using
        (Fintype.sum_equiv e
          (fun i : Fin D ↦ η (e i))
          (fun i : Fin D ↦ η i)
          (fun i ↦ by simp))
    have hprod :
        (∏ i : Fin D, Nat.factorial (η (e i))) = ∏ i : Fin D, Nat.factorial (η i) := by
      simpa using
        (Fintype.prod_equiv e
          (fun i : Fin D ↦ Nat.factorial (η (e i)))
          (fun i : Fin D ↦ Nat.factorial (η i))
          (fun i ↦ by simp))
    have hleft :
        (∏ i : Fin D, Nat.factorial (η i)) *
            Nat.multinomial (Finset.univ : Finset (Fin D)) (η ∘ e) =
          Nat.factorial (∑ i : Fin D, η i) := by
      calc
        (∏ i : Fin D, Nat.factorial (η i)) *
            Nat.multinomial (Finset.univ : Finset (Fin D)) (η ∘ e)
          = (∏ i : Fin D, Nat.factorial (η (e i))) *
              Nat.multinomial (Finset.univ : Finset (Fin D)) (η ∘ e) := by
                rw [hprod]
        _ = Nat.factorial (∑ i : Fin D, η (e i)) := by
              simpa using
                (Nat.multinomial_spec
                  (s := (Finset.univ : Finset (Fin D)))
                  (f := η ∘ e))
        _ = Nat.factorial (∑ i : Fin D, η i) := by
              rw [hsum]
    have hright :
        (∏ i : Fin D, Nat.factorial (η i)) *
            Nat.multinomial (Finset.univ : Finset (Fin D)) η =
          Nat.factorial (∑ i : Fin D, η i) := by
      simpa using
        (Nat.multinomial_spec (s := (Finset.univ : Finset (Fin D))) (f := η))
    have hpos : 0 < ∏ i : Fin D, Nat.factorial (η i) := by
      refine Finset.prod_pos ?_
      intro i hi
      exact Nat.factorial_pos (η i)
    exact Nat.eq_of_mul_eq_mul_left hpos (hleft.trans hright.symm)
  exact_mod_cast hnat

/-- Helper for Theorem 17.39: the head factor that appears when one box is split off from a
`(D + 1)`-box occupancy atom. -/
private def occupancyHeadMass (D n k : ℕ) : ℝ :=
  (Nat.choose n k : ℝ) * ((1 : ℝ) / (D + 1 : ℝ)) ^ k *
    ((D : ℝ) / (D + 1 : ℝ)) ^ (n - k)

/-- Helper for Theorem 17.39: consecutive head masses differ by the exact binomial ratio. -/
private lemma occupancyHeadMassSucc_ratio [NeZero D] {n k : ℕ} (hk : k < n) :
    occupancyHeadMass D n (k + 1) =
      occupancyHeadMass D n k * (((n - k : ℝ) / (k + 1 : ℝ)) / D) := by
  have hD_ne_zero : (D : ℝ) ≠ 0 := by
    exact_mod_cast (NeZero.ne D)
  have hDs_ne_zero : ((D + 1 : ℝ)) ≠ 0 := by
    positivity
  have hk1_ne_zero : (k + 1 : ℝ) ≠ 0 := by
    positivity
  have htail : n - k = n - (k + 1) + 1 := by
    omega
  have hchoose :
      (Nat.choose n (k + 1) : ℝ) =
        (Nat.choose n k : ℝ) * ((n - k : ℝ) / (k + 1 : ℝ)) := by
    have hchoose_nat : Nat.choose n (k + 1) * (k + 1) = Nat.choose n k * (n - k) :=
      Nat.choose_succ_right_eq n k
    field_simp [hk1_ne_zero]
    simpa [mul_assoc, mul_left_comm, mul_comm] using congrArg (fun m : ℕ ↦ (m : ℝ)) hchoose_nat
  -- Proof comment: rewrite the binomial coefficient by the standard successor ratio and peel one
  -- factor from the tail power, so the remaining scalar factor is exactly `((n-k)/(k+1))/D`.
  calc
    occupancyHeadMass D n (k + 1)
      = (Nat.choose n (k + 1) : ℝ) * ((1 : ℝ) / (D + 1 : ℝ)) ^ (k + 1) *
          ((D : ℝ) / (D + 1 : ℝ)) ^ (n - (k + 1)) := by
            rfl
    _ = ((Nat.choose n k : ℝ) * ((n - k : ℝ) / (k + 1 : ℝ))) *
          (((1 : ℝ) / (D + 1 : ℝ)) ^ k * ((1 : ℝ) / (D + 1 : ℝ))) *
          ((D : ℝ) / (D + 1 : ℝ)) ^ (n - (k + 1)) := by
            rw [hchoose, pow_succ]
    _ = ((Nat.choose n k : ℝ) * ((1 : ℝ) / (D + 1 : ℝ)) ^ k *
          ((D : ℝ) / (D + 1 : ℝ)) ^ (n - k)) *
          (((n - k : ℝ) / (k + 1 : ℝ)) / D) := by
            rw [htail, pow_succ]
            field_simp [hD_ne_zero, hDs_ne_zero, hk1_ne_zero]
            ring
    _ = occupancyHeadMass D n k * (((n - k : ℝ) / (k + 1 : ℝ)) / D) := by
          rfl

/-- Helper for Theorem 17.39: the head-binomial weights form a normalized probability mass
function. -/
private lemma occupancyHeadMass_sum_eq_one [NeZero D] (n : ℕ) :
    ∑ k in Finset.range (n + 1), occupancyHeadMass D n k = 1 := by
  have hbase :
      ((1 : ℝ) / (D + 1 : ℝ)) + ((D : ℝ) / (D + 1 : ℝ)) = 1 := by
    field_simp
    ring
  -- Proof comment: this is the binomial theorem for the two probabilities
  -- `1 / (D + 1)` and `D / (D + 1)`, whose sum is `1`.
  calc
    ∑ k in Finset.range (n + 1), occupancyHeadMass D n k
      = (((1 : ℝ) / (D + 1 : ℝ)) + ((D : ℝ) / (D + 1 : ℝ))) ^ n := by
          symm
          simpa [occupancyHeadMass, mul_assoc, mul_left_comm, mul_comm] using
            (add_pow ((1 : ℝ) / (D + 1 : ℝ)) ((D : ℝ) / (D + 1 : ℝ)) n)
    _ = 1 := by
          rw [hbase]
          simp

/-- Helper for Theorem 17.39: Stirling's formula gives a uniform upper bound for factorials that
is strong enough for the head-mode estimate. -/
private lemma factorial_le_stirling_exp_mul_sqrt {n : ℕ} (hn : n ≠ 0) :
    (n ! : ℝ) ≤ Real.exp 1 * Real.sqrt n * (n / Real.exp 1) ^ n := by
  rcases n with _ | n
  · cases hn rfl
  have hanti : Stirling.stirlingSeq (n + 1) ≤ Stirling.stirlingSeq 1 := by
    simpa using (Stirling.stirlingSeq'_antitone (show 0 ≤ n by exact Nat.zero_le _))
  have hpos :
      0 < Real.sqrt (2 * (n + 1 : ℝ)) * ((n + 1 : ℝ) / Real.exp 1) ^ (n + 1) := by
    positivity
  have hmul :
      ((n + 1)! : ℝ) ≤
        (Real.exp 1 / Real.sqrt 2) *
          (Real.sqrt (2 * (n + 1 : ℝ)) * ((n + 1 : ℝ) / Real.exp 1) ^ (n + 1)) := by
    rw [Stirling.stirlingSeq, Stirling.stirlingSeq_one] at hanti
    exact (div_le_iff₀ hpos).mp hanti
  have hsqrt :
      (Real.exp 1 / Real.sqrt 2) * Real.sqrt (2 * (n + 1 : ℝ)) =
        Real.exp 1 * Real.sqrt (n + 1 : ℝ) := by
    have hsqrt_mul :
        Real.sqrt (2 * (n + 1 : ℝ)) = Real.sqrt 2 * Real.sqrt (n + 1 : ℝ) := by
      rw [show (2 * (n + 1 : ℝ)) = (2 : ℝ) * (n + 1 : ℝ) by ring]
      rw [Real.sqrt_mul (by positivity)]
      positivity
    rw [hsqrt_mul]
    field_simp [Real.sqrt_ne_zero'.mpr (by positivity)]
    ring
  -- Proof comment: `stirlingSeq` is decreasing, so the time-`1` value controls every later
  -- factorial after the normalization is cleared.
  calc
    ((n + 1)! : ℝ)
      ≤ (Real.exp 1 / Real.sqrt 2) *
          (Real.sqrt (2 * (n + 1 : ℝ)) * ((n + 1 : ℝ) / Real.exp 1) ^ (n + 1)) := hmul
    _ = ((Real.exp 1 / Real.sqrt 2) * Real.sqrt (2 * (n + 1 : ℝ))) *
          (((n + 1 : ℝ) / Real.exp 1) ^ (n + 1)) := by
            ring
    _ = Real.exp 1 * Real.sqrt (n + 1 : ℝ) * (((n + 1 : ℝ) / Real.exp 1) ^ (n + 1)) := by
          rw [hsqrt]
    _ = Real.exp 1 * Real.sqrt (n + 1 : ℝ) * ((n + 1 : ℝ) / Real.exp 1) ^ (n + 1) := rfl

/-- Helper for Theorem 17.39: after reindexing by a suitable permutation, the head occupancy is
at most the average occupancy `n / (D + 1)`. -/
private lemma occupancyProfile_reindex_head_le_average
    (D n : ℕ) (η : Fin (D + 1) → ℕ)
    (hη : η ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (D + 1))) n) :
    ∃ e : Fin (D + 1) ≃ Fin (D + 1), (η ∘ e) 0 ≤ n / (D + 1) := by
  classical
  obtain ⟨i, -, hi_min⟩ :=
    Finset.exists_min_image (Finset.univ : Finset (Fin (D + 1))) η Finset.univ_nonempty
  have hsum : ∑ j : Fin (D + 1), η j = n := by
    simpa [Finset.mem_piAntidiag] using hη
  have hi_avg : η i ≤ n / (D + 1) := by
    by_contra hi
    have hi_succ : n / (D + 1) + 1 ≤ η i := Nat.succ_le_of_lt (Nat.lt_of_not_ge hi)
    have hlower : ∀ j : Fin (D + 1), n / (D + 1) + 1 ≤ η j := by
      intro j
      exact le_trans hi_succ (hi_min j (by simp))
    have hsum_lower :
        (D + 1) * (n / (D + 1) + 1) ≤ ∑ j : Fin (D + 1), η j := by
      calc
        ∑ j : Fin (D + 1), (n / (D + 1) + 1)
          ≤ ∑ j : Fin (D + 1), η j := by
              refine Finset.sum_le_sum ?_
              intro j hj
              exact hlower j
        _ = (D + 1) * (n / (D + 1) + 1) := by
              simp [Finset.card_univ]
    have : (D + 1) * (n / (D + 1) + 1) ≤ n := by
      simpa [hsum] using hsum_lower
    omega
  refine ⟨Equiv.swap 0 i, ?_⟩
  -- Proof comment: send the minimizing coordinate to the head position `0`; the average bound on
  -- that minimum is exactly the required left-of-mean estimate.
  simpa using hi_avg

/-- Helper for Theorem 17.39: on the left-of-mean range, the head binomial mass is monotone in
the head count. -/
private lemma occupancyHeadMass_step_mono [NeZero D] {n k : ℕ}
    (hk : k + 1 ≤ n / (D + 1)) :
    occupancyHeadMass D n k ≤ occupancyHeadMass D n (k + 1) := by
  have hklt : k < n := by
    have hk1_le_n : k + 1 ≤ n := le_trans hk (Nat.div_le_self _ _)
    exact lt_of_lt_of_le (Nat.lt_succ_self k) hk1_le_n
  have hnonneg : 0 ≤ occupancyHeadMass D n k := by
    positivity
  have hfactor_nat : D * (k + 1) ≤ n - k := by
    omega
  have hD_pos : 0 < (D : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne D)
  have hk1_pos : 0 < (k + 1 : ℝ) := by
    positivity
  have hfactor_ge_one : 1 ≤ (((n - k : ℝ) / (k + 1 : ℝ)) / D) := by
    have hfactor_real : (D : ℝ) * (k + 1 : ℝ) ≤ (n - k : ℝ) := by
      exact_mod_cast hfactor_nat
    have hfactor_eq :
        (((n - k : ℝ) / (k + 1 : ℝ)) / D) = (n - k : ℝ) / ((D : ℝ) * (k + 1 : ℝ)) := by
      field_simp [show (D : ℝ) ≠ 0 by exact_mod_cast (NeZero.ne D),
        show (k + 1 : ℝ) ≠ 0 by positivity]
      ring
    rw [hfactor_eq]
    exact (one_le_div_iff (by positivity)).2 hfactor_real
  -- Proof comment: the exact ratio from `occupancyHeadMassSucc_ratio` is at least `1` on the
  -- left-of-mean range, so the sequence is monotone there.
  rw [occupancyHeadMassSucc_ratio (D := D) hklt]
  simpa [one_mul] using mul_le_mul_of_nonneg_left hfactor_ge_one hnonneg

/-- Helper for Theorem 17.39: every left-of-mean head mass is bounded by the mode value at
`n / (D + 1)`. -/
private lemma occupancyHeadMass_le_mode [NeZero D] {n k : ℕ}
    (hk : k ≤ n / (D + 1)) :
    occupancyHeadMass D n k ≤ occupancyHeadMass D n (n / (D + 1)) := by
  have hiter :
      ∀ t : ℕ, k + t ≤ n / (D + 1) →
        occupancyHeadMass D n k ≤ occupancyHeadMass D n (k + t) := by
    intro t
    induction t with
    | zero =>
        intro ht
        simp
    | succ t iht =>
        intro ht
        have hkt : k + t ≤ n / (D + 1) := by
          omega
        have hstep :
            occupancyHeadMass D n (k + t) ≤ occupancyHeadMass D n (k + t + 1) := by
          simpa [Nat.add_assoc] using
            (occupancyHeadMass_step_mono (D := D) (n := n) (k := k + t) ht)
        exact le_trans (iht hkt) hstep
  -- Proof comment: iterate the one-step monotonicity from `k` up to the left-of-mean endpoint
  -- `n / (D + 1)`.
  simpa [Nat.add_sub_of_le hk] using
    hiter (n / (D + 1) - k) (by omega)

/-- Helper for Theorem 17.39: in the large-`n` regime, the floor-average head count
`n / (D + 1)` is positive and both `k` and `n - k` are comparable to `n`. -/
private lemma occupancyHeadMass_floorAverage_large_bounds [NeZero D] {n : ℕ}
    (hn : 2 * (D + 1) ≤ n) :
    let k := n / (D + 1)
    1 ≤ k ∧ n ≤ 2 * (D + 1) * k ∧ D * n ≤ (D + 1) * (n - k) := by
  let k := n / (D + 1)
  have hk_pos : 1 ≤ k := by
    dsimp [k]
    exact (Nat.one_le_div_iff (Nat.succ_pos D)).2 (by omega)
  have hdecomp : n = (D + 1) * k + n % (D + 1) := by
    dsimp [k]
    exact (Nat.div_add_mod n (D + 1)).symm
  have hmod_lt : n % (D + 1) < D + 1 := Nat.mod_lt _ (Nat.succ_pos D)
  have hlarge : n ≤ 2 * (D + 1) * k := by
    calc
      n = (D + 1) * k + n % (D + 1) := hdecomp
      _ ≤ (D + 1) * k + (D + 1) := by
            gcongr
            exact Nat.le_of_lt hmod_lt
      _ ≤ (D + 1) * k + (D + 1) * k := by
            gcongr
      _ = 2 * (D + 1) * k := by ring
  have hk_mul_le : (D + 1) * k ≤ n := by
    dsimp [k]
    exact Nat.div_mul_le_self _ _
  have htail_large : D * n ≤ (D + 1) * (n - k) := by
    omega
  exact ⟨hk_pos, hlarge, htail_large⟩

/-- Helper for Theorem 17.39: the floor-correction factor in the large-`n` mode estimate is
uniformly bounded by `exp 1`. -/
private lemma occupancyHeadMassFloorQuotient_pow_le_exp [NeZero D] {n : ℕ}
    (hn : 2 * (D + 1) ≤ n) :
    let k := n / (D + 1)
    ((n : ℝ) / ((D + 1 : ℝ) * k)) ^ k ≤ Real.exp 1 := by
  let k := n / (D + 1)
  rcases occupancyHeadMass_floorAverage_large_bounds (D := D) hn with ⟨hk_pos, -, -⟩
  have hk_pos_real : 0 < (k : ℝ) := by
    positivity
  have hdecomp : n = (D + 1) * k + n % (D + 1) := by
    dsimp [k]
    exact (Nat.div_add_mod n (D + 1)).symm
  have hnum_lt_nat : n < (D + 1) * (k + 1) := by
    have hmod_lt : n % (D + 1) < D + 1 := Nat.mod_lt _ (Nat.succ_pos D)
    calc
      n = (D + 1) * k + n % (D + 1) := hdecomp
      _ < (D + 1) * k + (D + 1) := by
            gcongr
      _ = (D + 1) * (k + 1) := by ring
  have hquot_lt :
      (n : ℝ) / ((D + 1 : ℝ) * k) < 1 + 1 / (k : ℝ) := by
    have hden_pos : 0 < ((D + 1 : ℝ) * k) := by positivity
    have hnum_lt :
        (n : ℝ) < ((D + 1 : ℝ) * (k + 1 : ℝ)) := by
      exact_mod_cast hnum_lt_nat
    have hdiv_lt :
        (n : ℝ) / ((D + 1 : ℝ) * k) <
          (((D + 1 : ℝ) * (k + 1 : ℝ)) / (((D + 1 : ℝ) * k))) := by
      exact div_lt_div_of_pos_right hnum_lt hden_pos
    refine hdiv_lt.trans_eq ?_
    field_simp [show (k : ℝ) ≠ 0 by positivity]
    ring
  have hquot_pow :
      ((n : ℝ) / ((D + 1 : ℝ) * k)) ^ k ≤ (1 + 1 / (k : ℝ)) ^ k := by
    exact pow_le_pow_left₀ (by positivity) hquot_lt.le k
  have hstep :
      (1 + 1 / (k : ℝ)) ^ k ≤ (Real.exp (1 / (k : ℝ))) ^ k := by
    exact pow_le_pow_left₀ (by positivity) (Real.add_one_le_exp (1 / (k : ℝ))) k
  calc
    ((n : ℝ) / ((D + 1 : ℝ) * k)) ^ k
      ≤ (Real.exp (1 / (k : ℝ))) ^ k := hquot_pow.trans hstep
    _ = Real.exp ((k : ℝ) * (1 / (k : ℝ))) := by
          rw [← Real.exp_nat_mul]
    _ = Real.exp 1 := by
          field_simp [show (k : ℝ) ≠ 0 by positivity]

/-- Helper for Theorem 17.39: rewriting `occupancyHeadMass` through factorials isolates the
Stirling denominator factors. -/
private lemma occupancyHeadMass_eq_factorial_ratio {D n k : ℕ} (hk : k ≤ n) :
    occupancyHeadMass D n k =
      ((Nat.factorial n : ℝ) / ((Nat.factorial k : ℝ) * (Nat.factorial (n - k) : ℝ))) *
        ((1 : ℝ) / (D + 1 : ℝ)) ^ k *
        ((D : ℝ) / (D + 1 : ℝ)) ^ (n - k) := by
  have hchoose :
      (Nat.choose n k : ℝ) =
        (Nat.factorial n : ℝ) / ((Nat.factorial k : ℝ) * (Nat.factorial (n - k) : ℝ)) := by
    have hden :
        ((Nat.factorial k : ℝ) * (Nat.factorial (n - k) : ℝ)) ≠ 0 := by
      positivity
    apply (eq_div_iff hden).2
    have hnat :
        ((Nat.choose n k * Nat.factorial k * Nat.factorial (n - k) : ℕ) : ℝ) =
          (Nat.factorial n : ℝ) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk
    ring_nf at hnat ⊢
    simpa [Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using hnat
  -- Proof comment: this is just the standard factorial expression for the binomial coefficient,
  -- inserted into the explicit head-mass formula.
  rw [occupancyHeadMass, hchoose]

/-- Helper for Theorem 17.39: in the large-`n` regime, the floor-average head mass already has an
explicit inverse-square-root bound. -/
private lemma headBinomialMode_large_le_const_invSqrt [NeZero D] {n : ℕ}
    (hn : 2 * (D + 1) ≤ n) :
    occupancyHeadMass D n (n / (D + 1)) ≤
      (2 * Real.exp 2 * (D + 1 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  let k := n / (D + 1)
  rcases occupancyHeadMass_floorAverage_large_bounds (D := D) hn with ⟨hk_one, hlarge, htail⟩
  have hk_pos : 0 < k := Nat.succ_le_iff.mp hk_one
  have hk_le_n : k ≤ n := by
    dsimp [k]
    exact Nat.div_le_self _ _
  have hk_add : k + (n - k) = n := Nat.add_sub_of_le hk_le_n
  have hn_nat_pos : 0 < n := by
    have hbase_pos : 0 < 2 * (D + 1) := by positivity
    exact lt_of_lt_of_le hbase_pos hn
  have htail_nat_pos : 0 < n - k := by
    have hD_one : 1 ≤ D := Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne D))
    have hn_le_Dn : n ≤ D * n := by
      simpa using Nat.mul_le_mul_right n hD_one
    have htail_nat : n ≤ (D + 1) * (n - k) := le_trans hn_le_Dn htail
    exact Nat.pos_of_mul_pos_left (lt_of_lt_of_le hn_nat_pos htail_nat)
  have hk_pos_real : 0 < (k : ℝ) := by exact_mod_cast hk_pos
  have htail_pos_real : 0 < (n - k : ℝ) := by exact_mod_cast htail_nat_pos
  have hn_pos_real : 0 < (n : ℝ) := by exact_mod_cast hn_nat_pos
  have hrewrite :=
    occupancyHeadMass_eq_factorial_ratio (D := D) (n := n) (k := k) hk_le_n
  rw [hrewrite]
  set denLower : ℝ :=
    (Real.sqrt (2 * Real.pi * k) * ((k : ℝ) / Real.exp 1) ^ k) *
      (Real.sqrt (2 * Real.pi * (n - k)) * ((n - k : ℝ) / Real.exp 1) ^ (n - k))
  have hnum_upper :
      (Nat.factorial n : ℝ) ≤ Real.exp 1 * Real.sqrt n * (n / Real.exp 1) ^ n := by
    exact factorial_le_stirling_exp_mul_sqrt (n := n) (by omega)
  have hk_lower : Real.sqrt (2 * Real.pi * k) * ((k : ℝ) / Real.exp 1) ^ k ≤ (k ! : ℝ) := by
    simpa using Stirling.le_factorial_stirling k
  have htail_lower :
      Real.sqrt (2 * Real.pi * (n - k)) * ((n - k : ℝ) / Real.exp 1) ^ (n - k) ≤
        ((n - k)! : ℝ) := by
    simpa using Stirling.le_factorial_stirling (n - k)
  have hdenLower_le :
      denLower ≤ ((Nat.factorial k : ℝ) * (Nat.factorial (n - k) : ℝ)) := by
    dsimp [denLower]
    exact mul_le_mul hk_lower htail_lower (by positivity) (by positivity)
  have hdenLower_pos : 0 < denLower := by
    dsimp [denLower]
    positivity
  have hratio_le :
      ((Nat.factorial n : ℝ) / ((Nat.factorial k : ℝ) * (Nat.factorial (n - k) : ℝ))) ≤
        (Real.exp 1 * Real.sqrt n * (n / Real.exp 1) ^ n) / denLower := by
    have hstep_den :
        ((Nat.factorial n : ℝ) / ((Nat.factorial k : ℝ) * (Nat.factorial (n - k) : ℝ))) ≤
          ((Nat.factorial n : ℝ) / denLower) := by
      exact div_le_div_of_nonneg_left (by positivity) hdenLower_pos hdenLower_le
    have hstep_num :
        ((Nat.factorial n : ℝ) / denLower) ≤
          (Real.exp 1 * Real.sqrt n * (n / Real.exp 1) ^ n) / denLower := by
      exact div_le_div_of_nonneg_right hnum_upper (by positivity)
    exact hstep_den.trans hstep_num
  have hpow_nonneg :
      0 ≤ ((1 : ℝ) / (D + 1 : ℝ)) ^ k * ((D : ℝ) / (D + 1 : ℝ)) ^ (n - k) := by
    positivity
  have hmain_le :
      (((Nat.factorial n : ℝ) / ((Nat.factorial k : ℝ) * (Nat.factorial (n - k) : ℝ))) *
          ((1 : ℝ) / (D + 1 : ℝ)) ^ k *
          ((D : ℝ) / (D + 1 : ℝ)) ^ (n - k)) ≤
        (((Real.exp 1 * Real.sqrt n * (n / Real.exp 1) ^ n) / denLower) *
          ((1 : ℝ) / (D + 1 : ℝ)) ^ k *
          ((D : ℝ) / (D + 1 : ℝ)) ^ (n - k)) := by
    exact mul_le_mul_of_nonneg_right hratio_le hpow_nonneg
  have hfactor :
      (((Real.exp 1 * Real.sqrt n * (n / Real.exp 1) ^ n) / denLower) *
          ((1 : ℝ) / (D + 1 : ℝ)) ^ k *
          ((D : ℝ) / (D + 1 : ℝ)) ^ (n - k)) =
        (((Real.exp 1 * Real.sqrt n) /
            (Real.sqrt (2 * Real.pi * k) * Real.sqrt (2 * Real.pi * (n - k)))) *
          ((n : ℝ) / ((D + 1 : ℝ) * k)) ^ k *
          (((D : ℝ) * n) / ((D + 1 : ℝ) * (n - k))) ^ (n - k)) := by
    have hk_ne : (k : ℝ) ≠ 0 := by positivity
    have htail_ne : (n - k : ℝ) ≠ 0 := by positivity
    have hDs_ne : ((D + 1 : ℝ)) ≠ 0 := by positivity
    have hexp_ne : Real.exp 1 ≠ 0 := by positivity
    have hkPow_ne : ((k : ℝ) / Real.exp 1) ^ k ≠ 0 := by positivity
    have htailPow_ne : ((n - k : ℝ) / Real.exp 1) ^ (n - k) ≠ 0 := by positivity
    have hsqrtk_ne : Real.sqrt (2 * Real.pi * k) ≠ 0 := by
      apply Real.sqrt_ne_zero'.mpr
      positivity
    have hsqrttail_ne : Real.sqrt (2 * Real.pi * (n - k)) ≠ 0 := by
      apply Real.sqrt_ne_zero'.mpr
      positivity
    dsimp [denLower]
    rw [← hk_add, pow_add]
    field_simp [hk_ne, htail_ne, hDs_ne, hexp_ne, hkPow_ne, htailPow_ne, hsqrtk_ne, hsqrttail_ne]
    ring
  have hquot_le_exp :
      ((n : ℝ) / ((D + 1 : ℝ) * k)) ^ k ≤ Real.exp 1 := by
    simpa [k] using occupancyHeadMassFloorQuotient_pow_le_exp (D := D) hn
  have htail_base_le_one :
      (((D : ℝ) * n) / ((D + 1 : ℝ) * (n - k))) ≤ 1 := by
    refine (div_le_iff (by positivity)).2 ?_
    exact_mod_cast htail
  have htail_factor_le_one :
      (((D : ℝ) * n) / ((D + 1 : ℝ) * (n - k))) ^ (n - k) ≤ 1 := by
    exact (pow_le_pow_left₀ (by positivity) htail_base_le_one (n - k)).trans_eq (by simp)
  have hsqrtk_le :
      Real.sqrt (k : ℝ) ≤ Real.sqrt (2 * Real.pi * k) := by
    refine Real.sqrt_le_sqrt ?_
    positivity
    nlinarith [Real.pi_gt_three, hk_pos_real]
  have hsqrttail_le :
      Real.sqrt (n - k : ℝ) ≤ Real.sqrt (2 * Real.pi * (n - k)) := by
    refine Real.sqrt_le_sqrt ?_
    positivity
    nlinarith [Real.pi_gt_three, htail_pos_real]
  have hsqrt_factor_le :
      ((Real.exp 1 * Real.sqrt n) /
          (Real.sqrt (2 * Real.pi * k) * Real.sqrt (2 * Real.pi * (n - k)))) ≤
        Real.exp 1 * (Real.sqrt n / (Real.sqrt k * Real.sqrt (n - k))) := by
    have hden_compare :
        Real.sqrt (k : ℝ) * Real.sqrt (n - k : ℝ) ≤
          Real.sqrt (2 * Real.pi * k) * Real.sqrt (2 * Real.pi * (n - k)) := by
      exact mul_le_mul hsqrtk_le hsqrttail_le (by positivity) (by positivity)
    exact
      (div_le_div_of_nonneg_left (by positivity) (by positivity) hden_compare).trans_eq
        (by ring)
  have hsqrt_bound :
      Real.sqrt n / (Real.sqrt k * Real.sqrt (n - k)) ≤
        (2 * (D + 1 : ℝ)) / Real.sqrt n := by
    have htail_linear_nat : n ≤ (D + 1) * (n - k) := by
      have hD_one : 1 ≤ D := Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne D))
      have hn_le_Dn : n ≤ D * n := by
        simpa using Nat.mul_le_mul_right n hD_one
      exact le_trans hn_le_Dn htail
    have hlarge_real : (n : ℝ) ≤ (2 * (D + 1 : ℝ)) * k := by
      exact_mod_cast hlarge
    have htail_real : (n : ℝ) ≤ (D + 1 : ℝ) * (n - k) := by
      exact_mod_cast htail_linear_nat
    have hquad :
        (n : ℝ) ^ 2 ≤ ((2 * (D + 1 : ℝ)) ^ 2) * ((k : ℝ) * (n - k : ℝ)) := by
      nlinarith
    have htarget :
        (n : ℝ) / ((k : ℝ) * (n - k : ℝ)) ≤ ((2 * (D + 1 : ℝ)) ^ 2) / (n : ℝ) := by
      exact (div_le_div_iff (by positivity) hn_pos_real).2 hquad
    have hlhs_sq :
        (Real.sqrt n / (Real.sqrt k * Real.sqrt (n - k))) ^ 2 =
          (n : ℝ) / ((k : ℝ) * (n - k : ℝ)) := by
      field_simp [show Real.sqrt (k : ℝ) ≠ 0 by exact Real.sqrt_ne_zero'.mpr hk_pos_real,
        show Real.sqrt (n - k : ℝ) ≠ 0 by exact Real.sqrt_ne_zero'.mpr htail_pos_real]
      ring_nf
      rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    have hrhs_sq :
        (((2 * (D + 1 : ℝ)) / Real.sqrt n) ^ 2) = ((2 * (D + 1 : ℝ)) ^ 2) / (n : ℝ) := by
      field_simp [show Real.sqrt (n : ℝ) ≠ 0 by exact Real.sqrt_ne_zero'.mpr hn_pos_real]
      ring_nf
      rw [Real.sq_sqrt (by positivity)]
    have hsq : (Real.sqrt n / (Real.sqrt k * Real.sqrt (n - k))) ^ 2 ≤
        (((2 * (D + 1 : ℝ)) / Real.sqrt n) ^ 2) := by
      rw [hlhs_sq, hrhs_sq]
      exact htarget
    nlinarith [show 0 ≤ Real.sqrt n / (Real.sqrt k * Real.sqrt (n - k)) by positivity,
      show 0 ≤ (2 * (D + 1 : ℝ)) / Real.sqrt n by positivity, hsq]
  have hrpow_sqrt :
      (n : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt n := by
    rw [Real.rpow_neg (by positivity)]
    rw [show (n : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt n by
      rw [Real.sqrt_eq_rpow]
      positivity]
  have hcore :
      (((Real.exp 1 * Real.sqrt n) /
            (Real.sqrt (2 * Real.pi * k) * Real.sqrt (2 * Real.pi * (n - k)))) *
          ((n : ℝ) / ((D + 1 : ℝ) * k)) ^ k *
          (((D : ℝ) * n) / ((D + 1 : ℝ) * (n - k))) ^ (n - k)) ≤
        (2 * Real.exp 2 * (D + 1 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
    have hstep1 :
        (((Real.exp 1 * Real.sqrt n) /
              (Real.sqrt (2 * Real.pi * k) * Real.sqrt (2 * Real.pi * (n - k)))) *
            ((n : ℝ) / ((D + 1 : ℝ) * k)) ^ k *
            (((D : ℝ) * n) / ((D + 1 : ℝ) * (n - k))) ^ (n - k)) ≤
          (((Real.exp 1 * Real.sqrt n) /
              (Real.sqrt (2 * Real.pi * k) * Real.sqrt (2 * Real.pi * (n - k)))) *
            Real.exp 1) := by
      have hmul :
          (((Real.exp 1 * Real.sqrt n) /
                (Real.sqrt (2 * Real.pi * k) * Real.sqrt (2 * Real.pi * (n - k)))) *
              ((n : ℝ) / ((D + 1 : ℝ) * k)) ^ k) *
            (((D : ℝ) * n) / ((D + 1 : ℝ) * (n - k))) ^ (n - k) ≤
          (((Real.exp 1 * Real.sqrt n) /
                (Real.sqrt (2 * Real.pi * k) * Real.sqrt (2 * Real.pi * (n - k)))) *
              Real.exp 1) * 1 := by
        exact mul_le_mul hquot_le_exp htail_factor_le_one (by positivity) (by positivity)
      simpa [mul_assoc] using hmul
    have hstep2 :
        (((Real.exp 1 * Real.sqrt n) /
              (Real.sqrt (2 * Real.pi * k) * Real.sqrt (2 * Real.pi * (n - k)))) *
            Real.exp 1) ≤
          (2 * Real.exp 2 * (D + 1 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
      have htemp :
          (((Real.exp 1 * Real.sqrt n) /
                (Real.sqrt (2 * Real.pi * k) * Real.sqrt (2 * Real.pi * (n - k)))) *
              Real.exp 1) ≤
            (Real.exp 1 * (Real.sqrt n / (Real.sqrt k * Real.sqrt (n - k)))) * Real.exp 1 := by
        exact mul_le_mul_of_nonneg_right hsqrt_factor_le (by positivity)
      have htemp' :
          (Real.exp 1 * (Real.sqrt n / (Real.sqrt k * Real.sqrt (n - k)))) * Real.exp 1 ≤
            (Real.exp 1 * ((2 * (D + 1 : ℝ)) / Real.sqrt n)) * Real.exp 1 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsqrt_bound (by positivity)) (by positivity)
      refine htemp.trans (htemp'.trans ?_)
      rw [mul_assoc, show Real.exp 1 * Real.exp 1 = Real.exp 2 by
        rw [← Real.exp_add]
        norm_num]
      rw [hrpow_sqrt, div_eq_mul_inv]
      ring
    exact hstep1.trans hstep2
  exact hmain_le.trans (by rw [hfactor]; exact hcore)

/-- Helper for Theorem 17.39: the floor-average head count already has the required
`(n + 1)^(-1/2)` decay. -/
private lemma headBinomialMode_le_const_rpow [NeZero D] :
    ∃ C > 0, ∀ n : ℕ,
      occupancyHeadMass D n (n / (D + 1)) ≤ C * (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) := by
  refine ⟨(4 * Real.exp 2 + 2) * (D + 1 : ℝ), by positivity, ?_⟩
  intro n
  by_cases hn_large : 2 * (D + 1) ≤ n
  · have hlarge :=
      headBinomialMode_large_le_const_invSqrt (D := D) hn_large
    have hn_nat_pos : 0 < n := by
      have hbase_pos : 0 < 2 * (D + 1) := by positivity
      exact lt_of_lt_of_le hbase_pos hn_large
    have hsqrt_compare : Real.sqrt (n + 1 : ℝ) ≤ 2 * Real.sqrt n := by
      have hsq :
          (Real.sqrt (n + 1 : ℝ)) ^ 2 ≤ (2 * Real.sqrt n) ^ 2 := by
        rw [Real.sq_sqrt (by positivity)]
        nlinarith
      have hnonneg : 0 ≤ 2 * Real.sqrt n := by positivity
      nlinarith
    have haux : 1 / (2 * Real.sqrt n) ≤ 1 / Real.sqrt (n + 1 : ℝ) := by
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hsqrt_compare
    have hrpow_compare :
        (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 2 * (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) := by
      have hrpow_n :
          (n : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt n := by
        rw [Real.rpow_neg (by positivity)]
        rw [show (n : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt n by
          rw [Real.sqrt_eq_rpow]
          positivity]
      have hrpow_succ :
          (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt (n + 1 : ℝ) := by
        rw [Real.rpow_neg (by positivity)]
        rw [show (n + 1 : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt (n + 1 : ℝ) by
          rw [Real.sqrt_eq_rpow]
          positivity]
      have hscaled := mul_le_mul_of_nonneg_left haux (by positivity : 0 ≤ (2 : ℝ))
      rw [hrpow_n, hrpow_succ] at hscaled
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hscaled
    -- Proof comment: the large-`n` Stirling estimate gives the mode bound at scale `n^(-1/2)`,
    -- and `n + 1 ≤ 4 n` upgrades it to the requested shifted normalization.
    calc
      occupancyHeadMass D n (n / (D + 1))
        ≤ (2 * Real.exp 2 * (D + 1 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ)) := hlarge
      _ ≤ ((4 * Real.exp 2) * (D + 1 : ℝ)) * (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) := by
            gcongr
      _ ≤ ((4 * Real.exp 2 + 2) * (D + 1 : ℝ)) * (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) := by
            gcongr
  · have hmass_nonneg : 0 ≤ occupancyHeadMass D n (n / (D + 1)) := by
      positivity
    have hmass_le_one : occupancyHeadMass D n (n / (D + 1)) ≤ 1 := by
      have hsum_eq : ∑ k in Finset.range (n + 1), occupancyHeadMass D n k = 1 :=
        occupancyHeadMass_sum_eq_one (D := D) n
      have hsingle :
          occupancyHeadMass D n (n / (D + 1)) ≤
            ∑ k in Finset.range (n + 1), occupancyHeadMass D n k := by
        refine Finset.single_le_sum ?_ ?_
        · intro k hk
          positivity
        · simpa using Nat.div_le_self n (D + 1)
      simpa [hsum_eq] using hsingle
    have hsmall_nat : n + 1 ≤ 2 * (D + 1) := by
      omega
    have hsmall_real : (n + 1 : ℝ) ≤ 2 * (D + 1 : ℝ) := by
      exact_mod_cast hsmall_nat
    have hrpow_small :
        1 ≤ (2 * (D + 1 : ℝ)) * (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) := by
      have hsqrt_le : Real.sqrt (n + 1 : ℝ) ≤ Real.sqrt (2 * (D + 1 : ℝ)) := by
        exact Real.sqrt_le_sqrt (by positivity) hsmall_real
      have haux :
          1 / Real.sqrt (2 * (D + 1 : ℝ)) ≤ 1 / Real.sqrt (n + 1 : ℝ) := by
        exact div_le_div_of_nonneg_left (by positivity) (by positivity) hsqrt_le
      have hrpow_succ :
          (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt (n + 1 : ℝ) := by
        rw [Real.rpow_neg (by positivity)]
        rw [show (n + 1 : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt (n + 1 : ℝ) by
          rw [Real.sqrt_eq_rpow]
          positivity]
      have hmul :=
        mul_le_mul_of_nonneg_left haux (by positivity : 0 ≤ Real.sqrt (2 * (D + 1 : ℝ)))
      have hsqrt_sq :
          (Real.sqrt (2 * (D + 1 : ℝ))) ^ 2 = 2 * (D + 1 : ℝ) := by
        rw [Real.sq_sqrt]
        positivity
      rw [hrpow_succ] at hmul
      have : 1 ≤ Real.sqrt (2 * (D + 1 : ℝ)) * (1 / Real.sqrt (n + 1 : ℝ)) := by
        simpa [hsqrt_sq, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
      have hsqrt_two_le : Real.sqrt (2 * (D + 1 : ℝ)) ≤ 2 * (D + 1 : ℝ) := by
        have hsq :
            (Real.sqrt (2 * (D + 1 : ℝ))) ^ 2 ≤ (2 * (D + 1 : ℝ)) ^ 2 := by
          rw [Real.sq_sqrt]
          nlinarith
        have hnonneg : 0 ≤ 2 * (D + 1 : ℝ) := by positivity
        nlinarith
      nlinarith [this, hsqrt_two_le]
    -- Proof comment: below the large-`n` threshold, the head-binomial atom is a single
    -- probability mass, so the uniform bound `≤ 1` can be absorbed into a fixed constant.
    calc
      occupancyHeadMass D n (n / (D + 1))
        ≤ 1 := hmass_le_one
      _ ≤ (2 * (D + 1 : ℝ)) * (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) := hrpow_small
      _ ≤ ((4 * Real.exp 2 + 2) * (D + 1 : ℝ)) * (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) := by
            gcongr

/-- Helper for Theorem 17.39: the analytic head-binomial input reduces the induction step to a
single one-dimensional `O((n + 1)^(-1/2))` bound. -/
private lemma headBinomialAtom_leftOfMean_le_const_rpow [NeZero D] :
    ∃ C > 0, ∀ n k : ℕ,
      k ≤ n / (D + 1) →
        occupancyHeadMass D n k ≤ C * (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) := by
  rcases headBinomialMode_le_const_rpow (D := D) with ⟨C, hC_pos, hC⟩
  refine ⟨C, hC_pos, ?_⟩
  intro n k hk
  -- Proof comment: once the floor-average mode is controlled, left-of-mean monotonicity reduces
  -- every smaller head count to that single mode value.
  exact (occupancyHeadMass_le_mode (D := D) hk).trans (hC n)

/-- Helper for Theorem 17.39: if the head count stays at most at the average `n / (m + 2)`, then
the shifted tail scale loses at most the factor `(m + 2)^(m/2)` in negative-`rpow` form. -/
private lemma shiftedTailRpow_le_averageFactor {m n k : ℕ}
    (hk : k ≤ n / (m + 2)) :
    (n - k + 1 : ℝ) ^ (-((m : ℝ) / 2)) ≤
      (m + 2 : ℝ) ^ ((m : ℝ) / 2) * (n + 1 : ℝ) ^ (-((m : ℝ) / 2)) := by
  have hscale_nat : n + 1 ≤ (m + 2) * (n - k + 1) := by
    omega
  have hscale_real : (n + 1 : ℝ) ≤ (m + 2 : ℝ) * (n - k + 1 : ℝ) := by
    exact_mod_cast hscale_nat
  have hm_nonneg : 0 ≤ (m : ℝ) / 2 := by
    positivity
  have hpow :
      (n + 1 : ℝ) ^ ((m : ℝ) / 2) ≤
        ((m + 2 : ℝ) * (n - k + 1 : ℝ)) ^ ((m : ℝ) / 2) := by
    exact Real.rpow_le_rpow (by positivity) hscale_real hm_nonneg
  have hpow' :
      (n + 1 : ℝ) ^ ((m : ℝ) / 2) ≤
        (m + 2 : ℝ) ^ ((m : ℝ) / 2) * (n - k + 1 : ℝ) ^ ((m : ℝ) / 2) := by
    simpa [Real.mul_rpow (by positivity) (by positivity)] using hpow
  have hconst_pos : 0 < (m + 2 : ℝ) ^ ((m : ℝ) / 2) := by
    positivity
  have hdiv :
      (n + 1 : ℝ) ^ ((m : ℝ) / 2) / (m + 2 : ℝ) ^ ((m : ℝ) / 2) ≤
        (n - k + 1 : ℝ) ^ ((m : ℝ) / 2) := by
    exact (div_le_iff hconst_pos).2 (by simpa [mul_assoc, mul_left_comm, mul_comm] using hpow')
  have hdiv_pos :
      0 < (n + 1 : ℝ) ^ ((m : ℝ) / 2) / (m + 2 : ℝ) ^ ((m : ℝ) / 2) := by
    positivity
  have hinv :
      1 / ((n - k + 1 : ℝ) ^ ((m : ℝ) / 2)) ≤
        1 / ((n + 1 : ℝ) ^ ((m : ℝ) / 2) / (m + 2 : ℝ) ^ ((m : ℝ) / 2)) := by
    exact one_div_le_one_div_of_le hdiv_pos hdiv
  have hrearr :
      1 / ((n + 1 : ℝ) ^ ((m : ℝ) / 2) / (m + 2 : ℝ) ^ ((m : ℝ) / 2)) =
        (m + 2 : ℝ) ^ ((m : ℝ) / 2) * (1 / (n + 1 : ℝ) ^ ((m : ℝ) / 2)) := by
    field_simp [show (n + 1 : ℝ) ^ ((m : ℝ) / 2) ≠ 0 by positivity,
      show (m + 2 : ℝ) ^ ((m : ℝ) / 2) ≠ 0 by positivity]
    ring
  -- Proof comment: the tail length is still a fixed proportion of the total length, so after
  -- rewriting negative powers as reciprocals only one dimension-dependent factor remains.
  rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity)]
  simpa [hrearr, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hinv

/-- Helper for Theorem 17.39: the atom bound is proved by induction over the number of occupied
boxes, starting from the trivial one-box case. -/
private lemma uniformOccupancyAtom_succ_le_const_rpow :
    ∀ m : ℕ, ∃ C > 0, ∀ n : ℕ, ∀ η : Fin (m + 1) → ℕ,
      η ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (m + 1))) n →
        ((Nat.multinomial Finset.univ η : ℝ) / ((m + 1 : ℝ) ^ n)) ≤
          C * (n + 1 : ℝ) ^ (-(((m + 1 : ℝ) - 1) / 2))
  | 0 => by
      refine ⟨1, by positivity, ?_⟩
      intro n η hη
      have huniv : (Finset.univ : Finset (Fin 1)) = {0} := by
        ext i
        fin_cases i <;> simp
      have hmult : Nat.multinomial (Finset.univ : Finset (Fin 1)) η = 1 := by
        simpa [huniv] using Nat.multinomial_singleton (0 : Fin 1) η
      -- Proof comment: in one box there is only one admissible occupancy profile, so the
      -- normalized atom is identically `1`.
      simpa [hmult]
  | m + 1 => by
      rcases uniformOccupancyAtom_succ_le_const_rpow (m := m) with ⟨Ctail, hCtail_pos, hCtail⟩
      rcases headBinomialAtom_leftOfMean_le_const_rpow (D := m + 1) with
        ⟨Chead, hChead_pos, hChead⟩
      refine ⟨Chead * Ctail * (m + 2 : ℝ) ^ ((m : ℝ) / 2), by positivity, ?_⟩
      intro n η hη
      classical
      rcases occupancyProfile_reindex_head_le_average (D := m + 1) (n := n) (η := η) hη with
        ⟨e, he_head⟩
      let η' : Fin (m + 2) → ℕ := η ∘ e
      let k : ℕ := η' 0
      let ξ : Fin (m + 1) → ℕ := fun i ↦ η' i.succ
      have hηsum : ∑ i : Fin (m + 2), η i = n := by
        simpa [Finset.mem_piAntidiag] using hη
      have hη'sum : ∑ i : Fin (m + 2), η' i = n := by
        calc
          ∑ i : Fin (m + 2), η' i = ∑ i : Fin (m + 2), η i := by
              simpa [η'] using
                (Fintype.sum_equiv e
                  (fun i : Fin (m + 2) ↦ η' i)
                  (fun i : Fin (m + 2) ↦ η i)
                  (fun i ↦ by simp [η']))
          _ = n := hηsum
      have hsplit : k + ∑ i : Fin (m + 1), ξ i = n := by
        simpa [k, ξ, η', Fin.sum_univ_succ] using hη'sum
      have hk : k ≤ n / (m + 2) := by
        simpa [k, η'] using he_head
      have hξsum : ∑ i : Fin (m + 1), ξ i = n - k := by
        omega
      have hξ :
          ξ ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (m + 1))) (n - k) := by
        simpa [Finset.mem_piAntidiag] using hξsum
      have hatom_split :
          ((Nat.multinomial Finset.univ η : ℝ) / ((m + 2 : ℝ) ^ n)) =
            occupancyHeadMass (m + 1) n k *
              ((Nat.multinomial Finset.univ ξ : ℝ) / ((m + 1 : ℝ) ^ (n - k))) := by
        calc
          ((Nat.multinomial Finset.univ η : ℝ) / ((m + 2 : ℝ) ^ n))
            = ((Nat.multinomial Finset.univ η' : ℝ) / ((m + 2 : ℝ) ^ n)) := by
                rw [← multinomialOccupancyAtom_reindex (D := m + 2) (e := e) (η := η)]
          _ = occupancyHeadMass (m + 1) n k *
                ((Nat.multinomial Finset.univ ξ : ℝ) / ((m + 1 : ℝ) ^ (n - k))) := by
                simpa [η', k, ξ] using
                  (multinomialOccupancyAtom_split_head
                    (D := m + 1) (n := n) (k := k) (ξ := ξ) hsplit)
      have hhead :
          occupancyHeadMass (m + 1) n k ≤
            Chead * (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) := by
        exact hChead n k hk
      have htail :
          ((Nat.multinomial Finset.univ ξ : ℝ) / ((m + 1 : ℝ) ^ (n - k))) ≤
            Ctail * (n - k + 1 : ℝ) ^ (-((m : ℝ) / 2)) := by
        simpa using hCtail (n - k) ξ hξ
      have htail_scale :
          (n - k + 1 : ℝ) ^ (-((m : ℝ) / 2)) ≤
            (m + 2 : ℝ) ^ ((m : ℝ) / 2) * (n + 1 : ℝ) ^ (-((m : ℝ) / 2)) := by
        exact shiftedTailRpow_le_averageFactor (m := m) (n := n) (k := k) hk
      have htail_scaled :
          Ctail * (n - k + 1 : ℝ) ^ (-((m : ℝ) / 2)) ≤
            Ctail *
              ((m + 2 : ℝ) ^ ((m : ℝ) / 2) * (n + 1 : ℝ) ^ (-((m : ℝ) / 2))) := by
        exact mul_le_mul_of_nonneg_left htail_scale (by positivity)
      have htail_nonneg :
          0 ≤ ((Nat.multinomial Finset.univ ξ : ℝ) / ((m + 1 : ℝ) ^ (n - k))) := by
        positivity
      have hprod_le :
          occupancyHeadMass (m + 1) n k *
              ((Nat.multinomial Finset.univ ξ : ℝ) / ((m + 1 : ℝ) ^ (n - k))) ≤
            (Chead * (n + 1 : ℝ) ^ (-(1 / 2 : ℝ))) *
              (Ctail *
                ((m + 2 : ℝ) ^ ((m : ℝ) / 2) * (n + 1 : ℝ) ^ (-((m : ℝ) / 2)))) := by
        exact mul_le_mul hhead (htail.trans htail_scaled) htail_nonneg (by positivity)
      -- Proof comment: after reindexing to a minimal head coordinate, the atom factors into a
      -- head binomial mass and a tail atom, and the two decay estimates combine additively in
      -- the exponent.
      calc
        ((Nat.multinomial Finset.univ η : ℝ) / ((m + 2 : ℝ) ^ n))
          = occupancyHeadMass (m + 1) n k *
              ((Nat.multinomial Finset.univ ξ : ℝ) / ((m + 1 : ℝ) ^ (n - k))) := hatom_split
        _ ≤ (Chead * (n + 1 : ℝ) ^ (-(1 / 2 : ℝ))) *
              (Ctail *
                ((m + 2 : ℝ) ^ ((m : ℝ) / 2) * (n + 1 : ℝ) ^ (-((m : ℝ) / 2)))) := hprod_le
        _ = (Chead * Ctail * (m + 2 : ℝ) ^ ((m : ℝ) / 2)) *
              ((n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) * (n + 1 : ℝ) ^ (-((m : ℝ) / 2))) := by
                ring
        _ = (Chead * Ctail * (m + 2 : ℝ) ^ ((m : ℝ) / 2)) *
              (n + 1 : ℝ) ^ (-((((m + 2 : ℝ) - 1) / 2))) := by
                congr 1
                rw [← Real.rpow_add (by positivity)]
                congr 1
                ring

/-- Helper for Theorem 17.39: each normalized occupancy atom should already satisfy the sharp
`(n + 1)^(-((D - 1)/2))` upper bound. -/
private lemma uniformOccupancyAtom_le_const_rpow
    [NeZero D] (hD : 2 ≤ D) :
    ∃ C > 0, ∀ n : ℕ, ∀ η : Fin D → ℕ,
      η ∈ Finset.piAntidiag (Finset.univ : Finset (Fin D)) n →
        ((Nat.multinomial Finset.univ η : ℝ) / (D : ℝ) ^ n) ≤
          C * (n + 1 : ℝ) ^ (-(((D : ℝ) - 1) / 2)) := by
  have hD_pos : 1 ≤ D := by
    omega
  -- Proof comment: the induction theorem already treats every dimension `m + 1`; instantiate it
  -- at `m = D - 1` and simplify the index arithmetic.
  simpa [Nat.sub_add_cancel hD_pos] using
    (uniformOccupancyAtom_succ_le_const_rpow (m := D - 1))

/-- Helper for Theorem 17.39: the occupancy collision on `D` boxes should decay like
`(n + 1)^(-((D - 1)/2))`. -/
private lemma uniformOccupancyCollision_le_const_rpow
    [NeZero D] (hD : 2 ≤ D) :
    ∃ C > 0, ∀ n : ℕ,
      ∑ η ∈ Finset.piAntidiag (Finset.univ : Finset (Fin D)) n,
        (((Nat.multinomial Finset.univ η : ℝ) / (D : ℝ) ^ n) ^ 2) ≤
          C * (n + 1 : ℝ) ^ (-(((D : ℝ) - 1) / 2)) := by
  -- Route correction: the walk-to-occupancy bridge is already proved, so the remaining work is a
  -- pure occupancy estimate. Collapse the collision sum to the stronger atom bound, so the
  -- remaining blocker is only the atom-level induction on the number of boxes.
  rcases uniformOccupancyAtom_le_const_rpow (D := D) hD with ⟨C, hC_pos, hC⟩
  refine ⟨C, hC_pos, ?_⟩
  intro n
  exact occupancyCollision_le_of_atomBound
    (D := D)
    (B := fun m ↦ C * (m + 1 : ℝ) ^ (-(((D : ℝ) - 1) / 2)))
    (hB := by
      intro m η hη
      exact hC m η hη)
    n

/-- Helper for Theorem 17.39: in dimensions at least `3`, the even return masses admit a summable
power-law majorant. -/
private lemma symmetricSimpleRandomWalkEvenOriginMass_toReal_le_const_rpow
    [NeZero D] (hD : 3 ≤ D) :
    ∃ C > 0, ∀ n : ℕ,
      symmetricSimpleRandomWalkEvenOriginMassToReal D n ≤
        C * (n + 1 : ℝ) ^ (-((D : ℝ) / 2)) := by
  have hDtwo : 2 ≤ D := by
    omega
  rcases uniformOccupancyCollision_le_const_rpow (D := D) hDtwo with ⟨Cocc, hCocc_pos, hCocc⟩
  refine ⟨2 * Cocc, by positivity, ?_⟩
  intro n
  have hcb_nonneg :
      0 ≤ ((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n) := by
    positivity
  have hocc_nonneg :
      0 ≤
        ∑ η ∈ Finset.piAntidiag (Finset.univ : Finset (Fin D)) n,
          (((Nat.multinomial Finset.univ η : ℝ) / (D : ℝ) ^ n) ^ 2) := by
    positivity
  have hpow :
      (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) *
          (n + 1 : ℝ) ^ (-(((D : ℝ) - 1) / 2)) =
        (n + 1 : ℝ) ^ (-((D : ℝ) / 2)) := by
    have hpos : 0 ≤ (n + 1 : ℝ) := by
      positivity
    rw [← Real.rpow_add hpos]
    congr 1
    ring
  -- Proof comment: use the exact walk-to-occupancy bridge, combine the central-binomial
  -- `n^(-1/2)` estimate with the occupancy decay, and merge the exponents.
  rw [symmetricSimpleRandomWalkEvenOriginMassToReal_eq_centralBinomial_mulOccupancyCollision
    (D := D) (n := n)]
  calc
    ((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n) *
        ∑ η ∈ Finset.piAntidiag (Finset.univ : Finset (Fin D)) n,
          (((Nat.multinomial Finset.univ η : ℝ) / (D : ℝ) ^ n) ^ 2)
      ≤ (2 * (n + 1 : ℝ) ^ (-(1 / 2 : ℝ))) *
          (Cocc * (n + 1 : ℝ) ^ (-(((D : ℝ) - 1) / 2))) := by
            exact mul_le_mul
              (centralBinomialReturnProbability_le_two_mul_rpow n)
              (hCocc n)
              hocc_nonneg
              hcb_nonneg
    _ = (2 * Cocc) * (n + 1 : ℝ) ^ (-((D : ℝ) / 2)) := by
          rw [hpow]
          ring

-- Helper for Theorem 17.39: the remaining canonical symmetric-walk blocker is the origin Green
-- criterion `G(0,0) = ⊤ ↔ D ≤ 2`.
/-- Helper for Theorem 17.39: the one-dimensional symmetric simple walk already has infinite
origin Green value. -/
private lemma symmetricSimpleRandomWalk_greenFunction_zero_zero_eq_top_dimOne
    (P1 : LatticePoint 1 → ProbabilityMeasure Ω) (X1 : ℕ → Ω → LatticePoint 1)
    [IsMarkovProcessRealization
      (fun n ↦ dirac_convolution_kernel (symmetricSimpleRandomWalkStepPMF 1).toMeasure ^ n) P1 X1] :
    (G[P1, X1]) (0 : LatticePoint 1) 0 = ⊤ := by
  -- Route correction: the global transport-to-Green reduction is already done, so the only
  -- missing work here is the one-dimensional return-mass divergence argument.
  let term : ℕ → ℝ≥0∞ := fun n ↦
    ((dirac_convolution_kernel (symmetricSimpleRandomWalkStepPMF 1).toMeasure ^ n)
      (0 : LatticePoint 1))
      ({0} : Set (LatticePoint 1))
  have hgreen : (G[P1, X1]) (0 : LatticePoint 1) 0 = ∑' n : ℕ, term n := by
    -- Proof comment: package the origin Green value once as the series of origin return masses.
    simpa [term] using
      latticeWalk_greenFunction_zero_zero_eq_tsum_originMass
        (D := 1) (ν := symmetricSimpleRandomWalkStepPMF 1) (P := P1) (X := X1)
  have hodd_tsum : (∑' n : ℕ, term (2 * n + 1)) = 0 := by
    -- Proof comment: parity kills every odd return time in dimension `1`.
    calc
      (∑' n : ℕ, term (2 * n + 1)) = ∑' n : ℕ, (0 : ℝ≥0∞) := by
        refine tsum_congr fun n ↦ ?_
        simpa [term] using symmetricSimpleRandomWalk_originMass_odd_eq_zero (D := 1) n
      _ = 0 := by simp
  have hEven_top : (∑' n : ℕ, term (2 * n)) = ∞ := by
    by_contra hfinite
    have hEvenSummable :
        Summable (fun n : ℕ ↦ (term (2 * n)).toReal) :=
      ENNReal.summable_toReal (f := fun n : ℕ ↦ term (2 * n)) <| by
        simpa using hfinite
    have hEvenShift :
        Summable (fun n : ℕ ↦ (term (2 * (n + 4))).toReal) := by
      -- Proof comment: finiteness of the even series would force summability of each finite tail.
      simpa [Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        ((_root_.summable_nat_add_iff (f := fun n : ℕ ↦ (term (2 * n)).toReal) 4).2
          hEvenSummable)
    have hHarmonicSummable :
        Summable (fun n : ℕ ↦ 1 / (n + 4 : ℝ)) := by
      -- Proof comment: the harmonic tail is pointwise dominated by the even return masses.
      refine Summable.of_nonneg_of_le (fun n ↦ by positivity) ?_ hEvenShift
      intro n
      have hcompare :
          1 / (n + 4 : ℝ) ≤
            (Nat.choose (2 * (n + 4)) (n + 4) : ℝ) / (4 : ℝ) ^ (n + 4) := by
        exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1
          (centralBinomialReturnMass_dimOne_ge_harmonic n)
      calc
        1 / (n + 4 : ℝ)
          ≤ (Nat.choose (2 * (n + 4)) (n + 4) : ℝ) / (4 : ℝ) ^ (n + 4) := hcompare
        _ = (term (2 * (n + 4))).toReal := by
            have hmass :
                (term (2 * (n + 4))).toReal =
                  (ENNReal.ofReal
                    ((Nat.choose (2 * (n + 4)) (n + 4) : ℝ) / (4 : ℝ) ^ (n + 4))).toReal := by
              simpa [term] using
                congrArg ENNReal.toReal
                  (symmetricSimpleRandomWalkOriginMass_even_dimOne (n := n + 4))
            rw [ENNReal.toReal_ofReal (by positivity)] at hmass
            exact hmass.symm
    have hHarmonicNot :
        ¬ Summable (fun n : ℕ ↦ 1 / (n + 4 : ℝ)) := by
      intro hs
      exact hs.tsum_ofReal_ne_top shiftedHarmonicOfReal_tsum_eq_top_dimOne
    exact hHarmonicNot hHarmonicSummable
  calc
    (G[P1, X1]) (0 : LatticePoint 1) 0 = ∑' n : ℕ, term n := hgreen
    _ = (∑' n : ℕ, term (2 * n)) + ∑' n : ℕ, term (2 * n + 1) := by
          rw [← tsum_even_add_odd ENNReal.summable ENNReal.summable]
    _ = (∑' n : ℕ, term (2 * n)) + 0 := by rw [hodd_tsum]
    _ = ∞ := by rw [hEven_top, top_add]

/-- Helper for Theorem 17.39: the two-dimensional symmetric simple walk already has infinite
origin Green value. -/
private lemma symmetricSimpleRandomWalk_greenFunction_zero_zero_eq_top_dimTwo
    (P2 : LatticePoint 2 → ProbabilityMeasure Ω) (X2 : ℕ → Ω → LatticePoint 2)
    [IsMarkovProcessRealization
      (fun n ↦ dirac_convolution_kernel (symmetricSimpleRandomWalkStepPMF 2).toMeasure ^ n) P2 X2] :
    (G[P2, X2]) (0 : LatticePoint 2) 0 = ⊤ := by
  -- Route correction: after the Green-function normalization, the remaining `D = 2` branch is
  -- purely analytic once the exact even-time return formula has been isolated.
  let term : ℕ → ℝ≥0∞ := fun n ↦
    ((dirac_convolution_kernel (symmetricSimpleRandomWalkStepPMF 2).toMeasure ^ n)
      (0 : LatticePoint 2))
      ({0} : Set (LatticePoint 2))
  have hgreen : (G[P2, X2]) (0 : LatticePoint 2) 0 = ∑' n : ℕ, term n := by
    -- Proof comment: package the planar origin Green value as the origin return-mass series.
    simpa [term] using
      latticeWalk_greenFunction_zero_zero_eq_tsum_originMass
        (D := 2) (ν := symmetricSimpleRandomWalkStepPMF 2) (P := P2) (X := X2)
  have hodd_tsum : (∑' n : ℕ, term (2 * n + 1)) = 0 := by
    -- Proof comment: parity still kills every odd return time in dimension `2`.
    calc
      (∑' n : ℕ, term (2 * n + 1)) = ∑' n : ℕ, (0 : ℝ≥0∞) := by
        refine tsum_congr fun n ↦ ?_
        simpa [term] using symmetricSimpleRandomWalk_originMass_odd_eq_zero (D := 2) n
      _ = 0 := by simp
  have hEven_top : (∑' n : ℕ, term (2 * n)) = ∞ := by
    by_contra hfinite
    have hEvenSummable :
        Summable (fun n : ℕ ↦ (term (2 * n)).toReal) :=
      ENNReal.summable_toReal (f := fun n : ℕ ↦ term (2 * n)) <| by
        simpa using hfinite
    have hHarmonicSummable :
        Summable (fun n : ℕ ↦ 1 / (Real.pi * (n + 1 : ℝ))) := by
      -- Proof comment: the exact planar even return formula together with the Wallis lower bound
      -- dominates a shifted harmonic series.
      refine Summable.of_nonneg_of_le (fun n ↦ by positivity) ?_ hEvenSummable
      intro n
      have hcompare :
          1 / (Real.pi * (n + 1 : ℝ)) ≤
            (((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n) ^ 2) :=
        centralBinomialReturnProbability_sq_ge_piInv_div_succ n
      calc
        1 / (Real.pi * (n + 1 : ℝ))
          ≤ (((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n) ^ 2) := hcompare
        _ = (term (2 * n)).toReal := by
            simpa [symmetricSimpleRandomWalkEvenOriginMassToReal, term] using
              (symmetricSimpleRandomWalkOriginMass_even_dimTwo_toReal n).symm
    have hHarmonicNot :
        ¬ Summable (fun n : ℕ ↦ 1 / (Real.pi * (n + 1 : ℝ))) := by
      intro hs
      have hsScaled :
          Summable (fun n : ℕ ↦ Real.pi * (1 / (Real.pi * (n + 1 : ℝ)))) :=
        hs.mul_left Real.pi
      have hsOne :
          Summable (fun n : ℕ ↦ 1 / (n + 1 : ℝ)) := by
        refine hsScaled.congr ?_
        intro n
        field_simp [Real.pi_ne_zero]
      have hnot : ¬ Summable (fun n : ℕ ↦ 1 / (n + 1 : ℝ)) := by
        simpa using
          mt ((_root_.summable_nat_add_iff (f := fun n : ℕ ↦ 1 / (n : ℝ)) 1).1)
            Real.not_summable_one_div_natCast
      exact hnot hsOne
    exact hHarmonicNot hHarmonicSummable
  calc
    (G[P2, X2]) (0 : LatticePoint 2) 0 = ∑' n : ℕ, term n := hgreen
    _ = (∑' n : ℕ, term (2 * n)) + ∑' n : ℕ, term (2 * n + 1) := by
          rw [← tsum_even_add_odd ENNReal.summable ENNReal.summable]
    _ = (∑' n : ℕ, term (2 * n)) + 0 := by rw [hodd_tsum]
    _ = ∞ := by rw [hEven_top, top_add]

/-- Helper for Theorem 17.39: in dimensions at least `3`, the symmetric simple walk has finite
origin Green value. -/
private lemma symmetricSimpleRandomWalk_greenFunction_zero_zero_ne_top_of_three_le_dimension
    [NeZero D]
    [IsMarkovProcessRealization
      (fun n ↦ dirac_convolution_kernel (symmetricSimpleRandomWalkStepPMF D).toMeasure ^ n) P X]
    (hD : 3 ≤ D) :
    (G[P, X]) (0 : LatticePoint D) 0 ≠ ⊤ := by
  -- Route correction: the kernel-identification work is complete, so only the transient
  -- high-dimensional return-series estimate remains after isolating the exact even-time bound.
  let term : ℕ → ℝ≥0∞ := fun n ↦
    ((dirac_convolution_kernel (symmetricSimpleRandomWalkStepPMF D).toMeasure ^ n)
      (0 : LatticePoint D))
      ({0} : Set (LatticePoint D))
  have hgreen : (G[P, X]) (0 : LatticePoint D) 0 = ∑' n : ℕ, term n := by
    -- Proof comment: package the origin Green value as the origin return-mass series once.
    simpa [term] using
      latticeWalk_greenFunction_zero_zero_eq_tsum_originMass
        (D := D) (ν := symmetricSimpleRandomWalkStepPMF D) (P := P) (X := X)
  have hodd_tsum : (∑' n : ℕ, term (2 * n + 1)) = 0 := by
    -- Proof comment: odd return times vanish in every positive dimension by the parity invariant.
    calc
      (∑' n : ℕ, term (2 * n + 1)) = ∑' n : ℕ, (0 : ℝ≥0∞) := by
        refine tsum_congr fun n ↦ ?_
        simpa [term] using symmetricSimpleRandomWalk_originMass_odd_eq_zero (D := D) n
      _ = 0 := by simp
  rcases symmetricSimpleRandomWalkEvenOriginMass_toReal_le_const_rpow (D := D) hD with
    ⟨C, hCpos, hCbound⟩
  have hExp : 1 < (D : ℝ) / 2 := by
    have hDreal : (3 : ℝ) ≤ D := by
      exact_mod_cast hD
    linarith
  have hBoundSummable :
      Summable (fun n : ℕ ↦ C * (n + 1 : ℝ) ^ (-((D : ℝ) / 2))) := by
    let s : ℝ := (D : ℝ) / 2
    have hbaseAbs :
        Summable (fun n : ℕ ↦ 1 / |n + (1 : ℝ)| ^ s) :=
      (Real.summable_one_div_nat_add_rpow 1 s).2 (by simpa [s] using hExp)
    have hbase :
        Summable (fun n : ℕ ↦ 1 / (n + 1 : ℝ) ^ ((D : ℝ) / 2)) :=
      hbaseAbs.congr fun n ↦ by
        rw [abs_of_nonneg]
        positivity
    have hscaled := hbase.mul_left C
    refine hscaled.congr ?_
    intro n
    have hnonneg : 0 ≤ (n + 1 : ℝ) := by positivity
    rw [div_eq_mul_inv, Real.rpow_neg hnonneg]
    ring
  have hEvenSummable :
      Summable (fun n : ℕ ↦ (term (2 * n)).toReal) := by
    -- Proof comment: the remaining high-dimensional helper gives a convergent `p`-series majorant
    -- for the even return masses.
    refine Summable.of_nonneg_of_le (fun n ↦ by positivity) ?_ hBoundSummable
    intro n
    simpa [symmetricSimpleRandomWalkEvenOriginMassToReal, term] using hCbound n
  have hEven_ne_top : (∑' n : ℕ, term (2 * n)) ≠ ∞ := by
    have hEven_eq :
        (∑' n : ℕ, term (2 * n)) =
          ∑' n : ℕ, ENNReal.ofReal ((term (2 * n)).toReal) := by
      refine tsum_congr fun n ↦ ?_
      exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    rw [hEven_eq]
    exact hEvenSummable.tsum_ofReal_ne_top
  rw [hgreen, ← tsum_even_add_odd ENNReal.summable ENNReal.summable, hodd_tsum, add_zero]
  exact hEven_ne_top

/-- Helper for Theorem 17.39: once the analytic branch lemmas are available, the `D ≤ 2`
direction is just a dimension split. -/
private lemma symmetricSimpleRandomWalk_greenFunction_zero_zero_eq_top_of_dimension_le_two
    [NeZero D]
    [IsMarkovProcessRealization
      (fun n ↦ dirac_convolution_kernel (symmetricSimpleRandomWalkStepPMF D).toMeasure ^ n) P X]
    (hD : D ≤ 2) :
    (G[P, X]) (0 : LatticePoint D) 0 = ⊤ := by
  -- Proof comment: `NeZero D` and `D ≤ 2` leave only the dimensions `1` and `2`.
  have hpos : 1 ≤ D := Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne D))
  have hcases : D = 1 ∨ D = 2 := by
    omega
  rcases hcases with rfl | rfl
  · -- Proof comment: the one-dimensional branch is isolated in its own local helper.
    exact symmetricSimpleRandomWalk_greenFunction_zero_zero_eq_top_dimOne (P1 := P) (X1 := X)
  · -- Proof comment: the two-dimensional branch is isolated in its own local helper.
    exact symmetricSimpleRandomWalk_greenFunction_zero_zero_eq_top_dimTwo (P2 := P) (X2 := X)

lemma symmetricSimpleRandomWalk_originGreen_eq_top_iff_dimension_le_two
    [NeZero D]
    [IsMarkovProcessRealization
      (fun n ↦ dirac_convolution_kernel (symmetricSimpleRandomWalkStepPMF D).toMeasure ^ n) P X] :
    (G[P, X]) (0 : LatticePoint D) 0 = ⊤ ↔ D ≤ 2 := by
  constructor
  · intro hgreen
    -- Proof comment: if the origin Green value were infinite in a high dimension, it would
    -- contradict the dedicated transient branch.
    by_contra hD
    have hthree : 3 ≤ D := by
      omega
    exact symmetricSimpleRandomWalk_greenFunction_zero_zero_ne_top_of_three_le_dimension
      (D := D) (P := P) (X := X) hthree hgreen
  · intro hD
    -- Proof comment: the low-dimensional branch is now reduced to the explicit `D = 1` and
    -- `D = 2` analytic closures.
    exact symmetricSimpleRandomWalk_greenFunction_zero_zero_eq_top_of_dimension_le_two
      (D := D) (P := P) (X := X) hD

/-- The canonical symmetric simple random walk on `ℤ^D` is recurrent exactly in dimensions at
most `2`. -/
theorem symmetricSimpleRandomWalk_isRecurrent_iff_dimension_le_two
    [NeZero D]
    [IsMarkovProcessRealization
      (fun n ↦ dirac_convolution_kernel (symmetricSimpleRandomWalkStepPMF D).toMeasure ^ n) P X] :
    IsRecurrentMarkovChain P X ↔ D ≤ 2 := by
  -- Proof comment: reduce the chain-level statement to the origin diagonal Green criterion for
  -- the canonical symmetric walk, which is the only remaining analytic frontier.
  rw [latticeWalk_isRecurrent_iff_originGreen_eq_top
    (ν := symmetricSimpleRandomWalkStepPMF D) (P := P) (X := X)]
  exact symmetricSimpleRandomWalk_originGreen_eq_top_iff_dimension_le_two
    (D := D) (P := P) (X := X)

/-- Theorem 17.39 (1): the symmetric nearest-neighbor simple random walk on `ℤ^D` is recurrent if
and only if the dimension satisfies `D ≤ 2`. -/
theorem symmetricSimpleRandomWalk_lattice_recurrent_iff_dimension_le_two
    [NeZero D] (p : LatticePoint D → LatticePoint D → ENNReal)
    [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel p ^ n) P X]
    (hp : IsTranslationInvariantStepMatrix p)
    (hstep : ∀ y, p 0 y = symmetricSimpleRandomWalkStepPMF D y) :
    IsRecurrentMarkovChain P X ↔ D ≤ 2 :=
  by
    have hkernel_eq :
        discreteMatrixKernel p =
          dirac_convolution_kernel (symmetricSimpleRandomWalkStepPMF D).toMeasure := by
      ext x s hs
      have hrow :
          discreteMatrixKernel p x =
            dirac_convolution_kernel (symmetricSimpleRandomWalkStepPMF D).toMeasure x := by
        refine Measure.ext_of_singleton ?_
        intro y
        rw [discreteMatrixKernel_apply, Measure.sum_apply _ (measurableSet_singleton y)]
        rw [tsum_eq_single y]
        · -- Proof comment: translation invariance reduces every row to the origin row, and the
          -- origin row is exactly the symmetric nearest-neighbor step law.
          rw [hp x y, hstep (y - x), dirac_convolution_kernel_apply, Measure.dirac_conv]
          rw [Measure.map_apply (by fun_prop) (measurableSet_singleton y)]
          have hpreimage :
              (fun z : LatticePoint D ↦ x + z) ⁻¹' ({y} : Set (LatticePoint D)) = {y - x} := by
            ext z
            simp only [Set.mem_preimage, Set.mem_singleton_iff]
            constructor
            · intro hz
              exact eq_sub_iff_add_eq.mpr (by simpa [add_comm] using hz)
            · intro hz
              exact by simpa [add_comm] using (eq_sub_iff_add_eq.mp hz)
          rw [hpreimage]
          simp [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton (y - x))]
        · intro z hz
          simp [hz]
      exact congrArg (fun μ ↦ μ s) hrow
    let hCanonical :
        IsMarkovProcessRealization
          (fun n ↦ dirac_convolution_kernel (symmetricSimpleRandomWalkStepPMF D).toMeasure ^ n)
          P X := by
      -- Proof comment: once the one-step kernels agree, the ambient realization can be read as a
      -- realization of the canonical symmetric convolution semigroup.
      simpa [hkernel_eq] using
        (inferInstance :
          IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel p ^ n) P X)
    letI :
        IsMarkovProcessRealization
          (fun n ↦ dirac_convolution_kernel (symmetricSimpleRandomWalkStepPMF D).toMeasure ^ n)
          P X := hCanonical
    -- Proof comment: after identifying the matrix walk with the canonical convolution walk, the
    -- claimed equivalence is exactly the owner theorem for the symmetric step law.
    simpa using
      (symmetricSimpleRandomWalk_isRecurrent_iff_dimension_le_two
        (D := D) (P := P) (X := X))

-/

/-- Helper for Theorem 17.39: the real-valued even return mass of the canonical symmetric walk. -/
private def symmetricSimpleRandomWalkEvenOriginMassToReal (D n : ℕ) [NeZero D] : ℝ :=
  ((((dirac_convolution_kernel (symmetricSimpleRandomWalkStepPMF D).toMeasure ^ (2 * n))
    (0 : LatticePoint D))
    ({0} : Set (LatticePoint D))).toReal)

/-- Helper for Theorem 17.39: the even return probabilities of the canonical symmetric walk have
the local-limit asymptotic from Exercise 17.5.1. -/
private lemma symmetricSimpleRandomWalkEvenOriginMassToReal_tendsto
    [NeZero D] :
    Tendsto
      (fun n : ℕ ↦
        (n : ℝ) ^ ((D : ℝ) / 2) * symmetricSimpleRandomWalkEvenOriginMassToReal D n)
      atTop
      (nhds ((2 : ℝ) * (4 * Real.pi / D) ^ (-(D : ℝ) / 2))) := by
  simpa [symmetricSimpleRandomWalkEvenOriginMassToReal, Measure.real_def] using
    (tendsto_scaled_simpleSymmetricRandomWalk_returnProbability (D := D))

/-- Helper for Theorem 17.39: in dimensions `1` and `2`, the origin Green function of the
canonical symmetric walk diverges. -/
private lemma symmetricSimpleRandomWalk_greenFunction_zero_zero_eq_top_of_dimension_le_two
    [NeZero D]
    [IsMarkovProcessRealization
      (fun n ↦ dirac_convolution_kernel (symmetricSimpleRandomWalkStepPMF D).toMeasure ^ n) P X]
    (hD : D ≤ 2) :
    (G[P, X]) (0 : LatticePoint D) 0 = ⊤ := by
  let term : ℕ → ℝ≥0∞ := fun n ↦
    ((dirac_convolution_kernel (symmetricSimpleRandomWalkStepPMF D).toMeasure ^ n)
      (0 : LatticePoint D))
      ({0} : Set (LatticePoint D))
  have hgreen : (G[P, X]) (0 : LatticePoint D) 0 = ∑' n : ℕ, term n := by
    simpa [term] using
      latticeWalk_greenFunction_zero_zero_eq_tsum_originMass
        (D := D) (ν := symmetricSimpleRandomWalkStepPMF D) (P := P) (X := X)
  have hodd_tsum : (∑' n : ℕ, term (2 * n + 1)) = 0 := by
    calc
      (∑' n : ℕ, term (2 * n + 1)) = ∑' n : ℕ, (0 : ℝ≥0∞) := by
        refine tsum_congr fun n ↦ ?_
        simpa [term] using symmetricSimpleRandomWalk_originMass_odd_eq_zero (D := D) n
      _ = 0 := by simp
  have hEven_top : (∑' n : ℕ, term (2 * n)) = ∞ := by
    by_contra hfinite
    have hEvenSummableToReal :
        Summable (fun n : ℕ ↦ (term (2 * n)).toReal) :=
      ENNReal.summable_toReal (f := fun n : ℕ ↦ term (2 * n)) <| by
        simpa using hfinite
    have hEvenSummable :
        Summable (fun n : ℕ ↦ symmetricSimpleRandomWalkEvenOriginMassToReal D n) := by
      simpa [term, symmetricSimpleRandomWalkEvenOriginMassToReal] using hEvenSummableToReal
    let s : ℝ := (D : ℝ) / 2
    let c : ℝ := (2 : ℝ) * (4 * Real.pi / D) ^ (-(D : ℝ) / 2)
    have hc_pos : 0 < c := by
      have hD_pos : 0 < (D : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne D)
      dsimp [c]
      refine mul_pos zero_lt_two ?_
      refine Real.rpow_pos_of_pos ?_ _
      positivity
    have htendsto :
        Tendsto
          (fun n : ℕ ↦ (n : ℝ) ^ s * symmetricSimpleRandomWalkEvenOriginMassToReal D n)
          atTop (nhds c) := by
      simpa [c, s] using symmetricSimpleRandomWalkEvenOriginMassToReal_tendsto (D := D)
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 htendsto (c / 2) (by positivity)
    have hshiftSummable :
        Summable (fun n : ℕ ↦ symmetricSimpleRandomWalkEvenOriginMassToReal D (n + (N + 1))) :=
      ((_root_.summable_nat_add_iff
        (f := fun n : ℕ ↦ symmetricSimpleRandomWalkEvenOriginMassToReal D n) (N + 1)).2
          hEvenSummable)
    have hscaledSummable :
        Summable (fun n : ℕ ↦ (c / 2) * (1 / (((n + (N + 1) : ℕ) : ℝ) ^ s))) := by
      refine Summable.of_nonneg_of_le (fun n ↦ by positivity) ?_ hshiftSummable
      intro n
      let m : ℕ := n + (N + 1)
      have hm_ge : N ≤ m := by
        dsimp [m]
        omega
      have hclose :
          |(m : ℝ) ^ s * symmetricSimpleRandomWalkEvenOriginMassToReal D m - c| < c / 2 := by
        simpa [Real.dist_eq, m] using hN m hm_ge
      have hlow : c / 2 ≤ (m : ℝ) ^ s * symmetricSimpleRandomWalkEvenOriginMassToReal D m := by
        nlinarith [abs_lt.mp hclose]
      have hm_pos : 0 < (m : ℝ) ^ s := by
        have hm_real_pos : 0 < (m : ℝ) := by
          dsimp [m]
          positivity
        exact Real.rpow_pos_of_pos hm_real_pos s
      have hdiv :
          (c / 2) / ((m : ℝ) ^ s) ≤ symmetricSimpleRandomWalkEvenOriginMassToReal D m := by
        rw [div_le_iff₀ hm_pos]
        simpa [mul_comm, mul_left_comm, mul_assoc] using hlow
      simpa [m, div_eq_mul_inv] using hdiv
    have htailSummable :
        Summable (fun n : ℕ ↦ 1 / (((n + (N + 1) : ℕ) : ℝ) ^ s)) := by
      have hc_ne : c ≠ 0 := by
        positivity
      have hmul := hscaledSummable.mul_left (2 / c)
      refine hmul.congr ?_
      intro n
      field_simp [hc_ne]
    have hbaseSummable :
        Summable (fun n : ℕ ↦ 1 / |(n : ℝ) + (N + 1 : ℝ)| ^ s) := by
      refine htailSummable.congr ?_
      intro n
      have hnonneg : 0 ≤ (n : ℝ) + (N + 1 : ℝ) := by
        positivity
      rw [abs_of_nonneg hnonneg]
      simp [Nat.cast_add, add_assoc, add_comm, add_left_comm]
    have hs : 1 < s := (Real.summable_one_div_nat_add_rpow (N + 1 : ℝ) s).1 hbaseSummable
    have hs_not : ¬ 1 < s := by
      dsimp [s]
      have hDreal : (D : ℝ) ≤ 2 := by
        exact_mod_cast hD
      linarith
    exact hs_not hs
  calc
    (G[P, X]) (0 : LatticePoint D) 0 = ∑' n : ℕ, term n := hgreen
    _ = (∑' n : ℕ, term (2 * n)) + ∑' n : ℕ, term (2 * n + 1) := by
          rw [← tsum_even_add_odd ENNReal.summable ENNReal.summable]
    _ = (∑' n : ℕ, term (2 * n)) + 0 := by
          rw [hodd_tsum]
    _ = ∞ := by
          rw [hEven_top, top_add]

/-- Helper for Theorem 17.39: in dimensions at least `3`, the origin Green function of the
canonical symmetric walk is finite. -/
private lemma symmetricSimpleRandomWalk_greenFunction_zero_zero_ne_top_of_three_le_dimension
    [NeZero D]
    [IsMarkovProcessRealization
      (fun n ↦ dirac_convolution_kernel (symmetricSimpleRandomWalkStepPMF D).toMeasure ^ n) P X]
    (hD : 3 ≤ D) :
    (G[P, X]) (0 : LatticePoint D) 0 ≠ ⊤ := by
  let term : ℕ → ℝ≥0∞ := fun n ↦
    ((dirac_convolution_kernel (symmetricSimpleRandomWalkStepPMF D).toMeasure ^ n)
      (0 : LatticePoint D))
      ({0} : Set (LatticePoint D))
  have hgreen : (G[P, X]) (0 : LatticePoint D) 0 = ∑' n : ℕ, term n := by
    simpa [term] using
      latticeWalk_greenFunction_zero_zero_eq_tsum_originMass
        (D := D) (ν := symmetricSimpleRandomWalkStepPMF D) (P := P) (X := X)
  have hodd_tsum : (∑' n : ℕ, term (2 * n + 1)) = 0 := by
    calc
      (∑' n : ℕ, term (2 * n + 1)) = ∑' n : ℕ, (0 : ℝ≥0∞) := by
        refine tsum_congr fun n ↦ ?_
        simpa [term] using symmetricSimpleRandomWalk_originMass_odd_eq_zero (D := D) n
      _ = 0 := by simp
  let s : ℝ := (D : ℝ) / 2
  let c : ℝ := (2 : ℝ) * (4 * Real.pi / D) ^ (-(D : ℝ) / 2)
  have hc_pos : 0 < c := by
    have hD_pos : 0 < (D : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne D)
    dsimp [c]
    refine mul_pos zero_lt_two ?_
    refine Real.rpow_pos_of_pos ?_ _
    positivity
  have htendsto :
      Tendsto
        (fun n : ℕ ↦ (n : ℝ) ^ s * symmetricSimpleRandomWalkEvenOriginMassToReal D n)
        atTop (nhds c) := by
    simpa [c, s] using symmetricSimpleRandomWalkEvenOriginMassToReal_tendsto (D := D)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 htendsto c hc_pos
  have hs : 1 < s := by
    dsimp [s]
    have hDreal : (3 : ℝ) ≤ D := by
      exact_mod_cast hD
    linarith
  have hbaseSummable :
      Summable (fun n : ℕ ↦ 1 / |(n : ℝ) + (N + 1 : ℝ)| ^ s) :=
    (Real.summable_one_div_nat_add_rpow (N + 1 : ℝ) s).2 hs
  have hscaledSummable :
      Summable (fun n : ℕ ↦ (2 * c) * (1 / |(n : ℝ) + (N + 1 : ℝ)| ^ s)) :=
    hbaseSummable.mul_left (2 * c)
  have hshiftSummable :
      Summable (fun n : ℕ ↦ symmetricSimpleRandomWalkEvenOriginMassToReal D (n + (N + 1))) := by
    refine Summable.of_nonneg_of_le
      (fun n ↦ by
        rw [symmetricSimpleRandomWalkEvenOriginMassToReal]
        exact ENNReal.toReal_nonneg)
      ?_ hscaledSummable
    intro n
    let m : ℕ := n + (N + 1)
    have hm_ge : N ≤ m := by
      dsimp [m]
      omega
    have hclose :
        |(m : ℝ) ^ s * symmetricSimpleRandomWalkEvenOriginMassToReal D m - c| < c := by
      simpa [Real.dist_eq, m] using hN m hm_ge
    have hupp :
        (m : ℝ) ^ s * symmetricSimpleRandomWalkEvenOriginMassToReal D m ≤ 2 * c := by
      nlinarith [abs_lt.mp hclose]
    have hm_pos : 0 < (m : ℝ) ^ s := by
      have hm_real_pos : 0 < (m : ℝ) := by
        dsimp [m]
        positivity
      exact Real.rpow_pos_of_pos hm_real_pos s
    have hdiv :
        symmetricSimpleRandomWalkEvenOriginMassToReal D m ≤ (2 * c) / ((m : ℝ) ^ s) := by
      rw [le_div_iff₀ hm_pos]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hupp
    have hnonneg : 0 ≤ (n : ℝ) + (N + 1 : ℝ) := by
      positivity
    simpa [m, abs_of_nonneg hnonneg, div_eq_mul_inv] using hdiv
  have hEvenSummable :
      Summable (fun n : ℕ ↦ symmetricSimpleRandomWalkEvenOriginMassToReal D n) :=
    ((_root_.summable_nat_add_iff
      (f := fun n : ℕ ↦ symmetricSimpleRandomWalkEvenOriginMassToReal D n) (N + 1)).1
        hshiftSummable)
  have hEven_eq :
      (∑' n : ℕ, term (2 * n)) =
        ∑' n : ℕ, ENNReal.ofReal (symmetricSimpleRandomWalkEvenOriginMassToReal D n) := by
    refine tsum_congr fun n ↦ ?_
    let κ : Kernel (LatticePoint D) (LatticePoint D) :=
      dirac_convolution_kernel (symmetricSimpleRandomWalkStepPMF D).toMeasure
    letI : IsMarkovKernel (κ ^ (2 * n)) :=
      by simpa [κ] using symmetricSimpleRandomWalkKernelPow_isMarkov (D := D) (2 * n)
    rw [symmetricSimpleRandomWalkEvenOriginMassToReal]
    exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  have hEven_ne_top : (∑' n : ℕ, term (2 * n)) ≠ ∞ := by
    rw [hEven_eq]
    exact hEvenSummable.tsum_ofReal_ne_top
  rw [hgreen, ← tsum_even_add_odd ENNReal.summable ENNReal.summable, hodd_tsum, add_zero]
  exact hEven_ne_top

lemma symmetricSimpleRandomWalk_originGreen_eq_top_iff_dimension_le_two
    [NeZero D]
    [IsMarkovProcessRealization
      (fun n ↦ dirac_convolution_kernel (symmetricSimpleRandomWalkStepPMF D).toMeasure ^ n) P X] :
    (G[P, X]) (0 : LatticePoint D) 0 = ⊤ ↔ D ≤ 2 := by
  constructor
  · intro hgreen
    by_contra hD
    have hthree : 3 ≤ D := by
      omega
    exact symmetricSimpleRandomWalk_greenFunction_zero_zero_ne_top_of_three_le_dimension
      (D := D) (P := P) (X := X) hthree hgreen
  · intro hD
    exact symmetricSimpleRandomWalk_greenFunction_zero_zero_eq_top_of_dimension_le_two
      (D := D) (P := P) (X := X) hD

/-- The canonical symmetric simple random walk on `ℤ^D` is recurrent exactly in dimensions at
most `2`. -/
theorem symmetricSimpleRandomWalk_isRecurrent_iff_dimension_le_two
    [NeZero D]
    [IsMarkovProcessRealization
      (fun n ↦ dirac_convolution_kernel (symmetricSimpleRandomWalkStepPMF D).toMeasure ^ n) P X] :
    IsRecurrentMarkovChain P X ↔ D ≤ 2 := by
  rw [latticeWalk_isRecurrent_iff_originGreen_eq_top
    (ν := symmetricSimpleRandomWalkStepPMF D) (P := P) (X := X)]
  exact symmetricSimpleRandomWalk_originGreen_eq_top_iff_dimension_le_two
    (D := D) (P := P) (X := X)

/-- Theorem 17.39 (1): the symmetric nearest-neighbor simple random walk on `ℤ^D` is recurrent if
and only if the dimension satisfies `D ≤ 2`. -/
theorem symmetricSimpleRandomWalk_lattice_recurrent_iff_dimension_le_two
    [NeZero D] (p : LatticePoint D → LatticePoint D → ENNReal)
    [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel p ^ n) P X]
    (hp : IsTranslationInvariantStepMatrix p)
    (hstep : ∀ y, p 0 y = symmetricSimpleRandomWalkStepPMF D y) :
    IsRecurrentMarkovChain P X ↔ D ≤ 2 := by
  have hkernel_eq :
      discreteMatrixKernel p =
        dirac_convolution_kernel (symmetricSimpleRandomWalkStepPMF D).toMeasure := by
    ext x s hs
    have hrow :
        discreteMatrixKernel p x =
          dirac_convolution_kernel (symmetricSimpleRandomWalkStepPMF D).toMeasure x := by
      refine Measure.ext_of_singleton ?_
      intro y
      rw [discreteMatrixKernel_apply, Measure.sum_apply _ (measurableSet_singleton y)]
      rw [tsum_eq_single y]
      · rw [hp x y, hstep (y - x), dirac_convolution_kernel_apply, Measure.dirac_conv]
        rw [Measure.map_apply (by fun_prop) (measurableSet_singleton y)]
        have hpreimage :
            (fun z : LatticePoint D ↦ x + z) ⁻¹' ({y} : Set (LatticePoint D)) = {y - x} := by
          ext z
          simp only [Set.mem_preimage, Set.mem_singleton_iff]
          constructor
          · intro hz
            exact eq_sub_iff_add_eq.mpr (by simpa [add_comm] using hz)
          · intro hz
            exact by simpa [add_comm] using (eq_sub_iff_add_eq.mp hz)
        rw [hpreimage]
        simp [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton (y - x))]
      · intro z hz
        simp [hz]
    exact congrArg (fun μ ↦ μ s) hrow
  let hCanonical :
      IsMarkovProcessRealization
        (fun n ↦ dirac_convolution_kernel (symmetricSimpleRandomWalkStepPMF D).toMeasure ^ n)
        P X := by
    simpa [hkernel_eq] using
      (inferInstance :
        IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel p ^ n) P X)
  letI :
      IsMarkovProcessRealization
        (fun n ↦ dirac_convolution_kernel (symmetricSimpleRandomWalkStepPMF D).toMeasure ^ n)
        P X := hCanonical
  simpa using
    (symmetricSimpleRandomWalk_isRecurrent_iff_dimension_le_two
      (D := D) (P := P) (X := X))

end LatticeWalk

section OneDimensionalWalk

variable (P : ℤ → ProbabilityMeasure Ω) (X : ℕ → Ω → ℤ)

/-- Helper for Theorem 17.39: the singleton-mass step matrix extracted from the convolution kernel
`dirac_convolution_kernel (ν : Measure ℤ)`. -/
def convolutionStepMatrix (ν : ProbabilityMeasure ℤ) : ℤ → ℤ → ℝ≥0∞ :=
  fun x y ↦ dirac_convolution_kernel (ν : Measure ℤ) x {y}

/-- Helper for Theorem 17.39: the discrete matrix kernel of `convolutionStepMatrix ν` is exactly
the convolution kernel generated by `ν`. -/
lemma convolutionStepMatrixKernel_eq (ν : ProbabilityMeasure ℤ) :
    discreteMatrixKernel (convolutionStepMatrix ν) =
      dirac_convolution_kernel (ν : Measure ℤ) :=
  by
    ext x s hs
    have hrow :
        discreteMatrixKernel (convolutionStepMatrix ν) x =
          dirac_convolution_kernel (ν : Measure ℤ) x := by
      refine Measure.ext_of_singleton ?_
      intro y
      -- Proof comment: on the discrete state space `ℤ`, equality of row measures is determined
      -- by singleton masses.
      rw [discreteMatrixKernel_apply, Measure.sum_apply _ (measurableSet_singleton y)]
      rw [tsum_eq_single y]
      · simp [convolutionStepMatrix]
      · intro z hz
        simp [convolutionStepMatrix, Measure.smul_apply, Measure.dirac_apply', hz]
    -- Proof comment: evaluate the row equality on the target measurable set.
    exact congrArg (fun μ ↦ μ s) hrow

/-- Helper for Theorem 17.39: the singleton-mass step matrix associated with `ν` is stochastic. -/
lemma convolutionStepMatrix_isStochastic (ν : ProbabilityMeasure ℤ) :
    IsStochasticMatrix (convolutionStepMatrix ν) :=
  by
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

/-- Helper for Theorem 17.39: the singleton-mass step matrix associated with `ν` is translation
invariant. -/
lemma convolutionStepMatrix_isTranslationInvariant (ν : ProbabilityMeasure ℤ) :
    IsTranslationInvariantStepMatrix (convolutionStepMatrix ν) :=
  by
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

/-- Helper for Theorem 17.39: the origin row of `convolutionStepMatrix ν` is the step law `ν`
itself. -/
lemma convolutionStepMatrix_originRow_eq (ν : ProbabilityMeasure ℤ) :
    discreteMatrixKernel (convolutionStepMatrix ν) 0 = (ν : Measure ℤ) :=
  by
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

/-- Helper for Theorem 17.39: rewriting the one-step kernel from convolution form to
`discreteMatrixKernel` also rewrites the ambient realization. -/
lemma convolutionStepMatrix_markovRealization
    (ν : ProbabilityMeasure ℤ) (P : ℤ → ProbabilityMeasure Ω) (X : ℕ → Ω → ℤ)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ dirac_convolution_kernel (ν : Measure ℤ) ^ n) P X] :
    IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (convolutionStepMatrix ν) ^ n) P X :=
  by
    -- Proof comment: the realization hypothesis depends only on the one-step kernel, and the
    -- previous kernel-extensionality lemma identifies the two semigroups.
    simpa [convolutionStepMatrixKernel_eq ν] using
      (inferInstance :
        IsMarkovProcessRealization
          (fun n : ℕ ↦ dirac_convolution_kernel (ν : Measure ℤ) ^ n) P X)

section DiagonalGreen

variable {κ : ℕ → Kernel ℤ ℤ}
variable [IsMarkovProcessRealization κ P X]

/-- Helper for Theorem 17.39: Theorem 17.29 specialized to `(x, x)` turns the iterated-entrance
probability series into the shifted power series of `F(x, x)`. -/
private lemma iteratedEntranceProbabilitySeries_eq_selfPowerSeries
    {κ : ℕ → Kernel ℤ ℤ} [IsMarkovProcessRealization κ P X] (x : ℤ) :
    (∑' k : ℕ+, ENNReal.ofReal ((P x : Measure Ω).real {ω | (τ_[X, x]^k) ω < ⊤})) =
      ∑' n : ℕ, ENNReal.ofReal (((F[P, X]) x x) ^ (n + 1)) :=
  by
    -- Proof comment: replace each iterated-entrance probability by the Theorem 17.29 formula,
    -- then reindex the `ℕ+`-series along `Equiv.pnatEquivNat`.
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

/-- Helper for Theorem 17.39: the positive-time diagonal Green function is the shifted geometric
series of successive return probabilities. -/
lemma greenFunctionFromOneSelf_eq_tsum_selfPowers [IsMarkovProcessRealization κ P X] (x : ℤ) :
    (G[P, X; 1]) x x =
      ∑' n : ℕ, ENNReal.ofReal (((F[P, X]) x x) ^ (n + 1)) :=
  by
    -- Proof comment: reuse the earlier positive-visit normalization to rewrite the positive-time
    -- Green function as the iterated-entrance series, then reindex that series along `ℕ+ ≃ ℕ`.
    exact
      (greenFunctionFromOneSelf_eq_tsum_iteratedEntranceProbabilities
        (P := P) (X := X) (κ := κ) x).trans
        (iteratedEntranceProbabilitySeries_eq_selfPowerSeries
          (κ := κ) (P := P) (X := X) x)

/-- Helper for Theorem 17.39: the full diagonal Green function splits into the deterministic
time-`0` visit and the strictly positive-time diagonal Green tail. -/
  lemma greenFunctionSelf_eq_one_add_greenFunctionFromOneSelf
    [IsMarkovProcessRealization κ P X] (x : ℤ) :
    (G[P, X]) x x = 1 + (G[P, X; 1]) x x :=
  by
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

/-- Helper for Theorem 17.39: a shifted geometric series of `ℝ≥0∞`-casts is finite whenever the
ratio lies in `[0, 1)`. -/
lemma ennrealOfRealTsumGeometricSucc_lt_top {q : ℝ}
    (hq_nonneg : 0 ≤ q) (hq_lt_one : q < 1) :
    ∑' n : ℕ, ENNReal.ofReal (q ^ (n + 1)) < ⊤ :=
  by
    have hsum : Summable (fun n : ℕ ↦ q ^ (n + 1)) :=
      (_root_.summable_nat_add_iff 1).2 (summable_geometric_of_lt_one hq_nonneg hq_lt_one)
    -- Proof comment: summability in `ℝ` keeps the pointwise `ℝ≥0∞` casts finite because all
    -- terms are nonnegative.
    calc
      ∑' n : ℕ, ENNReal.ofReal (q ^ (n + 1))
        = ENNReal.ofReal (∑' n : ℕ, q ^ (n + 1)) := by
            rw [ENNReal.ofReal_tsum_of_nonneg]
            · intro n
              exact pow_nonneg hq_nonneg _
            · exact hsum
      _ < ⊤ := by
            simp

/-- Helper for Theorem 17.39: an infinite diagonal Green value forces recurrence. -/
lemma isRecurrentState_of_greenFunctionSelf_eq_top
    [IsMarkovProcessRealization κ P X] (x : ℤ) (hx : (G[P, X]) x x = ⊤) :
    IsRecurrentState P X x :=
  by
    have hq_nonneg : 0 ≤ (F[P, X]) x x := measureReal_nonneg
    have hq_le_one : (F[P, X]) x x ≤ 1 := by
      rw [everHitsProbability_def]
      exact measureReal_le_one
    -- Route correction: instead of reopening the Green-function definition, normalize the
    -- positive-time diagonal tail to the shifted power series in `F(x, x)` and close by a
    -- geometric contradiction.
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
          rw [greenFunctionSelf_eq_one_add_greenFunctionFromOneSelf (P := P) (X := X) (κ := κ)]
        _ = 1 + ∑' n : ℕ, ENNReal.ofReal (((F[P, X]) x x) ^ (n + 1)) := by
          rw [greenFunctionFromOneSelf_eq_tsum_selfPowers (P := P) (X := X) (κ := κ)]
        _ < ⊤ := by
          exact ENNReal.add_lt_top.2 ⟨by simp, htail_lt_top⟩
    exact (ne_of_lt hgreen_lt_top) hx

/-- Helper for Theorem 17.39: recurrence forces the diagonal Green value to be infinite. -/
lemma greenFunctionSelf_eq_top_of_isRecurrentState
    [IsMarkovProcessRealization κ P X] (x : ℤ) (hx : IsRecurrentState P X x) :
    (G[P, X]) x x = ⊤ :=
  by
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
              simpa [hx]
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

end DiagonalGreen

/-- Helper for Theorem 17.39: the one-step increment law of the one-dimensional biased nearest-
neighbor walk, jumping to `1` with probability `p` and to `-1` with probability `1 - p`. -/
def biasedSimpleRandomWalkStepPMF (p : I) : PMF ℤ :=
  (PMF.bernoulli (unitInterval.toNNReal p) (by simpa using p.2.2)).map
    fun b ↦ if b then (1 : ℤ) else -1

-- TODO: reprove the singleton transition formula against the current convolution-kernel API.
/-- Helper for Theorem 17.39: evaluating the biased nearest-neighbor kernel on a singleton target
recovers the usual two-point transition formula. -/
theorem biasedSimpleRandomWalkKernel_apply_singleton (p : I) (x y : ℤ) :
    dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure x {y} =
      if y = x + 1 then ENNReal.ofReal (p : ℝ)
      else if y = x - 1 then ENNReal.ofReal (1 - (p : ℝ))
      else 0 :=
  by
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
    rw [hpreimage, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton (y - x))]
    by_cases hy1 : y = x + 1
    · have hy_sub : y - x = 1 := by
        omega
      have hp_nonneg : 0 ≤ (p : ℝ) := p.2.1
      rw [hy_sub]
      -- Proof comment: on the right-jump branch the singleton mass is the Bernoulli success
      -- probability.
      simp [biasedSimpleRandomWalkStepPMF, PMF.map_apply, PMF.bernoulli_apply, hy1]
      simpa [unitInterval.toNNReal] using (ENNReal.ofReal_eq_coe_nnreal hp_nonneg).symm
    · by_cases hy_left : y = x - 1
      · have hy_sub : y - x = -1 := by
          omega
        have hp_nonneg : 0 ≤ (p : ℝ) := p.2.1
        have hbranch : x - 1 ≠ x + 1 := by
          omega
        have hcoe : ENNReal.ofNNReal (unitInterval.toNNReal p) = ENNReal.ofReal (p : ℝ) := by
          simpa [unitInterval.toNNReal] using (ENNReal.ofReal_eq_coe_nnreal hp_nonneg).symm
        rw [hy_sub]
        -- Proof comment: on the left-jump branch the complementary Bernoulli mass is `1 - p`.
        simp [biasedSimpleRandomWalkStepPMF, PMF.map_apply, PMF.bernoulli_apply, hy_left]
        rw [if_neg hbranch]
        calc
          1 - ENNReal.ofNNReal (unitInterval.toNNReal p)
              = 1 - ENNReal.ofReal (p : ℝ) := by
                  rw [hcoe]
          _ = ENNReal.ofReal (1 - (p : ℝ)) := by
                symm
                simpa using (ENNReal.ofReal_sub 1 hp_nonneg)
      · have hy_sub_one : y - x ≠ 1 := by
          omega
        have hy_sub_negOne : y - x ≠ -1 := by
          omega
        have hpmf_zero : biasedSimpleRandomWalkStepPMF p (y - x) = 0 := by
          rw [biasedSimpleRandomWalkStepPMF, PMF.map_apply]
          apply ENNReal.tsum_eq_zero.2
          intro b
          cases b <;> simp [hy_sub_one, hy_sub_negOne]
        -- Proof comment: away from the two support points, the step law assigns zero mass.
        simp [hy1, hy_left, hpmf_zero]

/-- Helper for Theorem 17.39: composing a positive `n`-step singleton mass with a positive
one-step singleton mass keeps the concatenated singleton mass positive. -/
private theorem discreteMatrixKernelSingletonPosSucc
    {p : ℤ → ℤ → ℝ≥0∞} {x y z : ℤ} {n : ℕ}
    (hxy : 0 < ((discreteMatrixKernel p ^ n) x) ({y} : Set ℤ))
    (hyz : 0 < (discreteMatrixKernel p) y ({z} : Set ℤ)) :
    0 < ((discreteMatrixKernel p ^ (n + 1)) x) ({z} : Set ℤ) := by
  let κ := discreteMatrixKernel p
  have hmeas : Measurable fun w : ℤ ↦ κ w ({z} : Set ℤ) :=
    Kernel.measurable_coe κ (measurableSet_singleton z)
  have hySupport : y ∈ Function.support fun w : ℤ ↦ κ w ({z} : Set ℤ) := by
    change (κ y) ({z} : Set ℤ) ≠ 0
    exact ne_of_gt hyz
  have hsupportPos :
      0 < ((κ ^ n) x) (Function.support fun w : ℤ ↦ κ w ({z} : Set ℤ)) :=
    measure_pos_of_superset (Set.singleton_subset_iff.mpr hySupport) hxy.ne'
  -- Proof comment: the composition integral is positive because the support already contains the
  -- chosen intermediate state `y`.
  rw [Kernel.pow_succ_apply_eq_lintegral κ n x (measurableSet_singleton z)]
  rw [MeasureTheory.lintegral_pos_iff_support hmeas]
  exact hsupportPos

/-- Helper for Theorem 17.39: following `n` successive right jumps from `x` has positive `n`-step
mass for the biased nearest-neighbor kernel whenever `p > 0`. -/
private theorem biasedSimpleRandomWalkRightPathMass_pos
    (p : I) (hp0 : 0 < (p : ℝ)) (x : ℤ) :
    ∀ n : ℕ,
      0 <
        ((discreteMatrixKernel
            (fun a b ↦ dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure a {b}) ^ n)
          x) ({x + n} : Set ℤ) := by
  intro n
  induction n generalizing x with
  | zero =>
      -- Proof comment: the zero-step kernel is the identity, so it charges the starting state.
      rw [pow_zero]
      simpa using
        (show 0 < (Kernel.id x) ({x} : Set ℤ) by
          rw [Kernel.id_apply]
          simp)
  | succ n ih =>
      have hrest :
          0 <
            ((discreteMatrixKernel
                (fun a b ↦ dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure a {b}) ^ n)
              x) ({x + n} : Set ℤ) := ih x
      have hlast :
          0 <
            (discreteMatrixKernel fun a b ↦
              dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure a {b}) (x + n)
              ({x + (n + 1)} : Set ℤ) := by
        have htarget : x + ((n : ℤ) + 1) = (x + n) + 1 := by
          omega
        have hleft : (x + n : ℤ) + 1 ≠ (x + n : ℤ) - 1 := by
          omega
        -- Proof comment: the last step is a concrete right jump from `x + n` to `x + n + 1`.
        rw [htarget, discreteMatrixKernel_apply_singleton, biasedSimpleRandomWalkKernel_apply_singleton]
        simpa [hleft] using ENNReal.ofReal_pos.2 hp0
      exact discreteMatrixKernelSingletonPosSucc hrest hlast

/-- Helper for Theorem 17.39: following `n` successive left jumps from `x` has positive `n`-step
mass for the biased nearest-neighbor kernel whenever `p < 1`. -/
private theorem biasedSimpleRandomWalkLeftPathMass_pos
    (p : I) (hp1 : (p : ℝ) < 1) (x : ℤ) :
    ∀ n : ℕ,
      0 <
        ((discreteMatrixKernel
            (fun a b ↦ dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure a {b}) ^ n)
          x) ({x - n} : Set ℤ) := by
  intro n
  induction n generalizing x with
  | zero =>
      -- Proof comment: the zero-step kernel again charges the starting point with mass `1`.
      rw [pow_zero]
      simpa using
        (show 0 < (Kernel.id x) ({x} : Set ℤ) by
          rw [Kernel.id_apply]
          simp)
  | succ n ih =>
      have hrest :
          0 <
            ((discreteMatrixKernel
                (fun a b ↦ dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure a {b}) ^ n)
              x) ({x - n} : Set ℤ) := ih x
      have hlast :
          0 <
            (discreteMatrixKernel fun a b ↦
              dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure a {b}) (x - n)
              ({x - (n + 1)} : Set ℤ) := by
        have htarget : x - ((n : ℤ) + 1) = (x - n) - 1 := by
          omega
        have hright : (x - n : ℤ) - 1 ≠ (x - n : ℤ) + 1 := by
          omega
        -- Proof comment: the last step is a concrete left jump from `x - n` to `x - n - 1`.
        rw [htarget, discreteMatrixKernel_apply_singleton, biasedSimpleRandomWalkKernel_apply_singleton]
        simpa [hright] using ENNReal.ofReal_pos.2 (sub_pos.mpr hp1)
      exact discreteMatrixKernelSingletonPosSucc hrest hlast

/-- Helper for Theorem 17.39: the biased nearest-neighbor kernel on `ℤ` is irreducible whenever
both jump directions have positive one-step mass. -/
private theorem biasedSimpleRandomWalkStepMatrix_isIrreducible
    (p : I) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    Kernel.IsIrreducible (Measure.count : Measure ℤ)
      (discreteMatrixKernel fun x y ↦
        dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure x {y}) := by
  refine ⟨?_⟩
  intro A hA hcount x
  have hA_nonempty : A.Nonempty := by
    by_contra hA_empty
    simp [Set.not_nonempty_iff_eq_empty.mp hA_empty] at hcount
  rcases hA_nonempty with ⟨y, hyA⟩
  by_cases hxy : x ≤ y
  · let n : ℕ := Int.toNat (y - x)
    have hy : y = x + n := by
      dsimp [n]
      omega
    refine ⟨n, ?_⟩
    have hsingleton :
        0 <
          ((discreteMatrixKernel (fun a b ↦
              dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure a {b}) ^ n) x)
            ({y} : Set ℤ) := by
      simpa [hy] using biasedSimpleRandomWalkRightPathMass_pos p hp0 x n
    exact lt_of_lt_of_le hsingleton (measure_mono (Set.singleton_subset_iff.mpr hyA))
  · let n : ℕ := Int.toNat (x - y)
    have hy : y = x - n := by
      dsimp [n]
      omega
    refine ⟨n, ?_⟩
    have hsingleton :
        0 <
          ((discreteMatrixKernel (fun a b ↦
              dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure a {b}) ^ n) x)
            ({y} : Set ℤ) := by
      simpa [hy] using biasedSimpleRandomWalkLeftPathMass_pos p hp1 x n
    exact lt_of_lt_of_le hsingleton (measure_mono (Set.singleton_subset_iff.mpr hyA))

/-- Helper for Theorem 17.39: under a genuine bias parameter `0 < p < 1`, every state reaches
every distinct target state with positive probability for the biased nearest-neighbor walk on
`ℤ`. -/
private theorem biasedSimpleRandomWalk_everHits_pos_of_ne
    (p : I) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (P : ℤ → ProbabilityMeasure Ω) (X : ℕ → Ω → ℤ)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure ^ n) P X]
    (x y : ℤ) (hxy_ne : x ≠ y) :
    0 < (F[P, X]) x y := by
  let hReal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure ^ n)
        P X := inferInstance
  let hproc : IsStochasticProcess X := fun n ↦ hReal.measurable_process n
  by_cases hxy : x ≤ y
  · let n : ℕ := Int.toNat (y - x)
    have hy : y = x + n := by
      dsimp [n]
      omega
    have hsingleton :
        0 <
          ((discreteMatrixKernel (fun a b ↦
              dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure a {b}) ^ n) x)
            ({y} : Set ℤ) := by
      -- Proof comment: if `x ≤ y`, a monotone right-jump path reaches `y` in `n = y - x` steps.
      simpa [hy] using biasedSimpleRandomWalkRightPathMass_pos p hp0 x n
    have hn : 0 < n := by
      dsimp [n]
      omega
    have hkernel :
        discreteMatrixKernel (fun a b ↦
            dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure a {b}) =
          dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure := by
      let ν : ProbabilityMeasure ℤ :=
        ⟨(biasedSimpleRandomWalkStepPMF p).toMeasure, by infer_instance⟩
      change discreteMatrixKernel (convolutionStepMatrix ν) =
        dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure
      simpa [convolutionStepMatrix, ν] using (convolutionStepMatrixKernel_eq ν)
    have hkernelPow :
        discreteMatrixKernel (fun a b ↦
            dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure a {b}) ^ n =
          dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure ^ n := by
      exact congrArg (fun κ : Kernel ℤ ℤ ↦ κ ^ n) hkernel
    have hstep :
        0 <
          ((dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure ^ n) x)
            ({y} : Set ℤ) := by
      rw [← hkernelPow]
      exact hsingleton
    have hgreen : 0 < (G[P, X; 1]) x y := by
      exact
        greenFunctionFrom_one_pos_of_posStepMass
          (κ := fun m : ℕ ↦ dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure ^ m)
          P X hn hstep
    exact (greenFunctionFrom_one_pos_iff_everHitsProbability_pos P X hproc x y).1 hgreen
  · let n : ℕ := Int.toNat (x - y)
    have hy : y = x - n := by
      dsimp [n]
      omega
    have hsingleton :
        0 <
          ((discreteMatrixKernel (fun a b ↦
              dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure a {b}) ^ n) x)
            ({y} : Set ℤ) := by
      -- Proof comment: if `y < x`, a monotone left-jump path reaches `y` in `n = x - y` steps.
      simpa [hy] using biasedSimpleRandomWalkLeftPathMass_pos p hp1 x n
    have hn : 0 < n := by
      dsimp [n]
      omega
    have hkernel :
        discreteMatrixKernel (fun a b ↦
            dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure a {b}) =
          dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure := by
      let ν : ProbabilityMeasure ℤ :=
        ⟨(biasedSimpleRandomWalkStepPMF p).toMeasure, by infer_instance⟩
      change discreteMatrixKernel (convolutionStepMatrix ν) =
        dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure
      simpa [convolutionStepMatrix, ν] using (convolutionStepMatrixKernel_eq ν)
    have hkernelPow :
        discreteMatrixKernel (fun a b ↦
            dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure a {b}) ^ n =
          dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure ^ n := by
      exact congrArg (fun κ : Kernel ℤ ℤ ↦ κ ^ n) hkernel
    have hstep :
        0 <
          ((dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure ^ n) x)
            ({y} : Set ℤ) := by
      rw [← hkernelPow]
      exact hsingleton
    have hgreen : 0 < (G[P, X; 1]) x y := by
      exact
        greenFunctionFrom_one_pos_of_posStepMass
          (κ := fun m : ℕ ↦ dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure ^ m)
          P X hn hstep
    exact (greenFunctionFrom_one_pos_iff_everHitsProbability_pos P X hproc x y).1 hgreen

/-- Helper for Theorem 17.39: the quadratic discriminant in formula `(17.19)` is exactly the
square of `2p - 1`, so its principal square root is `|2p - 1|`. -/
lemma biasedSimpleRandomWalkSqrtDiscriminant_eq_abs (p : I) :
    Real.sqrt (1 - 4 * (p : ℝ) * (1 - (p : ℝ))) = |2 * (p : ℝ) - 1| := by
  have hdiscriminant :
      1 - 4 * (p : ℝ) * (1 - (p : ℝ)) = (2 * (p : ℝ) - 1) ^ 2 := by
    ring
  -- Proof comment: normalize the radicand to a square, then use the standard square-root
  -- simplification.
  rw [hdiscriminant, Real.sqrt_sq_eq_abs]

/-- Helper for Theorem 17.39: away from the symmetric point `p = 1 / 2`, the generalized-
binomial series is evaluated strictly inside the unit disk. -/
lemma biasedSimpleRandomWalkFourMul_lt_one_of_ne_half (p : I) (hp : (p : ℝ) ≠ 1 / 2) :
    4 * (p : ℝ) * (1 - (p : ℝ)) < 1 := by
  have hne : 2 * (p : ℝ) - 1 ≠ 0 := by
    intro hzero
    apply hp
    linarith
  have hsq_pos : 0 < (2 * (p : ℝ) - 1) ^ 2 := by
    exact sq_pos_of_ne_zero hne
  have hdiscriminant :
      1 - 4 * (p : ℝ) * (1 - (p : ℝ)) = (2 * (p : ℝ) - 1) ^ 2 := by
    ring
  -- Proof comment: the same discriminant identity turns the non-half hypothesis into the strict
  -- radius bound needed for the central-binomial power series.
  linarith [hsq_pos, hdiscriminant]

/-- Helper for Theorem 17.39: the diagonal Green value at the origin is the series of the origin
singleton masses of the biased walk's `n`-step kernel. -/
lemma biasedSimpleRandomWalk_greenFunction_zero_zero_eq_tsum_originMass
    (P : ℤ → ProbabilityMeasure Ω) (X : ℕ → Ω → ℤ) (p : I)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure ^ n) P X] :
    (G[P, X]) 0 0 =
      ∑' n : ℕ,
        ((dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure ^ n) (0 : ℤ))
          ({0} : Set ℤ) := by
  let hReal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure ^ n)
        P X := inferInstance
  let hX : IsStochasticProcess X := fun n ↦ hReal.measurable_process n
  -- Proof comment: expand the Green function into visit probabilities and rewrite each time-`n`
  -- term through the realization identity for the biased convolution kernel.
  rw [greenFunction_eq_tsum_stateProbabilities P X hX 0 0]
  refine tsum_congr fun n ↦ ?_
  have htransition :=
    congrArg
      (fun μ : Measure ℤ ↦ μ ({0} : Set ℤ))
      (hReal.transition_eq (0 : ℤ) n)
  simpa [Measure.map_apply (hReal.measurable_process n) (measurableSet_singleton (0 : ℤ))] using
    htransition

/-- Helper for Theorem 17.39: after `n` biased nearest-neighbor steps, choosing exactly `k` right
jumps produces the displacement `2k - n`. -/
def biasedSimpleRandomWalkDisplacement (n : ℕ) : ℕ → ℤ :=
  fun k ↦ (2 : ℤ) * k - n

/-- Helper for Theorem 17.39: convolving two pushforwards of laws on `ℕ` is the same as pushing
forward the product law by the sum of the transported coordinates. -/
private lemma map_conv_eq_map_prod_sum
    (μ ν : Measure ℕ) (f g : ℕ → ℤ) (hf : Measurable f) (hg : Measurable g) :
    Measure.map f μ ∗ Measure.map g ν =
      Measure.map (fun s : ℕ × ℕ ↦ f s.1 + g s.2) (μ.prod ν) := by
  -- Proof comment: unfold convolution and collapse the two coordinate pushforwards into one map
  -- on the product space.
  rw [Measure.conv]
  rw [Measure.map_prod_map μ ν hf hg]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  have hsumMap :
      ((fun x : ℤ × ℤ ↦ x.1 + x.2) ∘ Prod.map f g) =
        (fun s : ℕ × ℕ ↦ f s.1 + g s.2) := by
    funext s
    cases s
    rfl
  rw [hsumMap]

/-- Helper for Theorem 17.39: appending one more Bernoulli step adds the corresponding
displacements. -/
private lemma biasedSimpleRandomWalkDisplacement_add (n : ℕ) :
    (fun s : ℕ × ℕ ↦
      biasedSimpleRandomWalkDisplacement n s.1 +
        biasedSimpleRandomWalkDisplacement 1 s.2) =
      fun s : ℕ × ℕ ↦ biasedSimpleRandomWalkDisplacement (n + 1) (s.1 + s.2) := by
  -- Proof comment: both sides expand to the same affine expression in `(s.1, s.2)`.
  ext s
  simp [biasedSimpleRandomWalkDisplacement]
  ring

/-- Helper for Theorem 17.39: one more origin-started biased-walk step convolves the current
origin law with the one-step increment law. -/
private lemma biasedSimpleRandomWalkOriginLawIterateSucc (p : I) (n : ℕ) :
    (((dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure) ^ (n + 1)) (0 : ℤ)) =
      (((dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure) ^ n) (0 : ℤ)) ∗
        (biasedSimpleRandomWalkStepPMF p).toMeasure := by
  let κ : Kernel ℤ ℤ := dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure
  have hpow : κ ^ (n + 1) = κ ∘ₖ (κ ^ n) := by
    simpa [pow_one, Nat.one_add] using (ProbabilityTheory.Kernel.pow_add κ 1 n)
  have hcomp :
      κ ∘ₘ ((κ ^ n) (0 : ℤ)) =
        ((κ ^ n) (0 : ℤ)) ∗ (biasedSimpleRandomWalkStepPMF p).toMeasure := by
    have hconst :=
      congrArg
        (fun K : Kernel ℤ ℤ ↦ K (0 : ℤ))
        (dirac_convolution_kernel_comp_const_eq_const_conv
          (μ := ((κ ^ n) (0 : ℤ)))
          (ν := (biasedSimpleRandomWalkStepPMF p).toMeasure))
    simpa [Kernel.comp_apply, κ] using hconst
  -- Proof comment: rewrite the successor kernel power as one kernel composition and then
  -- evaluate that composition at the origin.
  calc
    (κ ^ (n + 1)) (0 : ℤ) = κ ∘ₘ ((κ ^ n) (0 : ℤ)) := by
      rw [hpow, Kernel.comp_apply]
    _ = ((κ ^ n) (0 : ℤ)) ∗ (biasedSimpleRandomWalkStepPMF p).toMeasure := hcomp

/-- Helper for Theorem 17.39: the singleton masses of `Bin(n, p)` are the usual binomial
weights, now packaged directly in `ℝ≥0∞`. -/
private lemma binomial_apply_singleton (n k : ℕ) (p : I) :
    Bin(n, p) ({k} : Set ℕ) =
      ENNReal.ofReal ((Nat.choose n k : ℝ) * (p : ℝ) ^ k * (1 - (p : ℝ)) ^ (n - k)) := by
  -- Proof comment: the Chapter 5 real-valued singleton formula becomes an `ENNReal` identity by
  -- reconstructing the finite mass from its `toReal`.
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  simpa using congrArg ENNReal.ofReal (binomial_apply_singleton_toReal n k p)

/-- Helper for Theorem 17.39: the one-step biased nearest-neighbor law is the pushforward of the
one-trial binomial law under `k ↦ 2 * k - 1`. -/
private lemma biasedSimpleRandomWalkStepLaw_eq_binomialPushforward (p : I) :
    Measure.map (biasedSimpleRandomWalkDisplacement 1) (Bin(1, p)) =
      (biasedSimpleRandomWalkStepPMF p).toMeasure := by
  refine Measure.ext_of_singleton fun y ↦ ?_
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton y)]
  by_cases hy1 : y = 1
  · subst hy1
    have hpreimage :
        biasedSimpleRandomWalkDisplacement 1 ⁻¹' ({(1 : ℤ)} : Set ℤ) = ({1} : Set ℕ) := by
      ext k
      simp [biasedSimpleRandomWalkDisplacement]
      omega
    rw [hpreimage, binomial_apply_singleton]
    have hp_nonneg : 0 ≤ (p : ℝ) := p.2.1
    -- Proof comment: the image mass at `1` is the success atom of `Bin(1, p)`.
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton (1 : ℤ))]
    simp [biasedSimpleRandomWalkStepPMF]
    simpa [unitInterval.toNNReal] using ENNReal.ofReal_eq_coe_nnreal hp_nonneg
  · by_cases hyNeg : y = -1
    · subst hyNeg
      have hpreimage :
          biasedSimpleRandomWalkDisplacement 1 ⁻¹' ({(-1 : ℤ)} : Set ℤ) = ({0} : Set ℕ) := by
        ext k
        simp [biasedSimpleRandomWalkDisplacement]
      rw [hpreimage, binomial_apply_singleton]
      have hp_nonneg : 0 ≤ (p : ℝ) := p.2.1
      -- Proof comment: the image mass at `-1` is the complementary Bernoulli atom.
      rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton (-1 : ℤ))]
      simp [biasedSimpleRandomWalkStepPMF, hy1]
      calc
        1 - ENNReal.ofNNReal (unitInterval.toNNReal p) = 1 - ENNReal.ofReal (p : ℝ) := by
          simpa [unitInterval.toNNReal] using (congrArg (fun z : ℝ≥0∞ ↦ 1 - z)
            (ENNReal.ofReal_eq_coe_nnreal hp_nonneg).symm)
        _ = ENNReal.ofReal (1 - (p : ℝ)) := by
          symm
          simpa using (ENNReal.ofReal_sub 1 hp_nonneg)
    · have hsupport :
          ∀ᵐ k : ℕ ∂Bin(1, p), k ≤ 1 := by
        simpa using
          (ProbabilityTheory.ae_le_of_hasLaw_binomial (n := 1) (p := p)
            (X := id) (P := Bin(1, p)) (ProbabilityTheory.HasLaw.id (μ := Bin(1, p))))
      have hleft :
          Bin(1, p) (biasedSimpleRandomWalkDisplacement 1 ⁻¹' ({y} : Set ℤ)) = 0 := by
        rw [measure_eq_zero_iff_ae_notMem]
        filter_upwards [hsupport] with k hk
        simp [Set.mem_preimage, Set.mem_singleton_iff]
        intro hky
        have hk_gt : 1 < k := by
          have hEq : (2 : ℤ) * k - 1 = y := by
            simpa [biasedSimpleRandomWalkDisplacement] using hky
          omega
        exact (not_lt_of_ge hk) hk_gt
      have hright :
          (biasedSimpleRandomWalkStepPMF p).toMeasure ({y} : Set ℤ) = 0 := by
        rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton y)]
        simp [biasedSimpleRandomWalkStepPMF, hy1, hyNeg]
      -- Proof comment: every `Bin(1, p)` sample lies in `{0, 1}`, but the displacement equation
      -- `2 * k - 1 = y` forces `k > 1` away from `±1`, so the preimage has zero mass.
      rw [hleft, hright]

/-- Helper for Theorem 17.39: the origin-started `n`-step law of the biased walk is the
pushforward of `Bin(n, p)` under the displacement `k ↦ 2 * k - n`. -/
private lemma biasedSimpleRandomWalkOriginLaw_eq_binomialPushforward (p : I) :
    ∀ n : ℕ,
      ((dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure ^ n) (0 : ℤ)) =
        Measure.map (biasedSimpleRandomWalkDisplacement n) (Bin(n, p))
  | 0 => by
      have hzero :
          ((dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure ^ 0) (0 : ℤ)) =
            Measure.dirac (0 : ℤ) := by
        simpa [pow_zero] using (Kernel.id_apply (0 : ℤ))
      -- Proof comment: both sides are the same Dirac mass at the origin once the zero-trial
      -- binomial law is rewritten canonically.
      rw [hzero, binomial_zero_left, Measure.map_dirac]
      simp [biasedSimpleRandomWalkDisplacement]
  | n + 1 => by
      have hmap :
          Measure.map
              (fun s : ℕ × ℕ ↦ biasedSimpleRandomWalkDisplacement (n + 1) (s.1 + s.2))
              (Bin(n, p).prod Bin(1, p)) =
            Measure.map (biasedSimpleRandomWalkDisplacement (n + 1))
              (Measure.map (fun s : ℕ × ℕ ↦ s.1 + s.2) (Bin(n, p).prod Bin(1, p))) := by
        -- Proof comment: factor the displacement through the addition map on the two binomial
        -- counters before using the binomial convolution theorem.
        symm
        rw [Measure.map_map (by fun_prop) (by fun_prop)]
        rfl
      calc
        ((dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure ^ (n + 1))
            (0 : ℤ))
            =
            ((dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure ^ n)
              (0 : ℤ)) ∗
              (biasedSimpleRandomWalkStepPMF p).toMeasure := by
                simpa using biasedSimpleRandomWalkOriginLawIterateSucc p n
        _ = Measure.map (biasedSimpleRandomWalkDisplacement n) (Bin(n, p)) ∗
              (biasedSimpleRandomWalkStepPMF p).toMeasure := by
                rw [biasedSimpleRandomWalkOriginLaw_eq_binomialPushforward p n]
        _ = Measure.map (biasedSimpleRandomWalkDisplacement n) (Bin(n, p)) ∗
              Measure.map (biasedSimpleRandomWalkDisplacement 1) (Bin(1, p)) := by
                rw [biasedSimpleRandomWalkStepLaw_eq_binomialPushforward p]
        _ = Measure.map
              (fun s : ℕ × ℕ ↦
                biasedSimpleRandomWalkDisplacement n s.1 +
                  biasedSimpleRandomWalkDisplacement 1 s.2)
              (Bin(n, p).prod Bin(1, p)) := by
                exact map_conv_eq_map_prod_sum
                  (μ := Bin(n, p))
                  (ν := Bin(1, p))
                  (f := biasedSimpleRandomWalkDisplacement n)
                  (g := biasedSimpleRandomWalkDisplacement 1)
                  (measurable_of_countable _)
                  (measurable_of_countable _)
        _ = Measure.map
              (fun s : ℕ × ℕ ↦ biasedSimpleRandomWalkDisplacement (n + 1) (s.1 + s.2))
              (Bin(n, p).prod Bin(1, p)) := by
                rw [biasedSimpleRandomWalkDisplacement_add n]
        _ = Measure.map (biasedSimpleRandomWalkDisplacement (n + 1))
              (Measure.map (fun s : ℕ × ℕ ↦ s.1 + s.2) (Bin(n, p).prod Bin(1, p))) := hmap
        _ = Measure.map (biasedSimpleRandomWalkDisplacement (n + 1)) (Bin(n, p) ∗ Bin(1, p)) := by
              rw [Measure.conv]
        _ = Measure.map (biasedSimpleRandomWalkDisplacement (n + 1)) (Bin(n + 1, p)) := by
              simpa [Nat.add_comm] using congrArg
                (Measure.map (biasedSimpleRandomWalkDisplacement (n + 1)))
                (example_3_4_binomial_conv n 1 p)

/-- Helper for Theorem 17.39: odd return times of the biased nearest-neighbor walk have zero
origin mass. -/
private lemma biasedSimpleRandomWalkOriginMass_odd (p : I) (n : ℕ) :
    ((dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure ^ (2 * n + 1))
      (0 : ℤ))
      ({0} : Set ℤ) = 0 := by
  rw [biasedSimpleRandomWalkOriginLaw_eq_binomialPushforward p (2 * n + 1)]
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton (0 : ℤ))]
  have hpreimage :
      biasedSimpleRandomWalkDisplacement (2 * n + 1) ⁻¹' ({(0 : ℤ)} : Set ℤ) = (∅ : Set ℕ) := by
    ext k
    simp [biasedSimpleRandomWalkDisplacement]
    omega
  rw [hpreimage, measure_empty]

/-- Helper for Theorem 17.39: even return times of the biased nearest-neighbor walk give the
central-binomial mass `(2n choose n) (p(1-p))^n`. -/
private lemma biasedSimpleRandomWalkOriginMass_even (p : I) (n : ℕ) :
    ((dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure ^ (2 * n))
      (0 : ℤ))
      ({0} : Set ℤ) =
      ENNReal.ofReal ((Nat.choose (2 * n) n : ℝ) * ((p : ℝ) * (1 - (p : ℝ))) ^ n) := by
  rw [biasedSimpleRandomWalkOriginLaw_eq_binomialPushforward p (2 * n)]
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton (0 : ℤ))]
  have hpreimage :
      biasedSimpleRandomWalkDisplacement (2 * n) ⁻¹' ({(0 : ℤ)} : Set ℤ) = ({n} : Set ℕ) := by
    ext k
    simp [biasedSimpleRandomWalkDisplacement]
    omega
  rw [hpreimage, binomial_apply_singleton]
  have hsub : 2 * n - n = n := by
    omega
  congr 1
  rw [hsub, mul_assoc, ← mul_pow]

/-- Helper for Theorem 17.39: once `p = 1 / 2`, the even return masses dominate a shifted
harmonic series. -/
private lemma centralBinomialReturnMass_at_half_ge_harmonic (n : ℕ) :
    ENNReal.ofReal (1 / (n + 4 : ℝ)) ≤
      ENNReal.ofReal ((Nat.choose (2 * (n + 4)) (n + 4) : ℝ) / (4 : ℝ) ^ (n + 4)) := by
  have hnat :
      4 ^ (n + 4) < (n + 4) * Nat.centralBinom (n + 4) := by
    exact Nat.four_pow_lt_mul_centralBinom (n + 4) (by omega)
  have hreal :
      (4 : ℝ) ^ (n + 4) < (n + 4 : ℝ) * (Nat.centralBinom (n + 4) : ℝ) := by
    exact_mod_cast hnat
  have hpow_pos : 0 < (4 : ℝ) ^ (n + 4) := by
    positivity
  have hnat_pos : 0 < (n + 4 : ℝ) := by
    positivity
  have hineq :
      1 / (n + 4 : ℝ) <
        (Nat.centralBinom (n + 4) : ℝ) / (4 : ℝ) ^ (n + 4) := by
    have htmp :
        (4 : ℝ) ^ (n + 4) / (n + 4 : ℝ) < (Nat.centralBinom (n + 4) : ℝ) := by
      rw [div_lt_iff₀ hnat_pos]
      simpa [Nat.centralBinom, mul_assoc, mul_comm, mul_left_comm] using hreal
    have hdiv :
        ((4 : ℝ) ^ (n + 4) / (n + 4 : ℝ)) / (4 : ℝ) ^ (n + 4) <
          (Nat.centralBinom (n + 4) : ℝ) / (4 : ℝ) ^ (n + 4) :=
      div_lt_div_of_pos_right htmp hpow_pos
    have hleft :
        ((4 : ℝ) ^ (n + 4) / (n + 4 : ℝ)) / (4 : ℝ) ^ (n + 4) = 1 / (n + 4 : ℝ) := by
      field_simp [hpow_pos.ne', hnat_pos.ne']
    rw [hleft] at hdiv
    exact hdiv
  exact ENNReal.ofReal_le_ofReal hineq.le

/-- Helper for Theorem 17.39: at the symmetric point `p = 1 / 2`, the even return mass rewrites
to the central-binomial coefficient divided by `4^n`. -/
private lemma biasedSimpleRandomWalkOriginMass_even_half
    (p : I) (hp_half : (p : ℝ) = 1 / 2) (n : ℕ) :
    ((dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure ^ (2 * n)) (0 : ℤ))
      ({0} : Set ℤ) =
      ENNReal.ofReal ((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n) := by
  rw [biasedSimpleRandomWalkOriginMass_even (p := p) (n := n)]
  congr 1
  have hpq : (p : ℝ) * (1 - (p : ℝ)) = 1 / 4 := by
    nlinarith [hp_half]
  rw [hpq]
  simp [div_eq_mul_inv, one_div, inv_pow, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Theorem 17.39: the shifted harmonic series diverges in `ℝ≥0∞`. -/
private lemma shiftedHarmonicOfReal_tsum_eq_top :
    (∑' n : ℕ, ENNReal.ofReal (1 / (n + 4 : ℝ))) = ∞ := by
  by_contra hfinite
  have hsummable :
      Summable (fun n : ℕ ↦ (ENNReal.ofReal (1 / (n + 4 : ℝ))).toReal) :=
    ENNReal.summable_toReal (f := fun n : ℕ ↦ ENNReal.ofReal (1 / (n + 4 : ℝ))) <| by
      simpa using hfinite
  have hshift :
      Summable (fun n : ℕ ↦ 1 / (n + 4 : ℝ)) := by
    -- Proof comment: finiteness of the `ℝ≥0∞` series would force summability of the real tail.
    refine hsummable.congr ?_
    intro n
    rw [ENNReal.toReal_ofReal]
    positivity
  have hnot : ¬ Summable (fun n : ℕ ↦ 1 / (n + 4 : ℝ)) := by
    simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm] using
      mt ((_root_.summable_nat_add_iff (f := fun n : ℕ ↦ 1 / (n : ℝ)) 4).1)
        Real.not_summable_one_div_natCast
  exact hnot hshift

/-- Helper for Theorem 17.39: away from `p = 1 / 2`, the central-binomial return series in
formula `(17.19)` sums to `(|2p - 1|)⁻¹`. -/
private lemma biasedSimpleRandomWalkReturnSeries_hasSum (p : I) (hp : (p : ℝ) ≠ 1 / 2) :
    HasSum
      (fun n : ℕ ↦ (Nat.choose (2 * n) n : ℝ) * ((p : ℝ) * (1 - (p : ℝ))) ^ n)
      ((|2 * (p : ℝ) - 1|)⁻¹) := by
  have hp_nonneg : 0 ≤ (p : ℝ) := p.2.1
  have hOne_sub_nonneg : 0 ≤ 1 - (p : ℝ) := sub_nonneg.mpr p.2.2
  have hx_nonneg : 0 ≤ 4 * (p : ℝ) * (1 - (p : ℝ)) := by
    positivity
  have hnorm : ‖((4 * (p : ℝ) * (1 - (p : ℝ)) : ℝ) : ℂ)‖ < 1 := by
    -- Proof comment: the generalized-binomial series is evaluated at the real point
    -- `4 p (1 - p)`, whose norm is just its absolute value.
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx_nonneg]
    exact biasedSimpleRandomWalkFourMul_lt_one_of_ne_half p hp
  have hbase :=
    inverse_sqrt_one_sub_hasSum
      (x := ((4 * (p : ℝ) * (1 - (p : ℝ)) : ℝ) : ℂ)) hnorm
  have hsqrt :
      Complex.sqrt (((1 - (p : ℝ) * ((1 - (p : ℝ)) * 4)) : ℝ) : ℂ) =
        (((1 - (p : ℝ) * ((1 - (p : ℝ)) * 4)).sqrt : ℝ) : ℂ) := by
    have hnonneg : 0 ≤ 1 - (p : ℝ) * ((1 - (p : ℝ)) * 4) := by
      linarith [biasedSimpleRandomWalkFourMul_lt_one_of_ne_half p hp]
    -- Proof comment: along the real nonnegative axis, the complex square root is the real square
    -- root viewed in `ℂ`.
    rw [Complex.sqrt_of_nonneg
      (a := (((1 - (p : ℝ) * ((1 - (p : ℝ)) * 4)) : ℝ) : ℂ))]
    · rfl
    · exact_mod_cast hnonneg
  have hreal0 :
      HasSum
        (fun n : ℕ ↦
          ((p : ℝ) * ((1 - (p : ℝ)) * 4)) ^ n *
            (((4 : ℝ) ^ n)⁻¹ * (Nat.choose (2 * n) n : ℝ)))
        ((1 - (p : ℝ) * ((1 - (p : ℝ)) * 4)).sqrt⁻¹) := by
    -- Proof comment: rewrite the complex half-binomial series as the `Complex.ofReal` image of a
    -- real series before dropping back to `ℝ`.
    apply (Complex.hasSum_ofReal).1
    convert hbase using 2
    · rename_i n
      -- Proof comment: simplify the summand to the real coefficient shape used in the return-mass
      -- formula.
      have hterm :
          ((p : ℝ) * ((1 - (p : ℝ)) * 4)) ^ n *
              (((4 : ℝ) ^ n)⁻¹ * (Nat.choose (2 * n) n : ℝ)) =
            (Nat.choose (2 * n) n : ℝ) * 4⁻¹ ^ n * (4 * (p : ℝ) * (1 - (p : ℝ))) ^ n := by
        calc
          ((p : ℝ) * ((1 - (p : ℝ)) * 4)) ^ n *
              (((4 : ℝ) ^ n)⁻¹ * (Nat.choose (2 * n) n : ℝ))
              =
              (((p : ℝ) * (1 - (p : ℝ))) * 4) ^ n *
                (((4 : ℝ) ^ n)⁻¹ * (Nat.choose (2 * n) n : ℝ)) := by
                  congr 1
                  ring
          _ = (((p : ℝ) * (1 - (p : ℝ))) ^ n * (4 : ℝ) ^ n) *
                (((4 : ℝ) ^ n)⁻¹ * (Nat.choose (2 * n) n : ℝ)) := by
                  rw [mul_pow]
          _ = ((p : ℝ) * (1 - (p : ℝ))) ^ n *
                ((4 : ℝ) ^ n * (((4 : ℝ) ^ n)⁻¹ * (Nat.choose (2 * n) n : ℝ))) := by
                  ring
          _ = ((p : ℝ) * (1 - (p : ℝ))) ^ n * (Nat.choose (2 * n) n : ℝ) := by
                simp
          _ = (Nat.choose (2 * n) n : ℝ) * ((p : ℝ) * (1 - (p : ℝ))) ^ n := by
                ring
          _ = (Nat.choose (2 * n) n : ℝ) * 4⁻¹ ^ n * (4 * (p : ℝ) * (1 - (p : ℝ))) ^ n := by
                calc
                  (Nat.choose (2 * n) n : ℝ) * ((p : ℝ) * (1 - (p : ℝ))) ^ n
                      = (Nat.choose (2 * n) n : ℝ) *
                          (4⁻¹ ^ n * ((4 : ℝ) * ((p : ℝ) * (1 - (p : ℝ)))) ^ n) := by
                            congr 1
                            calc
                              ((p : ℝ) * (1 - (p : ℝ))) ^ n
                                  = 4⁻¹ ^ n * ((4 : ℝ) ^ n * ((p : ℝ) * (1 - (p : ℝ))) ^ n) := by
                                      symm
                                      calc
                                        4⁻¹ ^ n * ((4 : ℝ) ^ n * ((p : ℝ) * (1 - (p : ℝ))) ^ n)
                                            = (4⁻¹ ^ n * (4 : ℝ) ^ n) *
                                                ((p : ℝ) * (1 - (p : ℝ))) ^ n := by
                                                  ring
                                        _ = ((p : ℝ) * (1 - (p : ℝ))) ^ n := by
                                              simp
                              _ = 4⁻¹ ^ n * (((4 : ℝ) * ((p : ℝ) * (1 - (p : ℝ)))) ^ n) := by
                                    congr 1
                                    symm
                                    rw [mul_pow]
                      _ = (Nat.choose (2 * n) n : ℝ) * 4⁻¹ ^ n *
                          (4 * (p : ℝ) * (1 - (p : ℝ))) ^ n := by
                            ring
      simpa [Complex.ofReal_mul, Complex.ofReal_pow, mul_assoc, mul_left_comm, mul_comm,
        sub_eq_add_neg] using congrArg (fun z : ℝ ↦ (z : ℂ)) hterm
    · -- Proof comment: the series value sits on the nonnegative real axis, so the square-root
      -- term becomes the ordinary real square root.
      rw [show (1 - ↑(4 * (p : ℝ) * (1 - (p : ℝ))) : ℂ) =
          (((1 - (p : ℝ) * ((1 - (p : ℝ)) * 4)) : ℝ) : ℂ) by
            norm_num [sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm]]
      rw [hsqrt]
      simp [one_div]
  have hseries :
      HasSum
        (fun n : ℕ ↦ (Nat.choose (2 * n) n : ℝ) * ((p : ℝ) * (1 - (p : ℝ))) ^ n)
        ((1 - (p : ℝ) * ((1 - (p : ℝ)) * 4)).sqrt⁻¹) := by
    refine hreal0.congr_fun ?_
    intro n
    symm
    -- Proof comment: cancel the bookkeeping factor `4^n` against `(4^n)⁻¹` and reorder the
    -- remaining real factors into the central-binomial coefficient shape.
    calc
      ((p : ℝ) * ((1 - (p : ℝ)) * 4)) ^ n * (((4 : ℝ) ^ n)⁻¹ * (Nat.choose (2 * n) n : ℝ))
          = (((p : ℝ) * (1 - (p : ℝ))) * 4) ^ n *
              (((4 : ℝ) ^ n)⁻¹ * (Nat.choose (2 * n) n : ℝ)) := by
                congr 1
                ring
      _ = (((p : ℝ) * (1 - (p : ℝ))) ^ n * (4 : ℝ) ^ n) *
            (((4 : ℝ) ^ n)⁻¹ * (Nat.choose (2 * n) n : ℝ)) := by
              rw [mul_pow]
      _ = ((p : ℝ) * (1 - (p : ℝ))) ^ n *
            ((4 : ℝ) ^ n * (((4 : ℝ) ^ n)⁻¹ * (Nat.choose (2 * n) n : ℝ))) := by
              ring
      _ = ((p : ℝ) * (1 - (p : ℝ))) ^ n * (Nat.choose (2 * n) n : ℝ) := by
            simp
      _ = (Nat.choose (2 * n) n : ℝ) * ((p : ℝ) * (1 - (p : ℝ))) ^ n := by
            ring
  have hvalue :
      (1 - (p : ℝ) * ((1 - (p : ℝ)) * 4)).sqrt⁻¹ =
        ((|2 * (p : ℝ) - 1|)⁻¹) := by
    -- Proof comment: the quadratic discriminant is exactly `(2p - 1)^2`, so the square root
    -- collapses to `|2p - 1|`.
    rw [show 1 - (p : ℝ) * ((1 - (p : ℝ)) * 4) =
        1 - 4 * (p : ℝ) * (1 - (p : ℝ)) by ring,
      biasedSimpleRandomWalkSqrtDiscriminant_eq_abs]
  simpa [hvalue] using hseries

-- TODO: restore the even/odd return-mass computation and generalized-binomial summation.
/-- Theorem 17.39 (2): for the one-dimensional nearest-neighbor walk with right-jump probability
`p` and left-jump probability `1 - p`, the Green function at the origin has the value
`1 / |2p - 1|` when `p ≠ 1 / 2` and is infinite when `p = 1 / 2`. This is the textbook formula
for `G(0,0)`. The parameter `p : I` is the canonical probability-valued owner, and the walk
kernel is derived from the step law `biasedSimpleRandomWalkStepPMF p`. -/
theorem biasedSimpleRandomWalk_greenFunction_zero_zero
    (P : ℤ → ProbabilityMeasure Ω) (X : ℕ → Ω → ℤ) (p : I)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure ^ n) P X] :
    (G[P, X]) 0 0 =
      if (p : ℝ) = 1 / 2 then
        ∞
      else
        ENNReal.ofReal ((|2 * (p : ℝ) - 1|)⁻¹) :=
  by
    let term : ℕ → ℝ≥0∞ := fun n ↦
      ((dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure ^ n) (0 : ℤ))
        ({0} : Set ℤ)
    have hgreen :
        (G[P, X]) 0 0 = ∑' n : ℕ, term n := by
      -- Proof comment: package the diagonal Green value as the origin-mass series once so that
      -- both branches can work by even/odd decomposition.
      simpa [term] using
        biasedSimpleRandomWalk_greenFunction_zero_zero_eq_tsum_originMass
          (P := P) (X := X) (p := p)
    have hodd_tsum : (∑' n : ℕ, term (2 * n + 1)) = 0 := by
      -- Proof comment: odd return times have zero origin mass, so the odd branch vanishes.
      calc
        (∑' n : ℕ, term (2 * n + 1)) = ∑' n : ℕ, (0 : ℝ≥0∞) := by
          refine tsum_congr fun n ↦ ?_
          simpa [term] using biasedSimpleRandomWalkOriginMass_odd (p := p) n
        _ = 0 := by simp
    -- Route correction: the remaining proof should no longer reopen the Green-function
    -- definition or the broken diagonal-translation route. First rewrite `G(0,0)` as the origin
    -- mass series via `biasedSimpleRandomWalk_greenFunction_zero_zero_eq_tsum_originMass`, then
    -- replace the odd/even origin masses by the binomial return formulas and evaluate the exact
    -- central-binomial series using Lemma 3.5.
    by_cases hp_half : (p : ℝ) = 1 / 2
    · rw [if_pos hp_half]
      have hEven_top : (∑' n : ℕ, term (2 * n)) = ∞ := by
        by_contra hfinite
        have hEvenSummable :
            Summable (fun n : ℕ ↦ (term (2 * n)).toReal) :=
          ENNReal.summable_toReal (f := fun n : ℕ ↦ term (2 * n)) <| by
            simpa using hfinite
        have hEvenShift :
            Summable (fun n : ℕ ↦ (term (2 * (n + 4))).toReal) := by
          -- Proof comment: a finite even-series sum would make every finite tail summable.
          simpa [Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            ((_root_.summable_nat_add_iff (f := fun n : ℕ ↦ (term (2 * n)).toReal) 4).2
              hEvenSummable)
        have hHarmonicSummable :
            Summable (fun n : ℕ ↦ 1 / (n + 4 : ℝ)) := by
          -- Proof comment: the harmonic tail is pointwise dominated by the symmetric even return
          -- masses, so it would inherit summability from the finite even tail.
          refine Summable.of_nonneg_of_le (fun n ↦ by positivity) ?_ hEvenShift
          intro n
          have hcompare :
              1 / (n + 4 : ℝ) ≤
                (Nat.choose (2 * (n + 4)) (n + 4) : ℝ) / (4 : ℝ) ^ (n + 4) := by
            exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1
              (centralBinomialReturnMass_at_half_ge_harmonic n)
          calc
            1 / (n + 4 : ℝ)
              ≤ (Nat.choose (2 * (n + 4)) (n + 4) : ℝ) / (4 : ℝ) ^ (n + 4) := hcompare
            _ = (term (2 * (n + 4))).toReal := by
              have hmass :
                  (term (2 * (n + 4))).toReal =
                    (Nat.choose (2 * (n + 4)) (n + 4) : ℝ) / (4 : ℝ) ^ (n + 4) := by
                have hmass0 :
                    (term (2 * (n + 4))).toReal =
                      (ENNReal.ofReal
                        ((Nat.choose (2 * (n + 4)) (n + 4) : ℝ) / (4 : ℝ) ^ (n + 4))).toReal := by
                  simpa [term] using
                    congrArg ENNReal.toReal
                      (biasedSimpleRandomWalkOriginMass_even_half (p := p) hp_half (n := n + 4))
                rw [ENNReal.toReal_ofReal (by positivity)] at hmass0
                exact hmass0
              exact hmass.symm
        have hHarmonicNot :
            ¬ Summable (fun n : ℕ ↦ 1 / (n + 4 : ℝ)) := by
          intro hs
          exact hs.tsum_ofReal_ne_top shiftedHarmonicOfReal_tsum_eq_top
        exact hHarmonicNot hHarmonicSummable
      calc
        (G[P, X]) 0 0 = ∑' n : ℕ, term n := hgreen
        _ = (∑' n : ℕ, term (2 * n)) + ∑' n : ℕ, term (2 * n + 1) := by
              rw [← tsum_even_add_odd ENNReal.summable ENNReal.summable]
        _ = (∑' n : ℕ, term (2 * n)) + 0 := by rw [hodd_tsum]
        _ = ∞ := by rw [hEven_top, top_add]
    · rw [if_neg hp_half]
      have hseries := biasedSimpleRandomWalkReturnSeries_hasSum p hp_half
      have hEven_tsum :
          (∑' n : ℕ, term (2 * n)) = ENNReal.ofReal ((|2 * (p : ℝ) - 1|)⁻¹) := by
        calc
          (∑' n : ℕ, term (2 * n)) =
              ∑' n : ℕ,
                ENNReal.ofReal
                  ((Nat.choose (2 * n) n : ℝ) * ((p : ℝ) * (1 - (p : ℝ))) ^ n) := by
                    refine tsum_congr fun n ↦ ?_
                    simpa [term] using biasedSimpleRandomWalkOriginMass_even (p := p) n
          _ = ENNReal.ofReal
                (∑' n : ℕ,
                  (Nat.choose (2 * n) n : ℝ) * ((p : ℝ) * (1 - (p : ℝ))) ^ n) := by
                rw [← ENNReal.ofReal_tsum_of_nonneg]
                · intro n
                  have hp_nonneg : 0 ≤ (p : ℝ) := p.2.1
                  have hOne_sub_nonneg : 0 ≤ 1 - (p : ℝ) := sub_nonneg.mpr p.2.2
                  exact mul_nonneg (by positivity)
                    (pow_nonneg (mul_nonneg hp_nonneg hOne_sub_nonneg) _)
                · exact hseries.summable
          _ = ENNReal.ofReal ((|2 * (p : ℝ) - 1|)⁻¹) := by rw [hseries.tsum_eq]
      calc
        (G[P, X]) 0 0 = ∑' n : ℕ, term n := hgreen
        _ = (∑' n : ℕ, term (2 * n)) + ∑' n : ℕ, term (2 * n + 1) := by
              rw [← tsum_even_add_odd ENNReal.summable ENNReal.summable]
        _ = ENNReal.ofReal ((|2 * (p : ℝ) - 1|)⁻¹) + 0 := by rw [hEven_tsum, hodd_tsum]
        _ = ENNReal.ofReal ((|2 * (p : ℝ) - 1|)⁻¹) := by simp

/-- Helper for Theorem 17.39: for bias `p = 1`, each one-step kernel row is the Dirac mass at the
deterministic successor state. -/
private lemma biasedSimpleRandomWalkOne_kernel_eq_diracSucc (x : ℤ) :
    dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF (1 : I)).toMeasure x =
      Measure.dirac (x + 1) := by
  refine Measure.ext_of_singleton fun y ↦ ?_
  by_cases hy : y = x + 1
  · subst hy
    -- Proof comment: at bias `1`, the only allowed step is the deterministic jump to `x + 1`.
    rw [biasedSimpleRandomWalkKernel_apply_singleton]
    simp
  · -- Proof comment: away from `x + 1`, the deterministic step law has zero singleton mass.
    rw [biasedSimpleRandomWalkKernel_apply_singleton]
    simp [hy]

-- TODO: reprove the deterministic right-drift kernel power formula with the current kernel API.
/-- Helper for Theorem 17.39: when the bias is `1`, the walk moves deterministically to `x + n`
after `n` steps. -/
lemma biasedSimpleRandomWalkOne_pow_eq_dirac (x : ℤ) :
    ∀ n : ℕ,
      ((dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF (1 : I)).toMeasure ^ n) x) =
        Measure.dirac (x + n) :=
  by
    intro n
    induction n with
    | zero =>
        -- Proof comment: the zero-step kernel is the identity, so it leaves the starting state
        -- fixed.
        simpa using (Kernel.id_apply x)
    | succ n ih =>
        have hstepLaw :
            (biasedSimpleRandomWalkStepPMF (1 : I)).toMeasure = Measure.dirac (1 : ℤ) := by
          refine Measure.ext_of_singleton fun z ↦ ?_
          rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton z)]
          by_cases hz : z = 1
          · subst hz
            simp [biasedSimpleRandomWalkStepPMF]
          · simp [biasedSimpleRandomWalkStepPMF, hz]
        refine Measure.ext_of_singleton fun y ↦ ?_
        -- Proof comment: compose the inductive Dirac law with the deterministic one-step shift.
        rw [Kernel.pow_succ_apply_eq_lintegral
          (dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF (1 : I)).toMeasure)
          n x (measurableSet_singleton y)]
        rw [ih]
        -- Proof comment: after rewriting the step law as `δ₁`, the convolution stays a Dirac mass
        -- at the translated successor state.
        simpa [hstepLaw, add_assoc] using
          (show
            ∫⁻ a,
                dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF (1 : I)).toMeasure a {y}
                ∂Measure.dirac (x + n) =
              Measure.dirac (x + n + 1) {y} by
              simp [hstepLaw, dirac_convolution_kernel_apply, Measure.dirac_conv])

/-- Helper for Theorem 17.39: composing a translation convolution kernel with a measure is just
measure convolution by the common step law. -/
private lemma diracConvolutionKernel_comp_measure_eq_conv
    (μ ν : Measure ℤ) [SFinite μ] [SFinite ν] :
    dirac_convolution_kernel ν ∘ₘ μ = μ ∗ ν := by
  have hconst :=
    congrArg
      (fun κ : Kernel ℤ ℤ ↦ κ (0 : ℤ))
      (dirac_convolution_kernel_comp_const_eq_const_conv (μ := μ) (ν := ν))
  simpa [Kernel.comp_apply] using hconst

/-- Helper for Theorem 17.39: after `n` steps, the row of a translation kernel is the translate
of the origin-started `n`-step law. -/
private lemma diracConvolutionKernel_pow_apply_eq_diracConv_origin
    (μ : Measure ℤ) :
    ∀ n : ℕ, ∀ x : ℤ,
      ((dirac_convolution_kernel μ ^ n) x) =
        (Measure.dirac x) ∗ ((dirac_convolution_kernel μ ^ n) (0 : ℤ))
  | 0, x => by
      -- Proof comment: the zero-step law is the starting Dirac mass.
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

/-- Helper for Theorem 17.39: the `n`-step singleton mass of the biased walk kernel depends only
on the displacement `y - x`. -/
private lemma diracConvolutionKernel_pow_apply_singleton_eq_originMass
    (μ : Measure ℤ) (n : ℕ) (x y : ℤ) :
    ((dirac_convolution_kernel μ ^ n) x) ({y} : Set ℤ) =
      ((dirac_convolution_kernel μ ^ n) (0 : ℤ)) ({y - x} : Set ℤ) := by
  rw [diracConvolutionKernel_pow_apply_eq_diracConv_origin μ n x]
  rw [Measure.dirac_conv]
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

/-- Helper for Theorem 17.39: for the biased convolution kernel, recurrence of the origin
propagates to every state because the diagonal Green function is translation invariant. -/
private theorem biasedSimpleRandomWalk_recurrentState_of_origin
    (P : ℤ → ProbabilityMeasure Ω) (X : ℕ → Ω → ℤ) (p : I)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure ^ n) P X]
    (hrec0 : IsRecurrentState P X 0) :
    ∀ x : ℤ, IsRecurrentState P X x := by
  intro x
  let hReal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure ^ n)
        P X := inferInstance
  let hX : IsStochasticProcess X := fun n ↦ hReal.measurable_process n
  have hgreen0 : (G[P, X]) 0 0 = ⊤ :=
    greenFunctionSelf_eq_top_of_isRecurrentState
      (P := P) (X := X)
      (κ := fun n : ℕ ↦ dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure ^ n)
      0 hrec0
  have hgreenx : (G[P, X]) x x = ⊤ := by
    -- Route correction: compare diagonal Green values through the `n`-step kernel rows, rather
    -- than trying to transport the realized marginals `(P x).map (X n)` directly.
    calc
      (G[P, X]) x x =
          ∑' n : ℕ,
            ((dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure ^ n) x)
              ({x} : Set ℤ) := by
                rw [greenFunction_eq_tsum_stateProbabilities P X hX x x]
                refine tsum_congr fun n ↦ ?_
                have htransition :=
                  congrArg
                    (fun μ : Measure ℤ ↦ μ ({x} : Set ℤ))
                    (hReal.transition_eq x n)
                simpa [Measure.map_apply (hReal.measurable_process n)
                  (measurableSet_singleton x)] using htransition
      _ = ∑' n : ℕ,
            ((dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure ^ n) (0 : ℤ))
              ({0} : Set ℤ) := by
                refine tsum_congr fun n ↦ ?_
                simpa using
                  diracConvolutionKernel_pow_apply_singleton_eq_originMass
                    (μ := (biasedSimpleRandomWalkStepPMF p).toMeasure) n x x
      _ = (G[P, X]) 0 0 := by
            symm
            exact biasedSimpleRandomWalk_greenFunction_zero_zero_eq_tsum_originMass
              (P := P) (X := X) (p := p)
      _ = ⊤ := hgreen0
  exact
    isRecurrentState_of_greenFunctionSelf_eq_top
      (P := P) (X := X)
      (κ := fun n : ℕ ↦ dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure ^ n)
      x hgreenx

-- TODO: restore the recurrence criterion from the diagonal Green-value calculation in part (2).
/-- Theorem 17.39 (3): a one-dimensional simple random walk with right-jump probability `p` is
recurrent exactly in the symmetric case `p = 1 / 2`. -/
theorem biasedSimpleRandomWalk_recurrent_iff_symmetric
    (P : ℤ → ProbabilityMeasure Ω) (X : ℕ → Ω → ℤ) (p : I)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure ^ n) P X] :
    IsRecurrentMarkovChain P X ↔ (p : ℝ) = 1 / 2 :=
  by
    constructor
    · intro hrec
      by_contra hp_half
      have hgreen_top :
          (G[P, X]) 0 0 = ⊤ :=
        greenFunctionSelf_eq_top_of_isRecurrentState
          (P := P) (X := X)
          (κ := fun n : ℕ ↦ dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure ^ n)
          0 (hrec 0)
      -- Proof comment: part (2) gives a finite diagonal Green value off the symmetric branch,
      -- contradicting recurrence of the origin.
      rw [biasedSimpleRandomWalk_greenFunction_zero_zero (P := P) (X := X) (p := p),
        if_neg hp_half] at hgreen_top
      exact ENNReal.ofReal_ne_top hgreen_top
    · intro hp_half
      have hgreen_top : (G[P, X]) 0 0 = ⊤ := by
        -- Proof comment: in the symmetric branch, part (2) identifies the origin Green value
        -- with `∞`.
        rw [biasedSimpleRandomWalk_greenFunction_zero_zero (P := P) (X := X) (p := p),
          if_pos hp_half]
      have hrec0 : IsRecurrentState P X 0 :=
        isRecurrentState_of_greenFunctionSelf_eq_top
          (P := P) (X := X)
          (κ := fun n : ℕ ↦ dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure ^ n)
          0 hgreen_top
      -- Proof comment: once the origin is recurrent, translation invariance of the convolution
      -- kernel makes every diagonal Green value infinite as well.
      exact biasedSimpleRandomWalk_recurrentState_of_origin (P := P) (X := X) (p := p) hrec0

/-- Helper for Theorem 17.39: the real-valued partial sums of the increment family agree with the
cast integer random walk. -/
lemma randomWalkProcess_real_apply
    {Ω' : Type*} [MeasurableSpace Ω'] (Z : ℕ → Ω' → ℤ) (n : ℕ) (ω : Ω') :
    (∑ i ∈ Finset.range n, (Z i ω : ℝ)) = (randomWalkProcess Z n ω : ℝ) :=
  by
    -- Proof comment: `randomWalkProcess` is exactly this finite integer sum, viewed after casting
    -- to `ℝ`.
    rw [randomWalkProcess_apply]
    exact_mod_cast rfl

/-- Helper for Theorem 17.39: the strong law for an i.i.d. increment family rewrites directly
into the random-walk notation. -/
lemma randomWalkProcess_ae_tendsto_stepMean
    {Ω' : Type*} [MeasurableSpace Ω'] (ν : ProbabilityMeasure ℤ)
    (Q : ProbabilityMeasure Ω') (Z : ℕ → Ω' → ℤ)
    (hfirstMoment : Integrable (fun z : ℤ ↦ (z : ℝ)) (ν : Measure ℤ))
    (hZ_indep : iIndepFun Z (Q : Measure Ω'))
    (hZ_law : ∀ n : ℕ, HasLaw (Z n) (ν : Measure ℤ) (Q : Measure Ω')) :
    ∀ᵐ ω ∂(Q : Measure Ω'),
      Tendsto (fun n : ℕ ↦ (randomWalkProcess Z n ω : ℝ) / n) atTop
        (nhds (∫ z, (z : ℝ) ∂(ν : Measure ℤ))) :=
  by
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
      have hcast_meas :
          Measurable ((↑) : ℤ → ℝ) := by
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

/-- Helper for Theorem 17.39: the diagonal Green value at the origin is the common origin-mass
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
  -- Proof comment: rewrite each time-`n` visit probability at the origin through the
  -- realization identity for the convolution kernel.
  rw [greenFunction_eq_tsum_stateProbabilities P X hX 0 0]
  refine tsum_congr fun n ↦ ?_
  have htransition :=
    congrArg (fun ρ : Measure ℤ ↦ ρ ({0} : Set ℤ)) (hReal.transition_eq (0 : ℤ) n)
  simpa [Measure.map_apply (hReal.measurable_process n) (measurableSet_singleton (0 : ℤ))] using
    htransition

/-- Helper for Theorem 17.39: once the origin diagonal Green value is infinite, translation
invariance of the convolution kernel makes every state recurrent. -/
private theorem integerRandomWalk_recurrentState_of_origin
    (ν : ProbabilityMeasure ℤ)
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
    -- Proof comment: compare the diagonal Green series through the `n`-step kernel rows, so the
    -- translation invariance is handled at the singleton-mass level.
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
            simpa using
              diracConvolutionKernel_pow_apply_singleton_eq_originMass
                (μ := (ν : Measure ℤ)) n x x
      _ = (G[P, X]) (0 : ℤ) 0 := by
            symm
            exact integerWalk_greenFunction_zero_zero_eq_tsum_originMass
              (ν := ν) (P := P) (X := X)
      _ = ⊤ := hgreen0
  exact
    isRecurrentState_of_greenFunctionSelf_eq_top
      (κ := fun n : ℕ ↦ dirac_convolution_kernel (ν : Measure ℤ) ^ n)
      (P := P) (X := X) x hgreenx

/-- Helper for Theorem 17.39: if a time-`n` history event already forces `X n = z`, then
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

/-- Helper for Theorem 17.39: `firstPositiveHitEvent X y n` is the event that the path first hits
`y` at the positive time `n`. -/
private def firstPositiveHitEvent (Y : ℕ → Ω → ℤ) (y : ℤ) (n : ℕ) : Set Ω :=
  {ω | Y n ω = y ∧ ∀ j : ℕ, 1 ≤ j → j ≤ n - 1 → Y j ω ≠ y}

/-- Helper for Theorem 17.39: the exact first-positive-hit event is measurable. -/
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

/-- Helper for Theorem 17.39: every exact first-positive-hit event is contained in the
corresponding state event. -/
private lemma firstPositiveHitEvent_subset_state
    (Y : ℕ → Ω → ℤ) (y : ℤ) (n : ℕ) :
    firstPositiveHitEvent Y y n ⊆ {ω | Y n ω = y} :=
  fun _ hω ↦ hω.1

/-- Helper for Theorem 17.39: exact first-positive-hit events at distinct positive times are
pairwise disjoint. -/
private lemma firstPositiveHitEvent_disjoint
    (Y : ℕ → Ω → ℤ) (y : ℤ) {m n : ℕ}
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

/-- Helper for Theorem 17.39: at a fixed positive time `k`, the state event `{X k = y}` splits
as the union over the exact first positive hit time of `y`. -/
private lemma firstPositiveHitEvent_partition_stateEvent
    (Y : ℕ → Ω → ℤ) (y : ℤ) {k : ℕ} (hk : 1 ≤ k) :
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
      intro j
      intro hj_pos
      intro hj_le
      intro hj_state
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

/-- Helper for Theorem 17.39: the exact first-positive-hit event is already measurable in the
time-`n` history filtration. -/
private lemma firstPositiveHitEvent_measurableInFiltration
    (Y : ℕ → Ω → ℤ) (y : ℤ) (n : ℕ) :
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

/-- Helper for Theorem 17.39: in any realized one-dimensional walk, the finite Green window at an
off-diagonal target is bounded by the corresponding diagonal window at that target. -/
private lemma truncatedGreen_offDiagonal_le_self
    {κ : ℕ → Kernel ℤ ℤ} {P : ℤ → ProbabilityMeasure Ω}
    [IsMarkovProcessRealization κ P X]
    (N : ℕ) (y : ℤ) :
    (∑ k ∈ Finset.range (N + 1), (P 0 : Measure Ω) {ω | X k ω = y}) ≤
      (∑ k ∈ Finset.range (N + 1), (P y : Measure Ω) {ω | X k ω = y}) := by
  by_cases hy : y = 0
  · -- Proof comment: on the diagonal, the two truncated Green windows are identical.
    simpa [hy]
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
    -- Proof comment: the time-`m` singleton mass from `y` is exactly the corresponding
    -- transition-kernel row evaluated on `{y}`.
    dsimp [selfMass]
    rw [hpreimage, ← Measure.map_apply (hReal.measurable_process m)
      (measurableSet_singleton y), hReal.transition_eq y m]
  have htimeZero :
      (P 0 : Measure Ω) {ω | X 0 ω = y} = 0 := by
    have hpreimage : {ω | X 0 ω = y} = X 0 ⁻¹' ({y} : Set ℤ) := by
      ext ω
      simp
    -- Proof comment: starting from `0`, the chain cannot be at the distinct state `y` at time
    -- `0`.
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
      -- Proof comment: the exact first-hit layers are disjoint, so their masses add.
      symm
      simpa [hitMass, U] using MeasureTheory.measure_biUnion_finset hhit_disjoint hhit_meas
    calc
      ∑ n ∈ Finset.Ico 1 (N + 1), hitMass n = (P 0 : Measure Ω) U := hsum
      _ ≤ (P 0 : Measure Ω) Set.univ := by
        exact measure_mono (by intro ω hω; simp [U])
      _ = 1 := by simp
  have hstate_decomp :
      ∀ k ∈ Finset.Ico 1 (N + 1),
        (P 0 : Measure Ω) {ω | X k ω = y} =
          ∑ n ∈ Finset.Ico 1 (k + 1), selfMass (k - n) * hitMass n := by
    intro k hk
    have hk_pos : 1 ≤ k := (Finset.mem_Ico.mp hk).1
    have hIccIco : Finset.Icc 1 k = Finset.Ico 1 (k + 1) := by
      ext n
      simp [Nat.lt_succ_iff]
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
    -- Proof comment: decompose the time-`k` state event by the exact first hit of `y`, then
    -- factor each slice through the post-hit return window from `y`.
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
  -- Proof comment: sum the slice decompositions over the time window, commute the triangular
  -- finite sum, and then bound the remaining first-hit mass by `1`.
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
            exact mul_le_mul_left' (hinner_le n hn) (hitMass n)
    _ = (∑ n ∈ Finset.Ico 1 (N + 1), hitMass n) * GselfN := by
            rw [Finset.sum_mul]
    _ = GselfN * (∑ n ∈ Finset.Ico 1 (N + 1), hitMass n) := by
            rw [mul_comm]
    _ ≤ GselfN * 1 := by
            exact mul_le_mul_left' hhit_sum_le_one GselfN
    _ = GselfN := by simp
    _ = ∑ k ∈ Finset.range (N + 1), (P y : Measure Ω) {ω | X k ω = y} := by
            rfl

/-- Helper for Theorem 17.39: on the canonical one-dimensional convolution walk, summing the
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
    -- Proof comment: the realized walk event is exactly the corresponding singleton event of the
    -- `k`-step convolution kernel.
    rw [hpreimage, ← Measure.map_apply (hReal.measurable_process k)
      (measurableSet_singleton y), hReal.transition_eq x k]
  have hintervalSplit :
      ∑ k ∈ Finset.range (N + 1),
          ((dirac_convolution_kernel (ν : Measure ℤ) ^ k) (0 : ℤ)) (window : Set ℤ) =
        ∑ y ∈ window, ∑ k ∈ Finset.range (N + 1),
          ((dirac_convolution_kernel (ν : Measure ℤ) ^ k) (0 : ℤ)) ({y} : Set ℤ) := by
    -- Proof comment: on the discrete state space `ℤ`, the interval mass is the finite sum of its
    -- singleton masses.
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
    -- Proof comment: the local first-hit argument compares the origin-to-`y` window with the
    -- diagonal window at `y`, and translation invariance identifies the latter with the origin
    -- diagonal window.
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
              diracConvolutionKernel_pow_apply_singleton_eq_originMass
                (μ := (ν : Measure ℤ)) k y y
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

/-- Helper for Theorem 17.39: if the normalized position is at most `1 / m` and `k ≤ m * L`,
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

/-- Helper for Theorem 17.39: starting the canonical walk deterministically from `0` rewrites the
ambient measure as the pushforward of the increment law by `ω ↦ (0, ω)`. -/
private lemma productStartRandomWalkMeasure_zero_eq_map
    {Ω' : Type*} [MeasurableSpace Ω'] (Qprob : ProbabilityMeasure Ω') :
    (productStartRandomWalkMeasure Qprob 0 : Measure (ℤ × Ω')) =
      (Qprob : Measure Ω').map (fun ω ↦ ((0 : ℤ), ω)) := by
  -- Proof comment: the first coordinate is fixed by the Dirac mass, so only the increment sample
  -- remains random.
  change ((Measure.dirac (0 : ℤ)).prod (Qprob : Measure Ω')) =
    (Qprob : Measure Ω').map (fun ω ↦ ((0 : ℤ), ω))
  rw [Measure.dirac_prod]

/-- Helper for Theorem 17.39: the normalized canonical walk `X_k / k` converges to `0` in
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
      ∀ᵐ s ∂μ0,
        Tendsto (fun n : ℕ ↦ (productStartRandomWalk Z n s : ℝ) / n) atTop
          (nhds (∫ z, (z : ℝ) ∂(ν : Measure ℤ))) := by
    let hprodMk : MeasurableEmbedding (fun ω : Ω' ↦ ((0 : ℤ), ω)) :=
      MeasurableEmbedding.prodMk_left (x := (0 : ℤ)) (f := id) MeasurableEmbedding.id
    change
      ∀ᵐ s ∂(productStartRandomWalkMeasure Qprob 0 : Measure (ℤ × Ω')),
        Tendsto (fun n : ℕ ↦ (productStartRandomWalk Z n s : ℝ) / n) atTop
          (nhds (∫ z, (z : ℝ) ∂(ν : Measure ℤ)))
    rw [productStartRandomWalkMeasure_zero_eq_map Qprob]
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
  -- Proof comment: finite-measure almost-sure convergence upgrades directly to convergence in
  -- measure once the normalized coordinates are measurable.
  simpa [hν_mean_zero] using MeasureTheory.tendstoInMeasure_of_tendsto_ae hmeas hlimit_ae

/-- Helper for Theorem 17.39: on the canonical product-start walk, the small-deviation event
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
  -- Proof comment: control the small-deviation event from below by the complement of the bad
  -- normalized event, and use that the latter has asymptotically vanishing probability.
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

/-- Helper for Theorem 17.39: realized window-event probabilities on the canonical product-start
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
  -- Proof comment: rewrite the realized event as a preimage under the time-`k` coordinate and
  -- then invoke the realization identity for the `k`-step kernel.
  rw [hpreimage, Measure.real, ← Measure.map_apply (hReal.measurable_process k) hS,
    hReal.transition_eq (0 : ℤ) k]

/-- Helper for Theorem 17.39: a uniform `1 / 2` lower bound on the small-deviation events forces
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
  let windowMass : ℕ → ℝ≥0∞ := fun k ↦ ((dirac_convolution_kernel (ν : Measure ℤ) ^ k) (0 : ℤ)) window
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
      MeasureTheory.measureReal_mono (μ := (productStartRandomWalkMeasure Qprob 0 : Measure (ℤ × Ω'))) hsubset
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
    simpa using Nat.card_Icc K (m * L)
  have htail_sum :
      ((m * L + 1 - K : ℝ) / 2) ≤
        ∑ k ∈ Finset.Icc K (m * L), (windowMass k).toReal := by
    -- Proof comment: there are exactly `m * L + 1 - K` tail times, and each contributes at
    -- least `1 / 2`.
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
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset_range (fun _ _ _ ↦ MeasureTheory.measureReal_nonneg)
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
          have htransition :=
            congrArg (fun μ : Measure ℤ ↦ μ Set.univ) (hReal.transition_eq (0 : ℤ) k)
          calc
            ((dirac_convolution_kernel (ν : Measure ℤ) ^ k) (0 : ℤ)) Set.univ =
                (Measure.map (productStartRandomWalk Z k)
                  (productStartRandomWalkMeasure Qprob 0 : Measure (ℤ × Ω'))) Set.univ := by
                    simpa using htransition.symm
            _ = 1 := by
                  rw [Measure.map_apply (hReal.measurable_process k) MeasurableSet.univ]
                  simp
        rw [huniv_eq_one]
        simp
      exact ne_top_of_le_ne_top huniv_ne_top (by simpa [windowMass] using hle)
  -- Proof comment: convert the full finite window sum to a real-valued finite sum, then compare
  -- the tail sub-sum with the whole range.
  calc
    ((m * L + 1 - K : ℝ) / 2) ≤ ∑ k ∈ Finset.Icc K (m * L), (windowMass k).toReal := htail_sum
    _ ≤ ∑ k ∈ Finset.range (m * L + 1), (windowMass k).toReal := hsum_le
    _ = (∑ k ∈ Finset.range (m * L + 1), windowMass k).toReal := htoReal_sum.symm
    _ =
        (∑ k ∈ Finset.range (m * L + 1),
          ((dirac_convolution_kernel (ν : Measure ℤ) ^ k) (0 : ℤ))
            ((Finset.Icc (-(L : ℤ)) L : Finset ℤ) : Set ℤ)).toReal := by
          rfl

/-- Helper for Theorem 17.39: the remaining zero-drift task is to prove that the origin Green
value diverges. This isolates the source proof's finite-window averaging argument from the
translation-invariance packaging used in the final theorem. -/
private lemma integerRandomWalk_greenFunction_zero_zero_eq_top_of_integrable_mean_zero
    (ν : ProbabilityMeasure ℤ)
    (hν_integrable : Integrable (fun z : ℤ ↦ (z : ℝ)) (ν : Measure ℤ))
    (hν_mean_zero : ∫ z, (z : ℝ) ∂(ν : Measure ℤ) = 0)
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
    -- Proof comment: this is the finite-window averaging inequality from the source proof,
    -- now packaged in canonical kernel language for the product-start walk.
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
        ((((8 * M + 1 : ℕ) : ℝ) * (K + 2 * M) + 1 - K) / 2) -
            ((2 * (K + 2 * M) + 1 : ℝ) * M) =
          (1 / 2 : ℝ) + 2 * (M : ℝ) * K + 4 * (M : ℝ) ^ 2 := by
      norm_num [Nat.cast_add, Nat.cast_mul]
      ring
    have haux :
        0 <
          ((((8 * M + 1 : ℕ) : ℝ) * (K + 2 * M) + 1 - K) / 2) -
            ((2 * (K + 2 * M) + 1 : ℝ) * M) := by
      rw [hdiff]
      positivity
    have hgoal :
        ((2 * (K + 2 * M) + 1 : ℝ) * M) <
          ((((8 * M + 1 : ℕ) : ℝ) * (K + 2 * M) + 1 - K) / 2) :=
      sub_pos.mp haux
    simpa [Nat.cast_add, Nat.cast_mul] using hgoal
  -- Proof comment: the lower window estimate and the averaging upper bound now force the same
  -- real quantity to be simultaneously larger and smaller than `(2L + 1) M`.
  have : ((2 * L + 1 : ℝ) * M) < ((2 * L + 1 : ℝ) * M) := by
    exact lt_trans hstrict_bound (lt_of_le_of_lt hwindowLower hwindow_lt_bound)
  exact (lt_irrefl ((2 * L + 1 : ℝ) * M)) this

/-- Theorem 17.39 (4): a one-dimensional random walk on `ℤ` with finite first moment and mean-zero
increment law is recurrent. -/
theorem integerRandomWalk_recurrent_of_integrable_mean_zero
    (ν : ProbabilityMeasure ℤ)
    (hν_integrable : Integrable (fun z : ℤ ↦ (z : ℝ)) (ν : Measure ℤ))
    (hν_mean_zero : ∫ z, (z : ℝ) ∂(ν : Measure ℤ) = 0)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ dirac_convolution_kernel (ν : Measure ℤ) ^ n) P X] :
    IsRecurrentMarkovChain P X := by
  have hgreen0 :
      (G[P, X]) (0 : ℤ) 0 = ⊤ :=
    integerRandomWalk_greenFunction_zero_zero_eq_top_of_integrable_mean_zero
      (P := P) (X := X) (ν := ν) hν_integrable hν_mean_zero
  -- Proof comment: once the origin Green function diverges, the earlier translation-invariance
  -- argument propagates recurrence from `0` to every state.
  exact integerRandomWalk_recurrentState_of_origin (ν := ν) (P := P) (X := X) hgreen0

end OneDimensionalWalk

end ProbabilityTheory
