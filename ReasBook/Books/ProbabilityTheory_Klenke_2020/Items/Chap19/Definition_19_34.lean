/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_11
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_16
import Books.ProbabilityTheory_Klenke_2020.Items.Chap08.Example_8_27
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

/-- A one-dimensional nearest-neighbor environment on `ℤ`, assigning to each site the
probability of a jump to the right. The left-jump probability is then `1 - W.rightJumpProb x`. -/
structure RandomEnvironment where
  /-- The probability of a jump from `x` to `x + 1`. -/
  rightJumpProb : ℤ → ℝ≥0
  /-- The right-jump probabilities are at most `1`. -/
  rightJumpProb_le_one : ∀ x : ℤ, rightJumpProb x ≤ 1

/-- The one-step transition matrix on `ℤ` determined by the environment `W`: from `x` the walk
jumps to `x + 1` with probability `W.rightJumpProb x` and to `x - 1` with the complementary
probability. This is the source-facing discrete owner; `discreteMatrixKernel` is the canonical
kernel bridge attached to it. -/
def randomEnvironmentTransitionMatrix (W : RandomEnvironment) : ℤ → ℤ → ℝ≥0∞ :=
  fun x y ↦
    if y = x + 1 then W.rightJumpProb x
    else if y = x - 1 then (1 : ℝ≥0) - W.rightJumpProb x
    else 0

/-- Evaluating the RWRE transition matrix recovers the textbook nearest-neighbor step
probabilities. -/
theorem randomEnvironmentTransitionMatrix_apply (W : RandomEnvironment) (x y : ℤ) :
    randomEnvironmentTransitionMatrix W x y =
      if y = x + 1 then (W.rightJumpProb x : ℝ≥0∞)
      else if y = x - 1 then (((1 : ℝ≥0) - W.rightJumpProb x : ℝ≥0) : ℝ≥0∞)
      else 0 := rfl

-- Proof sketch: every row is supported on the two neighbors `x ± 1`, and those two masses add to
-- `1`.
/-- The RWRE transition matrix is stochastic. -/
theorem randomEnvironmentTransitionMatrix_isStochastic (W : RandomEnvironment) :
    IsStochasticMatrix (randomEnvironmentTransitionMatrix W) := by
  intro x
  classical
  have hsupport :
      ∀ y ∉ ({x + 1, x - 1} : Finset ℤ), randomEnvironmentTransitionMatrix W x y = 0 := by
    intro y hy
    have hy_right : y ≠ x + 1 := by
      intro h
      exact hy (by simp [h])
    have hy_left : y ≠ x - 1 := by
      intro h
      exact hy (by simp [h])
    simp [randomEnvironmentTransitionMatrix, hy_right, hy_left]
  rw [tsum_eq_sum hsupport]
  have hneq : x + 1 ≠ x - 1 := by omega
  have hneq' : x - 1 ≠ x + 1 := by omega
  have hprob : (W.rightJumpProb x : ℝ≥0∞) ≤ 1 := by
    exact_mod_cast W.rightJumpProb_le_one x
  simpa [randomEnvironmentTransitionMatrix, hneq, hneq'] using add_tsub_cancel_of_le hprob

/-- The discrete kernel associated to `randomEnvironmentTransitionMatrix W` is Markov. -/
instance (W : RandomEnvironment) :
    IsMarkovKernel (discreteMatrixKernel (randomEnvironmentTransitionMatrix W)) :=
  discreteMatrixKernel_isMarkovKernel _ (randomEnvironmentTransitionMatrix_isStochastic W)

/-- At the right neighbor `x + 1`, the RWRE transition matrix has mass `W.rightJumpProb x`. -/
theorem randomEnvironmentTransitionMatrix_right (W : RandomEnvironment) (x : ℤ) :
    randomEnvironmentTransitionMatrix W x (x + 1) = W.rightJumpProb x := by
  simp [randomEnvironmentTransitionMatrix]

/-- At the left neighbor `x - 1`, the RWRE transition matrix has mass `1 - W.rightJumpProb x`. -/
theorem randomEnvironmentTransitionMatrix_left (W : RandomEnvironment) (x : ℤ) :
    randomEnvironmentTransitionMatrix W x (x - 1) = (1 : ℝ≥0) - W.rightJumpProb x := by
  have hneq : x - 1 ≠ x + 1 := by omega
  simp [randomEnvironmentTransitionMatrix, hneq]

namespace RandomEnvironment

/-- A one-dimensional environment is elliptic if every right-jump probability lies strictly
between `0` and `1`. -/
class IsElliptic (W : RandomEnvironment) : Prop where
  pos_lt_one (x : ℤ) : 0 < W.rightJumpProb x ∧ W.rightJumpProb x < 1

/-- In an elliptic environment, every right-jump probability is positive. -/
theorem IsElliptic.pos {W : RandomEnvironment} (hW : W.IsElliptic) (x : ℤ) :
    0 < W.rightJumpProb x :=
  (hW.pos_lt_one x).1

/-- In an elliptic environment, every right-jump probability is strictly less than `1`. -/
theorem IsElliptic.lt_one {W : RandomEnvironment} (hW : W.IsElliptic) (x : ℤ) :
    W.rightJumpProb x < 1 :=
  (hW.pos_lt_one x).2

end RandomEnvironment

/- Layering for Definition 19.34:
- `source-facing`: the nearest-neighbor transition matrix `randomEnvironmentTransitionMatrix W` on
  `ℤ` in the fixed environment `W`.
- `core/canonical`: the Chapter 17 discrete-time owner
  `IsMarkovProcessRealization
    (fun n ↦ discreteMatrixKernel (randomEnvironmentTransitionMatrix W) ^ n) P X`.
- `bridge/view`: the canonical kernel bridge `discreteMatrixKernel
  (randomEnvironmentTransitionMatrix W)` and direct reuse of Theorem 17.11 for the one-step
  conditional-law criterion, together with the textbook initial-state and one-step joint-law
  consequences. -/

section

variable (W : RandomEnvironment) (P : ℤ → ProbabilityMeasure Ω) (X : ℕ → Ω → ℤ)

/-- A process `X` with laws `P` is a random walk in the random environment `W` when it is the
discrete-time Markov-process realization with one-step transition matrix
`randomEnvironmentTransitionMatrix W`, equivalently with one-step kernel
`discreteMatrixKernel (randomEnvironmentTransitionMatrix W)`. This is the notion from
Definition 19.34. -/
abbrev IsRandomWalkInRandomEnvironment
    (W : RandomEnvironment) (P : ℤ → ProbabilityMeasure Ω) (X : ℕ → Ω → ℤ) : Prop :=
  IsMarkovProcessRealization
    (fun n : ℕ ↦ discreteMatrixKernel (randomEnvironmentTransitionMatrix W) ^ n)
    P X

end

section

variable {W : RandomEnvironment} {P : ℤ → ProbabilityMeasure Ω} {X : ℕ → Ω → ℤ}

-- Proof sketch: evaluate the `initial_eq` owner field at the singleton `{x}`.
/-- Under the canonical Chapter 17 RWRE owner, the walk started from `x` is almost surely at `x`
at time `0`. -/
theorem randomWalkInRandomEnvironment_start
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (randomEnvironmentTransitionMatrix W) ^ n) P X]
    (x : ℤ) :
    (P x : Measure Ω) (X 0 ⁻¹' {x}) = 1 := by
  have hReal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel (randomEnvironmentTransitionMatrix W) ^ n) P X :=
    inferInstance
  -- Proof comment: rewrite the time-`0` singleton event through the pushed-forward law and use
  -- the realization axiom `(P x).map (X 0) = dirac x`.
  have hInit := congrArg (fun ν : Measure ℤ ↦ ν {x}) (hReal.initial_eq x)
  simpa [Measure.map_apply (hReal.measurable_process 0) (measurableSet_singleton x)] using hInit

/-- Helper for Definition 19.34: the discrete kernel associated to
`randomEnvironmentTransitionMatrix W` evaluates on a singleton `{z}` to the matrix entry at
`(y, z)`. -/
lemma rwreKernel_apply_singleton (W : RandomEnvironment) (y z : ℤ) :
    discreteMatrixKernel (randomEnvironmentTransitionMatrix W) y ({z} : Set ℤ) =
      randomEnvironmentTransitionMatrix W y z := by
  -- Proof comment: on the discrete state space `ℤ`, the singleton mass of the row measure is
  -- exactly the weight assigned to that state in the matrix.
  rw [discreteMatrixKernel_apply, Measure.sum_apply _ (measurableSet_singleton z)]
  rw [tsum_eq_single z]
  · simp
  · intro i hi
    simp [hi]

-- Proof sketch: combine the owner-level Markov property for the one-step kernel
-- `discreteMatrixKernel (randomEnvironmentTransitionMatrix W)` with the discrete singleton
-- evaluation formula `discreteMatrixKernel p y {z} = p y z`.
/-- Definition 19.34: under the canonical Chapter 17 RWRE owner, the one-step joint law of
`(X_n, X_{n+1})` is the textbook transition weight
`randomEnvironmentTransitionMatrix W y z` times the time-`n` marginal at `y`. -/
theorem randomWalkInRandomEnvironment_transition
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (randomEnvironmentTransitionMatrix W) ^ n) P X]
    (x : ℤ) (n : ℕ) (y z : ℤ) :
    (P x : Measure Ω) {ω | X n ω = y ∧ X (n + 1) ω = z} =
      randomEnvironmentTransitionMatrix W y z * (P x : Measure Ω) (X n ⁻¹' {y}) := by
  let μ : Measure Ω := (P x : Measure Ω)
  let A : Set Ω := X n ⁻¹' {y}
  let B : Set Ω := X (n + 1) ⁻¹' {z}
  have hReal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel (randomEnvironmentTransitionMatrix W) ^ n) P X :=
    inferInstance
  have hA_meas : MeasurableSet A := by
    simpa [A] using (hReal.measurable_process n) (measurableSet_singleton y)
  have hB_meas : MeasurableSet B := by
    simpa [B] using (hReal.measurable_process (n + 1)) (measurableSet_singleton z)
  have hFiltration_le : generatedFiltrationSpace X n ≤ ‹MeasurableSpace Ω› := by
    refine iSup₂_le fun m hm ↦ ?_
    exact (hReal.measurable_process m).comap_le
  have hA_measFiltration : MeasurableSet[generatedFiltrationSpace X n] A := by
    have hXn_measF : Measurable[generatedFiltrationSpace X n] (X n) := by
      refine Measurable.of_comap_le ?_
      exact le_iSup_of_le n <| le_iSup_of_le le_rfl le_rfl
    simpa [A] using hXn_measF (measurableSet_singleton y)
  have hEvent :
      {ω | X n ω = y ∧ X (n + 1) ω = z} = A ∩ B := by
    ext ω
    simp [A, B]
  have hMarkovGenerated :
      μ⟦B | generatedFiltrationSpace X n⟧ =ᵐ[μ]
        fun ω ↦
          ((discreteMatrixKernel (randomEnvironmentTransitionMatrix W) (X n ω)).real
            ({z} : Set ℤ)) :=
    by
      simpa [B, add_comm] using
        hReal.markov_property x (A := ({z} : Set ℤ)) (measurableSet_singleton z) n 1
  have hIndicatorIntegrable : Integrable (B.indicator (fun _ ↦ (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hB_meas
  have hInterReal :
      μ.real (A ∩ B) =
        (randomEnvironmentTransitionMatrix W y z).toReal * μ.real A := by
    -- Proof comment: integrate the one-step Markov conditional expectation over the fiber
    -- `{X n = y}`; on that fiber, the kernel row is constant with value
    -- `randomEnvironmentTransitionMatrix W y z`.
    calc
      μ.real (A ∩ B) = ∫ ω in A, (μ⟦B | generatedFiltrationSpace X n⟧) ω ∂ μ := by
        rw [setIntegral_condExp hFiltration_le hIndicatorIntegrable hA_measFiltration,
          ← integral_indicator hA_meas]
        symm
        simpa [B, Set.indicator_indicator, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm,
          smul_eq_mul] using integral_indicator_const (1 : ℝ) (hA_meas.inter hB_meas)
      _ =
          ∫ ω in A,
            ((discreteMatrixKernel (randomEnvironmentTransitionMatrix W) (X n ω)).real
              ({z} : Set ℤ)) ∂ μ := by
            exact integral_congr_ae hMarkovGenerated.restrict
      _ = ∫ _ in A, (randomEnvironmentTransitionMatrix W y z).toReal ∂ μ := by
            refine integral_congr_ae ?_
            filter_upwards [self_mem_ae_restrict (μ := μ) (s := A) hA_meas] with ω hω
            have hω : X n ω = y := by
              simpa [A] using hω
            rw [hω]
            simpa [MeasureTheory.measureReal_def] using
              congrArg ENNReal.toReal (rwreKernel_apply_singleton (W := W) y z)
      _ = (randomEnvironmentTransitionMatrix W y z).toReal * μ.real A := by
            rw [setIntegral_const, smul_eq_mul]
            rw [mul_comm]
  have hStep_ne_top : randomEnvironmentTransitionMatrix W y z ≠ ∞ := by
    by_cases hz1 : z = y + 1
    · simp [randomEnvironmentTransitionMatrix, hz1]
    · by_cases hz2 : z = y - 1
      · have hneq : y - 1 ≠ y + 1 := by omega
        simp [randomEnvironmentTransitionMatrix, hz2, hneq]
      · simp [randomEnvironmentTransitionMatrix, hz1, hz2]
  have hInter :
      μ (A ∩ B) = randomEnvironmentTransitionMatrix W y z * μ A := by
    refine
      (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ (A ∩ B))
        (ENNReal.mul_ne_top hStep_ne_top (measure_ne_top μ A))).mp ?_
    simpa [measureReal_def, ENNReal.toReal_mul, hStep_ne_top, A] using hInterReal
  -- Proof comment: rewrite the pair event as the intersection of the current-state and next-state
  -- fibers, then transport the real-valued set-integral identity back to ENNReal.
  simpa [μ, A, hEvent] using hInter

end

end ProbabilityTheory
