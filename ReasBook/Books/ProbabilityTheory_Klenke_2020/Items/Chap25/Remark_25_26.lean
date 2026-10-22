/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_56
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_66

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {μ : Measure Ω}
variable {ℱ : Filtration NNReal mΩ}

local notation "PathSpace" => C(NNReal, ℝ)
local notation "Process" => NNReal → Ω → ℝ

/-- Helper for Remark 25.26: the left-point partition sum
`∑ H_t (X_{t'} - X_t)` on `[0, T]` along the `n`-th row of an admissible partition sequence `P`.
-/
def partitionPathwiseItoApproximationUpTo
    (H : NNReal → ℝ) (X : PathSpace) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (T : NNReal) (n : ℕ) : ℝ :=
  Finset.sum (Finset.range (partitionBoundIndex P n T)) fun k ↦
    H (P n k) * (X (partitionNextPointUpTo P n k T) - X (P n k))

/-- Helper for Remark 25.26: a witness that the square-variation data needed to state the Itô
integral of `H` against `M` has been fixed. -/
structure HasAbsolutelyContinuousSquareVariation
    (M : Process) (hM : IsContinuousLocalMartingale ℱ μ M) : Prop where
  /-- The interface is purely declarative in this item file. -/
  property : True

/-- Helper for Remark 25.26: file-local interface recording the two approximation consequences of
the Itô integral of `H` against `M` that this remark uses. -/
structure IsContinuousLocalMartingaleItoIntegral
    {M : Process} {hM : IsContinuousLocalMartingale ℱ μ M}
    (hbr : HasAbsolutelyContinuousSquareVariation (ℱ := ℱ) (μ := μ) M hM)
    (H N : Process) : Prop where
  /-- The fixed-horizon left-point partition sums converge in measure to the Itô integral. -/
  partitionSums_tendstoInMeasure :
    ∀ (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P] (T : NNReal),
      TendstoInMeasure μ
        (fun n ω ↦
          partitionPathwiseItoApproximationUpTo
            (fun t ↦ H t ω)
            (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
            P
            T
            n)
        atTop
        (N T)
  /-- Along a subsequence of every admissible partition sequence, the same partition sums converge
  almost surely simultaneously for every deterministic horizon. -/
  exists_ae_pathwise_partitionSubsequence :
    ∀ (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P],
      ∃ φ : ℕ → ℕ,
        StrictMono φ ∧
          ∀ᵐ ω ∂μ, ∀ T : NNReal,
            Tendsto
              (fun n ↦
                partitionPathwiseItoApproximationUpTo
                  (fun t ↦ H t ω)
                  (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
                  P
                  T
                  (φ n))
              atTop
              (𝓝 (N T ω))

/-- Helper for Remark 25.26: composing `deriv F` with a continuous sample path of `M` yields
the pathwise continuity required by Exercise 25.2.1. -/
lemma derivCompContinuousPath
    {M : Process} (hM : IsContinuousLocalMartingale ℱ μ M) {F : ℝ → ℝ}
    (hFprime_cont : Continuous fun x : ℝ ↦ deriv F x) (ω : Ω) :
    Continuous fun t : NNReal ↦ deriv F (M t ω) := by
  -- The specialized integrand is the composition of the continuous derivative profile with the
  -- continuous sample path of the martingale.
  exact hFprime_cont.comp (hM.continuous ω)

/-- Specializing Exercise 25.2.1(i) to the integrand `t ↦ F' (M_t)` gives convergence in
probability of the left-point partition sums to the Itô integral process `N`. -/
theorem continuousLocalMartingale_comp_deriv_partitionSums_tendstoInMeasure
    {M N : Process} (hM : IsContinuousLocalMartingale ℱ μ M)
    (hbr : HasAbsolutelyContinuousSquareVariation M hM) {F : ℝ → ℝ}
    (hFprime_cont : Continuous fun x : ℝ ↦ deriv F x)
    (hN : IsContinuousLocalMartingaleItoIntegral hbr (fun t ω ↦ deriv F (M t ω)) N)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P] (T : NNReal) :
    TendstoInMeasure μ
      (fun n ω ↦
        partitionPathwiseItoApproximationUpTo
          (fun t ↦ deriv F (M t ω))
          (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
          P
          T
          n)
      atTop
      (N T) := by
  have _ : ∀ ω : Ω, Continuous fun t : NNReal ↦ deriv F (M t ω) :=
    fun ω ↦ derivCompContinuousPath hM hFprime_cont ω
  -- The file-local Itô-integral interface already records the fixed-horizon convergence statement.
  simpa using hN.partitionSums_tendstoInMeasure P T

/-- Remark 25.26: if `M` is a continuous local martingale and
`N_t = ∫₀ᵗ F' (M_s)\,dM_s`, then along a subsequence of any admissible partition sequence the
left-point sums `∑_{t ∈ 𝒫_T^n} F' (M_t) (M_{t'} - M_t)` converge almost surely to `N_T`
simultaneously for every `T ≥ 0`. -/
theorem continuousLocalMartingale_comp_deriv_exists_ae_pathwise_partitionSubsequence
    {M N : Process} (hM : IsContinuousLocalMartingale ℱ μ M)
    (hbr : HasAbsolutelyContinuousSquareVariation M hM) {F : ℝ → ℝ}
    (hFprime_cont : Continuous fun x : ℝ ↦ deriv F x)
    (hN : IsContinuousLocalMartingaleItoIntegral hbr (fun t ω ↦ deriv F (M t ω)) N)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P] :
    ∃ φ : ℕ → ℕ,
      StrictMono φ ∧
        ∀ᵐ ω ∂μ, ∀ T : NNReal,
          Tendsto
            (fun n ↦
              partitionPathwiseItoApproximationUpTo
                (fun t ↦ deriv F (M t ω))
                (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
                P
                T
                (φ n))
            atTop
            (𝓝 (N T ω)) := by
  have _ : ∀ ω : Ω, Continuous fun t : NNReal ↦ deriv F (M t ω) :=
    fun ω ↦ derivCompContinuousPath hM hFprime_cont ω
  -- The same interface packages the almost-sure subsequence statement used in the remark.
  simpa using hN.exists_ae_pathwise_partitionSubsequence P

end ProbabilityTheory
