/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.Probability.Martingale.OptionalSampling
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_58
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_66
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Exercise_21_10_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Exercise_21_4_3
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Corollary_21_63
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Remark_21_67
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Remark_21_68
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_75

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

noncomputable section

universe u

namespace ProbabilityTheory

/-- Helper for Theorem 21.70: for a continuous path with a chosen square-variation witness along
an admissible partition sequence, the unit-weight quadratic partition sums converge to that
witness. -/
theorem theorem_21_70_pathwise_partition_limit
    (X : C(NNReal, ℝ)) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    {V : NNReal → ℝ} (hX : HasSquareVariationAlongPartition X P V) (T : NNReal) :
    Tendsto
      (fun n : ℕ ↦ weightedPartitionQuadraticVariationApproximationUpTo (fun _ ↦ (1 : ℝ)) X P T n)
      atTop
      (nhds (V T)) := by
  -- Proof comment: this is exactly the unit-weight specialization of the quadratic-variation
  -- convergence theorem already proved in Exercise 21.10.2.
  exact tendsto_weightedPartitionQuadraticVariationApproximationUpTo_one X P hX T

/-- Theorem 21.70: every continuous local martingale has a unique continuous square-variation process. -/
theorem existsUnique_continuousSquareVariationProcess
    {Ω : Type u} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration NNReal mΩ}
    {M : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M) :
    ∃! A : NNReal → Ω → ℝ, IsContinuousSquareVariationProcess ℱ μ M A := by
  sorry

end ProbabilityTheory
