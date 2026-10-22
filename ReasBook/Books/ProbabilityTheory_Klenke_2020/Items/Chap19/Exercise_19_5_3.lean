/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap19.Exercise_19_5_3Support

open MeasureTheory
open scoped ENNReal

noncomputable section

universe u

namespace ProbabilityTheory

/-- Exercise 19.5.3 (i): for the graph of Fig. 19.15, the effective conductance between `a` and
`z` is `√3`. This local main alias keeps the label attached to the theorem name tail expected by
the proof pipeline. -/
theorem Exercise1953.simpleLadder_effectiveConductance_between_a_z_eq_sqrt_three :
    dirichletEffectiveConductance (simpleGraphWeights fig19_15SimpleLadderGraph)
      ({fig19_15SimpleLadderA} : Set fig19_15SimpleLadderVertex)
      ({fig19_15SimpleLadderZ} : Set fig19_15SimpleLadderVertex) = Real.sqrt 3 :=
  ProbabilityTheory.simpleLadder_effectiveConductance_between_a_z_eq_sqrt_three

/-- Wrapper for Exercise 19.5.3 (i): re-export the effective conductance statement under the
chapter-level exercise name. -/
theorem exercise_19_5_3_effectiveConductance_between_a_z_eq_sqrt_three :
    dirichletEffectiveConductance (simpleGraphWeights fig19_15SimpleLadderGraph)
      ({fig19_15SimpleLadderA} : Set fig19_15SimpleLadderVertex)
      ({fig19_15SimpleLadderZ} : Set fig19_15SimpleLadderVertex) = Real.sqrt 3 :=
  Exercise1953.simpleLadder_effectiveConductance_between_a_z_eq_sqrt_three

/-- Wrapper for Exercise 19.5.3 (ii): re-export the hitting-probability statement under the
chapter-level exercise name. -/
theorem exercise_19_5_3_hit_z_before_return_to_a_eq_inv_sqrt_three
    {Ω : Type u} [MeasurableSpace Ω]
    {p : fig19_15SimpleLadderVertex → fig19_15SimpleLadderVertex → ℝ≥0∞}
    {P : fig19_15SimpleLadderVertex → ProbabilityMeasure Ω}
    {X : ℕ → Ω → fig19_15SimpleLadderVertex}
    [IsSimpleRandomWalk p fig19_15SimpleLadderGraph]
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X] :
    escapeToSetProbability P X fig19_15SimpleLadderA
      ({fig19_15SimpleLadderZ} : Set fig19_15SimpleLadderVertex) =
      ENNReal.ofReal (1 / Real.sqrt 3) :=
  simpleLadder_hit_z_before_return_to_a_eq_inv_sqrt_three

end ProbabilityTheory
