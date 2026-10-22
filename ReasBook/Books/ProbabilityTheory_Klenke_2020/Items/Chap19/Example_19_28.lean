/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_41

open MeasureTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

/-
`source-facing`: Example 19.28 asserts recurrence of the symmetric simple random walk on `ℤ²`.
`core/canonical`: the owner abstraction is the Markov realization driven by
`dirac_convolution_kernel (symmetricSimpleRandomWalkStepPMF 2).toMeasure`.
`bridge/view`: the translation-invariant matrix presentation belongs only to companion bridge
results from Chapter 17 and is not the main public layer here.
-/

-- Proof sketch: specialize the owner-level recurrence criterion for the canonical symmetric
-- simple random walk on `ℤ^d` to `d = 2`.
/-- Example 19.28: the symmetric simple random walk on `ℤ²`, with its canonical step law
`symmetricSimpleRandomWalkStepPMF 2`, is recurrent. -/
theorem symmetricSimpleRandomWalk_Z2_isRecurrent
    (P : LatticePoint 2 → ProbabilityMeasure Ω) (X : ℕ → Ω → LatticePoint 2)
    [IsMarkovProcessRealization
      (fun n ↦ dirac_convolution_kernel (symmetricSimpleRandomWalkStepPMF 2).toMeasure ^ n) P X] :
    IsRecurrentMarkovChain P X := by
  exact (symmetricSimpleRandomWalk_isRecurrent_iff_dimension_le_two P X).2 (by norm_num)

end ProbabilityTheory
