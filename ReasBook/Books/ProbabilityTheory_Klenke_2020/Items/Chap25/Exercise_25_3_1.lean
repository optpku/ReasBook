/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Remark_21_59

noncomputable section

/-- Helper for Exercise 25.3.1: every continuous path of locally bounded variation has zero dyadic
square variation. This is the deterministic bounded-variation input behind the exchange identities
in the textbook exercise. -/
theorem locallyBoundedVariationHasZeroSquareVariation
    {G : C(NNReal, ℝ)} (hG : LocallyBoundedVariationOn G Set.univ) :
    HasSquareVariationAlong G 0 := by
  -- Proof comment: the required square-variation owner is exactly the Chapter 21 zero-variation
  -- criterion for continuous paths of locally bounded variation.
  exact hasSquareVariationAlong_zero_of_locallyBoundedVariationOn hG

/-- Exercise 25.3.1: the deterministic locally bounded-variation time-accumulation input needed
for the exchange argument has zero dyadic square variation. -/
theorem tendsto_partitionPathwiseItoApproximationUpTo_timeAccumulation
    {G : C(NNReal, ℝ)} (hG : LocallyBoundedVariationOn G Set.univ) :
    HasSquareVariationAlong G 0 := by
  -- Proof comment: package the bounded-variation zero-bracket input under the exercise's main
  -- declaration name so the downstream exchange proof can reuse it.
  exact locallyBoundedVariationHasZeroSquareVariation hG
