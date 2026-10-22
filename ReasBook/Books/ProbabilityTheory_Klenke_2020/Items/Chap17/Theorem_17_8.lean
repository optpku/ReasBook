/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.MarkovProcessRealization
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Remark_17_4

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

universe u v w

namespace ProbabilityTheory

section

variable {E : Type u} [MeasurableSpace E] [StandardBorelSpace E]
variable {I : AddSubmonoid NNReal}
variable (κ : I → Kernel E E) [IsMarkovSemigroup κ]

/-- Theorem 17.8: under the ordered-difference hypothesis
`∀ ⦃s t : I⦄, s ≤ t → t.1 - s.1 ∈ I`, a Markov semigroup on the additive time set `I`
admits a path-space kernel whose time-`t` marginals are exactly the rows of `κ t`. -/
theorem exists_pathKernel_with_transitionKernel_of_markovSemigroup
    (hsub : ∀ ⦃s t : I⦄, s ≤ t → t.1 - s.1 ∈ I) :
    ∃ κpath : Kernel E (I → E),
      IsMarkovKernel κpath ∧
        ∀ t : I, transitionKernel κpath t = κ t := by
  simpa using
    (exists_pathKernel_with_transitionKernel_of_timeHomogeneousTransitionKernels
      (I := I) (κt := κ) (hsub := hsub))

omit [StandardBorelSpace E] [IsMarkovSemigroup κ] in
/-- Consequence for Theorem 17.8: every Markov-process realization already carries its transition
family as a Markov semigroup. -/
theorem isMarkovSemigroup_of_markovProcessRealization
    {Ω : Type v} [MeasurableSpace Ω]
    {P : E → ProbabilityMeasure Ω} {X : I → Ω → E}
    (hX : IsMarkovProcessRealization κ P X) :
    IsMarkovSemigroup κ :=
  hX.semigroup

end

end ProbabilityTheory
