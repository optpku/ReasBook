/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Definition_14_39
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Definition_14_40

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u v

section

variable {I : Type u} {E : Type v}
variable [AddCommSemigroup I] [PartialOrder I] [ExistsAddOfLE I] [AddLeftMono I]
variable [Sub I] [OrderedSub I]
variable [MeasurableSpace E]

/-- Lemma 14.41: if a family of stochastic kernels satisfies the Chapman--Kolmogorov semigroup
law, then the time-difference family `(s, t) ↦ κ (t - s)` is a consistent kernel family in the
sense of Definition 14.39. -/
theorem time_difference_kernels_consistent_of_chapman_kolmogorov
    (κ : I → Kernel E E)
    (hChapmanKolmogorov : ∀ s t : I, (κ t) ∘ₖ (κ s) = κ (s + t)) :
    IsConsistentKernelFamily (fun {s t} _ ↦ κ (t - s)) := by
  intro r s t hrs hst
  -- Specialize Chapman--Kolmogorov to the two time gaps appearing in the consistency goal.
  calc
    κ (t - s) ∘ₖ κ (s - r) = κ ((s - r) + (t - s)) := hChapmanKolmogorov (s - r) (t - s)
    -- Commute the two gap lengths so the standard subtraction identity applies.
    _ = κ ((t - s) + (s - r)) := by rw [add_comm]
    -- Collapse the adjacent differences to the direct time difference `t - r`.
    _ = κ (t - r) := by rw [tsub_add_tsub_cancel hst.le hrs.le]

end

section

variable {I : Type u} {E : Type v}
variable [AddCommMonoid I] [PartialOrder I] [ExistsAddOfLE I] [AddLeftMono I]
variable [Sub I] [OrderedSub I]
variable [MeasurableSpace E]
variable {κ : I → Kernel E E}

-- Proof sketch: apply Lemma 14.41 to the owner abstraction `IsMarkovSemigroup` and use its
-- Chapman--Kolmogorov field.
/-- A Markov semigroup induces a consistent family of time-difference kernels. -/
theorem IsMarkovSemigroup.time_difference_kernels_consistent
    (hκ : IsMarkovSemigroup κ) :
    IsConsistentKernelFamily (fun {s t} _ ↦ κ (t - s)) :=
  time_difference_kernels_consistent_of_chapman_kolmogorov κ hκ.comp_eq

end
