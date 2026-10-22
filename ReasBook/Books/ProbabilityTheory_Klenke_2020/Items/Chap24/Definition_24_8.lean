/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap24.Definition_24_6

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

universe u v

namespace RandomMeasure

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- Definition 24.8: a random measure on `E` under the probability law `P` has independent
increments if, for every finite family of pairwise disjoint measurable sets, the random variables
obtained by evaluating the measure on those sets are independent. -/
def HasIndependentIncrements (X : Kernel Ω E) (P : ProbabilityMeasure Ω) : Prop :=
  ∀ n, ∀ A : Fin n → Set E,
    (∀ i, MeasurableSet (A i)) →
    (Set.univ : Set (Fin n)).PairwiseDisjoint A →
    iIndepFun (fun i ω ↦ X ω (A i)) (P : Measure Ω)

/-- The owner-level independent-increments property yields the textbook `Fin n` finite-family
criterion. -/
theorem HasIndependentIncrements.iIndepFun_eval_fin
    {X : Kernel Ω E} {P : ProbabilityMeasure Ω}
    (hX : HasIndependentIncrements X P) (A : Fin n → Set E)
    (hA : ∀ i, MeasurableSet (A i))
    (hdisj : Pairwise (fun i j ↦ Disjoint (A i) (A j))) :
    iIndepFun (fun i ω ↦ X ω (A i)) (P : Measure Ω) := by
  have hpairwiseDisjoint : (Set.univ : Set (Fin n)).PairwiseDisjoint A := by
    simpa [Set.PairwiseDisjoint, Set.pairwise_univ, Function.onFun] using hdisj
  exact hX n A hA hpairwiseDisjoint

end RandomMeasure
