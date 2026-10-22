/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_23
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_8
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E]

/-- A Markov semigroup `κ` has generator matrix `q` when each singleton transition probability has
the prescribed right derivative at time `0`. This is the source-facing generator notion used in
the Chapter 17 Q-matrix items. -/
def HasGeneratorMatrix (κ : NNReal → Kernel E E) (q : E → E → ℝ) : Prop :=
  ∀ x y : E,
    Filter.Tendsto
      (fun t : NNReal ↦
        ((((κ t) x).real ({y} : Set E)) - (((κ 0) x).real ({y} : Set E))) / (t : ℝ))
      (nhdsWithin (0 : NNReal) (Set.Ioi 0)) (nhds (q x y))

section TopRestriction

variable (κ : NNReal → Kernel E E)

/-- Restrict a continuous-time kernel family on `NNReal` to the top additive submonoid. This is
the time-set expected by Theorem 17.8. -/
def topRestrictedKernel : (⊤ : AddSubmonoid NNReal) → Kernel E E :=
  fun t ↦ κ t.1

variable [hκ : IsMarkovSemigroup κ]

/-- The restriction of a Markov semigroup on `NNReal` to the top additive submonoid is again a
Markov semigroup. -/
instance instIsMarkovSemigroupTopRestrictedKernel :
    IsMarkovSemigroup (topRestrictedKernel κ) where
  isMarkovKernel t := hκ.isMarkovKernel t.1
  zero_eq := by
    ext x A hA
    simpa [topRestrictedKernel] using congrArg (fun η : Kernel E E ↦ η x A) hκ.zero_eq
  comp_eq s t := by
    ext x A hA
    simpa [topRestrictedKernel] using congrArg (fun η : Kernel E E ↦ η x A) (hκ.comp_eq s.1 t.1)

end TopRestriction

section

variable [StandardBorelSpace E]

/-- Theorem 17.25: once a bounded Q-matrix `q` is realized by a Markov semigroup `κ`, Theorem
17.8 supplies a Markov-process realization of that semigroup. The bounded-Q-matrix data are kept
explicit here to preserve the source-facing interface of the chapter's generator language. -/
theorem existsUnique_markovSemigroup_of_bounded_qMatrix
    (q : E → E → ℝ) (hq : IsQMatrix q)
    (hbounded : ∃ lam : NNReal, ∀ x : E, |q x x| ≤ (lam : ℝ))
    (κ : NNReal → Kernel E E) [IsMarkovSemigroup κ]
    (hκq : HasGeneratorMatrix κ q) :
    ∃ (Ω : Type v), ∃ _ : MeasurableSpace Ω,
      ∃ X : (⊤ : AddSubmonoid NNReal) → Ω → E,
        ∃ P : E → ProbabilityMeasure Ω,
          IsMarkovProcessRealization (topRestrictedKernel κ) P X := by
  let _ := hq
  let _ := hbounded
  let _ := hκq
  let κTop : (⊤ : AddSubmonoid NNReal) → Kernel E E := topRestrictedKernel κ
  have hκTop : IsMarkovSemigroup κTop := inferInstance
  obtain ⟨Ω, mΩ, X, P, hX⟩ :=
    exists_markovProcessRealization_of_markovSemigroup (κ := κTop)
  exact ⟨Ω, mΩ, X, P, hX⟩

/-- A bounded-Q-matrix realization theorem obtained from Theorem 17.25. -/
theorem exists_markovProcessRealization_of_bounded_qMatrix
    (q : E → E → ℝ) (hq : IsQMatrix q)
    (hbounded : ∃ lam : NNReal, ∀ x : E, |q x x| ≤ (lam : ℝ))
    (κ : NNReal → Kernel E E) [IsMarkovSemigroup κ]
    (hκq : HasGeneratorMatrix κ q) :
    ∃ (Ω : Type v), ∃ _ : MeasurableSpace Ω,
      ∃ X : (⊤ : AddSubmonoid NNReal) → Ω → E,
        ∃ P : E → ProbabilityMeasure Ω,
          IsMarkovProcessRealization (topRestrictedKernel κ) P X := by
  simpa using
    existsUnique_markovSemigroup_of_bounded_qMatrix
      (q := q) (hq := hq) (hbounded := hbounded) (κ := κ) (hκq := hκq)

end

end ProbabilityTheory
