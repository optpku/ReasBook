/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Theorem_14_47

open MeasureTheory ProbabilityTheory

noncomputable section

namespace ProbabilityTheory

/-- Example 17.6: a convolution semigroup on `ℝ^d` yields, for every starting point `x`, a
continuous-time path law on `(ℝ^d)^[0,∞)` whose coordinate process starts at `x` and has the
stationary independent increment laws prescribed by the semigroup. This packages the Chapter 14
construction pointwise in the initial state. -/
theorem exists_pathMeasureFamily_of_isConvolutionSemigroup
    {d : ℕ} (ν : NNReal → ProbabilityMeasure (Fin d → ℝ))
    (hν : IsConvolutionSemigroupWithZero ν) :
    ∃ P : (Fin d → ℝ) → ProbabilityMeasure (NNReal → Fin d → ℝ),
      ∀ x : Fin d → ℝ,
        HasLaw
            (Function.eval 0)
            (Measure.dirac x)
            (P x : Measure (NNReal → Fin d → ℝ)) ∧
          HasStationaryIndependentIncrements
            (Function.eval : NNReal → (NNReal → Fin d → ℝ) → Fin d → ℝ)
            (P x : Measure (NNReal → Fin d → ℝ)) ∧
          ∀ ⦃s t : NNReal⦄, s ≤ t →
            HasLaw
              (fun ω : NNReal → Fin d → ℝ ↦ ω t - ω s)
              (ν (t - s) : Measure (Fin d → ℝ))
              (P x : Measure (NNReal → Fin d → ℝ)) := by
  classical
  -- Proof comment: choose, for each deterministic start `x`, the Chapter 14 path measure with
  -- the required starting law and increment identities, then repackage those pointwise choices
  -- into a single family `x ↦ P x`.
  refine ⟨fun x ↦ Classical.choose (exists_pathMeasure_of_isConvolutionSemigroup ν hν x), ?_⟩
  intro x
  -- Proof comment: the specification of the chosen path measure is exactly the desired triple of
  -- properties for the family member at `x`.
  exact Classical.choose_spec (exists_pathMeasure_of_isConvolutionSemigroup ν hν x)

end ProbabilityTheory
