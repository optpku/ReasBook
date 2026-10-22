/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Set
open scoped ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The set of `τ`-invariant probability measures on the measurable space `Ω`. -/
def tauInvariantProbabilityMeasures (τ : Ω → Ω) : Set (Measure Ω) :=
  {μ | MeasurePreserving τ μ μ ∧ IsProbabilityMeasure μ}

-- Proof sketch: invariance under `τ` is preserved by nonnegative linear combinations because
-- pushforward is affine on measures, and the total mass of a convex combination of probability
-- measures is still `1`.
/-- Exercise 20.3.1 (1): the set of `τ`-invariant probability measures is convex. -/
theorem tauInvariantProbabilityMeasures_convex (τ : Ω → Ω) :
    Convex ℝ≥0∞ (tauInvariantProbabilityMeasures τ) := by
  intro μ hμ ν hν a b ha hb hab
  rcases hμ with ⟨hμτ, hμprob⟩
  rcases hν with ⟨hντ, hνprob⟩
  refine ⟨?_, ?_⟩
  · simpa using (hμτ.smul_measure a).add_measure (hντ.smul_measure b)
  · exact ⟨by simp [Measure.add_apply, hab, hμprob.measure_univ, hνprob.measure_univ]⟩

/- Exercise 20.3.1 (2): for probability measures, ergodicity is exactly the canonical mathlib
criterion `Ergodic.iff_mem_extremePoints`, identifying ergodic measures with the extreme points of
the set of invariant probability measures. -/
recall Ergodic.iff_mem_extremePoints
