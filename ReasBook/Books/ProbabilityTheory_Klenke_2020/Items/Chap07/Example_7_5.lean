/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open MeasureTheory Set
open unitInterval
open scoped NNReal unitInterval

/- Example 7.5 (1): A subset of `ℝ` is convex exactly when it is an interval, expressed in Lean
as order-connectedness. This is the canonical mathlib theorem
`convex_iff_ordConnected`; specializing it to `ℝ` gives the textbook statement. -/
recall convex_iff_ordConnected

/- Example 7.5 (2): Every linear subspace of a vector space is a convex subset of the ambient
space. This is exactly the canonical mathlib theorem `Submodule.convex`. -/
recall Submodule.convex

-- Proof sketch: if `μ` and `ν` both have total mass `1`, then any convex combination
-- `a • μ + b • ν` with `a + b = 1` again has total mass `1`.
/-- Example 7.5 (3): On a measurable space, the set of all probability measures is convex inside
the space of measures. -/
theorem probability_measures_convex {Ω : Type u} [MeasurableSpace Ω] :
    Convex ℝ≥0 {μ : Measure Ω | IsProbabilityMeasure μ} := by
  rw [convex_iff_add_mem]
  intro μ hμ ν hν a b ha hb hab
  letI : IsProbabilityMeasure μ := hμ
  letI : IsProbabilityMeasure ν := hν
  let p : I := ⟨a, ⟨ha, by
    have h : a ≤ a + b := le_add_of_nonneg_right hb
    simpa [hab] using h⟩⟩
  have hp : toNNReal p = a := rfl
  have hσp : toNNReal (σ p) = b := by
    apply NNReal.eq
    have hs : (a : ℝ) + (toNNReal (σ p) : ℝ) = 1 := by
      simpa [hp] using congrArg (fun x : ℝ≥0 ↦ (x : ℝ)) (toNNReal_add_toNNReal_symm p)
    have hab' : (a : ℝ) + (b : ℝ) = 1 := by
      exact_mod_cast hab
    linarith
  simpa [hp, hσp] using
    (inferInstance : IsProbabilityMeasure (toNNReal p • μ + toNNReal (σ p) • ν))
