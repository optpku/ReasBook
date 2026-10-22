/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

-- Proof sketch: for `n > 0`, the first coordinate gives an injection `ℝ ↪ EuclideanSpace ℝ (Fin n)`,
-- so `EuclideanSpace ℝ (Fin n)` is uncountable; then apply the general classification theorem
-- `PolishSpace.measurableEquivOfNotCountable`.
private theorem euclideanSpace_not_countable {n : ℕ} (hn : 0 < n) :
    ¬ Countable (EuclideanSpace ℝ (Fin n)) := by
  let i0 : Fin n := ⟨0, hn⟩
  have hsingle : Function.Injective (EuclideanSpace.single i0 : ℝ → EuclideanSpace ℝ (Fin n)) := by
    intro x y hxy
    simpa using congrArg (fun v ↦ v i0) hxy
  exact hsingle.uncountable.not_countable

/-- Exercise 8.3.8 (1): for every positive dimension `n`, the measurable spaces `ℝ` and
`EuclideanSpace ℝ (Fin n)`, both equipped with their Borel sigma-algebras, are isomorphic. -/
noncomputable def euclideanSpace_measurableEquiv_real {n : ℕ} (hn : 0 < n) :
    EuclideanSpace ℝ (Fin n) ≃ᵐ ℝ :=
  PolishSpace.measurableEquivOfNotCountable (euclideanSpace_not_countable hn) not_countable

-- Proof sketch: `EuclideanSpace ℝ (Fin n)` is a standard Borel space, and every measurable
-- subset of a standard Borel space is again standard Borel by `MeasurableSet.standardBorel`.
/- Exercise 8.3.8 (2): every Borel subset of `EuclideanSpace ℝ (Fin n)` is a Borel space in the
textbook sense, via the owner theorem `MeasurableSet.standardBorel` for measurable subsets of
standard Borel spaces. -/
recall MeasurableSet.standardBorel
