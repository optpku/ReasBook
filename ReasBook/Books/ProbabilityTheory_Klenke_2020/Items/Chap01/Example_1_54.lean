/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Set
open scoped ENNReal BigOperators

-- Proof sketch: apply the countable subadditivity of the canonical volume measure on `Fin n → ℝ`
-- to the countable cover by half-open rectangles; Example 1.39 identifies this measure with the
-- textbook rectangle volume.
/-- Example 1.54: If a half-open rectangle in `ℝ^n` is covered by countably many half-open
rectangles, then the canonical volume of the first rectangle is bounded above by the sum of the
volumes of the covering rectangles. This is the `σ`-subadditivity check used for extending the
rectangle volume to Borel sets. -/
theorem volume_pi_Ioc_le_tsum_of_subset_iUnion
    {n : ℕ} {a b : Fin n → ℝ} (coverA coverB : ℕ → Fin n → ℝ)
    (hcover :
      univ.pi (fun i ↦ Ioc (a i) (b i)) ⊆
        ⋃ k, univ.pi (fun i ↦ Ioc (coverA k i) (coverB k i))) :
    volume (univ.pi (fun i ↦ Ioc (a i) (b i))) ≤
      ∑' k, volume (univ.pi (fun i ↦ Ioc (coverA k i) (coverB k i))) := by
  calc
    volume (univ.pi (fun i ↦ Ioc (a i) (b i))) ≤ volume (⋃ k, univ.pi (fun i ↦ Ioc (coverA k i) (coverB k i))) :=
      measure_mono hcover
    _ ≤ ∑' k, volume (univ.pi (fun i ↦ Ioc (coverA k i) (coverB k i))) :=
      measure_iUnion_le _
