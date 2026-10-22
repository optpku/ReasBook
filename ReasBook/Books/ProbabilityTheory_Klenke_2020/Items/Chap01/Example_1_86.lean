/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

-- Proof sketch: `A` carries the subspace topology from `Fin n → ℝ`, so `borel A` is the Borel
-- measurable space of the induced topology. Then `borel_comap` identifies this with the comap of
-- the ambient Borel measurable space along the subtype inclusion.
/-- Example 1.86: For any subset `A` of `ℝⁿ`, modeled as `Fin n → ℝ`, the Borel `σ`-algebra on
`A` coming from the Euclidean subspace topology agrees with the restriction of the ambient Borel
`σ`-algebra to `A`. -/
theorem borel_subtype_eq_borel_comap_subtype_val (n : ℕ) (A : Set (Fin n → ℝ)) :
    borel A = (borel (Fin n → ℝ)).comap (Subtype.val : A → Fin n → ℝ) :=
  borel_comap
