/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

-- Proof sketch: the hypothesis identifies `f'` with the canonical derivative `deriv f` via
-- `deriv_eq hderiv`. Then apply the existing mathlib theorem `measurable_deriv f`.
/-- Exercise 1.4.3: If `f : ℝ → ℝ` has pointwise derivative `f'`, then `f'` is Borel measurable,
i.e. measurable from `B(ℝ)` to `B(ℝ)`. -/
theorem measurable_of_hasDerivAt_real {f f' : ℝ → ℝ}
    (hderiv : ∀ x : ℝ, HasDerivAt f (f' x) x) :
    Measurable f' := by
  simpa [deriv_eq hderiv] using measurable_deriv f
