/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Exercise 7.2.2: Minkowski's inequality for real-valued `ℒ^p(μ)` functions is the canonical
theorem `MeasureTheory.lpNorm_add_le`. The textbook proof route derives this estimate by applying
Jensen's inequality to the concave map `(x, y) ↦ (x^(1/p) + y^(1/p))^p` from Example 7.14. -/
recall MeasureTheory.lpNorm_add_le
