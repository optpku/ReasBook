/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]

/- Definition 7.47: For a real Banach space `V`, the dual space is formalized by the canonical
type `StrongDual ℝ V`, i.e. the space of continuous linear functionals `V →L[ℝ] ℝ` equipped with
its operator norm. Mathlib defines this canonically for every real normed space, hence in
particular for Banach spaces. -/
recall StrongDual

/-- The norm on the real dual space is the supremum of `|F v|` over all unit vectors. -/
theorem strongDual_norm_eq_sSup_abs_apply_unitSphere (F : StrongDual ℝ V) :
    ‖F‖ = sSup ((fun v : V ↦ |F v|) '' Metric.sphere (0 : V) 1) := by
  simpa [Real.norm_eq_abs] using F.sSup_sphere_eq_norm.symm
