/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory MeasureTheory.Measure

/- Theorem 7.33 (1): For sigma-finite measures `μ` and `ν`, the canonical Lebesgue decomposition
of `ν` with respect to `μ` is
`ν = ν.singularPart μ + μ.withDensity (ν.rnDeriv μ)`. Thus the absolutely continuous part is
given by `μ.withDensity (ν.rnDeriv μ)` and the singular part by `ν.singularPart μ`. -/
recall singularPart_add_rnDeriv

/- Theorem 7.33 (2): The absolutely continuous part `μ.withDensity (ν.rnDeriv μ)` is absolutely
continuous with respect to `μ`. -/
recall withDensity_absolutelyContinuous

/- Theorem 7.33 (3): The canonical singular part `ν.singularPart μ` is mutually singular with
respect to `μ`. -/
recall mutuallySingular_singularPart

/- Theorem 7.33 (4): If `ν = s + μ.withDensity f` with `s ⟂ₘ μ`, then the singular component
must be `s = ν.singularPart μ`. This is the uniqueness of the singular part in Lebesgue's
decomposition theorem. -/
recall eq_singularPart

/- Theorem 7.33 (5): If `ν = s + μ.withDensity f` with `s ⟂ₘ μ`, then the density is unique up
to `μ`-almost everywhere equality: `f = ν.rnDeriv μ` almost everywhere. -/
recall eq_rnDeriv

/- Theorem 7.33 (6): The Radon-Nikodym derivative `ν.rnDeriv μ`, i.e. the density of the
absolutely continuous part, is measurable. -/
recall measurable_rnDeriv

/- Theorem 7.33 (7): If `ν` is sigma-finite, then the Radon-Nikodym derivative `ν.rnDeriv μ` is
finite `μ`-almost everywhere. -/
recall rnDeriv_lt_top
