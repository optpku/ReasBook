/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/-- Definition 1.57: The Lebesgue--Stieltjes measure with distribution function `F` is the
canonical mathlib measure `StieltjesFunction.measure` associated to a Stieltjes function
`F : StieltjesFunction ℝ`, i.e. a monotone right-continuous real function on the Borel space
`ℝ`. -/
recall StieltjesFunction.measure

/-- The associated Stieltjes measure assigns the half-open interval `(a, b]` the mass `F b - F a`,
encoded in Lean as `ENNReal.ofReal (F b - F a)`. -/
recall StieltjesFunction.measure_Ioc
