/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

/- Theorem 15.8: a finite measure on `ℝ^d` is characterized by its characteristic function.
This is the owner-level uniqueness theorem for the canonical map `charFun`: mathlib's
`Measure.ext_of_charFun`, valid on complete second-countable real inner product spaces and hence in
particular on `EuclideanSpace ℝ (Fin d)`. -/
recall Measure.ext_of_charFun
