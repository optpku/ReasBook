/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 9.15: The canonical mathlib notion of a stopping time with respect to a
filtration `ℱ` is `MeasureTheory.IsStoppingTime ℱ τ`, where `τ : Ω → WithTop ι` and `WithTop ι`
models the book's time set `I ∪ {∞}`. -/
recall MeasureTheory.IsStoppingTime
