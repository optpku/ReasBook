/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory.Measure

/- Remark 7.31: Mutual singularity of measures is symmetric. The textbook statement
`μ ⟂ₘ ν ↔ ν ⟂ₘ μ` is exactly the canonical mathlib equivalence `MutuallySingular.comm`
in the owner namespace `MeasureTheory.Measure`. -/
recall MutuallySingular.comm
