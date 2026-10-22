/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Mathlib.Dynamics.Ergodic.Ergodic

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

universe u

variable {E : Type u} [MeasurableSpace E]

/- Definition 20.11: for the canonical process on the path space `ℕ → E`, ergodicity is exactly
the canonical mathlib notion `Ergodic` for the one-sided shift `Stream'.tail` acting on the
path-space law. No separate process-specific wrapper is needed. -/
#check (fun P : Measure (ℕ → E) ↦ Ergodic Stream'.tail P)
