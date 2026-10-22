/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

variable {I : Type u} {Ω : Type v} {S : Type w}

/- Remark 9.3: writing a stochastic process as `X = (X_t)_{t ∈ I}` only emphasizes its time
evolution; formally, it is the same time-indexed family already used as the owner object for a
process. -/
#check (I → Ω → S)
