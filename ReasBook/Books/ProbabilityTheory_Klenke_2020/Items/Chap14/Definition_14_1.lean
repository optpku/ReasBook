/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {I : Type u}
variable (Ω : I → Type v)

/- Definition 14.1: the product of a family of sets `(Ω i)_{i ∈ I}` is canonically the dependent
function type `((i : I) → Ω i)`. This core Lean type is the owner abstraction for the textbook
product space, so no parallel local wrapper is needed. -/
#check ((i : I) → Ω i)

variable (Ω₀ : Type v)

/- In the homogeneous case `Ω i = Ω₀` for all `i`, the product specializes to the ordinary
function space `I → Ω₀`. -/
#check (I → Ω₀)
