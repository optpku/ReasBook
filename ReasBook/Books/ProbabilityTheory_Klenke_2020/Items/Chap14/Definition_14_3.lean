/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {I : Type u} {Ω : I → Type v}

/- Definition 14.3: the `i`th coordinate map on a product space is the canonical evaluation map
`Function.eval i : ((j : I) → Ω j) → Ω i`, sending `ω` to its `i`th coordinate `ω i`. -/
recall Function.eval (i : I) (ω : (j : I) → Ω j) : Ω i

/- The canonical projection from the coordinates indexed by `J'` to those indexed by `J ⊆ J'` is
the restriction map `Set.restrict₂`, sending a dependent tuple on `J'` to its restriction to `J`.
-/
recall Set.restrict₂ {J J' : Set I} (hJJ' : J ⊆ J') (ω : (j : J') → Ω j) (j : J) : Ω j

/- In the special case `J' = I`, the projection `X_J = X_J^I` is the usual restriction map
`Set.restrict` from the full product `((i : I) → Ω i)` to the subproduct `((j : J) → Ω j)`. -/
recall Set.restrict (J : Set I) (ω : (i : I) → Ω i) (j : J) : Ω j
