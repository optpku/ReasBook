/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped InnerProductSpace

universe u

section

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [c : PreInnerProductSpace.Core ℝ V]

attribute [local instance] InnerProductSpace.Core.toSeminormedAddCommGroup

local instance : InnerProductSpace ℝ V := InnerProductSpace.ofCore c

/-- Lemma 7.23: A semi-inner product on a real vector space is continuous for the product
topology coming from the pseudo-metric `d (x, y) = ⟪x - y, x - y⟫_ℝ ^ (1 / 2)`. -/
theorem continuous_inner_of_semi_inner_product :
    Continuous (fun p : V × V ↦ ⟪p.1, p.2⟫_ℝ) :=
  continuous_inner

end
