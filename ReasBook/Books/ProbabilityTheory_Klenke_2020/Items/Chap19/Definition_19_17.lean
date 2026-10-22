/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap19.Definition_19_13
import Mathlib

universe u

noncomputable section

namespace ProbabilityTheory

variable {E : Type u} [Fintype E]

/- Definition 19.17 (1): for a chosen flow `I`, the textbook effective conductance toward `A₁`
is the canonical boundary current `netFlowOnSet I A₁`. This item is therefore a bridge to the
owner declaration `netFlowOnSet`, not a second owner-level definition. -/
recall ProbabilityTheory.netFlowOnSet {E : Type u} [Fintype E] (I : E → E → ℝ) (A₁ : Set E) : ℝ

/- Definition 19.17 (2): for the same chosen flow `I`, the textbook effective resistance toward
`A₁` is the reciprocal `1 / netFlowOnSet I A₁`. -/
#check fun (I : E → E → ℝ) (A₁ : Set E) ↦ (1 / netFlowOnSet I A₁ : ℝ)

end ProbabilityTheory
