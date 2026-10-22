/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

universe u v w

variable {I : Type u} {Ω : Type v} {E : Type w}

variable [MeasurableSpace Ω] [MeasurableSpace E]

/-- Definition 12.1: a family `(X i)ᵢ` is exchangeable when every finite injective coordinate tuple
has the same law after permuting its coordinates. This source-facing declaration is the chapter
owner for exchangeability; later items derive companion criteria and consequences from it. -/
def IsExchangeable (X : I → Ω → E) (μ : Measure Ω := by volume_tac) : Prop :=
  ∀ ⦃n : ℕ⦄ (u : Fin n ↪ I) (σ : Equiv.Perm (Fin n)),
    IdentDistrib (fun ω i ↦ X (u (σ i)) ω) (fun ω i ↦ X (u i) ω) μ μ
