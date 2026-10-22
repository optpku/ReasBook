/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u v

section

variable {I : Type v} [AddMonoid I]
variable {E : Type u} [MeasurableSpace E]

/-- Definition 14.40: a family `κ : I → Kernel E E` of stochastic kernels is a Markov semigroup
if `κ 0 = Kernel.id` and the Chapman--Kolmogorov equation holds in mathlib's composition order,
namely `κ t ∘ₖ κ s = κ (s + t)` for all `s t : I`. -/
class IsMarkovSemigroup (κ : I → Kernel E E) : Prop where
  /-- Each time slice of a Markov semigroup is a stochastic kernel. -/
  isMarkovKernel : ∀ t : I, IsMarkovKernel (κ t)
  /-- The time-zero kernel is the identity kernel `ω ↦ δ_ω`. -/
  zero_eq : κ 0 = Kernel.id
  /-- Chapman--Kolmogorov in mathlib's composition order. -/
  comp_eq : ∀ s t : I, κ t ∘ₖ κ s = κ (s + t)

/-- Every time slice of a Markov semigroup is a stochastic kernel. -/
instance (κ : I → Kernel E E) [hκ : IsMarkovSemigroup κ] (t : I) :
    IsMarkovKernel (κ t) :=
  hκ.isMarkovKernel t

namespace IsMarkovSemigroup

section

variable {I : Type v} [AddCommMonoid I]
variable {κ : I → Kernel E E}

-- Proof sketch: apply the semigroup identity to `(s, t)` and `(t, s)` and then rewrite by
-- commutativity of addition.
/-- In a commutative time semigroup, the kernels of a Markov semigroup commute under composition. -/
theorem comp_comm (hκ : IsMarkovSemigroup κ) (s t : I) :
    κ t ∘ₖ κ s = κ s ∘ₖ κ t := by
  rw [hκ.comp_eq, hκ.comp_eq]
  exact congrArg κ (add_comm s t)

end

end IsMarkovSemigroup

end
