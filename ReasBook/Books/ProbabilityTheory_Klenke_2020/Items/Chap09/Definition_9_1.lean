/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

universe u v w

variable {I : Type u} {Ω : Type v} [mΩ : MeasurableSpace Ω]
variable {E : Type w} [MeasurableSpace E]

/- Definition 9.1: a stochastic process with time set `I` and state space `E` is a family
`X : I → Ω → E` whose time marginals are random variables. -/
#check (I → Ω → E)

/-- Definition 9.1: a stochastic process is a time-indexed family of `E`-valued random variables,
i.e. each time marginal `X t` is measurable on `Ω`. -/
def IsStochasticProcess (X : I → Ω → E) : Prop :=
  ∀ t, Measurable (X t)

namespace IsStochasticProcess

variable {X : I → Ω → E}

/-- Every time marginal of a stochastic process is measurable. -/
theorem measurable (hX : IsStochasticProcess X) (t : I) : Measurable (X t) :=
  hX t

end IsStochasticProcess

/-- Unfolding `IsStochasticProcess` gives the coordinatewise measurability condition. -/
theorem isStochasticProcess_iff (X : I → Ω → E) :
    IsStochasticProcess X ↔ ∀ t, Measurable (X t) :=
  Iff.rfl

/-- Constant families are stochastic processes on any time set. -/
theorem isStochasticProcess_const (x : E) :
    IsStochasticProcess (fun _ _ ↦ x : I → Ω → E) :=
  fun _ ↦ measurable_const

section AdaptedBridge

variable [Preorder I]
variable {X : I → Ω → E}

/-- A stochastic process is adapted to the top filtration. -/
theorem IsStochasticProcess.adapted_top (hX : IsStochasticProcess X) :
    Adapted (⊤ : Filtration I mΩ) X := by
  intro t
  simpa using hX t

/-- For the top filtration, adaptedness is exactly the textbook measurability condition for a
stochastic process. -/
theorem isStochasticProcess_iff_adapted_top (X : I → Ω → E) :
    IsStochasticProcess X ↔ Adapted (⊤ : Filtration I mΩ) X := by
  constructor
  · exact IsStochasticProcess.adapted_top
  · intro hX t
    simpa using hX t

end AdaptedBridge
