/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Definition_26_12
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Remark_26_3

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

universe u

namespace ProbabilityTheory

variable {n m : ℕ}

local notation "State" => Fin n → ℝ
local notation "StatePathSpace" => ContinuousMap NNReal State

variable {μ₀ : Measure State} [IsProbabilityMeasure μ₀]

variable
    {SolvesSDE : {Ω : Type u} → [MeasurableSpace Ω] →
      Filtration NNReal (inferInstance : MeasurableSpace Ω) → Measure Ω →
      (Ω → StatePathSpace) → (NNReal → Ω → Fin m → ℝ) → Prop}

/-- Definition 26.17: a weak solution with initial distribution `μ₀` is pathwise unique if every
other realization of the same SDE on the same filtered probability space, driven by the same
Brownian motion and starting from the same initial state almost surely, agrees with it almost
surely as a continuous state path, equivalently outside a null set one has `X_t = X'_t` for all
`t ≥ 0`. -/
def WeakSDESolution.IsPathwiseUnique (L : WeakSDESolution n m μ₀ SolvesSDE) : Prop :=
  ∀ (X' : L.Ω → StatePathSpace)
    (_ : Adapted L.ℱ (fun t ω ↦ X' ω t))
    (_ : (fun ω ↦ (X' ω) 0) =ᵐ[L.μ] (fun ω ↦ (L.X ω) 0))
    (_ : SolvesSDE L.ℱ L.μ X' L.W),
    X' =ᵐ[L.μ] L

/-- A weak solution is pathwise unique exactly when every other solution on the same filtered
probability space agrees with it almost surely as a continuous path. -/
theorem WeakSDESolution.isPathwiseUnique_iff (L : WeakSDESolution n m μ₀ SolvesSDE) :
    L.IsPathwiseUnique ↔
      ∀ (X' : L.Ω → StatePathSpace)
        (_ : Adapted L.ℱ (fun t ω ↦ X' ω t))
        (_ : (fun ω ↦ (X' ω) 0) =ᵐ[L.μ] (fun ω ↦ (L.X ω) 0))
        (_ : SolvesSDE L.ℱ L.μ X' L.W),
        X' =ᵐ[L.μ] L :=
  Iff.rfl

end ProbabilityTheory
