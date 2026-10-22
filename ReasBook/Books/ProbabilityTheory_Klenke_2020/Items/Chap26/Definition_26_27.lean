/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

noncomputable section

universe u v w z

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {Ω' : Type v} [MeasurableSpace Ω']
variable {E : Type w} {E' : Type z}

/-- Definition 26.27: two families of `E`-valued and `E'`-valued stochastic processes, started
almost surely from their indexing points and governed by the law families `P` and `Q`, are dual
with duality function `H` when, for every `x`, `y`, and `t ≥ 0`, the observables
`ω ↦ H (X x t ω) y` and `ω ↦ H x (Y y t ω)` are integrable and have the same expectation. -/
class IsDualWith
    (P : E → ProbabilityMeasure Ω) (X : E → NNReal → Ω → E)
    (Q : E' → ProbabilityMeasure Ω') (Y : E' → NNReal → Ω' → E')
    (H : E → E' → ℂ) : Prop where
  /-- The `X`-family starts from its index point almost surely. -/
  left_initial (x : E) :
    X x 0 =ᵐ[(P x : Measure Ω)] fun _ ↦ x
  /-- The `Y`-family starts from its index point almost surely. -/
  right_initial (y : E') :
    Y y 0 =ᵐ[(Q y : Measure Ω')] fun _ ↦ y
  /-- The left-hand duality observable is integrable under the law of `Xˣ`. -/
  integrable_left (x : E) (y : E') (t : NNReal) :
    Integrable (fun ω ↦ H (X x t ω) y) (P x)
  /-- The right-hand duality observable is integrable under the law of `Yʸ`. -/
  integrable_right (x : E) (y : E') (t : NNReal) :
    Integrable (fun ω ↦ H x (Y y t ω)) (Q y)
  /-- The two duality expectations agree for every initial pair and every nonnegative time. -/
  expectation_eq (x : E) (y : E') (t : NNReal) :
    ∫ ω, H (X x t ω) y ∂(P x) = ∫ ω, H x (Y y t ω) ∂(Q y)

/- Bridge/view layer: fix one initial state and one law, and retain exactly the duality
integrability and expectation clauses needed for later uniqueness arguments. -/
/-- A process law `μ` started from `x` satisfies the duality relation with the family `(Q, Y)` and
duality function `H` if the left and right duality observables are integrable and have the same
expectation at every `y` and `t ≥ 0`. -/
def SatisfiesDualityAt
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : NNReal → Ω → E) (x : E)
    (Q : E' → ProbabilityMeasure Ω') (Y : E' → NNReal → Ω' → E')
    (H : E → E' → ℂ) : Prop :=
  ∀ y : E', ∀ t : NNReal,
    Integrable (fun ω ↦ H (X t ω) y) μ ∧
      Integrable (fun ω ↦ H x (Y y t ω)) (Q y) ∧
      ∫ ω, H (X t ω) y ∂μ = ∫ ω, H x (Y y t ω) ∂(Q y)

namespace IsDualWith

/-- A dual family yields the fixed-start duality relation for each chosen initial point. -/
theorem satisfiesDualityAt
    {P : E → ProbabilityMeasure Ω} {X : E → NNReal → Ω → E}
    {Q : E' → ProbabilityMeasure Ω'} {Y : E' → NNReal → Ω' → E'}
    {H : E → E' → ℂ}
    (h : IsDualWith P X Q Y H) (x : E) :
    SatisfiesDualityAt (P x : Measure Ω) (X x) x Q Y H := by
  intro y t
  exact ⟨h.integrable_left x y t, h.integrable_right x y t, h.expectation_eq x y t⟩

end IsDualWith

end ProbabilityTheory
