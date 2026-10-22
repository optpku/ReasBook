/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap11.Definition_11_5_extra_1

noncomputable section

open Filter

section

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

-- Semantic recall hits verified for this item:
-- Chapter 11 already owns the source nearest-point projection map `P` as
-- `nearestPointProjection`.
-- `DifferentiableAt.hasGradientAt` confirms that the source term `∇ f x` should only be used on
-- the public surface under an actual differentiability hypothesis at `x`.

/-- The difference quotient `(P (x - α • ∇ f x) - x) / α` appearing in the projected-gradient
definition. -/
def projectedGradientDifferenceQuotient
    (X : Set Point) (hX_nonempty : X.Nonempty) (hX_complete : IsComplete X)
    (hX_convex : Convex ℝ X) (f : Point → ℝ) (x : Point) :
    ℝ → Point :=
  fun α ↦
    α⁻¹ •
      (nearestPointProjection X hX_nonempty hX_complete hX_convex (x - α • gradient f x) - x)

/-- Unfolding `projectedGradientDifferenceQuotient X hX_nonempty hX_complete hX_convex f x α`
gives the source quotient `(P (x - α • ∇ f x) - x) / α`, where `P` is
`nearestPointProjection X hX_nonempty hX_complete hX_convex`. -/
theorem projectedGradientDifferenceQuotient_eq
    (X : Set Point) (hX_nonempty : X.Nonempty) (hX_complete : IsComplete X)
    (hX_convex : Convex ℝ X) (f : Point → ℝ) (x : Point) (α : ℝ) :
    projectedGradientDifferenceQuotient X hX_nonempty hX_complete hX_convex f x α =
      α⁻¹ •
        (nearestPointProjection X hX_nonempty hX_complete hX_convex (x - α • gradient f x) - x) :=
  rfl

/-- A vector `g` realizes the projected gradient of `f` at `x` with respect to a nonempty
complete convex feasible set `X` when `f` is differentiable at `x` and the projected-gradient
difference quotient tends to `g` as `α → 0+`. -/
def HasProjectedGradientAt
    (X : Set Point) (hX_nonempty : X.Nonempty) (hX_complete : IsComplete X)
    (hX_convex : Convex ℝ X) (f : Point → ℝ) (x : Point) (g : Point) : Prop :=
  DifferentiableAt ℝ f x ∧
    Tendsto
      (projectedGradientDifferenceQuotient X hX_nonempty hX_complete hX_convex f x)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds g)

theorem HasProjectedGradientAt.differentiableAt
    {X : Set Point} {hX_nonempty : X.Nonempty} {hX_complete : IsComplete X}
    {hX_convex : Convex ℝ X} {f : Point → ℝ} {x g : Point}
    (hg : HasProjectedGradientAt X hX_nonempty hX_complete hX_convex f x g) :
    DifferentiableAt ℝ f x :=
  hg.1

theorem HasProjectedGradientAt.tendsto
    {X : Set Point} {hX_nonempty : X.Nonempty} {hX_complete : IsComplete X}
    {hX_convex : Convex ℝ X} {f : Point → ℝ} {x g : Point}
    (hg : HasProjectedGradientAt X hX_nonempty hX_complete hX_convex f x g) :
    Tendsto
      (projectedGradientDifferenceQuotient X hX_nonempty hX_complete hX_convex f x)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds g) :=
  hg.2

/-- Chapter13 Definition 13.2-extra-1: the projected gradient of `f` at `x` with respect to a
nonempty complete convex feasible set `X`, defined as the right-limit value of
`(P (x - α • ∇ f x) - x) / α` as `α → 0+`, where `P` is the nearest-point projection onto `X`,
under the explicit hypothesis that some vector realizes this right limit. -/
noncomputable def projectedGradient
    (X : Set Point) (hX_nonempty : X.Nonempty) (hX_complete : IsComplete X)
    (hX_convex : Convex ℝ X) (f : Point → ℝ) (x : Point)
    (hlim : ∃ g, HasProjectedGradientAt X hX_nonempty hX_complete hX_convex f x g) : Point :=
  by
    let _ := hlim
    exact
      Filter.limUnder
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (projectedGradientDifferenceQuotient X hX_nonempty hX_complete hX_convex f x)

/-- Unfolding `HasProjectedGradientAt X hX_nonempty hX_complete hX_convex f x g` gives the
source differentiability and right-limit conditions defining the projected gradient of `f` at `x`
with respect to `X`. -/
theorem hasProjectedGradientAt_iff
    (X : Set Point) (hX_nonempty : X.Nonempty) (hX_complete : IsComplete X)
    (hX_convex : Convex ℝ X) (f : Point → ℝ) (x : Point) (g : Point) :
    HasProjectedGradientAt X hX_nonempty hX_complete hX_convex f x g ↔
      DifferentiableAt ℝ f x ∧
        Tendsto
        (fun α : ℝ ↦
          α⁻¹ •
            (nearestPointProjection X hX_nonempty hX_complete hX_convex (x - α • gradient f x) -
              x))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds g) :=
  Iff.rfl

/-- The value `projectedGradient X hX_nonempty hX_complete hX_convex f x hlim` satisfies the
projected-gradient differentiability and right-limit condition. -/
theorem projectedGradient_hasProjectedGradientAt
    (X : Set Point) (hX_nonempty : X.Nonempty) (hX_complete : IsComplete X)
    (hX_convex : Convex ℝ X) (f : Point → ℝ) (x : Point)
    (hlim : ∃ g, HasProjectedGradientAt X hX_nonempty hX_complete hX_convex f x g) :
    HasProjectedGradientAt X hX_nonempty hX_complete hX_convex f x
      (projectedGradient X hX_nonempty hX_complete hX_convex f x hlim) := by
  refine ⟨?_, ?_⟩
  · rcases hlim with ⟨g, hg⟩
    exact hg.differentiableAt
  · exact tendsto_nhds_limUnder <| by
      rcases hlim with ⟨g, hg⟩
      exact ⟨g, hg.tendsto⟩

/-- The projected gradient is defined only at points where `f` is differentiable. -/
theorem projectedGradient_differentiableAt
    (X : Set Point) (hX_nonempty : X.Nonempty) (hX_complete : IsComplete X)
    (hX_convex : Convex ℝ X) (f : Point → ℝ) (x : Point)
    (hlim : ∃ g, HasProjectedGradientAt X hX_nonempty hX_complete hX_convex f x g) :
    DifferentiableAt ℝ f x :=
  (projectedGradient_hasProjectedGradientAt X hX_nonempty hX_complete hX_convex f x hlim).1

/-- Unfolding `projectedGradient X hX_nonempty hX_complete hX_convex f x hlim` gives the source
right-limit formula for the projected gradient under the right-limit existence hypothesis `hlim`. -/
theorem projectedGradient_spec
    (X : Set Point) (hX_nonempty : X.Nonempty) (hX_complete : IsComplete X)
    (hX_convex : Convex ℝ X) (f : Point → ℝ) (x : Point)
    (hlim : ∃ g, HasProjectedGradientAt X hX_nonempty hX_complete hX_convex f x g) :
    Tendsto
      (projectedGradientDifferenceQuotient X hX_nonempty hX_complete hX_convex f x)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (projectedGradient X hX_nonempty hX_complete hX_convex f x hlim)) :=
  (projectedGradient_hasProjectedGradientAt X hX_nonempty hX_complete hX_convex f x hlim).2

#print axioms projectedGradientDifferenceQuotient
#print axioms projectedGradient

end
