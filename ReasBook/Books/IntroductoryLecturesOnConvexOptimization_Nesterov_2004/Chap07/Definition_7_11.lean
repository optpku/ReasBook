/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_9
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_44

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped SupportFunction WithTopConvexAnalysis

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Definition 7.11 lies in the support-function / subdifferential geometry of convex bodies.

Primary domain:
- support functions of convex bodies and the Euclidean radii of their subdifferentials at `0`

Sampled owner-style declarations:
- `ConvexBody` from mathlib
- `supportFunction` with notation `ξ[Q]` in `Chap03/Definition_3_9`
- `subdifferentialWithin` with notation `∂[Q] f(x)` in `Chap03/Theorem_3_44`

Best owner abstraction:
- `ConvexBody E`

Primitive data:
- a convex body `Q₂ : ConvexBody E`

Derived API:
- the real-valued support-function bridge `Q₂.supportFunctionReal`
- the source-facing set `∂F(0)` as `Q₂.supportFunctionSubdifferentialAtZero`
- the radii sets `γ₀`, `γ₁`, and the ratio `α`

Source/core/bridge triage:
- source-facing: the radii and relative-scale ratio attached to the support function of `Q₂`
- core/canonical: `ConvexBody`, `ξ[Q]`, and `∂[Q] f(x)`
- bridge/view: `supportFunctionReal` and `supportFunctionSubdifferentialAtZero`

The previous file duplicated both the support-function owner and the real-valued unconstrained
subdifferential owner, and it packaged the convex-body data in a second wrapper structure whose
interior assumption never entered the definitions. This refinement keeps the source-facing radii
and ratio, but moves the public owner to `ConvexBody E` and derives the rest from the existing
chapter API.
-/

namespace ConvexBody

/-- The real-valued support function of the convex body `Q₂`, obtained from the Chapter 3 owner
`ξ[Q₂] : E → EReal` by the canonical `toReal` bridge. For convex bodies this matches the textbook
finite support value. -/
abbrev supportFunctionReal (Q2 : ConvexBody E) : E → ℝ :=
  fun v ↦ (ξ[(Q2 : Set E)] v).toReal

@[simp] theorem supportFunctionReal_apply (Q2 : ConvexBody E) (v : E) :
    Q2.supportFunctionReal v = (ξ[(Q2 : Set E)] v).toReal :=
  rfl

/-- The subdifferential `∂F(0)` of the real-valued support function of `Q₂`. -/
abbrev supportFunctionSubdifferentialAtZero (Q2 : ConvexBody E) : Set E :=
  subdifferentialWithin (Set.univ : Set E) Q2.supportFunctionReal (0 : E)

@[simp] theorem mem_supportFunctionSubdifferentialAtZero_iff
    {Q2 : ConvexBody E} {g : E} :
    g ∈ Q2.supportFunctionSubdifferentialAtZero ↔
      ∀ y : E, Q2.supportFunctionReal y ≥ Q2.supportFunctionReal 0 + inner ℝ g (y - 0) := by
  change g ∈ subdifferentialWithin (Set.univ : Set E) Q2.supportFunctionReal (0 : E) ↔
      ∀ y : E, Q2.supportFunctionReal y ≥ Q2.supportFunctionReal 0 + inner ℝ g (y - 0)
  simpa using
    (mem_subdifferentialWithin_iff :
      g ∈ subdifferentialWithin (Set.univ : Set E) Q2.supportFunctionReal (0 : E) ↔
        (0 : E) ∈ (Set.univ : Set E) ∧
          ∀ ⦃y : E⦄, y ∈ (Set.univ : Set E) →
            Q2.supportFunctionReal y ≥ Q2.supportFunctionReal 0 + inner ℝ g (y - 0))

/-- The positive Euclidean radii whose closed balls are contained in `∂F(0)`. -/
def gammaZeroRadii (Q2 : ConvexBody E) : Set ℝ :=
  {r | 0 < r ∧ Metric.closedBall (0 : E) r ⊆ Q2.supportFunctionSubdifferentialAtZero}

/-- Membership in `gammaZeroRadii` means that the closed Euclidean ball of radius `r` is contained
in `∂F(0)`. -/
theorem mem_gammaZeroRadii_iff {Q2 : ConvexBody E} {r : ℝ} :
    r ∈ Q2.gammaZeroRadii ↔
      0 < r ∧ Metric.closedBall (0 : E) r ⊆ Q2.supportFunctionSubdifferentialAtZero :=
  Iff.rfl

/-- The positive Euclidean radii whose closed balls contain `∂F(0)`. -/
def gammaOneRadii (Q2 : ConvexBody E) : Set ℝ :=
  {r | 0 < r ∧ Q2.supportFunctionSubdifferentialAtZero ⊆ Metric.closedBall (0 : E) r}

/-- Membership in `gammaOneRadii` means that `∂F(0)` is contained in the closed Euclidean ball of
radius `r`. -/
theorem mem_gammaOneRadii_iff {Q2 : ConvexBody E} {r : ℝ} :
    r ∈ Q2.gammaOneRadii ↔
      0 < r ∧ Q2.supportFunctionSubdifferentialAtZero ⊆ Metric.closedBall (0 : E) r :=
  Iff.rfl

/-- The inner Euclidean radius `γ₀(F)` of `∂F(0)`, formalized as the supremum of the admissible
inscribed radii. -/
def gammaZero (Q2 : ConvexBody E) : ℝ :=
  sSup Q2.gammaZeroRadii

/-- Expanding `gammaZero` gives the supremum of the radii whose closed balls lie in `∂F(0)`. -/
theorem gammaZero_eq_sSup (Q2 : ConvexBody E) :
    Q2.gammaZero = sSup Q2.gammaZeroRadii :=
  rfl

/-- The outer Euclidean radius `γ₁(F)` of `∂F(0)`, formalized as the infimum of the admissible
enclosing radii. -/
def gammaOne (Q2 : ConvexBody E) : ℝ :=
  sInf Q2.gammaOneRadii

/-- Expanding `gammaOne` gives the infimum of the radii whose closed balls contain `∂F(0)`. -/
theorem gammaOne_eq_sInf (Q2 : ConvexBody E) :
    Q2.gammaOne = sInf Q2.gammaOneRadii :=
  rfl

/-- Definition 7.11: for the support function `F(v) = max_{u ∈ Q₂} ⟪v, u⟫` of a convex body
`Q₂`, the relative-scale ratio `α(F)` is the quotient `γ₀(F) / γ₁(F)` of the inner and outer
Euclidean radii of `∂F(0)`. The textbook hypothesis `0 ∈ interior Q₂` is not needed to define
this quotient itself, so it is left to later positivity/nondegeneracy results instead of being
packaged as primitive data here. -/
def relativeScaleRatio (Q2 : ConvexBody E) : ℝ :=
  Q2.gammaZero / Q2.gammaOne

/-- Expanding `relativeScaleRatio` recovers the quotient `γ₀(F) / γ₁(F)`. -/
theorem relativeScaleRatio_eq (Q2 : ConvexBody E) :
    Q2.relativeScaleRatio = Q2.gammaZero / Q2.gammaOne :=
  rfl

/-- If the inner radius is positive and does not exceed the outer radius, then the relative-scale
ratio is positive and at most `1`. -/
theorem relativeScaleRatio_pos_and_le_one
    (Q2 : ConvexBody E)
    (hγ0 : 0 < Q2.gammaZero)
    (hγ01 : Q2.gammaZero ≤ Q2.gammaOne) :
    0 < Q2.relativeScaleRatio ∧ Q2.relativeScaleRatio ≤ 1 := by
  rw [relativeScaleRatio_eq]
  have hγ1 : 0 < Q2.gammaOne := lt_of_lt_of_le hγ0 hγ01
  constructor
  · exact div_pos hγ0 hγ1
  · have hγ1_inv : 0 < Q2.gammaOne⁻¹ := inv_pos.mpr hγ1
    simpa [div_eq_mul_inv, hγ1.ne'] using
      mul_le_mul_of_nonneg_right hγ01 hγ1_inv.le

end ConvexBody
