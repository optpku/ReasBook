/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_2_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped ConvexAnalysis

variable {E₁ : Type u} [PseudoMetricSpace E₁]

/- Definition 4.4.13 lies in the local-model constrained-minimization domain on a
pseudo-metric ambient space.

Primary domain:
* local-model decrease quantities on closed trust-region balls
* the closed-ball specialization of the chapter's `EReal`-valued fiberwise-infimum owner

Sampled owner-style declarations:
* `partialInfProjection` in `Chap03/Theorem_3_1_2_3`, the chapter owner for constrained
  `EReal`-valued fiberwise infima
* `partialInfProjection_eq_sInf` in `Chap03/Theorem_3_1_2_3`, the canonical fiber-value
  specification theorem
* `extendedRealRealPart` in `Chap03/Definition_3_1_1_3`, the chapter bridge from finite
  `EReal` values to real values
* `extendedRealRealPart_partialInfProjection_eq_sInf` in `Chap03/Theorem_3_1_2_3`, the finite
  real-surface bridge for a fiberwise infimum

Best owner abstraction:
* source-facing: the textbook decrease quantity on the finite-value locus of the closed-ball
  infimum
* core/canonical: the closed-ball specialization
  `partialInfProjection (localModelClosedBallRelation r) (Real.toEReal ∘ Function.uncurry ψ)`
* bridge/view: the pointwise real-valued decrease obtained after supplying a finiteness proof for
  the closed-ball partial infimum

Primitive data:
* the local model `ψ`
* the radius `r`
* the ambient pseudo-metric structure needed to form `Metric.closedBall x r`
* the closed-ball fiber relation `{z | z.2 ∈ Metric.closedBall z.1 r}` used to specialize
  `partialInfProjection`

Derived API:
* the finite-value domain of the canonical closed-ball specialization of `partialInfProjection`
* the finite-value domain `localModelFiniteDomain ψ r`
* the source-facing decrease `localModelDecrease f ψ r : localModelFiniteDomain ψ r → ℝ`
* the pointwise bridge `localModelDecreaseAt f ψ r x hx`
* the finite-locus bridge theorems recovering the textbook real infimum formula

Source/core/bridge triage:
* source-facing: `localModelDecrease f ψ r`
* core/canonical:
  `partialInfProjection (localModelClosedBallRelation r) (Real.toEReal ∘ Function.uncurry ψ)`
* bridge/view: `localModelDecreaseAt`,
  `localModelDecreaseAt_eq_sub_sInf`, and `mem_localModelFiniteDomain_of_bddBelow`

This refinement deletes the duplicate closed-ball optimal-value owner, names the Chapter 3
`partialInfProjection` specialization explicitly as the canonical owner, and makes the real-valued
textbook decrease live on the natural finite-value domain rather than totalizing non-finite
infima through `EReal.toReal`.
-/

private def localModelClosedBallRelation (r : NNReal) : Set (E₁ × E₁) :=
  {z | z.2 ∈ Metric.closedBall z.1 r}

/-- The finite-value locus of the closed-ball local-model partial infimum. -/
abbrev localModelFiniteDomain (ψ : E₁ → E₁ → ℝ) (r : NNReal) : Set E₁ :=
  dom (partialInfProjection (localModelClosedBallRelation r) (Real.toEReal ∘ Function.uncurry ψ))

private theorem uncurry_image_localModelClosedBallFiber_eq
    (ψ : E₁ → E₁ → ℝ) (r : NNReal) (x : E₁) :
    Function.uncurry ψ '' {z : E₁ × E₁ | z ∈ localModelClosedBallRelation r ∧ z.1 = x} =
      ψ x '' Metric.closedBall x r := by
  ext t
  constructor
  · rintro ⟨⟨x', y⟩, hz, rfl⟩
    rcases hz with ⟨hy, rfl⟩
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨(x, y), ⟨hy, rfl⟩, rfl⟩

private theorem partialInfProjection_closedBall_eq_coe_sInf
    (ψ : E₁ → E₁ → ℝ) (r : NNReal) (x : E₁)
    (hψ : BddBelow (ψ x '' Metric.closedBall x r)) :
    partialInfProjection (localModelClosedBallRelation r)
        (Real.toEReal ∘ Function.uncurry ψ) x =
      (sInf (ψ x '' Metric.closedBall x r) : ℝ) := by
  let s : Set ℝ := ψ x '' Metric.closedBall x r
  have hs_nonempty : s.Nonempty := by
    refine ⟨ψ x x, ?_⟩
    exact ⟨x, Metric.mem_closedBall_self r.2, rfl⟩
  have hs_glb : IsGLB s (sInf s) := Real.isGLB_sInf hs_nonempty hψ
  have hs_glb' : IsGLB (((↑) : ℝ → EReal) '' s) ((sInf s : ℝ) : EReal) := by
    refine ⟨?_, ?_⟩
    · rintro z ⟨y, hy, rfl⟩
      exact_mod_cast hs_glb.1 hy
    · intro z hz
      by_cases hz_bot : z = ⊥
      · simp [hz_bot]
      · have hz_top : z ≠ ⊤ := by
          rcases hs_nonempty with ⟨y, hy⟩
          have hz_le : z ≤ (y : EReal) := hz ⟨y, hy, rfl⟩
          intro hz_eq_top
          rw [hz_eq_top] at hz_le
          simp at hz_le
        lift z to ℝ using ⟨hz_top, hz_bot⟩ with z
        have hz' : ∀ y ∈ s, z ≤ y := by
          intro y hy
          exact_mod_cast (hz ⟨y, hy, rfl⟩)
        exact_mod_cast hs_glb.2 hz'
  have hs_nonempty' : (((↑) : ℝ → EReal) '' s).Nonempty := hs_nonempty.image _
  change
    partialInfProjection (localModelClosedBallRelation r)
        (Real.toEReal ∘ Function.uncurry ψ) x =
      (sInf (ψ x '' Metric.closedBall x r) : ℝ)
  rw [partialInfProjection_eq_sInf]
  have himage :
      sInf ((Real.toEReal ∘ Function.uncurry ψ) ''
        {z : E₁ × E₁ | z ∈ localModelClosedBallRelation r ∧ z.1 = x}) =
        sInf (((↑) : ℝ → EReal) '' s) := by
    congr 1
    calc
      (Real.toEReal ∘ Function.uncurry ψ) ''
          {z : E₁ × E₁ | z ∈ localModelClosedBallRelation r ∧ z.1 = x} =
        ((↑) : ℝ → EReal) ''
          (Function.uncurry ψ ''
            {z : E₁ × E₁ | z ∈ localModelClosedBallRelation r ∧ z.1 = x}) := by
              ext z
              constructor
              · rintro ⟨p, hp, rfl⟩
                exact ⟨Function.uncurry ψ p, ⟨p, hp, rfl⟩, rfl⟩
              · rintro ⟨t, ⟨p, hp, rfl⟩, rfl⟩
                exact ⟨p, hp, rfl⟩
      _ = ((↑) : ℝ → EReal) '' s := by
        rw [uncurry_image_localModelClosedBallFiber_eq]
  rw [himage]
  exact hs_glb'.csInf_eq hs_nonempty'

/-- A bounded-below local-model image yields a finite value of the canonical Chapter 3 closed-ball
partial infimum at the center point, so the finite-locus bridge applies there. -/
theorem mem_localModelFiniteDomain_of_bddBelow
    (ψ : E₁ → E₁ → ℝ) (r : NNReal) (x : E₁)
    (hψ : BddBelow (ψ x '' Metric.closedBall x r)) :
    x ∈ localModelFiniteDomain ψ r := by
  constructor <;> intro hx
  · change
      partialInfProjection (localModelClosedBallRelation r)
          (Real.toEReal ∘ Function.uncurry ψ) x = ⊤ at hx
    rw [partialInfProjection_closedBall_eq_coe_sInf ψ r x hψ] at hx
    simp at hx
  · change
      partialInfProjection (localModelClosedBallRelation r)
          (Real.toEReal ∘ Function.uncurry ψ) x = ⊥ at hx
    rw [partialInfProjection_closedBall_eq_coe_sInf ψ r x hψ] at hx
    simp at hx

/-- A pointwise nonnegative local model has a closed-ball image that is bounded below by `0`. -/
theorem bddBelow_image_closedBall_of_nonneg
    (ψ : E₁ → E₁ → ℝ) (r : NNReal)
    (hψ : ∀ x y, 0 ≤ ψ x y) (x : E₁) :
    BddBelow (ψ x '' Metric.closedBall x r) := by
  refine ⟨0, ?_⟩
  rintro z ⟨y, -, rfl⟩
  exact hψ x y

/-- Definition 4.4.13: for a radius `r`, `localModelDecrease f ψ r` is the textbook decrease
quantity `Δ_r` on the natural finite-value locus of the closed-ball local-model partial infimum.
At a point `x` together with a proof that the Chapter 3 partial infimum is finite there, the
companion bridge theorem `localModelDecreaseAt_eq_sub_sInf` recovers the textbook formula
`Δ_r(x) = f x - inf_{y ∈ B̄(x,r)} ψ(x;y)`. -/
def localModelDecrease
    (f : E₁ → ℝ) (ψ : E₁ → E₁ → ℝ) (r : NNReal) :
    localModelFiniteDomain ψ r → ℝ :=
  fun x ↦
    f x - extendedRealRealPart
      (partialInfProjection
        (localModelClosedBallRelation r)
        (Real.toEReal ∘ Function.uncurry ψ)) x

/-- Pointwise evaluation of the finite-domain local-model decrease after supplying a finiteness
proof for the canonical closed-ball partial infimum. -/
abbrev localModelDecreaseAt
    (f : E₁ → ℝ) (ψ : E₁ → E₁ → ℝ) (r : NNReal)
    (x : E₁) (hx : x ∈ localModelFiniteDomain ψ r) : ℝ :=
  localModelDecrease f ψ r ⟨x, hx⟩

/-
Source-facing Lean notation for the textbook local-model decrease quantity `Δ_r(x)` after
supplying the required finiteness proof for the canonical closed-ball partial infimum.
-/
namespace LocalModelNotation

scoped notation:max "Δ[" f:arg "; " ψ:arg "; " r:arg "](" x:arg "; " hx:arg ")" =>
  localModelDecreaseAt f ψ r x hx

end LocalModelNotation

open scoped LocalModelNotation

/-- On the finite locus of the canonical Chapter 3 partial infimum, the source-facing quantity
`Δ_r(x)` is exactly `f x` minus the real infimum of the local model over `Metric.closedBall x r`.
-/
theorem localModelDecreaseAt_eq_sub_sInf
    (f : E₁ → ℝ) (ψ : E₁ → E₁ → ℝ) (r : NNReal)
    (x : E₁) (hx : x ∈ localModelFiniteDomain ψ r) :
    Δ[f; ψ; r](x; hx) = f x - sInf (ψ x '' Metric.closedBall x r) := by
  change f x - extendedRealRealPart
      (partialInfProjection
        (localModelClosedBallRelation r)
        (Real.toEReal ∘ Function.uncurry ψ)) x =
    f x - sInf (ψ x '' Metric.closedBall x r)
  congr 1
  calc
    extendedRealRealPart
        (partialInfProjection
          (localModelClosedBallRelation r)
          (Real.toEReal ∘ Function.uncurry ψ)) x =
      sInf (Function.uncurry ψ ''
        {z : E₁ × E₁ | z ∈ localModelClosedBallRelation r ∧ z.1 = x}) := by
          simpa using extendedRealRealPart_partialInfProjection_eq_sInf hx
    _ = sInf (ψ x '' Metric.closedBall x r) := by
      rw [uncurry_image_localModelClosedBallFiber_eq]

/-- If the local-model values on the radius-`r` closed ball are bounded below, then evaluating the
source-facing quantity at `x` recovers the textbook real closed-ball infimum formula. -/
theorem localModelDecreaseAt_eq_sub_sInf_of_bddBelow
    (f : E₁ → ℝ) (ψ : E₁ → E₁ → ℝ) (r : NNReal) (x : E₁)
    (hψ : BddBelow (ψ x '' Metric.closedBall x r)) :
    Δ[f; ψ; r](x; (mem_localModelFiniteDomain_of_bddBelow ψ r x hψ)) =
      f x - sInf (ψ x '' Metric.closedBall x r) := by
  simpa using localModelDecreaseAt_eq_sub_sInf f ψ r x
    (mem_localModelFiniteDomain_of_bddBelow ψ r x hψ)

end
