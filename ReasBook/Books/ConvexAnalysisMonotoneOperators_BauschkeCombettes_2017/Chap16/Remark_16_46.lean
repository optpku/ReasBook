/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Proposition_9_18
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Proposition_9_30
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Example_12_13
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Definition_12_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Corollary_13_38
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Definition_16_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Example_16_34

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise

universe u

namespace ERealFunction

section SubdifferentialCalculus

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: Proposition 16.42 identifies `∂ (f + g)` with `∂ f + ∂ g` once the conjugate
-- formula holds. Exactness of `f∗[hf] □ g∗[hg]` on `dom ((f + g)∗[...])` upgrades the ordinary
-- infimal convolution to that conjugate formula at precisely the points where
-- Proposition 16.42 needs it.
/-- If `f∗[hf] □ g∗[hg]` is exact on the domain of the canonical packaged conjugate of `f + g`,
then the subdifferential of `f + g` splits as the pointwise sum `∂ f + ∂ g`. This is the
statement displayed as `(16.39)` in Remark 16.46. -/
theorem subdifferential_add_eq_add_of_infimalConvolution_exactOn_dom_conjugate
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hexact :
      ∀ ⦃u : H⦄,
        u ∈ dom ((f + g)∗[pointwiseAdd_mem_gammaZero f g hf hg hdom]) →
          infimalConvolution.ExactAt (f∗[hf]) (g∗[hg]) u) :
    (∂ (f + g) : SetValuedOperator H H) = ∂ f + ∂ g := sorry

-- Proof sketch: starting from `∂ (f + g) = ∂ f + ∂ g`, apply the Exercise 16.12 argument quoted
-- in the remark: Fenchel--Young equality on the graph of `∂ ((f + g)∗[...])` produces
-- minimizing decompositions for `f∗[hf] □ g∗[hg]` at each point of
-- `dom (∂ ((f + g)∗[...]))`.
/-- If `∂ (f + g) = ∂ f + ∂ g`, then `f∗[hf] □ g∗[hg]` is exact at each point of the domain of
the subdifferential of the canonical packaged conjugate of `f + g`. This is the “almost
converse” displayed as `(16.40)` in Remark 16.46. -/
theorem infimalConvolution_exactAt_of_dom_conjugateAdd_of_subdifferential_add_eq_add
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hsub : (∂ (f + g) : SetValuedOperator H H) = ∂ f + ∂ g)
    {u : H}
    (hu :
      u ∈
        SetValuedOperator.dom
          (∂ ((f + g)∗[pointwiseAdd_mem_gammaZero f g hf hg hdom]))) :
    infimalConvolution.ExactAt (f∗[hf]) (g∗[hg]) u := sorry

end SubdifferentialCalculus

section Counterexample

namespace Remark16_46Counterexample

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedSpace_l2
attribute [local instance] ERealFunction.prod_completeSpace_l2
attribute [local instance] ERealFunction.prod_innerProductSpace_l2

private theorem epigraph_reciprocalBarrier_nonempty :
    (epigraph reciprocalBarrier : Set (ℝ × ℝ)).Nonempty := by
  refine ⟨((1 : ℝ), 1), ?_⟩
  simp [mem_epigraph_iff, reciprocalBarrier]

private theorem epigraph_conjugateReciprocalBarrier_nonempty :
    (epigraph reciprocalBarrier∗ : Set (ℝ × ℝ)).Nonempty := by
  refine ⟨((0 : ℝ), 0), ?_⟩
  change reciprocalBarrier∗ (0 : ℝ) ≤ (0 : ℝ)
  rw [conjugate_reciprocalBarrier]
  simp

/-- The first function in the explicit counterexample is the support function of the reciprocal
barrier epigraph, written as a `]-∞,+∞]`-valued function. -/
noncomputable abbrev barrierFunction : (ℝ × ℝ) → Set.Ioi (⊥ : EReal) :=
  properIoi (σ[epigraph reciprocalBarrier])
    (isProper_supportFunction_of_nonempty
      (epigraph reciprocalBarrier) epigraph_reciprocalBarrier_nonempty)

/-- The second function in the explicit counterexample is the support function of the conjugate
reciprocal-barrier epigraph, written as a `]-∞,+∞]`-valued function. -/
noncomputable abbrev conjugateBarrierFunction : (ℝ × ℝ) → Set.Ioi (⊥ : EReal) :=
  properIoi (σ[epigraph reciprocalBarrier∗])
    (isProper_supportFunction_of_nonempty
      (epigraph reciprocalBarrier∗) epigraph_conjugateReciprocalBarrier_nonempty)

/-- The first counterexample function belongs to `Γ₀(ℝ × ℝ)`. -/
theorem barrierFunction_mem_gammaZero :
    barrierFunction ∈ Γ₀(ℝ × ℝ) := sorry

/-- The second counterexample function belongs to `Γ₀(ℝ × ℝ)`. -/
theorem conjugateBarrierFunction_mem_gammaZero :
    conjugateBarrierFunction ∈ Γ₀(ℝ × ℝ) := sorry

/-- The effective domains of the counterexample functions intersect. -/
theorem effectiveDomain_inter_nonempty :
    (effectiveDomain barrierFunction ∩ effectiveDomain conjugateBarrierFunction).Nonempty := sorry

-- Proof sketch: identify `f^*` and `g^*` with the epigraph indicators from Example 12.13, use
-- the open-half-plane formula for their infimal convolution, and then apply `(16.39)` to the
-- exactness-on-the-conjugate-domain side. The conjugate of `f + g` is lower semicontinuous,
-- whereas the infimal convolution of the epigraph indicators jumps at `(0,0)`.
/-- In the explicit counterexample, the subdifferentials add exactly. -/
theorem subdifferential_add_eq_add :
    (∂ (barrierFunction + conjugateBarrierFunction) :
        SetValuedOperator (ℝ × ℝ) (ℝ × ℝ)) =
      ∂ barrierFunction + ∂ conjugateBarrierFunction := sorry

-- Proof sketch: after identifying `f^*` and `g^*` with the epigraph indicators from
-- Example 12.13, their infimal convolution is the indicator of the open upper half-plane. At the
-- boundary point `(0,0)` this value is `+∞`, while `(f + g)^*` takes the strictly smaller
-- lower-semicontinuous-envelope value.
/-- The conjugate identity fails for the explicit counterexample, already at the boundary point
`(0,0)`. -/
theorem conjugate_add_lt_infimalConvolution_conjugates_at_boundaryPoint :
    ((barrierFunction + conjugateBarrierFunction)∗[
        pointwiseAdd_mem_gammaZero barrierFunction conjugateBarrierFunction
          barrierFunction_mem_gammaZero conjugateBarrierFunction_mem_gammaZero
          effectiveDomain_inter_nonempty] (0, 0)) <
      (barrierFunction∗[barrierFunction_mem_gammaZero] □
        conjugateBarrierFunction∗[conjugateBarrierFunction_mem_gammaZero]) (0, 0) := sorry

end Remark16_46Counterexample

end Counterexample

end ERealFunction
