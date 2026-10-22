/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_2
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_11
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Definition_12_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Definition_12_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

section Proposition1214

variable (f g : H → Set.Ioi (⊥ : EReal))
variable (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
-- Clause (ii) is kept in the source-facing bounded-below form; the zero-slope affine-minorant
-- owner is only an internal bridge.
variable
  (hcase :
    Supercoercive f.asEReal ∨
      (Coercive f.asEReal ∧ ∃ η : ℝ, ∀ x : H, (η : EReal) ≤ g.asEReal x))

omit [CompleteSpace H] in
private theorem hasContinuousAffineMinorantWithSlope_zero_of_bddBelow
    (hg_bddBelow : ∃ η : ℝ, ∀ x : H, (η : EReal) ≤ g.asEReal x) :
    HasContinuousAffineMinorantWithSlope g.asEReal 0 := by
  simpa [HasContinuousAffineMinorantWithSlope]

/-- Under the hypotheses of Proposition 12.14, the infimal convolution never attains the value
`-∞`. -/
-- Proof sketch: for points in the effective domain of `f □ g`, use Proposition 12.6 to obtain a
-- decomposition `x = y + z` with finite summands, then apply Corollary 11.16 to the translated sum
-- `u ↦ f u + g (x - u)` to get a minimizer, so `(f □ g) x` is a real value. Outside the effective
-- domain, the value of `f □ g` is `⊤`.
private theorem infimalConvolution_mem_Ioi_bot_of_supercoercive_or_coercive_bddBelow
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hcase :
      Supercoercive f.asEReal ∨
        (Coercive f.asEReal ∧ ∃ η : ℝ, ∀ x : H, (η : EReal) ≤ g.asEReal x))
    (x : H) :
    (f □ g) x ∈ Set.Ioi (⊥ : EReal) := sorry

-- Proof sketch: the companion exactness lemma gives attainment for the translated sum
-- `u ↦ f u + g (x - u)`, Proposition 12.11 gives convexity of the real-height epigraph, and the
-- Chapter 9 lower-semicontinuity result applies to the `EReal`-valued infimal convolution
-- itself. Together with the previous exclusion of `-∞`, these ingredients give the canonical
-- owner-level conclusion `IsProper (f □ g) ∧ (f □ g) ∈ gamma H`.
/-- Proposition 12.14: if `f, g ∈ Γ₀(H)` and either (i) `f` is supercoercive or (ii) `f` is
coercive while `g` is bounded below, then the raw infimal convolution `f □ g` is proper,
convex, and lower semicontinuous. In the project's owner-level API this is expressed as
`IsProper (f □ g)` together with `(f □ g) ∈ gamma H`. -/
theorem isProper_and_mem_gamma_infimalConvolution_of_supercoercive_or_coercive_bddBelow
    :
    IsProper (f □ g) ∧ (f □ g) ∈ gamma H := sorry

/-- Thin `Γ₀(H)` companion to Proposition 12.14, obtained by repackaging the raw owner
`f □ g : H → EReal` into its canonical `]-∞,+∞]`-valued view. -/
theorem infimalConvolution_mem_gammaZero_of_supercoercive_or_coercive_bddBelow
    :
    (fun x ↦
      ⟨(f □ g) x,
        infimalConvolution_mem_Ioi_bot_of_supercoercive_or_coercive_bddBelow
          f g hf hg hcase x⟩) ∈ Γ₀(H) := sorry

-- Proof sketch: fix `x ∈ dom (f □ g)` and apply Corollary 11.16 to the translated sum
-- `u ↦ f u + g (x - u)` to obtain a minimizer; this is precisely
-- `infimalConvolution.ExactAt f g x`.
/-- Companion lemma to Proposition 12.14: under the same hypotheses, the infimal convolution is
exact. -/
lemma infimalConvolution_exact_of_supercoercive_or_coercive_bddBelow
    :
    infimalConvolution.Exact f g := sorry

end Proposition1214

end ERealFunction
