/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Definition_12_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Definition_12_5
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Definition_12_34
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Corollary_13_38
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap15.Definition_15_19

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

noncomputable section

universe u v

namespace ERealFunction

section DualInfimalConvolution

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K]

-- Proof sketch: every Fenchel conjugate is convex, and infimal postcomposition along a linear map
-- preserves convexity of the epigraph. Proposition 12.11 then yields convexity of the infimal
-- convolution of those two canonical pieces.
/-- The infimal convolution of a Fenchel conjugate with the infimal postcomposition of a Fenchel
conjugate has convex epigraph. This is the core convexity owner behind dual infimal convolutions. -/
theorem convex_epigraph_infimalConvolution_conjugate_infimalPostcomposition
    (f : H → Set.Ioi (⊥ : EReal)) (g : K → Set.Ioi (⊥ : EReal))
    (A : K →L[ℝ] H) :
    Convex ℝ (epigraph (f.asEReal∗ □ (A ▷ g.asEReal∗))) := sorry

end DualInfimalConvolution

section FenchelRockafellarDuality

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

-- Proof sketch: combine the Chapter 13 formula for the conjugate of a sum with linear
-- precomposition and the biconjugacy identity for `Γ₀` functions, then identify the resulting
-- right-hand side with the canonical `EReal`-valued dual infimal convolution
-- `f.asEReal∗ □ (L.adjoint ▷ g.asEReal∗)`.
/-- Proposition 15.26 (1): if `f ∈ Γ₀(H)` and `g ∈ Γ₀(K)` with
`effectiveDomain g ∩ L '' effectiveDomain f ≠ ∅`, then the conjugate of the composite primal
objective is the Fenchel biconjugate of `f* □ (L* ▷ g*)`. -/
theorem conjugate_pointwiseAddComp_eq_biconjugate_dualInfimalConvolution
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (g : K → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K)
    (hdom : (effectiveDomain g ∩ L '' effectiveDomain f).Nonempty) :
    (compositePrimalObjective f g L)∗ =
      (f.asEReal∗ □ (L.adjoint ▷ g.asEReal∗))∗∗ := sorry

-- Proof sketch: use clause (1) to identify the conjugate of
-- `f.asEReal∗ □ (L.adjoint ▷ g.asEReal∗)` with the proper `Γ₀`
-- composite primal objective, then apply the standard implication that properness of the
-- conjugate forces properness of the original function.
/-- Proposition 15.26 (2): under the same assumptions, the dual infimal convolution
`f* □ (L* ▷ g*)` is proper. -/
theorem isProper_dualInfimalConvolution
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (g : K → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K)
    (hdom : (effectiveDomain g ∩ L '' effectiveDomain f).Nonempty) :
    IsProper (f.asEReal∗ □ (L.adjoint ▷ g.asEReal∗)) := sorry

-- Proof sketch: apply the owner-level convexity theorem for `f* □ (A ▷ g*)` and specialize to
-- `A = L.adjoint`. No `Γ₀` or domain-intersection hypothesis is needed; completeness enters only
-- through the Hilbert adjoint `L.adjoint`.
/-- Proposition 15.26 (3): for arbitrary `]-∞,+∞]`-valued `f` and `g`, the dual infimal
convolution `f* □ (L* ▷ g*)` is convex on all of `H`. -/
theorem convex_epigraph_dualInfimalConvolution
    (f : H → Set.Ioi (⊥ : EReal)) (g : K → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K) :
    Convex ℝ
      (epigraph (f.asEReal∗ □ (L.adjoint ▷ g.asEReal∗))) := by
  simpa using
    convex_epigraph_infimalConvolution_conjugate_infimalPostcomposition f g L.adjoint

-- Proof sketch: by clause (1), the conjugate of
-- `f.asEReal∗ □ (L.adjoint ▷ g.asEReal∗)` is the proper composite
-- primal objective. The standard criterion relating a nontrivial conjugate to affine minorants
-- then produces a continuous affine minorant of the dual infimal convolution.
/-- Proposition 15.26 (4): under the same assumptions, the dual infimal convolution
`f* □ (L* ▷ g*)` admits a continuous affine minorant. -/
theorem exists_continuousAffineMinorantWithSlope_dualInfimalConvolution
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (g : K → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K)
    (hdom : (effectiveDomain g ∩ L '' effectiveDomain f).Nonempty) :
    ∃ u : H,
      HasContinuousAffineMinorantWithSlope
        (f.asEReal∗ □ (L.adjoint ▷ g.asEReal∗)) u := sorry

end FenchelRockafellarDuality

end ERealFunction
