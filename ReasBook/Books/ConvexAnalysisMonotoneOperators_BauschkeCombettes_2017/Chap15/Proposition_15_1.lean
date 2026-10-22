/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Proposition_9_30
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Proposition_12_11
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Corollary_13_38
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Proposition_13_10
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Proposition_13_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Proposition_13_24
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Proposition_13_45

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

section AttouchBrezisTheorem

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))

private theorem conjugate_infimalConvolution_gammaZeroConjugates_eq_pointwiseAdd_asEReal :
    (gammaZeroConjugate f hf □ gammaZeroConjugate g hg)∗ = (f + g).asEReal := by
  have hconj_f : (gammaZeroConjugate f hf).asEReal = f.asEReal∗ := by
    funext u
    simp
  have hconj_g : (gammaZeroConjugate g hg).asEReal = g.asEReal∗ := by
    funext u
    simp
  calc
    (gammaZeroConjugate f hf □ gammaZeroConjugate g hg)∗
        = (gammaZeroConjugate f hf).asEReal∗ + (gammaZeroConjugate g hg).asEReal∗ :=
          conjugate_infimalConvolution_eq (gammaZeroConjugate f hf) (gammaZeroConjugate g hg)
    _ = f.asEReal∗∗ + g.asEReal∗∗ := by rw [hconj_f, hconj_g]
    _ = f.asEReal + g.asEReal := by
          rw [biconjugate_eq_of_mem_gammaZero hf, biconjugate_eq_of_mem_gammaZero hg]
    _ = (f + g).asEReal := by
          funext x
          simp [Function.asEReal_apply]

-- Proof sketch: Proposition 13.24 identifies the conjugate of the raw infimal convolution
-- `f.asEReal∗ □ g.asEReal∗` with the pointwise sum `f + g`, and Corollary 13.38 rewrites the
-- resulting biconjugates back to `f` and `g`.
/-- Proposition 15.1: for `f, g ∈ Γ₀(H)`, the Fenchel conjugate of the pointwise sum `f + g` is
the Fenchel biconjugate of `f* □ g*`. -/
theorem conjugate_pointwiseAdd_eq_biconjugate_infimalConvolution_conjugates
    :
    (f + g).asEReal∗ =
      (gammaZeroConjugate f hf □ gammaZeroConjugate g hg)∗∗ := by
  simpa using
    congrArg conjugate
      (conjugate_infimalConvolution_gammaZeroConjugates_eq_pointwiseAdd_asEReal f g hf hg).symm

-- Proof sketch: identify the conjugate of `f.asEReal∗ □ g.asEReal∗` with the proper `Γ₀(H)`
-- function `f + g` via Proposition 15.1, then invoke the standard properness implication for
-- Fenchel conjugates.
/-- Proposition 15.1: under the same assumptions, the infimal convolution `f* □ g*` of the
Fenchel conjugates is proper. -/
theorem isProper_infimalConvolution_conjugates
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    :
    IsProper (gammaZeroConjugate f hf □ gammaZeroConjugate g hg) := by
  have hfg : f + g ∈ Γ₀(H) := pointwiseAdd_mem_gammaZero f g hf hg hdom
  have hconj :
      (gammaZeroConjugate f hf □ gammaZeroConjugate g hg)∗ = (f + g).asEReal :=
    conjugate_infimalConvolution_gammaZeroConjugates_eq_pointwiseAdd_asEReal f g hf hg
  have hproper_conj : IsProper ((gammaZeroConjugate f hf □ gammaZeroConjugate g hg)∗) := by
    rw [hconj]
    exact isProper_of_mem_gammaZero hfg
  exact is_proper_of_conjugate_is_proper hproper_conj

-- Proof sketch: the Fenchel conjugates `f*` and `g*` are convex because `f, g ∈ Γ₀(H)`. The
-- standard convexity theorem for infimal convolutions then yields convexity of the epigraph of
-- `f* □ g*`.
/-
Proposition 15.1: if `f, g ∈ Γ₀(H)`, then the infimal convolution `f* □ g*` of the Fenchel
conjugates is convex on all of `H`.
-/
omit [CompleteSpace H] in
theorem convex_epigraph_infimalConvolution_conjugates
    :
    Convex ℝ (epigraph (gammaZeroConjugate f hf □ gammaZeroConjugate g hg)) := by
  exact convex_epigraph_infimalConvolution
    (gammaZeroConjugate f hf) (gammaZeroConjugate g hg)
    (gammaZeroConjugate_mem_gammaZero hf).2
    (gammaZeroConjugate_mem_gammaZero hg).2

-- Proof sketch: by Proposition 15.1, the conjugate of `f.asEReal∗ □ g.asEReal∗` is the proper
-- function `f + g`. The standard bridge from a nontrivial conjugate to affine minorants then
-- yields a continuous affine minorant of `f* □ g*`.
/-- Proposition 15.1: under the same assumptions, the infimal convolution `f* □ g*` of the
Fenchel conjugates admits a continuous affine minorant. -/
theorem exists_continuousAffineMinorantWithSlope_infimalConvolution_conjugates
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    :
    ∃ u : H,
      HasContinuousAffineMinorantWithSlope
        (gammaZeroConjugate f hf □ gammaZeroConjugate g hg) u := by
  let F : H → EReal := gammaZeroConjugate f hf □ gammaZeroConjugate g hg
  have hfg : f + g ∈ Γ₀(H) := pointwiseAdd_mem_gammaZero f g hf hg hdom
  have hconj : F∗ = (f + g).asEReal := by
    simpa [F] using
      conjugate_infimalConvolution_gammaZeroConjugates_eq_pointwiseAdd_asEReal f g hf hg
  rcases hfg.2.nonempty with ⟨u, hu⟩
  refine ⟨u, ?_⟩
  have hdom_conj : u ∈ dom F∗ := by
    rw [hconj]
    simpa [effectiveDomain, dom] using hu
  simpa [F] using
    (mem_dom_conjugate_iff_hasContinuousAffineMinorantWithSlope F u).1 hdom_conj

-- Proof sketch: apply Proposition 13.45 to the dual infimal convolution `f* □ g*`; the
-- affine-minorant clause of Proposition 15.1 ensures this function has nonempty conjugate domain.
/-- Chapter 13 bridge consequence of Proposition 15.1: under the same hypotheses, the Fenchel
conjugate of `f + g` is the lower semicontinuous convex envelope `\breve{(f* □ g*)}`. -/
theorem conjugate_pointwiseAdd_eq_lscConvexEnvelope_infimalConvolution_conjugates
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    :
    (f + g).asEReal∗ =
      lowerSemicontinuousConvexEnvelope (gammaZeroConjugate f hf □ gammaZeroConjugate g hg) := by
  let F : H → EReal := gammaZeroConjugate f hf □ gammaZeroConjugate g hg
  have hfg : f + g ∈ Γ₀(H) := pointwiseAdd_mem_gammaZero f g hf hg hdom
  have hconj : F∗ = (f + g).asEReal := by
    simpa [F] using
      conjugate_infimalConvolution_gammaZeroConjugates_eq_pointwiseAdd_asEReal f g hf hg
  have hdom_conj : (dom F∗).Nonempty := by
    rw [hconj]
    simpa [effectiveDomain, dom] using hfg.2.nonempty
  calc
    (f + g).asEReal∗ = F∗∗ := by
      simpa [F] using conjugate_pointwiseAdd_eq_biconjugate_infimalConvolution_conjugates f g hf hg
    _ = lowerSemicontinuousConvexEnvelope F :=
      biconjugate_eq_lowerSemicontinuousConvexEnvelope_of_dom_conjugate_nonempty F hdom_conj
    _ = lowerSemicontinuousConvexEnvelope (gammaZeroConjugate f hf □ gammaZeroConjugate g hg) := by
      rfl

end AttouchBrezisTheorem

end ERealFunction
