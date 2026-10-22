/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap07.Definition_7_8
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Corollary_13_38
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Proposition_13_10

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

section Conjugation

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedSpace_l2
attribute [local instance] ERealFunction.prod_innerProductSpace_l2

-- Proof sketch: use Corollary 13.38 to rewrite `f.asEReal` as its Fenchel biconjugate, then apply
-- Proposition 13.10(v) to the canonical conjugate `f.asEReal∗`.
/-- Corollary 13.42 in canonical support-function form: if `f ∈ Γ₀(ℋ)`, then `f` is the support
function of the epigraph of its Fenchel conjugate, evaluated along `(x, -1)`. -/
theorem eq_supportFunction_epigraph_conjugate_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) :
    f.asEReal = fun x ↦ σ[epigraph (f.asEReal∗)] (x, -1) := by
  calc
    f.asEReal = f.asEReal∗∗ := (biconjugate_eq_of_mem_gammaZero hf).symm
    _ = fun x ↦ σ[epigraph (f.asEReal∗)] (x, -1) := by
      simpa using conjugate_eq_support_function_epigraph (f.asEReal∗)

-- Proof sketch: expand the support function in the preceding theorem to the supremum over the
-- conjugate epigraph.
/-- Corollary 13.42: if `f ∈ Γ₀(ℋ)`, then `f` is the supremum of its continuous affine minorants,
parametrized by the epigraph of the Fenchel conjugate `f*`. -/
theorem eq_sSup_image_epigraph_conjugate_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) :
    f.asEReal =
      fun x ↦
        sSup ((fun p : H × ℝ ↦ ((⟪p.1, x⟫_ℝ - p.2 : ℝ) : EReal)) ''
          epigraph (f.asEReal∗)) := by
  ext x
  calc
    f.asEReal x = f.asEReal∗∗ x := by
      simpa using congrFun (biconjugate_eq_of_mem_gammaZero hf).symm x
    _ =
        sSup ((fun p : H × ℝ ↦ ((⟪p.1, x⟫_ℝ - p.2 : ℝ) : EReal)) '' epigraph (f.asEReal∗)) := by
        simpa using conjugate_eq_sSup_image_epigraph (f.asEReal∗) x

end Conjugation

end ERealFunction
