/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.ScaledProximityOperator
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Definition_13_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Definition_13_34
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Proposition_13_15

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

section Conjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: an `]-∞,+∞]`-valued function never takes the value `-∞`, so a nonempty effective
-- domain upgrades to properness of the canonical `EReal`-valued coercion. Proposition 13.15 then
-- shows that its Fenchel conjugate never takes the value `-∞`.
/-- If an `]-∞,+∞]`-valued function has nonempty effective domain, then its canonical Fenchel
conjugate never takes the value `-∞`. -/
theorem conjugate_ne_bot_of_effectiveDomain_nonempty
    {f : H → Set.Ioi (⊥ : EReal)} (hdom : (effectiveDomain f).Nonempty) (u : H) :
    f.asEReal∗ u ≠ ⊥ := by
  have hproper : IsProper f.asEReal := by
    refine ⟨fun x ↦ ne_of_gt (f x).2, ?_⟩
    simpa [effectiveDomain, dom] using hdom
  exact conjugate_ne_bot_of_isProper hproper u

/-- The Fenchel conjugate of an `]-∞,+∞]`-valued function with nonempty effective domain, packaged
again as `]-∞,+∞]`-valued. -/
noncomputable abbrev properConjugateIoi (f : H → Set.Ioi (⊥ : EReal))
    (hdom : (effectiveDomain f).Nonempty) :
    H → Set.Ioi (⊥ : EReal) :=
  fun u ↦
    ⟨f.asEReal∗ u,
      bot_lt_iff_ne_bot.mpr (conjugate_ne_bot_of_effectiveDomain_nonempty hdom u)⟩

-- Proof sketch: unfold `properConjugateIoi`.
/-- Coercing `properConjugateIoi f hdom` back to `EReal` recovers the canonical Fenchel
conjugate `f.asEReal∗`. -/
@[simp] theorem properConjugateIoi_apply
    (f : H → Set.Ioi (⊥ : EReal)) (hdom : (effectiveDomain f).Nonempty) (u : H) :
    (properConjugateIoi f hdom u : EReal) = f.asEReal∗ u :=
  rfl

/-- The `Γ₀(H)` specialization of `properConjugateIoi`. -/
noncomputable abbrev gammaZeroConjugate (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) :
    H → Set.Ioi (⊥ : EReal) :=
  properConjugateIoi f hf.2.nonempty

/- Lean cannot infer the `Γ₀(H)` witness from `f` alone, so the packaged source-facing conjugate
keeps that witness explicit and writes the canonical `Γ₀(H)` Fenchel conjugate as `f∗[hf]`. -/
scoped notation:max f "∗[" hf "]" => gammaZeroConjugate f hf

-- Proof sketch: unfold `gammaZeroConjugate`.
/-- Coercing `gammaZeroConjugate f hf` back to `EReal` recovers the canonical Fenchel conjugate
`f.asEReal∗`. -/
@[simp] theorem gammaZeroConjugate_apply
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (u : H) :
    (f∗[hf] u : EReal) = f.asEReal∗ u :=
  rfl

-- Proof sketch: `conjugate_mem_gamma` gives lower semicontinuity and convexity of the canonical
-- `EReal` Fenchel conjugate, while `f∗[hf]` packages the same function back into
-- `]-∞,+∞]` using `conjugate_ne_bot_of_effectiveDomain_nonempty`.
/-- The Fenchel conjugate of a `Γ₀(H)` function again belongs to `Γ₀(H)`. -/
theorem gammaZeroConjugate_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) :
    f∗[hf] ∈ Γ₀(H) := sorry

end Conjugation

section Transpose

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedSpace_l2
attribute [local instance] ERealFunction.prod_innerProductSpace_l2

/-- The canonical `Γ₀(H × H)` representative of the transpose-conjugate `F^{*T}`. -/
noncomputable abbrev gammaZeroConjugateTranspose
    (F : H × H → Set.Ioi (⊥ : EReal)) (hF : F ∈ Γ₀(H × H)) :
    H × H → Set.Ioi (⊥ : EReal) :=
  (F∗[hF])ᵀ

/- Lean cannot infer the `Γ₀(H × H)` witness from `F` alone, so the packaged source-facing
transpose-conjugate keeps that witness explicit and writes `F^{*T}` as `F∗ᵀ[hF]`. -/
scoped notation:max F "∗ᵀ[" hF "]" => gammaZeroConjugateTranspose F hF

@[simp] theorem gammaZeroConjugateTranspose_apply
    (F : H × H → Set.Ioi (⊥ : EReal)) (hF : F ∈ Γ₀(H × H)) (u x : H) :
    F∗ᵀ[hF] (u, x) = F∗[hF] (x, u) :=
  rfl

/-- The transpose-conjugate `F^{*T}` of a `Γ₀(H × H)` function again belongs to `Γ₀(H × H)`. -/
theorem gammaZeroConjugateTranspose_mem_gammaZero
    {F : H × H → Set.Ioi (⊥ : EReal)} (hF : F ∈ Γ₀(H × H)) :
    F∗ᵀ[hF] ∈ Γ₀(H × H) := by
  simpa [gammaZeroConjugateTranspose] using
    mem_gammaZero_comp_continuousLinearEquiv
      (f := F∗[hF]) (gammaZeroConjugate_mem_gammaZero hF)
      (ContinuousLinearEquiv.prodComm ℝ H H)

end Transpose

section ProximityOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-
Source-facing notation for the proximity operator of the Fenchel conjugate `f*`, represented by
the canonical `Γ₀(H)`-valued owner `f∗[hf]`.
-/
notation "Prox⋆[" f ", " hf "]" =>
  Prox[f∗[hf], gammaZeroConjugate_mem_gammaZero hf]

/-
Source-facing notation for the scaled proximity operator `Prox_{γ f*}`, represented by the
canonical `Γ₀(H)`-valued owner `f∗[hf]`.
-/
notation "Prox⋆[" γ ", " f ", " hf "]" =>
  Prox[γ, f∗[hf], gammaZeroConjugate_mem_gammaZero hf]

end ProximityOperator

section TransposeProximityOperator

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedSpace_l2
attribute [local instance] ERealFunction.prod_innerProductSpace_l2

/- Source-facing notation for the proximity operator of the transpose-conjugate `F^{*T}`,
represented by the canonical `Γ₀(H × H)`-valued owner `F∗ᵀ[hF]`. -/
notation "Prox⋆ᵀ[" F ", " hF "]" =>
  Prox[F∗ᵀ[hF], gammaZeroConjugateTranspose_mem_gammaZero hF]

end TransposeProximityOperator

section FenchelMoreau

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: Theorem 13.37 applies to the `EReal`-valued coercion of `f` because
-- `isProper_of_mem_gammaZero hf` gives properness and `asEReal_mem_gamma_of_mem_gammaZero hf`
-- gives the `gamma H` hypothesis.
/-- A `Γ₀(H)` function coincides with the Fenchel biconjugate of its `EReal`-valued coercion. -/
theorem biconjugate_eq_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) :
    f.asEReal∗∗ = f.asEReal := sorry

-- Proof sketch: combine `gammaZeroConjugate_mem_gammaZero hf` with
-- `biconjugate_eq_of_mem_gammaZero hf`.
/-- Corollary 13.38: if `f ∈ Γ₀(H)`, then its canonical `Γ₀(H)`-valued Fenchel conjugate again
belongs to `Γ₀(H)`, and the Fenchel biconjugate of the `EReal`-valued coercion of `f` is `f`
itself. -/
theorem conjugate_mem_gammaZero_and_biconjugate_eq
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) :
    f∗[hf] ∈ Γ₀(H) ∧ f.asEReal∗∗ = f.asEReal := by
  exact ⟨gammaZeroConjugate_mem_gammaZero hf, biconjugate_eq_of_mem_gammaZero hf⟩

end FenchelMoreau

end ERealFunction
