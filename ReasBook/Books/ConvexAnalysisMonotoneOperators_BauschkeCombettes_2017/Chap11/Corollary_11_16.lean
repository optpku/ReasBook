/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Definition_8_7
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Proposition_9_30
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Corollary_11_9
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_3
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_11
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Proposition_11_14
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Proposition_11_15
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Definition_12_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Topology

universe u

namespace ERealFunction

section Normed

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {f g : H → Set.Ioi (⊥ : EReal)}

private theorem hasContinuousAffineMinorantWithSlope_zero_of_bddBelow
    (hg_bddBelow : BddBelow (Set.range g)) :
    HasContinuousAffineMinorantWithSlope g.asEReal 0 := by
  rcases hg_bddBelow with ⟨η, hη⟩
  by_cases hη_top : (η : EReal) = ⊤
  · refine ⟨0, ?_⟩
    intro x
    have hηx : (η : EReal) ≤ g.asEReal x := hη ⟨x, rfl⟩
    have hgx_top : g.asEReal x = ⊤ := by
      apply le_antisymm le_top
      simpa [hη_top] using hηx
    simp [hgx_top]
  · refine ⟨(η : EReal).toReal, ?_⟩
    intro x
    have hηx : (η : EReal) ≤ g.asEReal x := hη ⟨x, rfl⟩
    have hη_bot : (η : EReal) ≠ ⊥ := ne_of_gt η.2
    simpa [EReal.coe_toReal hη_top hη_bot] using hηx

-- Proof sketch: a zero-slope affine minorant of `g.asEReal` is just a real lower bound `η`.
-- Then `(f x : EReal) + (g x : EReal) ≥ (f x : EReal) + η`, so the coercive growth of `f`
-- forces the direct extended-real-valued sum to tend to `+∞` along `‖x‖ → +∞`.
/-- Adding a summand with a zero-slope continuous affine minorant to a coercive
`]-∞,+∞]`-valued function preserves coercivity. This is the affine-minorant companion to the
source-facing bounded-below formulation used in Corollary 11.16. -/
theorem pointwiseAdd_coercive_of_coercive_of_zeroSlopeAffineMinorant
    (hf_coe : Coercive f.asEReal)
    (hg_minor : HasContinuousAffineMinorantWithSlope g.asEReal 0) :
    Coercive (f + g).asEReal := by
  rw [Coercive, EReal.tendsto_nhds_top_iff_real] at hf_coe ⊢
  rcases hg_minor with ⟨η, hη⟩
  intro ξ
  have hf_tail : ∀ᶠ x in Bornology.cobounded H, ((ξ - η : ℝ) : EReal) < f.asEReal x :=
    hf_coe (ξ - η)
  filter_upwards [hf_tail] with x hx
  have hgx : (η : EReal) ≤ g.asEReal x := by
    simpa using hη x
  have hsum : (ξ : EReal) = ((ξ - η : ℝ) : EReal) + (η : EReal) := by
    rw [← EReal.coe_add]
    ring_nf
  calc
    (ξ : EReal) = ((ξ - η : ℝ) : EReal) + (η : EReal) := hsum
    _ < f.asEReal x + g.asEReal x := by
      exact EReal.add_lt_add_of_lt_of_le' hx hgx (by
        exact ne_of_gt (show (⊥ : EReal) < g.asEReal x from (g x).2)) <| by
          intro hgx_top hη_top
          simp at hη_top
    _ = (f + g).asEReal x := by simp [Function.asEReal]

end Normed

section RealVectorSpace

variable {H : Type u} [AddCommGroup H] [Module ℝ H]
variable {f g : H → Set.Ioi (⊥ : EReal)}

-- Proof sketch: on common effective-domain points, combine the strict Jensen inequality for `f`
-- with the weak Jensen inequality for `g`, then regroup the weighted sum.
/-- Adding a convex-on-effective-domain summand to a strictly convex `]-∞,+∞]`-valued function
preserves strict convexity. -/
theorem StrictlyConvex.add_convexOn_effectiveDomain
    (hf : StrictlyConvex f) (hg : ConvexOn g (effectiveDomain g)) :
    StrictlyConvex (f + g) := by
  intro x hx y hy hxy α hα0 hα1
  rcases (mem_effectiveDomain_pointwiseAdd_iff f g x).1 hx with ⟨hx_f, hx_g⟩
  rcases (mem_effectiveDomain_pointwiseAdd_iff f g y).1 hy with ⟨hy_f, hy_g⟩
  have hxg_top : (g x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx_g)
  have hyg_top : (g y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy_g)
  have hxg_bot : (g x : EReal) ≠ ⊥ := ne_of_gt (show (⊥ : EReal) < (g x : EReal) from (g x).2)
  have hyg_bot : (g y : EReal) ≠ ⊥ := ne_of_gt (show (⊥ : EReal) < (g y : EReal) from (g y).2)
  have hterm1_ne_top : (α : EReal) * (g x : EReal) ≠ ⊤ := by
    rw [EReal.mul_ne_top]
    refine ⟨Or.inl (EReal.coe_ne_bot α), Or.inl ?_, Or.inl (EReal.coe_ne_top α), Or.inr hxg_top⟩
    exact_mod_cast hα0.le
  have hterm2_ne_top : (1 - α : EReal) * (g y : EReal) ≠ ⊤ := by
    rw [EReal.mul_ne_top]
    refine ⟨Or.inl (EReal.coe_ne_bot (1 - α)), Or.inl ?_,
      Or.inl (EReal.coe_ne_top (1 - α)), Or.inr hyg_top⟩
    exact_mod_cast sub_nonneg.mpr hα1.le
  have hright_ne_top :
      (α : EReal) * (g x : EReal) + (1 - α : EReal) * (g y : EReal) ≠ ⊤ := by
    exact EReal.add_ne_top hterm1_ne_top hterm2_ne_top
  calc
    ((f + g) (α • x + (1 - α) • y) : EReal)
        = (f (α • x + (1 - α) • y) : EReal) + (g (α • x + (1 - α) • y) : EReal) := by simp
    _ < ((α : EReal) * (f x : EReal) + (1 - α : EReal) * (f y : EReal)) +
          ((α : EReal) * (g x : EReal) + (1 - α : EReal) * (g y : EReal)) := by
      exact EReal.add_lt_add_of_lt_of_le
        (hf.ineq hx_f hy_f hxy hα0 hα1)
        (hg.ineq hx_g hy_g hα0 hα1)
        (ne_of_gt (show (⊥ : EReal) < (g (α • x + (1 - α) • y) : EReal) from
          (g (α • x + (1 - α) • y)).2))
        hright_ne_top
    _ = (α : EReal) * ((f x : EReal) + (g x : EReal)) +
          (1 - α : EReal) * ((f y : EReal) + (g y : EReal)) := by
      have hα_nonneg : (0 : EReal) ≤ (α : EReal) := by
        exact_mod_cast hα0.le
      have hβ_nonneg : (0 : EReal) ≤ (1 - α : EReal) := by
        exact_mod_cast sub_nonneg.mpr hα1.le
      have hα_ne_top : (α : EReal) ≠ ⊤ := EReal.coe_ne_top α
      have hβ_ne_top : (1 - α : EReal) ≠ ⊤ := EReal.coe_ne_top (1 - α)
      rw [EReal.left_distrib_of_nonneg_of_ne_top hα_nonneg hα_ne_top,
        EReal.left_distrib_of_nonneg_of_ne_top hβ_nonneg hβ_ne_top]
      simp [add_assoc, add_left_comm]
    _ = (α : EReal) * (((f + g) x : EReal)) + (1 - α : EReal) * (((f + g) y : EReal)) := by
      simp

/-- Adding a strictly convex summand to a convex-on-effective-domain `]-∞,+∞]`-valued function
preserves strict convexity. -/
theorem ConvexOn.add_strictlyConvex_effectiveDomain
    (hf : ConvexOn f (effectiveDomain f)) (hg : StrictlyConvex g) :
    StrictlyConvex (f + g) := by
  convert hg.add_convexOn_effectiveDomain hf using 1
  ext x
  simp [add_comm]

end RealVectorSpace

section RealHilbert

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {f g : H → Set.Ioi (⊥ : EReal)}

-- Proof sketch: in case (i), commute the summands and apply Proposition 11.14 to `g + f`, then
-- pass from supercoercive to coercive. In case (ii), use the zero-slope affine minorant for `g`
-- together with coercivity of `f` and
-- `pointwiseAdd_coercive_of_coercive_of_zeroSlopeAffineMinorant`. The `Γ₀(H)` hypothesis on `f`
-- and the textbook domain-intersection hypothesis are both redundant for this coercivity
-- conclusion, so the Lean statement keeps only the assumptions that are actually used.
/-- Corollary 11.16 (1): if `g ∈ Γ₀(H)` and if either (i) `f` is supercoercive or (ii) `f` is
coercive while `g` is bounded below, then `f + g` is coercive. -/
theorem pointwiseAdd_coercive_of_supercoercive_or_coercive_bddBelow
    (hg : g ∈ Γ₀(H))
    (hcase :
      Supercoercive f.asEReal ∨
        (Coercive f.asEReal ∧ BddBelow (Set.range g))) :
    Coercive (f + g).asEReal := by
  rcases hcase with hf_super | ⟨hf_coe, hg_bddBelow⟩
  · convert
      coercive_of_supercoercive
        (pointwiseAdd_supercoercive_of_mem_gammaZero g f hg hf_super) using 1
    ext x
    simp [add_comm]
  · exact pointwiseAdd_coercive_of_coercive_of_zeroSlopeAffineMinorant hf_coe
      (hasContinuousAffineMinorantWithSlope_zero_of_bddBelow hg_bddBelow)

-- Proof sketch: first use the preceding coercivity theorem. If the effective domains intersect,
-- then `f + g ∈ Γ₀(H)` via `pointwiseAdd_mem_gammaZero`, so Proposition 11.15 applied
-- with `C = Set.univ` yields a minimizer. If they do not intersect, then
-- `mem_effectiveDomain_pointwiseAdd_iff` shows that the underlying sum is identically `⊤`, so any
-- point in the nonempty effective domain of `f` is a global minimizer. Thus the textbook
-- intersection hypothesis is redundant for existence and is omitted from the Lean statement.
/-- Corollary 11.16 (2): if `f, g ∈ Γ₀(H)` and if either (i) `f` is supercoercive or (ii) `f` is
coercive while `g` is bounded below, then `f + g` has a global minimizer. -/
theorem pointwiseAdd_argmin_nonempty_of_supercoercive_or_coercive_bddBelow
    (hg : g ∈ Γ₀(H)) (hf : f ∈ Γ₀(H))
    (hcase :
      Supercoercive f.asEReal ∨
        (Coercive f.asEReal ∧ BddBelow (Set.range g))) :
    (Argmin (f + g).asEReal).Nonempty := by
  by_cases hdom_fg : (effectiveDomain f ∩ effectiveDomain g).Nonempty
  · have hfg : f + g ∈ Γ₀(H) := pointwiseAdd_mem_gammaZero f g hf hg hdom_fg
    have hcoe : Coercive (f + g).asEReal :=
      pointwiseAdd_coercive_of_supercoercive_or_coercive_bddBelow hg hcase
    simpa using
      argminOn_nonempty_of_mem_gammaZero_of_coercive_or_bounded hfg
        isClosed_univ convex_univ Set.univ_nonempty (Or.inl hcoe)
  · rcases hf.2.nonempty with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [mem_argmin_iff, isMinOn_univ_iff]
    intro y
    have hy_top : (f + g).asEReal y = ⊤ := by
      apply le_antisymm le_top
      apply not_lt.mp
      intro hy
      exact hdom_fg ⟨y, ((mem_effectiveDomain_pointwiseAdd_iff f g y).1 hy).1,
        ((mem_effectiveDomain_pointwiseAdd_iff f g y).1 hy).2⟩
    simp [hy_top]
end RealHilbert

section GammaZeroRealVectorSpace

variable {H : Type u} [TopologicalSpace H] [AddCommGroup H] [Module ℝ H]
variable {f g : H → Set.Ioi (⊥ : EReal)}

-- Proof sketch: the intersection hypothesis gives a nonempty effective domain for `f + g`.
-- If one summand is strictly convex, the owner-level sum lemmas above upgrade this to strict
-- convexity of the same underlying sum. Corollary 11.9 then makes the argmin set subsingleton.
/-- Corollary 11.16 (3): if `f, g ∈ Γ₀(H)`, if their effective domains intersect, and if one
summand is strictly convex, then `f + g` has at most one global minimizer. -/
theorem pointwiseAdd_argmin_subsingleton_of_inter_nonempty_of_strictlyConvex
    (hg : g ∈ Γ₀(H)) (hf : f ∈ Γ₀(H))
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hstrict : StrictlyConvex f ∨ StrictlyConvex g) :
    (Argmin (f + g).asEReal).Subsingleton := by
  have hsum_strict : StrictlyConvex (f + g) := by
    rcases hstrict with hf_strict | hg_strict
    · exact hf_strict.add_convexOn_effectiveDomain hg.2
    · exact hf.2.add_strictlyConvex_effectiveDomain hg_strict
  exact
    argmin_subsingleton_of_nonempty_effectiveDomain_of_strictlyConvex
      (effectiveDomain_add_nonempty_of_inter_nonempty f g hdom) hsum_strict

end GammaZeroRealVectorSpace

end ERealFunction
