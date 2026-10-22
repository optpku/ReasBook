/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Proposition_13_24

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u v

namespace ERealFunction

section Conjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
variable [CompleteSpace H] [CompleteSpace K]

-- Proof sketch: use the hypothesis `⊥ ∉ range (L ▷ f)` to regard `L ▷ f` as an
-- `]-∞,+∞]`-valued function, apply Proposition 13.24(1) to its infimal convolution with `g`,
-- and then rewrite `(L ▷ f)^*` by Proposition 13.24(4).
/-- Corollary 13.25 (1): if the infimal postcomposition `L ▷ f` never attains `-∞`, then the
conjugate of its infimal convolution with `g` is `(f* ∘ L*) + g*`. -/
theorem conjugate_infimalConvolution_infimalPostcomposition_eq
    (f : H → Set.Ioi (⊥ : EReal)) (g : K → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K)
    (hL : (⊥ : EReal) ∉ Set.range (L ▷ f)) :
    (infimalConvolution (L ▷ f) g.asEReal)∗ =
      f.asEReal∗ ∘ L.adjoint + g.asEReal∗ := by
  let Lf : K → Set.Ioi (⊥ : EReal) := fun y ↦
    ⟨(L ▷ f) y, by
      by_contra hy
      exact hL ⟨y, le_antisymm (not_lt.mp hy) bot_le⟩⟩
  calc
    (infimalConvolution (L ▷ f) g.asEReal)∗ =
        (infimalConvolution Lf.asEReal g.asEReal)∗ := by rfl
    _ = Lf.asEReal∗ + g.asEReal∗ := conjugate_infimalConvolution_eq Lf g
    _ = f.asEReal∗ ∘ L.adjoint + g.asEReal∗ := by
      simpa [Lf] using
        congrArg (fun h : K → EReal ↦ h + g.asEReal∗)
          (conjugate_infimalPostcomposition_eq_comp_adjoint f L)

-- Proof sketch: apply Proposition 13.24(2) to `f + g ∘ L`, then bound the second conjugate term
-- by Proposition 13.24(5) and use the monotonicity of infimal convolution in its second entry.
/-- Corollary 13.25 (2): the conjugate of `f + g ∘ L` is bounded above by the infimal convolution
`f* □ (L* ▷ g*)`. -/
theorem conjugate_add_comp_le_infimalConvolution_infimalPostcomposition_adjoint_conjugate
    (f : H → Set.Ioi (⊥ : EReal)) (g : K → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K) :
    (f.asEReal + g.asEReal ∘ L)∗ ≤
      infimalConvolution f.asEReal∗ (L.adjoint ▷ g.asEReal∗) := by
  have hadd :
      (f.asEReal + g.asEReal ∘ L)∗ ≤
        infimalConvolution f.asEReal∗ (g ∘ L).asEReal∗ := by
    simpa using conjugate_add_le_infimalConvolution_conjugate f (g ∘ L)
  have hcomp :
      (g ∘ L).asEReal∗ ≤ L.adjoint ▷ g.asEReal∗ := by
    simpa using conjugate_comp_le_fiberInf_conjugate g L
  have hinf :
      infimalConvolution f.asEReal∗ (g ∘ L).asEReal∗ ≤
        infimalConvolution f.asEReal∗ (L.adjoint ▷ g.asEReal∗) := by
    intro x
    change (⨅ y : H, f.asEReal∗ y + (g ∘ L).asEReal∗ (x - y)) ≤
      ⨅ y : H, f.asEReal∗ y + (L.adjoint ▷ g.asEReal∗) (x - y)
    refine iInf_mono fun y ↦ ?_
    exact add_le_add le_rfl (hcomp (x - y))
  exact le_trans hadd hinf

end Conjugation

end ERealFunction
