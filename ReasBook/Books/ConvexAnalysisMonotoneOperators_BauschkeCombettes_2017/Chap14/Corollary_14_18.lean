/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Proposition_12_14
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Corollary_13_38
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Proposition_13_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Proposition_13_15
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Proposition_13_24
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap14.Proposition_14_15
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap14.Theorem_14_17

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

section Conjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
variable (hsuper : Supercoercive f.asEReal)

private noncomputable def infimalConvolutionIoi
    (_hf : f ∈ Γ₀(H)) (_hg : g ∈ Γ₀(H)) (_hsuper : Supercoercive f.asEReal) :
    H → Set.Ioi (⊥ : EReal) :=
  properIoi (f □ g)
    (isProper_and_mem_gamma_infimalConvolution_of_supercoercive_or_coercive_bddBelow f g).1

private theorem infimalConvolutionIoi_mem_gammaZero
    (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H)) (hsuper : Supercoercive f.asEReal) :
    infimalConvolutionIoi f g hf hg hsuper ∈ Γ₀(H) := by
  exact infimalConvolution_mem_gammaZero_of_supercoercive_or_coercive_bddBelow
    f g hf hg (Or.inl hsuper)

-- Proof sketch: Proposition 12.14 packages `f □ g` as a member of `Γ₀(H)` under the
-- supercoercivity hypothesis on `f`. Then Proposition 14.16 identifies coercivity with
-- `0 ∈ interior (dom (·)*)`, Proposition 13.24 rewrites `(f □ g)*` as `f* + g*`, and
-- Proposition 14.15 gives `dom f* = univ`, so the interior-domain condition reduces exactly to
-- the corresponding condition for `g`.
/-- Corollary 14.18 (1): if `f, g ∈ Γ₀(H)` and `f` is supercoercive, then the infimal
convolution `f □ g` is coercive if and only if `g` is coercive. -/
theorem coercive_infimalConvolution_iff_coercive_of_left_supercoercive
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hsuper : Supercoercive f.asEReal) :
    Coercive (f □ g) ↔ Coercive g.asEReal := by
  have hfg :
      infimalConvolutionIoi f g hf hg hsuper ∈ Γ₀(H) :=
    infimalConvolutionIoi_mem_gammaZero f g hf hg hsuper
  have hdom_iff :
      (0 : H) ∈ interior (dom (infimalConvolutionIoi f g hf hg hsuper).asEReal∗) ↔
        (0 : H) ∈ interior (dom g.asEReal∗) := by
    have hbounded_f :
        ∀ B : Set H, Bornology.IsBounded B →
          ∃ M : ℝ, ∀ u ∈ B, f.asEReal∗ u ≤ M :=
      (supercoercive_iff_conjugate_boundedOnEveryBoundedSet f hf).mp hsuper
    have hdom_f : dom f.asEReal∗ = Set.univ :=
      dom_conjugate_eq_univ_of_conjugate_boundedOnEveryBoundedSet f hbounded_f
    have hsum_dom :
        dom (infimalConvolutionIoi f g hf hg hsuper).asEReal∗ = dom g.asEReal∗ := by
      ext x
      change ((f □ g)∗ x < ⊤) ↔ g.asEReal∗ x < ⊤
      rw [conjugate_infimalConvolution_eq]
      constructor
      · intro hx
        by_contra hxg
        have hxbot : f.asEReal∗ x ≠ ⊥ :=
          conjugate_ne_bot_of_isProper (isProper_of_mem_gammaZero hf) x
        have hxtop : g.asEReal∗ x = ⊤ := by
          simpa [mem_dom_iff] using hxg
        have hsum : f.asEReal∗ x + g.asEReal∗ x = ⊤ := by
          rw [hxtop]
          exact EReal.add_top_of_ne_bot hxbot
        have hsum' : (f.asEReal∗ + g.asEReal∗) x = ⊤ := by
          simpa using hsum
        exact (not_lt_of_ge le_top) (hsum' ▸ hx)
      · intro hx
        have hxf_dom : x ∈ dom f.asEReal∗ := by
          simp [hdom_f]
        have hxf : f.asEReal∗ x < ⊤ :=
          (mem_dom_iff _ _).1 hxf_dom
        simpa using EReal.add_lt_top (ne_of_lt hxf) (ne_of_lt hx)
    simp [hsum_dom]
  have hcoercive_infimal :
      Coercive (f □ g) ↔
        (0 : H) ∈ interior (dom (infimalConvolutionIoi f g hf hg hsuper).asEReal∗) := by
    let z : H → EReal := fun x ↦ ((⟪x, (0 : H)⟫_ℝ : ℝ) : EReal)
    have hz : z = fun _ : H ↦ (0 : EReal) := by
      funext x
      simp [z]
    have hsub_zero : (f □ g) - (fun _ : H ↦ (0 : EReal)) = (f □ g) := by
      funext x
      simp
    simpa [infimalConvolutionIoi, z, hz, hsub_zero] using
      coercive_sub_inner_iff_mem_interior_dom_conjugate
        (infimalConvolutionIoi f g hf hg hsuper) hfg (0 : H)
  have hcoercive_g :
      Coercive g.asEReal ↔ (0 : H) ∈ interior (dom g.asEReal∗) := by
    let z : H → EReal := fun x ↦ ((⟪x, (0 : H)⟫_ℝ : ℝ) : EReal)
    have hz : z = fun _ : H ↦ (0 : EReal) := by
      funext x
      simp [z]
    have hsub_zero : g.asEReal - (fun _ : H ↦ (0 : EReal)) = g.asEReal := by
      funext x
      simp
    simpa [z, hz, hsub_zero] using
      coercive_sub_inner_iff_mem_interior_dom_conjugate g hg (0 : H)
  exact hcoercive_infimal.trans (hdom_iff.trans hcoercive_g.symm)

-- Proof sketch: Proposition 12.14 again puts `f □ g` in `Γ₀(H)`. Apply Proposition 14.15 to
-- characterize supercoercivity by boundedness of the conjugate on bounded sets, rewrite
-- `(f □ g)* = f* + g*` via Proposition 13.24, and use the bounded-on-bounded-sets property of
-- `f*` supplied by Proposition 14.15 from the supercoercivity of `f`.
/-- Corollary 14.18 (2): if `f, g ∈ Γ₀(H)` and `f` is supercoercive, then the infimal
convolution `f □ g` is supercoercive if and only if `g` is supercoercive. -/
theorem supercoercive_infimalConvolution_iff_supercoercive_of_left_supercoercive
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hsuper : Supercoercive f.asEReal) :
    Supercoercive (f □ g) ↔ Supercoercive g.asEReal := by
  have hfg :
      infimalConvolutionIoi f g hf hg hsuper ∈ Γ₀(H) :=
    infimalConvolutionIoi_mem_gammaZero f g hf hg hsuper
  have hbounded_f :
      ∀ B : Set H, Bornology.IsBounded B →
        ∃ M : ℝ, ∀ u ∈ B, f.asEReal∗ u ≤ M :=
    (supercoercive_iff_conjugate_boundedOnEveryBoundedSet f hf).mp hsuper
  have hproper_f : IsProper f.asEReal := isProper_of_mem_gammaZero hf
  have hdom_biconj_f : (dom f.asEReal∗∗).Nonempty := by
    rcases hproper_f.2 with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [biconjugate_eq_of_mem_gammaZero hf]
    simpa using hx
  have hbounded_iff :
      (∀ B : Set H, Bornology.IsBounded B →
        ∃ M : ℝ, ∀ u ∈ B, f.asEReal∗ u + g.asEReal∗ u ≤ M) ↔
      (∀ B : Set H, Bornology.IsBounded B →
        ∃ M : ℝ, ∀ u ∈ B, g.asEReal∗ u ≤ M) := by
    constructor
    · intro hsum B hB
      rcases hsum B hB with ⟨M, hM⟩
      rcases exists_real_lowerBound_on_bounded_set_of_dom_conjugate_nonempty
          (f.asEReal∗) hdom_biconj_f B hB with ⟨m, hm⟩
      refine ⟨M - m, ?_⟩
      intro u hu
      have hsum_um : ((m : ℝ) : EReal) + g.asEReal∗ u ≤ M := by
        calc
          ((m : ℝ) : EReal) + g.asEReal∗ u ≤ f.asEReal∗ u + g.asEReal∗ u := by
            exact add_le_add (hm u hu) le_rfl
          _ ≤ M := hM u hu
      have hsum_um' : g.asEReal∗ u + ((m : ℝ) : EReal) ≤ M := by
        simpa [add_comm] using hsum_um
      exact (EReal.le_sub_iff_add_le
        (Or.inl (EReal.coe_ne_bot m))
        (Or.inl (EReal.coe_ne_top m))).2 hsum_um'
    · intro hg_bounded B hB
      rcases hbounded_f B hB with ⟨Mf, hMf⟩
      rcases hg_bounded B hB with ⟨Mg, hMg⟩
      refine ⟨Mf + Mg, ?_⟩
      intro u hu
      exact add_le_add (hMf u hu) (hMg u hu)
  have hsuper_infimal_raw :
      Supercoercive (f □ g) ↔
        ∀ B : Set H, Bornology.IsBounded B →
          ∃ M : ℝ, ∀ u ∈ B, (f □ g)∗ u ≤ M := by
    simpa [infimalConvolutionIoi] using
      supercoercive_iff_conjugate_boundedOnEveryBoundedSet
        (infimalConvolutionIoi f g hf hg hsuper) hfg
  have hsuper_infimal :
      Supercoercive (f □ g) ↔
        ∀ B : Set H, Bornology.IsBounded B →
          ∃ M : ℝ, ∀ u ∈ B, f.asEReal∗ u + g.asEReal∗ u ≤ M := by
    constructor
    · intro h B hB
      rcases (hsuper_infimal_raw.mp h) B hB with ⟨M, hM⟩
      refine ⟨M, ?_⟩
      intro u hu
      calc
        f.asEReal∗ u + g.asEReal∗ u = (f □ g)∗ u := by
          simpa using (congrFun (conjugate_infimalConvolution_eq f g) u).symm
        _ ≤ M := hM u hu
    · intro h
      refine hsuper_infimal_raw.mpr ?_
      intro B hB
      rcases h B hB with ⟨M, hM⟩
      refine ⟨M, ?_⟩
      intro u hu
      calc
        (f □ g)∗ u = f.asEReal∗ u + g.asEReal∗ u := by
          simpa using congrFun (conjugate_infimalConvolution_eq f g) u
        _ ≤ M := hM u hu
  have hsuper_g :
      Supercoercive g.asEReal ↔
        ∀ B : Set H, Bornology.IsBounded B →
          ∃ M : ℝ, ∀ u ∈ B, g.asEReal∗ u ≤ M :=
    supercoercive_iff_conjugate_boundedOnEveryBoundedSet g hg
  exact hsuper_infimal.trans (hbounded_iff.trans hsuper_g.symm)

end Conjugation

end ERealFunction
