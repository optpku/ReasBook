/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_28
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Proposition_3_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Proposition_3_44
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap07.Proposition_7_13
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Corollary_8_5
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Proposition_8_11
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_2
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Proposition_9_14

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Topology

universe u

namespace ERealFunction

section

variable {H : Type u} [TopologicalSpace H]

/-- Proposition 11.1 (i): a lower semicontinuous function has the same supremum on a set and on
its closure. -/
theorem sSup_image_closure_eq_of_lowerSemicontinuous {f : H → EReal}
    (hf : LowerSemicontinuous f) (C : Set H) :
    sSup (f '' closure C) = sSup (f '' C) := by
  refine le_antisymm ?_ ?_
  · refine sSup_le ?_
    have hclosed : IsClosed {x : H | f x ≤ sSup (f '' C)} := by
      simpa [Set.preimage, Set.setOf_mem_eq] using
        (lowerSemicontinuous_iff_isClosed_preimage.mp hf) (sSup (f '' C))
    have hsubset : C ⊆ {x : H | f x ≤ sSup (f '' C)} := by
      intro x hx
      exact (isLUB_sSup _).1 (Set.mem_image_of_mem f hx)
    rintro _ ⟨x, hx, rfl⟩
    exact (closure_minimal hsubset hclosed) hx
  · exact sSup_le_sSup <| by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨x, subset_closure hx, rfl⟩

end

section

variable {H : Type u} [AddCommMonoid H] [Module ℝ H]

/-- The lower level sets of a Jensen-convex extended-real-valued function are convex. -/
private theorem convex_le_of_isConvex {f : H → EReal} (hf : IsConvex f) (r : EReal) :
    Convex ℝ {x : H | f x ≤ r} := by
  refine EReal.rec ?_ ?_ ?_ r
  · refine (convex_iff_forall_pos).2 ?_
    intro x hx y hy a b ha hb hab
    have ha_one : a ≤ 1 := by nlinarith
    have hb_eq : b = 1 - a := by nlinarith
    have hcomb :
        f (a • x + b • y) ≤ (a : EReal) * f x + (b : EReal) * f y := by
      simpa [hb_eq] using hf ha.le ha_one
    have hx_bot : f x = ⊥ := le_bot_iff.mp hx
    have hy_bot : f y = ⊥ := le_bot_iff.mp hy
    have haE : 0 < (a : EReal) := EReal.coe_pos.mpr ha
    have hbE : 0 < (b : EReal) := EReal.coe_pos.mpr hb
    simpa [hx_bot, hy_bot, EReal.mul_bot_of_pos haE, EReal.mul_bot_of_pos hbE] using hcomb
  · intro ξ
    have hconv_epi : Convex ℝ (epigraph f) := by
      refine (convex_epigraph_iff_jensen_on_dom f).2 ?_
      intro x y _ _ a ha ha_lt_one
      exact hf ha.le ha_lt_one.le
    simpa [lowerLevelSet, Set.preimage, Set.setOf_mem_eq] using
      convex_lowerLevelSet_of_convex_epigraph f hconv_epi ξ
  · simpa using (convex_univ : Convex ℝ (Set.univ : Set H))

/-- Proposition 11.1 (ii): a convex function has the same supremum on a set and on its convex
hull. -/
theorem sSup_image_convexHull_eq_of_isConvex {f : H → EReal} (hf : IsConvex f) (C : Set H) :
    sSup (f '' convexHull ℝ C) = sSup (f '' C) := by
  let r : EReal := sSup (f '' C)
  have hconv : Convex ℝ {x : H | f x ≤ r} := convex_le_of_isConvex hf r
  have hsubset : C ⊆ {x : H | f x ≤ r} := by
    intro x hx
    exact (isLUB_sSup _).1 (Set.mem_image_of_mem f hx)
  refine le_antisymm ?_ ?_
  · refine sSup_le ?_
    rintro _ ⟨x, hx, rfl⟩
    exact (convexHull_min hsubset hconv) hx
  · exact sSup_le_sSup <| by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨x, subset_convexHull ℝ C hx, rfl⟩

end

end ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Proposition 11.1 (iii), supremum form: the support function is unchanged by closed convex
hull. -/
theorem supportFunction_closure_convexHull_eq (C : Set H) :
    σ[closure (convexHull ℝ C)] = σ[C] := by
  obtain ⟨hconv, hclosure⟩ := supportFunction_eq_convexHull_and_closure_convexHull C
  exact hclosure.symm.trans hconv.symm

/-- Proposition 11.1 (iii), infimum form: the inner-product infimum is unchanged by closed convex
hull. -/
theorem innerInfimumOn_closure_convexHull_eq (C : Set H) (u : H) :
    innerInfimumOn (closure (convexHull ℝ C)) u = innerInfimumOn C u := by
  have hσ :
      -σ[closure (convexHull ℝ C)] (-u) = -σ[C] (-u) := by
    exact congrArg (fun g : H → EReal ↦ -g (-u)) (supportFunction_closure_convexHull_eq C)
  have hset_closure :
      (-·) '' ((fun x : H ↦ (⟪x, -u⟫_ℝ : EReal)) '' closure (convexHull ℝ C)) =
        (fun x : H ↦ (⟪x, u⟫_ℝ : EReal)) '' closure (convexHull ℝ C) := by
    ext a
    constructor
    · rintro ⟨b, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, by simp [inner_neg_right]⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(⟪x, -u⟫_ℝ : EReal), ⟨x, hx, rfl⟩, by simp [inner_neg_right]⟩
  have hset :
      (-·) '' ((fun x : H ↦ (⟪x, -u⟫_ℝ : EReal)) '' C) =
        (fun x : H ↦ (⟪x, u⟫_ℝ : EReal)) '' C := by
    ext a
    constructor
    · rintro ⟨b, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, by simp [inner_neg_right]⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(⟪x, -u⟫_ℝ : EReal), ⟨x, hx, rfl⟩, by simp [inner_neg_right]⟩
  have hleft :
      -σ[closure (convexHull ℝ C)] (-u) =
        innerInfimumOn (closure (convexHull ℝ C)) u := by
    rw [innerSupremumOn_eq_sSup_image, EReal.sSup_eq_neg_sInf_image_neg, neg_neg,
      innerInfimumOn_eq_sInf_image, hset_closure]
  have hright : -σ[C] (-u) = innerInfimumOn C u := by
    rw [innerSupremumOn_eq_sSup_image, EReal.sSup_eq_neg_sInf_image_neg, neg_neg,
      innerInfimumOn_eq_sInf_image, hset]
  calc
    innerInfimumOn (closure (convexHull ℝ C)) u = -σ[closure (convexHull ℝ C)] (-u) := hleft.symm
    _ = -σ[C] (-u) := hσ
    _ = innerInfimumOn C u := hright

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Proposition 11.1 (iv): for `f ∈ Γ₀(H)`, convexity of `C`, and a point of the effective domain
inside `interior C`, the infimum of `f` is unchanged by passing from `C` to `closure C`. -/
theorem sInf_image_closure_eq_of_mem_gammaZero_of_convex_of_effectiveDomain_inter_interior_nonempty
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {C : Set H} (hC : Convex ℝ C)
    (hinter : (effectiveDomain f ∩ interior C).Nonempty) :
    sInf (f.asEReal '' closure C) =
      sInf (f.asEReal '' C) := by
  rcases hinter with ⟨x₁, hx₁dom, hx₁int⟩
  refine le_antisymm ?_ ?_
  · exact sInf_le_sInf (Set.image_mono subset_closure)
  · refine le_sInf ?_
    rintro _ ⟨x₀, hx₀closure, rfl⟩
    by_cases hx₀dom : x₀ ∈ effectiveDomain f
    · let g : ℝ → EReal := fun α ↦ f.asEReal (AffineMap.lineMap x₀ x₁ α)
      have hconv_epi : Convex ℝ (epigraph f.asEReal) := by
        refine (convex_epigraph_iff_jensen_on_dom f.asEReal).2 ?_
        intro x y hx hy α hα0 hα1
        exact hf.2.ineq
          (by simpa [effectiveDomain, ERealFunction.dom] using hx)
          (by simpa [effectiveDomain, ERealFunction.dom] using hy)
          hα0 hα1
      have hg_tendsto : Filter.Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 (f.asEReal x₀)) := by
        simpa [g] using
          tendsto_apply_lineMap_right_zero_of_lowerSemicontinuous_epigraph_convex
            hf.1 (by simpa [epigraph] using hconv_epi) hx₀dom hx₁dom
      have hα_pos : ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), 0 < α := by
        simpa using (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))
      have hα_lt_one : ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), α < 1 := by
        exact nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
      have hlower :
          ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ),
            sInf (f.asEReal '' C) ≤ g α := by
        filter_upwards [hα_pos, hα_lt_one] with α hα_pos hα_lt_one
        have hline_mem : AffineMap.lineMap x₀ x₁ α ∈ C := by
          have hline_int :
              AffineMap.lineMap x₁ x₀ (1 - α) ∈ interior C := by
            refine
              lineMap_mem_interior_of_mem_Ico_of_mem_interior_of_mem_closure
                hC hx₁int hx₀closure ⟨sub_nonneg.mpr hα_lt_one.le, by linarith⟩
          have hline_eq : AffineMap.lineMap x₁ x₀ (1 - α) = AffineMap.lineMap x₀ x₁ α := by
            simp [AffineMap.lineMap_apply_module, add_comm]
          exact interior_subset (hline_eq ▸ hline_int)
        exact sInf_le ⟨AffineMap.lineMap x₀ x₁ α, hline_mem, rfl⟩
      exact ge_of_tendsto hg_tendsto hlower
    · have hx₀top : f.asEReal x₀ = ⊤ := by
        have : ¬ f.asEReal x₀ < ⊤ := by
          simpa [mem_effectiveDomain_iff] using hx₀dom
        exact top_unique (not_lt.mp this)
      simp [hx₀top]

end ERealFunction
