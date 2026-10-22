/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_2
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_7
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_8
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

section

open Metric

variable {E : Type u} [SeminormedAddCommGroup E]

-- Proof sketch: unfold `infimal_convolution`, expand `δ_C`, and use
-- `infDist_eq_iInf` to identify the infimum over `C` of the distances `dist x y = ‖x - y‖`
-- with the pointwise infimum over all `y : E` of `δ_C y + ‖x - y‖`.
/-- Helper for Example 2.6: for a nonempty set `C` in a real seminormed
space, the distance to `C` is the
infimal convolution of the extended indicator `δ_C` with the norm function `h₁(z) = ‖z‖`.

The source example applies this identity to convex sets, but convexity is not needed for the
equality itself. -/
theorem infimal_convolution_extendedIndicator_norm_eq_infDist
    (C : Set E) (hCne : C.Nonempty) (x : E) :
    (δ_ C □ fun z : E ↦ (‖z‖ : EReal)) x =
      (Metric.infDist x C : EReal) := by
  let F : EReal := (δ_ C □ fun z : E ↦ (‖z‖ : EReal)) x
  have hF_nonneg : 0 ≤ F := by
    -- Every summand in the defining infimum is nonnegative, so the infimum is nonnegative.
    dsimp [F]
    rw [infimal_convolution_apply]
    refine le_iInf ?_
    intro y
    by_cases hy : y ∈ C
    · simp [hy]
    · simp [hy]
  have hF_top : F ≠ ⊤ := by
    -- A witness from the nonempty set gives a finite upper bound on the infimum.
    rcases hCne with ⟨y, hy⟩
    have hFy : F ≤ (dist x y : EReal) := by
      dsimp [F]
      rw [infimal_convolution_apply]
      exact iInf_le_of_le y (by simp [hy, dist_eq_norm])
    intro hF_top
    simp [hF_top] at hFy
  have hF_bot : F ≠ ⊥ := by
    -- A nonnegative extended real value cannot be `⊥`.
    intro hF_bot
    simp [F, hF_bot] at hF_nonneg
  have hF_glb : IsGLB ((fun y : E ↦ dist x y) '' C) F.toReal := by
    refine ⟨?_, ?_⟩
    · intro r hr
      rcases hr with ⟨y, hy, rfl⟩
      have hFy : F ≤ (dist x y : EReal) := by
        dsimp [F]
        rw [infimal_convolution_apply]
        exact iInf_le_of_le y (by simp [hy, dist_eq_norm])
      exact EReal.toReal_le_toReal hFy hF_bot (by simp)
    · intro z hz
      have hz' : (z : EReal) ≤ F := by
        -- Any lower bound on the distance image is also a lower bound on every summand.
        dsimp [F]
        rw [infimal_convolution_apply]
        refine le_iInf ?_
        intro y
        by_cases hy : y ∈ C
        · have hyz : z ≤ dist x y := hz ⟨y, hy, rfl⟩
          simpa [hy, dist_eq_norm] using (EReal.coe_le_coe hyz)
        · simp [hy]
      exact EReal.toReal_le_toReal hz' (by simp) hF_top
  have h_toReal : F.toReal = Metric.infDist x C :=
    IsGLB.unique hF_glb (Metric.isGLB_infDist (x := x) (s := C) hCne)
  -- Compare finite extended-real values through their real parts.
  exact (EReal.toReal_eq_toReal hF_top hF_bot (by simp) (by simp)).mp h_toReal

end

section

open Metric

variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- Helper for Example 2.6: the extended indicator `δ_ C` of a convex set is convex as an
`EReal`-valued function. -/
lemma extendedIndicator_isConvexFunction_of_convex (C : Set E) (hC : Convex ℝ C) :
    is_convex_function (δ_ C) := by
  -- Route correction: prove convexity from the real epigraph directly, instead of forcing the
  -- `toReal` bridge on a function that already has a simple epigraph description.
  rw [is_convex_function_iff_convex_real_epigraph]
  have hepigraph :
      {p : E × ℝ | (δ_ C) p.1 ≤ (p.2 : EReal)} = C ×ˢ Set.Ici (0 : ℝ) := by
    -- On `C`, the indicator is `0`; outside `C`, the epigraph condition is impossible.
    ext p
    by_cases hp : p.1 ∈ C
    · simp [hp]
    · simp [hp]
  simpa [hepigraph] using hC.prod (convex_Ici (0 : ℝ))

omit [NormedSpace ℝ E] in
/-- Helper for Example 2.6: when `C` is nonempty, the infimal convolution `δ_ C □ ‖·‖` is finite
everywhere, so its effective domain is all of `Set.univ`. -/
lemma effectiveDomain_infimalConvolutionExtendedIndicatorNorm_eq_univ
    (C : Set E) (hCne : C.Nonempty) :
    effective_domain (δ_ C □ fun z : E ↦ (‖z‖ : EReal)) = Set.univ := by
  -- Rewrite every value as the finite real-cast distance to `C`.
  ext x
  rw [mem_effective_domain]
  rw [infimal_convolution_extendedIndicator_norm_eq_infDist C hCne x]
  simp

-- Mathlib recall: `convexOn_dist`, `convexOn_univ_dist`, `convexOn_univ_norm`, and
-- `Metric.infDist`.
-- Proof sketch: if `C = ∅`, then `Metric.infDist · C = 0`, so the function is constant. Otherwise
-- rewrite `infDist · C` using
-- `infimal_convolution_extendedIndicator_norm_eq_infDist`, note that the indicator of a convex set
-- is convex and that `z ↦ ‖z‖` is convex by `convexOn_univ_norm`, then apply the convexity
-- owner theorem `infimal_convolution_is_convex` and convert back to a real-valued `ConvexOn`
-- statement on the full effective domain.
/-- Example 2.6: if `C` is convex, then its distance function `x ↦ infDist x C` is convex on
the whole space. -/
theorem convexOn_infDist (C : Set E) (hC : Convex ℝ C) :
    ConvexOn ℝ Set.univ (fun x : E ↦ Metric.infDist x C) := by
  by_cases hCne : C.Nonempty
  · let g : E → EReal := δ_ C □ fun z : E ↦ (‖z‖ : EReal)
    have hg_convex : is_convex_function g := by
      -- Combine convexity of the indicator and convexity of the norm through the owner theorem.
      dsimp [g]
      exact infimal_convolution_is_convex (δ_ C) (fun z : E ↦ ‖z‖)
        (extendedIndicator_isConvexFunction_of_convex C hC) convexOn_univ_norm
    have hg_toReal :
        ConvexOn ℝ (effective_domain g) (fun x : E ↦ (g x).toReal) := by
      -- The nonempty-set identity turns every value of `g` into the finite distance cast.
      refine convexOn_toReal_of_is_convex_function hg_convex ?_
      intro x hx
      dsimp [g]
      rw [infimal_convolution_extendedIndicator_norm_eq_infDist C hCne x]
      simp
    -- Rewrite the effective domain to `univ` and the finite-valued restriction to `Metric.infDist`.
    dsimp [g] at hg_toReal ⊢
    simpa [effectiveDomain_infimalConvolutionExtendedIndicatorNorm_eq_univ C hCne,
      infimal_convolution_extendedIndicator_norm_eq_infDist C hCne] using hg_toReal
  · have hEmpty : C = ∅ := Set.not_nonempty_iff_eq_empty.mp hCne
    -- The distance to the empty set is identically zero, hence convex.
    simpa [hEmpty, Metric.infDist_empty] using
      (convexOn_const (0 : ℝ) (convex_univ : Convex ℝ (Set.univ : Set E)))

end

end
