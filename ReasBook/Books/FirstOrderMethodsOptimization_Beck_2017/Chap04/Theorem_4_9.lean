/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_5
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_7
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_8
import FirstOrderMethodsOptimization_Beck_2017.Chap02.FunctionToEReal
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Definition_4_1
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Theorem_4_2
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Theorem_4_7
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_8

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/- Theorem 4.9 is `source-facing` in the chapter infimal-convolution/conjugacy calculus. Its
ambient notions are already owned upstream by the project declarations
`is_convex_function`, `infimal_convolution`, and `conjugate_function`. The textbook right-hand
side `(h₁^* + h₂^*)^*` starts from a function on the dual space `E*`, so the source-facing bridge
back to the primal space is the canonical bidual equivalence `Module.evalEquiv ℝ E : E ≃ₗ[ℝ] E**`,
whose forward map is `Module.Dual.eval ℝ E`. This file therefore reuses the chapter owners
directly, together with the Chapter 2 bridge `Function.toEReal`, instead of repeating parallel
local copies. -/

recall is_convex_function
recall infimal_convolution
recall conjugate_function
recall effective_domain
recall biconjugate_function

-- Semantic recall note: no direct mathlib theorem surfaced for this chapter-local formula, so the
-- statement follows the repository owner-level precedent also used later in Proposition 5.17.

-- Proof sketch: apply the chapter formula for the conjugate of an infimal convolution to obtain
-- `(h₁ □ h₂.toEReal)* = h₁* + h₂*`. The infimal-convolution convexity theorem gives convexity of
-- `h₁ □ h₂.toEReal`, and the hypothesis that it is real-valued makes it proper and closed in the
-- finite-dimensional chapter setting. Theorem 4.2 then identifies `h₁ □ h₂.toEReal` with its
-- biconjugate, and the canonical bidual equivalence `Module.evalEquiv ℝ E` transports the
-- dual-space conjugate of `h₁* + h₂*` back to primal points.
omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Helper for Theorem 4.9: an everywhere-real-valued infimal convolution agrees with the canonical
`toEReal` lift of its `toReal` model. -/
lemma infimalConvolution_eq_toEReal_toReal
    (h₁ : E → EReal) (h₂ : E → ℝ)
    (hreal : ∀ x, ∃ r : ℝ, (h₁ □ h₂.toEReal) x = (r : EReal)) :
    (h₁ □ h₂.toEReal) = (fun x ↦ ((h₁ □ h₂.toEReal) x).toReal).toEReal := by
  -- Normalize each pointwise value by ruling out both infinite endpoints.
  funext x
  rcases hreal x with ⟨r, hr⟩
  have hx_ne_top : (h₁ □ h₂.toEReal) x ≠ ⊤ := by
    rw [hr]
    exact EReal.coe_ne_top r
  have hx_ne_bot : (h₁ □ h₂.toEReal) x ≠ ⊥ := by
    rw [hr]
    exact EReal.coe_ne_bot r
  -- Once the value is finite, `toReal` followed by the canonical coercion returns the same point.
  simpa [Function.toEReal] using (EReal.coe_toReal hx_ne_top hx_ne_bot).symm

/-- Helper for Theorem 4.9: if `h₁ □ h₂.toEReal` is convex and everywhere finite, then it is
lower semicontinuous. -/
lemma lowerSemicontinuous_infimalConvolution_of_realValued
    (h₁ : E → EReal) (h₂ : E → ℝ)
    (hh₁_convex : is_convex_function h₁)
    (hh₂_convex : ConvexOn ℝ Set.univ h₂)
    (hreal : ∀ x, ∃ r : ℝ, (h₁ □ h₂.toEReal) x = (r : EReal)) :
    LowerSemicontinuous (h₁ □ h₂.toEReal) := by
  let f : E → EReal := h₁ □ h₂.toEReal
  let g : E → ℝ := fun x ↦ (f x).toReal
  -- The infimal convolution is convex by the earlier Chapter 2 owner theorem.
  have hf_convex : is_convex_function f := by
    dsimp [f]
    simpa [Function.toEReal] using infimal_convolution_is_convex h₁ h₂ hh₁_convex hh₂_convex
  -- The real-valued hypothesis excludes `-∞` pointwise.
  have hf_ne_bot : ∀ x, f x ≠ ⊥ := by
    intro x
    rcases hreal x with ⟨r, hr⟩
    dsimp [f] at hr ⊢
    rw [hr]
    exact EReal.coe_ne_bot r
  -- The same hypothesis identifies the effective domain with the whole space.
  have hdom : effective_domain f = Set.univ := by
    ext x
    constructor
    · intro hx
      simp
    · intro hx
      refine mem_effective_domain.mpr ?_
      rcases hreal x with ⟨r, hr⟩
      dsimp [f]
      rw [hr]
      exact EReal.coe_lt_top r
  -- Convexity of the finite-valued real model now holds on the whole space.
  have hg_convex_dom : ConvexOn ℝ (effective_domain f) g := by
    dsimp [g]
    exact convexOn_toReal_of_is_convex_function hf_convex (fun x _ ↦ hf_ne_bot x)
  have hg_convex : ConvexOn ℝ Set.univ g := by
    simpa [hdom] using hg_convex_dom
  -- Finite-dimensional convexity on `univ` upgrades to continuity.
  have hg_cont : Continuous g := by
    simpa [continuousOn_univ] using hg_convex.continuousOn
  have hf_eq : f = g.toEReal := by
    simpa [f, g] using infimalConvolution_eq_toEReal_toReal h₁ h₂ hreal
  -- Lower semicontinuity is preserved by the canonical `toEReal` lift of a continuous function.
  have hf_lsc : LowerSemicontinuous f := by
    rw [hf_eq]
    exact Function.toEReal_lowerSemicontinuous_of_continuous hg_cont
  simpa [f] using hf_lsc

/-- Theorem 4.9: if `h₁` is a proper convex extended-real-valued function, `h₂` is a real-valued
convex function, and the infimal convolution `h₁ □ h₂.toEReal` is real-valued, then
`h₁ □ h₂.toEReal` equals the conjugate of the dual-space sum `h₁^* + h₂^*`, transported back to
`E` by the canonical bidual equivalence `Module.evalEquiv ℝ E`. This is the source-facing chapter
rendering of the textbook identity `h₁ □ h₂ = (h₁^* + h₂^*)^*`, with the real-valued function `h₂`
inserted into the extended-real calculus through the canonical bridge `Function.toEReal`. -/
theorem infimal_convolution_eq_dual_conjugate_of_sum_conjugates
    (h₁ : E → EReal) (h₂ : E → ℝ) (hh₁_proper : IsProperExtendedRealFunction h₁)
    (hh₁_convex : is_convex_function h₁)
    (hh₂_convex : ConvexOn ℝ Set.univ h₂)
    (hreal : ∀ x, ∃ r : ℝ, (h₁ □ h₂.toEReal) x = (r : EReal)) :
    (h₁ □ h₂.toEReal) =
      conjugate_function
        (conjugate_function h₁ + conjugate_function h₂.toEReal)
        ∘ Module.evalEquiv ℝ E := by
  let f : E → EReal := h₁ □ h₂.toEReal
  -- The source hypothesis makes the convex infimal convolution closed
  -- through its real-valued model.
  have hf_closed : LowerSemicontinuous f := by
    dsimp [f]
    exact
      lowerSemicontinuous_infimalConvolution_of_realValued
        h₁ h₂ hh₁_convex hh₂_convex hreal
  have hf_convex : is_convex_function f := by
    dsimp [f]
    simpa [Function.toEReal] using infimal_convolution_is_convex h₁ h₂ hh₁_convex hh₂_convex
  have hf_proper : IsProperExtendedRealFunction f := by
    refine ⟨?_, ?_⟩
    · intro x
      rcases hreal x with ⟨r, hr⟩
      dsimp [f]
      rw [hr]
      exact EReal.coe_ne_bot r
    · rcases hreal 0 with ⟨r, hr⟩
      refine ⟨0, ?_⟩
      dsimp [f]
      rw [mem_effective_domain, hr]
      exact EReal.coe_lt_top r
  -- Apply the chapter biconjugation theorem to the proper closed convex infimal convolution.
  have hf_biconjugate : f = biconjugate_function f := by
    simpa using
      (biconjugate_function_eq_self_of_proper_closed_convex
        f hf_proper hf_closed hf_convex).symm
  -- Rewrite the inner conjugate by Theorem 4.7 and identify the outer pullback with `f`.
  change f =
    conjugate_function
      (conjugate_function h₁ + conjugate_function h₂.toEReal)
      ∘ Module.evalEquiv ℝ E
  calc
    f = biconjugate_function f := hf_biconjugate
    _ =
        conjugate_function
          (conjugate_function h₁ + conjugate_function h₂.toEReal)
          ∘ Module.evalEquiv ℝ E := by
            ext x
            rw [biconjugate_function]
            rw [conjugate_function_infimal_convolution_eq_add_of_proper
              h₁ h₂.toEReal hh₁_proper (Function.toEReal_isProper h₂)]
            simp [Function.comp]

/-- Pointwise companion to Theorem 4.9, spelling the bidual transport as evaluation at
`Module.Dual.eval ℝ E x`. -/
theorem infimal_convolution_eq_dual_conjugate_of_sum_conjugates_apply
    (h₁ : E → EReal) (h₂ : E → ℝ) (hh₁_proper : IsProperExtendedRealFunction h₁)
    (hh₁_convex : is_convex_function h₁)
    (hh₂_convex : ConvexOn ℝ Set.univ h₂)
    (hreal : ∀ x, ∃ r : ℝ, (h₁ □ h₂.toEReal) x = (r : EReal))
    (x : E) :
    (h₁ □ h₂.toEReal) x =
      conjugate_function
        (conjugate_function h₁ + conjugate_function h₂.toEReal)
        (Module.Dual.eval ℝ E x) := by
  simpa [Function.comp] using
    congrArg (fun f : E → EReal ↦ f x)
      (infimal_convolution_eq_dual_conjugate_of_sum_conjugates
        h₁ h₂ hh₁_proper hh₁_convex hh₂_convex hreal)

end
