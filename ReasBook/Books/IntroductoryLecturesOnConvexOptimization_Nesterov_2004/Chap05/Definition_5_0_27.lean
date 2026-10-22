/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_1_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_8
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_5_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped ConvexAnalysis WithTopConvexAnalysis

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Definition 5.0.27 lies in the chapter's Fenchel-conjugacy domain.

Sampled owner-style declarations:
- `extendedRealEffectiveDomain` / `dom` in `Chap03/Definition_3_1_1_2`, the chapter owner for the
  effective domain of an `EReal`-valued function;
- `fenchelDual` in `Chap03/Definition_3_1_2_1`, the source-facing owner for the Fenchel conjugate
  of a `WithTop ℝ`-valued function on a real inner-product space;
- `fenchelDual_apply_eq_sSup_image_dom` in `Chap03/Definition_3_8`, the canonical bridge that
  restricts the defining supremum to `dom f`;
- `fenchelConjugate` in `Chap06/Definition_6_1`, the core dual-space owner underlying
  `fenchelDual`.

Best owner abstraction:
- source-facing: `fenchelDual`, written on the theorem surface as `f⋆`;
- core/canonical: `fenchelConjugate`;
- bridge/view: the `dom`-restricted supremum formula and the finite real part `withTopRealPart`.

Primitive data:
- `f : E → WithTop ℝ`.

Derived API:
- the recalled owner `f⋆`;
- the recalled dual effective domain `dom (f⋆)`;
- the recalled `dom`-restricted supremum formula `fenchelDual_apply_eq_sSup_image_dom`;
- the textbook bounded-below characterization of `dom (f⋆)` under `dom f` nonempty.

Source/core/bridge triage:
- source-facing: Definition 5.0.27, the Fenchel conjugate and its textbook dual domain on `ℝⁿ`;
- core/canonical: `fenchelConjugate`;
- bridge/view: the Euclidean specialization via `innerₗ E`.

This file is recall-first for the conjugate itself: the Chapter 3 owner already supplies the exact
source-facing Fenchel-dual construction and the canonical `dom`-restricted supremum formula, so
the previous local duplicate definitions are deleted. The dual effective domain is likewise
recalled directly as `dom (f⋆)`; only the textbook bounded-below condition remains as a companion
bridge theorem, because it is not the owner and it needs a nonempty-domain hypothesis to match the
canonical effective domain.
-/

/- Definition 5.0.27 recalls the source-facing Fenchel-dual owner on `ℝⁿ`. -/
recall fenchelDual

section

variable (f : E → WithTop ℝ)

/- Definition 5.0.27 also recalls the canonical dual effective domain surface `dom (f⋆)`. -/
#check dom (f⋆)

end

section

variable (f : E → WithTop ℝ) (s : E)

/- Restricting the recalled Fenchel-dual supremum to `dom f` gives the textbook formula. -/
#check fenchelDual_apply_eq_sSup_image_dom f s

end

section

variable {F : Type u} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Helper for Definition 5.0.27: dual-domain membership is equivalent to bounded-above of the
Fenchel support image on the primal effective domain. -/
-- Proof sketch: `s ∈ dom (f⋆)` means `(f⋆) s` is a finite `EReal`. Rewriting `(f⋆) s` as the
-- supremum over `dom f`, finiteness of that supremum is equivalent to a real upper bound for the
-- support values `⟪s, x⟫ - withTopRealPart f x`.
lemma mem_dom_fenchelDual_iff_bddAbove_support_image
    {f : F → WithTop ℝ} (hdom : (dom f).Nonempty) {s : F} :
    s ∈ dom (f⋆) ↔
      BddAbove ((fun x : F ↦ inner ℝ s x - withTopRealPart f x) '' dom f) := by
  constructor
  · intro hs
    rcases mem_extendedRealEffectiveDomain_iff.mp hs with ⟨hs_ne_top, hs_ne_bot⟩
    refine ⟨((f⋆) s).toReal, ?_⟩
    rintro z ⟨x, hx, rfl⟩
    -- Each support value is one term in the defining supremum of `(f⋆) s`.
    have hle : (((inner ℝ s x - withTopRealPart f x : ℝ) : EReal)) ≤ (f⋆) s := by
      rw [fenchelDual_apply_eq_sSup_image_dom]
      simpa only [withTopToEReal_eq_coe_withTopRealPart_of_mem_dom (f := f) hx,
        ← EReal.coe_sub] using
        (show ((inner ℝ s x : EReal) - withTopToEReal (f x)) ≤
            sSup ((fun y : F ↦ (inner ℝ s y : EReal) - withTopToEReal (f y)) '' dom f) from
          le_sSup ⟨x, hx, rfl⟩)
    -- Convert the finite `EReal` upper bound back to a real upper bound.
    have hsupport_toReal :
        ((((inner ℝ s x - withTopRealPart f x : ℝ) : EReal)).toReal) ≤ ((f⋆) s).toReal := by
      exact EReal.toReal_le_toReal hle (EReal.coe_ne_bot _) hs_ne_top
    have hsupport_real :
        inner ℝ s x - withTopRealPart f x ≤ ((f⋆) s).toReal := by
      have hleft :
          ((((inner ℝ s x - withTopRealPart f x : ℝ) : EReal)).toReal) =
            inner ℝ s x - (f x).untop₀ := by
        have hcoefs :
            (((inner ℝ s x - withTopRealPart f x : ℝ) : EReal)) =
              (((inner ℝ s x - (f x).untop₀ : ℝ) : EReal)) := by
          simp [withTopRealPart]
        exact_mod_cast congrArg EReal.toReal hcoefs
      have hsupport_sub :
          inner ℝ s x - (f x).untop₀ ≤ ((f⋆) s).toReal := by
        rw [← hleft]
        exact hsupport_toReal
      simpa [withTopRealPart] using hsupport_sub
    exact hsupport_real
  · rintro ⟨b, hb⟩
    rcases hdom with ⟨x, hx⟩
    have hs_ne_bot : (f⋆) s ≠ ⊥ := fenchelDual_ne_bot_of_mem_dom (f := f) (s := s) hx
    have hs_le : (f⋆) s ≤ (b : EReal) := by
      -- A real upper bound on the image bounds the supremum term-by-term.
      rw [fenchelDual_apply_eq_sSup_image_dom]
      refine sSup_le ?_
      rintro y ⟨x, hx, rfl⟩
      have hxy : inner ℝ s x - withTopRealPart f x ≤ b := hb ⟨x, hx, rfl⟩
      simpa only [
        withTopToEReal_eq_coe_withTopRealPart_of_mem_dom (f := f) hx,
        ← EReal.coe_sub] using
        (show (((inner ℝ s x - withTopRealPart f x : ℝ) : EReal)) ≤ (b : EReal) from by
          exact_mod_cast hxy)
    have hs_ne_top : (f⋆) s ≠ ⊤ := by
      exact ne_of_lt (lt_of_le_of_lt hs_le (EReal.coe_lt_top b))
    exact mem_extendedRealEffectiveDomain_iff.mpr ⟨hs_ne_top, hs_ne_bot⟩

/-- Helper for Definition 5.0.27: bounded-above of the support image is equivalent to bounded-below
of the affine-gap image obtained by negating those real values. -/
-- Proof sketch: the two images differ by multiplication by `-1`, so an upper bound `b` for one
-- image is the same as the lower bound `-b` for the other.
lemma bddAbove_support_image_iff_bddBelow_affine_gap_image
    {f : F → WithTop ℝ} {s : F} :
    BddAbove ((fun x : F ↦ inner ℝ s x - withTopRealPart f x) '' dom f) ↔
      BddBelow ((fun x : F ↦ withTopRealPart f x - inner ℝ s x) '' dom f) := by
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨-b, ?_⟩
    rintro z ⟨x, hx, rfl⟩
    have hx_bound : inner ℝ s x - withTopRealPart f x ≤ b := hb ⟨x, hx, rfl⟩
    linarith
  · rintro ⟨b, hb⟩
    refine ⟨-b, ?_⟩
    rintro z ⟨x, hx, rfl⟩
    have hx_bound : b ≤ withTopRealPart f x - inner ℝ s x := hb ⟨x, hx, rfl⟩
    linarith

/-- On a real inner-product space, under the nonempty-domain hypothesis needed to exclude the
empty-image edge case, membership in the canonical dual effective domain `dom (f⋆)` is equivalent
to the textbook condition that `x ↦ f(x) - ⟪s, x⟫` is bounded below on `dom f`. -/
-- Proof sketch: rewrite `(f⋆) s` with `fenchelDual_apply_eq_sSup_image_dom`; under
-- `(dom f).Nonempty`, the displayed image set is nonempty and consists of finite real values, so
-- finiteness of the supremum is equivalent to boundedness above of
-- `x ↦ inner ℝ s x - withTopRealPart f x`, equivalently to boundedness below of
-- `x ↦ withTopRealPart f x - inner ℝ s x`.
theorem mem_dom_fenchelDual_iff {f : F → WithTop ℝ} (hdom : (dom f).Nonempty) {s : F} :
    s ∈ dom (f⋆) ↔
      BddBelow ((fun x : F ↦ withTopRealPart f x - inner ℝ s x) '' dom f) := by
  -- First convert dual-domain membership into boundedness above of the Fenchel support image.
  rw [mem_dom_fenchelDual_iff_bddAbove_support_image (f := f) hdom]
  -- Then flip signs to match the textbook bounded-below affine-gap formulation.
  exact bddAbove_support_image_iff_bddBelow_affine_gap_image (f := f) (s := s)

end

end
