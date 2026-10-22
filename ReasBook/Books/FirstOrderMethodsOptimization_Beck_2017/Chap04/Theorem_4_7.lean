/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_5
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_8
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Definition_4_1
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Definition_4_8
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Theorem_4_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/- This item is `source-facing` in the chapter conjugacy calculus. The `core/canonical` owner
declarations already live upstream in the project: Chapter 2 owns `infimal_convolution`, while
Definition 4.1 owns `conjugate_function` and its primal-space notation `f∗`. This file therefore
keeps the source theorem together with the minimal reusable owner-form companion, reusing those
owners directly. -/
recall infimal_convolution
recall conjugate_function

-- Semantic recall note: `conjugate_function` is the Chapter 4 owner for Fenchel conjugates on the
-- dual space `Module.Dual ℝ E`, while the postfix notation `f∗` is only the derived primal-space
-- pullback along `InnerProductSpace.toDualMap ℝ E`. The main labeled theorem therefore stays on
-- the owner-level dual surface.
-- Proof sketch: expand `conjugate_function (h₁ □ h₂)` using the definition of infimal
-- convolution, rewrite the pairing against `x = u + v`, and separate the resulting supremum into
-- the two conjugate suprema for `h₁` and `h₂`.
/-- Helper for Theorem 4.7: subtracting an indexed infimum from a finite real is the indexed
supremum of the pointwise subtractions. -/
lemma erealReal_sub_iInf_eq_iSup_sub {ι : Sort*} (r : ℝ) (φ : ι → EReal) :
    ((r : EReal) - ⨅ i, φ i) = ⨆ i, ((r : EReal) - φ i) := by
  -- Push the antitone map `t ↦ r - t` through the indexed infimum.
  have hcont : ContinuousAt (fun t : EReal ↦ (r : EReal) - t) (⨅ i, φ i) := by
    let F : EReal → EReal × EReal := fun z ↦ ((r : EReal), -z)
    have hF : ContinuousAt F (⨅ i, φ i) := by
      simpa [F] using continuousAt_const.prodMk (continuous_neg.continuousAt)
    have hadd :
        ContinuousAt (fun p : EReal × EReal ↦ p.1 + p.2) (F (⨅ i, φ i)) := by
      simpa [F] using
        EReal.continuousAt_add (p := ((r : EReal), -(⨅ i, φ i)))
          (.inl (EReal.coe_ne_top r)) (.inl (EReal.coe_ne_bot r))
    simpa [sub_eq_add_neg] using
      hadd.comp hF
  have hantitone : Antitone fun t : EReal ↦ (r : EReal) - t := by
    intro a b hab
    simpa [sub_eq_add_neg] using add_le_add_right (show -b ≤ -a by simpa using hab) (r : EReal)
  simpa [Function.comp, sub_eq_add_neg] using
    (Antitone.map_iInf_of_continuousAt (g := φ) hcont hantitone (by simp))

/-- Helper for Theorem 4.7: after the change of variables `x = u + v`, the infimal-convolution
conjugate integrand splits into the two Fenchel perturbation terms. -/
lemma infimalConvolutionConjugateIntegrand_eq_sum
    (h₁ h₂ : E → EReal) (hh₁_ne_bot : ∀ x, h₁ x ≠ ⊥) (hh₂_ne_bot : ∀ x, h₂ x ≠ ⊥)
    (y : Module.Dual ℝ E) (u v : E) :
    (y (u + v) : EReal) - (h₁ u + h₂ v) =
      ((y u : EReal) - h₁ u) + ((y v : EReal) - h₂ v) := by
  -- Separate the linear pairing and the function sum into their two summand contributions.
  have hpair : ((y (u + v) : ℝ) : EReal) = (y u : EReal) + (y v : EReal) := by
    simp [map_add, EReal.coe_add]
  rw [hpair]
  rw [sub_eq_add_neg]
  rw [EReal.neg_add (.inl (hh₁_ne_bot u)) (.inr (hh₂_ne_bot v))]
  -- The remaining goal is only reassociation into the two conjugate terms.
  simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Helper for Theorem 4.7: the double supremum coming from the conjugate of the infimal
convolution can be rewritten as the product-index supremum of the separated Fenchel terms. -/
lemma infimalConvolutionConjugate_iSup_eq_productObjective
    (h₁ h₂ : E → EReal) (hh₁_ne_bot : ∀ x, h₁ x ≠ ⊥) (hh₂_ne_bot : ∀ x, h₂ x ≠ ⊥)
    (y : Module.Dual ℝ E) :
    (⨆ x, ⨆ u, (y x : EReal) - (h₁ u + h₂ (x - u))) =
      ⨆ p : E × E, (((y p.1 : EReal) - h₁ p.1) + ((y p.2 : EReal) - h₂ p.2)) := by
  rw [iSup_prod']
  refine le_antisymm ?_ ?_
  · -- Send each `(x,u)` term to the product witness `(u, x - u)`.
    refine iSup_le fun xu ↦ ?_
    have hdecomp : xu.2 + (xu.1 - xu.2) = xu.1 := by
      simp [sub_eq_add_neg, add_left_comm]
    calc
      (y xu.1 : EReal) - (h₁ xu.2 + h₂ (xu.1 - xu.2))
        = (y (xu.2 + (xu.1 - xu.2)) : EReal) - (h₁ xu.2 + h₂ (xu.1 - xu.2)) := by
            rw [hdecomp]
      _ = ((y xu.2 : EReal) - h₁ xu.2) + ((y (xu.1 - xu.2) : EReal) - h₂ (xu.1 - xu.2)) :=
            infimalConvolutionConjugateIntegrand_eq_sum h₁ h₂ hh₁_ne_bot hh₂_ne_bot y xu.2
              (xu.1 - xu.2)
      _ ≤ ⨆ p : E × E, (((y p.1 : EReal) - h₁ p.1) + ((y p.2 : EReal) - h₂ p.2)) := by
            exact le_iSup_of_le (xu.2, xu.1 - xu.2) le_rfl
  · -- Recover the `(x,u)` witness from the product point `(u,v)` by setting `x = u + v`.
    refine iSup_le fun p ↦ ?_
    have hsub : (p.1 + p.2) - p.1 = p.2 := by
      simp [sub_eq_add_neg, add_assoc]
    refine le_iSup_of_le (p.1 + p.2, p.1) ?_
    calc
      ((y p.1 : EReal) - h₁ p.1) + ((y p.2 : EReal) - h₂ p.2)
        = (y (p.1 + p.2) : EReal) - (h₁ p.1 + h₂ p.2) := by
            symm
            exact infimalConvolutionConjugateIntegrand_eq_sum h₁ h₂ hh₁_ne_bot hh₂_ne_bot y p.1 p.2
      _ = (y (p.1 + p.2) : EReal) - (h₁ p.1 + h₂ ((p.1 + p.2) - p.1)) := by
            rw [hsub]
      _ ≤ (y (p.1 + p.2) : EReal) - (h₁ p.1 + h₂ ((p.1 + p.2) - p.1)) := by
            exact le_rfl

/-- Theorem 4.7: ruling out the value `⊥` for both summands is enough for the Fenchel conjugate of
their infimal convolution to split as the pointwise sum of the conjugates. -/
theorem conjugate_function_infimal_convolution_eq_add
    (h₁ h₂ : E → EReal) (hh₁_ne_bot : ∀ x, h₁ x ≠ ⊥) (hh₂_ne_bot : ∀ x, h₂ x ≠ ⊥) :
    conjugate_function (h₁ □ h₂) = conjugate_function h₁ + conjugate_function h₂ := by
  funext y
  -- Expand the conjugate of the infimal convolution into a separated `iSup` expression.
  calc
    conjugate_function (h₁ □ h₂) y
      = ⨆ x : E, (y x : EReal) - (h₁ □ h₂) x := by
          rw [conjugate_function_apply, sSup_range]
    _ = ⨆ x : E, (y x : EReal) - ⨅ u : E, h₁ u + h₂ (x - u) := by
          simp [infimal_convolution_apply]
    _ = ⨆ x : E, ⨆ u : E, (y x : EReal) - (h₁ u + h₂ (x - u)) := by
          refine iSup_congr fun x ↦ ?_
          simpa using
            (erealReal_sub_iInf_eq_iSup_sub (r := y x) (φ := fun u : E ↦ h₁ u + h₂ (x - u)))
    _ = ⨆ p : E × E, (((y p.1 : EReal) - h₁ p.1) + ((y p.2 : EReal) - h₂ p.2)) := by
          exact infimalConvolutionConjugate_iSup_eq_productObjective h₁ h₂ hh₁_ne_bot hh₂_ne_bot y
    _ = (⨆ u : E, (y u : EReal) - h₁ u) + ⨆ v : E, (y v : EReal) - h₂ v := by
          simpa using
            (ereal_iSup_add_eq_iSup_prod
              (u := fun u : E ↦ (y u : EReal) - h₁ u)
              (v := fun v : E ↦ (y v : EReal) - h₂ v)).symm
    _ = conjugate_function h₁ y + conjugate_function h₂ y := by
          rw [conjugate_function_apply, conjugate_function_apply, sSup_range, sSup_range]
    _ = (conjugate_function h₁ + conjugate_function h₂) y := by
          rfl

/-- Source-facing properness corollary for Theorem 4.7: for two proper extended-real-valued
functions, the owner-level Fenchel conjugate of their infimal convolution on the dual space equals
the pointwise sum of their conjugates:
`conjugate_function (h₁ □ h₂) = conjugate_function h₁ + conjugate_function h₂`. -/
theorem conjugate_function_infimal_convolution_eq_add_of_proper
    (h₁ h₂ : E → EReal) (hh₁_proper : IsProperExtendedRealFunction h₁)
    (hh₂_proper : IsProperExtendedRealFunction h₂) :
    conjugate_function (h₁ □ h₂) = conjugate_function h₁ + conjugate_function h₂ :=
  conjugate_function_infimal_convolution_eq_add h₁ h₂ hh₁_proper.ne_bot hh₂_proper.ne_bot

end
