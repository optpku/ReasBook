/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_16
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_1_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_1_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_5_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_13
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_20
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_23
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_27
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_1_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.FenchelPrimalExtension
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Proposition_5_0_15
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Proposition_5_0_29
import Mathlib.Analysis.Matrix.Order

open scoped ConvexAnalysis DikinEllipsoidNotation Gradient HessianDualLocalNorm HessianLocalNorm
  MatrixOrder WithTopConvexAnalysis

noncomputable section

universe u

open InnerProductSpace

/-- The source quantity `‖∇ f x - ∇ f y‖_x^*`, read through the chapter's canonical Hessian dual
local norm owner at the base point `x`. -/
abbrev gradientDifferenceDualLocalNorm
    {X : Type u} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    (domain : Set X) (f : X → ℝ) [HasPositiveDefiniteHessianOn domain f] (x y : X)
    (hx : x ∈ domain) : ℝ :=
  HessianDualLocalNorm.ofPosDefMem f hx (toDual ℝ X (∇ f x - ∇ f y))

/-- Expanding `gradientDifferenceDualLocalNorm` recovers the chapter's canonical Hessian dual
local norm owner. -/
@[simp] theorem gradientDifferenceDualLocalNorm_def
    {X : Type u} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    (domain : Set X) (f : X → ℝ) [HasPositiveDefiniteHessianOn domain f] (x y : X)
    (hx : x ∈ domain) :
    gradientDifferenceDualLocalNorm domain f x y hx =
      HessianDualLocalNorm.ofPosDefMem f hx (toDual ℝ X (∇ f x - ∇ f y)) :=
  rfl

section OwnerLevel

variable {X : Type u} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
variable [FiniteDimensional ℝ X]
variable {domain : Set X} {Mf : NNReal} {f : X → ℝ} {x y : X}

local notation "F" => fenchelPrimalExtension domain f

-- Semantic recall check: LeanSearch did not expose a direct owner theorem for this
-- conjugate-Hessian comparison, so the source-facing statement is kept explicit here.

/-- Helper for Lemma 5.1.7: if `domain` is open, then the primal slope `∇ f z` maximizes the
Fenchel support functional of `F := fenchelPrimalExtension domain f` at `z`. -/
private lemma gradientSupportIsMaxOn_fenchelPrimalExtension_of_isOpen
    [HasPositiveDefiniteHessianOn domain f]
    (hconv : ConvexOn ℝ domain f)
    (hC2 : ContDiffOn ℝ 2 f domain)
    (hdomOpen : IsOpen domain)
    {z : X} (hz : z ∈ domain) :
    IsMaxOn (fun w : X ↦ inner ℝ (∇ f z) w - withTopRealPart F w) (dom F) z := by
  -- Work on the `+∞`-extension only through its domain-identification `dom F = domain`.
  have hzInterior : z ∈ interior (dom F) := by
    simpa [dom_fenchelPrimalExtension, hdomOpen.interior_eq] using hz
  have hzDomF : z ∈ dom F := interior_subset hzInterior
  have hzContDiffAt : ContDiffAt ℝ 2 f z := hC2.contDiffAt (hdomOpen.mem_nhds hz)
  have hzGradAt : HasGradientAt f (∇ f z) z := by
    exact (hzContDiffAt.differentiableAt (by norm_num)).hasGradientAt
  have hFEventuallyEq : withTopRealPart F =ᶠ[nhds z] f := by
    filter_upwards [hdomOpen.mem_nhds hz] with w hw
    simpa using
      (withTopRealPart_fenchelPrimalExtension_apply_of_mem (Q := domain) (f := f) hw)
  have hzFGradAt : HasGradientAt (withTopRealPart F) (∇ f z) z :=
    hzGradAt.congr_of_eventuallyEq hFEventuallyEq
  have hFConv :
      ConvexOn ℝ (dom F) (withTopRealPart F) := by
    have hFRealEq : Set.EqOn (withTopRealPart F) f (dom F) := by
      intro s hs
      simpa [dom_fenchelPrimalExtension] using
        (withTopRealPart_fenchelPrimalExtension_apply_of_mem (Q := domain) (f := f)
          ((by simpa [dom_fenchelPrimalExtension] using hs) : s ∈ domain))
    exact
      (show ConvexOn ℝ (dom F) f from by
        simpa [dom_fenchelPrimalExtension] using hconv).congr hFRealEq.symm
  have hzSub :
      ∇ f z ∈ ∂ F(z) :=
    gradient_mem_subdifferential_of_hasGradientAt hFConv hzInterior hzFGradAt
  intro w hw
  have hminorantWithTop :
      F w ≥ F z + (inner ℝ (∇ f z) (w - z) : WithTop ℝ) :=
    (mem_subdifferential_iff.mp hzSub).2 hw
  have hminorant :
      withTopRealPart F w ≥ withTopRealPart F z + inner ℝ (∇ f z) (w - z) := by
    rw [← coe_withTopRealPart hw, ← coe_withTopRealPart hzDomF] at hminorantWithTop
    exact_mod_cast hminorantWithTop
  have hsupport :
      inner ℝ (∇ f z) w - withTopRealPart F w ≤
        inner ℝ (∇ f z) z - withTopRealPart F z := by
    rw [inner_sub_right] at hminorant
    linarith
  exact hsupport

/-- Helper for Lemma 5.1.7: if `domain` is open, then the same primal slope `∇ f z` lies in
`dom (F⋆)` and maximizes the dual Fenchel support functional of `F⋆` at the primal point `z`. -/
private lemma dualSupportIsMaxOn_atPrimalGradient_of_isOpen
    [HasPositiveDefiniteHessianOn domain f]
    (hconv : ConvexOn ℝ domain f)
    (hC2 : ContDiffOn ℝ 2 f domain)
    (hdomOpen : IsOpen domain)
    {z : X} (hz : z ∈ domain) :
    ∇ f z ∈ dom (F⋆) ∧
      IsMaxOn
        (fun t : X ↦ inner ℝ z t - extendedRealRealPart (F⋆) t)
        (dom (F⋆)) (∇ f z) := by
  -- Start from the primal support maximizer and evaluate the dual support value at that slope.
  have hzDomF : z ∈ dom F := by
    simpa [dom_fenchelPrimalExtension] using hz
  have hzMax :
      IsMaxOn (fun w : X ↦ inner ℝ (∇ f z) w - withTopRealPart F w) (dom F) z :=
    gradientSupportIsMaxOn_fenchelPrimalExtension_of_isOpen hconv hC2 hdomOpen hz
  have hsDom : ∇ f z ∈ dom (F⋆) :=
    mem_dom_fenchelDual_of_isMaxOn (f := F) (s := ∇ f z) (x := z) hzDomF hzMax
  have hsValue :
      extendedRealRealPart (F⋆) (∇ f z) =
        inner ℝ z (∇ f z) - withTopRealPart F z := by
    simpa [real_inner_comm] using
      extendedRealRealPart_fenchelDual_eq_support_value_of_isMaxOn
        (f := F) (s := ∇ f z) (x := z) hzDomF hzMax
  refine ⟨hsDom, ?_⟩
  intro t ht
  have hdualLowerE :
      (inner ℝ t z : EReal) - withTopToEReal (F z) ≤ (F⋆) t :=
    fenchelDual_lower_bound_of_mem_dom (f := F) (s := t) hzDomF
  have hdualLower :
      inner ℝ z t - withTopRealPart F z ≤ extendedRealRealPart (F⋆) t := by
    exact
      (le_extendedRealRealPart_iff ht).2 <| by
        simpa [real_inner_comm, withTopToEReal_eq_coe_withTopRealPart_of_mem_dom hzDomF,
          ← EReal.coe_sub] using hdualLowerE
  have hsupport :
      inner ℝ z t - extendedRealRealPart (F⋆) t ≤
        inner ℝ z (∇ f z) - extendedRealRealPart (F⋆) (∇ f z) := by
    linarith [hdualLower, hsValue]
  exact hsupport

/-- Helper for Lemma 5.1.7: a `C²` real-valued function differentiates its gradient to the owner
Hessian at the base point. -/
private lemma gradientHasFDerivAt_ofContDiffAt
    {g : X → ℝ} {z : X} (hg : ContDiffAt ℝ 2 g z) :
    HasFDerivAt (∇ g) (hessian g z) z := by
  let D : StrongDual ℝ X →L[ℝ] X :=
    (InnerProductSpace.toDual ℝ X).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfderiv :
      DifferentiableAt ℝ (fderiv ℝ g) z := by
    have hcont : ContDiffAt ℝ 1 (fderiv ℝ g) z :=
      hg.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
    exact hcont.differentiableAt one_ne_zero
  have hgrad :
      DifferentiableAt ℝ (∇ g) z := by
    -- Rewrite the gradient through the Riesz isomorphism before differentiating it.
    simpa [gradient, D] using D.differentiableAt.comp z hfderiv
  -- The chapter owner `hessian` is the derivative of the gradient field.
  simpa [hessian] using hgrad.hasFDerivAt

/-- Helper for Lemma 5.1.7: on an open primal domain, the dual finite real part satisfies
`∇ (extendedRealRealPart (F⋆)) (∇ f z) = z`. -/
private lemma fenchelDualGradient_eq_primalPoint_atPrimalGradient_of_isOpen
    [HasPositiveDefiniteHessianOn domain f]
    (hconv : ConvexOn ℝ domain f)
    (hC2 : ContDiffOn ℝ 2 f domain)
    (hdual : IsSelfConcordantOnWith (dom (F⋆)) Mf (extendedRealRealPart (F⋆)))
    (hdomOpen : IsOpen domain)
    {z : X} (hz : z ∈ domain) :
    ∇ (extendedRealRealPart (F⋆)) (∇ f z) = z := by
  let G : X → WithTop ℝ := fenchelPrimalExtension (dom (F⋆)) (extendedRealRealPart (F⋆))
  have hs :
      ∇ f z ∈ dom (F⋆) ∧
        IsMaxOn
          (fun t : X ↦ inner ℝ z t - extendedRealRealPart (F⋆) t)
          (dom (F⋆)) (∇ f z) :=
    dualSupportIsMaxOn_atPrimalGradient_of_isOpen hconv hC2 hdomOpen hz
  have hsInterior : ∇ f z ∈ interior (dom G) := by
    simpa [G, dom_fenchelPrimalExtension, hdual.isOpen_domain.interior_eq] using hs.1
  have hdualC2 :
      ContDiffOn ℝ 2 (extendedRealRealPart (F⋆)) (dom (F⋆)) :=
    hdual.contDiffOn.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)
  have hGEqOn :
      Set.EqOn (withTopRealPart G) (extendedRealRealPart (F⋆)) (dom (F⋆)) := by
    intro s hsMem
    simpa using
      (withTopRealPart_fenchelPrimalExtension_apply_of_mem
        (Q := dom (F⋆)) (f := extendedRealRealPart (F⋆)) hsMem)
  have hGContDiff :
      ContDiffOn ℝ 2 (withTopRealPart G) (interior (dom G)) := by
    simpa [G, dom_fenchelPrimalExtension, hdual.isOpen_domain.interior_eq] using
      hdualC2.congr hGEqOn
  have hGMax :
      IsMaxOn
        (fun t : X ↦ inner ℝ z t - withTopRealPart G t)
        (dom G) (∇ f z) := by
    intro t ht
    have ht' : t ∈ dom (F⋆) := by
      simpa [G, dom_fenchelPrimalExtension] using ht
    have htValue :
        withTopRealPart G t = extendedRealRealPart (F⋆) t := by
      simpa using
        (withTopRealPart_fenchelPrimalExtension_apply_of_mem
          (Q := dom (F⋆)) (f := extendedRealRealPart (F⋆)) ht')
    have hsValue :
        withTopRealPart G (∇ f z) = extendedRealRealPart (F⋆) (∇ f z) := by
      simpa using
        (withTopRealPart_fenchelPrimalExtension_apply_of_mem
          (Q := dom (F⋆)) (f := extendedRealRealPart (F⋆)) hs.1)
    have htValueWithTop :
        G t = (extendedRealRealPart (F⋆) t : WithTop ℝ) := by
      simpa [G] using
        (fenchelPrimalExtension_apply_of_mem
          (Q := dom (F⋆)) (f := extendedRealRealPart (F⋆)) ht')
    have hsValueWithTop :
        G (∇ f z) = (extendedRealRealPart (F⋆) (∇ f z) : WithTop ℝ) := by
      simpa [G] using
        (fenchelPrimalExtension_apply_of_mem
          (Q := dom (F⋆)) (f := extendedRealRealPart (F⋆)) hs.1)
    -- Re-express the support functional on `dom G` through the already-established dual maximizer.
    simpa [Set.mem_setOf_eq, htValue, hsValue, htValueWithTop, hsValueWithTop] using hs.2 ht'
  have hGGradEq :
      ∇ (withTopRealPart G) (∇ f z) = z :=
    gradient_eq_of_fenchelSupport_isMaxOn_interior
      (f := G) hGContDiff hsInterior hGMax
  have hGGradAt :
      HasGradientAt (withTopRealPart G) z (∇ f z) := by
    have hsContDiffAt :
        ContDiffAt ℝ 2 (withTopRealPart G) (∇ f z) :=
      hGContDiff.contDiffAt (isOpen_interior.mem_nhds hsInterior)
    have hsDifferentiable :
        DifferentiableAt ℝ (withTopRealPart G) (∇ f z) :=
      hsContDiffAt.differentiableAt (by norm_num)
    simpa [hGGradEq] using hsDifferentiable.hasGradientAt
  have hDualEventuallyEq :
      extendedRealRealPart (F⋆) =ᶠ[nhds (∇ f z)] withTopRealPart G := by
    filter_upwards [hdual.isOpen_domain.mem_nhds hs.1] with s hsMem
    simpa using
      (withTopRealPart_fenchelPrimalExtension_apply_of_mem
        (Q := dom (F⋆)) (f := extendedRealRealPart (F⋆)) hsMem).symm
  have hDualGradAt :
      HasGradientAt (extendedRealRealPart (F⋆)) z (∇ f z) :=
    hGGradAt.congr_of_eventuallyEq hDualEventuallyEq
  exact hDualGradAt.gradient

/-- Helper for Lemma 5.1.7: on an open primal domain, the primal gradient always lands in the
effective domain of the Fenchel dual. -/
private lemma primalGradient_mem_dom_fenchelDual_of_isOpen
    [HasPositiveDefiniteHessianOn domain f]
    (hconv : ConvexOn ℝ domain f)
    (hC2 : ContDiffOn ℝ 2 f domain)
    (hdomOpen : IsOpen domain)
    {z : X} (hz : z ∈ domain) :
    ∇ f z ∈ dom (F⋆) :=
  (dualSupportIsMaxOn_atPrimalGradient_of_isOpen
    (domain := domain) (f := f) hconv hC2 hdomOpen hz).1

/-- Helper for Lemma 5.1.7: on an open primal domain, the primal point maximizes the dual support
functional at the primal gradient. -/
private lemma primalPoint_dualSupportIsMaxOn_of_isOpen
    [HasPositiveDefiniteHessianOn domain f]
    (hconv : ConvexOn ℝ domain f)
    (hC2 : ContDiffOn ℝ 2 f domain)
    (hdomOpen : IsOpen domain)
    {z : X} (hz : z ∈ domain) :
    IsMaxOn
      (fun t : X ↦ inner ℝ z t - extendedRealRealPart (F⋆) t)
      (dom (F⋆)) (∇ f z) :=
  (dualSupportIsMaxOn_atPrimalGradient_of_isOpen
    (domain := domain) (f := f) hconv hC2 hdomOpen hz).2

/-- Helper for Lemma 5.1.7: a quadratic family bounded above by `c` yields the discriminant
estimate `a² ≤ b c`. -/
private theorem sq_le_mul_of_quadratic_family
    {a b c : ℝ} (hb : 0 ≤ b)
    (hline : ∀ t : ℝ, 2 * t * a - t ^ (2 : ℕ) * b ≤ c) :
    a ^ (2 : ℕ) ≤ b * c := by
  -- Split on the degenerate quadratic coefficient and test the family at the critical point.
  by_cases hb_zero : b = 0
  · by_cases ha_zero : a = 0
    · simp [ha_zero, hb_zero]
    · have ha_eq_zero : a = 0 := by
        by_contra ha_ne
        have htest := hline ((|c| + 1) / a)
        have hcontr : 2 * (|c| + 1) ≤ c := by
          have hrew : 2 * ((|c| + 1) / a) * a ≤ c := by
            simpa [hb_zero] using htest
          field_simp [ha_ne] at hrew
          linarith
        have hbad : |c| + 2 ≤ 0 := by
          nlinarith [hcontr, le_abs_self c]
        have hpos : 0 < |c| + 2 := by
          nlinarith [abs_nonneg c]
        exact (not_le_of_gt hpos) hbad
      exact (ha_zero ha_eq_zero).elim
  · have hb_pos : 0 < b := lt_of_le_of_ne hb (by simpa [eq_comm] using hb_zero)
    have htest := hline (a / b)
    have hrewrite :
        2 * (a / b) * a - (a / b) ^ (2 : ℕ) * b = a ^ (2 : ℕ) / b := by
      field_simp [hb_zero]
      ring
    have hquot : a ^ (2 : ℕ) / b ≤ c := by
      simpa [hrewrite] using htest
    simpa [mul_comm] using (div_le_iff₀ hb_pos).1 hquot

/-- Helper for Lemma 5.1.7: squaring the local norm recovers the Hessian quadratic form at a
positive Hessian point. -/
private theorem sq_hessianLocalNorm_eq_inner_hessian
    [HasPositiveDefiniteHessianOn domain f]
    {z u : X} (hz : z ∈ domain) :
    ‖u‖[f; z] ^ (2 : ℕ) = inner ℝ u (hessian f z u) := by
  -- Positive definiteness makes the square-root owner exact after squaring.
  simpa [hessianLocalNorm_def] using
    Real.sq_sqrt ((HasPositiveDefiniteHessianOn.hessian_isPositive_of_mem hz).inner_nonneg_right u)

/-- Helper for Lemma 5.1.7: the Fenchel dual Hessian at a primal gradient point is the inverse of
the primal Hessian. -/
private lemma fenchelDualHessian_eq_inversePrimalHessian_atPrimalGradient_of_isOpen
    [HasPositiveDefiniteHessianOn domain f]
    (hconv : ConvexOn ℝ domain f)
    (hC2 : ContDiffOn ℝ 2 f domain)
    (hdual : IsSelfConcordantOnWith (dom (F⋆)) Mf (extendedRealRealPart (F⋆)))
    (hdomOpen : IsOpen domain)
    {z : X} (hz : z ∈ domain) :
    hessian (extendedRealRealPart (F⋆)) (∇ f z) = (hessian f z).inverse := by
  let g : X → ℝ := extendedRealRealPart (F⋆)
  let H : X →L[ℝ] X := hessian f z
  let K : X →L[ℝ] X := hessian g (∇ f z)
  have hzContDiffAt : ContDiffAt ℝ 2 f z :=
    hC2.contDiffAt (hdomOpen.mem_nhds hz)
  have hs : ∇ f z ∈ dom (F⋆) :=
    primalGradient_mem_dom_fenchelDual_of_isOpen
      (domain := domain) (f := f) hconv hC2 hdomOpen hz
  have hgContDiffAt : ContDiffAt ℝ 2 g (∇ f z) := by
    have hgC2 : ContDiffOn ℝ 2 g (dom (F⋆)) :=
      hdual.contDiffOn.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)
    exact hgC2.contDiffAt (hdual.isOpen_domain.mem_nhds hs)
  have hgradComp :
      HasFDerivAt (fun w : X ↦ ∇ g (∇ f w)) (K.comp H) z := by
    -- Differentiate the identity `w ↦ ∇g (∇f w)` at `z` by the chain rule.
    simpa [g, H, K] using
      (gradientHasFDerivAt_ofContDiffAt (g := g) hgContDiffAt).comp z
        (gradientHasFDerivAt_ofContDiffAt (g := f) hzContDiffAt)
  have hgradEventuallyEq :
      (fun w : X ↦ ∇ g (∇ f w)) =ᶠ[nhds z] fun w : X ↦ w := by
    filter_upwards [hdomOpen.mem_nhds hz] with w hw
    simpa [g] using
      fenchelDualGradient_eq_primalPoint_atPrimalGradient_of_isOpen
        (domain := domain) (Mf := Mf) (f := f) hconv hC2 hdual hdomOpen hw
  have hcompEq : K.comp H = (1 : X →L[ℝ] X) := by
    -- The differentiated composition agrees with the derivative of the identity map.
    exact (hgradComp.congr_of_eventuallyEq hgradEventuallyEq.symm).unique (hasFDerivAt_id z)
  have hInv : H.IsInvertible :=
    hessian_isInvertible_of_det_ne_zero
      (HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem hz)
  -- Apply the right-inverse identity to `H.inverse u` to identify the totalized inverse.
  apply ContinuousLinearMap.ext
  intro u
  have hu := congrArg (fun T : X →L[ℝ] X ↦ T (H.inverse u)) hcompEq
  simpa [H, K, ContinuousLinearMap.comp_apply, hInv.self_apply_inverse u] using hu

/-- Helper for Lemma 5.1.7: at a primal gradient point, the dual local norm of the Fenchel dual
matches the primal Hessian dual norm on the same vector. -/
private lemma fenchelDualLocalNorm_eq_hessianDualLocalNorm_atPrimalGradient_of_isOpen
    [HasPositiveDefiniteHessianOn domain f]
    (hconv : ConvexOn ℝ domain f)
    (hC2 : ContDiffOn ℝ 2 f domain)
    (hdual : IsSelfConcordantOnWith (dom (F⋆)) Mf (extendedRealRealPart (F⋆)))
    (hdomOpen : IsOpen domain)
    {z : X} (hz : z ∈ domain) (v : X) :
    ‖v‖[extendedRealRealPart (F⋆); ∇ f z] =
      HessianDualLocalNorm.ofPosDefMem f hz (toDual ℝ X v) := by
  -- Route correction: compare the two local norms only after rewriting the dual Hessian as the
  -- inverse primal Hessian at the gradient point.
  rw [hessianLocalNorm_def, HessianDualLocalNorm.ofPosDefMem_def,
    fenchelDualHessian_eq_inversePrimalHessian_atPrimalGradient_of_isOpen
      (domain := domain) (Mf := Mf) (f := f) hconv hC2 hdual hdomOpen hz]
  congr 1
  simp [InnerProductSpace.toDual_apply_apply]

/-- Helper for Lemma 5.1.7: pairing against a direction is controlled by the Hessian dual local
norm at the base point times the primal local norm of that direction. -/
private theorem absInner_le_dualLocalNorm_mul_localNorm_ofPosDefMem
    [HasPositiveDefiniteHessianOn domain f]
    {z k u : X} (hz : z ∈ domain) :
    |inner ℝ k u| ≤
      HessianDualLocalNorm.ofPosDefMem f hz (toDual ℝ X k) * ‖u‖[f; z] := by
  let H : X →L[ℝ] X := hessian f z
  let w : X := H.inverse k
  let hPos : H.IsPositive := HasPositiveDefiniteHessianOn.hessian_isPositive_of_mem hz
  let hInv : H.IsInvertible :=
    hessian_isInvertible_of_det_ne_zero
      (HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem hz)
  have hHw : H w = k := by
    dsimp [H, w]
    exact hInv.self_apply_inverse k
  have hquad : 0 ≤ inner ℝ u (H u) := hPos.inner_nonneg_right u
  have hpair_nonneg : 0 ≤ inner ℝ k w := by
    -- Rewrite the positive inverse-Hessian quadratic form as the required dual pairing.
    calc
      0 ≤ inner ℝ w (H w) := hPos.inner_nonneg_right w
      _ = inner ℝ k w := by rw [hHw, real_inner_comm]
  have hline :
      ∀ t : ℝ,
        2 * t * inner ℝ k u - t ^ (2 : ℕ) * inner ℝ u (H u) ≤ inner ℝ k w := by
    intro t
    have hnonneg : 0 ≤ inner ℝ (t • u - w) (H (t • u - w)) :=
      hPos.inner_nonneg_right (t • u - w)
    have hcross :
        inner ℝ w (H u) = inner ℝ k u := by
      calc
        inner ℝ w (H u) = inner ℝ (H w) u := by
          simpa [real_inner_comm] using hPos.isSymmetric u w
        _ = inner ℝ k u := by rw [hHw]
    have hrewrite :
        inner ℝ (t • u - w) (H (t • u - w)) =
          t ^ (2 : ℕ) * inner ℝ u (H u) - 2 * t * inner ℝ k u + inner ℝ k w := by
      -- Expand the quadratic form and rewrite the two mixed terms through `H w = k`.
      have hleft :
          inner ℝ (t • u) (H w) = t * inner ℝ k u := by
        rw [hHw, real_inner_comm, inner_smul_right]
      have hright :
          inner ℝ w (t • H u) = t * inner ℝ k u := by
        rw [inner_smul_right, hcross]
      have hdiag :
          inner ℝ w (H w) = inner ℝ k w := by
        rw [hHw, real_inner_comm]
      rw [map_sub, inner_sub_left, inner_sub_right, inner_sub_right]
      rw [ContinuousLinearMap.map_smul, inner_smul_left, inner_smul_right]
      rw [hleft, hright, hdiag]
      have hstar_t : (starRingEnd ℝ) t = t := by simp
      rw [hstar_t]
      ring_nf
    rw [hrewrite] at hnonneg
    nlinarith
  have hsq_raw :
      (inner ℝ k u) ^ (2 : ℕ) ≤ inner ℝ u (H u) * inner ℝ k w := by
    have hsq :=
      sq_le_mul_of_quadratic_family (a := inner ℝ k u) (b := inner ℝ u (H u))
        (c := inner ℝ k w) hquad hline
    simpa [mul_comm] using hsq
  have hdual_sq :
      (HessianDualLocalNorm.ofPosDefMem f hz (toDual ℝ X k)) ^ (2 : ℕ) = inner ℝ k w := by
    rw [HessianDualLocalNorm.ofPosDefMem_def]
    simpa [w, H, pow_two, real_inner_comm, InnerProductSpace.toDual_apply_apply] using
      Real.sq_sqrt hpair_nonneg
  have hlocal_sq : ‖u‖[f; z] ^ (2 : ℕ) = inner ℝ u (H u) := by
    simpa [H] using sq_hessianLocalNorm_eq_inner_hessian (domain := domain) (f := f) hz (u := u)
  have hsq_abs :
      |inner ℝ k u| ^ (2 : ℕ) ≤
        (HessianDualLocalNorm.ofPosDefMem f hz (toDual ℝ X k) * ‖u‖[f; z]) ^ (2 : ℕ) := by
    calc
      |inner ℝ k u| ^ (2 : ℕ) = (inner ℝ k u) ^ (2 : ℕ) := by
        rw [sq_abs]
      _ ≤ inner ℝ u (H u) * inner ℝ k w := hsq_raw
      _ = (HessianDualLocalNorm.ofPosDefMem f hz (toDual ℝ X k)) ^ (2 : ℕ) *
            ‖u‖[f; z] ^ (2 : ℕ) := by
              rw [hdual_sq, hlocal_sq, mul_comm]
      _ = (HessianDualLocalNorm.ofPosDefMem f hz (toDual ℝ X k) * ‖u‖[f; z]) ^ (2 : ℕ) := by
            ring
  have hright_nonneg :
      0 ≤ HessianDualLocalNorm.ofPosDefMem f hz (toDual ℝ X k) * ‖u‖[f; z] := by
    rw [HessianDualLocalNorm.ofPosDefMem_def]
    exact mul_nonneg (Real.sqrt_nonneg _) (hessianLocalNorm_nonneg f z u)
  exact le_of_sq_le_sq hsq_abs hright_nonneg

/-- Helper for Lemma 5.1.7: the Hessian dual local norm is even on covectors at a fixed domain
point. -/
private theorem hessianDualLocalNorm_ofPosDefMem_neg
    [HasPositiveDefiniteHessianOn domain f]
    {z : X} (hz : z ∈ domain) (g : StrongDual ℝ X) :
    HessianDualLocalNorm.ofPosDefMem f hz (-g) =
      HessianDualLocalNorm.ofPosDefMem f hz g := by
  -- Expanding both sides shows that the two minus signs cancel inside the inverse-Hessian pairing.
  rw [HessianDualLocalNorm.ofPosDefMem_def, HessianDualLocalNorm.ofPosDefMem_def]
  simp

/-- Helper for Lemma 5.1.7: applying the primal Hessian to a vector realizes the exact dual local
norm witness at the same base point. -/
private theorem hessianDualLocalNorm_hessian_apply_eq_localNorm_ofPosDefMem
    [HasPositiveDefiniteHessianOn domain f]
    {z u : X} (hz : z ∈ domain) :
    HessianDualLocalNorm.ofPosDefMem f hz (toDual ℝ X (hessian f z u)) = ‖u‖[f; z] := by
  let H : X →L[ℝ] X := hessian f z
  let hPos : H.IsPositive := HasPositiveDefiniteHessianOn.hessian_isPositive_of_mem hz
  let hInv : H.IsInvertible :=
    hessian_isInvertible_of_det_ne_zero
      (HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem hz)
  have hpair_nonneg : 0 ≤ inner ℝ (H u) (H.inverse (H u)) := by
    calc
      0 ≤ inner ℝ u (H u) := by
        simpa [real_inner_comm] using hPos.inner_nonneg_right u
      _ = inner ℝ (H u) (H.inverse (H u)) := by
        rw [hInv.inverse_apply_self u, real_inner_comm]
  -- Evaluate both norms through the same inverse-Hessian pairing and cancel the inverse action.
  rw [HessianDualLocalNorm.ofPosDefMem_def, hessianLocalNorm_def]
  have hcancel : H.inverse (H u) = u := hInv.inverse_apply_self u
  simp [H, InnerProductSpace.toDual_apply_apply, hcancel, real_inner_comm]

/-- Helper for Lemma 5.1.7: a Loewner upper bound on Hessians yields the corresponding local norm
comparison after taking square roots. -/
private theorem hessianLocalNorm_le_mul_of_loewner_upper
    {G : X → ℝ} {x y v : X} {c : ℝ} (hc : 0 ≤ c)
    (hcmp : hessian G y ≤ c • hessian G x) :
    ‖v‖[G; y] ≤ Real.sqrt c * ‖v‖[G; x] := by
  have hgap_pos : (c • hessian G x - hessian G y).IsPositive := by
    rw [← ContinuousLinearMap.le_def]
    exact hcmp
  have hinner_le :
      inner ℝ v (hessian G y v) ≤ c * inner ℝ v (hessian G x v) := by
    have hquad_gap :
        0 ≤ inner ℝ v ((c • hessian G x - hessian G y) v) :=
      hgap_pos.inner_nonneg_right v
    simpa [inner_sub_right, inner_smul_right] using hquad_gap
  rw [hessianLocalNorm_def, hessianLocalNorm_def]
  calc
    Real.sqrt (inner ℝ v (hessian G y v))
        ≤ Real.sqrt (c * inner ℝ v (hessian G x v)) := by
          exact Real.sqrt_le_sqrt hinner_le
    _ = Real.sqrt c * Real.sqrt (inner ℝ v (hessian G x v)) := by
          rw [Real.sqrt_mul hc]

/-- Helper for Lemma 5.1.7: a positive Loewner lower bound can be rewritten as the reciprocal
upper bound needed to compare the local norm at the base point with the local norm at the endpoint.
-/
private theorem hessianLocalNorm_le_mul_of_loewner_lower
    {G : X → ℝ} {x y v : X} {c : ℝ} (hc_pos : 0 < c)
    (hcmp : c • hessian G x ≤ hessian G y) :
    ‖v‖[G; x] ≤ Real.sqrt (c⁻¹) * ‖v‖[G; y] := by
  have hc_nonneg : 0 ≤ c := le_of_lt hc_pos
  have hc_inv_mul : c⁻¹ * c = 1 := by
    field_simp [hc_pos.ne']
  have hcmp' : hessian G x ≤ c⁻¹ • hessian G y := by
    have hgap_pos :
        (hessian G y - c • hessian G x).IsPositive :=
      by
        rw [ContinuousLinearMap.le_def] at hcmp
        simpa using hcmp
    have hscaled_pos :
        (c⁻¹ • (hessian G y - c • hessian G x)).IsPositive :=
      hgap_pos.smul_of_nonneg (inv_nonneg.mpr hc_nonneg)
    have hrewrite :
        c⁻¹ • (hessian G y - c • hessian G x) = c⁻¹ • hessian G y - hessian G x := by
      rw [smul_sub, smul_smul, hc_inv_mul, one_smul]
    rw [ContinuousLinearMap.le_def]
    rw [← hrewrite]
    exact hscaled_pos
  -- After rewriting the operator inequality, apply the upper-bound local-norm comparison.
  exact
    hessianLocalNorm_le_mul_of_loewner_upper
      (G := G) (x := y) (y := x) (v := v) (c := c⁻¹)
      (inv_nonneg.mpr hc_nonneg) hcmp'

/-- Helper for Lemma 5.1.7: transporting Hessian dual local norms from `y` back to `x` along the
Hessian image of `u` yields the linear local-norm comparison `a * ‖u‖[f; x] ≤ ‖u‖[f; y]`. -/
private theorem localNorm_le_of_dualNormTransport_onHessianApply
    [HasPositiveDefiniteHessianOn domain f]
    {x y u : X} (hx : x ∈ domain) (hy : y ∈ domain) {a : ℝ}
    (ha_pos : 0 < a)
    (htransport : ∀ v : X,
      HessianDualLocalNorm.ofPosDefMem f hy (toDual ℝ X v) ≤
        a⁻¹ * HessianDualLocalNorm.ofPosDefMem f hx (toDual ℝ X v)) :
    a * ‖u‖[f; x] ≤ ‖u‖[f; y] := by
  let δx : ℝ := ‖u‖[f; x]
  let δy : ℝ := ‖u‖[f; y]
  have hδx_nonneg : 0 ≤ δx := by
    simpa [δx] using hessianLocalNorm_nonneg f x u
  have hδy_nonneg : 0 ≤ δy := by
    simpa [δy] using hessianLocalNorm_nonneg f y u
  have hdual_transport :
      HessianDualLocalNorm.ofPosDefMem f hy (toDual ℝ X (hessian f x u)) ≤ a⁻¹ * δx := by
    -- Specialize the transport hypothesis at the Hessian image and rewrite the base-point norm.
    calc
      HessianDualLocalNorm.ofPosDefMem f hy (toDual ℝ X (hessian f x u)) ≤
          a⁻¹ * HessianDualLocalNorm.ofPosDefMem f hx (toDual ℝ X (hessian f x u)) :=
        htransport (hessian f x u)
      _ = a⁻¹ * δx := by
        rw [hessianDualLocalNorm_hessian_apply_eq_localNorm_ofPosDefMem
          (domain := domain) (f := f) (z := x) (u := u) hx]
  have hpair_nonneg : 0 ≤ inner ℝ (hessian f x u) u := by
    -- The positive Hessian makes the quadratic form nonnegative before we remove the
    -- absolute value.
    calc
      0 ≤ inner ℝ u (hessian f x u) :=
        (HasPositiveDefiniteHessianOn.hessian_isPositive_of_mem hx).inner_nonneg_right u
      _ = inner ℝ (hessian f x u) u := by rw [real_inner_comm]
  have hpair_bound :
      |inner ℝ (hessian f x u) u| ≤
        HessianDualLocalNorm.ofPosDefMem f hy (toDual ℝ X (hessian f x u)) * δy := by
    -- Bound the same Hessian image at the endpoint metric by the dual-primal Cauchy inequality.
    simpa [δy, real_inner_comm] using
      absInner_le_dualLocalNorm_mul_localNorm_ofPosDefMem
        (domain := domain) (f := f) (z := y) (hz := hy) (k := hessian f x u) (u := u)
  have hsq_bound : δx ^ (2 : ℕ) ≤ (a⁻¹ * δx) * δy := by
    -- Rewrite the quadratic form as a squared local norm and then insert the transported bound.
    calc
      δx ^ (2 : ℕ) = inner ℝ u (hessian f x u) := by
        simpa [δx] using
          sq_hessianLocalNorm_eq_inner_hessian
            (domain := domain) (f := f) (z := x) (u := u) hx
      _ = inner ℝ (hessian f x u) u := by rw [real_inner_comm]
      _ = |inner ℝ (hessian f x u) u| := by rw [abs_of_nonneg hpair_nonneg]
      _ ≤ HessianDualLocalNorm.ofPosDefMem f hy (toDual ℝ X (hessian f x u)) * δy := hpair_bound
      _ ≤ (a⁻¹ * δx) * δy := by
        exact mul_le_mul_of_nonneg_right hdual_transport hδy_nonneg
  by_cases hzero : δx = 0
  · -- The degenerate base norm vanishes, so the desired inequality is immediate.
    change a * δx ≤ δy
    simpa [hzero] using hδy_nonneg
  · have hδx_pos : 0 < δx := lt_of_le_of_ne hδx_nonneg (by simpa [eq_comm] using hzero)
    have hmul : a * (δx ^ (2 : ℕ)) ≤ δx * δy := by
      -- Multiply away the inverse factor before cancelling the positive base norm.
      calc
        a * (δx ^ (2 : ℕ)) ≤ a * ((a⁻¹ * δx) * δy) :=
          mul_le_mul_of_nonneg_left hsq_bound (le_of_lt ha_pos)
        _ = δx * δy := by
          field_simp [ha_pos.ne']
    -- Cancel the positive base norm with a scalar inequality rather than another
    -- rewrite-heavy step.
    nlinarith [hmul, hδx_pos]

/-- Helper for Lemma 5.1.7: transporting Hessian dual local norms from `y` back to `x` with factor
`a⁻¹` should force the corresponding primal quadratic-form lower bound `a^2 ∇²f(x) ⪯ ∇²f(y)`. -/
private theorem quadraticForm_lower_of_dualNormTransport
    [HasPositiveDefiniteHessianOn domain f]
    {x y u : X} (hx : x ∈ domain) (hy : y ∈ domain) {a c : ℝ}
    (ha_pos : 0 < a) (hc : c = a ^ (2 : ℕ))
    (htransport : ∀ v : X,
      HessianDualLocalNorm.ofPosDefMem f hy (toDual ℝ X v) ≤
        a⁻¹ * HessianDualLocalNorm.ofPosDefMem f hx (toDual ℝ X v)) :
    c * inner ℝ u (hessian f x u) ≤ inner ℝ u (hessian f y u) := by
  have hlinear :
      a * ‖u‖[f; x] ≤ ‖u‖[f; y] :=
    localNorm_le_of_dualNormTransport_onHessianApply
      (domain := domain) (f := f) (x := x) (y := y) (u := u) hx hy ha_pos htransport
  have hnormx_nonneg : 0 ≤ ‖u‖[f; x] := hessianLocalNorm_nonneg f x u
  have hnormy_nonneg : 0 ≤ ‖u‖[f; y] := hessianLocalNorm_nonneg f y u
  have hlinear_nonneg : 0 ≤ a * ‖u‖[f; x] := mul_nonneg (le_of_lt ha_pos) hnormx_nonneg
  have hsq :
      (a * ‖u‖[f; x]) ^ (2 : ℕ) ≤ ‖u‖[f; y] ^ (2 : ℕ) := by
    -- Square the linear comparison only after all transport has been eliminated.
    nlinarith [hlinear, hlinear_nonneg, hnormy_nonneg]
  have hquad :
      c * (‖u‖[f; x] ^ (2 : ℕ)) ≤ ‖u‖[f; y] ^ (2 : ℕ) := by
    simpa [hc, pow_two, mul_assoc, mul_left_comm, mul_comm] using hsq
  -- Rewrite both squared local norms back into Hessian quadratic forms.
  rw [← sq_hessianLocalNorm_eq_inner_hessian
      (domain := domain) (f := f) (z := x) (u := u) hx]
  rw [← sq_hessianLocalNorm_eq_inner_hessian
      (domain := domain) (f := f) (z := y) (u := u) hy]
  exact hquad

/-- Helper for Lemma 5.1.7: transporting Hessian dual local norms from `x` to `y` with factor
`a⁻¹` should force the reciprocal primal quadratic-form upper bound
`∇²f(y) ⪯ (a^2)⁻¹ ∇²f(x)`. -/
private theorem quadraticForm_upper_of_dualNormTransport
    [HasPositiveDefiniteHessianOn domain f]
    {x y u : X} (hx : x ∈ domain) (hy : y ∈ domain) {a c : ℝ}
    (ha_pos : 0 < a) (hc : c = a ^ (2 : ℕ))
    (htransport : ∀ v : X,
      HessianDualLocalNorm.ofPosDefMem f hx (toDual ℝ X v) ≤
        a⁻¹ * HessianDualLocalNorm.ofPosDefMem f hy (toDual ℝ X v)) :
    inner ℝ u (hessian f y u) ≤ c⁻¹ * inner ℝ u (hessian f x u) := by
  have hlinear :
      a * ‖u‖[f; y] ≤ ‖u‖[f; x] :=
    localNorm_le_of_dualNormTransport_onHessianApply
      (domain := domain) (f := f) (x := y) (y := x) (u := u) hy hx ha_pos htransport
  have hnormx_nonneg : 0 ≤ ‖u‖[f; x] := hessianLocalNorm_nonneg f x u
  have hnormy_nonneg : 0 ≤ ‖u‖[f; y] := hessianLocalNorm_nonneg f y u
  have hc_pos : 0 < c := by
    rw [hc]
    positivity
  have hlinear_nonneg : 0 ≤ a * ‖u‖[f; y] := mul_nonneg (le_of_lt ha_pos) hnormy_nonneg
  have hsq :
      (a * ‖u‖[f; y]) ^ (2 : ℕ) ≤ ‖u‖[f; x] ^ (2 : ℕ) := by
    -- Square the swapped linear comparison before reintroducing the reciprocal coefficient.
    nlinarith [hlinear, hlinear_nonneg, hnormx_nonneg]
  have hquad :
      c * (‖u‖[f; y] ^ (2 : ℕ)) ≤ ‖u‖[f; x] ^ (2 : ℕ) := by
    simpa [hc, pow_two, mul_assoc, mul_left_comm, mul_comm] using hsq
  rw [← sq_hessianLocalNorm_eq_inner_hessian
      (domain := domain) (f := f) (z := y) (u := u) hy]
  rw [← sq_hessianLocalNorm_eq_inner_hessian
      (domain := domain) (f := f) (z := x) (u := u) hx]
  -- Convert the squared comparison into the reciprocal coefficient form used by the owner theorem.
  have hdiv : ‖u‖[f; y] ^ (2 : ℕ) ≤ ‖u‖[f; x] ^ (2 : ℕ) / c := by
    exact (le_div_iff₀ hc_pos).2 (by simpa [mul_comm] using hquad)
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv

/-- Helper for Lemma 5.1.7: the exact dual-radius inequality
`gradientDifferenceDualLocalNorm domain f x y hx < 1 / M_f` should imply the primal Hessian
comparison with the same exact radius factor. -/
private theorem hessian_loewner_bounds_of_fenchelDual_selfConcordant_of_dualNorm_lt
    [HasPositiveDefiniteHessianOn domain f]
    (hconv : ConvexOn ℝ domain f)
    (hC2 : ContDiffOn ℝ 2 f domain)
    (hdomOpen : IsOpen domain)
    (hdual : IsSelfConcordantOnWith (dom (F⋆)) Mf (extendedRealRealPart (F⋆)))
    (hMf_pos : 0 < (Mf : ℝ))
    (hx : x ∈ domain) (hy : y ∈ domain)
    (hd_lt : gradientDifferenceDualLocalNorm domain f x y hx < 1 / (Mf : ℝ)) :
    let d := gradientDifferenceDualLocalNorm domain f x y hx
    ((1 - (Mf : ℝ) * d) ^ (2 : ℕ)) • hessian f x ≤ hessian f y ∧
      hessian f y ≤ ((1 - (Mf : ℝ) * d) ^ (2 : ℕ))⁻¹ • hessian f x := by
  let g : X → ℝ := extendedRealRealPart (F⋆)
  let sx : X := ∇ f x
  let sy : X := ∇ f y
  let d : ℝ := gradientDifferenceDualLocalNorm domain f x y hx
  let a : ℝ := 1 - (Mf : ℝ) * d
  let c : ℝ := a ^ (2 : ℕ)
  let Hx : X →L[ℝ] X := hessian f x
  let Hy : X →L[ℝ] X := hessian f y
  have hsx : sx ∈ dom (F⋆) :=
    primalGradient_mem_dom_fenchelDual_of_isOpen
      (domain := domain) (f := f) hconv hC2 hdomOpen hx
  have hsy : sy ∈ dom (F⋆) :=
    primalGradient_mem_dom_fenchelDual_of_isOpen
      (domain := domain) (f := f) hconv hC2 hdomOpen hy
  have hd_lt' : d < 1 / (Mf : ℝ) := by
    simpa [d] using hd_lt
  have ha_pos : 0 < a := by
    have hmul_lt_one : (Mf : ℝ) * d < 1 := by
      simpa [d, mul_comm] using (lt_div_iff₀ hMf_pos).1 hd_lt'
    dsimp [a]
    linarith
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    positivity
  have hc_pos : 0 < c := by
    dsimp [c]
    positivity
  have hsqrt_c : Real.sqrt c = a := by
    rw [show c = a ^ (2 : ℕ) by rfl, Real.sqrt_sq_eq_abs]
    exact abs_of_nonneg (le_of_lt ha_pos)
  have hsqrt_cinv : Real.sqrt (c⁻¹) = a⁻¹ := by
    rw [Real.sqrt_inv, hsqrt_c]
  have hHxPos : Hx.IsPositive := by
    simpa [Hx] using HasPositiveDefiniteHessianOn.hessian_isPositive_of_mem hx
  have hHyPos : Hy.IsPositive := by
    simpa [Hy] using HasPositiveDefiniteHessianOn.hessian_isPositive_of_mem hy
  have hnorm_eq : ‖sy - sx‖[g; sx] = d := by
    -- Rewrite the Fenchel-dual local norm at `sx` back to the primal Hessian dual norm at `x`.
    calc
      ‖sy - sx‖[g; sx] =
          HessianDualLocalNorm.ofPosDefMem f hx (toDual ℝ X (sy - sx)) := by
            simpa [g, sx] using
              fenchelDualLocalNorm_eq_hessianDualLocalNorm_atPrimalGradient_of_isOpen
                (domain := domain) (Mf := Mf) (f := f) hconv hC2 hdual hdomOpen
                (z := x) hx (sy - sx)
      _ = HessianDualLocalNorm.ofPosDefMem f hx (toDual ℝ X (-(∇ f x - ∇ f y))) := by
            simp [sy, sx, sub_eq_add_neg]
      _ = HessianDualLocalNorm.ofPosDefMem f hx (toDual ℝ X (∇ f x - ∇ f y)) := by
            -- The fixed-base dual local norm is even, so the sign change disappears.
            simpa using
              hessianDualLocalNorm_ofPosDefMem_neg
                (domain := domain) (f := f) hx (toDual ℝ X (∇ f x - ∇ f y))
      _ = d := by
            rfl
  let rmid : ℝ := (d + 1 / (Mf : ℝ)) / 2
  have hrmid_lt : rmid < 1 / (Mf : ℝ) := by
    dsimp [rmid]
    nlinarith
  have hsy_mid : sy ∈ W⁰[g; sx](rmid) := by
    -- Insert the midpoint radius between the exact dual distance and `1 / M_f`.
    rw [mem_openDikinEllipsoid_iff]
    dsimp [rmid]
    nlinarith [hnorm_eq, hd_lt']
  have hloewner :=
    hdual.hessian_loewner_bounds_of_exact_local_radius hsx hsy hrmid_lt hsy_mid
  have hdual_lower : c • hessian g sx ≤ hessian g sy := by
    simpa [g, sx, sy, c, a, d, hnorm_eq] using hloewner.1
  have hdual_upper : hessian g sy ≤ c⁻¹ • hessian g sx := by
    simpa [g, sx, sy, c, a, d, hnorm_eq] using hloewner.2
  have hdualNormAtY_le (v : X) :
      HessianDualLocalNorm.ofPosDefMem f hy (toDual ℝ X v) ≤
        a⁻¹ * HessianDualLocalNorm.ofPosDefMem f hx (toDual ℝ X v) := by
    have hnorm_cmp :=
      hessianLocalNorm_le_mul_of_loewner_upper
        (G := g) (x := sx) (y := sy) (v := v) (c := c⁻¹)
        (inv_nonneg.mpr hc_nonneg) hdual_upper
    -- Compare the dual local norms by transporting the dual Hessian comparison back to primal
    -- gradient points on the Fenchel-dual side.
    calc
      HessianDualLocalNorm.ofPosDefMem f hy (toDual ℝ X v) = ‖v‖[g; sy] := by
        symm
        simpa [g, sy] using
          fenchelDualLocalNorm_eq_hessianDualLocalNorm_atPrimalGradient_of_isOpen
            (domain := domain) (Mf := Mf) (f := f) hconv hC2 hdual hdomOpen
            (z := y) hy v
      _ ≤ Real.sqrt (c⁻¹) * ‖v‖[g; sx] := hnorm_cmp
      _ = a⁻¹ * ‖v‖[g; sx] := by rw [hsqrt_cinv]
      _ = a⁻¹ * HessianDualLocalNorm.ofPosDefMem f hx (toDual ℝ X v) := by
        rw [fenchelDualLocalNorm_eq_hessianDualLocalNorm_atPrimalGradient_of_isOpen
          (domain := domain) (Mf := Mf) (f := f) hconv hC2 hdual hdomOpen
          (z := x) hx v]
  have hdualNormAtX_le (v : X) :
      HessianDualLocalNorm.ofPosDefMem f hx (toDual ℝ X v) ≤
        a⁻¹ * HessianDualLocalNorm.ofPosDefMem f hy (toDual ℝ X v) := by
    have hnorm_cmp :=
      hessianLocalNorm_le_mul_of_loewner_lower
        (G := g) (x := sx) (y := sy) (v := v) hc_pos hdual_lower
    -- Reuse the same transported dual-side local norm comparison after swapping the endpoints.
    calc
      HessianDualLocalNorm.ofPosDefMem f hx (toDual ℝ X v) = ‖v‖[g; sx] := by
        symm
        simpa [g, sx] using
          fenchelDualLocalNorm_eq_hessianDualLocalNorm_atPrimalGradient_of_isOpen
            (domain := domain) (Mf := Mf) (f := f) hconv hC2 hdual hdomOpen
            (z := x) hx v
      _ ≤ Real.sqrt (c⁻¹) * ‖v‖[g; sy] := hnorm_cmp
      _ = a⁻¹ * ‖v‖[g; sy] := by rw [hsqrt_cinv]
      _ = a⁻¹ * HessianDualLocalNorm.ofPosDefMem f hy (toDual ℝ X v) := by
        rw [fenchelDualLocalNorm_eq_hessianDualLocalNorm_atPrimalGradient_of_isOpen
          (domain := domain) (Mf := Mf) (f := f) hconv hC2 hdual hdomOpen
          (z := y) hy v]
  have hlower_scalar (u : X) :
      c * inner ℝ u (Hx u) ≤ inner ℝ u (Hy u) := by
    -- Package the scalar lower comparison into the dedicated dual-norm transport helper.
    simpa [Hx, Hy] using
      quadraticForm_lower_of_dualNormTransport
        (domain := domain) (f := f) (x := x) (y := y) (u := u) hx hy ha_pos rfl hdualNormAtY_le
  have hupper_scalar (u : X) :
      inner ℝ u (Hy u) ≤ c⁻¹ * inner ℝ u (Hx u) := by
    -- Package the scalar upper comparison into the dedicated dual-norm transport helper.
    simpa [Hx, Hy] using
      quadraticForm_upper_of_dualNormTransport
        (domain := domain) (f := f) (x := x) (y := y) (u := u) hx hy ha_pos rfl hdualNormAtX_le
  constructor
  · -- Convert the scalarized lower bound into the lower Loewner comparison.
    rw [ContinuousLinearMap.le_def, ContinuousLinearMap.isPositive_iff]
    constructor
    · intro u v
      have hsymmX : inner ℝ (Hx u) v = inner ℝ u (Hx v) := by
        simpa using hHxPos.isSymmetric u v
      have hsymmY : inner ℝ (Hy u) v = inner ℝ u (Hy v) := by
        simpa using hHyPos.isSymmetric u v
      calc
        inner ℝ ((Hy - c • Hx) u) v = inner ℝ (Hy u) v - c * inner ℝ (Hx u) v := by
          simp [inner_sub_left, inner_smul_left]
        _ = inner ℝ u (Hy v) - c * inner ℝ u (Hx v) := by
          rw [hsymmY, hsymmX]
        _ = inner ℝ u ((Hy - c • Hx) v) := by
          simp [inner_sub_right, inner_smul_right]
    · intro u
      have hrewrite :
          inner ℝ ((Hy - c • Hx) u) u = inner ℝ u (Hy u) - c * inner ℝ u (Hx u) := by
        calc
          inner ℝ ((Hy - c • Hx) u) u = inner ℝ (Hy u) u - c * inner ℝ (Hx u) u := by
            simp [inner_sub_left, inner_smul_left]
          _ = inner ℝ u (Hy u) - c * inner ℝ u (Hx u) := by
            rw [real_inner_comm (Hy u) u, real_inner_comm (Hx u) u]
      rw [hrewrite]
      linarith [hlower_scalar u]
  · -- Convert the scalarized upper bound into the upper Loewner comparison.
    rw [ContinuousLinearMap.le_def, ContinuousLinearMap.isPositive_iff]
    constructor
    · intro u v
      have hsymmX : inner ℝ (Hx u) v = inner ℝ u (Hx v) := by
        simpa using hHxPos.isSymmetric u v
      have hsymmY : inner ℝ (Hy u) v = inner ℝ u (Hy v) := by
        simpa using hHyPos.isSymmetric u v
      calc
        inner ℝ (((c⁻¹) • Hx - Hy) u) v =
            c⁻¹ * inner ℝ (Hx u) v - inner ℝ (Hy u) v := by
              simp [inner_sub_left, inner_smul_left]
        _ = c⁻¹ * inner ℝ u (Hx v) - inner ℝ u (Hy v) := by
              rw [hsymmX, hsymmY]
        _ = inner ℝ u (((c⁻¹) • Hx - Hy) v) := by
              simp [inner_sub_right, inner_smul_right]
    · intro u
      have hrewrite :
          inner ℝ (((c⁻¹) • Hx - Hy) u) u =
            c⁻¹ * inner ℝ u (Hx u) - inner ℝ u (Hy u) := by
        calc
          inner ℝ (((c⁻¹) • Hx - Hy) u) u =
              c⁻¹ * inner ℝ (Hx u) u - inner ℝ (Hy u) u := by
                simp [inner_sub_left, inner_smul_left]
          _ = c⁻¹ * inner ℝ u (Hx u) - inner ℝ u (Hy u) := by
                rw [real_inner_comm (Hx u) u, real_inner_comm (Hy u) u]
      rw [hrewrite]
      linarith [hupper_scalar u]

/-- Lemma 5.1.7, source-facing form: if `f` is convex and `C²` on an open `domain`, the Fenchel
conjugate of `fenchelPrimalExtension domain f` is self-concordant on its effective domain with
positive constant `M_f`, and the Hessian of `f` is positive definite on `domain`, then the
primal Hessians at `x` and `y` satisfy the standard self-concordant Loewner-order comparison
whenever `d := gradientDifferenceDualLocalNorm domain f x y hx = ‖∇ f x - ∇ f y‖_x^*`
satisfies `d < 1 / M_f`. -/
theorem hessian_loewner_bounds_of_fenchelDual_selfConcordant
    [HasPositiveDefiniteHessianOn domain f]
    (hconv : ConvexOn ℝ domain f)
    (hC2 : ContDiffOn ℝ 2 f domain)
    (hdomOpen : IsOpen domain)
    (hdual : IsSelfConcordantOnWith (dom (F⋆)) Mf (extendedRealRealPart (F⋆)))
    (hMf_pos : 0 < (Mf : ℝ))
    (hx : x ∈ domain) (hy : y ∈ domain)
    (hd_lt : gradientDifferenceDualLocalNorm domain f x y hx < 1 / (Mf : ℝ)) :
    let d := gradientDifferenceDualLocalNorm domain f x y hx
    ((1 - (Mf : ℝ) * d) ^ (2 : ℕ)) • hessian f x ≤ hessian f y ∧
      hessian f y ≤ ((1 - (Mf : ℝ) * d) ^ (2 : ℕ))⁻¹ • hessian f x := by
  -- The public theorem is a thin wrapper around the owner-level proof above.
  simpa using
    hessian_loewner_bounds_of_fenchelDual_selfConcordant_of_dualNorm_lt
      (domain := domain) (Mf := Mf) (f := f) (x := x) (y := y)
      hconv hC2 hdomOpen hdual hMf_pos hx hy hd_lt

end OwnerLevel

section EuclideanBridge

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

variable {domain : Set E} {Mf : NNReal} {f : E → ℝ} {x y : E}

local notation "F" => fenchelPrimalExtension domain f

/-- Internal Euclidean matrix-view helper for the same Hessian comparison. -/
private theorem conjugate_selfConcordant_hessianMatrix_comparison
    [HasPositiveDefiniteHessianOn domain f]
    (hconv : ConvexOn ℝ domain f)
    (hC2 : ContDiffOn ℝ 2 f domain)
    (hdomOpen : IsOpen domain)
    (hdual : IsSelfConcordantOnWith (dom (F⋆)) Mf (extendedRealRealPart (F⋆)))
    (hMf_pos : 0 < (Mf : ℝ))
    (hx : x ∈ domain) (hy : y ∈ domain)
    (hd_lt : gradientDifferenceDualLocalNorm domain f x y hx < 1 / (Mf : ℝ)) :
    let d := gradientDifferenceDualLocalNorm domain f x y hx
    (((1 - (Mf : ℝ) * d) ^ (2 : ℕ)) • ∇² f x ≤ ∇² f y) ∧
      (∇² f y ≤ ((1 - (Mf : ℝ) * d) ^ (2 : ℕ))⁻¹ • ∇² f x) := by
  -- The Euclidean matrix view is just the same owner-level comparison specialized to `E`.
  simpa using
    hessian_loewner_bounds_of_fenchelDual_selfConcordant
      (domain := domain) (Mf := Mf) (f := f) (x := x) (y := y)
      hconv hC2 hdomOpen hdual hMf_pos hx hy hd_lt

end EuclideanBridge

end
