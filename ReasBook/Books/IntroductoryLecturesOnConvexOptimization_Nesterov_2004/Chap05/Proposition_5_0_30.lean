/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_16
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_1_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_27
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Proposition_5_0_29

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ConvexAnalysis Gradient WithTopConvexAnalysis

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Proposition 5.0.30 lies in the chapter's Fenchel-conjugacy / third-order differential-calculus
domain.

Sampled owner-style declarations:
* `fenchelDual` / notation `f⋆` in `Definition_5_0_27`, the chapter owner for the Fenchel dual;
* `dom` and `extendedRealRealPart` in `Chap03/Definition_3_1_1_3`, the canonical finite-value
  domain / finite-real-part owners for `EReal`-valued functions;
* `IsMaxOn`, the canonical maximizer predicate for the Fenchel support functional
  `y ↦ ⟪s, y⟫ - f y` on `dom f`;
* `gradient` / notation `∇`, the canonical first-order owner for the branch equation
  `∇ f (xStar s) = s`;
* `hessian` in `Chap01/Definition_1_4_16`, the intrinsic second-order owner;
* `fderiv ℝ (hessian g) x h` in `Definition_5_0_8`, the chapter owner for third derivatives;
* `fenchelConjugate_hessian_eq_inverse` in `Proposition_5_0_29`, the chapter owner for the
  preceding inverse-Hessian identity on `dom (f⋆)`;
* `exists_continuousLinearEquiv_fderiv_symm_eq` in mathlib, the canonical local-inverse
  differentiability bridge for genuine invertible Fréchet derivatives.

Best owner abstraction:
* source-facing: the third-derivative formula for `extendedRealRealPart (f⋆)` along a chosen
  Fenchel-maximizer branch `xStar : E → E` on `dom (f⋆)`;
* core/canonical: `extendedRealRealPart (f⋆)`, `hessian`, `∇`, and `IsMaxOn`;
* bridge/view: the prior identity
  `hessian (extendedRealRealPart (f⋆)) s = (hessian (withTopRealPart f) (xStar s)).inverse`.

Primitive data:
* the primal `WithTop ℝ`-valued function `f`;
* a branch `xStar : E → E` on `dom (f⋆)`;
* the source-facing facts that `xStar s` is the Fenchel-support maximizer at `s`,
  lies in `interior (dom f)`, and obeys the inverse-Hessian identity
  `hessian (extendedRealRealPart (f⋆)) s = (hessian (withTopRealPart f) (xStar s)).inverse`.

Derived API:
* the branch derivative identity
  `HasFDerivAt xStar (hessian (extendedRealRealPart (f⋆)) s) s`, exposed as the public bridge
  theorem `fenchelConjugate_maximizerBranch_hasFDerivAt`; in Lean the needed branch regularity is
  made explicit by assuming the chosen maximizer branch is continuous and locally right-inverts
  the primal gradient near each dual-domain slope;
* the third-derivative formula for `extendedRealRealPart (f⋆)` under the source hypotheses.

Source/core/bridge triage:
* source-facing: the branchwise `D³ f_*` formula on `dom (f⋆)`;
* core/canonical: the dual Hessian owner `hessian (extendedRealRealPart (f⋆))`;
* bridge/view: the reusable inverse-Hessian identity supplied separately by
  `fenchelConjugate_hessian_eq_inverse`, together with the branch-differentiability bridge theorem
  `fenchelConjugate_maximizerBranch_hasFDerivAt`.

The previous version strengthened the source statement by trying to derive the inverse-Hessian
identity from Proposition 5.0.29-style hypotheses instead of taking that identity as a primitive
assumption. This repair keeps the chosen branch `xStar` source-facing, restores the textbook
premise that the dual Hessian is already identified with the inverse primal Hessian on
`dom (f⋆)`, and leaves the stronger local tangent/branch-derivative package in the companion
within-domain and open-domain helper theorems used to prove the ambient `fderiv` formula. -/

section

-- Proof sketch: keep the auxiliary branch-differentiability bridge theorem separate, but state
-- Proposition 5.0.30 itself with the source assumptions that `xStar` is a maximizing branch and
-- already obeys the inverse-Hessian identity on `dom (f⋆)`.
-- The third-derivative formula is then the formal derivative of that assumed identity along the
-- branch.
/-- Helper for Proposition 5.0.30: the chosen interior Fenchel-maximizer branch satisfies the
source first-order stationarity equation `∇ f (xStar s) = s`. -/
lemma maximizerBranch_gradient_eq_slope
    {f : E → WithTop ℝ} {xStar : E → E}
    (hf_contDiff : ContDiffOn ℝ 2 (withTopRealPart f) (interior (dom f)))
    (hxStar_mem : ∀ ⦃s : E⦄, s ∈ dom (f⋆) → xStar s ∈ interior (dom f))
    (hxStar_isMaximizer :
      ∀ ⦃s : E⦄, s ∈ dom (f⋆) →
        IsMaxOn (fun y : E ↦ inner ℝ s y - withTopRealPart f y) (dom f) (xStar s))
    {s : E} (hs : s ∈ dom (f⋆)) :
    ∇ (withTopRealPart f) (xStar s) = s := by
  -- Reinterpret the selected branch point as the interior Fenchel-support maximizer from
  -- Proposition 5.0.29's first-order helper.
  exact
    gradient_eq_of_fenchelSupport_isMaxOn_interior hf_contDiff (hxStar_mem hs)
      (hxStar_isMaximizer hs)

/-- Helper for Proposition 5.0.30: the chosen branch point belongs to the primal effective
domain, so the uniqueness hypothesis for Fenchel-support maximizers can be applied directly at
`xStar s`. -/
lemma maximizerBranch_mem_dom
    {f : E → WithTop ℝ} {xStar : E → E}
    (hxStar_mem : ∀ ⦃s : E⦄, s ∈ dom (f⋆) → xStar s ∈ interior (dom f))
    {s : E} (hs : s ∈ dom (f⋆)) :
    xStar s ∈ dom f := by
  -- Interior membership immediately upgrades to membership in the underlying effective domain.
  exact interior_subset (hxStar_mem hs)

/-- Helper for Proposition 5.0.30: the selected unique Fenchel-maximizer branch gives the dual
gradient formula `∇ f⋆(s) = xStar s` at each dual-domain point once the ambient
closed-convex/self-concordant hypotheses from Proposition 5.0.29 are restored. -/
lemma maximizerBranch_hasGradientAt_fenchelConjugate
    {f : E → WithTop ℝ} {xStar : E → E}
    (hf_closedConvex : ClosedConvexFunction f)
    (hself : IsSelfConcordantOn (interior (dom f)) (withTopRealPart f))
    (hinterior_nonempty : (interior (dom f)).Nonempty)
    (hxStar_mem : ∀ ⦃s : E⦄, s ∈ dom (f⋆) → xStar s ∈ interior (dom f))
    (hxStar_isMaximizer :
      ∀ ⦃s : E⦄, s ∈ dom (f⋆) →
        IsMaxOn (fun y : E ↦ inner ℝ s y - withTopRealPart f y) (dom f) (xStar s))
    (hxStar_unique :
      ∀ ⦃s x : E⦄, s ∈ dom (f⋆) → x ∈ dom f →
        IsMaxOn (fun y : E ↦ inner ℝ s y - withTopRealPart f y) (dom f) x → x = xStar s)
    {s : E} (hs : s ∈ dom (f⋆)) :
    HasGradientAt (extendedRealRealPart (f⋆)) (xStar s) s := by
  -- Reuse Proposition 5.0.29's whole-space gradient theorem at the chosen maximizing branch.
  exact
    fenchelConjugate_hasGradientAt
      hf_closedConvex hself hinterior_nonempty
      hxStar_mem hxStar_isMaximizer hxStar_unique hs

/-- Helper for Proposition 5.0.30: the dual gradient at `s` is exactly the selected maximizer
`xStar s` under the same Proposition 5.0.29 ambient hypotheses. -/
lemma maximizerBranch_dualGradient_eq
    {f : E → WithTop ℝ} {xStar : E → E}
    (hf_closedConvex : ClosedConvexFunction f)
    (hself : IsSelfConcordantOn (interior (dom f)) (withTopRealPart f))
    (hinterior_nonempty : (interior (dom f)).Nonempty)
    (hxStar_mem : ∀ ⦃s : E⦄, s ∈ dom (f⋆) → xStar s ∈ interior (dom f))
    (hxStar_isMaximizer :
      ∀ ⦃s : E⦄, s ∈ dom (f⋆) →
        IsMaxOn (fun y : E ↦ inner ℝ s y - withTopRealPart f y) (dom f) (xStar s))
    (hxStar_unique :
      ∀ ⦃s x : E⦄, s ∈ dom (f⋆) → x ∈ dom f →
        IsMaxOn (fun y : E ↦ inner ℝ s y - withTopRealPart f y) (dom f) x → x = xStar s)
    {s : E} (hs : s ∈ dom (f⋆)) :
    ∇ (extendedRealRealPart (f⋆)) s = xStar s := by
  -- Read the pointwise gradient value from the gradient witness on the Fenchel conjugate.
  exact
    (maximizerBranch_hasGradientAt_fenchelConjugate
      hf_closedConvex hself hinterior_nonempty hxStar_mem hxStar_isMaximizer
      hxStar_unique hs).gradient

/-- Helper for Proposition 5.0.30: a `C³` primal finite real part gives a `C²` primal gradient
map at the point where the inverse-function theorem is applied. -/
private lemma primalGradient_contDiffAt_of_contDiffAt_three
    {f : E → WithTop ℝ} {x : E}
    (hcontAt : ContDiffAt ℝ 3 (withTopRealPart f) x) :
    ContDiffAt ℝ 2 (∇ (withTopRealPart f)) x := by
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfderiv_C2 : ContDiffAt ℝ 2 (fderiv ℝ (withTopRealPart f)) x := by
    -- First differentiate the primal finite real part once and keep the two remaining
    -- derivatives.
    exact hcontAt.fderiv_right (by norm_num : (2 : WithTop ℕ∞) + 1 ≤ 3)
  have hD_contDiff : ContDiff ℝ (⊤ : WithTop ℕ∞) D := D.contDiff
  have hD_contDiffAt : ContDiffAt ℝ 2 D (fderiv ℝ (withTopRealPart f) x) := by
    exact (hD_contDiff.of_le (show (2 : WithTop ℕ∞) ≤ ⊤ by simp)).contDiffAt
  -- Rewrite the gradient through the Riesz map so the remaining regularity becomes `C²`.
  simpa [gradient, D] using hD_contDiffAt.comp x hfderiv_C2

/-- Helper for Proposition 5.0.30: a `C²` primal finite real part differentiates its gradient to
the owner Hessian at each interior point. -/
private lemma primalGradient_hasFDerivAt_of_contDiffOn_two
    {f : E → WithTop ℝ}
    (hf_contDiff : ContDiffOn ℝ 2 (withTopRealPart f) (interior (dom f)))
    {x : E} (hx : x ∈ interior (dom f)) :
    HasFDerivAt (∇ (withTopRealPart f)) (hessian (withTopRealPart f) x) x := by
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfderiv :
      DifferentiableAt ℝ (fderiv ℝ (withTopRealPart f)) x := by
    have hcont :
        ContDiffAt ℝ 1 (fderiv ℝ (withTopRealPart f)) x :=
      (hf_contDiff.contDiffAt (IsOpen.mem_nhds isOpen_interior hx)).fderiv_right
        (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
    -- Restrict the `C¹` control of the first derivative to ordinary differentiability.
    exact hcont.differentiableAt one_ne_zero
  have hgrad : DifferentiableAt ℝ (∇ (withTopRealPart f)) x := by
    -- Rewrite the gradient through the Riesz map before taking its derivative.
    simpa [gradient, D] using D.differentiableAt.comp x hfderiv
  -- The chapter owner `hessian` is exactly the derivative of the gradient field.
  simpa [hessian] using hgrad.hasFDerivAt

/-- Helper for Proposition 5.0.30: at an interior point with invertible primal Hessian, the
inverse-Hessian family is genuinely differentiable. -/
private lemma inverse_hessian_differentiableAt
    {f : E → WithTop ℝ} {x : E}
    (hf_contDiff : ContDiffOn ℝ 3 (withTopRealPart f) (interior (dom f)))
    (hx : x ∈ interior (dom f))
    (hinv : (hessian (withTopRealPart f) x).IsInvertible) :
    DifferentiableAt ℝ (fun y ↦ (hessian (withTopRealPart f) y).inverse) x := by
  have hcontAt : ContDiffAt ℝ 3 (withTopRealPart f) x := by
    -- Restrict the `C³` hypothesis to the interior point `x`.
    exact hf_contDiff.contDiffAt (IsOpen.mem_nhds isOpen_interior hx)
  have hgrad_C2 : ContDiffAt ℝ 2 (∇ (withTopRealPart f)) x :=
    primalGradient_contDiffAt_of_contDiffAt_three hcontAt
  rcases exists_continuousLinearEquiv_fderiv_symm_eq hgrad_C2 hinv with
    ⟨N, -, hN_symm_C1, hN, -⟩
  have hEq : (fun y ↦ ((N y).symm : E →L[ℝ] E)) =ᶠ[nhds x]
      fun y ↦ (hessian (withTopRealPart f) y).inverse := by
    -- Near `x`, the chosen local equivalence family is exactly the primal Hessian family, so its
    -- inverse family is the genuine inverse-Hessian branch.
    filter_upwards [hN] with y hy
    have hy_inverse :
        (fderiv ℝ (∇ (withTopRealPart f)) y).inverse = ((N y).symm : E →L[ℝ] E) := by
      simpa [hy] using (ContinuousLinearMap.inverse_equiv (N y) : (N y : E →L[ℝ] E).inverse = (N y).symm)
    simpa [hessian] using hy_inverse.symm
  -- Transport differentiability from the smooth inverse family supplied by the local-inverse API.
  exact (hN_symm_C1.differentiableAt one_ne_zero).congr_of_eventuallyEq hEq.symm

/-- Helper for Proposition 5.0.30: differentiating the genuine inverse-Hessian family at an
interior point gives the textbook `-H⁻¹ (DH) H⁻¹` formula. -/
private lemma inverse_hessian_fderiv_eq
    {f : E → WithTop ℝ} {x h : E}
    (hf_contDiff : ContDiffOn ℝ 3 (withTopRealPart f) (interior (dom f)))
    (hx : x ∈ interior (dom f))
    (hinv : (hessian (withTopRealPart f) x).IsInvertible) :
    fderiv ℝ (fun y ↦ (hessian (withTopRealPart f) y).inverse) x h =
      -((hessian (withTopRealPart f) x).inverse.comp
        ((fderiv ℝ (hessian (withTopRealPart f)) x h).comp
          (hessian (withTopRealPart f) x).inverse)) := by
  have hcontAt : ContDiffAt ℝ 3 (withTopRealPart f) x := by
    -- Restrict the `C³` hypothesis to the interior point where the inverse formula is used.
    exact hf_contDiff.contDiffAt (IsOpen.mem_nhds isOpen_interior hx)
  have hgrad_C2 : ContDiffAt ℝ 2 (∇ (withTopRealPart f)) x :=
    primalGradient_contDiffAt_of_contDiffAt_three hcontAt
  rcases exists_continuousLinearEquiv_fderiv_symm_eq hgrad_C2 hinv with
    ⟨N, -, -, hN, hN_deriv⟩
  have hxN_raw : (N x : E →L[ℝ] E) = fderiv ℝ (∇ (withTopRealPart f)) x := by
    exact hN.self_of_nhds
  have hxN : N x = hessian (withTopRealPart f) x := by
    -- At the base point, the local equivalence family recovers the primal Hessian itself.
    simpa [hessian] using hxN_raw
  have hEq : (fun y ↦ ((N y).symm : E →L[ℝ] E)) =ᶠ[nhds x]
      fun y ↦ (hessian (withTopRealPart f) y).inverse := by
    -- Near `x`, the inverse family from mathlib is literally the inverse primal Hessian.
    filter_upwards [hN] with y hy
    have hy_inverse :
        (fderiv ℝ (∇ (withTopRealPart f)) y).inverse = ((N y).symm : E →L[ℝ] E) := by
      simpa [hy] using (ContinuousLinearMap.inverse_equiv (N y) : (N y : E →L[ℝ] E).inverse = (N y).symm)
    simpa [hessian] using hy_inverse.symm
  have hFderivEq :
      fderiv ℝ (fun y ↦ ((N y).symm : E →L[ℝ] E)) x =
        fderiv ℝ (fun y ↦ (hessian (withTopRealPart f) y).inverse) x :=
    Filter.EventuallyEq.fderiv_eq hEq
  calc
    fderiv ℝ (fun y ↦ (hessian (withTopRealPart f) y).inverse) x h
      = fderiv ℝ (fun y ↦ ((N y).symm : E →L[ℝ] E)) x h := by
        rw [← hFderivEq]
    _ = - (N x).symm ∘L ((fderiv ℝ (fderiv ℝ (∇ (withTopRealPart f))) x) h) ∘L (N x).symm := by
        -- Apply the canonical derivative formula for the inverse family of a `C²` map.
        exact hN_deriv h
    _ = -((hessian (withTopRealPart f) x).inverse.comp
          ((fderiv ℝ (hessian (withTopRealPart f)) x h).comp
            (hessian (withTopRealPart f) x).inverse)) := by
        -- Rewrite back to the chapter owner `hessian`.
        have hx_inverse :
            (fderiv ℝ (∇ (withTopRealPart f)) x).inverse = ((N x).symm : E →L[ℝ] E) := by
          simpa [hxN_raw] using
            (ContinuousLinearMap.inverse_equiv (N x) :
              (N x : E →L[ℝ] E).inverse = (N x).symm)
        simpa [ContinuousLinearMap.comp_assoc, hessian, hx_inverse]

/-- Helper for Proposition 5.0.30: the chosen branch is differentiable with derivative
`(hessian (withTopRealPart f) (xStar s)).inverse` at every dual-domain point once the branch is
interior, continuous at the dual slope, locally right-inverts the primal gradient there, and has
genuinely invertible primal Hessian there. This is the local inverse-function bridge available
from the present hypotheses before any dual-Hessian neighborhood identity is imposed. -/
theorem fenchelConjugate_maximizerBranch_hasFDerivAt
    {f : E → WithTop ℝ} {xStar : E → E}
    (hf_contDiff : ContDiffOn ℝ 2 (withTopRealPart f) (interior (dom f)))
    (hxStar_mem : ∀ ⦃s : E⦄, s ∈ dom (f⋆) → xStar s ∈ interior (dom f))
    (hxStar_continuousAt :
      ∀ ⦃s : E⦄, s ∈ dom (f⋆) → ContinuousAt xStar s)
    (hxStar_local_rightInverse :
      ∀ ⦃s : E⦄, s ∈ dom (f⋆) → ∀ᶠ t in nhds s, ∇ (withTopRealPart f) (xStar t) = t)
    (hxStar_hessian_invertible :
      ∀ ⦃s : E⦄, s ∈ dom (f⋆) →
        (hessian (withTopRealPart f) (xStar s)).IsInvertible)
    {s : E} (hs : s ∈ dom (f⋆)) :
    HasFDerivAt xStar ((hessian (withTopRealPart f) (xStar s)).inverse) s := by
  let G : E → E := ∇ (withTopRealPart f)
  let x : E := xStar s
  let H : E →L[ℝ] E := hessian (withTopRealPart f) x
  let e : E ≃L[ℝ] E := Classical.choose (hxStar_hessian_invertible hs)
  have he : (e : E →L[ℝ] E) = H := Classical.choose_spec (hxStar_hessian_invertible hs)
  have hgrad_fderiv : HasFDerivAt G H x := by
    -- Normalize the derivative of the primal gradient to the chapter owner `hessian`.
    simpa [G, H, x] using
      primalGradient_hasFDerivAt_of_contDiffOn_two hf_contDiff (hxStar_mem hs)
  have hgrad_fderiv_e : HasFDerivAt G (e : E →L[ℝ] E) x := by
    -- Replace the Hessian derivative by the chosen continuous linear equivalence.
    simpa [he] using hgrad_fderiv
  have he_inverse : (e.symm : E →L[ℝ] E) = H.inverse := by
    -- Rewrite the inverse derivative using the project's totalized inverse operator.
    calc
      (e.symm : E →L[ℝ] E) = (e : E →L[ℝ] E).inverse := by
        symm
        exact ContinuousLinearMap.inverse_equiv e
      _ = H.inverse := by
        simp [he]
  -- Semantic recall: `HasFDerivAt.of_local_left_inverse` is the intended mathlib bridge once the
  -- selector is explicitly assumed continuous and locally right-inverts the primal gradient near
  -- the dual slope `s`.
  have hxStar_deriv : HasFDerivAt xStar (e.symm : E →L[ℝ] E) s := by
    exact
      HasFDerivAt.of_local_left_inverse
        (hxStar_continuousAt hs) hgrad_fderiv_e
        (by simpa [G] using hxStar_local_rightInverse hs)
  simpa [H, x, he_inverse] using hxStar_deriv

/-- Helper for Proposition 5.0.30: if the chosen maximizing branch stays in the primal interior
when approaching `s` within `dom (f⋆)`, then the pointwise stationarity equation
`∇ f (xStar t) = t` already forces the within-domain derivative `∇² f⋆(s)` by the local
left-inverse theorem. -/
private lemma maximizerBranch_hasFDerivWithinAt_of_tendstoWithin
    {f : E → WithTop ℝ} {xStar : E → E} {s : E}
    (hf_contDiff : ContDiffOn ℝ 2 (withTopRealPart f) (interior (dom f)))
    (hxStar_mem : ∀ ⦃t : E⦄, t ∈ dom (f⋆) → xStar t ∈ interior (dom f))
    (hxStar_gradient_eq :
      ∀ ⦃t : E⦄, t ∈ dom (f⋆) →
        ∇ (withTopRealPart f) (xStar t) = t)
    (hxStar_hessian_invertible :
      ∀ ⦃t : E⦄, t ∈ dom (f⋆) →
        (hessian (withTopRealPart f) (xStar t)).IsInvertible)
    (hdual_hessian_eq_inverse :
      ∀ ⦃t : E⦄, t ∈ dom (f⋆) →
        hessian (extendedRealRealPart (f⋆)) t =
          (hessian (withTopRealPart f) (xStar t)).inverse)
    (hs : s ∈ dom (f⋆))
    (hxStar_tendsto :
      Filter.Tendsto xStar (nhdsWithin s (dom (f⋆)))
        (nhdsWithin (xStar s) (interior (dom f)))) :
    HasFDerivWithinAt xStar (hessian (extendedRealRealPart (f⋆)) s) (dom (f⋆)) s := by
  let G : E → E := ∇ (withTopRealPart f)
  let x : E := xStar s
  let H : E →L[ℝ] E := hessian (withTopRealPart f) x
  let e : E ≃L[ℝ] E := Classical.choose (hxStar_hessian_invertible hs)
  have he : (e : E →L[ℝ] E) = H := Classical.choose_spec (hxStar_hessian_invertible hs)
  have hgrad_within :
      HasFDerivWithinAt G (e : E →L[ℝ] E) (interior (dom f)) x := by
    -- Normalize the derivative of the primal gradient to the chosen equivalence witness.
    simpa [G, H, x, he] using
      (primalGradient_hasFDerivAt_of_contDiffOn_two hf_contDiff (hxStar_mem hs)).hasFDerivWithinAt
  have hrightInv : ∀ᶠ t in nhdsWithin s (dom (f⋆)), G (xStar t) = t := by
    -- The branch equation holds on the whole dual domain, hence also in the within filter at `s`.
    filter_upwards [self_mem_nhdsWithin] with t ht
    simpa [G] using hxStar_gradient_eq ht
  have he_inverse : (e.symm : E →L[ℝ] E) = H.inverse := by
    -- Rewrite the inverse of the chosen equivalence through the project's totalized inverse.
    calc
      (e.symm : E →L[ℝ] E) = (e : E →L[ℝ] E).inverse := by
        symm
        exact ContinuousLinearMap.inverse_equiv e
      _ = H.inverse := by
        simp [he]
  have hxStar_deriv :
      HasFDerivWithinAt xStar (e.symm : E →L[ℝ] E) (dom (f⋆)) s := by
    -- Apply the within-domain local left-inverse theorem to the branch equation `∇ f ∘ xStar = id`.
    exact HasFDerivWithinAt.of_local_left_inverse hxStar_tendsto hgrad_within hs hrightInv
  -- Replace the inverse derivative by the assumed dual Hessian at the base slope.
  simpa [H, x, he_inverse, hdual_hessian_eq_inverse hs] using hxStar_deriv

/-- Helper for Proposition 5.0.30: once the dual domain has a unique tangent and the maximizing
branch has the within-domain continuity needed by the local left-inverse theorem, the exact
derivative package required by the chain-rule helper is available. -/
private lemma maximizerBranch_withinDerivativePackage_of_uniqueDiffWithinAt_of_tendstoWithin
    {f : E → WithTop ℝ} {xStar : E → E} {s : E}
    (hf_contDiff : ContDiffOn ℝ 2 (withTopRealPart f) (interior (dom f)))
    (hxStar_mem : ∀ ⦃t : E⦄, t ∈ dom (f⋆) → xStar t ∈ interior (dom f))
    (hxStar_gradient_eq :
      ∀ ⦃t : E⦄, t ∈ dom (f⋆) →
        ∇ (withTopRealPart f) (xStar t) = t)
    (hxStar_hessian_invertible :
      ∀ ⦃t : E⦄, t ∈ dom (f⋆) →
        (hessian (withTopRealPart f) (xStar t)).IsInvertible)
    (hdual_hessian_eq_inverse :
      ∀ ⦃t : E⦄, t ∈ dom (f⋆) →
        hessian (extendedRealRealPart (f⋆)) t =
          (hessian (withTopRealPart f) (xStar t)).inverse)
    (hs : s ∈ dom (f⋆))
    (hunique : UniqueDiffWithinAt ℝ (dom (f⋆)) s)
    (hxStar_tendsto :
      Filter.Tendsto xStar (nhdsWithin s (dom (f⋆)))
        (nhdsWithin (xStar s) (interior (dom f)))) :
    UniqueDiffWithinAt ℝ (dom (f⋆)) s ∧
      HasFDerivWithinAt xStar (hessian (extendedRealRealPart (f⋆)) s) (dom (f⋆)) s := by
  constructor
  · -- Keep the unique-tangent assumption unchanged for the downstream chain-rule theorem.
    exact hunique
  · -- Package the within derivative obtained from the local left-inverse bridge above.
    exact
      maximizerBranch_hasFDerivWithinAt_of_tendstoWithin
        hf_contDiff hxStar_mem hxStar_gradient_eq hxStar_hessian_invertible
        hdual_hessian_eq_inverse hs hxStar_tendsto

/-- Helper for Proposition 5.0.30: once the maximizer branch derivative is available, the chain
rule differentiates the inverse primal Hessian along that branch. -/
private lemma inverse_hessian_along_branch_fderiv_eq
    {f : E → WithTop ℝ} {xStar : E → E}
    (hf_contDiff : ContDiffOn ℝ 3 (withTopRealPart f) (interior (dom f)))
    (hxStar_mem : ∀ ⦃s : E⦄, s ∈ dom (f⋆) → xStar s ∈ interior (dom f))
    (hxStar_hessian_invertible :
      ∀ ⦃s : E⦄, s ∈ dom (f⋆) →
        (hessian (withTopRealPart f) (xStar s)).IsInvertible)
    (hxStar_hasFDerivAt :
      ∀ ⦃s : E⦄, s ∈ dom (f⋆) →
        HasFDerivAt xStar (hessian (extendedRealRealPart (f⋆)) s) s)
    {s : E} (hs : s ∈ dom (f⋆))
    (h : E) :
    fderiv ℝ (fun t ↦ (hessian (withTopRealPart f) (xStar t)).inverse) s h =
      -((hessian (withTopRealPart f) (xStar s)).inverse.comp
        ((fderiv ℝ (hessian (withTopRealPart f)) (xStar s)
            ((hessian (extendedRealRealPart (f⋆)) s) h)).comp
          (hessian (withTopRealPart f) (xStar s)).inverse)) := by
  have hbranch_hasFDerivAt :
      HasFDerivAt xStar (hessian (extendedRealRealPart (f⋆)) s) s :=
    -- Assume separately the branch differentiability needed for this chain-rule helper.
    hxStar_hasFDerivAt hs
  have hinverse_diff :
      DifferentiableAt ℝ (fun y ↦ (hessian (withTopRealPart f) y).inverse) (xStar s) := by
    -- The outer inverse-Hessian family is differentiable at the branch point by the generic
    -- inverse-derivative lemma proved above.
    exact inverse_hessian_differentiableAt hf_contDiff (hxStar_mem hs) (hxStar_hessian_invertible hs)
  calc
    fderiv ℝ (fun t ↦ (hessian (withTopRealPart f) (xStar t)).inverse) s h
      = ((fderiv ℝ (fun y ↦ (hessian (withTopRealPart f) y).inverse) (xStar s)).comp
          (hessian (extendedRealRealPart (f⋆)) s)) h := by
        -- Differentiate the outer inverse-Hessian family after the maximizing branch.
        rw [show (fun t ↦ (hessian (withTopRealPart f) (xStar t)).inverse) =
          (fun y ↦ (hessian (withTopRealPart f) y).inverse) ∘ xStar from rfl]
        rw [fderiv_comp s hinverse_diff hbranch_hasFDerivAt.differentiableAt]
        simpa [hbranch_hasFDerivAt.fderiv]
    _ = -((hessian (withTopRealPart f) (xStar s)).inverse.comp
          ((fderiv ℝ (hessian (withTopRealPart f)) (xStar s)
              ((hessian (extendedRealRealPart (f⋆)) s) h)).comp
            (hessian (withTopRealPart f) (xStar s)).inverse)) := by
        -- Evaluate the generic inverse-Hessian derivative on the branch direction
        -- `DxStar(s) h = ∇² f⋆(s) h`.
        simpa using inverse_hessian_fderiv_eq hf_contDiff (hxStar_mem hs)
          (hxStar_hessian_invertible hs)

/-- Companion to Proposition 5.0.30: once the dual domain has a unique tangent and the chosen
maximizer branch is known to have derivative `∇² f⋆(s)` within that domain, the assumed
inverse-Hessian identity differentiates to the textbook `-H⁻¹ (DH) H⁻¹` formula. -/
theorem fenchelConjugate_hessianDerivative_formula_of_branchHasFDerivWithinAt
    {f : E → WithTop ℝ} {xStar : E → E}
    (hf_contDiff : ContDiffOn ℝ 3 (withTopRealPart f) (interior (dom f)))
    (hxStar_mem : ∀ ⦃s : E⦄, s ∈ dom (f⋆) → xStar s ∈ interior (dom f))
    (hxStar_hessian_invertible :
      ∀ ⦃s : E⦄, s ∈ dom (f⋆) →
        (hessian (withTopRealPart f) (xStar s)).IsInvertible)
    (hdual_hessian_eq_inverse :
      ∀ ⦃s : E⦄, s ∈ dom (f⋆) →
        hessian (extendedRealRealPart (f⋆)) s =
          (hessian (withTopRealPart f) (xStar s)).inverse)
    {s : E} (hs : s ∈ dom (f⋆))
    (hunique : UniqueDiffWithinAt ℝ (dom (f⋆)) s)
    (hxStar_hasFDerivWithinAt :
      HasFDerivWithinAt xStar (hessian (extendedRealRealPart (f⋆)) s) (dom (f⋆)) s)
    (h : E) :
    fderivWithin ℝ (hessian (extendedRealRealPart (f⋆))) (dom (f⋆)) s h =
      -((hessian (extendedRealRealPart (f⋆)) s).comp
        ((fderiv ℝ (hessian (withTopRealPart f)) (xStar s)
            ((hessian (extendedRealRealPart (f⋆)) s) h)).comp
          (hessian (extendedRealRealPart (f⋆)) s))) := by
  have hdual_eq :
      hessian (extendedRealRealPart (f⋆)) =ᶠ[nhdsWithin s (dom (f⋆))]
        fun t ↦ (hessian (withTopRealPart f) (xStar t)).inverse := by
    -- Rewrite the within-domain dual Hessian through the assumed inverse-Hessian identity.
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hdual_hessian_eq_inverse ht
  have houter_diff :
      DifferentiableWithinAt ℝ (fun y ↦ (hessian (withTopRealPart f) y).inverse) Set.univ
        (xStar s) := by
    -- The outer inverse-Hessian family is differentiable at the branch point in the ambient
    -- space, hence also within `univ`.
    exact (inverse_hessian_differentiableAt hf_contDiff (hxStar_mem hs)
      (hxStar_hessian_invertible hs)).differentiableWithinAt
  have hmapsTo : Set.MapsTo xStar (dom (f⋆)) Set.univ := by
    -- The chain rule only needs the trivial codomain control for the ambient outer function.
    exact fun _ _ ↦ by simp
  calc
    fderivWithin ℝ (hessian (extendedRealRealPart (f⋆))) (dom (f⋆)) s h
      = fderivWithin ℝ (fun t ↦ (hessian (withTopRealPart f) (xStar t)).inverse)
          (dom (f⋆)) s h := by
        -- Replace the target function by the inverse primal Hessian model on the dual domain.
        have hEqMap :
            fderivWithin ℝ (hessian (extendedRealRealPart (f⋆))) (dom (f⋆)) s =
              fderivWithin ℝ (fun t ↦ (hessian (withTopRealPart f) (xStar t)).inverse)
                (dom (f⋆)) s :=
          hdual_eq.fderivWithin_eq_of_mem hs
        rw [hEqMap]
    _ = ((fderivWithin ℝ (fun y ↦ (hessian (withTopRealPart f) y).inverse) Set.univ (xStar s)).comp
          (fderivWithin ℝ xStar (dom (f⋆)) s)) h := by
        -- Differentiate the inverse-Hessian model by the within-domain chain rule.
        have hCompMap :
            fderivWithin ℝ ((fun y ↦ (hessian (withTopRealPart f) y).inverse) ∘ xStar)
                (dom (f⋆)) s =
              (fderivWithin ℝ (fun y ↦ (hessian (withTopRealPart f) y).inverse) Set.univ
                  (xStar s)).comp
                (fderivWithin ℝ xStar (dom (f⋆)) s) :=
          fderivWithin_comp s houter_diff hxStar_hasFDerivWithinAt.differentiableWithinAt
            hmapsTo hunique
        have hCompMap' :
            fderivWithin ℝ (fun t ↦ (hessian (withTopRealPart f) (xStar t)).inverse)
                (dom (f⋆)) s =
              (fderivWithin ℝ (fun y ↦ (hessian (withTopRealPart f) y).inverse) Set.univ
                  (xStar s)).comp
                (fderivWithin ℝ xStar (dom (f⋆)) s) := by
          simpa using hCompMap
        rw [hCompMap']
    _ = ((fderiv ℝ (fun y ↦ (hessian (withTopRealPart f) y).inverse) (xStar s)).comp
          (hessian (extendedRealRealPart (f⋆)) s)) h := by
        -- Read the chosen within derivative of the branch as the assumed dual Hessian.
        rw [fderivWithin_univ, hxStar_hasFDerivWithinAt.fderivWithin hunique]
    _ = -((hessian (withTopRealPart f) (xStar s)).inverse.comp
          ((fderiv ℝ (hessian (withTopRealPart f)) (xStar s)
              ((hessian (extendedRealRealPart (f⋆)) s) h)).comp
            (hessian (withTopRealPart f) (xStar s)).inverse)) := by
        -- Evaluate the generic inverse-Hessian derivative in the branch direction.
        simpa using inverse_hessian_fderiv_eq hf_contDiff (hxStar_mem hs)
          (hxStar_hessian_invertible hs)
    _ = -((hessian (extendedRealRealPart (f⋆)) s).comp
          ((fderiv ℝ (hessian (withTopRealPart f)) (xStar s)
              ((hessian (extendedRealRealPart (f⋆)) s) h)).comp
            (hessian (extendedRealRealPart (f⋆)) s))) := by
        -- Normalize both inverse-Hessian factors back to the dual Hessian owner.
        simpa [hdual_hessian_eq_inverse hs]

/-- Helper for Proposition 5.0.30: on an open dual domain, an ambient derivative of the
maximizer branch immediately supplies the within-domain differentiability package needed by the
chain-rule proof. -/
private lemma branchHasFDerivWithinAtPackage_of_isOpen
    {f : E → WithTop ℝ} {xStar : E → E} {s : E}
    (hdom_open : IsOpen (dom (f⋆))) (hs : s ∈ dom (f⋆))
    (hxStar_hasFDerivAt :
      HasFDerivAt xStar (hessian (extendedRealRealPart (f⋆)) s) s) :
    UniqueDiffWithinAt ℝ (dom (f⋆)) s ∧
      HasFDerivWithinAt xStar (hessian (extendedRealRealPart (f⋆)) s) (dom (f⋆)) s := by
  constructor
  · -- Open sets have the unique tangent property required by `fderivWithin`.
    exact hdom_open.uniqueDiffWithinAt hs
  · -- Ambient differentiability restricts immediately to the dual effective domain.
    exact hxStar_hasFDerivAt.hasFDerivWithinAt

/-- Helper for Proposition 5.0.30: if the dual domain is open and the maximizing branch is
already known to have ambient derivative `∇² f⋆(s)`, the ambient third-derivative formula follows
directly from the within-domain chain-rule theorem. -/
theorem fenchelConjugate_hessianDerivative_formula_of_isOpen_of_branchHasFDerivAt
    {f : E → WithTop ℝ} {xStar : E → E}
    (hf_contDiff : ContDiffOn ℝ 3 (withTopRealPart f) (interior (dom f)))
    (hxStar_mem : ∀ ⦃s : E⦄, s ∈ dom (f⋆) → xStar s ∈ interior (dom f))
    (hxStar_hessian_invertible :
      ∀ ⦃s : E⦄, s ∈ dom (f⋆) →
        (hessian (withTopRealPart f) (xStar s)).IsInvertible)
    (hdual_hessian_eq_inverse :
      ∀ ⦃s : E⦄, s ∈ dom (f⋆) →
        hessian (extendedRealRealPart (f⋆)) s =
          (hessian (withTopRealPart f) (xStar s)).inverse)
    (hdom_open : IsOpen (dom (f⋆)))
    {s : E} (hs : s ∈ dom (f⋆))
    (hxStar_hasFDerivAt :
      HasFDerivAt xStar (hessian (extendedRealRealPart (f⋆)) s) s)
    (h : E) :
    fderiv ℝ (hessian (extendedRealRealPart (f⋆))) s h =
      -((hessian (extendedRealRealPart (f⋆)) s).comp
        ((fderiv ℝ (hessian (withTopRealPart f)) (xStar s)
            ((hessian (extendedRealRealPart (f⋆)) s) h)).comp
          (hessian (extendedRealRealPart (f⋆)) s))) := by
  obtain ⟨hunique, hxStar_hasFDerivWithinAt⟩ :=
    branchHasFDerivWithinAtPackage_of_isOpen
      hdom_open hs hxStar_hasFDerivAt
  -- Open-domain ambient differentiation is the within-domain formula specialized through the
  -- unique tangent package above.
  rw [← fderivWithin_of_isOpen hdom_open hs]
  exact
    fenchelConjugate_hessianDerivative_formula_of_branchHasFDerivWithinAt
      hf_contDiff hxStar_mem hxStar_hessian_invertible hdual_hessian_eq_inverse hs hunique
      hxStar_hasFDerivWithinAt h

/-- Companion within-domain form of the third-derivative Fenchel-conjugate identity: if the dual
effective domain has a
unique tangent at `s` and the chosen maximizer branch tends to the primal interior within
`dom (f⋆)`, then the textbook `D³ f⋆` identity holds as a `fderivWithin` statement. -/
theorem fenchelConjugate_hessianDerivative_formula_within
    {f : E → WithTop ℝ} {xStar : E → E}
    (hf_contDiff : ContDiffOn ℝ 3 (withTopRealPart f) (interior (dom f)))
    (hxStar_mem : ∀ ⦃s : E⦄, s ∈ dom (f⋆) → xStar s ∈ interior (dom f))
    (hxStar_isMaximizer :
      ∀ ⦃s : E⦄, s ∈ dom (f⋆) →
        IsMaxOn (fun y : E ↦ inner ℝ s y - withTopRealPart f y) (dom f) (xStar s))
    (hxStar_gradient_eq :
      ∀ ⦃s : E⦄, s ∈ dom (f⋆) →
        ∇ (withTopRealPart f) (xStar s) = s)
    (hxStar_hessian_invertible :
      ∀ ⦃s : E⦄, s ∈ dom (f⋆) →
        (hessian (withTopRealPart f) (xStar s)).IsInvertible)
    (hdual_hessian_eq_inverse :
      ∀ ⦃s : E⦄, s ∈ dom (f⋆) →
        hessian (extendedRealRealPart (f⋆)) s =
          (hessian (withTopRealPart f) (xStar s)).inverse)
    {s : E} (hs : s ∈ dom (f⋆))
    (hunique : UniqueDiffWithinAt ℝ (dom (f⋆)) s)
    (hxStar_tendsto :
      Filter.Tendsto xStar (nhdsWithin s (dom (f⋆)))
        (nhdsWithin (xStar s) (interior (dom f))))
    (h : E) :
    fderivWithin ℝ (hessian (extendedRealRealPart (f⋆))) (dom (f⋆)) s h =
      -((hessian (extendedRealRealPart (f⋆)) s).comp
        ((fderiv ℝ (hessian (withTopRealPart f)) (xStar s)
            ((hessian (extendedRealRealPart (f⋆)) s) h)).comp
          (hessian (extendedRealRealPart (f⋆)) s))) := by
  have _ : ∇ (withTopRealPart f) (xStar s) = s :=
    maximizerBranch_gradient_eq_slope
      (hf_contDiff.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3))
      hxStar_mem hxStar_isMaximizer hs
  have hxStar_hasFDerivWithinAt :
      HasFDerivWithinAt xStar (hessian (extendedRealRealPart (f⋆)) s) (dom (f⋆)) s :=
    (maximizerBranch_withinDerivativePackage_of_uniqueDiffWithinAt_of_tendstoWithin
      (hf_contDiff.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3))
      hxStar_mem hxStar_gradient_eq hxStar_hessian_invertible hdual_hessian_eq_inverse hs
      hunique hxStar_tendsto).2
  exact
    fenchelConjugate_hessianDerivative_formula_of_branchHasFDerivWithinAt
      hf_contDiff hxStar_mem hxStar_hessian_invertible hdual_hessian_eq_inverse hs hunique
      hxStar_hasFDerivWithinAt h

/-- Proposition 5.0.30: let `xStar : E → E` be a chosen Fenchel-support maximizer branch on
`dom (f⋆)`. Assume `f` is three times differentiable on `interior (dom f)`, that
`xStar s ∈ interior (dom f)` and `xStar s` maximizes `y ↦ ⟪s, y⟫ - f y` on `dom f` for every
`s ∈ dom (f⋆)`, that the source stationarity equation `∇ (withTopRealPart f) (xStar s) = s`
holds on `dom (f⋆)`, and that the source inverse-Hessian identity (5.u341) is represented in
Lean by
`hessian (extendedRealRealPart (f⋆)) s = (hessian (withTopRealPart f) (xStar s)).inverse`.
Because `ContinuousLinearMap.inverse` is totalized in Lean, we also record the genuine
primal-Hessian invertibility needed to express the source inverse-Hessian hypothesis faithfully.
Because Lean's differential operators are totalized, the source-facing `D³ f⋆` identity is stated
here in the within-domain form closest to the textbook meaning; the stronger ambient `fderiv`
consequence on an open dual domain remains available as the companion theorem
`fenchelConjugate_hessianDerivative_formula_of_isOpen`. -/
theorem fenchelConjugate_hessianDerivative_formula
    {f : E → WithTop ℝ} {xStar : E → E}
    (hf_contDiff : ContDiffOn ℝ 3 (withTopRealPart f) (interior (dom f)))
    (hxStar_mem : ∀ ⦃s : E⦄, s ∈ dom (f⋆) → xStar s ∈ interior (dom f))
    (hxStar_isMaximizer :
      ∀ ⦃s : E⦄, s ∈ dom (f⋆) →
        IsMaxOn (fun y : E ↦ inner ℝ s y - withTopRealPart f y) (dom f) (xStar s))
    (hxStar_gradient_eq :
      ∀ ⦃s : E⦄, s ∈ dom (f⋆) →
        ∇ (withTopRealPart f) (xStar s) = s)
    (hxStar_hessian_invertible :
      ∀ ⦃s : E⦄, s ∈ dom (f⋆) →
        (hessian (withTopRealPart f) (xStar s)).IsInvertible)
    (hdual_hessian_eq_inverse :
      ∀ ⦃s : E⦄, s ∈ dom (f⋆) →
        hessian (extendedRealRealPart (f⋆)) s =
          (hessian (withTopRealPart f) (xStar s)).inverse)
    {s : E} (hs : s ∈ dom (f⋆))
    (hunique : UniqueDiffWithinAt ℝ (dom (f⋆)) s)
    (hxStar_tendsto :
      Filter.Tendsto xStar (nhdsWithin s (dom (f⋆)))
        (nhdsWithin (xStar s) (interior (dom f))))
    (h : E) :
    fderivWithin ℝ (hessian (extendedRealRealPart (f⋆))) (dom (f⋆)) s h =
      -((hessian (extendedRealRealPart (f⋆)) s).comp
        ((fderiv ℝ (hessian (withTopRealPart f)) (xStar s)
            ((hessian (extendedRealRealPart (f⋆)) s) h)).comp
          (hessian (extendedRealRealPart (f⋆)) s))) := by
  exact
    fenchelConjugate_hessianDerivative_formula_within
      hf_contDiff hxStar_mem hxStar_isMaximizer hxStar_gradient_eq hxStar_hessian_invertible
      hdual_hessian_eq_inverse hs hunique hxStar_tendsto h

/-- Companion sufficient-condition form of the third-derivative Fenchel-conjugate identity: if
`dom (f⋆)` is open, the
ordinary `fderiv` statement follows from the within-domain chain-rule theorem once the chosen
maximizer branch is known to have ambient derivative `∇² f⋆(s)` at `s`. -/
theorem fenchelConjugate_hessianDerivative_formula_of_isOpen
    {f : E → WithTop ℝ} {xStar : E → E}
    (hf_contDiff : ContDiffOn ℝ 3 (withTopRealPart f) (interior (dom f)))
    (hxStar_mem : ∀ ⦃s : E⦄, s ∈ dom (f⋆) → xStar s ∈ interior (dom f))
    (hxStar_hessian_invertible :
      ∀ ⦃s : E⦄, s ∈ dom (f⋆) →
        (hessian (withTopRealPart f) (xStar s)).IsInvertible)
    (hdual_hessian_eq_inverse :
      ∀ ⦃s : E⦄, s ∈ dom (f⋆) →
        hessian (extendedRealRealPart (f⋆)) s =
          (hessian (withTopRealPart f) (xStar s)).inverse)
    (hdom_open : IsOpen (dom (f⋆)))
    {s : E} (hs : s ∈ dom (f⋆))
    (hxStar_hasFDerivAt :
      HasFDerivAt xStar (hessian (extendedRealRealPart (f⋆)) s) s)
    (h : E) :
    fderiv ℝ (hessian (extendedRealRealPart (f⋆))) s h =
      -((hessian (extendedRealRealPart (f⋆)) s).comp
        ((fderiv ℝ (hessian (withTopRealPart f)) (xStar s)
            ((hessian (extendedRealRealPart (f⋆)) s) h)).comp
          (hessian (extendedRealRealPart (f⋆)) s))) := by
  exact
    fenchelConjugate_hessianDerivative_formula_of_isOpen_of_branchHasFDerivAt
      hf_contDiff hxStar_mem hxStar_hessian_invertible hdual_hessian_eq_inverse hdom_open hs
      hxStar_hasFDerivAt h

end
