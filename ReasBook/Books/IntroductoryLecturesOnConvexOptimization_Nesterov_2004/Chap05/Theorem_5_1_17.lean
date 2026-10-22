/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_1_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_1_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Theorem_1_4_13
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_27
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_1_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Corollary_5_1_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.FenchelPrimalExtension
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Corollary_5_1_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Lemma_5_1_6
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Proposition_5_0_29
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_1_6

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ConvexAnalysis Gradient HessianLocalNorm WithTopConvexAnalysis

noncomputable section

universe u

variable {E : Type u}

/- Theorem 5.1.17 lies in the chapter's Fenchel-duality / self-concordance domain.

Source-facing owner choices:
- `IsSelfConcordantOnWith` from `Chap05/Definition_5_1_1`, the chapter owner for
  self-concordance with constant `Mf`;
- `fenchelPrimalExtension` from `Chap05/FenchelPrimalExtension`, the canonical `+∞`-extension of
  a real-valued primal function off its effective domain;
- `fenchelDual` / notation `f⋆`, `dom`, and `extendedRealRealPart`, the canonical owners for the
  Fenchel conjugate and its finite real part.

The source theorem states that the Fenchel conjugate of a self-concordant function is again
self-concordant with the same constant. In the local API, the owner
`IsSelfConcordantOnWith (dom (F⋆)) Mf (extendedRealRealPart (F⋆))` also requires openness of the
dual effective domain. The affine counterexamples already formalized earlier in the chapter show
that this openness is not automatic from self-concordance alone, so the standing closed-epigraph
and no-affine-line hypotheses from the surrounding source discussion are made explicit here. -/

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

section

variable {Q : Set E} {Mf : NNReal} {f : E → ℝ}

local notation "F" => fenchelPrimalExtension Q f

-- Semantic recall check: LeanSearch did not expose a direct mathlib owner for this Chapter 5
-- Fenchel-duality self-concordance transfer, so this theorem stays on the local project API.

namespace IsSelfConcordantOnWith

omit [FiniteDimensional ℝ E] in
/-- Helper for Theorem 5.1.17: self-concordance on an open domain depends only on the restriction
of the function to that domain. -/
theorem congrOnOpenDomainEqOn
    {s : Set E} {Mf : NNReal} {f g : E → ℝ}
    (h : IsSelfConcordantOnWith s Mf f) (hEq : Set.EqOn f g s) :
    IsSelfConcordantOnWith s Mf g := by
  refine
    { isOpen_domain := h.isOpen_domain
      contDiffOn := (contDiffOn_congr fun x hx ↦ (hEq hx).symm).2 h.contDiffOn
      convexOn := h.convexOn.congr hEq
      third_deriv_bound := ?_ }
  intro x hx u
  have hEqAt : g =ᶠ[nhds x] f := by
    refine Filter.mem_of_superset (h.isOpen_domain.mem_nhds hx) ?_
    intro y hy
    exact (hEq hy).symm
  have hfContDiffAt : ContDiffAt ℝ 3 f x :=
    h.contDiffOn.contDiffAt (h.isOpen_domain.mem_nhds hx)
  have hgContDiffAt : ContDiffAt ℝ 3 g x :=
    hfContDiffAt.congr_of_eventuallyEq hEqAt
  -- Rewrite both the cubic term and the Hessian local norm through neighborhood equality.
  have hthird :
      thirdDirectionalDerivative g x u = thirdDirectionalDerivative f x u := by
    have hiter :
        iteratedFDeriv ℝ 3 g x = iteratedFDeriv ℝ 3 f x :=
      (Filter.EventuallyEq.iteratedFDeriv ℝ hEqAt 3).eq_of_nhds
    simpa [thirdDirectionalDerivative_eq_iteratedFDeriv hgContDiffAt,
      thirdDirectionalDerivative_eq_iteratedFDeriv hfContDiffAt] using
      congrArg (fun A ↦ A fun _ ↦ u) hiter
  have hhess : hessian g x = hessian f x := by
    simpa [hessian] using (hEqAt.gradient.fderiv_eq (𝕜 := ℝ))
  have hnorm : ‖u‖[g; x] = ‖u‖[f; x] := by
    simp [hessianLocalNorm_def, hhess]
  calc
    |thirdDirectionalDerivative g x u| = |thirdDirectionalDerivative f x u| := by
      rw [hthird]
    _ ≤ 2 * (Mf : ℝ) * ‖u‖[f; x] ^ (3 : ℕ) :=
      h.third_deriv_bound hx u
    _ = 2 * (Mf : ℝ) * ‖u‖[g; x] ^ (3 : ℕ) := by
      rw [hnorm]

end IsSelfConcordantOnWith

omit [FiniteDimensional ℝ E] in
/-- Helper for Theorem 5.1.17: the `+∞`-extension `F := fenchelPrimalExtension Q f` carries the
same self-concordance structure as `f` on `Q = dom F`. -/
private theorem primalExtensionSelfConcordant
    (hself : IsSelfConcordantOnWith Q Mf f) :
    IsSelfConcordantOnWith (withTopEffectiveDomain F) Mf (withTopRealPart F) := by
  -- Transport the source self-concordance owner across the open-domain restriction equality.
  have hEq : Set.EqOn f (withTopRealPart F) Q := by
    intro x hx
    symm
    simpa using withTopRealPart_fenchelPrimalExtension_apply_of_mem (Q := Q) (f := f) hx
  simpa [dom_fenchelPrimalExtension] using hself.congrOnOpenDomainEqOn hEq

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] in
/-- Helper for Theorem 5.1.17: the constrained epigraph of the primal `+∞`-extension is exactly
the original constrained epigraph over `Q`. -/
private theorem primalExtensionConstrainedEpigraph_eq :
    constrainedEpigraph (dom F) F =
      constrainedEpigraph Q (fun y ↦ (f y : WithTop ℝ)) := by
  ext p
  constructor
  · rintro ⟨hpdom, hpLe⟩
    have hpQ : p.1 ∈ Q := by
      simpa [dom_fenchelPrimalExtension] using hpdom
    refine mem_constrainedEpigraph_iff.2 ⟨hpQ, ?_⟩
    simpa [fenchelPrimalExtension_apply_of_mem hpQ] using hpLe
  · rintro ⟨hpQ, hpLe⟩
    refine mem_constrainedEpigraph_iff.2 ⟨?_, ?_⟩
    · simpa [dom_fenchelPrimalExtension] using hpQ
    · simpa [fenchelPrimalExtension_apply_of_mem hpQ] using hpLe

omit [FiniteDimensional ℝ E] in
/-- Helper for Theorem 5.1.17: the primal extension `F := fenchelPrimalExtension Q f` is a
closed convex extended-real function. -/
private theorem primalExtensionClosedConvex
    (hclosed : IsClosed (constrainedEpigraph Q (fun y ↦ (f y : WithTop ℝ))))
    (hself : IsSelfConcordantOnWith Q Mf f) :
    ClosedConvexFunction F := by
  refine ⟨subset_rfl, ?_, ?_⟩
  · -- The owner-level epigraph rewrite transfers the closedness hypothesis directly to `F`.
    rw [primalExtensionConstrainedEpigraph_eq (Q := Q) (f := f)]
    exact hclosed
  · -- Convexity of the epigraph is exactly the convexity of `f` on `Q`.
    let G : E → WithTop ℝ := fun y ↦ (f y : WithTop ℝ)
    have hconstrained :
        constrainedEpigraph Q G =
          {p : E × ℝ | p.1 ∈ Q ∧ withTopRealPart G p.1 ≤ p.2} :=
      constrainedEpigraph_eq_epigraph_withTopRealPart (hQ_dom := fun _ _ ↦ by simp [G])
    rw [primalExtensionConstrainedEpigraph_eq (Q := Q) (f := f), hconstrained]
    simpa [G, withTopRealPart] using hself.convexOn.convex_epigraph

omit [FiniteDimensional ℝ E] in
/-- Helper for Theorem 5.1.17: on an open domain where both summands are `C²`, the Hessian of the
sum is the sum of the Hessians at the base point. -/
private theorem hessian_add_eq_of_contDiffOn
    {s : Set E} {g₁ g₂ : E → ℝ} {x : E}
    (hg₁ : ContDiffOn ℝ 2 g₁ s) (hg₂ : ContDiffOn ℝ 2 g₂ s)
    (hopen : IsOpen s) (hx : x ∈ s) :
    hessian (g₁ + g₂) x = hessian g₁ x + hessian g₂ x := by
  have hgrad_nhds :
      (fun y ↦ ∇ (g₁ + g₂) y) =ᶠ[nhds x] fun y ↦ ∇ g₁ y + ∇ g₂ y := by
    -- Near `x`, both summands are differentiable, so the gradient of the sum is pointwise
    -- additive on that neighborhood.
    filter_upwards [hopen.mem_nhds hx] with y hy
    have hg₁y : DifferentiableAt ℝ g₁ y := by
      exact (hg₁.contDiffAt (hopen.mem_nhds hy)).differentiableAt (by norm_num)
    have hg₂y : DifferentiableAt ℝ g₂ y := by
      exact (hg₂.contDiffAt (hopen.mem_nhds hy)).differentiableAt (by norm_num)
    rw [gradient, fderiv_add hg₁y hg₂y]
    simp [gradient]
  have hgrad₁ : DifferentiableAt ℝ (∇ g₁) x := by
    -- A `C²` function has a differentiable gradient field on the open domain.
    let D : StrongDual ℝ E →L[ℝ] E :=
      (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
    have hfderiv :
        DifferentiableAt ℝ (fderiv ℝ g₁) x := by
      exact
        ((hg₁.contDiffAt (hopen.mem_nhds hx)).fderiv_right
          (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)).differentiableAt one_ne_zero
    simpa [gradient, D] using D.differentiableAt.comp x hfderiv
  have hgrad₂ : DifferentiableAt ℝ (∇ g₂) x := by
    -- The same `C²` argument applies to the second summand.
    let D : StrongDual ℝ E →L[ℝ] E :=
      (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
    have hfderiv :
        DifferentiableAt ℝ (fderiv ℝ g₂) x := by
      exact
        ((hg₂.contDiffAt (hopen.mem_nhds hx)).fderiv_right
          (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)).differentiableAt one_ne_zero
    simpa [gradient, D] using D.differentiableAt.comp x hfderiv
  -- Differentiate the neighborhood identity for the gradient at the base point.
  rw [hessian, hgrad_nhds.fderiv_eq, fderiv_fun_add hgrad₁ hgrad₂]

omit [FiniteDimensional ℝ E] in
/-- Helper for Theorem 5.1.17: on an open self-concordant domain, the gradient field is
continuous. -/
private theorem gradient_continuousOn_selfConcordant
    {s : Set E} {Mf : NNReal} {g : E → ℝ}
    (hself : IsSelfConcordantOnWith s Mf g) :
    ContinuousOn (∇ g) s := by
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfd_cont : ContinuousOn (fderiv ℝ g) s := by
    exact
      ((hself.contDiffOn.of_le
          (show (2 : WithTop ℕ∞) ≤ 3 by norm_num)).fderiv_of_isOpen
          hself.isOpen_domain
          (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)).continuousOn
  -- Rewrite the gradient through the Riesz map to transport continuity from `fderiv`.
  simpa [gradient, D] using D.continuous.comp_continuousOn hfd_cont

omit [FiniteDimensional ℝ E] in
/-- Helper for Theorem 5.1.17: scalarizing the gradient along an affine line differentiates to
the corresponding Hessian pairing. -/
private theorem scalarizedGradientLine_hasDerivAt
    {s : Set E} {Mf : NNReal} {g : E → ℝ}
    (hself : IsSelfConcordantOnWith s Mf g)
    {z d u : E} {t : ℝ} (hzt : z + t • d ∈ s) :
    HasDerivAt (fun r : ℝ ↦ inner ℝ (∇ g (z + r • d)) u)
      (inner ℝ (hessian g (z + t • d) d) u) t := by
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfderiv : DifferentiableAt ℝ (fderiv ℝ g) (z + t • d) := by
    -- The self-concordant `C³` owner makes the Fréchet derivative differentiable on the domain.
    have hcont : ContDiffAt ℝ 1 (fderiv ℝ g) (z + t • d) :=
      (hself.contDiffOn.contDiffAt
        (hself.isOpen_domain.mem_nhds hzt)).fderiv_right
          (show (1 : WithTop ℕ∞) + 1 ≤ 3 by norm_num)
    exact hcont.differentiableAt one_ne_zero
  have hgrad : DifferentiableAt ℝ (∇ g) (z + t • d) := by
    -- Rewrite the gradient through the Riesz map before differentiating it.
    simpa [gradient, D] using D.differentiableAt.comp (z + t • d) hfderiv
  have hgradLine :
      HasFDerivAt (fun r : ℝ ↦ ∇ g (z + r • d))
        ((hessian g (z + t • d)).comp (ContinuousLinearMap.toSpanSingleton ℝ d)) t := by
    -- Compose the gradient derivative with the affine-line derivative.
    simpa [one_smul] using
      (hgrad.hasFDerivAt.comp t (((hasDerivAt_id t).smul_const d).const_add z).hasFDerivAt)
  let φ : E →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ E) u
  have hscalar :
      HasFDerivAt (fun r : ℝ ↦ φ (∇ g (z + r • d)))
        (φ.comp ((hessian g (z + t • d)).comp (ContinuousLinearMap.toSpanSingleton ℝ d))) t := by
    -- Postcompose with the fixed scalar functional `v ↦ ⟪u, v⟫`.
    simpa [φ] using (φ.hasFDerivAt.comp t hgradLine)
  simpa [φ, InnerProductSpace.toDual_apply_apply, real_inner_comm] using hscalar.hasDerivAt

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- Helper for Theorem 5.1.17: Fenchel-support maximizers are exactly minimizers of the affine
tilt `withTopRealPart F - ⟪s, ·⟫` on `dom F`. -/
private theorem fenchelSupport_isMaxOn_iff_tiltedIsMinOn
    {s x : E} :
    IsMaxOn (fun y : E ↦ inner ℝ s y - withTopRealPart F y) (dom F) x ↔
      IsMinOn
        (quadraticAffineObjective 0 (-s) (0 : E →L[ℝ] E) + withTopRealPart F)
        (dom F) x := by
  constructor
  · intro hmax z hz
    have hsupport : inner ℝ s z - withTopRealPart F z ≤ inner ℝ s x - withTopRealPart F x :=
      hmax hz
    simpa [quadraticAffineObjective_zero_operator, sub_eq_add_neg, add_assoc, add_left_comm,
      add_comm] using (neg_le_neg hsupport)
  · intro hmin z hz
    let G : E → ℝ := quadraticAffineObjective 0 (-s) (0 : E →L[ℝ] E) + withTopRealPart F
    have htilt0 : G x ≤ G z := by
      simpa [Set.mem_setOf_eq, G] using (hmin hz)
    have htilt :
        withTopRealPart F x - inner ℝ s x ≤ withTopRealPart F z - inner ℝ s z := by
      simpa [G, quadraticAffineObjective_zero_operator, sub_eq_add_neg, add_left_comm, add_comm]
        using htilt0
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using (neg_le_neg htilt)

omit [FiniteDimensional ℝ E] in
/-- Helper for Theorem 5.1.17: at a fixed dual slope, Fenchel-support maximizers on `dom F` are
unique because the corresponding affine tilt remains self-concordant with positive-definite
Hessian on the same open domain. -/
private theorem supportMaximizer_eq_of_isMaxOn
    (hFself : IsSelfConcordantOnWith (dom F) Mf (withTopRealPart F))
    (hclosedFReal :
      IsClosed (constrainedEpigraph (dom F) (fun y ↦ (withTopRealPart F y : WithTop ℝ))))
    (hnoAffineLineF :
      ∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ dom F)
    {s x y : E}
    (hx : x ∈ dom F) (hy : y ∈ dom F)
    (hxmax : IsMaxOn (fun z : E ↦ inner ℝ s z - withTopRealPart F z) (dom F) x)
    (hymax : IsMaxOn (fun z : E ↦ inner ℝ s z - withTopRealPart F z) (dom F) y) :
    x = y := by
  let G : E → ℝ := quadraticAffineObjective 0 (-s) (0 : E →L[ℝ] E) + withTopRealPart F
  have hGself : IsSelfConcordantOnWith (dom F) Mf G := by
    -- Affine tilting preserves self-concordance on the same domain.
    simpa [G] using
      hFself.add_quadraticAffineObjective 0 (-s) (0 : E →L[ℝ] E)
        ContinuousLinearMap.isPositive_zero
  let hFqual : IsSelfConcordantOn (dom F) (withTopRealPart F) := ⟨Mf, hFself⟩
  letI : HasPositiveDefiniteHessianOn (dom F) (withTopRealPart F) :=
    IsSelfConcordantOn.hasPositiveDefiniteHessianOn_of_no_affine_line
      hFqual hclosedFReal hnoAffineLineF
  have hzeroSelfAdjoint : IsSelfAdjoint (0 : E →L[ℝ] E) := by
    simp
  have hPosDefG : HasPositiveDefiniteHessianOn (dom F) G := by
    refine ⟨?_, ?_⟩
    · intro z hz
      -- The affine tilt has the same Hessian as the primal finite real part.
      have hG_hessian :
          hessian G z = hessian (withTopRealPart F) z := by
        have hquadContDiff :
            ContDiffOn ℝ 2 (quadraticAffineObjective 0 (-s) (0 : E →L[ℝ] E)) (dom F) :=
          (quadraticAffineObjective_contDiff 0 (-s) (0 : E →L[ℝ] E)).of_le
            (by norm_num) |>.contDiffOn
        have hFContDiff :
            ContDiffOn ℝ 2 (withTopRealPart F) (dom F) := hFself.contDiffOn.of_le (by norm_num)
        calc
          hessian G z
              = hessian (quadraticAffineObjective 0 (-s) (0 : E →L[ℝ] E) + withTopRealPart F) z :=
                by rfl
          _ = hessian (quadraticAffineObjective 0 (-s) (0 : E →L[ℝ] E)) z +
                hessian (withTopRealPart F) z := by
              exact hessian_add_eq_of_contDiffOn hquadContDiff hFContDiff hFself.isOpen_domain hz
          _ = (0 : E →L[ℝ] E) + hessian (withTopRealPart F) z := by
              rw [quadraticAffineObjective_hessian_eq 0 (-s) (0 : E →L[ℝ] E) hzeroSelfAdjoint]
          _ = hessian (withTopRealPart F) z := by simp
      have hbase : (hessian (withTopRealPart F) z).IsPositive :=
        HasPositiveDefiniteHessianOn.hessian_isPositive_of_mem hz
      simpa [hG_hessian] using hbase
    · intro z hz u hu
      -- The same Hessian identity transports strict positivity of the quadratic form.
      have hG_hessian :
          hessian G z = hessian (withTopRealPart F) z := by
        have hquadContDiff :
            ContDiffOn ℝ 2 (quadraticAffineObjective 0 (-s) (0 : E →L[ℝ] E)) (dom F) :=
          (quadraticAffineObjective_contDiff 0 (-s) (0 : E →L[ℝ] E)).of_le
            (by norm_num) |>.contDiffOn
        have hFContDiff :
            ContDiffOn ℝ 2 (withTopRealPart F) (dom F) := hFself.contDiffOn.of_le (by norm_num)
        calc
          hessian G z
              = hessian (quadraticAffineObjective 0 (-s) (0 : E →L[ℝ] E) + withTopRealPart F) z :=
                by rfl
          _ = hessian (quadraticAffineObjective 0 (-s) (0 : E →L[ℝ] E)) z +
                hessian (withTopRealPart F) z := by
              exact hessian_add_eq_of_contDiffOn hquadContDiff hFContDiff hFself.isOpen_domain hz
          _ = (0 : E →L[ℝ] E) + hessian (withTopRealPart F) z := by
              rw [quadraticAffineObjective_hessian_eq 0 (-s) (0 : E →L[ℝ] E) hzeroSelfAdjoint]
          _ = hessian (withTopRealPart F) z := by simp
      have hbase : 0 < inner ℝ u ((hessian (withTopRealPart F) z) u) :=
        HasPositiveDefiniteHessianOn.posdef hz hu
      simpa [hG_hessian] using hbase
  haveI : HasPositiveDefiniteHessianOn (dom F) G := hPosDefG
  have hxmin : IsMinOn G (dom F) x :=
    (fenchelSupport_isMaxOn_iff_tiltedIsMinOn (Q := Q) (f := f)).1 hxmax
  have hymin : IsMinOn G (dom F) y :=
    (fenchelSupport_isMaxOn_iff_tiltedIsMinOn (Q := Q) (f := f)).1 hymax
  have hxGrad : ∇ G x = 0 := by
    have hlocal : IsLocalMin G x := hxmin.isLocalMin (hGself.isOpen_domain.mem_nhds hx)
    exact isLocalMin_gradient_eq_zero hlocal
  have hyGrad : ∇ G y = 0 := by
    have hlocal : IsLocalMin G y := hymin.isLocalMin (hGself.isOpen_domain.mem_nhds hy)
    exact isLocalMin_gradient_eq_zero hlocal
  by_contra hxy
  let d : E := y - x
  have hd : d ≠ 0 := by
    intro hd0
    apply hxy
    simpa [d] using (sub_eq_zero.mp hd0).symm
  let φ : ℝ → ℝ := fun r ↦ inner ℝ (∇ G (x + r • d)) d
  have hsegment_mem :
      Set.MapsTo (fun r : ℝ ↦ x + r • d) (Set.Icc (0 : ℝ) 1) (dom F) := by
    intro r hr
    simpa [d] using hGself.convex_domain.add_smul_sub_mem hx hy hr
  have hφ_cont : ContinuousOn φ (Set.Icc (0 : ℝ) 1) := by
    have hgrad_cont : ContinuousOn (∇ G) (dom F) :=
      gradient_continuousOn_selfConcordant hGself
    have hlineMap_cont : Continuous fun r : ℝ ↦ x + r • d := by
      continuity
    have hline_cont :
        ContinuousOn (fun r : ℝ ↦ ∇ G (x + r • d)) (Set.Icc (0 : ℝ) 1) :=
      hgrad_cont.comp hlineMap_cont.continuousOn hsegment_mem
    -- Scalarize the continuous gradient line by pairing with the fixed chord direction `d`.
    simpa [φ] using hline_cont.inner continuousOn_const
  have hφ_deriv_pos : ∀ r ∈ interior (Set.Icc (0 : ℝ) 1), 0 < deriv φ r := by
    intro r hr
    have hr' : r ∈ Set.Ioo (0 : ℝ) 1 := by
      simpa [interior_Icc] using hr
    have hline_mem : x + r • d ∈ dom F :=
      hsegment_mem (Set.mem_Icc_of_Ioo hr')
    have hderiv :
        HasDerivAt φ (inner ℝ (hessian G (x + r • d) d) d) r := by
      simpa [φ] using
        scalarizedGradientLine_hasDerivAt hGself
          (z := x) (d := d) (u := d) hline_mem
    have hpos : 0 < inner ℝ (hessian G (x + r • d) d) d := by
      simpa [real_inner_comm] using
        (HasPositiveDefiniteHessianOn.posdef hline_mem hd :
          0 < inner ℝ d (hessian G (x + r • d) d))
    -- Positive-definite Hessians force strict growth of the scalarized gradient along the chord.
    simpa [hderiv.deriv] using hpos
  have hstrict : StrictMonoOn φ (Set.Icc (0 : ℝ) 1) :=
    strictMonoOn_of_deriv_pos (convex_Icc (0 : ℝ) 1) hφ_cont hφ_deriv_pos
  have hlt : φ 0 < φ 1 :=
    hstrict (by simp) (by simp) (by norm_num)
  have hφ0 : φ 0 = 0 := by
    simp [φ, d, hxGrad]
  have hφ1 : φ 1 = 0 := by
    simp [φ, d, hyGrad]
  linarith [hlt, hφ0, hφ1]

/-- Helper for Theorem 5.1.17: under the Chapter 5 maximizing-branch hypotheses, the canonical
dual gradient is `C²` at each dual-domain slope because it agrees locally with the inverse
function theorem local inverse of the primal gradient. -/
private theorem dualGradient_contDiffAtTwo_of_supportMaximizer
    {f : E → WithTop ℝ} {xStar : E → E}
    (hf_closedConvex : ClosedConvexFunction f)
    (hself : IsSelfConcordantOn (interior (dom f)) (withTopRealPart f))
    (hxStar_mem : ∀ ⦃s : E⦄, s ∈ dom (f⋆) → xStar s ∈ interior (dom f))
    (hxStar_isMaximizer :
      ∀ ⦃s : E⦄, s ∈ dom (f⋆) →
        IsMaxOn (fun y : E ↦ inner ℝ s y - withTopRealPart f y) (dom f) (xStar s))
    (hxStar_unique :
      ∀ ⦃s x : E⦄, s ∈ dom (f⋆) → x ∈ dom f →
        IsMaxOn (fun y : E ↦ inner ℝ s y - withTopRealPart f y) (dom f) x → x = xStar s)
    {s : E} (hs : s ∈ dom (f⋆)) :
    ContDiffAt ℝ 2 (∇ (extendedRealRealPart (f⋆))) s := by
  let G : E → E := ∇ (withTopRealPart f)
  let x : E := xStar s
  let H : E →L[ℝ] E := hessian (withTopRealPart f) x
  have hf_contDiff : ContDiffOn ℝ 2 (withTopRealPart f) (interior (dom f)) := by
    -- The self-concordant primal owner supplies the `C²` regularity for the gradient map.
    rcases hself with ⟨Mf, hMf⟩
    exact hMf.contDiffOn.of_le (by norm_num)
  have hcontAt : ContDiffAt ℝ 3 (withTopRealPart f) x := by
    -- Restrict the primal `C³` regularity to the selected interior support maximizer.
    rcases hself with ⟨_, hselfWith⟩
    exact hselfWith.contDiffOn.contDiffAt (IsOpen.mem_nhds isOpen_interior (hxStar_mem hs))
  have hx_grad : G x = s := by
    -- The selected branch point satisfies the source first-order stationarity equation.
    simpa [G, x] using
      gradient_eq_of_fenchelSupport_isMaxOn_interior (f := f) hf_contDiff (hxStar_mem hs)
        (hxStar_isMaximizer hs)
  have hgrad_C2 : ContDiffAt ℝ 2 G x := by
    let D : StrongDual ℝ E →L[ℝ] E :=
      (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
    have hfderiv_C2 : ContDiffAt ℝ 2 (fderiv ℝ (withTopRealPart f)) x := by
      -- Differentiating the primal finite real part once leaves a `C²` derivative field.
      exact hcontAt.fderiv_right (by norm_num : (2 : WithTop ℕ∞) + 1 ≤ 3)
    have hD_contDiffAt : ContDiffAt ℝ 2 D (fderiv ℝ (withTopRealPart f) x) := by
      exact (D.contDiff.of_le (show (2 : WithTop ℕ∞) ≤ ⊤ by simp)).contDiffAt
    simpa [G, gradient, D] using hD_contDiffAt.comp x hfderiv_C2
  have hgrad_fderiv : HasFDerivAt G H x := by
    let D : StrongDual ℝ E →L[ℝ] E :=
      (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
    have hfderiv :
        DifferentiableAt ℝ (fderiv ℝ (withTopRealPart f)) x := by
      have hcont : ContDiffAt ℝ 1 (fderiv ℝ (withTopRealPart f)) x :=
        hcontAt.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 3)
      exact hcont.differentiableAt one_ne_zero
    have hgrad : DifferentiableAt ℝ G x := by
      -- Rewrite the primal gradient through the Riesz map before reading off its derivative.
      simpa [G, gradient, D] using D.differentiableAt.comp x hfderiv
    simpa [G, H, hessian] using hgrad.hasFDerivAt
  have hinterior_nonempty : (interior (dom f)).Nonempty := ⟨xStar s, hxStar_mem hs⟩
  have hinv : H.IsInvertible := by
    -- Proposition 5.0.29 gives invertibility of the primal Hessian at the branch point.
    simpa [H, x] using
      (fenchelConjugate_primalHessian_isInvertible_of_fenchelSupport_isMaxOn
        (f := f) hf_closedConvex hself hinterior_nonempty hs (hxStar_mem hs)
        (hxStar_isMaximizer hs) (fun {y} hy hymax ↦ hxStar_unique hs hy hymax))
  let e : E ≃L[ℝ] E := Classical.choose hinv
  have he : (e : E →L[ℝ] E) = H := Classical.choose_spec hinv
  have hgrad_fderiv_e : HasFDerivAt G (e : E →L[ℝ] E) x := by
    -- Normalize the chosen equivalence back to the primal Hessian derivative.
    simpa [he] using hgrad_fderiv
  have hstrict : HasStrictFDerivAt G (e : E →L[ℝ] E) x := by
    -- A `C²` primal gradient upgrades its derivative to the strict form used by the IFT.
    exact hgrad_C2.hasStrictFDerivAt' hgrad_fderiv_e (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  have hleft :
      ∀ᶠ y in nhds x, ∇ (extendedRealRealPart (f⋆)) (G y) = y := by
    have hmemInterior : ∀ᶠ y in nhds x, y ∈ interior (dom f) := by
      -- The local inverse theorem only needs a neighborhood staying inside the primal interior.
      exact IsOpen.mem_nhds isOpen_interior (hxStar_mem hs)
    filter_upwards [hmemInterior] with y hy
    let t : E := G y
    have hy_isMaximizer :
        IsMaxOn (fun z : E ↦ inner ℝ t z - withTopRealPart f z) (dom f) y := by
      -- Any interior primal point maximizes the support model at its own gradient.
      simpa [G, t] using
        fenchelSupport_isMaxOn_of_gradient_eq_interior
          (f := f) hf_closedConvex hf_contDiff hy
          (show ∇ (withTopRealPart f) y = t by rfl)
    have ht : t ∈ dom (f⋆) :=
      mem_dom_fenchelDual_of_isMaxOn (f := f) (s := t) (x := y) (interior_subset hy)
        hy_isMaximizer
    have hdual_grad :
        HasGradientAt (extendedRealRealPart (f⋆)) (xStar t) t :=
      fenchelConjugate_hasGradientAt
        (f := f) (xStar := xStar) hf_closedConvex hself ⟨xStar t, hxStar_mem ht⟩
        hxStar_mem hxStar_isMaximizer hxStar_unique ht
    have hy_eq : y = xStar t := hxStar_unique ht (interior_subset hy) hy_isMaximizer
    -- Uniqueness identifies the dual gradient with the primal point near the base branch point.
    simpa [G, t] using hdual_grad.gradient.trans hy_eq.symm
  have hdual_eventuallyEq_localInverse :
      ∇ (extendedRealRealPart (f⋆)) =ᶠ[nhds s]
        hgrad_C2.localInverse hgrad_fderiv_e (by norm_num : (2 : WithTop ℕ∞) ≠ 0) := by
    -- The canonical dual gradient is the IFT local inverse of the primal gradient near `s`.
    simpa [G, x, hx_grad] using
      (hstrict.localInverse_unique (g := ∇ (extendedRealRealPart (f⋆))) hleft)
  have hlocalInverse_C2 :
      ContDiffAt ℝ 2
        (hgrad_C2.localInverse hgrad_fderiv_e (by norm_num : (2 : WithTop ℕ∞) ≠ 0)) s := by
    -- The inverse-function theorem supplies `C²` regularity of that local inverse.
    simpa [G, x, hx_grad] using
      hgrad_C2.to_localInverse hgrad_fderiv_e (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  -- Transport the `C²` regularity from the local inverse to the canonical dual gradient.
  exact hlocalInverse_C2.congr_of_eventuallyEq hdual_eventuallyEq_localInverse

omit [FiniteDimensional ℝ E] in
/-- Helper for Theorem 5.1.17: a `C³` primal finite real part gives a `C²` primal gradient map
at the point where the inverse-Hessian family is differentiated. -/
private theorem primalGradientContDiffAt_of_contDiffAtThree
    {f : E → WithTop ℝ} {x : E}
    (hcontAt : ContDiffAt ℝ 3 (withTopRealPart f) x) :
    ContDiffAt ℝ 2 (∇ (withTopRealPart f)) x := by
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfderiv_C2 : ContDiffAt ℝ 2 (fderiv ℝ (withTopRealPart f)) x := by
    -- First differentiate the primal finite real part once and keep the two remaining
    -- derivatives.
    exact hcontAt.fderiv_right (by norm_num : (2 : WithTop ℕ∞) + 1 ≤ 3)
  have hD_contDiffAt : ContDiffAt ℝ 2 D (fderiv ℝ (withTopRealPart f) x) := by
    exact ((D.contDiff.of_le (show (2 : WithTop ℕ∞) ≤ ⊤ by simp)).contDiffAt)
  -- Rewrite the gradient through the Riesz map so the remaining regularity becomes `C²`.
  simpa [gradient, D] using hD_contDiffAt.comp x hfderiv_C2

omit [FiniteDimensional ℝ E] in
/-- Helper for Theorem 5.1.17: at an interior point with invertible primal Hessian, the
inverse-Hessian family is genuinely differentiable. -/
private theorem inverseHessianDifferentiableAt
    {f : E → WithTop ℝ} {x : E}
    (hf_contDiff : ContDiffOn ℝ 3 (withTopRealPart f) (interior (dom f)))
    (hx : x ∈ interior (dom f))
    (hinv : (hessian (withTopRealPart f) x).IsInvertible) :
    DifferentiableAt ℝ (fun y ↦ (hessian (withTopRealPart f) y).inverse) x := by
  have hcontAt : ContDiffAt ℝ 3 (withTopRealPart f) x := by
    -- Restrict the `C³` hypothesis to the interior point `x`.
    exact hf_contDiff.contDiffAt (IsOpen.mem_nhds isOpen_interior hx)
  have hgrad_C2 : ContDiffAt ℝ 2 (∇ (withTopRealPart f)) x :=
    primalGradientContDiffAt_of_contDiffAtThree hcontAt
  rcases exists_continuousLinearEquiv_fderiv_symm_eq hgrad_C2 hinv with
    ⟨N, -, hN_symm_C1, hN, -⟩
  have hEq : (fun y ↦ ((N y).symm : E →L[ℝ] E)) =ᶠ[nhds x]
      fun y ↦ (hessian (withTopRealPart f) y).inverse := by
    -- Near `x`, the chosen local equivalence family is exactly the primal Hessian family, so its
    -- inverse family is the genuine inverse-Hessian branch.
    filter_upwards [hN] with y hy
    have hy_inverse :
        (fderiv ℝ (∇ (withTopRealPart f)) y).inverse = ((N y).symm : E →L[ℝ] E) := by
      simpa [hy] using
        (ContinuousLinearMap.inverse_equiv (N y) :
          (N y : E →L[ℝ] E).inverse = (N y).symm)
    simpa [hessian] using hy_inverse.symm
  -- Transport differentiability from the smooth inverse family supplied by the local-inverse API.
  exact (hN_symm_C1.differentiableAt one_ne_zero).congr_of_eventuallyEq hEq.symm

omit [FiniteDimensional ℝ E] in
/-- Helper for Theorem 5.1.17: differentiating the genuine inverse-Hessian family at an interior
point gives the textbook `-H⁻¹ (DH) H⁻¹` formula. -/
private theorem inverseHessianFDerivEq
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
    primalGradientContDiffAt_of_contDiffAtThree hcontAt
  rcases exists_continuousLinearEquiv_fderiv_symm_eq hgrad_C2 hinv with
    ⟨N, -, -, hN, hN_deriv⟩
  have hxN_raw : (N x : E →L[ℝ] E) = fderiv ℝ (∇ (withTopRealPart f)) x := by
    exact hN.self_of_nhds
  have hxN : N x = hessian (withTopRealPart f) x := by
    -- At the base point, the local equivalence family recovers the primal Hessian itself.
    simpa [hessian] using hxN_raw
  have hEq : (fun y ↦ ((N y).symm : E →L[ℝ] E)) =ᶠ[nhds x]
      fun y ↦ (hessian (withTopRealPart f) y).inverse := by
    -- Near `x`, the inverse family from the local-inverse API is literally the inverse Hessian.
    filter_upwards [hN] with y hy
    have hy_inverse :
        (fderiv ℝ (∇ (withTopRealPart f)) y).inverse = ((N y).symm : E →L[ℝ] E) := by
      simpa [hy] using
        (ContinuousLinearMap.inverse_equiv (N y) :
          (N y : E →L[ℝ] E).inverse = (N y).symm)
    simpa [hessian] using hy_inverse.symm
  have hFderivEq :
      fderiv ℝ (fun y ↦ ((N y).symm : E →L[ℝ] E)) x =
        fderiv ℝ (fun y ↦ (hessian (withTopRealPart f) y).inverse) x :=
    Filter.EventuallyEq.fderiv_eq hEq
  calc
    fderiv ℝ (fun y ↦ (hessian (withTopRealPart f) y).inverse) x h
      = fderiv ℝ (fun y ↦ ((N y).symm : E →L[ℝ] E)) x h := by
          rw [← hFderivEq]
    _ = -(N x).symm ∘L ((fderiv ℝ (fderiv ℝ (∇ (withTopRealPart f))) x) h) ∘L (N x).symm := by
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
          simp [hessian, hx_inverse]

omit [FiniteDimensional ℝ E] in
/-- Helper for Theorem 5.1.17: once the maximizing branch derivative is available, the chain rule
differentiates the inverse primal Hessian along that branch. -/
private theorem inverseHessianAlongBranchFDerivEq
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
    -- The chosen maximizing branch is differentiable with the dual Hessian as derivative.
    hxStar_hasFDerivAt hs
  have hinverse_diff :
      DifferentiableAt ℝ (fun y ↦ (hessian (withTopRealPart f) y).inverse) (xStar s) := by
    -- The outer inverse-Hessian family is differentiable at the branch point.
    exact inverseHessianDifferentiableAt hf_contDiff (hxStar_mem hs) (hxStar_hessian_invertible hs)
  calc
    fderiv ℝ (fun t ↦ (hessian (withTopRealPart f) (xStar t)).inverse) s h
      = ((fderiv ℝ (fun y ↦ (hessian (withTopRealPart f) y).inverse) (xStar s)).comp
          (hessian (extendedRealRealPart (f⋆)) s)) h := by
          -- Differentiate the outer inverse-Hessian family after the maximizing branch.
          rw [show (fun t ↦ (hessian (withTopRealPart f) (xStar t)).inverse) =
            (fun y ↦ (hessian (withTopRealPart f) y).inverse) ∘ xStar from rfl]
          rw [fderiv_comp s hinverse_diff hbranch_hasFDerivAt.differentiableAt]
          simp [hbranch_hasFDerivAt.fderiv]
    _ = -((hessian (withTopRealPart f) (xStar s)).inverse.comp
        ((fderiv ℝ (hessian (withTopRealPart f)) (xStar s)
            ((hessian (extendedRealRealPart (f⋆)) s) h)).comp
          (hessian (withTopRealPart f) (xStar s)).inverse)) := by
          -- Evaluate the inverse-Hessian derivative on the branch direction.
          simpa using
            inverseHessianFDerivEq hf_contDiff (hxStar_mem hs) (hxStar_hessian_invertible hs)

/-- Theorem 5.1.17: let `F` be the `+∞`-extension of a real-valued function `f` off `Q`. If `f`
is self-concordant on `Q` with constant `M_f`, if the constrained epigraph of `f` over `Q` is
closed and `Q` contains no affine line, then the finite real part of the Fenchel dual `F⋆` is
self-concordant on its finite-value domain with the same constant `M_f`. -/
theorem fenchelPrimalExtension_dualRealPart_isSelfConcordantOnWith
    (hclosed : IsClosed (constrainedEpigraph Q (fun y ↦ (f y : WithTop ℝ))))
    (hnoAffineLine : ∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q)
    (hself : IsSelfConcordantOnWith Q Mf f) :
    IsSelfConcordantOnWith
      (dom (F⋆))
      Mf
      (extendedRealRealPart (F⋆)) := by
  let hFself : IsSelfConcordantOnWith (withTopEffectiveDomain F) Mf (withTopRealPart F) :=
    primalExtensionSelfConcordant (Q := Q) (Mf := Mf) (f := f) hself
  have hFselfDom : IsSelfConcordantOnWith (dom F) Mf (withTopRealPart F) := by
    simpa [dom_fenchelPrimalExtension] using hFself
  have hFclosedConvex : ClosedConvexFunction F :=
    primalExtensionClosedConvex (Q := Q) (Mf := Mf) (f := f) hclosed hself
  have hFselfQual : IsSelfConcordantOn (dom F) (withTopRealPart F) := by
    -- Package the quantitative owner as the qualitative self-concordance input used by
    -- Lemma 5.1.6.
    refine ⟨Mf, ?_⟩
    simpa [dom_fenchelPrimalExtension] using hFself
  let hFqual : IsSelfConcordantOn (interior (withTopEffectiveDomain F)) (withTopRealPart F) := by
    have hInteriorEq : interior Q = Q := by
      simpa [dom_fenchelPrimalExtension] using hFself.isOpen_domain.interior_eq
    refine ⟨Mf, ?_⟩
    simpa [dom_fenchelPrimalExtension, hInteriorEq] using hFself
  have _hself_primalInterior :
      IsSelfConcordantOn (interior (withTopEffectiveDomain F)) (withTopRealPart F) := hFqual
  have hclosedFReal :
      IsClosed (constrainedEpigraph (dom F) (fun y ↦ (withTopRealPart F y : WithTop ℝ))) := by
    let G : E → WithTop ℝ := fun y ↦ (withTopRealPart F y : WithTop ℝ)
    have hEq :
        constrainedEpigraph (dom F) F = constrainedEpigraph (dom F) G := by
      ext p
      constructor
      · rintro ⟨hpdom, hpLe⟩
        have hpLeReal : withTopRealPart F p.1 ≤ p.2 :=
          (withTopRealPart_le_iff hpdom).2 hpLe
        refine mem_constrainedEpigraph_iff.2 ⟨hpdom, ?_⟩
        simpa [G] using
          (show (((withTopRealPart F p.1 : ℝ) : WithTop ℝ) ≤ (p.2 : WithTop ℝ)) from by
            exact_mod_cast hpLeReal)
      · rintro ⟨hpdom, hpLe⟩
        have hpLeReal : withTopRealPart F p.1 ≤ p.2 := by
          simpa [G] using hpLe
        exact mem_constrainedEpigraph_iff.2
          ⟨hpdom, (withTopRealPart_le_iff hpdom).1 hpLeReal⟩
    rw [← hEq]
    exact hFclosedConvex.isClosed_constrainedEpigraph
  have hnoAffineLineF :
      ∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ dom F := by
    intro x h hh
    simpa [dom_fenchelPrimalExtension] using hnoAffineLine (x := x) (h := h) hh
  have hdualImage :
      dom (F⋆) = ∇ (withTopRealPart F) '' dom F := by
    -- Lemma 5.1.6 packages the dual effective domain as the primal gradient image.
    exact
      dom_fenchelDual_eq_image_gradient_of_selfConcordant
        (f := F) hclosedFReal hFselfQual hnoAffineLineF
  have hdualOpen : IsOpen (dom (F⋆)) := by
    -- The same Lemma 5.1.6 also gives openness of the dual effective domain.
    exact
      isOpen_dom_fenchelDual_of_selfConcordant
        (f := F) hclosedFReal hFselfQual hnoAffineLineF
  have hdualConvexOn :
      ConvexOn ℝ (dom (F⋆)) (extendedRealRealPart (F⋆)) := by
    -- Exception: use the already imported Chapter 6 closed-convex epigraph owner to recover the
    -- canonical convexity surface of `F⋆`.
    have hdualEpiConvex : Convex ℝ (effectiveEpigraph (F⋆)) :=
      (fenchelDual_effectiveEpigraph_closed_convex F).2
    simpa [effectiveEpigraph] using
      ((convexOn_iff_convex_epigraph :
          ConvexOn ℝ (dom (F⋆)) (extendedRealRealPart (F⋆)) ↔
            Convex ℝ {p : E × ℝ |
              p.1 ∈ dom (F⋆) ∧ extendedRealRealPart (F⋆) p.1 ≤ p.2}).2
        hdualEpiConvex)
  have hxStar_exists :
      ∀ ⦃s : E⦄, s ∈ dom (F⋆) → ∃ x ∈ dom F, ∇ (withTopRealPart F) x = s := by
    intro s hs
    rw [hdualImage] at hs
    rcases hs with ⟨x, hx, hxgrad⟩
    exact ⟨x, hx, hxgrad⟩
  classical
  let xStar : E → E := fun s ↦
    if hs : s ∈ dom (F⋆) then Classical.choose (hxStar_exists hs) else 0
  have hFContDiffOnTwo :
      ContDiffOn ℝ 2 (withTopRealPart F) (interior (dom F)) := by
    exact hFselfDom.isOpen_domain.interior_eq.symm ▸
      hFselfDom.contDiffOn.of_le (show (2 : WithTop ℕ∞) ≤ 3 by norm_num)
  have hxStar_dom :
      ∀ ⦃s : E⦄, s ∈ dom (F⋆) → xStar s ∈ dom F := by
    intro s hs
    dsimp [xStar]
    split_ifs with h
    · exact (Classical.choose_spec (hxStar_exists hs)).1
    · contradiction
  have hxStar_mem :
      ∀ ⦃s : E⦄, s ∈ dom (F⋆) → xStar s ∈ interior (dom F) := by
    intro s hs
    exact hFselfDom.isOpen_domain.interior_eq.symm ▸ hxStar_dom hs
  have hxStar_grad :
      ∀ ⦃s : E⦄, s ∈ dom (F⋆) → ∇ (withTopRealPart F) (xStar s) = s := by
    intro s hs
    dsimp [xStar]
    split_ifs with h
    · exact (Classical.choose_spec (hxStar_exists hs)).2
    · contradiction
  have hxStar_isMaximizer :
      ∀ ⦃s : E⦄, s ∈ dom (F⋆) →
        IsMaxOn (fun y : E ↦ inner ℝ s y - withTopRealPart F y) (dom F) (xStar s) := by
    intro s hs
    -- The chosen branch point is interior and has gradient `s`, so it maximizes the support
    -- functional at slope `s`.
    exact
      fenchelSupport_isMaxOn_of_gradient_eq_interior hFclosedConvex hFContDiffOnTwo
        (hxStar_mem hs) (hxStar_grad hs)
  have hxStar_unique :
      ∀ ⦃s x : E⦄, s ∈ dom (F⋆) → x ∈ dom F →
        IsMaxOn (fun y : E ↦ inner ℝ s y - withTopRealPart F y) (dom F) x → x = xStar s := by
    intro s x hs hx hmax
    -- The affine-tilt route reduces support-maximizer uniqueness to the already-proved
    -- uniqueness of minimizers for self-concordant functions with positive-definite Hessian.
    exact
      supportMaximizer_eq_of_isMaxOn (Q := Q) (f := f) hFselfDom hclosedFReal hnoAffineLineF hx
        (hxStar_dom hs) hmax (hxStar_isMaximizer hs)
  have hFselfInterior : IsSelfConcordantOn (interior (dom F)) (withTopRealPart F) := by
    -- Proposition 5.0.29 is stated on `interior (dom F)`, so rewrite the open primal domain once.
    exact hFselfDom.isOpen_domain.interior_eq.symm ▸ hFselfQual
  have hFselfInteriorWith : IsSelfConcordantOnWith (interior (dom F)) Mf (withTopRealPart F) := by
    -- Keep the quantitative primal owner available for the inverse-Hessian derivative argument.
    simpa [dom_fenchelPrimalExtension, hself.isOpen_domain.interior_eq] using hFself
  have hdualGradient_hasFDerivAt :
      ∀ ⦃s : E⦄, s ∈ dom (F⋆) →
        HasFDerivAt (∇ (extendedRealRealPart (F⋆)))
          (hessian (extendedRealRealPart (F⋆)) s) s := by
    intro s hs
    let G : E → E := ∇ (withTopRealPart F)
    let x : E := xStar s
    let H : E →L[ℝ] E := hessian (withTopRealPart F) x
    have hinterior_nonempty : (interior (dom F)).Nonempty := ⟨xStar s, hxStar_mem hs⟩
    have hx_grad : G x = s := by
      -- The chosen support maximizer is a primal point whose gradient is the current dual slope.
      simpa [G, x] using hxStar_grad hs
    have hinv : H.IsInvertible := by
      -- Proposition 5.0.29 gives invertibility of the primal Hessian at the support maximizer.
      simpa [H, x] using
        (fenchelConjugate_primalHessian_isInvertible_of_fenchelSupport_isMaxOn
          (f := F) hFclosedConvex hFselfInterior hinterior_nonempty hs (hxStar_mem hs)
          (hxStar_isMaximizer hs) (fun {y} hy hymax ↦ hxStar_unique hs hy hymax))
    let e : E ≃L[ℝ] E := Classical.choose hinv
    have he : (e : E →L[ℝ] E) = H := Classical.choose_spec hinv
    have hgrad_C1 : ContDiffAt ℝ 1 G x := by
      let D : StrongDual ℝ E →L[ℝ] E :=
        (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
      have hfderiv_C1 : ContDiffAt ℝ 1 (fderiv ℝ (withTopRealPart F)) x := by
        -- The primal finite real part is `C²` on the open primal domain.
        exact
          (hFContDiffOnTwo.contDiffAt
            (IsOpen.mem_nhds isOpen_interior (hxStar_mem hs))).fderiv_right
            (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
      simpa [G, gradient, D] using D.contDiff.contDiffAt.comp x hfderiv_C1
    have hgrad_fderiv : HasFDerivAt G H x := by
      let D : StrongDual ℝ E →L[ℝ] E :=
        (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
      have hfderiv :
          DifferentiableAt ℝ (fderiv ℝ (withTopRealPart F)) x := by
        have hcont : ContDiffAt ℝ 1 (fderiv ℝ (withTopRealPart F)) x :=
          (hFContDiffOnTwo.contDiffAt
            (IsOpen.mem_nhds isOpen_interior (hxStar_mem hs))).fderiv_right
            (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
        exact hcont.differentiableAt one_ne_zero
      have hgrad : DifferentiableAt ℝ G x := by
        -- Rewrite the gradient through the Riesz map before differentiating it.
        simpa [G, gradient, D] using D.differentiableAt.comp x hfderiv
      simpa [G, H, hessian] using hgrad.hasFDerivAt
    have hgrad_fderiv_e : HasFDerivAt G (e : E →L[ℝ] E) x := by
      -- Normalize the chosen equivalence back to the Hessian derivative.
      simpa [he] using hgrad_fderiv
    have hstrict : HasStrictFDerivAt G (e : E →L[ℝ] E) x := by
      -- A `C¹` gradient field upgrades its derivative to the strict derivative form of the IFT.
      exact hgrad_C1.hasStrictFDerivAt' hgrad_fderiv_e one_ne_zero
    have he_inverse : (e.symm : E →L[ℝ] E) = H.inverse := by
      -- Rewrite the inverse equivalence through the project's totalized operator inverse.
      calc
        (e.symm : E →L[ℝ] E) = (e : E →L[ℝ] E).inverse := by
          symm
          exact ContinuousLinearMap.inverse_equiv e
        _ = H.inverse := by
          simp [he]
    have hleft :
        ∀ᶠ y in nhds x, ∇ (extendedRealRealPart (F⋆)) (G y) = y := by
      have hmemInterior : ∀ᶠ y in nhds x, y ∈ interior (dom F) := by
        -- The local inverse theorem only needs a neighborhood where primal points stay interior.
        exact IsOpen.mem_nhds isOpen_interior (hxStar_mem hs)
      filter_upwards [hmemInterior] with y hy
      let t : E := G y
      have hy_isMaximizer :
          IsMaxOn (fun z : E ↦ inner ℝ t z - withTopRealPart F z) (dom F) y := by
        -- Any interior primal point maximizes the support model at its own gradient.
        simpa [G, t] using
          fenchelSupport_isMaxOn_of_gradient_eq_interior
            (f := F) hFclosedConvex hFContDiffOnTwo hy
            (show ∇ (withTopRealPart F) y = t by rfl)
      have ht : t ∈ dom (F⋆) :=
        mem_dom_fenchelDual_of_isMaxOn (f := F) (s := t) (x := y) (interior_subset hy)
          hy_isMaximizer
      have hdual_grad :
          HasGradientAt (extendedRealRealPart (F⋆)) (xStar t) t :=
        fenchelConjugate_hasGradientAt
          (f := F) (xStar := xStar) hFclosedConvex hFselfInterior hinterior_nonempty
          hxStar_mem hxStar_isMaximizer hxStar_unique ht
      have hy_eq : y = xStar t := hxStar_unique ht (interior_subset hy) hy_isMaximizer
      -- Uniqueness identifies the dual gradient with the original primal point near `xStar s`.
      simpa [G, t] using hdual_grad.gradient.trans hy_eq.symm
    have hdual_strict :
        HasStrictFDerivAt (∇ (extendedRealRealPart (F⋆))) H.inverse s := by
      -- The dual gradient is the local left inverse of the primal gradient at slope `s`.
      simpa [G, H, x, hx_grad, he_inverse] using
        (hstrict.to_local_left_inverse (g := ∇ (extendedRealRealPart (F⋆))) hleft)
    have hdual_hessian :
        hessian (extendedRealRealPart (F⋆)) s = H.inverse := by
      -- Proposition 5.0.29 identifies the dual Hessian with the inverse primal Hessian here.
      simpa [H, x] using
        (fenchelConjugate_hessian_eq_inverse
          (f := F) (xStar := xStar) hFclosedConvex hFselfInterior hinterior_nonempty
          hxStar_mem hxStar_isMaximizer hxStar_unique hs)
    -- Read the dual Hessian as the derivative of the dual gradient.
    simpa [hdual_hessian] using hdual_strict.hasFDerivAt
  have hxStar_eventuallyEq_dualGradient :
      ∀ ⦃s : E⦄, s ∈ dom (F⋆) →
        xStar =ᶠ[nhds s] ∇ (extendedRealRealPart (F⋆)) := by
    intro s hs
    -- On the open dual domain, the chosen branch agrees pointwise with the canonical dual
    -- gradient from Proposition 5.0.29.
    filter_upwards [hdualOpen.mem_nhds hs] with t ht
    exact (fenchelConjugate_hasGradientAt
      (f := F) (xStar := xStar) hFclosedConvex hFselfInterior ⟨xStar t, hxStar_mem ht⟩
      hxStar_mem hxStar_isMaximizer hxStar_unique ht).gradient.symm
  have hxStar_hasFDerivAt :
      ∀ ⦃s : E⦄, s ∈ dom (F⋆) →
        HasFDerivAt xStar (hessian (extendedRealRealPart (F⋆)) s) s := by
    intro s hs
    -- Transfer the derivative from the canonical dual gradient across the neighborhood equality.
    exact (hdualGradient_hasFDerivAt hs).congr_of_eventuallyEq (hxStar_eventuallyEq_dualGradient hs)
  have hdualGradient_contDiffOnTwo :
      ContDiffOn ℝ 2 (∇ (extendedRealRealPart (F⋆))) (dom (F⋆)) := by
    intro s hs
    -- The pointwise inverse-function-theorem argument upgrades the canonical dual gradient to a
    -- `C²` field on the entire open dual domain.
    exact
      (dualGradient_contDiffAtTwo_of_supportMaximizer
        (f := F) (xStar := xStar) hFclosedConvex hFselfInterior
        hxStar_mem hxStar_isMaximizer hxStar_unique hs).contDiffWithinAt
  have hdualContDiffOn :
      ContDiffOn ℝ 3 (extendedRealRealPart (F⋆)) (dom (F⋆)) := by
    -- The dual finite real part is `C³` once its gradient is known to be `C²` on the open dual
    -- domain and the Chapter 5 gradient owner gives the derivative formula there.
    refine
      (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn
        (n := 2) hdualOpen.uniqueDiffOn).2 ?_
    refine
      ⟨?_, fun s ↦ (InnerProductSpace.toDual ℝ E) (∇ (extendedRealRealPart (F⋆)) s), ?_, ?_⟩
    · intro hω
      cases hω
    · have hmaps :
          Set.MapsTo (∇ (extendedRealRealPart (F⋆))) (dom (F⋆)) Set.univ := by
        intro y hy
        simp
      simpa [Function.comp] using
        ((InnerProductSpace.toDual ℝ E).contDiff.contDiffOn.comp hdualGradient_contDiffOnTwo hmaps)
    · intro s hs
      have hgrad :
          ∇ (extendedRealRealPart (F⋆)) s = xStar s :=
        (fenchelConjugate_hasGradientAt
          (f := F) (xStar := xStar) hFclosedConvex hFselfInterior ⟨xStar s, hxStar_mem hs⟩
          hxStar_mem hxStar_isMaximizer hxStar_unique hs).gradient
      simpa [hgrad] using
        (fenchelConjugate_hasGradientAt
          (f := F) (xStar := xStar) hFclosedConvex hFselfInterior ⟨xStar s, hxStar_mem hs⟩
          hxStar_mem hxStar_isMaximizer hxStar_unique hs).hasFDerivAt.hasFDerivWithinAt
  have hxStar_hessian_invertible :
      ∀ ⦃s : E⦄, s ∈ dom (F⋆) →
        (hessian (withTopRealPart F) (xStar s)).IsInvertible := by
    intro s hs
    have hinterior_nonempty : (interior (dom F)).Nonempty := ⟨xStar s, hxStar_mem hs⟩
    -- Proposition 5.0.29 makes the primal Hessian invertible at each selected support maximizer.
    simpa using
      (fenchelConjugate_primalHessian_isInvertible_of_fenchelSupport_isMaxOn
        (f := F) hFclosedConvex hFselfInterior hinterior_nonempty hs (hxStar_mem hs)
        (hxStar_isMaximizer hs) (fun {y} hy hymax ↦ hxStar_unique hs hy hymax))
  have hdualHessian_eq_inverse :
      ∀ ⦃s : E⦄, s ∈ dom (F⋆) →
        hessian (extendedRealRealPart (F⋆)) s =
          (hessian (withTopRealPart F) (xStar s)).inverse := by
    intro s hs
    have hinterior_nonempty : (interior (dom F)).Nonempty := ⟨xStar s, hxStar_mem hs⟩
    -- Proposition 5.0.29 also identifies the dual Hessian with the inverse primal Hessian.
    simpa using
      (fenchelConjugate_hessian_eq_inverse
        (f := F) (xStar := xStar) hFclosedConvex hFselfInterior hinterior_nonempty
        hxStar_mem hxStar_isMaximizer hxStar_unique hs)
  have dualHessianDerivative_formula :
      ∀ ⦃s : E⦄, s ∈ dom (F⋆) → ∀ u : E,
        fderiv ℝ (hessian (extendedRealRealPart (F⋆))) s u =
          -((hessian (extendedRealRealPart (F⋆)) s).comp
            ((fderiv ℝ (hessian (withTopRealPart F)) (xStar s)
                ((hessian (extendedRealRealPart (F⋆)) s) u)).comp
              (hessian (extendedRealRealPart (F⋆)) s))) := by
    intro s hs u
    have hEq :
        (hessian (extendedRealRealPart (F⋆))) =ᶠ[nhds s]
          fun t ↦ (hessian (withTopRealPart F) (xStar t)).inverse := by
      -- On the open dual domain, the dual Hessian is pointwise the inverse primal Hessian.
      filter_upwards [hdualOpen.mem_nhds hs] with t ht
      simpa using hdualHessian_eq_inverse ht
    calc
      fderiv ℝ (hessian (extendedRealRealPart (F⋆))) s u
          = fderiv ℝ (fun t ↦ (hessian (withTopRealPart F) (xStar t)).inverse) s u := by
              rw [Filter.EventuallyEq.fderiv_eq hEq]
      _ = -((hessian (withTopRealPart F) (xStar s)).inverse.comp
          ((fderiv ℝ (hessian (withTopRealPart F)) (xStar s)
              ((hessian (extendedRealRealPart (F⋆)) s) u)).comp
            (hessian (withTopRealPart F) (xStar s)).inverse)) := by
              simpa using
                inverseHessianAlongBranchFDerivEq
                  (f := F) (xStar := xStar) hFselfInteriorWith.contDiffOn
                  hxStar_mem hxStar_hessian_invertible hxStar_hasFDerivAt hs u
      _ = -((hessian (extendedRealRealPart (F⋆)) s).comp
          ((fderiv ℝ (hessian (withTopRealPart F)) (xStar s)
              ((hessian (extendedRealRealPart (F⋆)) s) u)).comp
            (hessian (extendedRealRealPart (F⋆)) s))) := by
              rw [hdualHessian_eq_inverse hs]
  have hdualHessianPositive :
      ∀ ⦃s : E⦄, s ∈ dom (F⋆) → (hessian (extendedRealRealPart (F⋆)) s).IsPositive := by
    have hdualC2 : ContDiffOn ℝ 2 (extendedRealRealPart (F⋆)) (dom (F⋆)) :=
      hdualContDiffOn.of_le (show (2 : WithTop ℕ∞) ≤ 3 by norm_num)
    intro s hs
    -- Convexity of the dual finite real part gives positivity of its Hessian on the open domain.
    exact
      ((convexOn_iff_hessian_isPositive hdualOpen hdualConvexOn.1 hdualC2).1
        hdualConvexOn) s hs
  have dualThirdDerivativeOperatorLe :
      ∀ ⦃s : E⦄, s ∈ dom (F⋆) → ∀ u : E,
        fderiv ℝ (hessian (extendedRealRealPart (F⋆))) s u ≤
          (2 * (Mf : ℝ) * ‖u‖[extendedRealRealPart (F⋆); s]) •
            hessian (extendedRealRealPart (F⋆)) s := by
    intro s hs u
    let x : E := xStar s
    let H : E →L[ℝ] E := hessian (withTopRealPart F) x
    let K : E →L[ℝ] E := hessian (extendedRealRealPart (F⋆)) s
    let w : E := K u
    let A : E →L[ℝ] E := fderiv ℝ (hessian (withTopRealPart F)) x w
    let c : ℝ := 2 * (Mf : ℝ) * ‖w‖[withTopRealPart F; x]
    have hK : K = H.inverse := by
      simpa [K, H, x] using hdualHessian_eq_inverse hs
    have hHinvertible : H.IsInvertible := by
      simpa [H, x] using hxStar_hessian_invertible hs
    have hKPos : K.IsPositive := by
      simpa [K] using hdualHessianPositive hs
    let B : E →L[ℝ] E := c • H - (-A)
    have hnorm_bridge :
        ‖u‖[extendedRealRealPart (F⋆); s] = ‖w‖[withTopRealPart F; x] := by
      -- Rewrite the dual local norm through the inverse-Hessian identity `K = H⁻¹`.
      calc
        ‖u‖[extendedRealRealPart (F⋆); s] = Real.sqrt (inner ℝ u (K u)) := by
          rw [hessianLocalNorm_def]
        _ = Real.sqrt (inner ℝ (K u) (H (K u))) := by
          rw [hK]
          congr 1
          rw [hHinvertible.self_apply_inverse u, real_inner_comm]
        _ = ‖w‖[withTopRealPart F; x] := by
          simp [w, H, hessianLocalNorm_def]
    have hA_lower : -A ≤ c • H := by
      -- Apply the primal operator bound in direction `-w` to get the lower bound on `A`.
      simpa [A, c, w, x, H, hessianLocalNorm_neg] using
        (hFselfDom.thirdDerivative_operator_le (hxStar_dom hs) (-w))
    have hA_lower' := hA_lower
    rw [ContinuousLinearMap.le_def, ContinuousLinearMap.isPositive_iff] at hA_lower'
    obtain ⟨hBsymm, hBquad⟩ := hA_lower'
    have hHK : ∀ y : E, H (K y) = y := by
      intro y
      rw [hK]
      exact hHinvertible.self_apply_inverse y
    have hgap_formula :
        ∀ y : E,
          (((2 * (Mf : ℝ) * ‖u‖[extendedRealRealPart (F⋆); s]) • K -
              fderiv ℝ (hessian (extendedRealRealPart (F⋆))) s u) y) =
            K (B (K y)) := by
      intro y
      rw [show 2 * (Mf : ℝ) * ‖u‖[extendedRealRealPart (F⋆); s] = c by
        simp [c, hnorm_bridge]]
      calc
        (((c : ℝ) • K - fderiv ℝ (hessian (extendedRealRealPart (F⋆))) s u) y)
            = (((c : ℝ) • K + K.comp (A.comp K)) y) := by
                rw [dualHessianDerivative_formula hs u]
                simp [A, x, w, K]
        _ = K (B (K y)) := by
              simp [B, ContinuousLinearMap.comp_apply, hHK y]
    rw [ContinuousLinearMap.le_def, ContinuousLinearMap.isPositive_iff]
    constructor
    · intro v z
      -- The dual gap is the conjugation of the primal positive operator `B` by the symmetric
      -- positive operator `K`.
      calc
        inner ℝ
            ((((2 * (Mf : ℝ) * ‖u‖[extendedRealRealPart (F⋆); s]) • K -
                fderiv ℝ (hessian (extendedRealRealPart (F⋆))) s u) v)) z
            = inner ℝ (K (B (K v))) z := by rw [hgap_formula v]
        _ = inner ℝ (B (K v)) (K z) := by
              simpa using hKPos.isSymmetric (B (K v)) z
        _ = inner ℝ (K v) (B (K z)) := by
              simpa [B] using hBsymm (K v) (K z)
        _ = inner ℝ v (K (B (K z))) := by
              simpa using hKPos.isSymmetric v (B (K z))
        _ = inner ℝ v
            ((((2 * (Mf : ℝ) * ‖u‖[extendedRealRealPart (F⋆); s]) • K -
                fderiv ℝ (hessian (extendedRealRealPart (F⋆))) s u) z)) := by
              rw [hgap_formula z]
    · intro v
      have hquad_rewrite :
          inner ℝ
              ((((2 * (Mf : ℝ) * ‖u‖[extendedRealRealPart (F⋆); s]) • K -
                  fderiv ℝ (hessian (extendedRealRealPart (F⋆))) s u) v))
              v
            =
              inner ℝ (B (K v)) (K v) := by
        rw [hgap_formula v]
        simpa using hKPos.isSymmetric (B (K v)) v
      -- Test the conjugated operator gap on `v` and reduce it to the primal positive operator
      -- `B = c • H - (-A) = c • H + A`.
      rw [hquad_rewrite]
      exact hBquad (K v)
  -- Route correction: the old blocker was the missing branch derivative. The branch is now
  -- identified with the canonical dual gradient near each dual slope, and the remaining work is
  -- finished by differentiating the inverse-Hessian identity and transporting the primal operator
  -- inequality through that identity.
  refine
    IsSelfConcordantOnWith.of_thirdDerivative_operator_le hdualOpen hdualContDiffOn hdualConvexOn
      ?_
  intro s hs u
  exact dualThirdDerivativeOperatorLe hs u

end

end
