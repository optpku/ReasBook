/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_1_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_18
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Proposition_5_0_15
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_3_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_1_6
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_1_11
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_3_3
import Mathlib.Analysis.Calculus.ImplicitContDiff

open scoped ConstrainedArgmin ConvexAnalysis Gradient
open ContinuousLinearMap

noncomputable section

universe u₁ u₂

variable {E₁ : Type u₁} {E₂ : Type u₂}
variable [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
variable [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]

local notation "Z" => WithLp 2 (E₁ × E₂)

section PartialMinimizationBarrier

variable {Q : Set (E₁ × E₂)} {ν : NNReal} {Φ : E₁ × E₂ → ℝ} {y : E₁ → E₂}

local notation "QZ" => ((WithLp.ofLp : Z → E₁ × E₂) ⁻¹' Q)
local notation "psiObj" => partialInfProjection Q (Real.toEReal ∘ Φ)
local notation "D" => dom psiObj
local notation "f" => extendedRealRealPart psiObj

/-- Helper for Theorem 5.3.6: the ambient lifted product objective used to compare the canonical
`WithLp` gradient with frozen product-coordinate slices. -/
private abbrev partialMinimizationLift
    (Φ : E₁ × E₂ → ℝ) : Z → ℝ :=
  Φ ∘ (WithLp.ofLp : Z → E₁ × E₂)

/-- Helper for Theorem 5.3.6: an attained fiber minimizer realizes the extended-real partial
infimum at the corresponding finite value. -/
private lemma partialInfProjection_eq_argmin_eReal
    (Q : Set (E₁ × E₂)) (Φ : E₁ × E₂ → ℝ) {x : E₁} {yy : E₂}
    (hyy : yy ∈ argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x)) :
    partialInfProjection Q (Real.toEReal ∘ Φ) x = (Φ (x, yy) : EReal) := by
  rcases mem_constrainedArgmin_iff.mp hyy with ⟨hyy_mem, hyy_min⟩
  have himage_mem :
      ((Φ (x, yy) : ℝ) : EReal) ∈
        (Real.toEReal ∘ Φ) '' {z : E₁ × E₂ | z ∈ Q ∧ z.1 = x} := by
    refine ⟨(x, yy), ⟨hyy_mem, rfl⟩, by simp⟩
  have himage_nonempty :
      ((Real.toEReal ∘ Φ) '' {z : E₁ × E₂ | z ∈ Q ∧ z.1 = x}).Nonempty := ⟨_, himage_mem⟩
  -- The chosen minimizer gives both a witness in the fiber image and the lower bound on every
  -- other feasible fiber value.
  rw [partialInfProjection_eq_sInf]
  refine le_antisymm ?_ ?_
  · exact sInf_le himage_mem
  · refine le_csInf himage_nonempty ?_
    rintro r ⟨⟨x', yy'⟩, hz, rfl⟩
    rcases hz with ⟨hyy'_mem, hx'⟩
    change x' = x at hx'
    subst x'
    have hmin : Φ (x, yy) ≤ Φ (x, yy') := by
      simpa using hyy_min hyy'_mem
    exact show ((Φ (x, yy) : ℝ) : EReal) ≤ ((Φ (x, yy') : ℝ) : EReal) from by
      exact_mod_cast hmin

/-- Helper for Theorem 5.3.6: once the fiber infimum is attained, the canonical real-valued
partial-minimization objective evaluates to that attained fiber value. -/
private lemma partialMinimizationObjective_eq_of_mem_argmin
    (Q : Set (E₁ × E₂)) (Φ : E₁ × E₂ → ℝ) {x : E₁} {yy : E₂}
    (hyy : yy ∈ argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x)) :
    extendedRealRealPart (partialInfProjection Q (Real.toEReal ∘ Φ)) x = Φ (x, yy) := by
  have hx_dom : x ∈ dom (partialInfProjection Q (Real.toEReal ∘ Φ)) := by
    -- The attained finite fiber value witnesses finiteness of the partial infimum.
    rw [mem_extendedRealEffectiveDomain_iff, partialInfProjection_eq_argmin_eReal Q Φ hyy]
    simp
  -- The Chapter 5 real-part bridge recovers the attained real value on the effective domain.
  apply EReal.coe_injective
  rw [coe_extendedRealRealPart hx_dom, partialInfProjection_eq_argmin_eReal Q Φ hyy]

/-- Helper for Theorem 5.3.6: the ambient feasible set `Q` is open because the barrier owner is
defined on the `WithLp` preimage of `Q`. -/
private lemma ambientDomain_isOpen_of_barrier
    (hΦ : IsSelfConcordantBarrierOnWith QZ ν (Φ ∘ WithLp.ofLp)) :
    IsOpen Q := by
  -- Pull back the open `WithLp` domain along the inverse chart `WithLp.toLp`.
  have hOpenQZ : IsOpen QZ := hΦ.toIsStandardSelfConcordantOn.isOpen_domain
  have hOpenPreimage : IsOpen ((WithLp.toLp 2 : E₁ × E₂ → Z) ⁻¹' QZ) :=
    hOpenQZ.preimage (WithLp.prod_continuous_toLp 2 E₁ E₂)
  simpa using hOpenPreimage

/-- Helper for Theorem 5.3.6: the ambient feasible set `Q` is convex because the lifted barrier
owner already carries convexity on the `WithLp` chart. -/
private lemma ambientDomain_convex_of_barrier
    (hΦ : IsSelfConcordantBarrierOnWith QZ ν (Φ ∘ WithLp.ofLp)) :
    Convex ℝ Q := by
  -- Transport convexity from the `WithLp` model back to the raw product coordinates.
  have hConvQZ : Convex ℝ QZ := hΦ.toIsStandardSelfConcordantOn.convex_domain
  intro z₁ hz₁ z₂ hz₂ a b ha hb hab
  have hz₁' : WithLp.toLp 2 z₁ ∈ QZ := by
    simpa using hz₁
  have hz₂' : WithLp.toLp 2 z₂ ∈ QZ := by
    simpa using hz₂
  have hcomb :
      a • WithLp.toLp 2 z₁ + b • WithLp.toLp 2 z₂ ∈ QZ :=
    hConvQZ hz₁' hz₂' ha hb hab
  simpa using hcomb

/-- Helper for Theorem 5.3.6: the barrier owner on `Q` also gives convexity of the ambient raw
objective `Φ` on `Q` after transporting the standard self-concordant owner through the `WithLp`
chart. -/
private lemma ambientConvexOn_of_barrier
    (hΦ : IsSelfConcordantBarrierOnWith QZ ν (Φ ∘ WithLp.ofLp)) :
    ConvexOn ℝ Q Φ := by
  constructor
  · exact ambientDomain_convex_of_barrier (Q := Q) (ν := ν) (Φ := Φ) hΦ
  · intro p hp q hq a b ha hb hab
    have hp' : WithLp.toLp 2 p ∈ QZ := by
      simpa using hp
    have hq' : WithLp.toLp 2 q ∈ QZ := by
      simpa using hq
    simpa [Function.comp, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add] using
      hΦ.toIsStandardSelfConcordantOn.convexOn.2 hp' hq' ha hb hab

/-- Helper for Theorem 5.3.6: any selected fiber minimizer over a domain point already lies in
`interior Q`, because `Q` is open under the barrier hypothesis. -/
private lemma selectedFiberMinimizer_mem_interior_of_dom
    (hΦ : IsSelfConcordantBarrierOnWith QZ ν (Φ ∘ WithLp.ofLp))
    (hy_argmin : ∀ ⦃x : E₁⦄, x ∈ D → y x ∈ argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x))
    {x : E₁} (hx : x ∈ D) :
    (x, y x) ∈ interior Q := by
  -- The chosen minimizer is feasible, and openness upgrades feasibility to interior membership.
  have hQ_open : IsOpen Q := ambientDomain_isOpen_of_barrier (Q := Q) (ν := ν) (Φ := Φ) hΦ
  have hy_mem : (x, y x) ∈ Q := by
    exact (mem_constrainedArgmin_iff.mp (hy_argmin hx)).1
  simpa [hQ_open.interior_eq] using hy_mem

/-- Helper for Theorem 5.3.6: the ambient lift already satisfies the standard self-concordant
owner on `interior Q`, which coincides with `Q` under the barrier hypothesis. -/
private lemma ambientLift_isStandardSelfConcordantOnInterior_of_barrier
    (hΦ : IsSelfConcordantBarrierOnWith QZ ν (Φ ∘ WithLp.ofLp)) :
    IsStandardSelfConcordantOn ((WithLp.ofLp : Z → E₁ × E₂) ⁻¹' interior Q) (Φ ∘ WithLp.ofLp) := by
  -- Replace `interior Q` by `Q` using openness, then reuse the parent standard-self-concordance
  -- field of the barrier owner.
  have hQ_open : IsOpen Q := ambientDomain_isOpen_of_barrier (Q := Q) (ν := ν) (Φ := Φ) hΦ
  simpa [hQ_open.interior_eq] using
    (hΦ.toIsStandardSelfConcordantOn :
      IsStandardSelfConcordantOn ((WithLp.ofLp : Z → E₁ × E₂) ⁻¹' Q) (Φ ∘ WithLp.ofLp))

/-- Helper for Theorem 5.3.6: freezing the first coordinate preserves the barrier owner on the
corresponding fiber slice. -/
private lemma fiberSlice_isSelfConcordantBarrierOn_of_barrier
    (hΦ : IsSelfConcordantBarrierOnWith QZ ν (Φ ∘ WithLp.ofLp)) (x : E₁) :
    IsSelfConcordantBarrierOnWith ((Prod.mk x) ⁻¹' Q) ν (Φ ∘ Prod.mk x) := by
  let gLin : E₂ →L[ℝ] Z :=
    ((WithLp.prodContinuousLinearEquiv 2 ℝ E₁ E₂).symm.toContinuousLinearMap).comp
      (ContinuousLinearMap.inr ℝ E₁ E₂)
  let g : E₂ →ᴬ[ℝ] Z :=
    gLin.toContinuousAffineMap +ᵥ
      ContinuousAffineMap.const ℝ E₂ (WithLp.toLp 2 (x, (0 : E₂)))
  have hg_apply : ∀ y : E₂, g y = WithLp.toLp 2 (x, y) := by
    intro y
    calc
      g y = gLin y + WithLp.toLp 2 (x, (0 : E₂)) := by
        simp [g]
      _ = WithLp.toLp 2 (x, (0 : E₂)) + WithLp.toLp 2 ((0 : E₁), y) := by
        simp [gLin, ContinuousLinearMap.comp_apply, add_comm]
      _ = WithLp.toLp 2 ((x, (0 : E₂)) + ((0 : E₁), y)) := by
        symm
        exact ((WithLp.prodContinuousLinearEquiv 2 ℝ E₁ E₂).symm.map_add
          (x, (0 : E₂)) ((0 : E₁), y))
      _ = WithLp.toLp 2 (x, y) := by
        simp
  have hg_dom : g ⁻¹' ((WithLp.ofLp : Z → E₁ × E₂) ⁻¹' Q) = (Prod.mk x) ⁻¹' Q := by
    ext y
    simp [hg_apply]
  have hg_fun : (Φ ∘ WithLp.ofLp) ∘ g = Φ ∘ Prod.mk x := by
    funext y
    simp [hg_apply]
  -- Pull the ambient barrier through the frozen-coordinate affine embedding once.
  simpa [hg_dom, hg_fun] using hΦ.comp_continuousAffineMap g

/-- Helper for Theorem 5.3.6: the frozen `yy` Hessian is at least semidefinite at the selected
fiber minimizer because the frozen slice is already standard self-concordant. -/
private lemma selectedFiberHessianNonneg_of_barrierArgmin
    (hΦ : IsSelfConcordantBarrierOnWith QZ ν (Φ ∘ WithLp.ofLp))
    (hy_argmin : ∀ ⦃x : E₁⦄, x ∈ D → y x ∈ argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x))
    {x : E₁} (hx : x ∈ D) (v : E₂) :
    0 ≤ inner ℝ v ((hessian (Φ ∘ Prod.mk x) (y x)) v) := by
  have hslice :
      IsSelfConcordantBarrierOnWith ((Prod.mk x) ⁻¹' Q) ν (Φ ∘ Prod.mk x) :=
    fiberSlice_isSelfConcordantBarrierOn_of_barrier (Q := Q) (ν := ν) (Φ := Φ) hΦ x
  have hy_mem : y x ∈ (Prod.mk x) ⁻¹' Q := by
    exact (mem_constrainedArgmin_iff.mp (hy_argmin hx)).1
  -- Read semidefiniteness directly from the frozen slice owner at the selected feasible point.
  exact hslice.toIsStandardSelfConcordantOn.hessian_posSemidef hy_mem v

/-- Helper for Theorem 5.3.6: an interior stationary point on a frozen fiber is already a global
minimizer on that fiber. -/
private lemma stationaryFiber_mem_argmin
    (hΦ : IsSelfConcordantBarrierOnWith QZ ν (Φ ∘ WithLp.ofLp))
    {x : E₁} {yy : E₂}
    (hyy_mem_interior : (x, yy) ∈ interior Q)
    (hyy_stationary : HasFDerivAt (Φ ∘ Prod.mk x) (0 : E₂ →L[ℝ] ℝ) yy) :
    yy ∈ argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x) := by
  let σ : E₂ → ℝ →ᵃ[ℝ] E₂ := fun z ↦ AffineMap.lineMap yy z
  have hΦ_conv : ConvexOn ℝ Q Φ := ambientConvexOn_of_barrier (Q := Q) (ν := ν) (Φ := Φ) hΦ
  have hyy_mem : (x, yy) ∈ Q := interior_subset hyy_mem_interior
  refine mem_constrainedArgmin_iff.mpr ?_
  refine ⟨by simpa using hyy_mem, ?_⟩
  intro z hz
  let γz : ℝ →ᵃ[ℝ] (E₁ × E₂) := AffineMap.lineMap (x, yy) (x, z)
  let φz : ℝ → ℝ := fun t ↦ Φ (γz t)
  have hzQ : (x, z) ∈ Q := by simpa using hz
  have hγ_maps : Set.MapsTo γz (Set.Icc (0 : ℝ) 1) Q := by
    exact hΦ_conv.1.mapsTo_lineMap hyy_mem hzQ
  have hφ_conv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) φz := by
    -- Restrict the ambient convex objective to the segment joining `yy` to `z` in the fixed
    -- `x`-fiber.
    exact (hΦ_conv.comp_affineMap γz).subset hγ_maps (convex_Icc (0 : ℝ) 1)
  have hσ_deriv : HasDerivAt (fun t : ℝ ↦ (σ z) t) (z - yy) 0 := by
    simpa [σ] using AffineMap.hasDerivAt_lineMap (a := yy) (b := z) (x := (0 : ℝ))
  have hφ_deriv_zero : HasDerivAt φz 0 0 := by
    have hσ_zero : (σ z) 0 = yy := by simp [σ]
    have hyy_stationary' :
        HasFDerivAt (Φ ∘ Prod.mk x) (0 : E₂ →L[ℝ] ℝ) ((σ z) 0) := by
      simpa [hσ_zero] using hyy_stationary
    have hcomp :
        HasDerivAt (((Φ ∘ Prod.mk x) ∘ fun t : ℝ ↦ (σ z) t)) 0 0 := by
      simpa using hyy_stationary'.comp_hasDerivAt (0 : ℝ) hσ_deriv
    convert hcomp using 1
    ext t
    have hfst : (1 - t : ℝ) • x + t • x = x := by
      calc
        (1 - t : ℝ) • x + t • x = ((1 - t : ℝ) + t) • x := by rw [← add_smul]
        _ = (1 : ℝ) • x := by
          congr 1
          ring
        _ = x := by simp
    simp [γz, σ, φz, AffineMap.lineMap_apply_module, hfst]
  have hslope_nonneg : 0 ≤ slope φz 0 1 := by
    simpa [hφ_deriv_zero.deriv] using
      hφ_conv.deriv_le_slope
        (by simp)
        (by simp)
        zero_lt_one
        hφ_deriv_zero.differentiableAt
  -- The vanishing derivative at the left endpoint forces every feasible fiber point to have
  -- value at least `Φ (x, yy)`.
  have hγ_zero : γz 0 = (x, yy) := by simp [γz]
  have hγ_one : γz 1 = (x, z) := by simp [γz]
  simpa [φz, hγ_zero, hγ_one, slope] using hslope_nonneg

/-- Helper for Theorem 5.3.6: if a positive symmetric operator has zero quadratic form on `v`,
then `v` lies in its kernel. -/
private lemma positiveOperator_apply_eq_zero_of_inner_eq_zero
    {H : E₂ →L[ℝ] E₂} (hH : H.IsPositive) {v : E₂}
    (hv : inner ℝ v (H v) = 0) :
    H v = 0 := by
  let B : LinearMap.BilinForm ℝ E₂ := ((innerSL ℝ).comp H).toBilinForm
  have hB_apply (u w : E₂) : B u w = inner ℝ (H u) w := rfl
  have hB_nonneg : ∀ u : E₂, 0 ≤ B u u := by
    intro u
    simpa [hB_apply, real_inner_comm] using hH.inner_nonneg_right u
  have hB_symm : LinearMap.IsSymm B := by
    rw [← LinearMap.BilinForm.isSymm_iff]
    rw [LinearMap.BilinForm.isSymm_def]
    intro u w
    rw [hB_apply, hB_apply]
    simpa [real_inner_comm] using hH.isSymmetric u w
  have hv_ker : v ∈ LinearMap.ker B := by
    exact (LinearMap.BilinForm.apply_apply_same_eq_zero_iff B hB_nonneg hB_symm).mp
      (by simpa [hB_apply, real_inner_comm] using hv)
  have hv_zero : B v = 0 := by
    simpa [LinearMap.mem_ker] using hv_ker
  -- Compare the operator output against every test vector through symmetry.
  apply ext_inner_right ℝ
  intro u
  have hu := congrArg (fun L : E₂ →ₗ[ℝ] ℝ ↦ L u) hv_zero
  simpa [hB_apply] using hu

/-- Helper for Theorem 5.3.6: affine lines `s ↦ x + s • d` differentiate to the fixed direction
`d`. -/
private lemma line_hasDerivAt (x d : E₂) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ x + s • d) d t := by
  -- Differentiate the scalar parameter and keep the direction fixed.
  simpa [one_smul] using (((hasDerivAt_id t).smul_const d).const_add x)

/-- Helper for Theorem 5.3.6: a `C²` real-valued function has a differentiable gradient at the
base point. -/
private lemma differentiableAtGradient_ofContDiffAtTwo
    {g : E₂ → ℝ} {z : E₂} (hg : ContDiffAt ℝ 2 g z) :
    DifferentiableAt ℝ (∇ g) z := by
  let dDual : StrongDual ℝ E₂ →L[ℝ] E₂ :=
    (InnerProductSpace.toDual ℝ E₂).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hg_fderiv : DifferentiableAt ℝ (fderiv ℝ g) z := by
    have hcont : ContDiffAt ℝ 1 (fderiv ℝ g) z :=
      hg.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
    exact hcont.differentiableAt one_ne_zero
  -- Rewrite the gradient through the Riesz isomorphism before differentiating it.
  change DifferentiableAt ℝ (fun y ↦ dDual (fderiv ℝ g y)) z
  exact (dDual.hasFDerivAt.comp z hg_fderiv.hasFDerivAt).differentiableAt

/-- Helper for Theorem 5.3.6: differentiating a scalarized gradient line gives the Hessian pairing
with the line direction. -/
private lemma scalarizedGradientLine_hasDerivAt
    {domain : Set E₂} {g : E₂ → ℝ}
    (hdom_open : IsOpen domain)
    (hg_contDiff : ContDiffOn ℝ 2 g domain)
    {x d v : E₂} {t : ℝ} (hxt : x + t • d ∈ domain) :
    HasDerivAt (fun s : ℝ ↦ inner ℝ (∇ g (x + s • d)) v)
      (inner ℝ (hessian g (x + t • d) d) v) t := by
  have hxt_C2 : ContDiffAt ℝ 2 g (x + t • d) := by
    exact hg_contDiff.contDiffAt (hdom_open.mem_nhds hxt)
  have hgradLine :
      HasFDerivAt (fun s : ℝ ↦ ∇ g (x + s • d))
        ((hessian g (x + t • d)).comp (ContinuousLinearMap.toSpanSingleton ℝ d)) t := by
    -- Differentiate the gradient field and compose it with the affine-line derivative.
    simpa using
      ((differentiableAtGradient_ofContDiffAtTwo hxt_C2).hasFDerivAt.comp t
        (line_hasDerivAt x d t).hasFDerivAt)
  let φ : E₂ →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ E₂) v
  have hscalar :
      HasFDerivAt (fun s : ℝ ↦ φ (∇ g (x + s • d)))
        (φ.comp ((hessian g (x + t • d)).comp (ContinuousLinearMap.toSpanSingleton ℝ d))) t := by
    -- Postcompose the gradient line with the fixed scalar functional `w ↦ ⟪w, v⟫`.
    simpa [φ] using (φ.hasFDerivAt.comp t hgradLine)
  simpa [φ, InnerProductSpace.toDual_apply_apply, real_inner_comm] using hscalar.hasDerivAt

/-- Helper for Theorem 5.3.6: along a Hessian-kernel direction, self-concordance keeps the whole
short affine line inside the domain and freezes the Hessian there. -/
private lemma hessian_eq_onKernelLine_of_selfConcordant
    {domain : Set E₂} {g : E₂ → ℝ} {Mf : NNReal}
    (hself : IsSelfConcordantOnWith domain Mf g)
    {x u : E₂}
    (hMf_pos : 0 < (Mf : ℝ))
    (hx : x ∈ domain)
    (hu_hess : hessian g x u = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε →
      x + t • u ∈ domain ∧ hessian g (x + t • u) = hessian g x := by
  letI : CompleteSpace E₂ := FiniteDimensional.complete ℝ E₂
  let r : ℝ := (1 / (Mf : ℝ)) / 2
  have hr_pos : 0 < r := by
    dsimp [r]
    positivity
  have hr_nonneg : 0 ≤ r := le_of_lt hr_pos
  have hr_lt_inv : r < 1 / (Mf : ℝ) := by
    simpa [r] using half_lt_self (one_div_pos.mpr hMf_pos)
  have hquad_zero : inner ℝ u (hessian g x u) = 0 := by
    simp [hu_hess]
  have hlineDomain : ∀ t : ℝ, x + t • u ∈ domain :=
    IsSelfConcordantOn.affine_line_mem_dom_of_zero_quadratic_form
      (f := g) hself hMf_pos hx hquad_zero
  refine ⟨1, by norm_num, ?_⟩
  intro t ht
  have htDomain : x + t • u ∈ domain := hlineDomain t
  have hquad_nonneg :
      0 ≤ inner ℝ ((x + t • u) - x) (hessian g x ((x + t • u) - x)) :=
    hself.hessian_posSemidef hx ((x + t • u) - x)
  have htDikin : x + t • u ∈ openDikinEllipsoid g x r := by
    refine
      (mem_openDikinEllipsoid_iff_hessian_quadratic_lt_sq
        g x (x + t • u) hquad_nonneg hr_nonneg).2 ?_
    simpa [sub_eq_add_neg, hu_hess] using sq_pos_of_pos hr_pos
  rcases hself.hessian_loewner_bounds_of_exact_local_radius hx htDomain hr_lt_inv htDikin with
    ⟨hlower, hupper⟩
  have hnorm_zero : hessianLocalNorm g x (t • u) = 0 := by
    rw [hessianLocalNorm_def]
    simp [hu_hess]
  refine ⟨htDomain, le_antisymm ?_ ?_⟩
  · simpa [hnorm_zero] using hupper
  · simpa [hnorm_zero] using hlower

/-- Helper for Theorem 5.3.6: if the Hessian stays constant along a short affine line and kills the
line direction at the base point, then the gradient stays constant there as well. -/
private lemma gradient_eq_onKernelLine_of_hessian_eq
    {domain : Set E₂} {g : E₂ → ℝ} {s x u : E₂} {ε : ℝ}
    (hdom_open : IsOpen domain)
    (hg_contDiff : ContDiffOn ℝ 2 g domain)
    (hx_grad : ∇ g x = s)
    (hu_hess : hessian g x u = 0)
    (hline :
      ∀ t : ℝ, |t| < ε → x + t • u ∈ domain ∧ hessian g (x + t • u) = hessian g x) :
    ∀ t : ℝ, |t| < ε → ∇ g (x + t • u) = s := by
  intro t ht
  apply ext_inner_right ℝ
  intro v
  let φ : ℝ → ℝ := fun τ ↦ inner ℝ (∇ g (x + τ • u)) v
  have hdiffOn : DifferentiableOn ℝ φ (Set.Ioo (-ε) ε) := by
    intro τ hτ
    have hτ_abs : |τ| < ε := by
      exact abs_lt.mpr ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    have hdiffτ :
        DifferentiableAt ℝ (fun z : ℝ ↦ inner ℝ (∇ g (x + z • u)) v) τ :=
      (scalarizedGradientLine_hasDerivAt
        (domain := domain) (g := g) hdom_open hg_contDiff
        (x := x) (d := u) (v := v) (t := τ) (hline τ hτ_abs).1).differentiableAt
    exact hdiffτ.differentiableWithinAt
  have hderiv_zero : Set.EqOn (deriv φ) 0 (Set.Ioo (-ε) ε) := by
    intro τ hτ
    have hτ_abs : |τ| < ε := by
      exact abs_lt.mpr ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    have hu_hessτ : hessian g (x + τ • u) u = 0 := by
      simpa [(hline τ hτ_abs).2] using hu_hess
    simpa [φ, hu_hessτ] using
      (scalarizedGradientLine_hasDerivAt
        (domain := domain) (g := g) hdom_open hg_contDiff
        (x := x) (d := u) (v := v) (t := τ) (hline τ hτ_abs).1).deriv
  have hzero_mem : (0 : ℝ) ∈ Set.Ioo (-ε) ε := by
    constructor <;> linarith
  have ht_mem : t ∈ Set.Ioo (-ε) ε := abs_lt.mp ht
  have hconst :
      φ t = φ 0 :=
    isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo hdiffOn hderiv_zero ht_mem
      hzero_mem
  calc
    inner ℝ (∇ g (x + t • u)) v = φ t := rfl
    _ = φ 0 := hconst
    _ = inner ℝ (∇ g x) v := by simp [φ]
    _ = inner ℝ s v := by simp [hx_grad]

/-- Helper for Theorem 5.3.6: a Hessian-kernel direction forces the frozen-slice gradient to stay
constant along a short affine line through the base point. -/
private lemma localGradient_eq_onKernelLine
    {domain : Set E₂} {g : E₂ → ℝ}
    (hg_contDiff : ContDiffOn ℝ 2 g domain)
    (hself : IsSelfConcordantOn domain g)
    {s x u : E₂}
    (hx : x ∈ domain)
    (hx_grad : ∇ g x = s)
    (hu_hess : hessian g x u = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε → x + t • u ∈ domain ∧ ∇ g (x + t • u) = s := by
  rcases hself with ⟨Mf0, hMf0⟩
  let Mf : NNReal := Mf0 + 1
  have hMf : IsSelfConcordantOnWith domain Mf g :=
    IsSelfConcordantOnWith.of_le hMf0 (by
      change Mf0 ≤ Mf0 + 1
      simp)
  have hMf_pos : 0 < (Mf : ℝ) := by
    dsimp [Mf]
    positivity
  rcases hessian_eq_onKernelLine_of_selfConcordant
      (domain := domain) (g := g) hMf hMf_pos hx hu_hess with
    ⟨ε, hε_pos, hline⟩
  refine ⟨ε, hε_pos, ?_⟩
  intro t ht
  exact ⟨(hline t ht).1,
    gradient_eq_onKernelLine_of_hessian_eq
      (domain := domain) (g := g) (s := s) (x := x) (u := u)
      hMf.isOpen_domain hg_contDiff hx_grad hu_hess hline t ht⟩

/-- Helper for Theorem 5.3.6: Fermat's rule gives a vanishing Fréchet derivative for the frozen
`y`-slice at the selected fiber minimizer. -/
private lemma selectedFiberHasFDerivAtZero_of_barrierArgmin
    (hΦ : IsSelfConcordantBarrierOnWith QZ ν (Φ ∘ WithLp.ofLp))
    (hy_argmin : ∀ ⦃x : E₁⦄, x ∈ D → y x ∈ argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x))
    {x : E₁} (hx : x ∈ D) :
    HasFDerivAt (Φ ∘ Prod.mk x) (0 : E₂ →L[ℝ] ℝ) (y x) := by
  have hxy_mem_interior :
      (x, y x) ∈ interior Q :=
    selectedFiberMinimizer_mem_interior_of_dom
      (Q := Q) (ν := ν) (Φ := Φ) (y := y) hΦ hy_argmin hx
  have hΦ_at :
      ContDiffAt ℝ 1 Φ (x, y x) := by
    have hxy_mem :
        WithLp.toLp 2 (x, y x) ∈ QZ := by
      simpa using (mem_constrainedArgmin_iff.mp (hy_argmin hx)).1
    have hLift_at :
        ContDiffAt ℝ 3 (Φ ∘ WithLp.ofLp) (WithLp.toLp 2 (x, y x)) :=
      hΦ.toIsStandardSelfConcordantOn.contDiffOn.contDiffAt
        (hΦ.toIsStandardSelfConcordantOn.isOpen_domain.mem_nhds hxy_mem)
    -- Pull the ambient `WithLp` regularity back to the raw frozen slice point.
    simpa [Function.comp] using
      (hLift_at.comp (x, y x)
        ((((WithLp.prodContinuousLinearEquiv 2 ℝ E₁ E₂).symm :
            (E₁ × E₂) ≃L[ℝ] Z)).contDiff.contDiffAt)).of_le (by norm_num)
  rcases mem_constrainedArgmin_iff.mp (hy_argmin hx) with ⟨_, hy_min⟩
  have hΦ_diff : DifferentiableAt ℝ Φ (x, y x) :=
    hΦ_at.differentiableAt (by norm_num)
  have hQ_nhds : Q ∈ nhds (x, y x) := by
    exact Filter.mem_of_superset
      (IsOpen.mem_nhds isOpen_interior hxy_mem_interior) interior_subset
  have hfiber_nhds : (Prod.mk x) ⁻¹' Q ∈ nhds (y x) := by
    exact
      (Continuous.prodMk continuous_const continuous_id).continuousAt.preimage_mem_nhds hQ_nhds
  have hlocal : IsLocalMin (Φ ∘ Prod.mk x) (y x) := hy_min.isLocalMin hfiber_nhds
  have hslice :
      HasFDerivAt (Φ ∘ Prod.mk x) (fderiv ℝ (Φ ∘ Prod.mk x) (y x)) (y x) := by
    exact
      (hΦ_diff.comp (y x) (hasFDerivAt_prodMk_right x (y x)).differentiableAt).hasFDerivAt
  have hzero : fderiv ℝ (Φ ∘ Prod.mk x) (y x) = 0 :=
    hlocal.hasFDerivAt_eq_zero hslice
  simpa [hzero] using hslice

/-- Helper for Theorem 5.3.6: the missing local contradiction is strict positivity of the frozen
`yy` Hessian at each selected minimizer. -/
private lemma selectedFiberHessianPos_of_barrierArgmin
    (hΦ : IsSelfConcordantBarrierOnWith QZ ν (Φ ∘ WithLp.ofLp))
    (hy_argmin : ∀ ⦃x : E₁⦄, x ∈ D → y x ∈ argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x))
    (hy_unique : ∀ ⦃x : E₁⦄, x ∈ D → ∀ ⦃y' : E₂⦄,
        y' ∈ argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x) → y' = y x)
    {x : E₁} (hx : x ∈ D) :
    ∀ v : E₂, v ≠ 0 → 0 < inner ℝ v ((hessian (Φ ∘ Prod.mk x) (y x)) v) := by
  intro v hv
  let g : E₂ → ℝ := Φ ∘ Prod.mk x
  let domx : Set E₂ := (Prod.mk x) ⁻¹' Q
  have hnonneg :
      0 ≤ inner ℝ v ((hessian (Φ ∘ Prod.mk x) (y x)) v) :=
    selectedFiberHessianNonneg_of_barrierArgmin
      (Q := Q) (ν := ν) (Φ := Φ) (y := y) hΦ hy_argmin hx v
  have hslice :
      IsSelfConcordantBarrierOnWith domx ν g :=
    fiberSlice_isSelfConcordantBarrierOn_of_barrier (Q := Q) (ν := ν) (Φ := Φ) hΦ x
  have hy_mem : y x ∈ domx := (mem_constrainedArgmin_iff.mp (hy_argmin hx)).1
  have hg_contDiff : ContDiffOn ℝ 2 g domx :=
    hslice.toIsStandardSelfConcordantOn.contDiffOn.of_le (by norm_num)
  have hgrad_zero : ∇ g (y x) = 0 := by
    have hzero_deriv :
        HasFDerivAt g (0 : E₂ →L[ℝ] ℝ) (y x) := by
      simpa [g, Function.comp] using
        selectedFiberHasFDerivAtZero_of_barrierArgmin
          (Q := Q) (ν := ν) (Φ := Φ) (y := y) hΦ hy_argmin hx
    have hg_diff : DifferentiableAt ℝ g (y x) :=
      by
        exact
          (hg_contDiff.contDiffAt
            (hslice.toIsStandardSelfConcordantOn.isOpen_domain.mem_nhds hy_mem)).differentiableAt
              (by norm_num)
    simpa using (hzero_deriv.hasGradientAt.unique hg_diff.hasGradientAt).symm
  by_cases hzero : inner ℝ v ((hessian g (y x)) v) = 0
  · have hH_zero : hessian g (y x) v = 0 := by
      have hH_pos : (hessian g (y x)).IsPositive :=
        hslice.toIsStandardSelfConcordantOn.hessian_isPositive hy_mem
      -- Collapse the zero quadratic form to a genuine kernel vector of the frozen Hessian.
      exact positiveOperator_apply_eq_zero_of_inner_eq_zero hH_pos hzero
    obtain ⟨ε, hε_pos, hline⟩ :=
      localGradient_eq_onKernelLine
        (domain := domx) (g := g) hg_contDiff
        ⟨1, hslice.toIsStandardSelfConcordantOn⟩ hy_mem hgrad_zero hH_zero
    let t : ℝ := ε / 2
    have ht_abs : |t| < ε := by
      dsimp [t]
      rw [abs_of_nonneg (by linarith)]
      linarith
    have ht_ne : t ≠ 0 := by
      dsimp [t]
      linarith
    let y' : E₂ := y x + t • v
    have hy'_mem : y' ∈ domx := (hline t ht_abs).1
    have hy'_grad_zero : ∇ g y' = 0 := by
      simpa [y', g] using (hline t ht_abs).2
    have hy'_contDiffAt :
        ContDiffAt ℝ 1 g y' := by
      exact
        (hg_contDiff.contDiffAt
          (hslice.toIsStandardSelfConcordantOn.isOpen_domain.mem_nhds hy'_mem)).of_le
          (by norm_num)
    have hy'_diff : DifferentiableAt ℝ g y' := hy'_contDiffAt.differentiableAt (by norm_num)
    have hy'_stationary : HasFDerivAt g (0 : E₂ →L[ℝ] ℝ) y' := by
      have hy'_grad_at_zero : HasGradientAt g 0 y' := by
        simpa [hy'_grad_zero] using hy'_diff.hasGradientAt
      simpa using hy'_grad_at_zero.hasFDerivAt
    have hQ_open : IsOpen Q := ambientDomain_isOpen_of_barrier (Q := Q) (ν := ν) (Φ := Φ) hΦ
    have hy'_mem_interior : (x, y') ∈ interior Q := by
      simpa [domx, hQ_open.interior_eq, y'] using hy'_mem
    have hy'_argmin : y' ∈ argmin[domx] g := by
      simpa [domx, g] using
        stationaryFiber_mem_argmin
          (Q := Q) (ν := ν) (Φ := Φ) hΦ hy'_mem_interior hy'_stationary
    have hy'_ne : y' ≠ y x := by
      intro hy'_eq
      have htv : t • v = 0 := by
        have : y x + t • v = y x + 0 := by
          simpa [y'] using hy'_eq
        exact add_left_cancel this
      exact hv ((smul_eq_zero.mp htv).resolve_left ht_ne)
    exact False.elim (hy'_ne (hy_unique hx hy'_argmin))
  · exact lt_of_le_of_ne hnonneg (Ne.symm hzero)

/-- Helper for Theorem 5.3.6: Fermat's rule annihilates the frozen `y`-gradient at the selected
fiber minimizer over every `x ∈ D`. -/
private lemma selectedFiberGradient_eq_zero_of_barrierArgmin
    (hΦ : IsSelfConcordantBarrierOnWith QZ ν (Φ ∘ WithLp.ofLp))
    (hy_argmin : ∀ ⦃x : E₁⦄, x ∈ D → y x ∈ argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x))
    {x : E₁} (hx : x ∈ D) :
    ∇ (Φ ∘ Prod.mk x) (y x) = 0 := by
  let g : E₂ → ℝ := Φ ∘ Prod.mk x
  let domx : Set E₂ := (Prod.mk x) ⁻¹' Q
  have hslice :
      IsSelfConcordantBarrierOnWith domx ν g :=
    fiberSlice_isSelfConcordantBarrierOn_of_barrier (Q := Q) (ν := ν) (Φ := Φ) hΦ x
  have hy_mem : y x ∈ domx := (mem_constrainedArgmin_iff.mp (hy_argmin hx)).1
  have hzero_deriv :
      HasFDerivAt g (0 : E₂ →L[ℝ] ℝ) (y x) := by
    simpa [g, Function.comp] using
      selectedFiberHasFDerivAtZero_of_barrierArgmin
        (Q := Q) (ν := ν) (Φ := Φ) (y := y) hΦ hy_argmin hx
  have hg_contDiff :
      ContDiffOn ℝ 2 g domx :=
    hslice.toIsStandardSelfConcordantOn.contDiffOn.of_le (by norm_num)
  have hg_diff : DifferentiableAt ℝ g (y x) := by
    exact
      (hg_contDiff.contDiffAt
        (hslice.toIsStandardSelfConcordantOn.isOpen_domain.mem_nhds hy_mem)).differentiableAt
        (by norm_num)
  simpa using (hzero_deriv.hasGradientAt.unique hg_diff.hasGradientAt).symm

/-- Helper for Theorem 5.3.6: strict positivity of the selected frozen `yy` Hessian makes it
invertible as a continuous linear map. -/
private lemma selectedFiberHessianInvertible_of_barrierArgmin
    (hΦ : IsSelfConcordantBarrierOnWith QZ ν (Φ ∘ WithLp.ofLp))
    (hy_argmin : ∀ ⦃x : E₁⦄, x ∈ D → y x ∈ argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x))
    (hy_unique : ∀ ⦃x : E₁⦄, x ∈ D → ∀ ⦃y' : E₂⦄,
        y' ∈ argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x) → y' = y x)
    {x : E₁} (hx : x ∈ D) :
    (hessian (Φ ∘ Prod.mk x) (y x)).IsInvertible := by
  let H : E₂ →L[ℝ] E₂ := hessian (Φ ∘ Prod.mk x) (y x)
  have hHinj : Function.Injective H := by
    intro v w hvw
    by_contra hvw_ne
    have hdiff_ne : v - w ≠ 0 := sub_ne_zero.mpr hvw_ne
    have hpos : 0 < inner ℝ (v - w) (H (v - w)) := by
      exact selectedFiberHessianPos_of_barrierArgmin
        (Q := Q) (ν := ν) (Φ := Φ) (y := y) hΦ hy_argmin hy_unique hx (v - w) hdiff_ne
    have hzero : H (v - w) = 0 := by
      simpa [H, map_sub, hvw]
    have hinner_zero : inner ℝ (v - w) (H (v - w)) = 0 := by
      simp [hzero]
    linarith
  have hHsurj : Function.Surjective H := LinearMap.surjective_of_injective hHinj
  -- Finite-dimensional injective endomorphisms are bijective, hence continuous linear
  -- equivalences.
  letI : CompleteSpace E₂ := FiniteDimensional.complete ℝ E₂
  refine ⟨ContinuousLinearEquiv.ofBijective H (LinearMap.ker_eq_bot.mpr hHinj)
    (LinearMap.range_eq_top.mpr hHsurj), ?_⟩
  exact ContinuousLinearEquiv.coe_ofBijective H (LinearMap.ker_eq_bot.mpr hHinj)
    (LinearMap.range_eq_top.mpr hHsurj)

/-- Helper for Theorem 5.3.6: the lifted `L²` product objective is `Cⁿ` at the canonical product
point whenever the raw objective is `Cⁿ` at the corresponding pair. -/
private lemma partialMinimizationLift_contDiffAt
    {n : WithTop ℕ∞} (Φ : E₁ × E₂ → ℝ) (x : E₁) (yy : E₂)
    (hPhi : ContDiffAt ℝ n Φ (x, yy)) :
    ContDiffAt ℝ n (partialMinimizationLift Φ) (WithLp.toLp 2 (x, yy)) := by
  -- The `WithLp` lift is just `Φ` composed with the fixed product equivalence.
  simpa [partialMinimizationLift, Function.comp] using
    hPhi.comp (WithLp.toLp 2 (x, yy))
      ((((WithLp.prodContinuousLinearEquiv 2 ℝ E₁ E₂ : Z ≃L[ℝ] E₁ × E₂) :
          Z →L[ℝ] E₁ × E₂)).contDiff.contDiffAt)

/-- Helper for Theorem 5.3.6: a `C²` lifted objective has a differentiable ambient gradient at the
base point. -/
private lemma partialMinimizationLift_gradient_differentiableAt
    (Φ : E₁ × E₂ → ℝ) (x : E₁) (yy : E₂)
    (hPhi : ContDiffAt ℝ 2 Φ (x, yy)) :
    DifferentiableAt ℝ (∇ (partialMinimizationLift Φ)) (WithLp.toLp 2 (x, yy)) := by
  let Ddual : StrongDual ℝ Z →L[ℝ] Z :=
    (InnerProductSpace.toDual ℝ Z).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hLift :
      ContDiffAt ℝ 2 (partialMinimizationLift Φ) (WithLp.toLp 2 (x, yy)) :=
    partialMinimizationLift_contDiffAt Φ x yy hPhi
  have hfderiv_C1 :
      ContDiffAt ℝ 1 (fderiv ℝ (partialMinimizationLift Φ)) (WithLp.toLp 2 (x, yy)) := by
    -- Differentiating once leaves a `C¹` field of Fréchet derivatives.
    exact hLift.fderiv_right (by norm_num)
  have hGrad_C1 :
      ContDiffAt ℝ 1 (∇ (partialMinimizationLift Φ)) (WithLp.toLp 2 (x, yy)) := by
    -- The gradient is the Riesz transport of `fderiv`, so it inherits the same local smoothness.
    simpa [gradient, Ddual] using
      Ddual.contDiff.contDiffAt.comp (WithLp.toLp 2 (x, yy)) hfderiv_C1
  exact hGrad_C1.differentiableAt (by norm_num)

/-- Helper for Theorem 5.3.6: the ambient Hessian block operator on the product chart. It
packages the mixed second derivatives needed by the implicit branch argument. -/
private abbrev partialMinimizationAmbientHessian
    (Φ : E₁ × E₂ → ℝ) (x : E₁) (yy : E₂) : E₁ × E₂ →L[ℝ] Z :=
  hessian (partialMinimizationLift Φ) (WithLp.toLp 2 (x, yy)) ∘L
    (WithLp.prodContinuousLinearEquiv 2 ℝ E₁ E₂).symm.toContinuousLinearMap

private abbrev partialMinimizationXXHessian
    (Φ : E₁ × E₂ → ℝ) (x : E₁) (yy : E₂) : E₁ →L[ℝ] E₁ :=
  WithLp.fstL 2 ℝ E₁ E₂ ∘L partialMinimizationAmbientHessian Φ x yy ∘L inl ℝ E₁ E₂

private abbrev partialMinimizationXYHessian
    (Φ : E₁ × E₂ → ℝ) (x : E₁) (yy : E₂) : E₂ →L[ℝ] E₁ :=
  WithLp.fstL 2 ℝ E₁ E₂ ∘L partialMinimizationAmbientHessian Φ x yy ∘L inr ℝ E₁ E₂

private abbrev partialMinimizationYXHessian
    (Φ : E₁ × E₂ → ℝ) (x : E₁) (yy : E₂) : E₁ →L[ℝ] E₂ :=
  WithLp.sndL 2 ℝ E₁ E₂ ∘L partialMinimizationAmbientHessian Φ x yy ∘L inl ℝ E₁ E₂

/-- Helper for Theorem 5.3.6: the ambient stationary-map derivative along the `y`-gradient. -/
private lemma partialMinimizationYGradient_hasFDerivAt
    (Φ : E₁ × E₂ → ℝ) (x : E₁) (yy : E₂)
    (hPhi : ContDiffAt ℝ 2 Φ (x, yy)) :
    HasFDerivAt
      (fun z : E₁ × E₂ ↦
        WithLp.sndL 2 ℝ E₁ E₂ (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 z)))
      ((WithLp.sndL 2 ℝ E₁ E₂).comp (partialMinimizationAmbientHessian Φ x yy))
      (x, yy) := by
  have hGrad :
      HasFDerivAt
        (fun z : Z ↦ ∇ (partialMinimizationLift Φ) z)
        (hessian (partialMinimizationLift Φ) (WithLp.toLp 2 (x, yy)))
        (WithLp.toLp 2 (x, yy)) := by
    -- The Hessian is, by definition, the derivative of the ambient gradient.
    simpa [hessian] using
      (partialMinimizationLift_gradient_differentiableAt Φ x yy hPhi).hasFDerivAt
  have hToLp :
      HasFDerivAt
        (fun z : E₁ × E₂ ↦ ∇ (partialMinimizationLift Φ) (WithLp.toLp 2 z))
        ((hessian (partialMinimizationLift Φ) (WithLp.toLp 2 (x, yy))).comp
          ((WithLp.prodContinuousLinearEquiv 2 ℝ E₁ E₂).symm : (E₁ × E₂) →L[ℝ] Z))
        (x, yy) := by
    -- Rewrite the derivative through the fixed `WithLp` chart.
    simpa [Function.comp] using
      hGrad.comp (x, yy)
        (((WithLp.prodContinuousLinearEquiv 2 ℝ E₁ E₂).symm :
          (E₁ × E₂) →L[ℝ] Z).hasFDerivAt)
  simpa [partialMinimizationAmbientHessian, Function.comp] using
    (WithLp.sndL 2 ℝ E₁ E₂).hasFDerivAt.comp (x, yy) hToLp

/-- Helper for Theorem 5.3.6: the ambient stationary map is `C²` at a `C³` point. -/
private lemma partialMinimizationYStationaryMap_contDiffAt
    (Φ : E₁ × E₂ → ℝ) (x : E₁) (yy : E₂)
    (hPhi : ContDiffAt ℝ 3 Φ (x, yy)) :
    ContDiffAt ℝ 2
      (fun z : E₁ × E₂ ↦
        WithLp.sndL 2 ℝ E₁ E₂ (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 z)))
      (x, yy) := by
  let Ddual : StrongDual ℝ Z →L[ℝ] Z :=
    (InnerProductSpace.toDual ℝ Z).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hLift :
      ContDiffAt ℝ 3 (partialMinimizationLift Φ) (WithLp.toLp 2 (x, yy)) :=
    partialMinimizationLift_contDiffAt Φ x yy hPhi
  have hfderiv_C2 :
      ContDiffAt ℝ 2 (fderiv ℝ (partialMinimizationLift Φ)) (WithLp.toLp 2 (x, yy)) := by
    exact hLift.fderiv_right (by norm_num)
  have hGrad_C2 :
      ContDiffAt ℝ 2 (∇ (partialMinimizationLift Φ)) (WithLp.toLp 2 (x, yy)) := by
    simpa [gradient, Ddual] using
      Ddual.contDiff.contDiffAt.comp (WithLp.toLp 2 (x, yy)) hfderiv_C2
  -- Compose the ambient gradient with the fixed `WithLp` chart and project to the `y`-component.
  simpa [Function.comp] using
    (WithLp.sndL 2 ℝ E₁ E₂).contDiff.contDiffAt.comp (x, yy)
      (hGrad_C2.comp (x, yy)
        (((((WithLp.prodContinuousLinearEquiv 2 ℝ E₁ E₂).symm :
            (E₁ × E₂) ≃L[ℝ] Z) : (E₁ × E₂) →L[ℝ] Z)).contDiff.contDiffAt))

/-- Helper for Theorem 5.3.6: at a `C¹` point, the `y`-component of the ambient gradient of the
lifted objective agrees with the gradient of the frozen `y`-slice. -/
private lemma partialMinimizationYGradient_eq_frozenYGradient
    (Φ : E₁ × E₂ → ℝ) (x : E₁) (yy : E₂)
    (hPhi : ContDiffAt ℝ 1 Φ (x, yy)) :
    WithLp.sndL 2 ℝ E₁ E₂ (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 (x, yy))) =
      ∇ (Φ ∘ Prod.mk x) yy := by
  have hLiftDiff :
      DifferentiableAt ℝ (partialMinimizationLift Φ) (WithLp.toLp 2 (x, yy)) := by
    -- Only first-order differentiability is needed to compare the two gradient presentations.
    simpa [partialMinimizationLift, Function.comp] using
      (hPhi.differentiableAt (by norm_num)).comp (WithLp.toLp 2 (x, yy))
        ((((WithLp.prodContinuousLinearEquiv 2 ℝ E₁ E₂ : Z ≃L[ℝ] E₁ × E₂) :
          Z →L[ℝ] E₁ × E₂)).hasFDerivAt.differentiableAt)
  have hAmbient :
      HasGradientAt (Φ ∘ Prod.mk x)
        (WithLp.sndL 2 ℝ E₁ E₂ (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 (x, yy)))) yy := by
    rw [hasGradientAt_iff_hasFDerivAt]
    -- Differentiate the lifted objective along the right-coordinate inclusion and rewrite the
    -- resulting dual map as the dual of the ambient `y`-gradient component.
    convert
      (hLiftDiff.hasGradientAt.hasFDerivAt.comp yy
        (((WithLp.prodContinuousLinearEquiv 2 ℝ E₁ E₂).symm.hasFDerivAt.comp yy
          (hasFDerivAt_prodMk_right x yy)))) using 1
    ext k
    simp [ContinuousLinearMap.comp_apply, InnerProductSpace.toDual_apply_apply,
      partialMinimizationLift, WithLp.prod_inner_apply]
  have hSliceDiff :
      DifferentiableAt ℝ (Φ ∘ Prod.mk x) yy := by
    simpa [Function.comp] using
      (hPhi.differentiableAt (by norm_num)).comp yy
        (hasFDerivAt_prodMk_right x yy).differentiableAt
  exact hAmbient.unique hSliceDiff.hasGradientAt

private lemma partialMinimizationXGradient_eq_frozenXGradient
    (Φ : E₁ × E₂ → ℝ) (x : E₁) (yy : E₂)
    (hPhi : ContDiffAt ℝ 1 Φ (x, yy)) :
    WithLp.fstL 2 ℝ E₁ E₂ (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 (x, yy))) =
      ∇ (fun u : E₁ ↦ Φ (u, yy)) x := by
  have hLiftDiff :
      DifferentiableAt ℝ (partialMinimizationLift Φ) (WithLp.toLp 2 (x, yy)) := by
    simpa [partialMinimizationLift, Function.comp] using
      (hPhi.differentiableAt (by norm_num)).comp (WithLp.toLp 2 (x, yy))
        ((((WithLp.prodContinuousLinearEquiv 2 ℝ E₁ E₂ : Z ≃L[ℝ] E₁ × E₂) :
          Z →L[ℝ] E₁ × E₂)).hasFDerivAt.differentiableAt)
  have hAmbient :
      HasGradientAt (fun u : E₁ ↦ Φ (u, yy))
        (WithLp.fstL 2 ℝ E₁ E₂ (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 (x, yy)))) x := by
    rw [hasGradientAt_iff_hasFDerivAt]
    -- Rewrite the derivative of the lifted objective along the left-coordinate inclusion.
    convert
      (hLiftDiff.hasGradientAt.hasFDerivAt.comp x
        (((WithLp.prodContinuousLinearEquiv 2 ℝ E₁ E₂).symm.hasFDerivAt.comp x
          (hasFDerivAt_prodMk_left x yy)))) using 1
    ext k
    simp [ContinuousLinearMap.comp_apply, InnerProductSpace.toDual_apply_apply,
      partialMinimizationLift, WithLp.prod_inner_apply]
  have hSliceDiff :
      DifferentiableAt ℝ (fun u : E₁ ↦ Φ (u, yy)) x := by
    -- Freeze the second coordinate and differentiate in the `x`-direction.
    simpa [Function.comp] using
      (hPhi.differentiableAt (by norm_num)).comp x
        (hasFDerivAt_prodMk_left x yy).differentiableAt
  exact hAmbient.unique hSliceDiff.hasGradientAt

/-- Helper for Theorem 5.3.6: vanishing of the ambient stationary map forces the frozen `y`-slice
derivative to vanish at the same point. -/
private lemma frozenYSlice_hasFDerivAtZero_of_stationaryMap_eq_zero
    (Φ : E₁ × E₂ → ℝ) (u : E₁) (yy : E₂)
    (hPhi : ContDiffAt ℝ 1 Φ (u, yy))
    (hStationary :
      WithLp.sndL 2 ℝ E₁ E₂ (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 (u, yy))) = 0) :
    HasFDerivAt (Φ ∘ Prod.mk u) (0 : E₂ →L[ℝ] ℝ) yy := by
  have hSliceDiff :
      DifferentiableAt ℝ (Φ ∘ Prod.mk u) yy := by
    -- The frozen slice inherits differentiability from the ambient `C¹` objective.
    simpa [Function.comp] using
      (hPhi.differentiableAt (by norm_num)).comp yy
        (hasFDerivAt_prodMk_right u yy).differentiableAt
  have hGradZero : ∇ (Φ ∘ Prod.mk u) yy = 0 := by
    -- Read the stationary map as the actual frozen-slice gradient first.
    calc
      ∇ (Φ ∘ Prod.mk u) yy
          = WithLp.sndL 2 ℝ E₁ E₂
              (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 (u, yy))) := by
                symm
                exact partialMinimizationYGradient_eq_frozenYGradient Φ u yy hPhi
      _ = 0 := hStationary
  have hGradAtZero : HasGradientAt (Φ ∘ Prod.mk u) 0 yy := by
    simpa [hGradZero] using hSliceDiff.hasGradientAt
  simpa using hGradAtZero.hasFDerivAt

/-- Helper for Theorem 5.3.6: the frozen `y`-gradient is differentiable at a `C²` point, and its
derivative is the frozen-slice Hessian. -/
private lemma frozenYGradient_hasFDerivAt_hessian
    (Φ : E₁ × E₂ → ℝ) (x : E₁) (yy : E₂)
    (hPhi : ContDiffAt ℝ 2 Φ (x, yy)) :
    HasFDerivAt (fun z : E₂ ↦ ∇ (Φ ∘ Prod.mk x) z) (hessian (Φ ∘ Prod.mk x) yy) yy := by
  let Ddual : StrongDual ℝ E₂ →L[ℝ] E₂ :=
    (InnerProductSpace.toDual ℝ E₂).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hSlice : ContDiffAt ℝ 2 (Φ ∘ Prod.mk x) yy := by
    have hProdMkRight : ContDiffAt ℝ 2 (Prod.mk x : E₂ → E₁ × E₂) yy := by
      fun_prop
    simpa [Function.comp] using hPhi.comp yy hProdMkRight
  have hfderiv_C1 :
      ContDiffAt ℝ 1 (fderiv ℝ (Φ ∘ Prod.mk x)) yy := by
    exact hSlice.fderiv_right (by norm_num)
  have hGrad_C1 : ContDiffAt ℝ 1 (∇ (Φ ∘ Prod.mk x)) yy := by
    simpa [gradient, Ddual] using Ddual.contDiff.contDiffAt.comp yy hfderiv_C1
  simpa [hessian] using (hGrad_C1.differentiableAt (by norm_num)).hasFDerivAt

/-- Helper for Theorem 5.3.6: restricting the ambient stationary-map derivative to the vertical
`y`-direction recovers the frozen-slice `yy` Hessian block. -/
private lemma partialMinimizationYGradient_comp_inr_eq_yyHessian
    (Φ : E₁ × E₂ → ℝ) (x : E₁) (yy : E₂)
    (hPhi : ContDiffAt ℝ 2 Φ (x, yy)) :
    (((WithLp.sndL 2 ℝ E₁ E₂).comp (partialMinimizationAmbientHessian Φ x yy)).comp
      (inr ℝ E₁ E₂)) = hessian (Φ ∘ Prod.mk x) yy := by
  have hAmbientDeriv :
      HasFDerivAt
        (fun z : E₂ ↦
          WithLp.sndL 2 ℝ E₁ E₂ (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 (x, z))))
        (((WithLp.sndL 2 ℝ E₁ E₂).comp (partialMinimizationAmbientHessian Φ x yy)).comp
          (inr ℝ E₁ E₂))
        yy := by
    simpa [Function.comp] using
      (partialMinimizationYGradient_hasFDerivAt Φ x yy hPhi).comp yy
        (hasFDerivAt_prodMk_right x yy)
  have hFrozenDeriv :
      HasFDerivAt
        (fun z : E₂ ↦ ∇ (Φ ∘ Prod.mk x) z)
        (hessian (Φ ∘ Prod.mk x) yy)
        yy :=
    frozenYGradient_hasFDerivAt_hessian Φ x yy hPhi
  have hEventEq :
      (fun z : E₂ ↦
        WithLp.sndL 2 ℝ E₁ E₂ (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 (x, z)))) =ᶠ[nhds yy]
          fun z : E₂ ↦ ∇ (Φ ∘ Prod.mk x) z := by
    -- Near a `C²` point, the ambient and frozen `y`-gradient presentations agree on the vertical
    -- line through `x`.
    exact
      (show (fun z : E₁ × E₂ ↦
          WithLp.sndL 2 ℝ E₁ E₂ (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 z))) =ᶠ[
            nhds (x, yy)] fun z : E₁ × E₂ ↦ ∇ (Φ ∘ Prod.mk z.1) z.2 from by
          rcases (hPhi.contDiffOn (m := 1) (by norm_num) (by simp)) with ⟨u, hu_nhds, hContU⟩
          rcases mem_nhds_iff.mp hu_nhds with ⟨v, hv_sub, hv_open, hv_mem⟩
          have hContV : ContDiffOn ℝ 1 Φ v := hContU.mono hv_sub
          filter_upwards [hv_open.mem_nhds hv_mem] with z hz
          exact partialMinimizationYGradient_eq_frozenYGradient Φ z.1 z.2
            (hContV.contDiffAt (hv_open.mem_nhds hz))).comp_tendsto
        ((Continuous.prodMk continuous_const continuous_id).continuousAt.tendsto)
  have hFrozenDeriv' :
      HasFDerivAt
        (fun z : E₂ ↦
          WithLp.sndL 2 ℝ E₁ E₂ (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 (x, z))))
        (hessian (Φ ∘ Prod.mk x) yy)
        yy := by
    exact hFrozenDeriv.congr_of_eventuallyEq hEventEq
  exact hAmbientDeriv.unique hFrozenDeriv'

/-- Helper for Theorem 5.3.6: near any point of `D`, the stationary equation admits a canonical
implicit `C²` branch through the selected minimizer. -/
private lemma implicitStationaryBranchPacket_of_mem_dom
    (hΦ : IsSelfConcordantBarrierOnWith QZ ν (Φ ∘ WithLp.ofLp))
    (hy_argmin : ∀ ⦃x : E₁⦄, x ∈ D → y x ∈ argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x))
    (hy_unique : ∀ ⦃x : E₁⦄, x ∈ D → ∀ ⦃y' : E₂⦄,
        y' ∈ argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x) → y' = y x)
    (hyy_pos :
      ∀ ⦃x : E₁⦄, x ∈ D → ∀ v : E₂, v ≠ 0 →
        0 < inner ℝ v ((hessian (Φ ∘ Prod.mk x) (y x)) v))
    {x : E₁} (hx : x ∈ D) :
    ∃ s : Set E₁, ∃ ψ : E₁ → E₂,
      IsOpen s ∧ x ∈ s ∧ ψ x = y x ∧ ContDiffOn ℝ 2 ψ s ∧
      HasStrictFDerivAt ψ (partialMinimizerImplicitFDeriv Φ x (y x)) x ∧
      ∀ u ∈ s, (u, ψ u) ∈ interior Q ∧
        WithLp.sndL 2 ℝ E₁ E₂ (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 (u, ψ u))) = 0 := by
  let F : E₁ × E₂ → E₂ := fun z ↦
    WithLp.sndL 2 ℝ E₁ E₂ (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 z))
  have hLift :
      ContDiffAt ℝ 3 (partialMinimizationLift Φ) (WithLp.toLp 2 (x, y x)) := by
    -- The ambient barrier owner already supplies the local `C³` regularity of `Φ`.
    simpa [partialMinimizationLift] using
      (ambientLift_isStandardSelfConcordantOnInterior_of_barrier
        (Q := Q) (ν := ν) (Φ := Φ) hΦ).contDiffOn.contDiffAt
          (by simpa using
            (ambientLift_isStandardSelfConcordantOnInterior_of_barrier
              (Q := Q) (ν := ν) (Φ := Φ) hΦ).isOpen_domain.mem_nhds
                (by
                  simpa using selectedFiberMinimizer_mem_interior_of_dom
                    (Q := Q) (ν := ν) (Φ := Φ) (y := y) hΦ hy_argmin hx))
  have hPhi :
      ContDiffAt ℝ 3 Φ (x, y x) := by
    -- Pull the lifted regularity back through the fixed `WithLp` product equivalence.
    simpa [partialMinimizationLift, Function.comp] using
      hLift.comp (x, y x)
        ((((WithLp.prodContinuousLinearEquiv 2 ℝ E₁ E₂).symm :
            (E₁ × E₂) ≃L[ℝ] Z)).contDiff.contDiffAt)
  have hF_cont :
      ContDiffAt ℝ 2 F (x, y x) := by
    simpa [F] using partialMinimizationYStationaryMap_contDiffAt Φ x (y x) hPhi
  have hF_deriv :
      HasFDerivAt F ((WithLp.sndL 2 ℝ E₁ E₂).comp
        (partialMinimizationAmbientHessian Φ x (y x))) (x, y x) := by
    simpa [F] using partialMinimizationYGradient_hasFDerivAt Φ x (y x) (hPhi.of_le (by norm_num))
  have hF_inr :
      fderiv ℝ F (x, y x) ∘L inr ℝ E₁ E₂ = hessian (Φ ∘ Prod.mk x) (y x) := by
    rw [hF_deriv.fderiv]
    exact partialMinimizationYGradient_comp_inr_eq_yyHessian Φ x (y x) (hPhi.of_le (by norm_num))
  have hF_inl :
      fderiv ℝ F (x, y x) ∘L inl ℝ E₁ E₂ = partialMinimizationYXHessian Φ x (y x) := by
    rw [hF_deriv.fderiv]
    rfl
  have hIf2 : (fderiv ℝ F (x, y x) ∘L inr ℝ E₁ E₂).IsInvertible := by
    rw [hF_inr]
    exact selectedFiberHessianInvertible_of_barrierArgmin
      (Q := Q) (ν := ν) (Φ := Φ) (y := y) hΦ hy_argmin hy_unique hx
  have hbase_zero :
      F (x, y x) = 0 := by
    have hPhi1 : ContDiffAt ℝ 1 Φ (x, y x) := hPhi.of_le (by norm_num)
    have hgrad_zero :
        ∇ (Φ ∘ Prod.mk x) (y x) = 0 :=
      selectedFiberGradient_eq_zero_of_barrierArgmin
        (Q := Q) (ν := ν) (Φ := Φ) (y := y) hΦ hy_argmin hx
    calc
      F (x, y x) = ∇ (Φ ∘ Prod.mk x) (y x) := by
        simpa [F] using partialMinimizationYGradient_eq_frozenYGradient Φ x (y x) hPhi1
      _ = 0 := hgrad_zero
  let ψ : E₁ → E₂ := hF_cont.implicitFunction (pn := by norm_num) hIf2
  have hψ_self : ψ x = y x := by
    simpa [ψ] using hF_cont.implicitFunction_apply_self (pn := by norm_num) hIf2
  have hψ_deriv :
      HasStrictFDerivAt ψ (partialMinimizerImplicitFDeriv Φ x (y x)) x := by
    simpa [ψ, partialMinimizerImplicitFDeriv, hF_inr, hF_inl] using
      (hF_cont.hasStrictFDerivAt_implicitFunction (pn := by norm_num) hIf2)
  have hψ_cont : ContDiffAt ℝ 2 ψ x := by
    simpa [ψ] using hF_cont.contDiffAt_implicitFunction (pn := by norm_num) hIf2
  have hψ_graph_tendsto :
      Filter.Tendsto (fun u ↦ (u, ψ u)) (nhds x) (nhds (x, y x)) := by
    simpa [hψ_self, nhds_prod_eq] using continuousAt_id.tendsto.prodMk hψ_cont.continuousAt.tendsto
  have hψ_mem_interior :
      ∀ᶠ u in nhds x, (u, ψ u) ∈ interior Q := by
    exact hψ_graph_tendsto.eventually
      (IsOpen.mem_nhds isOpen_interior
        (selectedFiberMinimizer_mem_interior_of_dom
          (Q := Q) (ν := ν) (Φ := Φ) (y := y) hΦ hy_argmin hx))
  have hψ_stationary :
      ∀ᶠ u in nhds x,
        WithLp.sndL 2 ℝ E₁ E₂ (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 (u, ψ u))) = 0 := by
    filter_upwards [hF_cont.eventually_apply_implicitFunction (pn := by norm_num) hIf2] with u hu
    have hu_zero : F (u, ψ u) = 0 := by
      exact hu.trans hbase_zero
    simpa [F] using hu_zero
  rcases hψ_cont.contDiffOn (m := 2) le_rfl (by simp) with ⟨t, ht_nhds, hψOn_t⟩
  have hcore :
      ∀ᶠ u in nhds x,
        u ∈ t ∧ (u, ψ u) ∈ interior Q ∧
          WithLp.sndL 2 ℝ E₁ E₂ (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 (u, ψ u))) = 0 := by
    filter_upwards [ht_nhds, hψ_mem_interior, hψ_stationary] with u hu_t hu_int hu_stat
    exact ⟨hu_t, hu_int, hu_stat⟩
  rcases mem_nhds_iff.mp hcore with ⟨s, hs_sub, hs_open, hsx⟩
  refine ⟨s, ψ, hs_open, hsx, hψ_self, ?_, hψ_deriv, ?_⟩
  · -- Restrict the implicit branch regularity to the honest open neighborhood `s`.
    exact hψOn_t.mono fun u hu ↦ (hs_sub hu).1
  · intro u hu
    -- Package the local interior and stationary data that will be transported to the selected
    -- minimizer branch on `D`.
    exact ⟨(hs_sub hu).2.1, (hs_sub hu).2.2⟩

/-- Helper for Theorem 5.3.6: on the implicit stationary branch, interior stationarity transports
to the actual selected minimizer branch and to the reduced objective value. -/
private lemma selectedMinimizerTransport_onImplicitBranch
    (hΦ : IsSelfConcordantBarrierOnWith QZ ν (Φ ∘ WithLp.ofLp))
    (hy_argmin : ∀ ⦃x : E₁⦄, x ∈ D → y x ∈ argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x))
    (hy_unique : ∀ ⦃x : E₁⦄, x ∈ D → ∀ ⦃y' : E₂⦄,
        y' ∈ argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x) → y' = y x)
    {s : Set E₁} {ψ : E₁ → E₂}
    (hpacket :
      ∀ u ∈ s, (u, ψ u) ∈ interior Q ∧
        WithLp.sndL 2 ℝ E₁ E₂ (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 (u, ψ u))) = 0) :
    ∀ u ∈ s,
      u ∈ D ∧
        ψ u ∈ argmin[(Prod.mk u) ⁻¹' Q] (Φ ∘ Prod.mk u) ∧
        ψ u = y u ∧
        f u = Φ (u, ψ u) := by
  intro u hu
  rcases hpacket u hu with ⟨hu_int, hu_stat⟩
  have hLift_u :
      ContDiffAt ℝ 3 (partialMinimizationLift Φ) (WithLp.toLp 2 (u, ψ u)) := by
    simpa [partialMinimizationLift] using
      (ambientLift_isStandardSelfConcordantOnInterior_of_barrier
        (Q := Q) (ν := ν) (Φ := Φ) hΦ).contDiffOn.contDiffAt
          (by simpa using
            (ambientLift_isStandardSelfConcordantOnInterior_of_barrier
              (Q := Q) (ν := ν) (Φ := Φ) hΦ).isOpen_domain.mem_nhds
                (by simpa using hu_int))
  have hPhi_u :
      ContDiffAt ℝ 3 Φ (u, ψ u) := by
    -- Pull the ambient `C³` regularity back to the raw pair on the branch.
    simpa [partialMinimizationLift, Function.comp] using
      hLift_u.comp (u, ψ u)
        ((((WithLp.prodContinuousLinearEquiv 2 ℝ E₁ E₂).symm :
            (E₁ × E₂) ≃L[ℝ] Z)).contDiff.contDiffAt)
  have hzero_deriv :
      HasFDerivAt (Φ ∘ Prod.mk u) (0 : E₂ →L[ℝ] ℝ) (ψ u) :=
    frozenYSlice_hasFDerivAtZero_of_stationaryMap_eq_zero Φ u (ψ u)
      (hPhi_u.of_le (by norm_num)) hu_stat
  have hψ_argmin :
      ψ u ∈ argmin[(Prod.mk u) ⁻¹' Q] (Φ ∘ Prod.mk u) :=
    stationaryFiber_mem_argmin (Q := Q) (ν := ν) (Φ := Φ) hΦ hu_int hzero_deriv
  have hu_dom : u ∈ D := by
    rw [mem_extendedRealEffectiveDomain_iff, partialInfProjection_eq_argmin_eReal Q Φ hψ_argmin]
    simp
  have hψ_eq : ψ u = y u := hy_unique hu_dom hψ_argmin
  refine ⟨hu_dom, hψ_argmin, hψ_eq, ?_⟩
  -- Once the stationary branch is known to be the actual minimizing branch, the reduced
  -- objective evaluates to its branch value.
  exact partialMinimizationObjective_eq_of_mem_argmin Q Φ hψ_argmin

/-- Helper for Theorem 5.3.6: at every point of `D`, the reduced objective has the envelope
gradient formula and the Schur-complement Hessian formula determined by the selected minimizer. -/
private lemma reducedObjectiveFormulas_of_mem_dom
    (hΦ : IsSelfConcordantBarrierOnWith QZ ν (Φ ∘ WithLp.ofLp))
    (hy_argmin : ∀ ⦃x : E₁⦄, x ∈ D → y x ∈ argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x))
    (hy_unique : ∀ ⦃x : E₁⦄, x ∈ D → ∀ ⦃y' : E₂⦄,
        y' ∈ argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x) → y' = y x)
    {x : E₁} (hx : x ∈ D) :
    ∇ f x = ∇ (fun u' ↦ Φ (u', y x)) x ∧
      hessian f x = partialMinimizationSchurHessian Φ x (y x) := by
  have hyy_pos :
      ∀ ⦃u : E₁⦄, u ∈ D → ∀ v : E₂, v ≠ 0 →
        0 < inner ℝ v ((hessian (Φ ∘ Prod.mk u) (y u)) v) := by
    intro u hu v hv
    exact selectedFiberHessianPos_of_barrierArgmin
      (Q := Q) (ν := ν) (Φ := Φ) (y := y) hΦ hy_argmin hy_unique hu v hv
  rcases implicitStationaryBranchPacket_of_mem_dom
      (Q := Q) (ν := ν) (Φ := Φ) (y := y)
      hΦ hy_argmin hy_unique hyy_pos hx with
    ⟨s, ψ, hs_open, hsx, hψ_self, hψ_cont, _, hpacket⟩
  have htransport :=
    selectedMinimizerTransport_onImplicitBranch
      (Q := Q) (ν := ν) (Φ := Φ) (y := y)
      hΦ hy_argmin hy_unique hpacket
  have hyy_inv :
      (hessian (Φ ∘ Prod.mk x) (y x)).IsInvertible :=
    selectedFiberHessianInvertible_of_barrierArgmin
      (Q := Q) (ν := ν) (Φ := Φ) (y := y) hΦ hy_argmin hy_unique hx
  have hψ_tendsto : Filter.Tendsto ψ (nhds x) (nhds (y x)) := by
    -- The implicit branch is continuous at `x` and passes through the selected minimizer.
    simpa [hψ_self] using
      (hψ_cont.contDiffAt (hs_open.mem_nhds hsx)).continuousAt.tendsto
  have hPhi_x :
      ContDiffAt ℝ 2 Φ (x, y x) := by
    have hLift_x :
        ContDiffAt ℝ 3 (partialMinimizationLift Φ) (WithLp.toLp 2 (x, ψ x)) := by
      -- The ambient barrier owner supplies `C³` regularity at the branch point.
      simpa [partialMinimizationLift] using
        (ambientLift_isStandardSelfConcordantOnInterior_of_barrier
          (Q := Q) (ν := ν) (Φ := Φ) hΦ).contDiffOn.contDiffAt
            (by simpa using
              (ambientLift_isStandardSelfConcordantOnInterior_of_barrier
                (Q := Q) (ν := ν) (Φ := Φ) hΦ).isOpen_domain.mem_nhds
                  (by simpa using (hpacket x hsx).1))
    have hPhi_branch :
        ContDiffAt ℝ 3 Φ (x, ψ x) := by
      -- Pull the lifted regularity back through the fixed product equivalence.
      simpa [partialMinimizationLift, Function.comp] using
        hLift_x.comp (x, ψ x)
          ((((WithLp.prodContinuousLinearEquiv 2 ℝ E₁ E₂).symm :
              (E₁ × E₂) ≃L[ℝ] Z)).contDiff.contDiffAt)
    simpa [hψ_self] using hPhi_branch.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)
  have hψ_argmin :
      ∀ᶠ u in nhds x, ψ u ∈ argmin[(Prod.mk u) ⁻¹' Q] (Φ ∘ Prod.mk u) := by
    -- On the branch neighborhood, the implicit stationary branch is already the selected
    -- minimizer branch.
    filter_upwards [hs_open.mem_nhds hsx] with u hu
    exact (htransport u hu).2.1
  have hgrad :
      ∇ f x = ∇ (fun u' ↦ Φ (u', ψ x)) x := by
    exact partialMinimizationObjective_gradient_eq_xGradient_of_eventually_argmin
      (Q := Q) (Φ := Φ) (x := x) (y := ψ)
      (by simpa [hψ_self] using hPhi_x.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2))
      ((hψ_cont.contDiffAt (hs_open.mem_nhds hsx)).differentiableAt
        (by norm_num : (2 : WithTop ℕ∞) ≠ 0))
      (by simpa [hψ_self] using (hpacket x hsx).1)
      hψ_argmin
  have hhess :
      hessian f x = partialMinimizationSchurHessian Φ x (ψ x) := by
    have hψ_tendsto_self : Filter.Tendsto ψ (nhds x) (nhds (ψ x)) := by
      simpa [hψ_self] using hψ_tendsto
    exact partialMinimizationObjective_hessian_eq_schur_of_isInvertible_yyHessian
      (Q := Q) (Φ := Φ) (x := x) (y := ψ)
      (by simpa [hψ_self] using hPhi_x) hψ_tendsto_self
      (by
        filter_upwards [hs_open.mem_nhds hsx] with u hu
        exact (hpacket u hu).1)
      hψ_argmin
      (by
        filter_upwards [hs_open.mem_nhds hsx] with u hu z hz
        calc
          z = y u := hy_unique (htransport u hu).1 hz
          _ = ψ u := ((htransport u hu).2.2.1).symm)
      (by simpa [hψ_self] using hyy_inv)
  -- Rewrite the local implicit branch back to the selected minimizer at the base point.
  exact ⟨by simpa [hψ_self] using hgrad, by simpa [hψ_self] using hhess⟩

/-- Helper for Theorem 5.3.6: on the graph direction of the implicit minimizer derivative, the
ambient Hessian quadratic form coincides with the quadratic form of the reduced Hessian. -/
private lemma partialMinimizationObjective_graphQuadraticForm_eq_on_dom
    (hΦ : IsSelfConcordantBarrierOnWith QZ ν (Φ ∘ WithLp.ofLp))
    (hy_argmin : ∀ ⦃x : E₁⦄, x ∈ D → y x ∈ argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x))
    (hy_unique : ∀ ⦃x : E₁⦄, x ∈ D → ∀ ⦃y' : E₂⦄,
        y' ∈ argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x) → y' = y x)
    {x : E₁} (hx : x ∈ D) (w : E₁) :
    inner ℝ (WithLp.toLp 2 (w, partialMinimizerImplicitFDeriv Φ x (y x) w))
      ((hessian (partialMinimizationLift Φ) (WithLp.toLp 2 (x, y x)))
        (WithLp.toLp 2 (w, partialMinimizerImplicitFDeriv Φ x (y x) w))) =
      inner ℝ w (hessian f x w) := by
  let v : E₂ := partialMinimizerImplicitFDeriv Φ x (y x) w
  have hyy_inv :
      (hessian (Φ ∘ Prod.mk x) (y x)).IsInvertible :=
    selectedFiberHessianInvertible_of_barrierArgmin
      (Q := Q) (ν := ν) (Φ := Φ) (y := y) hΦ hy_argmin hy_unique hx
  have hformulas :=
    reducedObjectiveFormulas_of_mem_dom
      (Q := Q) (ν := ν) (Φ := Φ) (y := y) hΦ hy_argmin hy_unique hx
  have hhess :
      hessian f x = partialMinimizationSchurHessian Φ x (y x) := hformulas.2
  have hLift_x :
      ContDiffAt ℝ 3 (partialMinimizationLift Φ) (WithLp.toLp 2 (x, y x)) := by
    -- The ambient barrier owner supplies `C³` regularity at the selected minimizer.
    simpa [partialMinimizationLift] using
      (ambientLift_isStandardSelfConcordantOnInterior_of_barrier
        (Q := Q) (ν := ν) (Φ := Φ) hΦ).contDiffOn.contDiffAt
          (by
            have hxy_int :
                (x, y x) ∈ interior Q :=
              selectedFiberMinimizer_mem_interior_of_dom
                (Q := Q) (ν := ν) (Φ := Φ) (y := y) hΦ hy_argmin hx
            simpa using
              (ambientLift_isStandardSelfConcordantOnInterior_of_barrier
                (Q := Q) (ν := ν) (Φ := Φ) hΦ).isOpen_domain.mem_nhds
                  (by simpa using hxy_int))
  have hPhi_x :
      ContDiffAt ℝ 2 Φ (x, y x) := by
    have hPhi_x3 :
        ContDiffAt ℝ 3 Φ (x, y x) := by
      -- Pull the lifted regularity back through the fixed product equivalence.
      simpa [partialMinimizationLift, Function.comp] using
        hLift_x.comp (x, y x)
          ((((WithLp.prodContinuousLinearEquiv 2 ℝ E₁ E₂).symm :
              (E₁ × E₂) ≃L[ℝ] Z)).contDiff.contDiffAt)
    exact hPhi_x3.of_le (by norm_num)
  have hAmbientHessianY :
      WithLp.sndL 2 ℝ E₁ E₂
          ((hessian (partialMinimizationLift Φ) (WithLp.toLp 2 (x, y x)))
            (WithLp.toLp 2 (w, v))) = 0 := by
    -- The implicit derivative kills the vertical Hessian block on graph directions.
    have hsplit :
        ((w, v) : E₁ × E₂) =
          (ContinuousLinearMap.inl ℝ E₁ E₂) w +
            (ContinuousLinearMap.inr ℝ E₁ E₂) v := by
      ext <;> simp
    calc
      WithLp.sndL 2 ℝ E₁ E₂
          ((hessian (partialMinimizationLift Φ) (WithLp.toLp 2 (x, y x)))
            (WithLp.toLp 2 (w, v)))
          = (((WithLp.sndL 2 ℝ E₁ E₂).comp (partialMinimizationAmbientHessian Φ x (y x)))
              (w, v)) := by
                rfl
      _ = (((WithLp.sndL 2 ℝ E₁ E₂).comp (partialMinimizationAmbientHessian Φ x (y x)))
            ((ContinuousLinearMap.inl ℝ E₁ E₂) w +
              (ContinuousLinearMap.inr ℝ E₁ E₂) v)) := by
            rw [hsplit]
      _ = (((WithLp.sndL 2 ℝ E₁ E₂).comp (partialMinimizationAmbientHessian Φ x (y x))).comp
            (ContinuousLinearMap.inl ℝ E₁ E₂)) w +
          ((((WithLp.sndL 2 ℝ E₁ E₂).comp (partialMinimizationAmbientHessian Φ x (y x))).comp
            (ContinuousLinearMap.inr ℝ E₁ E₂)) v) := by
              rw [map_add]
              rfl
      _ = partialMinimizationYXHessian Φ x (y x) w +
          (hessian (Φ ∘ Prod.mk x) (y x)) v := by
            rw [partialMinimizationYGradient_comp_inr_eq_yyHessian Φ x (y x) hPhi_x]
            rfl
      _ = partialMinimizationYXHessian Φ x (y x) w -
          partialMinimizationYXHessian Φ x (y x) w := by
            simp [v, partialMinimizerImplicitFDeriv, ContinuousLinearMap.comp_apply,
              hyy_inv.self_apply_inverse]
      _ = 0 := sub_self _
  have hAmbientHessianX :
      WithLp.fstL 2 ℝ E₁ E₂
          ((hessian (partialMinimizationLift Φ) (WithLp.toLp 2 (x, y x)))
            (WithLp.toLp 2 (w, v))) =
        hessian f x w := by
    -- The horizontal Hessian block on the graph direction is the Schur complement.
    have hsplit :
        ((w, v) : E₁ × E₂) =
          (ContinuousLinearMap.inl ℝ E₁ E₂) w +
            (ContinuousLinearMap.inr ℝ E₁ E₂) v := by
      ext <;> simp
    calc
      WithLp.fstL 2 ℝ E₁ E₂
          ((hessian (partialMinimizationLift Φ) (WithLp.toLp 2 (x, y x)))
            (WithLp.toLp 2 (w, v)))
          = (((WithLp.fstL 2 ℝ E₁ E₂).comp (partialMinimizationAmbientHessian Φ x (y x)))
              (w, v)) := by
                rfl
      _ = (((WithLp.fstL 2 ℝ E₁ E₂).comp (partialMinimizationAmbientHessian Φ x (y x)))
            ((ContinuousLinearMap.inl ℝ E₁ E₂) w +
              (ContinuousLinearMap.inr ℝ E₁ E₂) v)) := by
            rw [hsplit]
      _ = partialMinimizationXXHessian Φ x (y x) w +
          (partialMinimizationXYHessian Φ x (y x)) v := by
            rw [map_add]
            simp [partialMinimizationXXHessian, partialMinimizationXYHessian,
              ContinuousLinearMap.comp_apply]
      _ = partialMinimizationSchurHessian Φ x (y x) w := by
            simp [partialMinimizationSchurHessian, v, ContinuousLinearMap.comp_apply]
      _ = hessian f x w := by
            simpa [hhess]
  -- The graph Hessian vector has horizontal component `∇²f(x) w` and zero vertical component.
  calc
    inner ℝ (WithLp.toLp 2 (w, v))
        ((hessian (partialMinimizationLift Φ) (WithLp.toLp 2 (x, y x)))
          (WithLp.toLp 2 (w, v)))
        =
          inner ℝ w
            (WithLp.fstL 2 ℝ E₁ E₂
              ((hessian (partialMinimizationLift Φ) (WithLp.toLp 2 (x, y x)))
                (WithLp.toLp 2 (w, v)))) +
            inner ℝ v
              (WithLp.sndL 2 ℝ E₁ E₂
                ((hessian (partialMinimizationLift Φ) (WithLp.toLp 2 (x, y x)))
                  (WithLp.toLp 2 (w, v)))) := by
            simp [WithLp.prod_inner_apply]
    _ = inner ℝ w (hessian f x w) + inner ℝ v 0 := by
          rw [hAmbientHessianX, hAmbientHessianY]
    _ = inner ℝ w (hessian f x w) := by
          simp

/-- Helper for Theorem 5.3.6: the ambient barrier inequality rewrites to the reduced-objective
barrier inequality once the selected minimizer formulas are projected back to `E₁`. -/
private lemma reducedObjective_barrierBound_of_mem_dom
    (hΦ : IsSelfConcordantBarrierOnWith QZ ν (Φ ∘ WithLp.ofLp))
    (hy_argmin : ∀ ⦃x : E₁⦄, x ∈ D → y x ∈ argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x))
    (hy_unique : ∀ ⦃x : E₁⦄, x ∈ D → ∀ ⦃y' : E₂⦄,
        y' ∈ argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x) → y' = y x)
    {x : E₁} (hx : x ∈ D) (u : E₁) :
    2 * inner ℝ (∇ f x) u - inner ℝ u (hessian f x u) ≤ (ν : ℝ) := by
  let v : E₂ := partialMinimizerImplicitFDeriv Φ x (y x) u
  have hformulas :=
    reducedObjectiveFormulas_of_mem_dom
      (Q := Q) (ν := ν) (Φ := Φ) (y := y) hΦ hy_argmin hy_unique hx
  have hPhi_x :
      ContDiffAt ℝ 1 Φ (x, y x) := by
    have hLift_x :
        ContDiffAt ℝ 3 (partialMinimizationLift Φ) (WithLp.toLp 2 (x, y x)) := by
      -- The ambient barrier owner supplies the required local smoothness at the selected point.
      simpa [partialMinimizationLift] using
        hΦ.toIsStandardSelfConcordantOn.contDiffOn.contDiffAt
          (hΦ.toIsStandardSelfConcordantOn.isOpen_domain.mem_nhds
            (by simpa using (mem_constrainedArgmin_iff.mp (hy_argmin hx)).1))
    have hPhi_x3 :
        ContDiffAt ℝ 3 Φ (x, y x) := by
      simpa [partialMinimizationLift, Function.comp] using
        hLift_x.comp (x, y x)
          ((((WithLp.prodContinuousLinearEquiv 2 ℝ E₁ E₂).symm :
              (E₁ × E₂) ≃L[ℝ] Z)).contDiff.contDiffAt)
    exact hPhi_x3.of_le (by norm_num)
  have hgradX :
      WithLp.fstL 2 ℝ E₁ E₂ (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 (x, y x))) =
        ∇ f x := by
    calc
      WithLp.fstL 2 ℝ E₁ E₂ (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 (x, y x)))
          = ∇ (fun u' ↦ Φ (u', y x)) x := by
              exact partialMinimizationXGradient_eq_frozenXGradient Φ x (y x) hPhi_x
      _ = ∇ f x := hformulas.1.symm
  have hgradY :
      WithLp.sndL 2 ℝ E₁ E₂ (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 (x, y x))) = 0 := by
    calc
      WithLp.sndL 2 ℝ E₁ E₂ (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 (x, y x)))
          = ∇ (Φ ∘ Prod.mk x) (y x) := by
              exact partialMinimizationYGradient_eq_frozenYGradient Φ x (y x) hPhi_x
      _ = 0 := selectedFiberGradient_eq_zero_of_barrierArgmin
        (Q := Q) (ν := ν) (Φ := Φ) (y := y) hΦ hy_argmin hx
  have hquad :
      inner ℝ (WithLp.toLp 2 (u, v))
          ((hessian (partialMinimizationLift Φ) (WithLp.toLp 2 (x, y x)))
            (WithLp.toLp 2 (u, v))) =
        inner ℝ u (hessian f x u) :=
    partialMinimizationObjective_graphQuadraticForm_eq_on_dom
      (Q := Q) (ν := ν) (Φ := Φ) (y := y) hΦ hy_argmin hy_unique hx u
  have hx_mem : WithLp.toLp 2 (x, y x) ∈ QZ := by
    simpa using (mem_constrainedArgmin_iff.mp (hy_argmin hx)).1
  have hbar :=
    hΦ.barrier_parameter_bound hx_mem (WithLp.toLp 2 (u, v))
  have hgrad_fst :
      (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 (x, y x))).fst = ∇ f x := by
    simpa using hgradX
  have hgrad_snd :
      (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 (x, y x))).snd = 0 := by
    simpa using hgradY
  have hgrad_pair :
      inner ℝ (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 (x, y x)))
          (WithLp.toLp 2 (u, v)) =
        inner ℝ (∇ f x) u := by
    calc
      inner ℝ (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 (x, y x)))
          (WithLp.toLp 2 (u, v))
          = inner ℝ (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 (x, y x))).fst u +
              inner ℝ (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 (x, y x))).snd v := by
                simp [WithLp.prod_inner_apply]
      _ = inner ℝ (∇ f x) u + inner ℝ 0 v := by rw [hgrad_fst, hgrad_snd]
      _ = inner ℝ (∇ f x) u := by simp
  -- Rewrite the ambient inequality through the projected `x`-gradient and the graph quadratic
  -- identity for the reduced Hessian.
  calc
    2 * inner ℝ (∇ f x) u - inner ℝ u (hessian f x u)
        = 2 * inner ℝ (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 (x, y x)))
            (WithLp.toLp 2 (u, v)) -
          inner ℝ (WithLp.toLp 2 (u, v))
            ((hessian (partialMinimizationLift Φ) (WithLp.toLp 2 (x, y x)))
              (WithLp.toLp 2 (u, v))) := by
              rw [hgrad_pair, hquad]
    _ ≤ (ν : ℝ) := hbar

/-- Helper for Theorem 5.3.6: standard self-concordance on an open domain only depends on the
ambient function values on that domain. -/
private theorem selfConcordantOnWith_congrEqOnLocal
    {domain : Set E₁} {Mf : NNReal} {g₁ g₂ : E₁ → ℝ}
    (h : IsSelfConcordantOnWith domain Mf g₁) (hEq : Set.EqOn g₁ g₂ domain) :
    IsSelfConcordantOnWith domain Mf g₂ := by
  refine
    { isOpen_domain := h.isOpen_domain
      contDiffOn := (contDiffOn_congr fun x hx ↦ (hEq hx).symm).2 h.contDiffOn
      convexOn := h.convexOn.congr hEq
      third_deriv_bound := ?_ }
  intro x hx u
  have hEqAt : g₂ =ᶠ[nhds x] g₁ := by
    refine Filter.mem_of_superset (h.isOpen_domain.mem_nhds hx) ?_
    intro z hz
    exact (hEq hz).symm
  have hG1contAt : ContDiffAt ℝ 3 g₁ x :=
    h.contDiffOn.contDiffAt (h.isOpen_domain.mem_nhds hx)
  have hG2contAt : ContDiffAt ℝ 3 g₂ x :=
    hG1contAt.congr_of_eventuallyEq hEqAt
  have hthird :
      thirdDirectionalDerivative g₂ x u = thirdDirectionalDerivative g₁ x u := by
    have hiter : iteratedFDeriv ℝ 3 g₂ x = iteratedFDeriv ℝ 3 g₁ x :=
      (Filter.EventuallyEq.iteratedFDeriv ℝ hEqAt 3).eq_of_nhds
    simpa [thirdDirectionalDerivative_eq_iteratedFDeriv hG2contAt,
      thirdDirectionalDerivative_eq_iteratedFDeriv hG1contAt] using
      congrArg (fun A ↦ A fun _ ↦ u) hiter
  have hhess : hessian g₂ x = hessian g₁ x := by
    simpa [hessian] using (hEqAt.gradient.fderiv_eq (𝕜 := ℝ))
  have hnorm : hessianLocalNorm g₂ x u = hessianLocalNorm g₁ x u := by
    simp [hessianLocalNorm_def, hhess]
  calc
    |thirdDirectionalDerivative g₂ x u| = |thirdDirectionalDerivative g₁ x u| := by
      rw [hthird]
    _ ≤ 2 * (Mf : ℝ) * hessianLocalNorm g₁ x u ^ (3 : ℕ) := h.third_deriv_bound hx u
    _ = 2 * (Mf : ℝ) * hessianLocalNorm g₂ x u ^ (3 : ℕ) := by
      rw [hnorm]

/-- Helper for Theorem 5.3.6: the effective domain `D` is open because the implicit stationary
branch transports the selected minimizer packet to nearby points of `D`. -/
private lemma partialMinimizationObjective_dom_isOpen_of_argmin
    (hΦ : IsSelfConcordantBarrierOnWith QZ ν (Φ ∘ WithLp.ofLp))
    (hy_argmin : ∀ ⦃x : E₁⦄, x ∈ D → y x ∈ argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x))
    (hy_unique : ∀ ⦃x : E₁⦄, x ∈ D → ∀ ⦃y' : E₂⦄,
        y' ∈ argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x) → y' = y x) :
    IsOpen D := by
  have hyy_pos :
      ∀ ⦃x : E₁⦄, x ∈ D → ∀ v : E₂, v ≠ 0 →
        0 < inner ℝ v ((hessian (Φ ∘ Prod.mk x) (y x)) v) := by
    intro x hx v hv
    exact selectedFiberHessianPos_of_barrierArgmin
      (Q := Q) (ν := ν) (Φ := Φ) (y := y) hΦ hy_argmin hy_unique hx v hv
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rcases implicitStationaryBranchPacket_of_mem_dom
      (Q := Q) (ν := ν) (Φ := Φ) (y := y)
      hΦ hy_argmin hy_unique hyy_pos hx with
    ⟨s, ψ, hs_open, hsx, _, _, _, hpacket⟩
  -- The implicit minimizer packet stays on the selected branch near `x`, so nearby points stay
  -- inside the reduced domain.
  refine Filter.mem_of_superset (hs_open.mem_nhds hsx) ?_
  intro u hu
  exact
    (selectedMinimizerTransport_onImplicitBranch
      (Q := Q) (ν := ν) (Φ := Φ) (y := y)
      hΦ hy_argmin hy_unique hpacket u hu).1

/-- Helper for Theorem 5.3.6: convexity of the ambient barrier domain descends to convexity of
the effective domain `D` of the partial minimization objective. -/
private lemma partialMinimizationObjective_dom_convex_of_argmin
    (hΦ : IsSelfConcordantBarrierOnWith QZ ν (Φ ∘ WithLp.ofLp))
    (hy_argmin : ∀ ⦃x : E₁⦄, x ∈ D → y x ∈ argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x)) :
    Convex ℝ D := by
  classical
  have hQ_convex : Convex ℝ Q :=
    ambientDomain_convex_of_barrier (Q := Q) (ν := ν) (Φ := Φ) hΦ
  intro x₁ hx₁ x₂ hx₂ a b ha hb hab
  let z : E₁ := a • x₁ + b • x₂
  let yz : E₂ := a • y x₁ + b • y x₂
  have hx₁_int : (x₁, y x₁) ∈ interior Q :=
    selectedFiberMinimizer_mem_interior_of_dom
      (Q := Q) (ν := ν) (Φ := Φ) (y := y) hΦ hy_argmin hx₁
  have hx₂_int : (x₂, y x₂) ∈ interior Q :=
    selectedFiberMinimizer_mem_interior_of_dom
      (Q := Q) (ν := ν) (Φ := Φ) (y := y) hΦ hy_argmin hx₂
  have hx₁_mem : (x₁, y x₁) ∈ Q := interior_subset hx₁_int
  have hx₂_mem : (x₂, y x₂) ∈ Q := interior_subset hx₂_int
  have hyz_mem : (z, yz) ∈ Q := by
    -- Keep the selected fibers inside `Q` by convexity before testing finiteness at `z`.
    simpa [z, yz, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add] using
      hQ_convex hx₁_mem hx₂_mem ha hb hab
  have htop : partialInfProjection Q (Real.toEReal ∘ Φ) z ≠ ⊤ := by
    intro htop
    have hle :
        partialInfProjection Q (Real.toEReal ∘ Φ) z ≤ (Φ (z, yz) : EReal) := by
      exact sInf_le ⟨(z, yz), ⟨hyz_mem, rfl⟩, rfl⟩
    rw [htop] at hle
    simp at hle
  have hΦ_at_x :
      ContDiffAt ℝ 1 Φ (x₁, y x₁) := by
    have hx₁_memQZ : WithLp.toLp 2 (x₁, y x₁) ∈ QZ := by
      simpa using hx₁_mem
    have hLift_at :
        ContDiffAt ℝ 3 (Φ ∘ WithLp.ofLp) (WithLp.toLp 2 (x₁, y x₁)) :=
      hΦ.toIsStandardSelfConcordantOn.contDiffOn.contDiffAt
        (hΦ.toIsStandardSelfConcordantOn.isOpen_domain.mem_nhds hx₁_memQZ)
    -- Pull the ambient regularity back to the raw product coordinates at the first endpoint.
    simpa [Function.comp] using
      (hLift_at.comp (x₁, y x₁)
        ((((WithLp.prodContinuousLinearEquiv 2 ℝ E₁ E₂).symm :
            (E₁ × E₂) ≃L[ℝ] Z)).contDiff.contDiffAt)).of_le (by norm_num)
  let φTopLift : Z → WithTop ℝ := fun p ↦
    if p ∈ QZ then (partialMinimizationLift Φ p : WithTop ℝ) else ⊤
  have hdomLift : withTopEffectiveDomain φTopLift = QZ := by
    ext p
    constructor
    · intro hp
      change φTopLift p < ⊤ at hp
      by_contra hpQ
      change p.ofLp ∉ Q at hpQ
      simp [φTopLift, partialMinimizationLift, hpQ] at hp
    · intro hp
      change φTopLift p < ⊤
      change p.ofLp ∈ Q at hp
      simp [φTopLift, partialMinimizationLift, hp]
  have hφTopLift_conv :
      ConvexOn ℝ (withTopEffectiveDomain φTopLift) (withTopRealPart φTopLift) := by
    -- The lifted top extension agrees with the ambient objective on the barrier domain.
    rw [hdomLift]
    refine hΦ.toIsStandardSelfConcordantOn.convexOn.congr ?_
    intro p hp
    have hpdom : p ∈ withTopEffectiveDomain φTopLift := by
      simpa [hdomLift] using hp
    change p.ofLp ∈ Q at hp
    rw [withTopRealPart_eq_untop hpdom]
    simp [φTopLift, partialMinimizationLift, hp]
  have hx₁_memQZ : WithLp.toLp 2 (x₁, y x₁) ∈ QZ := by
    simpa using hx₁_mem
  have hφTopLift_eventuallyEq :
      withTopRealPart φTopLift =ᶠ[nhds (WithLp.toLp 2 (x₁, y x₁))]
        partialMinimizationLift Φ := by
    filter_upwards [hΦ.toIsStandardSelfConcordantOn.isOpen_domain.mem_nhds hx₁_memQZ] with p hp
    have hpdom : p ∈ withTopEffectiveDomain φTopLift := by
      simpa [hdomLift] using hp
    change p.ofLp ∈ Q at hp
    rw [withTopRealPart_eq_untop hpdom]
    simp [φTopLift, partialMinimizationLift, hp]
  have hLift_diff_x :
      DifferentiableAt ℝ (partialMinimizationLift Φ) (WithLp.toLp 2 (x₁, y x₁)) := by
    exact (partialMinimizationLift_contDiffAt Φ x₁ (y x₁) hΦ_at_x).differentiableAt
      (by norm_num)
  have hφTopLift_gradAt :
      HasGradientAt (withTopRealPart φTopLift)
        (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 (x₁, y x₁)))
        (WithLp.toLp 2 (x₁, y x₁)) := by
    exact hLift_diff_x.hasGradientAt.congr_of_eventuallyEq hφTopLift_eventuallyEq
  have hx₁_intQZ : WithLp.toLp 2 (x₁, y x₁) ∈ interior QZ := by
    simpa [hΦ.toIsStandardSelfConcordantOn.isOpen_domain.interior_eq] using hx₁_memQZ
  have hφTopLift_sub :
      ∇ (partialMinimizationLift Φ) (WithLp.toLp 2 (x₁, y x₁)) ∈
        subdifferential φTopLift (WithLp.toLp 2 (x₁, y x₁)) :=
    gradient_mem_subdifferential_of_hasGradientAt hφTopLift_conv
      (by simpa [hdomLift] using hx₁_intQZ) hφTopLift_gradAt
  have hslice_diff :
      DifferentiableAt ℝ (Φ ∘ Prod.mk x₁) (y x₁) := by
    simpa [Function.comp] using
      (hΦ_at_x.differentiableAt (by norm_num)).comp (y x₁)
        (hasFDerivAt_prodMk_right x₁ (y x₁)).differentiableAt
  have hslice_zero :
      HasFDerivAt (Φ ∘ Prod.mk x₁) (0 : E₂ →L[ℝ] ℝ) (y x₁) := by
    simpa [selectedFiberGradient_eq_zero_of_barrierArgmin
        (Q := Q) (ν := ν) (Φ := Φ) (y := y) hΦ hy_argmin hx₁] using
      hslice_diff.hasGradientAt.hasFDerivAt
  have hslice :
      HasFDerivAt (Φ ∘ Prod.mk x₁)
        ((fderiv ℝ Φ (x₁, y x₁)).comp (inr ℝ E₁ E₂)) (y x₁) := by
    simpa [Function.comp] using
      ((hΦ_at_x.differentiableAt (by norm_num)).hasFDerivAt.comp (y x₁)
        (hasFDerivAt_prodMk_right x₁ (y x₁)))
  have hslice_eq_zero :
      (fderiv ℝ Φ (x₁, y x₁)).comp (inr ℝ E₁ E₂) = 0 :=
    hslice.unique hslice_zero
  have hgrad_fst :
      WithLp.fstL 2 ℝ E₁ E₂
          (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 (x₁, y x₁))) =
        ∇ (fun u : E₁ ↦ Φ (u, y x₁)) x₁ := by
    exact partialMinimizationXGradient_eq_frozenXGradient Φ x₁ (y x₁) hΦ_at_x
  have hgrad_snd :
      WithLp.sndL 2 ℝ E₁ E₂
          (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 (x₁, y x₁))) = 0 := by
    calc
      WithLp.sndL 2 ℝ E₁ E₂
          (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 (x₁, y x₁)))
          = ∇ (Φ ∘ Prod.mk x₁) (y x₁) := by
              exact partialMinimizationYGradient_eq_frozenYGradient Φ x₁ (y x₁) hΦ_at_x
      _ = 0 :=
        selectedFiberGradient_eq_zero_of_barrierArgmin
          (Q := Q) (ν := ν) (Φ := Φ) (y := y) hΦ hy_argmin hx₁
  let lowerBound : ℝ :=
    Φ (x₁, y x₁) + inner ℝ (∇ (fun u : E₁ ↦ Φ (u, y x₁)) x₁) (z - x₁)
  have hlower :
      ∀ w : E₂, (z, w) ∈ Q → (lowerBound : EReal) ≤ (Φ (z, w) : EReal) := by
    intro w hzw_mem
    have hz_memQZ : WithLp.toLp 2 (z, w) ∈ QZ := by
      simpa using hzw_mem
    have hminorant_withTop :
        φTopLift (WithLp.toLp 2 (z, w)) ≥
          φTopLift (WithLp.toLp 2 (x₁, y x₁)) +
            (inner ℝ (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 (x₁, y x₁)))
              (WithLp.toLp 2 ((z, w) - (x₁, y x₁))) : WithTop ℝ) :=
      (mem_subdifferential_iff.mp hφTopLift_sub).2 (by
        simpa [hdomLift] using hz_memQZ)
    have hφTopLift_z :
        φTopLift (WithLp.toLp 2 (z, w)) = (Φ (z, w) : WithTop ℝ) := by
      change (if (z, w) ∈ Q then (Φ (z, w) : WithTop ℝ) else ⊤) = (Φ (z, w) : WithTop ℝ)
      simp [hzw_mem]
    have hφTopLift_x :
        φTopLift (WithLp.toLp 2 (x₁, y x₁)) = (Φ (x₁, y x₁) : WithTop ℝ) := by
      change
        (if (x₁, y x₁) ∈ Q then (Φ (x₁, y x₁) : WithTop ℝ) else ⊤) =
          (Φ (x₁, y x₁) : WithTop ℝ)
      simp [hx₁_mem]
    have hminorant_withTop' :
        ((Φ (x₁, y x₁) : ℝ) : WithTop ℝ) +
            (inner ℝ (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 (x₁, y x₁)))
              (WithLp.toLp 2 ((z, w) - (x₁, y x₁))) : WithTop ℝ) ≤
          (Φ (z, w) : WithTop ℝ) := by
      simpa [hφTopLift_z, hφTopLift_x, ge_iff_le] using hminorant_withTop
    have hminorant :
        Φ (x₁, y x₁) +
          inner ℝ (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 (x₁, y x₁)))
            (WithLp.toLp 2 ((z, w) - (x₁, y x₁))) ≤ Φ (z, w) := by
      exact_mod_cast hminorant_withTop'
    have hminorant_expanded :
        Φ (x₁, y x₁) +
            (inner ℝ
                (WithLp.fstL 2 ℝ E₁ E₂
                  (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 (x₁, y x₁))))
                (z - x₁) +
              inner ℝ
                (WithLp.sndL 2 ℝ E₁ E₂
                  (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 (x₁, y x₁))))
                (w - y x₁)) ≤
          Φ (z, w) := by
      simpa [WithLp.prod_inner_apply] using hminorant
    have hminorant' :
        lowerBound ≤ Φ (z, w) := by
      calc
        lowerBound
            = Φ (x₁, y x₁) +
                (inner ℝ
                    (WithLp.fstL 2 ℝ E₁ E₂
                      (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 (x₁, y x₁))))
                    (z - x₁) +
                  inner ℝ
                    (WithLp.sndL 2 ℝ E₁ E₂
                      (∇ (partialMinimizationLift Φ) (WithLp.toLp 2 (x₁, y x₁))))
                    (w - y x₁)) := by
                      simp [lowerBound, hgrad_fst, hgrad_snd]
        _ ≤ Φ (z, w) := hminorant_expanded
    exact_mod_cast hminorant'
  have hbot : partialInfProjection Q (Real.toEReal ∘ Φ) z ≠ ⊥ := by
    intro hbot
    have hle :
        (lowerBound : EReal) ≤ partialInfProjection Q (Real.toEReal ∘ Φ) z := by
      rw [partialInfProjection_eq_sInf]
      refine le_csInf ?_ ?_
      · exact ⟨(Φ (z, yz) : EReal), ⟨(z, yz), ⟨hyz_mem, rfl⟩, rfl⟩⟩
      · rintro r ⟨⟨z', w⟩, hw, rfl⟩
        rcases hw with ⟨hzw_mem, hz'⟩
        change z' = z at hz'
        subst z'
        exact hlower w hzw_mem
    rw [hbot] at hle
    simp at hle
  exact ⟨htop, hbot⟩

/-- Helper for Theorem 5.3.6: restricting the feasible set to `Q ∩ Prod.fst ⁻¹' D` does not
change the reduced objective on `D`. -/
private lemma restrictedPartialMinimization_eqOn_dom
    (hy_argmin : ∀ ⦃x : E₁⦄, x ∈ D → y x ∈ argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x)) :
    let Q' : Set (E₁ × E₂) := Q ∩ Prod.fst ⁻¹' D
    let g : E₁ → ℝ := extendedRealRealPart (partialInfProjection Q' (Real.toEReal ∘ Φ))
    Set.EqOn g f D := by
  intro Q' g
  intro x hx
  have hy_argminQ' :
      y x ∈ argmin[(Prod.mk x) ⁻¹' Q'] (Φ ∘ Prod.mk x) := by
    rcases mem_constrainedArgmin_iff.mp (hy_argmin hx) with ⟨hxy_mem, hxy_min⟩
    refine mem_constrainedArgmin_iff.mpr ?_
    refine ⟨⟨hxy_mem, hx⟩, ?_⟩
    intro z hz
    exact hxy_min hz.1
  -- Rewrite both reduced objectives through the same selected fiber minimizer.
  calc
    g x = Φ (x, y x) := by
      exact partialMinimizationObjective_eq_of_mem_argmin Q' Φ hy_argminQ'
    _ = f x := (partialMinimizationObjective_eq_of_mem_argmin Q Φ (hy_argmin hx)).symm

/-- Helper for Theorem 5.3.6: the restricted feasible-set route yields standard
self-concordance of the reduced objective on `D`. -/
private lemma partialMinimizationObjective_isStandardSelfConcordantOn_dom_of_argmin
    (hΦ : IsSelfConcordantBarrierOnWith QZ ν (Φ ∘ WithLp.ofLp))
    (hy_argmin : ∀ ⦃x : E₁⦄, x ∈ D → y x ∈ argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x))
    (hy_unique : ∀ ⦃x : E₁⦄, x ∈ D → ∀ ⦃y' : E₂⦄,
        y' ∈ argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x) → y' = y x) :
    IsStandardSelfConcordantOn D f := by
  classical
  by_cases hD_empty : D = (∅ : Set E₁)
  · refine
      { isOpen_domain := by simpa [hD_empty]
        contDiffOn := by simpa [hD_empty]
        convexOn := ?_
        third_deriv_bound := ?_ }
    · refine ⟨by simpa [hD_empty] using (convex_empty : Convex ℝ (∅ : Set E₁)), ?_⟩
      intro x hx y hy a b ha hb hab
      exact False.elim (by simpa [hD_empty] using hx)
    · intro x hx u
      exact False.elim (by simpa [hD_empty] using hx)
  · let Q' : Set (E₁ × E₂) := Q ∩ Prod.fst ⁻¹' D
    have hQ_convex : Convex ℝ Q :=
      ambientDomain_convex_of_barrier (Q := Q) (ν := ν) (Φ := Φ) hΦ
    have hQ_open : IsOpen Q :=
      ambientDomain_isOpen_of_barrier (Q := Q) (ν := ν) (Φ := Φ) hΦ
    have hD_open : IsOpen D :=
      partialMinimizationObjective_dom_isOpen_of_argmin
        (Q := Q) (ν := ν) (Φ := Φ) (y := y) hΦ hy_argmin hy_unique
    have hD_convex : Convex ℝ D :=
      partialMinimizationObjective_dom_convex_of_argmin
        (Q := Q) (ν := ν) (Φ := Φ) (y := y) hΦ hy_argmin
    have hQ'_open : IsOpen Q' := by
      simpa [Q'] using hQ_open.inter (hD_open.preimage continuous_fst)
    have hQ'_convex : Convex ℝ Q' := by
      intro z₁ hz₁ z₂ hz₂ a b ha hb hab
      exact ⟨hQ_convex hz₁.1 hz₂.1 ha hb hab, hD_convex hz₁.2 hz₂.2 ha hb hab⟩
    have hQ'_nonempty : Q'.Nonempty := by
      rcases Set.nonempty_iff_ne_empty.mpr hD_empty with ⟨x₀, hx₀⟩
      exact ⟨(x₀, y x₀), ⟨(mem_constrainedArgmin_iff.mp (hy_argmin hx₀)).1, hx₀⟩⟩
    have hy_argminQ' :
        ∀ ⦃x : E₁⦄, x ∈ D → y x ∈ argmin[(Prod.mk x) ⁻¹' Q'] (Φ ∘ Prod.mk x) := by
      intro x hx
      rcases mem_constrainedArgmin_iff.mp (hy_argmin hx) with ⟨hxy_mem, hxy_min⟩
      refine mem_constrainedArgmin_iff.mpr ?_
      refine ⟨⟨hxy_mem, hx⟩, ?_⟩
      intro z hz
      exact hxy_min hz.1
    have hy_uniqueQ' :
        ∀ ⦃x : E₁⦄, x ∈ D → ∀ ⦃y' : E₂⦄,
          y' ∈ argmin[(Prod.mk x) ⁻¹' Q'] (Φ ∘ Prod.mk x) → y' = y x := by
      intro x hx y' hy'
      rcases mem_constrainedArgmin_iff.mp hy' with ⟨hy'_mem, hy'_min⟩
      have hy'_argminQ : y' ∈ argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x) := by
        refine mem_constrainedArgmin_iff.mpr ?_
        refine ⟨hy'_mem.1, ?_⟩
        intro z hz
        exact hy'_min ⟨hz, hx⟩
      exact hy_unique hx hy'_argminQ
    have hsource_eq : partialMinimizationSourceDom Q' = D := by
      ext x
      constructor
      · intro hx
        rcases hx.2 with ⟨yy, hyy_mem, _⟩
        exact (by simpa [Q'] using hyy_mem : (x, yy) ∈ Q ∧ x ∈ D).2
      · intro hx
        have hxy_mem : (x, y x) ∈ Q' := by
          exact ⟨(mem_constrainedArgmin_iff.mp (hy_argmin hx)).1, hx⟩
        refine ⟨⟨y x, hxy_mem⟩, y x, hxy_mem, ?_⟩
        simpa [hQ'_open.interior_eq] using hxy_mem
    have hselfQ' :
        IsSelfConcordantOnWith ((WithLp.ofLp : Z → E₁ × E₂) ⁻¹' interior Q') 1
          (Φ ∘ WithLp.ofLp) := by
      -- Route correction: package the existing restricted-feasible-set route instead of
      -- re-entering the old D-local cubic-bound proof inside the final theorem.
      let hselfInt :=
        ambientLift_isStandardSelfConcordantOnInterior_of_barrier
          (Q := Q) (ν := ν) (Φ := Φ) hΦ
      have hsubset :
          ((WithLp.ofLp : Z → E₁ × E₂) ⁻¹' interior Q') ⊆
            ((WithLp.ofLp : Z → E₁ × E₂) ⁻¹' interior Q) := by
        intro z hz
        have hz' : WithLp.ofLp z ∈ Q' := by
          simpa [hQ'_open.interior_eq] using hz
        simpa [hQ_open.interior_eq] using hz'.1
      have hpre_convex :
          Convex ℝ ((WithLp.ofLp : Z → E₁ × E₂) ⁻¹' interior Q') := by
        intro z₁ hz₁ z₂ hz₂ a b ha hb hab
        have hz₁' : WithLp.ofLp z₁ ∈ Q' := by
          simpa [hQ'_open.interior_eq] using hz₁
        have hz₂' : WithLp.ofLp z₂ ∈ Q' := by
          simpa [hQ'_open.interior_eq] using hz₂
        simpa [hQ'_open.interior_eq] using hQ'_convex hz₁' hz₂' ha hb hab
      refine
        { isOpen_domain := by
            simpa [hQ'_open.interior_eq] using
              hQ'_open.preimage
                (((WithLp.prodContinuousLinearEquiv 2 ℝ E₁ E₂ : Z ≃L[ℝ] E₁ × E₂) :
                  Z →L[ℝ] E₁ × E₂).continuous)
          contDiffOn := hselfInt.contDiffOn.mono hsubset
          convexOn := hselfInt.convexOn.subset hsubset hpre_convex
          third_deriv_bound := ?_ }
      intro z hz u
      exact hselfInt.third_deriv_bound (hsubset hz) u
    have hy_mem_interior' :
        ∀ ⦃x : E₁⦄, x ∈ partialMinimizationSourceDom Q' → (x, y x) ∈ interior Q' := by
      intro x hx
      have hxD : x ∈ D := by simpa [hsource_eq] using hx
      have hxy_mem : (x, y x) ∈ Q' := by
        exact ⟨(mem_constrainedArgmin_iff.mp (hy_argmin hxD)).1, hxD⟩
      simpa [hQ'_open.interior_eq] using hxy_mem
    have hy_argmin' :
        ∀ ⦃x : E₁⦄, x ∈ partialMinimizationSourceDom Q' →
          y x ∈ argmin[(Prod.mk x) ⁻¹' Q'] (Φ ∘ Prod.mk x) := by
      intro x hx
      have hxD : x ∈ D := by simpa [hsource_eq] using hx
      exact hy_argminQ' hxD
    have hy_unique' :
        ∀ ⦃x : E₁⦄, x ∈ partialMinimizationSourceDom Q' → ∀ ⦃y' : E₂⦄,
          y' ∈ argmin[(Prod.mk x) ⁻¹' Q'] (Φ ∘ Prod.mk x) → y' = y x := by
      intro x hx y' hy'
      have hxD : x ∈ D := by simpa [hsource_eq] using hx
      exact hy_uniqueQ' hxD hy'
    have hyy_pos' :
        ∀ ⦃x : E₁⦄, x ∈ partialMinimizationSourceDom Q' → ∀ v : E₂, v ≠ 0 →
          0 < inner ℝ v ((hessian (Φ ∘ Prod.mk x) (y x)) v) := by
      intro x hx v hv
      have hxD : x ∈ D := by simpa [hsource_eq] using hx
      exact selectedFiberHessianPos_of_barrierArgmin
        (Q := Q) (ν := ν) (Φ := Φ) (y := y) hΦ hy_argmin hy_unique hxD v hv
    let g : E₁ → ℝ := extendedRealRealPart (partialInfProjection Q' (Real.toEReal ∘ Φ))
    have hstdD' : IsStandardSelfConcordantOn D g := by
      simpa [hsource_eq, g] using
        (partialMinimizationObjective_isSelfConcordantOnWith
          (Q := Q') (Mf := (1 : NNRealˣ)) (Φ := Φ) (y := y)
          hQ'_convex hQ'_nonempty hselfQ' hy_mem_interior' hy_argmin' hy_unique' hyy_pos')
    have hEqOnD : Set.EqOn g f D := by
      simpa [g, Q'] using
        (restrictedPartialMinimization_eqOn_dom
          (Q := Q) (Φ := Φ) (y := y) hy_argmin)
    exact selfConcordantOnWith_congrEqOnLocal hstdD' hEqOnD

/-- Theorem 5.3.6: if `Φ` is a `ν`-self-concordant barrier on `Q ⊆ E₁ × E₂`, and if for every
`x ∈ D`, where `D = dom (partialInfProjection Q (Real.toEReal ∘ Φ))`, the fiber problem
`min_y Φ(x, y)` over `(Prod.mk x) ⁻¹' Q` is attained uniquely at `y x`, then the canonical real
surface of the partial infimal projection is a `ν`-self-concordant barrier on its natural
domain. -/
theorem partialMinimizationObjective_isSelfConcordantBarrierOnWith_of_argmin
    (hΦ : IsSelfConcordantBarrierOnWith QZ ν (Φ ∘ WithLp.ofLp))
    (hy_argmin : ∀ ⦃x : E₁⦄, x ∈ D → y x ∈ argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x))
    (hy_unique : ∀ ⦃x : E₁⦄, x ∈ D → ∀ ⦃y' : E₂⦄,
        y' ∈ argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x) → y' = y x) :
    IsSelfConcordantBarrierOnWith D ν f := by
  by_cases hD_empty : D = (∅ : Set E₁)
  · -- If `D` is empty, both the standard self-concordance and barrier obligations are vacuous.
    refine
      { toIsStandardSelfConcordantOn := ?_
        barrier_parameter_bound := ?_ }
    · refine
        { isOpen_domain := by simpa [hD_empty]
          contDiffOn := by simpa [hD_empty]
          convexOn := ?_
          third_deriv_bound := ?_ }
      · refine ⟨by simpa [hD_empty] using (convex_empty : Convex ℝ (∅ : Set E₁)), ?_⟩
        intro x hx y hy a b ha hb hab
        have : False := by simpa [hD_empty] using hx
        exact this.elim
      · intro x hx u
        have : False := by simpa [hD_empty] using hx
        exact this.elim
    · intro x hx u
      have : False := by simpa [hD_empty] using hx
      exact this.elim
  · refine
      { toIsStandardSelfConcordantOn :=
          partialMinimizationObjective_isStandardSelfConcordantOn_dom_of_argmin
            (Q := Q) (ν := ν) (Φ := Φ) (y := y) hΦ hy_argmin hy_unique
        barrier_parameter_bound := ?_ }
    intro x hx u
    exact reducedObjective_barrierBound_of_mem_dom
      (Q := Q) (ν := ν) (Φ := Φ) (y := y) hΦ hy_argmin hy_unique hx u

end PartialMinimizationBarrier

end
