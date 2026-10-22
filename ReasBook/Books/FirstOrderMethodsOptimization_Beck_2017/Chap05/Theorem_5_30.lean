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
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_8
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_1
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_18
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_14
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_35
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_30
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Definition_5_2
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Proposition_5_2
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Theorem_5_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped Gradient

noncomputable section

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

recall effective_domain
recall is_convex_function
recall infimal_convolution

/- Theorem 5.30 is `source-facing` in the chapter infimal-convolution smoothing calculus. The owner
objects are Chapter 2's `IsProperExtendedRealFunction`, `effective_domain`,
`is_convex_function`, and `infimal_convolution`, together with Chapter 5's smoothness predicate
`is_l_smooth_on`, specialized to `Set.univ`. The theorem is stated directly for the canonical
infimal convolution `f □ ω.toEReal`, viewed as the real-valued map
`x ↦ ((f □ ω.toEReal) x).toReal` under the standing everywhere-finite hypothesis, rather than
through an auxiliary wrapper for the minimizing problem. -/

variable (f : E → EReal) (ω : E → ℝ) (L : NNReal)
variable (hf_proper : IsProperExtendedRealFunction f) (hf_closed : LowerSemicontinuous f)
variable (hf_convex : is_convex_function f)
variable (hω_convex : ConvexOn ℝ Set.univ ω) (hω_smooth : is_l_smooth_on ω Set.univ L)
variable (hreal : ∀ x, ∃ r : ℝ, (f □ ω.toEReal) x = (r : EReal))

include hf_proper hf_closed hf_convex hω_convex hω_smooth hreal

omit f ω L hf_proper hf_closed hf_convex hω_convex hω_smooth hreal in
/-- Helper for Theorem 5.30: adding a finite real constant commutes with the `EReal` infimum. -/
lemma iInf_add_real_eq_ereal (g : E → EReal) (c : ℝ) :
    (⨅ y, g y) + (c : EReal) = ⨅ y, g y + c := by
  -- Pull the finite additive term through the infimum using continuity of `z ↦ z + c`.
  let F : EReal → EReal × EReal := fun z ↦ (z, c)
  have hF : ContinuousAt F (⨅ y, g y) := by
    exact continuousAt_id.prodMk continuousAt_const
  have hAdd : ContinuousAt (fun p : EReal × EReal ↦ p.1 + p.2) (F (⨅ y, g y)) := by
    simpa [F] using
      EReal.continuousAt_add (p := (⨅ y, g y, (c : EReal)))
        (Or.inr (EReal.coe_ne_bot _))
        (Or.inr (EReal.coe_ne_top _))
  have hmono : Monotone (fun z : EReal ↦ z + c) := by
    intro a b hab
    simpa [add_comm] using add_le_add_left hab ((c : ℝ) : EReal)
  simpa [F] using
    Monotone.map_ciInf_of_continuousAt (ContinuousAt.comp hAdd hF) hmono

omit f ω L hf_proper hf_closed hf_convex hω_convex hω_smooth hreal in
/-- Helper for Theorem 5.30: a convex `0`-smooth real-valued function on `E` is affine. -/
lemma convexOn_eq_affine_of_is_l_smooth_on_zero
    {ω : E → ℝ}
    (hω_convex : ConvexOn ℝ Set.univ ω)
    (hω_smooth : is_l_smooth_on ω Set.univ 0) :
    ∃ b : E →L[ℝ] ℝ, ∀ x, ω x = b x + ω 0 := by
  -- Zero smoothness forces a constant gradient field, and convexity turns that into an affine law.
  have hω_diff : Differentiable ℝ ω := fun x ↦ hω_smooth.1 x (by simp)
  have hgrad_eq : ∀ x y : E, ∇ ω x = ∇ ω y := by
    have hnorm := (is_l_smooth_on_iff_forall_norm_sub_le.mp hω_smooth).2
    intro x y
    have hxy : ‖∇ ω x - ∇ ω y‖ = 0 := by
      refine le_antisymm ?_ (norm_nonneg _)
      simpa using hnorm x (by simp) y (by simp)
    exact sub_eq_zero.mp (norm_eq_zero.mp hxy)
  have hsupport : ∀ x y : E, ω y ≥ ω x + inner ℝ (∇ ω x) (y - x) := by
    intro x y
    -- Identify the unique Euclidean subgradient with the gradient.
    have hsingleton :
        euclideanSubdifferentialAt ω x = {∇ ω x} :=
      euclideanSubdifferentialAt_eq_singleton_gradient_of_differentiableAt
        hω_convex (hω_diff x)
    have hsub :
        ∇ ω x ∈ euclideanSubdifferentialAt ω x := by
      rw [hsingleton]
      simp
    have hsub' :
        InnerProductSpace.toDualMap ℝ E (∇ ω x) ∈ subdifferentialAt ω x :=
      mem_euclideanSubdifferentialAt_iff.mp hsub
    rw [subdifferentialAt, mem_strongDualSubdifferential, mem_subdifferential,
      is_subgradient_at_coe_iff] at hsub'
    simpa [InnerProductSpace.toDual_apply_eq_toDualMap_apply] using hsub' y
  have haffine : ∀ x y : E, ω y = ω x + inner ℝ (∇ ω 0) (y - x) := by
    intro x y
    have hxy : ω y ≥ ω x + inner ℝ (∇ ω 0) (y - x) := by
      simpa [hgrad_eq x 0] using hsupport x y
    have hyx : ω x ≥ ω y + inner ℝ (∇ ω 0) (x - y) := by
      simpa [hgrad_eq y 0] using hsupport y x
    refine le_antisymm ?_ hxy
    have hyx' : ω y ≤ ω x + inner ℝ (∇ ω 0) (y - x) := by
      have hyx'' : ω x ≥ ω y - inner ℝ (∇ ω 0) (y - x) := by
        simpa [sub_eq_add_neg, inner_add_right, inner_neg_right, add_assoc, add_left_comm,
          add_comm] using hyx
      linarith
    exact hyx'
  refine ⟨InnerProductSpace.toDual ℝ E (∇ ω 0), ?_⟩
  intro x
  -- Specialize the affine formula at the base point `0`.
  simpa [add_comm] using haffine 0 x

omit f ω L hf_proper hf_closed hf_convex hω_convex hω_smooth hreal in
/-- Helper for Theorem 5.30: a convex differentiable real-valued function lies above each of its
tangent planes. -/
lemma convexGradientFirstOrderLowerBoundLocal
    {φ : E → ℝ}
    (hφ_convex : ConvexOn ℝ Set.univ φ)
    (hφ_diff : Differentiable ℝ φ) :
    ∀ x y : E, φ y ≥ φ x + inner ℝ (∇ φ x) (y - x) := by
  intro x y
  -- Identify the unique Euclidean subgradient with the ambient gradient and unpack it.
  have hsingleton :
      euclideanSubdifferentialAt φ x = {∇ φ x} :=
    euclideanSubdifferentialAt_eq_singleton_gradient_of_differentiableAt
      hφ_convex (hφ_diff x)
  have hsub :
      ∇ φ x ∈ euclideanSubdifferentialAt φ x := by
    rw [hsingleton]
    simp
  have hsub' :
      InnerProductSpace.toDualMap ℝ E (∇ φ x) ∈ subdifferentialAt φ x :=
    mem_euclideanSubdifferentialAt_iff.mp hsub
  rw [subdifferentialAt, mem_strongDualSubdifferential, mem_subdifferential,
    is_subgradient_at_coe_iff] at hsub'
  simpa [InnerProductSpace.toDual_apply_eq_toDualMap_apply] using hsub' y

omit L hf_proper hf_closed hf_convex hω_convex hω_smooth in
/-- Helper for Theorem 5.30: if the smoothing kernel is affine, then the real-valued infimal
convolution is affine with the same linear part. -/
lemma infimalConvolution_toReal_eq_affine_of_kernel_eq_affine
    (b : E →L[ℝ] ℝ)
    (hω_affine : ∀ x, ω x = b x + ω 0) :
    ∀ x, ((f □ ω.toEReal) x).toReal = b x + ((f □ ω.toEReal) 0).toReal := by
  intro x
  let φ : E → EReal := fun y ↦ f y + (((-b y + ω 0 : ℝ) : EReal))
  have hx :
      (f □ ω.toEReal) x = ((b x : ℝ) : EReal) + ⨅ y, φ y := by
    -- Rewrite the kernel by its affine normal form, then pull the finite `b x` term past `⨅`.
    rw [infimal_convolution_apply]
    calc
      ⨅ y, f y + ω.toEReal (x - y)
          = ⨅ y, f y + ((((b (x - y) + ω 0 : ℝ)) : EReal)) := by
              refine iInf_congr (fun y ↦ ?_)
              rw [Function.toEReal_apply, hω_affine (x - y)]
      _ = ⨅ y, (((b x : ℝ) : EReal) + φ y) := by
            refine iInf_congr (fun y ↦ ?_)
            have hbxy : b (x - y) + ω 0 = b x + (-b y + ω 0) := by
              simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
            rw [hbxy]
            simp [φ, add_assoc, add_left_comm, add_comm]
      _ = ⨅ y, φ y + (b x : ℝ) := by
            refine iInf_congr (fun y ↦ ?_)
            rw [add_comm]
      _ = (⨅ y, φ y) + (b x : EReal) := by
            rw [← iInf_add_real_eq_ereal (g := φ) (c := b x)]
      _ = ((b x : ℝ) : EReal) + ⨅ y, φ y := by
            rw [add_comm]
  have hzero :
      (f □ ω.toEReal) 0 = ⨅ y, φ y := by
    -- The same affine rewrite at the origin identifies the shifted infimum.
    rw [infimal_convolution_apply]
    refine iInf_congr (fun y ↦ ?_)
    have hb0y : b (0 - y) + ω 0 = -b y + ω 0 := by
      simp [map_neg, sub_eq_add_neg]
    rw [Function.toEReal_apply, hω_affine (0 - y), hb0y]
  -- Convert the affine `EReal` identity back to the real-valued target using `hreal`.
  calc
    ((f □ ω.toEReal) x).toReal = (((b x : ℝ) : EReal) + (f □ ω.toEReal) 0).toReal := by
      rw [hx, hzero]
    _ = b x + ((f □ ω.toEReal) 0).toReal := by
      rcases hreal 0 with ⟨r0, hr0⟩
      have hsum :
          (((b x : ℝ) : EReal) + (r0 : EReal)) = (((b x + r0 : ℝ) : EReal)) := by
        simp
      rw [hr0, hsum]
      rfl

/-
The new slice-kernel helpers below intentionally omit irrelevant standing hypotheses so their
applications stay stable while the positive-`L` branch is still under construction.
-/
omit L hf_proper hf_closed hf_convex hω_smooth hreal in
/-- Helper for Theorem 5.30: affine precomposition preserves convexity of the reflected
slice kernel `v ↦ ω.toEReal (x - v)`. -/
lemma sliceKernel_isConvexFunction
    (x : E) :
    is_convex_function (fun v : E ↦ ω.toEReal (x - v)) := by
  -- Route correction: use affine precomposition of `ω.toEReal` instead of the old
  -- reflected-kernel transport chain.
  have hω_convex' : is_convex_function ω.toEReal :=
    Function.toEReal_isConvexFunction hω_convex
  simpa [sub_eq_add_neg, add_comm] using
    is_convex_function_precompose_linearMap_add
      hω_convex'
      (-(LinearMap.id : E →ₗ[ℝ] E))
      x

omit hf_proper hf_closed hf_convex hω_convex hreal in
/-- Helper for Theorem 5.30: the reflected slice kernel has gradient `-∇ ω (x - u)` at `u`. -/
lemma hasGradientAt_sliceKernel
    (x u : E) :
    HasGradientAt (fun v : E ↦ ω (x - v)) (-∇ ω (x - u)) u := by
  -- Differentiate the translated reflection by composing `ω` with `v ↦ x - v`.
  have hω_grad : HasGradientAt ω (∇ ω (x - u)) (x - u) :=
    (hω_smooth.1 (x - u) (by simp)).hasGradientAt
  have hreflect :
      HasFDerivAt (fun v : E ↦ x - v) (-(ContinuousLinearMap.id ℝ E)) u := by
    simpa using (hasFDerivAt_id u).const_sub x
  have hcomp :
      HasFDerivAt (fun v : E ↦ ω (x - v))
        ((InnerProductSpace.toDual ℝ E (∇ ω (x - u))).comp (-(ContinuousLinearMap.id ℝ E))) u :=
    hω_grad.hasFDerivAt.comp u hreflect
  have hlin :
      (InnerProductSpace.toDual ℝ E (∇ ω (x - u))).comp (-(ContinuousLinearMap.id ℝ E)) =
        InnerProductSpace.toDual ℝ E (-∇ ω (x - u)) := by
    ext v
    simp [InnerProductSpace.toDual_apply_eq_toDualMap_apply]
  rw [hlin] at hcomp
  simpa using hcomp.hasGradientAt

omit L hf_proper hf_closed hf_convex hω_convex hω_smooth hreal in
/-- Helper for Theorem 5.30: an exact minimizer realizes the infimal convolution value. -/
lemma sliceMinimizer_value_eq_infimalConvolution
    (x u : E)
    (hu : IsMinOn (fun v : E ↦ f v + ω.toEReal (x - v)) Set.univ u) :
    f u + ω.toEReal (x - u) = (f □ ω.toEReal) x := by
  -- Unfold the infimum and use the exact minimizing property in both directions.
  rw [isMinOn_iff] at hu
  rw [infimal_convolution_apply]
  refine le_antisymm ?_ ?_
  · exact le_iInf fun v ↦ hu v (by simp)
  · exact iInf_le _ u

omit hf_closed in
/-- Helper for Theorem 5.30: a minimizer of the slice problem yields the owner subgradient
`toDual (∇ ω (x - u))` of `f` at `u`. -/
lemma gradientSub_mem_subdifferential_of_isMinOn_slice
    (x u : E)
    (hu : IsMinOn (fun v : E ↦ f v + ω.toEReal (x - v)) Set.univ u) :
    (InnerProductSpace.toDual ℝ E (∇ ω (x - u)) : Module.Dual ℝ E) ∈ subdifferential f u := by
  -- Route correction: apply the Chapter 3 stationarity theorem directly to the slice objective
  -- instead of splitting a reflected-kernel strong-dual sum.
  have hvalue :
      f u + ω.toEReal (x - u) = (f □ ω.toEReal) x :=
    sliceMinimizer_value_eq_infimalConvolution
      (f := f) (ω := ω) (x := x) (u := u) hu
  have hu_dom : u ∈ effective_domain f := by
    rcases hreal x with ⟨r, hr⟩
    have hfinite_obj : f u + ω.toEReal (x - u) < ⊤ := by
      rw [hvalue, hr]
      exact EReal.coe_lt_top r
    refine mem_effective_domain.mpr ?_
    by_contra hu_top
    have hfu_top : f u = ⊤ := le_antisymm le_top (not_lt.mp hu_top)
    have htop_obj : f u + ω.toEReal (x - u) = ⊤ := by
      simp [hfu_top]
    exact (ne_of_lt hfinite_obj) htop_obj
  have hdom :
      effective_domain f ⊆ interior (finite_domain (fun v : E ↦ ω.toEReal (x - v))) := by
    intro v hv
    simp [finite_domain, effective_domain, Function.toEReal]
  have hdiff_slice : is_differentiable_at (fun v : E ↦ ω.toEReal (x - v)) u := by
    refine ⟨?_, ?_⟩
    · simp [finite_domain, effective_domain, Function.toEReal]
    · simpa [Function.toEReal] using
        (hasGradientAt_sliceKernel
          (ω := ω) (L := L) (hω_smooth := hω_smooth) (x := x) (u := u)).differentiableAt
  have hstat :=
    let hu_comm :
        IsMinOn (fun v : E ↦ ω.toEReal (x - v) + f v) Set.univ u := by
      rw [isMinOn_iff] at hu ⊢
      intro v hv
      simpa [add_comm] using hu v hv
    (isMinOn_univ_iff_is_stationary_point
      (f := fun v : E ↦ ω.toEReal (x - v))
      (g := f)
      (xStar := u)
      (hfproper := Function.toEReal_isProper (fun v : E ↦ ω (x - v)))
      (hgproper := hf_proper)
      (hgconvex := hf_convex)
      (hdom := hdom)
      (hxStar := hu_dom)
      (hdiff := hdiff_slice)
      (hfconvex := sliceKernel_isConvexFunction
        (ω := ω) (hω_convex := hω_convex) (x := x))).1 hu_comm
  rw [is_stationary_point_iff] at hstat
  have hgrad_slice :
      ∇ (fun v : E ↦ ((fun w : E ↦ ω.toEReal (x - w)) v).toReal) u =
        -∇ ω (x - u) := by
    simpa [Function.toEReal] using
      (hasGradientAt_sliceKernel
        (ω := ω) (L := L) (hω_smooth := hω_smooth) (x := x) (u := u)).gradient
  have hdual_slice :
      (-InnerProductSpace.toDual ℝ E
          (∇ (fun v : E ↦ ((fun w : E ↦ ω.toEReal (x - w)) v).toReal) u) :
          Module.Dual ℝ E) =
        InnerProductSpace.toDual ℝ E (∇ ω (x - u)) := by
    rw [hgrad_slice]
    ext v
    simp [InnerProductSpace.toDual_apply_eq_toDualMap_apply]
  convert hstat.2 using 1
  exact hdual_slice.symm

omit L hf_proper hf_closed hω_smooth in
/-- Helper for Theorem 5.30: the real-valued infimal convolution is convex once its values are
known to be finite everywhere. -/
lemma convexOn_infimalConvolution_toReal :
    ConvexOn ℝ Set.univ (fun y ↦ ((f □ ω.toEReal) y).toReal) := by
  have hconvex_infimal : is_convex_function (f □ ω.toEReal) := by
    simpa [Function.toEReal] using
      infimal_convolution_is_convex f ω hf_convex hω_convex
  -- The everywhere-finite hypothesis lets the Chapter 2 `toReal` bridge apply globally.
  have hdom_univ : effective_domain (f □ ω.toEReal) = Set.univ := by
    ext y
    rcases hreal y with ⟨r, hr⟩
    simp [effective_domain, hr]
  simpa [hdom_univ] using
    convexOn_toReal_of_is_convex_function hconvex_infimal <| by
      intro y hy
      rcases hreal y with ⟨r, hr⟩
      simp [hr]

omit hf_closed in
/-- Helper for Theorem 5.30: an exact minimizer of the defining slice problem produces the
Euclidean subgradient `∇ ω (x - u)` of the real-valued infimal convolution at `x`. -/
lemma gradientSub_mem_euclideanSubdifferentialAt_infimalConvolution_toReal_of_isMinOn
    (x u : E)
    (hu : IsMinOn (fun v : E ↦ f v + ω.toEReal (x - v)) Set.univ u) :
    ∇ ω (x - u) ∈ euclideanSubdifferentialAt (fun y ↦ ((f □ ω.toEReal) y).toReal) x := by
  -- Combine the slice subgradient of `f` with the tangent-plane bound for `ω`, and only then
  -- take the infimum over the free comparison point `v`.
  rw [mem_euclideanSubdifferentialAt_iff, subdifferentialAt, mem_strongDualSubdifferential,
    mem_subdifferential, is_subgradient_at_coe_iff]
  intro y
  let g : E := ∇ ω (x - u)
  have hsub :
      (InnerProductSpace.toDual ℝ E g : Module.Dual ℝ E) ∈ subdifferential f u :=
    gradientSub_mem_subdifferential_of_isMinOn_slice
      (f := f) (ω := ω) (L := L) (hf_proper := hf_proper) (hf_convex := hf_convex)
      (hω_convex := hω_convex) (hω_smooth := hω_smooth) (hreal := hreal) (x := x) (u := u) hu
  have hvalue :
      f u + ω.toEReal (x - u) = (f □ ω.toEReal) x :=
    sliceMinimizer_value_eq_infimalConvolution
      (f := f) (ω := ω) (x := x) (u := u) hu
  have hvalue_inf :
      (⨅ z : E, f z + ω.toEReal (x - z)) = f u + ω.toEReal (x - u) := by
    simpa [infimal_convolution_apply] using hvalue.symm
  rw [mem_subdifferential, is_subgradient_at_iff_forall_mem_effective_domain] at hsub
  have hω_diff : Differentiable ℝ ω := fun z ↦ hω_smooth.1 z (by simp)
  have hEReal :
      (f □ ω.toEReal) x + ((inner ℝ g (y - x) : ℝ) : EReal) ≤ (f □ ω.toEReal) y := by
    rw [infimal_convolution_apply]
    refine le_iInf ?_
    intro v
    by_cases hv : v ∈ effective_domain f
    · have hsub_v :
          f u + ((inner ℝ g (v - u) : ℝ) : EReal) ≤ f v := by
        simpa [ge_iff_le, InnerProductSpace.toDual_apply_eq_toDualMap_apply] using hsub.2 v hv
      have hω_v_real :
          ω (y - v) ≥ ω (x - u) + inner ℝ g ((y - v) - (x - u)) :=
        convexGradientFirstOrderLowerBoundLocal hω_convex hω_diff (x - u) (y - v)
      have hω_v_coe :
          (((ω (x - u) + inner ℝ g ((y - v) - (x - u)) : ℝ)) : EReal) ≤
            (ω (y - v) : EReal) :=
        EReal.coe_le_coe hω_v_real
      have hω_v :
          ω.toEReal (x - u) + ((inner ℝ g ((y - v) - (x - u)) : ℝ) : EReal) ≤
            ω.toEReal (y - v) := by
        simpa [Function.toEReal, EReal.coe_add] using hω_v_coe
      have hadd :
          (f u + ((inner ℝ g (v - u) : ℝ) : EReal)) +
              (ω.toEReal (x - u) + ((inner ℝ g ((y - v) - (x - u)) : ℝ) : EReal)) ≤
            f v + ω.toEReal (y - v) :=
        add_le_add hsub_v hω_v
      have hpair :
          inner ℝ g (v - u) + inner ℝ g ((y - v) - (x - u)) =
            inner ℝ g (y - x) := by
        calc
          inner ℝ g (v - u) + inner ℝ g ((y - v) - (x - u)) =
              inner ℝ g ((v - u) + ((y - v) - (x - u))) := by
                rw [← inner_add_right]
          _ = inner ℝ g (y - x) := by
                congr 1
                abel
      have hslice :
          (⨅ z : E, f z + ω.toEReal (x - z)) + ((inner ℝ g (y - x) : ℝ) : EReal) ≤
            f v + ω.toEReal (y - v) := by
        have hpairE :
            ((inner ℝ g (y - x) : ℝ) : EReal) =
              ((inner ℝ g (v - u) : ℝ) : EReal) +
                ((inner ℝ g ((y - v) - (x - u)) : ℝ) : EReal) := by
          have hpair' := congrArg (fun t : ℝ ↦ (t : EReal)) hpair.symm
          simpa [EReal.coe_add] using hpair'
        calc
          (⨅ z : E, f z + ω.toEReal (x - z)) + ((inner ℝ g (y - x) : ℝ) : EReal) =
              f u + ω.toEReal (x - u) + ((inner ℝ g (y - x) : ℝ) : EReal) := by
                rw [hvalue_inf]
          _ = f u + ω.toEReal (x - u) +
                (((inner ℝ g (v - u) : ℝ) : EReal) +
                  ((inner ℝ g ((y - v) - (x - u)) : ℝ) : EReal)) := by
                rw [hpairE]
          _ = f u +
                ((((inner ℝ g (v - u) : ℝ) : EReal) +
                  (ω.toEReal (x - u) +
                    ((inner ℝ g ((y - v) - (x - u)) : ℝ) : EReal)))) := by
                rw [add_assoc,
                  add_left_comm
                    (ω.toEReal (x - u))
                    (((inner ℝ g (v - u) : ℝ) : EReal))
                    (((inner ℝ g ((y - v) - (x - u)) : ℝ) : EReal)),
                  ← add_assoc]
          _ = (f u + ((inner ℝ g (v - u) : ℝ) : EReal)) +
                (ω.toEReal (x - u) + ((inner ℝ g ((y - v) - (x - u)) : ℝ) : EReal)) := by
                rw [← add_assoc]
          _ ≤ f v + ω.toEReal (y - v) := hadd
      simpa using hslice
    · have hv_top : f v = ⊤ := le_antisymm le_top (not_lt.mp hv)
      have htop :
          (f □ ω.toEReal) x + ((inner ℝ g (y - x) : ℝ) : EReal) ≤ ⊤ := le_top
      simpa [hv_top] using htop
  rcases hreal x with ⟨rx, hrx⟩
  rcases hreal y with ⟨ry, hry⟩
  rw [hrx, hry] at hEReal
  have hreal_support :
      rx + inner ℝ g (y - x) ≤ ry := by
    exact EReal.coe_le_coe_iff.mp (by simpa [EReal.coe_add] using hEReal)
  simpa [g, ge_iff_le, hrx, hry, InnerProductSpace.toDual_apply_eq_toDualMap_apply] using
    hreal_support

omit L hf_proper hf_closed hf_convex hω_convex hω_smooth in
/-- Helper for Theorem 5.30: every positive error budget admits an `ε`-slice witness for the
defining infimal convolution at `x`. -/
lemma exists_epsSlice_lt_infimalConvolution
    (x : E) {ε : ℝ} (hε : 0 < ε) :
    ∃ u : E, f u + ω.toEReal (x - u) <
      ((((f □ ω.toEReal) x).toReal + ε : ℝ) : EReal) := by
  rcases hreal x with ⟨rx, hrx⟩
  have hx_lt :
      (f □ ω.toEReal) x <
        ((((f □ ω.toEReal) x).toReal + ε : ℝ) : EReal) := by
    rw [hrx]
    exact EReal.coe_lt_coe_iff.mpr (by simpa using hε)
  have hx_lt' :
      sInf (Set.range
          (fun y : E ↦
            (fun p : E × E ↦ f p.2 + ω.toEReal (p.1 - p.2)) (x, y))) <
        ((((f □ ω.toEReal) x).toReal + ε : ℝ) : EReal) := by
    simpa [infimal_convolution_apply] using hx_lt
  obtain ⟨u, hu⟩ :=
    existsFiberLtOfSInfRangeLt
      (f := fun p : E × E ↦ f p.2 + ω.toEReal (p.1 - p.2))
      (x := x) hx_lt'
  exact ⟨u, by simpa using hu⟩

omit hf_proper hf_closed hf_convex in
/-- Helper for Theorem 5.30: an `ε`-slice witness yields the one-sided quadratic upper model for
the real-valued infimal convolution. -/
lemma epsSlice_quadraticUpperModel_infimalConvolution_toReal
    (x uε : E) {ε : ℝ} (hε : 0 < ε)
    (huε : f uε + ω.toEReal (x - uε) <
      ((((f □ ω.toEReal) x).toReal + ε : ℝ) : EReal)) :
    ∀ y : E,
      ((f □ ω.toEReal) y).toReal ≤
        ((f □ ω.toEReal) x).toReal + ε +
          inner ℝ (∇ ω (x - uε)) (y - x) +
            ((L : ℝ) / 2) * ‖x - y‖ ^ (2 : ℕ) := by
  let hω_diff : Differentiable ℝ ω := fun z ↦ hω_smooth.1 z (by simp)
  have hω_quad : quadratic_upper_model ω L :=
    (convex_l_smooth_iff_quadratic_upper_model
      (E := E) hω_convex hω_diff).mp hω_smooth
  intro y
  have h_eval : (f □ ω.toEReal) y ≤ f uε + ω.toEReal (y - uε) := by
    rw [infimal_convolution_apply]
    exact iInf_le _ uε
  have hshift : (y - uε) - (x - uε) = y - x := by
    abel
  have hnorm : (x - uε) - (y - uε) = x - y := by
    abel
  have hω_upper_real :
      ω (y - uε) ≤
        ω (x - uε) +
          inner ℝ (∇ ω (x - uε)) (y - x) +
            ((L : ℝ) / 2) * ‖x - y‖ ^ (2 : ℕ) := by
    simpa [hshift, hnorm] using
      quadratic_upper_model.apply hω_quad (x - uε) (y - uε)
  let c : ℝ :=
    inner ℝ (∇ ω (x - uε)) (y - x) +
      ((L : ℝ) / 2) * ‖x - y‖ ^ (2 : ℕ)
  have hω_upper :
      ω.toEReal (y - uε) ≤ ω.toEReal (x - uε) + (c : EReal) := by
    simpa [Function.toEReal, c, EReal.coe_add, add_assoc] using EReal.coe_le_coe hω_upper_real
  have hstep1 :
      f uε + ω.toEReal (y - uε) ≤
        (f uε + ω.toEReal (x - uε)) + (c : EReal) := by
    simpa [add_assoc, add_left_comm, add_comm] using add_le_add_left hω_upper (f uε)
  have hstep2 :
      (f uε + ω.toEReal (x - uε)) + (c : EReal) ≤
        ((((f □ ω.toEReal) x).toReal + ε : ℝ) : EReal) + (c : EReal) := by
    simpa [add_assoc, add_left_comm, add_comm] using add_le_add_right (le_of_lt huε) (c : EReal)
  have hboundE :
      (f □ ω.toEReal) y ≤
        ((((f □ ω.toEReal) x).toReal + ε : ℝ) : EReal) + (c : EReal) := by
    exact le_trans h_eval (le_trans hstep1 hstep2)
  rcases hreal y with ⟨ry, hry⟩
  exact EReal.coe_le_coe_iff.mp (by
    simpa [hry, c, EReal.coe_add, add_assoc, add_left_comm, add_comm] using hboundE)

omit hf_proper hf_closed hf_convex in
/-- Helper for Theorem 5.30: comparing an exact Euclidean subgradient with the `ε`-slice upper
model yields a test-direction error bound. -/
lemma subgradient_testDirection_le_epsSliceError
    {x p uε d : E} {ε : ℝ}
    (hp :
      p ∈ euclideanSubdifferentialAt
        (fun y ↦ ((f □ ω.toEReal) y).toReal) x)
    (hε : 0 < ε)
    (huε : f uε + ω.toEReal (x - uε) <
      ((((f □ ω.toEReal) x).toReal + ε : ℝ) : EReal)) :
    inner ℝ (p - ∇ ω (x - uε)) d ≤ ε + ((L : ℝ) / 2) * ‖d‖ ^ (2 : ℕ) := by
  have hp_support := hp
  rw [mem_euclideanSubdifferentialAt_iff, subdifferentialAt, mem_strongDualSubdifferential,
    mem_subdifferential, is_subgradient_at_coe_iff] at hp_support
  -- Evaluate the exact support inequality at the displaced point `x + d`.
  have hsupport :
      ((f □ ω.toEReal) x).toReal + inner ℝ p d ≤
        ((f □ ω.toEReal) (x + d)).toReal := by
    simpa [InnerProductSpace.toDual_apply_eq_toDualMap_apply, sub_eq_add_neg, add_assoc,
      add_left_comm, add_comm] using hp_support (x + d)
  -- Compare it with the already proved `ε`-slice quadratic upper model at the same point.
  have hupper :=
    epsSlice_quadraticUpperModel_infimalConvolution_toReal
      (f := f) (ω := ω) (L := L) (hω_convex := hω_convex) (hω_smooth := hω_smooth)
      (hreal := hreal) (x := x) (uε := uε) hε huε (x + d)
  have hshift : (x + d) - x = d := by abel
  have hnorm : x - (x + d) = -d := by abel
  -- Subtract the common value `((f □ ω.toEReal) x).toReal` and collect the remaining terms.
  have hmain :
      ((f □ ω.toEReal) x).toReal + inner ℝ p d ≤
        ((f □ ω.toEReal) x).toReal + ε +
          inner ℝ (∇ ω (x - uε)) d +
            ((L : ℝ) / 2) * ‖d‖ ^ (2 : ℕ) := by
    simpa [hshift, hnorm, norm_neg] using le_trans hsupport hupper
  have hsplit :
      inner ℝ p d =
        inner ℝ (p - ∇ ω (x - uε)) d + inner ℝ (∇ ω (x - uε)) d := by
    calc
      inner ℝ p d = inner ℝ ((p - ∇ ω (x - uε)) + ∇ ω (x - uε)) d := by
        congr 1
        abel
      _ = inner ℝ (p - ∇ ω (x - uε)) d + inner ℝ (∇ ω (x - uε)) d := by
        rw [inner_add_left]
  rw [hsplit] at hmain
  linarith

omit hf_proper hf_closed hf_convex in
/-- Helper for Theorem 5.30: every exact Euclidean subgradient at `x` lies within the canonical
`O(√ε)` distance of an `ε`-slice gradient. -/
lemma norm_sub_sq_le_two_mul_L_eps_of_subgradient_and_epsSlice
    (hL_pos : 0 < L)
    {x p uε : E} {ε : ℝ}
    (hp :
      p ∈ euclideanSubdifferentialAt
        (fun y ↦ ((f □ ω.toEReal) y).toReal) x)
    (hε : 0 < ε)
    (huε : f uε + ω.toEReal (x - uε) <
      ((((f □ ω.toEReal) x).toReal + ε : ℝ) : EReal)) :
    ‖p - ∇ ω (x - uε)‖ ^ (2 : ℕ) ≤ 2 * (L : ℝ) * ε := by
  have hLreal : 0 < (L : ℝ) := by
    exact_mod_cast hL_pos
  have hLinv_nonneg : 0 ≤ 1 / (L : ℝ) := by
    positivity
  let Δ : E := p - ∇ ω (x - uε)
  -- Route correction: first compare the exact subgradient with the `ε`-slice model for an
  -- arbitrary direction, and only then specialize to the normalized test direction.
  have htest :=
    subgradient_testDirection_le_epsSliceError
      (f := f) (ω := ω) (L := L) (hω_convex := hω_convex) (hω_smooth := hω_smooth)
      (hreal := hreal) (x := x) (p := p) (uε := uε) (d := (1 / (L : ℝ)) • Δ) hp hε huε
  have hinner :
      inner ℝ Δ ((1 / (L : ℝ)) • Δ) = (1 / (L : ℝ)) * ‖Δ‖ ^ (2 : ℕ) := by
    rw [inner_smul_right, real_inner_self_eq_norm_sq]
  have hquad :
      ((L : ℝ) / 2) * ‖(1 / (L : ℝ)) • Δ‖ ^ (2 : ℕ) =
        (1 / (2 * (L : ℝ))) * ‖Δ‖ ^ (2 : ℕ) := by
    rw [norm_smul, Real.norm_of_nonneg hLinv_nonneg, pow_two]
    field_simp [hLreal.ne']
  rw [hinner, hquad] at htest
  have hscaled_raw :
      (2 * (L : ℝ)) * ((1 / (L : ℝ)) * ‖Δ‖ ^ (2 : ℕ)) ≤
        (2 * (L : ℝ)) * (ε + (1 / (2 * (L : ℝ))) * ‖Δ‖ ^ (2 : ℕ)) := by
    exact mul_le_mul_of_nonneg_left htest (by positivity)
  have hscaled :
      2 * ‖Δ‖ ^ (2 : ℕ) ≤ 2 * (L : ℝ) * ε + ‖Δ‖ ^ (2 : ℕ) := by
    have hleft :
        (2 * (L : ℝ)) * ((1 / (L : ℝ)) * ‖Δ‖ ^ (2 : ℕ)) = 2 * ‖Δ‖ ^ (2 : ℕ) := by
      field_simp [hLreal.ne']
    have hright :
        (2 * (L : ℝ)) * (ε + (1 / (2 * (L : ℝ))) * ‖Δ‖ ^ (2 : ℕ)) =
          2 * (L : ℝ) * ε + ‖Δ‖ ^ (2 : ℕ) := by
      field_simp [hLreal.ne']
    calc
      2 * ‖Δ‖ ^ (2 : ℕ) = (2 * (L : ℝ)) * ((1 / (L : ℝ)) * ‖Δ‖ ^ (2 : ℕ)) := hleft.symm
      _ ≤ (2 * (L : ℝ)) * (ε + (1 / (2 * (L : ℝ))) * ‖Δ‖ ^ (2 : ℕ)) := hscaled_raw
      _ = 2 * (L : ℝ) * ε + ‖Δ‖ ^ (2 : ℕ) := hright
  -- The normalized step turns the directional comparison into the exact `2 L ε` proximity bound.
  nlinarith [hscaled]

omit hf_proper hf_closed hf_convex in
/-- Helper for Theorem 5.30: two exact Euclidean subgradients at the same point are simultaneously
close to the same `ε`-slice gradient, hence close to each other. -/
lemma norm_sub_sq_le_eight_mul_L_eps_of_twoSubgradients_and_epsSlice
    (hL_pos : 0 < L)
    {x p q uε : E} {ε : ℝ}
    (hp :
      p ∈ euclideanSubdifferentialAt
        (fun y ↦ ((f □ ω.toEReal) y).toReal) x)
    (hq :
      q ∈ euclideanSubdifferentialAt
        (fun y ↦ ((f □ ω.toEReal) y).toReal) x)
    (hε : 0 < ε)
    (huε : f uε + ω.toEReal (x - uε) <
      ((((f □ ω.toEReal) x).toReal + ε : ℝ) : EReal)) :
    ‖p - q‖ ^ (2 : ℕ) ≤ 8 * (L : ℝ) * ε := by
  let gε : E := ∇ ω (x - uε)
  have hp_bound :=
    norm_sub_sq_le_two_mul_L_eps_of_subgradient_and_epsSlice
      (f := f) (ω := ω) (L := L) (hω_convex := hω_convex) (hω_smooth := hω_smooth)
      (hreal := hreal) hL_pos (x := x) (p := p) (uε := uε) hp hε huε
  have hq_bound :=
    norm_sub_sq_le_two_mul_L_eps_of_subgradient_and_epsSlice
      (f := f) (ω := ω) (L := L) (hω_convex := hω_convex) (hω_smooth := hω_smooth)
      (hreal := hreal) hL_pos (x := x) (p := q) (uε := uε) hq hε huε
  -- Rewrite `p - q` through the common comparison point `gε` and apply the triangle inequality.
  have htriangle : ‖p - q‖ ≤ ‖p - gε‖ + ‖q - gε‖ := by
    calc
      ‖p - q‖ = ‖(p - gε) - (q - gε)‖ := by
        congr 1
        abel
      _ ≤ ‖p - gε‖ + ‖q - gε‖ := by
        simpa using norm_sub_le (p - gε) (q - gε)
  have hsquare :
      ‖p - q‖ ^ (2 : ℕ) ≤ (‖p - gε‖ + ‖q - gε‖) ^ (2 : ℕ) := by
    nlinarith [htriangle, norm_nonneg (p - q), norm_nonneg (p - gε), norm_nonneg (q - gε)]
  have hsum :
      (‖p - gε‖ + ‖q - gε‖) ^ (2 : ℕ) ≤ 8 * (L : ℝ) * ε := by
    have hnonneg_p : 0 ≤ ‖p - gε‖ := norm_nonneg _
    have hnonneg_q : 0 ≤ ‖q - gε‖ := norm_nonneg _
    nlinarith [hp_bound, hq_bound, hnonneg_p, hnonneg_q]
  exact le_trans hsquare hsum

omit hf_proper hf_closed in
/-- Helper for Theorem 5.30: in the positive-`L` branch, the Euclidean subdifferential of the
real-valued infimal convolution is a singleton at every point. -/
lemma euclideanSubdifferentialAt_infimalConvolution_toReal_eq_singleton
    (hL_pos : 0 < L) (x : E) :
    ∃ g : E,
      euclideanSubdifferentialAt (fun y ↦ ((f □ ω.toEReal) y).toReal) x = {g} := by
  have hLreal : 0 < (L : ℝ) := by
    exact_mod_cast hL_pos
  have hconv :
      ConvexOn ℝ Set.univ (fun y ↦ ((f □ ω.toEReal) y).toReal) :=
    convexOn_infimalConvolution_toReal
      (f := f) (ω := ω) (hf_convex := hf_convex) (hω_convex := hω_convex) (hreal := hreal)
  obtain ⟨φ, hφ⟩ := subdifferentialAt_nonempty_of_convexOn hconv x
  rcases (InnerProductSpace.toDual ℝ E).surjective φ with ⟨g, rfl⟩
  have hg :
      g ∈ euclideanSubdifferentialAt (fun y ↦ ((f □ ω.toEReal) y).toReal) x := by
    simpa [mem_euclideanSubdifferentialAt_iff, InnerProductSpace.toDual_apply_eq_toDualMap_apply]
      using hφ
  refine ⟨g, ?_⟩
  ext q
  constructor
  · intro hq
    by_cases hqg : q = g
    · simp [hqg]
    · let ε : ℝ := ‖q - g‖ ^ (2 : ℕ) / (16 * (L : ℝ))
      have hε_pos : 0 < ε := by
        have hqg_norm : 0 < ‖q - g‖ := by
          apply norm_pos_iff.mpr
          simpa [sub_eq_zero] using hqg
        have hqg_sq : 0 < ‖q - g‖ ^ (2 : ℕ) := by
          nlinarith [hqg_norm]
        dsimp [ε]
        exact div_pos hqg_sq (by positivity)
      obtain ⟨uε, huε⟩ :=
        exists_epsSlice_lt_infimalConvolution
          (f := f) (ω := ω) (hreal := hreal) (x := x) (ε := ε) hε_pos
      have hpair :=
        norm_sub_sq_le_eight_mul_L_eps_of_twoSubgradients_and_epsSlice
          (f := f) (ω := ω) (L := L) (hω_convex := hω_convex) (hω_smooth := hω_smooth)
          (hreal := hreal) hL_pos (x := x) (p := q) (q := g) (uε := uε) hq hg hε_pos huε
      have hrewrite : 8 * (L : ℝ) * ε = (‖q - g‖ ^ (2 : ℕ)) / 2 := by
        dsimp [ε]
        field_simp [hLreal.ne']
        ring
      rw [hrewrite] at hpair
      have hqg_sq : 0 < ‖q - g‖ ^ (2 : ℕ) := by
        have hqg_norm : 0 < ‖q - g‖ := by
          apply norm_pos_iff.mpr
          simpa [sub_eq_zero] using hqg
        nlinarith [hqg_norm]
      nlinarith
  · intro hq
    rcases Set.mem_singleton_iff.mp hq with rfl
    exact hg

omit hf_proper hf_closed in
/-- Helper for Theorem 5.30: the positive-`L` branch of the real-valued infimal convolution
satisfies the exact quadratic upper model from Theorem 5.8. -/
lemma quadraticUpperModel_infimalConvolution_toReal
    (hL_pos : 0 < L) :
    quadratic_upper_model (fun y ↦ ((f □ ω.toEReal) y).toReal) L := by
  have hLreal : 0 < (L : ℝ) := by
    exact_mod_cast hL_pos
  have hconv :
      ConvexOn ℝ Set.univ (fun y ↦ ((f □ ω.toEReal) y).toReal) :=
    convexOn_infimalConvolution_toReal
      (f := f) (ω := ω) (hf_convex := hf_convex) (hω_convex := hω_convex) (hreal := hreal)
  rw [quadratic_upper_model_iff]
  intro x y
  by_cases hxy : y = x
  · subst hxy
    simp
  · rcases euclideanSubdifferentialAt_infimalConvolution_toReal_eq_singleton
        (f := f) (ω := ω) (L := L) (hf_convex := hf_convex) (hω_convex := hω_convex)
        (hω_smooth := hω_smooth) (hreal := hreal) hL_pos x with
      ⟨g, hgset⟩
    have hg_mem :
        g ∈ euclideanSubdifferentialAt (fun z ↦ ((f □ ω.toEReal) z).toReal) x := by
      simp [hgset]
    have hgrad_data :=
      differentiableAt_and_eq_gradient_of_euclideanSubdifferentialAt_eq_singleton
        hconv hgset
    have hgrad : g = ∇ (fun z ↦ ((f □ ω.toEReal) z).toReal) x := hgrad_data.2
    -- Remove the residual `ε`-model error with an arbitrary positive slack.
    refine le_of_forall_pos_le_add ?_
    intro δ hδ
    let d : E := y - x
    have hd_pos : 0 < ‖d‖ := by
      dsimp [d]
      exact norm_pos_iff.mpr (by simpa [sub_eq_zero] using hxy)
    let σ : ℝ := δ / (2 * ‖d‖)
    let ε : ℝ := min (δ / 2) (σ ^ (2 : ℕ) / (2 * (L : ℝ)))
    have hε_pos : 0 < ε := by
      dsimp [ε, σ]
      apply lt_min
      · positivity
      · positivity
    have hε_le_half : ε ≤ δ / 2 := by
      dsimp [ε]
      exact min_le_left _ _
    have hε_le_sigma : ε ≤ σ ^ (2 : ℕ) / (2 * (L : ℝ)) := by
      dsimp [ε]
      exact min_le_right _ _
    obtain ⟨uε, huε⟩ :=
      exists_epsSlice_lt_infimalConvolution
        (f := f) (ω := ω) (hreal := hreal) (x := x) (ε := ε) hε_pos
    let gε : E := ∇ ω (x - uε)
    have hupper :=
      epsSlice_quadraticUpperModel_infimalConvolution_toReal
        (f := f) (ω := ω) (L := L) (hω_convex := hω_convex) (hω_smooth := hω_smooth)
        (hreal := hreal) (x := x) (uε := uε) hε_pos huε y
    have hprox :
        ‖g - gε‖ ^ (2 : ℕ) ≤ 2 * (L : ℝ) * ε := by
      simpa [gε] using
        norm_sub_sq_le_two_mul_L_eps_of_subgradient_and_epsSlice
          (f := f) (ω := ω) (L := L) (hω_convex := hω_convex) (hω_smooth := hω_smooth)
          (hreal := hreal) hL_pos (x := x) (p := g) (uε := uε) hg_mem hε_pos huε
    have hsigma_sq :
        ‖g - gε‖ ^ (2 : ℕ) ≤ σ ^ (2 : ℕ) := by
      have hscale_raw :
          (2 * (L : ℝ)) * ε ≤ (2 * (L : ℝ)) * (σ ^ (2 : ℕ) / (2 * (L : ℝ))) := by
        exact mul_le_mul_of_nonneg_left hε_le_sigma (by positivity)
      have hscale :
          (2 * (L : ℝ)) * ε ≤ σ ^ (2 : ℕ) := by
        have hcalc : (2 * (L : ℝ)) * (σ ^ (2 : ℕ) / (2 * (L : ℝ))) = σ ^ (2 : ℕ) := by
          field_simp [hLreal.ne']
        simpa [hcalc] using hscale_raw
      exact le_trans hprox hscale
    have hσ_nonneg : 0 ≤ σ := by
      dsimp [σ]
      positivity
    have hnorm_le_sigma : ‖g - gε‖ ≤ σ := by
      nlinarith [hsigma_sq, norm_nonneg (g - gε), hσ_nonneg]
    have hsigma_mul : σ * ‖d‖ = δ / 2 := by
      dsimp [σ]
      field_simp [hd_pos.ne']
    have hprod :
        ‖g - gε‖ * ‖d‖ ≤ δ / 2 := by
      have hmul := mul_le_mul_of_nonneg_right hnorm_le_sigma (norm_nonneg d)
      exact le_trans hmul (by simpa [hsigma_mul])
    have hinner :
        inner ℝ (gε - g) d ≤ δ / 2 := by
      have hcs : inner ℝ (gε - g) d ≤ ‖gε - g‖ * ‖d‖ := by
        simpa using real_inner_le_norm (gε - g) d
      exact le_trans hcs (by simpa [gε, norm_sub_rev, d] using hprod)
    have hsplit :
        inner ℝ gε d = inner ℝ g d + inner ℝ (gε - g) d := by
      calc
        inner ℝ gε d = inner ℝ ((gε - g) + g) d := by
          congr 1
          abel
        _ = inner ℝ (gε - g) d + inner ℝ g d := by
          rw [inner_add_left]
        _ = inner ℝ g d + inner ℝ (gε - g) d := by
          ring
    have hfinal :
        ((f □ ω.toEReal) y).toReal ≤
          (((f □ ω.toEReal) x).toReal +
            inner ℝ g d +
            ((L : ℝ) / 2) * ‖x - y‖ ^ (2 : ℕ)) + δ := by
      rw [hsplit] at hupper
      have herror : ε + inner ℝ (gε - g) d ≤ δ := by
        nlinarith [hε_le_half, hinner]
      nlinarith [hupper, herror]
    simpa [d, hgrad, add_assoc, add_left_comm, add_comm] using hfinal

-- Proof sketch: for each `x`, pick a minimizer of `u ↦ f u + ω (x - u)`, use first-order
-- optimality to produce a subgradient of `f` balancing `∇ ω (x - u(x))`, and deduce that this
-- vector is a subgradient of the real-valued infimal convolution. Monotonicity of the
-- subdifferential of `f` together with cocoercivity of the gradient of the convex `L`-smooth
-- kernel `ω` gives the `L`-Lipschitz bound for the resulting gradient field.
/-- Theorem 5.30 (1): if `f` is proper closed convex, `ω` is a convex `L`-smooth real-valued
function, and the infimal convolution `f □ ω.toEReal` is everywhere finite, then the real-valued map
`x ↦ ((f □ ω.toEReal) x).toReal` is `L`-smooth. -/
theorem infimal_convolution_toReal_is_l_smooth
    : is_l_smooth_on (fun x ↦ ((f □ ω.toEReal) x).toReal) Set.univ L := by
  by_cases hL_pos : 0 < L
  · have hconv :
        ConvexOn ℝ Set.univ (fun x ↦ ((f □ ω.toEReal) x).toReal) :=
      convexOn_infimalConvolution_toReal
        (f := f) (ω := ω) (hf_convex := hf_convex) (hω_convex := hω_convex) (hreal := hreal)
    have hdiff :
        Differentiable ℝ (fun x ↦ ((f □ ω.toEReal) x).toReal) := by
      intro x
      rcases euclideanSubdifferentialAt_infimalConvolution_toReal_eq_singleton
          (f := f) (ω := ω) (L := L) (hf_convex := hf_convex) (hω_convex := hω_convex)
          (hω_smooth := hω_smooth) (hreal := hreal) hL_pos x with
        ⟨g, hgset⟩
      exact
        (differentiableAt_and_eq_gradient_of_euclideanSubdifferentialAt_eq_singleton
          hconv hgset).1
    have hquad :=
      quadraticUpperModel_infimalConvolution_toReal
        (f := f) (ω := ω) (L := L) (hf_convex := hf_convex) (hω_convex := hω_convex)
        (hω_smooth := hω_smooth) (hreal := hreal) hL_pos
    exact (convex_l_smooth_iff_quadratic_upper_model hconv hdiff).2 hquad
  · have hL_zero : L = 0 := le_antisymm (not_lt.mp hL_pos) L.2
    subst hL_zero
    rcases (convexOn_eq_affine_of_is_l_smooth_on_zero (E := E) (ω := ω) hω_convex hω_smooth) with
      ⟨b, hb⟩
    -- In the zero-modulus branch the kernel is affine, so the infimal convolution is affine too.
    convert is_l_smooth_affine_functional b (((f □ ω.toEReal) 0).toReal) using 1
    ext x
    exact infimalConvolution_toReal_eq_affine_of_kernel_eq_affine
      (f := f) (ω := ω) (hreal := hreal) b hb x

-- Proof sketch: the minimizer assumption identifies `u` as an optimizer of the defining infimum at
-- `x`. The optimality condition yields `∇ ω (x - u) ∈ ∂f(u)`, hence the same vector is a
-- subgradient of `y ↦ ((f □ ω.toEReal) y).toReal` at `x`. Part (1) supplies differentiability of
-- the
-- infimal convolution, so Proposition 3.14 identifies its unique subgradient with its gradient,
-- giving the displayed formula.
/-- The canonical gradient companion for Theorem 5.30 (2): if `u` minimizes
`v ↦ f(v) + ω.toEReal (x - v)` at `x`, then the real-valued infimal convolution has gradient
`∇ ω (x - u)` at `x`. -/
theorem hasGradientAt_infimal_convolution_toReal_of_isMinOn
    (x u : E)
    (hu : IsMinOn (fun v : E ↦ f v + ω.toEReal (x - v)) Set.univ u) :
    HasGradientAt (fun y ↦ ((f □ ω.toEReal) y).toReal) (∇ ω (x - u)) x := by
  have hconv :
      ConvexOn ℝ Set.univ (fun y ↦ ((f □ ω.toEReal) y).toReal) :=
    convexOn_infimalConvolution_toReal
      (f := f) (ω := ω) (hf_convex := hf_convex) (hω_convex := hω_convex) (hreal := hreal)
  have hsmooth :=
    infimal_convolution_toReal_is_l_smooth
      (f := f) (ω := ω) (L := L) (hf_proper := hf_proper) (hf_closed := hf_closed)
      (hf_convex := hf_convex) (hω_convex := hω_convex) (hω_smooth := hω_smooth)
      (hreal := hreal)
  have hdiff : DifferentiableAt ℝ (fun y ↦ ((f □ ω.toEReal) y).toReal) x :=
    hsmooth.1 x (by simp)
  have hsub :
      ∇ ω (x - u) ∈
        euclideanSubdifferentialAt (fun y ↦ ((f □ ω.toEReal) y).toReal) x :=
    gradientSub_mem_euclideanSubdifferentialAt_infimalConvolution_toReal_of_isMinOn
      (f := f) (ω := ω) (L := L) (hf_proper := hf_proper) (hf_convex := hf_convex)
      (hω_convex := hω_convex) (hω_smooth := hω_smooth) (hreal := hreal) (x := x) (u := u) hu
  have hgrad_eq :
      ∇ ω (x - u) = ∇ (fun y ↦ ((f □ ω.toEReal) y).toReal) x := by
    -- Differentiability turns the Euclidean subdifferential into a singleton gradient set.
    simpa
      [euclideanSubdifferentialAt_eq_singleton_gradient_of_differentiableAt hconv hdiff] using hsub
  simpa [hgrad_eq] using hdiff.hasGradientAt

-- Proof sketch: apply `HasGradientAt.gradient` to
-- `hasGradientAt_infimal_convolution_toReal_of_isMinOn`.
/-- Theorem 5.30 (2): if `u` minimizes `v ↦ f(v) + ω.toEReal (x - v)` at `x`, then the
gradient of the real-valued infimal convolution at `x` is the gradient of `ω` at `x - u`. -/
theorem gradient_infimal_convolution_toReal_eq_gradient_sub_of_isMinOn
    (x u : E)
    (hu : IsMinOn (fun v : E ↦ f v + ω.toEReal (x - v)) Set.univ u) :
    ∇ (fun y ↦ ((f □ ω.toEReal) y).toReal) x = ∇ ω (x - u) :=
  (hasGradientAt_infimal_convolution_toReal_of_isMinOn
    f ω L hf_proper hf_closed hf_convex hω_convex hω_smooth hreal x u hu).gradient

omit hf_proper hf_closed hf_convex hω_convex hω_smooth hreal

end
