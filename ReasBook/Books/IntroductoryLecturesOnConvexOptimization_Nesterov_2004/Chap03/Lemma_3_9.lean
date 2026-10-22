/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_21

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Filter

open scoped WithTopConvexAnalysis

open scoped Topology

universe u v

variable {E₁ : Type u} {E₂ : Type v}

local notation "Z" => WithLp 2 (E₁ × E₂)
local notation "toZ" => WithLp.toLp 2

/- Lemma 3.9 lies in the product-space extended-valued subdifferential domain.

Primary domain:
- convex analysis of `WithTop ℝ`-valued functions on products of real inner-product spaces.

Relevant owner-style declarations sampled before refinement:
- `withTopEffectiveDomain` and `withTopRealPart` in `Definition_3_3`;
- `IsSubgradientAt`, `subdifferential`, and `mem_subdifferential_iff` in `Definition_3_1_5`;
- mathlib `gradient` on real inner-product spaces;
- mathlib `WithLp 2 (E₁ × E₂)`, `WithLp.fst`, `WithLp.snd`, and `WithLp.toLp` for the canonical
  `L²` product owner.

Best owner abstraction:
- core/canonical: the ambient owner `subdifferential` on the intrinsic `L²` product inner-product
  space `Z = WithLp 2 (E₁ × E₂)`;
- source-facing owner in this file: the first-slice gradient and second-slice subdifferential.

Primitive data:
- the frozen-factor slices `x ↦ f (WithLp.toLp 2 (x, z.snd))` and
  `y ↦ f (WithLp.toLp 2 (z.fst, y))`;
- the base point `z : Z`.

Derived API:
- `partialGradientFst`;
- `partialSubdifferentialSnd`;
- the neighborhood-form bridge theorem
  `subdifferential_eq_image_partialGradientFst_partialSubdifferentialSnd_of_nhds`.

Source/core/bridge triage:
- source-facing: `partialGradientFst` and `partialSubdifferentialSnd`;
- core/canonical: `subdifferential`;
- bridge/view: the neighborhood-form theorem below.

The ambient extended-valued subgradient owner already lives in `Definition_3_1_5`, so this file
keeps only the slice-level source-facing API and states its main theorem directly on the
intrinsic `L²` product space `Z`, using mathlib's canonical product inner-product structure
instead of an extra theorem binder.
-/

section Fst

variable [NormedAddCommGroup E₁]
variable [InnerProductSpace ℝ E₁] [CompleteSpace E₁]

/-- The first-variable partial gradient of `f` at `z = (x, y)` is the gradient of the finite real
part of the slice `x' ↦ f (x', y)`. -/
def partialGradientFst (f : Z → WithTop ℝ) (z : Z) : E₁ :=
  gradient (withTopRealPart fun x ↦ f (toZ (x, z.snd))) z.fst

end Fst

section Snd

variable [NormedAddCommGroup E₂]
variable [InnerProductSpace ℝ E₂]

/-- The second-variable partial subdifferential of `f` at `z = (x, y)` is the ambient owner
subdifferential of the frozen-first-coordinate slice `y' ↦ f (x, y')`. -/
def partialSubdifferentialSnd (f : Z → WithTop ℝ) (z : Z) : Set E₂ :=
  ∂ (fun y ↦ f (toZ (z.fst, y)))(z.snd)

end Snd

section Main

variable [NormedAddCommGroup E₁] [NormedAddCommGroup E₂]
variable [InnerProductSpace ℝ E₁] [CompleteSpace E₁] [InnerProductSpace ℝ E₂]

omit [InnerProductSpace ℝ E₁] [CompleteSpace E₁] [InnerProductSpace ℝ E₂] in
/-- Helper for Lemma 3.9: freezing the second coordinate preserves interior-domain membership at
the first-coordinate base point. -/
lemma fst_slice_mem_interior_dom
    {f : Z → WithTop ℝ} {zBar : Z}
    (hzBar : zBar ∈ interior (dom f)) :
    zBar.fst ∈ interior (dom (fun x : E₁ ↦ f (toZ (x, zBar.snd)))) := by
  -- Pull the ambient interior neighborhood back along the continuous frozen-second-coordinate map.
  let e : E₁ → Z := fun x ↦ toZ (x, zBar.snd)
  have he_cont : Continuous e := by
    fun_prop
  rw [mem_interior_iff_mem_nhds]
  have hpre : e ⁻¹' interior (dom f) ∈ 𝓝 zBar.fst := by
    exact he_cont.continuousAt.preimage_mem_nhds (IsOpen.mem_nhds isOpen_interior hzBar)
  refine Filter.mem_of_superset hpre ?_
  intro x hx
  simpa [e] using interior_subset hx

omit [InnerProductSpace ℝ E₁] [CompleteSpace E₁] [InnerProductSpace ℝ E₂] in
/-- Helper for Lemma 3.9: freezing the first coordinate preserves interior-domain membership at
the second-coordinate base point. -/
lemma snd_slice_mem_interior_dom
    {f : Z → WithTop ℝ} {zBar : Z}
    (hzBar : zBar ∈ interior (dom f)) :
    zBar.snd ∈ interior (dom (fun y : E₂ ↦ f (toZ (zBar.fst, y)))) := by
  -- Pull the ambient interior neighborhood back along the continuous frozen-first-coordinate map.
  let e : E₂ → Z := fun y ↦ toZ (zBar.fst, y)
  have he_cont : Continuous e := by
    fun_prop
  rw [mem_interior_iff_mem_nhds]
  have hpre : e ⁻¹' interior (dom f) ∈ 𝓝 zBar.snd := by
    exact he_cont.continuousAt.preimage_mem_nhds (IsOpen.mem_nhds isOpen_interior hzBar)
  refine Filter.mem_of_superset hpre ?_
  intro y hy
  simpa [e] using interior_subset hy

omit [CompleteSpace E₁] in
/-- Helper for Lemma 3.9: freezing the second coordinate preserves convexity on the first slice. -/
lemma fst_slice_convexOn
    {f : Z → WithTop ℝ}
    (hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    (y : E₂) :
    ConvexOn ℝ (dom (fun x : E₁ ↦ f (toZ (x, y))))
      (withTopRealPart fun x : E₁ ↦ f (toZ (x, y))) := by
  refine ⟨?_, ?_⟩
  · intro x hx w hw a b ha hb hab
    have hx' : toZ (x, y) ∈ dom f := by
      simpa using hx
    have hw' : toZ (w, y) ∈ dom f := by
      simpa using hw
    have hcomb :
        a • toZ (x, y) + b • toZ (w, y) = toZ (a • x + b • w, y) := by
      have hpair : a • (x, y) + b • (w, y) = (a • x + b • w, y) := by
        apply Prod.ext
        · simp [Prod.smul_mk, Prod.mk_add_mk]
        · calc
            a • y + b • y = (a + b) • y := by rw [← add_smul]
            _ = y := by rw [hab, one_smul]
      rw [← WithLp.toLp_add, ← WithLp.toLp_smul, ← WithLp.toLp_smul]
      rw [hpair]
    simpa [hcomb] using hf.1 hx' hw' ha hb hab
  · intro x hx w hw a b ha hb hab
    have hx' : toZ (x, y) ∈ dom f := by
      simpa using hx
    have hw' : toZ (w, y) ∈ dom f := by
      simpa using hw
    have hcomb :
        a • toZ (x, y) + b • toZ (w, y) = toZ (a • x + b • w, y) := by
      have hpair : a • (x, y) + b • (w, y) = (a • x + b • w, y) := by
        apply Prod.ext
        · simp [Prod.smul_mk, Prod.mk_add_mk]
        · calc
            a • y + b • y = (a + b) • y := by rw [← add_smul]
            _ = y := by rw [hab, one_smul]
      rw [← WithLp.toLp_add, ← WithLp.toLp_smul, ← WithLp.toLp_smul]
      rw [hpair]
    simpa [hcomb] using hf.2 hx' hw' ha hb hab

omit [CompleteSpace E₁] in
/-- Helper for Lemma 3.9: freezing the first coordinate preserves convexity on the second slice. -/
lemma snd_slice_convexOn
    {f : Z → WithTop ℝ}
    (hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    (x : E₁) :
    ConvexOn ℝ (dom (fun y : E₂ ↦ f (toZ (x, y))))
      (withTopRealPart fun y : E₂ ↦ f (toZ (x, y))) := by
  refine ⟨?_, ?_⟩
  · intro y hy w hw a b ha hb hab
    have hy' : toZ (x, y) ∈ dom f := by
      simpa using hy
    have hw' : toZ (x, w) ∈ dom f := by
      simpa using hw
    have hcomb :
        a • toZ (x, y) + b • toZ (x, w) = toZ (x, a • y + b • w) := by
      have hpair : a • (x, y) + b • (x, w) = (x, a • y + b • w) := by
        apply Prod.ext
        · calc
            a • x + b • x = (a + b) • x := by rw [← add_smul]
            _ = x := by rw [hab, one_smul]
        · simp [Prod.smul_mk, Prod.mk_add_mk]
      rw [← WithLp.toLp_add, ← WithLp.toLp_smul, ← WithLp.toLp_smul]
      rw [hpair]
    simpa [hcomb] using hf.1 hy' hw' ha hb hab
  · intro y hy w hw a b ha hb hab
    have hy' : toZ (x, y) ∈ dom f := by
      simpa using hy
    have hw' : toZ (x, w) ∈ dom f := by
      simpa using hw
    have hcomb :
        a • toZ (x, y) + b • toZ (x, w) = toZ (x, a • y + b • w) := by
      have hpair : a • (x, y) + b • (x, w) = (x, a • y + b • w) := by
        apply Prod.ext
        · calc
            a • x + b • x = (a + b) • x := by rw [← add_smul]
            _ = x := by rw [hab, one_smul]
        · simp [Prod.smul_mk, Prod.mk_add_mk]
      rw [← WithLp.toLp_add, ← WithLp.toLp_smul, ← WithLp.toLp_smul]
      rw [hpair]
    simpa [hcomb] using hf.2 hy' hw' ha hb hab

/-- Helper for Lemma 3.9: every domain point lies above the affine support built from the
directional derivative at an interior point. -/
lemma directionalDerivative_affine_support_of_mem_interior
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {f : V → WithTop ℝ}
    (hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    {x : V} (hx : x ∈ interior (dom f))
    {y : V} (hy : y ∈ dom f) :
    withTopRealPart f y ≥
      withTopRealPart f x + f′[hx] (y - x) := by
  let line : ℝ →ᵃ[ℝ] V := AffineMap.lineMap x y
  let S : Set ℝ := line ⁻¹' dom f
  let g : ℝ → ℝ := withTopRealPart f ∘ line
  have hline_apply (α : ℝ) : line α = x + α • (y - x) := by
    simpa [line, sub_eq_add_neg, add_smul, smul_add, add_assoc, add_left_comm, add_comm] using
      (AffineMap.lineMap_apply_module x y α)
  have hconv : ConvexOn ℝ S g := by
    -- Restrict the ambient convex function to the affine line through `x` and `y`.
    simpa [S, g] using hf.comp_affineMap line
  have hzero_mem : (0 : ℝ) ∈ S := by
    simpa [S, hline_apply] using interior_subset hx
  have hone_mem : (1 : ℝ) ∈ S := by
    simpa [S, hline_apply] using hy
  have hslice :
      (fun α : ℝ ↦ (withTopToEReal (f (x + α • (y - x)))).toReal) = g := by
    -- The scalar slice through `withTopToEReal` is exactly the finite real part along the same
    -- affine line.
    funext α
    change (withTopToEReal (f (x + α • (y - x)))).toReal = withTopRealPart f (line α)
    rw [hline_apply]
    simpa using
      (withTopToEReal_toReal_eq_withTopRealPart (f := f) (z := x + α • (y - x)))
  have hderiv_Ici : HasDerivWithinAt g (f′[hx] (y - x)) (Set.Ici (0 : ℝ)) 0 := by
    -- Read the ambient directional derivative through the scalar line.
    simpa [extendedRealRealPart_eq_toReal, Function.comp, hslice] using
      (convexDirectionalDerivative_toReal_hasDirectionalDerivAt hf hx (y - x)).hasDerivWithinAt
  have hderiv_Ioi : HasDerivWithinAt g (f′[hx] (y - x)) (Set.Ioi (0 : ℝ)) 0 :=
    hderiv_Ici.Ioi_of_Ici
  have hslope :
      f′[hx] (y - x) ≤ withTopRealPart f y - withTopRealPart f x := by
    -- A convex scalar slice lies above its right derivative at the left endpoint.
    simpa [g, slope_def_field, hline_apply] using
      hconv.le_slope_of_hasDerivWithinAt_Ioi hzero_mem hone_mem zero_lt_one hderiv_Ioi
  linarith

/-- Helper for Lemma 3.9: the real secant quotients converge to the finite directional derivative
at an interior point of the effective domain. -/
lemma directionalSecantQuotient_tendsto_of_mem_interior
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {f : V → WithTop ℝ}
    (hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    {x0 : V} (hx0 : x0 ∈ interior (dom f)) (p : V) :
    Tendsto
      (fun α : ℝ ↦ (withTopRealPart f (x0 + α • p) - withTopRealPart f x0) / α)
      (𝓝[>] (0 : ℝ)) (𝓝 (f′[hx0] p)) := by
  have hslice :
      (fun α : ℝ ↦ extendedRealRealPart (withTopToEReal ∘ f) (x0 + α • p)) =
        fun α : ℝ ↦ withTopRealPart f (x0 + α • p) := by
    funext α
    simpa using (withTopToEReal_toReal_eq_withTopRealPart (f := f) (z := x0 + α • p))
  have hderiv_Ioi :
      HasDerivWithinAt
        (fun α : ℝ ↦ extendedRealRealPart (withTopToEReal ∘ f) (x0 + α • p))
        (f′[hx0] p) (Set.Ioi (0 : ℝ)) 0 := by
    have hderiv_Ici := convexDirectionalDerivative_toReal_hasDirectionalDerivAt hf hx0 p
    exact hderiv_Ici.hasDerivWithinAt.Ioi_of_Ici
  rw [hasDerivWithinAt_iff_tendsto_slope' (show (0 : ℝ) ∉ Set.Ioi (0 : ℝ) by simp)] at hderiv_Ioi
  rw [hslice] at hderiv_Ioi
  simpa [slope_fun_def_field] using hderiv_Ioi

/-- Helper for Lemma 3.9: at an interior point of a convex slice, the finite directional
derivative is the pairing with the displayed gradient. -/
lemma directionalDerivative_eq_inner_gradient_of_hasGradientAt
    {φ : E₁ → WithTop ℝ}
    (hφconv : ConvexOn ℝ (dom φ) (withTopRealPart φ))
    {x : E₁} (hx : x ∈ interior (dom φ))
    {g : E₁} (hgrad : HasGradientAt (withTopRealPart φ) g x)
    (p : E₁) :
    φ′[hx] p = inner ℝ g p := by
  -- Read the same secant quotient through both the convex directional-derivative owner and the
  -- ordinary line derivative supplied by the gradient witness.
  have hsecant :
      Tendsto
        (fun α : ℝ ↦ (withTopRealPart φ (x + α • p) - withTopRealPart φ x) / α)
        (𝓝[>] (0 : ℝ)) (𝓝 (φ′[hx] p)) :=
      directionalSecantQuotient_tendsto_of_mem_interior hφconv hx p
  have hline :
      HasLineDerivAt ℝ (withTopRealPart φ) (inner ℝ g p) x p := by
    simpa [hgrad.fderiv_apply] using hgrad.hasFDerivAt.hasLineDerivAt p
  have hslope :
      Tendsto
        (fun α : ℝ ↦ (withTopRealPart φ (x + α • p) - withTopRealPart φ x) / α)
        (𝓝[>] (0 : ℝ)) (𝓝 (inner ℝ g p)) := by
    simpa [div_eq_mul_inv, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
      hline.tendsto_slope_zero_right
  exact tendsto_nhds_unique hsecant hslope

/-- Helper for Lemma 3.9: at an interior point of a convex slice, the displayed gradient is a
subgradient of that slice. -/
lemma gradient_mem_subdifferential_of_hasGradientAt
    {φ : E₁ → WithTop ℝ}
    (hφconv : ConvexOn ℝ (dom φ) (withTopRealPart φ))
    {x : E₁} (hx : x ∈ interior (dom φ))
    {g : E₁} (hgrad : HasGradientAt (withTopRealPart φ) g x) :
    g ∈ ∂ φ(x) := by
  -- Turn the affine-support inequality from the directional derivative into the subgradient
  -- inequality using the explicit gradient formula for the directional derivative.
  refine mem_subdifferential_iff.mpr ?_
  constructor
  · exact interior_subset hx
  · intro y hy
    have hsupport :=
      directionalDerivative_affine_support_of_mem_interior hφconv hx hy
    have hdir :
        φ′[hx] (y - x) = inner ℝ g (y - x) :=
      directionalDerivative_eq_inner_gradient_of_hasGradientAt hφconv hx hgrad (y - x)
    have hx_dom : x ∈ dom φ := interior_subset hx
    have hreal :
        withTopRealPart φ y ≥ withTopRealPart φ x + inner ℝ g (y - x) := by
      simpa [hdir] using hsupport
    rw [← coe_withTopRealPart hy, ← coe_withTopRealPart hx_dom]
    exact_mod_cast hreal

/-- Helper for Lemma 3.9: on a frozen slice, any subgradient at an interior point agrees with the
displayed gradient when that gradient exists. -/
lemma eq_gradient_of_mem_subdifferential_of_hasGradientAt
    {φ : E₁ → WithTop ℝ} {x g h : E₁}
    (hx : x ∈ interior (dom φ))
    (hgrad : HasGradientAt (withTopRealPart φ) g x)
    (hh : h ∈ ∂ φ(x)) :
    h = g := by
  -- Compare the subgradient lower bound with the line-derivative limits in directions `p` and `-p`.
  apply ext_inner_right ℝ
  intro p
  have hx_dom : x ∈ dom φ := interior_subset hx
  have hhsub := mem_subdifferential_iff.mp hh
  have hline_grad_pos : HasLineDerivAt ℝ (withTopRealPart φ) (inner ℝ g p) x p := by
    simpa [hgrad.fderiv_apply] using hgrad.hasFDerivAt.hasLineDerivAt p
  have hline_grad_neg : HasLineDerivAt ℝ (withTopRealPart φ) (inner ℝ g (-p)) x (-p) := by
    simpa [hgrad.fderiv_apply] using hgrad.hasFDerivAt.hasLineDerivAt (-p)
  have hpath_pos : Tendsto (fun α : ℝ ↦ x + α • p) (𝓝[>] (0 : ℝ)) (𝓝 x) := by
    have hcont : ContinuousAt (fun α : ℝ ↦ x + α • p) (0 : ℝ) := by
      fun_prop
    simpa [nhdsWithin, zero_smul] using hcont.tendsto.mono_left inf_le_left
  have hpath_neg : Tendsto (fun α : ℝ ↦ x + α • (-p)) (𝓝[>] (0 : ℝ)) (𝓝 x) := by
    have hcont : ContinuousAt (fun α : ℝ ↦ x + α • (-p)) (0 : ℝ) := by
      fun_prop
    simpa [nhdsWithin, zero_smul] using hcont.tendsto.mono_left inf_le_left
  have hdom_pos : ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), x + α • p ∈ dom φ := by
    exact (hpath_pos.eventually (IsOpen.mem_nhds isOpen_interior hx)).mono fun α hα ↦
      interior_subset hα
  have hdom_neg : ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), x + α • (-p) ∈ dom φ := by
    exact (hpath_neg.eventually (IsOpen.mem_nhds isOpen_interior hx)).mono fun α hα ↦
      interior_subset hα
  have hlim_pos :
      Tendsto (fun α : ℝ ↦ (withTopRealPart φ (x + α • p) - withTopRealPart φ x) / α)
        (𝓝[>] (0 : ℝ)) (𝓝 (inner ℝ g p)) := by
    simpa [div_eq_mul_inv, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
      hline_grad_pos.tendsto_slope_zero_right
  have hlim_neg :
      Tendsto (fun α : ℝ ↦ (withTopRealPart φ (x + α • (-p)) - withTopRealPart φ x) / α)
        (𝓝[>] (0 : ℝ)) (𝓝 (inner ℝ g (-p))) := by
    simpa [div_eq_mul_inv, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
      hline_grad_neg.tendsto_slope_zero_right
  have hpos : inner ℝ h p ≤ inner ℝ g p := by
    have hineq : ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ),
        inner ℝ h p ≤ (withTopRealPart φ (x + α • p) - withTopRealPart φ x) / α := by
      filter_upwards [hdom_pos, self_mem_nhdsWithin] with α hαdom hαpos
      have hsubineq :
          φ (x + α • p) ≥ φ x + (inner ℝ h (x + α • p - x) : WithTop ℝ) :=
        hhsub.2 hαdom
      have hreal :
          withTopRealPart φ (x + α • p) ≥ withTopRealPart φ x + α * inner ℝ h p := by
        rw [← coe_withTopRealPart hαdom, ← coe_withTopRealPart hx_dom] at hsubineq
        have hinner : inner ℝ h (x + α • p - x) = α * inner ℝ h p := by
          simp [inner_smul_right]
        rw [hinner] at hsubineq
        exact_mod_cast hsubineq
      have hdiff : α * inner ℝ h p ≤ withTopRealPart φ (x + α • p) - withTopRealPart φ x := by
        linarith
      rw [div_eq_mul_inv]
      exact (le_div_iff₀ hαpos).2 (by simpa [mul_comm] using hdiff)
    exact tendsto_le_of_eventuallyLE tendsto_const_nhds hlim_pos hineq
  have hneg : inner ℝ h p ≥ inner ℝ g p := by
    have hineq : ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ),
        inner ℝ h (-p) ≤ (withTopRealPart φ (x + α • (-p)) - withTopRealPart φ x) / α := by
      filter_upwards [hdom_neg, self_mem_nhdsWithin] with α hαdom hαpos
      have hsubineq :
          φ (x + α • (-p)) ≥ φ x + (inner ℝ h (x + α • (-p) - x) : WithTop ℝ) :=
        hhsub.2 hαdom
      have hreal :
          withTopRealPart φ (x + α • (-p)) ≥ withTopRealPart φ x + α * inner ℝ h (-p) := by
        rw [← coe_withTopRealPart hαdom, ← coe_withTopRealPart hx_dom] at hsubineq
        have hinner : inner ℝ h (x + α • (-p) - x) = α * inner ℝ h (-p) := by
          simp [inner_smul_right]
        rw [hinner] at hsubineq
        exact_mod_cast hsubineq
      have hdiff :
          α * inner ℝ h (-p) ≤ withTopRealPart φ (x + α • (-p)) - withTopRealPart φ x := by
        linarith
      rw [div_eq_mul_inv]
      exact (le_div_iff₀ hαpos).2 (by simpa [mul_comm] using hdiff)
    have hneg' : inner ℝ h (-p) ≤ inner ℝ g (-p) :=
      tendsto_le_of_eventuallyLE tendsto_const_nhds hlim_neg hineq
    simpa using hneg'
  linarith

/-- Helper for Lemma 3.9: the first-coordinate secant quotient converges to the pairing with the
partial gradient at the base point. -/
lemma fst_slice_secant_tendsto_partialGradientFst_pairing
    {f : Z → WithTop ℝ}
    (hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    {zBar : Z} (hzBar : zBar ∈ interior (dom f))
    (hgrad : ∀ᶠ z in 𝓝 zBar,
      HasGradientAt
        (withTopRealPart fun x ↦ f (toZ (x, z.snd)))
        (partialGradientFst f z) z.fst)
    (hcont : ContinuousAt (partialGradientFst f) zBar)
    (h : Z) :
    Tendsto
      (fun α : ℝ ↦
        (withTopRealPart f (zBar + α • h) -
            withTopRealPart f (toZ (zBar.fst, zBar.snd + α • h.snd))) / α)
      (𝓝[>] (0 : ℝ)) (𝓝 (inner ℝ (partialGradientFst f zBar) h.fst)) := by
  let pathSnd : ℝ → Z := fun α ↦ toZ (zBar.fst, zBar.snd + α • h.snd)
  let pathFull : ℝ → Z := fun α ↦ zBar + α • h
  let q : ℝ → ℝ := fun α ↦
    (withTopRealPart f (pathFull α) - withTopRealPart f (pathSnd α)) / α
  have hpathSnd : Tendsto pathSnd (𝓝[>] (0 : ℝ)) (𝓝 zBar) := by
    have hcont_pathSnd : ContinuousAt pathSnd (0 : ℝ) := by
      fun_prop
    simpa [pathSnd, zero_smul] using hcont_pathSnd.tendsto.mono_left inf_le_left
  have hpathFull : Tendsto pathFull (𝓝[>] (0 : ℝ)) (𝓝 zBar) := by
    have hcont_pathFull : ContinuousAt pathFull (0 : ℝ) := by
      fun_prop
    simpa [pathFull, zero_smul] using hcont_pathFull.tendsto.mono_left inf_le_left
  have hpathSnd_int :
      ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), pathSnd α ∈ interior (dom f) := by
    exact (hpathSnd.eventually (IsOpen.mem_nhds isOpen_interior hzBar))
  have hpathFull_int :
      ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), pathFull α ∈ interior (dom f) := by
    exact (hpathFull.eventually (IsOpen.mem_nhds isOpen_interior hzBar))
  have hpathSnd_grad :
      ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ),
        HasGradientAt
          (withTopRealPart fun x ↦ f (toZ (x, (pathSnd α).snd)))
          (partialGradientFst f (pathSnd α)) (pathSnd α).fst := by
    exact hpathSnd.eventually hgrad
  have hpathFull_grad :
      ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ),
        HasGradientAt
          (withTopRealPart fun x ↦ f (toZ (x, (pathFull α).snd)))
          (partialGradientFst f (pathFull α)) (pathFull α).fst := by
    exact hpathFull.eventually hgrad
  have hpos : ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), 0 < α := by
    simpa using
      (eventually_mem_nhdsWithin : ∀ᶠ α in 𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ), α ∈ Set.Ioi (0 : ℝ))
  have hlower :
      ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ),
        inner ℝ (partialGradientFst f (pathSnd α)) h.fst ≤ q α := by
    filter_upwards [hpathSnd_int, hpathFull_int, hpathSnd_grad, hpos] with
      α hαsnd hαfull hαgrad hαpos
    let φα : E₁ → WithTop ℝ := fun x ↦ f (toZ (x, zBar.snd + α • h.snd))
    have hslice_int : zBar.fst ∈ interior (dom φα) := by
      simpa [φα, pathSnd] using fst_slice_mem_interior_dom (f := f) (zBar := pathSnd α) hαsnd
    have hslice_grad :
        HasGradientAt (withTopRealPart φα) (partialGradientFst f (pathSnd α)) zBar.fst := by
      simpa [φα, pathSnd, partialGradientFst] using hαgrad
    have hslice_sub :
        partialGradientFst f (pathSnd α) ∈ ∂ φα(zBar.fst) :=
      gradient_mem_subdifferential_of_hasGradientAt
        (fst_slice_convexOn hf (zBar.snd + α • h.snd)) hslice_int hslice_grad
    have hfull_dom : pathFull α ∈ dom f := interior_subset hαfull
    have hslice_full_dom : zBar.fst + α • h.fst ∈ dom φα := by
      simpa [φα, pathFull, WithLp.toLp_add, WithLp.toLp_smul, Prod.smul_mk,
        Prod.mk_add_mk] using hfull_dom
    have hslice_ineq :
        φα (zBar.fst + α • h.fst) ≥
          φα zBar.fst +
            (inner ℝ (partialGradientFst f (pathSnd α))
              ((zBar.fst + α • h.fst) - zBar.fst) : WithTop ℝ) :=
      (mem_subdifferential_iff.mp hslice_sub).2 hslice_full_dom
    have hslice_ineq' :
        (f (pathFull α) : WithTop ℝ) ≥
          f (pathSnd α) +
            (inner ℝ (partialGradientFst f (pathSnd α))
              ((zBar.fst + α • h.fst) - zBar.fst) : WithTop ℝ) := by
      simpa [φα, pathFull, pathSnd, WithLp.toLp_add, WithLp.toLp_smul, Prod.smul_mk,
        Prod.mk_add_mk] using hslice_ineq
    have hreal :
        withTopRealPart f (pathFull α) ≥
          withTopRealPart f (pathSnd α) +
            α * inner ℝ (partialGradientFst f (pathSnd α)) h.fst := by
      rw [← coe_withTopRealPart hfull_dom,
        ← coe_withTopRealPart (interior_subset hαsnd)] at hslice_ineq'
      have hinner :
          inner ℝ (partialGradientFst f (pathSnd α))
              ((zBar.fst + α • h.fst) - zBar.fst) =
            α * inner ℝ (partialGradientFst f (pathSnd α)) h.fst := by
        simp [inner_smul_right]
      rw [hinner] at hslice_ineq'
      exact_mod_cast hslice_ineq'
    have hdiff :
        α * inner ℝ (partialGradientFst f (pathSnd α)) h.fst ≤
          withTopRealPart f (pathFull α) - withTopRealPart f (pathSnd α) := by
      linarith
    exact (le_div_iff₀ hαpos).2 (by simpa [q, pathFull, pathSnd, mul_comm] using hdiff)
  have hupper :
      ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ),
        q α ≤ inner ℝ (partialGradientFst f (pathFull α)) h.fst := by
    filter_upwards [hpathSnd_int, hpathFull_int, hpathFull_grad, hpos] with
      α hαsnd hαfull hαgrad hαpos
    let φα : E₁ → WithTop ℝ := fun x ↦ f (toZ (x, zBar.snd + α • h.snd))
    have hslice_int : zBar.fst + α • h.fst ∈ interior (dom φα) := by
      simpa [φα, pathFull, WithLp.toLp_add, WithLp.toLp_smul, Prod.smul_mk, Prod.mk_add_mk] using
        fst_slice_mem_interior_dom (f := f) (zBar := pathFull α) hαfull
    have hslice_grad :
        HasGradientAt (withTopRealPart φα) (partialGradientFst f (pathFull α))
          (zBar.fst + α • h.fst) := by
      simpa [φα, pathFull, partialGradientFst, WithLp.toLp_add, WithLp.toLp_smul,
        Prod.smul_mk, Prod.mk_add_mk] using hαgrad
    have hslice_sub :
        partialGradientFst f (pathFull α) ∈ subdifferential φα (zBar.fst + α • h.fst) :=
      gradient_mem_subdifferential_of_hasGradientAt
        (fst_slice_convexOn hf (zBar.snd + α • h.snd)) hslice_int hslice_grad
    have hslice_base_dom : zBar.fst ∈ dom φα := by
      simpa [φα, pathSnd] using interior_subset hαsnd
    have hslice_ineq :
        φα zBar.fst ≥
          φα (zBar.fst + α • h.fst) +
            (inner ℝ (partialGradientFst f (pathFull α))
              (zBar.fst - (zBar.fst + α • h.fst)) : WithTop ℝ) :=
      (mem_subdifferential_iff.mp hslice_sub).2 hslice_base_dom
    have hslice_ineq' :
        (f (pathSnd α) : WithTop ℝ) ≥
          f (pathFull α) +
            (inner ℝ (partialGradientFst f (pathFull α))
              (zBar.fst - (zBar.fst + α • h.fst)) : WithTop ℝ) := by
      simpa [φα, pathFull, pathSnd, WithLp.toLp_add, WithLp.toLp_smul, Prod.smul_mk,
        Prod.mk_add_mk] using hslice_ineq
    have hreal :
        withTopRealPart f (pathSnd α) ≥
          withTopRealPart f (pathFull α) -
            α * inner ℝ (partialGradientFst f (pathFull α)) h.fst := by
      rw [← coe_withTopRealPart (interior_subset hαsnd),
        ← coe_withTopRealPart (interior_subset hαfull)] at hslice_ineq'
      have hinner :
          inner ℝ (partialGradientFst f (pathFull α))
              (zBar.fst - (zBar.fst + α • h.fst)) =
            -α * inner ℝ (partialGradientFst f (pathFull α)) h.fst := by
        simp [inner_smul_right]
      rw [hinner] at hslice_ineq'
      have hreal' :
          withTopRealPart f (pathFull α) + -α * inner ℝ (partialGradientFst f (pathFull α)) h.fst ≤
            withTopRealPart f (pathSnd α) := by
        exact_mod_cast hslice_ineq'
      have hreal'' :
          withTopRealPart f (pathFull α) -
              α * inner ℝ (partialGradientFst f (pathFull α)) h.fst ≤
            withTopRealPart f (pathSnd α) := by
        simpa [sub_eq_add_neg] using hreal'
      linarith
    have hdiff :
        withTopRealPart f (pathFull α) - withTopRealPart f (pathSnd α) ≤
          α * inner ℝ (partialGradientFst f (pathFull α)) h.fst := by
      linarith
    exact (div_le_iff₀ hαpos).2 (by simpa [q, pathFull, pathSnd, mul_comm] using hdiff)
  have hpathSnd_pair :
      Tendsto
        (fun α : ℝ ↦ inner ℝ (partialGradientFst f (pathSnd α)) h.fst)
        (𝓝[>] (0 : ℝ)) (𝓝 (inner ℝ (partialGradientFst f zBar) h.fst)) := by
    -- The continuous partial gradient pulls the nearby slice gradient back to the base pairing.
    have hvec :
        Tendsto (fun α : ℝ ↦ partialGradientFst f (pathSnd α))
          (𝓝[>] (0 : ℝ)) (𝓝 (partialGradientFst f zBar)) :=
      hcont.tendsto.comp hpathSnd
    have hinner_cont : Continuous fun u : E₁ ↦ inner ℝ u h.fst := by
      fun_prop
    exact hinner_cont.continuousAt.tendsto.comp hvec
  have hpathFull_pair :
      Tendsto
        (fun α : ℝ ↦ inner ℝ (partialGradientFst f (pathFull α)) h.fst)
        (𝓝[>] (0 : ℝ)) (𝓝 (inner ℝ (partialGradientFst f zBar) h.fst)) := by
    -- The same continuity argument works along the full path.
    have hvec :
        Tendsto (fun α : ℝ ↦ partialGradientFst f (pathFull α))
          (𝓝[>] (0 : ℝ)) (𝓝 (partialGradientFst f zBar)) :=
      hcont.tendsto.comp hpathFull
    have hinner_cont : Continuous fun u : E₁ ↦ inner ℝ u h.fst := by
      fun_prop
    exact hinner_cont.continuousAt.tendsto.comp hvec
  simpa [q, pathFull, pathSnd] using
    (tendsto_of_tendsto_of_tendsto_of_le_of_le'
      hpathSnd_pair hpathFull_pair hlower hupper)

/-- Helper for Lemma 3.9: the full directional derivative splits into the first-coordinate
pairing and the directional derivative of the frozen-first slice. -/
lemma full_directionalDerivative_eq_partialGradientFst_add_snd_slice
    {f : Z → WithTop ℝ}
    (hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    {zBar : Z} (hzBar : zBar ∈ interior (dom f))
    (hgrad : ∀ᶠ z in 𝓝 zBar,
      HasGradientAt
        (withTopRealPart fun x ↦ f (toZ (x, z.snd)))
        (partialGradientFst f z) z.fst)
    (hcont : ContinuousAt (partialGradientFst f) zBar)
    {hyBar : zBar.snd ∈ interior (dom (fun y : E₂ ↦ f (toZ (zBar.fst, y))))}
    (h : Z) :
    f′[hzBar] h =
      inner ℝ (partialGradientFst f zBar) h.fst +
        ((fun y : E₂ ↦ f (toZ (zBar.fst, y)))′[hyBar] h.snd) := by
  let pathSnd : ℝ → Z := fun α ↦ toZ (zBar.fst, zBar.snd + α • h.snd)
  let qFull : ℝ → ℝ := fun α ↦
    (withTopRealPart f (zBar + α • h) - withTopRealPart f zBar) / α
  let qFst : ℝ → ℝ := fun α ↦
    (withTopRealPart f (zBar + α • h) - withTopRealPart f (pathSnd α)) / α
  let qSnd : ℝ → ℝ := fun α ↦
    (withTopRealPart f (pathSnd α) - withTopRealPart f zBar) / α
  have hfst :
      Tendsto qFst (𝓝[>] (0 : ℝ)) (𝓝 (inner ℝ (partialGradientFst f zBar) h.fst)) := by
    simpa [qFst, pathSnd] using
      fst_slice_secant_tendsto_partialGradientFst_pairing hf hzBar hgrad hcont h
  have hsnd :
      Tendsto qSnd (𝓝[>] (0 : ℝ))
        (𝓝 ((fun y : E₂ ↦ f (toZ (zBar.fst, y)))′[hyBar] h.snd)) := by
    simpa [qSnd, pathSnd] using
      directionalSecantQuotient_tendsto_of_mem_interior
        (snd_slice_convexOn hf zBar.fst) hyBar h.snd
  have hsum :
      Tendsto (fun α : ℝ ↦ qFst α + qSnd α) (𝓝[>] (0 : ℝ))
        (𝓝
          (inner ℝ (partialGradientFst f zBar) h.fst +
            (fun y : E₂ ↦ f (toZ (zBar.fst, y)))′[hyBar] h.snd)) :=
    hfst.add hsnd
  have hsplit : ∀ α : ℝ, qFull α = qFst α + qSnd α := by
    intro α
    dsimp [qFull, qFst, qSnd]
    ring
  have hfull' :
      Tendsto qFull (𝓝[>] (0 : ℝ))
        (𝓝
          (inner ℝ (partialGradientFst f zBar) h.fst +
            (fun y : E₂ ↦ f (toZ (zBar.fst, y)))′[hyBar] h.snd)) := by
    exact hsum.congr' (Filter.Eventually.of_forall fun α ↦ (hsplit α).symm)
  have hfull :
      Tendsto qFull (𝓝[>] (0 : ℝ)) (𝓝 (f′[hzBar] h)) := by
    simpa [qFull] using directionalSecantQuotient_tendsto_of_mem_interior hf hzBar h
  exact tendsto_nhds_unique hfull hfull'

omit [CompleteSpace E₁] in
/-- Helper for Lemma 3.9: every element of the second partial subdifferential is bounded above by
the directional derivative of the frozen-first slice. -/
lemma partialSubdifferentialSnd_pairing_le_directionalDerivative
    {f : Z → WithTop ℝ}
    (hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    {zBar : Z}
    {hyBar : zBar.snd ∈ interior (dom (fun y : E₂ ↦ f (toZ (zBar.fst, y))))}
    {g : E₂} (hg : g ∈ partialSubdifferentialSnd f zBar) :
    ∀ p : E₂,
      inner ℝ g p ≤ ((fun y : E₂ ↦ f (toZ (zBar.fst, y)))′[hyBar] p) := by
  intro p
  -- Pass the slice subgradient inequality to the right-limit of the corresponding secant quotient.
  have hslice := mem_subdifferential_iff.mp (by simpa [partialSubdifferentialSnd] using hg)
  have hpath :
      Tendsto (fun α : ℝ ↦ zBar.snd + α • p) (𝓝[>] (0 : ℝ)) (𝓝 zBar.snd) := by
    have hcont_path : ContinuousAt (fun α : ℝ ↦ zBar.snd + α • p) (0 : ℝ) := by
      fun_prop
    simpa [zero_smul] using hcont_path.tendsto.mono_left inf_le_left
  have hdom :
      ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ),
        zBar.snd + α • p ∈ dom (fun y : E₂ ↦ f (toZ (zBar.fst, y))) := by
    exact (hpath.eventually (IsOpen.mem_nhds isOpen_interior hyBar)).mono fun α hα ↦
      interior_subset hα
  have hpos : ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), 0 < α := by
    simpa using
      (eventually_mem_nhdsWithin : ∀ᶠ α in 𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ), α ∈ Set.Ioi (0 : ℝ))
  have hineq :
      ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ),
        inner ℝ g p ≤
          (withTopRealPart (fun y : E₂ ↦ f (toZ (zBar.fst, y))) (zBar.snd + α • p) -
              withTopRealPart (fun y : E₂ ↦ f (toZ (zBar.fst, y))) zBar.snd) / α := by
    filter_upwards [hdom, hpos] with α hαdom hαpos
    have hsubineq :
        (fun y : E₂ ↦ f (toZ (zBar.fst, y))) (zBar.snd + α • p) ≥
          (fun y : E₂ ↦ f (toZ (zBar.fst, y))) zBar.snd +
            (inner ℝ g ((zBar.snd + α • p) - zBar.snd) : WithTop ℝ) :=
      hslice.2 hαdom
    have hreal :
        withTopRealPart (fun y : E₂ ↦ f (toZ (zBar.fst, y))) (zBar.snd + α • p) ≥
          withTopRealPart (fun y : E₂ ↦ f (toZ (zBar.fst, y))) zBar.snd +
            α * inner ℝ g p := by
      have hαslice_dom : zBar.snd + α • p ∈ dom (fun y : E₂ ↦ f (toZ (zBar.fst, y))) := by
        simpa using hαdom
      have hsubineq_real :
          withTopRealPart (fun y : E₂ ↦ f (toZ (zBar.fst, y))) zBar.snd +
              inner ℝ g ((zBar.snd + α • p) - zBar.snd) ≤
            withTopRealPart (fun y : E₂ ↦ f (toZ (zBar.fst, y))) (zBar.snd + α • p) := by
        rw [le_withTopRealPart_iff hαslice_dom]
        have hsubineq_le :
            (fun y : E₂ ↦ f (toZ (zBar.fst, y))) zBar.snd +
                (inner ℝ g ((zBar.snd + α • p) - zBar.snd) : WithTop ℝ) ≤
              (fun y : E₂ ↦ f (toZ (zBar.fst, y))) (zBar.snd + α • p) := by
          simpa using hsubineq
        have hbase0 :
            (((withTopRealPart (fun y : E₂ ↦ f (toZ (zBar.fst, y))) zBar.snd : ℝ) :
                WithTop ℝ)) =
              (fun y : E₂ ↦ f (toZ (zBar.fst, y))) zBar.snd :=
          coe_withTopRealPart hslice.mem_dom
        have hbase :
            (((withTopRealPart (fun y : E₂ ↦ f (toZ (zBar.fst, y))) zBar.snd +
                  inner ℝ g ((zBar.snd + α • p) - zBar.snd) : ℝ) : WithTop ℝ)) =
              (fun y : E₂ ↦ f (toZ (zBar.fst, y))) zBar.snd +
                (inner ℝ g ((zBar.snd + α • p) - zBar.snd) : WithTop ℝ) := by
          rw [WithTop.coe_add, hbase0]
        exact hbase.symm ▸ hsubineq_le
      have hinner : inner ℝ g ((zBar.snd + α • p) - zBar.snd) = α * inner ℝ g p := by
        simp [inner_smul_right]
      rw [hinner] at hsubineq_real
      simpa [add_comm] using hsubineq_real
    have hdiff :
        α * inner ℝ g p ≤
          withTopRealPart (fun y : E₂ ↦ f (toZ (zBar.fst, y))) (zBar.snd + α • p) -
            withTopRealPart (fun y : E₂ ↦ f (toZ (zBar.fst, y))) zBar.snd := by
      linarith
    exact (le_div_iff₀ hαpos).2 (by simpa [mul_comm] using hdiff)
  exact
    tendsto_le_of_eventuallyLE tendsto_const_nhds
      (directionalSecantQuotient_tendsto_of_mem_interior
        (snd_slice_convexOn hf zBar.fst) hyBar p)
      hineq

omit [CompleteSpace E₁] in
/-- Helper for Lemma 3.9: a full subgradient restricts to the first-coordinate slice subgradient
whose value is the first component of the ambient product vector. -/
lemma fst_component_mem_subdifferential_fst_slice
    {f : Z → WithTop ℝ} {zBar z : Z}
    (hz : z ∈ ∂ f(zBar)) :
    z.fst ∈ ∂ (fun x : E₁ ↦ f (toZ (x, zBar.snd)))(zBar.fst) := by
  -- Freeze the second coordinate in the ambient subgradient inequality.
  have hzsub := mem_subdifferential_iff.mp hz
  have hzBar_dom : zBar ∈ dom f := hzsub.mem_dom
  refine mem_subdifferential_iff.mpr ?_
  constructor
  · simpa using hzBar_dom
  · intro x hx
    have hslice_dom : toZ (x, zBar.snd) ∈ dom f := by
      simpa using hx
    have hineq := hzsub.2 hslice_dom
    simpa [WithLp.prod_inner_apply] using hineq

omit [CompleteSpace E₁] in
/-- Helper for Lemma 3.9: a full subgradient restricts to a second-coordinate partial
subgradient. -/
lemma snd_component_mem_partialSubdifferentialSnd
    {f : Z → WithTop ℝ} {zBar z : Z}
    (hz : z ∈ ∂ f(zBar)) :
    z.snd ∈ partialSubdifferentialSnd f zBar := by
  -- Freeze the first coordinate in the ambient subgradient inequality.
  have hzsub := mem_subdifferential_iff.mp hz
  have hzBar_dom : zBar ∈ dom f := hzsub.mem_dom
  refine mem_subdifferential_iff.mpr ?_
  constructor
  · simpa [partialSubdifferentialSnd] using hzBar_dom
  · intro y hy
    have hslice_dom : toZ (zBar.fst, y) ∈ dom f := by
      simpa using hy
    have hineq := hzsub.2 hslice_dom
    simpa [partialSubdifferentialSnd, WithLp.prod_inner_apply] using hineq

-- Proof sketch: split the directional increment of `f` into the first-variable increment at a
-- moving frozen second coordinate and the second-variable increment at the base first coordinate.
-- The neighborhood differentiability and continuity hypotheses identify the first term with the
-- pairing against `partialGradientFst f (x̄, ȳ)`, while convexity at an interior point turns the
-- second term into the support function of `partialSubdifferentialSnd f (x̄, ȳ)`.
/-- Lemma 3.9: generalized from the textbook `ℝⁿ × ℝᵐ` setting, at an interior point of the
effective domain of a convex function on the intrinsic product `WithLp 2 (E₁ × E₂)` of real
inner-product spaces, if the first-variable slice admits the displayed partial gradient in a
neighborhood of the base point `zBar`, then the full subdifferential at `zBar` is exactly the
image of the product of the singleton containing the first partial gradient with the second
partial subdifferential under the canonical `L²` product map. -/
theorem subdifferential_eq_image_partialGradientFst_partialSubdifferentialSnd_of_nhds
    {f : Z → WithTop ℝ}
    (hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    {zBar : Z}
    (hzBar : zBar ∈ interior (dom f))
    (hgrad : ∀ᶠ z in 𝓝 zBar,
      HasGradientAt
        (withTopRealPart fun x ↦ f (toZ (x, z.snd)))
        (partialGradientFst f z) z.fst)
    (hcont : ContinuousAt (partialGradientFst f) zBar) :
    ∂ f(zBar) =
      toZ ''
        (({partialGradientFst f zBar} : Set E₁) ×ˢ partialSubdifferentialSnd f zBar) :=
  by
    -- Route correction: the finite-dimensional max-formula route from `Theorem_3_21` is unavailable
    -- here, so we isolate the forward inclusion first and leave only the reverse directional-limit
    -- step for re-planning.
    apply Set.Subset.antisymm
    · intro z hz
      -- Restrict the ambient subgradient to the frozen first slice and identify
      -- its first component.
      have hzfst :
          z.fst ∈ ∂ (fun x : E₁ ↦ f (toZ (x, zBar.snd)))(zBar.fst) :=
        fst_component_mem_subdifferential_fst_slice hz
      have hzBar_grad :
          HasGradientAt
            (withTopRealPart fun x : E₁ ↦ f (toZ (x, zBar.snd)))
            (partialGradientFst f zBar) zBar.fst :=
        by
          simpa using (Filter.Eventually.self_of_nhds hgrad)
      have hzfst_eq : z.fst = partialGradientFst f zBar := by
        exact eq_gradient_of_mem_subdifferential_of_hasGradientAt
          (fst_slice_mem_interior_dom hzBar) hzBar_grad hzfst
      -- The same ambient subgradient inequality restricted to the frozen first coordinate gives
      -- membership in the second partial subdifferential.
      have hzsnd : z.snd ∈ partialSubdifferentialSnd f zBar :=
        snd_component_mem_partialSubdifferentialSnd hz
      refine ⟨(z.fst, z.snd), ?_, ?_⟩
      · exact ⟨by simp [hzfst_eq], hzsnd⟩
      · change toZ (WithLp.ofLp z) = z
        exact WithLp.toLp_ofLp (p := (2 : ENNReal)) z
    · rintro z ⟨⟨xg, g⟩, hxzg, rfl⟩
      rcases hxzg with ⟨hxg, hg⟩
      have hxg' : xg = partialGradientFst f zBar := by
        simpa using hxg
      subst xg
      let hyBar : zBar.snd ∈ interior (dom (fun y : E₂ ↦ f (toZ (zBar.fst, y)))) :=
        snd_slice_mem_interior_dom (f := f) hzBar
      -- Apply the ambient affine-support inequality and lower-bound the directional derivative by
      -- the split first-slice pairing plus the second-slice subgradient pairing.
      refine mem_subdifferential_iff.mpr ?_
      constructor
      · exact interior_subset hzBar
      · intro y hy
        let h : Z := y - zBar
        have hsupport :=
          directionalDerivative_affine_support_of_mem_interior hf hzBar hy
        have hsnd :
            inner ℝ g h.snd ≤ (fun y' : E₂ ↦ f (toZ (zBar.fst, y')))′[hyBar] h.snd :=
          partialSubdifferentialSnd_pairing_le_directionalDerivative
            (f := f) hf (hyBar := hyBar) hg h.snd
        have hdecomp :
            f′[hzBar] h =
              inner ℝ (partialGradientFst f zBar) h.fst +
                (fun y' : E₂ ↦ f (toZ (zBar.fst, y')))′[hyBar] h.snd :=
          full_directionalDerivative_eq_partialGradientFst_add_snd_slice
            (f := f) hf hzBar hgrad hcont (hyBar := hyBar) h
        have hdir_lower :
            inner ℝ (partialGradientFst f zBar) h.fst + inner ℝ g h.snd ≤ f′[hzBar] h := by
          rw [hdecomp]
          linarith
        have hreal :
            withTopRealPart f y ≥
              withTopRealPart f zBar +
                inner ℝ (toZ (partialGradientFst f zBar, g)) (y - zBar) := by
          have : withTopRealPart f y ≥
              withTopRealPart f zBar +
                (inner ℝ (partialGradientFst f zBar) h.fst + inner ℝ g h.snd) := by
            linarith
          simpa [h, WithLp.prod_inner_apply, add_assoc, add_left_comm, add_comm] using this
        rw [← coe_withTopRealPart hy, ← coe_withTopRealPart (interior_subset hzBar)]
        exact_mod_cast hreal

end Main

end
