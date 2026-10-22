/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_56

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Lemma 6.16 lies in the Chapter 6 restricted-duality / concavity domain.

Sampled owner declarations:
- `restrictedDualFunction` in `Definition_6_55`, the Chapter 6 owner of the restricted dual
  supremum;
- `scaledRestrictedDualFunction` in `Definition_6_56`, the Chapter 6 owner of the contracted
  restricted dual supremum;
- `AffineMap.lineMap` in mathlib, the canonical affine owner of the contraction
  `y = (1 - τ) • xBar + τ • x` used inside `scaledRestrictedDualFunction`;
- `ConcaveOn` in mathlib, the canonical concavity owner on a feasible set.

Best owner abstraction:
- source-facing: the interval estimate comparing the scaled and unscaled restricted dual
  functions;
- core/canonical: `restrictedDualFunction` and `scaledRestrictedDualFunction`;
- bridge/view: the real-valued specialization `fun x ↦ (F x : WithTop ℝ)`.

Primitive data:
- the feasible set `Q`;
- the real-valued concave function `F`;
- the feasible base point `xBar ∈ Q`;
- the contraction parameter `τ ∈ [0, 1]`;
- the dual vector `s`.

Derived API:
- the canonical restricted dual value
  `restrictedDualFunction Q (fun x ↦ (F x : WithTop ℝ)) ... s`;
- the canonical scaled restricted dual value
  `scaledRestrictedDualFunction Q (fun x ↦ (F x : WithTop ℝ)) ... τ s`;
- the interval comparison below.

The previous file rebuilt local `ℝ`-valued owners for the same restricted-dual suprema already
introduced in `Definition_6_55` and `Definition_6_56`. This refinement removes that duplicate
wheel, keeps the owner layer in the Chapter 6 canonical `WithTop ℝ` form, and presents Lemma 6.16
as the real-valued bridge obtained from the canonical lift `fun x ↦ (F x : WithTop ℝ)`.
-/

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Helper for Lemma 6.16: the `WithTop` lift of a real-valued function is finite everywhere. -/
private lemma mem_realLift_domain
    {F : E → ℝ} (x : E) :
    x ∈ withTopEffectiveDomain (fun y ↦ (F y : WithTop ℝ)) := by
  -- A real-valued function never hits `⊤` after coercion to `WithTop ℝ`.
  simp [withTopEffectiveDomain]

/-- Helper for Lemma 6.16: the restricted-dual maximand of the real lift vanishes at the base
point. -/
private lemma restrictedDualMaximand_self_eq_zero
    {F : E → ℝ} {xBar : E}
    (hxBarDom : xBar ∈ withTopEffectiveDomain (fun x ↦ (F x : WithTop ℝ)))
    (s : StrongDual ℝ E) :
    restrictedDualMaximand (fun x ↦ (F x : WithTop ℝ)) ⟨xBar, hxBarDom⟩ s ⟨xBar, hxBarDom⟩ = 0 := by
  -- At the base point, both the linear displacement and the function-value gap are zero.
  simp [restrictedDualMaximand, withTopRealPart, Function.comp_apply]

/-- Helper for Lemma 6.16: the base point always belongs to its contracted feasible image. -/
private lemma self_mem_lineMap_image
    {Q : Set E} {xBar : E} (hxBar : xBar ∈ Q) (τ : ℝ) :
    xBar ∈ (fun z ↦ AffineMap.lineMap xBar z τ) '' Q := by
  -- Contracting the segment from `xBar` to itself leaves the base point unchanged.
  refine ⟨xBar, hxBar, ?_⟩
  simp

/-- Helper for Lemma 6.16: every contracted affine gap is bounded by `τ` times the original
affine gap. -/
private lemma restrictedDualMaximand_lineMap_le_smul
    {Q : Set E} {F : E → ℝ} (hF : ConcaveOn ℝ Q F)
    {xBar x : E} (hxBar : xBar ∈ Q) (hx : x ∈ Q)
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (s : StrongDual ℝ E) :
    s (xBar - AffineMap.lineMap xBar x τ) + F xBar - F (AffineMap.lineMap xBar x τ) ≤
      τ * (s (xBar - x) + F xBar - F x) := by
  have hτ_nonneg : 0 ≤ τ := hτ.1
  have h_one_sub_nonneg : 0 ≤ 1 - τ := sub_nonneg.mpr hτ.2
  have hconcave :
      (1 - τ) * F xBar + τ * F x ≤ F (AffineMap.lineMap xBar x τ) := by
    -- Concavity controls the function value at the contracted point on the segment.
    simpa [AffineMap.lineMap_apply_module, smul_eq_mul] using
      hF.2 hxBar hx h_one_sub_nonneg hτ_nonneg (by ring)
  have hlinear :
      s (xBar - AffineMap.lineMap xBar x τ) = τ * s (xBar - x) := by
    -- The displacement from `xBar` to the contracted point is exactly `τ • (xBar - x)`.
    calc
      s (xBar - AffineMap.lineMap xBar x τ) = s (τ • (xBar - x)) := by
        congr 1
        simpa using AffineMap.left_vsub_lineMap xBar x τ
      _ = τ * s (xBar - x) := by
        simp [smul_eq_mul]
  -- Combine the linear scaling with the concavity estimate for the function-value gap.
  rw [hlinear]
  linarith

/-- Helper for Lemma 6.16: the scaled restricted dual function is bounded above by `τ` times the
unscaled restricted dual function. -/
private lemma scaledRestrictedDualFunction_le_mul_restrictedDualFunction
    {Q : Set E} {F : E → ℝ} (hF : ConcaveOn ℝ Q F)
    (xBarSub : ↥(Q ∩ withTopEffectiveDomain (fun x ↦ (F x : WithTop ℝ))))
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (s : StrongDual ℝ E) :
    scaledRestrictedDualFunction Q (fun x ↦ (F x : WithTop ℝ)) xBarSub τ s ≤
      (τ : WithTop ℝ) * restrictedDualFunction Q (fun x ↦ (F x : WithTop ℝ)) xBarSub s := by
  let scaledSet : Set (WithTop ℝ) :=
    Set.range fun y :
      ↥(((fun z ↦ AffineMap.lineMap (xBarSub : E) z τ) '' Q) ∩
        withTopEffectiveDomain (fun z ↦ (F z : WithTop ℝ))) ↦
        ((restrictedDualMaximand (fun z ↦ (F z : WithTop ℝ)) ⟨xBarSub, xBarSub.2.2⟩ s
          ⟨y, y.2.2⟩ : ℝ) : WithTop ℝ)
  have hscaled_nonempty : scaledSet.Nonempty := by
    let ySub :
        ↥(((fun z ↦ AffineMap.lineMap (xBarSub : E) z τ) '' Q) ∩
          withTopEffectiveDomain (fun x ↦ (F x : WithTop ℝ))) :=
      ⟨xBarSub, ⟨self_mem_lineMap_image xBarSub.2.1 τ, mem_realLift_domain (xBarSub : E)⟩⟩
    exact ⟨_, ⟨ySub, rfl⟩⟩
  rw [scaledRestrictedDualFunction_apply]
  change sSup scaledSet ≤
    (τ : WithTop ℝ) * restrictedDualFunction Q (fun x ↦ (F x : WithTop ℝ)) xBarSub s
  refine csSup_le hscaled_nonempty ?_
  rintro _ ⟨y, rfl⟩
  rcases y.2.1 with ⟨x, hxQ, hyEq⟩
  have hy : (y : E) = AffineMap.lineMap (xBarSub : E) x τ := by
    simpa using hyEq.symm
  have hxDom : x ∈ withTopEffectiveDomain (fun z ↦ (F z : WithTop ℝ)) :=
    mem_realLift_domain x
  let xSub : ↥(Q ∩ withTopEffectiveDomain (fun z ↦ (F z : WithTop ℝ))) := ⟨x, ⟨hxQ, hxDom⟩⟩
  have hpointwise :
      s ((xBarSub : E) - y) + F xBarSub - F y ≤
        τ * (s ((xBarSub : E) - x) + F xBarSub - F x) :=
    by
      simpa [hy] using
        restrictedDualMaximand_lineMap_le_smul hF xBarSub.2.1 hxQ hτ s
  have hpointwise_withTop :
      (((s ((xBarSub : E) - y) + F xBarSub - F y : ℝ) : WithTop ℝ)) ≤
        (τ : WithTop ℝ) *
          (((s ((xBarSub : E) - x) + F xBarSub - F x : ℝ) : WithTop ℝ)) := by
    exact_mod_cast hpointwise
  have hx_le :
      (((restrictedDualMaximand (fun z ↦ (F z : WithTop ℝ)) ⟨xBarSub, xBarSub.2.2⟩ s
          ⟨x, hxDom⟩ : ℝ) : WithTop ℝ)) ≤
        restrictedDualFunction Q (fun z ↦ (F z : WithTop ℝ)) xBarSub s := by
    -- The unscaled supremum dominates the value at every feasible comparison point.
    rw [restrictedDualFunction_apply]
    have hunscaled_bddAbove :
        BddAbove
          (Set.range fun y : ↥(Q ∩ withTopEffectiveDomain (fun z ↦ (F z : WithTop ℝ))) ↦
            ((restrictedDualMaximand (fun z ↦ (F z : WithTop ℝ)) ⟨xBarSub, xBarSub.2.2⟩ s
              ⟨y, y.2.2⟩ : ℝ) : WithTop ℝ)) := ⟨⊤, by
                intro b hb
                exact le_top⟩
    exact le_csSup hunscaled_bddAbove ⟨xSub, rfl⟩
  -- Push the pointwise contracted-gap estimate through the unscaled supremum.
  calc
    ((restrictedDualMaximand (fun z ↦ (F z : WithTop ℝ)) ⟨xBarSub, xBarSub.2.2⟩ s
        ⟨y, y.2.2⟩ : ℝ) : WithTop ℝ) =
        (((s ((xBarSub : E) - y) + F xBarSub - F y : ℝ) : WithTop ℝ)) := by
      simp [restrictedDualMaximand, withTopRealPart, Function.comp_apply]
    _ ≤ (τ : WithTop ℝ) * (((s ((xBarSub : E) - x) + F xBarSub - F x : ℝ) : WithTop ℝ)) :=
      hpointwise_withTop
    _ = (τ : WithTop ℝ) *
          (((restrictedDualMaximand (fun z ↦ (F z : WithTop ℝ)) ⟨xBarSub, xBarSub.2.2⟩ s
              ⟨x, hxDom⟩ : ℝ) : WithTop ℝ)) := by
      simp [restrictedDualMaximand, withTopRealPart, Function.comp_apply]
    _ ≤ (τ : WithTop ℝ) * restrictedDualFunction Q (fun z ↦ (F z : WithTop ℝ)) xBarSub s := by
      by_cases hτ_zero : τ = 0
      · simp [hτ_zero]
      · by_cases hsup_top :
            restrictedDualFunction Q (fun z ↦ (F z : WithTop ℝ)) xBarSub s = ⊤
        · rw [hsup_top]
          simp [hτ_zero]
        · let r : ℝ :=
            (restrictedDualFunction Q (fun z ↦ (F z : WithTop ℝ)) xBarSub s).untop hsup_top
          have hsup_eq :
              ((r : ℝ) : WithTop ℝ) =
                restrictedDualFunction Q (fun z ↦ (F z : WithTop ℝ)) xBarSub s := by
            simp [r]
          have hx_le_real :
              restrictedDualMaximand (fun z ↦ (F z : WithTop ℝ)) ⟨xBarSub, xBarSub.2.2⟩ s
                  ⟨x, hxDom⟩ ≤
                r := by
            exact_mod_cast (hsup_eq ▸ hx_le)
          have hmul_real :
              τ *
                  restrictedDualMaximand (fun z ↦ (F z : WithTop ℝ)) ⟨xBarSub, xBarSub.2.2⟩ s
                    ⟨x, hxDom⟩ ≤
                τ * r :=
            mul_le_mul_of_nonneg_left hx_le_real hτ.1
          have hmul_withTop :
              (τ : WithTop ℝ) *
                  (((restrictedDualMaximand (fun z ↦ (F z : WithTop ℝ)) ⟨xBarSub, xBarSub.2.2⟩ s
                      ⟨x, hxDom⟩ : ℝ) : WithTop ℝ)) ≤
                (τ : WithTop ℝ) * ((r : ℝ) : WithTop ℝ) := by
            exact_mod_cast hmul_real
          simpa [hsup_eq] using hmul_withTop

/-- Lemma 6.16: for a concave real-valued function `F` on `Q`, the scaled restricted dual
function of the canonical `WithTop` lift of `F` at `(τ, xBar)` lies between `0` and `τ` times the
unscaled restricted dual function. -/
-- Proof sketch: the lower bound comes from the feasible choice `x = xBar`, where the affine gap
-- is `0`. For the upper bound, write `y = (1 - τ) • xBar + τ • x`; concavity keeps `y` in `Q`,
-- and `F y ≥ (1 - τ) * F xBar + τ * F x` gives
-- `s (xBar - y) + F xBar - F y ≤ τ * (s (xBar - x) + F xBar - F x)` pointwise. Taking suprema
-- yields the claimed factor-`τ` estimate.
theorem scaledRestrictedDualFunction_mem_Icc_of_concaveOn
    {Q : Set E} {F : E → ℝ} (hF : ConcaveOn ℝ Q F)
    {xBar : E} (hxBar : xBar ∈ Q) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1)
    (s : StrongDual ℝ E) :
    scaledRestrictedDualFunction Q (fun x ↦ (F x : WithTop ℝ))
        ⟨xBar, by simp [hxBar, withTopEffectiveDomain]⟩ τ s ∈
      Set.Icc
        (0 : WithTop ℝ)
        (((τ : WithTop ℝ) *
          restrictedDualFunction Q (fun x ↦ (F x : WithTop ℝ))
            ⟨xBar, by simp [hxBar, withTopEffectiveDomain]⟩ s)) := by
  have hxBarDom : xBar ∈ withTopEffectiveDomain (fun x ↦ (F x : WithTop ℝ)) :=
    mem_realLift_domain xBar
  let xBarSub : ↥(Q ∩ withTopEffectiveDomain (fun x ↦ (F x : WithTop ℝ))) :=
    ⟨xBar, ⟨hxBar, hxBarDom⟩⟩
  refine Set.mem_Icc.mpr ?_
  constructor
  · -- The base point remains feasible for the contracted problem and gives zero affine gap.
    let scaledSet : Set (WithTop ℝ) :=
      Set.range fun y :
        ↥(((fun z ↦ AffineMap.lineMap (xBarSub : E) z τ) '' Q) ∩
          withTopEffectiveDomain (fun z ↦ (F z : WithTop ℝ))) ↦
          ((restrictedDualMaximand (fun z ↦ (F z : WithTop ℝ)) ⟨xBarSub, xBarSub.2.2⟩ s
            ⟨y, y.2.2⟩ : ℝ) : WithTop ℝ)
    have hscaled_bddAbove : BddAbove scaledSet := ⟨⊤, by
      intro b hb
      exact le_top⟩
    rw [scaledRestrictedDualFunction_apply]
    change (0 : WithTop ℝ) ≤ sSup scaledSet
    let ySub :
        ↥(((fun z ↦ AffineMap.lineMap (xBarSub : E) z τ) '' Q) ∩
          withTopEffectiveDomain (fun x ↦ (F x : WithTop ℝ))) :=
      ⟨xBarSub, ⟨self_mem_lineMap_image xBarSub.2.1 τ, mem_realLift_domain (xBarSub : E)⟩⟩
    have hzero :
        restrictedDualMaximand (fun x ↦ (F x : WithTop ℝ))
          ⟨(xBarSub : E), ySub.2.2⟩ s ⟨(xBarSub : E), ySub.2.2⟩ = 0 :=
      restrictedDualMaximand_self_eq_zero ySub.2.2 s
    have hyMem : (0 : WithTop ℝ) ∈ scaledSet := by
      refine ⟨ySub, ?_⟩
      simpa [scaledSet, ySub] using congrArg (fun t : ℝ ↦ ((t : ℝ) : WithTop ℝ)) hzero
    exact le_csSup hscaled_bddAbove hyMem
  · -- The upper endpoint comes from the pointwise line-map estimate pushed through `sSup`.
    simpa [xBarSub] using
      scaledRestrictedDualFunction_le_mul_restrictedDualFunction hF xBarSub hτ s
end
