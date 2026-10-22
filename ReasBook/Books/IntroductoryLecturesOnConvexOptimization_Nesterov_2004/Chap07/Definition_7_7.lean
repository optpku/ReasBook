/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

noncomputable section

open Metric
open scoped WithTopConvexAnalysis

/- Definition 7.7 lies in the real continuous-dual / convex-analysis domain.

Sampled owner-style declarations:
- project `_root_.subdifferential` in `Chap03/Definition_3_1_5`
- project `_root_.mem_subdifferential_iff` in `Chap03/Definition_3_1_5`
- mathlib `InnerProductSpace.toDual`
- mathlib `normSeminorm`

Best owner abstraction:
- source-facing: the seminorm-based dual closed ball on `StrongDual ℝ E` and the resulting
  asphericity condition
- core/canonical: the chapter owner `_root_.subdifferential`
- bridge/view: the direct dual affine-support set transported through `InnerProductSpace.toDual`

Primitive data:
- the affine lower-support inequality for a continuous linear functional `g : StrongDual ℝ E`
- the seminorm `p : Seminorm ℝ E` determining the dual ball

Derived API:
- `dualClosedBall`
- `SatisfiesAsphericityCondition`
- the `InnerProductSpace.toDual` comparison theorem that rewrites the origin case into the chapter
  owner `∂`

Source/core/bridge triage:
- source-facing: `dualClosedBall` and `SatisfiesAsphericityCondition`
- core/canonical: `_root_.subdifferential`
- bridge/view: the `toDual` membership equivalence theorems

The seminorm-based `StrongDual` ball is the genuinely new source-facing object here, while the
subdifferential owner already exists upstream in the chapter. This file therefore defines
Definition 7.7 directly as the dual-ball sandwich around the affine-support set it needs, and then
proves that, under the stronger inner-product-space hypotheses needed for
`InnerProductSpace.toDual`, the origin case is exactly the chapter owner `∂`. -/

variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/- The closed dual ball of radius `γ` for the seminorm `p`, written on continuous linear
functionals as the pointwise estimate `|g x| ≤ γ p x`. -/
def dualClosedBall (p : Seminorm ℝ E) (γ : ℝ) : Set (StrongDual ℝ E) :=
  {g | ∀ x : E, |g x| ≤ γ * p x}

/-- Membership in `dualClosedBall p γ` is exactly the defining dual support estimate. -/
@[simp] theorem mem_dualClosedBall_iff
    (p : Seminorm ℝ E) (γ : ℝ) (g : StrongDual ℝ E) :
    g ∈ dualClosedBall p γ ↔ ∀ x : E, |g x| ≤ γ * p x :=
  Iff.rfl

/-- For the ambient norm seminorm, `dualClosedBall` is exactly the operator-norm closed ball in
the continuous dual. -/
theorem dualClosedBall_normSeminorm_eq_closedBall
    (γ : ℝ) (hγ : 0 ≤ γ) :
    dualClosedBall (normSeminorm ℝ E) γ = closedBall (0 : StrongDual ℝ E) γ := by
  ext g
  rw [mem_dualClosedBall_iff]
  simp only [Metric.mem_closedBall, dist_eq_norm, coe_normSeminorm]
  have hg : ‖g‖ ≤ γ ↔ ∀ x : E, ‖g x‖ ≤ γ * ‖x‖ := ContinuousLinearMap.opNorm_le_iff hγ
  simpa using hg.symm

/-- Definition 7.7: positive scalars `γ₀ ≤ γ₁` satisfy the asphericity condition for `f` with
respect to the chosen seminorm `p` when the dual affine supports of `f` at the origin are
sandwiched between the corresponding dual closed balls of radii `γ₀` and `γ₁`. -/
def SatisfiesAsphericityCondition (f : E → ℝ) (p : Seminorm ℝ E) (γ₀ γ₁ : ℝ) : Prop :=
  0 < γ₀ ∧
    γ₀ ≤ γ₁ ∧
    dualClosedBall p γ₀ ⊆ {g : StrongDual ℝ E | ∀ y : E, f 0 + g y ≤ f y} ∧
    {g : StrongDual ℝ E | ∀ y : E, f 0 + g y ≤ f y} ⊆ dualClosedBall p γ₁

/-- In the ambient norm case `p = normSeminorm ℝ E`, Definition 7.7 recovers the operator-norm
closed-ball formulation around the same dual affine-support set. -/
theorem satisfiesAsphericityCondition_normSeminorm_iff
    (f : E → ℝ) (γ₀ γ₁ : ℝ) :
    SatisfiesAsphericityCondition f (normSeminorm ℝ E) γ₀ γ₁ ↔
      0 < γ₀ ∧
        γ₀ ≤ γ₁ ∧
        closedBall (0 : StrongDual ℝ E) γ₀ ⊆
          {g : StrongDual ℝ E | ∀ y : E, f 0 + g y ≤ f y} ∧
        {g : StrongDual ℝ E | ∀ y : E, f 0 + g y ≤ f y} ⊆
          closedBall (0 : StrongDual ℝ E) γ₁ := by
  constructor
  · rintro ⟨hγ₀, hγ₀γ₁, hlower, hupper⟩
    refine ⟨hγ₀, hγ₀γ₁, ?_, ?_⟩
    · simpa [dualClosedBall_normSeminorm_eq_closedBall, hγ₀.le] using hlower
    · have hγ₁ : 0 ≤ γ₁ := le_trans hγ₀.le hγ₀γ₁
      simpa [dualClosedBall_normSeminorm_eq_closedBall, hγ₁] using hupper
  · rintro ⟨hγ₀, hγ₀γ₁, hlower, hupper⟩
    refine ⟨hγ₀, hγ₀γ₁, ?_, ?_⟩
    · simpa [dualClosedBall_normSeminorm_eq_closedBall, hγ₀.le] using hlower
    · have hγ₁ : 0 ≤ γ₁ := le_trans hγ₀.le hγ₀γ₁
      simpa [dualClosedBall_normSeminorm_eq_closedBall, hγ₁] using hupper

section InnerProductBridge

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Under the Riesz identification, the dual affine-support inequality is exactly the chapter
subgradient predicate. -/
theorem dualAffineSupport_iff_isSubgradientAt
    {f : E → ℝ} {x : E} {g : StrongDual ℝ E} :
    (∀ y : E, f x + (g y - g x) ≤ f y) ↔
      IsSubgradientAt (fun y ↦ (f y : WithTop ℝ)) x ((InnerProductSpace.toDual ℝ E).symm g) := by
  constructor
  · intro hg
    refine ⟨by simp [withTopEffectiveDomain], ?_⟩
    intro y hy
    have hreal : f x + (g y - g x) ≤ f y := by
      simpa using hg y
    have htop : (((f x + (g y - g x) : ℝ) : WithTop ℝ) ≤ (f y : WithTop ℝ)) := by
      exact_mod_cast hreal
    simpa [map_sub, InnerProductSpace.toDual_symm_apply] using htop
  · intro hg y
    have htop := hg.2 (by simp [withTopEffectiveDomain] : y ∈ dom (fun z ↦ (f z : WithTop ℝ)))
    have htop' :
        (((f x + inner ℝ ((InnerProductSpace.toDual ℝ E).symm g) (y - x) : ℝ) :
            WithTop ℝ) ≤ (f y : WithTop ℝ)) := by
      simpa using htop
    have hreal : f x + inner ℝ ((InnerProductSpace.toDual ℝ E).symm g) (y - x) ≤ f y := by
      exact_mod_cast htop'
    simpa [map_sub, InnerProductSpace.toDual_symm_apply] using hreal

/-- Under the Riesz identification, the dual affine-support condition is exactly membership in the
chapter subdifferential `∂ (fun y ↦ (f y : WithTop ℝ))(x)`. -/
@[simp] theorem toDual_symm_mem_subdifferential_iff
    {f : E → ℝ} {x : E} {g : StrongDual ℝ E} :
    (InnerProductSpace.toDual ℝ E).symm g ∈ ∂ (fun y ↦ (f y : WithTop ℝ))(x) ↔
      ∀ y : E, f x + (g y - g x) ≤ f y := by
  rw [mem_subdifferential_iff]
  exact dualAffineSupport_iff_isSubgradientAt.symm

/-- At the origin, the chapter subdifferential bridge is exactly the source-facing affine-support
inequality from Definition 7.7. -/
@[simp] theorem toDual_symm_mem_subdifferential_zero_iff
    {f : E → ℝ} {g : StrongDual ℝ E} :
    (InnerProductSpace.toDual ℝ E).symm g ∈ ∂ (fun y ↦ (f y : WithTop ℝ))((0 : E)) ↔
      ∀ y : E, f 0 + g y ≤ f y := by
  rw [toDual_symm_mem_subdifferential_iff]
  constructor
  · intro hg y
    simpa using hg y
  · intro hg y
    simpa using hg y

/-- Under the stronger inner-product-space hypotheses needed for `InnerProductSpace.toDual`,
Definition 7.7 is exactly the chapter’s existing subdifferential ball-sandwich condition at the
origin. -/
theorem satisfiesAsphericityCondition_normSeminorm_iff_chapterSubdifferential
    (f : E → ℝ) (γ₀ γ₁ : ℝ) :
    SatisfiesAsphericityCondition f (normSeminorm ℝ E) γ₀ γ₁ ↔
      0 < γ₀ ∧
        γ₀ ≤ γ₁ ∧
        closedBall (0 : E) γ₀ ⊆ ∂ (fun y ↦ (f y : WithTop ℝ))((0 : E)) ∧
        ∂ (fun y ↦ (f y : WithTop ℝ))((0 : E)) ⊆ closedBall (0 : E) γ₁ := by
  constructor
  · rintro ⟨hγ₀, hγ₀γ₁, hlower, hupper⟩
    refine ⟨hγ₀, hγ₀γ₁, ?_, ?_⟩
    · intro x hx
      have hxDual : (InnerProductSpace.toDual ℝ E) x ∈ dualClosedBall (normSeminorm ℝ E) γ₀ := by
        rw [dualClosedBall_normSeminorm_eq_closedBall γ₀ hγ₀.le]
        simpa [Metric.mem_closedBall] using hx
      have hxSupport :
          (InnerProductSpace.toDual ℝ E) x ∈ {g : StrongDual ℝ E | ∀ y : E, f 0 + g y ≤ f y} :=
        hlower hxDual
      simpa using
        (toDual_symm_mem_subdifferential_zero_iff.mpr (by simpa using hxSupport) :
          (InnerProductSpace.toDual ℝ E).symm ((InnerProductSpace.toDual ℝ E) x) ∈
            ∂ (fun y ↦ (f y : WithTop ℝ))((0 : E)))
    · have hγ₁ : 0 ≤ γ₁ := le_trans hγ₀.le hγ₀γ₁
      intro x hx
      have hxSupport :
          (InnerProductSpace.toDual ℝ E) x ∈ {g : StrongDual ℝ E | ∀ y : E, f 0 + g y ≤ f y} := by
        exact toDual_symm_mem_subdifferential_zero_iff.mp (by simpa using hx)
      have hxDual : (InnerProductSpace.toDual ℝ E) x ∈ dualClosedBall (normSeminorm ℝ E) γ₁ :=
        hupper hxSupport
      rw [dualClosedBall_normSeminorm_eq_closedBall γ₁ hγ₁] at hxDual
      simpa [Metric.mem_closedBall] using hxDual
  · rintro ⟨hγ₀, hγ₀γ₁, hlower, hupper⟩
    refine ⟨hγ₀, hγ₀γ₁, ?_, ?_⟩
    · intro g hg
      rw [dualClosedBall_normSeminorm_eq_closedBall γ₀ hγ₀.le] at hg
      have hgSub :
          (InnerProductSpace.toDual ℝ E).symm g ∈ ∂ (fun y ↦ (f y : WithTop ℝ))((0 : E)) :=
        hlower (by simpa [Metric.mem_closedBall] using hg)
      simpa using
        (toDual_symm_mem_subdifferential_zero_iff.mp hgSub :
          ∀ y : E, f 0 + g y ≤ f y)
    · have hγ₁ : 0 ≤ γ₁ := le_trans hγ₀.le hγ₀γ₁
      intro g hg
      have hgSub :
          (InnerProductSpace.toDual ℝ E).symm g ∈ ∂ (fun y ↦ (f y : WithTop ℝ))((0 : E)) := by
        simpa using
          (toDual_symm_mem_subdifferential_zero_iff.mpr (by simpa using hg) :
            (InnerProductSpace.toDual ℝ E).symm g ∈ ∂ (fun y ↦ (f y : WithTop ℝ))((0 : E)))
      have hgBall :
          (InnerProductSpace.toDual ℝ E).symm g ∈ closedBall (0 : E) γ₁ :=
        hupper hgSub
      rw [dualClosedBall_normSeminorm_eq_closedBall γ₁ hγ₁]
      simpa [Metric.mem_closedBall] using hgBall

end InnerProductBridge
