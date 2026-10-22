/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_9
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_1
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_24
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_46

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open InnerProductSpace (toDualMap)

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/-- The penalty `x ↦ λ ‖x‖_α` built from the auxiliary seminorm `alpha`. -/
def alphaNormPenalty (alpha : Seminorm ℝ E) (lam : ℝ) : E → EReal :=
  fun x ↦ ((lam * alpha x : ℝ) : EReal)

-- Proof sketch: unfold `alphaNormPenalty`; the displayed scalar multiple of `alpha x` is exactly
-- its definition.
/-- Evaluating `alphaNormPenalty alpha λ` at `x` gives the scalar value `λ ‖x‖_α`. -/
@[simp] theorem alphaNormPenalty_apply
    (alpha : Seminorm ℝ E) (lam : ℝ) (x : E) :
    alphaNormPenalty alpha lam x = ((lam * alpha x : ℝ) : EReal) :=
  rfl

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Example 6.47 is `source-facing`: the proximal objective still uses the ambient Euclidean
structure on `E`, but the penalty is built from a second norm `‖·‖_α` on the same real vector
space. The canonical owner API already present in the project is the set-valued proximal mapping
`prox[...]`, the set-valued projection mapping `P[...]`, the support function `support_function`,
and mathlib's canonical seminorm ball API. The primitive data are the auxiliary seminorm
`alpha : Seminorm ℝ E`; the dual ball is a derived `bridge/view` set built from the support
function of the seminorm unit ball, and the projection side should stay on the chapter owner
`P[...]` rather than on a local chosen-projection wrapper. -/

/-- The closed dual unit ball `{y ∈ E | ‖y‖_{α,*} ≤ 1}` under the ambient Riesz identification
`y ↦ toDualMap ℝ E y`, defined through the support function of the canonical seminorm unit ball
`alpha.closedBall 0 1`. -/
def alphaDualUnitBall (alpha : Seminorm ℝ E) : Set E :=
  {y | support_function (alpha.closedBall 0 1) (toDualMap ℝ E y) ≤ 1}

-- Proof sketch: unfold `alphaDualUnitBall`; membership is definitionally the inequality
-- `support_function (alpha.closedBall 0 1) (toDualMap y) ≤ 1`.
/-- A point belongs to `alphaDualUnitBall alpha` exactly when its Riesz functional has auxiliary
dual norm at most `1`. -/
@[simp] theorem mem_alphaDualUnitBall_iff
    (alpha : Seminorm ℝ E) (y : E) :
    y ∈ alphaDualUnitBall alpha ↔
      support_function (alpha.closedBall 0 1) (toDualMap ℝ E y) ≤ 1 :=
  Iff.rfl

-- Proof sketch: the support-function inequality on the auxiliary unit ball is equivalent to saying
-- that the Riesz functional of `y` is pointwise dominated by the seminorm `alpha`; the positive
-- radius case is handled by normalization, and the zero-radius case uses arbitrarily large
-- positive dilations of `z`.
/-- Helper for Example 6.47: a vector lies in the auxiliary dual unit ball exactly when its Riesz
functional is pointwise dominated by the auxiliary seminorm. -/
theorem mem_alphaDualUnitBall_iff_le_seminorm
    (alpha : Seminorm ℝ E) (y : E) :
    y ∈ alphaDualUnitBall alpha ↔ ∀ z, (toDualMap ℝ E y) z ≤ alpha z := by
  constructor
  · intro hy z
    by_cases hz : alpha z = 0
    · -- When `alpha z = 0`, any positive multiple of `z` stays in the unit ball.
      by_cases hnonpos : (toDualMap ℝ E y) z ≤ 0
      · simpa [hz] using hnonpos
      · have hpos : 0 < (toDualMap ℝ E y) z := lt_of_not_ge hnonpos
        let t : ℝ := 1 + ((toDualMap ℝ E y) z)⁻¹
        have ht_pos : 0 < t := by
          dsimp [t]
          positivity
        have htz_mem : t • z ∈ alpha.closedBall 0 1 := by
          rw [Seminorm.mem_closedBall_zero, map_smul_eq_mul alpha, hz, mul_zero]
          exact zero_le_one
        have hmem :
            (((toDualMap ℝ E y) (t • z) : ℝ) : EReal) ∈
              (fun x : E ↦ (((toDualMap ℝ E y) x : ℝ) : EReal)) '' alpha.closedBall 0 1 := by
          exact ⟨t • z, htz_mem, rfl⟩
        have htz_le : (((toDualMap ℝ E y) (t • z) : ℝ) : EReal) ≤ (1 : EReal) := by
          rw [mem_alphaDualUnitBall_iff] at hy
          exact le_trans (le_sSup hmem) hy
        have htz_le_real : (toDualMap ℝ E y) (t • z) ≤ 1 := by
          exact_mod_cast htz_le
        have hcalc : t * (toDualMap ℝ E y) z = (toDualMap ℝ E y) z + 1 := by
          have hinner_pos : 0 < inner ℝ y z := by
            simpa [InnerProductSpace.toDualMap_apply_apply] using hpos
          have hmul : (inner ℝ y z)⁻¹ * inner ℝ y z = 1 := by
            exact inv_mul_cancel₀ hinner_pos.ne'
          calc
            t * (toDualMap ℝ E y) z =
                (toDualMap ℝ E y) z + (((toDualMap ℝ E y) z)⁻¹ * (toDualMap ℝ E y) z) := by
                  dsimp [t]
                  ring
            _ = (toDualMap ℝ E y) z + 1 := by
              simpa [InnerProductSpace.toDualMap_apply_apply] using congrArg (fun r : ℝ ↦ inner ℝ y z + r) hmul
        have hgt : 1 < (toDualMap ℝ E y) (t • z) := by
          calc
            1 < (toDualMap ℝ E y) z + 1 := by linarith
            _ = t * (toDualMap ℝ E y) z := hcalc.symm
            _ = (toDualMap ℝ E y) (t • z) := by
              rw [ContinuousLinearMap.map_smul]
              simp [smul_eq_mul, mul_comm]
        linarith
    · -- When `alpha z > 0`, normalize `z` into the auxiliary unit ball and scale back.
      have hz_pos : 0 < alpha z := lt_of_le_of_ne (apply_nonneg alpha z) (Ne.symm hz)
      have hunit_mem : (alpha z)⁻¹ • z ∈ alpha.closedBall 0 1 := by
        rw [Seminorm.mem_closedBall_zero, map_smul_eq_mul alpha]
        rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hz_pos.le), inv_mul_cancel₀ hz]
      have hmem :
          (((toDualMap ℝ E y) ((alpha z)⁻¹ • z) : ℝ) : EReal) ∈
            (fun x : E ↦ (((toDualMap ℝ E y) x : ℝ) : EReal)) '' alpha.closedBall 0 1 := by
        exact ⟨(alpha z)⁻¹ • z, hunit_mem, rfl⟩
      have hunit_le : (((toDualMap ℝ E y) ((alpha z)⁻¹ • z) : ℝ) : EReal) ≤ (1 : EReal) := by
        rw [mem_alphaDualUnitBall_iff] at hy
        exact le_trans (le_sSup hmem) hy
      have hunit_le_real : (toDualMap ℝ E y) ((alpha z)⁻¹ • z) ≤ 1 := by
        exact_mod_cast hunit_le
      have hscaled :
          alpha z * (toDualMap ℝ E y) ((alpha z)⁻¹ • z) ≤ alpha z := by
        simpa using mul_le_mul_of_nonneg_left hunit_le_real hz_pos.le
      have hz_repr : z = alpha z • ((alpha z)⁻¹ • z) := by
        rw [smul_smul, mul_inv_cancel₀ hz, one_smul]
      calc
        (toDualMap ℝ E y) z = (toDualMap ℝ E y) (alpha z • ((alpha z)⁻¹ • z)) := by
          exact congrArg (fun w : E ↦ (toDualMap ℝ E y) w) hz_repr
        _ = alpha z * (toDualMap ℝ E y) ((alpha z)⁻¹ • z) := by
          rw [ContinuousLinearMap.map_smul]
          rfl
        _ ≤ alpha z := hscaled
  · intro hy
    rw [mem_alphaDualUnitBall_iff, support_function_apply]
    -- Pointwise domination on the unit ball gives a uniform upper bound of `1`.
    refine sSup_le fun a ha ↦ ?_
    rcases ha with ⟨z, hz, rfl⟩
    have hz_le_one : alpha z ≤ 1 := by
      simpa [Seminorm.mem_closedBall_zero] using hz
    have hreal : (toDualMap ℝ E y) z ≤ 1 := le_trans (hy z) hz_le_one
    exact (show ((((toDualMap ℝ E y) z : ℝ) : EReal)) ≤ (1 : EReal) by
      exact_mod_cast hreal)

-- Proof sketch: `0` belongs to the dual unit ball because the support function of the auxiliary
-- unit ball vanishes at the zero functional.
/-- The dual unit ball of the auxiliary norm is nonempty. -/
theorem alphaDualUnitBall_nonempty (alpha : Seminorm ℝ E) :
    (alphaDualUnitBall alpha).Nonempty := by
  -- The zero functional is trivially dominated by every seminorm.
  refine ⟨0, ?_⟩
  rw [mem_alphaDualUnitBall_iff_le_seminorm]
  intro z
  have hz_nonneg : 0 ≤ alpha z := apply_nonneg alpha z
  simp [hz_nonneg]

-- Proof sketch: the map `y ↦ support_function (alpha.closedBall 0 1) (toDualMap ℝ E y)` is
-- continuous, so the sublevel set `{y | ... ≤ 1}` is closed.
/-- The dual unit ball of the auxiliary norm is closed in the ambient Euclidean topology. -/
theorem alphaDualUnitBall_isClosed (alpha : Seminorm ℝ E) :
    IsClosed (alphaDualUnitBall alpha) := by
  -- Rewrite the dual unit ball as an intersection of closed affine half-spaces.
  have hrepr :
      alphaDualUnitBall alpha = ⋂ z : E, {y : E | (toDualMap ℝ E z) y ≤ alpha z} := by
    ext y
    rw [mem_alphaDualUnitBall_iff_le_seminorm]
    simp [InnerProductSpace.toDualMap_apply_apply, real_inner_comm]
  rw [hrepr]
  refine isClosed_iInter fun z ↦ ?_
  exact isClosed_Iic.preimage (toDualMap ℝ E z).continuous

-- Proof sketch: `y ↦ support_function (alpha.closedBall 0 1) (toDualMap ℝ E y)` is convex, and
-- the unit sublevel set of a convex function is convex.
/-- The dual unit ball of the auxiliary norm is convex. -/
theorem alphaDualUnitBall_convex (alpha : Seminorm ℝ E) :
    Convex ℝ (alphaDualUnitBall alpha) := by
  intro y₁ hy₁ y₂ hy₂ a b ha hb hab
  rw [mem_alphaDualUnitBall_iff_le_seminorm] at hy₁ hy₂ ⊢
  intro z
  -- Domination is preserved under convex combinations because `toDualMap` is linear.
  have h₁ : a * (toDualMap ℝ E y₁) z ≤ a * alpha z :=
    mul_le_mul_of_nonneg_left (hy₁ z) ha
  have h₂ : b * (toDualMap ℝ E y₂) z ≤ b * alpha z :=
    mul_le_mul_of_nonneg_left (hy₂ z) hb
  calc
    (toDualMap ℝ E (a • y₁ + b • y₂)) z =
        a * (toDualMap ℝ E y₁) z + b * (toDualMap ℝ E y₂) z := by
          simp [InnerProductSpace.toDualMap_apply_apply, smul_eq_mul]
    _ ≤ a * alpha z + b * alpha z := add_le_add h₁ h₂
    _ = alpha z := by nlinarith [apply_nonneg alpha z, hab]

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

-- Proof sketch: this is the dual-ball support-function identity from the earlier chapter,
-- specialized to the auxiliary norm `alpha` and transported back to `E` through `toDualMap ℝ E`.
/-- The support function of the auxiliary dual unit ball recovers the auxiliary norm
`‖·‖_α`. -/
theorem support_function_alphaDualUnitBall_eq_alpha
    (alpha : Seminorm ℝ E) (x : E) :
    support_function (alphaDualUnitBall alpha) (toDualMap ℝ E x) = ((alpha x : ℝ) : EReal) :=
  by
  by_cases hx : x = 0
  · -- At the origin, the support function of a nonempty set is `0`.
    subst hx
    apply le_antisymm
    · rw [support_function_apply]
      refine sSup_le fun a ha ↦ ?_
      rcases ha with ⟨y, hy, rfl⟩
      simp
    · rw [support_function_apply]
      rcases alphaDualUnitBall_nonempty alpha with ⟨y, hy⟩
      exact le_sSup ⟨y, hy, by simp⟩
  · have hupper :
        support_function (alphaDualUnitBall alpha) (toDualMap ℝ E x) ≤ ((alpha x : ℝ) : EReal) := by
      rw [support_function_apply]
      -- Every dual-ball vector gives a pairing bounded by `alpha x`.
      refine sSup_le fun a ha ↦ ?_
      rcases ha with ⟨y, hy, rfl⟩
      have hy_dom : (toDualMap ℝ E y) x ≤ alpha x :=
        (mem_alphaDualUnitBall_iff_le_seminorm alpha y).mp hy x
      have hy_dom' : (toDualMap ℝ E x) y ≤ alpha x := by
        simpa [InnerProductSpace.toDualMap_apply_apply, real_inner_comm] using hy_dom
      exact (show ((((toDualMap ℝ E x) y : ℝ) : EReal)) ≤ (((alpha x : ℝ) : EReal)) by
        exact_mod_cast hy_dom')
    -- Hahn-Banach provides a dominated functional attaining `alpha x` at `x`.
    let f : E →ₗ.[ℝ] ℝ := LinearPMap.mkSpanSingleton x (alpha x) hx
    have hf_hom : ∀ c : ℝ, 0 < c → ∀ z, alpha (c • z) = c * alpha z := by
      intro c hc z
      rw [map_smul_eq_mul alpha, Real.norm_of_nonneg hc.le]
    have hf_add : ∀ z₁ z₂, alpha (z₁ + z₂) ≤ alpha z₁ + alpha z₂ := by
      intro z₁ z₂
      exact map_add_le_add alpha z₁ z₂
    have hf_le : ∀ z : f.domain, f z ≤ alpha z := by
      intro z
      rcases Submodule.mem_span_singleton.mp z.2 with ⟨c, hc⟩
      have hspan : c • x ∈ f.domain := by
        simpa [f] using Submodule.smul_mem (ℝ ∙ x) c (Submodule.mem_span_singleton_self x)
      let xdom : f.domain := ⟨x, by simp [f]⟩
      have hz_subtype : z = ⟨c • x, hspan⟩ := by
        apply Subtype.ext
        exact hc.symm
      have happly : f ⟨c • x, hspan⟩ = c * alpha x := by
        calc
          f ⟨c • x, hspan⟩ = f (c • xdom) := by rfl
          _ = c • f xdom := by rw [LinearPMap.map_smul]
          _ = c * alpha x := by
            rw [LinearPMap.mkSpanSingleton_apply ℝ ℝ hx (alpha x)]
            simp [smul_eq_mul]
      calc
        f z = c * alpha x := by rw [hz_subtype]; exact happly
        _ ≤ |c| * alpha x := by
          exact mul_le_mul_of_nonneg_right (le_abs_self c) (apply_nonneg alpha x)
        _ = alpha z := by
          rw [hz_subtype]
          simp [map_smul_eq_mul alpha, Real.norm_eq_abs]
    obtain ⟨g, hg_ext, hg_le⟩ := exists_extension_of_le_sublinear f alpha hf_hom hf_add hf_le
    let gCL : StrongDual ℝ E := ⟨g, g.continuous_of_finiteDimensional⟩
    have hgx : g x = alpha x := by
      let xdom : f.domain := ⟨x, by simp [f]⟩
      have hxeq := hg_ext xdom
      rw [LinearPMap.mkSpanSingleton_apply ℝ ℝ hx (alpha x)] at hxeq
      simpa using hxeq
    obtain ⟨y, hy_eq_toDual⟩ := (InnerProductSpace.toDual ℝ E).surjective gCL
    have hy_apply : ∀ z, (toDualMap ℝ E y) z = g z := by
      intro z
      have h := congrArg (fun φ : StrongDual ℝ E => φ z) hy_eq_toDual
      simpa [gCL, InnerProductSpace.toDual_apply_eq_toDualMap_apply] using h
    have hy_mem : y ∈ alphaDualUnitBall alpha := by
      rw [mem_alphaDualUnitBall_iff_le_seminorm]
      intro z
      rw [hy_apply z]
      exact hg_le z
    have hlower :
        ((alpha x : ℝ) : EReal) ≤ support_function (alphaDualUnitBall alpha) (toDualMap ℝ E x) := by
      rw [support_function_apply]
      have hxy : (toDualMap ℝ E x) y = alpha x := by
        calc
          (toDualMap ℝ E x) y = (toDualMap ℝ E y) x := by
            simp [InnerProductSpace.toDualMap_apply_apply, real_inner_comm]
          _ = g x := hy_apply x
          _ = alpha x := hgx
      have hmem :
          ((alpha x : ℝ) : EReal) ∈
            (fun u : E ↦ (((toDualMap ℝ E x) u : ℝ) : EReal)) '' alphaDualUnitBall alpha := by
        refine ⟨y, hy_mem, ?_⟩
        exact congrArg (fun t : ℝ => (t : EReal)) hxy
      exact le_sSup hmem
    exact le_antisymm hupper hlower

variable (alpha : Seminorm ℝ E)

-- Proof sketch: evaluate both sides pointwise, rewrite the support function of the dual unit ball
-- using `support_function_alphaDualUnitBall_eq_alpha`, and identify the remaining scalar product.
/-- Helper for Example 6.47: the auxiliary penalty is the scalar multiple of the support function of
its auxiliary dual unit ball. -/
theorem alphaNormPenalty_eq_smul_support_function_primal_alphaDualUnitBall
    (lam : ℝ) :
    alphaNormPenalty alpha lam = (((lam : ℝ) : EReal) • σ[alphaDualUnitBall alpha]) := by
  funext x
  -- Both functions evaluate to the same scalar multiple of `alpha x`.
  rw [alphaNormPenalty_apply, Pi.smul_apply, support_function_primal_apply,
    support_function_alphaDualUnitBall_eq_alpha]
  simp [EReal.coe_mul]

-- Proof sketch: rewrite `alphaNormPenalty alpha` as the support function of
-- `alphaDualUnitBall alpha` using `support_function_alphaDualUnitBall_eq_alpha`, then apply
-- Theorem 6.46 to that dual unit ball, then rewrite the resulting singleton through the
-- chapter projection owner `P[...]`.
/-- Example 6.47: let `f(x) = λ ‖x‖_α` for `λ > 0`, where the source norm `‖·‖_α` on the ambient
Euclidean space `E` is encoded by the canonical owner `alpha : Seminorm ℝ E`, and let
`C = {y ∈ E | ‖y‖_{α,*} ≤ 1}` be its dual unit ball under the Riesz identification `E ≃ E*`. Then
the proximal mapping of `f` is the affine image of the projection set
`P[alphaDualUnitBall alpha] (x / λ)` under `u ↦ x - λ • u`. This is the chapter's set-valued
rendering of the textbook identity `prox_{λ ‖·‖_α}(x) = x - λ P_C(x / λ)`. -/
theorem prox_alphaNormPenalty_eq_sub_smul_projection_mapping_alphaDualUnitBall
    (lam : ℝ) (hlam : 0 < lam) (x : E) :
    prox[alphaNormPenalty alpha lam] x =
      Set.image (fun u : E ↦ x - lam • u) (P[alphaDualUnitBall alpha] (lam⁻¹ • x)) := by
  let lamPos : PosReal := ⟨lam, hlam⟩
  have hprox_support :
      prox[alphaNormPenalty alpha lam] x =
        {x - lam •
          (metricProjectionOfComplete (alphaDualUnitBall alpha)
            (alphaDualUnitBall_nonempty alpha)
            (alphaDualUnitBall_isClosed alpha).isComplete
            (alphaDualUnitBall_convex alpha) (lam⁻¹ • x) : E)} := by
    -- Rewrite the penalty as a scaled support function and invoke Theorem 6.46.
    rw [alphaNormPenalty_eq_smul_support_function_primal_alphaDualUnitBall]
    simpa [lamPos] using
      prox_support_function_eq_singleton_sub_smul_metricProjection
        (C := alphaDualUnitBall alpha)
        (hC_nonempty := alphaDualUnitBall_nonempty alpha)
        (hC_complete := (alphaDualUnitBall_isClosed alpha).isComplete)
        (hC_convex := alphaDualUnitBall_convex alpha)
        lamPos x
  have hproj :
      P[alphaDualUnitBall alpha] (lam⁻¹ • x) =
        {(metricProjectionOfComplete (alphaDualUnitBall alpha)
            (alphaDualUnitBall_nonempty alpha)
            (alphaDualUnitBall_isClosed alpha).isComplete
            (alphaDualUnitBall_convex alpha) (lam⁻¹ • x) : E)} := by
    -- Rewrite the set-valued projection as the singleton of the metric projection.
    simpa [projectionPoint_eq_metricProjectionOfComplete
      (C := alphaDualUnitBall alpha)
      (hC_nonempty := alphaDualUnitBall_nonempty alpha)
      (hC_complete := (alphaDualUnitBall_isClosed alpha).isComplete)
      (hC_convex := alphaDualUnitBall_convex alpha)
      (hC_closed := alphaDualUnitBall_isClosed alpha)
      (lam⁻¹ • x)] using
        projection_mapping_eq_singleton_of_nonempty_closed_convex
          (C := alphaDualUnitBall alpha)
          (hC_nonempty := alphaDualUnitBall_nonempty alpha)
          (hC_closed := alphaDualUnitBall_isClosed alpha)
          (hC_convex := alphaDualUnitBall_convex alpha)
          (lam⁻¹ • x)
  rw [hprox_support, hproj, Set.image_singleton]

end
