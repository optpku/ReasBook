/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Corollary_5_1_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_24
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_2_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_2_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_2_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Lemma_5_2_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_2_2

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace
open scoped Gradient NewtonDecrement AuxiliaryCentralPathNewtonDecrement

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A linear tilt preserves the positive-definite-Hessian owner on `dom`. -/
instance auxiliaryCentralPathObjective_hasPositiveDefiniteHessianOn
    {dom : Set E} (f : E → ℝ) [HasPositiveDefiniteHessianOn dom f]
    (y0 : dom) (t : ℝ) :
    HasPositiveDefiniteHessianOn dom (auxiliaryCentralPathObjective f y0 t) where
  isPositive {x} hx := by
    simpa [auxiliaryCentralPathObjective_hessian_eq] using
      (HasPositiveDefiniteHessianOn.hessian_isPositive_of_mem hx : (hessian f x).IsPositive)
  posdef {x} hx {u} hu := by
    simpa [auxiliaryCentralPathObjective_hessian_eq] using
      (HasPositiveDefiniteHessianOn.posdef hx hu : 0 < inner ℝ u (hessian f x u))

/-- The Hessian of the tilted objective `ψ(t; ·)` is nondegenerate at every domain point once the
ambient objective carries the chapter's positive-definite-Hessian owner. -/
theorem auxiliaryCentralPathObjective_hessian_det_ne_zero
    {dom : Set E} (f : E → ℝ) [HasPositiveDefiniteHessianOn dom f]
    (y0 : dom) (t : ℝ) {y : E} (hy : y ∈ dom) :
    (hessian (auxiliaryCentralPathObjective f y0 t) y).det ≠ 0 := by
  have hdet : (hessian f y).det ≠ 0 := HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem hy
  simpa [auxiliaryCentralPathObjective_hessian_eq] using hdet

/-- The approximate centering condition for the tilted objective `ψ(t; ·)` at `y`, expressed as
the bound `λ_{ψ(t; ·)}(y) ≤ β / M_f`. -/
def satisfies_approximate_centering_condition
    {dom : Set E} (f : E → ℝ) [HasPositiveDefiniteHessianOn dom f]
    (y0 : dom) (t : ℝ) (y : E) (hy : y ∈ dom) (Mf : NNRealˣ)
    (β : ℝ) : Prop :=
  λ[auxiliaryCentralPathObjective f y0 t; y | hy] ≤ β / (Mf : ℝ)

/-- Expanding `satisfies_approximate_centering_condition` recovers the inequality
`λ_{ψ(t; ·)}(y) ≤ β / M_f`. -/
theorem satisfies_approximate_centering_condition_iff
    {dom : Set E} (f : E → ℝ) [HasPositiveDefiniteHessianOn dom f]
    (y0 : dom) (t : ℝ) (y : E) (hy : y ∈ dom) (Mf : NNRealˣ) (β : ℝ) :
    satisfies_approximate_centering_condition f y0 t y hy Mf β ↔
      λ[auxiliaryCentralPathObjective f y0 t; y | hy] ≤ β / (Mf : ℝ) :=
  Iff.rfl

/-- Helper for Theorem 5 2 3: the approximate centering predicate is invariant under replacing
the path parameter, point, and domain-membership proof by equal data. -/
private theorem satisfiesApproximateCenteringCondition_congr
    {dom : Set E} {f : E → ℝ} [HasPositiveDefiniteHessianOn dom f]
    {y0 : dom} {t t' : ℝ} {y y' : E} {hy : y ∈ dom} {hy' : y' ∈ dom}
    {Mf : NNRealˣ} {β : ℝ} (ht : t = t') (hyEq : y = y') :
    satisfies_approximate_centering_condition f y0 t y hy Mf β ↔
      satisfies_approximate_centering_condition f y0 t' y' hy' Mf β := by
  subst ht
  subst hyEq
  have hproof : hy = hy' := by
    apply Subsingleton.elim
  subst hproof
  rfl

/-- A linear tilt preserves the Chapter 5 self-concordance owner, so the updated path parameter
determines a canonical intermediate Newton step for `ψ(t₊; ·)` on the same domain. -/
theorem auxiliaryCentralPathObjective_isSelfConcordantOnWith
    {dom : Set E} (f : E → ℝ) (Mf : NNReal) [IsSelfConcordantOnWith dom Mf f]
    (y0 : dom) (t : ℝ) :
    IsSelfConcordantOnWith dom Mf (auxiliaryCentralPathObjective f y0 t) := by
  let hf : IsSelfConcordantOnWith dom Mf f := inferInstance
  simpa [auxiliaryCentralPathObjective, quadraticAffineObjective_zero_operator, add_comm,
    add_left_comm, add_assoc, sub_eq_add_neg, inner_smul_left, mul_comm, mul_left_comm,
    mul_assoc] using
    hf.add_quadraticAffineObjective 0 (-(t : ℝ) • ∇ f (y0 : E)) (0 : E →L[ℝ] E)
      ContinuousLinearMap.isPositive_zero

private instance pathFollowingUpdate_auxiliaryCentralPathObjective_isSelfConcordantOnWith
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    (y0 : dom) (t : ℝ) :
    IsSelfConcordantOnWith dom (Mf : NNReal) (auxiliaryCentralPathObjective f y0 t) :=
  auxiliaryCentralPathObjective_isSelfConcordantOnWith f (Mf : NNReal) y0 t

/-- The path-following map sending `(t, y)` to the intermediate Newton update `(t₊, y₊)` for the
tilted objective based at `y₀` and path increment parameter `γ`. -/
def pathFollowingUpdate
    {dom : Set E} (f : E → ℝ) (Mf : NNRealˣ) [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    (y0 : dom) (t : Set.Icc (0 : ℝ) 1) (y : E) (hy : y ∈ dom)
    (hObjectiveNorm :
      0 < HessianDualLocalNorm.ofPosDefMem f hy ((toDual ℝ E) (∇ f (y0 : E))))
    (gamma : ℝ) : ℝ × E :=
  let hMf : 0 < (Mf : ℝ) := by
    have hMfNNReal : 0 < (Mf : NNReal) := by
      exact pos_iff_ne_zero.mpr (Units.ne_zero Mf)
    exact_mod_cast hMfNNReal
  let denominator : Set.Ioi (0 : ℝ) :=
    ⟨(Mf : ℝ) * HessianDualLocalNorm.ofPosDefMem f hy ((toDual ℝ E) (∇ f (y0 : E))),
      mul_pos hMf hObjectiveNorm⟩
  let tPlus :=
    (t : ℝ) - gamma / (denominator : ℝ)
  (tPlus,
    selfConcordantNewtonNextPoint
      (auxiliaryCentralPathObjective f y0 tPlus)
      (Mf : NNReal) .intermediate y hy
      (auxiliaryCentralPathObjective_hessian_det_ne_zero f y0 tPlus hy))

/-- The centering threshold `β = τ² (1 + τ + τ / (1 + τ + τ²))` used in the path-following
small-step estimate. -/
def pathFollowingCenteringBeta (τ : ℝ) : ℝ :=
  τ ^ (2 : ℕ) * (1 + τ + τ / (1 + τ + τ ^ (2 : ℕ)))

/-- Expanding `pathFollowingCenteringBeta τ` recovers the textbook formula
`τ² (1 + τ + τ / (1 + τ + τ²))`. -/
theorem pathFollowingCenteringBeta_def (τ : ℝ) :
    pathFollowingCenteringBeta τ =
      τ ^ (2 : ℕ) * (1 + τ + τ / (1 + τ + τ ^ (2 : ℕ))) :=
  rfl

/-- The admissible path-parameter increment bound
`τ - τ² (1 + τ + τ / (1 + τ + τ²))` from `(5.2.15)`. -/
def pathFollowingGammaRadius (τ : ℝ) : ℝ :=
  τ - pathFollowingCenteringBeta τ

/-- Expanding `pathFollowingGammaRadius τ` gives the bound from `(5.2.15)`. -/
theorem pathFollowingGammaRadius_def (τ : ℝ) :
    pathFollowingGammaRadius τ =
      τ - τ ^ (2 : ℕ) * (1 + τ + τ / (1 + τ + τ ^ (2 : ℕ))) := by
  simp [pathFollowingGammaRadius, pathFollowingCenteringBeta]

/-- The coefficient
`κ(τ) = ((τ - 3β(τ)) (1 + β(τ))) / (2 (1 + β(τ) + β(τ)^2))`
appearing in the path-following decay estimate. -/
def pathFollowingKappa (τ : ℝ) : ℝ :=
  ((τ - 3 * pathFollowingCenteringBeta τ) * (1 + pathFollowingCenteringBeta τ)) /
    (2 * (1 + pathFollowingCenteringBeta τ + (pathFollowingCenteringBeta τ) ^ (2 : ℕ)))

-- Proof sketch: unfold `pathFollowingKappa`.
/-- Expanding `pathFollowingKappa τ` gives the textbook formula for `κ(τ)`. -/
theorem pathFollowingKappa_def (τ : ℝ) :
    pathFollowingKappa τ =
      ((τ - 3 * pathFollowingCenteringBeta τ) * (1 + pathFollowingCenteringBeta τ)) /
        (2 * (1 + pathFollowingCenteringBeta τ + (pathFollowingCenteringBeta τ) ^ (2 : ℕ))) := by
  -- This wrapper theorem is purely definitional.
  rfl

/-- A path-following process for the tilted objective based at `y₀`, started from `t₀ = 1` and
generated by repeated application of `𝒫_γ` with `γ = τ - β(τ)`. -/
structure SelfConcordantPathFollowingProcess
    {dom : Set E} (f : E → ℝ) (Mf : NNRealˣ) [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    (y0 : dom) (τ : ℝ) where
  /-- The path parameters `t_k`, constrained to lie in `[0, 1]`. -/
  t : ℕ → Set.Icc (0 : ℝ) 1
  /-- The path-following iterates `y_k`. -/
  y : ℕ → E
  /-- Every iterate belongs to the domain of the objective. -/
  mem_domain : ∀ k : ℕ, y k ∈ dom
  /-- At each iterate, the denominator `M_f ‖∇ f(y₀)‖*_{y_k}` in the scalar path update is
  strictly positive, so the textbook update formula for `t_{k+1}` is mathematically defined. -/
  objectiveNorm_pos :
    ∀ k : ℕ,
      0 <
        HessianDualLocalNorm.ofPosDefMem f (mem_domain k)
          ((toDual ℝ E) (∇ f (y0 : E)))
  /-- The initial path parameter is `t₀ = 1`. -/
  t_zero : (t 0 : ℝ) = 1
  /-- The initial iterate is the prescribed base point `y₀`. -/
  y_zero : y 0 = y0
  /-- Each successive pair `(t_{k+1}, y_{k+1})` is obtained from the path-following map
  `𝒫_γ(t_k, y_k)` with `γ = τ - β(τ)`. -/
  step_eq :
    ∀ k : ℕ,
      ((t (k + 1) : ℝ), y (k + 1)) =
        pathFollowingUpdate f Mf y0 (t k) (y k) (mem_domain k) (objectiveNorm_pos k)
          (pathFollowingGammaRadius τ)

/-- Helper for Theorem 5 2 3: the Hessian dual local norm for the tilted objective does not
depend on the tilt parameter because the Hessian is unchanged. -/
private theorem auxiliaryCentralPathObjective_dualLocalNorm_eq
    {dom : Set E} (f : E → ℝ) [HasPositiveDefiniteHessianOn dom f]
    (y0 : dom) {y : E} (hy : y ∈ dom) (t t' : ℝ) (g : StrongDual ℝ E) :
    HessianDualLocalNorm.ofPosDefMem (auxiliaryCentralPathObjective f y0 t') hy g =
      HessianDualLocalNorm.ofPosDefMem (auxiliaryCentralPathObjective f y0 t) hy g := by
  -- Both sides reduce to the same inverse-Hessian quadratic form at the fixed point `y`.
  rw [HessianDualLocalNorm.ofPosDefMem_def, HessianDualLocalNorm.ofPosDefMem_def]
  simp [auxiliaryCentralPathObjective_hessian_eq]

/-- Helper for Theorem 5 2 3: at a fixed domain point, the Hessian dual local norm is
subadditive on covectors. -/
private theorem hessianDualLocalNorm_ofPosDefMem_add_le
    {dom : Set E} {F : E → ℝ} [HasPositiveDefiniteHessianOn dom F]
    {x : E} (hx : x ∈ dom) (g₁ g₂ : StrongDual ℝ E) :
    HessianDualLocalNorm.ofPosDefMem F hx (g₁ + g₂) ≤
      HessianDualLocalNorm.ofPosDefMem F hx g₁ +
        HessianDualLocalNorm.ofPosDefMem F hx g₂ := by
  let hPos : (hessian F x).IsPositive := HasPositiveDefiniteHessianOn.hessian_isPositive_of_mem hx
  let hH : (hessian F x).det ≠ 0 := HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem hx
  -- Route correction: reuse the public determinant-based dual-norm triangle inequality, then
  -- rewrite back to the `ofPosDefMem` owner.
  simpa [HessianDualLocalNorm.ofPosDefMem, HessianDualLocalNorm.ofDetNeZero, hPos, hH] using
    hessianDualLocalNorm_ofDetNeZero_add_le (F := F) (x := x) hPos hH g₁ g₂

/-- Helper for Theorem 5 2 3: fixed-point Hessian dual local norms pull out absolute scalar
factors from vectors viewed through the Riesz map. -/
private theorem hessianDualLocalNorm_ofPosDefMem_smul
    {dom : Set E} {F : E → ℝ} [HasPositiveDefiniteHessianOn dom F]
    {x : E} (hx : x ∈ dom) (v : E) (a : ℝ) :
    HessianDualLocalNorm.ofPosDefMem F hx ((toDual ℝ E) (a • v)) =
      |a| * HessianDualLocalNorm.ofPosDefMem F hx ((toDual ℝ E) v) := by
  let hPos : (hessian F x).IsPositive := HasPositiveDefiniteHessianOn.hessian_isPositive_of_mem hx
  let hH : (hessian F x).det ≠ 0 := HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem hx
  -- Rewrite the local owner through the determinant-based public homogeneity lemma.
  simpa [HessianDualLocalNorm.ofPosDefMem, HessianDualLocalNorm.ofDetNeZero, hPos, hH] using
    hessianDualLocalNorm_ofDetNeZero_smul (F := F) (x := x) hPos hH ((toDual ℝ E) v) a

/-- Helper for Theorem 5 2 3: at a positive-definite base point, the Euclidean pairing is
controlled by the Hessian dual local norm times the corresponding Hessian local norm. -/
private theorem abs_toDual_apply_le_dualLocalNorm_mul_hessianLocalNorm_ofPosDefMem
    {dom : Set E} {F : E → ℝ} [HasPositiveDefiniteHessianOn dom F]
    {x : E} (hx : x ∈ dom) (v z : E) :
    |inner ℝ v z| ≤
      HessianDualLocalNorm.ofPosDefMem F hx (toDual ℝ E v) * ‖z‖[F; x] := by
  let H := hessian F x
  let w := H.inverse v
  let hPos : H.IsPositive := HasPositiveDefiniteHessianOn.hessian_isPositive_of_mem hx
  let hInv : H.IsInvertible := hessian_isInvertible_of_det_ne_zero
    (HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem hx)
  have hHw : H w = v := by
    -- The inverse Hessian sends the chosen witness `w` back to the original vector `v`.
    dsimp [w, H]
    exact hInv.self_apply_inverse v
  have hquad : 0 ≤ inner ℝ z (H z) := hPos.inner_nonneg_right z
  have hpair_nonneg : 0 ≤ inner ℝ v w := by
    -- Rewrite the inverse-Hessian pairing as the positive quadratic form of `w`.
    calc
      0 ≤ inner ℝ w (H w) := hPos.inner_nonneg_right w
      _ = inner ℝ v w := by rw [hHw, real_inner_comm]
  have hline :
      ∀ t : ℝ,
        2 * t * inner ℝ v z - t ^ (2 : ℕ) * inner ℝ z (H z) ≤ inner ℝ v w := by
    intro t
    have hnonneg : 0 ≤ inner ℝ (t • z - w) (H (t • z - w)) := hPos.inner_nonneg_right (t • z - w)
    have hcross :
        inner ℝ w (H z) = inner ℝ v z := by
      -- Symmetry of the Hessian turns both mixed terms into the same base pairing.
      calc
        inner ℝ w (H z) = inner ℝ (H w) z := by
          simpa [real_inner_comm] using hPos.isSymmetric z w
        _ = inner ℝ v z := by rw [hHw]
    have hrewrite :
        inner ℝ (t • z - w) (H (t • z - w)) =
          t ^ (2 : ℕ) * inner ℝ z (H z) - 2 * t * inner ℝ v z + inner ℝ v w := by
      -- Expanding the quadratic form exposes the one-dimensional comparison family.
      have hleft :
          inner ℝ (t • z) (H w) = t * inner ℝ v z := by
        rw [hHw, real_inner_comm, inner_smul_right]
      have hright :
          inner ℝ w (t • H z) = t * inner ℝ v z := by
        rw [inner_smul_right, hcross]
      have hdiag :
          inner ℝ w (H w) = inner ℝ v w := by
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
      (inner ℝ v z) ^ (2 : ℕ) ≤ inner ℝ z (H z) * inner ℝ v w := by
    -- The quadratic family bound now yields the squared Cauchy inequality.
    have hsq :=
      sq_le_mul_of_quadratic_family (a := inner ℝ v z) (b := inner ℝ z (H z))
        (c := inner ℝ v w) hquad hline
    simpa [mul_comm] using hsq
  have hdual_sq :
      (HessianDualLocalNorm.ofPosDefMem F hx (toDual ℝ E v)) ^ (2 : ℕ) = inner ℝ v w := by
    -- Expand the dual local norm through the inverse Hessian witness `w`.
    rw [HessianDualLocalNorm.ofPosDefMem_def]
    simpa [w, H, pow_two, real_inner_comm, InnerProductSpace.toDual_apply_apply] using
      Real.sq_sqrt hpair_nonneg
  have hlocal_sq : ‖z‖[F; x] ^ (2 : ℕ) = inner ℝ z (H z) := by
    -- Squaring the local norm recovers the Hessian quadratic form at `x`.
    rw [hessianLocalNorm_def]
    simpa [H] using Real.sq_sqrt hquad
  have hsq_abs :
      |inner ℝ v z| ^ (2 : ℕ) ≤
        (HessianDualLocalNorm.ofPosDefMem F hx (toDual ℝ E v) * ‖z‖[F; x]) ^ (2 : ℕ) := by
    -- Translate the squared comparison back into the product of the two local norms.
    calc
      |inner ℝ v z| ^ (2 : ℕ) = (inner ℝ v z) ^ (2 : ℕ) := by rw [sq_abs]
      _ ≤ inner ℝ z (H z) * inner ℝ v w := hsq_raw
      _ =
          (HessianDualLocalNorm.ofPosDefMem F hx (toDual ℝ E v)) ^ (2 : ℕ) *
            ‖z‖[F; x] ^ (2 : ℕ) := by rw [hdual_sq, hlocal_sq, mul_comm]
      _ =
          (HessianDualLocalNorm.ofPosDefMem F hx (toDual ℝ E v) * ‖z‖[F; x]) ^ (2 : ℕ) := by
            ring
  have hdual_nonneg : 0 ≤ HessianDualLocalNorm.ofPosDefMem F hx (toDual ℝ E v) := by
    rw [HessianDualLocalNorm.ofPosDefMem_def]
    exact Real.sqrt_nonneg _
  exact le_of_sq_le_sq hsq_abs
    (mul_nonneg hdual_nonneg (hessianLocalNorm_nonneg F x z))

/-- Helper for Theorem 5 2 3: the base dual local norm of `∇ f(y₀)` at the current iterate. -/
private abbrev pathFollowingObjectiveNorm
    {dom : Set E} (f : E → ℝ) [HasPositiveDefiniteHessianOn dom f]
    (y0 : dom) (y : E) (hy : y ∈ dom) : ℝ :=
  HessianDualLocalNorm.ofPosDefMem f hy
    ((toDual ℝ E) (∇ f (y0 : E)))

/-- Helper for Theorem 5 2 3: changing the path parameter from `t` to `t'` changes the shifted
Newton decrement at a fixed point by at most `|t' - t| ‖∇ f(y₀)‖*_y`. -/
private theorem auxiliaryCentralPathObjective_decrement_le_add_objectiveNorm_mul_abs_sub
    {dom : Set E} {f : E → ℝ} [HasPositiveDefiniteHessianOn dom f]
    (y0 : dom) {y : E} (hy : y ∈ dom) (t t' : ℝ) :
    λ[auxiliaryCentralPathObjective f y0 t'; y | hy] ≤
      λ[auxiliaryCentralPathObjective f y0 t; y | hy] +
        |t' - t| * pathFollowingObjectiveNorm f y0 y hy := by
  let ψ := auxiliaryCentralPathObjective f y0 t
  let g0 := ∇ f (y0 : E)
  have ht' :
      λ[auxiliaryCentralPathObjective f y0 t'; y | hy] =
        HessianDualLocalNorm.ofPosDefMem ψ hy
          ((toDual ℝ E) (∇ f y - (t' : ℝ) • g0)) := by
    -- Rewrite the new decrement on the fixed Hessian surface of `ψ(t; ·)`.
    change
      HessianDualLocalNorm.ofPosDefMem (auxiliaryCentralPathObjective f y0 t') hy
        ((toDual ℝ E) (∇ (auxiliaryCentralPathObjective f y0 t') y)) = _
    rw [auxiliaryCentralPathObjective_dualLocalNorm_eq f y0 hy t t']
    simp [auxiliaryCentralPathObjective_gradient_eq, ψ, g0]
  have ht :
      λ[auxiliaryCentralPathObjective f y0 t; y | hy] =
        HessianDualLocalNorm.ofPosDefMem ψ hy
          ((toDual ℝ E) (∇ f y - (t : ℝ) • g0)) := by
    -- Expand the old decrement on the same fixed Hessian surface.
    simp [NewtonDecrement.ofPosDefMem, auxiliaryCentralPathObjective_gradient_eq, ψ, g0]
  have hsplit :
      ∇ f y - (t' : ℝ) • g0 =
        (∇ f y - (t : ℝ) • g0) + (t - t') • g0 := by
    -- The shifted gradients differ by a single affine perturbation term.
    rw [sub_smul]
    abel
  have hnorm_eq :
      HessianDualLocalNorm.ofPosDefMem ψ hy ((toDual ℝ E) g0) =
        pathFollowingObjectiveNorm f y0 y hy := by
    -- Setting the tilt parameter to `0` identifies the fixed Hessian surface with the original
    -- objective.
    rw [auxiliaryCentralPathObjective_dualLocalNorm_eq f y0 hy 0 t]
    simp [g0, pathFollowingObjectiveNorm, auxiliaryCentralPathObjective_hessian_eq]
  calc
    λ[auxiliaryCentralPathObjective f y0 t'; y | hy] =
        HessianDualLocalNorm.ofPosDefMem ψ hy
          (((toDual ℝ E) (∇ f y - (t : ℝ) • g0)) +
            ((toDual ℝ E) ((t - t') • g0))) := by
      rw [ht']
      congr 1
      rw [← map_add]
      simp [hsplit]
    _ ≤ HessianDualLocalNorm.ofPosDefMem ψ hy
          ((toDual ℝ E) (∇ f y - (t : ℝ) • g0)) +
        HessianDualLocalNorm.ofPosDefMem ψ hy
          ((toDual ℝ E) ((t - t') • g0)) := by
      exact hessianDualLocalNorm_ofPosDefMem_add_le hy _ _
    _ = λ[auxiliaryCentralPathObjective f y0 t; y | hy] +
        HessianDualLocalNorm.ofPosDefMem ψ hy
          ((toDual ℝ E) ((t - t') • g0)) := by
      rw [← ht]
    _ = λ[auxiliaryCentralPathObjective f y0 t; y | hy] +
        |t - t'| * HessianDualLocalNorm.ofPosDefMem ψ hy ((toDual ℝ E) g0) := by
      rw [hessianDualLocalNorm_ofPosDefMem_smul hy g0 (t - t')]
    _ = λ[auxiliaryCentralPathObjective f y0 t; y | hy] +
        |t' - t| * pathFollowingObjectiveNorm f y0 y hy := by
      rw [abs_sub_comm, hnorm_eq]

/-- Helper for Theorem 5 2 3: the first coordinate of the path-following update is the textbook
scalar update `t₊ = t - γ / (M_f ‖∇ f(y₀)‖*_y)`. -/
private theorem pathFollowingUpdate_fst
    {dom : Set E} (f : E → ℝ) (Mf : NNRealˣ) [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    (y0 : dom) (t : Set.Icc (0 : ℝ) 1) (y : E) (hy : y ∈ dom)
    (hObjectiveNorm :
      0 < HessianDualLocalNorm.ofPosDefMem f hy ((toDual ℝ E) (∇ f (y0 : E))))
    (gamma : ℝ) :
    (pathFollowingUpdate f Mf y0 t y hy hObjectiveNorm gamma).1 =
      (t : ℝ) - gamma / ((Mf : ℝ) *
        HessianDualLocalNorm.ofPosDefMem f hy ((toDual ℝ E) (∇ f (y0 : E)))) := by
  -- Unfold the update once so that the denominator is visible as the stated scalar product.
  simp [pathFollowingUpdate]

/-- Helper for Theorem 5 2 3: the second coordinate of the path-following update is the
intermediate Newton next point for the tilted objective at the updated parameter `t₊`. -/
private theorem pathFollowingUpdate_snd
    {dom : Set E} (f : E → ℝ) (Mf : NNRealˣ) [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    (y0 : dom) (t : Set.Icc (0 : ℝ) 1) (y : E) (hy : y ∈ dom)
    (hObjectiveNorm :
      0 < HessianDualLocalNorm.ofPosDefMem f hy ((toDual ℝ E) (∇ f (y0 : E))))
    (gamma : ℝ) :
    (pathFollowingUpdate f Mf y0 t y hy hObjectiveNorm gamma).2 =
      selfConcordantNewtonNextPoint
        (auxiliaryCentralPathObjective f y0
          ((pathFollowingUpdate f Mf y0 t y hy hObjectiveNorm gamma).1))
        (Mf : NNReal) .intermediate y hy
        (auxiliaryCentralPathObjective_hessian_det_ne_zero f y0
          ((pathFollowingUpdate f Mf y0 t y hy hObjectiveNorm gamma).1) hy) := by
  -- Unfold the pair and read off the second component directly.
  simp [pathFollowingUpdate]

/-- Helper for Theorem 5 2 3: the admissible increment radius `γ(τ)` is nonnegative on the
numerical regime `0 ≤ τ ≤ 0.23`. -/
private theorem pathFollowingGammaRadius_nonneg
    {τ : ℝ} (hτ_nonneg : 0 ≤ τ) (htau : τ ≤ 0.23) :
    0 ≤ pathFollowingGammaRadius τ := by
  -- Bound the fractional term by `τ`, so the centering correction is at most `τ² (1 + 2τ)`.
  have hden_ge_one : 1 ≤ 1 + τ + τ ^ (2 : ℕ) := by
    nlinarith [sq_nonneg τ]
  have hfrac_le : τ / (1 + τ + τ ^ (2 : ℕ)) ≤ τ := by
    have hden_pos : 0 < 1 + τ + τ ^ (2 : ℕ) := by positivity
    refine (div_le_iff₀ hden_pos).2 ?_
    nlinarith
  have hbeta_le :
      pathFollowingCenteringBeta τ ≤ τ ^ (2 : ℕ) * (1 + 2 * τ) := by
    rw [pathFollowingCenteringBeta_def]
    have hsq_nonneg : 0 ≤ τ ^ (2 : ℕ) := sq_nonneg τ
    calc
      τ ^ (2 : ℕ) * (1 + τ + τ / (1 + τ + τ ^ (2 : ℕ))) ≤
          τ ^ (2 : ℕ) * (1 + τ + τ) := by
            gcongr
      _ = τ ^ (2 : ℕ) * (1 + 2 * τ) := by ring
  calc
    0 ≤ τ - τ ^ (2 : ℕ) * (1 + 2 * τ) := by
          nlinarith
    _ ≤ pathFollowingGammaRadius τ := by
          rw [pathFollowingGammaRadius]
          linarith

/-- Helper for Theorem 5 2 3: the scaled shifted decrement bound `M_f δ ≤ τ ≤ 1 / 2` implies the
smallness condition required by the public intermediate-step theorem. -/
private theorem pathFollowingIntermediateSmallness_of_scaled_le_half
    {Mf : NNRealˣ} {δ τ : ℝ} (hδ_nonneg : 0 ≤ δ) (hscaled : (Mf : ℝ) * δ ≤ τ)
    (htau : τ ≤ 1 / 2) :
    (Mf : ℝ) * δ + (Mf : ℝ) ^ (2 : ℕ) * δ ^ (2 : ℕ) +
      (Mf : ℝ) ^ (3 : ℕ) * δ ^ (3 : ℕ) ≤ 1 := by
  let s : ℝ := (Mf : ℝ) * δ
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero Mf))
  have hs_nonneg : 0 ≤ s := by
    exact mul_nonneg (le_of_lt hMf_pos) hδ_nonneg
  have hs_le_half : s ≤ 1 / 2 := le_trans hscaled htau
  have hcore : s + s ^ (2 : ℕ) + s ^ (3 : ℕ) ≤ 1 := by
    nlinarith
  have hs_eq :
      s + s ^ (2 : ℕ) + s ^ (3 : ℕ) =
        (Mf : ℝ) * δ + (Mf : ℝ) ^ (2 : ℕ) * δ ^ (2 : ℕ) +
          (Mf : ℝ) ^ (3 : ℕ) * δ ^ (3 : ℕ) := by
    simp [s]
    ring
  rw [hs_eq] at hcore
  exact hcore

/-- Helper for Theorem 5 2 3: the explicit intermediate-step bound from Theorem 5.2.2 is
dominated by `β(τ) / M_f` once `M_f δ ≤ τ ≤ 1 / 2`. -/
private theorem pathFollowingExplicitIntermediateBound_le_centeringBeta_div
    {Mf : NNRealˣ} {δ τ : ℝ} (hδ_nonneg : 0 ≤ δ) (hscaled : (Mf : ℝ) * δ ≤ τ)
    (htau : τ ≤ 1 / 2) :
    ((Mf : ℝ) * δ ^ (2 : ℕ)) *
        (1 + (Mf : ℝ) * δ +
          ((Mf : ℝ) * δ) /
            (1 + (Mf : ℝ) * δ + (Mf : ℝ) ^ (2 : ℕ) * δ ^ (2 : ℕ))) ≤
      pathFollowingCenteringBeta τ / (Mf : ℝ) := by
  let s : ℝ := (Mf : ℝ) * δ
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero Mf))
  have hs_nonneg : 0 ≤ s := by
    exact mul_nonneg (le_of_lt hMf_pos) hδ_nonneg
  have hs_le : s ≤ τ := by
    simpa [s] using hscaled
  have hτ_nonneg : 0 ≤ τ := le_trans hs_nonneg hs_le
  have hden_s_pos : 0 < 1 + s + s ^ (2 : ℕ) := by positivity
  have hden_τ_pos : 0 < 1 + τ + τ ^ (2 : ℕ) := by positivity
  have hs_sq_le : s ^ (2 : ℕ) ≤ τ ^ (2 : ℕ) := by
    nlinarith
  have hfrac_le :
      s / (1 + s + s ^ (2 : ℕ)) ≤ τ / (1 + τ + τ ^ (2 : ℕ)) := by
    field_simp [hden_s_pos.ne', hden_τ_pos.ne']
    nlinarith
  have hbracket_le :
      1 + s + s / (1 + s + s ^ (2 : ℕ)) ≤
        1 + τ + τ / (1 + τ + τ ^ (2 : ℕ)) := by
    linarith
  have hmain :
      s ^ (2 : ℕ) * (1 + s + s / (1 + s + s ^ (2 : ℕ))) ≤
        τ ^ (2 : ℕ) * (1 + τ + τ / (1 + τ + τ ^ (2 : ℕ))) := by
    calc
      s ^ (2 : ℕ) * (1 + s + s / (1 + s + s ^ (2 : ℕ))) ≤
          s ^ (2 : ℕ) * (1 + τ + τ / (1 + τ + τ ^ (2 : ℕ))) := by
            gcongr
      _ ≤ τ ^ (2 : ℕ) * (1 + τ + τ / (1 + τ + τ ^ (2 : ℕ))) := by
            gcongr
  have hrewrite :
      ((Mf : ℝ) * δ ^ (2 : ℕ)) *
          (1 + (Mf : ℝ) * δ +
            ((Mf : ℝ) * δ) /
              (1 + (Mf : ℝ) * δ + (Mf : ℝ) ^ (2 : ℕ) * δ ^ (2 : ℕ))) =
        (s ^ (2 : ℕ) * (1 + s + s / (1 + s + s ^ (2 : ℕ)))) / (Mf : ℝ) := by
    -- Rewrite the coefficient through the scaled decrement `s = M_f δ`.
    dsimp [s]
    field_simp [hMf_pos.ne']
  rw [hrewrite, pathFollowingCenteringBeta_def]
  exact div_le_div_of_nonneg_right hmain (le_of_lt hMf_pos)

/-- Helper for Theorem 5 2 3: under the centering and step-size hypotheses, the updated iterate
produced by `pathFollowingUpdate` stays in `dom`. -/
private theorem pathFollowingUpdate_snd_mem
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f] [HasPositiveDefiniteHessianOn dom f]
    (y0 : dom) (t : Set.Icc (0 : ℝ) 1) {y : E} (hy : y ∈ dom) {τ gamma : ℝ}
    (hObjectiveNorm :
      0 < HessianDualLocalNorm.ofPosDefMem f hy ((toDual ℝ E) (∇ f (y0 : E))))
    (htau : τ ≤ 1 / 2)
    (hcenter : satisfies_approximate_centering_condition f y0 t y hy Mf
      (pathFollowingCenteringBeta τ))
    (hgamma : |gamma| ≤ pathFollowingGammaRadius τ) :
    (pathFollowingUpdate f Mf y0 t y hy hObjectiveNorm gamma).2 ∈ dom := by
  let tPlus := (pathFollowingUpdate f Mf y0 t y hy hObjectiveNorm gamma).1
  let ψ := auxiliaryCentralPathObjective f y0 tPlus
  let δ := λ[ψ; y | hy]
  have hδ_nonneg : 0 ≤ δ := NewtonDecrement.ofPosDefMem_nonneg ψ y hy
  have hcenter_old :
      λ[auxiliaryCentralPathObjective f y0 t; y | hy] ≤
        pathFollowingCenteringBeta τ / (Mf : ℝ) := by
    exact (satisfies_approximate_centering_condition_iff f y0 t y hy Mf
      (pathFollowingCenteringBeta τ)).1 hcenter
  have hδ_le_shifted :
      δ ≤ pathFollowingCenteringBeta τ / (Mf : ℝ) +
        |tPlus - (t : ℝ)| * pathFollowingObjectiveNorm f y0 y hy := by
    -- Compare the shifted decrement at `t₊` with the one at `t`, then insert the centering
    -- hypothesis.
    rw [show δ = λ[auxiliaryCentralPathObjective f y0 tPlus; y | hy] by rfl]
    calc
      λ[auxiliaryCentralPathObjective f y0 tPlus; y | hy] ≤
          λ[auxiliaryCentralPathObjective f y0 (t : ℝ); y | hy] +
            |tPlus - (t : ℝ)| * pathFollowingObjectiveNorm f y0 y hy := by
              simpa [tPlus] using
                auxiliaryCentralPathObjective_decrement_le_add_objectiveNorm_mul_abs_sub
                  (f := f) y0 hy (t : ℝ) tPlus
      _ ≤ pathFollowingCenteringBeta τ / (Mf : ℝ) +
          |tPlus - (t : ℝ)| * pathFollowingObjectiveNorm f y0 y hy := by
            gcongr
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero Mf))
  have hstep_eq :
      |tPlus - (t : ℝ)| * pathFollowingObjectiveNorm f y0 y hy =
        |gamma| / (Mf : ℝ) := by
    dsimp [tPlus]
    rw [pathFollowingUpdate_fst]
    have hObjectiveNorm_nonneg : 0 ≤ pathFollowingObjectiveNorm f y0 y hy := le_of_lt hObjectiveNorm
    calc
      |(t : ℝ) - gamma / ((Mf : ℝ) * pathFollowingObjectiveNorm f y0 y hy) - (t : ℝ)| *
          pathFollowingObjectiveNorm f y0 y hy =
          |(-gamma) / ((Mf : ℝ) * pathFollowingObjectiveNorm f y0 y hy)| *
            pathFollowingObjectiveNorm f y0 y hy := by
              congr 1
              ring
      _ = (|gamma| / ((Mf : ℝ) * pathFollowingObjectiveNorm f y0 y hy)) *
            pathFollowingObjectiveNorm f y0 y hy := by
              rw [abs_div, abs_neg, abs_mul, abs_of_pos hMf_pos,
                abs_of_nonneg hObjectiveNorm_nonneg]
      _ = |gamma| / (Mf : ℝ) := by
              field_simp [hMf_pos.ne', hObjectiveNorm.ne']
  have hδ_le_tau_div :
      δ ≤ τ / (Mf : ℝ) := by
    calc
      δ ≤ pathFollowingCenteringBeta τ / (Mf : ℝ) +
          |tPlus - (t : ℝ)| * pathFollowingObjectiveNorm f y0 y hy := hδ_le_shifted
      _ = pathFollowingCenteringBeta τ / (Mf : ℝ) + |gamma| / (Mf : ℝ) := by
            rw [hstep_eq]
      _ ≤ τ / (Mf : ℝ) := by
            have hsum :
                pathFollowingCenteringBeta τ + |gamma| ≤ τ := by
              calc
                pathFollowingCenteringBeta τ + |gamma| ≤
                    pathFollowingCenteringBeta τ + pathFollowingGammaRadius τ := by
                      gcongr
                _ = τ := by
                      simp [pathFollowingGammaRadius]
            simpa [add_div] using
              (div_le_div_of_nonneg_right hsum (le_of_lt hMf_pos))
  have hscaled : (Mf : ℝ) * δ ≤ τ := by
    simpa [mul_comm] using (le_div_iff₀ hMf_pos).mp hδ_le_tau_div
  have hsmall :
      (Mf : ℝ) * δ + (Mf : ℝ) ^ (2 : ℕ) * δ ^ (2 : ℕ) +
        (Mf : ℝ) ^ (3 : ℕ) * δ ^ (3 : ℕ) ≤ 1 := by
    simpa [δ] using
      pathFollowingIntermediateSmallness_of_scaled_le_half
        (Mf := Mf) hδ_nonneg hscaled htau
  obtain ⟨hyPlus, _, _⟩ :=
    selfConcordantNewton_mem_and_decrement_bounds_intermediate
      (Mf := Mf) (f := ψ) hy hsmall
  -- Rewrite the update point into the public intermediate Newton next-point owner.
  rw [pathFollowingUpdate_snd]
  exact hyPlus

/-- Helper for Theorem 5 2 3: one path-following update preserves the same approximate centering
condition when `τ ≤ 1 / 2` and `|γ| ≤ pathFollowingGammaRadius τ`. -/
private theorem pathFollowingUpdate_preserves_approximate_centering_condition
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f] [HasPositiveDefiniteHessianOn dom f]
    (y0 : dom) (t : Set.Icc (0 : ℝ) 1) {y : E} (hy : y ∈ dom) {τ gamma : ℝ}
    (hObjectiveNorm :
      0 < HessianDualLocalNorm.ofPosDefMem f hy ((toDual ℝ E) (∇ f (y0 : E))))
    (htau : τ ≤ 1 / 2)
    (hcenter : satisfies_approximate_centering_condition f y0 t y hy Mf
      (pathFollowingCenteringBeta τ))
    (hgamma : |gamma| ≤ pathFollowingGammaRadius τ) :
    satisfies_approximate_centering_condition f y0
      (pathFollowingUpdate f Mf y0 t y hy hObjectiveNorm gamma).1
      (pathFollowingUpdate f Mf y0 t y hy hObjectiveNorm gamma).2
      (pathFollowingUpdate_snd_mem y0 t hy hObjectiveNorm htau hcenter hgamma) Mf
      (pathFollowingCenteringBeta τ) := by
  let tPlus := (pathFollowingUpdate f Mf y0 t y hy hObjectiveNorm gamma).1
  let ψ := auxiliaryCentralPathObjective f y0 tPlus
  let δ := λ[ψ; y | hy]
  let yPlus :=
    selfConcordantNewtonNextPoint ψ (Mf : NNReal) .intermediate y hy
      (HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem (f := ψ) hy)
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero Mf))
  have hδ_nonneg : 0 ≤ δ := NewtonDecrement.ofPosDefMem_nonneg ψ y hy
  have hcenter_old :
      λ[auxiliaryCentralPathObjective f y0 t; y | hy] ≤
        pathFollowingCenteringBeta τ / (Mf : ℝ) := by
    exact (satisfies_approximate_centering_condition_iff f y0 t y hy Mf
      (pathFollowingCenteringBeta τ)).1 hcenter
  have hδ_le_shifted :
      δ ≤ pathFollowingCenteringBeta τ / (Mf : ℝ) +
        |tPlus - (t : ℝ)| * pathFollowingObjectiveNorm f y0 y hy := by
    -- Compare the shifted decrement at the updated parameter against the old centered point.
    calc
      δ ≤ λ[auxiliaryCentralPathObjective f y0 (t : ℝ); y | hy] +
          |tPlus - (t : ℝ)| * pathFollowingObjectiveNorm f y0 y hy := by
            have hshift_raw :
                λ[auxiliaryCentralPathObjective f y0 tPlus; y | hy] ≤
                  λ[auxiliaryCentralPathObjective f y0 (t : ℝ); y | hy] +
                    |tPlus - (t : ℝ)| * pathFollowingObjectiveNorm f y0 y hy :=
              auxiliaryCentralPathObjective_decrement_le_add_objectiveNorm_mul_abs_sub
                (f := f) y0 hy (t : ℝ) tPlus
            simpa [δ, ψ, tPlus] using hshift_raw
      _ ≤ pathFollowingCenteringBeta τ / (Mf : ℝ) +
          |tPlus - (t : ℝ)| * pathFollowingObjectiveNorm f y0 y hy := by
            gcongr
  have hstep_eq :
      |tPlus - (t : ℝ)| * pathFollowingObjectiveNorm f y0 y hy =
        |gamma| / (Mf : ℝ) := by
    dsimp [tPlus]
    rw [pathFollowingUpdate_fst]
    have hObjectiveNorm_nonneg : 0 ≤ pathFollowingObjectiveNorm f y0 y hy := le_of_lt hObjectiveNorm
    calc
      |(t : ℝ) - gamma / ((Mf : ℝ) * pathFollowingObjectiveNorm f y0 y hy) - (t : ℝ)| *
          pathFollowingObjectiveNorm f y0 y hy =
          |(-gamma) / ((Mf : ℝ) * pathFollowingObjectiveNorm f y0 y hy)| *
            pathFollowingObjectiveNorm f y0 y hy := by
              congr 1
              ring
      _ = (|gamma| / ((Mf : ℝ) * pathFollowingObjectiveNorm f y0 y hy)) *
            pathFollowingObjectiveNorm f y0 y hy := by
              rw [abs_div, abs_neg, abs_mul, abs_of_pos hMf_pos,
                abs_of_nonneg hObjectiveNorm_nonneg]
      _ = |gamma| / (Mf : ℝ) := by
              field_simp [hMf_pos.ne', hObjectiveNorm.ne']
  have hδ_le_tau_div :
      δ ≤ τ / (Mf : ℝ) := by
    calc
      δ ≤ pathFollowingCenteringBeta τ / (Mf : ℝ) +
          |tPlus - (t : ℝ)| * pathFollowingObjectiveNorm f y0 y hy := hδ_le_shifted
      _ = pathFollowingCenteringBeta τ / (Mf : ℝ) + |gamma| / (Mf : ℝ) := by
            rw [hstep_eq]
      _ ≤ τ / (Mf : ℝ) := by
            have hsum :
                pathFollowingCenteringBeta τ + |gamma| ≤ τ := by
              calc
                pathFollowingCenteringBeta τ + |gamma| ≤
                    pathFollowingCenteringBeta τ + pathFollowingGammaRadius τ := by
                      gcongr
                _ = τ := by
                      simp [pathFollowingGammaRadius]
            simpa [add_div] using
              (div_le_div_of_nonneg_right hsum (le_of_lt hMf_pos))
  have hscaled : (Mf : ℝ) * δ ≤ τ := by
    simpa [mul_comm] using (le_div_iff₀ hMf_pos).mp hδ_le_tau_div
  have hsmall :
      (Mf : ℝ) * δ + (Mf : ℝ) ^ (2 : ℕ) * δ ^ (2 : ℕ) +
        (Mf : ℝ) ^ (3 : ℕ) * δ ^ (3 : ℕ) ≤ 1 := by
    simpa [δ] using
      pathFollowingIntermediateSmallness_of_scaled_le_half
        (Mf := Mf) hδ_nonneg hscaled htau
  obtain ⟨hyPlus, hendpoint, _⟩ :=
    selfConcordantNewton_mem_and_decrement_bounds_intermediate
      (Mf := Mf) (f := ψ) hy hsmall
  have hcanonical :
      satisfies_approximate_centering_condition f y0 tPlus yPlus hyPlus Mf
        (pathFollowingCenteringBeta τ) := by
    -- Route correction: prove the endpoint bound in the canonical Newton-step spelling first.
    rw [satisfies_approximate_centering_condition_iff]
    exact le_trans hendpoint <|
      pathFollowingExplicitIntermediateBound_le_centeringBeta_div
        (Mf := Mf) hδ_nonneg hscaled htau
  have hyPlus_eq :
      yPlus =
        (pathFollowingUpdate f Mf y0 t y hy hObjectiveNorm gamma).2 := by
    -- The public intermediate endpoint and the path-following update differ only by proof fields.
    simpa [yPlus, ψ, tPlus] using
      (pathFollowingUpdate_snd f Mf y0 t y hy hObjectiveNorm gamma).symm
  exact
    (satisfiesApproximateCenteringCondition_congr
      (f := f) (y0 := y0) (t := tPlus)
      (t' := (pathFollowingUpdate f Mf y0 t y hy hObjectiveNorm gamma).1)
      (y := yPlus)
      (y' := (pathFollowingUpdate f Mf y0 t y hy hObjectiveNorm gamma).2)
      (hy := hyPlus)
      (hy' := pathFollowingUpdate_snd_mem y0 t hy hObjectiveNorm htau hcenter hgamma)
      (Mf := Mf) (β := pathFollowingCenteringBeta τ) rfl hyPlus_eq).mp hcanonical

/-- Helper for Theorem 5 2 3: the centering threshold `β(τ)` is nonnegative on the admissible
interval `0 ≤ τ`. -/
private theorem pathFollowingCenteringBeta_nonneg
    {τ : ℝ} (hτ_nonneg : 0 ≤ τ) :
    0 ≤ pathFollowingCenteringBeta τ := by
  -- Expanding `β(τ)` reduces the claim to a manifestly nonnegative rational expression.
  rw [pathFollowingCenteringBeta_def]
  positivity

/-- Helper for Theorem 5 2 3: the initial iterate `(t₀, y₀) = (1, y₀)` already satisfies the
approximate centering condition. -/
private theorem pathFollowingInitialCentering
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ} [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (hτ_nonneg : 0 ≤ τ) (y0 : dom) :
    satisfies_approximate_centering_condition f y0 1 (y0 : E) y0.2 Mf
      (pathFollowingCenteringBeta τ) := by
  have hβ_nonneg : 0 ≤ pathFollowingCenteringBeta τ :=
    pathFollowingCenteringBeta_nonneg hτ_nonneg
  rw [satisfies_approximate_centering_condition_iff]
  have hgrad :
      ∇ (auxiliaryCentralPathObjective f y0 1) (y0 : E) = 0 := by
    simp [auxiliaryCentralPathObjective_gradient_eq]
  have hdecrement :
      λ[auxiliaryCentralPathObjective f y0 1; (y0 : E) | y0.2] = 0 := by
    simp [NewtonDecrement.ofPosDefMem, hgrad]
  rw [hdecrement]
  positivity

/-- Helper for Theorem 5 2 3: the centering invariant is reduced to the initial iterate together
with the one-step path-following centering preservation lemma from Lemma 5.2.2. -/
private theorem pathFollowingCenteringInvariant
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ} [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (hτ_nonneg : 0 ≤ τ) (htau : τ ≤ 0.23) (y0 : dom)
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ) :
    ∀ k : ℕ,
      satisfies_approximate_centering_condition f y0 (process.t k) (process.y k)
        (process.mem_domain k) Mf (pathFollowingCenteringBeta τ) := by
  intro k
  induction k with
  | zero =>
      -- Rewrite the base state back to `(1, y₀)` and reuse the explicit initial centering proof.
      simpa [process.t_zero, process.y_zero] using
        pathFollowingInitialCentering hτ_nonneg y0 (Mf := Mf) (f := f) (τ := τ)
  | succ k ih =>
      have htau_half : τ ≤ 1 / 2 := by
        nlinarith
      have hgamma_nonneg : 0 ≤ pathFollowingGammaRadius τ :=
        pathFollowingGammaRadius_nonneg hτ_nonneg htau
      have hgamma :
          |pathFollowingGammaRadius τ| ≤ pathFollowingGammaRadius τ := by
        simpa [abs_of_nonneg hgamma_nonneg] using le_rfl
      have hupdate :
          satisfies_approximate_centering_condition f y0
            (pathFollowingUpdate f Mf y0 (process.t k) (process.y k)
              (process.mem_domain k) (process.objectiveNorm_pos k)
              (pathFollowingGammaRadius τ)).1
            (pathFollowingUpdate f Mf y0 (process.t k) (process.y k)
              (process.mem_domain k) (process.objectiveNorm_pos k)
              (pathFollowingGammaRadius τ)).2
            (pathFollowingUpdate_snd_mem y0 (process.t k) (process.mem_domain k)
              (process.objectiveNorm_pos k) htau_half ih hgamma)
            Mf (pathFollowingCenteringBeta τ) :=
        pathFollowingUpdate_preserves_approximate_centering_condition
          (f := f) (Mf := Mf) y0 (process.t k) (hy := process.mem_domain k)
          (hObjectiveNorm := process.objectiveNorm_pos k) (τ := τ)
          (gamma := pathFollowingGammaRadius τ) htau_half ih hgamma
      have ht :
          (pathFollowingUpdate f Mf y0 (process.t k) (process.y k)
            (process.mem_domain k) (process.objectiveNorm_pos k)
            (pathFollowingGammaRadius τ)).1 =
          (process.t (k + 1) : ℝ) := by
        exact congrArg Prod.fst (process.step_eq k).symm
      have hyEq :
          (pathFollowingUpdate f Mf y0 (process.t k) (process.y k)
            (process.mem_domain k) (process.objectiveNorm_pos k)
            (pathFollowingGammaRadius τ)).2 =
          process.y (k + 1) := by
        exact congrArg Prod.snd (process.step_eq k).symm
      exact
        (satisfiesApproximateCenteringCondition_congr
          (f := f) (y0 := y0)
          (t := (pathFollowingUpdate f Mf y0 (process.t k) (process.y k)
            (process.mem_domain k) (process.objectiveNorm_pos k)
            (pathFollowingGammaRadius τ)).1)
          (t' := process.t (k + 1))
          (y := (pathFollowingUpdate f Mf y0 (process.t k) (process.y k)
            (process.mem_domain k) (process.objectiveNorm_pos k)
            (pathFollowingGammaRadius τ)).2)
          (y' := process.y (k + 1))
          (hy := pathFollowingUpdate_snd_mem y0 (process.t k) (process.mem_domain k)
            (process.objectiveNorm_pos k) htau_half ih hgamma)
          (hy' := process.mem_domain (k + 1))
          (Mf := Mf) (β := pathFollowingCenteringBeta τ) ht hyEq).mp hupdate

/-- Helper for Theorem 5 2 3: once the ordinary Newton decrement stays in the Stage-1 regime up
to index `N`, the path parameter should satisfy the displayed exponential decay estimate. -/
private theorem pathFollowingInitialGap_nonneg
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    (y0 : dom) (xStar : dom) (hmin : IsMinOn f dom (xStar : E)) :
    0 ≤ f (y0 : E) - f (xStar : E) := by
  -- The chosen feasible minimizer cannot exceed the initial objective value.
  exact sub_nonneg.mpr ((isMinOn_iff.mp hmin) _ y0.2)

/-- Helper for Theorem 5 2 3: convexity at the base point `y₀` gives the supporting-nesterovHyperplane
bound against any other feasible point. -/
private theorem pathFollowingBasePoint_supportingHyperplane
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    {y0 : dom} {z : E} (hz : z ∈ dom) :
    inner ℝ (∇ f (y0 : E)) (z - (y0 : E)) ≤ f z - f (y0 : E) := by
  let hself : IsSelfConcordantOnWith dom (Mf : NNReal) f := inferInstance
  have hdiff : DifferentiableAt ℝ f (y0 : E) := by
    -- The Chapter 5 `C³` owner gives an ambient derivative at the base point.
    exact
      (hself.contDiffOn.contDiffAt (hself.isOpen_domain.mem_nhds y0.2)).differentiableAt
        (by norm_num : (3 : WithTop ℕ∞) ≠ 0)
  have hgrad :
      gradientWithin f dom (y0 : E) = ∇ f (y0 : E) := by
    -- On the open self-concordant domain, the within-gradient agrees with the ambient gradient.
    rw [gradientWithin, gradient]
    congr
    exact fderivWithin_eq_fderiv (hself.isOpen_domain.uniqueDiffWithinAt y0.2) hdiff
  have hsupport :
      f z ≥ f (y0 : E) + inner ℝ (∇ f (y0 : E)) (z - (y0 : E)) := by
    -- Reuse the canonical convex supporting-nesterovHyperplane inequality at `y₀`.
    simpa [hgrad] using
      hself.convexOn.lower_tangent_plane (y0 : E) y0.2 hdiff.differentiableWithinAt z hz
  linarith

/-- Helper for Theorem 5 2 3: the tilted objective gap between `y₀` and a feasible minimizer
`xStar` is controlled by the original initial gap with factor `1 - t`. -/
private theorem pathFollowingBasePoint_tiltedGap_le_one_sub_mul_initialGap
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    (y0 : dom) (xStar : dom) (t : Set.Icc (0 : ℝ) 1) :
    auxiliaryCentralPathObjective f y0 t (y0 : E) -
        auxiliaryCentralPathObjective f y0 t (xStar : E) ≤
      (1 - (t : ℝ)) * (f (y0 : E) - f (xStar : E)) := by
  have hsupport :
      inner ℝ (∇ f (y0 : E)) ((xStar : E) - (y0 : E)) ≤
        f (xStar : E) - f (y0 : E) :=
    pathFollowingBasePoint_supportingHyperplane (Mf := Mf) (f := f) (y0 := y0) xStar.2
  have hswap :
      inner ℝ (∇ f (y0 : E)) ((xStar : E) - (y0 : E)) =
        -inner ℝ (∇ f (y0 : E)) ((y0 : E) - (xStar : E)) := by
    have hsub : ((xStar : E) - (y0 : E)) = -((y0 : E) - (xStar : E)) := by
      abel
    rw [hsub, inner_neg_right]
  have hbase :
      f (y0 : E) - f (xStar : E) ≤
        inner ℝ (∇ f (y0 : E)) ((y0 : E) - (xStar : E)) := by
    nlinarith [hsupport, hswap]
  have ht_nonneg : 0 ≤ (t : ℝ) := t.2.1
  have htilt :
      -((t : ℝ) * inner ℝ (∇ f (y0 : E)) ((y0 : E) - (xStar : E))) ≤
        -((t : ℝ) * (f (y0 : E) - f (xStar : E))) := by
    -- Multiply the support lower bound by the nonnegative scalar `-t`.
    nlinarith
  calc
    auxiliaryCentralPathObjective f y0 t (y0 : E) -
        auxiliaryCentralPathObjective f y0 t (xStar : E) =
        (f (y0 : E) - f (xStar : E)) -
          (t : ℝ) * (inner ℝ (∇ f (y0 : E)) (y0 : E) -
            inner ℝ (∇ f (y0 : E)) (xStar : E)) := by
              simp [auxiliaryCentralPathObjective_apply]
              ring
    _ = (f (y0 : E) - f (xStar : E)) -
          (t : ℝ) * inner ℝ (∇ f (y0 : E)) ((y0 : E) - (xStar : E)) := by
            rw [← inner_sub_right]
    _ ≤ (f (y0 : E) - f (xStar : E)) -
          (t : ℝ) * (f (y0 : E) - f (xStar : E)) := by
            linarith
    _ = (1 - (t : ℝ)) * (f (y0 : E) - f (xStar : E)) := by
            ring

/-- Helper for Theorem 5 2 3: the first `N` odd integers sum to `N²`, written on the scalar
surface used by the exponential-decay estimate. -/
private theorem sumOdd_range_eq_sq (N : ℕ) :
    (Finset.range N).sum (fun k ↦ ((2 * k + 1 : ℕ) : ℝ)) = (N : ℝ) ^ (2 : ℕ) := by
  induction N with
  | zero =>
      -- The empty odd sum vanishes, matching `0²`.
      simp
  | succ N ih =>
      -- Peel off the last odd term and normalize the remaining scalar identity.
      rw [Finset.sum_range_succ, ih]
      have hodd : ((2 * N + 1 : ℕ) : ℝ) = 2 * (N : ℝ) + 1 := by
        norm_num
      have hsucc : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by
        norm_num
      rw [hodd, hsucc, pow_two]
      ring

/-- Helper for Theorem 5 2 3: because every next path parameter remains nonnegative, the scalar
update amount `γ / (M_f ‖∇ f(y₀)‖*_{y_k})` is bounded above by the current parameter `t_k`. -/
private theorem pathFollowingProcess_step_div_le_time
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (y0 : dom)
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ) (k : ℕ) :
    pathFollowingGammaRadius τ /
        ((Mf : ℝ) * pathFollowingObjectiveNorm f y0 (process.y k) (process.mem_domain k)) ≤
      (process.t k : ℝ) := by
  have hnext_nonneg : 0 ≤ (process.t (k + 1) : ℝ) := (process.t (k + 1)).2.1
  have hstep :
      (process.t (k + 1) : ℝ) =
        (process.t k : ℝ) -
          pathFollowingGammaRadius τ /
            ((Mf : ℝ) * pathFollowingObjectiveNorm f y0 (process.y k) (process.mem_domain k)) := by
    -- Read the first coordinate of the public process update in the exact scalar spelling.
    have hstepRaw := congrArg Prod.fst (process.step_eq k)
    simpa [pathFollowingObjectiveNorm] using
      (hstepRaw.trans <|
        pathFollowingUpdate_fst f Mf y0 (process.t k) (process.y k)
          (process.mem_domain k) (process.objectiveNorm_pos k) (pathFollowingGammaRadius τ))
  -- The next parameter lies in `Icc (0, 1)`, so the scalar decrement cannot exceed `t_k`.
  linarith

/-- Helper for Theorem 5 2 3: if `γ(τ) > 0`, then every current path parameter `t_k` is also
strictly positive, because the update subtracts a strictly positive amount while staying inside
`[0, 1]`. -/
private theorem pathFollowingProcess_time_pos_of_gamma_pos
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (y0 : dom)
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ)
    (hgamma_pos : 0 < pathFollowingGammaRadius τ) (k : ℕ) :
    0 < (process.t k : ℝ) := by
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero Mf))
  have hnorm_pos :
      0 < pathFollowingObjectiveNorm f y0 (process.y k) (process.mem_domain k) :=
    process.objectiveNorm_pos k
  have hdiv_pos :
      0 <
        pathFollowingGammaRadius τ /
          ((Mf : ℝ) * pathFollowingObjectiveNorm f y0 (process.y k) (process.mem_domain k)) := by
    positivity
  -- Compare the positive update amount with the upper bound `t_k`.
  exact lt_of_lt_of_le hdiv_pos <|
    pathFollowingProcess_step_div_le_time (f := f) (Mf := Mf) y0 process k

/-- Helper for Theorem 5 2 3: once `t_k > 0`, the public scalar update can be rewritten in the
ratio form needed for later logarithmic decay estimates. -/
private theorem pathFollowingProcess_step_ratio_form
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (y0 : dom)
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ) (k : ℕ)
    (htk_pos : 0 < (process.t k : ℝ)) :
    (process.t (k + 1) : ℝ) =
      (process.t k : ℝ) *
        (1 - pathFollowingGammaRadius τ /
          ((Mf : ℝ) * (process.t k : ℝ) *
            pathFollowingObjectiveNorm f y0 (process.y k) (process.mem_domain k))) := by
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero Mf))
  have hnorm_pos :
      0 < pathFollowingObjectiveNorm f y0 (process.y k) (process.mem_domain k) :=
    process.objectiveNorm_pos k
  have hstep :
      (process.t (k + 1) : ℝ) =
        (process.t k : ℝ) -
          pathFollowingGammaRadius τ /
            ((Mf : ℝ) * pathFollowingObjectiveNorm f y0 (process.y k) (process.mem_domain k)) := by
    -- Normalize the first coordinate once before factoring out `t_k`.
    have hstepRaw := congrArg Prod.fst (process.step_eq k)
    simpa [pathFollowingObjectiveNorm] using
      (hstepRaw.trans <|
        pathFollowingUpdate_fst f Mf y0 (process.t k) (process.y k)
          (process.mem_domain k) (process.objectiveNorm_pos k) (pathFollowingGammaRadius τ))
  calc
    (process.t (k + 1) : ℝ) =
        (process.t k : ℝ) -
          pathFollowingGammaRadius τ /
            ((Mf : ℝ) * pathFollowingObjectiveNorm f y0 (process.y k) (process.mem_domain k)) :=
      hstep
    _ = (process.t k : ℝ) *
          (1 - pathFollowingGammaRadius τ /
            ((Mf : ℝ) * (process.t k : ℝ) *
              pathFollowingObjectiveNorm f y0 (process.y k) (process.mem_domain k))) := by
        field_simp [hMf_pos.ne', hnorm_pos.ne', htk_pos.ne']

/-- Helper for Theorem 5 2 3: the public path update gives the exact additive decrement
`t_k - t_{k+1} = γ / (M_f ‖∇ f(y₀)‖*_{y_k})`. -/
private theorem pathFollowingProcess_step_sub_eq_div
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (y0 : dom)
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ) (k : ℕ) :
    (process.t k : ℝ) - (process.t (k + 1) : ℝ) =
      pathFollowingGammaRadius τ /
        ((Mf : ℝ) * pathFollowingObjectiveNorm f y0 (process.y k) (process.mem_domain k)) := by
  have hstep :
      (process.t (k + 1) : ℝ) =
        (process.t k : ℝ) -
          pathFollowingGammaRadius τ /
            ((Mf : ℝ) * pathFollowingObjectiveNorm f y0 (process.y k) (process.mem_domain k)) := by
    -- Read the first coordinate of the process step in the exact additive spelling.
    have hstepRaw := congrArg Prod.fst (process.step_eq k)
    simpa [pathFollowingObjectiveNorm] using
      (hstepRaw.trans <|
        pathFollowingUpdate_fst f Mf y0 (process.t k) (process.y k)
          (process.mem_domain k) (process.objectiveNorm_pos k) (pathFollowingGammaRadius τ))
  linarith

/-- Helper for Theorem 5 2 3: multiplying the additive path update by the current objective norm
turns the next parameter into `t_j ‖∇ f(y₀)‖*_{y_j} - γ / M_f`. -/
private theorem pathFollowingNextTime_mul_objectiveNorm_eq_sub_gammaDiv
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (y0 : dom)
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ) (j : ℕ) :
    (process.t (j + 1) : ℝ) *
        pathFollowingObjectiveNorm f y0 (process.y j) (process.mem_domain j) =
      (process.t j : ℝ) *
          pathFollowingObjectiveNorm f y0 (process.y j) (process.mem_domain j) -
        pathFollowingGammaRadius τ / (Mf : ℝ) := by
  let νj := pathFollowingObjectiveNorm f y0 (process.y j) (process.mem_domain j)
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero Mf))
  have hνj_pos : 0 < νj := process.objectiveNorm_pos j
  have hstep :=
    pathFollowingProcess_step_sub_eq_div (f := f) (Mf := Mf) y0 process j
  have hscaled :
      ((process.t j : ℝ) - (process.t (j + 1) : ℝ)) * νj =
        pathFollowingGammaRadius τ / (Mf : ℝ) := by
    -- Clear the common objective-norm denominator once so the update is linear in `ν_j`.
    rw [hstep]
    field_simp [hMf_pos.ne', hνj_pos.ne']
  -- Rewrite the next weighted parameter by subtracting the exact scaled update.
  calc
    (process.t (j + 1) : ℝ) * νj =
        (process.t j : ℝ) * νj -
          (((process.t j : ℝ) - (process.t (j + 1) : ℝ)) * νj) := by
            ring
    _ = (process.t j : ℝ) * νj - pathFollowingGammaRadius τ / (Mf : ℝ) := by
          rw [hscaled]

/-- Helper for Theorem 5 2 3: the Stage-1 lower bound at index `j`, combined with the exact
parameter update, yields the uniform estimate `((1/2) - τ) / M_f ≤ t_{j+1} ‖∇ f(y₀)‖*_{y_j}`. -/
private theorem pathFollowingNextTime_mul_objectiveNorm_lowerBound
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (hτ_nonneg : 0 ≤ τ) (htau : τ ≤ 0.23) (y0 : dom)
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ)
    (centering :
      ∀ j : ℕ,
        satisfies_approximate_centering_condition f y0 (process.t j) (process.y j)
          (process.mem_domain j) Mf (pathFollowingCenteringBeta τ))
    (N : ℕ)
    (hstage :
      ∀ j : ℕ, j ≤ N →
        1 / (2 * (Mf : ℝ)) ≤ λ[f; process.y j | process.mem_domain j])
    {j : ℕ} (hj : j ≤ N) :
    ((1 / 2 : ℝ) - τ) / (Mf : ℝ) ≤
      (process.t (j + 1) : ℝ) *
        pathFollowingObjectiveNorm f y0 (process.y j) (process.mem_domain j) := by
  let νj := pathFollowingObjectiveNorm f y0 (process.y j) (process.mem_domain j)
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero Mf))
  have hstage_j :
      ((1 / 2 : ℝ) - pathFollowingCenteringBeta τ) / (Mf : ℝ) ≤
        (process.t j : ℝ) * νj := by
    -- Reuse the Stage-1/centering lower bound at the current index `j`.
    simpa [νj] using
      pathFollowingStageCentering_timeObjectiveNormLowerBound
        (f := f) (Mf := Mf) y0 process centering N hstage (k := j) hj
  have hstep_j :
      (process.t (j + 1) : ℝ) * νj =
        (process.t j : ℝ) * νj - pathFollowingGammaRadius τ / (Mf : ℝ) := by
    -- Convert the public path update into the exact weighted-parameter identity.
    simpa [νj] using
      pathFollowingNextTime_mul_objectiveNorm_eq_sub_gammaDiv
        (f := f) (Mf := Mf) y0 process j
  have hrewrite :
      ((1 / 2 : ℝ) - τ) / (Mf : ℝ) =
        ((1 / 2 : ℝ) - pathFollowingCenteringBeta τ) / (Mf : ℝ) -
          pathFollowingGammaRadius τ / (Mf : ℝ) := by
    -- The path radius is defined so that `β(τ) + γ(τ) = τ`.
    rw [pathFollowingGammaRadius]
    field_simp [hMf_pos.ne']
    ring
  -- Substitute the exact update and then apply the Stage-1 lower bound at `j`.
  rw [hrewrite, hstep_j]
  linarith

/-- Helper for Theorem 5 2 3: the Stage-1 lower bound at index `j`, rewritten in the
dimensionless scalar variable `u_j = M_f t_{j+1} ‖∇ f(y₀)‖*_{y_j}`, gives
`(1 / 2) - τ ≤ u_j`. -/
private theorem pathFollowingScaledNextTime_mul_objectiveNorm_lowerBound
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (hτ_nonneg : 0 ≤ τ) (htau : τ ≤ 0.23) (y0 : dom)
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ)
    (centering :
      ∀ j : ℕ,
        satisfies_approximate_centering_condition f y0 (process.t j) (process.y j)
          (process.mem_domain j) Mf (pathFollowingCenteringBeta τ))
    (N : ℕ)
    (hstage :
      ∀ j : ℕ, j ≤ N →
        1 / (2 * (Mf : ℝ)) ≤ λ[f; process.y j | process.mem_domain j])
    {j : ℕ} (hj : j ≤ N) :
    (1 / 2 : ℝ) - τ ≤
      (Mf : ℝ) * (process.t (j + 1) : ℝ) *
        pathFollowingObjectiveNorm f y0 (process.y j) (process.mem_domain j) := by
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero Mf))
  have hbase :
      ((1 / 2 : ℝ) - τ) / (Mf : ℝ) ≤
        (process.t (j + 1) : ℝ) *
          pathFollowingObjectiveNorm f y0 (process.y j) (process.mem_domain j) := by
    -- Reuse the Stage-1 bridge before clearing the positive `M_f` denominator.
    exact
      pathFollowingNextTime_mul_objectiveNorm_lowerBound
        (f := f) (Mf := Mf) hτ_nonneg htau y0 process centering N hstage hj
  have hscaled := mul_le_mul_of_nonneg_left hbase hMf_pos.le
  -- Clear the positive factor `M_f` once so the result is in the normalized scalar spelling.
  calc
    (1 / 2 : ℝ) - τ =
        (Mf : ℝ) * (((1 / 2 : ℝ) - τ) / (Mf : ℝ)) := by
          field_simp [hMf_pos.ne']
    _ ≤
        (Mf : ℝ) *
          ((process.t (j + 1) : ℝ) *
            pathFollowingObjectiveNorm f y0 (process.y j) (process.mem_domain j)) := hscaled
    _ =
        (Mf : ℝ) * (process.t (j + 1) : ℝ) *
          pathFollowingObjectiveNorm f y0 (process.y j) (process.mem_domain j) := by
            ring

/-- Helper for Theorem 5 2 3: the path parameters are antitone along the process because each
update subtracts a nonnegative amount. -/
private theorem pathFollowingTime_antitone
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (hτ_nonneg : 0 ≤ τ) (htau : τ ≤ 0.23) (y0 : dom)
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ)
    {j k : ℕ} (hjk : j ≤ k) :
    (process.t k : ℝ) ≤ (process.t j : ℝ) := by
  induction k with
  | zero =>
      -- The only index below `0` is `0` itself.
      have hj : j = 0 := Nat.eq_zero_of_le_zero hjk
      subst hj
      exact le_rfl
  | succ k ih =>
      by_cases hEq : j = k + 1
      · -- The endpoint case is tautological.
        subst hEq
        exact le_rfl
      · have hjk' : j ≤ k := by
          exact Nat.le_of_lt_succ (lt_of_le_of_ne hjk (by
            intro hkj
            exact hEq (by simpa [Nat.succ_eq_add_one] using hkj)))
        have hgamma_nonneg : 0 ≤ pathFollowingGammaRadius τ :=
          pathFollowingGammaRadius_nonneg hτ_nonneg htau
        have hMf_pos : 0 < (Mf : ℝ) := by
          exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero Mf))
        have hnorm_pos :
            0 < pathFollowingObjectiveNorm f y0 (process.y k) (process.mem_domain k) :=
          process.objectiveNorm_pos k
        have hstep_nonneg :
            0 ≤ pathFollowingGammaRadius τ /
              ((Mf : ℝ) * pathFollowingObjectiveNorm f y0 (process.y k) (process.mem_domain k)) := by
          positivity
        have hnext_le :
            (process.t (k + 1) : ℝ) ≤ (process.t k : ℝ) := by
          have hstep :=
            pathFollowingProcess_step_sub_eq_div
              (f := f) (Mf := Mf) y0 process k
          linarith
        -- Chain the one-step decrease with the induction hypothesis on the prefix up to `k`.
        exact le_trans hnext_le (ih hjk')

/-- Helper for Theorem 5 2 3: changing the path parameter from `tj` to `tk` changes a tilted
objective gap by the exact linear correction `(tj - tk) ⟪∇ f(y₀), a - b⟫`. -/
private theorem auxiliaryCentralPathObjective_gap_shift
    {dom : Set E} {f : E → ℝ} (y0 : dom) (tk tj : ℝ) (a b : E) :
    auxiliaryCentralPathObjective f y0 tk a -
        auxiliaryCentralPathObjective f y0 tk b =
      auxiliaryCentralPathObjective f y0 tj a -
        auxiliaryCentralPathObjective f y0 tj b +
          (tj - tk) * inner ℝ (∇ f (y0 : E)) (a - b) := by
  -- Expand both tilted objectives and factor the parameter shift through the common gradient
  -- pairing.
  have hinner :
      inner ℝ (∇ f (y0 : E)) (a - b) =
        inner ℝ (∇ f (y0 : E)) a - inner ℝ (∇ f (y0 : E)) b := by
    rw [inner_sub_right]
  rw [auxiliaryCentralPathObjective_apply, auxiliaryCentralPathObjective_apply,
    auxiliaryCentralPathObjective_apply, auxiliaryCentralPathObjective_apply, hinner]
  ring

/-- Helper for Theorem 5 2 3: each actual objective drop rewrites as the native
`ψ_{j+1}`-surface drop plus the positive linear shift term at parameter `t_{j+1}`. -/
private theorem pathFollowingObjectiveStep_gap_shift
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (y0 : dom)
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ) (j : ℕ) :
    let tj1 := (process.t (j + 1) : ℝ)
    let ψj1 := auxiliaryCentralPathObjective f y0 tj1
    f (process.y j) - f (process.y (j + 1)) =
      ψj1 (process.y j) - ψj1 (process.y (j + 1)) +
        tj1 * inner ℝ (∇ f (y0 : E)) (process.y j - process.y (j + 1)) := by
  -- Route correction: move the one-step gap back to the original objective immediately instead of
  -- extending the old fixed-surface `ψ_k` telescope.
  simpa using
    auxiliaryCentralPathObjective_gap_shift
      (f := f) y0 0 (process.t (j + 1) : ℝ) (process.y j) (process.y (j + 1))

/-- Helper for Theorem 5 2 3: summing the actual objective drops from `y₀` to `y_k` telescopes on
the original objective `f`. -/
private theorem pathFollowingObjectiveGap_telescope
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (y0 : dom)
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ) (k : ℕ) :
    (Finset.range k).sum (fun j ↦ f (process.y j) - f (process.y (j + 1))) =
      f (y0 : E) - f (process.y k) := by
  -- Telescope the objective gaps and then rewrite the initial point as `y₀`.
  calc
    (Finset.range k).sum (fun j ↦ f (process.y j) - f (process.y (j + 1))) =
        f (process.y 0) - f (process.y k) := by
          simpa using (Finset.sum_range_sub' (fun j ↦ f (process.y j)) k)
    _ = f (y0 : E) - f (process.y k) := by
          simp [process.y_zero]

/-- Helper for Theorem 5 2 3: the ordinary decrement is controlled by the centered decrement at
the same point plus the linear tilt term `t ‖∇ f(y₀)‖*_y`. -/
private theorem pathFollowingOrdinaryDecrement_le_centeredPlusTimeObjectiveNorm
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    (y0 : dom) {t : Set.Icc (0 : ℝ) 1} {y : E} (hy : y ∈ dom) :
    λ[f; y | hy] ≤
      λ[auxiliaryCentralPathObjective f y0 (t : ℝ); y | hy] +
        (t : ℝ) * pathFollowingObjectiveNorm f y0 y hy := by
  -- Move from the unshifted decrement to the fixed tilted surface at parameter `t`.
  have hshift :
      λ[auxiliaryCentralPathObjective f y0 0; y | hy] ≤
        λ[auxiliaryCentralPathObjective f y0 (t : ℝ); y | hy] +
          |(0 : ℝ) - (t : ℝ)| * pathFollowingObjectiveNorm f y0 y hy := by
    simpa using
      auxiliaryCentralPathObjective_decrement_le_add_objectiveNorm_mul_abs_sub
        (f := f) y0 hy (t : ℝ) 0
  have htilt_zero :
      λ[auxiliaryCentralPathObjective f y0 0; y | hy] = λ[f; y | hy] := by
    -- At parameter `t = 0`, the auxiliary objective is just `f`.
    rw [NewtonDecrement.ofPosDefMem_def, NewtonDecrement.ofPosDefMem_def]
    simp [auxiliaryCentralPathObjective_gradient_eq, auxiliaryCentralPathObjective_hessian_eq]
  have habs :
      |(0 : ℝ) - (t : ℝ)| = (t : ℝ) := by
    -- The path parameter lives in `[0, 1]`, so the absolute value collapses.
    simpa using abs_of_nonneg t.2.1
  calc
    λ[f; y | hy] = λ[auxiliaryCentralPathObjective f y0 0; y | hy] := htilt_zero.symm
    _ ≤ λ[auxiliaryCentralPathObjective f y0 (t : ℝ); y | hy] +
        |(0 : ℝ) - (t : ℝ)| * pathFollowingObjectiveNorm f y0 y hy := hshift
    _ = λ[auxiliaryCentralPathObjective f y0 (t : ℝ); y | hy] +
        (t : ℝ) * pathFollowingObjectiveNorm f y0 y hy := by
          rw [habs]

/-- Helper for Theorem 5 2 3: the Stage-1 lower bound together with approximate centering at the
`k`-th iterate forces a lower bound on `t_k ‖∇ f(y₀)‖*_{y_k}`. -/
private theorem pathFollowingStageCentering_timeObjectiveNormLowerBound
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (y0 : dom)
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ)
    (centering :
      ∀ j : ℕ,
        satisfies_approximate_centering_condition f y0 (process.t j) (process.y j)
          (process.mem_domain j) Mf (pathFollowingCenteringBeta τ))
    (N : ℕ)
    (hstage :
      ∀ j : ℕ, j ≤ N →
        1 / (2 * (Mf : ℝ)) ≤ λ[f; process.y j | process.mem_domain j])
    {k : ℕ} (hk : k ≤ N) :
    ((1 / 2 : ℝ) - pathFollowingCenteringBeta τ) / (Mf : ℝ) ≤
      (process.t k : ℝ) *
        pathFollowingObjectiveNorm f y0 (process.y k) (process.mem_domain k) := by
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero Mf))
  have hcenterk :
      λ[auxiliaryCentralPathObjective f y0 (process.t k : ℝ); process.y k | process.mem_domain k] ≤
        pathFollowingCenteringBeta τ / (Mf : ℝ) := by
    -- Rewrite the centering invariant at index `k` into the explicit decrement inequality.
    exact
      (satisfies_approximate_centering_condition_iff
        f y0 (process.t k) (process.y k) (process.mem_domain k) Mf
        (pathFollowingCenteringBeta τ)).1 (centering k)
  have hordinary_le :
      λ[f; process.y k | process.mem_domain k] ≤
        λ[auxiliaryCentralPathObjective f y0 (process.t k : ℝ); process.y k |
          process.mem_domain k] +
            (process.t k : ℝ) *
              pathFollowingObjectiveNorm f y0 (process.y k) (process.mem_domain k) := by
    -- Compare the ordinary decrement to the centered decrement on the fixed `ψ_k` surface.
    simpa using
      pathFollowingOrdinaryDecrement_le_centeredPlusTimeObjectiveNorm
        (f := f) (Mf := Mf) y0 (t := process.t k) (hy := process.mem_domain k)
  have hbound :
      1 / (2 * (Mf : ℝ)) ≤
        pathFollowingCenteringBeta τ / (Mf : ℝ) +
          (process.t k : ℝ) *
            pathFollowingObjectiveNorm f y0 (process.y k) (process.mem_domain k) := by
    -- Insert the explicit centering estimate into the Stage-1 lower bound.
    exact le_trans (hstage k hk) <| by
      linarith
  have hrewrite :
      (((1 / 2 : ℝ) - pathFollowingCenteringBeta τ) / (Mf : ℝ)) =
        1 / (2 * (Mf : ℝ)) - pathFollowingCenteringBeta τ / (Mf : ℝ) := by
    -- Normalize the target so the previous scalar inequality closes it directly.
    field_simp [hMf_pos.ne']
  rw [hrewrite]
  linarith

/-- Helper for Theorem 5 2 3: on the fixed tilted surface `ψ_k`, each earlier path-following
step should contribute at least `2 κ(τ) M_f ν_k` to the scaled objective drop. -/
private theorem pathFollowingFixedSurfaceGap_shift
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (y0 : dom)
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ) (j k : ℕ) :
    let tk := (process.t k : ℝ)
    let tj1 := (process.t (j + 1) : ℝ)
    let ψk := auxiliaryCentralPathObjective f y0 tk
    let ψj1 := auxiliaryCentralPathObjective f y0 tj1
    ψk (process.y j) - ψk (process.y (j + 1)) =
      ψj1 (process.y j) - ψj1 (process.y (j + 1)) +
        (tj1 - tk) * inner ℝ (∇ f (y0 : E)) (process.y j - process.y (j + 1)) := by
  -- Move the fixed-surface gap from `t_k` to `t_{j+1}` before introducing any one-step estimates.
  simpa using
    auxiliaryCentralPathObjective_gap_shift
      (f := f) y0 (process.t k : ℝ) (process.t (j + 1) : ℝ)
      (process.y j) (process.y (j + 1))

/-- Helper for Theorem 5 2 3: the actual `ψ_{j+1}` update satisfies the canonical intermediate
value-drop lower bound from Lemma 5.2.1, rewritten in the process coordinates. -/
private theorem pathFollowingIntermediateSurfaceValueDrop_ge
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (y0 : dom)
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ) (j : ℕ) :
    let tj1 := (process.t (j + 1) : ℝ)
    let ψj1 := auxiliaryCentralPathObjective f y0 tj1
    let δj := λ[ψj1; process.y j | process.mem_domain j]
    (Mf : ℝ) ^ (2 : ℕ) *
        (ψj1 (process.y j) - ψj1 (process.y (j + 1))) ≥
      (Mf : ℝ) ^ (2 : ℕ) *
        (δj ^ (2 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ))) +
          (Mf : ℝ) * δj ^ (3 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δj) * (3 + 2 * (Mf : ℝ) * δj))) := by
  let tj1 := (process.t (j + 1) : ℝ)
  let ψj1 := auxiliaryCentralPathObjective f y0 tj1
  let δj := λ[ψj1; process.y j | process.mem_domain j]
  let hH :
      (hessian ψj1 (process.y j)).det ≠ 0 :=
    auxiliaryCentralPathObjective_hessian_det_ne_zero f y0 tj1 (process.mem_domain j)
  have hstep_t :
      (pathFollowingUpdate f Mf y0 (process.t j) (process.y j)
        (process.mem_domain j) (process.objectiveNorm_pos j)
        (pathFollowingGammaRadius τ)).1 = tj1 := by
    -- The first coordinate of the public step is exactly `t_{j+1}`.
    simpa [tj1] using congrArg Prod.fst (process.step_eq j).symm
  have hstep_y :
      process.y (j + 1) =
        selfConcordantNewtonNextPoint ψj1 (Mf : NNReal) .intermediate
          (process.y j) (process.mem_domain j) hH := by
    -- Rewrite the successor iterate into the canonical intermediate Newton owner for `ψ_{j+1}`.
    calc
      process.y (j + 1) =
          (pathFollowingUpdate f Mf y0 (process.t j) (process.y j)
            (process.mem_domain j) (process.objectiveNorm_pos j)
            (pathFollowingGammaRadius τ)).2 := by
              simpa using (congrArg Prod.snd (process.step_eq j).symm).symm
      _ =
          selfConcordantNewtonNextPoint
            (auxiliaryCentralPathObjective f y0
              ((pathFollowingUpdate f Mf y0 (process.t j) (process.y j)
                (process.mem_domain j) (process.objectiveNorm_pos j)
                (pathFollowingGammaRadius τ)).1))
            (Mf : NNReal) .intermediate
            (process.y j) (process.mem_domain j)
            (auxiliaryCentralPathObjective_hessian_det_ne_zero f y0
              ((pathFollowingUpdate f Mf y0 (process.t j) (process.y j)
                (process.mem_domain j) (process.objectiveNorm_pos j)
                (pathFollowingGammaRadius τ)).1) (process.mem_domain j)) := by
              simpa using
                pathFollowingUpdate_snd f Mf y0 (process.t j) (process.y j)
                  (process.mem_domain j) (process.objectiveNorm_pos j)
                  (pathFollowingGammaRadius τ)
      _ =
          selfConcordantNewtonNextPoint ψj1 (Mf : NNReal) .intermediate
            (process.y j) (process.mem_domain j) hH := by
              rw [hstep_t]
  have hδj :
      δj =
        NewtonDecrement.ofDetNeZero (Mf : NNReal) ψj1 (process.mem_domain j) hH := by
    -- The centered decrement notation and the determinant-based normal form agree at `y_j`.
    simpa [δj]
  have hdrop_raw :=
    selfConcordant_intermediateNewtonStep_value_drop_lower_bound
      (dom := dom) (Mf := (Mf : NNReal)) (f := ψj1)
      (x := process.y j) (hx := process.mem_domain j) hH
  have hMf_sq_nonneg : 0 ≤ (Mf : ℝ) ^ (2 : ℕ) := by
    positivity
  have hscaled := mul_le_mul_of_nonneg_left hdrop_raw hMf_sq_nonneg
  -- Keep the Chapter 5 lower bound on its native `ψ_{j+1}` surface before any parameter transport.
  dsimp [tj1, ψj1] at hscaled ⊢
  simpa [auxiliaryCentralPathObjective_apply, hstep_y, hδj, δj, ge_iff_le] using hscaled

/-- Helper for Theorem 5 2 3: on the intermediate tilted surface `ψ_{j+1}`, the base gradient
pairing is controlled by the objective norm at `y_j` times the corresponding local step norm. -/
private theorem pathFollowingBaseGradientPairing_abs_le_objectiveNorm_mul_intermediateLocalNorm
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (y0 : dom)
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ)
    (j : ℕ) :
    let tj1 := (process.t (j + 1) : ℝ)
    let ψj1 := auxiliaryCentralPathObjective f y0 tj1
    |inner ℝ (∇ f (y0 : E)) (process.y j - process.y (j + 1))| ≤
      pathFollowingObjectiveNorm f y0 (process.y j) (process.mem_domain j) *
        ‖process.y j - process.y (j + 1)‖[ψj1; process.y j] := by
  let tj1 := (process.t (j + 1) : ℝ)
  let ψj1 := auxiliaryCentralPathObjective f y0 tj1
  have hpair :
      |inner ℝ (∇ f (y0 : E)) (process.y j - process.y (j + 1))| ≤
        HessianDualLocalNorm.ofPosDefMem ψj1 (process.mem_domain j)
            (toDual ℝ E (∇ f (y0 : E))) *
          ‖process.y j - process.y (j + 1)‖[ψj1; process.y j] := by
    -- Apply the fixed-base dual/local Cauchy inequality on the unchanged Hessian surface `ψ_{j+1}`.
    exact
      abs_toDual_apply_le_dualLocalNorm_mul_hessianLocalNorm_ofPosDefMem
        (F := ψj1) (hx := process.mem_domain j) (∇ f (y0 : E))
        (process.y j - process.y (j + 1))
  have hnorm_eq :
      HessianDualLocalNorm.ofPosDefMem ψj1 (process.mem_domain j)
          (toDual ℝ E (∇ f (y0 : E))) =
        pathFollowingObjectiveNorm f y0 (process.y j) (process.mem_domain j) := by
    -- The tilt parameter does not change the Hessian metric, so the dual norm is exactly `ν_j`.
    rw [auxiliaryCentralPathObjective_dualLocalNorm_eq f y0 (process.mem_domain j) 0 tj1]
    simp [pathFollowingObjectiveNorm]
  simpa [ψj1, hnorm_eq] using hpair

/-- Helper for Theorem 5 2 3: after substituting the explicit intermediate-step norm, the base
gradient pairing is bounded below by the corresponding decrement-ratio correction. -/
private theorem pathFollowingBaseGradientPairing_ge_neg_objectiveNorm_mul_intermediateStepRatio
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (y0 : dom)
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ)
    (j : ℕ) :
    let tj1 := (process.t (j + 1) : ℝ)
    let ψj1 := auxiliaryCentralPathObjective f y0 tj1
    let δj := λ[ψj1; process.y j | process.mem_domain j]
    -pathFollowingObjectiveNorm f y0 (process.y j) (process.mem_domain j) *
        (δj * (1 + (Mf : ℝ) * δj) /
          (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ))) ≤
      inner ℝ (∇ f (y0 : E)) (process.y j - process.y (j + 1)) := by
  let tj1 := (process.t (j + 1) : ℝ)
  let ψj1 := auxiliaryCentralPathObjective f y0 tj1
  let δj := λ[ψj1; process.y j | process.mem_domain j]
  have hpair_abs :=
    pathFollowingBaseGradientPairing_abs_le_objectiveNorm_mul_intermediateLocalNorm
      (f := f) (Mf := Mf) y0 process j
  have hstep_norm :
      ‖process.y j - process.y (j + 1)‖[ψj1; process.y j] =
        δj * (1 + (Mf : ℝ) * δj) /
          (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ)) := by
    -- The local norm is invariant under negating the step, then the explicit ratio applies.
    have hsub :
        process.y j - process.y (j + 1) = -(process.y (j + 1) - process.y j) := by
      abel
    rw [hsub, hessianLocalNorm_neg]
    simpa [tj1, ψj1, δj] using
      pathFollowingIntermediateStep_localNorm_eq_decrementRatio
        (f := f) (Mf := Mf) y0 process j
  have hpair_abs_ratio :
      |inner ℝ (∇ f (y0 : E)) (process.y j - process.y (j + 1))| ≤
        pathFollowingObjectiveNorm f y0 (process.y j) (process.mem_domain j) *
          (δj * (1 + (Mf : ℝ) * δj) /
            (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ))) := by
    -- Replace the local step norm by its explicit decrement ratio.
    simpa [tj1, ψj1, δj, hstep_norm] using hpair_abs
  -- Unpack the absolute-value estimate into the lower side needed for the objective-gap route.
  exact (abs_le.mp hpair_abs_ratio).1

/-- Helper for Theorem 5 2 3: each actual one-step objective drop dominates the native
intermediate-surface drop minus the explicit base-gradient correction term. -/
private theorem pathFollowingObjectiveStep_gap_ge_scalarized
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (y0 : dom)
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ)
    (j : ℕ) :
    let tj1 := (process.t (j + 1) : ℝ)
    let ψj1 := auxiliaryCentralPathObjective f y0 tj1
    let δj := λ[ψj1; process.y j | process.mem_domain j]
    (Mf : ℝ) ^ (2 : ℕ) * (f (process.y j) - f (process.y (j + 1))) ≥
      (Mf : ℝ) ^ (2 : ℕ) *
        (δj ^ (2 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ))) +
          (Mf : ℝ) * δj ^ (3 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δj) * (3 + 2 * (Mf : ℝ) * δj)) -
          tj1 * pathFollowingObjectiveNorm f y0 (process.y j) (process.mem_domain j) *
            (δj * (1 + (Mf : ℝ) * δj) /
              (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ)))) := by
  let tj1 := (process.t (j + 1) : ℝ)
  let ψj1 := auxiliaryCentralPathObjective f y0 tj1
  let δj := λ[ψj1; process.y j | process.mem_domain j]
  have hMf_sq_nonneg : 0 ≤ (Mf : ℝ) ^ (2 : ℕ) := by
    positivity
  have htj1_nonneg : 0 ≤ tj1 := (process.t (j + 1)).2.1
  have hgap_shift :=
    pathFollowingObjectiveStep_gap_shift (f := f) (Mf := Mf) y0 process j
  have hdrop_native :=
    pathFollowingIntermediateSurfaceValueDrop_ge (f := f) (Mf := Mf) y0 process j
  have hpair_lower :=
    pathFollowingBaseGradientPairing_ge_neg_objectiveNorm_mul_intermediateStepRatio
      (f := f) (Mf := Mf) y0 process j
  have hscaled_pair :
      (Mf : ℝ) ^ (2 : ℕ) *
          (tj1 *
            (-pathFollowingObjectiveNorm f y0 (process.y j) (process.mem_domain j) *
              (δj * (1 + (Mf : ℝ) * δj) /
                (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ))))) ≤
        (Mf : ℝ) ^ (2 : ℕ) *
          (tj1 * inner ℝ (∇ f (y0 : E)) (process.y j - process.y (j + 1))) := by
    -- Multiply the pairing lower bound by the nonnegative time factor and `M_f^2`.
    exact
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hpair_lower htj1_nonneg)
        hMf_sq_nonneg
  -- Keep the actual objective drop on the `ψ_{j+1}` surface, then insert the native-drop and
  -- pairing lower bounds separately.
  dsimp [tj1, ψj1, δj] at hgap_shift hdrop_native hpair_lower hscaled_pair ⊢
  calc
    (Mf : ℝ) ^ (2 : ℕ) * (f (process.y j) - f (process.y (j + 1))) =
        (Mf : ℝ) ^ (2 : ℕ) *
            ((auxiliaryCentralPathObjective f y0 ↑(process.t (j + 1))) (process.y j) -
              (auxiliaryCentralPathObjective f y0 ↑(process.t (j + 1))) (process.y (j + 1))) +
          (Mf : ℝ) ^ (2 : ℕ) *
            (↑(process.t (j + 1)) *
              inner ℝ (∇ f (y0 : E)) (process.y j - process.y (j + 1))) := by
          rw [hgap_shift]
          ring
    _ ≥
        (Mf : ℝ) ^ (2 : ℕ) *
            (λ[auxiliaryCentralPathObjective f y0 ↑(process.t (j + 1)); process.y j |
                process.mem_domain j] ^ (2 : ℕ) /
                (2 *
                  (1 + (Mf : ℝ) *
                      λ[auxiliaryCentralPathObjective f y0 ↑(process.t (j + 1)); process.y j |
                        process.mem_domain j] +
                    (Mf : ℝ) ^ (2 : ℕ) *
                      λ[auxiliaryCentralPathObjective f y0 ↑(process.t (j + 1)); process.y j |
                        process.mem_domain j] ^ (2 : ℕ))) +
              (Mf : ℝ) *
                  λ[auxiliaryCentralPathObjective f y0 ↑(process.t (j + 1)); process.y j |
                    process.mem_domain j] ^ (3 : ℕ) /
                (2 *
                  (1 + (Mf : ℝ) *
                      λ[auxiliaryCentralPathObjective f y0 ↑(process.t (j + 1)); process.y j |
                        process.mem_domain j]) *
                    (3 + 2 * (Mf : ℝ) *
                      λ[auxiliaryCentralPathObjective f y0 ↑(process.t (j + 1)); process.y j |
                        process.mem_domain j]))) +
          (Mf : ℝ) ^ (2 : ℕ) *
            (↑(process.t (j + 1)) *
              (-pathFollowingObjectiveNorm f y0 (process.y j) (process.mem_domain j) *
                (λ[auxiliaryCentralPathObjective f y0 ↑(process.t (j + 1)); process.y j |
                    process.mem_domain j] *
                    (1 +
                      (Mf : ℝ) *
                        λ[auxiliaryCentralPathObjective f y0 ↑(process.t (j + 1)); process.y j |
                          process.mem_domain j]) /
                  (1 +
                    (Mf : ℝ) *
                      λ[auxiliaryCentralPathObjective f y0 ↑(process.t (j + 1)); process.y j |
                        process.mem_domain j] +
                    (Mf : ℝ) ^ (2 : ℕ) *
                      λ[auxiliaryCentralPathObjective f y0 ↑(process.t (j + 1)); process.y j |
                        process.mem_domain j] ^ (2 : ℕ))))) := by
          exact add_le_add hdrop_native hscaled_pair
    _ =
        (Mf : ℝ) ^ (2 : ℕ) *
          (λ[auxiliaryCentralPathObjective f y0 ↑(process.t (j + 1)); process.y j |
              process.mem_domain j] ^ (2 : ℕ) /
              (2 *
                (1 + (Mf : ℝ) *
                    λ[auxiliaryCentralPathObjective f y0 ↑(process.t (j + 1)); process.y j |
                      process.mem_domain j] +
                  (Mf : ℝ) ^ (2 : ℕ) *
                    λ[auxiliaryCentralPathObjective f y0 ↑(process.t (j + 1)); process.y j |
                      process.mem_domain j] ^ (2 : ℕ))) +
            (Mf : ℝ) *
                λ[auxiliaryCentralPathObjective f y0 ↑(process.t (j + 1)); process.y j |
                  process.mem_domain j] ^ (3 : ℕ) /
              (2 *
                (1 + (Mf : ℝ) *
                    λ[auxiliaryCentralPathObjective f y0 ↑(process.t (j + 1)); process.y j |
                      process.mem_domain j]) *
                  (3 + 2 * (Mf : ℝ) *
                    λ[auxiliaryCentralPathObjective f y0 ↑(process.t (j + 1)); process.y j |
                      process.mem_domain j])) -
            ↑(process.t (j + 1)) *
              pathFollowingObjectiveNorm f y0 (process.y j) (process.mem_domain j) *
                (λ[auxiliaryCentralPathObjective f y0 ↑(process.t (j + 1)); process.y j |
                    process.mem_domain j] *
                    (1 +
                      (Mf : ℝ) *
                        λ[auxiliaryCentralPathObjective f y0 ↑(process.t (j + 1)); process.y j |
                          process.mem_domain j]) /
                  (1 +
                    (Mf : ℝ) *
                      λ[auxiliaryCentralPathObjective f y0 ↑(process.t (j + 1)); process.y j |
                        process.mem_domain j] +
                    (Mf : ℝ) ^ (2 : ℕ) *
                      λ[auxiliaryCentralPathObjective f y0 ↑(process.t (j + 1)); process.y j |
                        process.mem_domain j] ^ (2 : ℕ)))) := by
          ring

/-- Helper for Theorem 5 2 3: on the fixed tilted surface `ψ_k`, the one-step contribution from
index `j` is bounded below by the native `ψ_{j+1}` value drop plus the exact parameter-shift
correction. -/
private theorem pathFollowingFixedSurfaceStepDrop_ge_nativePlusShift
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (y0 : dom)
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ)
    (j k : ℕ) :
    let ψk := auxiliaryCentralPathObjective f y0 (process.t k : ℝ)
    let tj1 := (process.t (j + 1) : ℝ)
    let ψj1 := auxiliaryCentralPathObjective f y0 tj1
    let δj := λ[ψj1; process.y j | process.mem_domain j]
    (Mf : ℝ) ^ (2 : ℕ) *
        (δj ^ (2 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ))) +
          (Mf : ℝ) * δj ^ (3 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δj) * (3 + 2 * (Mf : ℝ) * δj))) +
      (Mf : ℝ) ^ (2 : ℕ) *
        ((tj1 - (process.t k : ℝ)) *
          inner ℝ (∇ f (y0 : E)) (process.y j - process.y (j + 1))) ≤
      (Mf : ℝ) ^ (2 : ℕ) * (ψk (process.y j) - ψk (process.y (j + 1))) := by
  let ψk := auxiliaryCentralPathObjective f y0 (process.t k : ℝ)
  let tj1 := (process.t (j + 1) : ℝ)
  let ψj1 := auxiliaryCentralPathObjective f y0 tj1
  let δj := λ[ψj1; process.y j | process.mem_domain j]
  have hgap_shift :=
    pathFollowingFixedSurfaceGap_shift (f := f) (Mf := Mf) y0 process j k
  have hdrop_native :=
    pathFollowingIntermediateSurfaceValueDrop_ge (f := f) (Mf := Mf) y0 process j
  -- Route correction: the stronger `2 κ(τ) M_f ν_k` lower bound is false even for the
  -- one-dimensional quadratic model, so keep only the exact native-drop-plus-shift frontier.
  dsimp [ψk, tj1, ψj1, δj] at hgap_shift hdrop_native ⊢
  calc
    (Mf : ℝ) ^ (2 : ℕ) *
        (λ[auxiliaryCentralPathObjective f y0 ↑(process.t (j + 1)); process.y j |
            process.mem_domain j] ^ (2 : ℕ) /
            (2 *
              (1 + (Mf : ℝ) *
                  λ[auxiliaryCentralPathObjective f y0 ↑(process.t (j + 1)); process.y j |
                    process.mem_domain j] +
                (Mf : ℝ) ^ (2 : ℕ) *
                  λ[auxiliaryCentralPathObjective f y0 ↑(process.t (j + 1)); process.y j |
                    process.mem_domain j] ^ (2 : ℕ))) +
          (Mf : ℝ) *
              λ[auxiliaryCentralPathObjective f y0 ↑(process.t (j + 1)); process.y j |
                process.mem_domain j] ^ (3 : ℕ) /
            (2 *
              (1 + (Mf : ℝ) *
                  λ[auxiliaryCentralPathObjective f y0 ↑(process.t (j + 1)); process.y j |
                    process.mem_domain j]) *
                (3 + 2 * (Mf : ℝ) *
                  λ[auxiliaryCentralPathObjective f y0 ↑(process.t (j + 1)); process.y j |
                    process.mem_domain j]))) +
      (Mf : ℝ) ^ (2 : ℕ) *
        ((↑(process.t (j + 1)) - ↑(process.t k)) *
          inner ℝ (∇ f (y0 : E)) (process.y j - process.y (j + 1))) ≤
    (Mf : ℝ) ^ (2 : ℕ) *
        (f (process.y j) - ↑(process.t (j + 1)) * ⟪∇ f ↑y0, process.y j⟫_ℝ -
          (f (process.y (j + 1)) -
            ↑(process.t (j + 1)) * ⟪∇ f ↑y0, process.y (j + 1)⟫_ℝ)) +
        (Mf : ℝ) ^ (2 : ℕ) *
          ((↑(process.t (j + 1)) - ↑(process.t k)) *
            inner ℝ (∇ f (y0 : E)) (process.y j - process.y (j + 1))) := by
      exact add_le_add hdrop_native le_rfl
    _ = (Mf : ℝ) ^ (2 : ℕ) *
        (f (process.y j) - ↑(process.t k) * ⟪∇ f ↑y0, process.y j⟫_ℝ -
          (f (process.y (j + 1)) - ↑(process.t k) * ⟪∇ f ↑y0, process.y (j + 1)⟫_ℝ)) := by
      have hscaled_shift :=
        congrArg (fun x : ℝ ↦ (Mf : ℝ) ^ (2 : ℕ) * x) hgap_shift
      simpa [mul_add, mul_assoc, mul_left_comm, mul_comm] using hscaled_shift.symm

/-- Helper for Theorem 5 2 3: summing the verified native-drop-plus-shift bounds yields the same
lower bound for the total fixed-surface gap from `y₀` to `y_k`. -/
private theorem pathFollowingAccumulatedGap_ge_nativePlusShift
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (y0 : dom)
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ)
    (k : ℕ) :
    let ψk := auxiliaryCentralPathObjective f y0 (process.t k : ℝ)
    let stepLower : ℕ → ℝ := fun j ↦
      let tj1 := (process.t (j + 1) : ℝ)
      let ψj1 := auxiliaryCentralPathObjective f y0 tj1
      let δj := λ[ψj1; process.y j | process.mem_domain j]
      (Mf : ℝ) ^ (2 : ℕ) *
          (δj ^ (2 : ℕ) /
              (2 * (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ))) +
            (Mf : ℝ) * δj ^ (3 : ℕ) /
              (2 * (1 + (Mf : ℝ) * δj) * (3 + 2 * (Mf : ℝ) * δj))) +
        (Mf : ℝ) ^ (2 : ℕ) *
          (((process.t (j + 1) : ℝ) - (process.t k : ℝ)) *
            inner ℝ (∇ f (y0 : E)) (process.y j - process.y (j + 1)))
    (Finset.range k).sum stepLower ≤
      (Mf : ℝ) ^ (2 : ℕ) * (ψk (y0 : E) - ψk (process.y k)) := by
  let ψk := auxiliaryCentralPathObjective f y0 (process.t k : ℝ)
  let stepLower : ℕ → ℝ := fun j ↦
    let tj1 := (process.t (j + 1) : ℝ)
    let ψj1 := auxiliaryCentralPathObjective f y0 tj1
    let δj := λ[ψj1; process.y j | process.mem_domain j]
    (Mf : ℝ) ^ (2 : ℕ) *
        (δj ^ (2 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ))) +
          (Mf : ℝ) * δj ^ (3 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δj) * (3 + 2 * (Mf : ℝ) * δj))) +
      (Mf : ℝ) ^ (2 : ℕ) *
        (((process.t (j + 1) : ℝ) - (process.t k : ℝ)) *
          inner ℝ (∇ f (y0 : E)) (process.y j - process.y (j + 1)))
  have hsum_le :
      (Finset.range k).sum stepLower ≤
        (Finset.range k).sum
          (fun j ↦
            (Mf : ℝ) ^ (2 : ℕ) * (ψk (process.y j) - ψk (process.y (j + 1)))) := by
    -- Sum the verified one-step native-drop-plus-shift bounds across `j < k`.
    refine Finset.sum_le_sum ?_
    intro j hjmem
    simpa [stepLower, ψk] using
      pathFollowingFixedSurfaceStepDrop_ge_nativePlusShift
        (f := f) (Mf := Mf) y0 process j k
  have htel :
      (Finset.range k).sum (fun j ↦ ψk (process.y j) - ψk (process.y (j + 1))) =
        ψk (process.y 0) - ψk (process.y k) := by
    -- Telescope the fixed-surface successive gaps.
    simpa using (Finset.sum_range_sub' (fun j ↦ ψk (process.y j)) k)
  have hsum_right :
      (Finset.range k).sum
          (fun j ↦ (Mf : ℝ) ^ (2 : ℕ) * (ψk (process.y j) - ψk (process.y (j + 1)))) =
        (Mf : ℝ) ^ (2 : ℕ) * (ψk (y0 : E) - ψk (process.y k)) := by
    -- Rewrite the telescoped left endpoint back to the prescribed base point `y₀`.
    rw [← Finset.mul_sum, htel]
    simp [process.y_zero]
  rw [hsum_right] at hsum_le
  exact hsum_le

/-- Helper for Theorem 5 2 3: summing the one-step base-gradient pairings telescopes to the
single pairing with the net displacement from `y₀` to `y_k`. -/
private theorem pathFollowingBaseGradientPairing_telescope
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (y0 : dom)
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ)
    (k : ℕ) :
    (Finset.range k).sum
        (fun j ↦ inner ℝ (∇ f (y0 : E)) (process.y j - process.y (j + 1))) =
      inner ℝ (∇ f (y0 : E)) ((y0 : E) - process.y k) := by
  have hvec :
      (Finset.range k).sum (fun j ↦ process.y j - process.y (j + 1)) =
        process.y 0 - process.y k := by
    -- Telescope the successive iterate differences before applying the fixed base gradient.
    simpa using (Finset.sum_range_sub' (fun j ↦ process.y j) k)
  have hinner :=
    congrArg (fun z : E ↦ inner ℝ (∇ f (y0 : E)) z) hvec
  -- Rewrite the left endpoint back to the prescribed base point `y₀`.
  simpa [inner_sum, inner_sub_right, process.y_zero] using hinner

/-- Helper for Theorem 5 2 3: every actual objective step can be rewritten on the fixed surface
`ψ_k`, with the common tilt term `t_k ⟪∇ f(y₀), y_j - y_{j+1}⟫`. -/
private theorem pathFollowingObjectiveStep_gap_shift_currentSurface
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (y0 : dom)
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ)
    (j k : ℕ) :
    let ψk := auxiliaryCentralPathObjective f y0 (process.t k : ℝ)
    f (process.y j) - f (process.y (j + 1)) =
      ψk (process.y j) - ψk (process.y (j + 1)) +
        (process.t k : ℝ) *
          inner ℝ (∇ f (y0 : E)) (process.y j - process.y (j + 1)) := by
  -- Rewrite the actual one-step gap directly on the fixed surface at parameter `t_k`.
  simpa using
    auxiliaryCentralPathObjective_gap_shift
      (f := f) y0 0 (process.t k : ℝ) (process.y j) (process.y (j + 1))

/-- Helper for Theorem 5 2 3: the summed actual objective drops dominate the fixed-surface
prefix package together with the common `t_k` tilt term. -/
private theorem pathFollowingActualPrefixGap_ge_fixedSurfacePackageWithBaseTilt
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (y0 : dom)
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ)
    (k : ℕ) :
    let tk := (process.t k : ℝ)
    let stepLower : ℕ → ℝ := fun j ↦
      let tj1 := (process.t (j + 1) : ℝ)
      let ψj1 := auxiliaryCentralPathObjective f y0 tj1
      let δj := λ[ψj1; process.y j | process.mem_domain j]
      (Mf : ℝ) ^ (2 : ℕ) *
          (δj ^ (2 : ℕ) /
              (2 * (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ))) +
            (Mf : ℝ) * δj ^ (3 : ℕ) /
              (2 * (1 + (Mf : ℝ) * δj) * (3 + 2 * (Mf : ℝ) * δj))) +
        (Mf : ℝ) ^ (2 : ℕ) *
          (((process.t (j + 1) : ℝ) - tk) *
            inner ℝ (∇ f (y0 : E)) (process.y j - process.y (j + 1)))
    (Finset.range k).sum stepLower +
        (Mf : ℝ) ^ (2 : ℕ) * tk *
          inner ℝ (∇ f (y0 : E)) ((y0 : E) - process.y k) ≤
      (Finset.range k).sum
        (fun j ↦ (Mf : ℝ) ^ (2 : ℕ) * (f (process.y j) - f (process.y (j + 1)))) := by
  let tk := (process.t k : ℝ)
  let ψk := auxiliaryCentralPathObjective f y0 tk
  let stepLower : ℕ → ℝ := fun j ↦
    let tj1 := (process.t (j + 1) : ℝ)
    let ψj1 := auxiliaryCentralPathObjective f y0 tj1
    let δj := λ[ψj1; process.y j | process.mem_domain j]
    (Mf : ℝ) ^ (2 : ℕ) *
        (δj ^ (2 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ))) +
          (Mf : ℝ) * δj ^ (3 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δj) * (3 + 2 * (Mf : ℝ) * δj))) +
      (Mf : ℝ) ^ (2 : ℕ) *
        (((process.t (j + 1) : ℝ) - tk) *
          inner ℝ (∇ f (y0 : E)) (process.y j - process.y (j + 1)))
  let actualDrop : ℕ → ℝ := fun j ↦
    (Mf : ℝ) ^ (2 : ℕ) * (f (process.y j) - f (process.y (j + 1)))
  have hpackage_le :
      (Finset.range k).sum stepLower ≤
        (Finset.range k).sum
          (fun j ↦ (Mf : ℝ) ^ (2 : ℕ) * (ψk (process.y j) - ψk (process.y (j + 1)))) := by
    -- Sum the fixed-surface one-step lower bounds before restoring the common tilt term.
    refine Finset.sum_le_sum ?_
    intro j hj
    simpa [stepLower, ψk, tk] using
      pathFollowingFixedSurfaceStepDrop_ge_nativePlusShift
        (f := f) (Mf := Mf) y0 process j k
  have hpair_telescope :
      (Finset.range k).sum
          (fun j ↦ inner ℝ (∇ f (y0 : E)) (process.y j - process.y (j + 1))) =
        inner ℝ (∇ f (y0 : E)) ((y0 : E) - process.y k) :=
    pathFollowingBaseGradientPairing_telescope (f := f) (Mf := Mf) y0 process k
  have htilt_sum :
      (Finset.range k).sum
          (fun j ↦
            (Mf : ℝ) ^ (2 : ℕ) *
              (tk * inner ℝ (∇ f (y0 : E)) (process.y j - process.y (j + 1)))) =
        (Mf : ℝ) ^ (2 : ℕ) * tk *
          inner ℝ (∇ f (y0 : E)) ((y0 : E) - process.y k) := by
    -- Factor out the fixed scalars and telescope the remaining base-gradient pairings.
    calc
      (Finset.range k).sum
          (fun j ↦
            (Mf : ℝ) ^ (2 : ℕ) *
              (tk * inner ℝ (∇ f (y0 : E)) (process.y j - process.y (j + 1)))) =
        (Mf : ℝ) ^ (2 : ℕ) *
          (Finset.range k).sum
            (fun j ↦ tk * inner ℝ (∇ f (y0 : E)) (process.y j - process.y (j + 1))) := by
              rw [← Finset.mul_sum]
      _ =
        (Mf : ℝ) ^ (2 : ℕ) *
          (tk *
            (Finset.range k).sum
              (fun j ↦ inner ℝ (∇ f (y0 : E)) (process.y j - process.y (j + 1)))) := by
              congr 1
              rw [← Finset.mul_sum]
      _ =
        (Mf : ℝ) ^ (2 : ℕ) * tk *
          inner ℝ (∇ f (y0 : E)) ((y0 : E) - process.y k) := by
              rw [hpair_telescope]
              ring
  have hsum_actual :
      (Finset.range k).sum actualDrop =
        (Finset.range k).sum
          (fun j ↦ (Mf : ℝ) ^ (2 : ℕ) * (ψk (process.y j) - ψk (process.y (j + 1)))) +
        (Mf : ℝ) ^ (2 : ℕ) * tk *
          inner ℝ (∇ f (y0 : E)) ((y0 : E) - process.y k) := by
    -- Rewrite each actual drop on the fixed surface `ψ_k`, then telescope the common tilt term.
    calc
      (Finset.range k).sum actualDrop =
          (Finset.range k).sum
            (fun j ↦
              (Mf : ℝ) ^ (2 : ℕ) * (ψk (process.y j) - ψk (process.y (j + 1))) +
                (Mf : ℝ) ^ (2 : ℕ) *
                  (tk * inner ℝ (∇ f (y0 : E)) (process.y j - process.y (j + 1)))) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            dsimp [actualDrop]
            rw [pathFollowingObjectiveStep_gap_shift_currentSurface
              (f := f) (Mf := Mf) y0 process j k]
            ring
      _ =
          (Finset.range k).sum
            (fun j ↦ (Mf : ℝ) ^ (2 : ℕ) * (ψk (process.y j) - ψk (process.y (j + 1)))) +
            (Finset.range k).sum
              (fun j ↦
                (Mf : ℝ) ^ (2 : ℕ) *
                  (tk * inner ℝ (∇ f (y0 : E)) (process.y j - process.y (j + 1)))) := by
            rw [Finset.sum_add_distrib]
      _ =
          (Finset.range k).sum
            (fun j ↦ (Mf : ℝ) ^ (2 : ℕ) * (ψk (process.y j) - ψk (process.y (j + 1)))) +
            (Mf : ℝ) ^ (2 : ℕ) * tk *
              inner ℝ (∇ f (y0 : E)) ((y0 : E) - process.y k) := by
            rw [htilt_sum]
  calc
    (Finset.range k).sum stepLower +
        (Mf : ℝ) ^ (2 : ℕ) * tk *
          inner ℝ (∇ f (y0 : E)) ((y0 : E) - process.y k) ≤
      (Finset.range k).sum
          (fun j ↦ (Mf : ℝ) ^ (2 : ℕ) * (ψk (process.y j) - ψk (process.y (j + 1)))) +
        (Mf : ℝ) ^ (2 : ℕ) * tk *
          inner ℝ (∇ f (y0 : E)) ((y0 : E) - process.y k) := by
            exact add_le_add_right hpackage_le _
    _ = (Finset.range k).sum actualDrop := by
          rw [hsum_actual]

/-- Helper for Theorem 5 2 3: the terminal actual objective drop is the `j = k` instance of the
native-plus-shift rewrite on `f`. -/
private theorem pathFollowingTerminalObjectiveStep_gap_shift
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (y0 : dom)
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ)
    (k : ℕ) :
    let tk1 := (process.t (k + 1) : ℝ)
    let ψk1 := auxiliaryCentralPathObjective f y0 tk1
    f (process.y k) - f (process.y (k + 1)) =
      ψk1 (process.y k) - ψk1 (process.y (k + 1)) +
        tk1 * inner ℝ (∇ f (y0 : E)) (process.y k - process.y (k + 1)) := by
  -- This is exactly the `j = k` objective-gap normalization used in the positive-`κ` branch.
  simpa using pathFollowingObjectiveStep_gap_shift (f := f) (Mf := Mf) y0 process k

/-- Helper for Theorem 5 2 3: the terminal actual objective drop can be rewritten on the same
fixed surface `ψ_k` used for the accumulated prefix package. -/
private theorem pathFollowingTerminalObjectiveStep_gap_shift_currentSurface
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (y0 : dom)
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ)
    (k : ℕ) :
    let ψk := auxiliaryCentralPathObjective f y0 (process.t k : ℝ)
    f (process.y k) - f (process.y (k + 1)) =
      ψk (process.y k) - ψk (process.y (k + 1)) +
        (process.t k : ℝ) *
          inner ℝ (∇ f (y0 : E)) (process.y k - process.y (k + 1)) := by
  -- Reuse the fixed-surface rewrite specialized to the terminal index `j = k`.
  simpa using
    pathFollowingObjectiveStep_gap_shift_currentSurface
      (f := f) (Mf := Mf) y0 process k k

/-- Helper for Theorem 5 2 3: the centered decrement on the intermediate surface `ψ_{j+1}` is
uniformly bounded by `τ / M_f` along the path-following process. -/
private theorem pathFollowingIntermediateSurfaceDecrement_le_tau_div
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (hτ_nonneg : 0 ≤ τ) (htau : τ ≤ 0.23) (y0 : dom)
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ)
    (centering :
      ∀ j : ℕ,
        satisfies_approximate_centering_condition f y0 (process.t j) (process.y j)
          (process.mem_domain j) Mf (pathFollowingCenteringBeta τ))
    (j : ℕ) :
    let tj1 := (process.t (j + 1) : ℝ)
    let ψj1 := auxiliaryCentralPathObjective f y0 tj1
    let δj := λ[ψj1; process.y j | process.mem_domain j]
    δj ≤ τ / (Mf : ℝ) := by
  let tj1 := (process.t (j + 1) : ℝ)
  let ψj1 := auxiliaryCentralPathObjective f y0 tj1
  let δj := λ[ψj1; process.y j | process.mem_domain j]
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero Mf))
  have hγ_nonneg : 0 ≤ pathFollowingGammaRadius τ :=
    pathFollowingGammaRadius_nonneg hτ_nonneg htau
  have hcenter_old :
      λ[auxiliaryCentralPathObjective f y0 (process.t j : ℝ); process.y j |
          process.mem_domain j] ≤
        pathFollowingCenteringBeta τ / (Mf : ℝ) := by
    -- Read the centering invariant at the current iterate in its explicit decrement form.
    exact
      (satisfies_approximate_centering_condition_iff
        f y0 (process.t j) (process.y j) (process.mem_domain j) Mf
        (pathFollowingCenteringBeta τ)).1 (centering j)
  have hδ_le_shifted :
      δj ≤
        λ[auxiliaryCentralPathObjective f y0 (process.t j : ℝ); process.y j |
            process.mem_domain j] +
          |tj1 - (process.t j : ℝ)| *
            pathFollowingObjectiveNorm f y0 (process.y j) (process.mem_domain j) := by
    -- Compare the new centered decrement at `t_{j+1}` with the old one at `t_j`.
    simpa [δj, ψj1, tj1] using
      auxiliaryCentralPathObjective_decrement_le_add_objectiveNorm_mul_abs_sub
        (f := f) y0 (hy := process.mem_domain j) (process.t j : ℝ) tj1
  have hstep_eq :
      |tj1 - (process.t j : ℝ)| *
          pathFollowingObjectiveNorm f y0 (process.y j) (process.mem_domain j) =
        pathFollowingGammaRadius τ / (Mf : ℝ) := by
    -- Normalize the public scalar path update at index `j`.
    have hstep_t :
        (pathFollowingUpdate f Mf y0 (process.t j) (process.y j)
          (process.mem_domain j) (process.objectiveNorm_pos j)
          (pathFollowingGammaRadius τ)).1 = tj1 := by
      simpa [tj1] using congrArg Prod.fst (process.step_eq j).symm
    have hObjectiveNorm_nonneg :
        0 ≤ pathFollowingObjectiveNorm f y0 (process.y j) (process.mem_domain j) := by
      exact le_of_lt (process.objectiveNorm_pos j)
    calc
      |tj1 - (process.t j : ℝ)| *
          pathFollowingObjectiveNorm f y0 (process.y j) (process.mem_domain j) =
          |(process.t j : ℝ) -
              pathFollowingGammaRadius τ /
                ((Mf : ℝ) *
                  pathFollowingObjectiveNorm f y0 (process.y j) (process.mem_domain j)) -
            (process.t j : ℝ)| *
            pathFollowingObjectiveNorm f y0 (process.y j) (process.mem_domain j) := by
              rw [← hstep_t]
      _ =
          |(-pathFollowingGammaRadius τ) /
              ((Mf : ℝ) *
                pathFollowingObjectiveNorm f y0 (process.y j) (process.mem_domain j))| *
            pathFollowingObjectiveNorm f y0 (process.y j) (process.mem_domain j) := by
              congr 1
              ring
      _ =
          (|pathFollowingGammaRadius τ| /
              ((Mf : ℝ) *
                pathFollowingObjectiveNorm f y0 (process.y j) (process.mem_domain j))) *
            pathFollowingObjectiveNorm f y0 (process.y j) (process.mem_domain j) := by
              rw [abs_div, abs_neg, abs_mul, abs_of_pos hMf_pos,
                abs_of_nonneg hObjectiveNorm_nonneg]
      _ =
          (pathFollowingGammaRadius τ /
              ((Mf : ℝ) *
                pathFollowingObjectiveNorm f y0 (process.y j) (process.mem_domain j))) *
            pathFollowingObjectiveNorm f y0 (process.y j) (process.mem_domain j) := by
              rw [abs_of_nonneg hγ_nonneg]
      _ = pathFollowingGammaRadius τ / (Mf : ℝ) := by
            field_simp [hMf_pos.ne', (process.objectiveNorm_pos j).ne']
            ring
  have hsum :
      pathFollowingCenteringBeta τ + pathFollowingGammaRadius τ ≤ τ := by
    -- The admissible radius is defined precisely so that `β(τ) + γ(τ) = τ`.
    simp [pathFollowingGammaRadius]
  have hδ_le :
      δj ≤ τ / (Mf : ℝ) := by
    calc
      δj ≤
          pathFollowingCenteringBeta τ / (Mf : ℝ) +
            |tj1 - (process.t j : ℝ)| *
              pathFollowingObjectiveNorm f y0 (process.y j) (process.mem_domain j) := by
                exact le_trans hδ_le_shifted (add_le_add hcenter_old le_rfl)
      _ =
          pathFollowingCenteringBeta τ / (Mf : ℝ) +
            pathFollowingGammaRadius τ / (Mf : ℝ) := by
              rw [hstep_eq]
      _ ≤ τ / (Mf : ℝ) := by
            simpa [add_div] using
              (div_le_div_of_nonneg_right hsum (le_of_lt hMf_pos))
  simpa [δj] using hδ_le

/-- Helper for Theorem 5 2 3: the centered intermediate decrement at index `j`, rewritten as the
dimensionless scalar `s_j = M_f δ_j`, is bounded above by `τ`. -/
private theorem pathFollowingScaledIntermediateSurfaceDecrement_le_tau
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (hτ_nonneg : 0 ≤ τ) (htau : τ ≤ 0.23) (y0 : dom)
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ)
    (centering :
      ∀ j : ℕ,
        satisfies_approximate_centering_condition f y0 (process.t j) (process.y j)
          (process.mem_domain j) Mf (pathFollowingCenteringBeta τ))
    (j : ℕ) :
    let tj1 := (process.t (j + 1) : ℝ)
    let ψj1 := auxiliaryCentralPathObjective f y0 tj1
    let δj := λ[ψj1; process.y j | process.mem_domain j]
    (Mf : ℝ) * δj ≤ τ := by
  let tj1 := (process.t (j + 1) : ℝ)
  let ψj1 := auxiliaryCentralPathObjective f y0 tj1
  let δj := λ[ψj1; process.y j | process.mem_domain j]
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero Mf))
  have hbase :
      δj ≤ τ / (Mf : ℝ) := by
    -- Reuse the centered decrement bound before clearing the positive `M_f` denominator.
    simpa [tj1, ψj1, δj] using
      pathFollowingIntermediateSurfaceDecrement_le_tau_div
        (f := f) (Mf := Mf) hτ_nonneg htau y0 process centering j
  have hscaled := mul_le_mul_of_nonneg_left hbase hMf_pos.le
  -- The normalized variable `s_j` is exactly the left-hand side after multiplying by `M_f`.
  calc
    (Mf : ℝ) * δj ≤ (Mf : ℝ) * (τ / (Mf : ℝ)) := hscaled
    _ = τ := by
          field_simp [hMf_pos.ne']

/-- Helper for Theorem 5 2 3: the intermediate path-following displacement has the textbook
local-norm ratio on the updated tilted surface `ψ_{j+1}`. -/
private theorem pathFollowingIntermediateStep_localNorm_eq_decrementRatio
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (y0 : dom)
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ)
    (j : ℕ) :
    let tj1 := (process.t (j + 1) : ℝ)
    let ψj1 := auxiliaryCentralPathObjective f y0 tj1
    let δj := λ[ψj1; process.y j | process.mem_domain j]
    ‖process.y (j + 1) - process.y j‖[ψj1; process.y j] =
      δj * (1 + (Mf : ℝ) * δj) /
        (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ)) := by
  let tj1 := (process.t (j + 1) : ℝ)
  let ψj1 := auxiliaryCentralPathObjective f y0 tj1
  let δj := λ[ψj1; process.y j | process.mem_domain j]
  let hH :
      (hessian ψj1 (process.y j)).det ≠ 0 :=
    auxiliaryCentralPathObjective_hessian_det_ne_zero f y0 tj1 (process.mem_domain j)
  have hstep_t :
      (pathFollowingUpdate f Mf y0 (process.t j) (process.y j)
        (process.mem_domain j) (process.objectiveNorm_pos j)
        (pathFollowingGammaRadius τ)).1 = tj1 := by
    -- Read the new path parameter back from the public process update.
    simpa [tj1] using congrArg Prod.fst (process.step_eq j).symm
  have hstep_y :
      process.y (j + 1) =
        selfConcordantNewtonNextPoint ψj1 (Mf : NNReal) .intermediate
          (process.y j) (process.mem_domain j) hH := by
    -- Route correction: rewrite the successor iterate through `pathFollowingUpdate` before using
    -- the canonical intermediate-step norm formula.
    calc
      process.y (j + 1) =
          (pathFollowingUpdate f Mf y0 (process.t j) (process.y j)
            (process.mem_domain j) (process.objectiveNorm_pos j)
            (pathFollowingGammaRadius τ)).2 := by
              simpa using (congrArg Prod.snd (process.step_eq j).symm).symm
      _ =
          selfConcordantNewtonNextPoint
            (auxiliaryCentralPathObjective f y0
              ((pathFollowingUpdate f Mf y0 (process.t j) (process.y j)
                (process.mem_domain j) (process.objectiveNorm_pos j)
                (pathFollowingGammaRadius τ)).1))
            (Mf : NNReal) .intermediate
            (process.y j) (process.mem_domain j)
            (auxiliaryCentralPathObjective_hessian_det_ne_zero f y0
              ((pathFollowingUpdate f Mf y0 (process.t j) (process.y j)
                (process.mem_domain j) (process.objectiveNorm_pos j)
                (pathFollowingGammaRadius τ)).1) (process.mem_domain j)) := by
              simpa using
                pathFollowingUpdate_snd f Mf y0 (process.t j) (process.y j)
                  (process.mem_domain j) (process.objectiveNorm_pos j)
                  (pathFollowingGammaRadius τ)
      _ =
          selfConcordantNewtonNextPoint ψj1 (Mf : NNReal) .intermediate
            (process.y j) (process.mem_domain j) hH := by
              rw [hstep_t]
  have hδj :
      δj =
        NewtonDecrement.ofDetNeZero (Mf : NNReal) ψj1 (process.mem_domain j) hH := by
    -- The source-facing centered decrement notation is just the determinant-based one here.
    simpa [δj]
  calc
    ‖process.y (j + 1) - process.y j‖[ψj1; process.y j] =
        ‖selfConcordantNewtonNextPoint ψj1 (Mf : NNReal) .intermediate
            (process.y j) (process.mem_domain j) hH - process.y j‖[ψj1; process.y j] := by
          rw [hstep_y]
    _ =
        selfConcordantNewtonStepSize ψj1 (Mf : NNReal) .intermediate
            (process.y j) (process.mem_domain j) hH *
          NewtonDecrement.ofDetNeZero (Mf : NNReal) ψj1 (process.mem_domain j) hH := by
            simpa using
              next_point_sub_localNorm_eq_stepSize_mul_ndec
                (dom := dom) (Mf := Mf) (f := ψj1) .intermediate (process.mem_domain j) hH
    _ =
        ((1 + (Mf : ℝ) * NewtonDecrement.ofDetNeZero
            (Mf : NNReal) ψj1 (process.mem_domain j) hH) /
          (1 + (Mf : ℝ) * NewtonDecrement.ofDetNeZero
              (Mf : NNReal) ψj1 (process.mem_domain j) hH +
            (Mf : ℝ) ^ (2 : ℕ) *
              (NewtonDecrement.ofDetNeZero
                (Mf : NNReal) ψj1 (process.mem_domain j) hH) ^ (2 : ℕ))) *
          NewtonDecrement.ofDetNeZero (Mf : NNReal) ψj1 (process.mem_domain j) hH := by
            rw [intermediate_stepSize_eq
              (dom := dom) (Mf := Mf) (f := ψj1) (process.mem_domain j) hH]
    _ =
        δj * (1 + (Mf : ℝ) * δj) /
          (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ)) := by
            rw [hδj]
            field_simp

/-- Helper for Theorem 5 2 3: the odd-weight control is automatic whenever `κ(τ) ≤ 0`, because
the left-hand side is then nonpositive while the initial objective gap is nonnegative. -/
private theorem pathFollowingObjectiveNorm_odd_control_of_kappa_nonpos
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (y0 : dom) (xStar : dom)
    (hmin : IsMinOn f dom (xStar : E))
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ)
    (k : ℕ)
    (hkappa_nonpos : pathFollowingKappa τ ≤ 0) :
    pathFollowingKappa τ * (2 * k + 1 : ℝ) * (Mf : ℝ) *
        pathFollowingObjectiveNorm f y0 (process.y k) (process.mem_domain k) ≤
      (Mf : ℝ) ^ (2 : ℕ) * (f (y0 : E) - f (xStar : E)) := by
  have hMf_nonneg : 0 ≤ (Mf : ℝ) := by positivity
  have hkodd_nonneg : 0 ≤ (2 * k + 1 : ℝ) := by positivity
  have hnorm_nonneg :
      0 ≤ pathFollowingObjectiveNorm f y0 (process.y k) (process.mem_domain k) := by
    exact (process.objectiveNorm_pos k).le
  have hlhs_nonpos :
      pathFollowingKappa τ * (2 * k + 1 : ℝ) * (Mf : ℝ) *
          pathFollowingObjectiveNorm f y0 (process.y k) (process.mem_domain k) ≤ 0 := by
    -- Multiply the nonpositive `κ(τ)` by the nonnegative geometric factors.
    have htail_nonneg :
        0 ≤ (2 * k + 1 : ℝ) * (Mf : ℝ) *
          pathFollowingObjectiveNorm f y0 (process.y k) (process.mem_domain k) := by
      positivity
    have hprod_nonpos :
        pathFollowingKappa τ *
            ((2 * k + 1 : ℝ) * (Mf : ℝ) *
              pathFollowingObjectiveNorm f y0 (process.y k) (process.mem_domain k)) ≤ 0 := by
      exact mul_nonpos_of_nonpos_of_nonneg hkappa_nonpos htail_nonneg
    simpa [mul_assoc] using hprod_nonpos
  have hrhs_nonneg :
      0 ≤ (Mf : ℝ) ^ (2 : ℕ) * (f (y0 : E) - f (xStar : E)) := by
    -- The minimizer gap is nonnegative, so the scaled right-hand side is as well.
    have hgap_nonneg :=
      pathFollowingInitialGap_nonneg (Mf := Mf) (f := f) y0 xStar hmin
    positivity
  exact le_trans hlhs_nonpos hrhs_nonneg

/-- Helper for Theorem 5 2 3: the prefix package together with the terminal objective drop reduces
to the current objective gap plus the residual tilt term still anchored at `y_k`. -/
private theorem pathFollowingPrefixPackagePlusTerminal_le_currentGapWithBaseTilt
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (y0 : dom)
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ)
    (k : ℕ) :
    let tk := (process.t k : ℝ)
    let ψk := auxiliaryCentralPathObjective f y0 tk
    let stepLower : ℕ → ℝ := fun j ↦
      let tj1 := (process.t (j + 1) : ℝ)
      let ψj1 := auxiliaryCentralPathObjective f y0 tj1
      let δj := λ[ψj1; process.y j | process.mem_domain j]
      (Mf : ℝ) ^ (2 : ℕ) *
          (δj ^ (2 : ℕ) /
              (2 * (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ))) +
            (Mf : ℝ) * δj ^ (3 : ℕ) /
              (2 * (1 + (Mf : ℝ) * δj) * (3 + 2 * (Mf : ℝ) * δj))) +
        (Mf : ℝ) ^ (2 : ℕ) *
          (((process.t (j + 1) : ℝ) - tk) *
            inner ℝ (∇ f (y0 : E)) (process.y j - process.y (j + 1)))
    (Finset.range k).sum stepLower +
        (Mf : ℝ) ^ (2 : ℕ) * (f (process.y k) - f (process.y (k + 1))) ≤
      (Mf : ℝ) ^ (2 : ℕ) *
        (f (y0 : E) - f (process.y (k + 1)) -
          tk * inner ℝ (∇ f (y0 : E)) ((y0 : E) - process.y k)) := by
  let tk := (process.t k : ℝ)
  let ψk := auxiliaryCentralPathObjective f y0 tk
  let stepLower : ℕ → ℝ := fun j ↦
    let tj1 := (process.t (j + 1) : ℝ)
    let ψj1 := auxiliaryCentralPathObjective f y0 tj1
    let δj := λ[ψj1; process.y j | process.mem_domain j]
    (Mf : ℝ) ^ (2 : ℕ) *
        (δj ^ (2 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ))) +
          (Mf : ℝ) * δj ^ (3 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δj) * (3 + 2 * (Mf : ℝ) * δj))) +
      (Mf : ℝ) ^ (2 : ℕ) *
        (((process.t (j + 1) : ℝ) - tk) *
          inner ℝ (∇ f (y0 : E)) (process.y j - process.y (j + 1)))
  have hprefix_lower :
      (Finset.range k).sum stepLower ≤
        (Mf : ℝ) ^ (2 : ℕ) * (ψk (y0 : E) - ψk (process.y k)) := by
    -- Keep the accumulated package on the fixed `ψ_k` surface before appending the terminal drop.
    simpa [ψk, stepLower] using
      pathFollowingAccumulatedGap_ge_nativePlusShift
        (f := f) (Mf := Mf) y0 process k
  -- Append the terminal `f`-gap and expand `ψ_k` only once into the residual tilt correction.
  calc
    (Finset.range k).sum stepLower +
        (Mf : ℝ) ^ (2 : ℕ) * (f (process.y k) - f (process.y (k + 1))) ≤
      (Mf : ℝ) ^ (2 : ℕ) * (ψk (y0 : E) - ψk (process.y k)) +
        (Mf : ℝ) ^ (2 : ℕ) * (f (process.y k) - f (process.y (k + 1))) := by
          exact add_le_add_right hprefix_lower _
    _ =
      (Mf : ℝ) ^ (2 : ℕ) *
        (f (y0 : E) - f (process.y (k + 1)) -
          tk * inner ℝ (∇ f (y0 : E)) ((y0 : E) - process.y k)) := by
            -- Expand the fixed-surface gap and normalize the base-point tilt once.
            simp [ψk, tk, auxiliaryCentralPathObjective_apply]
            ring

/-- Helper for Theorem 5 2 3: the residual current-gap package is bounded by the initial gap plus
the remaining minimizer pairing `t_k ⟪∇ f(y₀), xStar - y_k⟫`. -/
private theorem pathFollowingCurrentGapWithBaseTilt_le_initialGapWithMinimizerPairing
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (y0 : dom) (xStar : dom)
    (hmin : IsMinOn f dom (xStar : E))
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ)
    (k : ℕ) :
    let tk := (process.t k : ℝ)
    (Mf : ℝ) ^ (2 : ℕ) *
        (f (y0 : E) - f (process.y (k + 1)) -
          tk * inner ℝ (∇ f (y0 : E)) ((y0 : E) - process.y k)) ≤
      (Mf : ℝ) ^ (2 : ℕ) *
        ((1 - tk) * (f (y0 : E) - f (xStar : E)) +
          tk * inner ℝ (∇ f (y0 : E)) ((xStar : E) - process.y k)) := by
  let tk := (process.t k : ℝ)
  have hMf_sq_nonneg : 0 ≤ (Mf : ℝ) ^ (2 : ℕ) := by
    positivity
  have hendpoint :
      f (xStar : E) ≤ f (process.y (k + 1)) := by
    -- The chosen minimizer cannot exceed the next process value.
    exact (isMinOn_iff.mp hmin) _ (process.mem_domain (k + 1))
  have htilted :
      auxiliaryCentralPathObjective f y0 tk (y0 : E) -
          auxiliaryCentralPathObjective f y0 tk (xStar : E) ≤
        (1 - tk) * (f (y0 : E) - f (xStar : E)) := by
    -- Apply the minimizer-side tilted-gap estimate at the current parameter `t_k`.
    simpa [tk] using
      pathFollowingBasePoint_tiltedGap_le_one_sub_mul_initialGap
        (f := f) (Mf := Mf) y0 xStar (process.t k)
  have hresidual :
      (Mf : ℝ) ^ (2 : ℕ) *
          (f (xStar : E) - f (process.y (k + 1)) +
            tk * inner ℝ (∇ f (y0 : E)) ((xStar : E) - process.y k)) ≤
        (Mf : ℝ) ^ (2 : ℕ) *
          (tk * inner ℝ (∇ f (y0 : E)) ((xStar : E) - process.y k)) := by
    -- The endpoint term is nonpositive, so it can be dropped from the residual package.
    have hcore :
        f (xStar : E) - f (process.y (k + 1)) +
            tk * inner ℝ (∇ f (y0 : E)) ((xStar : E) - process.y k) ≤
          tk * inner ℝ (∇ f (y0 : E)) ((xStar : E) - process.y k) := by
      linarith
    exact mul_le_mul_of_nonneg_left hcore hMf_sq_nonneg
  -- Split the anchored current gap at `xStar` and bound the two pieces separately.
  calc
    (Mf : ℝ) ^ (2 : ℕ) *
        (f (y0 : E) - f (process.y (k + 1)) -
          tk * inner ℝ (∇ f (y0 : E)) ((y0 : E) - process.y k)) =
      (Mf : ℝ) ^ (2 : ℕ) *
          (auxiliaryCentralPathObjective f y0 tk (y0 : E) -
            auxiliaryCentralPathObjective f y0 tk (xStar : E)) +
        (Mf : ℝ) ^ (2 : ℕ) *
          (f (xStar : E) - f (process.y (k + 1)) +
            tk * inner ℝ (∇ f (y0 : E)) ((xStar : E) - process.y k)) := by
          -- Expand the tilted objective once and regroup the minimizer residual explicitly.
          simp [tk, auxiliaryCentralPathObjective_apply]
          ring
    _ ≤
      (Mf : ℝ) ^ (2 : ℕ) * ((1 - tk) * (f (y0 : E) - f (xStar : E))) +
        (Mf : ℝ) ^ (2 : ℕ) *
          (tk * inner ℝ (∇ f (y0 : E)) ((xStar : E) - process.y k)) := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left htilted hMf_sq_nonneg)
              hresidual
    _ =
      (Mf : ℝ) ^ (2 : ℕ) *
        ((1 - tk) * (f (y0 : E) - f (xStar : E)) +
          tk * inner ℝ (∇ f (y0 : E)) ((xStar : E) - process.y k)) := by
            ring

/-- Helper for Theorem 5 2 3: after collapsing the prefix package to the anchored current gap,
the minimizer comparison leaves only the residual pairing `t_k ⟪∇ f(y₀), xStar - y_k⟫`. -/
private theorem pathFollowingPrefixPackagePlusTerminal_le_initialGapWithMinimizerPairing
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (y0 : dom) (xStar : dom)
    (hmin : IsMinOn f dom (xStar : E))
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ)
    (k : ℕ) :
    let tk := (process.t k : ℝ)
    let stepLower : ℕ → ℝ := fun j ↦
      let tj1 := (process.t (j + 1) : ℝ)
      let ψj1 := auxiliaryCentralPathObjective f y0 tj1
      let δj := λ[ψj1; process.y j | process.mem_domain j]
      (Mf : ℝ) ^ (2 : ℕ) *
          (δj ^ (2 : ℕ) /
              (2 * (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ))) +
            (Mf : ℝ) * δj ^ (3 : ℕ) /
              (2 * (1 + (Mf : ℝ) * δj) * (3 + 2 * (Mf : ℝ) * δj))) +
        (Mf : ℝ) ^ (2 : ℕ) *
          (((process.t (j + 1) : ℝ) - tk) *
            inner ℝ (∇ f (y0 : E)) (process.y j - process.y (j + 1)))
    (Finset.range k).sum stepLower +
        (Mf : ℝ) ^ (2 : ℕ) * (f (process.y k) - f (process.y (k + 1))) ≤
      (Mf : ℝ) ^ (2 : ℕ) *
        ((1 - tk) * (f (y0 : E) - f (xStar : E)) +
          tk * inner ℝ (∇ f (y0 : E)) ((xStar : E) - process.y k)) := by
  let tk := (process.t k : ℝ)
  let stepLower : ℕ → ℝ := fun j ↦
    let tj1 := (process.t (j + 1) : ℝ)
    let ψj1 := auxiliaryCentralPathObjective f y0 tj1
    let δj := λ[ψj1; process.y j | process.mem_domain j]
    (Mf : ℝ) ^ (2 : ℕ) *
        (δj ^ (2 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ))) +
          (Mf : ℝ) * δj ^ (3 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δj) * (3 + 2 * (Mf : ℝ) * δj))) +
      (Mf : ℝ) ^ (2 : ℕ) *
        (((process.t (j + 1) : ℝ) - tk) *
          inner ℝ (∇ f (y0 : E)) (process.y j - process.y (j + 1)))
  have hpackage :=
    pathFollowingPrefixPackagePlusTerminal_le_currentGapWithBaseTilt
      (f := f) (Mf := Mf) y0 process k
  have hcurrent :=
    pathFollowingCurrentGapWithBaseTilt_le_initialGapWithMinimizerPairing
      (f := f) (Mf := Mf) y0 xStar hmin process k
  -- First collapse to the anchored current-gap package, then transport that package to `xStar`.
  exact le_trans (by simpa [stepLower, tk] using hpackage) (by simpa [tk] using hcurrent)

/-- Helper for Theorem 5 2 3: comparing the base-point supporting-nesterovHyperplane bounds at `xStar`
and `y_k` controls the residual minimizer pairing by the corresponding objective gap. -/
private theorem pathFollowingMinimizerPairing_le_baseGap
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    {τ : ℝ} (y0 : dom) (xStar : dom)
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ)
    (k : ℕ) :
    inner ℝ (∇ f (y0 : E)) ((xStar : E) - process.y k) ≤
      f (xStar : E) - f (process.y k) := by
  have hxStar_support :
      inner ℝ (∇ f (y0 : E)) ((xStar : E) - (y0 : E)) ≤
        f (xStar : E) - f (y0 : E) :=
    pathFollowingBasePoint_supportingHyperplane (Mf := Mf) (f := f) (y0 := y0) xStar.2
  have hyk_support :
      inner ℝ (∇ f (y0 : E)) (process.y k - (y0 : E)) ≤
        f (process.y k) - f (y0 : E) :=
    pathFollowingBasePoint_supportingHyperplane
      (Mf := Mf) (f := f) (y0 := y0) (process.mem_domain k)
  -- Subtract the two supporting-nesterovHyperplane bounds so the base point `y₀` cancels out.
  linarith [hxStar_support, hyk_support]

/-- Helper for Theorem 5 2 3: once the residual minimizer pairing is known to be nonpositive, the
full prefix-plus-terminal package is bounded by the initial objective gap alone. -/
private theorem pathFollowingPrefixPackagePlusTerminal_le_initialGap
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (y0 : dom) (xStar : dom)
    (hmin : IsMinOn f dom (xStar : E))
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ)
    (k : ℕ) :
    let tk := (process.t k : ℝ)
    let stepLower : ℕ → ℝ := fun j ↦
      let tj1 := (process.t (j + 1) : ℝ)
      let ψj1 := auxiliaryCentralPathObjective f y0 tj1
      let δj := λ[ψj1; process.y j | process.mem_domain j]
      (Mf : ℝ) ^ (2 : ℕ) *
          (δj ^ (2 : ℕ) /
              (2 * (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ))) +
            (Mf : ℝ) * δj ^ (3 : ℕ) /
              (2 * (1 + (Mf : ℝ) * δj) * (3 + 2 * (Mf : ℝ) * δj))) +
        (Mf : ℝ) ^ (2 : ℕ) *
          (((process.t (j + 1) : ℝ) - tk) *
            inner ℝ (∇ f (y0 : E)) (process.y j - process.y (j + 1)))
    (Finset.range k).sum stepLower +
        (Mf : ℝ) ^ (2 : ℕ) * (f (process.y k) - f (process.y (k + 1))) ≤
      (Mf : ℝ) ^ (2 : ℕ) * (f (y0 : E) - f (xStar : E)) := by
  let tk := (process.t k : ℝ)
  let stepLower : ℕ → ℝ := fun j ↦
    let tj1 := (process.t (j + 1) : ℝ)
    let ψj1 := auxiliaryCentralPathObjective f y0 tj1
    let δj := λ[ψj1; process.y j | process.mem_domain j]
    (Mf : ℝ) ^ (2 : ℕ) *
        (δj ^ (2 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ))) +
          (Mf : ℝ) * δj ^ (3 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δj) * (3 + 2 * (Mf : ℝ) * δj))) +
      (Mf : ℝ) ^ (2 : ℕ) *
        (((process.t (j + 1) : ℝ) - tk) *
          inner ℝ (∇ f (y0 : E)) (process.y j - process.y (j + 1)))
  have hMf_sq_nonneg : 0 ≤ (Mf : ℝ) ^ (2 : ℕ) := by
    positivity
  have hgap_nonneg : 0 ≤ f (y0 : E) - f (xStar : E) :=
    pathFollowingInitialGap_nonneg (Mf := Mf) (f := f) y0 xStar hmin
  have hpairing_gap :
      inner ℝ (∇ f (y0 : E)) ((xStar : E) - process.y k) ≤
        f (xStar : E) - f (process.y k) :=
    pathFollowingMinimizerPairing_le_baseGap (Mf := Mf) (f := f) y0 xStar process k
  have hxStar_le_yk : f (xStar : E) ≤ f (process.y k) := by
    -- The minimizer cannot exceed the `k`-th process objective value.
    exact (isMinOn_iff.mp hmin) _ (process.mem_domain k)
  have hpairing_nonpos :
      inner ℝ (∇ f (y0 : E)) ((xStar : E) - process.y k) ≤ 0 := by
    -- Compare the residual pairing against the nonpositive minimizer gap at `y_k`.
    linarith [hpairing_gap, hxStar_le_yk]
  have hcore :
      (1 - tk) * (f (y0 : E) - f (xStar : E)) +
          tk * inner ℝ (∇ f (y0 : E)) ((xStar : E) - process.y k) ≤
        f (y0 : E) - f (xStar : E) := by
    have htk_nonneg : 0 ≤ tk := (process.t k).2.1
    have htk_le_one : tk ≤ 1 := (process.t k).2.2
    -- Drop the nonpositive residual pairing and use `1 - t_k ≤ 1`.
    linarith
  have hpackage :=
    pathFollowingPrefixPackagePlusTerminal_le_initialGapWithMinimizerPairing
      (f := f) (Mf := Mf) y0 xStar hmin process k
  -- Collapse the minimizer-anchored package to the plain initial objective gap.
  refine le_trans (by simpa [stepLower, tk] using hpackage) ?_
  exact mul_le_mul_of_nonneg_left hcore hMf_sq_nonneg

/-- Helper for Theorem 5 2 3: the fixed-surface prefix package plus the common `t_k` tilt term
can be rewritten as a pure prefix sum whose pairing coefficient is `t_{j+1}` at each step. -/
private theorem pathFollowingFixedSurfacePackageWithBaseTilt_eq_sumPrefixTerms
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (y0 : dom)
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ)
    (k : ℕ) :
    let tk := (process.t k : ℝ)
    let stepLower : ℕ → ℝ := fun j ↦
      let tj1 := (process.t (j + 1) : ℝ)
      let ψj1 := auxiliaryCentralPathObjective f y0 tj1
      let δj := λ[ψj1; process.y j | process.mem_domain j]
      (Mf : ℝ) ^ (2 : ℕ) *
          (δj ^ (2 : ℕ) /
              (2 * (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ))) +
            (Mf : ℝ) * δj ^ (3 : ℕ) /
              (2 * (1 + (Mf : ℝ) * δj) * (3 + 2 * (Mf : ℝ) * δj))) +
        (Mf : ℝ) ^ (2 : ℕ) *
          (((process.t (j + 1) : ℝ) - tk) *
            inner ℝ (∇ f (y0 : E)) (process.y j - process.y (j + 1)))
    let prefixTerm : ℕ → ℝ := fun j ↦
      let tj1 := (process.t (j + 1) : ℝ)
      let ψj1 := auxiliaryCentralPathObjective f y0 tj1
      let δj := λ[ψj1; process.y j | process.mem_domain j]
      (Mf : ℝ) ^ (2 : ℕ) *
          (δj ^ (2 : ℕ) /
              (2 * (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ))) +
            (Mf : ℝ) * δj ^ (3 : ℕ) /
              (2 * (1 + (Mf : ℝ) * δj) * (3 + 2 * (Mf : ℝ) * δj))) +
        (Mf : ℝ) ^ (2 : ℕ) *
          ((process.t (j + 1) : ℝ) *
            inner ℝ (∇ f (y0 : E)) (process.y j - process.y (j + 1)))
    (Finset.range k).sum stepLower +
        (Mf : ℝ) ^ (2 : ℕ) * tk *
          inner ℝ (∇ f (y0 : E)) ((y0 : E) - process.y k) =
      (Finset.range k).sum prefixTerm := by
  let tk := (process.t k : ℝ)
  let pairing : ℕ → ℝ := fun j ↦
    inner ℝ (∇ f (y0 : E)) (process.y j - process.y (j + 1))
  let stepLower : ℕ → ℝ := fun j ↦
    let tj1 := (process.t (j + 1) : ℝ)
    let ψj1 := auxiliaryCentralPathObjective f y0 tj1
    let δj := λ[ψj1; process.y j | process.mem_domain j]
    (Mf : ℝ) ^ (2 : ℕ) *
        (δj ^ (2 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ))) +
          (Mf : ℝ) * δj ^ (3 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δj) * (3 + 2 * (Mf : ℝ) * δj))) +
      (Mf : ℝ) ^ (2 : ℕ) * (((process.t (j + 1) : ℝ) - tk) * pairing j)
  let prefixTerm : ℕ → ℝ := fun j ↦
    let tj1 := (process.t (j + 1) : ℝ)
    let ψj1 := auxiliaryCentralPathObjective f y0 tj1
    let δj := λ[ψj1; process.y j | process.mem_domain j]
    (Mf : ℝ) ^ (2 : ℕ) *
        (δj ^ (2 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ))) +
          (Mf : ℝ) * δj ^ (3 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δj) * (3 + 2 * (Mf : ℝ) * δj))) +
      (Mf : ℝ) ^ (2 : ℕ) * ((process.t (j + 1) : ℝ) * pairing j)
  have hpair_telescope :
      (Finset.range k).sum pairing =
        inner ℝ (∇ f (y0 : E)) ((y0 : E) - process.y k) := by
    -- Telescope the fixed base-gradient pairings before distributing the common `t_k` factor.
    simpa [pairing] using
      pathFollowingBaseGradientPairing_telescope (f := f) (Mf := Mf) y0 process k
  have htilt_sum :
      (Mf : ℝ) ^ (2 : ℕ) * tk *
          inner ℝ (∇ f (y0 : E)) ((y0 : E) - process.y k) =
        (Finset.range k).sum (fun j ↦ (Mf : ℝ) ^ (2 : ℕ) * (tk * pairing j)) := by
    -- Rewrite the common tilt term as a sum so it can be merged pointwise with `stepLower`.
    calc
      (Mf : ℝ) ^ (2 : ℕ) * tk *
          inner ℝ (∇ f (y0 : E)) ((y0 : E) - process.y k) =
        (Mf : ℝ) ^ (2 : ℕ) * tk * (Finset.range k).sum pairing := by
            rw [hpair_telescope]
      _ =
        (Mf : ℝ) ^ (2 : ℕ) *
          ((Finset.range k).sum (fun j ↦ tk * pairing j)) := by
            rw [← Finset.mul_sum]
      _ =
        (Finset.range k).sum (fun j ↦ (Mf : ℝ) ^ (2 : ℕ) * (tk * pairing j)) := by
            rw [← Finset.mul_sum]
  calc
    (Finset.range k).sum stepLower +
        (Mf : ℝ) ^ (2 : ℕ) * tk *
          inner ℝ (∇ f (y0 : E)) ((y0 : E) - process.y k) =
      (Finset.range k).sum stepLower +
        (Finset.range k).sum (fun j ↦ (Mf : ℝ) ^ (2 : ℕ) * (tk * pairing j)) := by
          rw [htilt_sum]
    _ =
      (Finset.range k).sum
        (fun j ↦ stepLower j + (Mf : ℝ) ^ (2 : ℕ) * (tk * pairing j)) := by
          rw [← Finset.sum_add_distrib]
    _ = (Finset.range k).sum prefixTerm := by
      -- After distributing the common tilt through the sum, each coefficient becomes `t_{j+1}`.
      refine Finset.sum_congr rfl ?_
      intro j hj
      simp [stepLower, prefixTerm, pairing, tk]
      ring

/-- Helper for Theorem 5 2 3: each normalized prefix term dominates the exact scalar kernel
obtained by replacing the base-gradient pairing with its explicit lower bound. -/
private theorem pathFollowingPrefixTerm_ge_scalarizedKernel
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (y0 : dom)
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ)
    (j : ℕ) :
    let prefixTerm : ℕ → ℝ := fun i ↦
      let ti1 := (process.t (i + 1) : ℝ)
      let ψi1 := auxiliaryCentralPathObjective f y0 ti1
      let δi := λ[ψi1; process.y i | process.mem_domain i]
      (Mf : ℝ) ^ (2 : ℕ) *
          (δi ^ (2 : ℕ) /
              (2 * (1 + (Mf : ℝ) * δi + (Mf : ℝ) ^ (2 : ℕ) * δi ^ (2 : ℕ))) +
            (Mf : ℝ) * δi ^ (3 : ℕ) /
              (2 * (1 + (Mf : ℝ) * δi) * (3 + 2 * (Mf : ℝ) * δi))) +
        (Mf : ℝ) ^ (2 : ℕ) *
          (ti1 *
            inner ℝ (∇ f (y0 : E)) (process.y i - process.y (i + 1)))
    let scalarKernel : ℕ → ℝ := fun i ↦
      let ti1 := (process.t (i + 1) : ℝ)
      let ψi1 := auxiliaryCentralPathObjective f y0 ti1
      let δi := λ[ψi1; process.y i | process.mem_domain i]
      (Mf : ℝ) ^ (2 : ℕ) *
        (δi ^ (2 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δi + (Mf : ℝ) ^ (2 : ℕ) * δi ^ (2 : ℕ))) +
          (Mf : ℝ) * δi ^ (3 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δi) * (3 + 2 * (Mf : ℝ) * δi)) -
          ti1 * pathFollowingObjectiveNorm f y0 (process.y i) (process.mem_domain i) *
            (δi * (1 + (Mf : ℝ) * δi) /
              (1 + (Mf : ℝ) * δi + (Mf : ℝ) ^ (2 : ℕ) * δi ^ (2 : ℕ))))
    scalarKernel j ≤ prefixTerm j := by
  let prefixTerm : ℕ → ℝ := fun i ↦
    let ti1 := (process.t (i + 1) : ℝ)
    let ψi1 := auxiliaryCentralPathObjective f y0 ti1
    let δi := λ[ψi1; process.y i | process.mem_domain i]
    (Mf : ℝ) ^ (2 : ℕ) *
        (δi ^ (2 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δi + (Mf : ℝ) ^ (2 : ℕ) * δi ^ (2 : ℕ))) +
          (Mf : ℝ) * δi ^ (3 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δi) * (3 + 2 * (Mf : ℝ) * δi))) +
      (Mf : ℝ) ^ (2 : ℕ) *
        (ti1 *
          inner ℝ (∇ f (y0 : E)) (process.y i - process.y (i + 1)))
  let scalarKernel : ℕ → ℝ := fun i ↦
    let ti1 := (process.t (i + 1) : ℝ)
    let ψi1 := auxiliaryCentralPathObjective f y0 ti1
    let δi := λ[ψi1; process.y i | process.mem_domain i]
    (Mf : ℝ) ^ (2 : ℕ) *
      (δi ^ (2 : ℕ) /
          (2 * (1 + (Mf : ℝ) * δi + (Mf : ℝ) ^ (2 : ℕ) * δi ^ (2 : ℕ))) +
        (Mf : ℝ) * δi ^ (3 : ℕ) /
          (2 * (1 + (Mf : ℝ) * δi) * (3 + 2 * (Mf : ℝ) * δi)) -
        ti1 * pathFollowingObjectiveNorm f y0 (process.y i) (process.mem_domain i) *
          (δi * (1 + (Mf : ℝ) * δi) /
            (1 + (Mf : ℝ) * δi + (Mf : ℝ) ^ (2 : ℕ) * δi ^ (2 : ℕ))))
  let tj1 := (process.t (j + 1) : ℝ)
  let ψj1 := auxiliaryCentralPathObjective f y0 tj1
  let δj := λ[ψj1; process.y j | process.mem_domain j]
  have hMf_sq_nonneg : 0 ≤ (Mf : ℝ) ^ (2 : ℕ) := by
    positivity
  have htj1_nonneg : 0 ≤ tj1 := (process.t (j + 1)).2.1
  have hpair_lower :=
    pathFollowingBaseGradientPairing_ge_neg_objectiveNorm_mul_intermediateStepRatio
      (f := f) (Mf := Mf) y0 process j
  have hscaled_pair :
      (Mf : ℝ) ^ (2 : ℕ) *
          (tj1 *
            (-pathFollowingObjectiveNorm f y0 (process.y j) (process.mem_domain j) *
              (δj * (1 + (Mf : ℝ) * δj) /
                (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ))))) ≤
        (Mf : ℝ) ^ (2 : ℕ) *
          (tj1 *
            inner ℝ (∇ f (y0 : E)) (process.y j - process.y (j + 1))) := by
    -- Multiply the pairing lower bound by the nonnegative time factor and `M_f²`.
    exact
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hpair_lower htj1_nonneg)
        hMf_sq_nonneg
  have hkernel_le :
      scalarKernel j ≤ prefixTerm j := by
    -- Keep the native scalar piece fixed and only replace the base-gradient pairing term.
    exact add_le_add_left hscaled_pair _
  simpa [prefixTerm, scalarKernel, tj1, ψj1, δj] using hkernel_le

/-- Helper for Theorem 5 2 3: summing the verified per-step scalar kernels gives a lower bound
for the whole normalized prefix package. -/
private theorem pathFollowingPrefixTerms_ge_scalarizedKernelSum
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (y0 : dom)
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ)
    (k : ℕ) :
    let prefixTerm : ℕ → ℝ := fun i ↦
      let ti1 := (process.t (i + 1) : ℝ)
      let ψi1 := auxiliaryCentralPathObjective f y0 ti1
      let δi := λ[ψi1; process.y i | process.mem_domain i]
      (Mf : ℝ) ^ (2 : ℕ) *
          (δi ^ (2 : ℕ) /
              (2 * (1 + (Mf : ℝ) * δi + (Mf : ℝ) ^ (2 : ℕ) * δi ^ (2 : ℕ))) +
            (Mf : ℝ) * δi ^ (3 : ℕ) /
              (2 * (1 + (Mf : ℝ) * δi) * (3 + 2 * (Mf : ℝ) * δi))) +
        (Mf : ℝ) ^ (2 : ℕ) *
          (ti1 *
            inner ℝ (∇ f (y0 : E)) (process.y i - process.y (i + 1)))
    let scalarKernel : ℕ → ℝ := fun i ↦
      let ti1 := (process.t (i + 1) : ℝ)
      let ψi1 := auxiliaryCentralPathObjective f y0 ti1
      let δi := λ[ψi1; process.y i | process.mem_domain i]
      (Mf : ℝ) ^ (2 : ℕ) *
        (δi ^ (2 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δi + (Mf : ℝ) ^ (2 : ℕ) * δi ^ (2 : ℕ))) +
          (Mf : ℝ) * δi ^ (3 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δi) * (3 + 2 * (Mf : ℝ) * δi)) -
          ti1 * pathFollowingObjectiveNorm f y0 (process.y i) (process.mem_domain i) *
            (δi * (1 + (Mf : ℝ) * δi) /
              (1 + (Mf : ℝ) * δi + (Mf : ℝ) ^ (2 : ℕ) * δi ^ (2 : ℕ))))
    (Finset.range k).sum scalarKernel ≤ (Finset.range k).sum prefixTerm := by
  let prefixTerm : ℕ → ℝ := fun i ↦
    let ti1 := (process.t (i + 1) : ℝ)
    let ψi1 := auxiliaryCentralPathObjective f y0 ti1
    let δi := λ[ψi1; process.y i | process.mem_domain i]
    (Mf : ℝ) ^ (2 : ℕ) *
        (δi ^ (2 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δi + (Mf : ℝ) ^ (2 : ℕ) * δi ^ (2 : ℕ))) +
          (Mf : ℝ) * δi ^ (3 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δi) * (3 + 2 * (Mf : ℝ) * δi))) +
      (Mf : ℝ) ^ (2 : ℕ) *
        (ti1 *
          inner ℝ (∇ f (y0 : E)) (process.y i - process.y (i + 1)))
  let scalarKernel : ℕ → ℝ := fun i ↦
    let ti1 := (process.t (i + 1) : ℝ)
    let ψi1 := auxiliaryCentralPathObjective f y0 ti1
    let δi := λ[ψi1; process.y i | process.mem_domain i]
    (Mf : ℝ) ^ (2 : ℕ) *
      (δi ^ (2 : ℕ) /
          (2 * (1 + (Mf : ℝ) * δi + (Mf : ℝ) ^ (2 : ℕ) * δi ^ (2 : ℕ))) +
        (Mf : ℝ) * δi ^ (3 : ℕ) /
          (2 * (1 + (Mf : ℝ) * δi) * (3 + 2 * (Mf : ℝ) * δi)) -
        ti1 * pathFollowingObjectiveNorm f y0 (process.y i) (process.mem_domain i) *
          (δi * (1 + (Mf : ℝ) * δi) /
            (1 + (Mf : ℝ) * δi + (Mf : ℝ) ^ (2 : ℕ) * δi ^ (2 : ℕ))))
  -- Sum the verified per-step scalar lower bounds without reopening the fixed-surface algebra.
  refine Finset.sum_le_sum ?_
  intro j hj
  simpa [scalarKernel] using
    pathFollowingPrefixTerm_ge_scalarizedKernel (f := f) (Mf := Mf) y0 process j

/-- Helper for Theorem 5 2 3: the actual objective drop already dominates the same scalar kernel
that appears in the normalized prefix package. -/
private theorem pathFollowingActualDrop_ge_scalarizedKernel
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (y0 : dom)
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ)
    (j : ℕ) :
    let actualDrop : ℕ → ℝ := fun i ↦
      (Mf : ℝ) ^ (2 : ℕ) * (f (process.y i) - f (process.y (i + 1)))
    let scalarKernel : ℕ → ℝ := fun i ↦
      let ti1 := (process.t (i + 1) : ℝ)
      let ψi1 := auxiliaryCentralPathObjective f y0 ti1
      let δi := λ[ψi1; process.y i | process.mem_domain i]
      (Mf : ℝ) ^ (2 : ℕ) *
        (δi ^ (2 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δi + (Mf : ℝ) ^ (2 : ℕ) * δi ^ (2 : ℕ))) +
          (Mf : ℝ) * δi ^ (3 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δi) * (3 + 2 * (Mf : ℝ) * δi)) -
          ti1 * pathFollowingObjectiveNorm f y0 (process.y i) (process.mem_domain i) *
            (δi * (1 + (Mf : ℝ) * δi) /
              (1 + (Mf : ℝ) * δi + (Mf : ℝ) ^ (2 : ℕ) * δi ^ (2 : ℕ))))
    scalarKernel j ≤ actualDrop j := by
  let actualDrop : ℕ → ℝ := fun i ↦
    (Mf : ℝ) ^ (2 : ℕ) * (f (process.y i) - f (process.y (i + 1)))
  let scalarKernel : ℕ → ℝ := fun i ↦
    let ti1 := (process.t (i + 1) : ℝ)
    let ψi1 := auxiliaryCentralPathObjective f y0 ti1
    let δi := λ[ψi1; process.y i | process.mem_domain i]
    (Mf : ℝ) ^ (2 : ℕ) *
      (δi ^ (2 : ℕ) /
          (2 * (1 + (Mf : ℝ) * δi + (Mf : ℝ) ^ (2 : ℕ) * δi ^ (2 : ℕ))) +
        (Mf : ℝ) * δi ^ (3 : ℕ) /
          (2 * (1 + (Mf : ℝ) * δi) * (3 + 2 * (Mf : ℝ) * δi)) -
        ti1 * pathFollowingObjectiveNorm f y0 (process.y i) (process.mem_domain i) *
          (δi * (1 + (Mf : ℝ) * δi) /
            (1 + (Mf : ℝ) * δi + (Mf : ℝ) ^ (2 : ℕ) * δi ^ (2 : ℕ))))
  -- This is exactly the one-step scalarized objective-drop estimate in the current spelling.
  simpa [actualDrop, scalarKernel] using
    pathFollowingObjectiveStep_gap_ge_scalarized
      (f := f) (Mf := Mf) y0 process j

/-- Helper for Theorem 5 2 3: once the prefix package and the terminal actual drop are both
compared to the scalar-kernel spelling, the whole normalized package dominates the corresponding
prefix-plus-terminal scalar kernel package. -/
private theorem pathFollowingNormalizedPrefixPlusTerminal_ge_scalarizedKernelPackage
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (y0 : dom)
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ)
    (k : ℕ) :
    let actualDrop : ℕ → ℝ := fun i ↦
      (Mf : ℝ) ^ (2 : ℕ) * (f (process.y i) - f (process.y (i + 1)))
    let prefixTerm : ℕ → ℝ := fun i ↦
      let ti1 := (process.t (i + 1) : ℝ)
      let ψi1 := auxiliaryCentralPathObjective f y0 ti1
      let δi := λ[ψi1; process.y i | process.mem_domain i]
      (Mf : ℝ) ^ (2 : ℕ) *
          (δi ^ (2 : ℕ) /
              (2 * (1 + (Mf : ℝ) * δi + (Mf : ℝ) ^ (2 : ℕ) * δi ^ (2 : ℕ))) +
            (Mf : ℝ) * δi ^ (3 : ℕ) /
              (2 * (1 + (Mf : ℝ) * δi) * (3 + 2 * (Mf : ℝ) * δi))) +
        (Mf : ℝ) ^ (2 : ℕ) *
          (ti1 *
            inner ℝ (∇ f (y0 : E)) (process.y i - process.y (i + 1)))
    let scalarKernel : ℕ → ℝ := fun i ↦
      let ti1 := (process.t (i + 1) : ℝ)
      let ψi1 := auxiliaryCentralPathObjective f y0 ti1
      let δi := λ[ψi1; process.y i | process.mem_domain i]
      (Mf : ℝ) ^ (2 : ℕ) *
        (δi ^ (2 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δi + (Mf : ℝ) ^ (2 : ℕ) * δi ^ (2 : ℕ))) +
          (Mf : ℝ) * δi ^ (3 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δi) * (3 + 2 * (Mf : ℝ) * δi)) -
          ti1 * pathFollowingObjectiveNorm f y0 (process.y i) (process.mem_domain i) *
            (δi * (1 + (Mf : ℝ) * δi) /
              (1 + (Mf : ℝ) * δi + (Mf : ℝ) ^ (2 : ℕ) * δi ^ (2 : ℕ))))
    (Finset.range k).sum scalarKernel + scalarKernel k ≤
      (Finset.range k).sum prefixTerm + actualDrop k := by
  let actualDrop : ℕ → ℝ := fun i ↦
    (Mf : ℝ) ^ (2 : ℕ) * (f (process.y i) - f (process.y (i + 1)))
  let prefixTerm : ℕ → ℝ := fun i ↦
    let ti1 := (process.t (i + 1) : ℝ)
    let ψi1 := auxiliaryCentralPathObjective f y0 ti1
    let δi := λ[ψi1; process.y i | process.mem_domain i]
    (Mf : ℝ) ^ (2 : ℕ) *
        (δi ^ (2 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δi + (Mf : ℝ) ^ (2 : ℕ) * δi ^ (2 : ℕ))) +
          (Mf : ℝ) * δi ^ (3 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δi) * (3 + 2 * (Mf : ℝ) * δi))) +
      (Mf : ℝ) ^ (2 : ℕ) *
        (ti1 *
          inner ℝ (∇ f (y0 : E)) (process.y i - process.y (i + 1)))
  let scalarKernel : ℕ → ℝ := fun i ↦
    let ti1 := (process.t (i + 1) : ℝ)
    let ψi1 := auxiliaryCentralPathObjective f y0 ti1
    let δi := λ[ψi1; process.y i | process.mem_domain i]
    (Mf : ℝ) ^ (2 : ℕ) *
      (δi ^ (2 : ℕ) /
          (2 * (1 + (Mf : ℝ) * δi + (Mf : ℝ) ^ (2 : ℕ) * δi ^ (2 : ℕ))) +
        (Mf : ℝ) * δi ^ (3 : ℕ) /
          (2 * (1 + (Mf : ℝ) * δi) * (3 + 2 * (Mf : ℝ) * δi)) -
        ti1 * pathFollowingObjectiveNorm f y0 (process.y i) (process.mem_domain i) *
          (δi * (1 + (Mf : ℝ) * δi) /
            (1 + (Mf : ℝ) * δi + (Mf : ℝ) ^ (2 : ℕ) * δi ^ (2 : ℕ))))
  have hprefix :
      (Finset.range k).sum scalarKernel ≤ (Finset.range k).sum prefixTerm := by
    -- Reuse the verified per-step scalar-kernel lower bounds in summed form.
    simpa [prefixTerm, scalarKernel] using
      pathFollowingPrefixTerms_ge_scalarizedKernelSum
        (f := f) (Mf := Mf) y0 process k
  have hterminal :
      scalarKernel k ≤ actualDrop k := by
    -- The terminal actual drop closes the same scalar kernel in its exact one-step spelling.
    simpa [actualDrop, scalarKernel] using
      pathFollowingActualDrop_ge_scalarizedKernel
        (f := f) (Mf := Mf) y0 process k
  -- Append the terminal comparison after summing the prefix comparisons once.
  exact add_le_add hprefix hterminal

/-- Helper for Theorem 5 2 3: appending the terminal actual drop to the fixed-surface package
rewrite gives the exact normalized prefix-plus-terminal spelling used by the remaining bridge. -/
private theorem pathFollowingFixedSurfacePackageWithBaseTiltPlusTerminal_eq_sumPrefixTermsPlusActualDrop
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (y0 : dom)
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ)
    (k : ℕ) :
    let tk := (process.t k : ℝ)
    let stepLower : ℕ → ℝ := fun j ↦
      let tj1 := (process.t (j + 1) : ℝ)
      let ψj1 := auxiliaryCentralPathObjective f y0 tj1
      let δj := λ[ψj1; process.y j | process.mem_domain j]
      (Mf : ℝ) ^ (2 : ℕ) *
          (δj ^ (2 : ℕ) /
              (2 * (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ))) +
            (Mf : ℝ) * δj ^ (3 : ℕ) /
              (2 * (1 + (Mf : ℝ) * δj) * (3 + 2 * (Mf : ℝ) * δj))) +
        (Mf : ℝ) ^ (2 : ℕ) *
          (((process.t (j + 1) : ℝ) - tk) *
            inner ℝ (∇ f (y0 : E)) (process.y j - process.y (j + 1)))
    let actualDrop : ℕ → ℝ := fun j ↦
      (Mf : ℝ) ^ (2 : ℕ) * (f (process.y j) - f (process.y (j + 1)))
    let prefixTerm : ℕ → ℝ := fun j ↦
      let tj1 := (process.t (j + 1) : ℝ)
      let ψj1 := auxiliaryCentralPathObjective f y0 tj1
      let δj := λ[ψj1; process.y j | process.mem_domain j]
      (Mf : ℝ) ^ (2 : ℕ) *
          (δj ^ (2 : ℕ) /
              (2 * (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ))) +
            (Mf : ℝ) * δj ^ (3 : ℕ) /
              (2 * (1 + (Mf : ℝ) * δj) * (3 + 2 * (Mf : ℝ) * δj))) +
        (Mf : ℝ) ^ (2 : ℕ) *
          ((process.t (j + 1) : ℝ) *
            inner ℝ (∇ f (y0 : E)) (process.y j - process.y (j + 1)))
    (Finset.range k).sum stepLower +
        (Mf : ℝ) ^ (2 : ℕ) * tk *
          inner ℝ (∇ f (y0 : E)) ((y0 : E) - process.y k) +
        actualDrop k =
      (Finset.range k).sum prefixTerm + actualDrop k := by
  let tk := (process.t k : ℝ)
  let stepLower : ℕ → ℝ := fun j ↦
    let tj1 := (process.t (j + 1) : ℝ)
    let ψj1 := auxiliaryCentralPathObjective f y0 tj1
    let δj := λ[ψj1; process.y j | process.mem_domain j]
    (Mf : ℝ) ^ (2 : ℕ) *
        (δj ^ (2 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ))) +
          (Mf : ℝ) * δj ^ (3 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δj) * (3 + 2 * (Mf : ℝ) * δj))) +
      (Mf : ℝ) ^ (2 : ℕ) *
        (((process.t (j + 1) : ℝ) - tk) *
          inner ℝ (∇ f (y0 : E)) (process.y j - process.y (j + 1)))
  let actualDrop : ℕ → ℝ := fun j ↦
    (Mf : ℝ) ^ (2 : ℕ) * (f (process.y j) - f (process.y (j + 1)))
  let prefixTerm : ℕ → ℝ := fun j ↦
    let tj1 := (process.t (j + 1) : ℝ)
    let ψj1 := auxiliaryCentralPathObjective f y0 tj1
    let δj := λ[ψj1; process.y j | process.mem_domain j]
    (Mf : ℝ) ^ (2 : ℕ) *
        (δj ^ (2 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ))) +
          (Mf : ℝ) * δj ^ (3 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δj) * (3 + 2 * (Mf : ℝ) * δj))) +
      (Mf : ℝ) ^ (2 : ℕ) *
        ((process.t (j + 1) : ℝ) *
          inner ℝ (∇ f (y0 : E)) (process.y j - process.y (j + 1)))
  have hrewrite :
      (Finset.range k).sum stepLower +
          (Mf : ℝ) ^ (2 : ℕ) * tk *
            inner ℝ (∇ f (y0 : E)) ((y0 : E) - process.y k) =
        (Finset.range k).sum prefixTerm := by
    -- Reuse the fixed-surface rewrite before appending the unchanged terminal drop.
    simpa [stepLower, prefixTerm, tk] using
      pathFollowingFixedSurfacePackageWithBaseTilt_eq_sumPrefixTerms
        (f := f) (Mf := Mf) y0 process k
  -- Append the same terminal actual drop to both sides.
  rw [hrewrite]

/-- Helper for Theorem 5 2 3: after normalizing the fixed-surface package, the proved
prefix-plus-terminal scalar-kernel comparison transports back to the original package spelling. -/
private theorem pathFollowingFixedSurfacePackageWithBaseTiltPlusTerminal_ge_scalarizedKernelPackage
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (y0 : dom)
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ)
    (k : ℕ) :
    let tk := (process.t k : ℝ)
    let stepLower : ℕ → ℝ := fun j ↦
      let tj1 := (process.t (j + 1) : ℝ)
      let ψj1 := auxiliaryCentralPathObjective f y0 tj1
      let δj := λ[ψj1; process.y j | process.mem_domain j]
      (Mf : ℝ) ^ (2 : ℕ) *
          (δj ^ (2 : ℕ) /
              (2 * (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ))) +
            (Mf : ℝ) * δj ^ (3 : ℕ) /
              (2 * (1 + (Mf : ℝ) * δj) * (3 + 2 * (Mf : ℝ) * δj))) +
        (Mf : ℝ) ^ (2 : ℕ) *
          (((process.t (j + 1) : ℝ) - tk) *
            inner ℝ (∇ f (y0 : E)) (process.y j - process.y (j + 1)))
    let actualDrop : ℕ → ℝ := fun j ↦
      (Mf : ℝ) ^ (2 : ℕ) * (f (process.y j) - f (process.y (j + 1)))
    let prefixTerm : ℕ → ℝ := fun j ↦
      let tj1 := (process.t (j + 1) : ℝ)
      let ψj1 := auxiliaryCentralPathObjective f y0 tj1
      let δj := λ[ψj1; process.y j | process.mem_domain j]
      (Mf : ℝ) ^ (2 : ℕ) *
          (δj ^ (2 : ℕ) /
              (2 * (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ))) +
            (Mf : ℝ) * δj ^ (3 : ℕ) /
              (2 * (1 + (Mf : ℝ) * δj) * (3 + 2 * (Mf : ℝ) * δj))) +
        (Mf : ℝ) ^ (2 : ℕ) *
          ((process.t (j + 1) : ℝ) *
            inner ℝ (∇ f (y0 : E)) (process.y j - process.y (j + 1)))
    let scalarKernel : ℕ → ℝ := fun j ↦
      let tj1 := (process.t (j + 1) : ℝ)
      let ψj1 := auxiliaryCentralPathObjective f y0 tj1
      let δj := λ[ψj1; process.y j | process.mem_domain j]
      (Mf : ℝ) ^ (2 : ℕ) *
        (δj ^ (2 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ))) +
          (Mf : ℝ) * δj ^ (3 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δj) * (3 + 2 * (Mf : ℝ) * δj)) -
          tj1 * pathFollowingObjectiveNorm f y0 (process.y j) (process.mem_domain j) *
            (δj * (1 + (Mf : ℝ) * δj) /
              (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ))))
    (Finset.range k).sum scalarKernel + scalarKernel k ≤
      (Finset.range k).sum stepLower +
        (Mf : ℝ) ^ (2 : ℕ) * tk *
          inner ℝ (∇ f (y0 : E)) ((y0 : E) - process.y k) +
        actualDrop k := by
  let tk := (process.t k : ℝ)
  let stepLower : ℕ → ℝ := fun j ↦
    let tj1 := (process.t (j + 1) : ℝ)
    let ψj1 := auxiliaryCentralPathObjective f y0 tj1
    let δj := λ[ψj1; process.y j | process.mem_domain j]
    (Mf : ℝ) ^ (2 : ℕ) *
        (δj ^ (2 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ))) +
          (Mf : ℝ) * δj ^ (3 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δj) * (3 + 2 * (Mf : ℝ) * δj))) +
      (Mf : ℝ) ^ (2 : ℕ) *
        (((process.t (j + 1) : ℝ) - tk) *
          inner ℝ (∇ f (y0 : E)) (process.y j - process.y (j + 1)))
  let actualDrop : ℕ → ℝ := fun j ↦
    (Mf : ℝ) ^ (2 : ℕ) * (f (process.y j) - f (process.y (j + 1)))
  let prefixTerm : ℕ → ℝ := fun j ↦
    let tj1 := (process.t (j + 1) : ℝ)
    let ψj1 := auxiliaryCentralPathObjective f y0 tj1
    let δj := λ[ψj1; process.y j | process.mem_domain j]
    (Mf : ℝ) ^ (2 : ℕ) *
        (δj ^ (2 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ))) +
          (Mf : ℝ) * δj ^ (3 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δj) * (3 + 2 * (Mf : ℝ) * δj))) +
      (Mf : ℝ) ^ (2 : ℕ) *
        ((process.t (j + 1) : ℝ) *
          inner ℝ (∇ f (y0 : E)) (process.y j - process.y (j + 1)))
  let scalarKernel : ℕ → ℝ := fun j ↦
    let tj1 := (process.t (j + 1) : ℝ)
    let ψj1 := auxiliaryCentralPathObjective f y0 tj1
    let δj := λ[ψj1; process.y j | process.mem_domain j]
    (Mf : ℝ) ^ (2 : ℕ) *
      (δj ^ (2 : ℕ) /
          (2 * (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ))) +
        (Mf : ℝ) * δj ^ (3 : ℕ) /
          (2 * (1 + (Mf : ℝ) * δj) * (3 + 2 * (Mf : ℝ) * δj)) -
        tj1 * pathFollowingObjectiveNorm f y0 (process.y j) (process.mem_domain j) *
          (δj * (1 + (Mf : ℝ) * δj) /
            (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ))))
  have hkernel :
      (Finset.range k).sum scalarKernel + scalarKernel k ≤
        (Finset.range k).sum prefixTerm + actualDrop k := by
    -- Use the proved scalar-kernel comparison in the normalized prefix spelling.
    simpa [actualDrop, prefixTerm, scalarKernel] using
      pathFollowingNormalizedPrefixPlusTerminal_ge_scalarizedKernelPackage
        (f := f) (Mf := Mf) y0 process k
  have hrewrite :
      (Finset.range k).sum stepLower +
          (Mf : ℝ) ^ (2 : ℕ) * tk *
            inner ℝ (∇ f (y0 : E)) ((y0 : E) - process.y k) +
          actualDrop k =
        (Finset.range k).sum prefixTerm + actualDrop k := by
    -- Rewrite the fixed-surface package back to the normalized prefix spelling once.
    simpa [actualDrop, prefixTerm, stepLower, tk] using
      pathFollowingFixedSurfacePackageWithBaseTiltPlusTerminal_eq_sumPrefixTermsPlusActualDrop
        (f := f) (Mf := Mf) y0 process k
  rw [hrewrite]
  exact hkernel

/-- Helper for Theorem 5 2 3: the positive-`κ` fixed-surface package is the sum of the even-weight
prefix contribution and the terminal single-step drop. -/
-- TODO: prove the terminal `+1` contribution directly on the current-surface route by rewriting
-- the terminal actual drop, normalizing with `s := (Mf : ℝ) * δk`, and closing the scalar
-- inequality from the Stage-1/centering lower bound at index `k`.
/-- Helper for Theorem 5 2 3: for every `j ≤ N`, the normalized scalar variables
`s_j = M_f δ_j` and `u_j = M_f t_{j+1} ‖∇ f(y₀)‖*_{y_j}` satisfy the same source-faithful
centering and Stage-1 bounds used in the positive-`κ` package estimate. -/
private theorem pathFollowingIntermediateScalar_bounds
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (hτ_nonneg : 0 ≤ τ) (htau : τ ≤ 0.23) (y0 : dom)
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ)
    (centering :
      ∀ j : ℕ,
        satisfies_approximate_centering_condition f y0 (process.t j) (process.y j)
          (process.mem_domain j) Mf (pathFollowingCenteringBeta τ))
    (N : ℕ)
    (hstage :
      ∀ j : ℕ, j ≤ N →
        1 / (2 * (Mf : ℝ)) ≤ λ[f; process.y j | process.mem_domain j])
    {j : ℕ} (hj : j ≤ N) :
    let tj1 := (process.t (j + 1) : ℝ)
    let ψj1 := auxiliaryCentralPathObjective f y0 tj1
    let δj := λ[ψj1; process.y j | process.mem_domain j]
    let νj := pathFollowingObjectiveNorm f y0 (process.y j) (process.mem_domain j)
    (Mf : ℝ) * δj ≤ τ ∧
      (1 / 2 : ℝ) - τ ≤ (Mf : ℝ) * tj1 * νj := by
  let tj1 := (process.t (j + 1) : ℝ)
  let ψj1 := auxiliaryCentralPathObjective f y0 tj1
  let δj := λ[ψj1; process.y j | process.mem_domain j]
  let νj := pathFollowingObjectiveNorm f y0 (process.y j) (process.mem_domain j)
  constructor
  · -- Keep the centered decrement in the normalized `s_j` spelling before summing any kernels.
    simpa [tj1, ψj1, δj] using
      pathFollowingScaledIntermediateSurfaceDecrement_le_tau
        (f := f) (Mf := Mf) hτ_nonneg htau y0 process centering j
  · -- Keep the Stage-1 bound in the normalized `u_j` spelling before the final scalar algebra.
    simpa [tj1, νj] using
      pathFollowingScaledNextTime_mul_objectiveNorm_lowerBound
        (f := f) (Mf := Mf) hτ_nonneg htau y0 process centering N hstage
        (j := j) hj

/-- Helper for Theorem 5 2 3: at the terminal index `k`, the normalized scalar variables
`s_k = M_f δ_k` and `u_k = M_f t_{k+1} ‖∇ f(y₀)‖*_{y_k}` satisfy the Stage-1 bounds
`s_k ≤ τ` and `(1 / 2) - τ ≤ u_k`. -/
private theorem pathFollowingTerminalScalar_bounds
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (hτ_nonneg : 0 ≤ τ) (htau : τ ≤ 0.23) (y0 : dom)
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ)
    (centering :
      ∀ j : ℕ,
        satisfies_approximate_centering_condition f y0 (process.t j) (process.y j)
          (process.mem_domain j) Mf (pathFollowingCenteringBeta τ))
    (N : ℕ)
    (hstage :
      ∀ j : ℕ, j ≤ N →
        1 / (2 * (Mf : ℝ)) ≤ λ[f; process.y j | process.mem_domain j])
    {k : ℕ} (hk : k < N) :
    let tk1 := (process.t (k + 1) : ℝ)
    let ψk1 := auxiliaryCentralPathObjective f y0 tk1
    let δk := λ[ψk1; process.y k | process.mem_domain k]
    let νk := pathFollowingObjectiveNorm f y0 (process.y k) (process.mem_domain k)
    (Mf : ℝ) * δk ≤ τ ∧
      (1 / 2 : ℝ) - τ ≤ (Mf : ℝ) * tk1 * νk := by
  let tk1 := (process.t (k + 1) : ℝ)
  let ψk1 := auxiliaryCentralPathObjective f y0 tk1
  let δk := λ[ψk1; process.y k | process.mem_domain k]
  let νk := pathFollowingObjectiveNorm f y0 (process.y k) (process.mem_domain k)
  -- Specialize the general `j ≤ N` scalar bounds to the terminal index `k`.
  simpa [tk1, ψk1, δk, νk] using
    pathFollowingIntermediateScalar_bounds
      (f := f) (Mf := Mf) hτ_nonneg htau y0 process centering N hstage
      (j := k) (Nat.le_of_lt hk)

/-- Helper for Theorem 5 2 3: rewriting the native scalar kernel at index `j` in the
dimensionless variables `s_j = M_f δ_j` and `u_j = M_f t_{j+1} ‖∇ f(y₀)‖*_{y_j}` removes the
remaining explicit powers of `M_f`. -/
private theorem pathFollowingScalarKernel_eq_normalizedVariables
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (y0 : dom)
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ)
    (j : ℕ) :
    let tj1 := (process.t (j + 1) : ℝ)
    let ψj1 := auxiliaryCentralPathObjective f y0 tj1
    let δj := λ[ψj1; process.y j | process.mem_domain j]
    let νj := pathFollowingObjectiveNorm f y0 (process.y j) (process.mem_domain j)
    let sj : ℝ := (Mf : ℝ) * δj
    let uj : ℝ := (Mf : ℝ) * tj1 * νj
    let scalarKernel : ℕ → ℝ := fun i ↦
      let ti1 := (process.t (i + 1) : ℝ)
      let ψi1 := auxiliaryCentralPathObjective f y0 ti1
      let δi := λ[ψi1; process.y i | process.mem_domain i]
      (Mf : ℝ) ^ (2 : ℕ) *
        (δi ^ (2 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δi + (Mf : ℝ) ^ (2 : ℕ) * δi ^ (2 : ℕ))) +
          (Mf : ℝ) * δi ^ (3 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δi) * (3 + 2 * (Mf : ℝ) * δi)) -
          ti1 * pathFollowingObjectiveNorm f y0 (process.y i) (process.mem_domain i) *
            (δi * (1 + (Mf : ℝ) * δi) /
              (1 + (Mf : ℝ) * δi + (Mf : ℝ) ^ (2 : ℕ) * δi ^ (2 : ℕ))))
    scalarKernel j =
      sj ^ (2 : ℕ) / (2 * (1 + sj + sj ^ (2 : ℕ))) +
        sj ^ (3 : ℕ) / (2 * (1 + sj) * (3 + 2 * sj)) -
        uj * (sj * (1 + sj) / (1 + sj + sj ^ (2 : ℕ))) := by
  let tj1 := (process.t (j + 1) : ℝ)
  let ψj1 := auxiliaryCentralPathObjective f y0 tj1
  let δj := λ[ψj1; process.y j | process.mem_domain j]
  let νj := pathFollowingObjectiveNorm f y0 (process.y j) (process.mem_domain j)
  let sj : ℝ := (Mf : ℝ) * δj
  let uj : ℝ := (Mf : ℝ) * tj1 * νj
  let scalarKernel : ℕ → ℝ := fun i ↦
    let ti1 := (process.t (i + 1) : ℝ)
    let ψi1 := auxiliaryCentralPathObjective f y0 ti1
    let δi := λ[ψi1; process.y i | process.mem_domain i]
    (Mf : ℝ) ^ (2 : ℕ) *
      (δi ^ (2 : ℕ) /
          (2 * (1 + (Mf : ℝ) * δi + (Mf : ℝ) ^ (2 : ℕ) * δi ^ (2 : ℕ))) +
        (Mf : ℝ) * δi ^ (3 : ℕ) /
          (2 * (1 + (Mf : ℝ) * δi) * (3 + 2 * (Mf : ℝ) * δi)) -
        ti1 * pathFollowingObjectiveNorm f y0 (process.y i) (process.mem_domain i) *
          (δi * (1 + (Mf : ℝ) * δi) /
            (1 + (Mf : ℝ) * δi + (Mf : ℝ) ^ (2 : ℕ) * δi ^ (2 : ℕ))))
  -- Normalize the native scalar kernel once into the dimensionless source variables `s_j, u_j`.
  simp only [scalarKernel, sj, uj]
  ring

/-- Helper for Theorem 5 2 3: on the admissible scalar region `0 ≤ s ≤ τ ≤ 0.23`, the normalized
scalar kernel is nonpositive as soon as `u ≥ (1 / 2) - τ`. This certifies that the previous
odd-weight lower-bound route cannot be closed on the native scalar-kernel owner. -/
private theorem pathFollowingNormalizedScalarKernel_nonpos_of_bounds
    {τ s u : ℝ}
    (hs_nonneg : 0 ≤ s) (hs_le_tau : s ≤ τ) (htau : τ ≤ 0.23)
    (hu_ge : (1 / 2 : ℝ) - τ ≤ u) :
    s ^ (2 : ℕ) / (2 * (1 + s + s ^ (2 : ℕ))) +
        s ^ (3 : ℕ) / (2 * (1 + s) * (3 + 2 * s)) -
        u * (s * (1 + s) / (1 + s + s ^ (2 : ℕ))) ≤ 0 := by
  have hs_le_one : s ≤ 1 := by
    linarith
  have hs_sq_le_s : s ^ (2 : ℕ) ≤ s := by
    nlinarith
  have hs_cu_le_s : s ^ (3 : ℕ) ≤ s := by
    nlinarith
  have hcoeff_nonneg : 0 ≤ s * (1 + s) / (1 + s + s ^ (2 : ℕ)) := by
    positivity
  have hreduce_u :
      s ^ (2 : ℕ) / (2 * (1 + s + s ^ (2 : ℕ))) +
          s ^ (3 : ℕ) / (2 * (1 + s) * (3 + 2 * s)) -
          u * (s * (1 + s) / (1 + s + s ^ (2 : ℕ))) ≤
        s ^ (2 : ℕ) / (2 * (1 + s + s ^ (2 : ℕ))) +
          s ^ (3 : ℕ) / (2 * (1 + s) * (3 + 2 * s)) -
          (((1 / 2 : ℝ) - τ) * (s * (1 + s) / (1 + s + s ^ (2 : ℕ)))) := by
    have hmul :=
      mul_le_mul_of_nonneg_right hu_ge hcoeff_nonneg
    linarith
  have hden1_pos : 0 < 1 + s + s ^ (2 : ℕ) := by
    positivity
  have hden2_pos : 0 < 1 + s := by
    positivity
  have hden3_pos : 0 < 3 + 2 * s := by
    positivity
  have hpoly_upper :
      s ^ (4 : ℕ) + (4 * τ + 1) * s ^ (3 : ℕ) + (14 * τ - 1) * s ^ (2 : ℕ) +
          (16 * τ - 5) * s + (6 * τ - 3) ≤
        (257 / 50 : ℝ) * s + (6 * τ - 3) := by
    have hs4_le : s ^ (4 : ℕ) ≤ s := by
      nlinarith
    have hs3_scaled :
        (4 * τ + 1) * s ^ (3 : ℕ) ≤ (48 / 25 : ℝ) * s := by
      have hcoeff : 4 * τ + 1 ≤ (48 / 25 : ℝ) := by
        nlinarith
      have hcoeff_mul : (4 * τ + 1) * s ^ (3 : ℕ) ≤ (48 / 25 : ℝ) * s ^ (3 : ℕ) := by
        exact mul_le_mul_of_nonneg_right hcoeff (by positivity : 0 ≤ s ^ (3 : ℕ))
      exact hcoeff_mul.trans <| by
        exact mul_le_mul_of_nonneg_left hs_cu_le_s (by positivity : 0 ≤ (48 / 25 : ℝ))
    have hs2_scaled :
        (14 * τ - 1) * s ^ (2 : ℕ) ≤ (111 / 50 : ℝ) * s := by
      have hcoeff : 14 * τ - 1 ≤ (111 / 50 : ℝ) := by
        nlinarith
      have hcoeff_mul : (14 * τ - 1) * s ^ (2 : ℕ) ≤ (111 / 50 : ℝ) * s ^ (2 : ℕ) := by
        exact mul_le_mul_of_nonneg_right hcoeff (by positivity : 0 ≤ s ^ (2 : ℕ))
      exact hcoeff_mul.trans <| by
        exact mul_le_mul_of_nonneg_left hs_sq_le_s (by positivity : 0 ≤ (111 / 50 : ℝ))
    have hs1_neg : (16 * τ - 5) * s ≤ 0 := by
      have hcoeff : 16 * τ - 5 ≤ 0 := by
        nlinarith
      exact mul_nonpos_of_nonpos_of_nonneg hcoeff hs_nonneg
    linarith
  have hpoly_nonpos :
      s ^ (4 : ℕ) + (4 * τ + 1) * s ^ (3 : ℕ) + (14 * τ - 1) * s ^ (2 : ℕ) +
          (16 * τ - 5) * s + (6 * τ - 3) ≤ 0 := by
    have hlinear : (257 / 50 : ℝ) * s + (6 * τ - 3) ≤ 0 := by
      have hs_to_tau : (257 / 50 : ℝ) * s ≤ (257 / 50 : ℝ) * τ := by
        exact mul_le_mul_of_nonneg_left hs_le_tau (by positivity : 0 ≤ (257 / 50 : ℝ))
      have htau_linear : (257 / 50 : ℝ) * τ + (6 * τ - 3) ≤ 0 := by
        nlinarith
      linarith
    exact le_trans hpoly_upper hlinear
  have hkernel_at_lower :
      s ^ (2 : ℕ) / (2 * (1 + s + s ^ (2 : ℕ))) +
          s ^ (3 : ℕ) / (2 * (1 + s) * (3 + 2 * s)) -
          (((1 / 2 : ℝ) - τ) * (s * (1 + s) / (1 + s + s ^ (2 : ℕ)))) ≤ 0 := by
    have hclear :
        2 * (1 + s) * (3 + 2 * s) * (1 + s + s ^ (2 : ℕ)) *
            (s ^ (2 : ℕ) / (2 * (1 + s + s ^ (2 : ℕ))) +
              s ^ (3 : ℕ) / (2 * (1 + s) * (3 + 2 * s)) -
              (((1 / 2 : ℝ) - τ) * (s * (1 + s) / (1 + s + s ^ (2 : ℕ))))) ≤
          0 := by
      have hident :
          2 * (1 + s) * (3 + 2 * s) * (1 + s + s ^ (2 : ℕ)) *
              (s ^ (2 : ℕ) / (2 * (1 + s + s ^ (2 : ℕ))) +
                s ^ (3 : ℕ) / (2 * (1 + s) * (3 + 2 * s)) -
                (((1 / 2 : ℝ) - τ) * (s * (1 + s) / (1 + s + s ^ (2 : ℕ))))) =
            s * (s ^ (4 : ℕ) + (4 * τ + 1) * s ^ (3 : ℕ) + (14 * τ - 1) * s ^ (2 : ℕ) +
              (16 * τ - 5) * s + (6 * τ - 3)) := by
        field_simp [hden1_pos.ne', hden2_pos.ne', hden3_pos.ne']
        ring
      rw [hident]
      exact mul_nonpos_of_nonneg_of_nonpos hs_nonneg hpoly_nonpos
    exact (le_div_iff₀ (show 0 < 2 * (1 + s) * (3 + 2 * s) * (1 + s + s ^ (2 : ℕ)) by
      positivity)).mp <| by
        simpa [mul_assoc] using hclear
  exact le_trans hreduce_u hkernel_at_lower

/-- Helper for Theorem 5 2 3: every intermediate scalar-kernel term is nonpositive under the
Stage-1 and centering bounds, so the native scalarized owner cannot support the positive branch by
itself. -/
private theorem pathFollowingIntermediateScalarizedKernel_nonpos
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (hτ_nonneg : 0 ≤ τ) (htau : τ ≤ 0.23) (y0 : dom)
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ)
    (centering :
      ∀ j : ℕ,
        satisfies_approximate_centering_condition f y0 (process.t j) (process.y j)
          (process.mem_domain j) Mf (pathFollowingCenteringBeta τ))
    (N : ℕ)
    (hstage :
      ∀ j : ℕ, j ≤ N →
        1 / (2 * (Mf : ℝ)) ≤ λ[f; process.y j | process.mem_domain j])
    {j : ℕ} (hj : j ≤ N) :
    let scalarKernel : ℕ → ℝ := fun i ↦
      let ti1 := (process.t (i + 1) : ℝ)
      let ψi1 := auxiliaryCentralPathObjective f y0 ti1
      let δi := λ[ψi1; process.y i | process.mem_domain i]
      (Mf : ℝ) ^ (2 : ℕ) *
        (δi ^ (2 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δi + (Mf : ℝ) ^ (2 : ℕ) * δi ^ (2 : ℕ))) +
          (Mf : ℝ) * δi ^ (3 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δi) * (3 + 2 * (Mf : ℝ) * δi)) -
          ti1 * pathFollowingObjectiveNorm f y0 (process.y i) (process.mem_domain i) *
            (δi * (1 + (Mf : ℝ) * δi) /
              (1 + (Mf : ℝ) * δi + (Mf : ℝ) ^ (2 : ℕ) * δi ^ (2 : ℕ))))
    scalarKernel j ≤ 0 := by
  let tj1 := (process.t (j + 1) : ℝ)
  let ψj1 := auxiliaryCentralPathObjective f y0 tj1
  let δj := λ[ψj1; process.y j | process.mem_domain j]
  let νj := pathFollowingObjectiveNorm f y0 (process.y j) (process.mem_domain j)
  let sj : ℝ := (Mf : ℝ) * δj
  let uj : ℝ := (Mf : ℝ) * tj1 * νj
  let scalarKernel : ℕ → ℝ := fun i ↦
    let ti1 := (process.t (i + 1) : ℝ)
    let ψi1 := auxiliaryCentralPathObjective f y0 ti1
    let δi := λ[ψi1; process.y i | process.mem_domain i]
    (Mf : ℝ) ^ (2 : ℕ) *
      (δi ^ (2 : ℕ) /
          (2 * (1 + (Mf : ℝ) * δi + (Mf : ℝ) ^ (2 : ℕ) * δi ^ (2 : ℕ))) +
        (Mf : ℝ) * δi ^ (3 : ℕ) /
          (2 * (1 + (Mf : ℝ) * δi) * (3 + 2 * (Mf : ℝ) * δi)) -
        ti1 * pathFollowingObjectiveNorm f y0 (process.y i) (process.mem_domain i) *
          (δi * (1 + (Mf : ℝ) * δi) /
            (1 + (Mf : ℝ) * δi + (Mf : ℝ) ^ (2 : ℕ) * δi ^ (2 : ℕ))))
  have hs_nonneg : 0 ≤ sj := by
    have hδj_nonneg : 0 ≤ δj := by
      exact NewtonDecrement.ofPosDefMem_nonneg ψj1 (process.y j) (process.mem_domain j)
    exact mul_nonneg (by positivity : 0 ≤ (Mf : ℝ)) hδj_nonneg
  have hbounds :
      sj ≤ τ ∧ (1 / 2 : ℝ) - τ ≤ uj := by
    -- Read the intermediate centering and Stage-1 bounds directly in the normalized variables.
    simpa [sj, uj, tj1, ψj1, δj, νj] using
      pathFollowingIntermediateScalar_bounds
        (f := f) (Mf := Mf) hτ_nonneg htau y0 process centering N hstage
        (j := j) hj
  have hkernel_eq :
      scalarKernel j =
        sj ^ (2 : ℕ) / (2 * (1 + sj + sj ^ (2 : ℕ))) +
          sj ^ (3 : ℕ) / (2 * (1 + sj) * (3 + 2 * sj)) -
          uj * (sj * (1 + sj) / (1 + sj + sj ^ (2 : ℕ))) := by
    -- Normalize the native kernel once into the scalar owner `(s_j, u_j)`.
    simpa [scalarKernel, sj, uj, tj1, ψj1, δj, νj] using
      pathFollowingScalarKernel_eq_normalizedVariables
        (f := f) (Mf := Mf) y0 process j
  rw [hkernel_eq]
  exact
    pathFollowingNormalizedScalarKernel_nonpos_of_bounds
      hs_nonneg hbounds.1 htau hbounds.2

/-- Helper for Theorem 5 2 3: the terminal scalar-kernel term is also nonpositive under the same
normalized Stage-1 and centering bounds. -/
private theorem pathFollowingTerminalScalarizedKernel_nonpos
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (hτ_nonneg : 0 ≤ τ) (htau : τ ≤ 0.23) (y0 : dom)
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ)
    (centering :
      ∀ j : ℕ,
        satisfies_approximate_centering_condition f y0 (process.t j) (process.y j)
          (process.mem_domain j) Mf (pathFollowingCenteringBeta τ))
    (N : ℕ)
    (hstage :
      ∀ j : ℕ, j ≤ N →
        1 / (2 * (Mf : ℝ)) ≤ λ[f; process.y j | process.mem_domain j])
    {k : ℕ} (hk : k < N) :
    let scalarKernel : ℕ → ℝ := fun j ↦
      let tj1 := (process.t (j + 1) : ℝ)
      let ψj1 := auxiliaryCentralPathObjective f y0 tj1
      let δj := λ[ψj1; process.y j | process.mem_domain j]
      (Mf : ℝ) ^ (2 : ℕ) *
        (δj ^ (2 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ))) +
          (Mf : ℝ) * δj ^ (3 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δj) * (3 + 2 * (Mf : ℝ) * δj)) -
          tj1 * pathFollowingObjectiveNorm f y0 (process.y j) (process.mem_domain j) *
            (δj * (1 + (Mf : ℝ) * δj) /
              (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ))))
    scalarKernel k ≤ 0 := by
  let tk1 := (process.t (k + 1) : ℝ)
  let ψk1 := auxiliaryCentralPathObjective f y0 tk1
  let δk := λ[ψk1; process.y k | process.mem_domain k]
  let νk := pathFollowingObjectiveNorm f y0 (process.y k) (process.mem_domain k)
  let sk : ℝ := (Mf : ℝ) * δk
  let uk : ℝ := (Mf : ℝ) * tk1 * νk
  let scalarKernel : ℕ → ℝ := fun j ↦
    let tj1 := (process.t (j + 1) : ℝ)
    let ψj1 := auxiliaryCentralPathObjective f y0 tj1
    let δj := λ[ψj1; process.y j | process.mem_domain j]
    (Mf : ℝ) ^ (2 : ℕ) *
      (δj ^ (2 : ℕ) /
          (2 * (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ))) +
        (Mf : ℝ) * δj ^ (3 : ℕ) /
          (2 * (1 + (Mf : ℝ) * δj) * (3 + 2 * (Mf : ℝ) * δj)) -
        tj1 * pathFollowingObjectiveNorm f y0 (process.y j) (process.mem_domain j) *
          (δj * (1 + (Mf : ℝ) * δj) /
            (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ))))
  have hs_nonneg : 0 ≤ sk := by
    have hδk_nonneg : 0 ≤ δk := by
      exact NewtonDecrement.ofPosDefMem_nonneg ψk1 (process.y k) (process.mem_domain k)
    exact mul_nonneg (by positivity : 0 ≤ (Mf : ℝ)) hδk_nonneg
  have hbounds :
      sk ≤ τ ∧ (1 / 2 : ℝ) - τ ≤ uk := by
    -- Specialize the normalized scalar bounds to the terminal index `k`.
    simpa [sk, uk, tk1, ψk1, δk, νk] using
      pathFollowingTerminalScalar_bounds
        (f := f) (Mf := Mf) hτ_nonneg htau y0 process centering N hstage hk
  have hkernel_eq :
      scalarKernel k =
        sk ^ (2 : ℕ) / (2 * (1 + sk + sk ^ (2 : ℕ))) +
          sk ^ (3 : ℕ) / (2 * (1 + sk) * (3 + 2 * sk)) -
          uk * (sk * (1 + sk) / (1 + sk + sk ^ (2 : ℕ))) := by
    -- Normalize the terminal native kernel into the scalar owner `(s_k, u_k)`.
    simpa [scalarKernel, sk, uk, tk1, ψk1, δk, νk] using
      pathFollowingScalarKernel_eq_normalizedVariables
        (f := f) (Mf := Mf) y0 process k
  rw [hkernel_eq]
  exact
    pathFollowingNormalizedScalarKernel_nonpos_of_bounds
      hs_nonneg hbounds.1 htau hbounds.2

/-- Helper for Theorem 5 2 3: at the terminal index `k`, the current-surface decrement is
bounded by `β(τ) / M_f`, while the Stage-1 estimate supplies the complementary lower bound on
`t_k ‖∇ f(y₀)‖*_{y_k}`. -/
private theorem pathFollowingTerminalCurrentSurfaceScalar_bounds
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (y0 : dom)
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ)
    (centering :
      ∀ j : ℕ,
        satisfies_approximate_centering_condition f y0 (process.t j) (process.y j)
          (process.mem_domain j) Mf (pathFollowingCenteringBeta τ))
    (N : ℕ)
    (hstage :
      ∀ j : ℕ, j ≤ N →
        1 / (2 * (Mf : ℝ)) ≤ λ[f; process.y j | process.mem_domain j])
    {k : ℕ} (hk : k < N) :
    let tk := (process.t k : ℝ)
    let ψk := auxiliaryCentralPathObjective f y0 tk
    let δk := λ[ψk; process.y k | process.mem_domain k]
    let νk := pathFollowingObjectiveNorm f y0 (process.y k) (process.mem_domain k)
    (Mf : ℝ) * δk ≤ pathFollowingCenteringBeta τ ∧
      (1 / 2 : ℝ) - pathFollowingCenteringBeta τ ≤ (Mf : ℝ) * tk * νk := by
  let tk := (process.t k : ℝ)
  let ψk := auxiliaryCentralPathObjective f y0 tk
  let δk := λ[ψk; process.y k | process.mem_domain k]
  let νk := pathFollowingObjectiveNorm f y0 (process.y k) (process.mem_domain k)
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero Mf))
  constructor
  · have hcenterk :
        δk ≤ pathFollowingCenteringBeta τ / (Mf : ℝ) := by
      -- Read the approximate-centering invariant at index `k` in the current-surface spelling.
      exact
        (satisfies_approximate_centering_condition_iff
          f y0 (process.t k) (process.y k) (process.mem_domain k) Mf
          (pathFollowingCenteringBeta τ)).1 (centering k)
    have hscaled := mul_le_mul_of_nonneg_left hcenterk hMf_pos.le
    -- Clear the positive `M_f` denominator once so the bound is in the normalized scalar `s_k`.
    calc
      (Mf : ℝ) * δk ≤ (Mf : ℝ) * (pathFollowingCenteringBeta τ / (Mf : ℝ)) := hscaled
      _ = pathFollowingCenteringBeta τ := by
            field_simp [hMf_pos.ne']
  · have hbase :
        (((1 / 2 : ℝ) - pathFollowingCenteringBeta τ) / (Mf : ℝ)) ≤ tk * νk := by
      -- Reuse the Stage-1/centering bridge at the current time parameter `t_k`.
      simpa [tk, νk] using
        pathFollowingStageCentering_timeObjectiveNormLowerBound
          (f := f) (Mf := Mf) y0 process centering N hstage
          (k := k) (Nat.le_of_lt hk)
    have hscaled := mul_le_mul_of_nonneg_left hbase hMf_pos.le
    -- Clear the positive factor `M_f` once so the lower bound matches the normalized scalar `u_k`.
    calc
      (1 / 2 : ℝ) - pathFollowingCenteringBeta τ =
          (Mf : ℝ) * (((1 / 2 : ℝ) - pathFollowingCenteringBeta τ) / (Mf : ℝ)) := by
            field_simp [hMf_pos.ne']
      _ ≤ (Mf : ℝ) * (tk * νk) := hscaled
      _ = (Mf : ℝ) * tk * νk := by
            ring

/-- Helper for Theorem 5 2 3: the terminal current-surface package is exactly the actual
objective drop at index `k`. -/
private theorem pathFollowingTerminalCurrentSurfacePackage_eq_actualDrop
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (y0 : dom)
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ)
    (k : ℕ) :
    let tk := (process.t k : ℝ)
    let ψk := auxiliaryCentralPathObjective f y0 tk
    let actualDrop : ℕ → ℝ := fun j ↦
      (Mf : ℝ) ^ (2 : ℕ) * (f (process.y j) - f (process.y (j + 1)))
    (Mf : ℝ) ^ (2 : ℕ) * (ψk (process.y k) - ψk (process.y (k + 1))) +
        (Mf : ℝ) ^ (2 : ℕ) * tk *
          inner ℝ (∇ f (y0 : E)) (process.y k - process.y (k + 1)) =
      actualDrop k := by
  let tk := (process.t k : ℝ)
  let ψk := auxiliaryCentralPathObjective f y0 tk
  let actualDrop : ℕ → ℝ := fun j ↦
    (Mf : ℝ) ^ (2 : ℕ) * (f (process.y j) - f (process.y (j + 1)))
  have hshift :
      f (process.y k) - f (process.y (k + 1)) =
        ψk (process.y k) - ψk (process.y (k + 1)) +
          tk * inner ℝ (∇ f (y0 : E)) (process.y k - process.y (k + 1)) := by
    -- Rewrite the terminal actual drop on the same fixed surface `ψ_k` used by the source package.
    simpa [tk, ψk] using
      pathFollowingTerminalObjectiveStep_gap_shift_currentSurface
        (f := f) (Mf := Mf) y0 process k
  -- Scale the current-surface identity by `M_f²` so it matches the normalized actual-drop owner.
  calc
    (Mf : ℝ) ^ (2 : ℕ) * (ψk (process.y k) - ψk (process.y (k + 1))) +
        (Mf : ℝ) ^ (2 : ℕ) * tk *
          inner ℝ (∇ f (y0 : E)) (process.y k - process.y (k + 1)) =
      (Mf : ℝ) ^ (2 : ℕ) *
        (ψk (process.y k) - ψk (process.y (k + 1)) +
          tk * inner ℝ (∇ f (y0 : E)) (process.y k - process.y (k + 1))) := by
            ring
    _ = (Mf : ℝ) ^ (2 : ℕ) * (f (process.y k) - f (process.y (k + 1))) := by
          rw [hshift]
    _ = actualDrop k := by
          simp [actualDrop]

/-- Helper for Theorem 5 2 3: the exact next-iterate objective gap is the sum of the current
`ψ_k`-surface gap, the residual base-tilt term, and the terminal current-surface package. -/
private theorem pathFollowingCurrentSurfaceGapWithBaseTiltPlusTerminal_eq_actualGapToNextIterate
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (y0 : dom)
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ)
    (k : ℕ) :
    let tk := (process.t k : ℝ)
    let ψk := auxiliaryCentralPathObjective f y0 tk
    let terminalCurrentSurfacePackage : ℝ :=
      (Mf : ℝ) ^ (2 : ℕ) * (ψk (process.y k) - ψk (process.y (k + 1))) +
        (Mf : ℝ) ^ (2 : ℕ) * tk *
          inner ℝ (∇ f (y0 : E)) (process.y k - process.y (k + 1))
    (Mf : ℝ) ^ (2 : ℕ) * (ψk (y0 : E) - ψk (process.y k)) +
        (Mf : ℝ) ^ (2 : ℕ) * tk *
          inner ℝ (∇ f (y0 : E)) ((y0 : E) - process.y k) +
        terminalCurrentSurfacePackage =
      (Mf : ℝ) ^ (2 : ℕ) * (f (y0 : E) - f (process.y (k + 1))) := by
  let tk := (process.t k : ℝ)
  let ψk := auxiliaryCentralPathObjective f y0 tk
  let actualDrop : ℕ → ℝ := fun j ↦
    (Mf : ℝ) ^ (2 : ℕ) * (f (process.y j) - f (process.y (j + 1)))
  let terminalCurrentSurfacePackage : ℝ :=
    (Mf : ℝ) ^ (2 : ℕ) * (ψk (process.y k) - ψk (process.y (k + 1))) +
      (Mf : ℝ) ^ (2 : ℕ) * tk *
        inner ℝ (∇ f (y0 : E)) (process.y k - process.y (k + 1))
  have hterminal :
      terminalCurrentSurfacePackage = actualDrop k := by
    -- Rewrite the terminal current-surface step once into the native actual-drop spelling.
    simpa [terminalCurrentSurfacePackage, tk, ψk, actualDrop] using
      pathFollowingTerminalCurrentSurfacePackage_eq_actualDrop
        (f := f) (Mf := Mf) y0 process k
  -- Route correction: expanding `ψ_k (y₀) - ψ_k (y_k)` leaves the residual
  -- `-t_k ⟪∇ f(y₀), y₀ - y_k⟫`, so the exact owner must keep the base-tilt term explicitly.
  calc
    (Mf : ℝ) ^ (2 : ℕ) * (ψk (y0 : E) - ψk (process.y k)) +
        (Mf : ℝ) ^ (2 : ℕ) * tk *
          inner ℝ (∇ f (y0 : E)) ((y0 : E) - process.y k) +
        terminalCurrentSurfacePackage =
      (Mf : ℝ) ^ (2 : ℕ) * (ψk (y0 : E) - ψk (process.y k)) +
        (Mf : ℝ) ^ (2 : ℕ) * tk *
          inner ℝ (∇ f (y0 : E)) ((y0 : E) - process.y k) +
        actualDrop k := by
          rw [hterminal]
    _ =
      (Mf : ℝ) ^ (2 : ℕ) * (f (y0 : E) - f (process.y k)) + actualDrop k := by
          -- The current `ψ_k`-surface gap and the explicit base tilt recombine to the actual gap
          -- from `y₀` to `y_k`.
          simp [ψk, tk, auxiliaryCentralPathObjective_apply]
          ring
    _ =
      (Mf : ℝ) ^ (2 : ℕ) * (f (y0 : E) - f (process.y k)) +
        (Mf : ℝ) ^ (2 : ℕ) * (f (process.y k) - f (process.y (k + 1))) := by
          simp [actualDrop]
    _ = (Mf : ℝ) ^ (2 : ℕ) * (f (y0 : E) - f (process.y (k + 1))) := by
          ring

/-- Helper for Theorem 5 2 3: the current `ψ_k`-surface gap plus its explicit base-tilt
correction is exactly the plain objective gap from `y₀` to `y_k`. -/
private theorem pathFollowingCurrentSurfaceGapWithBaseTilt_eq_actualGap
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (y0 : dom)
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ)
    (k : ℕ) :
    let tk := (process.t k : ℝ)
    let ψk := auxiliaryCentralPathObjective f y0 tk
    (Mf : ℝ) ^ (2 : ℕ) * (ψk (y0 : E) - ψk (process.y k)) +
        (Mf : ℝ) ^ (2 : ℕ) * tk *
          inner ℝ (∇ f (y0 : E)) ((y0 : E) - process.y k) =
      (Mf : ℝ) ^ (2 : ℕ) * (f (y0 : E) - f (process.y k)) := by
  let tk := (process.t k : ℝ)
  let ψk := auxiliaryCentralPathObjective f y0 tk
  -- Expand the tilted objective once and keep the explicit base-tilt correction.
  simp [ψk, tk, auxiliaryCentralPathObjective_apply]
  ring

/-- Helper for Theorem 5 2 3: the native scalar-kernel package transports to the corrected
current-surface package once the fixed-surface prefix is rewritten as actual drops and the
terminal current-surface step is rewritten as the terminal actual drop. -/
private theorem pathFollowingCurrentSurfaceGapWithBaseTiltPlusTerminal_ge_scalarizedKernelPackage
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (y0 : dom)
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ)
    (k : ℕ) :
    let tk := (process.t k : ℝ)
    let ψk := auxiliaryCentralPathObjective f y0 tk
    let terminalCurrentSurfacePackage : ℝ :=
      (Mf : ℝ) ^ (2 : ℕ) * (ψk (process.y k) - ψk (process.y (k + 1))) +
        (Mf : ℝ) ^ (2 : ℕ) * tk *
          inner ℝ (∇ f (y0 : E)) (process.y k - process.y (k + 1))
    let scalarKernel : ℕ → ℝ := fun j ↦
      let tj1 := (process.t (j + 1) : ℝ)
      let ψj1 := auxiliaryCentralPathObjective f y0 tj1
      let δj := λ[ψj1; process.y j | process.mem_domain j]
      (Mf : ℝ) ^ (2 : ℕ) *
        (δj ^ (2 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ))) +
          (Mf : ℝ) * δj ^ (3 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δj) * (3 + 2 * (Mf : ℝ) * δj)) -
          tj1 * pathFollowingObjectiveNorm f y0 (process.y j) (process.mem_domain j) *
            (δj * (1 + (Mf : ℝ) * δj) /
              (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ))))
    (Finset.range k).sum scalarKernel + scalarKernel k ≤
      (Mf : ℝ) ^ (2 : ℕ) * (ψk (y0 : E) - ψk (process.y k)) +
        (Mf : ℝ) ^ (2 : ℕ) * tk *
          inner ℝ (∇ f (y0 : E)) ((y0 : E) - process.y k) +
        terminalCurrentSurfacePackage := by
  let tk := (process.t k : ℝ)
  let ψk := auxiliaryCentralPathObjective f y0 tk
  let stepLower : ℕ → ℝ := fun j ↦
    let tj1 := (process.t (j + 1) : ℝ)
    let ψj1 := auxiliaryCentralPathObjective f y0 tj1
    let δj := λ[ψj1; process.y j | process.mem_domain j]
    (Mf : ℝ) ^ (2 : ℕ) *
        (δj ^ (2 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ))) +
          (Mf : ℝ) * δj ^ (3 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δj) * (3 + 2 * (Mf : ℝ) * δj))) +
      (Mf : ℝ) ^ (2 : ℕ) *
        (((process.t (j + 1) : ℝ) - tk) *
          inner ℝ (∇ f (y0 : E)) (process.y j - process.y (j + 1)))
  let actualDrop : ℕ → ℝ := fun j ↦
    (Mf : ℝ) ^ (2 : ℕ) * (f (process.y j) - f (process.y (j + 1)))
  let terminalCurrentSurfacePackage : ℝ :=
    (Mf : ℝ) ^ (2 : ℕ) * (ψk (process.y k) - ψk (process.y (k + 1))) +
      (Mf : ℝ) ^ (2 : ℕ) * tk *
        inner ℝ (∇ f (y0 : E)) (process.y k - process.y (k + 1))
  let scalarKernel : ℕ → ℝ := fun j ↦
    let tj1 := (process.t (j + 1) : ℝ)
    let ψj1 := auxiliaryCentralPathObjective f y0 tj1
    let δj := λ[ψj1; process.y j | process.mem_domain j]
    (Mf : ℝ) ^ (2 : ℕ) *
      (δj ^ (2 : ℕ) /
          (2 * (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ))) +
        (Mf : ℝ) * δj ^ (3 : ℕ) /
          (2 * (1 + (Mf : ℝ) * δj) * (3 + 2 * (Mf : ℝ) * δj)) -
        tj1 * pathFollowingObjectiveNorm f y0 (process.y j) (process.mem_domain j) *
          (δj * (1 + (Mf : ℝ) * δj) /
            (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ))))
  have hkernel_fixed :
      (Finset.range k).sum scalarKernel + scalarKernel k ≤
        (Finset.range k).sum stepLower +
          (Mf : ℝ) ^ (2 : ℕ) * tk *
            inner ℝ (∇ f (y0 : E)) ((y0 : E) - process.y k) +
          actualDrop k := by
    -- Move the scalar-kernel owner back to the fixed-surface package once.
    simpa [actualDrop, scalarKernel, stepLower, tk] using
      pathFollowingFixedSurfacePackageWithBaseTiltPlusTerminal_ge_scalarizedKernelPackage
        (f := f) (Mf := Mf) y0 process k
  have hprefix_transport :
      (Finset.range k).sum stepLower +
          (Mf : ℝ) ^ (2 : ℕ) * tk *
            inner ℝ (∇ f (y0 : E)) ((y0 : E) - process.y k) ≤
        (Finset.range k).sum actualDrop := by
    -- Transport the fixed-surface prefix package to the native actual prefix gaps.
    simpa [actualDrop, stepLower, tk] using
      pathFollowingActualPrefixGap_ge_fixedSurfacePackageWithBaseTilt
        (f := f) (Mf := Mf) y0 process k
  have hactual_prefix :
      (Finset.range k).sum actualDrop =
        (Mf : ℝ) ^ (2 : ℕ) * (f (y0 : E) - f (process.y k)) := by
    -- Telescope the actual drops exactly to the objective gap from `y₀` to `y_k`.
    calc
      (Finset.range k).sum actualDrop =
          (Mf : ℝ) ^ (2 : ℕ) *
            (Finset.range k).sum (fun j ↦ f (process.y j) - f (process.y (j + 1))) := by
              simp [actualDrop, Finset.mul_sum]
      _ =
          (Mf : ℝ) ^ (2 : ℕ) * (f (y0 : E) - f (process.y k)) := by
            rw [pathFollowingObjectiveGap_telescope (f := f) (Mf := Mf) y0 process k]
  have hcurrent_prefix :
      (Mf : ℝ) ^ (2 : ℕ) * (ψk (y0 : E) - ψk (process.y k)) +
          (Mf : ℝ) ^ (2 : ℕ) * tk *
            inner ℝ (∇ f (y0 : E)) ((y0 : E) - process.y k) =
        (Finset.range k).sum actualDrop := by
    -- Rewrite the corrected current-surface prefix to the native objective gap owner.
    calc
      (Mf : ℝ) ^ (2 : ℕ) * (ψk (y0 : E) - ψk (process.y k)) +
          (Mf : ℝ) ^ (2 : ℕ) * tk *
            inner ℝ (∇ f (y0 : E)) ((y0 : E) - process.y k) =
        (Mf : ℝ) ^ (2 : ℕ) * (f (y0 : E) - f (process.y k)) := by
            simpa [tk, ψk] using
              pathFollowingCurrentSurfaceGapWithBaseTilt_eq_actualGap
                (f := f) (Mf := Mf) y0 process k
      _ = (Finset.range k).sum actualDrop := hactual_prefix.symm
  have hterminal :
      terminalCurrentSurfacePackage = actualDrop k := by
    -- The terminal current-surface package is exactly the terminal actual drop.
    simpa [terminalCurrentSurfacePackage, tk, ψk, actualDrop] using
      pathFollowingTerminalCurrentSurfacePackage_eq_actualDrop
        (f := f) (Mf := Mf) y0 process k
  -- Keep the hard scalar owner separate, then transport prefix and terminal pieces once each.
  calc
    (Finset.range k).sum scalarKernel + scalarKernel k ≤
      (Finset.range k).sum stepLower +
        (Mf : ℝ) ^ (2 : ℕ) * tk *
          inner ℝ (∇ f (y0 : E)) ((y0 : E) - process.y k) +
        actualDrop k := hkernel_fixed
    _ ≤ (Finset.range k).sum actualDrop + actualDrop k := by
      exact add_le_add_right hprefix_transport _
    _ = (Finset.range k).sum actualDrop + terminalCurrentSurfacePackage := by
      rw [← hterminal]
    _ =
      (Mf : ℝ) ^ (2 : ℕ) * (ψk (y0 : E) - ψk (process.y k)) +
        (Mf : ℝ) ^ (2 : ℕ) * tk *
          inner ℝ (∇ f (y0 : E)) ((y0 : E) - process.y k) +
        terminalCurrentSurfacePackage := by
          rw [← hcurrent_prefix]

/-- Helper for Theorem 5 2 3: the exact terminal current-surface package already dominates the
same one-step scalar kernel as the native actual-drop owner. -/
private theorem pathFollowingTerminalCurrentSurfacePackage_ge_scalarizedKernel
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (y0 : dom)
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ)
    (k : ℕ) :
    let tk := (process.t k : ℝ)
    let ψk := auxiliaryCentralPathObjective f y0 tk
    let terminalCurrentSurfacePackage : ℝ :=
      (Mf : ℝ) ^ (2 : ℕ) * (ψk (process.y k) - ψk (process.y (k + 1))) +
        (Mf : ℝ) ^ (2 : ℕ) * tk *
          inner ℝ (∇ f (y0 : E)) (process.y k - process.y (k + 1))
    let scalarKernel : ℕ → ℝ := fun j ↦
      let tj1 := (process.t (j + 1) : ℝ)
      let ψj1 := auxiliaryCentralPathObjective f y0 tj1
      let δj := λ[ψj1; process.y j | process.mem_domain j]
      (Mf : ℝ) ^ (2 : ℕ) *
        (δj ^ (2 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ))) +
          (Mf : ℝ) * δj ^ (3 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δj) * (3 + 2 * (Mf : ℝ) * δj)) -
          tj1 * pathFollowingObjectiveNorm f y0 (process.y j) (process.mem_domain j) *
            (δj * (1 + (Mf : ℝ) * δj) /
              (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ))))
    scalarKernel k ≤ terminalCurrentSurfacePackage := by
  let tk := (process.t k : ℝ)
  let ψk := auxiliaryCentralPathObjective f y0 tk
  let actualDrop : ℕ → ℝ := fun j ↦
    (Mf : ℝ) ^ (2 : ℕ) * (f (process.y j) - f (process.y (j + 1)))
  let terminalCurrentSurfacePackage : ℝ :=
    (Mf : ℝ) ^ (2 : ℕ) * (ψk (process.y k) - ψk (process.y (k + 1))) +
      (Mf : ℝ) ^ (2 : ℕ) * tk *
        inner ℝ (∇ f (y0 : E)) (process.y k - process.y (k + 1))
  let scalarKernel : ℕ → ℝ := fun j ↦
    let tj1 := (process.t (j + 1) : ℝ)
    let ψj1 := auxiliaryCentralPathObjective f y0 tj1
    let δj := λ[ψj1; process.y j | process.mem_domain j]
    (Mf : ℝ) ^ (2 : ℕ) *
      (δj ^ (2 : ℕ) /
          (2 * (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ))) +
        (Mf : ℝ) * δj ^ (3 : ℕ) /
          (2 * (1 + (Mf : ℝ) * δj) * (3 + 2 * (Mf : ℝ) * δj)) -
        tj1 * pathFollowingObjectiveNorm f y0 (process.y j) (process.mem_domain j) *
          (δj * (1 + (Mf : ℝ) * δj) /
            (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ))))
  have hkernel :
      scalarKernel k ≤ actualDrop k := by
    -- Reuse the native one-step scalarized lower bound before changing owners.
    simpa [actualDrop, scalarKernel] using
      pathFollowingActualDrop_ge_scalarizedKernel
        (f := f) (Mf := Mf) y0 process k
  have hterminal :
      terminalCurrentSurfacePackage = actualDrop k := by
    -- Transport the exact terminal current-surface owner to the native actual drop once.
    simpa [terminalCurrentSurfacePackage, tk, ψk, actualDrop] using
      pathFollowingTerminalCurrentSurfacePackage_eq_actualDrop
        (f := f) (Mf := Mf) y0 process k
  calc
    scalarKernel k ≤ actualDrop k := hkernel
    _ = terminalCurrentSurfacePackage := hterminal.symm

/-- Helper for Theorem 5 2 3: the native scalar-kernel package is in fact nonpositive under the
available Stage-1 and centering bounds, so the positive branch cannot be closed on this owner. -/
-- Route correction: the previous scalarized odd-weight lower bound is mathematically impossible
-- on this owner; the remaining positive branch must be reproved directly on the corrected
-- current-surface or actual-gap package instead.
private theorem pathFollowingScalarizedKernelPackage_nonpos
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (hτ_nonneg : 0 ≤ τ) (htau : τ ≤ 0.23) (y0 : dom)
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ)
    (centering :
      ∀ j : ℕ,
        satisfies_approximate_centering_condition f y0 (process.t j) (process.y j)
          (process.mem_domain j) Mf (pathFollowingCenteringBeta τ))
    (N : ℕ)
    (hstage :
      ∀ j : ℕ, j ≤ N →
        1 / (2 * (Mf : ℝ)) ≤ λ[f; process.y j | process.mem_domain j])
    {k : ℕ} (hk : k < N) :
    let scalarKernel : ℕ → ℝ := fun j ↦
      let tj1 := (process.t (j + 1) : ℝ)
      let ψj1 := auxiliaryCentralPathObjective f y0 tj1
      let δj := λ[ψj1; process.y j | process.mem_domain j]
      (Mf : ℝ) ^ (2 : ℕ) *
        (δj ^ (2 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ))) +
          (Mf : ℝ) * δj ^ (3 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δj) * (3 + 2 * (Mf : ℝ) * δj)) -
          tj1 * pathFollowingObjectiveNorm f y0 (process.y j) (process.mem_domain j) *
            (δj * (1 + (Mf : ℝ) * δj) /
              (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ))))
    (Finset.range k).sum scalarKernel + scalarKernel k ≤ 0 := by
  let scalarKernel : ℕ → ℝ := fun j ↦
    let tj1 := (process.t (j + 1) : ℝ)
    let ψj1 := auxiliaryCentralPathObjective f y0 tj1
    let δj := λ[ψj1; process.y j | process.mem_domain j]
    (Mf : ℝ) ^ (2 : ℕ) *
      (δj ^ (2 : ℕ) /
          (2 * (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ))) +
        (Mf : ℝ) * δj ^ (3 : ℕ) /
          (2 * (1 + (Mf : ℝ) * δj) * (3 + 2 * (Mf : ℝ) * δj)) -
        tj1 * pathFollowingObjectiveNorm f y0 (process.y j) (process.mem_domain j) *
          (δj * (1 + (Mf : ℝ) * δj) /
            (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ))))
  have hprefix_nonpos : (Finset.range k).sum scalarKernel ≤ 0 := by
    -- Sum the pointwise nonpositive intermediate kernels without reopening any transport.
    refine Finset.sum_nonpos ?_
    intro j hj
    have hjN : j ≤ N := by
      exact Nat.le_trans (Nat.le_of_lt (Finset.mem_range.mp hj)) (Nat.le_of_lt hk)
    simpa [scalarKernel] using
      pathFollowingIntermediateScalarizedKernel_nonpos
        (f := f) (Mf := Mf) hτ_nonneg htau y0 process centering N hstage
        (j := j) hjN
  have hterminal_nonpos : scalarKernel k ≤ 0 := by
    -- The terminal normalized kernel obeys the same nonpositivity estimate.
    simpa [scalarKernel] using
      pathFollowingTerminalScalarizedKernel_nonpos
        (f := f) (Mf := Mf) hτ_nonneg htau y0 process centering N hstage hk
  exact add_nonpos hprefix_nonpos hterminal_nonpos

/-- Helper for Theorem 5 2 3: the exact next-iterate objective gap splits into the current gap
at index `k` plus the terminal actual drop. -/
private theorem pathFollowingActualGapToNextIterate_eq_actualGap_add_terminalActualDrop
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (y0 : dom)
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ)
    (k : ℕ) :
    let actualGap : ℕ → ℝ := fun j ↦
      (Mf : ℝ) ^ (2 : ℕ) * (f (y0 : E) - f (process.y j))
    let actualDrop : ℕ → ℝ := fun j ↦
      (Mf : ℝ) ^ (2 : ℕ) * (f (process.y j) - f (process.y (j + 1)))
    actualGap (k + 1) = actualGap k + actualDrop k := by
  let actualGap : ℕ → ℝ := fun j ↦
    (Mf : ℝ) ^ (2 : ℕ) * (f (y0 : E) - f (process.y j))
  let actualDrop : ℕ → ℝ := fun j ↦
    (Mf : ℝ) ^ (2 : ℕ) * (f (process.y j) - f (process.y (j + 1)))
  -- Keep the exact owner spelling fixed and split only the scalarized objective gap.
  calc
    actualGap (k + 1) =
      (Mf : ℝ) ^ (2 : ℕ) *
        ((f (y0 : E) - f (process.y k)) + (f (process.y k) - f (process.y (k + 1)))) := by
          simp [actualGap]
          ring
    _ = actualGap k + actualDrop k := by
          simp [actualGap, actualDrop]
          ring

/-- Helper for Theorem 5 2 3: the accumulated actual drops through the terminal step `k`
telescope exactly to the objective gap `M_f^2 (f(y₀) - f(y_{k+1}))`. -/
private theorem pathFollowingActualGapToNextIterate_eq_sumActualDrop
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (y0 : dom)
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ)
    (k : ℕ) :
    let actualDrop : ℕ → ℝ := fun j ↦
      (Mf : ℝ) ^ (2 : ℕ) * (f (process.y j) - f (process.y (j + 1)))
    (Finset.range k).sum actualDrop + actualDrop k =
      (Mf : ℝ) ^ (2 : ℕ) * (f (y0 : E) - f (process.y (k + 1))) := by
  let actualDrop : ℕ → ℝ := fun j ↦
    (Mf : ℝ) ^ (2 : ℕ) * (f (process.y j) - f (process.y (j + 1)))
  have hsum_actual :
      (Finset.range k).sum actualDrop + actualDrop k =
        (Mf : ℝ) ^ (2 : ℕ) *
          (Finset.range (k + 1)).sum
            (fun j ↦ f (process.y j) - f (process.y (j + 1))) := by
    -- Append the terminal drop to the prefix sum, then factor out the fixed scalar `M_f²`.
    calc
      (Finset.range k).sum actualDrop + actualDrop k =
          (Finset.range (k + 1)).sum actualDrop := by
            rw [Finset.sum_range_succ]
      _ =
          (Mf : ℝ) ^ (2 : ℕ) *
            (Finset.range (k + 1)).sum
              (fun j ↦ f (process.y j) - f (process.y (j + 1))) := by
            simp [actualDrop, Finset.mul_sum]
  have htel :
      (Finset.range (k + 1)).sum (fun j ↦ f (process.y j) - f (process.y (j + 1))) =
        f (y0 : E) - f (process.y (k + 1)) :=
    pathFollowingObjectiveGap_telescope (f := f) (Mf := Mf) y0 process (k + 1)
  calc
    (Finset.range k).sum actualDrop + actualDrop k =
        (Mf : ℝ) ^ (2 : ℕ) *
          (Finset.range (k + 1)).sum
            (fun j ↦ f (process.y j) - f (process.y (j + 1))) := hsum_actual
    _ =
        (Mf : ℝ) ^ (2 : ℕ) * (f (y0 : E) - f (process.y (k + 1))) := by
          rw [htel]

/-- Helper for Theorem 5 2 3: the fixed-surface package plus the terminal actual drop transports
to the exact objective gap once the prefix package has already been rewritten as actual drops. -/
private theorem pathFollowingActualGapToNextIterate_ge_fixedSurfacePackageWithBaseTiltPlusTerminal
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (y0 : dom)
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ)
    (k : ℕ) :
    let tk := (process.t k : ℝ)
    let stepLower : ℕ → ℝ := fun j ↦
      let tj1 := (process.t (j + 1) : ℝ)
      let ψj1 := auxiliaryCentralPathObjective f y0 tj1
      let δj := λ[ψj1; process.y j | process.mem_domain j]
      (Mf : ℝ) ^ (2 : ℕ) *
          (δj ^ (2 : ℕ) /
              (2 * (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ))) +
            (Mf : ℝ) * δj ^ (3 : ℕ) /
              (2 * (1 + (Mf : ℝ) * δj) * (3 + 2 * (Mf : ℝ) * δj))) +
        (Mf : ℝ) ^ (2 : ℕ) *
          (((process.t (j + 1) : ℝ) - tk) *
            inner ℝ (∇ f (y0 : E)) (process.y j - process.y (j + 1)))
    let actualDrop : ℕ → ℝ := fun j ↦
      (Mf : ℝ) ^ (2 : ℕ) * (f (process.y j) - f (process.y (j + 1)))
    (Finset.range k).sum stepLower +
        (Mf : ℝ) ^ (2 : ℕ) * tk *
          inner ℝ (∇ f (y0 : E)) ((y0 : E) - process.y k) +
        actualDrop k ≤
      (Mf : ℝ) ^ (2 : ℕ) * (f (y0 : E) - f (process.y (k + 1))) := by
  let tk := (process.t k : ℝ)
  let stepLower : ℕ → ℝ := fun j ↦
    let tj1 := (process.t (j + 1) : ℝ)
    let ψj1 := auxiliaryCentralPathObjective f y0 tj1
    let δj := λ[ψj1; process.y j | process.mem_domain j]
    (Mf : ℝ) ^ (2 : ℕ) *
        (δj ^ (2 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ))) +
          (Mf : ℝ) * δj ^ (3 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δj) * (3 + 2 * (Mf : ℝ) * δj))) +
      (Mf : ℝ) ^ (2 : ℕ) *
        (((process.t (j + 1) : ℝ) - tk) *
          inner ℝ (∇ f (y0 : E)) (process.y j - process.y (j + 1)))
  let actualDrop : ℕ → ℝ := fun j ↦
    (Mf : ℝ) ^ (2 : ℕ) * (f (process.y j) - f (process.y (j + 1)))
  have hprefix_transport :
      (Finset.range k).sum stepLower +
          (Mf : ℝ) ^ (2 : ℕ) * tk *
            inner ℝ (∇ f (y0 : E)) ((y0 : E) - process.y k) ≤
        (Finset.range k).sum actualDrop := by
    -- Transport the fixed-surface prefix package to the corresponding actual prefix gaps.
    simpa [actualDrop, stepLower, tk] using
      pathFollowingActualPrefixGap_ge_fixedSurfacePackageWithBaseTilt
        (f := f) (Mf := Mf) y0 process k
  have hsum_actual :
      (Finset.range k).sum actualDrop + actualDrop k =
        (Mf : ℝ) ^ (2 : ℕ) * (f (y0 : E) - f (process.y (k + 1))) := by
    -- Telescope the transported prefix and the terminal actual drop only once.
    simpa [actualDrop] using
      pathFollowingActualGapToNextIterate_eq_sumActualDrop
        (f := f) (Mf := Mf) y0 process k
  -- Route correction: keep the package-to-actual-drop transport separate from the final
  -- objective-gap telescope so the positive-`κ` owner only needs the lower bound on this stable
  -- transported package.
  calc
    (Finset.range k).sum stepLower +
        (Mf : ℝ) ^ (2 : ℕ) * tk *
          inner ℝ (∇ f (y0 : E)) ((y0 : E) - process.y k) +
        actualDrop k ≤
      (Finset.range k).sum actualDrop + actualDrop k := by
        exact add_le_add_right hprefix_transport _
    _ =
      (Mf : ℝ) ^ (2 : ℕ) * (f (y0 : E) - f (process.y (k + 1))) := hsum_actual

/-- Helper for Theorem 5 2 3: the normalized prefix-plus-terminal owner is exactly the
compensated fixed-surface package together with the terminal actual drop. -/
private theorem pathFollowingNormalizedPrefixPlusTerminal_eq_fixedSurfacePackageWithBaseTiltPlusTerminal
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (y0 : dom)
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ)
    (k : ℕ) :
    let tk := (process.t k : ℝ)
    let stepLower : ℕ → ℝ := fun j ↦
      let tj1 := (process.t (j + 1) : ℝ)
      let ψj1 := auxiliaryCentralPathObjective f y0 tj1
      let δj := λ[ψj1; process.y j | process.mem_domain j]
      (Mf : ℝ) ^ (2 : ℕ) *
          (δj ^ (2 : ℕ) /
              (2 * (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ))) +
            (Mf : ℝ) * δj ^ (3 : ℕ) /
              (2 * (1 + (Mf : ℝ) * δj) * (3 + 2 * (Mf : ℝ) * δj))) +
        (Mf : ℝ) ^ (2 : ℕ) *
          (((process.t (j + 1) : ℝ) - tk) *
            inner ℝ (∇ f (y0 : E)) (process.y j - process.y (j + 1)))
    let prefixTerm : ℕ → ℝ := fun j ↦
      let tj1 := (process.t (j + 1) : ℝ)
      let ψj1 := auxiliaryCentralPathObjective f y0 tj1
      let δj := λ[ψj1; process.y j | process.mem_domain j]
      (Mf : ℝ) ^ (2 : ℕ) *
          (δj ^ (2 : ℕ) /
              (2 * (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ))) +
            (Mf : ℝ) * δj ^ (3 : ℕ) /
              (2 * (1 + (Mf : ℝ) * δj) * (3 + 2 * (Mf : ℝ) * δj))) +
        (Mf : ℝ) ^ (2 : ℕ) *
          ((process.t (j + 1) : ℝ) *
            inner ℝ (∇ f (y0 : E)) (process.y j - process.y (j + 1)))
    let actualDrop : ℕ → ℝ := fun j ↦
      (Mf : ℝ) ^ (2 : ℕ) * (f (process.y j) - f (process.y (j + 1)))
    let ψk := auxiliaryCentralPathObjective f y0 tk
    let terminalCurrentSurfacePackage : ℝ :=
      (Mf : ℝ) ^ (2 : ℕ) * (ψk (process.y k) - ψk (process.y (k + 1))) +
        (Mf : ℝ) ^ (2 : ℕ) * tk *
          inner ℝ (∇ f (y0 : E)) (process.y k - process.y (k + 1))
    (Finset.range k).sum prefixTerm + terminalCurrentSurfacePackage =
      (Finset.range k).sum stepLower +
        (Mf : ℝ) ^ (2 : ℕ) * tk *
          inner ℝ (∇ f (y0 : E)) ((y0 : E) - process.y k) +
        actualDrop k := by
  let tk := (process.t k : ℝ)
  let stepLower : ℕ → ℝ := fun j ↦
    let tj1 := (process.t (j + 1) : ℝ)
    let ψj1 := auxiliaryCentralPathObjective f y0 tj1
    let δj := λ[ψj1; process.y j | process.mem_domain j]
    (Mf : ℝ) ^ (2 : ℕ) *
        (δj ^ (2 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ))) +
          (Mf : ℝ) * δj ^ (3 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δj) * (3 + 2 * (Mf : ℝ) * δj))) +
      (Mf : ℝ) ^ (2 : ℕ) *
        (((process.t (j + 1) : ℝ) - tk) *
          inner ℝ (∇ f (y0 : E)) (process.y j - process.y (j + 1)))
  let prefixTerm : ℕ → ℝ := fun j ↦
    let tj1 := (process.t (j + 1) : ℝ)
    let ψj1 := auxiliaryCentralPathObjective f y0 tj1
    let δj := λ[ψj1; process.y j | process.mem_domain j]
    (Mf : ℝ) ^ (2 : ℕ) *
        (δj ^ (2 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ))) +
          (Mf : ℝ) * δj ^ (3 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δj) * (3 + 2 * (Mf : ℝ) * δj))) +
      (Mf : ℝ) ^ (2 : ℕ) *
        ((process.t (j + 1) : ℝ) *
          inner ℝ (∇ f (y0 : E)) (process.y j - process.y (j + 1)))
  let actualDrop : ℕ → ℝ := fun j ↦
    (Mf : ℝ) ^ (2 : ℕ) * (f (process.y j) - f (process.y (j + 1)))
  let ψk := auxiliaryCentralPathObjective f y0 tk
  let terminalCurrentSurfacePackage : ℝ :=
    (Mf : ℝ) ^ (2 : ℕ) * (ψk (process.y k) - ψk (process.y (k + 1))) +
      (Mf : ℝ) ^ (2 : ℕ) * tk *
        inner ℝ (∇ f (y0 : E)) (process.y k - process.y (k + 1))
  have hprefix :
      (Finset.range k).sum stepLower +
          (Mf : ℝ) ^ (2 : ℕ) * tk *
            inner ℝ (∇ f (y0 : E)) ((y0 : E) - process.y k) =
        (Finset.range k).sum prefixTerm := by
    -- Rewrite the compensated fixed-surface prefix package once into the normalized owner.
    simpa [stepLower, prefixTerm, tk] using
      pathFollowingFixedSurfacePackageWithBaseTilt_eq_sumPrefixTerms
        (f := f) (Mf := Mf) y0 process k
  have hterminal :
      terminalCurrentSurfacePackage = actualDrop k := by
    -- Rewrite the terminal current-surface contribution once into the native actual-drop owner.
    simpa [terminalCurrentSurfacePackage, tk, ψk, actualDrop] using
      pathFollowingTerminalCurrentSurfacePackage_eq_actualDrop
        (f := f) (Mf := Mf) y0 process k
  -- Combine the prefix and terminal transports into one stable aggregate owner equality.
  calc
    (Finset.range k).sum prefixTerm + terminalCurrentSurfacePackage =
        ((Finset.range k).sum stepLower +
            (Mf : ℝ) ^ (2 : ℕ) * tk *
              inner ℝ (∇ f (y0 : E)) ((y0 : E) - process.y k)) +
          terminalCurrentSurfacePackage := by
            rw [hprefix]
    _ =
        ((Finset.range k).sum stepLower +
            (Mf : ℝ) ^ (2 : ℕ) * tk *
              inner ℝ (∇ f (y0 : E)) ((y0 : E) - process.y k)) +
          actualDrop k := by
            rw [hterminal]
    _ =
        (Finset.range k).sum stepLower +
          (Mf : ℝ) ^ (2 : ℕ) * tk *
            inner ℝ (∇ f (y0 : E)) ((y0 : E) - process.y k) +
          actualDrop k := by
            ring

/-- Helper for Theorem 5 2 3: splitting the odd weight `2 k + 1` into its even-prefix part
`2 k` and its terminal single-step part `1` reduces the final lower bound to two independent
component inequalities on the same owner. -/
private theorem pathFollowingOddWeightFromEvenPrefixAndTerminal
    {Mf : NNRealˣ} {τ ν prefixBound terminalBound : ℝ} (k : ℕ)
    (hprefix :
      pathFollowingKappa τ * (2 * k : ℝ) * (Mf : ℝ) * ν ≤ prefixBound)
    (hterminal :
      pathFollowingKappa τ * (Mf : ℝ) * ν ≤ terminalBound) :
    pathFollowingKappa τ * (2 * k + 1 : ℝ) * (Mf : ℝ) * ν ≤
      prefixBound + terminalBound := by
  have hsplit :
      pathFollowingKappa τ * (2 * k + 1 : ℝ) * (Mf : ℝ) * ν =
        pathFollowingKappa τ * (2 * k : ℝ) * (Mf : ℝ) * ν +
          pathFollowingKappa τ * (Mf : ℝ) * ν := by
    -- Expand the odd coefficient once so the two component bounds can be added directly.
    ring
  -- After the coefficient split, add the even-prefix and terminal estimates on the common owner.
  rw [hsplit]
  exact add_le_add hprefix hterminal

/-- Helper for Theorem 5 2 3: clearing the canonical denominator in `κ(τ)` isolates the
source-facing numerator `(τ - 3 β(τ)) (1 + β(τ))`. -/
private theorem pathFollowingKappa_mul_denominator
    {τ : ℝ} :
    pathFollowingKappa τ *
        (2 * (1 + pathFollowingCenteringBeta τ +
          (pathFollowingCenteringBeta τ) ^ (2 : ℕ))) =
      (τ - 3 * pathFollowingCenteringBeta τ) *
        (1 + pathFollowingCenteringBeta τ) := by
  -- Expand `κ(τ)` once, then cancel the common denominator on the positive-branch scalar side.
  rw [pathFollowingKappa_def]
  ring

/-- Helper for Theorem 5 2 3: the live positive-`κ` frontier is the aggregate lower bound on the
normalized prefix-plus-terminal owner, without splitting it into separate prefix and terminal
subclaims. -/
private theorem pathFollowingNormalizedPrefixPlusTerminal_ge_oddWeightObjectiveNorm_core
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (hτ_nonneg : 0 ≤ τ) (htau : τ ≤ 0.23) (y0 : dom)
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ)
    (centering :
      ∀ j : ℕ,
        satisfies_approximate_centering_condition f y0 (process.t j) (process.y j)
          (process.mem_domain j) Mf (pathFollowingCenteringBeta τ))
    (N : ℕ)
    (hstage :
      ∀ j : ℕ, j ≤ N →
        1 / (2 * (Mf : ℝ)) ≤ λ[f; process.y j | process.mem_domain j])
    {k : ℕ} (hk : k < N)
    (hkappa_pos : 0 < pathFollowingKappa τ) :
    let prefixTerm : ℕ → ℝ := fun j ↦
      let tj1 := (process.t (j + 1) : ℝ)
      let ψj1 := auxiliaryCentralPathObjective f y0 tj1
      let δj := λ[ψj1; process.y j | process.mem_domain j]
      (Mf : ℝ) ^ (2 : ℕ) *
          (δj ^ (2 : ℕ) /
              (2 * (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ))) +
            (Mf : ℝ) * δj ^ (3 : ℕ) /
              (2 * (1 + (Mf : ℝ) * δj) * (3 + 2 * (Mf : ℝ) * δj))) +
        (Mf : ℝ) ^ (2 : ℕ) *
          ((process.t (j + 1) : ℝ) *
            inner ℝ (∇ f (y0 : E)) (process.y j - process.y (j + 1)))
    let tk := (process.t k : ℝ)
    let ψk := auxiliaryCentralPathObjective f y0 tk
    let terminalCurrentSurfacePackage : ℝ :=
      (Mf : ℝ) ^ (2 : ℕ) * (ψk (process.y k) - ψk (process.y (k + 1))) +
        (Mf : ℝ) ^ (2 : ℕ) * tk *
          inner ℝ (∇ f (y0 : E)) (process.y k - process.y (k + 1))
    pathFollowingKappa τ * (2 * k + 1 : ℝ) * (Mf : ℝ) *
        pathFollowingObjectiveNorm f y0 (process.y k) (process.mem_domain k) ≤
      (Finset.range k).sum prefixTerm + terminalCurrentSurfacePackage := by
  let prefixTerm : ℕ → ℝ := fun j ↦
    let tj1 := (process.t (j + 1) : ℝ)
    let ψj1 := auxiliaryCentralPathObjective f y0 tj1
    let δj := λ[ψj1; process.y j | process.mem_domain j]
    (Mf : ℝ) ^ (2 : ℕ) *
        (δj ^ (2 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ))) +
          (Mf : ℝ) * δj ^ (3 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δj) * (3 + 2 * (Mf : ℝ) * δj))) +
      (Mf : ℝ) ^ (2 : ℕ) *
        ((process.t (j + 1) : ℝ) *
          inner ℝ (∇ f (y0 : E)) (process.y j - process.y (j + 1)))
  let tk := (process.t k : ℝ)
  let ψk := auxiliaryCentralPathObjective f y0 tk
  let terminalCurrentSurfacePackage : ℝ :=
    (Mf : ℝ) ^ (2 : ℕ) * (ψk (process.y k) - ψk (process.y (k + 1))) +
      (Mf : ℝ) ^ (2 : ℕ) * tk *
        inner ℝ (∇ f (y0 : E)) (process.y k - process.y (k + 1))
  -- Route correction: the old conjunction `hpieces : A ∧ B` forced a false split between an
  -- even-prefix estimate and an independent terminal estimate. The real blocker is the single
  -- aggregate lower bound on the normalized owner.
  -- TODO: prove the aggregate odd-weight lower bound directly on
  -- `(Finset.range k).sum prefixTerm + terminalCurrentSurfacePackage`, then transport it to the
  -- fixed-surface and exact-gap owners through the existing rewrite lemmas below.
  sorry

/-- Helper for Theorem 5 2 3: the positive-`κ` branch should be closed on the compensated
fixed-surface package with the shared `t_k` tilt and the terminal actual drop, not on the split
exact owner `actualGap k + actualDrop k`. -/
private theorem pathFollowingFixedSurfacePackageWithBaseTiltPlusTerminal_ge_oddWeightObjectiveNorm
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (hτ_nonneg : 0 ≤ τ) (htau : τ ≤ 0.23) (y0 : dom)
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ)
    (centering :
      ∀ j : ℕ,
        satisfies_approximate_centering_condition f y0 (process.t j) (process.y j)
          (process.mem_domain j) Mf (pathFollowingCenteringBeta τ))
    (N : ℕ)
    (hstage :
      ∀ j : ℕ, j ≤ N →
        1 / (2 * (Mf : ℝ)) ≤ λ[f; process.y j | process.mem_domain j])
    {k : ℕ} (hk : k < N)
    (hkappa_pos : 0 < pathFollowingKappa τ) :
    let tk := (process.t k : ℝ)
    let stepLower : ℕ → ℝ := fun j ↦
      let tj1 := (process.t (j + 1) : ℝ)
      let ψj1 := auxiliaryCentralPathObjective f y0 tj1
      let δj := λ[ψj1; process.y j | process.mem_domain j]
      (Mf : ℝ) ^ (2 : ℕ) *
          (δj ^ (2 : ℕ) /
              (2 * (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ))) +
            (Mf : ℝ) * δj ^ (3 : ℕ) /
              (2 * (1 + (Mf : ℝ) * δj) * (3 + 2 * (Mf : ℝ) * δj))) +
        (Mf : ℝ) ^ (2 : ℕ) *
          (((process.t (j + 1) : ℝ) - tk) *
            inner ℝ (∇ f (y0 : E)) (process.y j - process.y (j + 1)))
    let actualDrop : ℕ → ℝ := fun j ↦
      (Mf : ℝ) ^ (2 : ℕ) * (f (process.y j) - f (process.y (j + 1)))
    pathFollowingKappa τ * (2 * k + 1 : ℝ) * (Mf : ℝ) *
        pathFollowingObjectiveNorm f y0 (process.y k) (process.mem_domain k) ≤
      (Finset.range k).sum stepLower +
        (Mf : ℝ) ^ (2 : ℕ) * tk *
          inner ℝ (∇ f (y0 : E)) ((y0 : E) - process.y k) +
        actualDrop k := by
  let tk := (process.t k : ℝ)
  let stepLower : ℕ → ℝ := fun j ↦
    let tj1 := (process.t (j + 1) : ℝ)
    let ψj1 := auxiliaryCentralPathObjective f y0 tj1
    let δj := λ[ψj1; process.y j | process.mem_domain j]
    (Mf : ℝ) ^ (2 : ℕ) *
        (δj ^ (2 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ))) +
          (Mf : ℝ) * δj ^ (3 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δj) * (3 + 2 * (Mf : ℝ) * δj))) +
      (Mf : ℝ) ^ (2 : ℕ) *
        (((process.t (j + 1) : ℝ) - tk) *
          inner ℝ (∇ f (y0 : E)) (process.y j - process.y (j + 1)))
  let actualDrop : ℕ → ℝ := fun j ↦
    (Mf : ℝ) ^ (2 : ℕ) * (f (process.y j) - f (process.y (j + 1)))
  have hnormalized :
      pathFollowingKappa τ * (2 * k + 1 : ℝ) * (Mf : ℝ) *
          pathFollowingObjectiveNorm f y0 (process.y k) (process.mem_domain k) ≤
        let prefixTerm : ℕ → ℝ := fun j ↦
          let tj1 := (process.t (j + 1) : ℝ)
          let ψj1 := auxiliaryCentralPathObjective f y0 tj1
          let δj := λ[ψj1; process.y j | process.mem_domain j]
          (Mf : ℝ) ^ (2 : ℕ) *
              (δj ^ (2 : ℕ) /
                  (2 * (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ))) +
                (Mf : ℝ) * δj ^ (3 : ℕ) /
                  (2 * (1 + (Mf : ℝ) * δj) * (3 + 2 * (Mf : ℝ) * δj))) +
            (Mf : ℝ) ^ (2 : ℕ) *
              ((process.t (j + 1) : ℝ) *
                inner ℝ (∇ f (y0 : E)) (process.y j - process.y (j + 1)))
        let ψk := auxiliaryCentralPathObjective f y0 tk
        let terminalCurrentSurfacePackage : ℝ :=
          (Mf : ℝ) ^ (2 : ℕ) * (ψk (process.y k) - ψk (process.y (k + 1))) +
            (Mf : ℝ) ^ (2 : ℕ) * tk *
              inner ℝ (∇ f (y0 : E)) (process.y k - process.y (k + 1))
        (Finset.range k).sum prefixTerm + terminalCurrentSurfacePackage := by
    -- Route correction: keep the only open positive-`κ` obligation on the normalized owner,
    -- where the blocker is the single aggregate odd-weight lower bound.
    simpa [tk] using
      pathFollowingNormalizedPrefixPlusTerminal_ge_oddWeightObjectiveNorm_core
        (f := f) (Mf := Mf) hτ_nonneg htau y0 process centering N hstage hk hkappa_pos
  have hrewrite :
      (let prefixTerm : ℕ → ℝ := fun j ↦
          let tj1 := (process.t (j + 1) : ℝ)
          let ψj1 := auxiliaryCentralPathObjective f y0 tj1
          let δj := λ[ψj1; process.y j | process.mem_domain j]
          (Mf : ℝ) ^ (2 : ℕ) *
              (δj ^ (2 : ℕ) /
                  (2 * (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ))) +
                (Mf : ℝ) * δj ^ (3 : ℕ) /
                  (2 * (1 + (Mf : ℝ) * δj) * (3 + 2 * (Mf : ℝ) * δj))) +
            (Mf : ℝ) ^ (2 : ℕ) *
              ((process.t (j + 1) : ℝ) *
                inner ℝ (∇ f (y0 : E)) (process.y j - process.y (j + 1)))
        let ψk := auxiliaryCentralPathObjective f y0 tk
        let terminalCurrentSurfacePackage : ℝ :=
          (Mf : ℝ) ^ (2 : ℕ) * (ψk (process.y k) - ψk (process.y (k + 1))) +
            (Mf : ℝ) ^ (2 : ℕ) * tk *
              inner ℝ (∇ f (y0 : E)) (process.y k - process.y (k + 1))
        (Finset.range k).sum prefixTerm + terminalCurrentSurfacePackage) =
      (Finset.range k).sum stepLower +
        (Mf : ℝ) ^ (2 : ℕ) * tk *
          inner ℝ (∇ f (y0 : E)) ((y0 : E) - process.y k) +
        actualDrop k := by
    -- Rewrite the normalized owner once back to the compensated fixed-surface package.
    simpa [stepLower, tk, actualDrop] using
      pathFollowingNormalizedPrefixPlusTerminal_eq_fixedSurfacePackageWithBaseTiltPlusTerminal
        (f := f) (Mf := Mf) y0 process k
  calc
    pathFollowingKappa τ * (2 * k + 1 : ℝ) * (Mf : ℝ) *
        pathFollowingObjectiveNorm f y0 (process.y k) (process.mem_domain k) ≤
      let prefixTerm : ℕ → ℝ := fun j ↦
        let tj1 := (process.t (j + 1) : ℝ)
        let ψj1 := auxiliaryCentralPathObjective f y0 tj1
        let δj := λ[ψj1; process.y j | process.mem_domain j]
        (Mf : ℝ) ^ (2 : ℕ) *
            (δj ^ (2 : ℕ) /
                (2 * (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ))) +
              (Mf : ℝ) * δj ^ (3 : ℕ) /
                (2 * (1 + (Mf : ℝ) * δj) * (3 + 2 * (Mf : ℝ) * δj))) +
          (Mf : ℝ) ^ (2 : ℕ) *
            ((process.t (j + 1) : ℝ) *
              inner ℝ (∇ f (y0 : E)) (process.y j - process.y (j + 1)))
      let ψk := auxiliaryCentralPathObjective f y0 tk
      let terminalCurrentSurfacePackage : ℝ :=
        (Mf : ℝ) ^ (2 : ℕ) * (ψk (process.y k) - ψk (process.y (k + 1))) +
          (Mf : ℝ) ^ (2 : ℕ) * tk *
            inner ℝ (∇ f (y0 : E)) (process.y k - process.y (k + 1))
      (Finset.range k).sum prefixTerm + terminalCurrentSurfacePackage := hnormalized
    _ =
      (Finset.range k).sum stepLower +
        (Mf : ℝ) ^ (2 : ℕ) * tk *
          inner ℝ (∇ f (y0 : E)) ((y0 : E) - process.y k) +
        actualDrop k := hrewrite

/-- Helper for Theorem 5 2 3: once the odd-weight lower bound is proved on the compensated
fixed-surface package, the normalized prefix-plus-terminal version is just the combined rewrite
back to the original owner. -/
private theorem pathFollowingNormalizedPrefixPlusTerminal_ge_oddWeightObjectiveNorm
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (hτ_nonneg : 0 ≤ τ) (htau : τ ≤ 0.23) (y0 : dom)
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ)
    (centering :
      ∀ j : ℕ,
        satisfies_approximate_centering_condition f y0 (process.t j) (process.y j)
          (process.mem_domain j) Mf (pathFollowingCenteringBeta τ))
    (N : ℕ)
    (hstage :
      ∀ j : ℕ, j ≤ N →
        1 / (2 * (Mf : ℝ)) ≤ λ[f; process.y j | process.mem_domain j])
    {k : ℕ} (hk : k < N)
    (hkappa_pos : 0 < pathFollowingKappa τ) :
    let prefixTerm : ℕ → ℝ := fun j ↦
      let tj1 := (process.t (j + 1) : ℝ)
      let ψj1 := auxiliaryCentralPathObjective f y0 tj1
      let δj := λ[ψj1; process.y j | process.mem_domain j]
      (Mf : ℝ) ^ (2 : ℕ) *
          (δj ^ (2 : ℕ) /
              (2 * (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ))) +
            (Mf : ℝ) * δj ^ (3 : ℕ) /
              (2 * (1 + (Mf : ℝ) * δj) * (3 + 2 * (Mf : ℝ) * δj))) +
        (Mf : ℝ) ^ (2 : ℕ) *
          ((process.t (j + 1) : ℝ) *
            inner ℝ (∇ f (y0 : E)) (process.y j - process.y (j + 1)))
    let tk := (process.t k : ℝ)
    let ψk := auxiliaryCentralPathObjective f y0 tk
    let terminalCurrentSurfacePackage : ℝ :=
      (Mf : ℝ) ^ (2 : ℕ) * (ψk (process.y k) - ψk (process.y (k + 1))) +
        (Mf : ℝ) ^ (2 : ℕ) * tk *
          inner ℝ (∇ f (y0 : E)) (process.y k - process.y (k + 1))
    pathFollowingKappa τ * (2 * k + 1 : ℝ) * (Mf : ℝ) *
        pathFollowingObjectiveNorm f y0 (process.y k) (process.mem_domain k) ≤
      (Finset.range k).sum prefixTerm + terminalCurrentSurfacePackage := by
  -- Route correction: this theorem is now a thin alias to the normalized-owner core theorem, so
  -- the remaining blocker stays isolated on one aggregate proof surface.
  simpa using
    pathFollowingNormalizedPrefixPlusTerminal_ge_oddWeightObjectiveNorm_core
      (f := f) (Mf := Mf) hτ_nonneg htau y0 process centering N hstage hk hkappa_pos

/-- Helper for Theorem 5 2 3: once the compensated fixed-surface package is bounded from below by
the odd-weight term, the exact next-iterate objective gap follows by a single transport step. -/
private theorem pathFollowingActualGapToNextIterate_ge_oddWeightObjectiveNorm_direct
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (hτ_nonneg : 0 ≤ τ) (htau : τ ≤ 0.23) (y0 : dom)
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ)
    (centering :
      ∀ j : ℕ,
        satisfies_approximate_centering_condition f y0 (process.t j) (process.y j)
          (process.mem_domain j) Mf (pathFollowingCenteringBeta τ))
    (N : ℕ)
    (hstage :
      ∀ j : ℕ, j ≤ N →
        1 / (2 * (Mf : ℝ)) ≤ λ[f; process.y j | process.mem_domain j])
    {k : ℕ} (hk : k < N)
    (hkappa_pos : 0 < pathFollowingKappa τ) :
    pathFollowingKappa τ * (2 * k + 1 : ℝ) * (Mf : ℝ) *
        pathFollowingObjectiveNorm f y0 (process.y k) (process.mem_domain k) ≤
      (Mf : ℝ) ^ (2 : ℕ) * (f (y0 : E) - f (process.y (k + 1))) := by
  let tk := (process.t k : ℝ)
  let stepLower : ℕ → ℝ := fun j ↦
    let tj1 := (process.t (j + 1) : ℝ)
    let ψj1 := auxiliaryCentralPathObjective f y0 tj1
    let δj := λ[ψj1; process.y j | process.mem_domain j]
    (Mf : ℝ) ^ (2 : ℕ) *
        (δj ^ (2 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ))) +
          (Mf : ℝ) * δj ^ (3 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δj) * (3 + 2 * (Mf : ℝ) * δj))) +
      (Mf : ℝ) ^ (2 : ℕ) *
        (((process.t (j + 1) : ℝ) - tk) *
          inner ℝ (∇ f (y0 : E)) (process.y j - process.y (j + 1)))
  let actualDrop : ℕ → ℝ := fun j ↦
    (Mf : ℝ) ^ (2 : ℕ) * (f (process.y j) - f (process.y (j + 1)))
  have hpackage_lower :
      pathFollowingKappa τ * (2 * k + 1 : ℝ) * (Mf : ℝ) *
          pathFollowingObjectiveNorm f y0 (process.y k) (process.mem_domain k) ≤
        (Finset.range k).sum stepLower +
          (Mf : ℝ) ^ (2 : ℕ) * tk *
            inner ℝ (∇ f (y0 : E)) ((y0 : E) - process.y k) +
          actualDrop k := by
    -- Keep the positive branch on the compensated fixed-surface package where the shared `t_k`
    -- correction is still visible.
    simpa [tk, stepLower, actualDrop] using
      pathFollowingFixedSurfacePackageWithBaseTiltPlusTerminal_ge_oddWeightObjectiveNorm
        (f := f) (Mf := Mf) hτ_nonneg htau y0 process centering N hstage hk hkappa_pos
  have htransport :
      (Finset.range k).sum stepLower +
          (Mf : ℝ) ^ (2 : ℕ) * tk *
            inner ℝ (∇ f (y0 : E)) ((y0 : E) - process.y k) +
          actualDrop k ≤
        (Mf : ℝ) ^ (2 : ℕ) * (f (y0 : E) - f (process.y (k + 1))) := by
    -- Transport the compensated fixed-surface package to the exact next-iterate objective gap
    -- only once, after the lower bound is proved on the stable owner.
    simpa [tk, stepLower, actualDrop] using
      pathFollowingActualGapToNextIterate_ge_fixedSurfacePackageWithBaseTiltPlusTerminal
        (f := f) (Mf := Mf) y0 process k
  exact le_trans hpackage_lower htransport

/-- Helper for Theorem 5 2 3: the aggregate odd-weight lower bound on the exact current-surface
package is obtained by proving the exact gap theorem first and rewriting the owner once. -/
private theorem pathFollowingCurrentSurfaceGapWithBaseTiltPlusTerminal_ge_oddWeightObjectiveNorm
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (hτ_nonneg : 0 ≤ τ) (htau : τ ≤ 0.23) (y0 : dom)
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ)
    (centering :
      ∀ j : ℕ,
        satisfies_approximate_centering_condition f y0 (process.t j) (process.y j)
          (process.mem_domain j) Mf (pathFollowingCenteringBeta τ))
    (N : ℕ)
    (hstage :
      ∀ j : ℕ, j ≤ N →
        1 / (2 * (Mf : ℝ)) ≤ λ[f; process.y j | process.mem_domain j])
    {k : ℕ} (hk : k < N)
    (hkappa_pos : 0 < pathFollowingKappa τ) :
    let tk := (process.t k : ℝ)
    let ψk := auxiliaryCentralPathObjective f y0 tk
    let terminalCurrentSurfacePackage : ℝ :=
      (Mf : ℝ) ^ (2 : ℕ) * (ψk (process.y k) - ψk (process.y (k + 1))) +
        (Mf : ℝ) ^ (2 : ℕ) * tk *
          inner ℝ (∇ f (y0 : E)) (process.y k - process.y (k + 1))
    let scalarKernel : ℕ → ℝ := fun j ↦
      let tj1 := (process.t (j + 1) : ℝ)
      let ψj1 := auxiliaryCentralPathObjective f y0 tj1
      let δj := λ[ψj1; process.y j | process.mem_domain j]
      (Mf : ℝ) ^ (2 : ℕ) *
        (δj ^ (2 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ))) +
          (Mf : ℝ) * δj ^ (3 : ℕ) /
            (2 * (1 + (Mf : ℝ) * δj) * (3 + 2 * (Mf : ℝ) * δj)) -
          tj1 * pathFollowingObjectiveNorm f y0 (process.y j) (process.mem_domain j) *
            (δj * (1 + (Mf : ℝ) * δj) /
              (1 + (Mf : ℝ) * δj + (Mf : ℝ) ^ (2 : ℕ) * δj ^ (2 : ℕ))))
    pathFollowingKappa τ * (2 * k + 1 : ℝ) * (Mf : ℝ) *
        pathFollowingObjectiveNorm f y0 (process.y k) (process.mem_domain k) ≤
      (Mf : ℝ) ^ (2 : ℕ) * (ψk (y0 : E) - ψk (process.y k)) +
        (Mf : ℝ) ^ (2 : ℕ) * tk *
          inner ℝ (∇ f (y0 : E)) ((y0 : E) - process.y k) +
        terminalCurrentSurfacePackage := by
  let tk := (process.t k : ℝ)
  let ψk := auxiliaryCentralPathObjective f y0 tk
  let terminalCurrentSurfacePackage : ℝ :=
    (Mf : ℝ) ^ (2 : ℕ) * (ψk (process.y k) - ψk (process.y (k + 1))) +
      (Mf : ℝ) ^ (2 : ℕ) * tk *
        inner ℝ (∇ f (y0 : E)) (process.y k - process.y (k + 1))
  have hactual :
      pathFollowingKappa τ * (2 * k + 1 : ℝ) * (Mf : ℝ) *
          pathFollowingObjectiveNorm f y0 (process.y k) (process.mem_domain k) ≤
        (Mf : ℝ) ^ (2 : ℕ) * (f (y0 : E) - f (process.y (k + 1))) := by
    -- Prove the exact objective-gap bound on the compensated fixed-surface owner first.
    exact
      pathFollowingActualGapToNextIterate_ge_oddWeightObjectiveNorm_direct
        (f := f) (Mf := Mf) hτ_nonneg htau y0 process centering N hstage hk hkappa_pos
  -- Rewrite the exact next-iterate gap back to the corrected current-surface package once.
  simpa [tk, ψk, terminalCurrentSurfacePackage] using hactual

/-- Helper for Theorem 5 2 3: the missing bridge in the additive route is an odd-weight upper
bound for the exact denominator `M_f ‖∇ f(y₀)‖*_{y_k}`. -/
private theorem pathFollowingObjectiveGapToNextIterate_ge_oddWeightObjectiveNorm
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (hτ_nonneg : 0 ≤ τ) (htau : τ ≤ 0.23) (y0 : dom)
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ)
    (centering :
      ∀ j : ℕ,
        satisfies_approximate_centering_condition f y0 (process.t j) (process.y j)
          (process.mem_domain j) Mf (pathFollowingCenteringBeta τ))
    (N : ℕ)
    (hstage :
      ∀ j : ℕ, j ≤ N →
        1 / (2 * (Mf : ℝ)) ≤ λ[f; process.y j | process.mem_domain j])
    {k : ℕ} (hk : k < N)
    (hkappa_pos : 0 < pathFollowingKappa τ) :
    pathFollowingKappa τ * (2 * k + 1 : ℝ) * (Mf : ℝ) *
        pathFollowingObjectiveNorm f y0 (process.y k) (process.mem_domain k) ≤
      (Mf : ℝ) ^ (2 : ℕ) * (f (y0 : E) - f (process.y (k + 1))) := by
  let tk := (process.t k : ℝ)
  let ψk := auxiliaryCentralPathObjective f y0 tk
  let terminalCurrentSurfacePackage : ℝ :=
    (Mf : ℝ) ^ (2 : ℕ) * (ψk (process.y k) - ψk (process.y (k + 1))) +
      (Mf : ℝ) ^ (2 : ℕ) * tk *
        inner ℝ (∇ f (y0 : E)) (process.y k - process.y (k + 1))
  have hpackage_lower :
      pathFollowingKappa τ * (2 * k + 1 : ℝ) * (Mf : ℝ) *
          pathFollowingObjectiveNorm f y0 (process.y k) (process.mem_domain k) ≤
        (Mf : ℝ) ^ (2 : ℕ) * (ψk (y0 : E) - ψk (process.y k)) +
          (Mf : ℝ) ^ (2 : ℕ) * tk *
            inner ℝ (∇ f (y0 : E)) ((y0 : E) - process.y k) +
          terminalCurrentSurfacePackage := by
    -- Route correction: use the exact base-tilt-corrected current-surface owner directly.
    simpa [tk, ψk, terminalCurrentSurfacePackage] using
      pathFollowingCurrentSurfaceGapWithBaseTiltPlusTerminal_ge_oddWeightObjectiveNorm
        (f := f) (Mf := Mf) hτ_nonneg htau y0 process centering N hstage hk hkappa_pos
  have hrewrite :
      (Mf : ℝ) ^ (2 : ℕ) * (ψk (y0 : E) - ψk (process.y k)) +
          (Mf : ℝ) ^ (2 : ℕ) * tk *
            inner ℝ (∇ f (y0 : E)) ((y0 : E) - process.y k) +
          terminalCurrentSurfacePackage =
        (Mf : ℝ) ^ (2 : ℕ) * (f (y0 : E) - f (process.y (k + 1))) := by
    -- Rewrite the corrected owner once to the exact next-iterate objective gap.
    simpa [tk, ψk, terminalCurrentSurfacePackage] using
      pathFollowingCurrentSurfaceGapWithBaseTiltPlusTerminal_eq_actualGapToNextIterate
        (f := f) (Mf := Mf) y0 process k
  -- The positive branch is now reduced to the exact current-surface owner and its single rewrite
  -- to the next-iterate objective gap.
  calc
    pathFollowingKappa τ * (2 * k + 1 : ℝ) * (Mf : ℝ) *
        pathFollowingObjectiveNorm f y0 (process.y k) (process.mem_domain k) ≤
      (Mf : ℝ) ^ (2 : ℕ) * (ψk (y0 : E) - ψk (process.y k)) +
        (Mf : ℝ) ^ (2 : ℕ) * tk *
          inner ℝ (∇ f (y0 : E)) ((y0 : E) - process.y k) +
        terminalCurrentSurfacePackage := hpackage_lower
    _ =
      (Mf : ℝ) ^ (2 : ℕ) * (f (y0 : E) - f (process.y (k + 1))) := hrewrite

/-- Helper for Theorem 5 2 3: the missing bridge in the additive route is an odd-weight upper
bound for the exact denominator `M_f ‖∇ f(y₀)‖*_{y_k}`. -/
private theorem pathFollowingObjectiveGap_ge_oddWeightObjectiveNorm
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (hτ_nonneg : 0 ≤ τ) (htau : τ ≤ 0.23) (y0 : dom) (xStar : dom)
    (hmin : IsMinOn f dom (xStar : E))
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ)
    (centering :
      ∀ j : ℕ,
        satisfies_approximate_centering_condition f y0 (process.t j) (process.y j)
          (process.mem_domain j) Mf (pathFollowingCenteringBeta τ))
    (N : ℕ)
    (hstage :
      ∀ j : ℕ, j ≤ N →
        1 / (2 * (Mf : ℝ)) ≤ λ[f; process.y j | process.mem_domain j])
    {k : ℕ} (hk : k < N)
    (hkappa_pos : 0 < pathFollowingKappa τ) :
    pathFollowingKappa τ * (2 * k + 1 : ℝ) * (Mf : ℝ) *
        pathFollowingObjectiveNorm f y0 (process.y k) (process.mem_domain k) ≤
      (Mf : ℝ) ^ (2 : ℕ) * (f (y0 : E) - f (xStar : E)) := by
  have hendpoint_lower :
      pathFollowingKappa τ * (2 * k + 1 : ℝ) * (Mf : ℝ) *
          pathFollowingObjectiveNorm f y0 (process.y k) (process.mem_domain k) ≤
        (Mf : ℝ) ^ (2 : ℕ) * (f (y0 : E) - f (process.y (k + 1))) := by
    -- Route correction: reduce the odd-weight package to the actual gap up to `y_{k+1}` first.
    exact
      pathFollowingObjectiveGapToNextIterate_ge_oddWeightObjectiveNorm
        (f := f) (Mf := Mf) hτ_nonneg htau y0 process centering N hstage hk hkappa_pos
  have hendpoint_le_initial :
      (Mf : ℝ) ^ (2 : ℕ) * (f (y0 : E) - f (process.y (k + 1))) ≤
        (Mf : ℝ) ^ (2 : ℕ) * (f (y0 : E) - f (xStar : E)) := by
    have hMf_sq_nonneg : 0 ≤ (Mf : ℝ) ^ (2 : ℕ) := by
      positivity
    have hmin_endpoint : f (xStar : E) ≤ f (process.y (k + 1)) := by
      -- The minimizer cannot exceed the objective value at the telescoped endpoint.
      exact (isMinOn_iff.mp hmin) _ (process.mem_domain (k + 1))
    have hgap :
        f (y0 : E) - f (process.y (k + 1)) ≤ f (y0 : E) - f (xStar : E) := by
      linarith
    -- Scale the endpoint comparison by the nonnegative factor `M_f^2`.
    exact mul_le_mul_of_nonneg_left hgap hMf_sq_nonneg
  exact le_trans hendpoint_lower hendpoint_le_initial

/-- Helper for Theorem 5 2 3: the missing bridge in the additive route is an odd-weight upper
bound for the exact denominator `M_f ‖∇ f(y₀)‖*_{y_k}`. -/
private theorem pathFollowingObjectiveNorm_odd_control
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (hτ_nonneg : 0 ≤ τ) (htau : τ ≤ 0.23) (y0 : dom) (xStar : dom)
    (hmin : IsMinOn f dom (xStar : E))
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ)
    (centering :
      ∀ j : ℕ,
        satisfies_approximate_centering_condition f y0 (process.t j) (process.y j)
          (process.mem_domain j) Mf (pathFollowingCenteringBeta τ))
    (N : ℕ)
    (hstage :
      ∀ j : ℕ, j ≤ N →
        1 / (2 * (Mf : ℝ)) ≤ λ[f; process.y j | process.mem_domain j])
    {k : ℕ} (hk : k < N) :
    pathFollowingKappa τ * (2 * k + 1 : ℝ) * (Mf : ℝ) *
        pathFollowingObjectiveNorm f y0 (process.y k) (process.mem_domain k) ≤
      (Mf : ℝ) ^ (2 : ℕ) * (f (y0 : E) - f (xStar : E)) := by
  by_cases hkappa_nonpos : pathFollowingKappa τ ≤ 0
  · -- If `κ(τ)` is nonpositive, the target bound is immediate from sign considerations.
    exact
      pathFollowingObjectiveNorm_odd_control_of_kappa_nonpos
        (f := f) (Mf := Mf) y0 xStar hmin process k hkappa_nonpos
  · have hkappa_pos : 0 < pathFollowingKappa τ := lt_of_not_ge hkappa_nonpos
    -- Route correction: delegate the positive branch to the sign-safe odd-control theorem on `f`.
    exact
      pathFollowingObjectiveGap_ge_oddWeightObjectiveNorm
        (f := f) (Mf := Mf) hτ_nonneg htau y0 xStar hmin process centering N hstage hk
        hkappa_pos

/-- Helper for Theorem 5 2 3: once the odd-weight denominator control is available, the exact
additive update yields the one-step lower bound used in the final `N²` telescope. -/
private theorem pathFollowingTimeDecayStep
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (hτ_nonneg : 0 ≤ τ) (htau : τ ≤ 0.23) (y0 : dom) (xStar : dom)
    (hmin : IsMinOn f dom (xStar : E))
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ)
    (centering :
      ∀ j : ℕ,
        satisfies_approximate_centering_condition f y0 (process.t j) (process.y j)
          (process.mem_domain j) Mf (pathFollowingCenteringBeta τ))
    (N : ℕ)
    (hstage :
      ∀ j : ℕ, j ≤ N →
        1 / (2 * (Mf : ℝ)) ≤ λ[f; process.y j | process.mem_domain j])
    (hgamma_pos : 0 < pathFollowingGammaRadius τ)
    (hgap_pos : 0 < f (y0 : E) - f (xStar : E))
    {k : ℕ} (hk : k < N) :
    pathFollowingGammaRadius τ * pathFollowingKappa τ * (2 * k + 1 : ℝ) /
        ((Mf : ℝ) ^ (2 : ℕ) * (f (y0 : E) - f (xStar : E))) ≤
      (process.t k : ℝ) - (process.t (k + 1) : ℝ) := by
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero Mf))
  have hnorm_pos :
      0 < pathFollowingObjectiveNorm f y0 (process.y k) (process.mem_domain k) :=
    process.objectiveNorm_pos k
  have hΔ0_pos :
      0 <
        (Mf : ℝ) ^ (2 : ℕ) * (f (y0 : E) - f (xStar : E)) := by
    positivity
  have hodd_control :=
    pathFollowingObjectiveNorm_odd_control (f := f) (Mf := Mf) hτ_nonneg htau y0 xStar hmin
      process centering N hstage hk
  have hcore :
      pathFollowingKappa τ * (2 * k + 1 : ℝ) /
          ((Mf : ℝ) ^ (2 : ℕ) * (f (y0 : E) - f (xStar : E))) ≤
        1 /
          ((Mf : ℝ) * pathFollowingObjectiveNorm f y0 (process.y k) (process.mem_domain k)) := by
    have hden_pos :
        0 <
          (Mf : ℝ) * pathFollowingObjectiveNorm f y0 (process.y k) (process.mem_domain k) := by
      exact mul_pos hMf_pos hnorm_pos
    have hdiv :
        pathFollowingKappa τ * (2 * k + 1 : ℝ) ≤
          ((Mf : ℝ) ^ (2 : ℕ) * (f (y0 : E) - f (xStar : E))) /
            ((Mf : ℝ) * pathFollowingObjectiveNorm f y0 (process.y k) (process.mem_domain k)) := by
      exact (le_div_iff₀ hden_pos).2 <| by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hodd_control
    exact (div_le_iff₀ hΔ0_pos).2 <| by
      calc
        pathFollowingKappa τ * (2 * k + 1 : ℝ) ≤
            ((Mf : ℝ) ^ (2 : ℕ) * (f (y0 : E) - f (xStar : E))) /
              ((Mf : ℝ) * pathFollowingObjectiveNorm f y0 (process.y k) (process.mem_domain k)) :=
          hdiv
        _ =
            (1 /
                ((Mf : ℝ) * pathFollowingObjectiveNorm f y0 (process.y k)
                  (process.mem_domain k))) *
              ((Mf : ℝ) ^ (2 : ℕ) * (f (y0 : E) - f (xStar : E))) := by
              ring
  have hscaled :=
    mul_le_mul_of_nonneg_left hcore hgamma_pos.le
  -- Rewrite the exact additive step and insert the denominator-control estimate.
  calc
    pathFollowingGammaRadius τ * pathFollowingKappa τ * (2 * k + 1 : ℝ) /
        ((Mf : ℝ) ^ (2 : ℕ) * (f (y0 : E) - f (xStar : E))) =
      pathFollowingGammaRadius τ *
        (pathFollowingKappa τ * (2 * k + 1 : ℝ) /
          ((Mf : ℝ) ^ (2 : ℕ) * (f (y0 : E) - f (xStar : E)))) := by
            ring
    _ ≤
        pathFollowingGammaRadius τ *
          (1 /
            ((Mf : ℝ) * pathFollowingObjectiveNorm f y0 (process.y k)
              (process.mem_domain k))) := hscaled
    _ = pathFollowingGammaRadius τ /
          ((Mf : ℝ) * pathFollowingObjectiveNorm f y0 (process.y k)
            (process.mem_domain k)) := by
          ring
    _ = (process.t k : ℝ) - (process.t (k + 1) : ℝ) := by
          symm
          exact pathFollowingProcess_step_sub_eq_div (f := f) (Mf := Mf) y0 process k

/-- Helper for Theorem 5 2 3: summing the exact additive path decrements telescopes to
`1 - t_N`. -/
private theorem pathFollowingProcess_time_telescope
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (y0 : dom)
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ) (N : ℕ) :
    (Finset.range N).sum (fun k ↦ ((process.t k : ℝ) - (process.t (k + 1) : ℝ))) =
      1 - (process.t N : ℝ) := by
  -- Telescope the finite sum and then rewrite the initial path parameter with `t₀ = 1`.
  calc
    (Finset.range N).sum (fun k ↦ ((process.t k : ℝ) - (process.t (k + 1) : ℝ))) =
        (process.t 0 : ℝ) - (process.t N : ℝ) := by
          simpa using (Finset.sum_range_sub' (fun k ↦ (process.t k : ℝ)) N)
    _ = 1 - (process.t N : ℝ) := by
          simp [process.t_zero]

/-- Helper for Theorem 5 2 3: if the initial gap already vanishes, then the displayed decay bound
is immediate because the denominator collapses to `0` and every path parameter lies in `[0, 1]`. -/
private theorem pathFollowingParameterDecayUpTo_of_initialGap_eq_zero
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (y0 : dom) (xStar : dom)
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ)
    (N : ℕ) (hgap0 : f (y0 : E) - f (xStar : E) = 0) :
    (process.t N : ℝ) ≤
      Real.exp
        (-(pathFollowingGammaRadius τ * pathFollowingKappa τ * (N : ℝ) ^ (2 : ℕ) /
            ((Mf : ℝ) ^ (2 : ℕ) * (f (y0 : E) - f (xStar : E))))) := by
  -- The path parameter is always at most `1`, while the right-hand side becomes `exp 0 = 1`.
  calc
    (process.t N : ℝ) ≤ 1 := (process.t N).2.2
    _ = Real.exp
          (-(pathFollowingGammaRadius τ * pathFollowingKappa τ * (N : ℝ) ^ (2 : ℕ) /
              ((Mf : ℝ) ^ (2 : ℕ) * (f (y0 : E) - f (xStar : E))))) := by
          simp [hgap0]

/-- Helper for Theorem 5 2 3: once the ordinary Newton decrement stays in the Stage-1 regime up
to index `N`, the path parameter should satisfy the displayed exponential decay estimate. -/
private theorem pathFollowingParameterDecayUpTo
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ} [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (hτ_nonneg : 0 ≤ τ) (htau : τ ≤ 0.23) (y0 : dom) (xStar : dom)
    (hmin : IsMinOn f dom (xStar : E))
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ)
    (centering :
      ∀ k : ℕ,
        satisfies_approximate_centering_condition f y0 (process.t k) (process.y k)
          (process.mem_domain k) Mf (pathFollowingCenteringBeta τ))
    (N : ℕ)
    (hstage :
      ∀ k : ℕ, k ≤ N →
        1 / (2 * (Mf : ℝ)) ≤ λ[f; process.y k | process.mem_domain k]) :
    (process.t N : ℝ) ≤
      Real.exp
        (-(pathFollowingGammaRadius τ * pathFollowingKappa τ * (N : ℝ) ^ (2 : ℕ) /
            ((Mf : ℝ) ^ (2 : ℕ) * (f (y0 : E) - f (xStar : E))))) := by
  by_cases hgap0 : f (y0 : E) - f (xStar : E) = 0
  · -- When the initial gap is zero, the displayed denominator vanishes and the bound is trivial.
    exact pathFollowingParameterDecayUpTo_of_initialGap_eq_zero y0 xStar process N hgap0
  · have hgap_nonneg : 0 ≤ f (y0 : E) - f (xStar : E) :=
      pathFollowingInitialGap_nonneg (Mf := Mf) (f := f) y0 xStar hmin
    have hgap_pos : 0 < f (y0 : E) - f (xStar : E) := by
      exact lt_of_le_of_ne hgap_nonneg (by simpa [eq_comm] using hgap0)
    let Δ0 : ℝ := (Mf : ℝ) ^ (2 : ℕ) * (f (y0 : E) - f (xStar : E))
    have hgamma_nonneg : 0 ≤ pathFollowingGammaRadius τ :=
      pathFollowingGammaRadius_nonneg hτ_nonneg htau
    by_cases hgamma0 : pathFollowingGammaRadius τ = 0
    · -- If the path increment vanishes, then the exponential bound reduces to the trivial
      -- estimate `t_N ≤ exp 0 = 1`.
      calc
        (process.t N : ℝ) ≤ 1 := (process.t N).2.2
        _ = Real.exp
              (-(pathFollowingGammaRadius τ * pathFollowingKappa τ * (N : ℝ) ^ (2 : ℕ) / Δ0)) := by
                simp [hgamma0, Δ0]
    · have hgamma_ne : 0 ≠ pathFollowingGammaRadius τ := by
        simpa [eq_comm] using hgamma0
      have hgamma_pos : 0 < pathFollowingGammaRadius τ := lt_of_le_of_ne hgamma_nonneg hgamma_ne
      have hstep_sum :
          ∀ k : ℕ,
            k < N →
              pathFollowingGammaRadius τ * pathFollowingKappa τ * (2 * k + 1 : ℝ) / Δ0 ≤
                (process.t k : ℝ) - (process.t (k + 1) : ℝ) := by
        intro k hk
        -- Route correction: stay on the additive surface `t_k - t_{k+1}` and defer only the
        -- odd-weight denominator control needed for the one-step bound.
        simpa [Δ0] using
          pathFollowingTimeDecayStep (f := f) (Mf := Mf) hτ_nonneg htau y0 xStar hmin process
            centering N hstage hgamma_pos hgap_pos hk
      have hsum_le :
          (Finset.range N).sum
              (fun k ↦
                pathFollowingGammaRadius τ * pathFollowingKappa τ * (2 * k + 1 : ℝ) / Δ0) ≤
            (Finset.range N).sum
              (fun k ↦ ((process.t k : ℝ) - (process.t (k + 1) : ℝ))) := by
        refine Finset.sum_le_sum ?_
        intro k hk
        exact hstep_sum k (Finset.mem_range.mp hk)
      have hsum_odd :
          (Finset.range N).sum
              (fun k ↦
                pathFollowingGammaRadius τ * pathFollowingKappa τ * (2 * k + 1 : ℝ) / Δ0) =
            (pathFollowingGammaRadius τ * pathFollowingKappa τ / Δ0) *
              (Finset.range N).sum (fun k ↦ ((2 * k + 1 : ℕ) : ℝ)) := by
        -- Pull the constant factor outside the odd sum before using `sumOdd_range_eq_sq`.
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
          (Finset.mul_sum (s := Finset.range N)
            (f := fun k ↦ ((2 * k + 1 : ℕ) : ℝ))
            (pathFollowingGammaRadius τ * pathFollowingKappa τ / Δ0)).symm
      have hsum_left :
          (Finset.range N).sum
              (fun k ↦
                pathFollowingGammaRadius τ * pathFollowingKappa τ * (2 * k + 1 : ℝ) / Δ0) =
            pathFollowingGammaRadius τ * pathFollowingKappa τ * (N : ℝ) ^ (2 : ℕ) / Δ0 := by
        calc
          (Finset.range N).sum
              (fun k ↦
                pathFollowingGammaRadius τ * pathFollowingKappa τ * (2 * k + 1 : ℝ) / Δ0) =
              (pathFollowingGammaRadius τ * pathFollowingKappa τ / Δ0) *
                (Finset.range N).sum (fun k ↦ ((2 * k + 1 : ℕ) : ℝ)) := hsum_odd
          _ = (pathFollowingGammaRadius τ * pathFollowingKappa τ / Δ0) * (N : ℝ) ^ (2 : ℕ) := by
                rw [sumOdd_range_eq_sq]
          _ = pathFollowingGammaRadius τ * pathFollowingKappa τ * (N : ℝ) ^ (2 : ℕ) / Δ0 := by
                ring
      have htel :
          (Finset.range N).sum
              (fun k ↦ ((process.t k : ℝ) - (process.t (k + 1) : ℝ))) =
            1 - (process.t N : ℝ) :=
        pathFollowingProcess_time_telescope (f := f) (Mf := Mf) y0 process N
      have hdrop :
          pathFollowingGammaRadius τ * pathFollowingKappa τ * (N : ℝ) ^ (2 : ℕ) / Δ0 ≤
            1 - (process.t N : ℝ) := by
        calc
          pathFollowingGammaRadius τ * pathFollowingKappa τ * (N : ℝ) ^ (2 : ℕ) / Δ0 =
              (Finset.range N).sum
                (fun k ↦
                  pathFollowingGammaRadius τ * pathFollowingKappa τ * (2 * k + 1 : ℝ) / Δ0) := by
                    rw [hsum_left]
          _ ≤
              (Finset.range N).sum
                (fun k ↦ ((process.t k : ℝ) - (process.t (k + 1) : ℝ))) := hsum_le
          _ = 1 - (process.t N : ℝ) := htel
      have htn_le :
          (process.t N : ℝ) ≤
            1 -
              pathFollowingGammaRadius τ * pathFollowingKappa τ * (N : ℝ) ^ (2 : ℕ) / Δ0 := by
        linarith
      calc
        (process.t N : ℝ) ≤
            1 -
              pathFollowingGammaRadius τ * pathFollowingKappa τ * (N : ℝ) ^ (2 : ℕ) / Δ0 :=
          htn_le
        _ ≤ Real.exp
              (-(pathFollowingGammaRadius τ * pathFollowingKappa τ * (N : ℝ) ^ (2 : ℕ) / Δ0)) := by
                simpa [sub_eq_add_neg] using
                  Real.one_sub_le_exp_neg
                    (pathFollowingGammaRadius τ * pathFollowingKappa τ * (N : ℝ) ^ (2 : ℕ) / Δ0)

-- Proof sketch: use `process.t_zero` and `process.y_zero` to obtain vanishing of the
-- shifted-gradient dual local norm at the initial pair `(1, y₀)`, then iterate
-- `pathFollowingUpdate_preserves_approximate_centering_condition` to propagate the uniform bound
-- `λ_k ≤ β(τ) / M_f`. For the decay of `t_N`, combine the one-step decrease estimate for
-- `f(y_k) - f(y_{k+1})` with the lower bound `1 / (2 M_f) ≤ λ_f(y_k)` for `k ≤ N`, and sum the
-- resulting reciprocal estimate using the scalar minimum `(N + 1)^2`.
/-- Theorem 5 2 3: for the path-following process `(t_k, y_k)` generated by `𝒫_γ` with
`γ = τ - β(τ)` and `0 ≤ τ ≤ 0.23`, the shifted Newton decrement remains bounded by `β(τ) / M_f` at
every iterate. If, in addition, the ordinary Newton decrement satisfies
`1 / (2 M_f) ≤ λ_f(y_k)` for all `k = 0, ..., N`, then the path parameter obeys the exponential
bound `t_N ≤ exp (-(γ κ(τ) N^2) / Δ_f(x₀))`, written here using a chosen feasible minimizer
`xStar : dom` as `Δ_f(x₀) = M_f^2 * (f(y₀) - f(xStar))`. -/
theorem selfConcordantPathFollowing_parameter_exponential_decay
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ} [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (hτ_nonneg : 0 ≤ τ) (htau : τ ≤ 0.23) (y0 : dom) (xStar : dom)
    (hmin : IsMinOn f dom (xStar : E))
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ)
    :
    (∀ k : ℕ,
      satisfies_approximate_centering_condition f y0 (process.t k) (process.y k)
        (process.mem_domain k) Mf (pathFollowingCenteringBeta τ)) ∧
      ∀ N : ℕ,
        (∀ k : ℕ, k ≤ N →
          1 / (2 * (Mf : ℝ)) ≤ λ[f; process.y k | process.mem_domain k]) →
        (process.t N : ℝ) ≤
          Real.exp
            (-(pathFollowingGammaRadius τ * pathFollowingKappa τ * (N : ℝ) ^ (2 : ℕ) /
                ((Mf : ℝ) ^ (2 : ℕ) * (f (y0 : E) - f (xStar : E))))) := by
  let centering :=
    pathFollowingCenteringInvariant hτ_nonneg htau y0 process
  constructor
  · -- The first conjunct is exactly the centering invariant skeleton recorded above.
    exact centering
  · intro N hstage
    -- The second conjunct is isolated in the decay helper to keep the theorem surface stable.
    exact pathFollowingParameterDecayUpTo hτ_nonneg htau y0 xStar hmin process centering N hstage

end
