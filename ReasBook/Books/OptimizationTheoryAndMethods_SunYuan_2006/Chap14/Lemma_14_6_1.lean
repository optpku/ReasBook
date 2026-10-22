/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Basic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Definition_14_1_extra_4
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.EuclideanSubgradient
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Exercise_14_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Lemma_14_1_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Lemma_14_1_4
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Lemma_14_1_6
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Definition_14_6_extra_1

noncomputable section

section

variable {n m : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "ValuePoint" => EuclideanSpace ℝ (Fin m)
local notation "JacobianTranspose" => Matrix (Fin n) (Fin m) ℝ

-- Domain-style sampling:
-- * primary domain: Section 14.6 composite first-order models;
-- * inspected canonical surfaces: `clarkeDirectionalDeriv`, `clarkeDifferential`,
--   `CompositeNonsmoothOptimizationProblem`,
--   the chapter's convex subdifferential owner `∂`, and the Euclidean bridge
--   `Chapter14.IsSubgradientAt`;
-- * source-facing owners kept here: the Jacobian-transpose field, the directional-value set,
--   `compositeNonsmoothDF`, the owner-specialized model `problem.firstOrderModel`, and the
--   notation `DF[problem](x, d)`;
--   stationary-condition equivalence of Lemma 14.6.1;
-- * bridge/view: the identification of the Clarke generalized directional derivative of `h ∘ f`
--   with the source quantity `DF(x, d)`.

/-- The source matrix field `A(x) = ∇ f(x)ᵀ`, written as the transpose of the matrix of
`fderiv ℝ f x` in the standard Euclidean bases. -/
def compositeNonsmoothJacobianTranspose
    (f : Point → ValuePoint) (x : Point) : JacobianTranspose :=
  (LinearMap.toMatrix
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
      (fderiv ℝ f x).toLinearMap).transpose

/-- Unfolding `compositeNonsmoothJacobianTranspose f x` gives the source matrix
`A(x) = ∇ f(x)ᵀ`. -/
theorem compositeNonsmoothJacobianTranspose_eq
    (f : Point → ValuePoint) (x : Point) :
    compositeNonsmoothJacobianTranspose f x =
      (LinearMap.toMatrix
          (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
          (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
          (fderiv ℝ f x).toLinearMap).transpose :=
  rfl

/-- The source value set `{dᵀ A(x) λ | λ ∈ ∂ h(f x)}` from `(14.6.6)`, with the codomain
subgradient condition expressed through the chapter's Euclidean bridge
`Chapter14.IsSubgradientAt`. -/
def compositeNonsmoothDirectionalValueSet
    (h : ValuePoint → ℝ) (f : Point → ValuePoint) (x d : Point) : Set ℝ :=
  {r : ℝ |
    ∃ lam : ValuePoint,
      Chapter14.IsSubgradientAt h (f x) lam ∧
        inner ℝ d
          (WithLp.toLp 2 ((compositeNonsmoothJacobianTranspose f x).mulVec lam.ofLp)) = r}

/-- Membership in `compositeNonsmoothDirectionalValueSet h f x d` is exactly the existence of a
codomain Euclidean subgradient `lam ∈ ∂ h(f x)` producing the value `r = dᵀ A(x) λ`. -/
@[simp] theorem mem_compositeNonsmoothDirectionalValueSet_iff
    (h : ValuePoint → ℝ) (f : Point → ValuePoint) (x d : Point) (r : ℝ) :
    r ∈ compositeNonsmoothDirectionalValueSet h f x d ↔
      ∃ lam : ValuePoint,
        Chapter14.IsSubgradientAt h (f x) lam ∧
          inner ℝ d
            (WithLp.toLp 2 ((compositeNonsmoothJacobianTranspose f x).mulVec lam.ofLp)) = r :=
  Iff.rfl

/-- Helper for Chapter14 Lemma 14.6.1: the source matrix quantity `dᵀ A(x) λ` is the
subgradient functional `toDual λ` evaluated on the Fréchet derivative `(fderiv ℝ f x) d`. -/
theorem compositeNonsmoothDirectionalValue_eq_subgradientEval_fderiv
    (f : Point → ValuePoint) (x d : Point) (lam : ValuePoint) :
    inner ℝ d
      (WithLp.toLp 2 ((compositeNonsmoothJacobianTranspose f x).mulVec lam.ofLp)) =
        (InnerProductSpace.toDual ℝ ValuePoint lam) ((fderiv ℝ f x) d) := by
  let A : Matrix (Fin m) (Fin n) ℝ :=
    LinearMap.toMatrix
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
      (fderiv ℝ f x).toLinearMap
  have hA_toEuclidean :
      Matrix.toEuclideanLin A = (fderiv ℝ f x).toLinearMap := by
    -- Recover the Fréchet derivative from its orthonormal-basis matrix.
    simpa [A, Matrix.toEuclideanLin_eq_toLin_orthonormal] using
      (Matrix.toLin_toMatrix
        (v₁ := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis)
        (v₂ := (EuclideanSpace.basisFun (Fin m) ℝ).toBasis)
        ((fderiv ℝ f x).toLinearMap))
  have hAdj :
      LinearMap.adjoint (Matrix.toEuclideanLin A) = Matrix.toEuclideanLin A.transpose := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.toEuclideanLin_conjTranspose_eq_adjoint (A := A)).symm
  calc
    inner ℝ d
        (WithLp.toLp 2 ((compositeNonsmoothJacobianTranspose f x).mulVec lam.ofLp))
      = inner ℝ d (Matrix.toEuclideanLin A.transpose lam) := by
          -- Unfold the source Jacobian-transpose owner as the Euclidean matrix action.
          simp [A, compositeNonsmoothJacobianTranspose_eq, Matrix.toEuclideanLin_apply]
    _ = inner ℝ (LinearMap.adjoint (Matrix.toEuclideanLin A) lam) d := by
          -- Commute the real inner product so the matrix adjoint theorem applies.
          simp [hAdj, real_inner_comm]
    _ = inner ℝ lam (Matrix.toEuclideanLin A d) := by
          -- Move the transpose action across the Euclidean inner product.
          simpa using
            (LinearMap.adjoint_inner_left (Matrix.toEuclideanLin A) d lam)
    _ = inner ℝ lam ((fderiv ℝ f x) d) := by
          -- Replace the Euclidean matrix action by the Fréchet derivative itself.
          simp [hA_toEuclidean]
    _ = (InnerProductSpace.toDual ℝ ValuePoint lam) ((fderiv ℝ f x) d) := by
          simp

/-- Helper for Chapter14 Lemma 14.6.1: membership in the source directional-value set is exactly
membership in the image of the convex subdifferential under evaluation on `(fderiv ℝ f x) d`. -/
theorem mem_compositeNonsmoothDirectionalValueSet_iff_exists_mem_subdifferential_eval_fderiv
    (h : ValuePoint → ℝ) (f : Point → ValuePoint) (x d : Point) (r : ℝ) :
    r ∈ compositeNonsmoothDirectionalValueSet h f x d ↔
      ∃ ξ : StrongDual ℝ ValuePoint,
        ξ ∈ subdifferential h (f x) ∧ ξ ((fderiv ℝ f x) d) = r := by
  constructor
  · intro hr
    rcases (mem_compositeNonsmoothDirectionalValueSet_iff h f x d r).mp hr with
      ⟨lam, hlam, hval⟩
    refine ⟨InnerProductSpace.toDual ℝ ValuePoint lam, ?_, ?_⟩
    · -- Rewrite the Euclidean subgradient witness as subdifferential membership.
      simpa [Chapter14.isSubgradientAt_iff_mem_subdifferential] using hlam
    · -- Replace the source matrix pairing by the canonical dual evaluation.
      simpa [compositeNonsmoothDirectionalValue_eq_subgradientEval_fderiv] using hval
  · rintro ⟨ξ, hξ, hval⟩
    refine (mem_compositeNonsmoothDirectionalValueSet_iff h f x d r).mpr ?_
    refine ⟨(InnerProductSpace.toDual ℝ ValuePoint).symm ξ, ?_, ?_⟩
    · -- Recover the Euclidean subgradient vector from the Riesz-represented functional.
      simpa [Chapter14.isSubgradientAt_iff_mem_subdifferential] using hξ
    · -- The canonical evaluation identity specializes back to the source matrix formula.
      simpa [compositeNonsmoothDirectionalValue_eq_subgradientEval_fderiv] using hval

/-- Helper for Chapter14 Lemma 14.6.1: the directional-value set is the image of the convex
subdifferential under the support-function evaluation `ξ ↦ ξ ((fderiv ℝ f x) d)`. -/
theorem compositeNonsmoothDirectionalValueSet_eq_image_subdifferentialEval_fderiv
    (h : ValuePoint → ℝ) (f : Point → ValuePoint) (x d : Point) :
    compositeNonsmoothDirectionalValueSet h f x d =
      (fun ξ : StrongDual ℝ ValuePoint ↦ ξ ((fderiv ℝ f x) d)) ''
        subdifferential h (f x) := by
  ext r
  constructor
  · intro hr
    rcases
      (mem_compositeNonsmoothDirectionalValueSet_iff_exists_mem_subdifferential_eval_fderiv
        h f x d r).mp hr with ⟨ξ, hξ, hξr⟩
    exact ⟨ξ, hξ, hξr⟩
  · rintro ⟨ξ, hξ, rfl⟩
    exact
      (mem_compositeNonsmoothDirectionalValueSet_iff_exists_mem_subdifferential_eval_fderiv
        h f x d (ξ ((fderiv ℝ f x) d))).mpr ⟨ξ, hξ, rfl⟩

/-- Chapter 14's first-order model quantity
`DF(x, d) = sup_(λ ∈ ∂ h(f x)) dᵀ A(x) λ` from `(14.6.6)`, where
`A(x) = compositeNonsmoothJacobianTranspose f x = ∇ f(x)ᵀ`, represented using the Euclidean
inner product. -/
def compositeNonsmoothDF
    (h : ValuePoint → ℝ) (f : Point → ValuePoint) (x d : Point) : ℝ :=
  sSup (compositeNonsmoothDirectionalValueSet h f x d)

/-- Unfolding `compositeNonsmoothDF h f x d` gives the Chapter 14 supremum formula for
`DF(x, d)`. -/
theorem compositeNonsmoothDF_eq_sSup
    (h : ValuePoint → ℝ) (f : Point → ValuePoint) (x d : Point) :
    compositeNonsmoothDF h f x d =
      sSup (compositeNonsmoothDirectionalValueSet h f x d) :=
  rfl

/-- Helper for Chapter14 Lemma 14.6.1: after rewriting the source directional-value set through
the convex subdifferential, `DF(x, d)` is the support supremum of the image of
`subdifferential h (f x)` under evaluation on `(fderiv ℝ f x) d`. -/
theorem compositeNonsmoothDF_eq_sSup_image_subdifferentialEval_fderiv
    (h : ValuePoint → ℝ) (f : Point → ValuePoint) (x d : Point) :
    compositeNonsmoothDF h f x d =
      sSup
        ((fun ξ : StrongDual ℝ ValuePoint ↦ ξ ((fderiv ℝ f x) d)) ''
          subdifferential h (f x)) := by
  -- Normalize the source supremum to the subdifferential image that the support argument uses.
  rw [compositeNonsmoothDF_eq_sSup]
  rw [compositeNonsmoothDirectionalValueSet_eq_image_subdifferentialEval_fderiv]

namespace CompositeNonsmoothOptimizationProblem

/-- The Section 14.6 first-order model `DF(x, d)` attached to a composite nonsmooth problem,
with Lean surface notation `DF[problem](x, d)`. -/
def firstOrderModel (problem : CompositeNonsmoothOptimizationProblem n m) (x d : Point) : ℝ :=
  compositeNonsmoothDF problem.outerFunction problem.smoothMap x d

/-- Unfolding `problem.firstOrderModel x d` recovers the raw Section 14.6 owner
`compositeNonsmoothDF problem.outerFunction problem.smoothMap x d`. -/
@[simp] theorem firstOrderModel_eq_compositeNonsmoothDF
    (problem : CompositeNonsmoothOptimizationProblem n m) (x d : Point) :
    problem.firstOrderModel x d =
      compositeNonsmoothDF problem.outerFunction problem.smoothMap x d :=
  rfl

end CompositeNonsmoothOptimizationProblem

/- The source notation `DF(x, d)` for a fixed composite problem is written in Lean as
`DF[problem](x, d)`. -/
scoped[CompositeNonsmooth] notation:100 "DF[" problem "](" x ", " d ")" =>
  CompositeNonsmoothOptimizationProblem.firstOrderModel problem x d

open scoped CompositeNonsmooth

/-- Helper for Chapter14 Lemma 14.6.1: a convex outer function on the whole Euclidean codomain
is locally Lipschitz at every evaluation point in the project-local sense. -/
theorem convexOn_univ_locallyLipschitzAt
    (h : ValuePoint → ℝ) (y : ValuePoint)
    (h_convex : ConvexOn ℝ Set.univ h) :
    LocallyLipschitzAt h y := by
  -- Use mathlib's finite-dimensional convex regularity and shrink the neighborhood to a closed
  -- ball, matching the project's `LocallyLipschitzAt` owner.
  rcases (ConvexOn.locallyLipschitz h_convex) y with ⟨K, s, hs_mem, hK⟩
  rcases Metric.mem_nhds_iff.mp hs_mem with ⟨ε, hε_pos, hε_sub⟩
  exact locallyLipschitzAt_of_closedBall (K := K) <| by
    refine ⟨ε / 2, by linarith, ?_⟩
    exact hK.mono fun z hz ↦ hε_sub ((Metric.closedBall_subset_ball (by linarith)) hz)

/-- Helper for Chapter14 Lemma 14.6.1: the smooth-inner / convex-outer composite `h ∘ f` is
locally Lipschitz at `x`, which is the finiteness bridge needed to pass between the real and
`EReal` Clarke directional derivatives. -/
theorem composite_locallyLipschitzAt
    (h : ValuePoint → ℝ) (f : Point → ValuePoint) (x : Point)
    (h_contDiff : ContDiff ℝ 1 f)
    (h_convex : ConvexOn ℝ Set.univ h) :
    LocallyLipschitzAt (h ∘ f) x := by
  -- Control each scalar component of the smooth inner map by `C¹` local Lipschitz regularity.
  refine locallyLipschitzAt_comp_of_components h f x ?_ ?_
  · intro i
    have h_component : ContDiff ℝ 1 (fun y : Point ↦ f y i) := by
      exact ((contDiff_piLp (p := (2 : ENNReal))).1 h_contDiff) i
    exact h_component.contDiffAt.locallyLipschitzAt
  · -- The convex outer function is locally Lipschitz on the whole codomain.
    exact convexOn_univ_locallyLipschitzAt h (f x) h_convex

/-- Helper for Chapter14 Lemma 14.6.1: composing the smooth inner map `f` with a fixed dual
functional `ξ` gives the scalar derivative `ξ.comp (fderiv ℝ f x)` at `x`. -/
theorem hasFDerivAt_dual_comp
    (f : Point → ValuePoint) (x : Point) (ξ : StrongDual ℝ ValuePoint)
    (h_contDiff : ContDiff ℝ 1 f) :
    HasFDerivAt (fun y : Point ↦ ξ (f y)) (ξ.comp (fderiv ℝ f x)) x := by
  -- Normalize the scalar map to the canonical composition `(fun z ↦ ξ z) ∘ f`.
  change HasFDerivAt ((fun z : ValuePoint ↦ ξ z) ∘ f) (ξ.comp (fderiv ℝ f x)) x
  -- Differentiate the outer continuous linear functional after the inner `C¹` map.
  exact (ContinuousLinearMap.hasFDerivAt ξ).comp x
    ((h_contDiff.contDiffAt.differentiableAt (by norm_num)).hasFDerivAt)

/-- Helper for Chapter14 Lemma 14.6.1: the scalar pushforward `y ↦ ξ (f y)` is smooth, so its
real-valued Clarke directional derivative is exactly evaluation of `ξ` on the Fréchet
derivative of `f` at `x`. -/
theorem clarkeDirectionalDerivReal_dual_comp_eq_eval_fderiv
    (f : Point → ValuePoint) (x d : Point) (ξ : StrongDual ℝ ValuePoint)
    (h_contDiff : ContDiff ℝ 1 f) :
    clarkeDirectionalDerivReal (fun y : Point ↦ ξ (f y)) x d =
      ξ ((fderiv ℝ f x) d) := by
  have h_scalar_contDiff : ContDiff ℝ 1 (fun y : Point ↦ ξ (f y)) := by
    -- Normalize to the canonical composition before applying the `ContDiff` chain rule.
    change ContDiff ℝ 1 ((fun z : ValuePoint ↦ ξ z) ∘ f)
    exact ξ.contDiff.comp h_contDiff
  have h_scalar_local : LocallyLipschitzAt (fun y : Point ↦ ξ (f y)) x :=
    h_scalar_contDiff.contDiffAt.locallyLipschitzAt
  have h_fderiv : fderiv ℝ (fun y : Point ↦ ξ (f y)) x = ξ.comp (fderiv ℝ f x) := by
    -- Use the explicit scalar derivative adapter to pin down the singleton Clarke differential.
    simpa using (hasFDerivAt_dual_comp f x ξ h_contDiff).fderiv
  have h_singleton :
      ((fun η : StrongDual ℝ Point ↦ η d) ''
          clarkeDifferential (fun y : Point ↦ ξ (f y)) x) =
        ({ξ ((fderiv ℝ f x) d)} : Set ℝ) := by
    -- Exercise 14.3 collapses the Clarke differential of the smooth scalar map to one point.
    rw [clarkeDifferential_eq_singleton_fderiv_of_contDiff (fun y : Point ↦ ξ (f y)) x
      h_scalar_contDiff]
    ext r
    constructor
    · rintro ⟨η, hη, rfl⟩
      -- The image of a singleton differential is the singleton support value.
      rcases Set.mem_singleton_iff.mp hη with rfl
      simp [h_fderiv]
    · intro hr
      -- Conversely, the support value is realized by the unique Clarke differential element.
      rcases Set.mem_singleton_iff.mp hr with rfl
      refine ⟨fderiv ℝ (fun y : Point ↦ ξ (f y)) x, ?_, ?_⟩
      · simp
      · simp [h_fderiv]
  have h_mem :
      clarkeDirectionalDerivReal (fun y : Point ↦ ξ (f y)) x d ∈
        ({ξ ((fderiv ℝ f x) d)} : Set ℝ) := by
    -- Lemma 14.1.3 identifies the Clarke directional derivative with the maximal support value.
    simpa [h_singleton] using
      (clarkeDirectionalDeriv_isGreatest_image_clarkeDifferential_of_locallyLipschitzAt
        (fun y : Point ↦ ξ (f y)) x d h_scalar_local).1
  -- Read the unique point of the singleton support set as the desired scalar chain rule.
  exact Set.mem_singleton_iff.mp h_mem

/-- Helper for Chapter14 Lemma 14.6.1: subtracting two real-valued locally Lipschitz maps at the
same point preserves the project-local `LocallyLipschitzAt` owner. -/
theorem LocallyLipschitzAt.sub
    {u v : Point → ℝ} {x : Point}
    (hu : LocallyLipschitzAt u x) (hv : LocallyLipschitzAt v x) :
    LocallyLipschitzAt (fun y ↦ u y - v y) x := by
  rcases (locallyLipschitzAt_iff.mp hu) with ⟨εu, hεu, Ku, hKu⟩
  rcases (locallyLipschitzAt_iff.mp hv) with ⟨εv, hεv, Kv, hKv⟩
  refine locallyLipschitzAt_of_closedBall (K := Ku + Kv) ?_
  refine ⟨min εu εv, lt_min hεu hεv, ?_⟩
  refine LipschitzOnWith.of_le_add_mul (Ku + Kv) ?_
  intro y hy z hz
  have hyu : y ∈ Metric.closedBall x εu :=
    Metric.closedBall_subset_closedBall (min_le_left _ _) hy
  have hzu : z ∈ Metric.closedBall x εu :=
    Metric.closedBall_subset_closedBall (min_le_left _ _) hz
  have hyv : y ∈ Metric.closedBall x εv :=
    Metric.closedBall_subset_closedBall (min_le_right _ _) hy
  have hzv : z ∈ Metric.closedBall x εv :=
    Metric.closedBall_subset_closedBall (min_le_right _ _) hz
  have hu_le : u y ≤ u z + Ku * dist y z :=
    hKu.le_add_mul hyu hzu
  have hv_le : v z ≤ v y + Kv * dist y z := by
    simpa [dist_comm] using hKv.le_add_mul hzv hyv
  have hv_neg : -v y ≤ -v z + Kv * dist y z := by
    linarith
  calc
    u y - v y = u y + (-v y) := by ring
    _ ≤ (u z + Ku * dist y z) + (-v z + Kv * dist y z) := by
          gcongr
    _ = u z - v z + (Ku + Kv) * dist y z := by
          ring

/-- Helper for Chapter14 Lemma 14.6.1: every pushed-forward outer subgradient value is bounded
above by the Clarke directional derivative of the composite objective in the same direction. -/
theorem subdifferential_pushforward_value_le_clarkeDirectionalDerivReal_comp
    (h : ValuePoint → ℝ) (f : Point → ValuePoint) (x d : Point)
    (ξ : StrongDual ℝ ValuePoint)
    (h_contDiff : ContDiff ℝ 1 f)
    (h_convex : ConvexOn ℝ Set.univ h)
    (hξ : ξ ∈ subdifferential h (f x)) :
    ξ ((fderiv ℝ f x) d) ≤ clarkeDirectionalDerivReal (h ∘ f) x d := by
  let correction : Point → ℝ := fun y ↦ -ξ (f y)
  let minorant : Point → ℝ := fun y ↦ h (f y) + correction y
  have h_local_comp : LocallyLipschitzAt (h ∘ f) x :=
    composite_locallyLipschitzAt h f x h_contDiff h_convex
  have h_scalar_contDiff : ContDiff ℝ 1 (fun y : Point ↦ ξ (f y)) := by
    -- The scalar evaluation route stays smooth because a continuous linear functional is `C¹`.
    change ContDiff ℝ 1 ((fun z : ValuePoint ↦ ξ z) ∘ f)
    exact ξ.contDiff.comp h_contDiff
  have h_scalar_local : LocallyLipschitzAt (fun y : Point ↦ ξ (f y)) x :=
    h_scalar_contDiff.contDiffAt.locallyLipschitzAt
  have h_correction_local : LocallyLipschitzAt correction x := by
    -- Negating the scalar correction preserves the local Lipschitz control.
    simpa [correction] using h_scalar_local.neg
  have h_minorant_local : LocallyLipschitzAt minorant x := by
    -- The source minorant `h ∘ f - ξ ∘ f` is the locally Lipschitz object used for stationarity.
    simpa [minorant, correction] using h_local_comp.add h_correction_local
  have h_minorant_min : IsMinOn minorant Set.univ x := by
    -- The subgradient inequality makes `x` a global minimizer of the source minorant.
    rw [isMinOn_univ_iff]
    intro z
    have h_subgrad := (mem_subdifferential_iff h (f x) ξ).mp hξ (f z)
    dsimp [minorant, correction]
    have h_map_sub : ξ (f z - f x) = ξ (f z) - ξ (f x) := by
      simp
    rw [h_map_sub] at h_subgrad
    linarith
  have h_zero_mem_minorant : (0 : StrongDual ℝ Point) ∈ clarkeDifferential minorant x := by
    -- A local minimizer of the locally Lipschitz minorant is Clarke stationary.
    exact
      (isClarkeStationaryPoint_iff_zero_mem_clarkeDifferential).mp <|
        (h_minorant_min.isLocalMin (by simp)).isClarkeStationaryPoint h_minorant_local
  have h_minorant_nonneg :
      0 ≤ clarkeDirectionalDerivReal minorant x d := by
    -- The zero generalized gradient forces every directional support value of the minorant
    -- to be nonnegative.
    simpa using
      (mem_clarkeDifferential_real_iff_of_locallyLipschitzAt
        minorant x h_minorant_local (0 : StrongDual ℝ Point)).1 h_zero_mem_minorant d
  have h_minorant_le :
      clarkeDirectionalDerivReal minorant x d ≤
        clarkeDirectionalDerivReal (h ∘ f) x d +
          clarkeDirectionalDerivReal correction x d := by
    -- Compare the minorant support value with the sum of the composite term and its correction.
    simpa [minorant] using
      clarkeDirectionalDerivReal_add_le (h ∘ f) correction x d h_local_comp h_correction_local
  have h_correction_eval :
      clarkeDirectionalDerivReal correction x d = -ξ ((fderiv ℝ f x) d) := by
    -- The smooth scalar correction differentiates to the pushed-forward linear form with a sign.
    simpa [correction] using
      clarkeDirectionalDerivReal_dual_comp_eq_eval_fderiv f x d (-ξ) h_contDiff
  have h_support_nonneg :
      0 ≤ clarkeDirectionalDerivReal (h ∘ f) x d +
        clarkeDirectionalDerivReal correction x d :=
    le_trans h_minorant_nonneg h_minorant_le
  rw [h_correction_eval] at h_support_nonneg
  linarith

/-- Helper for Chapter14 Lemma 14.6.1: every outer subgradient `ξ ∈ ∂ h(f x)` pushes forward
through the Fréchet derivative of `f` to a Clarke generalized gradient of the composite
objective `h ∘ f` at `x`. -/
theorem pushforward_subgradient_mem_clarkeDifferential_comp
    (h : ValuePoint → ℝ) (f : Point → ValuePoint) (x : Point)
    (ξ : StrongDual ℝ ValuePoint)
    (h_contDiff : ContDiff ℝ 1 f)
    (h_convex : ConvexOn ℝ Set.univ h)
    (hξ : ξ ∈ subdifferential h (f x)) :
    ξ.comp (fderiv ℝ f x) ∈ clarkeDifferential (h ∘ f) x := by
  have h_local_comp : LocallyLipschitzAt (h ∘ f) x :=
    composite_locallyLipschitzAt h f x h_contDiff h_convex
  -- Repackage the pointwise support inequality as Clarke-differential membership.
  refine (mem_clarkeDifferential_real_iff_of_locallyLipschitzAt
    (h ∘ f) x h_local_comp (ξ.comp (fderiv ℝ f x))).2 ?_
  intro d
  simpa using
    subdifferential_pushforward_value_le_clarkeDirectionalDerivReal_comp
      h f x d ξ h_contDiff h_convex hξ

/-- Helper for Chapter14 Lemma 14.6.1: differentiating the `i`-th component of the smooth inner
map `f` is the same as evaluating `fderiv ℝ f x` at direction `d` and then reading the
`i`-th coordinate. -/
theorem fderiv_component_apply_eq
    (f : Point → ValuePoint) (x d : Point) (i : Fin m)
    (h_contDiff : ContDiff ℝ 1 f) :
    (fderiv ℝ (fun y : Point ↦ f y i) x) d = (fderiv ℝ f x d) i := by
  let coord : StrongDual ℝ ValuePoint :=
    InnerProductSpace.toDual ℝ ValuePoint (EuclideanSpace.single i (1 : ℝ))
  have h_coord_apply (v : ValuePoint) : coord v = v i := by
    simp [coord, EuclideanSpace.inner_single_left]
  have h_coord_fun : (fun y : Point ↦ coord (f y)) = fun y : Point ↦ f y i := by
    funext y
    exact h_coord_apply (f y)
  have h_coord_fderiv :
      fderiv ℝ (fun y : Point ↦ coord (f y)) x = coord.comp (fderiv ℝ f x) := by
    -- Differentiate the `i`-th coordinate functional after the smooth inner map.
    simpa using (hasFDerivAt_dual_comp f x coord h_contDiff).fderiv
  -- Evaluate the differentiated coordinate functional at `d`.
  rw [← h_coord_fun, h_coord_fderiv]
  simpa using h_coord_apply ((fderiv ℝ f x) d)

/-- Helper for Chapter14 Lemma 14.6.1: every chain-rule generator already evaluates to a value
bounded above by the source support quantity `DF(x, d)`. -/
theorem chainRuleGenerator_eval_le_compositeNonsmoothDF
    (h : ValuePoint → ℝ) (f : Point → ValuePoint) (x d : Point)
    (h_contDiff : ContDiff ℝ 1 f)
    (h_convex : ConvexOn ℝ Set.univ h)
    {η : WeakDual ℝ Point}
    (hη : η ∈ chainRuleGeneratorSet h f x) :
    η d ≤ compositeNonsmoothDF h f x d := by
  rcases hη with ⟨⟨ξ, ζ⟩, hpair, rfl⟩
  rcases hpair with ⟨hξ_clarke, hζ_mem⟩
  have h_outer_local : LocallyLipschitzAt h (f x) :=
    convexOn_univ_locallyLipschitzAt h (f x) h_convex
  have hξ_sub : ξ ∈ subdifferential h (f x) := by
    -- Under convexity, the outer Clarke differential is exactly the convex subdifferential.
    simpa [clarkeDifferential_eq_subdifferential_of_convexOn_of_locallyLipschitzAt
      h (f x) h_convex h_outer_local] using hξ_clarke
  let S : Set ℝ :=
    ((fun ξ : StrongDual ℝ ValuePoint ↦ ξ ((fderiv ℝ f x) d)) '' subdifferential h (f x))
  have hS_bdd : BddAbove S := by
    refine ⟨clarkeDirectionalDerivReal h (f x) ((fderiv ℝ f x) d), ?_⟩
    intro r hr
    rcases hr with ⟨ξ', hξ'_sub, rfl⟩
    have hξ'_clarke : ξ' ∈ clarkeDifferential h (f x) := by
      simpa [clarkeDifferential_eq_subdifferential_of_convexOn_of_locallyLipschitzAt
        h (f x) h_convex h_outer_local] using hξ'_sub
    exact
      (mem_clarkeDifferential_real_iff_of_locallyLipschitzAt
        h (f x) h_outer_local ξ').1 hξ'_clarke ((fderiv ℝ f x) d)
  have hξ_mem_S : ξ ((fderiv ℝ f x) d) ∈ S := by
    exact ⟨ξ, hξ_sub, rfl⟩
  have h_generator_eval :
      (StrongDual.toWeakDual
          (∑ i : Fin m, (ξ (EuclideanSpace.single i (1 : ℝ))) • ζ i)) d =
        ξ ((fderiv ℝ f x) d) := by
    -- Normalize the chain-rule generator by replacing each component Clarke subgradient with the
    -- actual derivative of that smooth coordinate map.
    calc
      (StrongDual.toWeakDual
          (∑ i : Fin m, (ξ (EuclideanSpace.single i (1 : ℝ))) • ζ i)) d
        = (∑ i : Fin m, (ξ (EuclideanSpace.single i (1 : ℝ))) • ζ i) d := by
            rfl
      _ = ∑ i : Fin m, (ξ (EuclideanSpace.single i (1 : ℝ))) * ζ i d := by
            let ev : StrongDual ℝ Point →ₗ[ℝ] ℝ :=
              { toFun := fun θ ↦ θ d
                map_add' := by intro θ₁ θ₂; rfl
                map_smul' := by intro c θ; rfl }
            change ev (∑ i : Fin m, (ξ (EuclideanSpace.single i (1 : ℝ))) • ζ i) =
              ∑ i : Fin m, ev ((ξ (EuclideanSpace.single i (1 : ℝ))) • ζ i)
            rw [map_sum]
      _ = ∑ i : Fin m, (ξ (EuclideanSpace.single i (1 : ℝ))) * (fderiv ℝ f x d) i := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            have h_component_contDiff : ContDiff ℝ 1 (fun y : Point ↦ f y i) := by
              exact ((contDiff_piLp (p := (2 : ENNReal))).1 h_contDiff) i
            have h_component_eq :
                ζ i = fderiv ℝ (fun y : Point ↦ f y i) x := by
              exact (mem_clarkeDifferential_iff_eq_fderiv_of_contDiff
                (fun y : Point ↦ f y i) x (ζ i) h_component_contDiff).1 (hζ_mem i)
            rw [h_component_eq, fderiv_component_apply_eq f x d i h_contDiff]
      _ = ξ ((fderiv ℝ f x) d) := by
            symm
            simpa using codomainDual_apply_eq_sum_single_coeff (n := m) ξ ((fderiv ℝ f x) d)
  -- The normalized generator value belongs to the support image defining `DF(x, d)`.
  calc
    (StrongDual.toWeakDual (∑ i : Fin m, (ξ (EuclideanSpace.single i (1 : ℝ))) • ζ i)) d
      = ξ ((fderiv ℝ f x) d) := h_generator_eval
    _ ≤ sSup S := by
          exact le_csSup hS_bdd hξ_mem_S
    _ = compositeNonsmoothDF h f x d := by
          rw [show S =
            ((fun ξ : StrongDual ℝ ValuePoint ↦ ξ ((fderiv ℝ f x) d)) ''
              subdifferential h (f x) : Set ℝ) by rfl]
          rw [← compositeNonsmoothDF_eq_sSup_image_subdifferentialEval_fderiv]

/-- Helper for Chapter14 Lemma 14.6.1: after the local-Lipschitz bridge, the remaining source
frontier is the real-valued support identity
`clarkeDirectionalDerivReal (h ∘ f) x d = DF(x, d)`. -/
theorem clarkeDirectionalDerivReal_comp_eq_compositeNonsmoothDF
    (h : ValuePoint → ℝ) (f : Point → ValuePoint) (x d : Point)
    (h_contDiff : ContDiff ℝ 1 f)
    (h_convex : ConvexOn ℝ Set.univ h) :
    clarkeDirectionalDerivReal (h ∘ f) x d = compositeNonsmoothDF h f x d := by
  have h_outer_local : LocallyLipschitzAt h (f x) :=
    convexOn_univ_locallyLipschitzAt h (f x) h_convex
  let S : Set ℝ :=
    ((fun ξ : StrongDual ℝ ValuePoint ↦ ξ ((fderiv ℝ f x) d)) '' subdifferential h (f x))
  have h_component_local : ∀ i : Fin m, LocallyLipschitzAt (fun y : Point ↦ f y i) x := by
    -- Each scalar coordinate of the smooth inner map is locally Lipschitz.
    intro i
    exact (((contDiff_piLp (p := (2 : ENNReal))).1 h_contDiff) i).contDiffAt.locallyLipschitzAt
  have h_subdiff_nonempty : (subdifferential h (f x)).Nonempty := by
    rcases clarkeDifferential_nonempty_of_locallyLipschitzAt h (f x) h_outer_local with ⟨ξ, hξ⟩
    refine ⟨ξ, ?_⟩
    simpa [clarkeDifferential_eq_subdifferential_of_convexOn_of_locallyLipschitzAt
      h (f x) h_convex h_outer_local] using hξ
  have hS_nonempty : S.Nonempty := by
    rcases h_subdiff_nonempty with ⟨ξ, hξ⟩
    exact ⟨ξ ((fderiv ℝ f x) d), ⟨ξ, hξ, rfl⟩⟩
  have h_df_le_clarke :
      compositeNonsmoothDF h f x d ≤ clarkeDirectionalDerivReal (h ∘ f) x d := by
    -- Every pushed-forward outer subgradient contributes a support value below the Clarke
    -- directional derivative of the composite.
    rw [compositeNonsmoothDF_eq_sSup_image_subdifferentialEval_fderiv]
    change sSup S ≤ clarkeDirectionalDerivReal (h ∘ f) x d
    refine csSup_le hS_nonempty ?_
    rintro r ⟨ξ, hξ, rfl⟩
    exact
      subdifferential_pushforward_value_le_clarkeDirectionalDerivReal_comp
        h f x d ξ h_contDiff h_convex hξ
  obtain ⟨η, hη_mem, hη_dom⟩ :=
    exists_mem_chainRule_generator_eval_ge_comp h f x d h_component_local h_outer_local
  have h_clarke_le_df :
      clarkeDirectionalDerivReal (h ∘ f) x d ≤ compositeNonsmoothDF h f x d := by
    -- The chain-rule generator witness already evaluates to a value lying in the source support
    -- set, so it bounds the composite Clarke directional derivative from above.
    exact le_trans hη_dom
      (chainRuleGenerator_eval_le_compositeNonsmoothDF h f x d h_contDiff h_convex hη_mem)
  exact le_antisymm h_clarke_le_df h_df_le_clarke

/-- Under the Section 14.6 smooth/convex hypotheses, the Clarke generalized directional
derivative of the composite objective `h ∘ f` agrees with the source first-order quantity
`DF(x, d)`. This is bridge API; the main labeled item in this file is the stationary-condition
equivalence below. -/
theorem clarkeDirectionalDeriv_comp_eq_compositeNonsmoothDF
    (h : ValuePoint → ℝ) (f : Point → ValuePoint) (x d : Point)
    (h_contDiff : ContDiff ℝ 1 f)
    (h_convex : ConvexOn ℝ Set.univ h) :
    clarkeDirectionalDeriv (h ∘ f) x d = compositeNonsmoothDF h f x d := by
  -- First reduce the `EReal` statement to the finite real-valued support identity.
  have h_local_comp : LocallyLipschitzAt (h ∘ f) x :=
    composite_locallyLipschitzAt h f x h_contDiff h_convex
  have h_real :
      clarkeDirectionalDerivReal (h ∘ f) x d = compositeNonsmoothDF h f x d :=
    clarkeDirectionalDerivReal_comp_eq_compositeNonsmoothDF h f x d h_contDiff h_convex
  calc
    clarkeDirectionalDeriv (h ∘ f) x d =
        ((clarkeDirectionalDerivReal (h ∘ f) x d : ℝ) : EReal) := by
          -- Local Lipschitz regularity lets us pass from the textbook real owner back to `EReal`.
          symm
          exact coe_clarkeDirectionalDerivReal_of_locallyLipschitzAt (h ∘ f) x d h_local_comp
    _ = compositeNonsmoothDF h f x d := by
          -- Coerce the real-valued support identity obtained above.
          exact congrArg (fun r : ℝ ↦ (r : EReal)) h_real

/-- Chapter14 Lemma 14.6.1: for the composite objective `h ∘ f`, the source stationary condition
that every Clarke generalized directional derivative at `x` is nonnegative is equivalent to
nonnegativity of the source first-order model `DF(x, d)` in every direction. -/
theorem compositeNonsmoothStationaryCondition_iff_nonneg_compositeNonsmoothDF
    (h : ValuePoint → ℝ) (f : Point → ValuePoint) (x : Point)
    (h_contDiff : ContDiff ℝ 1 f)
    (h_convex : ConvexOn ℝ Set.univ h) :
    (∀ d : Point, 0 ≤ clarkeDirectionalDeriv (h ∘ f) x d) ↔
      ∀ d : Point, 0 ≤ compositeNonsmoothDF h f x d := by
  constructor
  · intro h_nonneg d
    -- Once the derivative bridge is in place, the source stationary inequality is a cast-cleanup.
    have h_dir : (0 : EReal) ≤ compositeNonsmoothDF h f x d := by
      simpa [clarkeDirectionalDeriv_comp_eq_compositeNonsmoothDF h f x d h_contDiff h_convex]
        using h_nonneg d
    exact_mod_cast h_dir
  · intro h_nonneg d
    -- The converse is the same pointwise rewrite in the opposite direction.
    have h_dir : (0 : EReal) ≤ compositeNonsmoothDF h f x d := by
      exact_mod_cast h_nonneg d
    simpa [clarkeDirectionalDeriv_comp_eq_compositeNonsmoothDF h f x d h_contDiff h_convex]
      using h_dir

/-- If the composite objective `h ∘ f` is locally Lipschitz at `x`, then the Chapter 14 Clarke
differential condition `0 ∈ ∂ (h ∘ f)(x)` is equivalent to the same Section 14.6 stationary
condition `DF(x, d) ≥ 0` for every direction `d`. -/
theorem zero_mem_clarkeDifferential_comp_iff_nonneg_compositeNonsmoothDF
    (h : ValuePoint → ℝ) (f : Point → ValuePoint) (x : Point)
    [LocallyLipschitzAt (h ∘ f) x]
    (h_contDiff : ContDiff ℝ 1 f)
    (h_convex : ConvexOn ℝ Set.univ h) :
    0 ∈ clarkeDifferential (h ∘ f) x ↔
      ∀ d : Point, 0 ≤ compositeNonsmoothDF h f x d := by
  -- Rewrite the Clarke-differential condition through the chapter's stationary-point owner.
  rw [← isClarkeStationaryPoint_iff_zero_mem_clarkeDifferential, isClarkeStationaryPoint_iff]
  exact compositeNonsmoothStationaryCondition_iff_nonneg_compositeNonsmoothDF
    h f x h_contDiff h_convex

namespace CompositeNonsmoothOptimizationProblem

/-- For a composite nonsmooth problem `problem`, the Clarke generalized directional derivative of
its objective agrees with the owner-specialized first-order model `DF[problem](x, d)`. -/
theorem clarkeDirectionalDeriv_eq_firstOrderModel
    (problem : CompositeNonsmoothOptimizationProblem n m) (x d : Point) :
    clarkeDirectionalDeriv problem x d = DF[problem](x, d) := by
  simpa [CompositeNonsmoothOptimizationProblem.objective,
    CompositeNonsmoothOptimizationProblem.firstOrderModel] using
    clarkeDirectionalDeriv_comp_eq_compositeNonsmoothDF
      problem.outerFunction problem.smoothMap x d
      problem.smoothMap_contDiff problem.outerFunction_convex

/-- For a composite nonsmooth problem `problem`, the Section 14.6 stationary condition for its
objective is equivalent to nonnegativity of the owner-specialized first-order model
`DF[problem](x, d)` in every direction. -/
theorem stationaryCondition_iff_nonneg_firstOrderModel
    (problem : CompositeNonsmoothOptimizationProblem n m) (x : Point) :
    (∀ d : Point, 0 ≤ clarkeDirectionalDeriv problem x d) ↔
      ∀ d : Point, 0 ≤ DF[problem](x, d) := by
  simpa [CompositeNonsmoothOptimizationProblem.objective,
    CompositeNonsmoothOptimizationProblem.firstOrderModel] using
    compositeNonsmoothStationaryCondition_iff_nonneg_compositeNonsmoothDF
      problem.outerFunction problem.smoothMap x
      problem.smoothMap_contDiff problem.outerFunction_convex

/-- If the objective of a composite nonsmooth problem `problem` is locally Lipschitz at `x`,
then `0 ∈ ∂ problem(x)` is equivalent to nonnegativity of `DF[problem](x, d)` in every
direction. -/
theorem zero_mem_clarkeDifferential_iff_nonneg_firstOrderModel
    (problem : CompositeNonsmoothOptimizationProblem n m) (x : Point)
    [LocallyLipschitzAt problem x] :
    0 ∈ clarkeDifferential problem x ↔
      ∀ d : Point, 0 ≤ DF[problem](x, d) := by
  let _ : LocallyLipschitzAt (problem.outerFunction ∘ problem.smoothMap) x := by
    simpa [CompositeNonsmoothOptimizationProblem.objective] using
      (inferInstance : LocallyLipschitzAt problem x)
  simpa [CompositeNonsmoothOptimizationProblem.objective,
    CompositeNonsmoothOptimizationProblem.firstOrderModel] using
    zero_mem_clarkeDifferential_comp_iff_nonneg_compositeNonsmoothDF
      problem.outerFunction problem.smoothMap x
      problem.smoothMap_contDiff problem.outerFunction_convex

end CompositeNonsmoothOptimizationProblem

#print axioms CompositeNonsmoothOptimizationProblem.firstOrderModel
#print axioms compositeNonsmoothDF

end
