/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Algorithm_4_3_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_3_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.FirstOrderTaylorModel
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Lemma_1_5_11
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Lemma_2_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Proposition_2_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_30
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Proposition_4_3_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open LinearMap (BilinForm)
open LinearMap.BilinForm
open scoped BInducedNorm CubicNewtonStepNotation Gradient

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Lemma 4.3.4 lies in the optimal cubic-Newton estimating-sequence domain on a finite-dimensional
real inner-product space.

Sampled owner-style declarations:
* `OptimalCubicNewtonMethod.psi` in `Algorithm_4_3_1`
* `OptimalCubicNewtonMethod.psi_zero` in `Algorithm_4_3_1`
* `OptimalCubicNewtonMethod.psi_succ` in `Algorithm_4_3_1`
* `CubicNewtonStep.residual` in `Definition_4_3_6`
* `ConvexOn.lower_tangent_plane` in `Chap02/Definition_2_2`

Best owner abstraction:
* core/canonical: `OptimalCubicNewtonMethod B Mf f x0 sigma`

Primitive data:
* the method data already stored by `OptimalCubicNewtonMethod`

Derived API:
* the estimating functions `ψ_k`
* the cubic-step residuals `r[(method.step)] (method.y k)`
* the accumulated lower-bound correction term `B_k`
* the convex lower-support inequality from `ConvexOn.lower_tangent_plane`

Source/core/bridge triage:
* source-facing: Lemma 4.3.4's lower bound
  `A_k f(x_k) + B_k ≤ ψ_k(v_k)`
* core/canonical: the owner `OptimalCubicNewtonMethod` with its `psi` recursion
* bridge/view: the scalar correction term `B_k`, derived from the method data rather than stored
  as extra primitive structure
-/

namespace OptimalCubicNewtonMethod

/-- The accumulated cubic correction term `B_k` from the estimating-sequence lower bound. -/
def estimatingLowerBoundCorrection
    {B : BilinForm ℝ E} {Mf : NNRealˣ} {f : PrimalSpace B → ℝ}
    [Fact B.toQuadraticMap.PosDef]
    {x0 : PrimalSpace B} {sigma : ℝ}
    (method : OptimalCubicNewtonMethod B Mf f x0 sigma) :
    ℕ → ℝ :=
  fun k ↦
    (((1 - sigma ^ (2 : ℕ)) / 4 : ℝ) * ((Mf : ℝ) / sigma)) *
      Finset.sum (Finset.range k) fun i ↦
        method.A (i + 1) * (r[(method.step)] (method.y i)) ^ (3 : ℕ)

/-- The cubic correction term vanishes at the initial stage `k = 0`. -/
@[simp] theorem estimatingLowerBoundCorrection_zero
    {B : BilinForm ℝ E} {Mf : NNRealˣ} {f : PrimalSpace B → ℝ}
    [Fact B.toQuadraticMap.PosDef]
    {x0 : PrimalSpace B} {sigma : ℝ}
    (method : OptimalCubicNewtonMethod B Mf f x0 sigma) :
    method.estimatingLowerBoundCorrection 0 = 0 := by
  -- The defining finite sum is empty at `k = 0`.
  simp [estimatingLowerBoundCorrection]

/-- Helper for Lemma 4.3.4: the accumulated cubic correction gains exactly the new
stage-`k` cubic term when passing from `k` to `k + 1`. -/
@[simp] theorem estimatingLowerBoundCorrection_succ
    {B : BilinForm ℝ E} {Mf : NNRealˣ} {f : PrimalSpace B → ℝ}
    [Fact B.toQuadraticMap.PosDef]
    {x0 : PrimalSpace B} {sigma : ℝ}
    (method : OptimalCubicNewtonMethod B Mf f x0 sigma)
    (k : ℕ) :
    method.estimatingLowerBoundCorrection (k + 1) =
      method.estimatingLowerBoundCorrection k +
        (((1 - sigma ^ (2 : ℕ)) / 4 : ℝ) * method.M) *
          (method.A (k + 1) * (r[(method.step)] (method.y k)) ^ (3 : ℕ)) := by
  -- Expand the defining sum once and rewrite `method.M = (Mf : ℝ) / sigma`.
  unfold estimatingLowerBoundCorrection OptimalCubicNewtonMethod.M
  rw [Finset.sum_range_succ]
  ring

end OptimalCubicNewtonMethod

section

variable {B : BilinForm ℝ E} {Mf : NNRealˣ} {f : PrimalSpace B → ℝ}
  [Fact B.toQuadraticMap.PosDef]
  {x0 : PrimalSpace B} {sigma : ℝ}
  (method : OptimalCubicNewtonMethod B Mf f x0 sigma)

attribute [local instance]
  LinearMap.BilinForm.instNormedAddCommGroupPrimalSpaceOfFactPosDefRealToQuadraticMap
attribute [local instance] LinearMap.BilinForm.instNormedSpaceRealPrimalSpace

/-- Helper for Lemma 4.3.4: this local alias fixes the `C22` owner surface to the chapter's
`B`-induced normed structure on `PrimalSpace B`, so later helper statements do not drift onto the
inherited Hilbert-space spelling. -/
private abbrev primalSpaceMemC22
    (Mf : NNReal) (f : PrimalSpace B → ℝ) : Prop :=
  f ∈ C22[Mf]

/-
The ambient `C22` hypothesis is only used through pointwise regularity in this file, so keep the
original local theorem surface here and repair the remaining instance mismatch lower down.
-/
omit [FiniteDimensional ℝ E] [Fact B.toQuadraticMap.PosDef] in
/-- Helper for Lemma 4.3.4: the ambient `C22` hypothesis still gives pointwise `C²` regularity at
every point of `PrimalSpace B`. -/
private lemma primalSpaceMemC22ContDiffAt
    (hf : primalSpaceMemC22 (B := B) (Mf := (Mf : NNReal)) f)
    (x : PrimalSpace B) :
    ContDiffAt ℝ 2 f x := by
  -- Read the pointwise `C²` regularity directly from the ambient `C22` membership.
  simpa using (hf.contDiff.contDiffAt (x := x))

/-- Helper for Lemma 4.3.4: for real continuous linear functionals, the support function of the
ambient closed unit ball equals the operator norm. -/
private theorem ContinuousLinearMap.sSupUnitClosedBallEqNormReal
    {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] (g : F →L[ℝ] ℝ) :
    sSup (g '' Metric.closedBall (0 : F) 1) = ‖g‖ := by
  let S : Set ℝ := g '' Metric.closedBall (0 : F) 1
  let T : Set ℝ := (fun x : F ↦ |g x|) '' Metric.closedBall (0 : F) 1
  have hS_nonempty : S.Nonempty := ⟨0, ⟨0, by simp, by simp⟩⟩
  have hS_bound : ∀ y ∈ S, y ≤ ‖g‖ := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hx_norm : ‖x‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hx
    have hgx : |g x| ≤ ‖g‖ * ‖x‖ := by
      simpa [Real.norm_eq_abs] using g.le_opNorm x
    have hgnonneg : 0 ≤ ‖g‖ := norm_nonneg _
    -- Bound each evaluation on the closed unit ball by the operator norm.
    calc
      g x ≤ |g x| := le_abs_self _
      _ ≤ ‖g‖ * ‖x‖ := hgx
      _ ≤ ‖g‖ := by
            nlinarith
  have hS_bdd : BddAbove S := ⟨‖g‖, hS_bound⟩
  have hT_nonempty : T.Nonempty := ⟨0, ⟨0, by simp, by simp⟩⟩
  have hT_subset : T ⊆ S := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    by_cases hgx : 0 ≤ g x
    · exact ⟨x, hx, by simp [abs_of_nonneg hgx]⟩
    · refine ⟨-x, by simpa [Metric.mem_closedBall, dist_eq_norm] using hx, ?_⟩
      simp [abs_of_neg (lt_of_not_ge hgx)]
  have hsSup_T_le : sSup T ≤ sSup S := by
    refine csSup_le hT_nonempty ?_
    intro y hy
    exact le_csSup hS_bdd (hT_subset hy)
  have hT_eq : sSup T = ‖g‖ := by
    simpa [T, Real.norm_eq_abs] using ContinuousLinearMap.sSup_unitClosedBall_eq_norm g
  have hsSup_S_le : sSup S ≤ ‖g‖ := csSup_le hS_nonempty hS_bound
  have hnorm_le : ‖g‖ ≤ sSup S := by
    rw [← hT_eq]
    exact hsSup_T_le
  -- The absolute-value support formula and symmetry of the ball recover the usual support value.
  exact le_antisymm hsSup_S_le hnorm_le

/-- Helper for Lemma 4.3.4: on `PrimalSpace B`, the primal `B`-unit ball is exactly the ambient
closed unit ball for the induced norm. -/
private lemma primalUnitBall_eq_closedBall
    {F : Type u} [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]
    (B : BilinForm ℝ F) [Fact B.toQuadraticMap.PosDef] :
    {x : PrimalSpace B | B.primalSeminorm Fact.out x ≤ 1} =
      Metric.closedBall (0 : PrimalSpace B) 1 := by
  ext x
  constructor
  · intro hx
    -- On `PrimalSpace B`, the ambient closed unit ball is cut out by the same norm inequality.
    change B.primalSeminorm Fact.out x ≤ 1 at hx
    have hx' : ‖x‖ ≤ 1 := by
      change B.primalSeminorm Fact.out x ≤ 1
      exact hx
    simpa [Metric.mem_closedBall, dist_eq_norm] using hx'
  · intro hx
    -- Rewrite the closed-ball condition to the equivalent intrinsic norm inequality.
    have hx' : ‖x‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hx
    change B.primalSeminorm Fact.out x ≤ 1 at hx'
    change B.primalSeminorm Fact.out x ≤ 1
    exact hx'

/-- Helper for Lemma 4.3.4: on the intrinsic carrier `PrimalSpace B`, the ambient operator norm
on the continuous dual agrees with the chapter's `B`-dual norm. -/
private lemma strongDualNormEqBDualNormOnPrimalSpace
    {F : Type u} [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]
    (B : BilinForm ℝ F) [Fact B.toQuadraticMap.PosDef]
    (g : PrimalSpace B →L[ℝ] ℝ) :
    ‖g‖ = ‖g‖[B,*] := by
  rw [LinearMap.BilinForm.dualNorm_eq_sSup_primalUnitBall_strongDual]
  rw [primalUnitBall_eq_closedBall (B := B)]
  symm
  exact ContinuousLinearMap.sSupUnitClosedBallEqNormReal g

/-- Helper for Lemma 4.3.4: the `B`-dual norm controls every linear evaluation by the product
`‖g‖[B,*] * ‖x‖[B]`. -/
private lemma dualEvalNormLe
    (g : PrimalSpace B →L[ℝ] ℝ)
    (x : PrimalSpace B) :
    ‖g x‖ ≤ ‖g‖[B,*] * ‖x‖[B] := by
  let gVec : PrimalSpace B := (InnerProductSpace.toDual ℝ (PrimalSpace B)).symm g
  have hupper :
      inner ℝ gVec x ≤
        Seminorm.dualNorm (B.primalSeminorm Fact.out) gVec * ‖x‖[B] := by
    -- Compare the pairing against the Chapter 2 dual norm attached to the primal `B`-seminorm.
    simpa using Seminorm.inner_le_dualNorm_mul (B.primalSeminorm Fact.out) x gVec
  have hlower :
      -(Seminorm.dualNorm (B.primalSeminorm Fact.out) gVec * ‖x‖[B]) ≤ inner ℝ gVec x := by
    have hneg :
        -(inner ℝ gVec x) ≤ Seminorm.dualNorm (B.primalSeminorm Fact.out) gVec * ‖x‖[B] := by
      -- Apply the same pairing estimate at `-x` to control the negative direction.
      simpa [neg_mul, mul_comm, mul_left_comm, mul_assoc] using
        (Seminorm.inner_le_dualNorm_mul (B.primalSeminorm Fact.out) (-x) gVec)
    linarith
  have habs :
      |inner ℝ gVec x| ≤
        Seminorm.dualNorm (B.primalSeminorm Fact.out) gVec * ‖x‖[B] := by
    -- The two one-sided bounds package into the desired absolute-value estimate.
    exact abs_le.mpr ⟨hlower, hupper⟩
  have hdual :
      Seminorm.dualNorm (B.primalSeminorm Fact.out) gVec = ‖g‖[B,*] := by
    -- The `toDual` bridge identifies the Chapter 2 dual norm with the Chapter 4 `B`-dual norm.
    simpa [gVec] using
      (seminormDualNorm_eq_dualNorm_toDual B Fact.out gVec)
  -- Rewrite the pairing back to `g x` and then identify the two dual norms.
  rw [← hdual]
  simpa [Real.norm_eq_abs, gVec, InnerProductSpace.toDual_symm_apply] using habs

/-- Helper for Lemma 4.3.4: convexity at `x_{k+1}` bounds the affine model used in the
`ψ_{k+1}` update by the comparison value `f z`. -/
private lemma supportAtSuccessor
    (hf : primalSpaceMemC22 (B := B) (Mf := (Mf : NNReal)) f)
    (hf_conv : ConvexOn ℝ Set.univ f)
    (k : ℕ) (z : PrimalSpace B) :
    f (method (k + 1)) +
        inner ℝ (∇ f (method (k + 1))) (z - method (k + 1)) ≤
      f z := by
  have hdiff :
      DifferentiableWithinAt ℝ f Set.univ (method (k + 1)) := by
    -- The `C²` hypothesis gives the differentiability needed by the tangent-plane inequality.
    have hcontDiffAt : ContDiffAt ℝ 2 f (method (k + 1)) :=
      primalSpaceMemC22ContDiffAt (B := B) (Mf := Mf) (f := f) hf (method (k + 1))
    exact
      (hcontDiffAt.differentiableAt
        (by norm_num)).differentiableWithinAt
  -- Apply convex support at `x_{k+1}` and rewrite the canonical gradient notation.
  simpa [gradientWithin, gradient, fderivWithin_univ] using
    hf_conv.lower_tangent_plane
      (method (k + 1))
      (by simp)
      hdiff
      z
      (by simp)

/-- Helper for Lemma 4.3.4: the affine part of the estimating function is convex on the whole
space because affine maps preserve binary convex combinations exactly. -/
private lemma affinePartConvexOn
    (k : ℕ) :
    ConvexOn ℝ Set.univ (method.affinePart k) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  -- The affine part turns the convex combination in the argument into the same convex combination
  -- of the two endpoint values.
  exact le_of_eq <| by
    simpa [smul_eq_mul] using
      (Convex.combo_affine_apply hab :
        method.affinePart k (a • x + b • y) =
          a • method.affinePart k x + b • method.affinePart k y)

omit [FiniteDimensional ℝ E] in
/-- Helper for Lemma 4.3.4: the symmetric associated form keeps the same positive quadratic data
as `B`, so the `B`-geometry can be rewritten on a symmetric surface when needed. -/
private lemma associatedPosDef :
    (B.toQuadraticMap.associated).toQuadraticMap.PosDef := by
  -- The associated form has the same diagonal quadratic form, so positivity is unchanged.
  rw [QuadraticMap.posDef_iff_nonneg]
  let hPos : B.toQuadraticMap.PosDef := Fact.out
  refine ⟨?_, ?_⟩
  · intro z
    rw [show (B.toQuadraticMap.associated).toQuadraticMap z = B.toQuadraticMap z by
      simpa using QuadraticMap.associated_eq_self_apply ℝ B.toQuadraticMap z]
    exact hPos.nonneg z
  · intro z hz
    apply hPos.anisotropic z
    rw [← show (B.toQuadraticMap.associated).toQuadraticMap z = B.toQuadraticMap z by
      simpa using QuadraticMap.associated_eq_self_apply ℝ B.toQuadraticMap z]
    exact hz

/-- Helper for Lemma 4.3.4: typeclass search can use the positive-definite quadratic data of the
associated symmetric form. -/
private instance associatedPosDefFact :
    Fact (B.toQuadraticMap.associated).toQuadraticMap.PosDef :=
  ⟨associatedPosDef⟩

omit [FiniteDimensional ℝ E] in
/-- Helper for Lemma 4.3.4: the associated symmetric form induces the same primal norm as `B`
because both forms have the same quadratic map on diagonal values. -/
private lemma associatedPrimalNormEq
    (z : PrimalSpace B) :
    ‖z‖[B.toQuadraticMap.associated] = ‖z‖[B] := by
  -- Rewrite both norms by their diagonal formulas and use `associated_eq_self_apply`.
  rw [LinearMap.BilinForm.primalSeminorm_apply, LinearMap.BilinForm.primalSeminorm_apply]
  simpa using
    congrArg Real.sqrt (QuadraticMap.associated_eq_self_apply ℝ B.toQuadraticMap z)

omit [FiniteDimensional ℝ E] in
/-- Helper for Lemma 4.3.4: squaring the `B`-norm is the same as evaluating the associated
symmetric form on the diagonal. -/
private lemma associatedNormSqEq
    (z : PrimalSpace B) :
    ‖z‖[B] ^ (2 : ℕ) = (B.toQuadraticMap.associated) z z := by
  -- Move to the associated form, where the norm square is the defining quadratic value.
  rw [← associatedPrimalNormEq z, LinearMap.BilinForm.primalSeminorm_apply]
  have hnonneg : 0 ≤ (B.toQuadraticMap.associated) z z := by
    change 0 ≤ (B.toQuadraticMap.associated).toQuadraticMap z
    exact QuadraticMap.PosDef.nonneg associatedPosDef z
  simpa [pow_two] using Real.sq_sqrt hnonneg

omit [FiniteDimensional ℝ E] in
/-- Helper for Lemma 4.3.4: the centered half squared `B`-norm satisfies the exact affine-combo
identity required for `1`-strong convexity. -/
private lemma centeredHalfBNormSq_affineComboExact
    (x0 x y : PrimalSpace B) {a b : ℝ} (hab : a + b = 1) :
    (1 / 2 : ℝ) * ‖a • x + b • y - x0‖[B] ^ (2 : ℕ) =
      a * ((1 / 2 : ℝ) * ‖x - x0‖[B] ^ (2 : ℕ)) +
        b * ((1 / 2 : ℝ) * ‖y - x0‖[B] ^ (2 : ℕ)) -
          a * b * ((1 / 2 : ℝ) * ‖x - y‖[B] ^ (2 : ℕ)) := by
  let A : BilinForm ℝ (PrimalSpace B) := B.toQuadraticMap.associated
  let u0 : PrimalSpace B := x - x0
  let v0 : PrimalSpace B := y - x0
  have hA_symm : A.IsSymm := by
    exact ⟨QuadraticMap.associated_isSymm ℝ B.toQuadraticMap⟩
  have hcross : A u0 v0 = A v0 u0 := by
    exact hA_symm.eq _ _
  have hcombo_center :
      a • x + b • y - x0 = a • u0 + b • v0 := by
    have hx0 :
        x0 = a • x0 + b • x0 := by
      calc
        x0 = (1 : ℝ) • x0 := by simp
        _ = (a + b) • x0 := by rw [hab]
        _ = a • x0 + b • x0 := by rw [add_smul]
    -- Rewrite the center `x0` as the same affine combination before regrouping terms.
    rw [hx0]
    simp [u0, v0, sub_eq_add_neg, smul_add, add_assoc, add_left_comm, add_comm]
  have hcombo_expand :
      A (a • u0 + b • v0) (a • u0 + b • v0) =
        a ^ (2 : ℕ) * A u0 u0 +
          (a * b) * A u0 v0 +
            (a * b) * A v0 u0 +
              b ^ (2 : ℕ) * A v0 v0 := by
    -- Expand the associated quadratic form into diagonal and cross terms.
    simp [A, map_add, map_smul, pow_two]
    ring
  have hdiff_expand :
      A (u0 - v0) (u0 - v0) =
        A u0 u0 - 2 * A u0 v0 + A v0 v0 := by
    -- Expand the squared difference and then use symmetry to merge the two cross terms.
    calc
      A (u0 - v0) (u0 - v0)
          = A u0 u0 - A u0 v0 - A v0 u0 + A v0 v0 := by
              simp [A, sub_eq_add_neg, map_add]
              ring_nf
      _ = A u0 u0 - 2 * A u0 v0 + A v0 v0 := by
            rw [hcross]
            ring
  have hdiff_eq : u0 - v0 = x - y := by
    -- The common center cancels, so the correction term depends only on `x - y`.
    simp [u0, v0]
  calc
    (1 / 2 : ℝ) * ‖a • x + b • y - x0‖[B] ^ (2 : ℕ)
        = (1 / 2 : ℝ) * A (a • u0 + b • v0) (a • u0 + b • v0) := by
            rw [hcombo_center, associatedNormSqEq (a • u0 + b • v0)]
    _ =
        (1 / 2 : ℝ) *
          (a ^ (2 : ℕ) * A u0 u0 +
            (a * b) * A u0 v0 +
              (a * b) * A v0 u0 +
                b ^ (2 : ℕ) * A v0 v0) := by
                  rw [hcombo_expand]
    _ =
        a * ((1 / 2 : ℝ) * A u0 u0) +
          b * ((1 / 2 : ℝ) * A v0 v0) -
            a * b * ((1 / 2 : ℝ) * (A u0 u0 - 2 * A u0 v0 + A v0 v0)) := by
              rw [hcross]
              have hb' : b = 1 - a := by linarith
              rw [hb']
              ring
    _ =
        a * ((1 / 2 : ℝ) * ‖x - x0‖[B] ^ (2 : ℕ)) +
          b * ((1 / 2 : ℝ) * ‖y - x0‖[B] ^ (2 : ℕ)) -
            a * b * ((1 / 2 : ℝ) * A (u0 - v0) (u0 - v0)) := by
              rw [← hdiff_expand, ← associatedNormSqEq u0, ← associatedNormSqEq v0]
    _ =
        a * ((1 / 2 : ℝ) * ‖x - x0‖[B] ^ (2 : ℕ)) +
          b * ((1 / 2 : ℝ) * ‖y - x0‖[B] ^ (2 : ℕ)) -
            a * b * ((1 / 2 : ℝ) * ‖x - y‖[B] ^ (2 : ℕ)) := by
              rw [hdiff_eq, associatedNormSqEq (x - y)]

omit [FiniteDimensional ℝ E] in
/-- Helper for Lemma 4.3.4: every affine perturbation of the centered half squared `B`-norm is
`1`-strongly convex on `Set.univ` with respect to the intrinsic `B`-seminorm. -/
private lemma affinePlusCenteredHalfBNormSq_strongConvexOnWith
    (affinePart : PrimalSpace B →ᵃ[ℝ] ℝ) :
    StrongConvexOnWith
      (B.primalSeminorm Fact.out)
      (1 : ℝ)
      Set.univ
      (fun z : PrimalSpace B ↦ affinePart z + (1 / 2 : ℝ) * ‖z - x0‖[B] ^ (2 : ℕ)) := by
  refine ⟨convex_univ, by norm_num, ?_⟩
  intro x hx y hy a b ha hb hab
  have haff :
      affinePart (a • x + b • y) = a * affinePart x + b * affinePart y := by
    -- The affine part preserves convex combinations exactly.
    simpa [smul_eq_mul] using
      (Convex.combo_affine_apply hab :
        affinePart (a • x + b • y) = a • affinePart x + b • affinePart y)
  -- Combine the exact affine identity with the exact quadratic identity.
  exact le_of_eq <| by
    calc
      (fun z : PrimalSpace B ↦ affinePart z + (1 / 2 : ℝ) * ‖z - x0‖[B] ^ (2 : ℕ))
          (a • x + b • y)
          =
          affinePart (a • x + b • y) +
            (1 / 2 : ℝ) * ‖a • x + b • y - x0‖[B] ^ (2 : ℕ) := by
              simp
      _ =
          a * affinePart x + b * affinePart y +
            (1 / 2 : ℝ) * ‖a • x + b • y - x0‖[B] ^ (2 : ℕ) := by
              rw [haff]
      _ =
          a * affinePart x + b * affinePart y +
            (a * ((1 / 2 : ℝ) * ‖x - x0‖[B] ^ (2 : ℕ)) +
              b * ((1 / 2 : ℝ) * ‖y - x0‖[B] ^ (2 : ℕ)) -
                a * b * ((1 / 2 : ℝ) * ‖x - y‖[B] ^ (2 : ℕ))) := by
                  rw [centeredHalfBNormSq_affineComboExact x0 x y hab]
      _ =
          a • (fun z : PrimalSpace B ↦ affinePart z + (1 / 2 : ℝ) * ‖z - x0‖[B] ^ (2 : ℕ)) x +
            b • (fun z : PrimalSpace B ↦ affinePart z + (1 / 2 : ℝ) * ‖z - x0‖[B] ^ (2 : ℕ)) y -
              a * b * ((1 / 2 : ℝ) * ‖x - y‖[B] ^ (2 : ℕ)) := by
                simp [smul_eq_mul]
                ring

/-- Helper for Lemma 4.3.4: the cubic Newton model is unchanged after replacing `B` by its
associated symmetric form because the cubic penalty only depends on the induced norm. -/
private lemma cubicNewtonModelAssociatedEq
    {M : ℝ} (x T : PrimalSpace B) :
    cubicNewtonModel B.toQuadraticMap.associated f M x T =
      cubicNewtonModel B f M x T := by
  -- Keep the source cubic model intact and only rewrite the norm surface.
  rw [cubicNewtonModel_apply, cubicNewtonModel_apply,
    associatedPrimalNormEq (T - x)]

/-- Helper for Lemma 4.3.4: the original cubic Newton step is still a minimizer for the
associated symmetric model because the model itself is unchanged. -/
private lemma associatedCubicNewtonStepIsMinOn
    {M : ℝ} (step : CubicNewtonStep B f M) (x : PrimalSpace B) :
    IsMinOn (cubicNewtonModel B.toQuadraticMap.associated f M x) Set.univ (step x) := by
  -- Transfer the minimizing property pointwise across the identical cubic model.
  intro y hy
  simpa [cubicNewtonModelAssociatedEq x (step x), cubicNewtonModelAssociatedEq x y] using
    step.isMinOn_apply x hy

/-- Helper for Lemma 4.3.4: the same step map can be viewed as a cubic Newton step for the
associated symmetric form without changing its values. -/
private abbrev associatedCubicNewtonStep
    {M : ℝ} (step : CubicNewtonStep B f M) :
    CubicNewtonStep B.toQuadraticMap.associated f M :=
  { toFun := step
    isMinOn := associatedCubicNewtonStepIsMinOn step }

/-- Helper for Lemma 4.3.4: the bilinear-form covector `A d` is bundled as a continuous linear
functional when the first-order optimality theorem is used on the associated symmetric surface. -/
private abbrev bilinCovector
    (A : BilinForm ℝ E) (d : E) :
    E →L[ℝ] ℝ :=
  ((LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] E →L[ℝ] ℝ) (A d))

/-- Helper for Lemma 4.3.4: every estimating function `ψ_k` is `1`-strongly convex with respect
to the intrinsic `B`-seminorm because it is an affine perturbation of the fixed quadratic
regularizer. -/
private lemma psiStrongConvexWith
    (k : ℕ) :
    StrongConvexOnWith (B.primalSeminorm Fact.out) (1 : ℝ) Set.univ (method.psi k) := by
  -- Route correction: rewrite `ψ_k` once into the canonical affine-plus-centered-half-square
  -- owner, then reuse the exact `B`-geometry strong-convexity lemma above.
  have hpsi :
      method.psi k =
        (fun z : PrimalSpace B ↦
          method.affinePart k z + (1 / 2 : ℝ) * ‖z - x0‖[B] ^ (2 : ℕ)) := by
    funext z
    exact method.psi_apply k z
  rw [hpsi]
  exact
    affinePlusCenteredHalfBNormSq_strongConvexOnWith (method.affinePart k)

/-- Helper for Lemma 4.3.4: the quadratic regularizer and a linear tilt satisfy the standard
completion-of-squares lower bound. -/
private lemma quadraticTiltLowerBound
    {a : ℝ} (ha : 0 ≤ a)
    (g : PrimalSpace B →L[ℝ] ℝ)
    (u : PrimalSpace B) :
    (1 / 2 : ℝ) * ‖u‖[B] ^ (2 : ℕ) + a * g u ≥
      -(((a ^ (2 : ℕ)) / 2 : ℝ) * ‖g‖[B,*] ^ (2 : ℕ)) := by
  -- First bound the linear evaluation from below by the dual/primal norm product.
  have hlinear :
      -(‖g‖[B,*] * ‖u‖[B]) ≤ g u := by
    have habs : |g u| ≤ ‖g‖[B,*] * ‖u‖[B] := by
      simpa [Real.norm_eq_abs] using dualEvalNormLe g u
    exact (abs_le.mp habs).1
  have hscaled :
      -(a * (‖g‖[B,*] * ‖u‖[B])) ≤ a * g u := by
    simpa [neg_mul, mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_left hlinear ha
  -- Then complete the square in the scalar variable `‖u‖[B]`.
  have hsq : 0 ≤ (‖u‖[B] - a * ‖g‖[B,*]) ^ (2 : ℕ) := by
    exact sq_nonneg (‖u‖[B] - a * ‖g‖[B,*])
  nlinarith

/-- Helper for Lemma 4.3.4: evaluating `ψ_{k+1}` at the next minimizer splits into the previous
stage value at `v_{k+1}` plus the old comparison tilt at `v_k` and the fresh increment
`v_{k+1} - v_k`. -/
private lemma psiSuccAtNext_split
    (k : ℕ) :
    method.psi (k + 1) (method.v (k + 1)) =
      method.psi k (method.v (k + 1)) +
        method.a (k + 1) *
          (f (method (k + 1)) +
            inner ℝ (∇ f (method (k + 1))) (method.v k - method (k + 1))) +
        method.a (k + 1) *
          inner ℝ (∇ f (method (k + 1))) (method.v (k + 1) - method.v k) := by
  -- Split the new affine tilt into the comparison term at `v_k` and the increment to `v_{k+1}`.
  rw [method.psi_succ]
  simp only
  have hu :
      method.v (k + 1) - method (k + 1) =
        (method.v k - method (k + 1)) + (method.v (k + 1) - method.v k) := by
    simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  rw [hu, inner_add_right]
  ring

/-- Helper for Lemma 4.3.4: minimizing the next estimating function can lose at most the standard
quadratic dual penalty coming from the new linear tilt. -/
private lemma psiSuccLowerBoundViaQuadraticCompletion
    (hf : primalSpaceMemC22 (B := B) (Mf := (Mf : NNReal)) f)
    (k : ℕ) :
    method.psi (k + 1) (method.v (k + 1)) ≥
      method.psi k (method.v k) +
        method.a (k + 1) *
          (f (method (k + 1)) +
            inner ℝ (∇ f (method (k + 1))) (method.v k - method (k + 1))) -
        (((method.a (k + 1)) ^ (2 : ℕ)) / 2 : ℝ) *
          ‖fderiv ℝ f (method (k + 1))‖[B,*] ^ (2 : ℕ) := by
  -- Rewrite `ψ_{k+1}(v_{k+1})`, use quadratic growth of `ψ_k` at `v_k`, and then complete the
  -- square in the fresh linear tilt `v_{k+1} - v_k`.
  have hquadratic :
      method.psi k (method.v (k + 1)) ≥
        method.psi k (method.v k) +
          (1 / 2 : ℝ) * ‖method.v (k + 1) - method.v k‖[B] ^ (2 : ℕ) := by
    -- The `ψ_k` minimizer `v_k` gives the canonical quadratic-growth lower bound.
    have hstrong := psiStrongConvexWith method k
    have hmin := method.v_isMin k
    simpa using
      (hstrong.quadratic_growth_of_isMinOn_of_mem
        (by simp : method.v k ∈ Set.univ)
        hmin
        (method.v (k + 1))
        (by simp : method.v (k + 1) ∈ Set.univ))
  have hcontDiffAt : ContDiffAt ℝ 2 f (method (k + 1)) := by
    -- The `C²` hypothesis supplies the differentiability needed for the gradient/Fréchet bridge.
    exact primalSpaceMemC22ContDiffAt (B := B) (Mf := Mf) (f := f) hf (method (k + 1))
  have hgradAt : HasGradientAt f (∇ f (method (k + 1))) (method (k + 1)) := by
    exact (hcontDiffAt.differentiableAt (by norm_num)).hasGradientAt
  have hgradEval :
      inner ℝ (∇ f (method (k + 1))) (method.v (k + 1) - method.v k) =
        fderiv ℝ f (method (k + 1)) (method.v (k + 1) - method.v k) := by
    -- Stay in the `fderiv` spelling before invoking the quadratic-completion lemma.
    have hgradCovector :
        (InnerProductSpace.toDual ℝ (PrimalSpace B)) (∇ f (method (k + 1))) =
          fderiv ℝ f (method (k + 1)) := by
      have hfderiv := hgradAt.hasFDerivAt.fderiv
      exact hfderiv.symm
    calc
      inner ℝ (∇ f (method (k + 1))) (method.v (k + 1) - method.v k) =
          ((InnerProductSpace.toDual ℝ (PrimalSpace B)) (∇ f (method (k + 1))))
            (method.v (k + 1) - method.v k) := by
              simp
      _ = fderiv ℝ f (method (k + 1)) (method.v (k + 1) - method.v k) := by
            rw [hgradCovector]
  have htilt :
      (1 / 2 : ℝ) * ‖method.v (k + 1) - method.v k‖[B] ^ (2 : ℕ) +
          method.a (k + 1) *
            inner ℝ (∇ f (method (k + 1))) (method.v (k + 1) - method.v k) ≥
        -(((method.a (k + 1)) ^ (2 : ℕ)) / 2 : ℝ) *
          ‖fderiv ℝ f (method (k + 1))‖[B,*] ^ (2 : ℕ) := by
    -- Complete the square for the new linear tilt on the displacement `v_{k+1} - v_k`.
    rw [hgradEval]
    simpa using
      (quadraticTiltLowerBound
        (method.a_pos k).le
        (fderiv ℝ f (method (k + 1)))
        (method.v (k + 1) - method.v k))
  -- Assemble the exact `ψ_{k+1}` split with the two scalar lower bounds.
  rw [psiSuccAtNext_split method k]
  linarith

omit [Fact B.toQuadraticMap.PosDef] in
private lemma gradientCovector_eq_fderivAt
    {z : PrimalSpace B} (hcont : ContDiffAt ℝ 2 f z) :
    (InnerProductSpace.toDual ℝ (PrimalSpace B)) (∇ f z) = fderiv ℝ f z := by
  -- The `C²` hypothesis gives the standard identification between the gradient covector and the
  -- Fréchet derivative.
  simpa using
    (((hcont.differentiableAt (by norm_num)).hasGradientAt.hasFDerivAt.fderiv).symm)

omit [Fact B.toQuadraticMap.PosDef] in
/-- Helper for Lemma 4.3.4: pairing the gradient with a vector is evaluation by the Fréchet
derivative at the same point. -/
private lemma gradientInner_eq_fderiv_apply
    (hf : primalSpaceMemC22 (B := B) (Mf := (Mf : NNReal)) f)
    (z x : PrimalSpace B) :
    inner ℝ (∇ f z) x = fderiv ℝ f z x := by
  have hcont : ContDiffAt ℝ 2 f z := hf.contDiff.contDiffAt
  -- Rewrite the gradient pairing through the canonical covector/derivative identification.
  calc
    inner ℝ (∇ f z) x
        = ((InnerProductSpace.toDual ℝ (PrimalSpace B)) (∇ f z)) x := by
            simp
    _ = fderiv ℝ f z x := by
          rw [gradientCovector_eq_fderivAt (f := f) hcont]

/-- Helper for Lemma 4.3.4: the stable interpolation identity rewrites the stage-`k` tangent term
into the canonical `x_k` and `v_k` contributions. -/
private lemma scaledInterpolationGapGradientEq
    (k : ℕ) :
    method.A (k + 1) * inner ℝ (∇ f (method (k + 1))) (method.y k - method (k + 1)) =
      method.A k * inner ℝ (∇ f (method (k + 1))) (method k - method (k + 1)) +
        method.a (k + 1) * inner ℝ (∇ f (method (k + 1))) (method.v k - method (k + 1)) := by
  have hA_pos : 0 < method.A (k + 1) := by
    rw [method.A_succ k]
    exact add_pos_of_nonneg_of_pos (method.A_nonneg k) (method.a_pos k)
  have hweighted :
      method.A (k + 1) • method.y k =
        method.A k • method k + method.a (k + 1) • method.v k := by
    rw [method.y_eq k]
    have hmul_x :
        method.A (k + 1) * (1 - method.a (k + 1) / method.A (k + 1)) = method.A k := by
      field_simp [hA_pos.ne']
      nlinarith [method.A_succ k]
    have hmul_v :
        method.A (k + 1) * (method.a (k + 1) / method.A (k + 1)) = method.a (k + 1) := by
      field_simp [hA_pos.ne']
    -- Expand the weighted interpolation point and simplify the two scalar coefficients.
    calc
      method.A (k + 1) •
          ((1 - method.a (k + 1) / method.A (k + 1)) • method k +
            (method.a (k + 1) / method.A (k + 1)) • method.v k)
          =
          (method.A (k + 1) * (1 - method.a (k + 1) / method.A (k + 1))) • method k +
            (method.A (k + 1) * (method.a (k + 1) / method.A (k + 1))) • method.v k := by
              simp [smul_add, smul_smul]
      _ = method.A k • method k + method.a (k + 1) • method.v k := by
            rw [hmul_x, hmul_v]
  have hvector :
      method.A (k + 1) • (method.y k - method (k + 1)) =
        method.A k • (method k - method (k + 1)) +
          method.a (k + 1) • (method.v k - method (k + 1)) := by
    -- Subtract the common weighted successor term and regroup the two coefficients.
    calc
      method.A (k + 1) • (method.y k - method (k + 1))
          = method.A (k + 1) • method.y k - method.A (k + 1) • method (k + 1) := by
              simp [smul_sub]
      _ = method.A k • method k + method.a (k + 1) • method.v k -
            method.A (k + 1) • method (k + 1) := by
              rw [hweighted]
      _ = method.A k • (method k - method (k + 1)) +
            method.a (k + 1) • (method.v k - method (k + 1)) := by
              rw [method.A_succ k, add_smul]
              simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  have hpair :=
    congrArg (fun z : PrimalSpace B ↦ inner ℝ (∇ f (method (k + 1))) z) hvector
  -- Pair the stable vector identity with the successor gradient.
  simpa [inner_add_right, inner_sub_right, inner_smul_right, smul_eq_mul, mul_assoc,
    mul_left_comm, mul_comm] using hpair

omit [Fact B.toQuadraticMap.PosDef] in
/-- Helper for Lemma 4.3.4: adding the covector `a • A d` shifts the canonical `A.dualPreimage`
by the corresponding primal vector `a • d`. -/
private lemma dualPreimageAddBilinSmul
    {A : BilinForm ℝ (PrimalSpace B)} [Fact A.toQuadraticMap.PosDef]
    (g : PrimalSpace B →L[ℝ] ℝ) (d : PrimalSpace B) (a : ℝ) :
    A.dualPreimage Fact.out (g.toLinearMap + a • A d) =
      A.dualPreimage Fact.out g.toLinearMap + a • d := by
  let hnd : A.Nondegenerate := A.nondegenerate_of_posDef Fact.out
  -- Evaluate both candidate preimages against `A` and use injectivity of `A.toDual`.
  apply (A.toDual hnd).injective
  ext u
  simp [LinearMap.BilinForm.dualPreimage, LinearMap.BilinForm.toDual_def, map_add, map_smul]

omit [Fact B.toQuadraticMap.PosDef] in
/-- Helper for Lemma 4.3.4: for a symmetric positive-definite form, the square of the dual norm
equals the self-pairing of the canonical dual preimage. -/
private lemma dualNormSqEqSelfPairing
    {A : BilinForm ℝ (PrimalSpace B)} [Fact A.toQuadraticMap.PosDef]
    (hSymm : A.IsSymm) (g : PrimalSpace B →L[ℝ] ℝ) :
    ‖g‖[A,*] ^ (2 : ℕ) = g (A.dualPreimage Fact.out g.toLinearMap) := by
  let hPos : A.toQuadraticMap.PosDef := Fact.out
  have hz_nonneg : 0 ≤ g (A.dualPreimage Fact.out g.toLinearMap) := by
    simpa using hPos.nonneg (A.dualPreimage Fact.out g.toLinearMap)
  -- Rewrite the dual norm by the `A.dualPreimage` formula and square the displayed root.
  calc
    ‖g‖[A,*] ^ (2 : ℕ) =
        (Real.sqrt (g (A.dualPreimage Fact.out g.toLinearMap))) ^ (2 : ℕ) := by
          rw [LinearMap.BilinForm.dualNorm_apply_strongDual A hSymm Fact.out g]
    _ = g (A.dualPreimage Fact.out g.toLinearMap) := by
          simp [hz_nonneg]

omit [Fact B.toQuadraticMap.PosDef] in
/-- Helper for Lemma 4.3.4: on a symmetric positive-definite surface, the square of the shifted
dual norm expands quadratically in the shift coefficient. -/
private lemma shiftedDualNormSqEq
    {A : BilinForm ℝ (PrimalSpace B)} [Fact A.toQuadraticMap.PosDef]
    (hSymm : A.IsSymm) (g : PrimalSpace B →L[ℝ] ℝ) (d : PrimalSpace B) (a : ℝ) :
    ‖g + a • bilinCovector A d‖[A,*] ^ (2 : ℕ) =
      ‖g‖[A,*] ^ (2 : ℕ) + 2 * a * g d + a ^ (2 : ℕ) * ‖d‖[A] ^ (2 : ℕ) := by
  let r : ℝ := ‖d‖[A]
  let u : PrimalSpace B := A.dualPreimage Fact.out g.toLinearMap
  let shift : PrimalSpace B →L[ℝ] ℝ := g + a • bilinCovector A d
  have hnormSq : r ^ (2 : ℕ) = A d d := by
    dsimp [r]
    rw [LinearMap.BilinForm.primalSeminorm_apply]
    have hA_nonneg : 0 ≤ (A d) d := by
      change 0 ≤ A.toQuadraticMap d
      exact QuadraticMap.PosDef.nonneg Fact.out d
    simpa [pow_two] using (Real.sq_sqrt hA_nonneg)
  have hpairG : ‖g‖[A,*] ^ (2 : ℕ) = A u u := by
    simpa [u] using dualNormSqEqSelfPairing (B := B) hSymm g
  have hpairShift :
      ‖shift‖[A,*] ^ (2 : ℕ) = shift (A.dualPreimage Fact.out shift.toLinearMap) := by
    exact dualNormSqEqSelfPairing (B := B) hSymm shift
  have hpreimage :
      A.dualPreimage Fact.out shift.toLinearMap = u + a • d := by
    simpa [u, shift] using dualPreimageAddBilinSmul (B := B) g d a
  have hud : A u d = g d := by
    simpa only [u] using A.dualPreimage_apply Fact.out g.toLinearMap d
  have hdu : A d u = g d := by
    rw [hSymm.eq d u, hud]
  have hdd : A d d = ‖d‖[A] ^ (2 : ℕ) := by
    exact hnormSq.symm
  have hgu :
      g (u + a • d) = A u (u + a • d) := by
    simpa only [u] using (A.dualPreimage_apply Fact.out g.toLinearMap (u + a • d)).symm
  calc
    ‖g + a • bilinCovector A d‖[A,*] ^ (2 : ℕ) = ‖shift‖[A,*] ^ (2 : ℕ) := by
      rfl
    _ = shift (A.dualPreimage Fact.out shift.toLinearMap) := hpairShift
    _ = shift (u + a • d) := by
          rw [hpreimage]
    _ = g (u + a • d) + a * (bilinCovector A d) (u + a • d) := by
          simp [shift]
    _ = A u (u + a • d) + a * A d (u + a • d) := by
          rw [hgu]
          simp [bilinCovector]
    _ = A u u + a * A u d + (a * A d u + a ^ (2 : ℕ) * A d d) := by
          rw [(A u).map_add, (A d).map_add, (A u).map_smul, (A d).map_smul]
          ring
    _ = A u u + 2 * a * g d + a ^ (2 : ℕ) * ‖d‖[A] ^ (2 : ℕ) := by
          rw [hud, hdu, hdd]
          ring
    _ = ‖g‖[A,*] ^ (2 : ℕ) + 2 * a * g d + a ^ (2 : ℕ) * ‖d‖[A] ^ (2 : ℕ) := by
          rw [hpairG]

omit [Fact B.toQuadraticMap.PosDef] in
/-- Helper for Lemma 4.3.4: if the `A`-radius of the displacement vanishes, positive
definiteness forces `d = 0`, so the lower bound degenerates to the trivial identity `0 ≥ 0`. -/
private lemma dualPairingLowerBoundOfDualShiftBoundZero
    {A : BilinForm ℝ (PrimalSpace B)} [Fact A.toQuadraticMap.PosDef]
    {M Mf : ℝ}
    (d : PrimalSpace B) (g : PrimalSpace B →L[ℝ] ℝ)
    (hd0 : ‖d‖[A] = 0) :
    g (-d) ≥
      (1 / (M * ‖d‖[A])) * ‖g‖[A,*] ^ (2 : ℕ) +
        ((M ^ (2 : ℕ) - Mf ^ (2 : ℕ)) / (4 * M)) * ‖d‖[A] ^ (3 : ℕ) := by
  -- Vanishing `A`-radius forces `d = 0`, so every term in the target inequality collapses.
  have hd : d = 0 := by
    rw [LinearMap.BilinForm.primalSeminorm_apply] at hd0
    have hA_nonneg : 0 ≤ (A d) d := by
      change 0 ≤ A.toQuadraticMap d
      exact QuadraticMap.PosDef.nonneg Fact.out d
    have hsq0 : (Real.sqrt ((A d) d)) ^ (2 : ℕ) = 0 := by
      rw [hd0]
      norm_num
    have hddZero : (A d) d = 0 := by
      calc
        (A d) d = (Real.sqrt ((A d) d)) ^ (2 : ℕ) := by
          symm
          simpa [pow_two] using (Real.sq_sqrt hA_nonneg)
        _ = 0 := hsq0
    exact (QuadraticMap.PosDef.anisotropic Fact.out d) <| by
      change A.toQuadraticMap d = 0
      simpa using hddZero
  simp [hd]

omit [Fact B.toQuadraticMap.PosDef] in
/-- Helper for Lemma 4.3.4: in the positive-radius branch, squaring the shifted dual estimate and
expanding the `A.dualPreimage` expression yields the full algebraic lower bound. -/
private lemma dualPairingLowerBoundOfDualShiftBoundPos
    {A : BilinForm ℝ (PrimalSpace B)} [Fact A.toQuadraticMap.PosDef]
    (hSymm : A.IsSymm) {M Mf : ℝ} (hM : 0 < M)
    (d : PrimalSpace B) (g : PrimalSpace B →L[ℝ] ℝ)
    (hd_pos : 0 < ‖d‖[A])
    (hshift :
      ‖g + (((M / 2 : ℝ) * ‖d‖[A]) • bilinCovector A d)‖[A,*] ≤
        ((Mf : ℝ) / 2) * ‖d‖[A] ^ (2 : ℕ)) :
    g (-d) ≥
      (1 / (M * ‖d‖[A])) * ‖g‖[A,*] ^ (2 : ℕ) +
        ((M ^ (2 : ℕ) - Mf ^ (2 : ℕ)) / (4 * M)) * ‖d‖[A] ^ (3 : ℕ) := by
  let r : ℝ := ‖d‖[A]
  let a : ℝ := ((M / 2 : ℝ) * r)
  let shift : PrimalSpace B →L[ℝ] ℝ := g + a • bilinCovector A d
  have hshift_nonneg : 0 ≤ ‖shift‖[A,*] := by
    rw [LinearMap.BilinForm.dualNorm_apply_strongDual A hSymm Fact.out shift]
    exact Real.sqrt_nonneg _
  have hshift_rhs_nonneg : 0 ≤ ((Mf : ℝ) / 2) * r ^ (2 : ℕ) := by
    exact le_trans hshift_nonneg <| by
      simpa [r, a, shift] using hshift
  have hsq :
      ‖shift‖[A,*] ^ (2 : ℕ) ≤
        (((Mf : ℝ) / 2) * r ^ (2 : ℕ)) ^ (2 : ℕ) := by
    exact (sq_le_sq₀ hshift_nonneg hshift_rhs_nonneg).2 <| by
      simpa [r, a, shift] using hshift
  have hleft_expand :
      ‖shift‖[A,*] ^ (2 : ℕ) =
        ‖g‖[A,*] ^ (2 : ℕ) + M * r * g d +
          (M ^ (2 : ℕ) / 4) * r ^ (4 : ℕ) := by
    -- Reuse the standalone quadratic expansion for the shifted dual norm.
    calc
      ‖shift‖[A,*] ^ (2 : ℕ) = ‖g + a • bilinCovector A d‖[A,*] ^ (2 : ℕ) := by
            rfl
      _ = ‖g‖[A,*] ^ (2 : ℕ) + 2 * a * g d + a ^ (2 : ℕ) * ‖d‖[A] ^ (2 : ℕ) := by
            exact shiftedDualNormSqEq (B := B) hSymm g d a
      _ = ‖g‖[A,*] ^ (2 : ℕ) + M * r * g d +
            (M ^ (2 : ℕ) / 4) * r ^ (4 : ℕ) := by
            dsimp [a, r]
            ring
  have hrhs_sq :
      (((Mf : ℝ) / 2) * r ^ (2 : ℕ)) ^ (2 : ℕ) =
        ((Mf ^ (2 : ℕ)) / 4) * r ^ (4 : ℕ) := by
    ring_nf
  have hbound :
      ‖g‖[A,*] ^ (2 : ℕ) + M * r * g d +
          (M ^ (2 : ℕ) / 4) * r ^ (4 : ℕ) ≤
        ((Mf ^ (2 : ℕ)) / 4) * r ^ (4 : ℕ) := by
    rw [hleft_expand, hrhs_sq] at hsq
    exact hsq
  have hbound' :
      ‖g‖[A,*] ^ (2 : ℕ) + M * r * g d ≤
        ((Mf ^ (2 : ℕ) - M ^ (2 : ℕ)) / 4) * r ^ (4 : ℕ) := by
    nlinarith [hbound]
  have hnum :
      M * r * g (-d) ≥
        ‖g‖[A,*] ^ (2 : ℕ) +
          ((M ^ (2 : ℕ) - Mf ^ (2 : ℕ)) / 4) * r ^ (4 : ℕ) := by
    -- Move the cross term to the target side and rewrite it through `g (-d) = -g d`.
    have hneg : g (-d) = -g d := by
      simp
    rw [hneg]
    nlinarith [hbound']
  have hMr_pos : 0 < M * r := by
    dsimp [r]
    exact mul_pos hM hd_pos
  have hquot :
      (‖g‖[A,*] ^ (2 : ℕ) +
          ((M ^ (2 : ℕ) - Mf ^ (2 : ℕ)) / 4) * r ^ (4 : ℕ)) / (M * r) ≤
        g (-d) := by
    apply (div_le_iff₀ hMr_pos).2
    simpa [mul_comm, mul_left_comm, mul_assoc] using hnum
  have hrepr :
      (‖g‖[A,*] ^ (2 : ℕ) +
          ((M ^ (2 : ℕ) - Mf ^ (2 : ℕ)) / 4) * r ^ (4 : ℕ)) / (M * r) =
        (1 / (M * r)) * ‖g‖[A,*] ^ (2 : ℕ) +
          ((M ^ (2 : ℕ) - Mf ^ (2 : ℕ)) / (4 * M)) * r ^ (3 : ℕ) := by
    field_simp [hM.ne', hd_pos.ne']
  rw [← hrepr]
  exact hquot

omit [Fact B.toQuadraticMap.PosDef] in
/-- Helper for Lemma 4.3.4: a shifted covector bound on a symmetric positive-definite surface
implies the source lower bound on the dual pairing with the step displacement. -/
private lemma dualPairingLowerBoundOfDualShiftBound
    {A : BilinForm ℝ (PrimalSpace B)} [Fact A.toQuadraticMap.PosDef]
    (hSymm : A.IsSymm) {M Mf : ℝ} (hM : 0 < M)
    (d : PrimalSpace B) (g : PrimalSpace B →L[ℝ] ℝ)
    (hshift :
      ‖g + (((M / 2 : ℝ) * ‖d‖[A]) • bilinCovector A d)‖[A,*] ≤
        ((Mf : ℝ) / 2) * ‖d‖[A] ^ (2 : ℕ)) :
    g (-d) ≥
      (1 / (M * ‖d‖[A])) * ‖g‖[A,*] ^ (2 : ℕ) +
        ((M ^ (2 : ℕ) - Mf ^ (2 : ℕ)) / (4 * M)) * ‖d‖[A] ^ (3 : ℕ) := by
  by_cases hd0 : ‖d‖[A] = 0
  · -- The zero-radius branch collapses to the trivial identity after positivity forces `d = 0`.
    exact dualPairingLowerBoundOfDualShiftBoundZero (B := B) d g hd0
  · have hd_nonneg : 0 ≤ ‖d‖[A] := by
      rw [LinearMap.BilinForm.primalSeminorm_apply]
      exact Real.sqrt_nonneg _
    have hd_pos : 0 < ‖d‖[A] := lt_of_le_of_ne hd_nonneg (Ne.symm hd0)
    -- In the positive-radius branch, reuse the already-expanded algebraic estimate verbatim.
    exact dualPairingLowerBoundOfDualShiftBoundPos (B := B) hSymm hM d g hd_pos hshift

/-- Helper for Lemma 4.3.4: the coefficient from Lemma 4.3.3 dominates the sigma-dependent cubic
coefficient once `method.M ≥ Mf / sigma` with `sigma ∈ (0, 1]`. -/
private lemma sigmaCubicCoefficientLowerBound
    {M σ : ℝ}
    (hσ : σ ∈ Set.Ioc (0 : ℝ) 1)
    (hMσ : M ≥ (1 / σ) * (Mf : ℝ))
    (hM : 0 < M) :
    ((1 - σ ^ (2 : ℕ)) / 4 : ℝ) * M ≤
      (M ^ (2 : ℕ) - (Mf : ℝ) ^ (2 : ℕ)) / (4 * M) := by
  have hσ_pos : 0 < σ := hσ.1
  have hσ_ne : σ ≠ 0 := ne_of_gt hσ_pos
  have hMf_le : (Mf : ℝ) ≤ σ * M := by
    have hσ_mul :=
      mul_le_mul_of_nonneg_left hMσ hσ_pos.le
    calc
      (Mf : ℝ) = σ * ((1 / σ) * (Mf : ℝ)) := by
        field_simp [hσ_ne]
      _ ≤ σ * M := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hσ_mul
  have hsq : (Mf : ℝ) ^ (2 : ℕ) ≤ σ ^ (2 : ℕ) * M ^ (2 : ℕ) := by
    nlinarith
  field_simp [hM.ne']
  nlinarith

/-- Helper for Lemma 4.3.4: every cubic-step residual is nonnegative because it is a `B`-norm of
the step displacement. -/
private lemma residualNonneg
    {M : ℝ} (step : CubicNewtonStep B f M) (x : PrimalSpace B) :
    0 ≤ r[step](x) := by
  -- Unfold the residual to the displacement norm and use norm nonnegativity.
  rw [CubicNewtonStep.residual_apply]
  positivity

/-- Helper for Lemma 4.3.4: on `PrimalSpace B`, the associated-form residual rewrite stays in the
single intrinsic spelling needed by the zero-residual branch. -/
private lemma associatedStepResidualNormEq
    {M : ℝ} (step : CubicNewtonStep B f M) (x : PrimalSpace B) :
    ‖step x - x‖[B.toQuadraticMap.associated] = r[step](x) := by
  -- Rewrite the associated norm back to the source `B`-norm before unfolding the residual.
  rw [associatedPrimalNormEq (step x - x), CubicNewtonStep.residual_apply]

/-- Helper for Lemma 4.3.4: finite dimensionality on `E` transfers to the intrinsic carrier
`PrimalSpace B`, so later norm bridges do not need repeated local instance search. -/
private instance primalSpaceFiniteDimensional :
    FiniteDimensional ℝ (PrimalSpace B) := by
  -- The intrinsic carrier is definitionally the same finite-dimensional vector space.
  change FiniteDimensional ℝ E
  infer_instance

/-- Helper for Lemma 4.3.4: finite dimensionality makes the `B`-induced primal space complete,
so the Banach-valued FTC lemmas can stay on the intrinsic carrier. -/
private instance primalSpaceCompleteSpace :
    CompleteSpace (PrimalSpace B) := by
  -- Use the inherited complete-space structure instead of rebuilding it in each lemma.
  infer_instance

section GenericFderivRemainder

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable {L3 : NNReal} {g : X → ℝ}

omit [CompleteSpace X] in
/-- Helper for Lemma 4.3.4: on any real normed space, the affine segment `s ↦ x + s • d` has
derivative `d`. -/
private lemma genericLine_hasDerivAt
    (x d : X) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ x + s • d) d t := by
  -- Differentiate the scalar multiple and then translate by the base point.
  simpa [one_smul] using ((hasDerivAt_id t).smul_const d).const_add x

omit [CompleteSpace X] in
/-- Helper for Lemma 4.3.4: the affine segment of the Fréchet derivative integrates to the exact
first-order increment of `fderiv ℝ g`. -/
private lemma segment_fderiv_integral_eq_generic
    (hg : g ∈ C22[L3])
    (x d : X) :
    fderiv ℝ g (x + d) - fderiv ℝ g x =
      ∫ t in 0..1, fderiv ℝ (fderiv ℝ g) (x + t • d) d := by
  have hderiv :
      ∀ t ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun s : ℝ ↦ fderiv ℝ g (x + s • d))
          (fderiv ℝ (fderiv ℝ g) (x + t • d) d) t := by
    intro t ht
    have hcontAt : ContDiffAt ℝ 1 (fderiv ℝ g) (x + t • d) :=
      (hg.contDiff.contDiffAt (x := x + t • d)).fderiv_right
        (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))
    -- Differentiate the derivative field after restricting it to the affine segment.
    simpa [Function.comp] using
      hcontAt.differentiableAt one_ne_zero |>.hasFDerivAt.comp_hasDerivAt t
        (genericLine_hasDerivAt x d t)
  have hcont :
      Continuous (fun t : ℝ ↦ fderiv ℝ (fderiv ℝ g) (x + t • d) d) := by
    have hcontFDeriv :
        Continuous (fun t : ℝ ↦ fderiv ℝ (fderiv ℝ g) (x + t • d)) :=
      hg.sndFDeriv_lipschitz.continuous.comp
        (continuous_const.add (continuous_id.smul continuous_const))
    exact hcontFDeriv.clm_apply continuous_const
  have hint :
      IntervalIntegrable (fun t : ℝ ↦ fderiv ℝ (fderiv ℝ g) (x + t • d) d)
        MeasureTheory.volume 0 1 :=
    hcont.intervalIntegrable 0 1
  -- Apply Banach-valued FTC to the derivative field on the segment.
  symm
  simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

omit [CompleteSpace X] in
/-- Helper for Lemma 4.3.4: the Hessian-Lipschitz owner estimate controls the action of the
second Fréchet derivative increment along a segment direction. -/
private lemma segment_sndFDeriv_action_bound_generic
    (hg : g ∈ C22[L3])
    (x d : X)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖(fderiv ℝ (fderiv ℝ g) (x + t • d) - fderiv ℝ (fderiv ℝ g) x) d‖
      ≤ (L3 : ℝ) * t * ‖d‖ ^ (2 : ℕ) := by
  have hnorm :
      ‖fderiv ℝ (fderiv ℝ g) (x + t • d) - fderiv ℝ (fderiv ℝ g) x‖
        ≤ (L3 : ℝ) * ‖t • d‖ := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      HasLipschitzContinuousHessian.sndFDeriv_norm_sub_le hg (x + t • d) x
  -- Convert the operator-norm bound into an action bound on the displacement vector.
  calc
    ‖(fderiv ℝ (fderiv ℝ g) (x + t • d) - fderiv ℝ (fderiv ℝ g) x) d‖
      ≤ ‖fderiv ℝ (fderiv ℝ g) (x + t • d) - fderiv ℝ (fderiv ℝ g) x‖ * ‖d‖ := by
          exact ContinuousLinearMap.le_opNorm _ _
    _ ≤ ((L3 : ℝ) * ‖t • d‖) * ‖d‖ := by
          gcongr
    _ = ((L3 : ℝ) * (t * ‖d‖)) * ‖d‖ := by
          rw [norm_smul, Real.norm_of_nonneg ht.1]
    _ = (L3 : ℝ) * t * ‖d‖ ^ (2 : ℕ) := by
          ring

namespace HasLipschitzContinuousHessian

omit [CompleteSpace X] in
/-- Helper for Lemma 4.3.4: on a complete real normed space, the first-order Taylor remainder of
`fderiv ℝ g` is controlled by the global Lipschitz constant of `x ↦ D²g(x)`. -/
private lemma fderivRemainderNorm_le
    (hg : g ∈ C22[L3])
    (x y : X) :
    ‖fderiv ℝ g y - fderiv ℝ g x - fderiv ℝ (fderiv ℝ g) x (y - x)‖ ≤
      ((L3 : ℝ) / 2) * ‖y - x‖ ^ (2 : ℕ) := by
  let d : X := y - x
  have hy : x + d = y := by
    simp [d]
  have hcontIntegrand :
      Continuous (fun t : ℝ ↦
        (fderiv ℝ (fderiv ℝ g) (x + t • d) - fderiv ℝ (fderiv ℝ g) x) d) := by
    have hcontFDeriv :
        Continuous (fun t : ℝ ↦
          fderiv ℝ (fderiv ℝ g) (x + t • d) - fderiv ℝ (fderiv ℝ g) x) :=
      (hg.sndFDeriv_lipschitz.continuous.comp
        (continuous_const.add (continuous_id.smul continuous_const))).sub continuous_const
    exact hcontFDeriv.clm_apply continuous_const
  have hintIntegrand :
      IntervalIntegrable
        (fun t : ℝ ↦
          (fderiv ℝ (fderiv ℝ g) (x + t • d) - fderiv ℝ (fderiv ℝ g) x) d)
        MeasureTheory.volume 0 1 :=
    hcontIntegrand.intervalIntegrable 0 1
  have hintBound :
      IntervalIntegrable (fun t : ℝ ↦ (L3 : ℝ) * t * ‖d‖ ^ (2 : ℕ))
        MeasureTheory.volume 0 1 :=
    ((continuous_const.mul continuous_id).mul continuous_const).intervalIntegrable 0 1
  have hmono :
      ∫ t in 0..1,
          ‖(fderiv ℝ (fderiv ℝ g) (x + t • d) - fderiv ℝ (fderiv ℝ g) x) d‖
        ≤ ∫ t in 0..1, (L3 : ℝ) * t * ‖d‖ ^ (2 : ℕ) := by
    -- Bound the Banach-valued integrand pointwise on the whole segment.
    refine intervalIntegral.integral_mono_on (show (0 : ℝ) ≤ 1 by norm_num)
      hintIntegrand.norm hintBound ?_
    intro t ht
    exact segment_sndFDeriv_action_bound_generic (hg := hg) (x := x) (d := d) ht
  have hrewrite :
      fderiv ℝ g y - fderiv ℝ g x - fderiv ℝ (fderiv ℝ g) x d =
        ∫ t in 0..1,
          (fderiv ℝ (fderiv ℝ g) (x + t • d) - fderiv ℝ (fderiv ℝ g) x) d := by
    -- Rewrite the remainder as an integral of second-derivative differences.
    rw [← hy, segment_fderiv_integral_eq_generic (hg := hg) (x := x) (d := d)]
    have hconst :
        fderiv ℝ (fderiv ℝ g) x d =
          ∫ t in 0..1, fderiv ℝ (fderiv ℝ g) x d := by
      simp
    rw [hconst]
    have hsub0 :
        ∫ t in 0..1, fderiv ℝ (fderiv ℝ g) (x + t • d) d - fderiv ℝ (fderiv ℝ g) x d =
          (∫ t in 0..1, fderiv ℝ (fderiv ℝ g) (x + t • d) d) -
            ∫ t in 0..1, fderiv ℝ (fderiv ℝ g) x d := by
      simpa using
        (intervalIntegral.integral_sub
          (f := fun t : ℝ ↦ fderiv ℝ (fderiv ℝ g) (x + t • d) d)
          (g := fun _ : ℝ ↦ fderiv ℝ (fderiv ℝ g) x d)
          (μ := MeasureTheory.volume)
          (((hg.sndFDeriv_lipschitz.continuous.comp
              (continuous_const.add (continuous_id.smul continuous_const))).clm_apply
                continuous_const).intervalIntegrable 0 1)
          (continuous_const.intervalIntegrable 0 1))
    have hsub :
        (∫ t in 0..1, fderiv ℝ (fderiv ℝ g) (x + t • d) d) -
            ∫ t in 0..1, fderiv ℝ (fderiv ℝ g) x d =
          ∫ t in 0..1, fderiv ℝ (fderiv ℝ g) (x + t • d) d -
            fderiv ℝ (fderiv ℝ g) x d := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsub0.symm
    calc
      (∫ t in 0..1, fderiv ℝ (fderiv ℝ g) (x + t • d) d) -
          ∫ t in 0..1, fderiv ℝ (fderiv ℝ g) x d =
        ∫ t in 0..1, fderiv ℝ (fderiv ℝ g) (x + t • d) d -
          fderiv ℝ (fderiv ℝ g) x d := hsub
      _ = ∫ t in 0..1,
            (fderiv ℝ (fderiv ℝ g) (x + t • d) - fderiv ℝ (fderiv ℝ g) x) d := by
            refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall ?_)
            intro t ht
            simp
  -- Integrate the pointwise second-derivative bound and compute `∫₀¹ t = 1 / 2`.
  simpa [d] using
    calc
      ‖fderiv ℝ g y - fderiv ℝ g x - fderiv ℝ (fderiv ℝ g) x d‖
        = ‖∫ t in 0..1,
            (fderiv ℝ (fderiv ℝ g) (x + t • d) - fderiv ℝ (fderiv ℝ g) x) d‖ := by
              rw [hrewrite]
      _ ≤ ∫ t in 0..1,
            ‖(fderiv ℝ (fderiv ℝ g) (x + t • d) - fderiv ℝ (fderiv ℝ g) x) d‖ := by
              exact intervalIntegral.norm_integral_le_integral_norm
                (f := fun t : ℝ ↦
                  (fderiv ℝ (fderiv ℝ g) (x + t • d) - fderiv ℝ (fderiv ℝ g) x) d)
                (a := (0 : ℝ)) (b := 1) (show (0 : ℝ) ≤ 1 by norm_num)
      _ ≤ ∫ t in 0..1, (L3 : ℝ) * t * ‖d‖ ^ (2 : ℕ) := hmono
      _ = ((L3 : ℝ) / 2) * ‖d‖ ^ (2 : ℕ) := by
            calc
              ∫ t in 0..1, (L3 : ℝ) * t * ‖d‖ ^ (2 : ℕ)
                = ∫ t in 0..1, ((L3 : ℝ) * ‖d‖ ^ (2 : ℕ)) * t := by
                    congr with t
                    ring
              _ = ((L3 : ℝ) * ‖d‖ ^ (2 : ℕ)) * (1 / 2 : ℝ) := by
                    rw [intervalIntegral.integral_const_mul, integral_id]
                    norm_num
              _ = ((L3 : ℝ) / 2) * ‖d‖ ^ (2 : ℕ) := by
                    ring

end HasLipschitzContinuousHessian

end GenericFderivRemainder

/-- Helper for Lemma 4.3.4: on `PrimalSpace B`, the associated dual norm agrees with the source
`B`-dual norm because both dual unit balls are cut out by the same primal norm. -/
private lemma associatedDualNormEqOnPrimalSpace
    (g : PrimalSpace B →L[ℝ] ℝ) :
    ‖g‖[B.toQuadraticMap.associated,*] = ‖g‖[B,*] := by
  -- Rewrite both dual norms onto the same support-function set cut out by the primal unit ball.
  rw [LinearMap.BilinForm.dualNorm_eq_sSup_primalUnitBall_strongDual,
    LinearMap.BilinForm.dualNorm_eq_sSup_primalUnitBall_strongDual]
  congr 1
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hzA : ‖z‖[B.toQuadraticMap.associated] ≤ 1 := by
      simpa using hz
    have hzB : ‖z‖[B] ≤ 1 := by
      rwa [associatedPrimalNormEq (B := B) z] at hzA
    exact ⟨z, by
      simpa using hzB, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    have hzB : ‖z‖[B] ≤ 1 := by
      simpa using hz
    have hzA : ‖z‖[B.toQuadraticMap.associated] ≤ 1 := by
      rwa [associatedPrimalNormEq (B := B) z]
    exact ⟨z, by
      simpa using hzA, rfl⟩

omit [Fact B.toQuadraticMap.PosDef] in
/-- Helper for Lemma 4.3.4: the Riesz map identifies a primal vector on `PrimalSpace B` with the
corresponding continuous covector. -/
private def primalToStrongDualMap :
    PrimalSpace B →L[ℝ] StrongDual ℝ (PrimalSpace B) :=
  (InnerProductSpace.toDual ℝ (PrimalSpace B)).toContinuousLinearEquiv.toContinuousLinearMap

omit [Fact B.toQuadraticMap.PosDef] in
/-- Helper for Lemma 4.3.4: the inverse Riesz map sends a continuous covector on `PrimalSpace B`
to its representing primal vector. -/
private def strongDualToPrimalMap :
    StrongDual ℝ (PrimalSpace B) →L[ℝ] PrimalSpace B :=
  (InnerProductSpace.toDual ℝ (PrimalSpace B)).symm.toContinuousLinearEquiv.toContinuousLinearMap

omit [Fact B.toQuadraticMap.PosDef] in
/-- Helper for Lemma 4.3.4: on `PrimalSpace B`, the second Fréchet derivative is the Hessian
transported through the Riesz map. -/
private lemma sndFDeriv_eq_toDual_comp_hessian_onPrimalSpace
    {x : PrimalSpace B} (hcont : ContDiffAt ℝ 2 f x) :
    fderiv ℝ (fderiv ℝ f) x = primalToStrongDualMap.comp (hessian f x) := by
  have hfdiff : DifferentiableAt ℝ (fderiv ℝ f) x := by
    have hfderiv : ContDiffAt ℝ 1 (fderiv ℝ f) x :=
      hcont.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))
    exact hfderiv.differentiableAt one_ne_zero
  have hhess :
      hessian f x = strongDualToPrimalMap.comp (fderiv ℝ (fderiv ℝ f) x) := by
    -- Route correction: fix the operator-level Riesz transport once before evaluating at `d`.
    simpa [gradient, hessian, strongDualToPrimalMap] using
      fderiv_comp x strongDualToPrimalMap.differentiableAt hfdiff
  -- Compare the two operators pointwise after evaluating them on the same direction.
  ext d u
  have happly : hessian f x d = strongDualToPrimalMap (fderiv ℝ (fderiv ℝ f) x d) := by
    simpa [ContinuousLinearMap.comp_apply] using congrArg (fun T => T d) hhess
  have hdual :
      strongDualToPrimalMap (fderiv ℝ (fderiv ℝ f) x d) =
        (InnerProductSpace.toDual ℝ (PrimalSpace B)).symm (fderiv ℝ (fderiv ℝ f) x d) := by
    rfl
  calc
    (fderiv ℝ (fderiv ℝ f) x d) u
        = (InnerProductSpace.toDual ℝ (PrimalSpace B))
            ((InnerProductSpace.toDual ℝ (PrimalSpace B)).symm
              (fderiv ℝ (fderiv ℝ f) x d)) u := by
              simp
    _ = (InnerProductSpace.toDual ℝ (PrimalSpace B))
          (strongDualToPrimalMap (fderiv ℝ (fderiv ℝ f) x d)) u := by
            rw [hdual]
    _ = (InnerProductSpace.toDual ℝ (PrimalSpace B)) (hessian f x d) u := by
          rw [happly]
    _ = ((primalToStrongDualMap.comp (hessian f x)) d) u := by
          rfl

omit [Fact B.toQuadraticMap.PosDef] in
/-- Helper for Lemma 4.3.4: evaluating the operator-level Riesz bridge recovers the Hessian
covector as the applied second Fréchet derivative. -/
private lemma hessianCovector_eq_sndFDeriv_apply
    {x d : PrimalSpace B} (hcont : ContDiffAt ℝ 2 f x) :
    (InnerProductSpace.toDual ℝ (PrimalSpace B)) (hessian f x d) =
      fderiv ℝ (fderiv ℝ f) x d := by
  -- Evaluate the operator bridge at the same displacement direction on both sides.
  simpa [ContinuousLinearMap.comp_apply] using
    congrArg (fun T => T d)
      (sndFDeriv_eq_toDual_comp_hessian_onPrimalSpace (f := f) hcont).symm


/-- Helper for Lemma 4.3.4: on an arbitrary cubic-step surface, the associated first-order
optimality identity rewrites directly to the first-order Taylor remainder of `fderiv ℝ f`. -/
private lemma associatedShiftEqFderivRemainderAtStep
    {M : ℝ} (step : CubicNewtonStep B f M) (x : PrimalSpace B)
    (hcont : ContDiffAt ℝ 2 f x) :
    (fderiv ℝ f (step x) : PrimalSpace B →L[ℝ] ℝ) +
        (((M / 2 : ℝ) * r[step](x)) •
          bilinCovector (B.toQuadraticMap.associated) (step x - x)) =
      fderiv ℝ f (step x) - fderiv ℝ f x -
        fderiv ℝ (fderiv ℝ f) x (step x - x) := by
  let d : PrimalSpace B := step x - x
  have hSymm :
      BilinForm.IsSymm (B.toQuadraticMap.associated : BilinForm ℝ (PrimalSpace B)) := by
    -- The associated bilinear form is symmetric by construction.
    exact ⟨QuadraticMap.associated_isSymm ℝ B.toQuadraticMap⟩
  have hgrad :
      (InnerProductSpace.toDual ℝ (PrimalSpace B)) (∇ f x) = fderiv ℝ f x :=
    gradientCovector_eq_fderivAt (f := f) hcont
  have hhess :
      (InnerProductSpace.toDual ℝ (PrimalSpace B)) (hessian f x d) =
        fderiv ℝ (fderiv ℝ f) x d := by
    -- Rewrite the Hessian covector to the applied second Fréchet derivative once at `d`.
    exact hessianCovector_eq_sndFDeriv_apply (f := f) (d := d) hcont
  have hopt :
      (InnerProductSpace.toDual ℝ (PrimalSpace B)) (∇ f x + hessian f x d) +
          (((M / 2 : ℝ) * r[step](x)) •
            bilinCovector (B.toQuadraticMap.associated) d) = 0 := by
    -- Route correction: consume first-order optimality only on the generic step surface `step x`.
    simpa [d, bilinCovector, associatedStepResidualNormEq step x] using
      CubicNewtonStep.firstOrderOptimalityCondition_toDual
        (B := B.toQuadraticMap.associated) (f := f) (M := M)
        (step := associatedCubicNewtonStep step) (x := x) hSymm hcont
  have hopt' :
      fderiv ℝ f x + fderiv ℝ (fderiv ℝ f) x d +
          (((M / 2 : ℝ) * r[step](x)) •
            bilinCovector (B.toQuadraticMap.associated) d) = 0 := by
    -- Rewrite the transported optimality identity from gradients/Hessians to `fderiv`.
    simpa [map_add, hgrad, hhess] using hopt
  have hshift :
      (((M / 2 : ℝ) * r[step](x)) • bilinCovector (B.toQuadraticMap.associated) d) =
        -(fderiv ℝ f x + fderiv ℝ (fderiv ℝ f) x d) := by
    -- Solve the stationarity identity for the explicit associated covector shift.
    exact eq_neg_of_add_eq_zero_right hopt'
  -- Add `fderiv ℝ f (step x)` to the solved shift relation and flatten the additive spelling.
  calc
    (fderiv ℝ f (step x) : PrimalSpace B →L[ℝ] ℝ) +
        (((M / 2 : ℝ) * r[step](x)) • bilinCovector (B.toQuadraticMap.associated) d)
      = fderiv ℝ f (step x) + (-(fderiv ℝ f x + fderiv ℝ (fderiv ℝ f) x d)) := by
          rw [hshift]
    _ = fderiv ℝ f (step x) - fderiv ℝ f x - fderiv ℝ (fderiv ℝ f) x d := by
          abel_nf

/-- Helper for Lemma 4.3.4: zero residual at `y_k` forces the step to stay at `y_k`, so the
successor derivative vanishes by first-order optimality. -/
private lemma zeroResidualStepEqInterpolationPoint
    (k : ℕ)
    (hr : r[(method.step)] (method.y k) = 0) :
    method (k + 1) = method.y k := by
  have hnorm : ‖method (k + 1) - method.y k‖[B] = 0 := by
    -- Rewrite the residual through the successor step formula.
    simpa [method.x_succ] using hr
  have hdisp : method (k + 1) - method.y k = 0 := by
    rw [LinearMap.BilinForm.primalSeminorm_apply] at hnorm
    have hquad_nonneg : 0 ≤ B (method (k + 1) - method.y k) (method (k + 1) - method.y k) := by
      change 0 ≤ B.toQuadraticMap (method (k + 1) - method.y k)
      exact QuadraticMap.PosDef.nonneg Fact.out _
    have hquad_zero : B (method (k + 1) - method.y k) (method (k + 1) - method.y k) = 0 := by
      exact (Real.sqrt_eq_zero hquad_nonneg).mp (by simpa using hnorm)
    -- Positive definiteness turns the zero quadratic value into zero displacement.
    exact (QuadraticMap.PosDef.anisotropic Fact.out (method (k + 1) - method.y k)) <| by
      change B.toQuadraticMap (method (k + 1) - method.y k) = 0
      simpa using hquad_zero
  exact sub_eq_zero.mp hdisp

/-- Helper for Lemma 4.3.4: zero residual at `y_k` forces the step to stay at `y_k`, so the
successor derivative vanishes by first-order optimality. -/
private lemma fderiv_eq_zero_of_residual_eq_zero
    (hf : primalSpaceMemC22 (B := B) (Mf := (Mf : NNReal)) f)
    (k : ℕ)
    (hr : r[(method.step)] (method.y k) = 0) :
    fderiv ℝ f (method (k + 1)) = 0 := by
  have hsucc : method (k + 1) = method.y k :=
    zeroResidualStepEqInterpolationPoint method k hr
  have hstep : method.step (method.y k) = method.y k := by
    simpa [method.x_succ] using hsucc
  have hcont : ContDiffAt ℝ 2 f (method.y k) := by
    exact primalSpaceMemC22ContDiffAt (B := B) (Mf := Mf) (f := f) hf (method.y k)
  have hshift :=
    associatedShiftEqFderivRemainderAtStep
      (B := B) (f := f) (step := method.step) (x := method.y k) hcont
  have hzero : fderiv ℝ f (method.y k) = 0 := by
    have hshiftEq := hshift
    rw [hstep, hr] at hshiftEq
    simpa [method.y_eq k, method.A_succ k] using hshiftEq
  exact hsucc.symm ▸ hzero

/-- Helper for Lemma 4.3.4: the first-order Taylor remainder of `fderiv ℝ f` on `PrimalSpace B`
is bounded by `((Mf : ℝ) / 2) * ‖y - x‖^2`. -/
private lemma fderivDeviationLe
    (hf : primalSpaceMemC22 (B := B) (Mf := (Mf : NNReal)) f)
    (x y : PrimalSpace B) :
    ‖fderiv ℝ f y - fderiv ℝ f x - fderiv ℝ (fderiv ℝ f) x (y - x)‖[B,*] ≤
      ((Mf : ℝ) / 2) * ‖y - x‖[B] ^ (2 : ℕ) := by
  let remainder : PrimalSpace B →L[ℝ] ℝ :=
    fderiv ℝ f y - fderiv ℝ f x - fderiv ℝ (fderiv ℝ f) x (y - x)
  have hresult :
      ‖remainder‖[B,*] ≤ ((Mf : ℝ) / 2) * ‖y - x‖[B] ^ (2 : ℕ) := by
    have hgeneric :
        ‖remainder‖ ≤ ((Mf : ℝ) / 2) * ‖y - x‖ ^ (2 : ℕ) := by
      -- Reuse the generic Chapter 1 Taylor remainder estimate for `fderiv`.
      exact
        HasLipschitzContinuousHessian.fderivRemainderNorm_le
          (L3 := Mf) (g := f) hf x y
    have hball :
        {z : PrimalSpace B | B.primalSeminorm Fact.out z ≤ 1} =
          Metric.closedBall (0 : PrimalSpace B) 1 :=
      primalUnitBall_eq_closedBall (B := B)
    have hnorm :
        ‖remainder‖[B,*] = ‖remainder‖ := by
      -- Rewrite the `B`-dual norm onto the ambient closed unit ball for the current norm spelling.
      rw [LinearMap.BilinForm.dualNorm_eq_sSup_primalUnitBall_strongDual, hball]
      symm
      exact (ContinuousLinearMap.sSupUnitClosedBallEqNormReal remainder).symm
    -- Transport the ambient operator norm to the chapter `B`-dual norm only once.
    calc
      ‖remainder‖[B,*] = ‖remainder‖ := hnorm
      _ ≤ ((Mf : ℝ) / 2) * ‖y - x‖ ^ (2 : ℕ) := hgeneric
      _ = ((Mf : ℝ) / 2) * ‖y - x‖[B] ^ (2 : ℕ) := by
            simpa using
              congrArg (fun t : ℝ ↦ ((Mf : ℝ) / 2) * t ^ (2 : ℕ))
                (LinearMap.BilinForm.primalSpace_norm_eq_bInducedNorm (B := B) (x := y - x))
  simpa only [remainder] using hresult

/-- Helper for Lemma 4.3.4: at the interpolation point `y_k`, the associated shifted covector is
bounded by the first-order Taylor remainder of `fderiv ℝ f`. -/
private lemma interpolationPointAssociatedDualShiftBound
    (hf : primalSpaceMemC22 (B := B) (Mf := (Mf : NNReal)) f)
    (k : ℕ) :
    ‖(fderiv ℝ f (method (k + 1)) : PrimalSpace B →L[ℝ] ℝ) +
        (((method.M / 2 : ℝ) * r[(method.step)] (method.y k)) •
          bilinCovector (B.toQuadraticMap.associated)
            (method (k + 1) - method.y k))‖[B.toQuadraticMap.associated,*]
      ≤
      ((Mf : ℝ) / 2) * (r[(method.step)] (method.y k)) ^ (2 : ℕ) := by
  letI : Fact (B.toQuadraticMap.associated).toQuadraticMap.PosDef := ⟨associatedPosDef (B := B)⟩
  have hcont : ContDiffAt ℝ 2 f (method.y k) := by
    -- Reuse the existing `C²` hypothesis directly on the interpolation point.
    exact primalSpaceMemC22ContDiffAt (B := B) (Mf := Mf) (f := f) hf (method.y k)
  have hbd :
      ‖fderiv ℝ f (method (k + 1)) - fderiv ℝ f (method.y k) -
          fderiv ℝ (fderiv ℝ f) (method.y k) (method (k + 1) - method.y k)‖[B,*] ≤
        ((Mf : ℝ) / 2) * ‖method (k + 1) - method.y k‖[B] ^ (2 : ℕ) := by
    simpa using
      fderivDeviationLe (B := B) (Mf := Mf) (f := f) hf (method.y k) (method (k + 1))
  have hshiftEq :
      (fderiv ℝ f (method (k + 1)) : PrimalSpace B →L[ℝ] ℝ) +
          (((method.M / 2 : ℝ) * r[(method.step)] (method.y k)) •
            bilinCovector (B.toQuadraticMap.associated)
              (method (k + 1) - method.y k)) =
        fderiv ℝ f (method (k + 1)) - fderiv ℝ f (method.y k) -
          fderiv ℝ (fderiv ℝ f) (method.y k) (method (k + 1) - method.y k) := by
    simpa [method.x_succ, OptimalCubicNewtonMethod.M] using
      associatedShiftEqFderivRemainderAtStep
        (B := B) (f := f) (step := method.step) (x := method.y k) hcont
  calc
    ‖(fderiv ℝ f (method (k + 1)) : PrimalSpace B →L[ℝ] ℝ) +
        (((method.M / 2 : ℝ) * r[(method.step)] (method.y k)) •
          bilinCovector (B.toQuadraticMap.associated)
            (method (k + 1) - method.y k))‖[B.toQuadraticMap.associated,*]
        = ‖fderiv ℝ f (method (k + 1)) - fderiv ℝ f (method.y k) -
            fderiv ℝ (fderiv ℝ f) (method.y k)
              (method (k + 1) - method.y k)‖[B.toQuadraticMap.associated,*] := by
            rw [hshiftEq]
    _ = ‖fderiv ℝ f (method (k + 1)) - fderiv ℝ f (method.y k) -
          fderiv ℝ (fderiv ℝ f) (method.y k) (method (k + 1) - method.y k)‖[B,*] := by
          rw [associatedDualNormEqOnPrimalSpace]
    _ ≤ ((Mf : ℝ) / 2) * ‖method (k + 1) - method.y k‖[B] ^ (2 : ℕ) := hbd
    _ = ((Mf : ℝ) / 2) * (r[(method.step)] (method.y k)) ^ (2 : ℕ) := by
          rw [method.x_succ, CubicNewtonStep.residual_apply]

/-- Helper for Lemma 4.3.4: the interpolation-point displacement already satisfies the associated
dual-pairing lower bound with the source coefficient `((M² - M_f²) / (4M))`. -/
private lemma interpolationPointDualPairingLowerBoundBase
    (hf : primalSpaceMemC22 (B := B) (Mf := (Mf : NNReal)) f)
    (k : ℕ) :
    let g : PrimalSpace B →L[ℝ] ℝ := fderiv ℝ f (method (k + 1))
    let residual : ℝ := r[(method.step)] (method.y k)
    g (method.y k - method (k + 1)) ≥
      (1 / (method.M * residual)) * ‖g‖[B,*] ^ (2 : ℕ) +
        ((method.M ^ (2 : ℕ) - (Mf : ℝ) ^ (2 : ℕ)) / (4 * method.M)) *
          residual ^ (3 : ℕ) := by
  dsimp
  let A : BilinForm ℝ (PrimalSpace B) := B.toQuadraticMap.associated
  let g : PrimalSpace B →L[ℝ] ℝ := fderiv ℝ f (method (k + 1))
  let d : PrimalSpace B := method.step (method.y k) - method.y k
  have hSymm : BilinForm.IsSymm A := by
    -- The associated surface is symmetric by construction.
    dsimp [A]
    exact ⟨QuadraticMap.associated_isSymm ℝ B.toQuadraticMap⟩
  have hshift :
      ‖g + (((method.M / 2 : ℝ) * ‖d‖[A]) • bilinCovector A d)‖[A,*] ≤
        ((Mf : ℝ) / 2) * ‖d‖[A] ^ (2 : ℕ) := by
    have hd :
        d = method (k + 1) - method.y k := by
      -- Normalize the step displacement once before rewriting the shift bound.
      simp [d]
    -- Rewrite the interpolation-point shift bound into the norm spelling required by the algebraic
    -- dual-pairing engine.
    calc
      ‖g + (((method.M / 2 : ℝ) * ‖d‖[A]) • bilinCovector A d)‖[A,*]
          = ‖g + (((method.M / 2 : ℝ) * r[(method.step)] (method.y k)) •
              bilinCovector A (method (k + 1) - method.y k))‖[A,*] := by
                rw [associatedStepResidualNormEq
                  (B := B) (f := f) (step := method.step) (x := method.y k)]
                rw [hd]
      _ ≤ ((Mf : ℝ) / 2) * (r[(method.step)] (method.y k)) ^ (2 : ℕ) := by
            simpa [A] using
              interpolationPointAssociatedDualShiftBound
                (B := B) (Mf := Mf) (f := f) method hf k
      _ = ((Mf : ℝ) / 2) * ‖d‖[A] ^ (2 : ℕ) := by
            rw [← associatedStepResidualNormEq
              (B := B) (f := f) (step := method.step) (x := method.y k)]
  have hbase :
      g (-d) ≥
        (1 / (method.M * ‖d‖[A])) * ‖g‖[A,*] ^ (2 : ℕ) +
          ((method.M ^ (2 : ℕ) - (Mf : ℝ) ^ (2 : ℕ)) / (4 * method.M)) *
            ‖d‖[A] ^ (3 : ℕ) := by
    exact dualPairingLowerBoundOfDualShiftBound
      (B := B) (A := A) hSymm method.M_pos d g hshift
  have hdisp : method.y k - method (k + 1) = -d := by
    -- Normalize the displacement once before transporting the lower bound back to `y_k`.
    dsimp [d]
    rw [method.x_succ]
    abel
  calc
    g (method.y k - method (k + 1)) = g (-d) := by
      rw [hdisp]
    _ ≥
        (1 / (method.M * ‖d‖[A])) * ‖g‖[A,*] ^ (2 : ℕ) +
          ((method.M ^ (2 : ℕ) - (Mf : ℝ) ^ (2 : ℕ)) / (4 * method.M)) *
            ‖d‖[A] ^ (3 : ℕ) := hbase
    _ =
        (1 / (method.M * r[(method.step)] (method.y k))) * ‖g‖[B,*] ^ (2 : ℕ) +
          ((method.M ^ (2 : ℕ) - (Mf : ℝ) ^ (2 : ℕ)) / (4 * method.M)) *
            (r[(method.step)] (method.y k)) ^ (3 : ℕ) := by
          have hdual : ‖g‖[A,*] = ‖g‖[B,*] := by
            dsimp [A]
            simpa using associatedDualNormEqOnPrimalSpace (B := B) g
          have hres : ‖d‖[A] = r[(method.step)] (method.y k) := by
            dsimp [A, d]
            simpa using associatedStepResidualNormEq
              (B := B) (f := f) (step := method.step) (x := method.y k)
          rw [hdual, hres]

/-- Helper for Lemma 4.3.4: the specialized one-step cubic lower bound at the interpolation point
`y_k` is the only remaining structural ingredient from Lemma 4.3.3. -/
private lemma cubicStepDualPairingLowerBoundAtInterpolationPoint
    (hf : primalSpaceMemC22 (B := B) (Mf := (Mf : NNReal)) f)
    (k : ℕ) :
    let g : PrimalSpace B →L[ℝ] ℝ := fderiv ℝ f (method (k + 1))
    let residual : ℝ := r[(method.step)] (method.y k)
    let cubicCoeff : ℝ := (((1 - sigma ^ (2 : ℕ)) / 4 : ℝ) * method.M)
    g (method.y k - method (k + 1)) ≥
      (1 / (method.M * residual)) * ‖g‖[B,*] ^ (2 : ℕ) +
        cubicCoeff * residual ^ (3 : ℕ) := by
  dsimp
  have hMσ : method.M ≥ (1 / sigma) * (Mf : ℝ) := by
    -- `method.M` is definitionally `Mf / sigma`, so the required coefficient comparison is exact.
    simp [OptimalCubicNewtonMethod.M, div_eq_mul_inv, mul_comm]
  have hbase :=
    interpolationPointDualPairingLowerBoundBase (B := B) (Mf := Mf) (f := f) method hf k
  have hcoeff :
      (((1 - sigma ^ (2 : ℕ)) / 4 : ℝ) * method.M) ≤
        (method.M ^ (2 : ℕ) - (Mf : ℝ) ^ (2 : ℕ)) / (4 * method.M) :=
    sigmaCubicCoefficientLowerBound (Mf := Mf)
      ⟨method.sigma_mem.1, method.sigma_mem.2.le⟩ hMσ method.M_pos
  have hrad : 0 ≤ r[(method.step)] (method.y k) :=
    residualNonneg (B := B) (f := f) (step := method.step) (x := method.y k)
  have hterm :
      (1 / (method.M * r[(method.step)] (method.y k))) * ‖fderiv ℝ f (method (k + 1))‖[B,*] ^
          (2 : ℕ) +
        (((1 - sigma ^ (2 : ℕ)) / 4 : ℝ) * method.M) *
          (r[(method.step)] (method.y k)) ^ (3 : ℕ)
      ≤
      (1 / (method.M * r[(method.step)] (method.y k))) * ‖fderiv ℝ f (method (k + 1))‖[B,*] ^
          (2 : ℕ) +
        ((method.M ^ (2 : ℕ) - (Mf : ℝ) ^ (2 : ℕ)) / (4 * method.M)) *
          (r[(method.step)] (method.y k)) ^ (3 : ℕ) := by
    have hrad_nonneg : 0 ≤ (r[(method.step)] (method.y k)) ^ (3 : ℕ) := by
      exact pow_nonneg hrad 3
    gcongr
  exact hterm.trans hbase

/-- Helper for Lemma 4.3.4: residual control implies the reciprocal coefficient at the true
residual is at least the one built from `ρ_k`. -/
private lemma reciprocalGapNonnegOfResidualLeRho
    (hresidual : ∀ k : ℕ, r[(method.step)] (method.y k) ≤ method.rho k)
    (k : ℕ)
    (hr_pos : 0 < r[(method.step)] (method.y k)) :
    0 ≤ 1 / (method.M * r[(method.step)] (method.y k)) -
      1 / (method.M * method.rho k) := by
  have hMr_pos : 0 < method.M * r[(method.step)] (method.y k) := mul_pos method.M_pos hr_pos
  have hmul_le :
      method.M * r[(method.step)] (method.y k) ≤ method.M * method.rho k := by
    nlinarith [hresidual k, method.M_pos]
  have hrecip :
      1 / (method.M * method.rho k) ≤ 1 / (method.M * r[(method.step)] (method.y k)) := by
    exact one_div_le_one_div_of_le hMr_pos hmul_le
  -- Rewrite the claim as the nonnegativity of a reciprocal gap.
  linarith

/-- Helper for Lemma 4.3.4: the algorithmic weight identity and residual bound compare the
quadratic penalty coefficient with the reciprocal residual coefficient. -/
private lemma weightPenaltyLeResidualPenalty
    (hresidual : ∀ k : ℕ, r[(method.step)] (method.y k) ≤ method.rho k)
    (k : ℕ)
    (hr_pos : 0 < r[(method.step)] (method.y k)) :
    (((method.a (k + 1)) ^ (2 : ℕ)) / 2 : ℝ) ≤
      method.A (k + 1) * (1 / (method.M * r[(method.step)] (method.y k))) := by
  have hrecip_gap :=
    reciprocalGapNonnegOfResidualLeRho method hresidual k hr_pos
  have hrecip :
      1 / (method.M * method.rho k) ≤ 1 / (method.M * r[(method.step)] (method.y k)) := by
    linarith
  have ha_sq :
      (((method.a (k + 1)) ^ (2 : ℕ)) / 2 : ℝ) =
        method.A (k + 1) / (method.M * method.rho k) := by
    calc
      (((method.a (k + 1)) ^ (2 : ℕ)) / 2 : ℝ)
          = (((2 : ℝ) * (method.A k + method.a (k + 1)) /
                (method.M * method.rho k)) / 2 : ℝ) := by
              rw [method.a_succ_sq]
      _ = method.A (k + 1) / (method.M * method.rho k) := by
            rw [method.A_succ]
            field_simp [method.M_pos.ne', (method.rho_pos k).ne']
  -- Replace the abstract weight identity by a monotone reciprocal comparison.
  calc
    (((method.a (k + 1)) ^ (2 : ℕ)) / 2 : ℝ)
        = method.A (k + 1) / (method.M * method.rho k) := ha_sq
    _ = method.A (k + 1) * (1 / (method.M * method.rho k)) := by
          simp [div_eq_mul_inv]
    _ ≤ method.A (k + 1) * (1 / (method.M * r[(method.step)] (method.y k))) := by
          exact mul_le_mul_of_nonneg_left hrecip (method.A_nonneg (k + 1))

/-- Helper for Lemma 4.3.4: when the residual vanishes, the successor gradient and every new
penalty contribution vanish as well, so only the old support inequality remains. -/
private lemma zeroResidualSuccessorAssembly
    (hf : primalSpaceMemC22 (B := B) (Mf := (Mf : NNReal)) f)
    (hf_conv : ConvexOn ℝ Set.univ f)
    (k : ℕ)
    (hr : r[(method.step)] (method.y k) = 0) :
    method.A (k + 1) * f (method (k + 1)) +
        method.estimatingLowerBoundCorrection (k + 1) ≤
    method.A k * f (method k) +
        method.estimatingLowerBoundCorrection k +
        method.a (k + 1) *
          (f (method (k + 1)) +
            inner ℝ (∇ f (method (k + 1))) (method.v k - method (k + 1))) -
        (((method.a (k + 1)) ^ (2 : ℕ)) / 2 : ℝ) *
          ‖fderiv ℝ f (method (k + 1))‖[B,*] ^ (2 : ℕ) := by
  have hstep : method (k + 1) = method.y k :=
    zeroResidualStepEqInterpolationPoint method k hr
  have hcontDiffAt : ContDiffAt ℝ 2 f (method (k + 1)) := by
    exact primalSpaceMemC22ContDiffAt (B := B) (Mf := Mf) (f := f) hf (method (k + 1))
  have hdiff :
      DifferentiableWithinAt ℝ f Set.univ (method (k + 1)) := by
    exact
      (hcontDiffAt.differentiableAt
        (by norm_num)).differentiableWithinAt
  have hsupport :
      f (method (k + 1)) +
          inner ℝ (∇ f (method (k + 1))) (method k - method (k + 1)) ≤
        f (method k) := by
    simpa [gradientWithin, gradient, fderivWithin_univ] using
      hf_conv.lower_tangent_plane
        (method (k + 1))
        (by simp)
        hdiff
        (method k)
        (by simp)
  have hsupportScaled :
      method.A k * f (method (k + 1)) +
          method.A k * inner ℝ (∇ f (method (k + 1))) (method k - method (k + 1)) ≤
        method.A k * f (method k) := by
    -- Scale the convex support inequality by the nonnegative stage weight `A_k`.
    simpa [mul_add, add_comm, add_left_comm, add_assoc] using
      mul_le_mul_of_nonneg_left hsupport (method.A_nonneg k)
  have hgap :
      method.A k * inner ℝ (∇ f (method (k + 1))) (method k - method (k + 1)) +
          method.a (k + 1) *
            inner ℝ (∇ f (method (k + 1))) (method.v k - method (k + 1)) = 0 := by
    -- Once the zero-residual step collapses to `y_k`, the interpolation-gap identity loses its
    -- left-hand side completely.
    calc
      method.A k * inner ℝ (∇ f (method (k + 1))) (method k - method (k + 1)) +
          method.a (k + 1) *
            inner ℝ (∇ f (method (k + 1))) (method.v k - method (k + 1))
          =
            method.A (k + 1) *
              inner ℝ (∇ f (method (k + 1))) (method.y k - method (k + 1)) := by
                exact
                  (scaledInterpolationGapGradientEq
                    (B := B) (Mf := Mf) (f := f) method k).symm
      _ = 0 := by
            have hyZero :
                inner ℝ (∇ f (method (k + 1))) (method.y k - method (k + 1)) = 0 := by
              rw [hstep]
              simp
            rw [hyZero]
            ring
  have hmain :
      method.A (k + 1) * f (method (k + 1)) ≤
        method.A k * f (method k) +
          method.a (k + 1) *
            (f (method (k + 1)) +
              inner ℝ (∇ f (method (k + 1))) (method.v k - method (k + 1))) := by
    have hgap' :
        method.A k * inner ℝ (∇ f (method (k + 1))) (method k - method (k + 1)) =
          -(method.a (k + 1) *
            inner ℝ (∇ f (method (k + 1))) (method.v k - method (k + 1))) :=
      eq_neg_of_add_eq_zero_left hgap
    calc
      method.A (k + 1) * f (method (k + 1))
          = method.A k * f (method (k + 1)) +
              method.a (k + 1) * f (method (k + 1)) := by
                rw [method.A_succ k]
                ring
      _ = (method.A k * f (method (k + 1)) +
            method.A k * inner ℝ (∇ f (method (k + 1))) (method k - method (k + 1))) +
            method.a (k + 1) *
              (f (method (k + 1)) +
                inner ℝ (∇ f (method (k + 1))) (method.v k - method (k + 1))) := by
              rw [hgap']
              ring
      _ ≤ method.A k * f (method k) +
            method.a (k + 1) *
              (f (method (k + 1)) +
                inner ℝ (∇ f (method (k + 1))) (method.v k - method (k + 1))) := by
              simpa [add_assoc, add_left_comm, add_comm] using
                add_le_add_right
                  hsupportScaled
                  (method.a (k + 1) *
                    (f (method (k + 1)) +
                      inner ℝ (∇ f (method (k + 1))) (method.v k - method (k + 1))))
  have hfderiv_zero :
      fderiv ℝ f (method (k + 1)) = 0 :=
    fderiv_eq_zero_of_residual_eq_zero (B := B) (Mf := Mf) (f := f) method hf k hr
  have hcorr_zero :
      (((1 - sigma ^ (2 : ℕ)) / 4 : ℝ) * method.M) *
          (method.A (k + 1) * (r[(method.step)] (method.y k)) ^ (3 : ℕ)) = 0 := by
    rw [hr]
    simp
  have hpenalty_zero :
      (((method.a (k + 1)) ^ (2 : ℕ)) / 2 : ℝ) *
          ‖fderiv ℝ f (method (k + 1))‖[B,*] ^ (2 : ℕ) = 0 := by
    have hzeroNorm : ‖(0 : PrimalSpace B →L[ℝ] ℝ)‖[B,*] = 0 := by
      rw [LinearMap.BilinForm.dualNorm_eq_sSup_primalUnitBall_strongDual]
      change sSup
          ((fun _ : PrimalSpace B ↦ (0 : ℝ)) ''
            {x : PrimalSpace B | B.primalSeminorm Fact.out x ≤ 1}) = 0
      have himage :
          (fun _ : PrimalSpace B ↦ (0 : ℝ)) ''
              {x : PrimalSpace B | B.primalSeminorm Fact.out x ≤ 1} =
            ({0} : Set ℝ) := by
        ext t
        constructor
        · rintro ⟨x, hx, rfl⟩
          simp
        · intro ht
          refine ⟨0, ?_, by simpa using ht.symm⟩
          simp
      rw [himage]
      simp
    rw [hfderiv_zero, hzeroNorm]
    simp
  -- Rewrite the vanished cubic correction and the zero penalty, then reuse the scalar branch bound.
  rw [method.estimatingLowerBoundCorrection_succ]
  rw [hcorr_zero, hpenalty_zero]
  nlinarith [hmain]

/-- Helper for Lemma 4.3.4: in the positive-residual branch, the cubic lower bound and the weight
comparison assemble the core inequality before the recursive correction term is restored. -/
private lemma positiveResidualCoreAssembly
    (hf : primalSpaceMemC22 (B := B) (Mf := (Mf : NNReal)) f)
    (hf_conv : ConvexOn ℝ Set.univ f)
    (hresidual : ∀ k : ℕ, r[(method.step)] (method.y k) ≤ method.rho k)
    (k : ℕ)
    (hr_pos : 0 < r[(method.step)] (method.y k)) :
    let residual : ℝ := r[(method.step)] (method.y k)
    let gNormSq : ℝ := ‖fderiv ℝ f (method (k + 1))‖[B,*] ^ (2 : ℕ)
    let cubicCoeff : ℝ := (((1 - sigma ^ (2 : ℕ)) / 4 : ℝ) * method.M)
    let penalty : ℝ := (((method.a (k + 1)) ^ (2 : ℕ)) / 2 : ℝ) * gNormSq
    method.A (k + 1) * f (method (k + 1)) +
        cubicCoeff * (method.A (k + 1) * residual ^ (3 : ℕ)) +
        penalty ≤
      method.A k * f (method k) +
          method.a (k + 1) *
            (f (method (k + 1)) +
              inner ℝ (∇ f (method (k + 1))) (method.v k - method (k + 1))) := by
  dsimp
  let residual : ℝ := r[(method.step)] (method.y k)
  let gNormSq : ℝ := ‖fderiv ℝ f (method (k + 1))‖[B,*] ^ (2 : ℕ)
  let cubicCoeff : ℝ := (((1 - sigma ^ (2 : ℕ)) / 4 : ℝ) * method.M)
  let gapEval : ℝ := fderiv ℝ f (method (k + 1)) (method.y k - method (k + 1))
  let penalty : ℝ := (((method.a (k + 1)) ^ (2 : ℕ)) / 2 : ℝ) * gNormSq
  have hcontDiffAt : ContDiffAt ℝ 2 f (method (k + 1)) := by
    exact primalSpaceMemC22ContDiffAt (B := B) (Mf := Mf) (f := f) hf (method (k + 1))
  have hdiff :
      DifferentiableWithinAt ℝ f Set.univ (method (k + 1)) := by
    exact
      (hcontDiffAt.differentiableAt
        (by norm_num)).differentiableWithinAt
  have hsupport :
      f (method (k + 1)) +
          inner ℝ (∇ f (method (k + 1))) (method k - method (k + 1)) ≤
        f (method k) := by
    simpa [gradientWithin, gradient, fderivWithin_univ] using
      hf_conv.lower_tangent_plane
        (method (k + 1))
        (by simp)
        hdiff
        (method k)
        (by simp)
  have hsupportScaled :
      method.A k * f (method (k + 1)) +
          method.A k * inner ℝ (∇ f (method (k + 1))) (method k - method (k + 1)) ≤
        method.A k * f (method k) := by
    -- Scale the convex support inequality by the nonnegative weight `A_k`.
    simpa [mul_add, add_comm, add_left_comm, add_assoc] using
      mul_le_mul_of_nonneg_left hsupport (method.A_nonneg k)
  have hgap :
      method.A (k + 1) * inner ℝ (∇ f (method (k + 1))) (method.y k - method (k + 1)) =
        method.A k * inner ℝ (∇ f (method (k + 1))) (method k - method (k + 1)) +
          method.a (k + 1) *
            inner ℝ (∇ f (method (k + 1))) (method.v k - method (k + 1)) :=
    scaledInterpolationGapGradientEq (B := B) (Mf := Mf) (f := f) method k
  have hgapEval :
      inner ℝ (∇ f (method (k + 1))) (method.y k - method (k + 1)) = gapEval := by
    -- Rewrite the interpolation gap from the gradient pairing to evaluation by `fderiv`.
    dsimp [gapEval]
    calc
      inner ℝ (∇ f (method (k + 1))) (method.y k - method (k + 1))
          = ((InnerProductSpace.toDual ℝ (PrimalSpace B)) (∇ f (method (k + 1))))
              (method.y k - method (k + 1)) := by
                simp
      _ = fderiv ℝ f (method (k + 1)) (method.y k - method (k + 1)) := by
            rw [gradientCovector_eq_fderivAt (f := f) hcontDiffAt]
  have hmain :
      method.A (k + 1) * f (method (k + 1)) +
          method.A (k + 1) * gapEval ≤
        method.A k * f (method k) +
          method.a (k + 1) *
            (f (method (k + 1)) +
              inner ℝ (∇ f (method (k + 1))) (method.v k - method (k + 1))) := by
    have hgap' :
        method.A k * inner ℝ (∇ f (method (k + 1))) (method k - method (k + 1)) +
            method.a (k + 1) *
              inner ℝ (∇ f (method (k + 1))) (method.v k - method (k + 1)) =
          method.A (k + 1) * gapEval := by
      calc
        method.A k * inner ℝ (∇ f (method (k + 1))) (method k - method (k + 1)) +
            method.a (k + 1) *
              inner ℝ (∇ f (method (k + 1))) (method.v k - method (k + 1))
            = method.A (k + 1) *
                inner ℝ (∇ f (method (k + 1))) (method.y k - method (k + 1)) := hgap.symm
        _ = method.A (k + 1) * gapEval := by rw [hgapEval]
    have hgap'' :
        (method.A k + method.a (k + 1)) * gapEval =
          method.A k * inner ℝ (∇ f (method (k + 1))) (method k - method (k + 1)) +
            method.a (k + 1) *
              inner ℝ (∇ f (method (k + 1))) (method.v k - method (k + 1)) := by
      simpa [method.A_succ k] using hgap'.symm
    calc
      method.A (k + 1) * f (method (k + 1)) + method.A (k + 1) * gapEval
          = method.A k * f (method (k + 1)) +
              method.a (k + 1) * f (method (k + 1)) +
              (method.A k * inner ℝ (∇ f (method (k + 1))) (method k - method (k + 1)) +
                method.a (k + 1) *
                  inner ℝ (∇ f (method (k + 1))) (method.v k - method (k + 1))) := by
                rw [method.A_succ k, hgap'']
                ring
      _ = (method.A k * f (method (k + 1)) +
            method.A k * inner ℝ (∇ f (method (k + 1))) (method k - method (k + 1))) +
            method.a (k + 1) *
              (f (method (k + 1)) +
                inner ℝ (∇ f (method (k + 1))) (method.v k - method (k + 1))) := by
              ring
      _ ≤ method.A k * f (method k) +
            method.a (k + 1) *
              (f (method (k + 1)) +
                inner ℝ (∇ f (method (k + 1))) (method.v k - method (k + 1))) := by
              simpa [add_assoc, add_left_comm, add_comm] using
                add_le_add_right
                  hsupportScaled
                  (method.a (k + 1) *
                    (f (method (k + 1)) +
                      inner ℝ (∇ f (method (k + 1))) (method.v k - method (k + 1))))
  have hcubicRaw :
      (1 / (method.M * residual)) * gNormSq +
          cubicCoeff * residual ^ (3 : ℕ) ≤
        gapEval := by
    -- Reuse the normalized one-step cubic lower bound at the interpolation point.
    simpa [residual, gNormSq, cubicCoeff, gapEval] using
      cubicStepDualPairingLowerBoundAtInterpolationPoint (B := B) (Mf := Mf) (f := f) method hf k
  have hcubicScaled :
      method.A (k + 1) * ((1 / (method.M * residual)) * gNormSq) +
          cubicCoeff * (method.A (k + 1) * residual ^ (3 : ℕ)) ≤
        method.A (k + 1) * gapEval := by
    -- Scale the cubic lower bound by `A_{k+1}` and distribute the factor to match the recursive
    -- correction term.
    have hscaled :
        method.A (k + 1) *
            ((1 / (method.M * residual)) * gNormSq + cubicCoeff * residual ^ (3 : ℕ)) ≤
          method.A (k + 1) * gapEval := by
      exact mul_le_mul_of_nonneg_left hcubicRaw (method.A_nonneg (k + 1))
    simpa [mul_add, mul_assoc, mul_left_comm, mul_comm] using hscaled
  have hweight :
      (((method.a (k + 1)) ^ (2 : ℕ)) / 2 : ℝ) ≤
        method.A (k + 1) * (1 / (method.M * residual)) := by
    -- The algorithmic weight identity compares the quadratic penalty coefficient with the
    -- reciprocal residual coefficient built from the true residual.
    simpa only [residual] using
      weightPenaltyLeResidualPenalty (B := B) (Mf := Mf) (f := f) method hresidual k hr_pos
  have hpenalty :
      penalty ≤ method.A (k + 1) * ((1 / (method.M * residual)) * gNormSq) := by
    -- Multiply the coefficient comparison by the nonnegative squared dual norm.
    have hnorm_nonneg : 0 ≤ gNormSq := by
      dsimp [gNormSq]
      positivity
    calc
      penalty
          = ((((method.a (k + 1)) ^ (2 : ℕ)) / 2 : ℝ) * gNormSq) := by
              rfl
      _ ≤
          (method.A (k + 1) * (1 / (method.M * residual))) * gNormSq := by
            exact mul_le_mul_of_nonneg_right hweight hnorm_nonneg
      _ = method.A (k + 1) * ((1 / (method.M * residual)) * gNormSq) := by
            ring
  have hcore :
      method.A (k + 1) * f (method (k + 1)) +
          cubicCoeff * (method.A (k + 1) * residual ^ (3 : ℕ)) +
          penalty ≤
        method.A k * f (method k) +
          method.a (k + 1) *
            (f (method (k + 1)) +
              inner ℝ (∇ f (method (k + 1))) (method.v k - method (k + 1))) := by
    have hfirst :
        method.A (k + 1) * f (method (k + 1)) +
            cubicCoeff * (method.A (k + 1) * residual ^ (3 : ℕ)) +
            penalty ≤
          method.A (k + 1) * f (method (k + 1)) +
            cubicCoeff * (method.A (k + 1) * residual ^ (3 : ℕ)) +
            method.A (k + 1) * ((1 / (method.M * residual)) * gNormSq) := by
      -- Replace the explicit quadratic penalty by the stronger reciprocal-residual contribution.
      nlinarith [hpenalty]
    have hsecond :
        method.A (k + 1) * f (method (k + 1)) +
            cubicCoeff * (method.A (k + 1) * residual ^ (3 : ℕ)) +
            method.A (k + 1) * ((1 / (method.M * residual)) * gNormSq) ≤
          method.A (k + 1) * f (method (k + 1)) + method.A (k + 1) * gapEval := by
      -- The scaled cubic lower bound turns the residual correction and reciprocal term into the
      -- interpolation-point pairing term.
      nlinarith [hcubicScaled]
    exact le_trans hfirst (le_trans hsecond hmain)
  exact hcore

/-- Helper for Lemma 4.3.4: in the positive-residual branch, the cubic lower bound at `y_k`
dominates the new cubic correction and quadratic penalty terms after coefficient normalization. -/
private lemma positiveResidualSuccessorAssembly
    (hf : primalSpaceMemC22 (B := B) (Mf := (Mf : NNReal)) f)
    (hf_conv : ConvexOn ℝ Set.univ f)
    (hresidual : ∀ k : ℕ, r[(method.step)] (method.y k) ≤ method.rho k)
    (k : ℕ)
    (hr_pos : 0 < r[(method.step)] (method.y k)) :
    let increment : ℝ :=
      method.a (k + 1) *
          (f (method (k + 1)) +
            inner ℝ (∇ f (method (k + 1))) (method.v k - method (k + 1))) -
        (((method.a (k + 1)) ^ (2 : ℕ)) / 2 : ℝ) *
          ‖fderiv ℝ f (method (k + 1))‖[B,*] ^ (2 : ℕ)
    method.A (k + 1) * f (method (k + 1)) +
        method.estimatingLowerBoundCorrection (k + 1) ≤
      method.A k * f (method k) +
        method.estimatingLowerBoundCorrection k + increment := by
  dsimp
  have hcore :
      method.A (k + 1) * f (method (k + 1)) +
          (((1 - sigma ^ (2 : ℕ)) / 4 : ℝ) * method.M) *
            (method.A (k + 1) * (r[(method.step)] (method.y k)) ^ (3 : ℕ)) +
          ((((method.a (k + 1)) ^ (2 : ℕ)) / 2 : ℝ) *
            ‖fderiv ℝ f (method (k + 1))‖[B,*] ^ (2 : ℕ)) ≤
        method.A k * f (method k) +
          method.a (k + 1) *
            (f (method (k + 1)) +
              inner ℝ (∇ f (method (k + 1))) (method.v k - method (k + 1))) := by
    simpa using positiveResidualCoreAssembly method hf hf_conv hresidual k hr_pos
  have hcore' :=
    add_le_add_right hcore (method.estimatingLowerBoundCorrection k)
  rw [method.estimatingLowerBoundCorrection_succ]
  nlinarith [hcore']

/-- Helper for Lemma 4.3.4: the successor stage converts the previous estimating minimum and the
local cubic-step lower bound into the next accumulated lower bound. -/
private lemma successorAccumulatedValueLePreviousTiltedValue
    (hf : primalSpaceMemC22 (B := B) (Mf := (Mf : NNReal)) f)
    (hf_conv : ConvexOn ℝ Set.univ f)
    (hresidual : ∀ k : ℕ, r[(method.step)] (method.y k) ≤ method.rho k)
    (k : ℕ) :
    method.A (k + 1) * f (method (k + 1)) +
        method.estimatingLowerBoundCorrection (k + 1) ≤
    method.A k * f (method k) +
        method.estimatingLowerBoundCorrection k +
        method.a (k + 1) *
          (f (method (k + 1)) +
            inner ℝ (∇ f (method (k + 1))) (method.v k - method (k + 1))) -
        (((method.a (k + 1)) ^ (2 : ℕ)) / 2 : ℝ) *
          ‖fderiv ℝ f (method (k + 1))‖[B,*] ^ (2 : ℕ) := by
  -- Route correction: split the old monolithic branch proof into a zero-residual closure and a
  -- positive-residual closure so the reciprocal arithmetic is normalized once per branch.
  by_cases hr : r[(method.step)] (method.y k) = 0
  · exact zeroResidualSuccessorAssembly method hf hf_conv k hr
  · have hr_nonneg : 0 ≤ r[(method.step)] (method.y k) := by
      exact residualNonneg (B := B) (f := f) (step := method.step) (x := method.y k)
    have hr_pos : 0 < r[(method.step)] (method.y k) :=
      lt_of_le_of_ne hr_nonneg (Ne.symm hr)
    have hpos := positiveResidualSuccessorAssembly method hf hf_conv hresidual k hr_pos
    dsimp at hpos
    nlinarith [hpos]

/-- Lemma 4.3.4: if `f ∈ C22[Mf]` is convex and the algorithmic parameters satisfy
`r_M(y_k) ≤ ρ_k` for every `k`, then `A_k f(x_k) + B_k` is bounded above by
`ψ_k(v_k) = ψ_k^* = min_x ψ_k(x)`, where `B_k` is the accumulated cubic correction term
`((1 - σ^2) / 4) M * ∑_{i=0}^{k-1} A_{i+1} r_M(y_i)^3`. -/
-- Proof sketch: argue by induction on `k`. Use the recursion for `ψ_{k+1}`, the convexity bound
-- comparing `f(x_k)` and the linearization at `x_{k+1}`, invoke the `C22[(Mf : NNReal)]`
-- regularity through Lemma 4.3.3 / Proposition 4.3.3, minimize the resulting quadratic term at
-- `v_k`, and absorb the new cubic contribution into the recursive definition of the correction
-- term.
lemma optimalCubicNewtonMethod_accumulated_value_le_estimating_minimum
    (hf : primalSpaceMemC22 (B := B) (Mf := (Mf : NNReal)) f)
    (hf_conv : ConvexOn ℝ Set.univ f)
    (hresidual : ∀ k : ℕ, r[(method.step)] (method.y k) ≤ method.rho k)
    (k : ℕ) :
    method.A k * f (method k) +
        method.estimatingLowerBoundCorrection k ≤
      method.psi k (method.v k) := by
  induction k with
  | zero =>
      -- At stage `0`, the weighted objective and cubic correction both vanish.
      rw [method.A_zero, method.estimatingLowerBoundCorrection_zero]
      simp
  | succ k hk =>
      have hsucc :=
        successorAccumulatedValueLePreviousTiltedValue method hf hf_conv hresidual k
      have hpsi :=
        psiSuccLowerBoundViaQuadraticCompletion method hf k
      let increment :=
        method.a (k + 1) *
            (f (method (k + 1)) +
              inner ℝ (∇ f (method (k + 1))) (method.v k - method (k + 1))) -
          (((method.a (k + 1)) ^ (2 : ℕ)) / 2 : ℝ) *
            ‖fderiv ℝ f (method (k + 1))‖[B,*] ^ (2 : ℕ)
      have hk' :
          method.A k * f (method k) + method.estimatingLowerBoundCorrection k + increment ≤
            method.psi k (method.v k) + increment := by
        simpa [add_assoc, add_left_comm, add_comm] using add_le_add_right hk increment
      -- Chain the induction hypothesis with the one-step lower bound for the new estimating
      -- minimum.
      calc
        method.A (k + 1) * f (method (k + 1)) +
            method.estimatingLowerBoundCorrection (k + 1)
            ≤ method.A k * f (method k) +
                method.estimatingLowerBoundCorrection k +
                method.a (k + 1) *
                  (f (method (k + 1)) +
                    inner ℝ (∇ f (method (k + 1))) (method.v k - method (k + 1))) -
                (((method.a (k + 1)) ^ (2 : ℕ)) / 2 : ℝ) *
                  ‖fderiv ℝ f (method (k + 1))‖[B,*] ^ (2 : ℕ) := hsucc
        _ ≤ method.psi k (method.v k) +
              method.a (k + 1) *
                (f (method (k + 1)) +
                  inner ℝ (∇ f (method (k + 1))) (method.v k - method (k + 1))) -
              (((method.a (k + 1)) ^ (2 : ℕ)) / 2 : ℝ) *
                ‖fderiv ℝ f (method (k + 1))‖[B,*] ^ (2 : ℕ) := by
                  simpa [increment] using hk'
        _ ≤ method.psi (k + 1) (method.v (k + 1)) := by
              exact hpsi

end
