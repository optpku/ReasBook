/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_1_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

/- Example 5.1.2 lies in the Chapter 5 self-concordance / quadratic-objective domain.

Sampled owner-style declarations in this domain:
* `hessian` from `Chap01/Definition_1_4_16`, the canonical second-order owner;
* `thirdDirectionalDerivative` from `Chap05/Definition_5_0_10`, the Chapter 5 source-facing
  owner for diagonal third derivatives;
* `IsSelfConcordantOnWith` from `Chap05/Definition_5_1_1`, the chapter owner predicate;
* `quadraticObjective` from `Chap01/Definition_1_9_1`, the Euclidean matrix-model quadratic owner;
* `nesterovQuadraticObjective` from `Chap02/Proposition_2_6`, the specialized operator quadratic
  owner without an affine term.

Source/core/bridge triage:
* source-facing: the affine-quadratic objective `x ↦ α + ⟪a, x⟫ + (1 / 2) ⟪A x, x⟫`;
* core/canonical: `hessian`, `thirdDirectionalDerivative`, and `IsSelfConcordantOnWith`;
* bridge/view: the Euclidean matrix model `quadraticObjective` and the Chapter 2 specialization
  `nesterovQuadraticObjective`.

Primitive data:
* the scalar offset `α`;
* the linear coefficient `a`;
* the bounded operator `A : E →L[ℝ] E`.

Derived API:
* the gradient identity `∇f(x) = a + A x`;
* the constant-Hessian identity `hessian f x = A`;
* the vanishing third directional derivative;
* the self-concordance conclusion with constant `0`.

No upstream owner packages this exact affine operator-valued quadratic objective at the intrinsic
Hilbert-space level, so this file remains the source-facing owner. The supporting API is refined to
the canonical Chapter 1/5 differential owners rather than the raw `fderiv ℝ (∇ ·)` surface. -/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The quadratic-affine objective `x ↦ α + ⟪a, x⟫ + (1 / 2) ⟪A x, x⟫` on `E`. -/
def quadraticAffineObjective (α : ℝ) (a : E) (A : E →L[ℝ] E) : E → ℝ :=
  fun x ↦ α + inner ℝ a x + (1 / 2 : ℝ) * inner ℝ (A x) x

/-- Evaluating the quadratic-affine objective gives its defining formula. -/
@[simp]
theorem quadraticAffineObjective_apply (α : ℝ) (a : E) (A : E →L[ℝ] E) (x : E) :
    quadraticAffineObjective α a A x =
      α + inner ℝ a x + (1 / 2 : ℝ) * inner ℝ (A x) x :=
  rfl

/-- The zero-quadratic specialization of `quadraticAffineObjective` is the affine objective
`x ↦ α + ⟪a, x⟫`. -/
@[simp]
theorem quadraticAffineObjective_zero_operator (α : ℝ) (a : E) :
    quadraticAffineObjective α a (0 : E →L[ℝ] E) = fun x ↦ α + inner ℝ a x := by
  funext x
  simp [quadraticAffineObjective]

/-- Helper for Example 5.1.2: restricting the quadratic-affine objective to a line produces a
scalar quadratic polynomial in the line parameter. -/
theorem quadraticAffineObjective_directionalSlice_eq
    (α : ℝ) (a : E) (A : E →L[ℝ] E) (x u : E) :
    directionalSlice (quadraticAffineObjective α a A) x u =
      fun t : ℝ ↦
        quadraticAffineObjective α a A x +
          (inner ℝ a u + (1 / 2 : ℝ) * (inner ℝ (A x) u + inner ℝ (A u) x)) * t +
          ((1 / 2 : ℝ) * inner ℝ (A u) u) * t ^ (2 : ℕ) := by
  -- Expand the line slice and collect the constant, linear, and quadratic scalar terms.
  funext t
  simp [directionalSlice, quadraticAffineObjective, inner_add_right, inner_add_left,
    inner_smul_right, inner_smul_left, map_add, map_smul, pow_two]
  ring

/-- The third directional derivative of a quadratic-affine objective vanishes identically. -/
-- Proof sketch: the Hessian is constant, so differentiating it once more gives zero.
theorem quadraticAffineObjective_thirdDirectionalDerivative_eq_zero
    (α : ℝ) (a : E) (A : E →L[ℝ] E) (x u : E) :
    thirdDirectionalDerivative (quadraticAffineObjective α a A) x u = 0 := by
  let c0 : ℝ := quadraticAffineObjective α a A x
  let c1 : ℝ := inner ℝ a u + (1 / 2 : ℝ) * (inner ℝ (A x) u + inner ℝ (A u) x)
  let c2 : ℝ := (1 / 2 : ℝ) * inner ℝ (A u) u
  have hlin : ContDiffAt ℝ 3 (fun t : ℝ ↦ c1 * t) 0 := by
    -- The linear coefficient contributes a smooth affine term in the slice parameter.
    simpa using contDiffAt_const.mul contDiffAt_id
  have hquad : ContDiffAt ℝ 3 (fun t : ℝ ↦ c2 * t ^ (2 : ℕ)) 0 := by
    -- The quadratic coefficient contributes a smooth quadratic term in the slice parameter.
    simpa using contDiffAt_const.mul (contDiffAt_id.pow 2)
  have hlinThird : iteratedDeriv 3 (fun t : ℝ ↦ c1 * t) 0 = 0 := by
    -- A linear function has vanishing third iterated derivative.
    calc
      iteratedDeriv 3 (fun t : ℝ ↦ c1 * t) 0 = c1 * iteratedDeriv 3 (fun t : ℝ ↦ t) 0 := by
        simpa using
          (iteratedDeriv_const_mul_field (n := 3) (x := 0) (c := c1) (f := fun t : ℝ ↦ t))
      _ = 0 := by
        simp [iteratedDeriv_fun_id]
  have hquadThird : iteratedDeriv 3 (fun t : ℝ ↦ c2 * t ^ (2 : ℕ)) 0 = 0 := by
    -- A quadratic polynomial also has vanishing third iterated derivative.
    calc
      iteratedDeriv 3 (fun t : ℝ ↦ c2 * t ^ (2 : ℕ)) 0 =
          c2 * iteratedDeriv 3 (fun t : ℝ ↦ t ^ (2 : ℕ)) 0 := by
            simpa using
              (iteratedDeriv_const_mul_field (n := 3) (x := 0) (c := c2)
                (f := fun t : ℝ ↦ t ^ (2 : ℕ)))
      _ = 0 := by
        simp [iteratedDeriv_pow]
  -- Rewrite the slice as a scalar quadratic polynomial and differentiate term-by-term.
  rw [thirdDirectionalDerivative, quadraticAffineObjective_directionalSlice_eq]
  calc
    iteratedDeriv 3 (fun t : ℝ ↦ c0 + c1 * t + c2 * t ^ (2 : ℕ)) 0
        = iteratedDeriv 3 (fun t : ℝ ↦ c0 + c1 * t) 0 +
            iteratedDeriv 3 (fun t : ℝ ↦ c2 * t ^ (2 : ℕ)) 0 := by
              simpa [Pi.add_apply] using
                iteratedDeriv_add (x := 0) (n := 3) (contDiffAt_const.add hlin) hquad
    _ = (iteratedDeriv 3 (fun t : ℝ ↦ c0) 0 +
          iteratedDeriv 3 (fun t : ℝ ↦ c1 * t) 0) +
            iteratedDeriv 3 (fun t : ℝ ↦ c2 * t ^ (2 : ℕ)) 0 := by
              congr 1
              simpa [Pi.add_apply] using
                iteratedDeriv_add (x := 0) (n := 3) (f := fun t : ℝ ↦ c0)
                  (g := fun t : ℝ ↦ c1 * t) contDiffAt_const hlin
    _ = 0 := by
          rw [iteratedDeriv_const, hlinThird, hquadThird]
          simp

variable [CompleteSpace E]

/-- The gradient of the quadratic-affine objective is `x ↦ a + A x` when `A` is self-adjoint. -/
-- Proof sketch: differentiate the affine term and the quadratic form; self-adjointness identifies
-- the symmetrized Hessian contribution with `A`.
theorem quadraticAffineObjective_gradient_eq
    (α : ℝ) (a : E) (A : E →L[ℝ] E) (hA : IsSelfAdjoint A) :
    ∇ (quadraticAffineObjective α a A) = fun x ↦ a + A x := by
  have hgradAt : ∀ x : E, HasGradientAt (quadraticAffineObjective α a A) (a + A x) x := by
    intro x
    have hAffine : HasFDerivAt (fun y : E ↦ inner ℝ a y) (innerSL ℝ a) x := by
      -- The affine term differentiates to the fixed Riesz functional `innerSL ℝ a`.
      simpa using (innerSL ℝ a).hasFDerivAt
    have hQuad' : HasFDerivAt (fun y : E ↦ inner ℝ (A y) y) (2 • innerSL ℝ (A x)) x := by
      -- Self-adjointness collapses the two product-rule contributions to the same vector `A x`.
      convert (A.hasFDerivAt.inner ℝ (hasFDerivAt_id x))
      ext y
      simp only [ContinuousLinearMap.coe_smul', coe_innerSL_apply, Pi.smul_apply, nsmul_eq_mul,
        Nat.cast_ofNat, id_eq, ContinuousLinearMap.coe_comp', Function.comp_apply,
        ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_id', fderivInnerCLM_apply]
      calc
        2 * inner ℝ (A x) y = inner ℝ y (A x) + inner ℝ y (A x) := by
          rw [real_inner_comm y (A x)]
          ring
        _ = inner ℝ y (A x) + inner ℝ (A y) x := by
          congr 1
          exact (hA.isSymmetric y x).symm
        _ = inner ℝ (A x) y + inner ℝ (A y) x := by
          rw [real_inner_comm y (A x)]
    have hQuad0 : HasFDerivAt (fun y : E ↦ (1 / 2 : ℝ) • inner ℝ (A y) y)
        ((1 / 2 : ℝ) • (2 • innerSL ℝ (A x))) x :=
      hQuad'.const_smul (1 / 2 : ℝ)
    have hscale : ((1 / 2 : ℝ) • (2 • innerSL ℝ (A x))) = innerSL ℝ (A x) := by
      -- The prefactor `1 / 2` cancels the doubled product-rule contribution.
      apply ContinuousLinearMap.ext
      intro y
      simp
    have hQuad : HasFDerivAt (fun y : E ↦ (1 / 2 : ℝ) • inner ℝ (A y) y)
        (innerSL ℝ (A x)) x :=
      hscale ▸ hQuad0
    have hSum : HasFDerivAt
        (fun y : E ↦ inner ℝ a y + (1 / 2 : ℝ) • inner ℝ (A y) y)
        (innerSL ℝ a + innerSL ℝ (A x)) x := by
      -- Add the affine and quadratic derivative contributions.
      simpa [Pi.add_apply, add_assoc] using hAffine.add hQuad
    have hDeriv0 : HasFDerivAt
        (fun y : E ↦ α + (inner ℝ a y + (1 / 2 : ℝ) • inner ℝ (A y) y))
        (innerSL ℝ a + innerSL ℝ (A x)) x :=
      hSum.const_add α
    have hDeriv : HasFDerivAt (quadraticAffineObjective α a A)
        (innerSL ℝ a + innerSL ℝ (A x)) x := by
      -- Rewrite the source-facing objective to the assembled affine-plus-quadratic expression.
      convert hDeriv0 using 1
      funext y
      simp [quadraticAffineObjective, add_assoc, smul_eq_mul]
    have hdual :
        (InnerProductSpace.toDual ℝ E).symm (innerSL ℝ a + innerSL ℝ (A x)) = a + A x := by
      -- Identify the dual functional with its Riesz representative.
      apply (InnerProductSpace.toDual ℝ E).injective
      ext z
      simp [innerSL_apply_apply]
    simpa [hdual] using hDeriv.hasGradientAt
  -- Package the pointwise gradient witnesses into the global gradient formula.
  exact gradient_eq hgradAt

/-- The Hessian of the quadratic-affine objective is the constant operator `A` when `A` is
self-adjoint. -/
-- Proof sketch: differentiate `quadraticAffineObjective_gradient_eq`; the affine term vanishes and
-- the derivative of `x ↦ A x` is the constant operator `A`.
theorem quadraticAffineObjective_hessian_eq
    (α : ℝ) (a : E) (A : E →L[ℝ] E) (hA : IsSelfAdjoint A) (x : E) :
    hessian (quadraticAffineObjective α a A) x = A := by
  have hgradDeriv : HasFDerivAt (∇ (quadraticAffineObjective α a A)) A x := by
    -- Rewrite the gradient to the affine map `y ↦ a + A y`, whose derivative is exactly `A`.
    simpa [quadraticAffineObjective_gradient_eq α a A hA] using (A.hasFDerivAt.const_add a)
  -- The Hessian is the derivative of the gradient.
  simpa [hessian] using hgradDeriv.fderiv

omit [CompleteSpace E] in
/-- Helper for Example 5.1.2: the quadratic-affine objective is `C³` on the whole space. -/
lemma quadraticAffineObjective_contDiff
    (α : ℝ) (a : E) (A : E →L[ℝ] E) :
    ContDiff ℝ 3 (quadraticAffineObjective α a A) := by
  have hAffine : ContDiff ℝ 3 (fun x : E ↦ inner ℝ a x) := by
    -- The affine functional is smooth.
    simpa using (innerSL ℝ a).contDiff
  have hQuad : ContDiff ℝ 3 (fun x : E ↦ inner ℝ (A x) x) := by
    -- The quadratic term is the inner product of two smooth maps.
    simpa using ContDiff.inner ℝ A.contDiff contDiff_id
  have hSum : ContDiff ℝ 3
      (fun x : E ↦ inner ℝ a x + (1 / 2 : ℝ) • inner ℝ (A x) x) := by
    -- Combine the affine and quadratic smooth pieces.
    simpa [Pi.add_apply, add_assoc] using hAffine.add (hQuad.const_smul (1 / 2 : ℝ))
  have hShifted : ContDiff ℝ 3
      (fun x : E ↦ α + (inner ℝ a x + (1 / 2 : ℝ) • inner ℝ (A x) x)) :=
    contDiff_const.add hSum
  -- Rewrite back to the source-facing objective.
  convert hShifted using 1
  funext x
  simp [quadraticAffineObjective, add_assoc, smul_eq_mul]

/-- Example 5.1.2: if `A` is positive, then the quadratic-affine objective
`f(x) = α + ⟪a, x⟫ + (1 / 2) ⟪A x, x⟫` on all of `E` is self-concordant with self-concordance
constant `M_f = 0`. -/
-- Proof sketch: `A.IsPositive` gives the Hessian positive-semidefinite condition, the quadratic
-- objective is `C^3` on all of `E`, and
-- `quadraticAffineObjective_thirdDirectionalDerivative_eq_zero` makes the cubic bound with
-- constant `0` immediate.
theorem quadraticAffineObjective_isSelfConcordantOnWith_zero
    (α : ℝ) (a : E) (A : E →L[ℝ] E) (hA : A.IsPositive) :
    IsSelfConcordantOnWith (Set.univ : Set E) 0 (quadraticAffineObjective α a A) := by
  have hA_self : IsSelfAdjoint A := hA.isSelfAdjoint
  have h2le3 : (2 : WithTop ℕ∞) ≤ 3 := by
    norm_num
  have hC2 : ContDiffOn ℝ 2 (quadraticAffineObjective α a A) (Set.univ : Set E) := by
    -- The global `C³` regularity immediately yields the `C²` regularity needed for convexity.
    exact (quadraticAffineObjective_contDiff α a A).of_le h2le3 |>.contDiffOn
  refine
    { isOpen_domain := isOpen_univ
      contDiffOn := (quadraticAffineObjective_contDiff α a A).contDiffOn
      convexOn := ?_
      third_deriv_bound := ?_ }
  · -- Use the constant positive Hessian to obtain convexity on the whole space.
    apply (convexOn_iff_hessian_isPositive isOpen_univ convex_univ hC2).2
    intro x hx
    simpa [quadraticAffineObjective_hessian_eq α a A hA_self x] using hA
  · intro x hx u
    -- The third directional derivative vanishes, so the `M_f = 0` cubic bound is immediate.
    rw [quadraticAffineObjective_thirdDirectionalDerivative_eq_zero α a A x u]
    simp

end
