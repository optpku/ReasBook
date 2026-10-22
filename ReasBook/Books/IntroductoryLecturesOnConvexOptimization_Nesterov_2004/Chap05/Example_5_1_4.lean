/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Example_5_1_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_1_4

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped Gradient HessianLocalNorm

noncomputable section

universe u

/- Example 5.1.4 lies in the Chapter 5 self-concordance / logarithmic-sublevel-barrier domain.

Sampled owner-style declarations:
* `quadraticAffineObjective` from `Example_5_1_2`, the chapter source-facing owner for affine-
  quadratic objectives on a real Hilbert space;
* `sublevelLogBarrier` from `Theorem_5_1_4`, the chapter owner for barriers `x ↦ -log (β - f x)`;
* `IsStandardSelfConcordantOn` from `Definition_5_1_1`, the core self-concordance owner for
  constant `1`;
* `ContinuousLinearMap.IsPositive`, the canonical positivity owner for self-adjoint positive
  semidefinite operators.

Source/core/bridge triage:
* source-facing: the logarithmic barrier of the concave affine-quadratic potential
  `φ(x) = α + ⟪a, x⟫ - (1 / 2) ⟪A x, x⟫`;
* core/canonical: `sublevelLogBarrier (quadraticAffineObjective (-α) (-a) A) 0` on
  `{x : E | x ∈ (Set.univ : Set E) ∧ quadraticAffineObjective (-α) (-a) A x < 0}`;
* bridge/view: the sign rewrite
  `0 - quadraticAffineObjective (-α) (-a) A x = α + ⟪a, x⟫ - (1 / 2) ⟪A x, x⟫`.

Primitive data:
* `α`, `a`, and `A`.

Derived API:
* the generic strict sublevel set expression as a proof bridge for the textbook positivity set;
* the generic Chapter 5 sublevel barrier as a proof bridge for the textbook `-log φ`.

This example remains source-facing at the theorem surface: the public statement keeps the textbook
positivity domain and logarithmic barrier, while the Chapter 5 sublevel-barrier owners remain the
canonical internal bridge. -/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- The canonical strict-sublevel domain
`{x | quadraticAffineObjective (-α) (-a) A x < 0}` is exactly the textbook positivity domain
`{x | 0 < α + ⟪a, x⟫ - (1 / 2) ⟪A x, x⟫}`. -/
theorem quadraticAffineObjective_neg_strictSublevel_eq
    (α : ℝ) (a : E) (A : E →L[ℝ] E) :
    {x : E | quadraticAffineObjective (-α) (-a) A x < 0} =
      {x : E | 0 < α + inner ℝ a x - (1 / 2 : ℝ) * inner ℝ (A x) x} := by
  ext x
  change quadraticAffineObjective (-α) (-a) A x < 0 ↔
    0 < α + inner ℝ a x - (1 / 2 : ℝ) * inner ℝ (A x) x
  rw [quadraticAffineObjective_apply]
  simp only [inner_neg_left]
  constructor <;> intro hx <;> linarith

/- The canonical sublevel-log-barrier owner
`sublevelLogBarrier (quadraticAffineObjective (-α) (-a) A) 0` evaluates to the textbook
logarithmic barrier of the concave affine-quadratic potential. -/
theorem sublevelLogBarrier_quadraticAffineObjective_neg_eq
    (α : ℝ) (a : E) (A : E →L[ℝ] E) :
    sublevelLogBarrier (quadraticAffineObjective (-α) (-a) A) 0 =
      fun x ↦ -Real.log (α + inner ℝ a x - (1 / 2 : ℝ) * inner ℝ (A x) x) := by
  funext x
  rw [sublevelLogBarrier_apply, quadraticAffineObjective_apply]
  simp only [inner_neg_left]
  congr 1
  ring_nf

variable [CompleteSpace E]

/-- Helper for Example 5.1.4: a `C²` objective has a differentiable gradient because the gradient
is the Fréchet derivative transported through the Riesz isomorphism. -/
private theorem differentiableAt_gradient_of_contDiffAt_two
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) :
    DifferentiableAt ℝ (∇ f) x := by
  -- Rewrite the gradient through the continuous linear Riesz isomorphism and differentiate the
  -- Fréchet derivative field.
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfdiff : DifferentiableAt ℝ (fderiv ℝ f) x := by
    exact
      (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))).differentiableAt
        one_ne_zero
  change DifferentiableAt ℝ (fun y ↦ D (fderiv ℝ f y)) x
  exact (D.hasFDerivAt.comp x hfdiff.hasFDerivAt).differentiableAt

/-- Helper for Example 5.1.4: the quadratic-affine source objective has nonnegative second
directional derivative because its Hessian is the positive operator `A`. -/
private theorem quadraticAffineObjective_secondDirectionalDerivative_nonneg
    (α : ℝ) (a : E) (A : E →L[ℝ] E) (hA : A.IsPositive) (x u : E) :
    0 ≤ secondDirectionalDerivative (quadraticAffineObjective (-α) (-a) A) x u := by
  let f : E → ℝ := quadraticAffineObjective (-α) (-a) A
  have hbase_self : IsSelfConcordantOnWith (Set.univ : Set E) 0 f := by
    simpa [f] using quadraticAffineObjective_isSelfConcordantOnWith_zero (-α) (-a) A hA
  have hcontAt : ContDiffAt ℝ 3 f x := by
    -- Restrict the global `C³` regularity of the quadratic owner to the current point.
    exact hbase_self.contDiffOn.contDiffAt (hbase_self.isOpen_domain.mem_nhds (by simp))
  have hdiff : DifferentiableAt ℝ f x := hcontAt.differentiableAt (by norm_num)
  have hgrad : DifferentiableAt ℝ (∇ f) x := by
    -- The second-derivative bridge needs differentiability of the gradient.
    exact differentiableAt_gradient_of_contDiffAt_two
      (hcontAt.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3))
  -- Rewrite the source second directional derivative as the Hessian quadratic form.
  rw [secondDirectionalDerivative_eq_hessian_quadratic_form hdiff hgrad]
  exact hbase_self.hessian_posSemidef (by simp) u

/-- Helper for Example 5.1.4: after normalizing by the positive slack `s = -f x`, the canonical
barrier formulas become the textbook `ω₁`/`ω₂` identities. -/
private theorem quadraticAffineBarrierNormalizedData
    (α : ℝ) (a : E) (A : E →L[ℝ] E) (hA : A.IsPositive) (x u : E)
    (hx : quadraticAffineObjective (-α) (-a) A x < 0) :
    let f : E → ℝ := quadraticAffineObjective (-α) (-a) A
    let F : E → ℝ := sublevelLogBarrier f 0
    let s : ℝ := -f x
    let omega1 : ℝ := inner ℝ (∇ f x) u / s
    let omega2 : ℝ := secondDirectionalDerivative f x u / s
    ‖u‖[F; x] ^ (2 : ℕ) = omega1 ^ (2 : ℕ) + omega2 ∧
      thirdDirectionalDerivative F x u = 2 * omega1 ^ (3 : ℕ) + 3 * omega1 * omega2 := by
  dsimp
  let f : E → ℝ := quadraticAffineObjective (-α) (-a) A
  let F : E → ℝ := sublevelLogBarrier f 0
  let s : ℝ := -f x
  let omega1 : ℝ := inner ℝ (∇ f x) u / s
  let omega2 : ℝ := secondDirectionalDerivative f x u / s
  have hbase_self : IsSelfConcordantOnWith (Set.univ : Set E) 0 f := by
    simpa [f] using quadraticAffineObjective_isSelfConcordantOnWith_zero (-α) (-a) A hA
  have hs : 0 < s := by
    -- The barrier slack is exactly the positive quantity `-f x`.
    dsimp [s]
    linarith
  have hnorm_sq :
      ‖u‖[F; x] ^ (2 : ℕ) =
        secondDirectionalDerivative f x u / s +
          (inner ℝ (∇ f x) u) ^ (2 : ℕ) / s ^ (2 : ℕ) := by
    -- Read off the barrier local norm from the canonical Chapter 5 formula.
    simpa [F, s] using
      hbase_self.sublevel_barrier_local_norm_sq 0 (x := x) (u := u) (hx := by simp) (hβ := hx)
  have hthird :
      thirdDirectionalDerivative F x u =
        thirdDirectionalDerivative f x u / s +
          3 * (inner ℝ (∇ f x) u / s) * (secondDirectionalDerivative f x u / s) +
          2 * (inner ℝ (∇ f x) u / s) ^ (3 : ℕ) := by
    -- The barrier third derivative is the normalized cubic combination of the source data.
    simpa [F, s] using
      hbase_self.sublevel_barrier_third_deriv_formula 0
        (x := x) (u := u) (hx := by simp) (hβ := hx)
  have hthird_source : thirdDirectionalDerivative f x u = 0 := by
    -- The quadratic source owner has vanishing third directional derivative.
    simpa [f] using quadraticAffineObjective_thirdDirectionalDerivative_eq_zero (-α) (-a) A x u
  constructor
  · -- Rewrite the local norm square into the textbook `ω₁² + ω₂` form.
    calc
      ‖u‖[F; x] ^ (2 : ℕ)
          = secondDirectionalDerivative f x u / s +
              (inner ℝ (∇ f x) u) ^ (2 : ℕ) / s ^ (2 : ℕ) := hnorm_sq
      _ = omega1 ^ (2 : ℕ) + omega2 := by
            dsimp [omega1, omega2]
            field_simp [hs.ne']
            ring
  · -- The vanishing source cubic term leaves exactly `2 ω₁³ + 3 ω₁ ω₂`.
    calc
      thirdDirectionalDerivative F x u
          = thirdDirectionalDerivative f x u / s +
              3 * (inner ℝ (∇ f x) u / s) * (secondDirectionalDerivative f x u / s) +
              2 * (inner ℝ (∇ f x) u / s) ^ (3 : ℕ) := hthird
      _ = 2 * omega1 ^ (3 : ℕ) + 3 * omega1 * omega2 := by
            rw [hthird_source]
            dsimp [omega1, omega2]
            ring

/-- Helper for Example 5.1.4: the quadratic-affine barrier Hessian is positive semidefinite on
its strict sublevel domain because it dominates the square of the barrier gradient pairing. -/
private theorem quadraticAffineBarrierHessianQuadraticForm_nonneg
    (α : ℝ) (a : E) (A : E →L[ℝ] E) (hA : A.IsPositive) (x u : E)
    (hx : quadraticAffineObjective (-α) (-a) A x < 0) :
    0 ≤ inner ℝ u
      (hessian (sublevelLogBarrier (quadraticAffineObjective (-α) (-a) A) 0) x u) := by
  let f : E → ℝ := quadraticAffineObjective (-α) (-a) A
  let F : E → ℝ := sublevelLogBarrier f 0
  have hbase_self : IsSelfConcordantOnWith (Set.univ : Set E) 0 f := by
    simpa [f] using quadraticAffineObjective_isSelfConcordantOnWith_zero (-α) (-a) A hA
  have hineq :
      inner ℝ u (hessian F x u) ≥
        (inner ℝ (∇ F x) u) ^ (2 : ℕ) := by
    -- Use the canonical barrier lower bound on the Hessian quadratic form.
    simpa [f, F] using
      hbase_self.sublevelLogBarrier_hessian_quadraticForm_ge_gradient_sq 0
        (x := x) (h := u) (hx := by simp) (hβ := hx)
  have hsq_nonneg : 0 ≤ (inner ℝ (∇ F x) u) ^ (2 : ℕ) := by
    positivity
  exact le_trans hsq_nonneg hineq

/-- Helper for Example 5.1.4: the normalized scalar cubic estimate closes the self-concordance
bound as soon as the curvature term is nonnegative. -/
private theorem omega_cubic_bound_of_nonneg
    {omega1 omega2 : ℝ} (homega2 : 0 ≤ omega2) :
    |2 * omega1 ^ (3 : ℕ) + 3 * omega1 * omega2| ≤
      2 * (Real.sqrt (omega1 ^ (2 : ℕ) + omega2)) ^ (3 : ℕ) := by
  let total : ℝ := omega1 ^ (2 : ℕ) + omega2
  have htotal_nonneg : 0 ≤ total := by
    dsimp [total]
    nlinarith [sq_nonneg omega1, homega2]
  have hpoly :
      4 * total ^ (3 : ℕ) - (2 * omega1 ^ (3 : ℕ) + 3 * omega1 * omega2) ^ (2 : ℕ) =
        omega2 ^ (2 : ℕ) * (3 * omega1 ^ (2 : ℕ) + 4 * omega2) := by
    dsimp [total]
    ring
  have hsq :
      (2 * omega1 ^ (3 : ℕ) + 3 * omega1 * omega2) ^ (2 : ℕ) ≤ 4 * total ^ (3 : ℕ) := by
    have hrhs_nonneg :
        0 ≤ omega2 ^ (2 : ℕ) * (3 * omega1 ^ (2 : ℕ) + 4 * omega2) := by
      nlinarith [sq_nonneg omega1, sq_nonneg omega2, homega2]
    nlinarith [hpoly]
  have hright_sq :
      (2 * (Real.sqrt total) ^ (3 : ℕ)) ^ (2 : ℕ) = 4 * total ^ (3 : ℕ) := by
    calc
      (2 * (Real.sqrt total) ^ (3 : ℕ)) ^ (2 : ℕ)
          = 4 * ((Real.sqrt total) ^ (2 : ℕ)) ^ (3 : ℕ) := by
              ring
      _ = 4 * total ^ (3 : ℕ) := by
            rw [Real.sq_sqrt htotal_nonneg]
  have hsq' :
      |2 * omega1 ^ (3 : ℕ) + 3 * omega1 * omega2| ^ (2 : ℕ) ≤
        (2 * (Real.sqrt total) ^ (3 : ℕ)) ^ (2 : ℕ) := by
    rw [sq_abs, hright_sq]
    exact hsq
  have hleft_nonneg : 0 ≤ |2 * omega1 ^ (3 : ℕ) + 3 * omega1 * omega2| := by
    exact abs_nonneg _
  have hright_nonneg : 0 ≤ 2 * (Real.sqrt total) ^ (3 : ℕ) := by
    positivity
  nlinarith

/-- Example 5.1.4: if `A` is positive, then the logarithmic barrier attached to the affine-
quadratic potential `φ(x) = α + ⟪a, x⟫ - (1 / 2) ⟪A x, x⟫` is standard self-concordant on its
positivity domain `{x | 0 < φ(x)}`. The generic Chapter 5 sublevel-barrier owners are only a
proof bridge behind this source-facing formulation. -/
theorem logAffineQuadraticBarrier_isStandardSelfConcordantOn
    (α : ℝ) (a : E) (A : E →L[ℝ] E) (hA : A.IsPositive) :
    IsStandardSelfConcordantOn
      {x : E | 0 < α + inner ℝ a x - (1 / 2 : ℝ) * inner ℝ (A x) x}
      (fun x ↦ -Real.log (α + inner ℝ a x - (1 / 2 : ℝ) * inner ℝ (A x) x)) := by
  let f : E → ℝ := quadraticAffineObjective (-α) (-a) A
  let dom : Set E := {x : E | f x < 0}
  let F : E → ℝ := sublevelLogBarrier f 0
  have hdom :
      dom = {x : E | 0 < α + inner ℝ a x - (1 / 2 : ℝ) * inner ℝ (A x) x} := by
    simpa [dom, f] using quadraticAffineObjective_neg_strictSublevel_eq α a A
  have hfun :
      F = fun x ↦ -Real.log (α + inner ℝ a x - (1 / 2 : ℝ) * inner ℝ (A x) x) := by
    simpa [F, f] using sublevelLogBarrier_quadraticAffineObjective_neg_eq α a A
  have hbase_self : IsSelfConcordantOnWith (Set.univ : Set E) 0 f := by
    simpa [f] using quadraticAffineObjective_isSelfConcordantOnWith_zero (-α) (-a) A hA
  have hf_cont : ContDiff ℝ 3 f := by
    -- The quadratic owner is globally `C³`.
    simpa [f] using quadraticAffineObjective_contDiff (-α) (-a) A
  have hcanonical : IsStandardSelfConcordantOn dom F := by
    have hdom_open : IsOpen dom := by
      -- The strict sublevel of the continuous quadratic owner is open.
      simpa [dom] using isOpen_lt hf_cont.continuous continuous_const
    have hdom_convex : Convex ℝ dom := by
      -- The domain is the strict sublevel set of a convex quadratic owner over `univ`.
      simpa [dom] using hbase_self.convexOn.convex_lt (0 : ℝ)
    have hF_contDiffOn : ContDiffOn ℝ 3 F dom := by
      intro x hx
      have hf_contAt : ContDiffAt ℝ 3 f x := hf_cont.contDiffAt
      have hslack_pos : 0 < 0 - f x := sub_pos.mpr hx
      have hslack_cont : ContDiffAt ℝ 3 (fun y : E ↦ (0 : ℝ) - f y) x :=
        contDiffAt_const.sub hf_contAt
      -- Compose `log` with the positive slack and then add the outer minus sign.
      simpa only [F, sublevelLogBarrier] using
        (((Real.contDiffAt_log.2 hslack_pos.ne').comp x hslack_cont).neg.contDiffWithinAt)
    have hF_C2 : ContDiffOn ℝ 2 F dom := by
      exact hF_contDiffOn.of_le (by norm_num)
    refine
      { isOpen_domain := hdom_open
        contDiffOn := hF_contDiffOn
        convexOn := ?_
        third_deriv_bound := ?_ }
    · -- Route correction: use the canonical barrier Hessian lower bound instead of the old slice.
      refine (convexOn_iff_hessian_quadratic_form_nonneg hdom_open hdom_convex hF_C2).2 ?_
      intro x hx u
      simpa [real_inner_comm] using
        quadraticAffineBarrierHessianQuadraticForm_nonneg α a A hA x u
          (by simpa [dom, f] using hx)
    · intro x hx u
      let s : ℝ := -f x
      let omega1 : ℝ := inner ℝ (∇ f x) u / s
      let omega2 : ℝ := secondDirectionalDerivative f x u / s
      have hx0 : f x < 0 := by
        simpa [dom] using hx
      have hs : 0 < s := by
        -- The canonical slack is positive on the strict sublevel domain.
        dsimp [s]
        linarith
      have hdir :
          ‖u‖[F; x] ^ (2 : ℕ) = omega1 ^ (2 : ℕ) + omega2 ∧
            thirdDirectionalDerivative F x u =
              2 * omega1 ^ (3 : ℕ) + 3 * omega1 * omega2 := by
        simpa [f, F, s, omega1, omega2] using
          quadraticAffineBarrierNormalizedData α a A hA x u hx0
      have homega2_nonneg : 0 ≤ omega2 := by
        -- The source quadratic term contributes the nonnegative normalized curvature.
        dsimp [omega2, s]
        exact div_nonneg
          (quadraticAffineObjective_secondDirectionalDerivative_nonneg α a A hA x u)
          hs.le
      have hnorm_sq : ‖u‖[F; x] ^ (2 : ℕ) = omega1 ^ (2 : ℕ) + omega2 := hdir.1
      have homega_nonneg : 0 ≤ omega1 ^ (2 : ℕ) + omega2 := by
        have hsq_nonneg : 0 ≤ ‖u‖[F; x] ^ (2 : ℕ) := by
          positivity
        rwa [hnorm_sq] at hsq_nonneg
      have hsqrt_norm :
          Real.sqrt (omega1 ^ (2 : ℕ) + omega2) = ‖u‖[F; x] := by
        have hsq :
            (Real.sqrt (omega1 ^ (2 : ℕ) + omega2)) ^ (2 : ℕ) =
              ‖u‖[F; x] ^ (2 : ℕ) := by
          rw [Real.sq_sqrt homega_nonneg, hnorm_sq]
        have hsqrt_nonneg : 0 ≤ Real.sqrt (omega1 ^ (2 : ℕ) + omega2) := by
          exact Real.sqrt_nonneg _
        have hnorm_nonneg : 0 ≤ ‖u‖[F; x] := hessianLocalNorm_nonneg F x u
        nlinarith
      calc
        |thirdDirectionalDerivative F x u| = |2 * omega1 ^ (3 : ℕ) + 3 * omega1 * omega2| := by
          rw [hdir.2]
        _ ≤ 2 * (Real.sqrt (omega1 ^ (2 : ℕ) + omega2)) ^ (3 : ℕ) := by
          exact omega_cubic_bound_of_nonneg homega2_nonneg
        _ = 2 * ‖u‖[F; x] ^ (3 : ℕ) := by
          rw [hsqrt_norm]
        _ = 2 * (1 : ℝ) * ‖u‖[F; x] ^ (3 : ℕ) := by
          ring
  convert hcanonical using 1
  · exact hdom.symm
  · exact hfun.symm

end
