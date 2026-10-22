/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_17
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_35

/- Proposition 2.35 lies in constrained projected-gradient models on real inner-product spaces.

Owner declarations sampled for this refinement:
* `affineModelAt` in `Chap01/FirstOrderTaylorModel`, the primitive first-order model with an
  explicit gradient field;
* `firstOrderTaylorModelAt` in `Chap01/Definition_1_4_17`, the source-facing specialization using
  the totalized gradient;
* `IsProjectionPointOn.iff_isMinOn` in `Definition_2_33`, the owner bridge from distance
  minimizers to projection points;
* `IsProjectionPointOn.eq` in `Theorem_2_33`, the owner uniqueness API for projection points on a
  convex set;
* `HasFDerivAt` together with `InnerProductSpace.toDualMap`, the primitive derivative owner for an
  explicit first-order datum `g` without completeness assumptions;
* `IsLocalMinOn.hasFDerivWithinAt_nonneg` in mathlib, the owner first-order optimality API used to
  recover the projection-point inequality for the objective minimizer.

Best owner abstraction:
* `HasFDerivAt f (InnerProductSpace.toDualMap ℝ E g) tStar` together with
  `IsProjectionPointOn Q (tStar - ((γ : ℝ)⁻¹) • g) p`.

Source/core/bridge triage:
* source-facing: Proposition 2.35 in its textbook `firstOrderTaylorModelAt` form;
* core/canonical: the owner theorem below for `affineModelAt`, `HasFDerivAt`, and
  `IsProjectionPointOn`;
* bridge/view: the specialization from the explicit gradient witness to the source-facing
  `firstOrderTaylorModelAt` statement.

Primitive data:
* the feasible set `Q`, objective `f`, positive inverse-stepsize parameter `γ`, gradient
  witness `g`, and points `t0`,
  `tStar`;
* convexity of `Q`;
* feasibility and minimizing hypotheses for `t0` and `tStar`.

Derived API:
* the model minimizer `t0` is promoted to a projection point by the completed-square rewrite for
  the regularized affine model;
* the primitive derivative witness represented by `g` is fed directly to
  `IsLocalMinOn.hasFDerivWithinAt_nonneg`, and then `tStar` is promoted to the same projection
  point by the first-order optimality inequality and
  `norm_eq_iInf_iff_real_inner_le_zero`;
* convexity then identifies the two projection points.
-/

open scoped Gradient

noncomputable section

universe u

section RegularizedAffineModel

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {Q : Set E} {f : E → ℝ} {g : E} {γ : NNRealˣ}

/-- Completing the square rewrites the quadratically regularized affine model at `xBar` with
constant gradient witness `g` as a constant plus a squared-distance term from the explicit step
`xBar - γ⁻¹ • g`. -/
theorem quadraticallyRegularizedObjective_affineModelAt_eq_completedSquare
    (f : E → ℝ) (g xBar x : E) (γ : NNRealˣ) :
    quadraticallyRegularizedObjective (affineModelAt f (fun _ ↦ g) xBar) (γ : ℝ) xBar x =
      f xBar + ((γ : ℝ) / 2) * ‖x - (xBar - ((γ : ℝ)⁻¹) • g)‖ ^ (2 : ℕ) -
        (1 / (2 * (γ : ℝ))) * ‖g‖ ^ (2 : ℕ) := by
  have hγ : (γ : ℝ) ≠ 0 := by
    exact (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero γ))).ne'
  have hsub :
      x - (xBar - ((γ : ℝ)⁻¹) • g) = (x - xBar) + ((γ : ℝ)⁻¹) • g := by
    abel_nf
  have hsq :
      ((γ : ℝ) / 2 : ℝ) * ‖x - (xBar - ((γ : ℝ)⁻¹) • g)‖ ^ (2 : ℕ) =
        ((γ : ℝ) / 2 : ℝ) * ‖x - xBar‖ ^ (2 : ℕ) +
          inner ℝ g (x - xBar) +
          (1 / (2 * (γ : ℝ))) * ‖g‖ ^ (2 : ℕ) := by
    calc
      ((γ : ℝ) / 2 : ℝ) * ‖x - (xBar - ((γ : ℝ)⁻¹) • g)‖ ^ (2 : ℕ)
          = ((γ : ℝ) / 2 : ℝ) *
              inner ℝ (x - (xBar - ((γ : ℝ)⁻¹) • g)) (x - (xBar - ((γ : ℝ)⁻¹) • g)) := by
                rw [real_inner_self_eq_norm_sq]
      _ = ((γ : ℝ) / 2 : ℝ) *
            inner ℝ ((x - xBar) + ((γ : ℝ)⁻¹) • g) ((x - xBar) + ((γ : ℝ)⁻¹) • g) := by
            rw [hsub]
      _ = ((γ : ℝ) / 2 : ℝ) *
            (inner ℝ (x - xBar) (x - xBar) +
              inner ℝ (x - xBar) (((γ : ℝ)⁻¹) • g) +
              inner ℝ (((γ : ℝ)⁻¹) • g) (x - xBar) +
              inner ℝ (((γ : ℝ)⁻¹) • g) (((γ : ℝ)⁻¹) • g)) := by
                rw [inner_add_add_self]
      _ = ((γ : ℝ) / 2 : ℝ) * ‖x - xBar‖ ^ (2 : ℕ) +
            inner ℝ g (x - xBar) +
            (1 / (2 * (γ : ℝ))) * ‖g‖ ^ (2 : ℕ) := by
              rw [real_inner_self_eq_norm_sq, inner_smul_right, real_inner_smul_left,
                real_inner_smul_left, inner_smul_right, real_inner_self_eq_norm_sq]
              have hcomm : inner ℝ (x - xBar) g = inner ℝ g (x - xBar) := by
                simpa using (real_inner_comm (x - xBar) g).symm
              rw [hcomm]
              field_simp [hγ]
              ring
  rw [quadraticallyRegularizedObjective_apply, affineModelAt_apply]
  calc
    f xBar + inner ℝ g (x - xBar) + ((γ : ℝ) / 2) * ‖x - xBar‖ ^ (2 : ℕ) =
        f xBar +
          ((((γ : ℝ) / 2 : ℝ) * ‖x - xBar‖ ^ (2 : ℕ)) +
            inner ℝ g (x - xBar) +
            (1 / (2 * (γ : ℝ))) * ‖g‖ ^ (2 : ℕ)) -
          (1 / (2 * (γ : ℝ))) * ‖g‖ ^ (2 : ℕ) := by
      ring
    _ = f xBar + ((γ : ℝ) / 2) * ‖x - (xBar - ((γ : ℝ)⁻¹) • g)‖ ^ (2 : ℕ) -
          (1 / (2 * (γ : ℝ))) * ‖g‖ ^ (2 : ℕ) := by
      rw [← hsq]

/-- Proposition 2.35 at the owner layer: if `t0 ∈ Q` minimizes the quadratically regularized
affine model determined by an explicit first-order witness `g` at `tStar`, and `tStar ∈ Q`
minimizes `f` on the convex set `Q`, then `t0 = tStar`. -/
-- Proof sketch: the completed-square identity rewrites the regularized affine model as a positive
-- multiple of the squared distance to `tStar - μ⁻¹ • g` plus a constant, so the minimizer `t0`
-- is a projection point of that explicit step onto `Q`. The minimizing property of `tStar`
-- and the primitive Fréchet derivative witness represented by `g` give the same projection-point
-- statement for `tStar` through the first-order optimality step.
-- Convexity of `Q` then gives projection uniqueness.
theorem eq_of_isMinOn_quadraticallyRegularizedObjective_affineModelAt_of_isMinOn
    (hQ_convex : Convex ℝ Q) {t0 tStar : E}
    (htStar_fderiv : HasFDerivAt f (InnerProductSpace.toDualMap ℝ E g) tStar)
    (ht0_mem : t0 ∈ Q) (htStar_mem : tStar ∈ Q)
    (ht0 : IsMinOn
      (quadraticallyRegularizedObjective (affineModelAt f (fun _ ↦ g) tStar) (γ : ℝ) tStar) Q t0)
    (htStar : IsMinOn f Q tStar) :
    t0 = tStar := by
  have hγ : 0 < (γ : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero γ))
  let y : E := tStar - ((γ : ℝ)⁻¹) • g
  let model : E → ℝ :=
    quadraticallyRegularizedObjective (affineModelAt f (fun _ ↦ g) tStar) (γ : ℝ) tStar
  have ht0_proj : IsProjectionPointOn Q y t0 := by
    refine (IsProjectionPointOn.iff_isMinOn).2 ?_
    refine ⟨ht0_mem, ?_⟩
    rw [isMinOn_iff]
    intro x hx
    have ht0_model :
        model t0 =
          f tStar + ((γ : ℝ) / 2) * ‖t0 - y‖ ^ (2 : ℕ) -
            (1 / (2 * (γ : ℝ))) * ‖g‖ ^ (2 : ℕ) := by
      simpa [model, y] using
        quadraticallyRegularizedObjective_affineModelAt_eq_completedSquare f g tStar t0 γ
    have hx_model :
        model x =
          f tStar + ((γ : ℝ) / 2) * ‖x - y‖ ^ (2 : ℕ) -
            (1 / (2 * (γ : ℝ))) * ‖g‖ ^ (2 : ℕ) := by
      simpa [model, y] using
        quadraticallyRegularizedObjective_affineModelAt_eq_completedSquare f g tStar x γ
    have hsq : ‖t0 - y‖ ^ (2 : ℕ) ≤ ‖x - y‖ ^ (2 : ℕ) := by
      have hmin : model t0 ≤ model x := (isMinOn_iff.mp ht0) x hx
      nlinarith [hmin, ht0_model, hx_model, hγ]
    exact
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (by simpa [pow_two] using hsq)
  have hvariational :
      ∀ x ∈ Q, inner ℝ (y - tStar) (x - tStar) ≤ 0 := by
    intro x hx
    have hdir : x - tStar ∈ posTangentConeAt Q tStar := by
      exact sub_mem_posTangentConeAt_of_segment_subset (hQ_convex.segment_subset htStar_mem hx)
    have hfirstOrder :=
      htStar.localize.hasFDerivWithinAt_nonneg htStar_fderiv.hasFDerivWithinAt hdir
    have hgrad : 0 ≤ inner ℝ g (x - tStar) := by
      simpa [InnerProductSpace.toDualMap_apply_apply] using hfirstOrder
    have hscaled : 0 ≤ ((γ : ℝ)⁻¹) * inner ℝ g (x - tStar) :=
      mul_nonneg (inv_nonneg.mpr hγ.le) hgrad
    simpa [y, sub_eq_add_neg, inner_smul_left, mul_comm, mul_left_comm, mul_assoc] using
      (neg_nonpos.mpr hscaled)
  have htStar_proj : IsProjectionPointOn Q y tStar := by
    refine IsProjectionPointOn.of_norm_eq_iInf htStar_mem ?_
    exact (norm_eq_iInf_iff_real_inner_le_zero hQ_convex htStar_mem).2 hvariational
  exact ht0_proj.eq hQ_convex htStar_proj

end RegularizedAffineModel

section RegularizedTaylorModel

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {Q : Set E} {f : E → ℝ} {γ : NNRealˣ}

/-- Proposition 2.35: let `tStar ∈ Q` minimize `f` on a closed convex set `Q`, and let `t0 ∈ Q`
minimize the quadratically regularized first-order Taylor model of `f` centered at `tStar`.
Then `t0 = tStar` on any complete real inner-product space; the textbook Euclidean statement is
the specialization `E = EuclideanSpace ℝ (Fin n)`. -/
-- Proof sketch: this is the source-facing specialization of the owner theorem above, taking the
-- gradient witness to be the canonical totalized gradient `∇ f tStar`.
theorem eq_of_isMinOn_quadraticallyRegularizedObjective_firstOrderTaylorModelAt_of_isMinOn
    (hQ_convex : Convex ℝ Q) {t0 tStar : E}
    (htStar_diff : DifferentiableAt ℝ f tStar)
    (ht0_mem : t0 ∈ Q) (htStar_mem : tStar ∈ Q)
    (ht0 : IsMinOn
      (quadraticallyRegularizedObjective (firstOrderTaylorModelAt f tStar) (γ : ℝ) tStar) Q t0)
    (htStar : IsMinOn f Q tStar) :
    t0 = tStar := by
  simpa [InnerProductSpace.toDual_apply_eq_toDualMap_apply, firstOrderTaylorModelAt, affineModelAt]
    using
    eq_of_isMinOn_quadraticallyRegularizedObjective_affineModelAt_of_isMinOn
      hQ_convex htStar_diff.hasGradientAt.hasFDerivAt
      ht0_mem htStar_mem ht0 htStar

end RegularizedTaylorModel

end
