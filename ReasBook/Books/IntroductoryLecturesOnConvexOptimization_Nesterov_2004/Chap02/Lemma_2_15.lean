/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_34
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Lemma_2_13
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_33
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient SmoothConvex

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-
Lemma 2.15 lies in the projection / smooth-convex domain of real inner-product spaces.

Sampled owner-style declarations:
* `Metric.infDist_closure` and `Metric.infDist_empty` in mathlib, showing that
  `Q.halfSquaredDistance` depends only on `closure Q` and becomes the zero function on `∅`;
* `IsProjectionPointOn Q x p` in `Chap07/Definition_7_3`, the project owner predicate for
  nearest-point geometry;
* `euclideanProjection` and `euclideanProjection_isProjectionPointOn` in `Theorem_2_33`, the
  chosen projection map and its bridge back to the owner predicate;
* `euclideanProjection_nonexpansive` in `Theorem_2_34`, the canonical map-level `1`-Lipschitz
  control on the chosen projection;
* `f ∈ 𝓕[L, normSeminorm ℝ E]¹¹` in `Theorem_2_5`, the owner predicate for whole-space `C¹`
  convex objectives with `L`-Lipschitz gradient.

Source/core/bridge triage:
* source-facing: the textbook gradient identity for the half squared distance and the resulting
  `1`-smooth convexity statement; the Euclidean `ℝⁿ` version is the specialization
  `E = EuclideanSpace ℝ (Fin n)`;
* core/canonical: `IsProjectionPointOn Q x p` on the geometric side and
  `Q.halfSquaredDistance ∈ 𝓕[1, normSeminorm ℝ E]¹¹` on the objective side;
* bridge/view: the specialization from an arbitrary projection point to the chosen map
  `euclideanProjection`.

Primitive data:
* the set `Q`, base point `x`, projection point `p`, and convexity / closedness / nonemptiness
  hypotheses exactly when they affect existence of the chosen projection map;
* for the owner-level gradient identity, only the convexity of `Q` and the witness
  `IsProjectionPointOn Q x p`, with completeness entering only through the ambient gradient API;
* for the final smoothness statement, the public mathematical input is `Convex ℝ Q` together with
  the finite-dimensional ambient owner required by `𝓕[1, normSeminorm ℝ E]¹¹`, while closure and
  emptiness reductions come canonically from `Metric.infDist`.

Derived API:
* the gradient formula at an arbitrary owner-level projection point;
* the smooth-objective packaging in `ConvexC1SeminormSmooth`.

Accordingly, the main geometric theorem remains owner-based in the namespace
`IsProjectionPointOn`, and the smoothness result is stated directly in the chapter owner
abstraction. The specialization to the chosen projection map is already a one-line downstream
bridge via `euclideanProjection_isProjectionPointOn`, so no parallel local wrapper is kept here.
-/

namespace IsProjectionPointOn

section

variable [CompleteSpace E]

/-- Helper for Lemma 2.15: at a projection point `p` of `x`, the half squared distance lies above
its affine model with slope `x - p`, and the tangent error is at most `‖z - x‖² / 2`. -/
  lemma halfSquaredDistance_tangent_bounds
    {Q : Set E} (hQ_convex : Convex ℝ Q) {x p z : E} (hp : IsProjectionPointOn Q x p) :
    0 ≤ Q.halfSquaredDistance z - Q.halfSquaredDistance x - inner ℝ (x - p) (z - x) ∧
      Q.halfSquaredDistance z - Q.halfSquaredDistance x - inner ℝ (x - p) (z - x) ≤
        (1 / 2 : ℝ) * ‖z - x‖ ^ (2 : ℕ) := by
  let Qc : Set E := closure Q
  have hp_mem_closure : p ∈ Qc := by
    simpa [Qc] using (subset_closure hp.1)
  have hQc_convex : Convex ℝ Qc := hQ_convex.closure
  have hQc_nonempty : Qc.Nonempty := ⟨p, hp_mem_closure⟩
  let zproj : E := euclideanProjection Qc hQc_nonempty isClosed_closure hQc_convex z
  have hzproj : IsProjectionPointOn Qc z zproj :=
    euclideanProjection_isProjectionPointOn Qc hQc_nonempty isClosed_closure hQc_convex z
  have hp_closure : IsProjectionPointOn Qc x p := by
    refine ⟨hp_mem_closure, ?_⟩
    simpa [Qc, Metric.infDist_closure] using hp.2
  have hz_eq :
      Q.halfSquaredDistance z = (1 / 2 : ℝ) * ‖z - zproj‖ ^ (2 : ℕ) := by
    calc
      Q.halfSquaredDistance z = Qc.halfSquaredDistance z := by
        simp [Set.halfSquaredDistance, Qc, Metric.infDist_closure]
      _ = (1 / 2 : ℝ) * ‖z - zproj‖ ^ (2 : ℕ) := hzproj.halfSquaredDistance_eq
  have hupper_half :
      Q.halfSquaredDistance z ≤ (1 / 2 : ℝ) * ‖z - p‖ ^ (2 : ℕ) := by
    have hdist : Metric.infDist z Q ≤ ‖z - p‖ := by
      simpa [dist_eq_norm] using Metric.infDist_le_dist_of_mem (x := z) hp.1
    calc
      Q.halfSquaredDistance z = (1 / 2 : ℝ) * Metric.infDist z Q ^ (2 : ℕ) := rfl
      _ ≤ (1 / 2 : ℝ) * ‖z - p‖ ^ (2 : ℕ) := by
        nlinarith [Metric.infDist_nonneg (x := z) (s := Q), norm_nonneg (z - p), hdist]
  have hupper :
      Q.halfSquaredDistance z - Q.halfSquaredDistance x - inner ℝ (x - p) (z - x) ≤
        (1 / 2 : ℝ) * ‖z - x‖ ^ (2 : ℕ) := by
    have hz_sub : z - p = (z - x) + (x - p) := by
      abel_nf
    calc
      Q.halfSquaredDistance z - Q.halfSquaredDistance x - inner ℝ (x - p) (z - x)
          ≤ (1 / 2 : ℝ) * ‖z - p‖ ^ (2 : ℕ) -
              Q.halfSquaredDistance x - inner ℝ (x - p) (z - x) := by
              linarith
      _ = (1 / 2 : ℝ) * ‖z - p‖ ^ (2 : ℕ) -
            (1 / 2 : ℝ) * ‖x - p‖ ^ (2 : ℕ) - inner ℝ (x - p) (z - x) := by
            rw [hp.halfSquaredDistance_eq]
      _ = (1 / 2 : ℝ) * ‖z - x‖ ^ (2 : ℕ) := by
        rw [hz_sub, norm_add_sq_real, real_inner_comm (z - x) (x - p)]
        ring
  have hproj_inner :
      0 ≤ inner ℝ (p - x) (zproj - p) :=
    hp_closure.inner_sub_nonneg hQc_convex hzproj.1
  have hlower :
      0 ≤ Q.halfSquaredDistance z - Q.halfSquaredDistance x - inner ℝ (x - p) (z - x) := by
    let d : E := (z - x) - (zproj - p)
    have hz_sub :
        z - zproj = d + (x - p) := by
      dsimp [d]
      abel_nf
    have hzx :
        z - x = d + (zproj - p) := by
      dsimp [d]
      abel_nf
    calc
      0
          ≤ (1 / 2 : ℝ) * ‖d‖ ^ (2 : ℕ) +
              inner ℝ (p - x) (zproj - p) := by
              positivity
      _ = (1 / 2 : ℝ) * ‖z - zproj‖ ^ (2 : ℕ) -
            (1 / 2 : ℝ) * ‖x - p‖ ^ (2 : ℕ) -
              inner ℝ (x - p) (z - x) := by
            calc
              (1 / 2 : ℝ) * ‖d‖ ^ (2 : ℕ) + inner ℝ (p - x) (zproj - p)
                  = (1 / 2 : ℝ) * ‖d‖ ^ (2 : ℕ) - inner ℝ (x - p) (zproj - p) := by
                      have hneg :
                          inner ℝ (p - x) (zproj - p) = -inner ℝ (x - p) (zproj - p) := by
                        simp [sub_eq_add_neg, inner_add_left, inner_neg_left]
                      simpa [sub_eq_add_neg] using
                        congrArg (fun t : ℝ ↦ (1 / 2 : ℝ) * ‖d‖ ^ (2 : ℕ) + t) hneg
              _ = (1 / 2 : ℝ) * ‖d‖ ^ (2 : ℕ) + inner ℝ (x - p) d - inner ℝ (x - p) (z - x) := by
                    rw [hzx, inner_add_right]
                    ring
              _ = (1 / 2 : ℝ) * ‖z - zproj‖ ^ (2 : ℕ) -
                    (1 / 2 : ℝ) * ‖x - p‖ ^ (2 : ℕ) -
                      inner ℝ (x - p) (z - x) := by
                    rw [hz_sub, norm_add_sq_real, real_inner_comm d (x - p)]
                    ring
      _ = Q.halfSquaredDistance z - Q.halfSquaredDistance x - inner ℝ (x - p) (z - x) := by
            rw [← hz_eq, hp.halfSquaredDistance_eq]
  exact ⟨hlower, hupper⟩

/-- Helper for Lemma 2.15: the tangent-error sandwich at a projection point makes the affine
remainder little-o of `‖y - x‖`. -/
lemma halfSquaredDistance_sub_affineApproximation_isLittleO
    {Q : Set E} (hQ_convex : Convex ℝ Q) {x p : E} (hp : IsProjectionPointOn Q x p) :
    (fun y ↦
      Q.halfSquaredDistance y - (Q.halfSquaredDistance x + inner ℝ (x - p) (y - x))) =o[nhds x]
      fun y ↦ ‖y - x‖ := by
  let r : E → ℝ :=
    fun y ↦ Q.halfSquaredDistance y - (Q.halfSquaredDistance x + inner ℝ (x - p) (y - x))
  -- Convert the quadratic tangent bound into a local `O(‖y - x‖²)` estimate for the remainder.
  have hBigO :
      r =O[nhds x] fun y ↦ ‖y - x‖ ^ (2 : ℕ) := by
    refine Asymptotics.IsBigO.of_bound (1 / 2 : ℝ) ?_
    filter_upwards with y
    have hy := hp.halfSquaredDistance_tangent_bounds hQ_convex (z := y)
    calc
      ‖r y‖ = |Q.halfSquaredDistance y - (Q.halfSquaredDistance x + inner ℝ (x - p) (y - x))| := by
        simp [r, Real.norm_eq_abs]
      _ = Q.halfSquaredDistance y - (Q.halfSquaredDistance x + inner ℝ (x - p) (y - x)) := by
        rw [abs_of_nonneg]
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hy.1
      _ ≤ (1 / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ) := by
        have hy' := hy.2
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hy'
      _ ≤ (1 / 2 : ℝ) * ‖‖y - x‖ ^ (2 : ℕ)‖ := by
        simp
  -- A quadratic remainder has zero Fréchet derivative, which is exactly the desired little-o
  -- statement after unpacking the zero linear part.
  have hDeriv0 : HasFDerivAt r (0 : E →L[ℝ] ℝ) x :=
    hBigO.hasFDerivAt (by norm_num : 1 < 2)
  simpa [r] using (hasFDerivAt_iff_isLittleO).mp hDeriv0

/-- The gradient of the half squared distance to a convex set equals the displacement from the base
point to its projection point onto that set. -/
-- Proof sketch: compare the first-order lower support inequality coming from the projection
-- optimality condition with the one-step upper bound obtained by testing the defining minimization
-- at a fixed projection point `p`. The matching lower and upper expansions identify the
-- directional derivative at `x` with the linear functional `d ↦ ⟪x - p, d⟫`, hence the gradient
-- is `x - p`.
theorem gradient_halfSquaredDistance
    {Q : Set E} (hQ_convex : Convex ℝ Q) {x p : E} (hp : IsProjectionPointOn Q x p) :
    ∇ Q.halfSquaredDistance x = x - p := by
  -- Convert the projection-point tangent sandwich into the canonical little-o affine remainder.
  have hLittle := hp.halfSquaredDistance_sub_affineApproximation_isLittleO hQ_convex
  -- The Chapter 1 affine-approximation criterion then identifies the gradient exactly.
  exact ((hasGradientAt_iff_sub_affineApproximation_isLittleO).2 hLittle).gradient

end

end IsProjectionPointOn

section

variable [CompleteSpace E]

/-- Helper for Lemma 2.15: a projection selector on a convex set gives the global quadratic bound
for the affine model of the half squared distance. -/
lemma halfSquaredDistance_affineModel_bound_of_projection_selector
    {Q : Set E} (hQ_convex : Convex ℝ Q) {projQ : E → E}
    (hproj : ∀ x : E, IsProjectionPointOn Q x (projQ x)) :
    ∀ x y,
      |Q.halfSquaredDistance y - affineModelAt Q.halfSquaredDistance (fun z ↦ z - projQ z) x y| ≤
        (1 / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ) := by
  intro x y
  have hxy := (hproj x).halfSquaredDistance_tangent_bounds hQ_convex (z := y)
  -- The tangent error is already nonnegative, so its absolute value is the same quantity.
  refine abs_le.2 ?_
  constructor
  · have hnonneg : 0 ≤ (1 / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ) := by positivity
    have hmodel_nonneg :
        0 ≤
          Q.halfSquaredDistance y -
            affineModelAt Q.halfSquaredDistance (fun z ↦ z - projQ z) x y := by
      simpa [affineModelAt_apply, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hxy.1
    linarith
  · simpa [affineModelAt_apply, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hxy.2

/-- Helper for Lemma 2.15: every projection selector yields a global affine lower support for the
half squared distance. -/
lemma halfSquaredDistance_lower_support_of_projection_selector
    {Q : Set E} (hQ_convex : Convex ℝ Q) {projQ : E → E}
    (hproj : ∀ x : E, IsProjectionPointOn Q x (projQ x)) :
    ∀ x y,
      Q.halfSquaredDistance y ≥
        Q.halfSquaredDistance x + inner ℝ (x - projQ x) (y - x) := by
  intro x y
  -- The nonnegativity half of the tangent sandwich is exactly the lower-support inequality.
  have hxy := ((hproj x).halfSquaredDistance_tangent_bounds hQ_convex (z := y)).1
  linarith

end

section

variable [FiniteDimensional ℝ E]

/-- Lemma 2.15 on the canonical real Hilbert-space owner layer: the half squared distance to a
convex set is a convex `C¹` objective whose gradient is `1`-Lipschitz in the ambient norm. The
textbook Euclidean statement is the specialization to `ℝⁿ`. -/
-- Proof sketch: first reduce privately to the closed case using `Metric.infDist_closure`, and to
-- the empty-set case using `Metric.infDist_empty`, so the public statement depends only on
-- convexity. For the nonempty closed convex reduction, use the projection optimality inequality to
-- derive the global supporting-plane inequality for `Q.halfSquaredDistance`, giving
-- convexity. The companion gradient formula identifies the gradient with the displacement from
-- `x` to the chosen projection of `x` onto `closure Q`, and the projection map is nonexpansive,
-- so this gradient map is `1`-Lipschitz. The explicit gradient formula then upgrades the
-- differentiability statement to `ContDiff ℝ 1`.
theorem halfSquaredDistance_mem_F11
    (Q : Set E) (hQ_convex : Convex ℝ Q) :
    Q.halfSquaredDistance ∈ 𝓕[1, normSeminorm ℝ E]¹¹ := by
  by_cases hQ_empty : Q = ∅
  · have hzero :
      (fun _ : E ↦ (0 : ℝ)) ∈ 𝓕[1, normSeminorm ℝ E]¹¹ := by
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · -- The zero function is globally `C¹`.
        simpa [contDiffOn_univ] using (contDiff_const : ContDiff ℝ 1 (fun _ : E ↦ (0 : ℝ)))
      · -- The zero function is convex because every affine combination has the same value.
        simpa using convexOn_const (0 : ℝ) convex_univ
      · -- Its ambient gradient is the zero vector at every point.
        intro x hx
        simpa [gradient_const] using (hasGradientAt_const (x := x) (c := (0 : ℝ)))
      · -- The dual norm of the zero gradient difference vanishes identically.
        intro x hx y hy
        simp [Seminorm.dualNorm_normSeminorm_eq_norm]
    have hempty_fun : (∅ : Set E).halfSquaredDistance = fun _ : E ↦ (0 : ℝ) := by
      funext x
      simp [Set.halfSquaredDistance, Metric.infDist_empty]
    simpa [hQ_empty, hempty_fun] using hzero
  · have hQ_nonempty : Q.Nonempty := Set.nonempty_iff_ne_empty.mpr hQ_empty
    let Qc : Set E := closure Q
    have hQc_convex : Convex ℝ Qc := hQ_convex.closure
    have hQc_nonempty : Qc.Nonempty := hQ_nonempty.closure
    let projQ : E → E := euclideanProjection Qc hQc_nonempty isClosed_closure hQc_convex
    have hproj : ∀ x : E, IsProjectionPointOn Qc x (projQ x) :=
      fun x ↦ euclideanProjection_isProjectionPointOn Qc hQc_nonempty isClosed_closure hQc_convex x
    have hquad :
        ∀ x y,
          |Qc.halfSquaredDistance y -
              affineModelAt Qc.halfSquaredDistance (fun z ↦ z - projQ z) x y| ≤
            (1 / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ) :=
      halfSquaredDistance_affineModel_bound_of_projection_selector hQc_convex hproj
    have hContDiffAndLip :
        ContDiff ℝ 1 Qc.halfSquaredDistance ∧ LipschitzWith 1 (∇ Qc.halfSquaredDistance) :=
      mem_contDiffOne_withLipschitzGradient_of_sub_affineApproximation_norm_sq_bound
        (L := 1) (f := Qc.halfSquaredDistance) (g := fun z ↦ z - projQ z) hquad
    have hgrad_eq :
        ∇ Qc.halfSquaredDistance = fun z ↦ z - projQ z :=
      gradient_eq_of_sub_affineApproximation_norm_sq_bound
        (L := 1) (f := Qc.halfSquaredDistance) (g := fun z ↦ z - projQ z) hquad
    have hConvex :
        ConvexOn ℝ Set.univ Qc.halfSquaredDistance := by
      refine
        (convexOn_iff_lower_tangent_plane_of_contDiffOn
          (Q := Set.univ) (f := Qc.halfSquaredDistance) convex_univ
          (contDiffOn_univ.2 hContDiffAndLip.1)).2 ?_
      intro x hx y hy
      -- Rewrite the selector lower-support inequality into the canonical gradient form.
      have hgradx :
          HasGradientAt Qc.halfSquaredDistance (x - projQ x) x :=
        hasGradientAt_of_sub_affineApproximation_norm_sq_bound
          (L := 1) (f := Qc.halfSquaredDistance) (g := fun z ↦ z - projQ z) hquad x
      have hcanon :
          HasGradientAt Qc.halfSquaredDistance
            (gradientWithin Qc.halfSquaredDistance Set.univ x) x := by
        have hdiffWithin :
            DifferentiableWithinAt ℝ
              Qc.halfSquaredDistance Set.univ x :=
          ((hContDiffAndLip.1.contDiffAt).differentiableAt_one).differentiableWithinAt
        exact (hasGradientWithinAt_univ).mp hdiffWithin.hasGradientWithinAt
      have hgradWithin :
          gradientWithin Qc.halfSquaredDistance Set.univ x = x - projQ x :=
        hcanon.unique hgradx
      simpa [hgradWithin] using
        halfSquaredDistance_lower_support_of_projection_selector hQc_convex hproj x y
    have hQc_mem :
        Qc.halfSquaredDistance ∈ 𝓕[1, normSeminorm ℝ E]¹¹ := by
      refine ⟨⟨contDiffOn_univ.2 hContDiffAndLip.1, hConvex⟩, ?_, ?_⟩
      · -- The recovered `C¹` regularity gives the ambient gradient witness at every point.
        intro x hx
        exact ((hContDiffAndLip.1.contDiffAt).differentiableAt_one).hasGradientAt
      · -- The chapter owner wants the dual-norm Lipschitz estimate, which matches the usual norm
        -- in the `normSeminorm` specialization.
        intro x hx y hy
        simpa [Seminorm.dualNorm_normSeminorm_eq_norm] using hContDiffAndLip.2.norm_sub_le x y
    have hclosure_fun : Q.halfSquaredDistance = Qc.halfSquaredDistance := by
      funext x
      simp [Set.halfSquaredDistance, Qc, Metric.infDist_closure]
    simpa [hclosure_fun] using hQc_mem

end

end
