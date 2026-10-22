/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Algorithm_7_8
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_23
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_46
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_14

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators ConstrainedArgmin PositiveDefMatrixNorm
open scoped Gradient

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Proposition 7.16 lies in Chapter 7's weighted smooth convex minimization / accelerated
projected-gradient domain.

Sampled owner-style declarations:
- `AcceleratedConvexMinimizationScheme` in `Algorithm_7_8`, the chapter owner of an accelerated
  feasible-set run with chosen gradient field, weighted proximal matrix, and positive smoothness
  constant;
- `argmin[Q]` and `mem_constrainedArgmin_iff` in `Chap01/Definition_1_3_3`, the project owner of
  a constrained minimizer together with the canonical feasibility-plus-`IsMinOn` membership
  bridge;
- `acceleratedSchemeSearchPoint` and `acceleratedSchemeProximalMinimand` in `Algorithm_7_8`, the
  derived chapter API for the extrapolated point and proximal objective;
- `positiveDefMatrixNorm` and the notations `‖·‖[G]`, `‖·‖[G,*]` in `Definition_7_23`, the
  chapter owners of the weighted norm and its dual norm for a positive-definite matrix;
- `CompositeSmoothConvexMinimizationProblem` in `Definition_7_39`, the nearby problem owner that
  uses the same positive `NNRealˣ` smoothness parameter and positive-definite matrix owner.

Best owner abstraction:
- source-facing: Proposition 7.16's rate estimate for an accelerated run on a closed convex set;
- core/canonical: `AcceleratedConvexMinimizationScheme n N`;
- bridge/view: the weighted dual-gradient Lipschitz hypothesis, stated pointwise on the feasible
  set and consumed by the accelerated-scheme owner, together with the constrained-minimizer
  membership `xStar ∈ argmin[Q] φ` unpacked via `mem_constrainedArgmin_iff` when needed.

Primitive data:
- the constrained problem, chosen gradient field, positive smoothness constant, positive-definite
  matrix owner, initial point, and iterate/prox-center sequences, all owned by
  `AcceleratedConvexMinimizationScheme`;
- the minimizing point `xStar`, packaged canonically as a member of
  `argmin[scheme.problem.feasibleSet] scheme.problem`.

Derived API:
- the extrapolated point `yₖ`, through `acceleratedSchemeSearchPoint`;
- the proximal argmin step, through `scheme.v_succ_mem_argmin`;
- feasibility and `IsMinOn` for `xStar`, through `mem_constrainedArgmin_iff`;
- the weighted and dual weighted norms, through `positiveDefMatrixNorm`.

The previous version duplicated the chapter owner by introducing a second public scheme structure
with the same mathematical content and a weaker raw-`L` parameter surface. This refinement
deletes that duplicate layer and states the proposition directly over the existing Chapter 7 owner.
-/

-- Proof sketch: derive the weighted smoothness inequality from the assumed dual-gradient Lipschitz
-- bound, then run the standard estimate-sequence argument for the chapter owner
-- `scheme : AcceleratedConvexMinimizationScheme n N`. Evaluating the resulting potential estimate
-- at the minimizer `xStar` gives the final bound for the output iterate `x_N`.
namespace AcceleratedConvexMinimizationScheme

/-- Helper for Proposition 7.16: the stage weights of Algorithm 7.8 sum to the closed form
`A_k = k (k + 1) / 4`. -/
lemma estimate_weight_sum_eq
    (k : ℕ) :
    Finset.sum (Finset.range k) (fun i ↦ ((((i : ℝ) + 1) / 2) : ℝ)) =
      (k : ℝ) * ((k : ℝ) + 1) / 4 := by
  induction k with
  | zero =>
      -- The empty sum gives the initial coefficient `A₀ = 0`.
      simp
  | succ k hk =>
      -- Extend the finite sum by its last stage weight and simplify the scalar recurrence.
      rw [Finset.sum_range_succ, hk]
      norm_num [Nat.cast_add]
      ring

/-- Helper for Proposition 7.16: the affine auxiliary point from the Chapter 2 accelerated proof
is exactly the stored sequence `v_k` for Algorithm 7.8. -/
lemma searchPoint_auxPoint_eq_v
    {N : ℕ} (scheme : AcceleratedConvexMinimizationScheme n N)
    (k : ℕ) :
    ((((k + 2 : ℕ) : ℝ) / 2) : ℝ) • acceleratedSchemeSearchPoint scheme.x scheme.v k -
        (((((k + 2 : ℕ) : ℝ) / 2) : ℝ) - 1) • scheme.x k =
      scheme.v k := by
  -- Expand `y_k` and cancel the textbook coefficients `t_k = (k + 2) / 2`.
  rw [acceleratedSchemeSearchPoint_eq]
  have hxcoef :
      ((((k + 2 : ℕ) : ℝ) / 2) : ℝ) * ((k : ℝ) / (k + 2)) -
          (((((k + 2 : ℕ) : ℝ) / 2) : ℝ) - 1) =
        0 := by
    have hk2 : ((k : ℝ) + 2) ≠ 0 := by positivity
    field_simp [hk2]
    norm_num [Nat.cast_add]
  have hvcoef :
      ((((k + 2 : ℕ) : ℝ) / 2) : ℝ) * ((2 : ℝ) / (k + 2)) = 1 := by
    have hk2 : ((k : ℝ) + 2) ≠ 0 := by positivity
    field_simp [hk2]
    norm_num [Nat.cast_add]
  calc
    ((((k + 2 : ℕ) : ℝ) / 2) : ℝ) •
          (((k : ℝ) / (k + 2)) • scheme.x k + ((2 : ℝ) / (k + 2)) • scheme.v k) -
        (((((k + 2 : ℕ) : ℝ) / 2) : ℝ) - 1) • scheme.x k
        =
          ((((((k + 2 : ℕ) : ℝ) / 2) : ℝ) * ((k : ℝ) / (k + 2)) -
              (((((k + 2 : ℕ) : ℝ) / 2) : ℝ) - 1)) : ℝ) • scheme.x k +
            ((((((k + 2 : ℕ) : ℝ) / 2) : ℝ) * ((2 : ℝ) / (k + 2))) : ℝ) • scheme.v k := by
              module
    _ = 0 • scheme.x k + 1 • scheme.v k := by
          rw [hxcoef, hvcoef]
          simp
    _ = scheme.v k := by simp

/-- Helper for Proposition 7.16: every iterate `x_k`, every auxiliary point `v_k`, and every
search point `y_k` stay in the feasible set throughout the finite horizon. -/
lemma iterates_and_searchPoint_mem_feasible
    {N : ℕ} (scheme : AcceleratedConvexMinimizationScheme n N) :
    ∀ {k : ℕ}, k ≤ N →
      scheme.x k ∈ scheme.problem.feasibleSet ∧
        scheme.v k ∈ scheme.problem.feasibleSet ∧
          acceleratedSchemeSearchPoint scheme.x scheme.v k ∈ scheme.problem.feasibleSet := by
  intro k hk
  induction k with
  | zero =>
      have hx0 : scheme.x 0 ∈ scheme.problem.feasibleSet := by
        simpa [scheme.x_zero] using scheme.initialPoint_mem
      have hv0 : scheme.v 0 ∈ scheme.problem.feasibleSet := by
        simpa [scheme.v_zero] using scheme.initialPoint_mem
      have hy0 : acceleratedSchemeSearchPoint scheme.x scheme.v 0 ∈ scheme.problem.feasibleSet := by
        -- At the initial stage the search point is exactly `v₀ = x₀`.
        simpa [acceleratedSchemeSearchPoint] using hv0
      exact ⟨hx0, hv0, hy0⟩
  | succ k ih =>
      have hk_lt : k < N := Nat.lt_of_succ_le hk
      have hk_le : k ≤ N := Nat.le_of_lt hk_lt
      rcases ih hk_le with ⟨hxk, hvk, _⟩
      have hvsucc : scheme.v (k + 1) ∈ scheme.problem.feasibleSet := by
        exact (mem_constrainedArgmin_iff.mp (scheme.v_succ_mem_argmin_set hk_lt)).1
      have hxsucc : scheme.x (k + 1) ∈ scheme.problem.feasibleSet := by
        -- The successor iterate is the convex combination prescribed by Algorithm 7.8.
        rw [scheme.x_succ k hk_lt]
        have hα_nonneg : 0 ≤ (k : ℝ) / (k + 2) := by positivity
        have hβ_nonneg : 0 ≤ (2 : ℝ) / (k + 2) := by positivity
        have hsum : (k : ℝ) / (k + 2) + (2 : ℝ) / (k + 2) = 1 := by
          field_simp
        exact scheme.convexSet hxk hvsucc hα_nonneg hβ_nonneg hsum
      have hysucc :
          acceleratedSchemeSearchPoint scheme.x scheme.v (k + 1) ∈
            scheme.problem.feasibleSet := by
        -- The next search point is the same convex interpolation between `x_{k+1}` and `v_{k+1}`.
        rw [acceleratedSchemeSearchPoint_eq]
        have hα_nonneg : 0 ≤ ((k + 1 : ℕ) : ℝ) / (((k + 1 : ℕ) : ℝ) + 2) := by positivity
        have hβ_nonneg : 0 ≤ (2 : ℝ) / (((k + 1 : ℕ) : ℝ) + 2) := by positivity
        have hsum :
            ((k + 1 : ℕ) : ℝ) / (((k + 1 : ℕ) : ℝ) + 2) +
              (2 : ℝ) / (((k + 1 : ℕ) : ℝ) + 2) =
            1 := by
          field_simp
        exact scheme.convexSet hxsucc hvsucc hα_nonneg hβ_nonneg hsum
      exact ⟨hxsucc, hvsucc, hysucc⟩

/-- Helper for Proposition 7.16: along a feasible segment, the corrected first-order remainder
has derivative given by the weighted-gradient increment paired with the segment direction. -/
private lemma weighted_segment_corrected_remainder_hasDerivAt
    {N : ℕ} (scheme : AcceleratedConvexMinimizationScheme n N)
    {x y : E}
    (hx : x ∈ scheme.problem.feasibleSet)
    (hy : y ∈ scheme.problem.feasibleSet)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt
      (fun u : ℝ ↦
        scheme.problem.objective (x + u • (y - x)) - scheme.problem.objective x -
          u * inner ℝ (scheme.gradient x) (y - x))
      (inner ℝ (scheme.gradient (x + t • (y - x)) - scheme.gradient x) (y - x))
      t := by
  let d : E := y - x
  -- Keep the segment point inside the feasible set so the chosen gradient witness is available.
  have hseg_mem : x + t • d ∈ scheme.problem.feasibleSet := by
    simpa [d, AffineMap.lineMap_apply, add_comm, add_left_comm, add_assoc] using
      scheme.convexSet.mapsTo_lineMap hx hy ⟨ht.1.le, ht.2.le⟩
  have hdiff : DifferentiableAt ℝ scheme.problem.objective (x + t • d) :=
    (scheme.gradient_hasGradientAt hseg_mem).differentiableAt
  have hseg :
      HasDerivAt
        (fun u : ℝ ↦ scheme.problem.objective (x + u • d))
        ((fderiv ℝ scheme.problem.objective (x + t • d)) d)
        t := by
    have hline : HasDerivAt (fun u : ℝ ↦ x + u • d) d t := by
      simpa [one_smul] using (((hasDerivAt_id t).smul_const d).const_add x)
    simpa [Function.comp] using (hdiff.hasFDerivAt.comp t hline.hasFDerivAt).hasDerivAt
  have hlin :
      HasDerivAt (fun u : ℝ ↦ u * inner ℝ (scheme.gradient x) d)
        (inner ℝ (scheme.gradient x) d) t := by
    simpa [one_mul] using (hasDerivAt_id t).mul_const (inner ℝ (scheme.gradient x) d)
  have hmain :
      HasDerivAt
        (fun u : ℝ ↦
          scheme.problem.objective (x + u • d) - scheme.problem.objective x -
            u * inner ℝ (scheme.gradient x) d)
        (((fderiv ℝ scheme.problem.objective (x + t • d)) d) - inner ℝ (scheme.gradient x) d)
        t := by
    have hmain_raw :=
      hseg.sub ((hasDerivAt_const t (scheme.problem.objective x)).add hlin)
    convert hmain_raw using 1
    · ext u
      simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    · ring
  -- Rewrite the Fréchet derivative through the chosen gradient field at the segment point.
  have hgrad_eval :
      (fderiv ℝ scheme.problem.objective (x + t • d)) d =
        inner ℝ (scheme.gradient (x + t • d)) d := by
    simpa [show ∇ scheme.problem.objective (x + t • d) = scheme.gradient (x + t • d) by
          simpa using (scheme.gradient_hasGradientAt hseg_mem).gradient]
      using (inner_gradient_left (y := d) hdiff).symm
  convert hmain using 1
  rw [inner_sub_left]
  change inner ℝ (scheme.gradient (x + t • d)) d - inner ℝ (scheme.gradient x) d =
    (fderiv ℝ scheme.problem.objective (x + t • d)) d - inner ℝ (scheme.gradient x) d
  rw [hgrad_eval]

/-- Helper for Proposition 7.16: the weighted tangent error on the feasible segment from `x` to
`y` is bounded by the quadratic weighted norm term. -/
private lemma weighted_tangent_error_upper_bound
    {N : ℕ} (scheme : AcceleratedConvexMinimizationScheme n N)
    (hgradient_lipschitz :
      ∀ ⦃x y : E⦄,
        x ∈ scheme.problem.feasibleSet →
        y ∈ scheme.problem.feasibleSet →
          ‖scheme.gradient x - scheme.gradient y‖[scheme.metricMatrix,*] ≤
            (scheme.smoothness : ℝ) * ‖x - y‖[scheme.metricMatrix])
    {x y : E}
    (hx : x ∈ scheme.problem.feasibleSet)
    (hy : y ∈ scheme.problem.feasibleSet) :
    scheme.problem.objective y - scheme.problem.objective x - inner ℝ (scheme.gradient x) (y - x) ≤
      ((scheme.smoothness : ℝ) / 2) * ‖x - y‖[scheme.metricMatrix] ^ (2 : ℕ) := by
  let d : E := y - x
  have hmaps :
      Set.MapsTo (fun t : ℝ ↦ x + t • d) (Set.Icc (0 : ℝ) 1) scheme.problem.feasibleSet := by
    intro t ht
    simpa [d, AffineMap.lineMap_apply, add_comm, add_left_comm, add_assoc] using
      scheme.convexSet.mapsTo_lineMap hx hy ht
  -- The one-dimensional corrected remainder is continuous on `[0, 1]`.
  have hproblem_cont : ContinuousOn scheme.problem.objective scheme.problem.feasibleSet := by
    intro z hz
    exact (scheme.gradient_hasGradientAt hz).continuousAt.continuousWithinAt
  have hcont :
      ContinuousOn
        (fun t : ℝ ↦
          scheme.problem.objective (x + t • d) - scheme.problem.objective x -
            t * inner ℝ (scheme.gradient x) d)
        (Set.Icc (0 : ℝ) 1) := by
    have hseg_cont :
        ContinuousOn (fun t : ℝ ↦ scheme.problem.objective (x + t • d)) (Set.Icc (0 : ℝ) 1) :=
      hproblem_cont.comp (by fun_prop) hmaps
    have hlin_cont : Continuous (fun t : ℝ ↦ t * inner ℝ (scheme.gradient x) d) := by
      fun_prop
    exact (hseg_cont.sub continuousOn_const).sub hlin_cont.continuousOn
  -- The derivative formula from the segment helper controls the interior derivative.
  have hdiff :
      DifferentiableOn ℝ
        (fun t : ℝ ↦
          scheme.problem.objective (x + t • d) - scheme.problem.objective x -
            t * inner ℝ (scheme.gradient x) d)
        (Set.Ioo (0 : ℝ) 1) := by
    intro t ht
    exact
      (weighted_segment_corrected_remainder_hasDerivAt (scheme := scheme) hx hy ht).differentiableAt
        |>.differentiableWithinAt
  have hbound :=
    norm_sub_le_integral_of_norm_deriv_le_of_le
      (f := fun t : ℝ ↦
        scheme.problem.objective (x + t • d) - scheme.problem.objective x -
          t * inner ℝ (scheme.gradient x) d)
      (B := fun t : ℝ ↦ (scheme.smoothness : ℝ) * t * ‖d‖[scheme.metricMatrix] ^ (2 : ℕ))
      (a := (0 : ℝ)) (b := 1)
      (by norm_num) hcont hdiff
      (Filter.Eventually.of_forall fun t ht ↦ by
        have hderivAt :=
          weighted_segment_corrected_remainder_hasDerivAt (scheme := scheme) hx hy ht
        rw [hderivAt.deriv]
        have hseg_mem : x + t • d ∈ scheme.problem.feasibleSet := hmaps ⟨ht.1.le, ht.2.le⟩
        have hinner_abs :
            |inner ℝ (scheme.gradient (x + t • d) - scheme.gradient x) d| ≤
              ‖scheme.gradient (x + t • d) - scheme.gradient x‖[scheme.metricMatrix,*] *
                ‖d‖[scheme.metricMatrix] := by
          refine abs_le.2 ?_
          constructor
          · have hneg :=
              Seminorm.inner_le_dualNorm_mul
                (positiveDefMatrixNorm scheme.metricMatrix.1 scheme.metricMatrix.2)
                (-d)
                (scheme.gradient (x + t • d) - scheme.gradient x)
            have hneg' :
                -(inner ℝ (scheme.gradient (x + t • d) - scheme.gradient x) d) ≤
                  ‖scheme.gradient (x + t • d) - scheme.gradient x‖[scheme.metricMatrix,*] *
                    ‖d‖[scheme.metricMatrix] := by
              simpa [inner_neg_right] using hneg
            linarith
          · exact
              Seminorm.inner_le_dualNorm_mul
                (positiveDefMatrixNorm scheme.metricMatrix.1 scheme.metricMatrix.2)
                d
                (scheme.gradient (x + t • d) - scheme.gradient x)
        have hgrad_bound :
            ‖scheme.gradient (x + t • d) - scheme.gradient x‖[scheme.metricMatrix,*] ≤
              (scheme.smoothness : ℝ) * ‖(x + t • d) - x‖[scheme.metricMatrix] :=
          hgradient_lipschitz hseg_mem hx
        have hseg_norm : ‖(x + t • d) - x‖[scheme.metricMatrix] = t * ‖d‖[scheme.metricMatrix] := by
          calc
            ‖(x + t • d) - x‖[scheme.metricMatrix] = ‖t • d‖[scheme.metricMatrix] := by simp
            _ = |t| * ‖d‖[scheme.metricMatrix] := by
                  simpa [Real.norm_eq_abs] using
                    (map_smul_eq_mul
                      (positiveDefMatrixNorm scheme.metricMatrix.1 scheme.metricMatrix.2)
                      t
                      d)
            _ = t * ‖d‖[scheme.metricMatrix] := by rw [abs_of_pos ht.1]
        calc
          |inner ℝ (scheme.gradient (x + t • d) - scheme.gradient x) d| ≤
              ‖scheme.gradient (x + t • d) - scheme.gradient x‖[scheme.metricMatrix,*] *
                ‖d‖[scheme.metricMatrix] := hinner_abs
          _ ≤ ((scheme.smoothness : ℝ) * ‖(x + t • d) - x‖[scheme.metricMatrix]) *
                ‖d‖[scheme.metricMatrix] := by
                  exact
                    mul_le_mul_of_nonneg_right hgrad_bound
                      (apply_nonneg
                        (positiveDefMatrixNorm scheme.metricMatrix.1 scheme.metricMatrix.2)
                        d)
          _ = ((scheme.smoothness : ℝ) * (t * ‖d‖[scheme.metricMatrix])) *
                ‖d‖[scheme.metricMatrix] := by rw [hseg_norm]
          _ = (scheme.smoothness : ℝ) * t * ‖d‖[scheme.metricMatrix] ^ (2 : ℕ) := by ring)
      (by
        have hint : IntervalIntegrable (fun t : ℝ ↦ t) MeasureTheory.volume 0 1 :=
          Continuous.intervalIntegrable continuous_id 0 1
        simpa [mul_assoc] using
          hint.const_mul ((scheme.smoothness : ℝ) * ‖d‖[scheme.metricMatrix] ^ (2 : ℕ)))
  have hR0 :
      (fun t : ℝ ↦
        scheme.problem.objective (x + t • d) - scheme.problem.objective x -
          t * inner ℝ (scheme.gradient x) d) 0 = 0 := by
    simp [d]
  have hR1 :
      (fun t : ℝ ↦
        scheme.problem.objective (x + t • d) - scheme.problem.objective x -
          t * inner ℝ (scheme.gradient x) d) 1 =
          scheme.problem.objective y - scheme.problem.objective x -
            inner ℝ (scheme.gradient x) (y - x) := by
    simp [d]
  have habs :
      |scheme.problem.objective y - scheme.problem.objective x -
          inner ℝ (scheme.gradient x) (y - x)| ≤
        ((scheme.smoothness : ℝ) / 2) * ‖d‖[scheme.metricMatrix] ^ (2 : ℕ) := by
    rw [hR1, hR0, sub_zero, Real.norm_eq_abs] at hbound
    calc
      |scheme.problem.objective y - scheme.problem.objective x -
          inner ℝ (scheme.gradient x) (y - x)| ≤
          ∫ t in (0 : ℝ)..1, (scheme.smoothness : ℝ) * t * ‖d‖[scheme.metricMatrix] ^ (2 : ℕ) :=
        hbound
      _ = ((scheme.smoothness : ℝ) / 2) * ‖d‖[scheme.metricMatrix] ^ (2 : ℕ) := by
            calc
              ∫ t in (0 : ℝ)..1, (scheme.smoothness : ℝ) * t * ‖d‖[scheme.metricMatrix] ^ (2 : ℕ) =
                  ∫ t in (0 : ℝ)..1,
                    ((scheme.smoothness : ℝ) * ‖d‖[scheme.metricMatrix] ^ (2 : ℕ)) * t := by
                      congr with t
                      ring
              _ = ((scheme.smoothness : ℝ) * ‖d‖[scheme.metricMatrix] ^ (2 : ℕ)) *
                    ∫ t in (0 : ℝ)..1, t := by
                      rw [intervalIntegral.integral_const_mul]
              _ = ((scheme.smoothness : ℝ) / 2) * ‖d‖[scheme.metricMatrix] ^ (2 : ℕ) := by
                      rw [integral_id]
                      norm_num
                      ring
  have hupper :
      scheme.problem.objective y - scheme.problem.objective x -
          inner ℝ (scheme.gradient x) (y - x) ≤
        ((scheme.smoothness : ℝ) / 2) * ‖d‖[scheme.metricMatrix] ^ (2 : ℕ) :=
    (abs_le.mp habs).2
  have hp : ‖d‖[scheme.metricMatrix] = ‖x - y‖[scheme.metricMatrix] := by
    simpa [d, neg_sub] using
      (map_neg_eq_map (positiveDefMatrixNorm scheme.metricMatrix.1 scheme.metricMatrix.2) (x - y))
  calc
    scheme.problem.objective y - scheme.problem.objective x -
        inner ℝ (scheme.gradient x) (y - x) ≤
        ((scheme.smoothness : ℝ) / 2) * ‖d‖[scheme.metricMatrix] ^ (2 : ℕ) := hupper
    _ = ((scheme.smoothness : ℝ) / 2) * ‖x - y‖[scheme.metricMatrix] ^ (2 : ℕ) := by rw [hp]

/-- Helper for Proposition 7.16: the feasible-set gradient Lipschitz hypothesis upgrades to the
weighted tangent upper model on the feasible set. -/
lemma weighted_smooth_upper_model_on_feasible
    {N : ℕ} (scheme : AcceleratedConvexMinimizationScheme n N)
    (hgradient_lipschitz :
      ∀ ⦃x y : E⦄,
        x ∈ scheme.problem.feasibleSet →
        y ∈ scheme.problem.feasibleSet →
          ‖scheme.gradient x - scheme.gradient y‖[scheme.metricMatrix,*] ≤
            (scheme.smoothness : ℝ) * ‖x - y‖[scheme.metricMatrix])
    {x y : E}
    (hx : x ∈ scheme.problem.feasibleSet)
    (hy : y ∈ scheme.problem.feasibleSet) :
    scheme.problem y ≤
      scheme.problem x +
        inner ℝ (scheme.gradient x) (y - x) +
          ((scheme.smoothness : ℝ) / 2) * ‖x - y‖[scheme.metricMatrix] ^ (2 : ℕ) := by
  -- Route correction: prove the weighted upper model directly along the feasible segment instead
  -- of trying to repackage the chosen gradient field into the Chapter 2 smooth owner first.
  -- Use the one-dimensional corrected-remainder estimate along the feasible segment from `x` to
  -- `y` to bound the tangent error by the weighted quadratic term.
  have hupper :=
    weighted_tangent_error_upper_bound (scheme := scheme) hgradient_lipschitz hx hy
  linarith

/-- Helper for Proposition 7.16: the proximal point `v_{k+1}` minimizes the current weighted
proximal minimand over the feasible set. -/
lemma weighted_proximal_argmin_le
    {N : ℕ} (scheme : AcceleratedConvexMinimizationScheme n N)
    {k : ℕ} (hk : k < N) {u : E}
    (hu : u ∈ scheme.problem.feasibleSet) :
    acceleratedSchemeProximalMinimand
        scheme.gradient
        scheme.metricMatrix
        scheme.smoothness
        scheme.initialPoint
        scheme.x
        scheme.v
        k
        (scheme.v (k + 1)) ≤
      acceleratedSchemeProximalMinimand
        scheme.gradient
        scheme.metricMatrix
        scheme.smoothness
        scheme.initialPoint
        scheme.x
        scheme.v
        k
        u := by
  -- Unpack the constrained argmin membership to recover the minimizing property on the feasible
  -- set.
  exact (mem_constrainedArgmin_iff.mp (scheme.v_succ_mem_argmin_set hk)).2 hu

/-- Helper for Proposition 7.16: when the coefficients add to `1`, subtracting a fixed base point
from an affine combination distributes across the two shifted summands. -/
private lemma sub_point_affine_combo
    {x u v : E} {a b : ℝ} (hab : a + b = 1) :
    a • u + b • v - x = a • (u - x) + b • (v - x) := by
  -- Rewrite the single translated point as the same affine combination of the translated
  -- summands, using `a + b = 1` to distribute the common shift.
  calc
    a • u + b • v - x = a • u + b • v + (a + b) • (-x) := by
      simp [sub_eq_add_neg, hab]
    _ = a • (u - x) + b • (v - x) := by
      simp [sub_eq_add_neg, smul_add, add_smul, add_assoc, add_left_comm, add_comm]

/-- Helper for Proposition 7.16: the weighted gradient linear term is affine in the shifted
comparison point. -/
private lemma weighted_gradient_sum_inner_affine_combo
    {N : ℕ} (scheme : AcceleratedConvexMinimizationScheme n N)
    (k : ℕ) {u v : E} {a b : ℝ} (hab : a + b = 1) :
    inner ℝ (acceleratedSchemeWeightedGradientSum scheme.gradient scheme.x scheme.v k)
        ((a • u + b • v) - scheme.initialPoint) =
      a * inner ℝ (acceleratedSchemeWeightedGradientSum scheme.gradient scheme.x scheme.v k)
            (u - scheme.initialPoint) +
        b * inner ℝ (acceleratedSchemeWeightedGradientSum scheme.gradient scheme.x scheme.v k)
            (v - scheme.initialPoint) := by
  -- First move the common shift inside the affine combination, then use bilinearity of the inner
  -- product in the second argument.
  rw [sub_point_affine_combo hab, inner_add_right, inner_smul_right, inner_smul_right]

/-- Helper for Proposition 7.16: the proximal minimand is exactly the weighted linear term plus
the weighted quadratic-distance owner centered at the initial point. -/
lemma proximalMinimand_eq_weightedQuadraticDistance
    {N : ℕ} (scheme : AcceleratedConvexMinimizationScheme n N)
    (k : ℕ) (u : E) :
    acceleratedSchemeProximalMinimand
        scheme.gradient
        scheme.metricMatrix
        scheme.smoothness
        scheme.initialPoint
        scheme.x
        scheme.v
        k
        u =
      inner ℝ (acceleratedSchemeWeightedGradientSum scheme.gradient scheme.x scheme.v k)
          (u - scheme.initialPoint) +
        (scheme.smoothness : ℝ) *
          (positiveDefMatrixNorm scheme.metricMatrix.1 scheme.metricMatrix.2).quadraticDistanceTo
            scheme.initialPoint
            u := by
  -- Route correction: rewrite the raw norm-square penalty through the canonical owner
  -- `quadraticDistanceTo` before proving any strong-convexity statement about the minimand.
  rw [acceleratedSchemeProximalMinimand_apply,
    positiveDefMatrixNorm_quadraticDistanceTo_apply]
  -- The quadratic penalty is exactly `(scheme.smoothness : ℝ)` times the owner value.
  ring

/-- Helper for Proposition 7.16: the weighted squared norm is the quadratic form of the matrix
operator `Matrix.toEuclideanLin G.1`. -/
private lemma positiveDefMatrixNorm_sq_eq_matrix_quadratic
    (G : {G : Matrix (Fin n) (Fin n) ℝ // G.PosDef}) (z : E) :
    ‖z‖[G] ^ (2 : ℕ) = inner ℝ ((Matrix.toEuclideanLin G.1) z) z := by
  -- Rewrite the weighted norm through its canonical matrix quadratic form and discharge the
  -- nonnegativity side condition from positive semidefiniteness.
  have hPosLin : (Matrix.toEuclideanLin G.1).IsPositive :=
    Matrix.isPositive_toEuclideanLin_iff.mpr G.2.posSemidef
  have hnonneg : 0 ≤ inner ℝ ((Matrix.toEuclideanLin G.1) z) z := by
    simpa [real_inner_comm] using hPosLin.inner_nonneg_right z
  rw [positiveDefMatrixNorm_def, Real.sq_sqrt hnonneg]

/-- Helper for Proposition 7.16: the matrix quadratic form attached to a positive-definite matrix
is symmetric in its two vector arguments. -/
private lemma positiveDefMatrixNorm_matrix_quadratic_symm
    (G : {G : Matrix (Fin n) (Fin n) ℝ // G.PosDef}) (x y : E) :
    inner ℝ ((Matrix.toEuclideanLin G.1) x) y =
      inner ℝ ((Matrix.toEuclideanLin G.1) y) x := by
  -- Positive operators are symmetric, so the cross term can be swapped before the scalar algebra.
  have hPosLin : (Matrix.toEuclideanLin G.1).IsPositive :=
    Matrix.isPositive_toEuclideanLin_iff.mpr G.2.posSemidef
  simpa [real_inner_comm] using hPosLin.isSymmetric x y

/-- Helper for Proposition 7.16: the weighted quadratic-distance owner satisfies the exact
affine-combination identity needed for the estimate-sequence proof. -/
private lemma weighted_quadraticDistanceTo_affine_combo_exact
    (G : {G : Matrix (Fin n) (Fin n) ℝ // G.PosDef}) (x0 u v : E)
    (a b : ℝ) (hab : a + b = 1) :
    (positiveDefMatrixNorm G.1 G.2).quadraticDistanceTo x0 (a • u + b • v) =
      a * (positiveDefMatrixNorm G.1 G.2).quadraticDistanceTo x0 u +
        b * (positiveDefMatrixNorm G.1 G.2).quadraticDistanceTo x0 v -
          a * b * ((1 / 2 : ℝ) * ‖u - v‖[G] ^ (2 : ℕ)) := by
  let T : E →ₗ[ℝ] E := Matrix.toEuclideanLin G.1
  let u0 : E := u - x0
  let v0 : E := v - x0
  have hb : b = 1 - a := by linarith
  have hcombo_shift :
      a • u + b • v - x0 = a • u0 + b • v0 := by
    -- Move the common base point `x0` inside the affine combination.
    simpa [u0, v0] using (sub_point_affine_combo (x := x0) (u := u) (v := v) hab)
  have hu0_sq : ‖u0‖[G] ^ (2 : ℕ) = inner ℝ (T u0) u0 := by
    simpa [T, u0] using positiveDefMatrixNorm_sq_eq_matrix_quadratic (G := G) u0
  have hv0_sq : ‖v0‖[G] ^ (2 : ℕ) = inner ℝ (T v0) v0 := by
    simpa [T, v0] using positiveDefMatrixNorm_sq_eq_matrix_quadratic (G := G) v0
  have hdiff_sq : ‖u0 - v0‖[G] ^ (2 : ℕ) = inner ℝ (T (u0 - v0)) (u0 - v0) := by
    simpa [T] using positiveDefMatrixNorm_sq_eq_matrix_quadratic (G := G) (u0 - v0)
  have hcross :
      inner ℝ (T v0) u0 = inner ℝ (T u0) v0 := by
    simpa [T] using positiveDefMatrixNorm_matrix_quadratic_symm (G := G) v0 u0
  have hcombo_expand :
      inner ℝ (T (a • u0 + b • v0)) (a • u0 + b • v0) =
        a ^ (2 : ℕ) * inner ℝ (T u0) u0 +
          (a * b) * inner ℝ (T u0) v0 +
            (a * b) * inner ℝ (T v0) u0 +
              b ^ (2 : ℕ) * inner ℝ (T v0) v0 := by
    -- Expand the quadratic form of the affine combination into its diagonal and cross terms.
    simp [T, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, pow_two]
    ring
  have hdiff_expand :
      inner ℝ (T (u0 - v0)) (u0 - v0) =
        inner ℝ (T u0) u0 - 2 * inner ℝ (T u0) v0 + inner ℝ (T v0) v0 := by
    -- Expand the squared difference and use symmetry to identify the two cross terms.
    calc
      inner ℝ (T (u0 - v0)) (u0 - v0)
          = inner ℝ (T u0) u0 - inner ℝ (T u0) v0 - inner ℝ (T v0) u0 +
              inner ℝ (T v0) v0 := by
                simp [sub_eq_add_neg, T, inner_add_left, inner_add_right, inner_neg_left,
                  inner_neg_right]
                ring_nf
      _ = inner ℝ (T u0) u0 - 2 * inner ℝ (T u0) v0 + inner ℝ (T v0) v0 := by
            rw [hcross]
            ring
  rw [positiveDefMatrixNorm_quadraticDistanceTo_apply,
    positiveDefMatrixNorm_quadraticDistanceTo_apply,
    positiveDefMatrixNorm_quadraticDistanceTo_apply,
    hcombo_shift]
  calc
    (1 / 2 : ℝ) * ‖a • u0 + b • v0‖[G] ^ (2 : ℕ)
        = (1 / 2 : ℝ) * inner ℝ (T (a • u0 + b • v0)) (a • u0 + b • v0) := by
            rw [positiveDefMatrixNorm_sq_eq_matrix_quadratic (G := G) (a • u0 + b • v0)]
    _ =
        (1 / 2 : ℝ) *
          (a ^ (2 : ℕ) * inner ℝ (T u0) u0 +
            (a * b) * inner ℝ (T u0) v0 +
              (a * b) * inner ℝ (T v0) u0 +
                b ^ (2 : ℕ) * inner ℝ (T v0) v0) := by
                  rw [hcombo_expand]
    _ =
        a * ((1 / 2 : ℝ) * inner ℝ (T u0) u0) +
          b * ((1 / 2 : ℝ) * inner ℝ (T v0) v0) -
            a * b *
              ((1 / 2 : ℝ) *
                (inner ℝ (T u0) u0 - 2 * inner ℝ (T u0) v0 + inner ℝ (T v0) v0)) := by
                  rw [hcross, hb]
                  ring
    _ =
        a * ((1 / 2 : ℝ) * ‖u0‖[G] ^ (2 : ℕ)) +
          b * ((1 / 2 : ℝ) * ‖v0‖[G] ^ (2 : ℕ)) -
            a * b * ((1 / 2 : ℝ) * inner ℝ (T (u0 - v0)) (u0 - v0)) := by
              rw [← hdiff_expand]
              rw [← hu0_sq, ← hv0_sq]
    _ =
        a * ((1 / 2 : ℝ) * ‖u0‖[G] ^ (2 : ℕ)) +
          b * ((1 / 2 : ℝ) * ‖v0‖[G] ^ (2 : ℕ)) -
            a * b * ((1 / 2 : ℝ) * ‖u0 - v0‖[G] ^ (2 : ℕ)) := by
              rw [← hdiff_sq]
    _ =
        a * (positiveDefMatrixNorm G.1 G.2).quadraticDistanceTo x0 u +
          b * (positiveDefMatrixNorm G.1 G.2).quadraticDistanceTo x0 v -
            a * b * ((1 / 2 : ℝ) * ‖u - v‖[G] ^ (2 : ℕ)) := by
              have hdiff_eq : u0 - v0 = u - v := by
                simp [u0, v0]
              simp [u0, v0, hdiff_eq]

/-- Helper for Proposition 7.16: the weighted quadratic-distance owner is `1`-strongly convex on
the whole space with respect to the weighted norm. -/
private lemma weighted_quadraticDistanceTo_strongConvexOnWith
    (G : {G : Matrix (Fin n) (Fin n) ℝ // G.PosDef}) (x0 : E) :
    StrongConvexOnWith
      (positiveDefMatrixNorm G.1 G.2)
      1
      Set.univ
      ((positiveDefMatrixNorm G.1 G.2).quadraticDistanceTo x0) := by
  refine ⟨convex_univ, by norm_num, ?_⟩
  intro x hx y hy a b ha hb hab
  -- The owner satisfies the strong-convexity inequality with equality, so it is enough to
  -- rewrite the affine-combination value exactly.
  exact le_of_eq <| by
    simpa [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
      weighted_quadraticDistanceTo_affine_combo_exact (G := G) x0 x y a b hab

/-- Helper for Proposition 7.16: the weighted proximal minimand inherits modulus
`scheme.smoothness` from the quadratic-distance owner because the gradient term is affine. -/
lemma proximalMinimand_strongConvexOnWith
    {N : ℕ} (scheme : AcceleratedConvexMinimizationScheme n N)
    (k : ℕ) :
    StrongConvexOnWith
      (positiveDefMatrixNorm scheme.metricMatrix.1 scheme.metricMatrix.2)
      (scheme.smoothness : ℝ)
      scheme.problem.feasibleSet
      (acceleratedSchemeProximalMinimand
        scheme.gradient
        scheme.metricMatrix
        scheme.smoothness
        scheme.initialPoint
        scheme.x
        scheme.v
        k) := by
  refine ⟨scheme.convexSet, ?_, ?_⟩
  · have hsmooth : 0 < (scheme.smoothness : NNReal) := by
      exact pos_iff_ne_zero.mpr (Units.ne_zero scheme.smoothness)
    exact_mod_cast hsmooth
  intro x hx y hy a b ha hb hab
  -- Route correction: keep the source route by rewriting the proximal minimand into an affine
  -- gradient term plus the canonical weighted quadratic-distance owner before applying algebra.
  rw [proximalMinimand_eq_weightedQuadraticDistance,
    proximalMinimand_eq_weightedQuadraticDistance,
    proximalMinimand_eq_weightedQuadraticDistance]
  rw [weighted_gradient_sum_inner_affine_combo (scheme := scheme) k hab]
  rw [weighted_quadraticDistanceTo_affine_combo_exact
    (G := scheme.metricMatrix) scheme.initialPoint x y a b hab]
  exact le_of_eq <| by
    simp [smul_eq_mul]
    ring

/-- Helper for Proposition 7.16: the proximal argmin property of `v_{k+1}` upgrades to the
weighted quadratic-growth inequality required by the estimate sequence. -/
lemma weighted_proximal_argmin_variational_inequality
    {N : ℕ} (scheme : AcceleratedConvexMinimizationScheme n N)
    {k : ℕ} (hk : k < N) {u : E}
    (hu : u ∈ scheme.problem.feasibleSet) :
    acceleratedSchemeProximalMinimand
        scheme.gradient
        scheme.metricMatrix
        scheme.smoothness
        scheme.initialPoint
        scheme.x
        scheme.v
        k
        u ≥
      acceleratedSchemeProximalMinimand
        scheme.gradient
        scheme.metricMatrix
        scheme.smoothness
        scheme.initialPoint
        scheme.x
        scheme.v
        k
        (scheme.v (k + 1)) +
        ((scheme.smoothness : ℝ) / 2) * ‖u - scheme.v (k + 1)‖[scheme.metricMatrix] ^ (2 : ℕ) :=
    by
  let prox :
      E → ℝ :=
    acceleratedSchemeProximalMinimand
      scheme.gradient
      scheme.metricMatrix
      scheme.smoothness
      scheme.initialPoint
      scheme.x
      scheme.v
      k
  have hv_succ :=
    mem_constrainedArgmin_iff.mp (scheme.v_succ_mem_argmin_set hk)
  have hstrong := proximalMinimand_strongConvexOnWith (scheme := scheme) k
  -- Apply the canonical quadratic-growth theorem at the constrained minimizer `v_{k+1}`.
  simpa [prox] using
    hstrong.quadratic_growth_of_isMinOn_of_mem hv_succ.1 hv_succ.2 u hu

/-- Helper for Proposition 7.16: the source estimate-sequence potential
`Ψ_k(u) = L D_G(x₀, u) + ∑_{i < k} a_i [φ(y_i) + ⟪∇φ(y_i), u - y_i⟫]`
packaging the textbook proof route directly on the Chapter 7 owner. -/
def estimateSequencePotential
    {N : ℕ} (scheme : AcceleratedConvexMinimizationScheme n N)
    (k : ℕ) (u : E) : ℝ :=
  (scheme.smoothness : ℝ) *
      (positiveDefMatrixNorm scheme.metricMatrix.1 scheme.metricMatrix.2).quadraticDistanceTo
        scheme.initialPoint
        u +
    Finset.sum (Finset.range k) (fun i ↦
      ((((i : ℝ) + 1) / 2) : ℝ) *
        (scheme.problem (acceleratedSchemeSearchPoint scheme.x scheme.v i) +
          inner ℝ (scheme.gradient (acceleratedSchemeSearchPoint scheme.x scheme.v i))
            (u - acceleratedSchemeSearchPoint scheme.x scheme.v i)))

/-- Helper for Proposition 7.16: `Ψ_{k+1}` is the stage-`k` proximal minimand plus the
`u`-independent source constant. -/
lemma estimateSequencePotential_succ_eq_proximalMinimand_add_constant
    {N : ℕ} (scheme : AcceleratedConvexMinimizationScheme n N)
    (k : ℕ) (u : E) :
    estimateSequencePotential scheme (k + 1) u =
      acceleratedSchemeProximalMinimand
          scheme.gradient
          scheme.metricMatrix
          scheme.smoothness
          scheme.initialPoint
          scheme.x
          scheme.v
          k
          u +
        Finset.sum (Finset.range (k + 1)) (fun i ↦
          ((((i : ℝ) + 1) / 2) : ℝ) *
            (scheme.problem (acceleratedSchemeSearchPoint scheme.x scheme.v i) +
              inner ℝ (scheme.gradient (acceleratedSchemeSearchPoint scheme.x scheme.v i))
                (scheme.initialPoint - acceleratedSchemeSearchPoint scheme.x scheme.v i))) := by
  -- Expand `Ψ_{k+1}` and split each displacement `u - yᵢ` at the common base point `x₀`.
  rw [estimateSequencePotential, proximalMinimand_eq_weightedQuadraticDistance]
  rw [acceleratedSchemeWeightedGradientSum_eq_sum]
  have hsplit :
      Finset.sum (Finset.range (k + 1)) (fun i ↦
        ((((i : ℝ) + 1) / 2) : ℝ) *
          inner ℝ (scheme.gradient (acceleratedSchemeSearchPoint scheme.x scheme.v i))
            (u - acceleratedSchemeSearchPoint scheme.x scheme.v i)) =
        inner ℝ
          (Finset.sum (Finset.range (k + 1)) (fun i ↦
            ((((i : ℝ) + 1) / 2) : ℝ) •
              scheme.gradient (acceleratedSchemeSearchPoint scheme.x scheme.v i)))
          (u - scheme.initialPoint) +
        Finset.sum (Finset.range (k + 1)) (fun i ↦
          ((((i : ℝ) + 1) / 2) : ℝ) *
            inner ℝ (scheme.gradient (acceleratedSchemeSearchPoint scheme.x scheme.v i))
              (scheme.initialPoint - acceleratedSchemeSearchPoint scheme.x scheme.v i)) := by
    -- The stagewise linear term splits into the weighted gradient sum against `u - x₀` plus the
    -- source constant that only depends on the search points.
    calc
      Finset.sum (Finset.range (k + 1)) (fun i ↦
        ((((i : ℝ) + 1) / 2) : ℝ) *
          inner ℝ (scheme.gradient (acceleratedSchemeSearchPoint scheme.x scheme.v i))
            (u - acceleratedSchemeSearchPoint scheme.x scheme.v i))
          =
        Finset.sum (Finset.range (k + 1)) (fun i ↦
          ((((i : ℝ) + 1) / 2) : ℝ) *
            inner ℝ (scheme.gradient (acceleratedSchemeSearchPoint scheme.x scheme.v i))
              ((u - scheme.initialPoint) +
                (scheme.initialPoint - acceleratedSchemeSearchPoint scheme.x scheme.v i))) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              congr 1
              abel
      _ =
        Finset.sum (Finset.range (k + 1)) (fun i ↦
          ((((i : ℝ) + 1) / 2) : ℝ) *
            (inner ℝ (scheme.gradient (acceleratedSchemeSearchPoint scheme.x scheme.v i))
                (u - scheme.initialPoint) +
              inner ℝ (scheme.gradient (acceleratedSchemeSearchPoint scheme.x scheme.v i))
                (scheme.initialPoint - acceleratedSchemeSearchPoint scheme.x scheme.v i))) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [inner_add_right]
      _ =
        Finset.sum (Finset.range (k + 1)) (fun i ↦
          ((((i : ℝ) + 1) / 2) : ℝ) *
            inner ℝ (scheme.gradient (acceleratedSchemeSearchPoint scheme.x scheme.v i))
              (u - scheme.initialPoint)) +
          Finset.sum (Finset.range (k + 1)) (fun i ↦
            ((((i : ℝ) + 1) / 2) : ℝ) *
              inner ℝ (scheme.gradient (acceleratedSchemeSearchPoint scheme.x scheme.v i))
                (scheme.initialPoint - acceleratedSchemeSearchPoint scheme.x scheme.v i)) := by
              calc
                Finset.sum (Finset.range (k + 1)) (fun i ↦
                  ((((i : ℝ) + 1) / 2) : ℝ) *
                    (inner ℝ (scheme.gradient (acceleratedSchemeSearchPoint scheme.x scheme.v i))
                        (u - scheme.initialPoint) +
                      inner ℝ (scheme.gradient (acceleratedSchemeSearchPoint scheme.x scheme.v i))
                        (scheme.initialPoint - acceleratedSchemeSearchPoint scheme.x scheme.v i))) =
                    Finset.sum (Finset.range (k + 1)) (fun i ↦
                      ((((i : ℝ) + 1) / 2) : ℝ) *
                          inner ℝ (scheme.gradient (acceleratedSchemeSearchPoint scheme.x scheme.v i))
                            (u - scheme.initialPoint) +
                        ((((i : ℝ) + 1) / 2) : ℝ) *
                          inner ℝ (scheme.gradient (acceleratedSchemeSearchPoint scheme.x scheme.v i))
                            (scheme.initialPoint - acceleratedSchemeSearchPoint scheme.x scheme.v i)) := by
                      refine Finset.sum_congr rfl ?_
                      intro i hi
                      ring
                _ = _ := by
                      rw [Finset.sum_add_distrib]
      _ =
        inner ℝ
          (Finset.sum (Finset.range (k + 1)) (fun i ↦
            ((((i : ℝ) + 1) / 2) : ℝ) •
              scheme.gradient (acceleratedSchemeSearchPoint scheme.x scheme.v i)))
          (u - scheme.initialPoint) +
        Finset.sum (Finset.range (k + 1)) (fun i ↦
          ((((i : ℝ) + 1) / 2) : ℝ) *
            inner ℝ (scheme.gradient (acceleratedSchemeSearchPoint scheme.x scheme.v i))
              (scheme.initialPoint - acceleratedSchemeSearchPoint scheme.x scheme.v i)) := by
              refine congrArg₂ (· + ·) ?_ rfl
              calc
                Finset.sum (Finset.range (k + 1)) (fun i ↦
                  ((((i : ℝ) + 1) / 2) : ℝ) *
                    inner ℝ (scheme.gradient (acceleratedSchemeSearchPoint scheme.x scheme.v i))
                      (u - scheme.initialPoint)) =
                    Finset.sum (Finset.range (k + 1)) (fun i ↦
                      inner ℝ
                        (((((i : ℝ) + 1) / 2) : ℝ) •
                          scheme.gradient (acceleratedSchemeSearchPoint scheme.x scheme.v i))
                        (u - scheme.initialPoint)) := by
                      refine Finset.sum_congr rfl ?_
                      intro i hi
                      rw [real_inner_smul_left]
                _ = inner ℝ
                    (Finset.sum (Finset.range (k + 1)) (fun i ↦
                      ((((i : ℝ) + 1) / 2) : ℝ) •
                        scheme.gradient (acceleratedSchemeSearchPoint scheme.x scheme.v i)))
                    (u - scheme.initialPoint) := by
                      rw [sum_inner]
  have hconst_expand :
      Finset.sum (Finset.range (k + 1)) (fun i ↦
        ((((i : ℝ) + 1) / 2) : ℝ) *
          (scheme.problem (acceleratedSchemeSearchPoint scheme.x scheme.v i) +
            inner ℝ (scheme.gradient (acceleratedSchemeSearchPoint scheme.x scheme.v i))
              (scheme.initialPoint - acceleratedSchemeSearchPoint scheme.x scheme.v i))) =
        Finset.sum (Finset.range (k + 1)) (fun i ↦
          ((((i : ℝ) + 1) / 2) : ℝ) *
            scheme.problem (acceleratedSchemeSearchPoint scheme.x scheme.v i)) +
          Finset.sum (Finset.range (k + 1)) (fun i ↦
            ((((i : ℝ) + 1) / 2) : ℝ) *
              inner ℝ (scheme.gradient (acceleratedSchemeSearchPoint scheme.x scheme.v i))
                (scheme.initialPoint - acceleratedSchemeSearchPoint scheme.x scheme.v i)) := by
    calc
      Finset.sum (Finset.range (k + 1)) (fun i ↦
        ((((i : ℝ) + 1) / 2) : ℝ) *
          (scheme.problem (acceleratedSchemeSearchPoint scheme.x scheme.v i) +
            inner ℝ (scheme.gradient (acceleratedSchemeSearchPoint scheme.x scheme.v i))
              (scheme.initialPoint - acceleratedSchemeSearchPoint scheme.x scheme.v i))) =
          Finset.sum (Finset.range (k + 1)) (fun i ↦
            ((((i : ℝ) + 1) / 2) : ℝ) *
                scheme.problem (acceleratedSchemeSearchPoint scheme.x scheme.v i) +
              ((((i : ℝ) + 1) / 2) : ℝ) *
                inner ℝ (scheme.gradient (acceleratedSchemeSearchPoint scheme.x scheme.v i))
                  (scheme.initialPoint - acceleratedSchemeSearchPoint scheme.x scheme.v i)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            ring
      _ = _ := by
            rw [Finset.sum_add_distrib]
  have hu_expand :
      Finset.sum (Finset.range (k + 1)) (fun i ↦
        ((((i : ℝ) + 1) / 2) : ℝ) *
          (scheme.problem (acceleratedSchemeSearchPoint scheme.x scheme.v i) +
            inner ℝ (scheme.gradient (acceleratedSchemeSearchPoint scheme.x scheme.v i))
              (u - acceleratedSchemeSearchPoint scheme.x scheme.v i))) =
        Finset.sum (Finset.range (k + 1)) (fun i ↦
          ((((i : ℝ) + 1) / 2) : ℝ) *
            scheme.problem (acceleratedSchemeSearchPoint scheme.x scheme.v i)) +
          Finset.sum (Finset.range (k + 1)) (fun i ↦
            ((((i : ℝ) + 1) / 2) : ℝ) *
              inner ℝ (scheme.gradient (acceleratedSchemeSearchPoint scheme.x scheme.v i))
                (u - acceleratedSchemeSearchPoint scheme.x scheme.v i)) := by
    calc
      Finset.sum (Finset.range (k + 1)) (fun i ↦
        ((((i : ℝ) + 1) / 2) : ℝ) *
          (scheme.problem (acceleratedSchemeSearchPoint scheme.x scheme.v i) +
            inner ℝ (scheme.gradient (acceleratedSchemeSearchPoint scheme.x scheme.v i))
              (u - acceleratedSchemeSearchPoint scheme.x scheme.v i))) =
          Finset.sum (Finset.range (k + 1)) (fun i ↦
            ((((i : ℝ) + 1) / 2) : ℝ) *
                scheme.problem (acceleratedSchemeSearchPoint scheme.x scheme.v i) +
              ((((i : ℝ) + 1) / 2) : ℝ) *
                inner ℝ (scheme.gradient (acceleratedSchemeSearchPoint scheme.x scheme.v i))
                  (u - acceleratedSchemeSearchPoint scheme.x scheme.v i)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            ring
      _ = _ := by
            rw [Finset.sum_add_distrib]
  -- After the split, the remaining terms are exactly the proximal minimand plus the stagewise
  -- source constant.
  calc
    (scheme.smoothness : ℝ) *
        (positiveDefMatrixNorm scheme.metricMatrix.1 scheme.metricMatrix.2).quadraticDistanceTo
          scheme.initialPoint
          u +
      Finset.sum (Finset.range (k + 1)) (fun i ↦
        ((((i : ℝ) + 1) / 2) : ℝ) *
          (scheme.problem (acceleratedSchemeSearchPoint scheme.x scheme.v i) +
            inner ℝ (scheme.gradient (acceleratedSchemeSearchPoint scheme.x scheme.v i))
              (u - acceleratedSchemeSearchPoint scheme.x scheme.v i)))
        =
      (inner ℝ
          (Finset.sum (Finset.range (k + 1)) (fun i ↦
            ((((i : ℝ) + 1) / 2) : ℝ) •
              scheme.gradient (acceleratedSchemeSearchPoint scheme.x scheme.v i)))
          (u - scheme.initialPoint) +
        (scheme.smoothness : ℝ) *
          (positiveDefMatrixNorm scheme.metricMatrix.1 scheme.metricMatrix.2).quadraticDistanceTo
            scheme.initialPoint
            u) +
        Finset.sum (Finset.range (k + 1)) (fun i ↦
          ((((i : ℝ) + 1) / 2) : ℝ) *
            (scheme.problem (acceleratedSchemeSearchPoint scheme.x scheme.v i) +
              inner ℝ (scheme.gradient (acceleratedSchemeSearchPoint scheme.x scheme.v i))
                (scheme.initialPoint - acceleratedSchemeSearchPoint scheme.x scheme.v i))) := by
            rw [hu_expand, hsplit, hconst_expand]
            ring
    _ = _ := by rfl

/-- Helper for Proposition 7.16: `v_{k+1}` minimizes the source potential `Ψ_{k+1}` over the
feasible set because the extra source term is stagewise constant. -/
lemma estimateSequencePotential_succ_argmin_le
    {N : ℕ} (scheme : AcceleratedConvexMinimizationScheme n N)
    {k : ℕ} (hk : k < N) {u : E}
    (hu : u ∈ scheme.problem.feasibleSet) :
    estimateSequencePotential scheme (k + 1) (scheme.v (k + 1)) ≤
      estimateSequencePotential scheme (k + 1) u := by
  -- Rewrite both potentials as the same stage constant plus the proximal minimand.
  rw [estimateSequencePotential_succ_eq_proximalMinimand_add_constant,
    estimateSequencePotential_succ_eq_proximalMinimand_add_constant]
  -- The minimizing property of `v_{k+1}` for the proximal problem survives after adding the same
  -- source constant to both sides.
  simpa [add_comm, add_left_comm, add_assoc] using
    add_le_add_right (weighted_proximal_argmin_le (scheme := scheme) hk hu)
      (Finset.sum (Finset.range (k + 1)) (fun i ↦
        ((((i : ℝ) + 1) / 2) : ℝ) *
          (scheme.problem (acceleratedSchemeSearchPoint scheme.x scheme.v i) +
            inner ℝ (scheme.gradient (acceleratedSchemeSearchPoint scheme.x scheme.v i))
              (scheme.initialPoint - acceleratedSchemeSearchPoint scheme.x scheme.v i))))

/-- Helper for Proposition 7.16: the difference between the new iterate and the old search point
is the textbook scaled displacement of the prox centers. -/
lemma x_succ_sub_searchPoint_eq_smul_v_diff
    {N : ℕ} (scheme : AcceleratedConvexMinimizationScheme n N)
    {k : ℕ} (hk : k < N) :
    scheme.x (k + 1) - acceleratedSchemeSearchPoint scheme.x scheme.v k =
      (2 / (((k : ℝ) + 2))) • (scheme.v (k + 1) - scheme.v k) := by
  -- Expand both affine combinations and collect the common `x_k` coefficient.
  rw [scheme.x_succ k hk, acceleratedSchemeSearchPoint_eq]
  calc
    ((k : ℝ) / (k + 2)) • scheme.x k + ((2 : ℝ) / (k + 2)) • scheme.v (k + 1) -
        (((k : ℝ) / (k + 2)) • scheme.x k + ((2 : ℝ) / (k + 2)) • scheme.v k)
        =
      ((2 : ℝ) / (k + 2)) • (scheme.v (k + 1) - scheme.v k) := by
            module

/-- Helper for Proposition 7.16: every feasible tangent model in `Ψ_k` is dominated by the
objective value at a constrained minimizer `xStar`. -/
private lemma tangent_model_at_feasible_le_constrained_minimizer
    {N : ℕ} (scheme : AcceleratedConvexMinimizationScheme n N)
    {y xStar : E}
    (hy : y ∈ scheme.problem.feasibleSet)
    (hxStar : xStar ∈ argmin[scheme.problem.feasibleSet] scheme.problem) :
    scheme.problem y + inner ℝ (scheme.gradient y) (xStar - y) ≤ scheme.problem xStar := by
  -- Use the convex lower-support inequality at the feasible base point `y`.
  have hxStar_mem : xStar ∈ scheme.problem.feasibleSet :=
    (mem_constrainedArgmin_iff.mp hxStar).1
  have hgradWithin :
      HasGradientWithinAt scheme.problem (scheme.gradient y) scheme.problem.feasibleSet y :=
    by
      simpa using
        (scheme.gradient_hasGradientAt hy).hasFDerivAt.hasFDerivWithinAt.hasGradientWithinAt
  simpa using
    scheme.objective_convex.lower_tangent_plane_of_hasGradientWithinAt
      y hy (scheme.gradient y) hgradWithin xStar hxStar_mem

/-- Helper for Proposition 7.16: evaluating `Ψ_k` at a constrained minimizer `xStar` bounds each
linearized stage term by `φ(xStar)`, leaving only the initial quadratic-distance term. -/
lemma estimateSequencePotential_at_constrained_minimizer_le
    {N : ℕ} (scheme : AcceleratedConvexMinimizationScheme n N)
    {k : ℕ} (hk : k ≤ N) {xStar : E}
    (hxStar : xStar ∈ argmin[scheme.problem.feasibleSet] scheme.problem) :
    estimateSequencePotential scheme k xStar ≤
      Finset.sum (Finset.range k) (fun i ↦ ((((i : ℝ) + 1) / 2) : ℝ)) * scheme.problem xStar +
        (scheme.smoothness : ℝ) *
          (positiveDefMatrixNorm scheme.metricMatrix.1 scheme.metricMatrix.2).quadraticDistanceTo
            scheme.initialPoint
            xStar := by
  -- Keep the source potential explicit and bound each tangent model by `φ(xStar)` using the
  -- minimizer-support inequality from convexity.
  rw [estimateSequencePotential]
  have hsum :
      Finset.sum (Finset.range k) (fun i ↦
        ((((i : ℝ) + 1) / 2) : ℝ) *
          (scheme.problem (acceleratedSchemeSearchPoint scheme.x scheme.v i) +
            inner ℝ (scheme.gradient (acceleratedSchemeSearchPoint scheme.x scheme.v i))
              (xStar - acceleratedSchemeSearchPoint scheme.x scheme.v i))) ≤
        Finset.sum (Finset.range k) (fun i ↦
          ((((i : ℝ) + 1) / 2) : ℝ) * scheme.problem xStar) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    have hi_le : i ≤ N := Nat.le_trans (Nat.le_of_lt (Finset.mem_range.mp hi)) hk
    have hyi :
        acceleratedSchemeSearchPoint scheme.x scheme.v i ∈ scheme.problem.feasibleSet :=
      (iterates_and_searchPoint_mem_feasible (scheme := scheme) hi_le).2.2
    exact mul_le_mul_of_nonneg_left
      (tangent_model_at_feasible_le_constrained_minimizer
        (scheme := scheme) hyi hxStar)
      (by positivity)
  have hsum_eq :
      Finset.sum (Finset.range k) (fun i ↦ ((((i : ℝ) + 1) / 2) : ℝ) * scheme.problem xStar) =
        Finset.sum (Finset.range k) (fun i ↦ ((((i : ℝ) + 1) / 2) : ℝ)) * scheme.problem xStar := by
    rw [← Finset.sum_mul]
  calc
    (scheme.smoothness : ℝ) *
        (positiveDefMatrixNorm scheme.metricMatrix.1 scheme.metricMatrix.2).quadraticDistanceTo
          scheme.initialPoint
          xStar +
      Finset.sum (Finset.range k) (fun i ↦
        ((((i : ℝ) + 1) / 2) : ℝ) *
          (scheme.problem (acceleratedSchemeSearchPoint scheme.x scheme.v i) +
            inner ℝ (scheme.gradient (acceleratedSchemeSearchPoint scheme.x scheme.v i))
              (xStar - acceleratedSchemeSearchPoint scheme.x scheme.v i))) ≤
      (scheme.smoothness : ℝ) *
          (positiveDefMatrixNorm scheme.metricMatrix.1 scheme.metricMatrix.2).quadraticDistanceTo
            scheme.initialPoint
            xStar +
        Finset.sum (Finset.range k) (fun i ↦ ((((i : ℝ) + 1) / 2) : ℝ) * scheme.problem xStar) :=
      by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_left
            hsum
            ((scheme.smoothness : ℝ) *
              (positiveDefMatrixNorm scheme.metricMatrix.1 scheme.metricMatrix.2).quadraticDistanceTo
                scheme.initialPoint
                xStar)
    _ =
      Finset.sum (Finset.range k) (fun i ↦ ((((i : ℝ) + 1) / 2) : ℝ)) * scheme.problem xStar +
        (scheme.smoothness : ℝ) *
          (positiveDefMatrixNorm scheme.metricMatrix.1 scheme.metricMatrix.2).quadraticDistanceTo
            scheme.initialPoint
            xStar := by
          rw [hsum_eq]
          ring

/-- Helper for Proposition 7.16: the terminal estimate-sequence potential at `v_N` is bounded by
its value at the constrained minimizer `xStar`, then by the tangent-plane evaluation of `Ψ_N`. -/
lemma estimate_sequence_at_constrained_minimizer_le
    {N : ℕ} (scheme : AcceleratedConvexMinimizationScheme n N)
    (hN : 1 ≤ N) {xStar : E}
    (hxStar : xStar ∈ argmin[scheme.problem.feasibleSet] scheme.problem) :
    estimateSequencePotential scheme N (scheme.v N) ≤
      Finset.sum (Finset.range N) (fun i ↦ ((((i : ℝ) + 1) / 2) : ℝ)) * scheme.problem xStar +
        (scheme.smoothness : ℝ) *
          (positiveDefMatrixNorm scheme.metricMatrix.1 scheme.metricMatrix.2).quadraticDistanceTo
            scheme.initialPoint
            xStar := by
  -- Rewrite the terminal stage as `(N - 1) + 1`, compare the minimizer `v_N` to `xStar`, and
  -- then reuse the tangent-plane upper bound for `Ψ_N(xStar)`.
  have hN_pos : 0 < N := Nat.succ_le_iff.mp hN
  have hpred_lt : N - 1 < N := Nat.pred_lt hN_pos.ne'
  have hxStar_mem : xStar ∈ scheme.problem.feasibleSet :=
    (mem_constrainedArgmin_iff.mp hxStar).1
  have hpred_eq : (N - 1) + 1 = N := Nat.succ_pred_eq_of_pos hN_pos
  calc
    estimateSequencePotential scheme N (scheme.v N)
        = estimateSequencePotential scheme ((N - 1) + 1) (scheme.v ((N - 1) + 1)) := by
            rw [hpred_eq]
    _ ≤ estimateSequencePotential scheme ((N - 1) + 1) xStar :=
      estimateSequencePotential_succ_argmin_le
        (scheme := scheme) (k := N - 1) hpred_lt hxStar_mem
    _ = estimateSequencePotential scheme N xStar := by rw [hpred_eq]
    _ ≤
        Finset.sum (Finset.range N) (fun i ↦ ((((i : ℝ) + 1) / 2) : ℝ)) * scheme.problem xStar +
          (scheme.smoothness : ℝ) *
            (positiveDefMatrixNorm scheme.metricMatrix.1 scheme.metricMatrix.2).quadraticDistanceTo
              scheme.initialPoint
              xStar :=
      estimateSequencePotential_at_constrained_minimizer_le
        (scheme := scheme) (k := N) (by exact le_rfl) hxStar

/-- Helper for Proposition 7.16: the estimate-sequence potential dominates the weighted objective
at the current iterate together with the quadratic prox term from the current prox center. -/
lemma estimateSequencePotential_lower_bound
    {N : ℕ} (scheme : AcceleratedConvexMinimizationScheme n N)
    {k : ℕ} (hk : k ≤ N) {u : E}
    (hgradient_lipschitz :
      ∀ ⦃x y : E⦄,
        x ∈ scheme.problem.feasibleSet →
        y ∈ scheme.problem.feasibleSet →
          ‖scheme.gradient x - scheme.gradient y‖[scheme.metricMatrix,*] ≤
            (scheme.smoothness : ℝ) * ‖x - y‖[scheme.metricMatrix])
    (hu : u ∈ scheme.problem.feasibleSet) :
    Finset.sum (Finset.range k) (fun i ↦ ((((i : ℝ) + 1) / 2) : ℝ)) * scheme.problem (scheme.x k) +
        (scheme.smoothness : ℝ) *
          (positiveDefMatrixNorm scheme.metricMatrix.1 scheme.metricMatrix.2).quadraticDistanceTo
            (scheme.v k)
            u ≤
      estimateSequencePotential scheme k u := by
  induction k generalizing u with
  | zero =>
      -- At stage `0`, both the weight sum and the stagewise linearized sum vanish, and `v₀ = x₀`.
      simpa [estimateSequencePotential, scheme.v_zero]
  | succ k ih =>
      let p : Seminorm ℝ E :=
        positiveDefMatrixNorm scheme.metricMatrix.1 scheme.metricMatrix.2
      let yk : E := acceleratedSchemeSearchPoint scheme.x scheme.v k
      let ak : ℝ := ((((k : ℝ) + 1) / 2) : ℝ)
      let Aprev : ℝ := Finset.sum (Finset.range k) (fun i ↦ ((((i : ℝ) + 1) / 2) : ℝ))
      let Anext : ℝ := Finset.sum (Finset.range (k + 1)) (fun i ↦ ((((i : ℝ) + 1) / 2) : ℝ))
      have hk_lt : k < N := Nat.lt_of_succ_le hk
      have hk_le : k ≤ N := Nat.le_of_lt hk_lt
      have hAprev_formula : Aprev = (k : ℝ) * ((k : ℝ) + 1) / 4 := by
        simp [Aprev, estimate_weight_sum_eq]
      have hAnext_formula : Anext = ((k : ℝ) + 1) * ((k : ℝ) + 2) / 4 := by
        calc
          Anext = ((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1) / 4 := by
            simp [Anext, estimate_weight_sum_eq]
          _ = ((k : ℝ) + 1) * ((k : ℝ) + 2) / 4 := by
            have hk1 : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by
              norm_num [Nat.cast_add]
            rw [hk1]
            ring
      have hAprev_nonneg : 0 ≤ Aprev := by
        rw [hAprev_formula]
        positivity
      have hAnext_nonneg : 0 ≤ Anext := by
        rw [hAnext_formula]
        positivity
      have hAnext_eq : Anext = Aprev + ak := by
        simp [Anext, Aprev, ak, Finset.sum_range_succ]
      have hAprev_eq : Aprev = ak * ((k : ℝ) / 2) := by
        rw [hAprev_formula]
        dsimp [ak]
        ring
      have hAnext_beta : Anext * (2 / ((k : ℝ) + 2)) = ak := by
        rw [hAnext_formula]
        dsimp [ak]
        have hk2 : (k : ℝ) + 2 ≠ 0 := by positivity
        field_simp [hk2]
        ring
      have hcoef_quad : Anext * (2 / ((k : ℝ) + 2)) ^ (2 : ℕ) ≤ 1 := by
        rw [hAnext_formula]
        have hk2 : (k : ℝ) + 2 ≠ 0 := by positivity
        field_simp [hk2]
        nlinarith
      have hmem_k :=
        iterates_and_searchPoint_mem_feasible (scheme := scheme) (k := k) hk_le
      have hmem_succ :=
        iterates_and_searchPoint_mem_feasible (scheme := scheme) (k := k + 1) hk
      have hxk_mem : scheme.x k ∈ scheme.problem.feasibleSet := hmem_k.1
      have hvk_mem : scheme.v k ∈ scheme.problem.feasibleSet := hmem_k.2.1
      have hyk_mem : yk ∈ scheme.problem.feasibleSet := by
        simpa [yk] using hmem_k.2.2
      have hxsucc_mem : scheme.x (k + 1) ∈ scheme.problem.feasibleSet := hmem_succ.1
      have hvsucc_mem : scheme.v (k + 1) ∈ scheme.problem.feasibleSet := hmem_succ.2.1
      -- First lift the induction hypothesis from `v_{k+1}` to an arbitrary feasible comparison
      -- point `u` using the quadratic growth of the proximal subproblem.
      have hpotential_lift :
          estimateSequencePotential scheme (k + 1) (scheme.v (k + 1)) +
              (scheme.smoothness : ℝ) * p.quadraticDistanceTo (scheme.v (k + 1)) u ≤
            estimateSequencePotential scheme (k + 1) u := by
        let stageConst : ℝ :=
          Finset.sum (Finset.range (k + 1)) (fun i ↦
            ((((i : ℝ) + 1) / 2) : ℝ) *
              (scheme.problem (acceleratedSchemeSearchPoint scheme.x scheme.v i) +
                inner ℝ (scheme.gradient (acceleratedSchemeSearchPoint scheme.x scheme.v i))
                  (scheme.initialPoint - acceleratedSchemeSearchPoint scheme.x scheme.v i)))
        have hprox :=
          weighted_proximal_argmin_variational_inequality
            (scheme := scheme) (k := k) hk_lt hu
        have hprox' := add_le_add_right hprox stageConst
        have hqd :
            (scheme.smoothness : ℝ) * p.quadraticDistanceTo (scheme.v (k + 1)) u =
              ((scheme.smoothness : ℝ) / 2) *
                ‖u - scheme.v (k + 1)‖[scheme.metricMatrix] ^ (2 : ℕ) := by
          dsimp [p]
          ring
        rw [hqd]
        dsimp [p, stageConst] at hprox' ⊢
        simpa [estimateSequencePotential_succ_eq_proximalMinimand_add_constant,
          add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm]
          using hprox'
      -- Next prove the stage inequality that advances the weighted objective term from `x_k` to
      -- `x_{k+1}` while keeping the source estimate-sequence structure explicit.
      have hsearch_shift :
          ((k : ℝ) / 2) • (yk - scheme.x k) = scheme.v k - yk := by
        have haux :
            ((((k + 2 : ℕ) : ℝ) / 2) : ℝ) • yk -
                (((((k + 2 : ℕ) : ℝ) / 2) : ℝ) - 1) • scheme.x k =
              scheme.v k := by
          simpa [yk] using searchPoint_auxPoint_eq_v (scheme := scheme) k
        have hshift :
            scheme.v k - yk =
              (((((k + 2 : ℕ) : ℝ) / 2) : ℝ) - 1) • (yk - scheme.x k) := by
          calc
            scheme.v k - yk =
                (((((k + 2 : ℕ) : ℝ) / 2) : ℝ) • yk -
                    (((((k + 2 : ℕ) : ℝ) / 2) : ℝ) - 1) • scheme.x k) -
                  yk := by
                    rw [haux]
            _ = (((((k + 2 : ℕ) : ℝ) / 2) : ℝ) - 1) • (yk - scheme.x k) := by
                  module
        have hcoef :
            (((((k + 2 : ℕ) : ℝ) / 2) : ℝ) - 1) = (k : ℝ) / 2 := by
          have hcast : ((k + 2 : ℕ) : ℝ) = (k : ℝ) + 2 := by
            norm_num [Nat.cast_add]
          rw [hcast]
          ring
        rw [hshift, hcoef]
      have hAprev_inner :
          Aprev * inner ℝ (scheme.gradient yk) (yk - scheme.x k) =
            ak * inner ℝ (scheme.gradient yk) (scheme.v k - yk) := by
        calc
          Aprev * inner ℝ (scheme.gradient yk) (yk - scheme.x k)
              = ak * (((k : ℝ) / 2) * inner ℝ (scheme.gradient yk) (yk - scheme.x k)) := by
                  rw [hAprev_eq]
                  ring
          _ = ak * inner ℝ (scheme.gradient yk) (((k : ℝ) / 2) • (yk - scheme.x k)) := by
                rw [inner_smul_right]
          _ = ak * inner ℝ (scheme.gradient yk) (scheme.v k - yk) := by
                rw [hsearch_shift]
      have hgradWithin_yk :
          HasGradientWithinAt scheme.problem (scheme.gradient yk) scheme.problem.feasibleSet yk := by
        simpa [yk] using
          (scheme.gradient_hasGradientAt hyk_mem).hasFDerivAt.hasFDerivWithinAt.hasGradientWithinAt
      have htangent_xk :
          scheme.problem yk ≤
            scheme.problem (scheme.x k) + inner ℝ (scheme.gradient yk) (yk - scheme.x k) := by
        have hraw :=
          scheme.objective_convex.lower_tangent_plane_of_hasGradientWithinAt
            yk hyk_mem (scheme.gradient yk) hgradWithin_yk (scheme.x k) hxk_mem
        have hflip :
            inner ℝ (scheme.gradient yk) (scheme.x k - yk) =
              -inner ℝ (scheme.gradient yk) (yk - scheme.x k) := by
          rw [show scheme.x k - yk = -(yk - scheme.x k) by abel, inner_neg_right]
        rw [hflip] at hraw
        linarith
      have hAprev_yk :
          Aprev * scheme.problem yk ≤
            Aprev * scheme.problem (scheme.x k) +
              ak * inner ℝ (scheme.gradient yk) (scheme.v k - yk) := by
        have hscaled := mul_le_mul_of_nonneg_left htangent_xk hAprev_nonneg
        rw [mul_add] at hscaled
        rw [hAprev_inner] at hscaled
        simpa [add_assoc, add_left_comm, add_comm] using hscaled
      have hnorm_xsucc_sub :
          ‖scheme.x (k + 1) - yk‖[scheme.metricMatrix] =
            (2 / ((k : ℝ) + 2)) * ‖scheme.v (k + 1) - scheme.v k‖[scheme.metricMatrix] := by
        calc
          ‖scheme.x (k + 1) - yk‖[scheme.metricMatrix]
              = ‖(2 / ((k : ℝ) + 2)) • (scheme.v (k + 1) - scheme.v k)‖[scheme.metricMatrix] := by
                  rw [x_succ_sub_searchPoint_eq_smul_v_diff (scheme := scheme) hk_lt]
          _ = (2 / |(k : ℝ) + 2|) *
                ‖scheme.v (k + 1) - scheme.v k‖[scheme.metricMatrix] := by
                simpa using
                  (map_smul_eq_mul
                    (positiveDefMatrixNorm scheme.metricMatrix.1 scheme.metricMatrix.2)
                    (2 / ((k : ℝ) + 2))
                    (scheme.v (k + 1) - scheme.v k))
          _ = (2 / ((k : ℝ) + 2)) *
                ‖scheme.v (k + 1) - scheme.v k‖[scheme.metricMatrix] := by
                have hk2_pos : 0 < (k : ℝ) + 2 := by positivity
                rw [abs_of_pos hk2_pos]
      have hnorm_yk_sub :
          ‖yk - scheme.x (k + 1)‖[scheme.metricMatrix] =
            (2 / ((k : ℝ) + 2)) * ‖scheme.v (k + 1) - scheme.v k‖[scheme.metricMatrix] := by
        have hsym :
            ‖yk - scheme.x (k + 1)‖[scheme.metricMatrix] =
              ‖scheme.x (k + 1) - yk‖[scheme.metricMatrix] := by
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
            (map_neg_eq_map
              (positiveDefMatrixNorm scheme.metricMatrix.1 scheme.metricMatrix.2)
              (scheme.x (k + 1) - yk))
        rw [hsym, hnorm_xsucc_sub]
      have hAnext_inner :
          Anext * inner ℝ (scheme.gradient yk) (scheme.x (k + 1) - yk) =
            ak * inner ℝ (scheme.gradient yk) (scheme.v (k + 1) - scheme.v k) := by
        calc
          Anext * inner ℝ (scheme.gradient yk) (scheme.x (k + 1) - yk)
              = (Anext * (2 / ((k : ℝ) + 2))) *
                  inner ℝ (scheme.gradient yk) (scheme.v (k + 1) - scheme.v k) := by
                    rw [x_succ_sub_searchPoint_eq_smul_v_diff (scheme := scheme) hk_lt,
                      inner_smul_right]
                    ring
          _ = ak * inner ℝ (scheme.gradient yk) (scheme.v (k + 1) - scheme.v k) := by
                rw [hAnext_beta]
      have hquad_bound :
          Anext *
              (((scheme.smoothness : ℝ) / 2) *
                ‖yk - scheme.x (k + 1)‖[scheme.metricMatrix] ^ (2 : ℕ)) ≤
            (scheme.smoothness : ℝ) * p.quadraticDistanceTo (scheme.v k) (scheme.v (k + 1)) := by
        dsimp [p]
        rw [hnorm_yk_sub]
        have hterm_nonneg :
            0 ≤
              ((scheme.smoothness : ℝ) / 2) *
                ‖scheme.v (k + 1) - scheme.v k‖[scheme.metricMatrix] ^ (2 : ℕ) := by
          positivity
        have hmul :=
          mul_le_mul_of_nonneg_right hcoef_quad hterm_nonneg
        calc
          Anext *
              (((scheme.smoothness : ℝ) / 2) *
                ((2 / ((k : ℝ) + 2)) *
                  ‖scheme.v (k + 1) - scheme.v k‖[scheme.metricMatrix]) ^ (2 : ℕ))
              =
            (Anext * (2 / ((k : ℝ) + 2)) ^ (2 : ℕ)) *
              (((scheme.smoothness : ℝ) / 2) *
                ‖scheme.v (k + 1) - scheme.v k‖[scheme.metricMatrix] ^ (2 : ℕ)) := by
                  rw [pow_two]
                  ring
          _ ≤
              1 *
                (((scheme.smoothness : ℝ) / 2) *
                  ‖scheme.v (k + 1) - scheme.v k‖[scheme.metricMatrix] ^ (2 : ℕ)) := hmul
          _ = (scheme.smoothness : ℝ) * (1 / 2 *
                ‖scheme.v (k + 1) - scheme.v k‖[scheme.metricMatrix] ^ (2 : ℕ)) := by
                  ring
      have hsmooth_upper :=
        weighted_smooth_upper_model_on_feasible
          (scheme := scheme) (x := yk) (y := scheme.x (k + 1))
          hgradient_lipschitz hyk_mem hxsucc_mem
      have hsmooth_scaled :
          Anext * scheme.problem (scheme.x (k + 1)) ≤
            Anext * scheme.problem yk +
              ak * inner ℝ (scheme.gradient yk) (scheme.v (k + 1) - scheme.v k) +
              (scheme.smoothness : ℝ) * p.quadraticDistanceTo (scheme.v k) (scheme.v (k + 1)) := by
        have hscaled := mul_le_mul_of_nonneg_left hsmooth_upper hAnext_nonneg
        calc
          Anext * scheme.problem (scheme.x (k + 1))
              ≤
                Anext *
                  (scheme.problem yk +
                    inner ℝ (scheme.gradient yk) (scheme.x (k + 1) - yk) +
                    ((scheme.smoothness : ℝ) / 2) *
                      ‖yk - scheme.x (k + 1)‖[scheme.metricMatrix] ^ (2 : ℕ)) := by
                        simpa [mul_add, add_assoc, add_left_comm, add_comm] using hscaled
          _ =
              Anext * scheme.problem yk +
                Anext * inner ℝ (scheme.gradient yk) (scheme.x (k + 1) - yk) +
                Anext *
                  (((scheme.smoothness : ℝ) / 2) *
                    ‖yk - scheme.x (k + 1)‖[scheme.metricMatrix] ^ (2 : ℕ)) := by
                      ring
          _ ≤
              Anext * scheme.problem yk +
                ak * inner ℝ (scheme.gradient yk) (scheme.v (k + 1) - scheme.v k) +
                (scheme.smoothness : ℝ) * p.quadraticDistanceTo (scheme.v k) (scheme.v (k + 1)) := by
                      rw [hAnext_inner]
                      nlinarith [hquad_bound]
      have hinner_merge :
          ak * inner ℝ (scheme.gradient yk) (scheme.v k - yk) +
              ak * inner ℝ (scheme.gradient yk) (scheme.v (k + 1) - scheme.v k) =
            ak * inner ℝ (scheme.gradient yk) (scheme.v (k + 1) - yk) := by
        calc
          ak * inner ℝ (scheme.gradient yk) (scheme.v k - yk) +
              ak * inner ℝ (scheme.gradient yk) (scheme.v (k + 1) - scheme.v k)
              =
            ak *
              (inner ℝ (scheme.gradient yk) (scheme.v k - yk) +
                inner ℝ (scheme.gradient yk) (scheme.v (k + 1) - scheme.v k)) := by
                  ring
          _ =
              ak * inner ℝ (scheme.gradient yk)
                ((scheme.v k - yk) + (scheme.v (k + 1) - scheme.v k)) := by
                  rw [← inner_add_right]
          _ = ak * inner ℝ (scheme.gradient yk) (scheme.v (k + 1) - yk) := by
                congr 2
                abel
      have hstage :
          Anext * scheme.problem (scheme.x (k + 1)) ≤
            Aprev * scheme.problem (scheme.x k) +
              ak * (scheme.problem yk +
                inner ℝ (scheme.gradient yk) (scheme.v (k + 1) - yk)) +
              (scheme.smoothness : ℝ) * p.quadraticDistanceTo (scheme.v k) (scheme.v (k + 1)) := by
        have hAnext_yk :
            Anext * scheme.problem yk ≤
              Aprev * scheme.problem (scheme.x k) +
                ak * inner ℝ (scheme.gradient yk) (scheme.v k - yk) +
                ak * scheme.problem yk := by
          rw [hAnext_eq, add_mul]
          simpa [add_assoc, add_left_comm, add_comm] using
            add_le_add_right hAprev_yk (ak * scheme.problem yk)
        have hcombine :
            Anext * scheme.problem yk +
                (ak * inner ℝ (scheme.gradient yk) (scheme.v (k + 1) - scheme.v k) +
                  (scheme.smoothness : ℝ) * p.quadraticDistanceTo (scheme.v k) (scheme.v (k + 1))) ≤
              (Aprev * scheme.problem (scheme.x k) +
                ak * inner ℝ (scheme.gradient yk) (scheme.v k - yk) +
                ak * scheme.problem yk) +
              (ak * inner ℝ (scheme.gradient yk) (scheme.v (k + 1) - scheme.v k) +
                (scheme.smoothness : ℝ) * p.quadraticDistanceTo (scheme.v k) (scheme.v (k + 1))) := by
          exact add_le_add hAnext_yk le_rfl
        calc
          Anext * scheme.problem (scheme.x (k + 1))
              ≤
                Anext * scheme.problem yk +
                  (ak * inner ℝ (scheme.gradient yk) (scheme.v (k + 1) - scheme.v k) +
                    (scheme.smoothness : ℝ) * p.quadraticDistanceTo
                      (scheme.v k)
                      (scheme.v (k + 1))) := by
                        simpa [add_assoc] using hsmooth_scaled
          _ ≤
              (Aprev * scheme.problem (scheme.x k) +
                ak * inner ℝ (scheme.gradient yk) (scheme.v k - yk) +
                ak * scheme.problem yk) +
              (ak * inner ℝ (scheme.gradient yk) (scheme.v (k + 1) - scheme.v k) +
                (scheme.smoothness : ℝ) * p.quadraticDistanceTo
                  (scheme.v k)
                  (scheme.v (k + 1))) := hcombine
          _ =
              Aprev * scheme.problem (scheme.x k) +
                ak * (scheme.problem yk +
                  inner ℝ (scheme.gradient yk) (scheme.v (k + 1) - yk)) +
                (scheme.smoothness : ℝ) * p.quadraticDistanceTo
                  (scheme.v k)
                  (scheme.v (k + 1)) := by
                    calc
                      (Aprev * scheme.problem (scheme.x k) +
                          ak * inner ℝ (scheme.gradient yk) (scheme.v k - yk) +
                          ak * scheme.problem yk) +
                        (ak * inner ℝ (scheme.gradient yk) (scheme.v (k + 1) - scheme.v k) +
                          (scheme.smoothness : ℝ) * p.quadraticDistanceTo
                            (scheme.v k)
                            (scheme.v (k + 1))) =
                          Aprev * scheme.problem (scheme.x k) +
                            (ak * inner ℝ (scheme.gradient yk) (scheme.v k - yk) +
                              ak * inner ℝ (scheme.gradient yk) (scheme.v (k + 1) - scheme.v k)) +
                            ak * scheme.problem yk +
                            (scheme.smoothness : ℝ) * p.quadraticDistanceTo
                              (scheme.v k)
                              (scheme.v (k + 1)) := by
                                ring
                      _ =
                          Aprev * scheme.problem (scheme.x k) +
                            ak * inner ℝ (scheme.gradient yk) (scheme.v (k + 1) - yk) +
                            ak * scheme.problem yk +
                            (scheme.smoothness : ℝ) * p.quadraticDistanceTo
                              (scheme.v k)
                              (scheme.v (k + 1)) := by
                                rw [hinner_merge]
                      _ =
                          Aprev * scheme.problem (scheme.x k) +
                            ak * (scheme.problem yk +
                              inner ℝ (scheme.gradient yk) (scheme.v (k + 1) - yk)) +
                            (scheme.smoothness : ℝ) * p.quadraticDistanceTo
                              (scheme.v k)
                              (scheme.v (k + 1)) := by
                                ring
      -- Now evaluate the induction hypothesis at `u = v_{k+1}` and absorb the new stage term into
      -- the definition of `Ψ_{k+1}(v_{k+1})`.
      have hih_vsucc :=
        ih (u := scheme.v (k + 1)) hk_le hvsucc_mem
      have hPsi_succ_vsucc :
          estimateSequencePotential scheme (k + 1) (scheme.v (k + 1)) =
            estimateSequencePotential scheme k (scheme.v (k + 1)) +
              ak * (scheme.problem yk +
                inner ℝ (scheme.gradient yk) (scheme.v (k + 1) - yk)) := by
        dsimp [yk, ak]
        rw [estimateSequencePotential, estimateSequencePotential, Finset.sum_range_succ]
        ring
      have hih_step :
          Aprev * scheme.problem (scheme.x k) +
              ak * (scheme.problem yk +
                inner ℝ (scheme.gradient yk) (scheme.v (k + 1) - yk)) +
              (scheme.smoothness : ℝ) * p.quadraticDistanceTo (scheme.v k) (scheme.v (k + 1)) ≤
            estimateSequencePotential scheme (k + 1) (scheme.v (k + 1)) := by
        have hadded :=
          add_le_add_right hih_vsucc
            (ak * (scheme.problem yk +
              inner ℝ (scheme.gradient yk) (scheme.v (k + 1) - yk)))
        have hadded' :
            (Aprev * scheme.problem (scheme.x k) +
                (scheme.smoothness : ℝ) * p.quadraticDistanceTo (scheme.v k) (scheme.v (k + 1))) +
              ak * (scheme.problem yk +
                inner ℝ (scheme.gradient yk) (scheme.v (k + 1) - yk)) ≤
            estimateSequencePotential scheme k (scheme.v (k + 1)) +
              ak * (scheme.problem yk +
                inner ℝ (scheme.gradient yk) (scheme.v (k + 1) - yk)) := by
          simpa [add_assoc, add_left_comm, add_comm] using hadded
        calc
          Aprev * scheme.problem (scheme.x k) +
              ak * (scheme.problem yk +
                inner ℝ (scheme.gradient yk) (scheme.v (k + 1) - yk)) +
              (scheme.smoothness : ℝ) * p.quadraticDistanceTo (scheme.v k) (scheme.v (k + 1))
              =
            (Aprev * scheme.problem (scheme.x k) +
                (scheme.smoothness : ℝ) * p.quadraticDistanceTo (scheme.v k) (scheme.v (k + 1))) +
              ak * (scheme.problem yk +
                inner ℝ (scheme.gradient yk) (scheme.v (k + 1) - yk)) := by
                  ring
          _ ≤ estimateSequencePotential scheme k (scheme.v (k + 1)) +
              ak * (scheme.problem yk +
                inner ℝ (scheme.gradient yk) (scheme.v (k + 1) - yk)) := hadded'
          _ = estimateSequencePotential scheme (k + 1) (scheme.v (k + 1)) := by
                rw [hPsi_succ_vsucc]
      have hvsucc_bound :
          Anext * scheme.problem (scheme.x (k + 1)) ≤
            estimateSequencePotential scheme (k + 1) (scheme.v (k + 1)) := by
        exact hstage.trans hih_step
      -- Finally combine the stage inequality with the proximal lift from `v_{k+1}` to `u`.
      have hfinal :=
        add_le_add_right hvsucc_bound
          ((scheme.smoothness : ℝ) * p.quadraticDistanceTo (scheme.v (k + 1)) u)
      have hfinal' :
          Anext * scheme.problem (scheme.x (k + 1)) +
              (scheme.smoothness : ℝ) * p.quadraticDistanceTo (scheme.v (k + 1)) u ≤
            estimateSequencePotential scheme (k + 1) (scheme.v (k + 1)) +
              (scheme.smoothness : ℝ) * p.quadraticDistanceTo (scheme.v (k + 1)) u := by
        simpa [add_assoc, add_left_comm, add_comm] using hfinal
      have hresult := hfinal'.trans hpotential_lift
      dsimp [Anext, p] at hresult ⊢
      exact hresult

/-- Proposition 7.16: if `scheme` is the accelerated projected-gradient run
`S(φ, L, Q, G, x₀, N)` with positive horizon `N ≥ 1`, and the chosen gradient field is
`L`-Lipschitz with respect to the weighted norm `‖·‖[G]` and dual norm `‖·‖[G,*]` on the
feasible set, then the output point `scheme.outputPoint = x_N` satisfies
`φ(x_N) - φ(xStar) ≤ 2 L ‖x₀ - xStar‖[G]^2 / (N (N + 1))` for every minimizer `xStar` of `φ` on
`Q`. -/
theorem outputPoint_suboptimality_le
    {N : ℕ} (scheme : AcceleratedConvexMinimizationScheme n N)
    (hN : 1 ≤ N)
    (hgradient_lipschitz :
      ∀ ⦃x y : E⦄,
        x ∈ scheme.problem.feasibleSet →
        y ∈ scheme.problem.feasibleSet →
          ‖scheme.gradient x - scheme.gradient y‖[scheme.metricMatrix,*] ≤
            (scheme.smoothness : ℝ) * ‖x - y‖[scheme.metricMatrix])
    {xStar : E} (hxStar : xStar ∈ argmin[scheme.problem.feasibleSet] scheme.problem) :
    scheme.problem scheme.outputPoint - scheme.problem xStar ≤
      (2 * (scheme.smoothness : ℝ) * ‖scheme.initialPoint - xStar‖[scheme.metricMatrix] ^ (2 : ℕ)) /
        ((N : ℝ) * ((N : ℝ) + 1)) := by
  -- Rewrite the output owner to the final iterate so the estimate-sequence bounds apply directly.
  rw [scheme.outputPoint_eq]
  have hvN_mem : scheme.v N ∈ scheme.problem.feasibleSet :=
    (iterates_and_searchPoint_mem_feasible (scheme := scheme) (k := N) le_rfl).2.1
  have hlower :=
    estimateSequencePotential_lower_bound
      (scheme := scheme) (k := N) le_rfl (u := scheme.v N) hgradient_lipschitz hvN_mem
  have hupper :=
    estimate_sequence_at_constrained_minimizer_le (scheme := scheme) hN hxStar
  have hquad_self :
      (scheme.smoothness : ℝ) *
          (positiveDefMatrixNorm scheme.metricMatrix.1 scheme.metricMatrix.2).quadraticDistanceTo
            (scheme.v N)
            (scheme.v N) =
        0 := by
    rw [positiveDefMatrixNorm_quadraticDistanceTo_apply]
    simp
  have hlower' :
      Finset.sum (Finset.range N) (fun i ↦ ((((i : ℝ) + 1) / 2) : ℝ)) *
          scheme.problem (scheme.x N) ≤
        estimateSequencePotential scheme N (scheme.v N) := by
    simpa [hquad_self] using hlower
  let A : ℝ := Finset.sum (Finset.range N) (fun i ↦ ((((i : ℝ) + 1) / 2) : ℝ))
  let D : ℝ :=
    (positiveDefMatrixNorm scheme.metricMatrix.1 scheme.metricMatrix.2).quadraticDistanceTo
      scheme.initialPoint
      xStar
  have hAeq : A = (N : ℝ) * ((N : ℝ) + 1) / 4 := by
    simp [A, estimate_weight_sum_eq]
  have hDeq : D = (1 / 2 : ℝ) * ‖scheme.initialPoint - xStar‖[scheme.metricMatrix] ^ (2 : ℕ) := by
    rw [show D =
      (positiveDefMatrixNorm scheme.metricMatrix.1 scheme.metricMatrix.2).quadraticDistanceTo
        scheme.initialPoint xStar by rfl]
    rw [positiveDefMatrixNorm_quadraticDistanceTo_apply]
    have hnorm_eq :
        ‖xStar - scheme.initialPoint‖[scheme.metricMatrix] =
          ‖scheme.initialPoint - xStar‖[scheme.metricMatrix] := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        (map_neg_eq_map
          (positiveDefMatrixNorm scheme.metricMatrix.1 scheme.metricMatrix.2)
          (scheme.initialPoint - xStar))
    rw [hnorm_eq]
  have hweighted_gap :
      A * (scheme.problem (scheme.x N) - scheme.problem xStar) ≤
        (scheme.smoothness : ℝ) * D := by
    have hchain :
        A * scheme.problem (scheme.x N) ≤
          A * scheme.problem xStar + (scheme.smoothness : ℝ) * D := by
      exact hlower'.trans hupper
    dsimp [A, D] at hchain
    nlinarith
  have hN_real_pos : 0 < (N : ℝ) := by
    exact_mod_cast Nat.succ_le_iff.mp hN
  have hden_pos : 0 < (N : ℝ) * ((N : ℝ) + 1) := by
    positivity
  rw [hAeq, hDeq] at hweighted_gap
  refine (le_div_iff₀ hden_pos).2 ?_
  nlinarith

end AcceleratedConvexMinimizationScheme

end
