/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import Mathlib.Analysis.InnerProductSpace.Positive
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_16
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_62

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {m : ℕ}

variable (a : Fin m → E) (b : Fin m → ℝ)

/- Definition 3.63 lies in the chapter's bounded-polyhedron / analytic-barrier / Hessian
log-determinant domain.

Sampled owner declarations used here:
* `analyticBarrierDomain`, `AnalyticBarrierPoint`, `analyticBarrierAmbient`, and
  `analyticBarrierDomain_eq_interior_innerLePolyhedron` from `Definition_3_62`, which keep the
  Chapter 3 strict-slack owner and the explicit interior bridge separate;
* `Bornology.IsBounded`, the ambient owner predicate for bounded subsets;
* `hessian` from `Chap01/Definition_1_4_16`, the intrinsic Hessian owner;
* `IsMinOn`, the canonical owner predicate for minimizers.

Best owner abstraction:
* source-facing: the volumetric barrier on `AnalyticBarrierPoint a b`, together with its
  bounded-polyhedron positivity theorem and the minimizer condition
  `IsMinOn (volumetricBarrier a b) Set.univ y`;
* core/canonical: `analyticBarrierDomain a b`, `analyticBarrierAmbient a b`, `hessian`, and
  `IsMinOn`;
* bridge/view: `volumetricBarrierAmbient a b` on `E`, plus the explicit transport theorem to
  `interior (innerLePolyhedron a b)` under the hypothesis that the chosen presentation recovers
  that intrinsic interior.

Primitive data:
* the affine half-space presentation `a`, `b`.

Derived API:
* the ambient bridge formula `volumetricBarrierAmbient a b`;
* the strict-domain volumetric barrier `volumetricBarrier a b`;
* the source-facing positivity theorem `volumetricBarrier_hessian_det_pos`;
* the strict-domain ambient minimizer bridge `isMinOn_volumetricBarrier_iff`;
* the interior bridge `isMinOn_volumetricBarrier_iff_interior`.

The Chapter 3 owner API in `Definition_3_62` keeps the analytic barrier on the strict positive-
slack domain and treats the intrinsic interior only through an explicit bridge hypothesis. This
file follows that owner split: the source-facing volumetric barrier lives on
`AnalyticBarrierPoint a b`, while the interior formulation is recovered only under the same
explicit bridge assumption.
-/

section

variable [FiniteDimensional ℝ E]

/-- The ambient formula `x ↦ log det ∇²F(x)` for the analytic barrier
`F = analyticBarrierAmbient a b`. It is only a bridge view; the source-facing owner is
`volumetricBarrier a b` on `AnalyticBarrierPoint a b`. -/
def volumetricBarrierAmbient :
    E → ℝ :=
  fun x ↦ Real.log ((hessian (analyticBarrierAmbient a b) x).det)

/-- Evaluating the ambient volumetric-barrier formula gives the textbook expression
`log det ∇²F(x)` for `F = analyticBarrierAmbient a b`. -/
@[simp] theorem volumetricBarrierAmbient_apply (x : E) :
    volumetricBarrierAmbient a b x =
      Real.log ((hessian (analyticBarrierAmbient a b) x).det) :=
  rfl

/-- The volumetric barrier attached to `analyticBarrier a b` is the restriction of
`volumetricBarrierAmbient a b` to the strict barrier domain `AnalyticBarrierPoint a b`. The
interior formulation is a separate bridge consequence, not the primitive owner. -/
def volumetricBarrier :
    AnalyticBarrierPoint a b → ℝ :=
  fun x ↦ volumetricBarrierAmbient a b x

/- For a bounded polyhedron, every strict-slack point has positive Hessian determinant for the
ambient analytic barrier, so the logarithm in `volumetricBarrier a b` is mathematically faithful
on its source-facing domain. -/
/-- Helper for Definition 3.63: the Riesz isomorphism sends the inner-product functional
`innerSL ℝ z` back to the representing vector `z`. -/
private theorem toDual_symm_innerSL_eq (z : E) :
    (InnerProductSpace.toDual ℝ E).symm ((innerSL ℝ) z) = z := by
  -- Check the Riesz representative against every test vector through the inner product.
  apply ext_inner_right ℝ
  intro y
  simp [InnerProductSpace.toDual_symm_apply]

/-- Helper for Definition 3.63: a single logarithmic-barrier term has gradient equal to the
corresponding normal divided by its slack. -/
private theorem analyticBarrierAmbient_term_hasGradientAt
    (j : Fin m) (x : E) (hx : inner ℝ (a j) x < b j) :
    HasGradientAt
      (fun y : E ↦ -Real.log (b j - inner ℝ (a j) y))
      ((1 / (b j - inner ℝ (a j) x)) • a j)
      x := by
  -- Differentiate the affine slack map before applying the logarithm.
  have hslack :
      HasFDerivAt
        (fun y : E ↦ b j - inner ℝ (a j) y)
        (-(innerSL ℝ (a j)))
        x := by
    simpa using (hasFDerivAt_const (x := x) (c := b j)).sub (innerSL ℝ (a j)).hasFDerivAt
  have hlog :
      HasFDerivAt
        (fun y : E ↦ Real.log (b j - inner ℝ (a j) y))
        (((b j - inner ℝ (a j) x)⁻¹ : ℝ) • (-(innerSL ℝ (a j))))
        x := by
    have hslack_ne : b j - inner ℝ (a j) x ≠ 0 := (sub_pos.mpr hx).ne'
    simpa [Function.comp] using (Real.hasDerivAt_log hslack_ne).comp_hasFDerivAt x hslack
  -- Negating the logarithm flips the Fréchet derivative sign and produces the positive gradient.
  rw [hasGradientAt_iff_hasFDerivAt]
  simpa [one_div, smul_smul, mul_assoc, mul_left_comm, mul_comm, toDual_symm_innerSL_eq] using
    hlog.neg

/-- Helper for Definition 3.63: the ambient analytic barrier is the finite sum of its individual
negative logarithmic slack functions. -/
private theorem analyticBarrierAmbient_eq_sum_neg_log :
    analyticBarrierAmbient a b =
      ∑ j : Fin m, fun y : E ↦ -Real.log (b j - inner ℝ (a j) y) := by
  have hs :
      (@Finset.univ (Fin m) (Fintype.ofFinite (Fin m))) =
        (@Finset.univ (Fin m) (Fin.fintype m)) := by
    simpa using congrArg (fun I : Fintype (Fin m) => @Fintype.elems (Fin m) I)
      (Subsingleton.elim (Fintype.ofFinite (Fin m)) (Fin.fintype m))
  -- Rewrite the owner definition `-(∑ log ...)` into the literal sum form needed for
  -- finite-sum differentiation.
  funext y
  rw [analyticBarrierAmbient, ← Finset.sum_neg_distrib]
  rw [hs]
  simp

/-- Helper for Definition 3.63: the Riesz map carries the sum of reciprocal-slack normals to the
sum of the corresponding dual functionals. -/
private theorem toDual_sum_reciprocal_normals
    (x : AnalyticBarrierPoint a b) :
    (InnerProductSpace.toDual ℝ E) (∑ j : Fin m, (1 / (b j - inner ℝ (a j) x)) • a j) =
      ∑ j : Fin m, InnerProductSpace.toDual ℝ E ((1 / (b j - inner ℝ (a j) x)) • a j) := by
  -- Compare both dual maps on an arbitrary test vector and use linearity of the inner product.
  apply ContinuousLinearMap.ext
  intro u
  simp [InnerProductSpace.toDual_apply_apply]

/-- Helper for Definition 3.63: at a strict-slack point, the ambient analytic barrier has the
Fréchet derivative given by the sum of the reciprocal-slack normal functionals. -/
private theorem analyticBarrierAmbient_hasFDerivAt_strict_point
    (x : AnalyticBarrierPoint a b) :
    HasFDerivAt
      (analyticBarrierAmbient a b)
      ((InnerProductSpace.toDual ℝ E)
        (∑ j : Fin m, (1 / (b j - inner ℝ (a j) x)) • a j))
      x := by
  have hx : ∀ j : Fin m, inner ℝ (a j) x < b j := by
    simpa using (mem_analyticBarrierDomain_iff a b).mp x.property
  have hterms :
      ∀ j ∈ (Finset.univ : Finset (Fin m)),
        HasFDerivAt
          (fun y : E ↦ -Real.log (b j - inner ℝ (a j) y))
          (InnerProductSpace.toDual ℝ E ((1 / (b j - inner ℝ (a j) x)) • a j))
          x := by
    intro j hj
    simpa using
      (analyticBarrierAmbient_term_hasGradientAt (a := a) (b := b) j (x : E) (hx j)).hasFDerivAt
  -- Differentiate the exact finite-sum presentation term-by-term and rewrite the summed dual map
  -- back through the Riesz image of the summed gradient vector.
  rw [analyticBarrierAmbient_eq_sum_neg_log (a := a) (b := b)]
  simpa [toDual_sum_reciprocal_normals (a := a) (b := b) x] using HasFDerivAt.sum hterms

/-- Helper for Definition 3.63: at a strict-slack point, the analytic-barrier gradient is the sum
of reciprocal-slack normals. -/
private theorem analyticBarrierAmbient_hasGradientAt
    (x : AnalyticBarrierPoint a b) :
    HasGradientAt
      (analyticBarrierAmbient a b)
      (∑ j : Fin m, (1 / (b j - inner ℝ (a j) x)) • a j)
      x := by
  -- Route correction: assemble the Fréchet derivative in the literal sum form first, then
  -- convert back to a gradient through the Riesz isomorphism.
  rw [hasGradientAt_iff_hasFDerivAt]
  simpa using analyticBarrierAmbient_hasFDerivAt_strict_point (a := a) (b := b) x

/-- Helper for Definition 3.63: differentiating the reciprocal-slack normal field produces the
positive rank-one Hessian summands. -/
private theorem analyticBarrierAmbient_gradient_hasFDerivAt
    (x : AnalyticBarrierPoint a b) :
    HasFDerivAt
      (fun y : E ↦ ∑ j : Fin m, (1 / (b j - inner ℝ (a j) y)) • a j)
      (∑ j : Fin m,
        (1 / (b j - inner ℝ (a j) x) ^ (2 : ℕ)) • InnerProductSpace.rankOne ℝ (a j) (a j))
      x := by
  have hx : ∀ j : Fin m, inner ℝ (a j) x < b j := by
    simpa using (mem_analyticBarrierDomain_iff a b).mp x.property
  -- Differentiate each reciprocal-slack vector term separately.
  have hterms :
      ∀ j ∈ (Finset.univ : Finset (Fin m)),
        HasFDerivAt
          (fun y : E ↦ (1 / (b j - inner ℝ (a j) y)) • a j)
          ((1 / (b j - inner ℝ (a j) x) ^ (2 : ℕ)) • InnerProductSpace.rankOne ℝ (a j) (a j))
          x := by
    intro j hj
    have hslack :
        HasFDerivAt
          (fun y : E ↦ b j - inner ℝ (a j) y)
          (-(innerSL ℝ (a j)))
          (x : E) := by
      simpa using (hasFDerivAt_const (x := (x : E)) (c := b j)).sub (innerSL ℝ (a j)).hasFDerivAt
    have hinv :
        HasFDerivAt
          (fun y : E ↦ 1 / (b j - inner ℝ (a j) y))
          (((1 / (b j - inner ℝ (a j) x) ^ (2 : ℕ)) : ℝ) • (innerSL ℝ (a j)))
          (x : E) := by
      have hslack_ne : b j - inner ℝ (a j) x ≠ 0 := (sub_pos.mpr (hx j)).ne'
      convert (hasFDerivAt_inv hslack_ne).comp (x : E) hslack using 1
      · funext y
        simp [one_div]
      · ext u
        simp [one_div, div_eq_mul_inv, smul_smul, pow_two, mul_assoc, mul_left_comm, mul_comm]
    -- The derivative of a scalar field times a fixed vector is the corresponding rank-one map.
    convert hinv.smul_const (a j) using 1
    ext u
    simp [InnerProductSpace.rankOne_def, ContinuousLinearMap.smulRight_apply, smul_smul,
      mul_assoc, mul_left_comm, mul_comm]
  convert HasFDerivAt.sum hterms using 1
  · funext y
    simp

/-- Helper for Definition 3.63: the analytic-barrier Hessian is the sum of positive rank-one
operators associated with the defining normals. -/
private theorem analyticBarrierAmbient_hessian_eq_sum_rankOne
    (x : AnalyticBarrierPoint a b) :
    hessian (analyticBarrierAmbient a b) x =
      ∑ j : Fin m,
        (1 / (b j - inner ℝ (a j) x) ^ (2 : ℕ)) • InnerProductSpace.rankOne ℝ (a j) (a j) := by
  have hpos :
      {y : E | ∀ j : Fin m, inner ℝ (a j) y < b j} ∈ nhds (x : E) := by
    have hopen : IsOpen {y : E | ∀ j : Fin m, inner ℝ (a j) y < b j} := by
      simpa [Set.setOf_forall] using
        isOpen_iInter_of_finite fun j : Fin m ↦
          isOpen_lt (innerSL ℝ (a j)).continuous continuous_const
    have hx_mem : (x : E) ∈ {y : E | ∀ j : Fin m, inner ℝ (a j) y < b j} := by
      simpa using (mem_analyticBarrierDomain_iff a b).mp x.property
    exact hopen.mem_nhds hx_mem
  let Gf : E → E := gradient (analyticBarrierAmbient a b)
  have hEq : Filter.EventuallyEq (nhds (x : E)) Gf
      (fun y : E ↦ ∑ j : Fin m, (1 / (b j - inner ℝ (a j) y)) • a j) := by
    filter_upwards [hpos] with y hy
    change Gf y = ∑ j : Fin m, (1 / (b j - inner ℝ (a j) y)) • a j
    exact (analyticBarrierAmbient_hasGradientAt (a := a) (b := b) ⟨y, (mem_analyticBarrierDomain_iff a b).2 hy⟩).gradient
  -- The Hessian is the derivative of the gradient, so the neighborhood gradient formula
  -- differentiates directly to the rank-one sum.
  change fderiv ℝ (gradient (analyticBarrierAmbient a b)) (x : E) =
      ∑ j : Fin m,
        (1 / (b j - inner ℝ (a j) x) ^ (2 : ℕ)) • InnerProductSpace.rankOne ℝ (a j) (a j)
  simpa [Gf] using
    (analyticBarrierAmbient_gradient_hasFDerivAt (a := a) (b := b) x).congr_of_eventuallyEq hEq |>.fderiv

/-- Helper for Definition 3.63: the analytic-barrier Hessian quadratic form is the sum of squared
constraint projections scaled by reciprocal squared slacks. -/
private theorem analyticBarrierAmbient_hessian_quadratic_form
    (x : AnalyticBarrierPoint a b) (u : E) :
    inner ℝ (hessian (analyticBarrierAmbient a b) x u) u =
      ∑ j : Fin m, ((inner ℝ (a j) u) ^ (2 : ℕ)) / (b j - inner ℝ (a j) x) ^ (2 : ℕ) := by
  have hx : ∀ j : Fin m, inner ℝ (a j) x < b j := by
    simpa using (mem_analyticBarrierDomain_iff a b).mp x.property
  -- Expand the Hessian operator and evaluate each rank-one contribution on the test direction.
  rw [analyticBarrierAmbient_hessian_eq_sum_rankOne (a := a) (b := b) x]
  calc
    inner ℝ
        ((∑ j : Fin m,
            (1 / (b j - inner ℝ (a j) x) ^ (2 : ℕ)) • InnerProductSpace.rankOne ℝ (a j) (a j)) u)
        u
        = ∑ j : Fin m,
            inner ℝ
              ((1 / (b j - inner ℝ (a j) x) ^ (2 : ℕ)) • InnerProductSpace.rankOne ℝ (a j) (a j) u)
              u := by
              rw [show
                ((∑ j : Fin m,
                    (1 / (b j - inner ℝ (a j) x) ^ (2 : ℕ)) • InnerProductSpace.rankOne ℝ (a j) (a j)) u)
                  = ∑ j : Fin m,
                      ((1 / (b j - inner ℝ (a j) x) ^ (2 : ℕ)) • InnerProductSpace.rankOne ℝ (a j) (a j)) u by
                  simp]
              rw [sum_inner]
              rfl
    _ = ∑ j : Fin m, ((inner ℝ (a j) u) ^ (2 : ℕ)) / (b j - inner ℝ (a j) x) ^ (2 : ℕ) := by
          apply Finset.sum_congr rfl
          intro j hj
          calc
            inner ℝ
                ((1 / (b j - inner ℝ (a j) x) ^ (2 : ℕ)) • InnerProductSpace.rankOne ℝ (a j) (a j) u)
                u
                = inner ℝ
                    ((1 / (b j - inner ℝ (a j) x) ^ (2 : ℕ)) • (inner ℝ (a j) u • a j))
                    u := by
                      rw [InnerProductSpace.rankOne_apply]
            _ = ((1 / (b j - inner ℝ (a j) x) ^ (2 : ℕ)) * inner ℝ (a j) u) * inner ℝ (a j) u := by
                  simp [inner_smul_left, inner_smul_right, mul_assoc]
            _ = ((inner ℝ (a j) u) ^ (2 : ℕ)) / (b j - inner ℝ (a j) x) ^ (2 : ℕ) := by
                  field_simp [(sub_pos.mpr (hx j)).ne']

/-- Helper for Definition 3.63: the analytic-barrier Hessian is a positive operator at every
strict-slack point. -/
private theorem analyticBarrierAmbient_hessian_isPositive
    (x : AnalyticBarrierPoint a b) :
    (hessian (analyticBarrierAmbient a b) x).IsPositive := by
  -- Rewrite the Hessian as a finite sum of nonnegative multiples of positive rank-one maps.
  rw [analyticBarrierAmbient_hessian_eq_sum_rankOne (a := a) (b := b) x]
  refine ContinuousLinearMap.isPositive_sum (s := Finset.univ) ?_
  intro j hj
  have hxj : inner ℝ (a j) x < b j := by
    simpa using (mem_analyticBarrierDomain_iff a b).mp x.property j
  exact (InnerProductSpace.isPositive_rankOne_self (𝕜 := ℝ) (a j)).smul_of_nonneg <| by
    positivity

/-- Helper for Definition 3.63: the Hessian quadratic form vanishes exactly on vectors
orthogonal to every defining normal. -/
private theorem analyticBarrierAmbient_hessian_zero_iff
    (x : AnalyticBarrierPoint a b) (u : E) :
    inner ℝ (hessian (analyticBarrierAmbient a b) x u) u = 0 ↔
      ∀ j : Fin m, inner ℝ (a j) u = 0 := by
  have hx : ∀ j : Fin m, inner ℝ (a j) x < b j := by
    simpa using (mem_analyticBarrierDomain_iff a b).mp x.property
  rw [analyticBarrierAmbient_hessian_quadratic_form (a := a) (b := b) x u]
  constructor
  · intro hsum j
    have hnonneg :
        ∀ i ∈ (Finset.univ : Finset (Fin m)),
          0 ≤ ((inner ℝ (a i) u) ^ (2 : ℕ)) / (b i - inner ℝ (a i) x) ^ (2 : ℕ) := by
      intro i hi
      positivity
    have hterm_zero :
        ((inner ℝ (a j) u) ^ (2 : ℕ)) / (b j - inner ℝ (a j) x) ^ (2 : ℕ) = 0 := by
      exact (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum j (Finset.mem_univ j)
    have hnum_zero : (inner ℝ (a j) u) ^ (2 : ℕ) = 0 := by
      have hden_ne : (b j - inner ℝ (a j) x) ^ (2 : ℕ) ≠ 0 := by
        exact pow_ne_zero 2 (sub_pos.mpr (hx j)).ne'
      rw [div_eq_zero_iff] at hterm_zero
      exact hterm_zero.elim id (fun hden => False.elim (hden_ne hden))
    nlinarith
  · intro hu
    -- Once every projected component is zero, every Hessian summand vanishes termwise.
    calc
      ∑ j : Fin m, ((inner ℝ (a j) u) ^ (2 : ℕ)) / (b j - inner ℝ (a j) x) ^ (2 : ℕ)
          = ∑ j : Fin m, 0 := by
              apply Finset.sum_congr rfl
              intro j hj
              simp [hu j]
      _ = 0 := by simp

/-- Helper for Definition 3.63: boundedness rules out a nonzero vector orthogonal to every
constraint normal, because such a vector would generate an unbounded affine line in the
polyhedron. -/
private theorem orthogonal_to_constraints_eq_zero_of_bounded
    (hQ_bounded : Bornology.IsBounded (innerLePolyhedron a b))
    (x : AnalyticBarrierPoint a b) {u : E}
    (hu : ∀ j : Fin m, inner ℝ (a j) u = 0) :
    u = 0 := by
  by_contra hu_ne
  obtain ⟨R, hR⟩ := hQ_bounded.exists_norm_le
  let t : ℝ := (R + ‖(x : E)‖ + 1) / ‖u‖
  have hu_norm_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu_ne
  have hx_mem : (x : E) ∈ innerLePolyhedron a b := by
    rw [mem_innerLePolyhedron_iff]
    intro j
    exact (show inner ℝ (a j) (x : E) < b j by
      simpa using (mem_analyticBarrierDomain_iff a b).mp x.property j).le
  have hRx : ‖(x : E)‖ ≤ R := hR _ hx_mem
  have ht_pos : 0 < t := by
    have hnum_pos : 0 < R + ‖(x : E)‖ + 1 := by
      nlinarith [hRx, norm_nonneg (x : E)]
    exact div_pos hnum_pos hu_norm_pos
  have hx : ∀ j : Fin m, inner ℝ (a j) (x : E) < b j := by
    simpa using (mem_analyticBarrierDomain_iff a b).mp x.property
  have hline_mem : (x : E) + t • u ∈ innerLePolyhedron a b := by
    rw [mem_innerLePolyhedron_iff]
    intro j
    calc
      inner ℝ (a j) ((x : E) + t • u)
          = inner ℝ (a j) (x : E) + t * inner ℝ (a j) u := by
              simp [inner_add_right, inner_smul_right]
      _ = inner ℝ (a j) (x : E) := by simp [hu j]
      _ ≤ b j := (hx j).le
  have hbound : ‖(x : E) + t • u‖ ≤ R := hR _ hline_mem
  have htu : ‖t • u‖ = R + ‖(x : E)‖ + 1 := by
    calc
      ‖t • u‖ = |t| * ‖u‖ := norm_smul t u
      _ = t * ‖u‖ := by rw [abs_of_nonneg ht_pos.le]
      _ = R + ‖(x : E)‖ + 1 := by
            rw [show t = (R + ‖(x : E)‖ + 1) / ‖u‖ by rfl]
            field_simp [hu_norm_pos.ne']
  have htriangle : ‖t • u‖ ≤ ‖(x : E) + t • u‖ + ‖(x : E)‖ := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (norm_add_le ((x : E) + t • u) (-(x : E)))
  linarith

/-- Helper for Definition 3.63: in any orthonormal basis, boundedness upgrades the Hessian matrix
of the analytic barrier from positive semidefinite to positive definite. -/
private theorem analyticBarrierAmbient_hessian_toMatrix_posDef_of_bounded
    (hQ_bounded : Bornology.IsBounded (innerLePolyhedron a b))
    (x : AnalyticBarrierPoint a b)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : OrthonormalBasis ι ℝ E) :
    (LinearMap.toMatrix e.toBasis e.toBasis (hessian (analyticBarrierAmbient a b) x).toLinearMap).PosDef := by
  let A : E →ₗ[ℝ] E := (hessian (analyticBarrierAmbient a b) x).toLinearMap
  have hA_pos : A.IsPositive := (analyticBarrierAmbient_hessian_isPositive (a := a) (b := b) x).toLinearMap
  have hA_psd :
      (LinearMap.toMatrix e.toBasis e.toBasis A).PosSemidef := by
    exact (LinearMap.posSemidef_toMatrix_iff e).2 hA_pos
  have hA_det_ne : LinearMap.det A ≠ 0 := by
    rw [ne_eq, LinearMap.det_eq_zero_iff_ker_ne_bot]
    intro hker
    obtain ⟨u, hu_mem, hu_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
    have hu_zero : hessian (analyticBarrierAmbient a b) x u = 0 := hu_mem
    have hu_constraints : ∀ j : Fin m, inner ℝ (a j) u = 0 := by
      have hinner_zero : inner ℝ (hessian (analyticBarrierAmbient a b) x u) u = 0 := by
        simpa [hu_zero]
      exact (analyticBarrierAmbient_hessian_zero_iff (a := a) (b := b) x u).1 hinner_zero
    exact hu_ne <|
      orthogonal_to_constraints_eq_zero_of_bounded (a := a) (b := b) hQ_bounded x hu_constraints
  have hM_det_ne :
      (LinearMap.toMatrix e.toBasis e.toBasis A).det ≠ 0 := by
    simpa [LinearMap.det_toMatrix e.toBasis A] using hA_det_ne
  exact (hA_psd.posDef_iff_det_ne_zero).2 hM_det_ne

theorem volumetricBarrier_hessian_det_pos
    (hQ_bounded : Bornology.IsBounded (innerLePolyhedron a b))
    (x : AnalyticBarrierPoint a b) :
    0 < (hessian (analyticBarrierAmbient a b) x).det := by
  let e := stdOrthonormalBasis ℝ E
  have hPosDef :
      (LinearMap.toMatrix e.toBasis e.toBasis (hessian (analyticBarrierAmbient a b) x).toLinearMap).PosDef :=
    analyticBarrierAmbient_hessian_toMatrix_posDef_of_bounded (a := a) (b := b) hQ_bounded x e
  -- Pass to an orthonormal-basis matrix, use positive definiteness there, then rewrite back.
  have hdet :
      0 <
        (LinearMap.toMatrix e.toBasis e.toBasis (hessian (analyticBarrierAmbient a b) x).toLinearMap).det :=
    hPosDef.det_pos
  change 0 < LinearMap.det (hessian (analyticBarrierAmbient a b) x).toLinearMap
  simpa [LinearMap.det_toMatrix e.toBasis (hessian (analyticBarrierAmbient a b) x).toLinearMap] using hdet

/-- Evaluating `volumetricBarrier a b` at a strict-slack point recovers the ambient bridge
formula `volumetricBarrierAmbient a b`. -/
@[simp] theorem volumetricBarrier_apply (x : AnalyticBarrierPoint a b) :
    volumetricBarrier a b x = volumetricBarrierAmbient a b x :=
  rfl

/-- Minimizing the strict-domain volumetric barrier is equivalent to minimizing the ambient
Hessian log-determinant formula over the strict barrier domain. -/
theorem isMinOn_volumetricBarrier_iff
    (y : AnalyticBarrierPoint a b) :
    IsMinOn (volumetricBarrier a b) Set.univ y ↔
      IsMinOn (volumetricBarrierAmbient a b) (analyticBarrierDomain a b) y := by
  rw [isMinOn_univ_iff, isMinOn_iff]
  constructor
  · intro hy x hx
    simpa [volumetricBarrier] using hy ⟨x, hx⟩
  · intro hy x
    simpa [volumetricBarrier] using hy x x.property

/-- If the chosen half-space presentation recovers the intrinsic interior of
`innerLePolyhedron a b`, then the strict-domain minimizer condition for `volumetricBarrier a b`
is equivalent to minimizing the ambient Hessian log-determinant formula over that interior. -/
theorem isMinOn_volumetricBarrier_iff_interior
    (hinterior : interior (innerLePolyhedron a b) ⊆ analyticBarrierDomain a b)
    (y : AnalyticBarrierPoint a b) :
    IsMinOn (volumetricBarrier a b) Set.univ y ↔
      IsMinOn (volumetricBarrierAmbient a b) (interior (innerLePolyhedron a b)) y := by
  rw [isMinOn_volumetricBarrier_iff]
  simp [analyticBarrierDomain_eq_interior_innerLePolyhedron a b hinterior]

section

variable (y : AnalyticBarrierPoint a b)

/- Definition 3.63: for a bounded polyhedron `innerLePolyhedron a b` with nonempty interior, a
volumetric center is a strict-slack point that globally minimizes the volumetric barrier
`x ↦ log det ∇²F(x)` on the strict barrier domain. The canonical owner is `IsMinOn`, so this file
reuses `IsMinOn` directly on `volumetricBarrier a b` rather than adding a parallel
`IsVolumetricCenter` wrapper. If one additionally knows that the chosen presentation identifies
`analyticBarrierDomain a b` with `interior (innerLePolyhedron a b)`, the same minimizer condition
transports to the intrinsic interior by `isMinOn_volumetricBarrier_iff_interior`. The boundedness
hypothesis belongs only to `volumetricBarrier_hessian_det_pos`; it is not primitive data of the
center predicate itself. -/
recall IsMinOn
recall isMinOn_univ_iff

set_option linter.hashCommand false in
#check IsMinOn (volumetricBarrier a b) Set.univ y

set_option linter.hashCommand false in
#check IsMinOn (volumetricBarrierAmbient a b) (analyticBarrierDomain a b) y

end

end

end
