/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_10_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_62
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_26
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Theorem_7_8

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open EuclideanSpace (nonnegativeOrthant)
open Matrix
open scoped EllipsoidNotation Pointwise

variable {m n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "Matₙ" => Matrix (Fin n) (Fin n) ℝ

/- Theorem 7.9 lies in Chapter 7's diagonal ellipsoid / orthant-polyhedron rounding domain.

Sampled owner-style declarations:
- `matrixEllipsoid` with notation `W[r](G)` in `Chap07/Definition_7_26`, the chapter owner for
  radius-parametrized ellipsoids;
- `mem_centeredMatrixEllipsoid_iff_dualNorm_le` in `Chap07/Definition_7_26`, the canonical
  positive-definite membership view for `W[r](G)`;
- `innerLePolyhedron` and `mem_innerLePolyhedron_iff` in `Chap03/Definition_3_62`, the chapter
  owner for finite inner-product half-space presentations;
- `Matrix.IsDiag` and `Matrix.isDiag_diagonal` in mathlib's matrix diagonal API, the canonical
  owner and constructor theorem for diagonality;
- `Matrix.posDef_diagonal_iff` in mathlib's positive-definite diagonal API, the canonical matrix
  positivity criterion for diagonal matrices;
- `EuclideanSpace.nonnegativeOrthant` and `EuclideanSpace.mem_nonnegativeOrthant_iff` in
  `Chap01/Definition_1_10_2`, the chapter owner for orthant constraints.

Best owner abstraction:
- source-facing: the orthant-constrained polyhedron from Theorem 7.9;
- core/canonical: `W[r](G)`, `innerLePolyhedron`, `nonnegativeOrthant`, `Matrix.IsDiag`, and
  `Matrix.PosDef`;
- bridge/view: the orthant-specialized view `orthantHalfspacePolyhedron`.

Primitive data:
- `a : Fin m → Eₙ` and `b : Fin m → ℝ`;
- boundedness of the source-facing orthant polyhedron `orthantHalfspacePolyhedron a b`.

Derived API:
- the diagonal positive-definite rounding matrix `D : Matₙ`;
- the centered diagonal ellipsoids `W[1](D)` and `W[r](D)`;
- the source-facing orthant polyhedron `orthantHalfspacePolyhedron a b`, built from
  `innerLePolyhedron a b`.

Source/core/bridge triage:
- source-facing: `orthantHalfspacePolyhedron` and the theorem below;
- core/canonical: `W[r](G)`, `innerLePolyhedron`, `nonnegativeOrthant`, `Matrix.IsDiag`, and
  `Matrix.PosDef`;
- bridge/view: no additional public bridge owner is needed.

This refinement keeps the orthant polyhedron source-facing, but moves the existential witness to
the matrix owner level used by Chapter 7 ellipsoids: the theorem now returns a diagonal matrix
together with an orthant-specialized rounding predicate, rather than a four-way conjunction of
matrix properties and containments.
-/

/-- The polyhedron in the nonnegative orthant cut out by the inequalities
`⟪a_i, x⟫ ≤ b_i`. -/
def orthantHalfspacePolyhedron (a : Fin m → Eₙ) (b : Fin m → ℝ) : Set Eₙ :=
  nonnegativeOrthant n ∩ innerLePolyhedron a b

-- Proof sketch: unfold `orthantHalfspacePolyhedron` and use `mem_innerLePolyhedron_iff`.
/-- Membership in `orthantHalfspacePolyhedron a b` means belonging to the nonnegative orthant and
satisfying all inequalities `⟪a_i, x⟫ ≤ b_i`. -/
@[simp] theorem mem_orthantHalfspacePolyhedron_iff
    (a : Fin m → Eₙ) (b : Fin m → ℝ) (x : Eₙ) :
    x ∈ orthantHalfspacePolyhedron a b ↔
      x ∈ nonnegativeOrthant n ∧ ∀ i : Fin m, inner ℝ (a i) x ≤ b i := by
  simp [orthantHalfspacePolyhedron]

/-- An orthant ellipsoidal rounding of `C` with parameter `γ` is a positive-definite matrix `D`
whose unit ellipsoid restricted to the nonnegative orthant lies in `C`, and whose outer ellipsoid
of radius `γ √n`, again restricted to the nonnegative orthant, contains `C`. -/
structure IsOrthantEllipsoidalRounding
    (C : Set Eₙ) (γ : ℝ) (D : Matₙ) : Prop where
  /-- The rounding matrix is positive definite. -/
  posDef : D.PosDef
  /-- The positive-orthant slice of the unit ellipsoid lies in `C`. -/
  unit_ellipsoid_inter_nonnegativeOrthant_subset :
    W[1](D) ∩ nonnegativeOrthant n ⊆ C
  /-- The set `C` lies in the positive-orthant slice of the outer ellipsoid of radius `γ √n`. -/
  subset_outer_ellipsoid_inter_nonnegativeOrthant :
    C ⊆ W[(γ * Real.sqrt (n : ℝ))](D) ∩ nonnegativeOrthant n

/-- Helper for Theorem 7.9: the coordinatewise absolute-value map on `ℝⁿ`. -/
def pointwiseAbs (x : Eₙ) : Eₙ :=
  WithLp.toLp 2 fun j ↦ |x j|

/-- Helper for Theorem 7.9: the coordinates of `pointwiseAbs x` are the absolute values of the
coordinates of `x`. -/
@[simp] theorem pointwiseAbs_apply (x : Eₙ) (j : Fin n) :
    pointwiseAbs x j = |x j| := by
  simp [pointwiseAbs]

/-- Helper for Theorem 7.9: nonnegative vectors are fixed by coordinatewise absolute value. -/
theorem pointwiseAbs_eq_self_of_nonnegative {x : Eₙ} (hx : x ∈ nonnegativeOrthant n) :
    pointwiseAbs x = x := by
  ext j
  simp [pointwiseAbs, abs_of_nonneg (hx j)]

/-- Helper for Theorem 7.9: coordinatewise absolute value lands in the nonnegative orthant. -/
theorem pointwiseAbs_mem_nonnegativeOrthant (x : Eₙ) :
    pointwiseAbs x ∈ nonnegativeOrthant n := by
  intro j
  simp [pointwiseAbs]

/-- Helper for Theorem 7.9: coordinatewise absolute value preserves the Euclidean norm. -/
theorem norm_pointwiseAbs_eq_norm (x : Eₙ) :
    ‖pointwiseAbs x‖ = ‖x‖ := by
  have hsq : ‖pointwiseAbs x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    simp [pointwiseAbs, pow_two]
  rcases eq_or_eq_neg_of_sq_eq_sq ‖pointwiseAbs x‖ ‖x‖ hsq with hEq | hEq
  · exact hEq
  · have hzero : ‖x‖ = 0 := by
      nlinarith [norm_nonneg (pointwiseAbs x), norm_nonneg x, hEq]
    nlinarith [hEq, hzero]

/-- Helper for Theorem 7.9: the sign-invariant body obtained by replacing each orthant constraint
with its absolute-value version. -/
def absoluteConstraintBody (a : Fin m → Eₙ) (b : Fin m → ℝ) : Set Eₙ :=
  {x | ∀ i : Fin m, inner ℝ (a i) (pointwiseAbs x) ≤ b i}

-- Proof sketch: on the nonnegative orthant, the pointwise absolute value is the identity, so the
-- absolute-value body and the orthant polyhedron have the same inequality description.
/-- Helper for Theorem 7.9: on the nonnegative orthant, the absolute-value body is exactly the
orthant polyhedron. -/
theorem mem_absolute_constraint_body_iff_of_nonnegative
    (a : Fin m → Eₙ) (b : Fin m → ℝ) {x : Eₙ} (hx : x ∈ nonnegativeOrthant n) :
    x ∈ absoluteConstraintBody a b ↔ x ∈ orthantHalfspacePolyhedron a b := by
  -- Replace `|x|` by `x` coordinatewise before comparing the two membership predicates.
  have h_abs_eq : pointwiseAbs x = x := pointwiseAbs_eq_self_of_nonnegative hx
  rw [mem_orthantHalfspacePolyhedron_iff]
  simp [absoluteConstraintBody, h_abs_eq, hx]

/-- Helper for Theorem 7.9: coordinatewise sign changes do not alter pointwise absolute values. -/
theorem abs_signVector_smul_eq
    {σ : Fin n → ℝ} (hσ : σ ∈ signVectorSet (Fin n)) (x : Eₙ) :
    pointwiseAbs (σ • x) = pointwiseAbs x := by
  -- Each coordinate multiplier is `±1`, so its absolute value is `1`.
  ext j
  rcases mem_signVectorSet_iff.mp hσ j with hσj | hσj
  · simp [pointwiseAbs, hσj]
  · simp [pointwiseAbs, hσj]

/-- Helper for Theorem 7.9: if the coefficient vector is nonnegative, then the inner product with
the absolute value of a convex combination is bounded by the corresponding convex combination of
absolute values. -/
theorem inner_abs_smul_add_le
    {u x y : Eₙ} (hu : u ∈ nonnegativeOrthant n)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    inner ℝ u (pointwiseAbs (s • x + t • y)) ≤
      inner ℝ u (s • pointwiseAbs x + t • pointwiseAbs y) := by
  -- Expand the Euclidean inner product into a finite sum and apply the scalar triangle
  -- inequality in each coordinate with nonnegative weights.
  have hu_nonneg : ∀ j : Fin n, 0 ≤ u j := by
    simpa using hu
  have hcoord : ∀ j : Fin n, |s * x j + t * y j| ≤ s * |x j| + t * |y j| := by
    intro j
    calc
      |s * x j + t * y j| ≤ |s * x j| + |t * y j| := abs_add_le _ _
      _ = s * |x j| + t * |y j| := by
        simp [abs_mul, abs_of_nonneg hs, abs_of_nonneg ht]
  have hsum :
      ∑ j : Fin n, u j * |s * x j + t * y j| ≤
        ∑ j : Fin n, u j * (s * |x j| + t * |y j|) := by
    refine Finset.sum_le_sum ?_
    intro j hj
    exact mul_le_mul_of_nonneg_left (hcoord j) (hu_nonneg j)
  have hreal_inner_mul : ∀ a b : ℝ, inner ℝ a b = a * b := by
    intro a b
    calc
      inner ℝ a b = inner ℝ (a • (1 : ℝ)) (b • (1 : ℝ)) := by simp
      _ = a * (b * inner ℝ (1 : ℝ) (1 : ℝ)) := by
        rw [real_inner_smul_left, real_inner_smul_right]
      _ = a * b := by simp
  convert hsum using 1
  · simp [PiLp.inner_apply, pointwiseAbs, hreal_inner_mul]
  · simp [PiLp.inner_apply, pointwiseAbs, hreal_inner_mul, mul_add]

-- Proof sketch: the defining inequalities of `absoluteConstraintBody a b` depend only on `|x|`,
-- so every coordinatewise sign flip preserves membership.
/-- Helper for Theorem 7.9: the absolute-value body is sign-invariant. -/
theorem absolute_constraint_body_sign_invariant
    (a : Fin m → Eₙ) (b : Fin m → ℝ) :
    IsSignInvariant (absoluteConstraintBody a b) := by
  intro x hx σ hσ
  -- Rewrite the transformed point using the invariance of absolute value under sign vectors.
  simpa [absoluteConstraintBody, abs_signVector_smul_eq hσ x] using hx

-- Proof sketch: for each inequality, the coefficient vector is nonnegative, so the triangle
-- inequality gives the convex-combination estimate after summing the coordinates.
/-- Helper for Theorem 7.9: the absolute-value body is convex. -/
theorem absolute_constraint_body_convex
    (a : Fin m → Eₙ) (b : Fin m → ℝ)
    (ha_nonneg : ∀ i : Fin m, a i ∈ nonnegativeOrthant n) :
    Convex ℝ (absoluteConstraintBody a b) := by
  intro x hx y hy s t hs ht hst i
  -- Check each defining inequality separately after pushing the convex combination through `abs`.
  calc
    inner ℝ (a i) (pointwiseAbs (s • x + t • y))
      ≤ inner ℝ (a i) (s • pointwiseAbs x + t • pointwiseAbs y) :=
        inner_abs_smul_add_le (hu := ha_nonneg i) hs ht
    _ = s * inner ℝ (a i) (pointwiseAbs x) + t * inner ℝ (a i) (pointwiseAbs y) := by
      rw [inner_add_right, inner_smul_right, inner_smul_right]
    _ ≤ b i := by
      have hineq :
          s * inner ℝ (a i) (pointwiseAbs x) + t * inner ℝ (a i) (pointwiseAbs y) ≤
            s * b i + t * b i := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left (hx i) hs)
          (mul_le_mul_of_nonneg_left (hy i) ht)
      have hsumb : s * b i + t * b i = b i := by
        calc
          s * b i + t * b i = (s + t) * b i := by ring
          _ = b i := by rw [hst, one_mul]
      simpa [hsumb] using hineq

-- Proof sketch: the strict inequalities `⟪a_i, |x|⟫ < b_i` define an open neighborhood of `0`,
-- and this neighborhood is contained in the closed-inequality body.
/-- Helper for Theorem 7.9: the origin lies in the interior of the absolute-value body. -/
theorem zero_mem_interior_absolute_constraint_body
    (a : Fin m → Eₙ) (b : Fin m → ℝ)
    (hb_pos : ∀ i : Fin m, 0 < b i) :
    (0 : Eₙ) ∈ interior (absoluteConstraintBody a b) := by
  -- It is enough to exhibit an open strict-inequality neighborhood of `0` contained in the body.
  rw [mem_interior_iff_mem_nhds]
  let S : Set Eₙ := {x | ∀ i : Fin m, inner ℝ (a i) (pointwiseAbs x) < b i}
  have hcont_abs_fun : Continuous fun x : Eₙ => fun j : Fin n => |x j| := by
    refine continuous_pi ?_
    intro j
    simpa using
      (((continuous_apply j).comp (PiLp.continuous_ofLp 2 (fun _ : Fin n => ℝ))).abs)
  have hcont_abs : Continuous fun x : Eₙ => pointwiseAbs x := by
    simpa [pointwiseAbs] using
      (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).comp hcont_abs_fun
  have hcont : ∀ i : Fin m, Continuous fun x : Eₙ => inner ℝ (a i) (pointwiseAbs x) := by
    intro i
    exact continuous_const.inner hcont_abs
  have hS_open : IsOpen S := by
    -- Finite intersections of the coordinatewise strict halfspaces stay open.
    rw [show S = ⋂ i : Fin m, {x : Eₙ | inner ℝ (a i) (pointwiseAbs x) < b i} by
      ext x
      simp [S]]
    exact isOpen_iInter_of_finite fun i => isOpen_lt (hcont i) continuous_const
  have hS_zero : (0 : Eₙ) ∈ S := by
    -- At the origin every left-hand side vanishes, and `b_i > 0`.
    intro i
    have hzero_abs : pointwiseAbs (0 : Eₙ) = 0 := by
      ext j
      simp [pointwiseAbs]
    calc
      inner ℝ (a i) (pointwiseAbs (0 : Eₙ)) = inner ℝ (a i) (0 : Eₙ) := by
        rw [hzero_abs]
      _ = 0 := by simp
      _ < b i := hb_pos i
  have hS_subset : S ⊆ absoluteConstraintBody a b := by
    -- Strict feasibility implies feasibility for each defining inequality.
    intro x hx i
    exact (hx i).le
  exact Filter.mem_of_superset (hS_open.mem_nhds hS_zero) hS_subset

-- Proof sketch: if `x` satisfies the absolute-value constraints, then `|x|` lies in the bounded
-- orthant polyhedron; the norm is unchanged by absolute value, so the same radius bounds `x`.
/-- Helper for Theorem 7.9: boundedness of the orthant polyhedron transfers to the absolute-value
body. -/
theorem absolute_constraint_body_bounded
    (a : Fin m → Eₙ) (b : Fin m → ℝ)
    (h_bounded : Bornology.IsBounded (orthantHalfspacePolyhedron a b)) :
    Bornology.IsBounded (absoluteConstraintBody a b) := by
  -- Use the radius that bounds the orthant polyhedron and pull it back through `x ↦ |x|`.
  obtain ⟨R, hR_pos, hR⟩ := h_bounded.exists_pos_norm_le
  refine
    (Metric.isBounded_closedBall : Bornology.IsBounded (Metric.closedBall (0 : Eₙ) R)).subset ?_
  intro x hx
  have h_abs_mem : pointwiseAbs x ∈ orthantHalfspacePolyhedron a b := by
    rw [mem_orthantHalfspacePolyhedron_iff]
    constructor
    · exact pointwiseAbs_mem_nonnegativeOrthant x
    · intro i
      simpa [absoluteConstraintBody] using hx i
  have hnorm : ‖x‖ ≤ R := by
    have habs : ‖pointwiseAbs x‖ = ‖x‖ := norm_pointwiseAbs_eq_norm x
    simpa [habs] using hR (pointwiseAbs x) h_abs_mem
  simpa [Metric.mem_closedBall, dist_eq_norm] using hnorm

-- Proof sketch: apply the diagonal comparison theorem for positive homogeneous convex functions on
-- the nonnegative orthant to the gauge `f(x) = max_i ⟪a_i, x⟫ / b_i`, which is convex and
-- positively homogeneous because each `a_i` lies in `ℝⁿ_+` and each `b_i` is positive. The extra
-- boundedness hypothesis rules out degenerate orthant directions where all these inequalities stay
-- vacuous. The unit sublevel set of `f` is exactly `orthantHalfspacePolyhedron a b`, and the
-- comparison `‖x‖_D ≤ f(x) ≤ √n ‖x‖_D` rewrites as an orthant ellipsoidal rounding of
-- `orthantHalfspacePolyhedron a b`.
/-- Theorem 7.9: if `a_i ∈ ℝⁿ_+`, `b_i > 0` for `i = 1, …, m`, and the orthant polyhedron
`{x ∈ ℝⁿ_+ | ⟪a_i, x⟫ ≤ b_i for all i}` is bounded, then it is sandwiched between
`W₁(D) ∩ ℝⁿ_+` and `W_{√n}(D) ∩ ℝⁿ_+` for some diagonal positive-definite matrix `D`. -/
theorem exists_positive_diagonal_rounding_of_orthant_polyhedron
    (a : Fin m → Eₙ) (b : Fin m → ℝ)
    (ha_nonneg : ∀ i : Fin m, a i ∈ nonnegativeOrthant n)
    (hb_pos : ∀ i : Fin m, 0 < b i)
    (h_bounded : Bornology.IsBounded (orthantHalfspacePolyhedron a b)) :
    ∃ D : Matₙ, D.IsDiag ∧
      IsOrthantEllipsoidalRounding (orthantHalfspacePolyhedron a b) 1 D := by
  -- Apply Theorem 7.8 to the sign-invariant absolute-value body and then restrict back to
  -- the nonnegative orthant using the rewriting lemma above.
  let C : Set Eₙ := absoluteConstraintBody a b
  have h_sign : IsSignInvariant C := absolute_constraint_body_sign_invariant a b
  have h_convex : Convex ℝ C := absolute_constraint_body_convex a b ha_nonneg
  have h_interior : (interior C).Nonempty := by
    exact ⟨0, zero_mem_interior_absolute_constraint_body a b hb_pos⟩
  have hC_bounded : Bornology.IsBounded C := absolute_constraint_body_bounded a b h_bounded
  rcases
      exists_diagonal_rounding_of_signInvariant_convex_interior_nonempty_bounded
        h_sign h_convex h_interior hC_bounded with
    ⟨D, hDdiag, hrounding⟩
  refine ⟨D, hDdiag, ?_⟩
  refine
    { posDef := hrounding.posDef
      unit_ellipsoid_inter_nonnegativeOrthant_subset := ?_
      subset_outer_ellipsoid_inter_nonnegativeOrthant := ?_ }
  · intro x hx
    have hxC : x ∈ C := hrounding.unit_ellipsoid_subset hx.1
    exact (mem_absolute_constraint_body_iff_of_nonnegative a b hx.2).mp hxC
  · intro x hx
    have hxC : x ∈ C :=
      (mem_absolute_constraint_body_iff_of_nonnegative a b
        ((mem_orthantHalfspacePolyhedron_iff a b x).mp hx).1).mpr hx
    refine ⟨?_, ((mem_orthantHalfspacePolyhedron_iff a b x).mp hx).1⟩
    simpa [C] using hrounding.subset_outer_ellipsoid hxC

end
