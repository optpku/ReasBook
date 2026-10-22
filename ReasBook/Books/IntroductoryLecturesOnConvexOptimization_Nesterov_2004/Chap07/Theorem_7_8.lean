/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_17
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_27
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_29
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_33
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Lemma_7_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open scoped BigOperators ConvexAnalysis EllipsoidNotation PositiveDefMatrixNorm SupportFunction
  SymmetricBox

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "DiagVec" => Fin n → ℝ

/- Theorem 7.8 lies in the Chapter 7 centered ellipsoid-rounding / sign-invariant convex-set
domain.

Sampled owner-style declarations:
* `IsEllipsoidalRounding` in `Chap07/Definition_7_29`, the chapter owner of centered
  `γ √n`-ellipsoidal roundings;
* `IsEllipsoidalRounding.unit_ellipsoid_subset` and
  `IsEllipsoidalRounding.subset_outer_ellipsoid` in `Chap07/Definition_7_29`, the derived inner
  and outer containment API for that owner;
* `IsSignInvariant` in `Chap07/Definition_7_33`, the chapter owner of sign-symmetry;
* `matrixEllipsoid` / `W[r](G)` in `Chap07/Definition_7_26`, reused upstream by
  `IsEllipsoidalRounding`.

Best owner abstraction:
* source-facing: the existence of a diagonal centered ellipsoidal rounding for a
  sign-invariant convex set with nonempty interior, after making the needed compactness repair
  explicit on the raw-set surface;
* core/canonical: `IsEllipsoidalRounding C γ D`;
* bridge/view: the extra diagonality condition `D.IsDiag` on the rounding matrix.

Primitive data:
* raw-set data `C : Set E` together with explicit sign-invariance, convexity, nonempty interior,
  and compactness on the source-facing main theorem;
* companion input data `C : ConvexBody E` for the convenience bridge theorem, or `C : Set E` with
  explicit boundedness and closedness when those are the easier raw-set inputs;
* a matrix `D : Mat`.

Derived API:
* positive definiteness and the two ellipsoid containments, all supplied by
  `IsEllipsoidalRounding C 1 D`;
* diagonality as the only additional theorem-specific datum.

This refinement deletes the duplicate local wrapper `IsDiagonalEllipsoidalRounding`. The theorem is
source-facing, but its rounding core is already owned by `IsEllipsoidalRounding`; only the extra
diagonality requirement remains on the theorem surface. The semantic-defect report identifies that
boundedness alone does not rule out counterexamples such as open balls in dimension `1`; the
repaired source-facing surface therefore keeps the theorem on raw sets and makes compactness
explicit, while the convex-body and bounded-closed formulations remain as companions.
-/

-- Semantic search note: `lean_leansearch` surfaced generic convex-body infrastructure such as
-- `ConvexBody.isCompact`, but not a direct diagonal-rounding theorem. The chapter-local owner
-- `IsEllipsoidalRounding` therefore remains the right core surface, with the raw-set compact
-- theorem as the main source-facing surface and convex-body / bounded-closed bridge theorems as
-- companions.

-- Proof sketch: choose a volume-maximizing feasible diagonal matrix among those whose unit
-- ellipsoid lies in `C`, and use the sign-invariant rounding argument from Lemma 7.7 to show that
-- the optimal outer radius is at most `Real.sqrt n`.
/-- Helper for Theorem 7.8: sign symmetry and convexity move any interior point to the origin. -/
lemma zero_mem_interior_of_signInvariant_convex_interior_nonempty
    {C : Set E} (h_sign : IsSignInvariant C) (h_convex : Convex ℝ C)
    (h_interior : (interior C).Nonempty) :
    (0 : E) ∈ interior C := by
  rcases h_interior with ⟨x, hx⟩
  let σ : Fin n → ℝ := fun _ ↦ (-1 : ℝ)
  have hσ : σ ∈ signVectorSet (Fin n) := by
    -- The constant `-1` vector is a legitimate sign vector.
    rw [mem_signVectorSet_iff]
    intro i
    left
    simp [σ]
  have h_negx : (-x : E) ∈ interior C := by
    -- Move a neighborhood of `x` across the sign flip to get a neighborhood of `-x`.
    have hC_nhds : C ∈ nhds x := mem_interior_iff_mem_nhds.mp hx
    rw [mem_interior_iff_mem_nhds]
    rw [Metric.mem_nhds_iff]
    rcases Metric.mem_nhds_iff.mp hC_nhds with ⟨ε, hεpos, hεsub⟩
    refine ⟨ε, hεpos, ?_⟩
    intro y hy
    have hneg_mem : (-y : E) ∈ C := by
      -- Negating a point in the ball around `-x` lands in the ball around `x`.
      have hneg_ball : (-y : E) ∈ Metric.ball x ε := by
        rw [Metric.mem_ball] at hy ⊢
        simpa [dist_neg y x] using hy
      exact hεsub hneg_ball
    -- Flipping the sign of `-y` returns `y`, so sign invariance closes the argument.
    have hσy : ((σ • (-y : E) : E)) ∈ C := h_sign.smul_mem hneg_mem hσ
    have hσy_eq : (σ • (-y : E) : E) = y := by
      ext i
      simp [σ]
    rw [hσy_eq] at hσy
    exact hσy
  have hInteriorConvex : Convex ℝ (interior C) := h_convex.interior
  -- The midpoint of `x` and `-x` is `0`, and convexity keeps midpoints inside the interior.
  have h_midpoint :
      ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • (-x) : E) ∈ interior C := by
    refine hInteriorConvex hx h_negx ?_ ?_ ?_
    · positivity
    · positivity
    · ring
  simpa using h_midpoint

/-- Helper for Theorem 7.8: once `0` is an interior point of a bounded set, the set contains a
small centered
closed ball and is contained in a large centered closed ball. -/
lemma exists_centered_inner_outer_radii_of_zero_mem_interior
    {C : Set E} (h_zero : (0 : E) ∈ interior C) (h_bounded : Bornology.IsBounded C) :
    ∃ r R : ℝ, 0 < r ∧ 0 < R ∧
      Metric.closedBall (0 : E) r ⊆ C ∧
      C ⊆ Metric.closedBall (0 : E) R := by
  have hC_nhds : C ∈ nhds (0 : E) := mem_interior_iff_mem_nhds.mp h_zero
  rcases Metric.mem_nhds_iff.mp hC_nhds with ⟨ε, hεpos, hεsub⟩
  rcases h_bounded.subset_closedBall_lt 0 (0 : E) with ⟨R, hRpos, hRsub⟩
  refine ⟨ε / 2, R, by positivity, hRpos, ?_, hRsub⟩
  -- Shrink the interior ball so that its closed ball still fits inside `C`.
  intro x hx
  exact hεsub <| Metric.closedBall_subset_ball (half_lt_self hεpos) hx

/-- Helper for Theorem 7.8: the scalar diagonal matrix `r² I` is diagonal and positive definite
whenever `r > 0`. -/
lemma scalar_diagonal_sq_isDiag_posDef {r : ℝ} (hr : 0 < r) :
    (((Matrix.diagonal fun _ : Fin n ↦ r ^ (2 : ℕ)) : Mat).IsDiag) ∧
      (((Matrix.diagonal fun _ : Fin n ↦ r ^ (2 : ℕ)) : Mat).PosDef) := by
  refine ⟨Matrix.isDiag_diagonal _, ?_⟩
  -- Positive definiteness of a diagonal matrix is equivalent to positivity on the diagonal.
  refine Matrix.PosDef.diagonal ?_
  intro i
  simpa [pow_two] using sq_pos_of_ne_zero (ne_of_gt hr)

/-- Helper for Theorem 7.8: a point outside `W[√n](D)` has dual norm strictly larger than
`√n`. -/
lemma sqrtDim_lt_dualNorm_of_not_mem_outerEllipsoid
    {D : Mat} (hDpos : D.PosDef) {g : E}
    (hg_outer : g ∉ W[(Real.sqrt (n : ℝ))](D)) :
    Real.sqrt (n : ℝ) < ‖g‖[⟨D, hDpos⟩,*] := by
  -- Rewrite ellipsoid membership as the canonical dual-norm inequality.
  by_contra hle
  exact hg_outer <| (mem_centeredMatrixEllipsoid_iff_dualNorm_le hDpos).2 (le_of_not_gt hle)

/-- Helper for Theorem 7.8: support functions are monotone under set inclusion. -/
lemma supportFunction_mono_of_subset {Q₁ Q₂ : Set E} (hQ : Q₁ ⊆ Q₂) (x : E) :
    ξ[Q₁] x ≤ ξ[Q₂] x := by
  -- Unfold both support functions and enlarge the supremum image along the inclusion.
  rw [supportFunction_apply, supportFunction_apply]
  exact sSup_le_sSup (Set.image_mono hQ)

/-- Helper for Theorem 7.8: the primal norm of a positive diagonal matrix is the corresponding
weighted Euclidean norm. -/
lemma primalNorm_diagonal_eq_sqrt_sum
    {d : DiagVec} (hd_pos : ∀ i, 0 < d i) (x : E) :
    ‖x‖[⟨Matrix.diagonal d, Matrix.PosDef.diagonal hd_pos⟩] =
      Real.sqrt (∑ i, d i * (x i) ^ (2 : ℕ)) := by
  -- Expand the primal norm formula and then collapse the diagonal quadratic form coordinatewise.
  rw [positiveDefMatrixNorm_def]
  rw [PiLp.inner_apply]
  simp [Matrix.toEuclideanLin_apply, Matrix.mulVec_diagonal, real_inner_eq_re_inner,
    RCLike.inner_apply]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro i hi
  ring

/-- Helper for Theorem 7.8: the scalar diagonal unit ellipsoid `W[1](r² I)` lies in the centered
closed ball of radius `r`. -/
lemma scalarDiagonalUnitEllipsoid_subset_closedBall
    {r : ℝ} (hr : 0 < r) :
    centeredMatrixEllipsoid (Matrix.diagonal (fun _ : Fin n ↦ r ^ (2 : ℕ))) 1 ⊆
      Metric.closedBall (0 : E) r := by
  intro x hx
  have hr_sq_pos : 0 < r ^ (2 : ℕ) := by positivity
  have hdiag_unit : IsUnit (fun _ : Fin n ↦ r ^ (2 : ℕ)) :=
    Pi.isUnit_iff.mpr fun i ↦ isUnit_iff_ne_zero.mpr (pow_ne_zero 2 (ne_of_gt hr))
  have hdiag_inv :
      ((↑hdiag_unit.unit⁻¹ : Fin n → ℝ)) = fun _ : Fin n ↦ (r ^ (2 : ℕ))⁻¹ := by
    funext i
    simpa using hdiag_unit.val_inv_apply i
  -- Expand the scalar diagonal inverse ellipsoid inequality into the Euclidean norm formula.
  rw [mem_centeredMatrixEllipsoid_iff] at hx
  rw [Metric.mem_closedBall, dist_zero_right, EuclideanSpace.norm_eq]
  rw [Matrix.toEuclideanLin_apply, Matrix.inv_diagonal, Ring.inverse_of_isUnit hdiag_unit] at hx
  rw [hdiag_inv] at hx
  have hx_sq :
      (r ^ (2 : ℕ))⁻¹ * ∑ i : Fin n, (x i) ^ (2 : ℕ) ≤ 1 := by
    -- After rewriting the inverse diagonal, the defining quadratic form becomes the scaled sum of
    -- coordinate squares.
    rw [Real.sqrt_le_iff] at hx
    have hinner_eq :
        inner ℝ
            (WithLp.toLp 2
              ((Matrix.diagonal (fun _ : Fin n ↦ (r ^ (2 : ℕ))⁻¹)) *ᵥ x.ofLp)) x =
          (r ^ (2 : ℕ))⁻¹ * ∑ i : Fin n, (x i) ^ (2 : ℕ) := by
      rw [PiLp.inner_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i hi
      simp [Matrix.mulVec_diagonal, real_inner_eq_re_inner, RCLike.inner_apply, pow_two,
        mul_left_comm, mul_comm]
    have hx_inner :
        inner ℝ
            (WithLp.toLp 2
              ((Matrix.diagonal (fun _ : Fin n ↦ (r ^ (2 : ℕ))⁻¹)) *ᵥ x.ofLp)) x ≤
          1 := by
      simpa using hx.2
    rw [hinner_eq] at hx_inner
    exact hx_inner
  have hsum_le : ∑ i : Fin n, (x i) ^ (2 : ℕ) ≤ r ^ (2 : ℕ) := by
    have hscaled :=
      mul_le_mul_of_nonneg_left hx_sq hr_sq_pos.le
    simpa [hr_sq_pos.ne', mul_assoc, mul_left_comm, mul_comm] using hscaled
  -- Taking square roots recovers the Euclidean closed-ball bound.
  have hsqrt_le :
      Real.sqrt (∑ i : Fin n, (x i) ^ (2 : ℕ)) ≤ Real.sqrt (r ^ (2 : ℕ)) :=
    Real.sqrt_le_sqrt hsum_le
  have hsqrt_r : Real.sqrt (r ^ (2 : ℕ)) = r := by
    simpa [pow_two, abs_of_pos hr] using Real.sqrt_sq_eq_abs r
  rw [hsqrt_r] at hsqrt_le
  simpa [Real.norm_eq_abs, sq_abs] using hsqrt_le

/-- Helper for Theorem 7.8: a unit ellipsoid containment gives the corresponding real-valued
support-function bound. -/
lemma supportRealBound_of_unitEllipsoidSubset
    {C : Set E} (h_compact : IsCompact C) (hC_nonempty : C.Nonempty)
    {d : DiagVec} (hd_pos : ∀ i, 0 < d i)
    (hsubset : centeredMatrixEllipsoid (Matrix.diagonal d) 1 ⊆ C) :
    ∀ x : E, Real.sqrt (∑ i, d i * (x i) ^ (2 : ℕ)) ≤ (ξ[C] x).toReal := by
  intro x
  have hmono : ξ[(centeredMatrixEllipsoid (Matrix.diagonal d) 1 : Set E)] x ≤ ξ[C] x :=
    supportFunction_mono_of_subset hsubset x
  have hCfinite := supportFunction_ne_top_ne_bot_of_isCompact h_compact hC_nonempty x
  -- Rewrite the ellipsoid support value through the diagonal primal norm formula.
  rw [supportFunction_centeredMatrixEllipsoid_eq_coe_primalNorm
      (Matrix.diagonal d) (Matrix.PosDef.diagonal hd_pos), primalNorm_diagonal_eq_sqrt_sum hd_pos x] at hmono
  rw [← EReal.coe_toReal hCfinite.1 hCfinite.2] at hmono
  exact_mod_cast hmono

/-- Helper for Theorem 7.8: the real-valued support bound reconstructs the corresponding unit
ellipsoid containment. -/
lemma unitEllipsoidSubset_of_supportRealBound
    {C : Set E} (h_compact : IsCompact C) (hC_nonempty : C.Nonempty) (h_convex : Convex ℝ C)
    {d : DiagVec} (hd_pos : ∀ i, 0 < d i)
    (hsupport : ∀ x : E, Real.sqrt (∑ i, d i * (x i) ^ (2 : ℕ)) ≤ (ξ[C] x).toReal) :
    centeredMatrixEllipsoid (Matrix.diagonal d) 1 ⊆ C := by
  -- Convert the real-valued bound back to the support-function inequality on the effective domain.
  refine subset_of_supportFunction_le_on_domain
    (centeredMatrixEllipsoid (Matrix.diagonal d) 1) C hC_nonempty h_compact.isClosed h_convex ?_
  intro x hxdom
  have hCfinite := supportFunction_ne_top_ne_bot_of_isCompact h_compact hC_nonempty x
  rw [supportFunction_centeredMatrixEllipsoid_eq_coe_primalNorm
      (Matrix.diagonal d) (Matrix.PosDef.diagonal hd_pos), primalNorm_diagonal_eq_sqrt_sum hd_pos x]
  rw [← EReal.coe_toReal hCfinite.1 hCfinite.2]
  exact_mod_cast hsupport x

/-- Helper for Theorem 7.8: a fixed support-feasibility slice is closed in the diagonal
coordinates. -/
lemma isClosed_diagonalSupportSlice
    {C : Set E} (x : E) :
    IsClosed {d : DiagVec | Real.sqrt (∑ i, d i * (x i) ^ (2 : ℕ)) ≤ (ξ[C] x).toReal} := by
  -- The defining left-hand side is continuous in the diagonal coordinates, so the slice is a
  -- closed sublevel set.
  refine isClosed_le ?_ continuous_const
  exact Real.continuous_sqrt.comp (by fun_prop)

/-- Helper for Theorem 7.8: evaluating a support-feasible diagonal at a basis vector bounds the
corresponding coordinate by the squared support value in that direction. -/
lemma feasibleCoordSqBound_of_basisSupport
    {C : Set E} {d : DiagVec}
    (hd_nonneg : ∀ i, 0 ≤ d i)
    (hsupport : ∀ x : E, Real.sqrt (∑ i, d i * (x i) ^ (2 : ℕ)) ≤ (ξ[C] x).toReal) :
    ∀ i : Fin n, d i ≤ ((ξ[C] (EuclideanSpace.single i (1 : ℝ))).toReal) ^ (2 : ℕ) := by
  intro i
  have hs := hsupport (EuclideanSpace.single i (1 : ℝ))
  have hs_basis :
      Real.sqrt (d i) ≤ (ξ[C] (EuclideanSpace.single i (1 : ℝ))).toReal := by
    -- The basis vector isolates the `i`-th coordinate inside the quadratic form.
    simpa [EuclideanSpace.single, hd_nonneg i] using hs
  have hsupport_nonneg : 0 ≤ (ξ[C] (EuclideanSpace.single i (1 : ℝ))).toReal :=
    le_trans (Real.sqrt_nonneg _) hs_basis
  have hsq_le :
      (Real.sqrt (d i)) ^ (2 : ℕ) ≤
        ((ξ[C] (EuclideanSpace.single i (1 : ℝ))).toReal) ^ (2 : ℕ) := by
    have habs :
        |Real.sqrt (d i)| ≤ |(ξ[C] (EuclideanSpace.single i (1 : ℝ))).toReal| := by
      rw [abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg hsupport_nonneg]
      exact hs_basis
    exact sq_le_sq.mpr habs
  simpa [Real.sq_sqrt (hd_nonneg i)] using hsq_le

/-- Helper for Theorem 7.8: the explicit coordinate update is exactly the diagonal interpolation
matrix from Lemma 7.7. -/
lemma diagonalInterpolation_eq
    (d : DiagVec) (g : E) (α : ℝ) :
    ellipsoidBoxInterpolationMatrix (Matrix.diagonal d) g α =
      Matrix.diagonal (fun i : Fin n ↦ (1 - α) * d i + α * (g i) ^ (2 : ℕ)) := by
  -- Both matrices are diagonal with the same diagonal entries, so entrywise extensionality closes.
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [ellipsoidBoxInterpolationMatrix]
  · simp [ellipsoidBoxInterpolationMatrix, hij]

/-- Helper for Theorem 7.8: for a diagonal update, the Lemma 7.7 log-volume potential is the log
of the ratio of the coordinate products. -/
lemma ellipsoidBoxLogVolumePotential_eq_logProdRatio_diagonalUpdate
    (d : DiagVec) (g : E) (α : ℝ) :
    let d' : DiagVec := fun i ↦ (1 - α) * d i + α * (g i) ^ (2 : ℕ)
    ellipsoidBoxLogVolumePotential (Matrix.diagonal d) g α =
      Real.log ((∏ i, d i) / (∏ i, d' i)) := by
  -- Expand the potential and rewrite both interpolation matrices through diagonal determinants.
  dsimp
  rw [ellipsoidBoxLogVolumePotential_def, diagonalInterpolation_eq]
  -- At `α = 0`, the interpolation matrix collapses back to the original diagonal matrix.
  simp [ellipsoidBoxInterpolationMatrix, Matrix.det_diagonal]

/-- Helper for Theorem 7.8: the explicit Lemma 7.7 update stays inside `C` once the base diagonal
is support-feasible and `g` witnesses an outer violation. -/
lemma updatedDiagonalUnitEllipsoid_subset_of_outerViolation
    {C : Set E} (h_sign : IsSignInvariant C) (h_convex : Convex ℝ C)
    (h_compact : IsCompact C) (hC_nonempty : C.Nonempty)
    {d : DiagVec} (hd_pos : ∀ i, 0 < d i)
    (hsupport : ∀ x : E, Real.sqrt (∑ i, d i * (x i) ^ (2 : ℕ)) ≤ (ξ[C] x).toReal)
    {g : E} (hgC : g ∈ C)
    (hg_outer : g ∉ centeredMatrixEllipsoid (Matrix.diagonal d) (Real.sqrt (n : ℝ))) :
    let α := ellipsoidBoxAlphaStar (Matrix.diagonal d) (Matrix.PosDef.diagonal hd_pos) g
    let d' : DiagVec := fun i ↦ (1 - α) * d i + α * (g i) ^ (2 : ℕ)
    centeredMatrixEllipsoid (Matrix.diagonal d') 1 ⊆ C := by
  -- Route correction: the intended proof first rebuilds `W[1](diag d) ⊆ C` from the support
  -- bound, then uses sign-invariance to place `B(|g|)` inside `C`, and finally applies the public
  -- closed-interpolation inclusion from Lemma 7.7 after rewriting the interpolation matrix back to
  -- `Matrix.diagonal d'`.
  dsimp
  let α := ellipsoidBoxAlphaStar (Matrix.diagonal d) (Matrix.PosDef.diagonal hd_pos) g
  let d' : DiagVec := fun i ↦ (1 - α) * d i + α * (g i) ^ (2 : ℕ)
  have hD_subset : centeredMatrixEllipsoid (Matrix.diagonal d) 1 ⊆ C :=
    unitEllipsoidSubset_of_supportRealBound h_compact hC_nonempty h_convex hd_pos hsupport
  have hbox_subset : B(fun i ↦ |g i|) ⊆ C := by
    exact (isSignInvariant_iff_symmetricBox_subset_of_convex h_convex).mp h_sign g hgC
  have hgenerated_subset :
      ellipsoidBoxGeneratedConvexSet (Matrix.diagonal d) g ⊆ C := by
    -- The generated convex hull stays inside `C` because both generators already do.
    rw [ellipsoidBoxGeneratedConvexSet_def]
    refine convexHull_min ?_ h_convex
    rintro x (hx | hx)
    · exact hD_subset hx
    · exact hbox_subset hx
  have hdual_gt :
      Real.sqrt (n : ℝ) <
        ‖g‖[⟨Matrix.diagonal d, Matrix.PosDef.diagonal hd_pos⟩,*] :=
    sqrtDim_lt_dualNorm_of_not_mem_outerEllipsoid (Matrix.PosDef.diagonal hd_pos) hg_outer
  have hS :
      (n : ℝ) <
        ‖g‖[⟨Matrix.diagonal d, Matrix.PosDef.diagonal hd_pos⟩,*] ^ (2 : ℕ) := by
    -- Squaring the strict outer violation gives the `S > n` hypothesis needed by Lemma 7.7.
    have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
    have hsqrt_sq : (Real.sqrt (n : ℝ)) ^ (2 : ℕ) = (n : ℝ) := by
      simp [Real.sq_sqrt hn_nonneg]
    have hdual_sq :
        (Real.sqrt (n : ℝ)) ^ (2 : ℕ) <
          ‖g‖[⟨Matrix.diagonal d, Matrix.PosDef.diagonal hd_pos⟩,*] ^ (2 : ℕ) := by
      have hdual_nonneg :
          0 ≤ ‖g‖[⟨Matrix.diagonal d, Matrix.PosDef.diagonal hd_pos⟩,*] := by
        nlinarith [hdual_gt, Real.sqrt_nonneg (n : ℝ)]
      rw [sq_lt_sq]
      simpa [abs_of_nonneg (Real.sqrt_nonneg _),
        abs_of_nonneg hdual_nonneg] using hdual_gt
    simpa [hsqrt_sq] using hdual_sq
  have hα : α ∈ Set.Ico (0 : ℝ) 1 := by
    simpa [α] using
      ellipsoidBoxAlphaStar_mem_halfOpenUnitInterval
        (Matrix.diagonal d) (Matrix.PosDef.diagonal hd_pos) g hS
  have hclosed_section :
      ellipsoidBoxClosedInterpolationSection (Matrix.diagonal d) g α ⊆
        ellipsoidBoxGeneratedConvexSet (Matrix.diagonal d) g := by
    -- Apply the closed-interval interpolation containment from Lemma 7.7 at `α = α*`.
    refine centeredMatrixEllipsoid_closedInterpolation_subset_ellipsoidBoxGeneratedConvexSet
      (Matrix.diagonal d) (Matrix.isDiag_diagonal d) (Matrix.PosDef.diagonal hd_pos) g α
      ⟨hα.1, hα.2.le⟩
  have hupdated_subset :
      centeredMatrixEllipsoid (Matrix.diagonal d') 1 ⊆
        ellipsoidBoxGeneratedConvexSet (Matrix.diagonal d) g := by
    -- Rewrite the closed interpolation section back to the updated diagonal ellipsoid.
    rw [ellipsoidBoxClosedInterpolationSection_eq_centeredMatrixEllipsoid
      (Matrix.diagonal d) g (show α ≠ 1 from ne_of_lt hα.2)] at hclosed_section
    rw [diagonalInterpolation_eq d g α] at hclosed_section
    simpa [d', α] using hclosed_section
  exact hupdated_subset.trans hgenerated_subset

/-- Helper for Theorem 7.8: the Lemma 7.7 update strictly increases the diagonal product whenever
`g` violates the outer `√n`-ellipsoid bound. -/
lemma updatedDiagonalProduct_gt_of_outerViolation
    {d : DiagVec} (hd_pos : ∀ i, 0 < d i) {g : E}
    (hg_outer : g ∉ centeredMatrixEllipsoid (Matrix.diagonal d) (Real.sqrt (n : ℝ))) :
    let D := Matrix.diagonal d
    let α := ellipsoidBoxAlphaStar D (Matrix.PosDef.diagonal hd_pos) g
    let d' : DiagVec := fun i ↦ (1 - α) * d i + α * (g i) ^ (2 : ℕ)
    ∏ i, d i < ∏ i, d' i := by
  -- Route correction: the intended proof rewrites the Lemma 7.7 potential as
  -- `log ((∏ d i) / (∏ d' i))`, proves that value is negative using the endpoint
  -- `γ = ‖g‖*_D / √n`, and exponentiates to conclude `∏ d i < ∏ d' i`.
  by_cases hn : n = 0
  · -- In dimension `0`, the ambient space is trivial, so no outer violation can occur.
    have hg_zero : g = 0 := by
      ext i
      exact False.elim (by simpa [hn] using i.2)
    have hzero_mem :
        (0 : E) ∈ centeredMatrixEllipsoid (Matrix.diagonal d) (Real.sqrt (n : ℝ)) := by
      rw [mem_centeredMatrixEllipsoid_iff_dualNorm_le (Matrix.PosDef.diagonal hd_pos)]
      rw [positiveDefMatrixNorm_dualNorm_eq_sqrt_inner_inv]
      simp
    exact False.elim <| hg_outer <| by simpa [hg_zero]
  · let D : Mat := Matrix.diagonal d
    let α : ℝ := ellipsoidBoxAlphaStar D (Matrix.PosDef.diagonal hd_pos) g
    let d' : DiagVec := fun i ↦ (1 - α) * d i + α * (g i) ^ (2 : ℕ)
    have hn_pos : 0 < n := Nat.pos_iff_ne_zero.mpr hn
    have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := by
      exact Real.sqrt_pos.2 (by exact_mod_cast hn_pos)
    have hdual_gt :
        Real.sqrt (n : ℝ) < ‖g‖[⟨D, Matrix.PosDef.diagonal hd_pos⟩,*] := by
      simpa [D] using
        sqrtDim_lt_dualNorm_of_not_mem_outerEllipsoid (Matrix.PosDef.diagonal hd_pos) hg_outer
    have hS :
        (n : ℝ) < ‖g‖[⟨D, Matrix.PosDef.diagonal hd_pos⟩,*] ^ (2 : ℕ) := by
      -- Squaring the strict norm inequality produces the threshold required by Lemma 7.7.
      have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
      have hsqrt_sq : (Real.sqrt (n : ℝ)) ^ (2 : ℕ) = (n : ℝ) := by
        simp [Real.sq_sqrt hn_nonneg]
      have hdual_sq :
          (Real.sqrt (n : ℝ)) ^ (2 : ℕ) <
            ‖g‖[⟨D, Matrix.PosDef.diagonal hd_pos⟩,*] ^ (2 : ℕ) := by
        have hdual_nonneg : 0 ≤ ‖g‖[⟨D, Matrix.PosDef.diagonal hd_pos⟩,*] := by
          nlinarith [hdual_gt, Real.sqrt_nonneg (n : ℝ)]
        rw [sq_lt_sq]
        simpa [abs_of_nonneg (Real.sqrt_nonneg _),
          abs_of_nonneg hdual_nonneg] using hdual_gt
      simpa [hsqrt_sq] using hdual_sq
    have hα : α ∈ Set.Ico (0 : ℝ) 1 := by
      simpa [D, α] using ellipsoidBoxAlphaStar_mem_halfOpenUnitInterval D
        (Matrix.PosDef.diagonal hd_pos) g hS
    have hd'_pos : ∀ i, 0 < d' i := by
      -- Each updated coordinate is a strict convex combination of a positive entry and a square.
      intro i
      have hsq_nonneg : 0 ≤ (g i) ^ (2 : ℕ) := by positivity
      have hone_sub_pos : 0 < 1 - α := sub_pos.mpr hα.2
      nlinarith [hd_pos i, hsq_nonneg, hα.1]
    have hprod_pos : 0 < ∏ i, d i := by
      exact Finset.prod_pos fun i _ ↦ hd_pos i
    have hprod'_pos : 0 < ∏ i, d' i := by
      exact Finset.prod_pos fun i _ ↦ hd'_pos i
    let γ : ℝ := ‖g‖[⟨D, Matrix.PosDef.diagonal hd_pos⟩,*] / Real.sqrt (n : ℝ)
    have hγ : γ ∈ Set.Ioc (1 : ℝ) (‖g‖[⟨D, Matrix.PosDef.diagonal hd_pos⟩,*] / Real.sqrt (n : ℝ)) := by
      -- Choose the endpoint parameter `γ = ‖g‖*_D / √n`, which is admissible because the outer
      -- violation makes it strictly larger than `1`.
      refine ⟨?_, le_rfl⟩
      simpa [γ] using (one_lt_div hsqrt_pos).2 hdual_gt
    have hpotential_lt :
        ellipsoidBoxLogVolumePotential D g α < 0 := by
      rcases
          ellipsoidBoxLogVolumePotential_alphaStar_le_gammaComparison_and_lt_zero
            D (Matrix.isDiag_diagonal d) (Matrix.PosDef.diagonal hd_pos) g hS γ hγ with
        ⟨hupper, hneg⟩
      exact lt_of_le_of_lt hupper hneg
    have hlog_lt :
        Real.log ((∏ i, d i) / (∏ i, d' i)) < 0 := by
      simpa [D, α, d'] using
        (ellipsoidBoxLogVolumePotential_eq_logProdRatio_diagonalUpdate d g α ▸ hpotential_lt)
    have hratio_lt_one : ((∏ i, d i) / (∏ i, d' i)) < 1 := by
      exact (Real.log_neg_iff (div_pos hprod_pos hprod'_pos)).mp hlog_lt
    have hprod_lt : ∏ i, d i < ∏ i, d' i := by
      exact (div_lt_one hprod'_pos).mp hratio_lt_one
    simpa [D, α, d'] using hprod_lt

/-- Theorem 7.8: if `C ⊆ ℝⁿ` is a sign-symmetric compact convex set with nonempty interior, then
there exists a diagonal matrix `D` with `D ≻ 0` such that
`W_1(D) ⊆ C ⊆ W_(sqrt n)(D)`. -/
theorem exists_diagonal_rounding_of_signInvariant_convex_interior_nonempty
    {C : Set E} (h_sign : IsSignInvariant C) (h_convex : Convex ℝ C)
    (h_interior : (interior C).Nonempty) (h_compact : IsCompact C) :
    ∃ D : Mat, D.IsDiag ∧ IsEllipsoidalRounding C 1 D := by
  -- Route correction: replace the stalled `[0, R²]^n` feasibility family by the leaner
  -- support-feasible family, derive compactness afterward from basis-direction support bounds,
  -- and then run the Lemma 7.7 update contradiction against a product maximizer.
  have h_zero : (0 : E) ∈ interior C :=
    zero_mem_interior_of_signInvariant_convex_interior_nonempty h_sign h_convex h_interior
  have h_bounded : Bornology.IsBounded C := h_compact.isBounded
  rcases
      exists_centered_inner_outer_radii_of_zero_mem_interior h_zero h_bounded with
    ⟨r, _, hr, _, h_innerBall, _⟩
  have hC_nonempty : C.Nonempty := h_interior.mono interior_subset
  have hzero_memC : (0 : E) ∈ C := interior_subset h_zero
  let F : Set DiagVec :=
    {d | (∀ i, 0 ≤ d i) ∧
      ∀ x : E, Real.sqrt (∑ i, d i * (x i) ^ (2 : ℕ)) ≤ (ξ[C] x).toReal}
  let d0 : DiagVec := fun _ ↦ r ^ (2 : ℕ)
  have hd0_pos : ∀ i, 0 < d0 i := by
    intro i
    dsimp [d0]
    positivity
  have hd0_subset : centeredMatrixEllipsoid (Matrix.diagonal d0) 1 ⊆ C := by
    -- The scalar witness ellipsoid lies in the centered inner ball, hence inside `C`.
    exact (scalarDiagonalUnitEllipsoid_subset_closedBall hr).trans h_innerBall
  have hd0F : d0 ∈ F := by
    refine ⟨?_, ?_⟩
    · intro i
      exact (hd0_pos i).le
    · -- Convert the witness ellipsoid inclusion into the support-feasibility inequalities.
      exact supportRealBound_of_unitEllipsoidSubset h_compact hC_nonempty hd0_pos hd0_subset
  have hF_nonempty : F.Nonempty := ⟨d0, hd0F⟩
  have hF_closed : IsClosed F := by
    have hnonneg_closed : IsClosed {d : DiagVec | ∀ i, 0 ≤ d i} := by
      have hEq :
          {d : DiagVec | ∀ i, 0 ≤ d i} = ⋂ i : Fin n, {d : DiagVec | 0 ≤ d i} := by
        ext d
        simp
      rw [hEq]
      exact isClosed_iInter fun i : Fin n =>
        isClosed_le continuous_const (by fun_prop)
    have hsupport_closed :
        IsClosed
          {d : DiagVec |
            ∀ x : E, Real.sqrt (∑ i, d i * (x i) ^ (2 : ℕ)) ≤ (ξ[C] x).toReal} := by
      have hEq :
          {d : DiagVec |
            ∀ x : E, Real.sqrt (∑ i, d i * (x i) ^ (2 : ℕ)) ≤ (ξ[C] x).toReal} =
            ⋂ x : E,
              {d : DiagVec | Real.sqrt (∑ i, d i * (x i) ^ (2 : ℕ)) ≤ (ξ[C] x).toReal} := by
        ext d
        simp
      rw [hEq]
      exact isClosed_iInter fun x : E => isClosed_diagonalSupportSlice (C := C) x
    simpa [F] using hnonneg_closed.inter hsupport_closed
  let K : Set DiagVec :=
    Set.univ.pi fun i : Fin n ↦
      Set.Icc (0 : ℝ) (((ξ[C] (EuclideanSpace.single i (1 : ℝ))).toReal) ^ (2 : ℕ))
  have hK_compact : IsCompact K := by
    -- The ambient coordinate box is compact because each support-based interval is compact.
    exact isCompact_univ_pi fun _ ↦ isCompact_Icc
  have hF_subset_K : F ⊆ K := by
    intro d hdF
    rcases hdF with ⟨hd_nonneg, hd_support⟩
    intro i hi
    refine ⟨hd_nonneg i, feasibleCoordSqBound_of_basisSupport hd_nonneg hd_support i⟩
  have hF_compact : IsCompact F := hK_compact.of_isClosed_subset hF_closed hF_subset_K
  let volume : DiagVec → ℝ := fun d ↦ ∏ i, d i
  obtain ⟨dStar, hdStarF, hdStarMax⟩ :=
    hF_compact.exists_isMaxOn hF_nonempty (show ContinuousOn volume F from by
      dsimp [volume]
      fun_prop)
  have hdStar_nonneg : ∀ i, 0 ≤ dStar i := hdStarF.1
  have hd0_prod_pos : 0 < volume d0 := by
    -- The scalar witness has strictly positive coordinate product.
    dsimp [volume, d0]
    exact Finset.prod_pos fun i _ ↦ by positivity
  have hdStar_prod_pos : 0 < volume dStar := by
    exact lt_of_lt_of_le hd0_prod_pos (hdStarMax hd0F)
  have hdStar_pos : ∀ i, 0 < dStar i := by
    intro i
    by_contra hnot_pos
    have hzero : dStar i = 0 := le_antisymm (le_of_not_gt hnot_pos) (hdStar_nonneg i)
    have hprod_zero : volume dStar = 0 := by
      classical
      dsimp [volume]
      rw [Finset.prod_eq_zero_iff]
      exact ⟨i, by simp, hzero⟩
    have : ¬ volume dStar = 0 := ne_of_gt hdStar_prod_pos
    exact this hprod_zero
  have hdStar_support :
      ∀ x : E, Real.sqrt (∑ i, dStar i * (x i) ^ (2 : ℕ)) ≤ (ξ[C] x).toReal := hdStarF.2
  let D : Mat := Matrix.diagonal dStar
  have hDpos : D.PosDef := by
    simpa [D] using Matrix.PosDef.diagonal hdStar_pos
  have hinner_subset : centeredMatrixEllipsoid D 1 ⊆ C := by
    -- Rebuild the inner containment from the maximizing support-feasible diagonal.
    simpa [D] using
      unitEllipsoidSubset_of_supportRealBound h_compact hC_nonempty h_convex hdStar_pos
        hdStar_support
  have houter_subset : C ⊆ centeredMatrixEllipsoid D (Real.sqrt (n : ℝ)) := by
    intro g hgC
    by_contra hg_outer
    let α : ℝ := ellipsoidBoxAlphaStar D hDpos g
    let d' : DiagVec := fun i ↦ (1 - α) * dStar i + α * (g i) ^ (2 : ℕ)
    have hdual_gt : Real.sqrt (n : ℝ) < ‖g‖[⟨D, hDpos⟩,*] :=
      sqrtDim_lt_dualNorm_of_not_mem_outerEllipsoid hDpos hg_outer
    have hS : (n : ℝ) < ‖g‖[⟨D, hDpos⟩,*] ^ (2 : ℕ) := by
      -- Squaring the outer violation produces the strict threshold needed for `α*`.
      have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
      have hsqrt_sq : (Real.sqrt (n : ℝ)) ^ (2 : ℕ) = (n : ℝ) := by
        simp [Real.sq_sqrt hn_nonneg]
      have hdual_sq :
          (Real.sqrt (n : ℝ)) ^ (2 : ℕ) <
            ‖g‖[⟨D, hDpos⟩,*] ^ (2 : ℕ) := by
        have hdual_nonneg : 0 ≤ ‖g‖[⟨D, hDpos⟩,*] := by
          nlinarith [hdual_gt, Real.sqrt_nonneg (n : ℝ)]
        rw [sq_lt_sq]
        simpa [abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg hdual_nonneg] using hdual_gt
      simpa [hsqrt_sq] using hdual_sq
    have hα : α ∈ Set.Ico (0 : ℝ) 1 := by
      simpa [α] using ellipsoidBoxAlphaStar_mem_halfOpenUnitInterval D hDpos g hS
    have hd'_nonneg : ∀ i, 0 ≤ d' i := by
      intro i
      have hsq_nonneg : 0 ≤ (g i) ^ (2 : ℕ) := by positivity
      have hone_sub_nonneg : 0 ≤ 1 - α := sub_nonneg.mpr hα.2.le
      nlinarith [hdStar_nonneg i, hsq_nonneg, hα.1]
    have hd'_pos : ∀ i, 0 < d' i := by
      intro i
      have hsq_nonneg : 0 ≤ (g i) ^ (2 : ℕ) := by positivity
      have hone_sub_pos : 0 < 1 - α := sub_pos.mpr hα.2
      nlinarith [hdStar_pos i, hsq_nonneg, hα.1]
    have hd'_subset : centeredMatrixEllipsoid (Matrix.diagonal d') 1 ⊆ C := by
      -- Lemma 7.7's explicit diagonal update stays inside `C`.
      simpa [D, α, d'] using
        updatedDiagonalUnitEllipsoid_subset_of_outerViolation h_sign h_convex h_compact
          hC_nonempty hdStar_pos hdStar_support hgC hg_outer
    have hd'F : d' ∈ F := by
      refine ⟨hd'_nonneg, ?_⟩
      -- Convert the updated inner ellipsoid inclusion back into support feasibility.
      exact supportRealBound_of_unitEllipsoidSubset h_compact hC_nonempty hd'_pos hd'_subset
    have hmax_le : volume d' ≤ volume dStar := hdStarMax hd'F
    have hprod_lt : volume dStar < volume d' := by
      -- The same update strictly increases the diagonal product, contradicting maximality.
      simpa [volume, D, α, d'] using updatedDiagonalProduct_gt_of_outerViolation hdStar_pos hg_outer
    exact (not_lt_of_ge hmax_le) hprod_lt
  refine ⟨D, ?_, ?_⟩
  · simpa [D] using Matrix.isDiag_diagonal dStar
  · refine ⟨hDpos, ?_⟩
    refine
      { unit_ellipsoid_subset := ?_
        subset_beta_ellipsoid := ?_ }
    · -- The inner containment is exactly the `W[1](D) ⊆ C` part of the rounding.
      simpa [D, centeredMatrixEllipsoid_one_eq_affineEllipsoid]
        using hinner_subset
    · -- The contradiction argument established the outer `√n` containment.
      simpa [D, centeredMatrixEllipsoid, one_mul] using houter_subset

/-- Convex-body bridge for Theorem 7.8. -/
theorem exists_diagonal_rounding_of_signInvariant_convexBody_interior_nonempty
    (C : ConvexBody E) (h_sign : IsSignInvariant (C : Set E))
    (h_interior : (interior (C : Set E)).Nonempty) :
    ∃ D : Mat, D.IsDiag ∧ IsEllipsoidalRounding (C : Set E) 1 D := by
  -- Reuse the raw-set theorem on the carrier of the convex body.
  simpa using
    exists_diagonal_rounding_of_signInvariant_convex_interior_nonempty
      (C := (C : Set E)) h_sign C.convex h_interior C.isCompact

/-- Bounded-closed raw-set bridge for Theorem 7.8. -/
theorem exists_diagonal_rounding_of_signInvariant_convex_interior_nonempty_bounded_closed
    {C : Set E} (h_sign : IsSignInvariant C) (h_convex : Convex ℝ C)
    (h_interior : (interior C).Nonempty) (h_bounded : Bornology.IsBounded C)
    (h_closed : IsClosed C) :
    ∃ D : Mat, D.IsDiag ∧ IsEllipsoidalRounding C 1 D := by
  -- Upgrade boundedness and closedness to compactness in the Euclidean ambient space.
  have h_compact : IsCompact C :=
    Metric.isCompact_of_isClosed_isBounded h_closed h_bounded
  exact
    exists_diagonal_rounding_of_signInvariant_convex_interior_nonempty
      h_sign h_convex h_interior h_compact

/-- Helper for Theorem 7.8: downstream alias for the bounded raw-set bridge. -/
theorem exists_diagonal_rounding_of_signInvariant_convex_interior_nonempty_bounded
    {C : Set E} (h_sign : IsSignInvariant C) (h_convex : Convex ℝ C)
    (h_interior : (interior C).Nonempty) (h_bounded : Bornology.IsBounded C)
    (h_closed : IsClosed C) :
    ∃ D : Mat, D.IsDiag ∧ IsEllipsoidalRounding C 1 D := by
  -- Forward to the bounded-closed bridge under the downstream theorem name.
  exact
    exists_diagonal_rounding_of_signInvariant_convex_interior_nonempty_bounded_closed
      h_sign h_convex h_interior h_bounded h_closed
