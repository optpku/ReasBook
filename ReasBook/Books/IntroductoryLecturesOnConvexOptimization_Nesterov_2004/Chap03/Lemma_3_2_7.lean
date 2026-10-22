/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Lemma_1_8_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open MeasureTheory Matrix
open scoped RealInnerProductSpace MatrixOrder MatrixPosDef

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/- Lemma 3.2.7 lies in the chapter's Euclidean ellipsoid / ellipsoid-method update domain.

Relevant owner-style declarations sampled before refinement:
- `Matrix.toEuclideanLin`, the canonical matrix action on `EuclideanSpace ℝ (Fin n)`;
- `Matrix.vecMulVec`, the canonical matrix outer-product construction;
- `ContinuousLinearMap.rankOne` and the matrix/operator bridges from Chapter 1's rank-one update
  files, showing that rank-one update data should be derived from the canonical owner rather than
  stored as a separate public wrapper;
- downstream chapter recalls such as `Definition_3_56`, `Definition_3_57`, and `Lemma_3_32`,
  which treat the present file as the owner of the ellipsoid-update API.

Best owner abstraction:
- source-facing: `affineEllipsoid`, `centerCutEllipsoid`, `updatedEllipsoidCenter`,
  `updatedEllipsoidMatrix`, and the main containment/volume theorem;
- core/canonical: `Matrix.toEuclideanLin` and `Matrix.vecMulVec`;
- bridge/view: the companion membership lemmas and the explicit textbook update-formula lemmas.

Primitive data:
- the shape matrix `H`;
- the center `xBar`;
- the cut direction `g`;

Derived API:
- ellipsoid and center-cut membership views;
- the updated center and updated shape matrix as the textbook raw formulas;
- the valid-update theorem keeping positive definiteness, `g ≠ 0`, and `1 < n` as theorem
  hypotheses rather than owner data.

The previous helper `ellipsoidUpdateDirectionMatrix` was only a renamed shell around the canonical
outer product `Matrix.vecMulVec` and carried no source-facing mathematics, so it is removed. -/

/-- The ellipsoid with shape matrix `H` and center `xBar`, written in the textbook's
`E(H, x̄)` notation. -/
def affineEllipsoid (H : Mat) (xBar : E) : Set E :=
  {x | inner ℝ ((H⁻¹).toEuclideanLin (x - xBar)) (x - xBar) ≤ 1}

namespace EllipsoidNotation

scoped notation:max "E(" H ", " xBar ")" => affineEllipsoid H xBar

end EllipsoidNotation

open scoped EllipsoidNotation

/-- Membership in `E(H, x̄)` is exactly the defining quadratic inequality. -/
theorem mem_affineEllipsoid_iff {H : Mat} {xBar x : E} :
    x ∈ E(H, xBar) ↔
      inner ℝ ((H⁻¹).toEuclideanLin (x - xBar)) (x - xBar) ≤ 1 :=
  Iff.rfl

/-- The center `x̄` always belongs to its ellipsoid `E(H, x̄)`. -/
theorem center_mem_affineEllipsoid (H : Mat) (xBar : E) :
    xBar ∈ E(H, xBar) := by
  simp [affineEllipsoid]

/-- The center of a positive-definite ellipsoid lies in the interior of that ellipsoid. -/
theorem center_mem_interior_affineEllipsoid
    (H : Mat) (xBar : E) (hH : H.PosDef) :
    xBar ∈ interior (E(H, xBar) : Set E) := by
  obtain ⟨m, hm, M, hM, hbound⟩ := posDef_exists_quadraticForm_bounds H⁻¹ hH.inv
  rw [mem_interior_iff_mem_nhds]
  have hball : Metric.ball xBar ((Real.sqrt M)⁻¹) ∈ nhds xBar :=
    Metric.ball_mem_nhds xBar (inv_pos.mpr (Real.sqrt_pos.2 hM))
  refine Filter.mem_of_superset hball ?_
  intro x hx
  rw [Metric.mem_ball, dist_eq_norm] at hx
  rw [mem_affineEllipsoid_iff]
  have hquad_le : inner ℝ (toEuclideanLin H⁻¹ (x - xBar)) (x - xBar) ≤ M * ‖x - xBar‖ ^ 2 :=
    (hbound (x - xBar)).2
  have hnorm_lt_sq : ‖x - xBar‖ ^ 2 < ((Real.sqrt M)⁻¹) ^ (2 : ℕ) := by
    nlinarith [norm_nonneg (x - xBar), inv_nonneg.mpr (Real.sqrt_nonneg M), hx]
  have hnorm_lt : ‖x - xBar‖ ^ 2 < M⁻¹ := by
    simpa [inv_pow, Real.sq_sqrt hM.le] using hnorm_lt_sq
  have hmul : M * ‖x - xBar‖ ^ 2 < M * M⁻¹ :=
    mul_lt_mul_of_pos_left hnorm_lt hM
  have hquad_lt : inner ℝ (toEuclideanLin H⁻¹ (x - xBar)) (x - xBar) < 1 := by
    exact lt_of_le_of_lt hquad_le (by simpa [hM.ne'] using hmul)
  exact le_of_lt hquad_lt

/-- A positive-definite ellipsoid `E(H, x̄)` is bounded. -/
theorem affineEllipsoid_bounded
    (H : Mat) (xBar : E) (hH : H.PosDef) :
    Bornology.IsBounded (E(H, xBar)) := by
  obtain ⟨m, hm, _, _, hbound⟩ := posDef_exists_quadraticForm_bounds H⁻¹ hH.inv
  refine (Metric.isBounded_iff_subset_closedBall xBar).2 ?_
  refine ⟨(Real.sqrt m)⁻¹, ?_⟩
  intro x hx
  rw [Metric.mem_closedBall, dist_eq_norm]
  have hquad :
      inner ℝ ((H⁻¹).toEuclideanLin (x - xBar)) (x - xBar) ≤ 1 :=
    (mem_affineEllipsoid_iff.1 hx)
  have hm0 : m ≠ 0 := ne_of_gt hm
  have hnormsq_le : ‖x - xBar‖ ^ (2 : ℕ) ≤ m⁻¹ := by
    have hlower := (hbound (x - xBar)).1
    have hmul : m⁻¹ * (m * ‖x - xBar‖ ^ (2 : ℕ)) ≤ m⁻¹ * 1 := by
      exact mul_le_mul_of_nonneg_left (le_trans hlower hquad) (inv_nonneg.mpr hm.le)
    simpa [mul_assoc, hm0] using hmul
  have hsq : ‖x - xBar‖ ^ (2 : ℕ) ≤ ((Real.sqrt m)⁻¹) ^ (2 : ℕ) := by
    simpa [inv_pow, Real.sq_sqrt hm.le] using hnormsq_le
  nlinarith
    [norm_nonneg (x - xBar),
      inv_nonneg.mpr (Real.sqrt_nonneg m), hsq]

/-- The half-ellipsoid cut `E₊` obtained by intersecting `E(H, x̄)` with the halfspace
`⟪g, x - x̄⟫ ≤ 0`. -/
def centerCutEllipsoid (H : Mat) (xBar g : E) : Set E :=
  {x | x ∈ E(H, xBar) ∧ inner ℝ g (x - xBar) ≤ 0}

namespace EllipsoidNotation

scoped notation:max "E₊(" H ", " xBar ", " g ")" => centerCutEllipsoid H xBar g

end EllipsoidNotation

/-- Membership in `E₊` is ellipsoid membership together with the cutting inequality. -/
theorem mem_centerCutEllipsoid_iff {H : Mat} {xBar g x : E} :
    x ∈ E₊(H, xBar, g) ↔
      x ∈ E(H, xBar) ∧ inner ℝ g (x - xBar) ≤ 0 :=
  Iff.rfl

/-- Helper for Lemma 3.2.7: the bilinear form attached to a matrix acts by the associated
Euclidean quadratic form. -/
private def matrixBilin (A : Mat) : LinearMap.BilinForm ℝ E :=
  ((innerSL ℝ).comp A.toEuclideanLin.toContinuousLinearMap).toBilinForm

/-- Helper for Lemma 3.2.7: a positive-definite matrix induces a symmetric bilinear form. -/
private theorem matrixBilin_isSymm_of_posDef
    (A : Mat) (hA : A.PosDef) :
    LinearMap.IsSymm (matrixBilin A) := by
  -- Positive operators are symmetric, so the induced bilinear form is symmetric as well.
  rw [← LinearMap.BilinForm.isSymm_iff, LinearMap.BilinForm.isSymm_def]
  intro x y
  change inner ℝ (A.toEuclideanLin x) y = inner ℝ (A.toEuclideanLin y) x
  have hPosLin : A.toEuclideanLin.IsPositive :=
    Matrix.isPositive_toEuclideanLin_iff.mpr hA.posSemidef
  simpa [real_inner_comm] using hPosLin.isSymmetric x y

/-- Helper for Lemma 3.2.7: the quadratic form of a positive-definite matrix is nonnegative. -/
private theorem matrixBilin_nonneg_of_posDef
    (A : Mat) (hA : A.PosDef) (x : E) :
    0 ≤ matrixBilin A x x := by
  -- This is the usual nonnegativity of the quadratic form attached to a positive operator.
  change 0 ≤ inner ℝ (A.toEuclideanLin x) x
  have hPosLin : A.toEuclideanLin.IsPositive :=
    Matrix.isPositive_toEuclideanLin_iff.mpr hA.posSemidef
  simpa [real_inner_comm] using hPosLin.inner_nonneg_right x

/-- Helper for Lemma 3.2.7: the inverse matrix cancels the original matrix on Euclidean vectors. -/
private theorem nonsing_inv_toEuclideanLin_comp
    (H : Mat) (hH : H.PosDef) (x : E) :
    (H⁻¹).toEuclideanLin (H.toEuclideanLin x) = x := by
  -- Convert the Euclidean action back to matrix `mulVec` and cancel with the nonsingular inverse.
  have hHdet : IsUnit H.det := isUnit_iff_ne_zero.mpr (ne_of_gt hH.det_pos)
  have hmul : H⁻¹ * H = 1 := Matrix.nonsing_inv_mul H hHdet
  ext i
  simp [Matrix.mulVec_mulVec, hmul]

/-- Helper for Lemma 3.2.7: the `H⁻¹` quadratic form controls the cut pairing by weighted
Cauchy-Schwarz. -/
private theorem cut_pairing_sq_le
    (H : Mat) (hH : H.PosDef) (g y : E) :
    (inner ℝ g y) ^ (2 : ℕ) ≤
      inner ℝ (H.toEuclideanLin g) g *
        inner ℝ ((H⁻¹).toEuclideanLin y) y := by
  let B : LinearMap.BilinForm ℝ E := matrixBilin H⁻¹
  have hB_nonneg : ∀ z : E, 0 ≤ B z z := by
    intro z
    simpa [B] using matrixBilin_nonneg_of_posDef H⁻¹ hH.inv z
  have hB_symm : LinearMap.IsSymm B := by
    simpa [B] using matrixBilin_isSymm_of_posDef H⁻¹ hH.inv
  have hB_symm_form : B.IsSymm := (LinearMap.BilinForm.isSymm_iff).2 hB_symm
  have hcs := LinearMap.BilinForm.apply_sq_le_of_symm B hB_nonneg hB_symm y (H.toEuclideanLin g)
  have hleft :
      B y (H.toEuclideanLin g) = inner ℝ g y := by
    -- Symmetry lets us move the `H⁻¹` action onto `H g`, where it cancels.
    calc
      B y (H.toEuclideanLin g) = B (H.toEuclideanLin g) y := by
        exact hB_symm_form.eq _ _
      _ = inner ℝ ((H⁻¹).toEuclideanLin (H.toEuclideanLin g)) y := by
        rfl
      _ = inner ℝ g y := by
        rw [nonsing_inv_toEuclideanLin_comp H hH]
  have hright :
      B (H.toEuclideanLin g) (H.toEuclideanLin g) =
        inner ℝ (H.toEuclideanLin g) g := by
    -- The same cancellation identifies the comparison factor with `⟪H g, g⟫`.
    calc
      B (H.toEuclideanLin g) (H.toEuclideanLin g) =
          inner ℝ ((H⁻¹).toEuclideanLin (H.toEuclideanLin g)) (H.toEuclideanLin g) := by
            rfl
      _ = inner ℝ g (H.toEuclideanLin g) := by
        rw [nonsing_inv_toEuclideanLin_comp H hH]
      _ = inner ℝ (H.toEuclideanLin g) g := by
        rw [real_inner_comm]
  simpa [B, hleft, hright, mul_comm] using hcs

/-- Helper for Lemma 3.2.7: after normalizing the cut pairing by `⟪H g, g⟫^{1/2}`, the scalar
expression from the textbook expansion is at most `1`. -/
private theorem center_cut_update_scalar_bound
    {u t : ℝ} (hn : 1 < n) (ht : t ≤ 1) (hu_nonpos : u ≤ 0) (hu_sq : u ^ (2 : ℕ) ≤ t) :
    ((((n : ℝ) ^ (2 : ℕ)) - 1) / ((n : ℝ) ^ (2 : ℕ))) *
        (t + (2 / ((n : ℝ) - 1)) * (u ^ (2 : ℕ) + u) +
          1 / (((n : ℝ) ^ (2 : ℕ)) - 1)) ≤ 1 := by
  -- First note that `u ∈ [-1, 0]`, so `u² + u ≤ 0` and the mixed term is harmless.
  have hn_real : 1 < (n : ℝ) := by
    exact_mod_cast hn
  have hden_pos : 0 < ((n : ℝ) - 1) := by
    linarith
  have hsq_le_one : u ^ (2 : ℕ) ≤ 1 := le_trans hu_sq ht
  have hu_ge_neg_one : -1 ≤ u := by
    nlinarith
  have hquad_nonpos : u ^ (2 : ℕ) + u ≤ 0 := by
    nlinarith
  have hcoef_nonneg : 0 ≤ 2 / ((n : ℝ) - 1) := by
    positivity
  have hmain :
      t + (2 / ((n : ℝ) - 1)) * (u ^ (2 : ℕ) + u) +
          1 / (((n : ℝ) ^ (2 : ℕ)) - 1) ≤
        t + 1 / (((n : ℝ) ^ (2 : ℕ)) - 1) := by
    nlinarith
  have hsq_pos : 0 < ((n : ℝ) ^ (2 : ℕ)) := by
    positivity
  have hsq_sub_pos : 0 < ((n : ℝ) ^ (2 : ℕ)) - 1 := by
    nlinarith
  have hscale_nonneg :
      0 ≤ (((n : ℝ) ^ (2 : ℕ)) - 1) / ((n : ℝ) ^ (2 : ℕ)) := by
    positivity
  have hstep1 :
      ((((n : ℝ) ^ (2 : ℕ)) - 1) / ((n : ℝ) ^ (2 : ℕ))) *
          (t + (2 / ((n : ℝ) - 1)) * (u ^ (2 : ℕ) + u) +
            1 / (((n : ℝ) ^ (2 : ℕ)) - 1)) ≤
        ((((n : ℝ) ^ (2 : ℕ)) - 1) / ((n : ℝ) ^ (2 : ℕ))) *
          (t + 1 / (((n : ℝ) ^ (2 : ℕ)) - 1)) := by
    gcongr
  have hstep2 :
      ((((n : ℝ) ^ (2 : ℕ)) - 1) / ((n : ℝ) ^ (2 : ℕ))) *
          (t + 1 / (((n : ℝ) ^ (2 : ℕ)) - 1)) ≤
        ((((n : ℝ) ^ (2 : ℕ)) - 1) / ((n : ℝ) ^ (2 : ℕ))) *
          (1 + 1 / (((n : ℝ) ^ (2 : ℕ)) - 1)) := by
    gcongr
  have hfinal :
      ((((n : ℝ) ^ (2 : ℕ)) - 1) / ((n : ℝ) ^ (2 : ℕ))) *
          (1 + 1 / (((n : ℝ) ^ (2 : ℕ)) - 1)) = 1 := by
    field_simp [show ((n : ℝ) ^ (2 : ℕ)) ≠ 0 by positivity,
      show (((n : ℝ) ^ (2 : ℕ)) - 1) ≠ 0 by positivity]
    ring
  exact le_trans hstep1 (le_trans hstep2 (by rw [hfinal]))

private theorem ellipsoidUpdate_quadratic_pos
    (H : Mat) (hH : H.PosDef) {g : E} (hg : g ≠ 0) :
    0 < inner ℝ (H.toEuclideanLin g) g := by
  have hg_coord : g.ofLp ≠ 0 := by
    intro hg_zero
    apply hg
    exact congrArg (WithLp.toLp 2) hg_zero
  have hdot : 0 < dotProduct g.ofLp (H *ᵥ g.ofLp) := by
    simpa using hH.dotProduct_mulVec_pos hg_coord
  have hinner := EuclideanSpace.inner_eq_star_dotProduct (H.toEuclideanLin g) g
  simp only [Matrix.ofLp_toLpLin] at hinner
  simpa [hinner] using hdot

/-- The updated center `x̄₊` in the ellipsoid method. -/
def updatedEllipsoidCenter (H : Mat) (xBar g : E) : E :=
  let Hg := H.toEuclideanLin g
  xBar - ((n : ℝ) + 1)⁻¹ • ((Real.sqrt (inner ℝ Hg g))⁻¹ • Hg)

namespace EllipsoidNotation

scoped notation:max "x̄₊(" H ", " xBar ", " g ")" => updatedEllipsoidCenter H xBar g

end EllipsoidNotation

/-- The updated shape matrix `H₊` in the ellipsoid method. -/
def updatedEllipsoidMatrix (H : Mat) (g : E) : Mat :=
  let Hg := H.toEuclideanLin g
  ((((n : ℝ) ^ (2 : ℕ)) / (((n : ℝ) ^ (2 : ℕ)) - 1)) : ℝ) •
    (H - (((2 : ℝ) / ((n : ℝ) + 1)) / inner ℝ Hg g) • vecMulVec Hg Hg)

namespace EllipsoidNotation

scoped notation:max "H₊(" H ", " g ")" => updatedEllipsoidMatrix H g

end EllipsoidNotation

/-- Helper for Lemma 3.2.7: the original matrix also cancels the inverse matrix on Euclidean
vectors. -/
private theorem toEuclideanLin_nonsing_inv_comp
    (H : Mat) (hH : H.PosDef) (x : E) :
    H.toEuclideanLin ((H⁻¹).toEuclideanLin x) = x := by
  -- Convert the Euclidean action back to matrix `mulVec` and cancel with the left inverse.
  have hHdet : IsUnit H.det := isUnit_iff_ne_zero.mpr (ne_of_gt hH.det_pos)
  have hmul : H * H⁻¹ = 1 := Matrix.mul_nonsing_inv H hHdet
  ext i
  simp [Matrix.mulVec_mulVec, hmul]

/-- Helper for Lemma 3.2.7: for a Hermitian real matrix, right multiplication by the matrix
agrees with the Euclidean action of that matrix. -/
private theorem vecMul_eq_toEuclideanLin_of_isHermitian
    (A : Mat) (hA : A.IsHermitian) (x : E) :
    x.ofLp ᵥ* A = (A.toEuclideanLin x).ofLp := by
  -- Rewrite the row action as multiplication by the transpose, then use Hermitian symmetry.
  have hAT : Aᵀ = A := by
    simpa using hA.eq
  simpa [Matrix.ofLp_toLpLin, hAT] using (Matrix.vecMul_transpose Aᵀ x.ofLp)

/-- Helper for Lemma 3.2.7: a factorization `A = Bᴴ B` rewrites the quadratic form of `A`
as the Euclidean norm of `B x`. -/
private theorem sqrt_inner_eq_euclidean_image_norm
    (A B : Mat) (hAeq : A = Bᴴ * B) (x : E) :
    Real.sqrt (inner ℝ (A.toEuclideanLin x) x) = ‖B.toEuclideanLin x‖ := by
  -- Rewrite the quadratic form in coordinates and collapse it to a squared Euclidean norm.
  have hquad : inner ℝ (A.toEuclideanLin x) x = ‖B.toEuclideanLin x‖ ^ 2 := by
    calc
      inner ℝ (A.toEuclideanLin x) x = dotProduct x.ofLp (A *ᵥ x.ofLp) := by
        simpa only [Matrix.ofLp_toLpLin] using
          (EuclideanSpace.inner_eq_star_dotProduct (A.toEuclideanLin x) x)
      _ = dotProduct x.ofLp ((Bᴴ * B) *ᵥ x.ofLp) := by
        rw [hAeq]
      _ = dotProduct (B *ᵥ x.ofLp) (B *ᵥ x.ofLp) := by
        rw [dotProduct_comm]
        rw [dotProduct_comm, ← mulVec_mulVec, dotProduct_mulVec, vecMul_conjTranspose]
        simp
      _ = ‖B.toEuclideanLin x‖ ^ 2 := by
        have hraw :=
          EuclideanSpace.inner_eq_star_dotProduct (B.toEuclideanLin x) (B.toEuclideanLin x)
        simp only [Matrix.ofLp_toLpLin] at hraw
        have hnorm : inner ℝ (B.toEuclideanLin x) (B.toEuclideanLin x) =
            ‖B.toEuclideanLin x‖ ^ 2 := by
          simp
        exact hraw.symm.trans hnorm
  rw [hquad, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

/-- Helper for Lemma 3.2.7: the rank-one matrix `ggᵀ` contributes exactly the square of the
pairing `⟪g, z⟫`. -/
private theorem vecMulVec_quadratic (g z : E) :
    inner ℝ ((Matrix.vecMulVec g g).toEuclideanLin z) z = (inner ℝ g z) ^ (2 : ℕ) := by
  -- The outer product acts by sending `z` to `⟪g, z⟫ g`.
  have hmul : ((Matrix.vecMulVec g g).toEuclideanLin z).ofLp = (inner ℝ g z) • g.ofLp := by
    have hinner : inner ℝ g z = g.ofLp ⬝ᵥ z.ofLp := by
      have hraw := EuclideanSpace.inner_eq_star_dotProduct g z
      simpa [dotProduct_comm] using hraw
    simp [Matrix.ofLp_toLpLin, Matrix.vecMulVec_mulVec, hinner]
  have hin : ((Matrix.vecMulVec g g).toEuclideanLin z) = (inner ℝ g z) • g := by
    ext i
    simpa using congrArg (fun v : Fin n → ℝ ↦ v i) hmul
  calc
    inner ℝ ((Matrix.vecMulVec g g).toEuclideanLin z) z = inner ℝ ((inner ℝ g z) • g) z := by
      rw [hin]
    _ = (inner ℝ g z) * inner ℝ g z := by
      simp [real_inner_smul_left]
    _ = (inner ℝ g z) ^ (2 : ℕ) := by
      ring

/-- Helper for Lemma 3.2.7: the updated matrix has the explicit Woodbury inverse from the
textbook proof. -/
private theorem updatedEllipsoidMatrix_inv_formula
    (H : Mat) (hH : H.PosDef) (g : E) (hg : g ≠ 0) (hn : 1 < n) :
    (H₊(H, g))⁻¹ =
      ((((n : ℝ) ^ (2 : ℕ)) - 1) / ((n : ℝ) ^ (2 : ℕ))) •
        (H⁻¹ + ((((2 : ℝ) / ((n : ℝ) - 1)) / inner ℝ (H.toEuclideanLin g) g)) •
          Matrix.vecMulVec g g) := by
  -- Route correction: instead of reopening the `Fin 1` Woodbury interface, verify the displayed
  -- candidate directly as a right inverse of the rank-one update.
  let q : ℝ := inner ℝ (H.toEuclideanLin g) g
  let β : ℝ := (((2 : ℝ) / ((n : ℝ) + 1)) / q)
  let γ : ℝ := (((2 : ℝ) / ((n : ℝ) - 1)) / q)
  let α : ℝ := (((n : ℝ) ^ (2 : ℕ)) / (((n : ℝ) ^ (2 : ℕ)) - 1))
  let c : ℝ := ((((n : ℝ) ^ (2 : ℕ)) - 1) / ((n : ℝ) ^ (2 : ℕ)))
  let Hg : E := H.toEuclideanLin g
  let K : Mat := H - β • Matrix.vecMulVec Hg Hg
  let B : Mat := H⁻¹ + γ • Matrix.vecMulVec g g
  have hq_pos : 0 < q := by
    simpa [q] using ellipsoidUpdate_quadratic_pos H hH hg
  have hn_real : (1 : ℝ) < n := by
    exact_mod_cast hn
  have hαc : α * c = 1 := by
    have hsq_ne : ((n : ℝ) ^ (2 : ℕ)) ≠ 0 := by
      positivity
    have hsq_sub_ne : (((n : ℝ) ^ (2 : ℕ)) - 1) ≠ 0 := by
      nlinarith
    dsimp [α, c]
    field_simp [hsq_ne, hsq_sub_ne]
  have hcore : K * B = 1 := by
    have hHdet : IsUnit H.det := isUnit_iff_ne_zero.mpr (ne_of_gt hH.det_pos)
    have hrowH : g.ofLp ᵥ* H = Hg.ofLp := by
      have hsymm : Hᵀ = H := by
        simpa [Hg] using hH.isHermitian.eq
      simpa [Hg, Matrix.ofLp_toLpLin, hsymm] using (Matrix.vecMul_transpose Hᵀ g.ofLp)
    have hrowInv : Hg.ofLp ᵥ* H⁻¹ = g.ofLp := by
      have hsymm : (H⁻¹)ᵀ = H⁻¹ := by
        simpa [Hg] using hH.inv.isHermitian.eq
      calc
        Hg.ofLp ᵥ* H⁻¹ = ((H⁻¹).toEuclideanLin Hg).ofLp := by
          simpa [Hg, Matrix.ofLp_toLpLin, hsymm] using
            (Matrix.vecMul_transpose (H⁻¹)ᵀ Hg.ofLp)
        _ = g.ofLp := by
          ext i
          simpa [Hg] using congrArg (fun v : E ↦ v i) (nonsing_inv_toEuclideanLin_comp H hH g)
    have hdot : g.ofLp ⬝ᵥ Hg.ofLp = q := by
      have hinner := EuclideanSpace.inner_eq_star_dotProduct g Hg
      calc
        g.ofLp ⬝ᵥ Hg.ofLp = inner ℝ g Hg := by
          simpa [dotProduct_comm] using hinner.symm
        _ = q := by
          simp [Hg, q, real_inner_comm]
    have hcore' :
        K * B = 1 + (γ - β - β * γ * q) • Matrix.vecMulVec Hg g := by
      have hmul₁ : H * (γ • Matrix.vecMulVec g g) = γ • Matrix.vecMulVec Hg g := by
        rw [Matrix.mul_smul, Matrix.mul_vecMulVec]
        simp [Hg]
      have hmul₂ : (β • Matrix.vecMulVec Hg Hg) * H⁻¹ = β • Matrix.vecMulVec Hg g := by
        rw [smul_mul_assoc, Matrix.vecMulVec_mul, hrowInv]
      have hmul₃ :
          (β • Matrix.vecMulVec Hg Hg) * (γ • Matrix.vecMulVec g g) =
            (β * γ * q) • Matrix.vecMulVec Hg g := by
        have hdot' : Hg.ofLp ⬝ᵥ g.ofLp = q := by
          simpa [dotProduct_comm] using hdot
        rw [smul_mul_assoc, mul_smul_comm, Matrix.vecMulVec_mul_vecMulVec, hdot']
        simp [smul_smul, mul_assoc]
      calc
        K * B
            = H * H⁻¹ + H * (γ • Matrix.vecMulVec g g)
                - (β • Matrix.vecMulVec Hg Hg) * H⁻¹
                - (β • Matrix.vecMulVec Hg Hg) * (γ • Matrix.vecMulVec g g) := by
                  dsimp [K, B]
                  rw [sub_mul, mul_add, mul_add]
                  abel
        _ = 1 + γ • Matrix.vecMulVec Hg g
                - β • Matrix.vecMulVec Hg g
                - (β * γ * q) • Matrix.vecMulVec Hg g := by
                  rw [Matrix.mul_nonsing_inv H hHdet, hmul₁, hmul₂, hmul₃]
        _ = 1 + (γ - β - β * γ * q) • Matrix.vecMulVec Hg g := by
          ext i j
          simp [sub_eq_add_neg]
          ring
    have hcoef : γ - β - β * γ * q = 0 := by
      have hq_ne : q ≠ 0 := ne_of_gt hq_pos
      have hnm1_ne : ((n : ℝ) - 1) ≠ 0 := by
        linarith
      have hnp1_ne : ((n : ℝ) + 1) ≠ 0 := by
        positivity
      dsimp [β, γ]
      field_simp [hq_ne, hnm1_ne, hnp1_ne]
      ring
    rw [hcore', hcoef, zero_smul, add_zero]
  have hright : H₊(H, g) * (c • B) = 1 := by
    calc
      H₊(H, g) * (c • B)
          = (α • K) * (c • B) := by
              simp [updatedEllipsoidMatrix, α, β, q, Hg, K]
      _ = (α * c) • (K * B) := by
        rw [smul_mul_smul]
      _ = 1 := by
        simp [hαc, hcore]
  simpa [c, B, γ] using (inv_eq_right_inv hright : (H₊(H, g))⁻¹ = c • B)

/-- Helper for Lemma 3.2.7: the inverse formula implies that the updated matrix is still positive
definite. -/
private theorem updatedEllipsoidMatrix_posDef
    (H : Mat) (hH : H.PosDef) (g : E) (hg : g ≠ 0) (hn : 1 < n) :
    (H₊(H, g)).PosDef := by
  -- The inverse formula exhibits `H₊⁻¹` as a positive scalar multiple of a positive-definite
  -- matrix plus a positive-semidefinite rank-one correction.
  have hInv :
      (H₊(H, g))⁻¹ =
        ((((n : ℝ) ^ (2 : ℕ)) - 1) / ((n : ℝ) ^ (2 : ℕ))) •
          (H⁻¹ + ((((2 : ℝ) / ((n : ℝ) - 1)) / inner ℝ (H.toEuclideanLin g) g)) •
            Matrix.vecMulVec g g) :=
    updatedEllipsoidMatrix_inv_formula H hH g hg hn
  have hn_real : (1 : ℝ) < n := by
    exact_mod_cast hn
  have hnm1_pos : 0 < (n : ℝ) - 1 := by
    linarith
  have hq_pos : 0 < inner ℝ (H.toEuclideanLin g) g := by
    exact ellipsoidUpdate_quadratic_pos H hH hg
  have hgamma_nonneg :
      0 ≤ (((2 : ℝ) / ((n : ℝ) - 1)) / inner ℝ (H.toEuclideanLin g) g) := by
    positivity
  have hsum_pos :
      (H⁻¹ + ((((2 : ℝ) / ((n : ℝ) - 1)) / inner ℝ (H.toEuclideanLin g) g)) •
        Matrix.vecMulVec g g).PosDef := by
    -- Add the positive-semidefinite rank-one term to the positive-definite inverse `H⁻¹`.
    exact hH.inv.add_posSemidef ((Matrix.posSemidef_vecMulVec_self_star g).smul hgamma_nonneg)
  have hscale_pos :
      0 < ((((n : ℝ) ^ (2 : ℕ)) - 1) / ((n : ℝ) ^ (2 : ℕ))) := by
    have hsq_pos : 0 < (n : ℝ) ^ (2 : ℕ) := by
      positivity
    have hsq_sub_pos : 0 < (n : ℝ) ^ (2 : ℕ) - 1 := by
      nlinarith
    positivity
  have hInvPos : (H₊(H, g))⁻¹.PosDef := by
    rw [hInv]
    exact hsum_pos.smul hscale_pos
  exact Matrix.posDef_inv_iff.mp hInvPos

/-- Helper for Lemma 3.2.7: the determinant of the updated matrix has the explicit ratio from the
textbook proof. -/
private theorem updatedEllipsoidMatrix_det_ratio
    (H : Mat) (hH : H.PosDef) (g : E) (hg : g ≠ 0) (hn : 1 < n) :
    (H₊(H, g)).det =
      ((((n : ℝ) ^ (2 : ℕ)) / (((n : ℝ) ^ (2 : ℕ)) - 1)) ^ n) *
        (((n : ℝ) - 1) / ((n : ℝ) + 1)) * H.det := by
  let q : ℝ := inner ℝ (H.toEuclideanLin g) g
  let β : ℝ := (((2 : ℝ) / ((n : ℝ) + 1)) / q)
  let α : ℝ := (((n : ℝ) ^ (2 : ℕ)) / (((n : ℝ) ^ (2 : ℕ)) - 1))
  let Hg : E := H.toEuclideanLin g
  have hq_pos : 0 < q := by
    simpa [q] using ellipsoidUpdate_quadratic_pos H hH hg
  have hHdet : IsUnit H.det := isUnit_iff_ne_zero.mpr (ne_of_gt hH.det_pos)
  have hrowInv : Hg.ofLp ᵥ* H⁻¹ = g.ofLp := by
    have hsymm : (H⁻¹)ᵀ = H⁻¹ := by
      simpa [Hg] using hH.inv.isHermitian.eq
    calc
      Hg.ofLp ᵥ* H⁻¹ = ((H⁻¹).toEuclideanLin Hg).ofLp := by
        simpa [Hg, Matrix.ofLp_toLpLin, hsymm] using
          (Matrix.vecMul_transpose (H⁻¹)ᵀ Hg.ofLp)
      _ = g.ofLp := by
        ext i
        simpa [Hg] using congrArg (fun v : E ↦ v i) (nonsing_inv_toEuclideanLin_comp H hH g)
  have hrowMul :
      Matrix.replicateRow (Fin 1) Hg * H⁻¹ = Matrix.replicateRow (Fin 1) g := by
    ext i j
    fin_cases i
    simpa [Matrix.mul_apply] using congrArg (fun v : Fin n → ℝ ↦ v j) hrowInv
  have hdot : g.ofLp ⬝ᵥ Hg.ofLp = q := by
    have hinner := EuclideanSpace.inner_eq_star_dotProduct g Hg
    calc
      g.ofLp ⬝ᵥ Hg.ofLp = inner ℝ g Hg := by
        simpa [dotProduct_comm] using hinner.symm
      _ = q := by
        simp [Hg, q, real_inner_comm]
  have hdecay :
      (1 + Matrix.replicateRow (Fin 1) Hg * H⁻¹ * Matrix.replicateCol (Fin 1) (-(β • Hg))).det =
        (((n : ℝ) - 1) / ((n : ℝ) + 1)) := by
    -- Collapse the `1 × 1` correction term to the scalar `1 - β q = (n - 1)/(n + 1)`.
    have hcore :
        Matrix.replicateRow (Fin 1) Hg * H⁻¹ * Matrix.replicateCol (Fin 1) (-(β • Hg)) =
          !![-β * q] := by
      rw [hrowMul]
      ext i j
      fin_cases i
      fin_cases j
      rw [Matrix.replicateRow_mul_replicateCol_apply]
      simp [q, hdot]
    rw [hcore, Matrix.det_fin_one]
    simp
    dsimp [β]
    field_simp [q, show ((n : ℝ) + 1) ≠ 0 by positivity, show q ≠ 0 by linarith]
    ring
  have hcoreEq :
      H - β • Matrix.vecMulVec Hg Hg =
        H + Matrix.replicateCol (Fin 1) (-(β • Hg)) * Matrix.replicateRow (Fin 1) Hg := by
    ext i j
    simp [β, Hg, Matrix.vecMulVec_eq (Fin 1), Matrix.mul_apply, sub_eq_add_neg]
    ring
  -- Rewrite `H₊` as a scalar multiple of the rank-one perturbation and apply the matrix
  -- determinant lemma to the unscaled core.
  calc
    (H₊(H, g)).det
        = α ^ n * (H + Matrix.replicateCol (Fin 1) (-(β • Hg)) * Matrix.replicateRow (Fin 1) Hg).det := by
            rw [updatedEllipsoidMatrix, hcoreEq, Matrix.det_smul]
            simp [α]
    _ = α ^ n * (H.det * (1 + Matrix.replicateRow (Fin 1) Hg * H⁻¹ *
          Matrix.replicateCol (Fin 1) (-(β • Hg))).det) := by
          congr 1
          simpa using
            (Matrix.det_add_replicateCol_mul_replicateRow (ι := Fin 1)
              (A := H) hHdet (-(β • Hg)).ofLp Hg.ofLp)
    _ = α ^ n * (H.det * (((n : ℝ) - 1) / ((n : ℝ) + 1))) := by
          rw [hdecay]
    _ = ((((n : ℝ) ^ (2 : ℕ)) / (((n : ℝ) ^ (2 : ℕ)) - 1)) ^ n) *
          (((n : ℝ) - 1) / ((n : ℝ) + 1)) * H.det := by
          rw [mul_assoc]
          congr 1
          ring

/-- Helper for Lemma 3.2.7: the volume of a positive-definite affine ellipsoid is `√det(H)` times
the volume of the unit closed ball. -/
private theorem affineEllipsoid_volume_eq_sqrt_det_mul_closedBall
    (H : Mat) (xBar : E) (hH : H.PosDef) :
    (volume (E(H, xBar))).toReal =
      Real.sqrt H.det * (volume (Metric.closedBall (0 : E) 1)).toReal := by
  obtain ⟨B, hBunit, hBself, hfactor⟩ :=
    (CStarAlgebra.isStrictlyPositive_iff_exists_isUnit_and_isSelfAdjoint_and_eq_mul_self).mp
      hH.isStrictlyPositive
  have htranslate : E(H, xBar) = (fun y : E ↦ y + (-xBar)) ⁻¹' E(H, (0 : E)) := by
    -- Translation reduces the general ellipsoid to the centered one.
    ext y
    simpa [affineEllipsoid, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  have hInvFactor : H⁻¹ = B⁻¹ᴴ * B⁻¹ := by
    -- Inverting `H = B * B` gives the quadratic form needed for the preimage description.
    calc
      H⁻¹ = (B * B)⁻¹ := by
        rw [hfactor]
      _ = B⁻¹ * B⁻¹ := by
        rw [Matrix.mul_inv_rev]
      _ = B⁻¹ᴴ * B⁻¹ := by
        congr 1
        rw [Matrix.conjTranspose_nonsing_inv]
        simpa using congrArg Inv.inv hBself.symm
  have hzero : E(H, (0 : E)) = ((B⁻¹).toEuclideanLin) ⁻¹' Metric.closedBall (0 : E) 1 := by
    -- The centered ellipsoid is exactly the inverse image of the unit ball under `B⁻¹`.
    ext y
    simp [affineEllipsoid, Set.preimage, Metric.mem_closedBall, dist_eq_norm]
    have hsqrt := sqrt_inner_eq_euclidean_image_norm H⁻¹ B⁻¹ hInvFactor y
    constructor
    · intro hy
      have hsqrt_le : Real.sqrt (inner ℝ ((H⁻¹).toEuclideanLin y) y) ≤ 1 := by
        have h' : 0 ≤ (1 : ℝ) ∧ inner ℝ ((H⁻¹).toEuclideanLin y) y ≤ 1 ^ (2 : ℕ) := by
          simpa using hy
        exact (Real.sqrt_le_iff).2 h'
      simpa [hsqrt] using hsqrt_le
    · intro hy
      have hsqrt_le : Real.sqrt (inner ℝ ((H⁻¹).toEuclideanLin y) y) ≤ 1 := by
        simpa [hsqrt] using hy
      simpa using (Real.sqrt_le_iff.1 hsqrt_le).2
  have hdetLinInv : LinearMap.det ((B⁻¹).toEuclideanLin : E →ₗ[ℝ] E) = (B.det)⁻¹ := by
    -- Identify the determinant of the Euclidean linear map with the determinant of its matrix.
    calc
      LinearMap.det ((B⁻¹).toEuclideanLin : E →ₗ[ℝ] E) = (B⁻¹).det := by
        simpa [Matrix.toEuclideanLin_eq_toLin_orthonormal] using
          (LinearMap.det_toMatrix ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis)
            ((B⁻¹).toEuclideanLin : E →ₗ[ℝ] E)).symm
      _ = (B.det)⁻¹ := by
        simpa using (Matrix.det_nonsing_inv B)
  have hBdet : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).mp hBunit
  have hdetLinInv_ne : LinearMap.det ((B⁻¹).toEuclideanLin : E →ₗ[ℝ] E) ≠ 0 := by
    rw [hdetLinInv]
    exact inv_ne_zero hBdet.ne_zero
  have hdetBabs : |B.det| = Real.sqrt H.det := by
    rw [hfactor, Matrix.det_mul]
    simpa [pow_two, mul_comm] using (Real.sqrt_sq_eq_abs B.det).symm
  calc
    (volume (E(H, xBar))).toReal =
        (volume ((fun y : E ↦ y + (-xBar)) ⁻¹' E(H, (0 : E)))).toReal := by
          rw [htranslate]
    _ = (volume (E(H, (0 : E)))).toReal := by
      rw [MeasureTheory.measure_preimage_add_right volume (-xBar) (E(H, (0 : E)))]
    _ = (volume (((B⁻¹).toEuclideanLin) ⁻¹' Metric.closedBall (0 : E) 1)).toReal := by
      rw [hzero]
    _ =
        (ENNReal.ofReal |(LinearMap.det ((B⁻¹).toEuclideanLin : E →ₗ[ℝ] E))⁻¹| *
          volume (Metric.closedBall (0 : E) 1)).toReal := by
            rw [MeasureTheory.Measure.addHaar_preimage_linearMap volume hdetLinInv_ne]
    _ = |(LinearMap.det ((B⁻¹).toEuclideanLin : E →ₗ[ℝ] E))⁻¹| *
          (volume (Metric.closedBall (0 : E) 1)).toReal := by
            rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal]
            simp
    _ = |B.det| * (volume (Metric.closedBall (0 : E) 1)).toReal := by
      have hdet_abs : |(LinearMap.det ((B⁻¹).toEuclideanLin : E →ₗ[ℝ] E))⁻¹| = |B.det| := by
        rw [hdetLinInv]
        simp
      rw [hdet_abs]
    _ = Real.sqrt H.det * (volume (Metric.closedBall (0 : E) 1)).toReal := by
      rw [hdetBabs]

/-- Helper for Lemma 3.2.7: the exact determinant ratio is bounded by the standard decay factor. -/
private theorem updatedEllipsoid_detRatio_le_decayFactor
    (hn : 1 < n) :
    Real.sqrt ((((n : ℝ) ^ (2 : ℕ) / (((n : ℝ) ^ (2 : ℕ)) - 1)) ^ n) *
      (((n : ℝ) - 1) / ((n : ℝ) + 1))) ≤
      Real.rpow (1 - 1 / (((n : ℝ) + 1) ^ (2 : ℕ))) ((n : ℝ) / 2) := by
  let base : ℝ := 1 - 1 / (((n : ℝ) + 1) ^ (2 : ℕ))
  let a : ℝ := 1 - 2 / ((n : ℝ) * ((n : ℝ) + 1))
  let c : ℝ := ((n : ℝ) ^ (2 : ℕ)) / (((n : ℝ) ^ (2 : ℕ)) - 1)
  have hpow_pos : 0 < (((n : ℝ) + 1) ^ (2 : ℕ)) := by
    positivity
  have hpow_ge_one : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ (2 : ℕ) := by
    have hn_nonneg : (0 : ℝ) ≤ n := by
      exact_mod_cast Nat.zero_le n
    nlinarith
  have hbase_nonneg : 0 ≤ base := by
    have h_inv_le : 1 / (((n : ℝ) + 1) ^ (2 : ℕ)) ≤ (1 : ℝ) := by
      refine (div_le_iff₀ hpow_pos).2 ?_
      simpa using hpow_ge_one
    dsimp [base]
    nlinarith
  have hc0 : 0 ≤ c := by
    dsimp [c]
    have : 0 < ((n : ℝ) ^ (2 : ℕ)) - 1 := by
      nlinarith [show (1 : ℝ) < n by exact_mod_cast hn]
    positivity
  have hc_nonneg : 0 ≤ c ^ n := pow_nonneg hc0 _
  have haux : -2 ≤ (-2 / ((n : ℝ) * ((n : ℝ) + 1))) := by
    have hm : 1 ≤ (n : ℝ) * ((n : ℝ) + 1) := by
      nlinarith [show (1 : ℝ) < n by exact_mod_cast hn]
    have hm_pos : 0 < (n : ℝ) * ((n : ℝ) + 1) := by
      positivity
    refine (le_div_iff₀ hm_pos).2 ?_
    nlinarith
  have hpow := one_add_mul_le_pow haux n
  have hlin : ((n : ℝ) - 1) / ((n : ℝ) + 1) =
      1 + (n : ℝ) * (-2 / ((n : ℝ) * ((n : ℝ) + 1))) := by
    have hn_ne : (n : ℝ) ≠ 0 := by
      nlinarith [show (1 : ℝ) < n by exact_mod_cast hn]
    have hnp1_ne : ((n : ℝ) + 1) ≠ 0 := by
      nlinarith
    field_simp [hn_ne, hnp1_ne]
    ring
  have hbernoulli : ((n : ℝ) - 1) / ((n : ℝ) + 1) ≤ a ^ n := by
    -- Bernoulli gives the scalar decay estimate used in the textbook.
    calc
      ((n : ℝ) - 1) / ((n : ℝ) + 1) = 1 + (n : ℝ) * (-2 / ((n : ℝ) * ((n : ℝ) + 1))) := hlin
      _ ≤ (1 + -2 / ((n : ℝ) * ((n : ℝ) + 1))) ^ n := hpow
      _ = a ^ n := by
        congr 1
        ring
  have hratio_le : c ^ n * (((n : ℝ) - 1) / ((n : ℝ) + 1)) ≤ base ^ n := by
    have hmul := mul_le_mul_of_nonneg_left hbernoulli hc_nonneg
    have hident : c * a = base := by
      dsimp [a, c, base]
      have hn_sq_ne : ((n : ℝ) ^ (2 : ℕ)) - 1 ≠ 0 := by
        nlinarith [show (1 : ℝ) < n by exact_mod_cast hn]
      have hn_ne : (n : ℝ) ≠ 0 := by
        nlinarith [show (1 : ℝ) < n by exact_mod_cast hn]
      have hnp1_ne : ((n : ℝ) + 1) ≠ 0 := by
        nlinarith
      field_simp [hn_sq_ne, hn_ne, hnp1_ne]
      ring
    calc
      c ^ n * (((n : ℝ) - 1) / ((n : ℝ) + 1)) ≤ c ^ n * a ^ n := hmul
      _ = (c * a) ^ n := by rw [← mul_pow]
      _ = base ^ n := by rw [hident]
  have hsqrt := Real.sqrt_le_sqrt hratio_le
  have hrpow : Real.rpow base ((n : ℝ) / 2) = Real.sqrt (base ^ n) := by
    calc
      Real.rpow base ((n : ℝ) / 2) = Real.rpow base ((n : ℝ) * (1 / 2 : ℝ)) := by
        congr
        ring
      _ = Real.rpow (Real.rpow base (n : ℝ)) (1 / 2 : ℝ) := by
        simpa using (Real.rpow_mul hbase_nonneg (n : ℝ) (1 / 2 : ℝ))
      _ = Real.rpow (base ^ n) (1 / 2 : ℝ) := by
        simpa using congrArg (fun t : ℝ ↦ Real.rpow t (1 / 2 : ℝ)) (Real.rpow_natCast base n)
      _ = Real.sqrt (base ^ n) := by
        simpa using (Real.sqrt_eq_rpow (base ^ n)).symm
  calc
    Real.sqrt ((((n : ℝ) ^ (2 : ℕ) / (((n : ℝ) ^ (2 : ℕ)) - 1)) ^ n) *
        (((n : ℝ) - 1) / ((n : ℝ) + 1))) ≤ Real.sqrt (base ^ n) := hsqrt
    _ = Real.rpow base ((n : ℝ) / 2) := hrpow.symm
    _ = Real.rpow (1 - 1 / (((n : ℝ) + 1) ^ (2 : ℕ))) ((n : ℝ) / 2) := by
      rfl

/-- Helper for Lemma 3.2.7: shifting by the updated center adds the normalized `⟪H g, g⟫`
term to the cut pairing. -/
private theorem shifted_cut_pairing_eq
    (H : Mat) (g y : E) (δ : ℝ) :
    inner ℝ g (y + δ • H.toEuclideanLin g) =
      inner ℝ g y + δ * inner ℝ (H.toEuclideanLin g) g := by
  -- Expand the shifted pairing once so the main proof can work with the normalized scalar `u`.
  calc
    inner ℝ g (y + δ • H.toEuclideanLin g)
      = inner ℝ g y + inner ℝ g (δ • H.toEuclideanLin g) := by
          rw [inner_add_right]
    _ = inner ℝ g y + δ * inner ℝ g (H.toEuclideanLin g) := by
          rw [inner_smul_right]
    _ = inner ℝ g y + δ * inner ℝ (H.toEuclideanLin g) g := by
          rw [show inner ℝ g (H.toEuclideanLin g) = inner ℝ (H.toEuclideanLin g) g by
            rw [real_inner_comm]]

/-- Helper for Lemma 3.2.7: shifting by the updated center expands the original quadratic form
into the old quadratic term plus the two textbook correction terms. -/
private theorem shifted_inverse_quadratic_eq
    (H : Mat) (hH : H.PosDef) (g y : E) (δ : ℝ) :
    inner ℝ ((H⁻¹).toEuclideanLin (y + δ • H.toEuclideanLin g)) (y + δ • H.toEuclideanLin g) =
      inner ℝ ((H⁻¹).toEuclideanLin y) y + 2 * δ * inner ℝ g y +
        δ ^ (2 : ℕ) * inner ℝ (H.toEuclideanLin g) g := by
  have hsymm : (matrixBilin H⁻¹).IsSymm :=
    (LinearMap.BilinForm.isSymm_iff).2 (matrixBilin_isSymm_of_posDef H⁻¹ hH.inv)
  have hcross :
      inner ℝ ((H⁻¹).toEuclideanLin y) (H.toEuclideanLin g) = inner ℝ g y := by
    -- Symmetry moves the inverse off `y`, and then `H⁻¹ (H g) = g`.
    calc
      inner ℝ ((H⁻¹).toEuclideanLin y) (H.toEuclideanLin g)
          = matrixBilin H⁻¹ y (H.toEuclideanLin g) := by
              rfl
      _ = matrixBilin H⁻¹ (H.toEuclideanLin g) y := by
            exact hsymm.eq _ _
      _ = inner ℝ ((H⁻¹).toEuclideanLin (H.toEuclideanLin g)) y := by
            rfl
      _ = inner ℝ g y := by
            rw [nonsing_inv_toEuclideanLin_comp H hH]
  -- Expand the quadratic form after the shift and identify the mixed terms.
  calc
    inner ℝ ((H⁻¹).toEuclideanLin (y + δ • H.toEuclideanLin g)) (y + δ • H.toEuclideanLin g)
      = inner ℝ (((H⁻¹).toEuclideanLin y) + δ • g) (y + δ • H.toEuclideanLin g) := by
          rw [LinearMap.map_add, LinearMap.map_smul, nonsing_inv_toEuclideanLin_comp H hH]
    _ = inner ℝ ((H⁻¹).toEuclideanLin y) y +
          inner ℝ ((H⁻¹).toEuclideanLin y) (δ • H.toEuclideanLin g) +
          (inner ℝ (δ • g) y + inner ℝ (δ • g) (δ • H.toEuclideanLin g)) := by
            rw [inner_add_left, inner_add_right, inner_add_right]
    _ = inner ℝ ((H⁻¹).toEuclideanLin y) y +
          δ * inner ℝ ((H⁻¹).toEuclideanLin y) (H.toEuclideanLin g) +
          (δ * inner ℝ g y + δ * (δ * inner ℝ g (H.toEuclideanLin g))) := by
            rw [inner_smul_right, inner_smul_left, inner_smul_left, inner_smul_right]
            simp
    _ = inner ℝ ((H⁻¹).toEuclideanLin y) y +
          δ * inner ℝ g y +
          (δ * inner ℝ g y + δ * (δ * inner ℝ g (H.toEuclideanLin g))) := by
            rw [hcross]
    _ = inner ℝ ((H⁻¹).toEuclideanLin y) y + 2 * δ * inner ℝ g y +
          δ ^ (2 : ℕ) * inner ℝ (H.toEuclideanLin g) g := by
            rw [show inner ℝ g (H.toEuclideanLin g) = inner ℝ (H.toEuclideanLin g) g by
              rw [real_inner_comm]]
            ring_nf

/-- Helper for Lemma 3.2.7: after shifting to the updated center, the updated quadratic form
matches the textbook scalar expression controlled by `center_cut_update_scalar_bound`. -/
private theorem updated_shifted_quadratic_eq
    (H : Mat) (hH : H.PosDef) (g y : E) (hg : g ≠ 0) (hn : 1 < n)
    (q δ u t : ℝ)
    (hq : q = inner ℝ (H.toEuclideanLin g) g)
    (hδ : δ = ((n : ℝ) + 1)⁻¹ * (Real.sqrt q)⁻¹)
    (hu : u = (Real.sqrt q)⁻¹ * inner ℝ g y)
    (ht : t = inner ℝ ((H⁻¹).toEuclideanLin y) y) :
    inner ℝ (((H₊(H, g))⁻¹).toEuclideanLin (y + δ • H.toEuclideanLin g))
      (y + δ • H.toEuclideanLin g) =
      ((((n : ℝ) ^ (2 : ℕ)) - 1) / ((n : ℝ) ^ (2 : ℕ))) *
        (t + (2 / ((n : ℝ) - 1)) * (u ^ (2 : ℕ) + u) +
          1 / (((n : ℝ) ^ (2 : ℕ)) - 1)) := by
  subst q δ u t
  have hq_pos : 0 < inner ℝ (H.toEuclideanLin g) g := ellipsoidUpdate_quadratic_pos H hH hg
  have hq_ne : inner ℝ (H.toEuclideanLin g) g ≠ 0 := ne_of_gt hq_pos
  have hsqrt_pos : 0 < Real.sqrt (inner ℝ (H.toEuclideanLin g) g) := Real.sqrt_pos.2 hq_pos
  have hsqrt_ne : Real.sqrt (inner ℝ (H.toEuclideanLin g) g) ≠ 0 := ne_of_gt hsqrt_pos
  have hn_real : (1 : ℝ) < n := by
    exact_mod_cast hn
  have hnm1_ne : (n : ℝ) - 1 ≠ 0 := by
    linarith
  have hnp1_ne : (n : ℝ) + 1 ≠ 0 := by
    positivity
  have hsq_sub_ne : ((n : ℝ) ^ (2 : ℕ)) - 1 ≠ 0 := by
    nlinarith
  have hscale_apply
      (A : Mat) (z : E) (c : ℝ) :
      ((c • A).toEuclideanLin z) = c • (A.toEuclideanLin z) := by
    ext i
    simp [Matrix.toEuclideanLin_apply, Matrix.smul_mulVec]
  have hadd_apply
      (A B : Mat) (z : E) :
      ((A + B).toEuclideanLin z) = A.toEuclideanLin z + B.toEuclideanLin z := by
    ext i
    simp [Matrix.toEuclideanLin_apply, Matrix.add_mulVec]
  -- Rewrite the updated inverse form into the shifted old quadratic term plus the rank-one term.
  calc
    inner ℝ
        (((H₊(H, g))⁻¹).toEuclideanLin
          (y + (((n : ℝ) + 1)⁻¹ * (Real.sqrt (inner ℝ (H.toEuclideanLin g) g))⁻¹) •
            H.toEuclideanLin g))
        (y + (((n : ℝ) + 1)⁻¹ * (Real.sqrt (inner ℝ (H.toEuclideanLin g) g))⁻¹) •
          H.toEuclideanLin g)
      =
        ((((n : ℝ) ^ (2 : ℕ)) - 1) / ((n : ℝ) ^ (2 : ℕ))) *
          (inner ℝ
            ((H⁻¹).toEuclideanLin
              (y + (((n : ℝ) + 1)⁻¹ * (Real.sqrt (inner ℝ (H.toEuclideanLin g) g))⁻¹) •
                H.toEuclideanLin g))
            (y + (((n : ℝ) + 1)⁻¹ * (Real.sqrt (inner ℝ (H.toEuclideanLin g) g))⁻¹) •
              H.toEuclideanLin g) +
            ((((2 : ℝ) / ((n : ℝ) - 1)) / inner ℝ (H.toEuclideanLin g) g) *
              inner ℝ
                ((Matrix.vecMulVec g g).toEuclideanLin
                  (y + (((n : ℝ) + 1)⁻¹ * (Real.sqrt (inner ℝ (H.toEuclideanLin g) g))⁻¹) •
                    H.toEuclideanLin g))
                (y + (((n : ℝ) + 1)⁻¹ * (Real.sqrt (inner ℝ (H.toEuclideanLin g) g))⁻¹) •
                  H.toEuclideanLin g))) := by
          rw [updatedEllipsoidMatrix_inv_formula H hH g hg hn]
          rw [hscale_apply]
          rw [inner_smul_left]
          rw [hadd_apply]
          rw [inner_add_left]
          rw [hscale_apply]
          rw [inner_smul_left]
          simp
    _ =
        ((((n : ℝ) ^ (2 : ℕ)) - 1) / ((n : ℝ) ^ (2 : ℕ))) *
          (inner ℝ ((H⁻¹).toEuclideanLin y) y +
            2 * ((((n : ℝ) + 1)⁻¹ * (Real.sqrt (inner ℝ (H.toEuclideanLin g) g))⁻¹)) *
              inner ℝ g y +
            ((((n : ℝ) + 1)⁻¹ * (Real.sqrt (inner ℝ (H.toEuclideanLin g) g))⁻¹) ^ (2 : ℕ)) *
              inner ℝ (H.toEuclideanLin g) g +
            ((((2 : ℝ) / ((n : ℝ) - 1)) / inner ℝ (H.toEuclideanLin g) g) *
              (inner ℝ g y +
                (((n : ℝ) + 1)⁻¹ * (Real.sqrt (inner ℝ (H.toEuclideanLin g) g))⁻¹) *
                  inner ℝ (H.toEuclideanLin g) g) ^ (2 : ℕ))) := by
          rw [shifted_inverse_quadratic_eq H hH g y
            ((((n : ℝ) + 1)⁻¹ * (Real.sqrt (inner ℝ (H.toEuclideanLin g) g))⁻¹))]
          rw [vecMulVec_quadratic]
          rw [shifted_cut_pairing_eq H g y
            ((((n : ℝ) + 1)⁻¹ * (Real.sqrt (inner ℝ (H.toEuclideanLin g) g))⁻¹))]
    _ =
        ((((n : ℝ) ^ (2 : ℕ)) - 1) / ((n : ℝ) ^ (2 : ℕ))) *
          (inner ℝ ((H⁻¹).toEuclideanLin y) y +
            (2 / ((n : ℝ) - 1)) *
              (((Real.sqrt (inner ℝ (H.toEuclideanLin g) g))⁻¹ * inner ℝ g y) ^ (2 : ℕ) +
                (Real.sqrt (inner ℝ (H.toEuclideanLin g) g))⁻¹ * inner ℝ g y) +
            1 / (((n : ℝ) ^ (2 : ℕ)) - 1)) := by
          set a : ℝ := inner ℝ g y with ha
          set s : ℝ := Real.sqrt (inner ℝ (H.toEuclideanLin g) g) with hs
          set r : ℝ := inner ℝ ((H⁻¹).toEuclideanLin y) y with hr
          have hs_ne : s ≠ 0 := by
            rw [hs]
            exact hsqrt_ne
          have hs_sq : s ^ (2 : ℕ) = inner ℝ (H.toEuclideanLin g) g := by
            rw [hs]
            exact Real.sq_sqrt hq_pos.le
          rw [hs_sq.symm]
          field_simp [hs_ne, hnm1_ne, hnp1_ne, hsq_sub_ne]
          ring_nf

/-- Helper for Lemma 3.2.7: the explicit determinant ratio transports directly to the stated
volume decay bound for the updated affine ellipsoid. -/
private theorem updated_affineEllipsoid_volume_le_decayFactor
    (H : Mat) (hH : H.PosDef) (xBar g : E) (hg : g ≠ 0) (hn : 1 < n) :
    (volume (E(H₊(H, g), x̄₊(H, xBar, g)))).toReal ≤
      Real.rpow (1 - 1 / (((n : ℝ) + 1) ^ (2 : ℕ))) ((n : ℝ) / 2) *
        (volume (E(H, xBar))).toReal := by
  have hHplus : (H₊(H, g)).PosDef := updatedEllipsoidMatrix_posDef H hH g hg hn
  have hvol_plus :=
    affineEllipsoid_volume_eq_sqrt_det_mul_closedBall
      (H₊(H, g)) (x̄₊(H, xBar, g)) hHplus
  have hvol :=
    affineEllipsoid_volume_eq_sqrt_det_mul_closedBall H xBar hH
  have hratio :=
    updatedEllipsoid_detRatio_le_decayFactor (n := n) hn
  have hdet_ratio :=
    updatedEllipsoidMatrix_det_ratio H hH g hg hn
  have hn_real : (1 : ℝ) < n := by
    exact_mod_cast hn
  have hratio_nonneg :
      0 ≤ ((((n : ℝ) ^ (2 : ℕ) / (((n : ℝ) ^ (2 : ℕ)) - 1)) ^ n) *
        (((n : ℝ) - 1) / ((n : ℝ) + 1))) := by
    have hpow_nonneg :
        0 ≤ (((n : ℝ) ^ (2 : ℕ) / (((n : ℝ) ^ (2 : ℕ)) - 1)) ^ n) := by
      have hbase_nonneg :
          0 ≤ ((n : ℝ) ^ (2 : ℕ) / (((n : ℝ) ^ (2 : ℕ)) - 1)) := by
        have hden_pos : 0 < (((n : ℝ) ^ (2 : ℕ)) - 1) := by
          nlinarith
        positivity
      exact pow_nonneg hbase_nonneg _
    have hfrac_nonneg : 0 ≤ (((n : ℝ) - 1) / ((n : ℝ) + 1)) := by
      have hnm1_nonneg : 0 ≤ (n : ℝ) - 1 := by
        linarith
      have hnp1_pos : 0 < (n : ℝ) + 1 := by
        positivity
      exact div_nonneg hnm1_nonneg hnp1_pos.le
    exact mul_nonneg hpow_nonneg hfrac_nonneg
  have hball_nonneg :
      0 ≤ (volume (Metric.closedBall (0 : E) 1)).toReal := ENNReal.toReal_nonneg
  have hsqrtH_nonneg : 0 ≤ Real.sqrt H.det := Real.sqrt_nonneg _
  have hfactor_nonneg :
      0 ≤ Real.sqrt H.det * (volume (Metric.closedBall (0 : E) 1)).toReal :=
    mul_nonneg hsqrtH_nonneg hball_nonneg
  -- Rewrite both ellipsoid volumes through the determinant, then isolate the common factor.
  rw [hvol_plus, hvol, hdet_ratio]
  calc
    Real.sqrt
        ((((n : ℝ) ^ (2 : ℕ) / (((n : ℝ) ^ (2 : ℕ)) - 1)) ^ n) *
          (((n : ℝ) - 1) / ((n : ℝ) + 1)) * H.det) *
        (volume (Metric.closedBall (0 : E) 1)).toReal
      =
        (Real.sqrt
            ((((n : ℝ) ^ (2 : ℕ) / (((n : ℝ) ^ (2 : ℕ)) - 1)) ^ n) *
              (((n : ℝ) - 1) / ((n : ℝ) + 1))) *
          Real.sqrt H.det) *
        (volume (Metric.closedBall (0 : E) 1)).toReal := by
          have hsqrt_mul :
              Real.sqrt
                  (((((n : ℝ) ^ (2 : ℕ) / (((n : ℝ) ^ (2 : ℕ)) - 1)) ^ n) *
                    (((n : ℝ) - 1) / ((n : ℝ) + 1))) * H.det) =
                Real.sqrt
                  ((((n : ℝ) ^ (2 : ℕ) / (((n : ℝ) ^ (2 : ℕ)) - 1)) ^ n) *
                    (((n : ℝ) - 1) / ((n : ℝ) + 1))) * Real.sqrt H.det := by
            simpa [mul_assoc] using
              (Real.sqrt_mul hratio_nonneg H.det)
          rw [hsqrt_mul]
    _ =
        Real.sqrt
            ((((n : ℝ) ^ (2 : ℕ) / (((n : ℝ) ^ (2 : ℕ)) - 1)) ^ n) *
              (((n : ℝ) - 1) / ((n : ℝ) + 1))) *
          (Real.sqrt H.det * (volume (Metric.closedBall (0 : E) 1)).toReal) := by
            ring
    _ ≤ Real.rpow (1 - 1 / (((n : ℝ) + 1) ^ (2 : ℕ))) ((n : ℝ) / 2) *
          (Real.sqrt H.det * (volume (Metric.closedBall (0 : E) 1)).toReal) := by
            exact mul_le_mul_of_nonneg_right hratio hfactor_nonneg

/-- Lemma 3.2.7: for a positive-definite ellipsoid `E(H, x̄)` and a nonzero cutting direction
`g`, the center cut `E₊` is contained in the updated ellipsoid `E(H₊, x̄₊)`, and the Lebesgue
volume of the updated ellipsoid is at most
`(1 - 1 / (n + 1)^2)^(n / 2)` times the original volume. -/
-- Proof sketch: normalize by translating `x̄` to `0` and scaling so that `⟪H g, g⟫ = 1`.
-- Expand the quadratic form of `H₊⁻¹` at `x - x̄₊` and use the halfspace condition
-- `⟪g, x - x̄⟫ ≤ 0` together with membership in `E(H, x̄)` to show every `x ∈ E₊` lies in
-- `E(H₊, x̄₊)`. For the volume estimate, compute the determinant ratio `det H₊ / det H`
-- using the rank-one update formula and rewrite the ellipsoid volumes via the determinant.
theorem centerCutEllipsoid_subset_updatedEllipsoid_and_volume_le
    (H : Mat) (hH : H.PosDef) (xBar g : E) (hg : g ≠ 0) (hn : 1 < n) :
    E₊(H, xBar, g) ⊆ E(H₊(H, g), x̄₊(H, xBar, g)) ∧
      ((volume (E(H₊(H, g), x̄₊(H, xBar, g)))).toReal ≤
        Real.rpow (1 - 1 / (((n : ℝ) + 1) ^ (2 : ℕ))) ((n : ℝ) / 2) *
          (volume (E(H, xBar))).toReal) := by
  constructor
  · intro x hx
    rcases hx with ⟨hxEllipsoid, hxCut⟩
    set y : E := x - xBar with hy
    set q : ℝ := inner ℝ (H.toEuclideanLin g) g with hq
    set δ : ℝ := ((n : ℝ) + 1)⁻¹ * (Real.sqrt q)⁻¹ with hδ
    set u : ℝ := (Real.sqrt q)⁻¹ * inner ℝ g y with hu
    set t : ℝ := inner ℝ ((H⁻¹).toEuclideanLin y) y with ht
    have hq_pos : 0 < q := by
      rw [hq]
      exact ellipsoidUpdate_quadratic_pos H hH hg
    have hyE : t ≤ 1 := by
      simpa [mem_affineEllipsoid_iff, hy, ht] using hxEllipsoid
    have hyCut : inner ℝ g y ≤ 0 := by
      simpa [hy] using hxCut
    have hu_nonpos : u ≤ 0 := by
      have hsqrt_inv_nonneg : 0 ≤ (Real.sqrt q)⁻¹ := by
        positivity
      exact by
        rw [hu]
        exact mul_nonpos_of_nonneg_of_nonpos hsqrt_inv_nonneg hyCut
    have hpair_sq : (inner ℝ g y) ^ (2 : ℕ) ≤ q * t := by
      rw [hq, ht]
      simpa [hy, mul_comm] using cut_pairing_sq_le H hH g y
    have hu_sq : u ^ (2 : ℕ) ≤ t := by
      have hsqrt_ne : Real.sqrt q ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hq_pos)
      have hq_ne : q ≠ 0 := ne_of_gt hq_pos
      have hdiv : (inner ℝ g y) ^ (2 : ℕ) / q ≤ t := by
        exact (div_le_iff₀ hq_pos).2
          (by simpa [mul_comm, mul_left_comm, mul_assoc] using hpair_sq)
      have hu_sq_eq : u ^ (2 : ℕ) = (inner ℝ g y) ^ (2 : ℕ) / q := by
        rw [hu]
        field_simp [hq_ne, hsqrt_ne]
        rw [show (Real.sqrt q) ^ (2 : ℕ) = q by exact Real.sq_sqrt hq_pos.le]
        ring_nf
      rw [hu_sq_eq]
      exact hdiv
    have hshift :
        x - x̄₊(H, xBar, g) = y + δ • H.toEuclideanLin g := by
      rw [updatedEllipsoidCenter, hy, hδ, hq]
      simp [sub_eq_add_neg, add_assoc, add_comm, smul_smul]
    rw [mem_affineEllipsoid_iff]
    -- Rewrite the shifted quadratic form into the normalized scalar inequality from the textbook.
    calc
      inner ℝ (((H₊(H, g))⁻¹).toEuclideanLin (x - x̄₊(H, xBar, g)))
          (x - x̄₊(H, xBar, g))
        =
          inner ℝ (((H₊(H, g))⁻¹).toEuclideanLin (y + δ • H.toEuclideanLin g))
            (y + δ • H.toEuclideanLin g) := by
              rw [hshift]
      _ =
          ((((n : ℝ) ^ (2 : ℕ)) - 1) / ((n : ℝ) ^ (2 : ℕ))) *
            (t + (2 / ((n : ℝ) - 1)) * (u ^ (2 : ℕ) + u) +
              1 / (((n : ℝ) ^ (2 : ℕ)) - 1)) := by
                exact updated_shifted_quadratic_eq H hH g y hg hn q δ u t hq hδ hu ht
      _ ≤ 1 := center_cut_update_scalar_bound (n := n) hn hyE hu_nonpos hu_sq
  · exact updated_affineEllipsoid_volume_le_decayFactor H hH xBar g hg hn

end
