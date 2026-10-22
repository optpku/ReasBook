/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_26
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_33
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Proposition_7_11

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open scoped BigOperators EllipsoidNotation RealSymmetricMatrixSpace SymmetricBox

variable {n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "Matₙ" => Matrix (Fin n) (Fin n) ℝ
local notation "SymmMatₙ" => 𝕊^n

/- Definition 7.34 lies in Chapter 7's diagonal ellipsoid / symmetric-box rounding domain.

Sampled owner-style declarations:
- `symmetricBox` in `Definition_7_33`, the earlier chapter owner of the box `B(g)`;
- `matrixEllipsoid` and the notation `W[r](G)` in `Definition_7_26`, the chapter owner for
  radius-parametrized ellipsoids;
- `Matrix.IsDiag.diagonal_diag` and `Matrix.diag` in mathlib's diagonal matrix API, the canonical
  matrix-level bridge from a diagonal matrix to its diagonal entries;
- `logDetRatioPotential` in `Proposition_7_11`, the chapter owner for scalar determinant-ratio
  potentials attached to matrix paths.

Best owner abstraction:
- source-facing: `ellipsoidBoxGeneratedConvexSet`, `ellipsoidBoxInterpolationMatrix`, and
  `ellipsoidBoxLogVolumePotential`;
- core/canonical: `symmetricBox`, `W[1](D)`, `Matrix.diag`, and the path owner
  `logDetRatioPotential`;
- bridge/view: the entrywise diagonal formula for `G(α)`, the positive-definite
  difference-of-logs formula, and the interval-restricted coordinate sum identity.

Primitive data:
- a matrix `D : Matₙ`;
- a vector `g : Eₙ`;
- a scalar interpolation parameter `α : ℝ`.

Derived API:
- the convex hull `Conv(W₁(D) ∪ B(|g|))`;
- the coordinate ratio and entrywise interpolation formulas;
- the determinant-ratio potential specialized to the interpolation path;
- the positive-definite difference-of-logs and interval-restricted coordinate-sum identities.

This refinement reuses the matrix-level owner from `Lemma_7_8`: the source-facing constructions are
stated directly in terms of a matrix `D`, with the diagonal-dependent pieces extracted via the
canonical matrix diagonal API instead of through a separate entry package.
-/

/-- The Definition 7.34 convex-set generator formed from the ellipsoid `W₁(D)` and the symmetric
box `B(|g|)` is their convex hull `Conv(W₁(D) ∪ B(|g|))`. -/
def ellipsoidBoxGeneratedConvexSet
    (D : Matₙ) (g : Eₙ) : Set Eₙ :=
  convexHull ℝ (W[1](D) ∪ B(|g|))

-- Proof sketch: unfold `ellipsoidBoxGeneratedConvexSet`; the right-hand side is the defining
-- convex hull of the ellipsoid-box union.
/-- Expanding `ellipsoidBoxGeneratedConvexSet d g` recovers the textbook formula
`Conv(W₁(D) ∪ B(|g|))`. -/
theorem ellipsoidBoxGeneratedConvexSet_def
    (D : Matₙ) (g : Eₙ) :
    ellipsoidBoxGeneratedConvexSet D g =
      convexHull ℝ (W[1](D) ∪ B(|g|)) :=
  rfl

/-- The auxiliary matrix `G(α) = (1 - α) D + α D²(g)` for `α ∈ [0, 1)`. -/
def ellipsoidBoxInterpolationMatrix
    (D : Matₙ) (g : Eₙ) (α : ℝ) : Matₙ :=
  Matrix.diagonal (fun i : Fin n ↦ (1 - α) * D i i + α * (g i) ^ (2 : ℕ))

-- Proof sketch: unfold `ellipsoidBoxInterpolationMatrix` and read off the diagonal entries.
/-- The entries of `ellipsoidBoxInterpolationMatrix d g α` are those of the diagonal matrix with
diagonal `(1 - α) d i + α (g i)^2`. -/
theorem ellipsoidBoxInterpolationMatrix_apply
    (D : Matₙ) (g : Eₙ) (α : ℝ) (i j : Fin n) :
    ellipsoidBoxInterpolationMatrix D g α i j =
      if i = j then (1 - α) * D i i + α * (g i) ^ (2 : ℕ) else 0 := by
  by_cases hij : i = j
  · subst hij
    simp [ellipsoidBoxInterpolationMatrix]
  · simp [ellipsoidBoxInterpolationMatrix, hij]

/-- The coordinate ratios `τ_i = (g i)^2 / d i` appearing in the logarithmic volume formula. -/
def ellipsoidBoxCoordinateRatio
    (D : Matₙ) (g : Eₙ) : Fin n → ℝ :=
  fun i : Fin n ↦ (g i) ^ (2 : ℕ) / D i i

/-- The auxiliary logarithmic volume potential
`V(α) = log (det G(0) / det G(α))`. -/
def ellipsoidBoxLogVolumePotential
    (D : Matₙ) (g : Eₙ) (α : ℝ) : ℝ :=
  logDetRatioPotential (ellipsoidBoxInterpolationMatrix D g) α

/-- Expanding `ellipsoidBoxLogVolumePotential d g α` gives the determinant-ratio formula
`log (det G(0) / det G(α))`. -/
theorem ellipsoidBoxLogVolumePotential_def
    (D : Matₙ) (g : Eₙ) (α : ℝ) :
    ellipsoidBoxLogVolumePotential D g α =
      Real.log
        (Matrix.det (ellipsoidBoxInterpolationMatrix D g 0) /
          Matrix.det (ellipsoidBoxInterpolationMatrix D g α)) :=
  rfl

/-- Helper for Definition 7.34: the diagonal interpolation matrix belongs to the real symmetric
matrix space `𝕊^n`. -/
theorem ellipsoidBoxInterpolationMatrix_mem_symmMat
    (D : Matₙ) (g : Eₙ) (α : ℝ) :
    ellipsoidBoxInterpolationMatrix D g α ∈ SymmMatₙ := by
  -- A diagonal matrix is symmetric, so the interpolation path lands in `𝕊^n`.
  rw [RealSymmetricMatrixSpace.mem_iff_isSymm]
  simp [ellipsoidBoxInterpolationMatrix]

/-- Helper for Definition 7.34: the interpolation matrix viewed as a point of `𝕊^n`. -/
def ellipsoidBoxInterpolationSymmMatrix
    (D : Matₙ) (g : Eₙ) (α : ℝ) : SymmMatₙ :=
  ⟨ellipsoidBoxInterpolationMatrix D g α,
    ellipsoidBoxInterpolationMatrix_mem_symmMat D g α⟩

/-- Helper for Definition 7.34: every diagonal entry of `G(α)` stays positive on
`α ∈ [0, 1)` when `D` is positive definite. -/
theorem ellipsoidBoxInterpolationEntry_pos
    (D : Matₙ) (hDpos : D.PosDef) (g : Eₙ) (α : ℝ)
    (hα : α ∈ Set.Ico (0 : ℝ) 1) (i : Fin n) :
    0 < (1 - α) * D i i + α * (g i) ^ (2 : ℕ) := by
  -- The positive diagonal of `D` and the nonnegative square term keep the convex combination
  -- strictly positive.
  have hDii_pos : 0 < D i i := hDpos.diag_pos
  have hα_nonneg : 0 ≤ α := hα.1
  have hone_sub_pos : 0 < 1 - α := sub_pos.mpr hα.2
  nlinarith [sq_nonneg (g i), hDii_pos]

/-- Helper for Definition 7.34: the interpolation matrix `G(α)` is positive definite on
`α ∈ [0, 1)` when `D` is positive definite. -/
theorem ellipsoidBoxInterpolationMatrix_posDefIco
    (D : Matₙ) (hDpos : D.PosDef) (g : Eₙ) (α : ℝ)
    (hα : α ∈ Set.Ico (0 : ℝ) 1) :
    (ellipsoidBoxInterpolationMatrix D g α).PosDef := by
  -- Positive diagonal entries are enough because `G(α)` is diagonal by construction.
  apply Matrix.PosDef.diagonal
  intro i
  simpa [ellipsoidBoxInterpolationMatrix] using
    ellipsoidBoxInterpolationEntry_pos D hDpos g α hα i

/-- Helper for Definition 7.34: the `i`th diagonal entry of `G(α)` factors through the
coordinate ratio `τ_i = (g i)^2 / D i i`. -/
theorem ellipsoidBoxInterpolationEntry_eq_diagMulRatio
    (D : Matₙ) (hDpos : D.PosDef) (g : Eₙ) (α : ℝ) (i : Fin n) :
    (1 - α) * D i i + α * (g i) ^ (2 : ℕ) =
      D i i * (1 + α * (ellipsoidBoxCoordinateRatio D g i - 1)) := by
  -- Rewrite the square term as `D i i * τ_i`, then factor out `D i i`.
  have hDii_ne : D i i ≠ 0 := hDpos.diag_pos.ne'
  have hratio :
      D i i * ellipsoidBoxCoordinateRatio D g i = (g i) ^ (2 : ℕ) := by
    rw [ellipsoidBoxCoordinateRatio]
    field_simp [hDii_ne]
  calc
    (1 - α) * D i i + α * (g i) ^ (2 : ℕ)
        = D i i - α * D i i + α * (g i) ^ (2 : ℕ) := by ring
    _ = D i i - α * D i i + α * (D i i * ellipsoidBoxCoordinateRatio D g i) := by
      rw [hratio]
    _ = D i i * (1 + α * (ellipsoidBoxCoordinateRatio D g i - 1)) := by ring

/-- Helper for Definition 7.34: the textbook factor `1 + α (τ_i - 1)` is positive on
`α ∈ [0, 1)` when `D` is positive definite. -/
theorem one_add_alpha_coordinateRatio_sub_one_pos
    (D : Matₙ) (hDpos : D.PosDef) (g : Eₙ) (α : ℝ)
    (hα : α ∈ Set.Ico (0 : ℝ) 1) (i : Fin n) :
    0 < 1 + α * (ellipsoidBoxCoordinateRatio D g i - 1) := by
  -- Transfer positivity from the diagonal entry of `G(α)` by factoring out `D i i > 0`.
  have hentry :
      0 < D i i * (1 + α * (ellipsoidBoxCoordinateRatio D g i - 1)) := by
    rw [← ellipsoidBoxInterpolationEntry_eq_diagMulRatio D hDpos g α i]
    exact ellipsoidBoxInterpolationEntry_pos D hDpos g α hα i
  exact (mul_pos_iff_of_pos_left hDpos.diag_pos).mp hentry

-- Route correction: the source identity requires `D > 0`, so the barrier bridge is stated on
-- the positive-definite regime instead of for an arbitrary diagonal input matrix.
-- Proof sketch: apply the Chapter 7 bridge
-- `logDetRatioPotential_eq_sub_logDetBarrierAmbient` to the interpolation path
-- `ellipsoidBoxInterpolationMatrix D g`; the interval hypothesis is the source-facing domain
-- restriction for the same path.
/- On the half-open unit interval, the source-facing determinant-ratio potential is the difference
of the Chapter 5 ambient log-determinant barrier values along the interpolation path. -/
theorem ellipsoidBoxLogVolumePotential_eq_sub_logDetBarrierAmbient
    (D : Matₙ) (hDpos : D.PosDef) (g : Eₙ) {α : ℝ} (hα : α ∈ Set.Ico (0 : ℝ) 1) :
    ellipsoidBoxLogVolumePotential D g α =
      logDetBarrierAmbient n (ellipsoidBoxInterpolationSymmMatrix D g α) -
        logDetBarrierAmbient n (ellipsoidBoxInterpolationSymmMatrix D g 0) := by
  -- The Proposition 7.11 bridge applies once both endpoints of the interpolation path are
  -- positive definite.
  have hG0 : (ellipsoidBoxInterpolationMatrix D g 0).PosDef := by
    simpa using
      ellipsoidBoxInterpolationMatrix_posDefIco D hDpos g 0 (by simp)
  have hGα : (ellipsoidBoxInterpolationMatrix D g α).PosDef :=
    ellipsoidBoxInterpolationMatrix_posDefIco D hDpos g α hα
  simpa [ellipsoidBoxLogVolumePotential, ellipsoidBoxInterpolationSymmMatrix] using
    logDetRatioPotential_eq_sub_logDetBarrierAmbient
      (n := n) (G := ellipsoidBoxInterpolationMatrix D g) hG0 hGα

-- Route correction: the coordinate-sum formula also needs `D > 0`, both for the source validity
-- and for the logarithmic factorization through `τ_i`.
-- Proof sketch: first rewrite the determinant-ratio potential as a difference of logarithms on the
-- positive-definite interpolation path; then use the diagonal determinant formulas
-- `det G(0) = ∏ i, d i` and `det G(α) = ∏ i, ((1 - α) d i + α (g i)^2)` to obtain the stated
-- coordinate sum.
/-- Definition 7.34: the logarithmic potential `ellipsoidBoxLogVolumePotential d g α` is the
coordinate formula `-∑ i, log (1 + α (τ_i - 1))`. -/
theorem ellipsoidBoxLogVolumePotential_eq
    (D : Matₙ) (hDpos : D.PosDef) (g : Eₙ) (α : ℝ)
    (hα : α ∈ Set.Ico (0 : ℝ) 1) :
    ellipsoidBoxLogVolumePotential D g α =
      -(∑ i : Fin n, Real.log (1 + α * (ellipsoidBoxCoordinateRatio D g i - 1))) := by
  -- Positive definiteness gives the determinant positivity needed to split the logarithmic ratio.
  have hG0 : (ellipsoidBoxInterpolationMatrix D g 0).PosDef := by
    simpa using
      ellipsoidBoxInterpolationMatrix_posDefIco D hDpos g 0 (by simp)
  have hGα : (ellipsoidBoxInterpolationMatrix D g α).PosDef :=
    ellipsoidBoxInterpolationMatrix_posDefIco D hDpos g α hα
  have hlog0 :
      Real.log (Matrix.det (ellipsoidBoxInterpolationMatrix D g 0)) =
        ∑ i : Fin n, Real.log (D i i) := by
    -- At `α = 0`, the interpolation matrix is exactly the diagonal matrix with entries `D i i`.
    have hdet0 :
        Matrix.det (ellipsoidBoxInterpolationMatrix D g 0) =
          ∏ i : Fin n, D i i := by
      rw [ellipsoidBoxInterpolationMatrix, Matrix.det_diagonal]
      simp
    rw [hdet0]
    exact
      Real.log_prod
        (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) ↦
          hDpos.diag_pos.ne')
  have hlogα :
      Real.log (Matrix.det (ellipsoidBoxInterpolationMatrix D g α)) =
        ∑ i : Fin n, Real.log ((1 - α) * D i i + α * (g i) ^ (2 : ℕ)) := by
    -- For general `α`, the determinant is the product of the positive diagonal entries.
    rw [ellipsoidBoxInterpolationMatrix, Matrix.det_diagonal]
    exact
      Real.log_prod
        (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) ↦
          (ellipsoidBoxInterpolationEntry_pos D hDpos g α hα i).ne')
  have hlogEntry :
      ∀ i : Fin n,
        Real.log ((1 - α) * D i i + α * (g i) ^ (2 : ℕ)) =
          Real.log (D i i) +
            Real.log (1 + α * (ellipsoidBoxCoordinateRatio D g i - 1)) := by
    intro i
    -- Factor each entry through `D i i * (1 + α (τ_i - 1))`, then split the logarithm.
    rw [ellipsoidBoxInterpolationEntry_eq_diagMulRatio D hDpos g α i]
    rw [Real.log_mul hDpos.diag_pos.ne'
      (one_add_alpha_coordinateRatio_sub_one_pos D hDpos g α hα i).ne']
  have hsum :
      ∑ i : Fin n, Real.log ((1 - α) * D i i + α * (g i) ^ (2 : ℕ)) =
        ∑ i : Fin n,
          (Real.log (D i i) +
            Real.log (1 + α * (ellipsoidBoxCoordinateRatio D g i - 1))) := by
    -- Summing the entrywise logarithmic factorization gives the determinant formula at `α`.
    refine Finset.sum_congr rfl ?_
    intro i hi
    exact hlogEntry i
  calc
    ellipsoidBoxLogVolumePotential D g α
        = Real.log (Matrix.det (ellipsoidBoxInterpolationMatrix D g 0)) -
            Real.log (Matrix.det (ellipsoidBoxInterpolationMatrix D g α)) := by
          rw [ellipsoidBoxLogVolumePotential_def, Real.log_div hG0.det_pos.ne' hGα.det_pos.ne']
    _ = (∑ i : Fin n, Real.log (D i i)) -
          (∑ i : Fin n, Real.log ((1 - α) * D i i + α * (g i) ^ (2 : ℕ))) := by
          rw [hlog0, hlogα]
    _ = (∑ i : Fin n, Real.log (D i i)) -
          (∑ i : Fin n,
            (Real.log (D i i) +
              Real.log (1 + α * (ellipsoidBoxCoordinateRatio D g i - 1)))) := by
          rw [hsum]
    _ = (∑ i : Fin n, Real.log (D i i)) -
          ((∑ i : Fin n, Real.log (D i i)) +
            ∑ i : Fin n, Real.log (1 + α * (ellipsoidBoxCoordinateRatio D g i - 1))) := by
          rw [Finset.sum_add_distrib]
    _ = -(∑ i : Fin n, Real.log (1 + α * (ellipsoidBoxCoordinateRatio D g i - 1))) := by
          ring

end
