/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_2_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_20
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_17
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_23
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_26
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Proposition_7_8

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open scoped EllipsoidNotation PositiveDefMatrixNorm SupportFunction

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/- Lemma 7.4 lies in Chapter 7's positive-definite ellipsoid-rounding / rank-one update domain.

Sampled owner-style declarations:
- `affineEllipsoid` and `mem_affineEllipsoid_iff` in `Chap03/Lemma_3_2_7`, the chapter owner and
  defining membership theorem for unit-radius ellipsoids;
- `matrixEllipsoid`, `centeredMatrixEllipsoid_one_eq_affineEllipsoid`, and
  `mem_centeredMatrixEllipsoid_iff_dualNorm_le` in `Definition_7_26`, the radius-parametrized
  ellipsoid owner and its positive-definite dual-norm bridge;
- `positiveDefMatrixNorm` in `Definition_7_23`, the chapter owner of the `G`-primal norm and its
  induced dual norm;
- `centralSymmetryRoundingObjective` and `centralSymmetryRoundingAlphaStar` in `Proposition_7_8`,
  the scalar owner declarations for the logarithmic objective and its critical point;
- `Matrix.vecMulVec`, the canonical rank-one outer-product owner from mathlib.

Best owner abstraction:
- source-facing: the rank-one matrix path, the signed convex hull, and the scalar potential data
  specific to Lemma 7.4;
- core/canonical: `affineEllipsoid`, `positiveDefMatrixNorm`, and `Matrix.vecMulVec`;
- bridge/view: the ellipsoid-containment and determinant-ratio theorems for the source-facing
  constructions.

Primitive data:
- a matrix `G : Mat`;
- a direction `g : E`;
- an interpolation parameter `α : ℝ`;
- a positive-definiteness proof `hG` only when the `G`-dual norm enters.

Derived API:
- the centered unit ellipsoid is expressed directly through `affineEllipsoid`, not through a
  parallel local owner;
- the scalar parameter `σ`;
- the matrix-level potential and optimal parameter, obtained by specializing the scalar owner from
  `Proposition_7_8`;
- the containment and determinant-ratio conclusions used downstream in Definition 7.28.

Source/core/bridge triage:
- source-facing: `rankOneUpdatedMatrix`, `rankOneUpdateAugmentedHull`, `rankOneUpdateSigma`,
  `rankOneUpdatePotential`, and `rankOneUpdateOptimalAlpha`;
- core/canonical: `affineEllipsoid`, `positiveDefMatrixNorm`, and `Matrix.vecMulVec`;
- bridge/view: the remaining theorem-level consequences below.

The centered unit ellipsoid already belongs to the chapter owner `affineEllipsoid`, so this file
keeps only the genuinely source-facing rank-one update objects and derives their ellipsoid views
from that owner. -/

/-- The rank-one matrix update `G(α) = (1 - α) G + α ggᵀ`. -/
def rankOneUpdatedMatrix
    (G : Mat) (g : E) (α : ℝ) : Mat :=
  (1 - α) • G + α • Matrix.vecMulVec g g

-- Proof sketch: unfold `rankOneUpdatedMatrix` and simplify the scalar coefficients at `α = 0`.
/-- At `α = 0`, the rank-one update `G(α)` is the original matrix `G`. -/
@[simp] theorem rankOneUpdatedMatrix_zero
    (G : Mat) (g : E) :
    rankOneUpdatedMatrix G g 0 = G := by
  simp [rankOneUpdatedMatrix]

/-- The convex body `C_{± g}(G)`, defined as the convex hull of the unit ellipsoid `E(G, 0)` and
the two points `g` and `-g`. -/
def rankOneUpdateAugmentedHull
    (G : Mat) (g : E) : Set E :=
  convexHull ℝ (E(G, (0 : E)) ∪ ({g, -g} : Set E))

-- Proof sketch: unfold `rankOneUpdateAugmentedHull`.
/-- Expanding `rankOneUpdateAugmentedHull G g` gives the convex hull of `E(G, 0) ∪ {g, -g}`. -/
theorem rankOneUpdateAugmentedHull_def
    (G : Mat) (g : E) :
    rankOneUpdateAugmentedHull G g =
      convexHull ℝ (E(G, (0 : E)) ∪ ({g, -g} : Set E)) :=
  rfl

/-- The quantity `σ = (1 / n) ‖g‖_{G,*}² - 1` appearing in the determinant estimate. -/
def rankOneUpdateSigma
    (G : Mat) (hG : G.PosDef) (g : E) : ℝ :=
  (‖g‖[⟨G, hG⟩,*] ^ (2 : ℕ)) / n - 1

-- Proof sketch: unfold `rankOneUpdateSigma`.
/-- Expanding `rankOneUpdateSigma G g` gives `(‖g‖_{G,*}^2 / n) - 1`. -/
theorem rankOneUpdateSigma_def
    (G : Mat) (hG : G.PosDef) (g : E) :
    rankOneUpdateSigma G hG g =
      (‖g‖[⟨G, hG⟩,*] ^ (2 : ℕ)) / n - 1 :=
  rfl

/-- The logarithmic determinant potential
`V(α) = log (1 + α (n (1 + σ) - 1)) + (n - 1) log (1 - α)`. -/
def rankOneUpdatePotential
    (G : Mat) (hG : G.PosDef) (g : E) (α : ℝ) : ℝ :=
  centralSymmetryRoundingObjective n (rankOneUpdateSigma G hG g) α

-- Proof sketch: unfold `rankOneUpdatePotential` and then `centralSymmetryRoundingObjective`.
/-- Expanding `rankOneUpdatePotential G g α` gives the explicit closed form for `V(α)`. -/
theorem rankOneUpdatePotential_def
    (G : Mat) (hG : G.PosDef) (g : E) (α : ℝ) :
    rankOneUpdatePotential G hG g α =
      Real.log (1 + α * ((n : ℝ) * (1 + rankOneUpdateSigma G hG g) - 1)) +
        ((n : ℝ) - 1) * Real.log (1 - α) := by
  simp [rankOneUpdatePotential, centralSymmetryRoundingObjective]

/-- The candidate maximizer `α* = σ / (n (1 + σ) - 1)` for the potential `V`. -/
def rankOneUpdateOptimalAlpha
    (G : Mat) (hG : G.PosDef) (g : E) : ℝ :=
  centralSymmetryRoundingAlphaStar n (rankOneUpdateSigma G hG g)

-- Proof sketch: unfold `rankOneUpdateOptimalAlpha` and then `centralSymmetryRoundingAlphaStar`.
/-- Expanding `rankOneUpdateOptimalAlpha G g` gives the explicit formula for `α*`. -/
theorem rankOneUpdateOptimalAlpha_def
    (G : Mat) (hG : G.PosDef) (g : E) :
    rankOneUpdateOptimalAlpha G hG g =
      rankOneUpdateSigma G hG g /
        ((n : ℝ) * (1 + rankOneUpdateSigma G hG g) - 1) := by
  simp [rankOneUpdateOptimalAlpha, centralSymmetryRoundingAlphaStar]

-- Proof sketch: this is the matrix specialization of
-- `centralSymmetryRoundingAlphaStar_mem_Ico` from Proposition 7.8.
/-- If `2 ≤ n` and `σ = (1 / n) ‖g‖_{G,*}^2 - 1` is positive, then the candidate maximizer
`α* = σ / (n (1 + σ) - 1)` lies in the interval `[0, 1)`. -/
theorem rankOneUpdateOptimalAlpha_mem_Ico
    (G : Mat) (hG : G.PosDef) (g : E) (hn : 2 ≤ n)
    (hσ : 0 < rankOneUpdateSigma G hG g) :
    rankOneUpdateOptimalAlpha G hG g ∈ Set.Ico (0 : ℝ) 1 := by
  simpa [rankOneUpdateOptimalAlpha] using
    centralSymmetryRoundingAlphaStar_mem_Ico hn hσ.le

/-- Helper for Lemma 7.4: the rank-one update stays positive definite on `α ∈ [0, 1)`. -/
lemma rankOneUpdatedMatrix_posDef_of_mem_Ico
    (G : Mat) (hG : G.PosDef) (g : E) {α : ℝ}
    (hα : α ∈ Set.Ico (0 : ℝ) 1) :
    (rankOneUpdatedMatrix G g α).PosDef := by
  rcases hα with ⟨hα0, hα1⟩
  have hone_sub_pos : 0 < 1 - α := by
    linarith
  have hrankOne_psd : (Matrix.vecMulVec g g).PosSemidef := by
    simpa using Matrix.posSemidef_vecMulVec_self_star g
  -- Add the nonnegative rank-one perturbation to the positive-definite scaled base matrix.
  rw [rankOneUpdatedMatrix]
  exact (hG.smul hone_sub_pos).add_posSemidef (hrankOne_psd.smul hα0)

/-- Helper for Lemma 7.4: squaring the primal `G`-norm recovers the quadratic form `⟪Gx, x⟫`. -/
lemma positiveDefMatrixNorm_sq_eq_matrix_quadratic
    (G : {A : Mat // A.PosDef}) (x : E) :
    ‖x‖[G] ^ (2 : ℕ) =
      inner ℝ ((Matrix.toEuclideanLin G.1) x) x := by
  have hPosLin : (Matrix.toEuclideanLin G.1).IsPositive :=
    Matrix.isPositive_toEuclideanLin_iff.mpr G.2.posSemidef
  have hnonneg : 0 ≤ inner ℝ ((Matrix.toEuclideanLin G.1) x) x := by
    simpa [real_inner_comm] using hPosLin.inner_nonneg_right x
  -- Square the defining square root after recording the positivity of the quadratic form.
  rw [positiveDefMatrixNorm_def, Real.sq_sqrt hnonneg]

/-- Helper for Lemma 7.4: the rank-one matrix `ggᵀ` contributes exactly the square
of `⟪g, z⟫`. -/
lemma vecMulVec_quadratic
    (g z : E) :
    inner ℝ ((Matrix.vecMulVec g g).toEuclideanLin z) z = (inner ℝ g z) ^ (2 : ℕ) := by
  have hmul : ((Matrix.vecMulVec g g).toEuclideanLin z).ofLp = (inner ℝ g z) • g.ofLp := by
    have hinner : inner ℝ g z = g.ofLp ⬝ᵥ z.ofLp := by
      have hraw := EuclideanSpace.inner_eq_star_dotProduct g z
      simpa [dotProduct_comm] using hraw
    simp [Matrix.ofLp_toLpLin, Matrix.vecMulVec_mulVec, hinner]
  have hin : ((Matrix.vecMulVec g g).toEuclideanLin z) = (inner ℝ g z) • g := by
    ext i
    simpa using congrArg (fun v : Fin n → ℝ ↦ v i) hmul
  -- Rewrite the rank-one action as a scalar multiple of `g` and collapse the pairing.
  calc
    inner ℝ ((Matrix.vecMulVec g g).toEuclideanLin z) z = inner ℝ ((inner ℝ g z) • g) z := by
      rw [hin]
    _ = (inner ℝ g z) * inner ℝ g z := by
      simp [real_inner_smul_left]
    _ = (inner ℝ g z) ^ (2 : ℕ) := by
      ring

/-- Helper for Lemma 7.4: the `1 × 1` correction term in the matrix determinant lemma collapses
to the inverse quadratic form `1 + c ⟪g, G⁻¹ g⟫`. -/
lemma oneByOneRankOneCorrection_det
    (G : Mat) (g : E) (c : ℝ) :
    (1 + Matrix.replicateRow (Fin 1) g.ofLp * G⁻¹ *
        Matrix.replicateCol (Fin 1) ((c • g).ofLp)).det =
      1 + c * inner ℝ g ((Matrix.toEuclideanLin G⁻¹) g) := by
  rw [Matrix.det_fin_one]
  change (((1 : Matrix (Fin 1) (Fin 1) ℝ) +
      Matrix.replicateRow (Fin 1) g.ofLp * G⁻¹ *
        Matrix.replicateCol (Fin 1) (c • g).ofLp) 0 0) = _
  have hmul :
      G⁻¹ * Matrix.replicateCol (Fin 1) ((c • g).ofLp) =
        Matrix.replicateCol (Fin 1) (((Matrix.toEuclideanLin G⁻¹) (c • g)).ofLp) := by
    ext i j
    fin_cases j
    change ((G⁻¹ *ᵥ (c • g).ofLp) i) =
      (((Matrix.toEuclideanLin G⁻¹) (c • g)).ofLp) i
    rw [Matrix.toEuclideanLin, Matrix.toLpLin_apply]
  -- Move the rank-one correction to a scalar identity at the unique entry of the `1 × 1` matrix.
  calc
    (((1 : Matrix (Fin 1) (Fin 1) ℝ) +
        Matrix.replicateRow (Fin 1) g.ofLp * G⁻¹ *
          Matrix.replicateCol (Fin 1) (c • g).ofLp) 0 0)
        = (((1 : Matrix (Fin 1) (Fin 1) ℝ) +
            Matrix.replicateRow (Fin 1) g.ofLp *
              Matrix.replicateCol (Fin 1)
                (((Matrix.toEuclideanLin G⁻¹) (c • g)).ofLp)) 0 0) := by
            rw [Matrix.mul_assoc, hmul]
    _ = 1 + g.ofLp ⬝ᵥ (((Matrix.toEuclideanLin G⁻¹) (c • g)).ofLp) := by
          simp [Matrix.replicateRow_mul_replicateCol_apply]
    _ = 1 + inner ℝ g ((Matrix.toEuclideanLin G⁻¹) (c • g)) := by
          have hraw :=
            EuclideanSpace.inner_eq_star_dotProduct g
              ((Matrix.toEuclideanLin G⁻¹) (c • g))
          simpa [dotProduct_comm, real_inner_comm] using
            (congrArg (fun t : ℝ ↦ 1 + t) hraw).symm
    _ = 1 + c * inner ℝ g ((Matrix.toEuclideanLin G⁻¹) g) := by
          simp [real_inner_smul_right]

/-- Helper for Lemma 7.4: in positive dimension, the determinant ratio of `G(α)` has the closed
form from equation `(7.u208)`. -/
lemma rankOneUpdatedMatrix_detRatio_of_pos
    (G : Mat) (hG : G.PosDef) (g : E) {α : ℝ}
    (hn : 0 < n) (hα : α ∈ Set.Ico (0 : ℝ) 1) :
    Matrix.det (rankOneUpdatedMatrix G g α) / Matrix.det G =
      (1 - α) ^ (n - 1) *
        (1 + α * (((n : ℝ) * (1 + rankOneUpdateSigma G hG g)) - 1)) := by
  let r : ℝ := ‖g‖[⟨G, hG⟩,*]
  let t : ℝ := α / (1 - α)
  have hdetG_unit : IsUnit (Matrix.det G) := by
    exact isUnit_iff_ne_zero.mpr (ne_of_gt hG.det_pos)
  have hdetG_ne : Matrix.det G ≠ 0 := by
    exact ne_of_gt hG.det_pos
  have hone_sub_pos : 0 < 1 - α := by
    linarith [hα.2]
  have hone_sub_ne : 1 - α ≠ 0 := hone_sub_pos.ne'
  have hn1 : 1 ≤ n := Nat.succ_le_of_lt hn
  have hquad_nonneg :
      0 ≤ inner ℝ g ((Matrix.toEuclideanLin G⁻¹) g) := by
    -- Positive definiteness of `G⁻¹` makes the inverse quadratic form nonnegative.
    have hPosLin : (Matrix.toEuclideanLin G⁻¹).IsPositive := by
      exact Matrix.isPositive_toEuclideanLin_iff.mpr hG.inv.posSemidef
    simpa [real_inner_comm] using hPosLin.inner_nonneg_right g
  have hr_sq :
      r ^ (2 : ℕ) = inner ℝ g ((Matrix.toEuclideanLin G⁻¹) g) := by
    have hr_eq :
        r = Real.sqrt (inner ℝ g ((Matrix.toEuclideanLin G⁻¹) g)) := by
      simpa [r] using positiveDefMatrixNorm_dualNorm_eq_sqrt_inner_inv ⟨G, hG⟩ g
    rw [hr_eq, Real.sq_sqrt hquad_nonneg]
  have hmatrix :
      rankOneUpdatedMatrix G g α =
        (1 - α) • (G + t • Matrix.vecMulVec g g) := by
    -- Pull out the common factor `(1 - α)` so the remaining determinant is a rank-one update.
    rw [rankOneUpdatedMatrix]
    ext i j
    dsimp [t]
    field_simp [hone_sub_ne]
  have hpow :
      (1 - α) ^ n = (1 - α) ^ (n - 1) * (1 - α) := by
    cases n with
    | zero =>
        cases Nat.not_lt_zero _ hn
    | succ k =>
        rw [pow_succ, Nat.succ_sub_one]
  have hpow_card :
      (1 - α) ^ Fintype.card (Fin n) = (1 - α) ^ (n - 1) * (1 - α) := by
    simpa using hpow
  have hcore :
      Matrix.det (G + t • Matrix.vecMulVec g g) =
        Matrix.det G * (1 + t * r ^ (2 : ℕ)) := by
    -- Apply the matrix determinant lemma and collapse the `1 × 1` correction factor.
    calc
      Matrix.det (G + t • Matrix.vecMulVec g g)
          = Matrix.det G *
              (1 + Matrix.replicateRow (Fin 1) g.ofLp * G⁻¹ *
                Matrix.replicateCol (Fin 1) ((t • g).ofLp)).det := by
              simpa [Matrix.vecMulVec_eq (Fin 1)] using
                (@Matrix.det_add_replicateCol_mul_replicateRow
                  (Fin n) ℝ _ _ _ (Fin 1) inferInstance G
                  hdetG_unit ((t • g).ofLp) g.ofLp)
      _ = Matrix.det G * (1 + t * inner ℝ g ((Matrix.toEuclideanLin G⁻¹) g)) := by
            rw [oneByOneRankOneCorrection_det G g t]
      _ = Matrix.det G * (1 + t * r ^ (2 : ℕ)) := by
            rw [hr_sq]
  have hn_cast_ne : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  -- Rewrite the determinant ratio and then fold the squared dual norm into `σ`.
  rw [hmatrix, Matrix.det_smul, hcore]
  rw [hpow_card]
  dsimp [t, r]
  rw [rankOneUpdateSigma_def]
  field_simp [hdetG_ne, hone_sub_ne, hn_cast_ne]
  ring

/-- Helper for Lemma 7.4: on `0 ≤ α < 1`, the singular logarithmic term is bounded by
`α / (1 - α)`. -/
lemma negLogOneSub_le_div_of_mem_Ico
    {α : ℝ} (hα : α ∈ Set.Ico (0 : ℝ) 1) :
    -Real.log (1 - α) ≤ α / (1 - α) := by
  have hone_sub_pos : 0 < 1 - α := by
    linarith [hα.2]
  have hlog_aux :
      -Real.log (1 - α) ≤ (1 - α)⁻¹ - 1 := by
    -- Rewrite the bound through `log ((1 - α)⁻¹)` so that `log_le_sub_one_of_pos` applies.
    simpa [Real.log_inv] using
      (Real.log_le_sub_one_of_pos (x := (1 - α)⁻¹) (inv_pos.mpr hone_sub_pos))
  have hrewrite : (1 - α)⁻¹ - 1 = α / (1 - α) := by
    field_simp [hone_sub_pos.ne']
    ring
  rwa [hrewrite] at hlog_aux

/-- Helper for Lemma 7.4: the scalar gap
`log (1 + σ) - σ / (1 + σ)` dominates the rational lower bound
`σ² / ((1 + σ) (2 + σ))` for `σ ≥ 0`. -/
lemma sigmaLogGap_ge_rational
    {σ : ℝ} (hσ : 0 ≤ σ) :
    σ ^ (2 : ℕ) / ((1 + σ) * (2 + σ)) ≤
      Real.log (1 + σ) - σ / (1 + σ) := by
  have hlog : 2 * σ / (σ + 2) ≤ Real.log (1 + σ) :=
    Real.le_log_one_add_of_nonneg hσ
  have hden1 : 0 < 1 + σ := by
    linarith
  have hden2 : 0 < 2 + σ := by
    linarith
  have hrewrite :
      σ / (1 + σ) + σ ^ (2 : ℕ) / ((1 + σ) * (2 + σ)) =
        2 * σ / (σ + 2) := by
    -- Clear denominators once to normalize the rational identity.
    field_simp [hden1.ne', hden2.ne']
    ring
  have hsum :
      σ / (1 + σ) + σ ^ (2 : ℕ) / ((1 + σ) * (2 + σ)) ≤
        Real.log (1 + σ) := by
    rw [hrewrite]
    simpa [add_comm] using hlog
  linarith

/-- Helper for Lemma 7.4: the convex join of two compact sets in `E` is compact. -/
lemma convexJoin_isCompact
    {s t : Set E} (hs : IsCompact s) (ht : IsCompact t) :
    IsCompact (convexJoin ℝ s t) := by
  let f : ℝ × (E × E) → E := fun p ↦ (1 - p.1) • p.2.1 + p.1 • p.2.2
  have hf : Continuous f := by
    -- Realize the join as the continuous image of `[0, 1] × s × t`.
    refine ((continuous_const.sub continuous_fst).smul continuous_snd.fst).add ?_
    exact continuous_fst.smul continuous_snd.snd
  have himage :
      convexJoin ℝ s t = f '' (Set.Icc (0 : ℝ) 1 ×ˢ (s ×ˢ t)) := by
    ext z
    constructor
    · intro hz
      rcases mem_convexJoin.mp hz with ⟨x, hx, y, hy, hseg⟩
      rw [segment_eq_image] at hseg
      rcases hseg with ⟨θ, hθ, hzθ⟩
      refine ⟨⟨θ, (x, y)⟩, ?_, ?_⟩
      · exact ⟨hθ, hx, hy⟩
      · simpa [f] using hzθ
    · rintro ⟨⟨θ, x, y⟩, hmem, rfl⟩
      rcases hmem with ⟨hθ, hx, hy⟩
      refine mem_convexJoin.mpr ⟨x, hx, y, hy, ?_⟩
      rw [segment_eq_image]
      exact ⟨θ, hθ, by simp [f]⟩
  -- Compactness follows from compactness of the product domain.
  rw [himage]
  exact (isCompact_Icc.prod (hs.prod ht)).image hf

/-- Helper for Lemma 7.4: positive-definite ellipsoids are compact. -/
lemma affineEllipsoid_isCompact_of_posDef
    (G : Mat) (hG : G.PosDef) (v : E) :
    IsCompact (E(G, v)) := by
  have hclosed : IsClosed (E(G, v) : Set E) := by
    -- The defining quadratic form is continuous, so the sublevel set at `1` is closed.
    refine isClosed_le ?_ continuous_const
    have hlin :
        Continuous fun x : E ↦ (G⁻¹).toEuclideanLin (x - v) :=
      (LinearMap.continuous_of_finiteDimensional ((G⁻¹).toEuclideanLin)).comp
        (continuous_id.sub continuous_const)
    simpa [affineEllipsoid] using hlin.inner (continuous_id.sub continuous_const)
  exact Metric.isCompact_of_isClosed_isBounded hclosed (affineEllipsoid_bounded G v hG)

/-- Helper for Lemma 7.4: `E(G, 0)` is convex because it is the closed unit ball of the dual
weighted seminorm. -/
lemma affineEllipsoid_convex_of_posDef
    (G : Mat) (hG : G.PosDef) :
    Convex ℝ (E(G, (0 : E))) := by
  let p : Seminorm ℝ E := positiveDefMatrixNorm G⁻¹ hG.inv
  rw [← centeredMatrixEllipsoid_one_eq_affineEllipsoid G]
  -- Rewrite the ellipsoid as a closed seminorm ball and use the owner convexity theorem.
  simpa [p, Seminorm.mem_closedBall_zero, positiveDefMatrixNorm_def, real_inner_comm] using
    p.convex_closedBall (0 : E) 1

/-- Helper for Lemma 7.4: the signed augmented hull is compact. -/
lemma rankOneUpdateAugmentedHull_isCompact
    (G : Mat) (hG : G.PosDef) (g : E) :
    IsCompact (rankOneUpdateAugmentedHull G g) := by
  have hEllipsoidCompact : IsCompact (E(G, (0 : E))) :=
    affineEllipsoid_isCompact_of_posDef G hG (0 : E)
  have hEllipsoidConvex : Convex ℝ (E(G, (0 : E))) :=
    affineEllipsoid_convex_of_posDef G hG
  have hEllipsoidNonempty : (E(G, (0 : E)) : Set E).Nonempty := by
    exact ⟨0, center_mem_affineEllipsoid G (0 : E)⟩
  have hPairNonempty : ({g, -g} : Set E).Nonempty := by
    simp
  have hPairFinite : ({g, -g} : Set E).Finite := by
    simp
  have hPairCompact : IsCompact (convexHull ℝ ({g, -g} : Set E)) :=
    hPairFinite.isCompact_convexHull ℝ
  -- Route correction: package the signed hull as a convex join of two compact convex pieces.
  rw [rankOneUpdateAugmentedHull_def, convexHull_union hEllipsoidNonempty hPairNonempty,
    hEllipsoidConvex.convexHull_eq]
  exact convexJoin_isCompact hEllipsoidCompact hPairCompact

/-- Helper for Lemma 7.4: the support of the centered ellipsoid `E(H, 0)` is the primal
`H`-norm. -/
lemma supportFunction_affineEllipsoid_zero_eq_coe_primalNorm
    (H : Mat) (hH : H.PosDef) (x : E) :
    ξ[E(H, (0 : E))] x = (((‖x‖[⟨H, hH⟩] : ℝ)) : EReal) := by
  let K : {A : Mat // A.PosDef} := ⟨H, hH⟩
  let _ : Invertible H := hH.isUnit.invertible
  have hmax :
      IsGreatest ((fun y : E ↦ inner ℝ y x) '' E(H, (0 : E)))
        ‖x‖[K] := by
    -- Specialize the Chapter 3 maximizer at `A := H⁻¹` so the source set is exactly `E(H, 0)`.
    have hmax' :
        IsGreatest ((fun y : E ↦ inner ℝ y x) '' E(H, (0 : E)))
          (Real.sqrt (inner ℝ x ((Matrix.toEuclideanLin H) x))) := by
      simpa [real_inner_comm, Matrix.inv_inv_of_invertible] using
        (isGreatest_inner_image_spdEllipsoid H⁻¹ hH.inv x)
    have hnorm :
        Real.sqrt (inner ℝ x ((Matrix.toEuclideanLin H) x)) = ‖x‖[K] := by
      rw [positiveDefMatrixNorm_def]
      simp [K, real_inner_comm]
    simpa [hnorm] using hmax'
  have hupper : ξ[E(H, (0 : E))] x ≤ (((‖x‖[K] : ℝ)) : EReal) := by
    rw [supportFunction_apply]
    refine sSup_le ?_
    rintro _ ⟨y, hy, rfl⟩
    change (((inner ℝ y x : ℝ) : EReal) ≤ (((‖x‖[K] : ℝ)) : EReal))
    exact_mod_cast (hmax.2 ⟨y, hy, rfl⟩)
  have hlower : (((‖x‖[K] : ℝ)) : EReal) ≤ ξ[E(H, (0 : E))] x := by
    rcases hmax.1 with ⟨y, hy, hyEq⟩
    rw [supportFunction_apply]
    simpa [hyEq] using
      (le_sSup ⟨y, hy, rfl⟩ :
        (((inner ℝ y x : ℝ) : EReal) ≤
          sSup ((fun y : E ↦ ((inner ℝ y x : ℝ) : EReal)) '' E(H, (0 : E)))))
  simpa [K] using le_antisymm hupper hlower

/-- Helper for Lemma 7.4: the support function of the symmetric pair `{g, -g}` is `|⟪g, x⟫|`. -/
lemma supportFunction_pair_eq_coe_absInner
    (g x : E) :
    ξ[({g, -g} : Set E)] x = (((|inner ℝ g x| : ℝ)) : EReal) := by
  rw [supportFunction_apply, Set.image_pair, sSup_pair]
  have hinner_neg : inner ℝ (-g) x = - inner ℝ g x := by
    simp
  -- Rewrite the `-g` contribution to the support function in the same scalar normal form.
  rw [hinner_neg, EReal.coe_neg]
  by_cases h : 0 ≤ inner ℝ g x
  · have hneg : -(inner ℝ g x) ≤ inner ℝ g x := by
      linarith
    have hneg' : (-((inner ℝ g x : ℝ) : EReal)) ≤ ((inner ℝ g x : ℝ) : EReal) := by
      exact_mod_cast hneg
    calc
      max (((inner ℝ g x : ℝ)) : EReal) (-(((inner ℝ g x : ℝ)) : EReal))
          = (((inner ℝ g x : ℝ)) : EReal) := max_eq_left hneg'
      _ = (((|inner ℝ g x| : ℝ)) : EReal) := by rw [abs_of_nonneg h]
  · have hle : inner ℝ g x ≤ 0 := le_of_not_ge h
    have hneg : inner ℝ g x ≤ -(inner ℝ g x) := by
      linarith
    have hneg' : (((inner ℝ g x : ℝ)) : EReal) ≤ -(((inner ℝ g x : ℝ)) : EReal) := by
      exact_mod_cast hneg
    calc
      max (((inner ℝ g x : ℝ)) : EReal) (-(((inner ℝ g x : ℝ)) : EReal))
          = -(((inner ℝ g x : ℝ)) : EReal) := max_eq_right hneg'
      _ = (((-(inner ℝ g x) : ℝ)) : EReal) := by rw [← EReal.coe_neg]
      _ = (((|inner ℝ g x| : ℝ)) : EReal) := by
            rw [(abs_of_nonpos hle).symm]

/-- Helper for Lemma 7.4: the support of the augmented hull is the maximum of the primal norm
and the signed linear form. -/
lemma supportFunction_rankOneUpdateAugmentedHull_eq_max
    (G : Mat) (hG : G.PosDef) (g x : E) :
    ξ[rankOneUpdateAugmentedHull G g] x =
      max ((((‖x‖[⟨G, hG⟩] : ℝ)) : EReal))
        ((((|inner ℝ g x| : ℝ)) : EReal)) := by
  -- Normalize the convex hull support once, then compute the symmetric-pair support explicitly.
  rw [rankOneUpdateAugmentedHull_def, supportFunction_convexHull_union_eq_max]
  rw [supportFunction_affineEllipsoid_zero_eq_coe_primalNorm,
    supportFunction_pair_eq_coe_absInner]

/-- Helper for Lemma 7.4: applying `rankOneUpdatedMatrix G g α` to `x` splits into the base
matrix action and the rank-one correction. -/
lemma rankOneUpdatedMatrix_toEuclideanLin_eq_smul_add
    (G : Mat) (g x : E) (α : ℝ) :
    (rankOneUpdatedMatrix G g α).toEuclideanLin x =
      (1 - α) • (G.toEuclideanLin x) + α • ((Matrix.vecMulVec g g).toEuclideanLin x) := by
  -- Expand the matrix action to isolate the rank-one term.
  simp [rankOneUpdatedMatrix, Matrix.toEuclideanLin, Matrix.toLpLin_apply]

/-- Helper for Lemma 7.4: the squared primal norm of the updated matrix is the convex combination
of the base quadratic form and the square of `⟪g, x⟫`. -/
lemma rankOneUpdatedMatrix_primalNorm_sq_eq_combo
    (G : Mat) (hG : G.PosDef) (g x : E) {α : ℝ}
    (hα : α ∈ Set.Ico (0 : ℝ) 1) :
    ‖x‖[⟨rankOneUpdatedMatrix G g α, rankOneUpdatedMatrix_posDef_of_mem_Ico G hG g hα⟩] ^
        (2 : ℕ) =
      (1 - α) * ‖x‖[⟨G, hG⟩] ^ (2 : ℕ) + α * (inner ℝ g x) ^ (2 : ℕ) := by
  let updated : {A : Mat // A.PosDef} :=
    ⟨rankOneUpdatedMatrix G g α, rankOneUpdatedMatrix_posDef_of_mem_Ico G hG g hα⟩
  -- Rewrite the updated quadratic form through the linearized matrix action.
  calc
    ‖x‖[updated] ^ (2 : ℕ) = inner ℝ ((updated.1).toEuclideanLin x) x := by
      simpa [updated] using positiveDefMatrixNorm_sq_eq_matrix_quadratic updated x
    _ = inner ℝ
          ((1 - α) • (G.toEuclideanLin x) + α • ((Matrix.vecMulVec g g).toEuclideanLin x)) x := by
      rw [rankOneUpdatedMatrix_toEuclideanLin_eq_smul_add]
    _ =
        inner ℝ ((1 - α) • (G.toEuclideanLin x)) x +
          inner ℝ (α • ((Matrix.vecMulVec g g).toEuclideanLin x)) x := by
            rw [inner_add_left]
    _ = (1 - α) * inner ℝ (G.toEuclideanLin x) x +
          α * inner ℝ ((Matrix.vecMulVec g g).toEuclideanLin x) x := by
            simp [real_inner_smul_left]
    _ = (1 - α) * ‖x‖[⟨G, hG⟩] ^ (2 : ℕ) + α * (inner ℝ g x) ^ (2 : ℕ) := by
          rw [← positiveDefMatrixNorm_sq_eq_matrix_quadratic ⟨G, hG⟩ x, vecMulVec_quadratic]

/-- Helper for Lemma 7.4: the updated primal norm is bounded by the larger of the old norm and
the signed linear form. -/
lemma rankOneUpdatedMatrix_primalNorm_le_max_absInner
    (G : Mat) (hG : G.PosDef) (g x : E) {α : ℝ}
    (hα : α ∈ Set.Ico (0 : ℝ) 1) :
    ‖x‖[⟨rankOneUpdatedMatrix G g α, rankOneUpdatedMatrix_posDef_of_mem_Ico G hG g hα⟩] ≤
      max ‖x‖[⟨G, hG⟩] |inner ℝ g x| := by
  let updated : {A : Mat // A.PosDef} :=
    ⟨rankOneUpdatedMatrix G g α, rankOneUpdatedMatrix_posDef_of_mem_Ico G hG g hα⟩
  let m : ℝ := max ‖x‖[⟨G, hG⟩] |inner ℝ g x|
  have hα_nonneg : 0 ≤ α := hα.1
  have hone_sub_nonneg : 0 ≤ 1 - α := by
    linarith [hα.2]
  have hnorm_nonneg : 0 ≤ ‖x‖[⟨G, hG⟩] := by
    positivity
  have hm_nonneg : 0 ≤ m := by
    dsimp [m]
    exact le_trans hnorm_nonneg (le_max_left _ _)
  have hsq_base : ‖x‖[⟨G, hG⟩] ^ (2 : ℕ) ≤ m ^ (2 : ℕ) := by
    rw [sq_le_sq]
    simp [m, abs_of_nonneg hnorm_nonneg, abs_of_nonneg hm_nonneg]
  have hsq_inner : (inner ℝ g x) ^ (2 : ℕ) ≤ m ^ (2 : ℕ) := by
    rw [sq_le_sq]
    simp [m, abs_of_nonneg hm_nonneg]
  have hsq :
      ‖x‖[updated] ^ (2 : ℕ) ≤ m ^ (2 : ℕ) := by
    calc
      ‖x‖[updated] ^ (2 : ℕ)
          = (1 - α) * ‖x‖[⟨G, hG⟩] ^ (2 : ℕ) + α * (inner ℝ g x) ^ (2 : ℕ) := by
              simpa [updated] using rankOneUpdatedMatrix_primalNorm_sq_eq_combo G hG g x hα
      _ ≤ (1 - α) * m ^ (2 : ℕ) + α * m ^ (2 : ℕ) := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left hsq_base hone_sub_nonneg)
              (mul_le_mul_of_nonneg_left hsq_inner hα_nonneg)
      _ = m ^ (2 : ℕ) := by
            ring
  -- Compare squares in the nonnegative regime and then drop the squares.
  exact le_of_sq_le_sq hsq hm_nonneg

-- Proof sketch: compare support functions. For every `x`, the quadratic form of `G(α)` is bounded
-- by the maximum of the support functions of `W₁(G)` and `conv({±g})`, and the support function of
-- the convex hull is the maximum of the two support functions.
/-- The unit ellipsoid associated with `G(α)` is contained in the convex hull of `W₁(G)` and the
two points `±g`. -/
theorem rankOneUpdatedMatrix_affineEllipsoid_subset_augmentedHull
    (G : Mat) (hG : G.PosDef) (g : E) {α : ℝ}
    (hα : α ∈ Set.Ico (0 : ℝ) 1) :
    E(rankOneUpdatedMatrix G g α, (0 : E)) ⊆
      rankOneUpdateAugmentedHull G g := by
  have hUpdatedPos :
      (rankOneUpdatedMatrix G g α).PosDef :=
    rankOneUpdatedMatrix_posDef_of_mem_Ico G hG g hα
  have hHullNonempty : (rankOneUpdateAugmentedHull G g).Nonempty := by
    -- The center `0` of the base ellipsoid already lies in the augmented hull.
    refine ⟨0, ?_⟩
    rw [rankOneUpdateAugmentedHull_def]
    exact subset_convexHull ℝ _ (Or.inl (center_mem_affineEllipsoid G (0 : E)))
  have hHullClosed : IsClosed (rankOneUpdateAugmentedHull G g) :=
    (rankOneUpdateAugmentedHull_isCompact G hG g).isClosed
  have hHullConvex : Convex ℝ (rankOneUpdateAugmentedHull G g) := by
    simpa [rankOneUpdateAugmentedHull_def] using
      (convex_convexHull ℝ (E(G, (0 : E)) ∪ ({g, -g} : Set E)))
  -- Compare the two support functions after rewriting them to their explicit normal forms.
  refine subset_of_supportFunction_le_on_domain
    (E(rankOneUpdatedMatrix G g α, (0 : E))) (rankOneUpdateAugmentedHull G g)
    hHullNonempty hHullClosed hHullConvex ?_
  intro x hxdom
  rw [supportFunction_affineEllipsoid_zero_eq_coe_primalNorm
      (rankOneUpdatedMatrix G g α) hUpdatedPos,
    supportFunction_rankOneUpdateAugmentedHull_eq_max G hG g x]
  have hmax_coe :
      (((max ‖x‖[⟨G, hG⟩] |inner ℝ g x| : ℝ)) : EReal) =
        max ((((‖x‖[⟨G, hG⟩] : ℝ)) : EReal)) ((((|inner ℝ g x| : ℝ)) : EReal)) := by
    by_cases hcompare : ‖x‖[⟨G, hG⟩] ≤ |inner ℝ g x|
    · rw [max_eq_right hcompare, max_eq_right]
      exact_mod_cast hcompare
    · have hcompare' : |inner ℝ g x| ≤ ‖x‖[⟨G, hG⟩] := le_of_not_ge hcompare
      rw [max_eq_left hcompare', max_eq_left]
      exact_mod_cast hcompare'
  change
    ((((‖x‖[⟨rankOneUpdatedMatrix G g α, hUpdatedPos⟩] : ℝ)) : EReal) ≤
      max ((((‖x‖[⟨G, hG⟩] : ℝ)) : EReal)) ((((|inner ℝ g x| : ℝ)) : EReal)))
  have hreal :
      ‖x‖[⟨rankOneUpdatedMatrix G g α, hUpdatedPos⟩] ≤
        max ‖x‖[⟨G, hG⟩] |inner ℝ g x| :=
    rankOneUpdatedMatrix_primalNorm_le_max_absInner G hG g x hα
  have hrealE :
      ((((‖x‖[⟨rankOneUpdatedMatrix G g α, hUpdatedPos⟩] : ℝ)) : EReal) ≤
        (((max ‖x‖[⟨G, hG⟩] |inner ℝ g x| : ℝ)) : EReal)) := by
    exact_mod_cast hreal
  simpa [hmax_coe] using hrealE

-- Proof sketch: use the matrix determinant lemma to rewrite
-- `det (rankOneUpdatedMatrix G g α) / det G` as the closed form depending on
-- `rankOneUpdateSigma G g`.
/-- The logarithmic potential `V(α)` agrees with the determinant ratio
`log (det G(α) / det G)`. -/
theorem rankOneUpdatePotential_eq_log_det_ratio
    (G : Mat) (hG : G.PosDef) (g : E) {α : ℝ}
    (hα : α ∈ Set.Ico (0 : ℝ) 1) :
    rankOneUpdatePotential G hG g α =
      Real.log (Matrix.det (rankOneUpdatedMatrix G g α) / Matrix.det G) := by
  by_cases hn0 : n = 0
  · subst hn0
    have hg0 : g = 0 := Subsingleton.elim _ _
    subst hg0
    -- In dimension `0`, the determinants are `1`, and the scalar objective collapses to
    -- `log (1 - α) - log (1 - α)`.
    have hlog_cancel : Real.log (1 + -α) + -Real.log (1 - α) = 0 := by
      rw [show 1 + -α = 1 - α by ring]
      ring
    simpa [rankOneUpdatePotential_def, rankOneUpdatedMatrix, rankOneUpdateSigma,
      Matrix.det_fin_zero] using hlog_cancel
  have hn : 0 < n := Nat.pos_of_ne_zero hn0
  let σ := rankOneUpdateSigma G hG g
  have hσrfl : σ = rankOneUpdateSigma G hG g := rfl
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    exact Nat.cast_pred hn
  have hone_sub_pos : 0 < 1 - α := by
    linarith [hα.2]
  have hn_cast_ne : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  have harg_pos :
      0 < 1 + α * (((n : ℝ) * (1 + σ)) - 1) := by
    have hrewrite :
        1 + α * (((n : ℝ) * (1 + σ)) - 1) =
          (1 - α) + α * (‖g‖[⟨G, hG⟩,*] ^ (2 : ℕ)) := by
      rw [hσrfl, rankOneUpdateSigma_def]
      field_simp [hn_cast_ne]
      ring
    rw [hrewrite]
    have hnorm_sq_nonneg : 0 ≤ ‖g‖[⟨G, hG⟩,*] ^ (2 : ℕ) := by
      positivity
    have hterm_nonneg : 0 ≤ α * (‖g‖[⟨G, hG⟩,*] ^ (2 : ℕ)) := by
      exact mul_nonneg hα.1 hnorm_sq_nonneg
    linarith [hone_sub_pos, hterm_nonneg]
  -- Rewrite the determinant ratio into the same product of logarithmic factors as `V(α)`.
  rw [rankOneUpdatedMatrix_detRatio_of_pos G hG g hn hα, rankOneUpdatePotential_def,
    Real.log_mul (pow_ne_zero _ hone_sub_pos.ne') harg_pos.ne', Real.log_pow, hcast]
  ring

-- Proof sketch: specialize the scalar maximizer theorem
-- `centralSymmetryRoundingObjective_isMaxOn_iff` from Proposition 7.8 at
-- `σ = rankOneUpdateSigma G hG g`.
/-- For Lemma 7.4, if `2 ≤ n` and `σ = (1 / n) ‖g‖_{G,*}^2 - 1` is positive, then `V(α)` attains
its maximum on `[0, 1)` at `α* = σ / (n (1 + σ) - 1)`. -/
theorem rankOneUpdatePotential_isMaxOn_optimalAlpha
    (G : Mat) (hG : G.PosDef) (g : E) (hn : 2 ≤ n)
    (hσ : 0 < rankOneUpdateSigma G hG g) :
    IsMaxOn (rankOneUpdatePotential G hG g) (Set.Ico (0 : ℝ) 1)
      (rankOneUpdateOptimalAlpha G hG g) := by
  have hα :
      rankOneUpdateOptimalAlpha G hG g ∈ Set.Ico (0 : ℝ) 1 :=
    rankOneUpdateOptimalAlpha_mem_Ico G hG g hn hσ
  simpa [rankOneUpdatePotential, rankOneUpdateOptimalAlpha] using
    (centralSymmetryRoundingObjective_isMaxOn_iff hn hσ.le hα).2 rfl

-- Proof sketch: specialize the scalar value formula
-- `centralSymmetryRoundingObjective_alphaStar_value` from Proposition 7.8.
/-- If `2 ≤ n` and `σ = (1 / n) ‖g‖_{G,*}^2 - 1` is positive, then evaluating `V` at `α*` gives
the closed formula from Lemma 7.4. -/
theorem rankOneUpdatePotential_at_optimalAlpha
    (G : Mat) (hG : G.PosDef) (g : E) (hn : 2 ≤ n)
    (hσ : 0 < rankOneUpdateSigma G hG g) :
    rankOneUpdatePotential G hG g (rankOneUpdateOptimalAlpha G hG g) =
      Real.log (1 + rankOneUpdateSigma G hG g) +
        ((n : ℝ) - 1) *
          Real.log
            (((n : ℝ) - 1) * (1 + rankOneUpdateSigma G hG g) /
              ((n : ℝ) * (1 + rankOneUpdateSigma G hG g) - 1)) := by
  have hn' : (2 : ℝ) ≤ n := by
    exact_mod_cast hn
  have hcoeff :
      ((n : ℝ) * (1 + rankOneUpdateSigma G hG g) - 1) ≠ 0 := by
    have hcoeff_pos : 0 < (n : ℝ) * (1 + rankOneUpdateSigma G hG g) - 1 := by
      nlinarith
    exact ne_of_gt hcoeff_pos
  have hvalue :
      centralSymmetryRoundingObjective n (rankOneUpdateSigma G hG g)
          (centralSymmetryRoundingAlphaStar n (rankOneUpdateSigma G hG g)) =
        Real.log (1 + rankOneUpdateSigma G hG g) +
          ((n : ℝ) - 1) *
            Real.log
              (((n : ℝ) - 1) * (1 + rankOneUpdateSigma G hG g) /
                ((n : ℝ) * (1 + rankOneUpdateSigma G hG g) - 1)) :=
    centralSymmetryRoundingObjective_alphaStar_value hcoeff
  simpa [rankOneUpdatePotential, rankOneUpdateOptimalAlpha] using hvalue

-- Proof sketch: rewrite the second logarithm as `log (1 - t)` with
-- `t = σ / (n (1 + σ) - 1)` and apply the standard bound `log (1 - t) ≥ -t / (1 - t)`.
/-- If `2 ≤ n` and `σ = (1 / n) ‖g‖_{G,*}^2 - 1` is positive, then the optimal value of `V` is
bounded below by `log (1 + σ) - σ / (1 + σ)`. -/
theorem rankOneUpdatePotential_optimalAlpha_lower_bound_log
    (G : Mat) (hG : G.PosDef) (g : E) (hn : 2 ≤ n)
    (hσ : 0 < rankOneUpdateSigma G hG g) :
    Real.log (1 + rankOneUpdateSigma G hG g) -
        rankOneUpdateSigma G hG g / (1 + rankOneUpdateSigma G hG g) ≤
      rankOneUpdatePotential G hG g (rankOneUpdateOptimalAlpha G hG g) := by
  let σ := rankOneUpdateSigma G hG g
  have hσrfl : σ = rankOneUpdateSigma G hG g := rfl
  have hαmem : rankOneUpdateOptimalAlpha G hG g ∈ Set.Ico (0 : ℝ) 1 :=
    rankOneUpdateOptimalAlpha_mem_Ico G hG g hn hσ
  have hn' : (2 : ℝ) ≤ n := by
    exact_mod_cast hn
  have hn1_nonneg : 0 ≤ (n : ℝ) - 1 := by
    linarith
  have hn1_pos : 0 < (n : ℝ) - 1 := by
    linarith
  have hcoeff_pos : 0 < (n : ℝ) * (1 + σ) - 1 := by
    have hσ1 : 1 ≤ 1 + σ := by
      linarith
    nlinarith
  have hcoeff : ((n : ℝ) * (1 + σ) - 1) ≠ 0 := hcoeff_pos.ne'
  have hσ1_pos : 0 < 1 + σ := by
    linarith
  have hone_sub_scalar :
      ((n : ℝ) - 1) * (1 + σ) / ((n : ℝ) * (1 + σ) - 1) =
        1 - centralSymmetryRoundingAlphaStar n σ := by
    dsimp [centralSymmetryRoundingAlphaStar]
    field_simp [hcoeff]
    ring_nf
  have hone_sub :
      ((n : ℝ) - 1) * (1 + σ) / ((n : ℝ) * (1 + σ) - 1) =
        1 - rankOneUpdateOptimalAlpha G hG g := by
    -- Switch back from the scalar owner `α*` to the matrix specialization.
    simpa [rankOneUpdateOptimalAlpha, hσrfl] using hone_sub_scalar
  have hratio :
      ((n : ℝ) - 1) *
          (rankOneUpdateOptimalAlpha G hG g /
            (1 - rankOneUpdateOptimalAlpha G hG g)) =
        σ / (1 + σ) := by
    have hratio_scalar :
        ((n : ℝ) - 1) *
            (centralSymmetryRoundingAlphaStar n σ /
              (1 - centralSymmetryRoundingAlphaStar n σ)) =
          σ / (1 + σ) := by
      rw [← hone_sub_scalar]
      dsimp [centralSymmetryRoundingAlphaStar]
      field_simp [hcoeff, hσ1_pos.ne', hn1_pos.ne']
    -- Reuse the scalar ratio identity after identifying the specialized `α*`.
    simpa [rankOneUpdateOptimalAlpha, hσrfl] using hratio_scalar
  have hbound_raw :
      -(((n : ℝ) - 1) * Real.log (1 - rankOneUpdateOptimalAlpha G hG g)) ≤
        ((n : ℝ) - 1) *
          (rankOneUpdateOptimalAlpha G hG g /
            (1 - rankOneUpdateOptimalAlpha G hG g)) := by
    have hbase := negLogOneSub_le_div_of_mem_Ico hαmem
    have hmul := mul_le_mul_of_nonneg_left hbase hn1_nonneg
    simpa [neg_mul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hmul
  have hbound :
      -(σ / (1 + σ)) ≤
        ((n : ℝ) - 1) * Real.log (1 - rankOneUpdateOptimalAlpha G hG g) := by
    rw [hratio] at hbound_raw
    linarith
  have hvalue :
      rankOneUpdatePotential G hG g (rankOneUpdateOptimalAlpha G hG g) =
        Real.log (1 + σ) +
          ((n : ℝ) - 1) * Real.log (1 - rankOneUpdateOptimalAlpha G hG g) := by
    -- Rewrite the second logarithmic argument in the closed formula as `1 - α*`.
    rw [rankOneUpdatePotential_at_optimalAlpha G hG g hn hσ, hσrfl, hone_sub]
  -- Insert the logarithmic lower bound into the explicit value formula at `α*`.
  calc
    Real.log (1 + σ) - σ / (1 + σ)
        = Real.log (1 + σ) + (-(σ / (1 + σ))) := by
            ring
    _ ≤ Real.log (1 + σ) +
          (((n : ℝ) - 1) * Real.log (1 - rankOneUpdateOptimalAlpha G hG g)) := by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_left hbound (Real.log (1 + σ))
    _ = rankOneUpdatePotential G hG g (rankOneUpdateOptimalAlpha G hG g) := by
          rw [hvalue]

-- Proof sketch: compare the function
-- `σ ↦ log (1 + σ) - σ / (1 + σ) - σ^2 / ((1 + σ) (2 + σ))`
-- with `0` by differentiating and checking that its derivative is nonnegative on `σ ≥ 0`.
/-- Lemma 7.4: if `2 ≤ n` and `σ = (1 / n) ‖g‖_{G,*}^2 - 1` is positive, then the optimal value
of `V` is bounded below by `σ² / ((1 + σ) (2 + σ))`. -/
theorem rankOneUpdatePotential_optimalAlpha_lower_bound_rational
    (G : Mat) (hG : G.PosDef) (g : E) (hn : 2 ≤ n)
    (hσ : 0 < rankOneUpdateSigma G hG g) :
    (rankOneUpdateSigma G hG g ^ (2 : ℕ)) /
        ((1 + rankOneUpdateSigma G hG g) * (2 + rankOneUpdateSigma G hG g)) ≤
      rankOneUpdatePotential G hG g (rankOneUpdateOptimalAlpha G hG g) := by
  let σ := rankOneUpdateSigma G hG g
  have hgap : σ ^ (2 : ℕ) / ((1 + σ) * (2 + σ)) ≤
      Real.log (1 + σ) - σ / (1 + σ) :=
    sigmaLogGap_ge_rational hσ.le
  have hlog :
      Real.log (1 + σ) - σ / (1 + σ) ≤
        rankOneUpdatePotential G hG g (rankOneUpdateOptimalAlpha G hG g) :=
    rankOneUpdatePotential_optimalAlpha_lower_bound_log G hG g hn hσ
  -- Chain the scalar gap estimate with the logarithmic lower bound at `α*`.
  exact le_trans hgap hlog
