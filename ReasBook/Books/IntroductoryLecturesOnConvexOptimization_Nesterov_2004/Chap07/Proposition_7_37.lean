/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_23

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open scoped PositiveDefMatrixNorm

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Proposition 7.37 lies in Chapter 7's positive-definite matrix / weighted dual-norm /
rank-one-update domain.

Relevant owner-style declarations sampled before refinement:
- `positiveDefMatrixNorm` and the notation `‖g‖[G,*]` in `Definition_7_23`, the chapter owner for
  the dual norm attached to a positive-definite matrix;
- `positiveDefMatrixNorm_dualNorm_eq_sqrt_inner_inv` in `Definition_7_23`, the canonical bridge
  from that owner to the inverse-matrix quadratic form `√⟪g, G⁻¹ g⟫`;
- `rankOneUpdatedMatrix` in `Lemma_7_4`, the chapter owner for the basic interpolation
  `(1 - α) G + α ggᵀ`;
- mathlib `Matrix.add_mul_mul_inv_eq_sub`, the Woodbury/binomial inverse owner for inverse
  formulas of rank-one perturbations.

Best owner abstraction:
- source-facing: Proposition 7.37's quasi-Newton Hessian update with coefficient
  `(δ / (1 - δ)) / ‖g‖[G,*]^2`;
- core/canonical: the Chapter 7 dual norm owner `‖g‖[G,*]`;
- bridge/view: the update-expansion and inverse-expansion theorems below.

Primitive data:
- a positive-definite Hessian matrix `G`;
- a vector `g`;
- the accuracy parameter `δ`.

Derived API:
- the squared dual norm appears as `‖g‖[G,*] ^ 2`, derived from the existing owner rather than as
  a second local definition;
- the rank-one update formula and its inverse identity.

The duplicate wheel in the previous version was the local scalar owner
`quasiNewtonDualNormSq`. This refinement deletes that duplicate and rewrites the source-facing
update directly in terms of the chapter owner `‖g‖[G,*]`.
-/

/-- The rank-one Hessian update
`G + (δ / (1 - δ)) * (ggᵀ / ‖g‖_{G}^{*2})` from the relative-accuracy quasi-Newton scheme,
written using the canonical Chapter 7 dual norm owner. -/
def quasiNewtonUpdatedHessian
    (δ : ℝ) (G : {G : Matrix (Fin n) (Fin n) ℝ // G.PosDef}) (g : E) :
    Matrix (Fin n) (Fin n) ℝ :=
  G.1 + ((δ / (1 - δ)) / (‖g‖[G,*] ^ (2 : ℕ))) • Matrix.vecMulVec g g

/-- Expanding `quasiNewtonUpdatedHessian δ G g` gives the displayed rank-one update formula for
the next Hessian matrix. -/
-- Proof sketch: unfold `quasiNewtonUpdatedHessian`.
theorem quasiNewtonUpdatedHessian_def
    (δ : ℝ) (G : {G : Matrix (Fin n) (Fin n) ℝ // G.PosDef}) (g : E) :
    quasiNewtonUpdatedHessian δ G g =
      G.1 + ((δ / (1 - δ)) / (‖g‖[G,*] ^ (2 : ℕ))) • Matrix.vecMulVec g g := rfl

/-- Helper for Proposition 7.37: the scalar coefficient in the rank-one update is nonnegative
when `δ ∈ (0, 1)`. -/
private theorem quasi_newton_updateCoeff_nonneg
    {δ : ℝ} (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (G : {G : Matrix (Fin n) (Fin n) ℝ // G.PosDef}) (g : E) :
    0 ≤ ((δ / (1 - δ)) / (‖g‖[G,*] ^ (2 : ℕ))) := by
  -- The numerator and denominator are both nonnegative under `δ ∈ (0, 1)`.
  have hdelta_nonneg : 0 ≤ δ / (1 - δ) := by
    have hδ_pos : 0 < δ := hδ.1
    have hone_sub_pos : 0 < 1 - δ := sub_pos.mpr hδ.2
    positivity
  have hnormsq_nonneg : 0 ≤ ‖g‖[G,*] ^ (2 : ℕ) := by
    positivity
  exact div_nonneg hdelta_nonneg hnormsq_nonneg

/-- Helper for Proposition 7.37: squaring the Chapter 7 dual norm recovers the inverse-matrix
quadratic form. -/
private theorem dual_norm_sq_eq_inner_inv
    (G : {G : Matrix (Fin n) (Fin n) ℝ // G.PosDef}) (g : E) :
    ‖g‖[G,*] ^ (2 : ℕ) = inner ℝ g ((Matrix.toEuclideanLin G.1⁻¹) g) := by
  -- Rewrite the square through the canonical dual-norm formula from Definition 7.23.
  have hinner_eq_dotProduct :
      inner ℝ g ((Matrix.toEuclideanLin G.1⁻¹) g) =
        g.ofLp ⬝ᵥ (G.1⁻¹ *ᵥ g.ofLp) := by
    change ((Matrix.toEuclideanLin G.1⁻¹) g).ofLp ⬝ᵥ star g.ofLp =
      g.ofLp ⬝ᵥ (G.1⁻¹ *ᵥ g.ofLp)
    rw [Matrix.toEuclideanLin_apply, dotProduct_comm]
    simp
  have harg_nonneg :
      0 ≤ inner ℝ g ((Matrix.toEuclideanLin G.1⁻¹) g) := by
    have hnonneg : 0 ≤ g.ofLp ⬝ᵥ (G.1⁻¹ *ᵥ g.ofLp) := by
      simpa using G.2.inv.posSemidef.dotProduct_mulVec_nonneg g.ofLp
    rw [hinner_eq_dotProduct]
    exact hnonneg
  calc
    ‖g‖[G,*] ^ (2 : ℕ)
        = (Real.sqrt (inner ℝ g ((Matrix.toEuclideanLin G.1⁻¹) g))) ^ (2 : ℕ) := by
            rw [positiveDefMatrixNorm_dualNorm_eq_sqrt_inner_inv]
    _ = inner ℝ g ((Matrix.toEuclideanLin G.1⁻¹) g) := by
          exact Real.sq_sqrt harg_nonneg

/-- Helper for Proposition 7.37: the original matrix cancels the inverse action on Euclidean
vectors. -/
private theorem toEuclideanLin_nonsing_inv_comp
    (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef) (x : E) :
    G.toEuclideanLin ((G⁻¹).toEuclideanLin x) = x := by
  -- Convert the Euclidean action back to `mulVec` and use the matrix inverse identity.
  have hGdet : IsUnit G.det := isUnit_iff_ne_zero.mpr (ne_of_gt hG.det_pos)
  have hmul : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv G hGdet
  ext i
  simp [Matrix.mulVec_mulVec, hmul]

/-- Helper for Proposition 7.37: for a Hermitian real matrix, row multiplication agrees with the
Euclidean linear action. -/
private theorem vecMul_eq_toEuclideanLin_of_isHermitian
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) (x : E) :
    x.ofLp ᵥ* A = (A.toEuclideanLin x).ofLp := by
  -- Rewrite the row action through the transpose, then use symmetry of the real Hermitian matrix.
  have hAT : Aᵀ = A := by
    simpa using hA.eq
  simpa [Matrix.ofLp_toLpLin, hAT] using (Matrix.vecMul_transpose Aᵀ x.ofLp)

/-- Helper for Proposition 7.37: the squared dual norm is strictly positive away from the zero
vector. -/
private theorem dual_norm_sq_pos
    (G : {G : Matrix (Fin n) (Fin n) ℝ // G.PosDef}) {g : E} (hg : g ≠ 0) :
    0 < ‖g‖[G,*] ^ (2 : ℕ) := by
  -- After rewriting by `G⁻¹`, positivity is the positive-definite quadratic form inequality.
  rw [dual_norm_sq_eq_inner_inv]
  have hg_coord : g.ofLp ≠ 0 := by
    intro hg_zero
    apply hg
    exact congrArg (WithLp.toLp 2) hg_zero
  have hdot : 0 < g.ofLp ⬝ᵥ (G.1⁻¹ *ᵥ g.ofLp) := by
    simpa using G.2.inv.dotProduct_mulVec_pos hg_coord
  have hinner_eq_dotProduct :
      inner ℝ g ((Matrix.toEuclideanLin G.1⁻¹) g) =
        g.ofLp ⬝ᵥ (G.1⁻¹ *ᵥ g.ofLp) := by
    change ((Matrix.toEuclideanLin G.1⁻¹) g).ofLp ⬝ᵥ star g.ofLp =
      g.ofLp ⬝ᵥ (G.1⁻¹ *ᵥ g.ofLp)
    rw [Matrix.toEuclideanLin_apply, dotProduct_comm]
    simp
  rw [hinner_eq_dotProduct]
  exact hdot

/-- The rank-one update preserves positive definiteness when `δ ∈ (0, 1)`. -/
-- Proof sketch: the update coefficient is nonnegative for `δ ∈ (0, 1)`, and
-- `Matrix.vecMulVec g g` is positive semidefinite. A positive-definite matrix plus a
-- nonnegative multiple of this rank-one form remains positive definite.
theorem quasiNewtonUpdatedHessian_posDef
    {δ : ℝ} (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (G : {G : Matrix (Fin n) (Fin n) ℝ // G.PosDef}) (g : E) :
    (quasiNewtonUpdatedHessian δ G g).PosDef := by
  -- Unfold the update and add a nonnegative rank-one positive-semidefinite term to `G`.
  rw [quasiNewtonUpdatedHessian_def]
  exact G.2.add_posSemidef
    ((Matrix.posSemidef_vecMulVec_self_star g).smul (quasi_newton_updateCoeff_nonneg hδ G g))

/-- Helper for Proposition 7.37: the rank-one Hessian update satisfies the displayed inverse
formula. -/
private theorem quasiNewtonUpdatedHessian_inv
    {δ : ℝ} (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (G : {G : Matrix (Fin n) (Fin n) ℝ // G.PosDef}) (g : E) :
    (quasiNewtonUpdatedHessian δ G g)⁻¹ =
      G.1⁻¹ - (δ / (‖g‖[G,*] ^ (2 : ℕ))) •
        (G.1⁻¹ * Matrix.vecMulVec g g * G.1⁻¹) := by
  by_cases hg : g = 0
  · -- In the zero-gradient case, every rank-one term vanishes and the update is trivial.
    subst hg
    simp [quasiNewtonUpdatedHessian]
  · -- For `g ≠ 0`, verify the Sherman-Morrison candidate as a right inverse.
    let q : ℝ := ‖g‖[G,*] ^ (2 : ℕ)
    let c : ℝ := (δ / (1 - δ)) / q
    let η : ℝ := δ / q
    let Hg : E := (Matrix.toEuclideanLin G.1⁻¹) g
    have hq_eq : q = inner ℝ g Hg := by
      simp [q, Hg, dual_norm_sq_eq_inner_inv]
    have hq_pos : 0 < q := by
      simpa [q] using dual_norm_sq_pos G hg
    have hq_ne : q ≠ 0 := ne_of_gt hq_pos
    have hone_sub_ne : 1 - δ ≠ 0 := by
      linarith [hδ.2]
    have hGdet : IsUnit G.1.det := isUnit_iff_ne_zero.mpr (ne_of_gt G.2.det_pos)
    have hmulVec : G.1 *ᵥ Hg.ofLp = g.ofLp := by
      ext i
      simpa [Hg, Matrix.ofLp_toLpLin] using
        congrArg (fun v : E ↦ v i) (toEuclideanLin_nonsing_inv_comp G.1 G.2 g)
    have hrowInv : g.ofLp ᵥ* G.1⁻¹ = Hg.ofLp := by
      simpa [Hg] using vecMul_eq_toEuclideanLin_of_isHermitian G.1⁻¹ G.2.inv.isHermitian g
    have hdot : g.ofLp ⬝ᵥ Hg.ofLp = q := by
      calc
        g.ofLp ⬝ᵥ Hg.ofLp = inner ℝ g Hg := by
          simpa [dotProduct_comm] using (EuclideanSpace.inner_eq_star_dotProduct g Hg).symm
        _ = q := by
          exact hq_eq.symm
    have hrank :
        G.1⁻¹ * Matrix.vecMulVec g g * G.1⁻¹ = Matrix.vecMulVec Hg Hg := by
      calc
        G.1⁻¹ * Matrix.vecMulVec g g * G.1⁻¹
            = Matrix.vecMulVec Hg g * G.1⁻¹ := by
                rw [Matrix.mul_vecMulVec]
                simp [Hg, Matrix.toEuclideanLin_apply]
        _ = Matrix.vecMulVec Hg Hg := by
              rw [Matrix.vecMulVec_mul, hrowInv]
    have hright :
        quasiNewtonUpdatedHessian δ G g * (G.1⁻¹ - η • Matrix.vecMulVec Hg Hg) = 1 := by
      have hmul₁ :
          G.1 * (η • Matrix.vecMulVec Hg Hg) = η • Matrix.vecMulVec g Hg := by
        rw [Matrix.mul_smul, Matrix.mul_vecMulVec]
        rw [hmulVec]
      have hmul₂ :
          (c • Matrix.vecMulVec g g) * G.1⁻¹ = c • Matrix.vecMulVec g Hg := by
        rw [smul_mul_assoc, Matrix.vecMulVec_mul, hrowInv]
      have hmul₃ :
          (c • Matrix.vecMulVec g g) * (η • Matrix.vecMulVec Hg Hg) =
            (c * η * q) • Matrix.vecMulVec g Hg := by
        rw [smul_mul_assoc, mul_smul_comm, Matrix.vecMulVec_mul_vecMulVec, hdot]
        simp [smul_smul, mul_assoc]
      have hcoef : -η + c - c * η * q = 0 := by
        dsimp [η, c]
        field_simp [hq_ne, hone_sub_ne]
        ring
      calc
        quasiNewtonUpdatedHessian δ G g * (G.1⁻¹ - η • Matrix.vecMulVec Hg Hg)
            = (G.1 + c • Matrix.vecMulVec g g) * (G.1⁻¹ - η • Matrix.vecMulVec Hg Hg) := by
                simp [quasiNewtonUpdatedHessian, c, q]
        _ = G.1 * G.1⁻¹ - G.1 * (η • Matrix.vecMulVec Hg Hg)
              + (c • Matrix.vecMulVec g g) * G.1⁻¹
              - (c • Matrix.vecMulVec g g) * (η • Matrix.vecMulVec Hg Hg) := by
                rw [add_mul, mul_sub, mul_sub]
                abel
        _ = 1 - η • Matrix.vecMulVec g Hg + c • Matrix.vecMulVec g Hg
              - (c * η * q) • Matrix.vecMulVec g Hg := by
                rw [Matrix.mul_nonsing_inv _ hGdet, hmul₁, hmul₂, hmul₃]
        _ = 1 + (-η + c - c * η * q) • Matrix.vecMulVec g Hg := by
              ext i j
              simp [sub_eq_add_neg]
              ring
        _ = 1 := by
              rw [hcoef, zero_smul, add_zero]
    -- Rewrite the verified right inverse back into the source-facing matrix expression.
    calc
      (quasiNewtonUpdatedHessian δ G g)⁻¹ = G.1⁻¹ - η • Matrix.vecMulVec Hg Hg := by
        exact Matrix.inv_eq_right_inv hright
      _ = G.1⁻¹ - η • (G.1⁻¹ * Matrix.vecMulVec g g * G.1⁻¹) := by
            rw [hrank]
      _ = G.1⁻¹ - (δ / (‖g‖[G,*] ^ (2 : ℕ))) •
            (G.1⁻¹ * Matrix.vecMulVec g g * G.1⁻¹) := by
              simp [η, q]

-- Proof sketch: the first identity is the definition of `quasiNewtonUpdatedHessian`. For the
-- second, apply the Sherman-Morrison formula to `G + u uᵀ` with
-- `u = √((δ / (1 - δ)) / ‖g‖[G,*]^2) • g`, then simplify the scalar factor using
-- `1 + (δ / (1 - δ)) = (1 - δ)⁻¹`.
/-- Proposition 7.37: if `ψ_k` is a quadratic estimating function with positive-definite Hessian
`G_k`, then the next Hessian is obtained by the rank-one update
`G_{k+1} = G_k + (δ / (1 - δ)) * g_k g_kᵀ / ‖g_k‖_{G_k}^{*2}`, and its inverse satisfies the
Sherman-Morrison identity
`G_{k+1}^{-1} = G_k^{-1} - δ * G_k^{-1} g_k g_kᵀ G_k^{-1} / ‖g_k‖_{G_k}^{*2}`. -/
theorem quasiNewtonRankOneHessianUpdate_and_inverse
    {δ : ℝ} (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (Gk : {G : Matrix (Fin n) (Fin n) ℝ // G.PosDef}) (gk : E) :
    quasiNewtonUpdatedHessian δ Gk gk =
      Gk.1 + ((δ / (1 - δ)) / (‖gk‖[Gk,*] ^ (2 : ℕ))) • Matrix.vecMulVec gk gk ∧
    (quasiNewtonUpdatedHessian δ Gk gk)⁻¹ =
      Gk.1⁻¹ - (δ / (‖gk‖[Gk,*] ^ (2 : ℕ))) •
        (Gk.1⁻¹ * Matrix.vecMulVec gk gk * Gk.1⁻¹) := by
  constructor
  · -- The first conjunct is exactly the defining rank-one update formula.
    exact quasiNewtonUpdatedHessian_def δ Gk gk
  · -- The second conjunct is the Sherman-Morrison inverse identity proved above.
    exact quasiNewtonUpdatedHessian_inv hδ Gk gk

end
