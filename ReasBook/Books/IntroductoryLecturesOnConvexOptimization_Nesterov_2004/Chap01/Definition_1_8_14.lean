/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Matrix.Hermitian
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_8_11

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix InnerProductSpace LinearMap

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/-
Definition 1.8.14 is `source-facing` through the Broyden--Fletcher--Goldfarb--Shanno correction
`ΔHₖ`, with the next inverse-Hessian approximation and the algorithmic update rule derived from
that increment.

Primary domain:
- quasi-Newton inverse-Hessian updates on Euclidean space.

Owner abstractions sampled before refinement:
- the direct secant equation `HkNext.toEuclideanLin γk = δk`, recalled in
  `Definition_1_8_11`
- `Matrix.toEuclideanLin`
- `InnerProductSpace.rankOne`
- `LinearMap.adjoint`

Primitive data:
- the current inverse-Hessian approximation `Hk`
- the gradient difference `γk`
- the step `δk`

Derived API:
- the source-facing BFGS increment `bfgsMatrixDifference`
- the next inverse-Hessian approximation `bfgsUpdatedMatrix = Hk + ΔHₖ`
- the secant-equation and positive-definiteness consequences under the usual curvature hypotheses
- the direct specialization of the secant equation to consecutive gradient and iterate differences

Layer triage:
- `source-facing`: `bfgsMatrixDifference`
- `core/canonical`: the direct secant equation from `Definition_1_8_11`,
  `Matrix.toEuclideanLin`, `Matrix.PosDef`, `InnerProductSpace.rankOne`, `LinearMap.adjoint`
- `bridge/view`: `bfgsUpdatedMatrix`,
  `bfgsUpdatedMatrix_step_secantEquation`
-/
private abbrev bfgsDifferenceOperator (Hk : Mat) (γk δk : E) : E →ₗ[ℝ] E :=
  let H := Hk.toEuclideanLin
  let rho : ℝ := (inner ℝ γk δk)⁻¹
  let hγ := H γk
  let beta := 1 + inner ℝ hγ γk * rho
  H + (beta * rho) • rankOne ℝ δk δk -
    rho • (rankOne ℝ hγ δk + rankOne ℝ δk (adjoint H γk))

/-- Definition 1.8.14: `ΔHₖ` is the Broyden--Fletcher--Goldfarb--Shanno (BFGS) correction
`(βₖ / ⟪γₖ, δₖ⟫) δₖ δₖᵀ - (Hₖ γₖ δₖᵀ + δₖ γₖᵀ Hₖ) / ⟪γₖ, δₖ⟫`,
where `βₖ = 1 + ⟪Hₖ γₖ, γₖ⟫ / ⟪γₖ, δₖ⟫`. The curvature hypotheses belong on the secant and
positivity theorems rather than on this source-facing matrix formula. -/
def bfgsMatrixDifference (Hk : Mat) (γk δk : E) : Mat :=
  toEuclideanLin.symm (bfgsDifferenceOperator Hk γk δk - Hk.toEuclideanLin)

/-- The BFGS correction matrix realizes the canonical operator-level BFGS formula on Euclidean
space. -/
theorem bfgsMatrixDifference_toEuclideanLin (Hk : Mat) (γk δk : E) :
    (bfgsMatrixDifference Hk γk δk).toEuclideanLin =
      let H := Hk.toEuclideanLin
      let rho : ℝ := (inner ℝ γk δk)⁻¹
      let hγ := H γk
      let beta := 1 + inner ℝ hγ γk * rho
      (beta * rho) • rankOne ℝ δk δk -
        rho • (rankOne ℝ hγ δk + rankOne ℝ δk (adjoint H γk)) := by
  rw [bfgsMatrixDifference]
  simp only [LinearEquiv.apply_symm_apply]
  dsimp [bfgsDifferenceOperator]
  abel

/-- The BFGS update defines the next inverse-Hessian approximation by `Hₖ₊₁ = Hₖ + ΔHₖ`. -/
def bfgsUpdatedMatrix (Hk : Mat) (γk δk : E) : Mat :=
  Hk + bfgsMatrixDifference Hk γk δk

/-- Helper for Definition 1.8.14: evaluating the adjoint on the same vector recovers the same
quadratic scalar as evaluating the original map. -/
theorem inner_adjoint_apply_self_eq_inner_apply_self (H : E →ₗ[ℝ] E) (γ : E) :
    inner ℝ (LinearMap.adjoint H γ) γ = inner ℝ γ (H γ) := by
  -- Rewrite the left inner product through the adjoint pairing and then commute the real inner
  -- product back to the source-side quadratic scalar.
  calc
    inner ℝ (LinearMap.adjoint H γ) γ =
        inner ℝ γ (LinearMap.adjoint H γ) := by
      rw [real_inner_comm]
    _ = inner ℝ (H γ) γ := by
      simpa using LinearMap.adjoint_inner_right H γ γ
    _ = inner ℝ γ (H γ) := by
      rw [real_inner_comm]

/-- Helper for Definition 1.8.14: the BFGS-updated matrix realizes the canonical operator-level
BFGS formula on Euclidean space. -/
theorem bfgsUpdatedMatrix_toEuclideanLin (Hk : Mat) (γk δk : E) :
    (bfgsUpdatedMatrix Hk γk δk).toEuclideanLin =
      let H := Hk.toEuclideanLin
      let rho : ℝ := (inner ℝ γk δk)⁻¹
      let hγ := H γk
      let beta := 1 + inner ℝ hγ γk * rho
      H + (beta * rho) • rankOne ℝ δk δk -
        rho • (rankOne ℝ hγ δk + rankOne ℝ δk (adjoint H γk)) := by
  -- The updated operator is exactly the original map plus the canonical BFGS correction term.
  rw [bfgsUpdatedMatrix]
  rw [LinearEquiv.map_add]
  rw [bfgsMatrixDifference_toEuclideanLin]
  simp [sub_eq_add_neg, add_assoc]

/-- Helper for Definition 1.8.14: symmetry of `Hₖ` lets us swap `Hₖ` across the Euclidean inner
product. -/
theorem isSymm_inner_toEuclideanLin_swap (Hk : Mat) (hHk : Hk.IsSymm) (x y : E) :
    inner ℝ x (Hk.toEuclideanLin y) = inner ℝ (Hk.toEuclideanLin x) y := by
  -- Transport matrix symmetry to the linear operator view and use the defining symmetric identity.
  have hsymm : (Hk.toEuclideanLin : E →ₗ[ℝ] E).IsSymmetric :=
    (Matrix.isSymmetric_toEuclideanLin_iff (A := Hk)).2 <| by
      simpa [Matrix.IsSymm, Matrix.IsHermitian] using hHk
  exact (hsymm x y).symm

/-- Helper for Definition 1.8.14: when `Hₖ` is symmetric, the BFGS operator has the standard
factorized form `(I - ρ δ γᵀ) Hₖ (I - ρ γ δᵀ) + ρ δ δᵀ`. -/
theorem bfgsUpdatedMatrix_toEuclideanLin_factorized (Hk : Mat) (γk δk : E)
    (hHk : Hk.IsSymm) :
    (bfgsUpdatedMatrix Hk γk δk).toEuclideanLin =
      let H := Hk.toEuclideanLin
      let rho : ℝ := (inner ℝ γk δk)⁻¹
      (((1 : E →ₗ[ℝ] E) - rho • rankOne ℝ δk γk) * H *
        ((1 : E →ₗ[ℝ] E) - rho • rankOne ℝ γk δk)) +
        rho • rankOne ℝ δk δk := by
  -- Route correction: expand the factorization at a test vector and rewrite the mixed
  -- `⟪γₖ, Hₖ x⟫` term only once using symmetry of `Hₖ.toEuclideanLin`.
  rw [bfgsUpdatedMatrix_toEuclideanLin]
  dsimp
  have hsymm : (Hk.toEuclideanLin : E →ₗ[ℝ] E).IsSymmetric :=
    (Matrix.isSymmetric_toEuclideanLin_iff (A := Hk)).2 <| by
      simpa [Matrix.IsSymm, Matrix.IsHermitian] using hHk
  have hAdj : LinearMap.adjoint (Hk.toEuclideanLin : E →ₗ[ℝ] E) = Hk.toEuclideanLin := by
    simpa using hsymm.adjoint_eq
  -- Compare the two operators coordinatewise after one common expansion.
  ext x i
  simp only [smul_add, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
    ContinuousLinearMap.coe_coe, rankOne_apply, PiLp.sub_apply, PiLp.add_apply, ofLp_toLpLin,
    toLin'_apply, PiLp.smul_apply, smul_eq_mul, Module.End.mul_apply, Module.End.one_apply,
    map_sub, map_smul]
  rw [hAdj, isSymm_inner_toEuclideanLin_swap Hk hHk γk γk,
    isSymm_inner_toEuclideanLin_swap Hk hHk γk x]
  ring_nf

/-- Helper for Definition 1.8.14: the left BFGS rank-one perturbation is the adjoint of the
corresponding right perturbation. -/
theorem bfgs_rankOne_perturbation_adjoint (γk δk : E) (rho : ℝ) :
    ((1 : E →ₗ[ℝ] E) - rho • rankOne ℝ δk γk) =
      ((1 : E →ₗ[ℝ] E) - rho • rankOne ℝ γk δk).adjoint := by
  -- Verify the adjoint identity through the defining inner-product relation.
  rw [LinearMap.eq_adjoint_iff]
  intro x y
  simp [rankOne_apply, sub_eq_add_neg, smul_smul, real_inner_comm, inner_add_left,
    inner_add_right, inner_smul_left, inner_smul_right, mul_comm]
  ring

/-- Helper for Definition 1.8.14: a positive-definite matrix yields a strictly positive Euclidean
quadratic form on every nonzero vector. -/
theorem posDef_inner_toEuclideanLin_pos (Hk : Mat) (hHkPosDef : Hk.PosDef) {x : E} (hx : x ≠ 0) :
    0 < inner ℝ x (Hk.toEuclideanLin x) := by
  have hx' : x.ofLp ≠ 0 := by
    simpa using hx
  have hdot : 0 < x.ofLp ⬝ᵥ Hk *ᵥ x.ofLp := hHkPosDef.dotProduct_mulVec_pos (x := x.ofLp) hx'
  calc
    0 < x.ofLp ⬝ᵥ Hk *ᵥ x.ofLp := hdot
    _ = (Hk.toEuclideanLin x).ofLp ⬝ᵥ x.ofLp := by
      simp [Matrix.ofLp_toLpLin, Matrix.toLin'_apply, dotProduct_comm]
    _ = inner ℝ x (Hk.toEuclideanLin x) := by
      simpa using (EuclideanSpace.inner_eq_star_dotProduct x (Hk.toEuclideanLin x)).symm

/-- Helper for Definition 1.8.14: a positive-definite `Hₖ` gives a strictly positive quadratic
form for the updated BFGS operator under the curvature condition. -/
theorem bfgsUpdatedMatrix_inner_pos (Hk : Mat) (γk δk : E) (hHkPosDef : Hk.PosDef)
    (hγδ : 0 < inner ℝ γk δk) {x : E} (hx : x ≠ 0) :
    0 < inner ℝ x ((bfgsUpdatedMatrix Hk γk δk).toEuclideanLin x) := by
  have hHkSymm : Hk.IsSymm := by
    simpa using hHkPosDef.1
  let rho : ℝ := (inner ℝ γk δk)⁻¹
  let S : E →ₗ[ℝ] E := (1 : E →ₗ[ℝ] E) - rho • rankOne ℝ γk δk
  have hrepr : (bfgsUpdatedMatrix Hk γk δk).toEuclideanLin =
      ((1 : E →ₗ[ℝ] E) - rho • rankOne ℝ δk γk) * Hk.toEuclideanLin * S +
        rho • rankOne ℝ δk δk := by
    simpa [S, rho] using bfgsUpdatedMatrix_toEuclideanLin_factorized Hk γk δk hHkSymm
  -- The factorization exposes the transported vector `v = (I - ρ γ δᵀ) x`.
  rw [hrepr, bfgs_rankOne_perturbation_adjoint γk δk rho]
  let v : E := S x
  have hrho : 0 < rho := by
    dsimp [rho]
    exact inv_pos.mpr hγδ
  have hdecomp :
      inner ℝ x ((S.adjoint * Hk.toEuclideanLin * S + rho • rankOne ℝ δk δk) x) =
        inner ℝ v (Hk.toEuclideanLin v) + rho * (inner ℝ δk x)^2 := by
    -- Move the left factor across the inner product and collect the explicit rank-one term.
    dsimp [v]
    simp only [inner_add_right, inner_smul_right]
    rw [LinearMap.adjoint_inner_right, real_inner_comm x δk]
    ring_nf
  rw [hdecomp]
  by_cases hv : v = 0
  · -- If the transported vector vanishes, the curvature term must carry the positivity.
    have hs : inner ℝ δk x ≠ 0 := by
      intro hs0
      apply hx
      dsimp [v, S, rho] at hv
      ext i
      have hi := congrArg (fun z : E => z.ofLp i) hv
      simp only [hs0, PiLp.zero_apply, PiLp.sub_apply, PiLp.smul_apply, zero_smul] at hi
      simpa using hi
    have hsq : 0 < (inner ℝ δk x)^2 := sq_pos_of_ne_zero hs
    have hterm : 0 < rho * (inner ℝ δk x)^2 := mul_pos hrho hsq
    simpa [hv] using hterm
  · -- Otherwise the conjugated positive-definite quadratic form is already strictly positive.
    have hmain : 0 < inner ℝ v (Hk.toEuclideanLin v) :=
      posDef_inner_toEuclideanLin_pos Hk hHkPosDef hv
    have hterm : 0 ≤ rho * (inner ℝ δk x)^2 := mul_nonneg hrho.le (sq_nonneg _)
    linarith

/-- The BFGS updated matrix remains symmetric when the current quasi-Newton matrix is symmetric. -/
-- Proof sketch: `Hₖ` is symmetric by hypothesis, `δₖ δₖᵀ` is symmetric, and if `Hₖ` is symmetric
-- then `(Hₖᵀ) γₖ = Hₖ γₖ`, so the mixed term in `ΔHₖ` is the sum of a matrix and its transpose.
theorem bfgsUpdatedMatrix_isSymm (Hk : Mat) (γk δk : E) (hHk : Hk.IsSymm) :
    (bfgsUpdatedMatrix Hk γk δk).IsSymm := by
  apply (Matrix.isSymmetric_toEuclideanLin_iff (A := bfgsUpdatedMatrix Hk γk δk)).1
  let rho : ℝ := (inner ℝ γk δk)⁻¹
  let S : E →ₗ[ℝ] E := (1 : E →ₗ[ℝ] E) - rho • rankOne ℝ γk δk
  have hrepr : (bfgsUpdatedMatrix Hk γk δk).toEuclideanLin =
      ((1 : E →ₗ[ℝ] E) - rho • rankOne ℝ δk γk) * Hk.toEuclideanLin * S +
        rho • rankOne ℝ δk δk := by
    simpa [S, rho] using bfgsUpdatedMatrix_toEuclideanLin_factorized Hk γk δk hHk
  have hsymm : (Hk.toEuclideanLin : E →ₗ[ℝ] E).IsSymmetric :=
    (Matrix.isSymmetric_toEuclideanLin_iff (A := Hk)).2 <| by
      simpa [Matrix.IsSymm, Matrix.IsHermitian] using hHk
  -- Replace the left perturbation by the adjoint of the right perturbation.
  rw [hrepr, bfgs_rankOne_perturbation_adjoint γk δk rho]
  have hconj : (S.adjoint * Hk.toEuclideanLin * S).IsSymmetric :=
    hsymm.adjoint_conj S
  have hrank : (rankOne ℝ δk δk : E →ₗ[ℝ] E).IsSymmetric := by
    simp
  have hrho : star rho = rho := by
    simp [rho]
  -- The factorized term is symmetric by conjugation, and the correction is a symmetric rank-one
  -- operator scaled by a real scalar.
  exact hconj.add (LinearMap.IsSymmetric.smul hrho hrank)

/-- Helper for Definition 1.8.14: the Euclidean quadratic form of `A.toEuclideanLin` matches the
matrix quadratic form `xᵀ A x`. -/
theorem inner_toEuclideanLin_eq_dotProduct_mulVec (A : Mat) (x : E) :
    inner ℝ x (A.toEuclideanLin x) = x.ofLp ⬝ᵥ A *ᵥ x.ofLp := by
  -- First view the Euclidean inner product as a dot product, then unfold the matrix action.
  calc
    inner ℝ x (A.toEuclideanLin x) = (A.toEuclideanLin x).ofLp ⬝ᵥ x.ofLp := by
      simpa using (EuclideanSpace.inner_eq_star_dotProduct x (A.toEuclideanLin x))
    _ = x.ofLp ⬝ᵥ A *ᵥ x.ofLp := by
      simp [Matrix.ofLp_toLpLin, Matrix.toLin'_apply, dotProduct_comm]

/-- The BFGS updated matrix remains positive definite under the usual curvature condition. -/
-- Proof sketch: rewrite `bfgsUpdatedMatrix` in the standard factorized BFGS form and apply the
-- classical preservation argument using `⟪γₖ, δₖ⟫ > 0` and positive definiteness of `Hₖ`.
theorem bfgsUpdatedMatrix_posDef (Hk : Mat) (γk δk : E) (hHkPosDef : Hk.PosDef)
    (hγδ : 0 < inner ℝ γk δk) :
    (bfgsUpdatedMatrix Hk γk δk).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · -- Positive definiteness over `ℝ` needs Hermitian symmetry, which is exactly matrix symmetry.
    simpa [Matrix.IsSymm, Matrix.IsHermitian] using
      bfgsUpdatedMatrix_isSymm Hk γk δk (by simpa using hHkPosDef.1)
  · intro x hx
    let y : E := WithLp.toLp 2 x
    have hy : y ≠ 0 := by
      dsimp [y]
      simpa using hx
    have hinner :
        0 < inner ℝ y ((bfgsUpdatedMatrix Hk γk δk).toEuclideanLin y) :=
      bfgsUpdatedMatrix_inner_pos Hk γk δk hHkPosDef hγδ hy
    -- Transport the Euclidean-space inequality back to the matrix quadratic form.
    calc
      0 < inner ℝ y ((bfgsUpdatedMatrix Hk γk δk).toEuclideanLin y) := hinner
      _ = x ⬝ᵥ (bfgsUpdatedMatrix Hk γk δk) *ᵥ x := by
        dsimp [y]
        change inner ℝ (WithLp.toLp 2 x)
          (WithLp.toLp 2 ((bfgsUpdatedMatrix Hk γk δk) *ᵥ x)) =
            x ⬝ᵥ (bfgsUpdatedMatrix Hk γk δk) *ᵥ x
        simpa [dotProduct_comm] using
          (EuclideanSpace.inner_toLp_toLp (x := x)
            (y := (bfgsUpdatedMatrix Hk γk δk) *ᵥ x))

/-- Helper for Definition 1.8.14: the scalar BFGS secant coefficient simplifies to `1` once the
curvature denominator is nonzero. -/
theorem bfgs_secant_scalar_cleanup {a c : ℝ} (hc : c ≠ 0) :
    c * (c⁻¹ * (1 + c⁻¹ * a)) - c⁻¹ * a = 1 := by
  -- Clear the denominator and normalize the remaining scalar polynomial identity.
  field_simp [hc]
  ring

/-- The BFGS updated matrix satisfies the quasi-Newton secant equation whenever the curvature
denominator is nonzero. -/
-- Proof sketch: write `Hₖ₊₁ = Hₖ + ΔHₖ`, apply the two rank-one terms in `ΔHₖ` to `γₖ`, and use
-- the nonvanishing curvature denominator `⟪γₖ, δₖ⟫` to cancel the old image `Hₖ γₖ`.
theorem bfgsUpdatedMatrix_secantEquation (Hk : Mat) (γk δk : E)
    (hγδ : inner ℝ γk δk ≠ 0) :
    (bfgsUpdatedMatrix Hk γk δk).toEuclideanLin γk = δk := by
  rw [bfgsUpdatedMatrix_toEuclideanLin]
  dsimp
  -- Expand the update on `γₖ`, then isolate the remaining scalar coefficient on `δₖ`.
  ext i
  have hc : inner ℝ δk γk ≠ 0 := by
    simpa [real_inner_comm] using hγδ
  have hInv : inner ℝ δk γk * (inner ℝ δk γk)⁻¹ = 1 := mul_inv_cancel₀ hc
  simp [inner_adjoint_apply_self_eq_inner_apply_self, sub_eq_add_neg, smul_smul, mul_comm]
  rw [real_inner_comm δk γk, hInv, real_inner_comm γk (Hk.toEuclideanLin γk)]
  have hCoeff := congrArg (fun t : ℝ ↦ δk.ofLp i * t)
    (bfgs_secant_scalar_cleanup (a := inner ℝ γk (Hk.toEuclideanLin γk))
      (c := inner ℝ δk γk) hc)
  ring_nf at hCoeff ⊢
  linarith

/-- Specializing the BFGS secant equation to consecutive iterates and gradients uses only the
curvature witness for that actual step data. -/
theorem bfgsUpdatedMatrix_step_secantEquation
    (xk xNext gk gNext : E) (Hk : Mat)
    (hcurvature : inner ℝ (gNext - gk) (xNext - xk) ≠ 0) :
    (bfgsUpdatedMatrix Hk (gNext - gk) (xNext - xk)).toEuclideanLin (gNext - gk) =
      xNext - xk := by
  simpa using
    bfgsUpdatedMatrix_secantEquation Hk (gNext - gk) (xNext - xk) hcurvature

end
