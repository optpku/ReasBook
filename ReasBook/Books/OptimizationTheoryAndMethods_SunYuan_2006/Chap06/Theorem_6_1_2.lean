/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.LinearAlgebra.Matrix.PosDef
import OptimizationTheoryAndMethods_SunYuan_2006.Chap06.Lemma_6_1_3

noncomputable section

section

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ

-- Domain sampling for this refine pass:
-- * `Chapter06.Definition_6_1_extra_1.TrustRegionSubproblem` is the Chapter 6 owner for the
--   quadratic model, feasible set, and solution predicate `TrustRegionSubproblem.IsSolution`.
-- * `IsMinOn` from `Mathlib.Order.Filter.Extr` remains the canonical minimizer API underneath
--   that owner.
-- Source/core/bridge triage:
-- * source-facing: `P.IsSolution sStar`, expressing that `sStar` solves the trust-region
--   subproblem.
-- * core/canonical: `IsMinOn P P.feasibleSet sStar`.
-- * bridge/view: `TrustRegionSubproblem.isSolution_iff_mem_feasibleSet_and_isMinOn` in the
--   owner file.
-- This file therefore keeps only the auxiliary shifted Hessian definition and states the source
-- KKT clauses directly on the theorem surface.

/-- The shifted Hessian in the trust-region KKT condition is `B + λ I`. -/
def TrustRegionSubproblem.shiftedHessian
    (P : TrustRegionSubproblem n) (lambdaStar : ℝ) : MatrixN :=
  P.hessianApprox + lambdaStar • (1 : MatrixN)

/-- Helper for Chapter06 Theorem 6.1.2: in the Euclidean step space, the matrix dot product
`x ⬝ᵥ x` is the squared norm `‖x‖₂²`. -/
lemma dotProduct_self_eq_norm_sq (x : Point) :
    dotProduct x x = ‖x‖ ^ 2 := by
  -- Convert the coordinate dot product into the ambient inner product.
  have h := EuclideanSpace.inner_eq_star_dotProduct x x
  simpa [real_inner_self_eq_norm_sq] using h.symm

/-- Helper for Chapter06 Theorem 6.1.2: applying the shifted Hessian `B + λ I` to a vector
splits into the original Hessian action plus the radial term `λ s`. -/
lemma TrustRegionSubproblem.shiftedHessian_mulVec
    (P : TrustRegionSubproblem n) (lambdaStar : ℝ) (s : Point) :
    (P.shiftedHessian lambdaStar).mulVec s =
      P.hessianApprox.mulVec s + lambdaStar • s := by
  -- Expand `B + λ I` on the test vector.
  ext i
  rw [TrustRegionSubproblem.shiftedHessian, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec]

/-- Helper for Chapter06 Theorem 6.1.2: the quadratic model increment along the line
`sStar + t d` separates into the linear residual term and the quadratic curvature term. -/
lemma TrustRegionSubproblem.quadraticModel_increment_eq
    (P : TrustRegionSubproblem n) (sStar d : Point) (t : ℝ) :
    P (sStar + t • d) - P sStar =
      t * dotProduct P.gradient d +
        t * dotProduct d (P.hessianApprox.mulVec sStar) +
        (1 / 2 : ℝ) * t ^ 2 * dotProduct d (P.hessianApprox.mulVec d) := by
  -- Expand the quadratic model and merge the mixed Hessian terms using symmetry of `B`.
  have hsymm :
      dotProduct sStar (P.hessianApprox.mulVec d) =
        dotProduct d (P.hessianApprox.mulVec sStar) := by
    simpa [P.hessianApprox_symm.eq] using
      (Matrix.dotProduct_transpose_mulVec (A := P.hessianApprox) (x := sStar) (y := d))
  simp [TrustRegionSubproblem.quadraticModel_eq, dotProduct_add, dotProduct_smul,
    smul_dotProduct, Matrix.mulVec_add,
    Matrix.mulVec_smul, hsymm]
  ring

/-- Helper for Chapter06 Theorem 6.1.2: under stationarity, the model difference
`P s - P sStar` is the shifted-Hessian quadratic term plus the multiplier norm-gap term. -/
lemma TrustRegionSubproblem.quadraticDifference_eq_shiftedHessian
    (P : TrustRegionSubproblem n) (sStar s : Point) (lambdaStar : ℝ)
    (hstat : P.hessianApprox.mulVec sStar + P.gradient = -lambdaStar • sStar) :
    P s - P sStar =
      (1 / 2 : ℝ) *
          dotProduct (s - sStar) ((P.shiftedHessian lambdaStar).mulVec (s - sStar)) +
        (lambdaStar / 2) * (‖sStar‖ ^ 2 - ‖s‖ ^ 2) := by
  -- Rewrite the model difference along the displacement `d = s - sStar`.
  let d : Point := s - sStar
  have hinc := P.quadraticModel_increment_eq sStar d 1
  have hnorm_gap :
      -lambdaStar * dotProduct sStar d - (lambdaStar / 2) * dotProduct d d =
        (lambdaStar / 2) * (‖sStar‖ ^ 2 - ‖s‖ ^ 2) := by
    -- Expand the squared norms of `s` and `sStar` in dot-product form.
    have hs : dotProduct s s = ‖s‖ ^ 2 :=
      dotProduct_self_eq_norm_sq s
    have hsStar : dotProduct sStar sStar = ‖sStar‖ ^ 2 :=
      dotProduct_self_eq_norm_sq sStar
    simp [d, dotProduct_sub, hs, hsStar, dotProduct_comm]
    ring
  have hsplit :
      -lambdaStar * dotProduct sStar d +
          (1 / 2 : ℝ) * dotProduct d (P.hessianApprox.mulVec d) =
        (1 / 2 : ℝ) * dotProduct d (P.hessianApprox.mulVec d) +
          (lambdaStar / 2) * dotProduct d d +
          (-lambdaStar * dotProduct sStar d - (lambdaStar / 2) * dotProduct d d) := by
    ring
  calc
    P s - P sStar
      = dotProduct P.gradient d +
          dotProduct d (P.hessianApprox.mulVec sStar) +
          (1 / 2 : ℝ) * dotProduct d (P.hessianApprox.mulVec d) := by
          simpa [d] using hinc
    _ = dotProduct (-lambdaStar • sStar) d +
          (1 / 2 : ℝ) * dotProduct d (P.hessianApprox.mulVec d) := by
          have hdot :
              dotProduct P.gradient d + dotProduct d (P.hessianApprox.mulVec sStar) =
                dotProduct (-lambdaStar • sStar) d := by
            simpa [dotProduct_add, dotProduct_comm, add_comm] using
              congrArg (fun v ↦ dotProduct d v) hstat
          rw [hdot]
    _ = -lambdaStar * dotProduct sStar d +
          (1 / 2 : ℝ) * dotProduct d (P.hessianApprox.mulVec d) := by
          simp
    _ = (1 / 2 : ℝ) * dotProduct d (P.hessianApprox.mulVec d) +
          (lambdaStar / 2) * dotProduct d d +
          (-lambdaStar * dotProduct sStar d - (lambdaStar / 2) * dotProduct d d) := by
          exact hsplit
    _ = (1 / 2 : ℝ) *
          dotProduct d ((P.shiftedHessian lambdaStar).mulVec d) +
        (lambdaStar / 2) * (‖sStar‖ ^ 2 - ‖s‖ ^ 2) := by
          rw [hnorm_gap, P.shiftedHessian_mulVec, dotProduct_add, dotProduct_smul]
          ring

/-- Helper for Chapter06 Theorem 6.1.2: an interior feasible point remains feasible after a
small perturbation `t • d` whose size fits in the remaining trust-region radius gap. -/
lemma TrustRegionSubproblem.add_smul_mem_feasibleSet_of_abs_mul_norm_le
    (P : TrustRegionSubproblem n) {sStar d : Point} {t : ℝ}
    (hsStar : ‖sStar‖ < P.radius)
    (ht : |t| * ‖d‖ ≤ P.radius - ‖sStar‖) :
    sStar + t • d ∈ P.feasibleSet := by
  -- Bound the perturbed norm by the triangle inequality and absorb the explicit gap bound.
  rw [TrustRegionSubproblem.mem_feasibleSet_iff]
  have hnorm : ‖sStar + t • d‖ ≤ ‖sStar‖ + |t| * ‖d‖ := by
    simpa [norm_smul] using norm_add_le sStar (t • d)
  linarith

/-- Helper for Chapter06 Theorem 6.1.2: the KKT clauses imply that `sStar` minimizes the
quadratic model on the trust-region ball. -/
lemma TrustRegionSubproblem.isSolution_of_exists_multiplier
    (P : TrustRegionSubproblem n) (sStar : Point) {lambdaStar : ℝ}
    (hNonneg : 0 ≤ lambdaStar)
    (hStationarity : (P.shiftedHessian lambdaStar).mulVec sStar = -P.gradient)
    (hFeasible : ‖sStar‖ ≤ P.radius)
    (hComplementarity : lambdaStar * (P.radius - ‖sStar‖) = 0)
    (hPosSemidef : (P.shiftedHessian lambdaStar).PosSemidef) :
    P.IsSolution sStar := by
  -- Route correction: the reverse direction is handled by an exact quadratic identity rather
  -- than by importing a later trust-region KKT theorem.
  rw [TrustRegionSubproblem.isSolution_iff_mem_feasibleSet_and_isMinOn]
  refine ⟨?_, ?_⟩
  · -- Repackage the explicit norm bound as feasibility.
    simpa [TrustRegionSubproblem.mem_feasibleSet_iff] using hFeasible
  · -- Compare `P s` with `P sStar` through the shifted-Hessian expansion.
    rw [isMinOn_iff]
    intro s hs
    have hsFeasible : ‖s‖ ≤ P.radius :=
      (P.mem_feasibleSet_iff s).1 hs
    have hstatZero :
        P.hessianApprox.mulVec sStar + P.gradient + lambdaStar • sStar = 0 := by
      have htmp := hStationarity
      rw [P.shiftedHessian_mulVec] at htmp
      simpa [add_comm, add_left_comm, add_assoc] using
        congrArg (fun v ↦ v + P.gradient.ofLp) htmp
    have hstat :
        P.hessianApprox.mulVec sStar + P.gradient = -lambdaStar • sStar := by
      simpa [neg_smul] using eq_neg_iff_add_eq_zero.mpr hstatZero
    have hquad :
        0 ≤ (1 / 2 : ℝ) *
          dotProduct (s - sStar) ((P.shiftedHessian lambdaStar).mulVec (s - sStar)) := by
      -- Positive semidefiniteness controls the shifted quadratic term.
      have hnonneg :=
        Matrix.PosSemidef.dotProduct_mulVec_nonneg hPosSemidef (s - sStar)
      have hnonneg' :
          0 ≤ dotProduct (s - sStar) ((P.shiftedHessian lambdaStar).mulVec (s - sStar)) := by
        simpa using hnonneg
      have hhalf : 0 ≤ (1 / 2 : ℝ) := by positivity
      exact mul_nonneg hhalf hnonneg'
    have hgap :
        0 ≤ (lambdaStar / 2) * (‖sStar‖ ^ 2 - ‖s‖ ^ 2) := by
      -- Complementarity reduces the norm-gap term to either `0` or the boundary gap.
      rcases eq_zero_or_eq_zero_of_mul_eq_zero hComplementarity with hLambda | hBoundary
      · simp [hLambda]
      · have hsStar_eq : ‖sStar‖ = P.radius := by
          linarith
        have hradius_sq : 0 ≤ P.radius ^ 2 - ‖s‖ ^ 2 := by
          have hsub : 0 ≤ P.radius - ‖s‖ := sub_nonneg.mpr hsFeasible
          have hsum : 0 ≤ P.radius + ‖s‖ := by
            linarith [P.radius_pos, norm_nonneg s]
          have hmul : 0 ≤ (P.radius - ‖s‖) * (P.radius + ‖s‖) := mul_nonneg hsub hsum
          nlinarith
        have hscaled : 0 ≤ (lambdaStar / 2) * (P.radius ^ 2 - ‖s‖ ^ 2) := by
          have hhalf : 0 ≤ lambdaStar / 2 := by nlinarith
          exact mul_nonneg hhalf hradius_sq
        simpa [hsStar_eq] using hscaled
    have hdiff :=
      P.quadraticDifference_eq_shiftedHessian sStar s lambdaStar hstat
    have hdiff_nonneg : 0 ≤ P s - P sStar := by
      rw [hdiff]
      nlinarith
    linarith

/-- Helper for Chapter06 Theorem 6.1.2: an exact trust-region solution satisfies the first-order
residual inequality against every feasible comparison point on the ball. -/
lemma TrustRegionSubproblem.linearizedNecessaryCondition_of_isSolution
    (P : TrustRegionSubproblem n) {sStar s : Point}
    (hsol : P.IsSolution sStar) (hs : s ∈ P.feasibleSet) :
    0 ≤ dotProduct (s - sStar) (P.hessianApprox.mulVec sStar + P.gradient) := by
  -- Route correction: the forward residual is kept in pure `Point` form so the later multiplier
  -- and boundary lemmas can reuse the same normal form without extra `.ofLp` transport.
  rcases hsol with ⟨hsStar, hminOn⟩
  rw [isMinOn_iff] at hminOn
  let d : Point := s - sStar
  let a : ℝ := dotProduct d (P.hessianApprox.mulVec sStar + P.gradient)
  let b : ℝ := dotProduct d (P.hessianApprox.mulVec d)
  have hsStar_norm : ‖sStar‖ ≤ P.radius :=
    (P.mem_feasibleSet_iff sStar).mp hsStar
  have hs_norm : ‖s‖ ≤ P.radius :=
    (P.mem_feasibleSet_iff s).mp hs
  have hsegment_mem :
      ∀ {t : ℝ}, 0 ≤ t → t ≤ 1 → sStar + t • d ∈ P.feasibleSet := by
    intro t ht0 ht1
    -- Every segment point between two feasible steps stays in the closed trust-region ball.
    rw [P.mem_feasibleSet_iff]
    have hrewrite : sStar + t • d = (1 - t) • sStar + t • s := by
      ext i
      simp [d, sub_eq_add_neg]
      ring
    calc
      ‖sStar + t • d‖ = ‖(1 - t) • sStar + t • s‖ := by rw [hrewrite]
      _ ≤ ‖(1 - t) • sStar‖ + ‖t • s‖ := norm_add_le _ _
      _ = (1 - t) * ‖sStar‖ + t * ‖s‖ := by
            rw [norm_smul, norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr ht1),
              Real.norm_of_nonneg ht0]
      _ ≤ (1 - t) * P.radius + t * P.radius := by
            gcongr
      _ = P.radius := by ring
  have hincrement :
      ∀ t : ℝ,
        P (sStar + t • d) - P sStar = t * a + (1 / 2 : ℝ) * t ^ 2 * b := by
    intro t
    -- Expanding the quadratic model along the feasible segment isolates the linear residual `a`.
    calc
      P (sStar + t • d) - P sStar
        = t * dotProduct P.gradient d +
            t * dotProduct d (P.hessianApprox.mulVec sStar) +
            (1 / 2 : ℝ) * t ^ 2 * dotProduct d (P.hessianApprox.mulVec d) := by
            simpa [d] using P.quadraticModel_increment_eq sStar d t
      _ = t * dotProduct d (P.hessianApprox.mulVec sStar + P.gradient) +
            (1 / 2 : ℝ) * t ^ 2 * dotProduct d (P.hessianApprox.mulVec d) := by
            rw [dotProduct_comm P.gradient d, dotProduct_add]
            ring
      _ = t * a + (1 / 2 : ℝ) * t ^ 2 * b := by simp [a, b]
  by_contra ha_nonneg
  have ha_neg : a < 0 := lt_of_not_ge ha_nonneg
  let t : ℝ := min 1 ((-a) / (2 * (|b| + 1)))
  have ht_pos : 0 < t := by
    -- Choosing `t` positive and small forces the negative linear term to dominate the quadratic term.
    have hdiv_pos : 0 < (-a) / (2 * (|b| + 1)) := by
      have hnum : 0 < -a := by linarith
      have hden : 0 < 2 * (|b| + 1) := by positivity
      exact div_pos hnum hden
    exact lt_min one_pos hdiv_pos
  have ht0 : 0 ≤ t := le_of_lt ht_pos
  have ht1 : t ≤ 1 := by
    dsimp [t]
    exact min_le_left _ _
  have hfeasible_t : sStar + t • d ∈ P.feasibleSet :=
    hsegment_mem ht0 ht1
  have hmodel_t : 0 ≤ P (sStar + t • d) - P sStar := by
    have hmin := hminOn (sStar + t • d) hfeasible_t
    linarith
  have hquadratic_nonneg : 0 ≤ t * a + (1 / 2 : ℝ) * t ^ 2 * b := by
    simpa [hincrement t] using hmodel_t
  have ht_small : t * (|b| + 1) ≤ -a / 2 := by
    have ht_le :
        t ≤ (-a) / (2 * (|b| + 1)) := by
      dsimp [t]
      exact min_le_right _ _
    have habs_nonneg : 0 ≤ |b| + 1 := by positivity
    have hmul := mul_le_mul_of_nonneg_right ht_le habs_nonneg
    have hden_ne : 2 * (|b| + 1) ≠ 0 := by positivity
    calc
      t * (|b| + 1)
        ≤ ((-a) / (2 * (|b| + 1))) * (|b| + 1) := hmul
      _ = -a / 2 := by
            field_simp [hden_ne]
  have hquadratic_upper : (1 / 2 : ℝ) * t ^ 2 * b ≤ -t * a / 4 := by
    have hcoeff_nonneg : 0 ≤ (1 / 2 : ℝ) * t ^ 2 := by positivity
    calc
      (1 / 2 : ℝ) * t ^ 2 * b ≤ (1 / 2 : ℝ) * t ^ 2 * |b| := by
        exact mul_le_mul_of_nonneg_left (le_abs_self b) hcoeff_nonneg
      _ ≤ (1 / 2 : ℝ) * t ^ 2 * (|b| + 1) := by
        have habs_le : |b| ≤ |b| + 1 := by
          linarith [abs_nonneg b]
        exact mul_le_mul_of_nonneg_left habs_le hcoeff_nonneg
      _ = ((1 / 2 : ℝ) * t) * (t * (|b| + 1)) := by ring
      _ ≤ ((1 / 2 : ℝ) * t) * (-a / 2) := by
        gcongr
      _ = -t * a / 4 := by ring
  have hnegative : t * a + (1 / 2 : ℝ) * t ^ 2 * b < 0 := by
    have hta_neg : t * a < 0 := mul_neg_of_pos_of_neg ht_pos ha_neg
    nlinarith
  linarith

/-- Helper for Chapter06 Theorem 6.1.2: a vector whose linear form is minimized on the closed
trust-region ball at a boundary point must be a negative multiple of that boundary point. -/
lemma TrustRegionSubproblem.boundaryResidual_eq_neg_smul
    (P : TrustRegionSubproblem n) {sStar r : Point}
    (hsBoundary : ‖sStar‖ = P.radius)
    (hr : r ≠ 0)
    (hlin : ∀ s : Point, s ∈ P.feasibleSet → 0 ≤ dotProduct (s - sStar) r) :
    ∃ lambdaStar : ℝ, 0 ≤ lambdaStar ∧ r = -lambdaStar • sStar := by
  -- Route correction: extract the boundary normal cone by comparing with the explicit feasible
  -- point on the steepest-descent ray, then use equality in Cauchy-Schwarz once.
  let sCmp : Point := -((P.radius / ‖r‖) : ℝ) • r
  have hrNorm_ne : ‖r‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hr
  have hsStar_norm_ne : ‖sStar‖ ≠ 0 := by
    rw [hsBoundary]
    exact P.radius_pos.ne'
  have hsCmp_mem : sCmp ∈ P.feasibleSet := by
    -- The comparison point lies exactly on the trust-region boundary.
    rw [P.mem_feasibleSet_iff]
    have hsCmp_norm : ‖sCmp‖ = P.radius := by
      dsimp [sCmp]
      rw [norm_smul, Real.norm_eq_abs, abs_neg,
        abs_of_nonneg (div_nonneg P.radius_pos.le (norm_nonneg _))]
      field_simp [hrNorm_ne]
    rw [hsCmp_norm]
  have hcmp_ineq : 0 ≤ dotProduct (sCmp - sStar) r :=
    hlin sCmp hsCmp_mem
  have hcmp_eval :
      dotProduct (sCmp - sStar) r = -P.radius * ‖r‖ - dotProduct sStar r := by
    -- Expanding the comparison inequality isolates the boundary lower bound.
    dsimp [sCmp]
    rw [sub_dotProduct, smul_dotProduct]
    simp [dotProduct_self_eq_norm_sq]
    field_simp [hrNorm_ne]
  have hLower' : P.radius * ‖r‖ ≤ -dotProduct sStar r := by
    rw [hcmp_eval] at hcmp_ineq
    nlinarith
  have hLower : P.radius * ‖r‖ ≤ dotProduct sStar (-r) := by
    simpa using hLower'
  have hUpper : dotProduct sStar (-r) ≤ ‖sStar‖ * ‖-r‖ := by
    have hUpperInner : inner ℝ (-r) sStar ≤ ‖-r‖ * ‖sStar‖ :=
      real_inner_le_norm (-r) sStar
    have hInnerDot : inner ℝ (-r) sStar = dotProduct sStar (-r) := by
      simpa using (EuclideanSpace.inner_eq_star_dotProduct (-r) sStar)
    rw [hInnerDot] at hUpperInner
    simpa [mul_comm] using hUpperInner
  have hEqDot : dotProduct sStar (-r) = ‖sStar‖ * ‖-r‖ := by
    have hLowerNorm : ‖sStar‖ * ‖-r‖ ≤ dotProduct sStar (-r) := by
      simpa [hsBoundary, norm_neg] using hLower
    nlinarith
  have hEqInner : inner ℝ (-r) sStar = ‖-r‖ * ‖sStar‖ := by
    have hInnerDot : inner ℝ (-r) sStar = dotProduct sStar (-r) := by
      simpa using (EuclideanSpace.inner_eq_star_dotProduct (-r) sStar)
    rw [hInnerDot]
    simpa [mul_comm] using hEqDot
  have hCollinear : ‖sStar‖ • (-r) = ‖-r‖ • sStar :=
    (inner_eq_norm_mul_iff_real.mp hEqInner)
  refine ⟨‖r‖ / ‖sStar‖, div_nonneg (norm_nonneg _) (norm_nonneg _), ?_⟩
  -- Divide the collinearity identity by `‖sStar‖` to solve for `r`.
  have hScaled : (-r) = (‖-r‖ / ‖sStar‖) • sStar := by
    calc
      (-r) = (1 / ‖sStar‖) • (‖sStar‖ • (-r)) := by
          simpa [smul_smul, div_eq_mul_inv, hsStar_norm_ne]
      _ = (1 / ‖sStar‖) • (‖-r‖ • sStar) := by rw [hCollinear]
      _ = (‖-r‖ / ‖sStar‖) • sStar := by
          simp [smul_smul, div_eq_mul_inv, mul_comm]
  simpa [norm_neg] using congrArg Neg.neg hScaled

/-- Helper for Chapter06 Theorem 6.1.2: a vector whose linear form is minimized on the closed
trust-region ball must lie in the normal cone `-λ sStar` of the boundary point `sStar`. -/
lemma TrustRegionSubproblem.exists_multiplier_of_ballLinearMin
    (P : TrustRegionSubproblem n) {sStar r : Point}
    (hsFeasible : ‖sStar‖ ≤ P.radius)
    (hlin : ∀ s : Point, s ∈ P.feasibleSet → 0 ≤ dotProduct (s - sStar) r) :
    ∃ lambdaStar : ℝ,
      0 ≤ lambdaStar ∧
      r = -lambdaStar • sStar ∧
      lambdaStar * (P.radius - ‖sStar‖) = 0 := by
  by_cases hInterior : ‖sStar‖ < P.radius
  · -- In the interior, two-sided feasible perturbations force the residual to vanish.
    let ε : ℝ := (P.radius - ‖sStar‖) / (2 * (‖r‖ + 1))
    have hε_pos : 0 < ε := by
      dsimp [ε]
      have hgap : 0 < P.radius - ‖sStar‖ := sub_pos.mpr hInterior
      positivity
    have hε_nonneg : 0 ≤ ε := le_of_lt hε_pos
    have hε_bound : |ε| * ‖r‖ ≤ P.radius - ‖sStar‖ := by
      rw [abs_of_nonneg hε_nonneg]
      have hr_le : ‖r‖ ≤ ‖r‖ + 1 := by
        nlinarith [norm_nonneg r]
      have hmul :
          ε * ‖r‖ ≤ ε * (‖r‖ + 1) := by
        exact mul_le_mul_of_nonneg_left hr_le hε_nonneg
      have hhalf :
          ε * (‖r‖ + 1) = (P.radius - ‖sStar‖) / 2 := by
        dsimp [ε]
        field_simp
      nlinarith [hmul]
    have hPlus_mem : sStar + ε • r ∈ P.feasibleSet :=
      P.add_smul_mem_feasibleSet_of_abs_mul_norm_le hInterior hε_bound
    have hMinus_mem : sStar + (-ε) • r ∈ P.feasibleSet := by
      apply P.add_smul_mem_feasibleSet_of_abs_mul_norm_le hInterior
      simpa [abs_neg] using hε_bound
    have hPlus : 0 ≤ ε * dotProduct r r := by
      simpa [dotProduct_smul] using hlin (sStar + ε • r) hPlus_mem
    have hMinus : 0 ≤ -ε * dotProduct r r := by
      simpa [dotProduct_smul] using hlin (sStar + (-ε) • r) hMinus_mem
    have hrr_zero : dotProduct r r = 0 := by
      nlinarith
    have hr_zero : r = 0 := by
      have hnorm_zero : ‖r‖ = 0 := by
        simpa [dotProduct_self_eq_norm_sq] using hrr_zero
      exact norm_eq_zero.mp hnorm_zero
    refine ⟨0, le_rfl, ?_, ?_⟩
    · simpa [hr_zero]
    · ring
  · -- On the boundary, the residual lies in the normal cone extracted by the comparison point.
    have hsBoundary : ‖sStar‖ = P.radius := by
      linarith
    by_cases hr : r = 0
    · refine ⟨0, le_rfl, ?_, ?_⟩
      · simpa [hr]
      · simp [hsBoundary]
    · rcases P.boundaryResidual_eq_neg_smul hsBoundary hr hlin with
        ⟨lambdaStar, hNonneg, hResidual⟩
      refine ⟨lambdaStar, hNonneg, hResidual, ?_⟩
      simp [hsBoundary]

/-- Helper for Chapter06 Theorem 6.1.2: the quadratic forms of the opposite tilts
`z ± ε • sStar` add up with their mixed terms cancelled. -/
lemma TrustRegionSubproblem.shiftedQuadratic_tiltSum_eq
    (P : TrustRegionSubproblem n) (lambdaStar : ℝ) (z sStar : Point) (ε : ℝ) :
    dotProduct (z + ε • sStar) ((P.shiftedHessian lambdaStar).mulVec (z + ε • sStar)) +
      dotProduct (z - ε • sStar) ((P.shiftedHessian lambdaStar).mulVec (z - ε • sStar)) =
        2 * dotProduct z ((P.shiftedHessian lambdaStar).mulVec z) +
          2 * ε ^ 2 * dotProduct sStar ((P.shiftedHessian lambdaStar).mulVec sStar) := by
  -- Expanding both tilts once makes the cross terms cancel algebraically.
  simp [dotProduct_add, dotProduct_sub, dotProduct_smul, smul_dotProduct,
    Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul]
  ring

/-- Helper for Chapter06 Theorem 6.1.2: when the boundary perturbation parameter is chosen as in
the source proof, the perturbed step stays on the same Euclidean sphere. -/
lemma boundaryPerturbation_preserves_norm
    {sStar z : Point} (hcross : dotProduct z sStar ≠ 0) :
    let t : ℝ := -2 * dotProduct z sStar / ‖z‖ ^ 2
    ‖sStar + t • z‖ = ‖sStar‖ := by
  dsimp
  have hz_ne : z ≠ 0 := by
    intro hz
    apply hcross
    simp [hz]
  have hnormz_ne : ‖z‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hz_ne
  have hnorm_sq :
      ‖sStar + (-2 * dotProduct z sStar / ‖z‖ ^ 2) • z‖ ^ 2 = ‖sStar‖ ^ 2 := by
    -- Expanding the squared norm shows that the chosen parameter cancels the cross term exactly.
    rw [← dotProduct_self_eq_norm_sq
        (sStar + (-2 * dotProduct z sStar / ‖z‖ ^ 2) • z),
      ← dotProduct_self_eq_norm_sq sStar]
    have hz_sq : dotProduct z z = ‖z‖ ^ 2 :=
      dotProduct_self_eq_norm_sq z
    simp [dotProduct_add, dotProduct_smul, dotProduct_comm, hz_sq]
    field_simp [pow_ne_zero 2 hnormz_ne]
    ring
  nlinarith [norm_nonneg (sStar + (-2 * dotProduct z sStar / ‖z‖ ^ 2) • z),
    norm_nonneg sStar, hnorm_sq]

/-- Helper for Chapter06 Theorem 6.1.2: once the stationarity equation is normalized to
`B sStar + g = -λ sStar`, the exact boundary perturbation formula becomes a pure shifted-Hessian
quadratic term. -/
lemma TrustRegionSubproblem.boundaryQuadraticDifference_eq
    (P : TrustRegionSubproblem n) (sStar z : Point) (lambdaStar t : ℝ)
    (hstat : P.hessianApprox.mulVec sStar + P.gradient = -lambdaStar • sStar)
    (hnorm : ‖sStar + t • z‖ = ‖sStar‖) :
    P (sStar + t • z) - P sStar =
      (1 / 2 : ℝ) * t ^ 2 * dotProduct z ((P.shiftedHessian lambdaStar).mulVec z) := by
  -- Route correction: reuse the stable shifted-Hessian difference identity instead of reopening
  -- the raw quadratic expansion on the boundary perturbation.
  have hdiff :=
    P.quadraticDifference_eq_shiftedHessian sStar (sStar + t • z) lambdaStar hstat
  have hnorm_sq : ‖sStar‖ ^ 2 - ‖sStar + t • z‖ ^ 2 = 0 := by
    nlinarith [congrArg (fun x : ℝ ↦ x ^ 2) hnorm]
  calc
    P (sStar + t • z) - P sStar
      = (1 / 2 : ℝ) *
          dotProduct ((sStar + t • z) - sStar)
            ((P.shiftedHessian lambdaStar).mulVec ((sStar + t • z) - sStar)) +
          (lambdaStar / 2) * (‖sStar‖ ^ 2 - ‖sStar + t • z‖ ^ 2) := by
            simpa using hdiff
    _ = (1 / 2 : ℝ) *
          dotProduct (t • z) ((P.shiftedHessian lambdaStar).mulVec (t • z)) +
          (lambdaStar / 2) * (‖sStar‖ ^ 2 - ‖sStar + t • z‖ ^ 2) := by
            simp
    _ = (1 / 2 : ℝ) *
          dotProduct (t • z) ((t : ℝ) • (P.shiftedHessian lambdaStar).mulVec z) +
          (lambdaStar / 2) * (‖sStar‖ ^ 2 - ‖sStar + t • z‖ ^ 2) := by
            rw [Matrix.mulVec_smul]
    _ = (1 / 2 : ℝ) * t ^ 2 * dotProduct z ((P.shiftedHessian lambdaStar).mulVec z) := by
            rw [hnorm_sq]
            simp [dotProduct_smul, smul_dotProduct]
            ring

/-- Helper for Chapter06 Theorem 6.1.2: on the trust-region boundary, the exact sphere-preserving
perturbation in a nonorthogonal direction forces the shifted quadratic form to be nonnegative. -/
lemma TrustRegionSubproblem.shiftedQuadratic_nonneg_of_boundary_nonorthogonal
    (P : TrustRegionSubproblem n) {sStar z : Point} {lambdaStar : ℝ}
    (hsol : P.IsSolution sStar)
    (hstat : (P.shiftedHessian lambdaStar).mulVec sStar = -P.gradient)
    (hboundary : ‖sStar‖ = P.radius)
    (hcross : dotProduct z sStar ≠ 0) :
    0 ≤ dotProduct z ((P.shiftedHessian lambdaStar).mulVec z) := by
  -- Route correction: the boundary step is now handled by the normalized shifted-Hessian
  -- difference identity, avoiding the earlier transport-heavy re-expansion of the model.
  rcases hsol with ⟨_, hminOn⟩
  rw [isMinOn_iff] at hminOn
  have hz_ne : z ≠ 0 := by
    intro hz
    apply hcross
    simp [hz]
  let t : ℝ := -2 * dotProduct z sStar / ‖z‖ ^ 2
  have hnorm : ‖sStar + t • z‖ = ‖sStar‖ := by
    simpa [t] using boundaryPerturbation_preserves_norm (sStar := sStar) (z := z) hcross
  have htrial : sStar + t • z ∈ P.feasibleSet := by
    -- The chosen perturbation lands exactly on the trust-region boundary.
    rw [P.mem_feasibleSet_iff, hnorm, hboundary]
  have hmodel : 0 ≤ P (sStar + t • z) - P sStar := by
    have hmin := hminOn (sStar + t • z) htrial
    linarith
  have hstat' := hstat
  rw [P.shiftedHessian_mulVec] at hstat'
  have hres :
      P.hessianApprox.mulVec sStar + P.gradient = -lambdaStar • sStar := by
    -- Rewrite stationarity once into the residual normal form used by the quadratic adapter.
    have hsum := congrArg (fun v ↦ v + P.gradient.ofLp) hstat'
    have hsum' :
        P.hessianApprox.mulVec sStar + P.gradient + lambdaStar • sStar = 0 := by
      simpa [add_assoc, add_comm, add_left_comm] using hsum
    simpa [neg_smul] using eq_neg_iff_add_eq_zero.mpr hsum'
  have hdiff :=
    P.boundaryQuadraticDifference_eq sStar z lambdaStar t hres hnorm
  have hprod :
      0 ≤ (1 / 2 : ℝ) * t ^ 2 * dotProduct z ((P.shiftedHessian lambdaStar).mulVec z) := by
    simpa [hdiff] using hmodel
  have ht_ne_zero : t ≠ 0 := by
    -- Nonorthogonality makes the exact boundary parameter nonzero.
    dsimp [t]
    refine div_ne_zero ?_ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hz_ne))
    exact mul_ne_zero (by norm_num) hcross
  have hfactor_pos : 0 < (1 / 2 : ℝ) * t ^ 2 := by
    have ht_sq : 0 < t ^ 2 := sq_pos_of_ne_zero ht_ne_zero
    nlinarith
  nlinarith

/-- Helper for Chapter06 Theorem 6.1.2: on the trust-region boundary, orthogonal directions are
handled by tilting them slightly into nonorthogonal directions and summing the resulting bounds. -/
lemma TrustRegionSubproblem.shiftedQuadratic_nonneg_of_boundary_orthogonal
    (P : TrustRegionSubproblem n) {sStar z : Point} {lambdaStar : ℝ}
    (hsol : P.IsSolution sStar)
    (hstat : (P.shiftedHessian lambdaStar).mulVec sStar = -P.gradient)
    (hboundary : ‖sStar‖ = P.radius)
    (horth : dotProduct z sStar = 0) :
    0 ≤ dotProduct z ((P.shiftedHessian lambdaStar).mulVec z) := by
  -- Route correction: tilt the orthogonal direction into two nonorthogonal ones and sum the
  -- resulting nonnegative quadratic forms using the exact tilt-sum identity.
  let qz : ℝ := dotProduct z ((P.shiftedHessian lambdaStar).mulVec z)
  let qs : ℝ := dotProduct sStar ((P.shiftedHessian lambdaStar).mulVec sStar)
  by_contra hqz_nonneg
  have hqz_neg : qz < 0 := lt_of_not_ge hqz_nonneg
  let ε : ℝ := min 1 ((-qz) / (4 * (|qs| + 1)))
  have hε_pos : 0 < ε := by
    dsimp [ε]
    have hdiv_pos : 0 < (-qz) / (4 * (|qs| + 1)) := by
      have hnum : 0 < -qz := by
        linarith
      have hden : 0 < 4 * (|qs| + 1) := by
        positivity
      exact div_pos hnum hden
    exact lt_min one_pos hdiv_pos
  have hε_nonneg : 0 ≤ ε := le_of_lt hε_pos
  have hε_ne : ε ≠ 0 := hε_pos.ne'
  have hsStar_norm_ne : ‖sStar‖ ≠ 0 := by
    rw [hboundary]
    exact P.radius_pos.ne'
  have hPlus_cross : dotProduct (z + ε • sStar) sStar ≠ 0 := by
    have hEval : dotProduct (z + ε • sStar) sStar = ε * ‖sStar‖ ^ 2 := by
      simp [add_dotProduct, smul_dotProduct, horth, dotProduct_self_eq_norm_sq]
    rw [hEval]
    exact mul_ne_zero hε_ne (pow_ne_zero 2 hsStar_norm_ne)
  have hMinus_cross : dotProduct (z - ε • sStar) sStar ≠ 0 := by
    have hEval : dotProduct (z - ε • sStar) sStar = -(ε * ‖sStar‖ ^ 2) := by
      simp [sub_dotProduct, smul_dotProduct, horth, dotProduct_self_eq_norm_sq]
    rw [hEval]
    exact neg_ne_zero.mpr <| mul_ne_zero hε_ne (pow_ne_zero 2 hsStar_norm_ne)
  have hPlus_nonneg :
      0 ≤ dotProduct (z + ε • sStar)
        ((P.shiftedHessian lambdaStar).mulVec (z + ε • sStar)) :=
    P.shiftedQuadratic_nonneg_of_boundary_nonorthogonal hsol hstat hboundary hPlus_cross
  have hMinus_nonneg :
      0 ≤ dotProduct (z - ε • sStar)
        ((P.shiftedHessian lambdaStar).mulVec (z - ε • sStar)) :=
    P.shiftedQuadratic_nonneg_of_boundary_nonorthogonal hsol hstat hboundary hMinus_cross
  have hSum_nonneg :
      0 ≤ dotProduct (z + ε • sStar)
            ((P.shiftedHessian lambdaStar).mulVec (z + ε • sStar)) +
          dotProduct (z - ε • sStar)
            ((P.shiftedHessian lambdaStar).mulVec (z - ε • sStar)) := by
    exact add_nonneg hPlus_nonneg hMinus_nonneg
  have hε_le_one : ε ≤ 1 := by
    dsimp [ε]
    exact min_le_left _ _
  have hε_sq_le : ε ^ 2 ≤ ε := by
    nlinarith
  have hε_bound : ε * (|qs| + 1) ≤ -qz / 4 := by
    have hle : ε ≤ (-qz) / (4 * (|qs| + 1)) := by
      dsimp [ε]
      exact min_le_right _ _
    have hmul := mul_le_mul_of_nonneg_right hle (by positivity : 0 ≤ |qs| + 1)
    have hden_ne : 4 * (|qs| + 1) ≠ 0 := by positivity
    calc
      ε * (|qs| + 1)
        ≤ ((-qz) / (4 * (|qs| + 1))) * (|qs| + 1) := hmul
      _ = -qz / 4 := by
            field_simp [hden_ne]
  have hTilt_small : 2 * ε ^ 2 * |qs| ≤ -qz / 2 := by
    calc
      2 * ε ^ 2 * |qs| ≤ 2 * ε ^ 2 * (|qs| + 1) := by
        nlinarith [abs_nonneg qs]
      _ ≤ 2 * ε * (|qs| + 1) := by
        have hsq_mul :
            ε ^ 2 * (|qs| + 1) ≤ ε * (|qs| + 1) := by
          exact mul_le_mul_of_nonneg_right hε_sq_le (by positivity : 0 ≤ |qs| + 1)
        nlinarith [hsq_mul]
      _ ≤ -qz / 2 := by
        nlinarith [hε_bound]
  have hQs_abs : 2 * ε ^ 2 * qs ≤ 2 * ε ^ 2 * |qs| := by
    exact mul_le_mul_of_nonneg_left (le_abs_self qs) (by positivity)
  have hSum_neg : 2 * qz + 2 * ε ^ 2 * qs < 0 := by
    nlinarith [hqz_neg, hTilt_small, hQs_abs]
  rw [P.shiftedQuadratic_tiltSum_eq] at hSum_nonneg
  have : 0 ≤ 2 * qz + 2 * ε ^ 2 * qs := by
    simpa [qz, qs] using hSum_nonneg
  linarith

/-- Helper for Chapter06 Theorem 6.1.2: once stationarity and complementarity are known, the
source proof's interior/boundary split yields positive semidefiniteness of `B + λ I`. -/
lemma TrustRegionSubproblem.shiftedHessian_posSemidef_of_isSolution
    (P : TrustRegionSubproblem n) (sStar : Point) {lambdaStar : ℝ}
    (hsol : P.IsSolution sStar)
    (hstat : (P.shiftedHessian lambdaStar).mulVec sStar = -P.gradient)
    (hcompl : lambdaStar * (P.radius - ‖sStar‖) = 0) :
    (P.shiftedHessian lambdaStar).PosSemidef := by
  -- Route correction: prove nonnegativity of the shifted quadratic form by the source
  -- interior/boundary split, then invoke the standard Hermitian matrix criterion for PSD.
  have hSymm : (P.shiftedHessian lambdaStar).IsSymm := by
    simpa [TrustRegionSubproblem.shiftedHessian] using
      P.hessianApprox_symm.add ((Matrix.isSymm_one : (1 : MatrixN).IsSymm).smul lambdaStar)
  have hHerm : (P.shiftedHessian lambdaStar).IsHermitian := by
    simpa [Matrix.isHermitian_iff_isSymm] using hSymm
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHerm ?_
  intro z
  have hsFeasible : ‖sStar‖ ≤ P.radius :=
    (P.mem_feasibleSet_iff sStar).mp hsol.1
  let zP : Point := WithLp.toLp 2 z
  have hzNonneg : 0 ≤ dotProduct zP ((P.shiftedHessian lambdaStar).mulVec zP) := by
    by_cases hInterior : ‖sStar‖ < P.radius
    · -- An interior minimizer is unconstrained, so `λ = 0` and small feasible perturbations work.
      have hLambdaZero : lambdaStar = 0 := by
        nlinarith
      let ε : ℝ := (P.radius - ‖sStar‖) / (2 * (‖zP‖ + 1))
      have hε_pos : 0 < ε := by
        dsimp [ε]
        have hgap : 0 < P.radius - ‖sStar‖ := sub_pos.mpr hInterior
        positivity
      have hε_nonneg : 0 ≤ ε := le_of_lt hε_pos
      have hε_bound : |ε| * ‖zP‖ ≤ P.radius - ‖sStar‖ := by
        rw [abs_of_nonneg hε_nonneg]
        have hz_le : ‖zP‖ ≤ ‖zP‖ + 1 := by
          nlinarith [norm_nonneg zP]
        have hmul :
            ε * ‖zP‖ ≤ ε * (‖zP‖ + 1) := by
          exact mul_le_mul_of_nonneg_left hz_le hε_nonneg
        have hhalf :
            ε * (‖zP‖ + 1) = (P.radius - ‖sStar‖) / 2 := by
          dsimp [ε]
          field_simp
        nlinarith [hmul]
      have hTrial_mem : sStar + ε • zP ∈ P.feasibleSet :=
        P.add_smul_mem_feasibleSet_of_abs_mul_norm_le hInterior hε_bound
      rcases hsol with ⟨_, hminOn⟩
      rw [isMinOn_iff] at hminOn
      have hModel : 0 ≤ P (sStar + ε • zP) - P sStar := by
        have hmin := hminOn (sStar + ε • zP) hTrial_mem
        linarith
      have hStat_zero : P.hessianApprox.mulVec sStar + P.gradient = -(0 : ℝ) • sStar := by
        have hStat_zero' : (P.shiftedHessian 0).mulVec sStar = -P.gradient := by
          simpa [hLambdaZero] using hstat
        have hVec : P.hessianApprox.mulVec sStar = -P.gradient := by
          simpa [P.shiftedHessian_mulVec] using hStat_zero'
        simpa using eq_neg_iff_add_eq_zero.mp hVec
      have hDiff :=
        P.quadraticDifference_eq_shiftedHessian sStar (sStar + ε • zP) 0 hStat_zero
      have hQuad :
          0 ≤ ε * (ε * dotProduct zP ((P.shiftedHessian 0).mulVec zP)) := by
        rw [hDiff] at hModel
        simpa [dotProduct_smul, smul_dotProduct, Matrix.mulVec_smul] using hModel
      have hCoeff : 0 < ε * ε := by
        positivity
      have hNonneg0 : 0 ≤ dotProduct zP ((P.shiftedHessian 0).mulVec zP) := by
        nlinarith
      simpa [hLambdaZero] using hNonneg0
    · -- On the boundary, use the nonorthogonal and orthogonal quadratic lemmas.
      have hBoundary : ‖sStar‖ = P.radius := by
        linarith [hsFeasible]
      by_cases hCross : dotProduct zP sStar = 0
      · exact P.shiftedQuadratic_nonneg_of_boundary_orthogonal hsol hstat hBoundary hCross
      · exact P.shiftedQuadratic_nonneg_of_boundary_nonorthogonal hsol hstat hBoundary hCross
  simpa [zP, dotProduct] using hzNonneg

/-- Helper for Chapter06 Theorem 6.1.2: the forward implication reduces to the closed-ball
normal-cone argument plus the shifted-Hessian positivity argument from the source proof. -/
lemma TrustRegionSubproblem.exists_multiplier_of_isSolution
    (P : TrustRegionSubproblem n) (sStar : Point) (hsol : P.IsSolution sStar) :
    ∃ lambdaStar : ℝ,
      0 ≤ lambdaStar ∧
      (P.shiftedHessian lambdaStar).mulVec sStar = -P.gradient ∧
      ‖sStar‖ ≤ P.radius ∧
      lambdaStar * (P.radius - ‖sStar‖) = 0 ∧
      (P.shiftedHessian lambdaStar).PosSemidef := by
  -- Combine the linearized necessary condition with the closed-ball multiplier extraction, then
  -- normalize the residual once into stationarity and invoke the PSD helper.
  have hsFeasible : ‖sStar‖ ≤ P.radius :=
    (P.mem_feasibleSet_iff sStar).mp hsol.1
  let r : Point := Matrix.toEuclideanLin P.hessianApprox sStar + P.gradient
  have hlin :
      ∀ s : Point, s ∈ P.feasibleSet → 0 ≤ dotProduct (s - sStar) r := by
    intro s hs
    simpa [r, Matrix.toEuclideanLin_apply] using
      P.linearizedNecessaryCondition_of_isSolution hsol hs
  rcases
      P.exists_multiplier_of_ballLinearMin (sStar := sStar)
        (r := r) hsFeasible hlin with
    ⟨lambdaStar, hNonneg, hResidual, hCompl⟩
  have hResidualPoint :
      Matrix.toEuclideanLin P.hessianApprox sStar + P.gradient = -(lambdaStar • sStar) := by
    simpa [r] using hResidual
  have hResidual' :
      P.hessianApprox.mulVec sStar + P.gradient = -(lambdaStar • sStar) := by
    exact congrArg (fun v : Point ↦ v.ofLp) hResidualPoint
  have hStationarityVec :
      P.hessianApprox.mulVec sStar + lambdaStar • sStar = -P.gradient := by
    -- Reorder the residual equation once to isolate the shifted-Hessian stationarity term.
    apply eq_neg_iff_add_eq_zero.mpr
    calc
      P.hessianApprox.mulVec sStar + lambdaStar • sStar + P.gradient
        = P.hessianApprox.mulVec sStar + P.gradient + lambdaStar • sStar := by
            abel
      _ = 0 := by
            simpa using (eq_neg_iff_add_eq_zero.mp hResidual')
  have hStationarity :
      (P.shiftedHessian lambdaStar).mulVec sStar = -P.gradient := by
    simpa [P.shiftedHessian_mulVec] using hStationarityVec
  refine ⟨lambdaStar, hNonneg, hStationarity, hsFeasible, hCompl, ?_⟩
  exact P.shiftedHessian_posSemidef_of_isSolution sStar hsol hStationarity hCompl

/-- Chapter06 Theorem 6.1.2: a step `sStar` solves the trust-region subproblem if and only if it
admits a nonnegative multiplier `λ` satisfying the source KKT conditions. The source-facing
owner `P.IsSolution sStar` keeps the Chapter 6 notion of "solves the subproblem" while
reusing the canonical minimizer API internally, and the feasibility clause is stated directly as
the textbook trust-region inequality `‖sStar‖ ≤ Δ`. -/
theorem TrustRegionSubproblem.isSolution_iff_exists_multiplier
    (P : TrustRegionSubproblem n) (sStar : Point) :
    P.IsSolution sStar ↔
      ∃ lambdaStar : ℝ,
        0 ≤ lambdaStar ∧
        (P.shiftedHessian lambdaStar).mulVec sStar = -P.gradient ∧
        ‖sStar‖ ≤ P.radius ∧
        lambdaStar * (P.radius - ‖sStar‖) = 0 ∧
        (P.shiftedHessian lambdaStar).PosSemidef := by
  constructor
  · -- The forward implication is isolated in a dedicated helper lemma.
    intro hsol
    exact P.exists_multiplier_of_isSolution sStar hsol
  · -- The reverse implication is the completed quadratic-model argument.
    rintro ⟨lambdaStar, hNonneg, hStationarity, hFeasible, hComplementarity, hPosSemidef⟩
    exact P.isSolution_of_exists_multiplier sStar hNonneg hStationarity hFeasible
      hComplementarity hPosSemidef

end
