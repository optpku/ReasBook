module

public import ReasLib.Optimization.DFP.InverseUpdate.QuadraticForm
public import ReasLib.Optimization.DFP.InverseUpdate.Determinant
public import ReasLib.Optimization.DFP.Orbit
public import ReasLib.Optimization.DFP.LevelSetGlobalConvergence
public import ReasLib.Optimization.DFP.AbstractSecantStep
public import ReasLib.Analysis.Convex.HessianSecant
public import ReasLib.Analysis.Calculus.ContDiff.AffineCutoffBump
public import ReasLib.Analysis.Calculus.ContDiff.AffineBounds
public import ReasLib.Analysis.Calculus.ContDiff.SupportBounds
public import ReasLib.Analysis.Calculus.EuclideanPlaneSmoothCutoff
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointBump
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointBumpBounds
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointBump.GlobalRegularity
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.RealizedObjective
public import ReasLib.Optimization.DFP.TwoPhaseControls.SlowCurve
public import ReasLib.Analysis.Convex.HessianPerturbation
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointBump.JetDecay
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointIsolation.ShrinkingSupport
public import ReasLib.Analysis.Calculus.ContDiff.DisjointFinsumC2Jets
public import ReasLib.LinearAlgebra.Matrix.OrthogonalTransport
public import ReasLib.Geometry.Euclidean.Plane.Rotation
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Tactic

/-!
# Planar DFP convergence with locally Lipschitz Hessian

The proof of `thm:planar-convergence` in `main-new.tex` controls the free
coefficient in the planar secant representation. Nonconvergence forces this
coefficient to vanish. A corrected logarithmic quantity with summable
increments rules out that degeneration under a locally Lipschitz Hessian.

The public raw-orbit theorem derives later positive definiteness from the
initial matrix and includes stationary termination. The module also proves
the C3 specialization and the failure of local Hessian Lipschitz regularity
for planar weak-Wolfe counterexamples.
-/

public section

open scoped Matrix
open Filter
open scoped Nat ContDiff
open scoped Topology

namespace DFP.PlanarConvergence

/-- Helper for lem:planar-degeneration: a symmetric planar secant matrix has
off-diagonal entry determined by its transverse entry and the secant vector. -/
theorem secantOffDiagonal {H : Matrix (Fin 2) (Fin 2) ℝ} {κ β : ℝ}
    (hH : H.IsHermitian) (hκ : κ ≠ 0)
    (hsec : H *ᵥ ![κ, β] = ![1, 0]) :
    H 0 1 = -(H 1 1 * β / κ) := by
  have hsym : H 1 0 = H 0 1 := by
    simpa using hH.apply 0 1
  have hrow := congrFun hsec 1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one] at hrow
  rw [hsym] at hrow
  apply (eq_neg_iff_add_eq_zero).mpr
  apply (mul_right_cancel₀ hκ)
  field_simp
  nlinarith [hrow]

/-- Helper for lem:planar-degeneration: the longitudinal entry follows from
the first secant equation. -/
theorem secantLongitudinal {H : Matrix (Fin 2) (Fin 2) ℝ} {κ β : ℝ}
    (hH : H.IsHermitian) (hκ : κ ≠ 0)
    (hsec : H *ᵥ ![κ, β] = ![1, 0]) :
    H 0 0 = 1 / κ + H 1 1 * β ^ 2 / κ ^ 2 := by
  have hoff := secantOffDiagonal hH hκ hsec
  have hrow := congrFun hsec 0
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one] at hrow
  rw [hoff] at hrow
  field_simp at hrow ⊢
  nlinarith [hrow]

/-- Helper for lem:planar-degeneration: in secant coordinates, the full matrix
is determined by the curvature, transverse secant component, and one free entry. -/
theorem secantMatrixRepresentation {H : Matrix (Fin 2) (Fin 2) ℝ} {κ β : ℝ}
    (hH : H.IsHermitian) (hκ : κ ≠ 0)
    (hsec : H *ᵥ ![κ, β] = ![1, 0]) :
    H = !![1 / κ + H 1 1 * β ^ 2 / κ ^ 2, -(H 1 1 * β / κ);
      -(H 1 1 * β / κ), H 1 1] := by
  have hsym : H 1 0 = H 0 1 := by
    simpa using hH.apply 0 1
  ext i j
  fin_cases i
  · fin_cases j
    · exact secantLongitudinal hH hκ hsec
    · exact secantOffDiagonal hH hκ hsec
  · fin_cases j
    · exact hsym.trans (secantOffDiagonal hH hκ hsec)
    · rfl

/-- Helper for lem:planar-degeneration: the free transverse entry is the
secant curvature times the determinant, rather than an eigenvalue. -/
theorem transverseEntry_eq_curvature_mul_det
    {H : Matrix (Fin 2) (Fin 2) ℝ} {κ β : ℝ}
    (hH : H.IsHermitian) (hκ : κ ≠ 0)
    (hsec : H *ᵥ ![κ, β] = ![1, 0]) :
    H 1 1 = κ * H.det := by
  have hsym : H 1 0 = H 0 1 := by
    simpa using hH.apply 0 1
  rw [Matrix.det_fin_two, hsym, secantLongitudinal hH hκ hsec,
    secantOffDiagonal hH hκ hsec]
  field_simp
  ring

/-- Helper for lem:planar-degeneration: positive definiteness makes the free
coefficient in the secant representation strictly positive. -/
theorem curvature_mul_det_pos {H : Matrix (Fin 2) (Fin 2) ℝ} {κ β : ℝ}
    (hH : H.PosDef) (hκ : κ ≠ 0)
    (hsec : H *ᵥ ![κ, β] = ![1, 0]) :
    0 < κ * H.det := by
  rw [← transverseEntry_eq_curvature_mul_det hH.isHermitian hκ hsec]
  exact hH.diag_pos

/-- Helper for lem:planar-degeneration: absorption of the small current-step
term yields the product bound on the free secant coefficient. -/
theorem freeCoefficientProductBound {a C u v lam : ℝ}
    (ha : 0 < a) (hlam : 0 ≤ lam) (hsmall : C * v ≤ a / 2)
    (hbound : a * lam ≤ C * v * (u + lam)) :
    lam ≤ (2 * C / a) * u * v := by
  have habsorb : C * v * lam ≤ (a / 2) * lam :=
    mul_le_mul_of_nonneg_right hsmall hlam
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
  apply (le_div_iff₀ ha).mpr
  nlinarith

/-- Helper for thm:planar-convergence: summable increments of the corrected
logarithm, a vanishing correction, and an upper bound on the gradient norms
give a positive eventual lower bound for the free secant coefficient. -/
theorem positiveLowerBoundOfCorrectedLog
    {lam eta N : ℕ → ℝ} {Nmax : ℝ}
    (hlam : ∀ k, 0 < lam k) (hN : ∀ k, 0 < N k)
    (hNupper : ∀ k, N k ≤ Nmax)
    (heta : Tendsto eta atTop (𝓝 0))
    (hincrements : Summable (fun k ↦
      |(Real.log (lam (k + 1)) - eta (k + 1) + 2 * Real.log (N (k + 1))) -
        (Real.log (lam k) - eta k + 2 * Real.log (N k))|)) :
    ∃ δ > 0, ∀ᶠ k in atTop, δ ≤ lam k := by
  let invariant : ℕ → ℝ := fun k ↦ Real.log (lam k) - eta k + 2 * Real.log (N k)
  have hdist : Summable (fun k ↦ dist (invariant k) (invariant (k + 1))) := by
    simpa only [invariant, Real.dist_eq, abs_sub_comm] using hincrements
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist hdist)
  have hInvariantLower : ∀ᶠ k in atTop, L - 1 < invariant k :=
    hL.eventually (eventually_gt_nhds (sub_lt_self L zero_lt_one))
  have hEtaLower : ∀ᶠ k in atTop, (-1 : ℝ) < eta k :=
    heta.eventually (eventually_gt_nhds (neg_lt_zero.mpr zero_lt_one))
  refine ⟨Real.exp (L - 2 - 2 * Real.log Nmax), Real.exp_pos _, ?_⟩
  filter_upwards [hInvariantLower, hEtaLower] with k hk hetaLower
  have hlogN : Real.log (N k) ≤ Real.log Nmax := Real.log_le_log (hN k) (hNupper k)
  have hlogLower : L - 2 - 2 * Real.log Nmax ≤ Real.log (lam k) := by
    dsimp only [invariant] at hk
    linarith
  have hexp := Real.exp_le_exp.mpr hlogLower
  rwa [Real.exp_log (hlam k)] at hexp

/-- Helper for thm:planar-convergence: a positive eventual lower bound is
incompatible with the degeneration of the free secant coefficient to zero. -/
theorem not_tendsto_zero_of_eventually_positive_lower_bound
    {lam : ℕ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hlower : ∀ᶠ k in atTop, δ ≤ lam k) :
    ¬ Tendsto lam atTop (𝓝 0) := by
  intro hzero
  have hle : δ ≤ 0 := ge_of_tendsto hzero hlower
  exact (not_le_of_gt hδ) hle

/-- Helper for thm:planar-convergence: the logarithm has a uniform quadratic
remainder on the half-unit interval. -/
theorem logOneAddQuadraticRemainder {r : ℝ} (hr : |r| ≤ 1 / 2) :
    |Real.log (1 + r) - r| ≤ 2 * r ^ 2 := by
  have hrlt : |-r| < 1 := by
    rw [abs_neg]
    linarith
  have hseries := Real.abs_log_sub_add_sum_range_le hrlt 1
  have htaylor : |Real.log (1 + r) - r| ≤ r ^ 2 / (1 - |r|) := by
    simpa [Finset.sum_range_succ, sub_eq_add_neg, add_comm] using hseries
  have hden : 0 < 1 - |r| := by linarith
  have hquotient : r ^ 2 / (1 - |r|) ≤ 2 * r ^ 2 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [mul_le_mul_of_nonneg_left hr (sq_nonneg r)]
  exact htaylor.trans hquotient

/-- Helper for thm:planar-convergence: after the first-order terms are
removed, the logarithmic determinant increment has a quadratic remainder. -/
theorem logDeterminantQuadraticRemainder {P Q : ℝ}
    (hP : |P| ≤ 1 / 2) (hQ : |Q| ≤ 1 / 2) :
    |2 * Real.log (1 + P) - Real.log (1 + Q) - (2 * P - Q)| ≤
      4 * P ^ 2 + 2 * Q ^ 2 := by
  have hsplit : 2 * Real.log (1 + P) - Real.log (1 + Q) - (2 * P - Q) =
      2 * (Real.log (1 + P) - P) - (Real.log (1 + Q) - Q) := by ring
  rw [hsplit]
  calc
    |2 * (Real.log (1 + P) - P) - (Real.log (1 + Q) - Q)| ≤
        |2 * (Real.log (1 + P) - P)| + |Real.log (1 + Q) - Q| :=
      abs_sub _ _
    _ = 2 * |Real.log (1 + P) - P| + |Real.log (1 + Q) - Q| := by
      norm_num [abs_mul]
    _ ≤ 4 * P ^ 2 + 2 * Q ^ 2 := by
      nlinarith [logOneAddQuadraticRemainder hP, logOneAddQuadraticRemainder hQ]

/-- Helper for thm:planar-convergence: the old secant equation eliminates
the matrix from the two linear terms in a perturbed quadratic form. -/
theorem secantQuadraticPerturbation
    {ι : Type*} [Fintype ι] {H : Matrix ι ι ℝ} {u v : ι → ℝ}
    (hH : H.IsHermitian) (hsec : H *ᵥ v = u) (dv : ι → ℝ) :
    (v + dv) ⬝ᵥ (H *ᵥ (v + dv)) =
      u ⬝ᵥ v + 2 * (u ⬝ᵥ dv) + dv ⬝ᵥ (H *ᵥ dv) := by
  have hrow : v ᵥ* H = H *ᵥ v := by
    have hstar := Matrix.star_mulVec H v
    rw [hH.eq] at hstar
    simpa using hstar.symm
  rw [Matrix.mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct,
    hsec, Matrix.dotProduct_mulVec v H dv, hrow, hsec]
  rw [dotProduct_comm v u, dotProduct_comm dv u]
  ring

/-- Helper for thm:planar-convergence: perturbing both oriented secant
vectors gives their exact curvature increment. -/
theorem secantCurvaturePerturbation
    {ι : Type*} [Fintype ι] (u v du dv : ι → ℝ) :
    (u + du) ⬝ᵥ (v + dv) =
      u ⬝ᵥ v + v ⬝ᵥ du + u ⬝ᵥ dv + du ⬝ᵥ dv := by
  rw [dotProduct_add, add_dotProduct, add_dotProduct, dotProduct_comm du v]
  ring

/-- Helper for lem:planar-degeneration: the secant-energy estimate and
vanishing step lengths force the nonnegative free coefficient to vanish. -/
theorem freeCoefficientTendstoZero {lam ell : ℕ → ℝ} {a C : ℝ}
    (ha : 0 < a) (hell : Tendsto ell atTop (𝓝 0))
    (hlam : ∀ᶠ k in atTop, 0 ≤ lam k)
    (henergy : ∀ᶠ k in atTop,
      a * lam k ≤ C * ell (k + 1) * (ell k + lam k)) :
    Tendsto lam atTop (𝓝 0) := by
  have hnext : Tendsto (fun k ↦ ell (k + 1)) atTop (𝓝 0) :=
    hell.comp (tendsto_add_atTop_nat 1)
  have hscaled : Tendsto (fun k ↦ C * ell (k + 1)) atTop (𝓝 0) := by
    simpa using hnext.const_mul C
  have hsmall : ∀ᶠ k in atTop, C * ell (k + 1) < a / 2 :=
    hscaled.eventually (eventually_lt_nhds (half_pos ha))
  have hbound : ∀ᶠ k in atTop,
      lam k ≤ (2 * C / a) * ell k * ell (k + 1) := by
    filter_upwards [hlam, hsmall, henergy] with k hk hs he
    exact freeCoefficientProductBound ha hk hs.le he
  have hproduct : Tendsto (fun k ↦ (2 * C / a) * ell k * ell (k + 1))
      atTop (𝓝 0) := by
    simpa using (hell.const_mul (2 * C / a)).mul hnext
  exact squeeze_zero' hlam hbound hproduct

/-- Helper for thm:planar-convergence: the first-order secant-vector
variation cancels from twice the curvature increment minus the quadratic
form increment. -/
theorem normalizedSecantFirstOrderCancellation
    {ι : Type*} [Fintype ι] (H : Matrix ι ι ℝ)
    (u v du dv : ι → ℝ) (κ : ℝ) :
    2 * ((v ⬝ᵥ du + u ⬝ᵥ dv + du ⬝ᵥ dv) / κ) -
        ((2 * (u ⬝ᵥ dv) + dv ⬝ᵥ (H *ᵥ dv)) / κ) =
      2 * (v ⬝ᵥ du) / κ +
        (2 * (du ⬝ᵥ dv) - dv ⬝ᵥ (H *ᵥ dv)) / κ := by
  ring

/-- Helper for thm:planar-convergence: the normalized determinant recurrence
has precisely the logarithmic form used in the corrected invariant. -/
theorem normalizedDeterminantLogIncrement {lam lamNext P Q : ℝ}
    (hlam : 0 < lam) (hP : 0 < 1 + P) (hQ : 0 < 1 + Q)
    (hrec : lamNext = lam * (1 + P) ^ 2 / (1 + Q)) :
    Real.log lamNext - Real.log lam =
      2 * Real.log (1 + P) - Real.log (1 + Q) := by
  rw [hrec, Real.log_div (mul_ne_zero (ne_of_gt hlam)
    (pow_ne_zero 2 (ne_of_gt hP))) (ne_of_gt hQ),
    Real.log_mul (ne_of_gt hlam) (pow_ne_zero 2 (ne_of_gt hP)), Real.log_pow]
  ring

/-- Helper for thm:planar-convergence: under the nonconvergent-orbit energy
estimate, no vanishing correction can make the corrected log increments
absolutely summable while the positive gradient norms remain bounded above. -/
theorem not_summable_correctedLogIncrements
    {lam eta N ell : ℕ → ℝ} {a C Nmax : ℝ}
    (ha : 0 < a) (hell : Tendsto ell atTop (𝓝 0))
    (hlam : ∀ k, 0 < lam k) (hN : ∀ k, 0 < N k)
    (hNupper : ∀ k, N k ≤ Nmax) (heta : Tendsto eta atTop (𝓝 0))
    (henergy : ∀ᶠ k in atTop,
      a * lam k ≤ C * ell (k + 1) * (ell k + lam k)) :
    ¬ Summable (fun k ↦
      |(Real.log (lam (k + 1)) - eta (k + 1) + 2 * Real.log (N (k + 1))) -
        (Real.log (lam k) - eta k + 2 * Real.log (N k))|) := by
  intro hincrements
  obtain ⟨δ, hδ, hlower⟩ :=
    positiveLowerBoundOfCorrectedLog hlam hN hNupper heta hincrements
  have hnonnegative : ∀ᶠ k in atTop, 0 ≤ lam k :=
    Eventually.of_forall (fun k ↦ (hlam k).le)
  have hzero := freeCoefficientTendstoZero ha hell hnonnegative henergy
  exact not_tendsto_zero_of_eventually_positive_lower_bound hδ hlower hzero

/-- Helper for lem:planar-degeneration: a global positive Hessian lower
bound supplies an explicit global lower bound for the objective. -/
theorem objectiveLowerBoundOfHessian
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) {μ : ℝ} (hf : ContDiff ℝ 2 f) (hμ : 0 < μ)
    (hHessian : ∀ x v : E,
      μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient f) x v) v) (x : E) :
    f 0 - ‖gradient f 0‖ ^ 2 / (2 * μ) ≤ f x := by
  have hfirst := hf.firstOrderOfHessianLowerBound f μ hμ hHessian 0 x
  simp only [sub_zero] at hfirst
  have hinner : -(‖gradient f 0‖ * ‖x‖) ≤ inner ℝ (gradient f 0) x :=
    neg_le_of_abs_le (abs_real_inner_le_norm _ _)
  have hden : 0 < 2 * μ := by positivity
  have hquadratic : -(‖gradient f 0‖ ^ 2) / (2 * μ) ≤
      inner ℝ (gradient f 0) x + μ / 2 * ‖x‖ ^ 2 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [mul_le_mul_of_nonneg_left hinner hden.le,
      sq_nonneg (μ * ‖x‖ - ‖gradient f 0‖)]
  rw [neg_div] at hquadratic
  linarith

/-- Helper for lem:planar-degeneration: a lower-bounded objective that
decreases by a fixed positive multiple of nonnegative costs has summable costs. -/
theorem summableCostsOfDescent {F q : ℕ → ℝ} {c B : ℝ}
    (hc : 0 < c) (hq : ∀ k, 0 ≤ q k) (hbelow : ∀ k, B ≤ F k)
    (hdescent : ∀ k, F (k + 1) ≤ F k - c * q k) : Summable q := by
  have hpartial : ∀ n, c * ∑ k ∈ Finset.range n, q k ≤ F 0 - F n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, mul_add]
      linarith [hdescent n]
  apply summable_of_sum_range_le (c := (F 0 - B) / c) hq
  intro n
  apply (le_div_iff₀ hc).mpr
  have hbound := hpartial n
  have hfloor := hbelow n
  nlinarith

/-- Helper for lem:planar-degeneration: the actual predicted decreases of
a positive-step weak-Wolfe DFP orbit are summable under a global positive
Hessian lower bound. -/
theorem summablePredictedDecrease {n : ℕ}
    (iteration : DFP.InverseIteration (Fin n)) {μ c₁ c₂ : ℝ}
    (hf : ContDiff ℝ 2 iteration.objective) (hμ : 0 < μ)
    (hHessian : ∀ x v,
      μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient iteration.objective) x v) v)
    (hStep : ∀ k, 0 < iteration.stepLength k)
    (hWolfe : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ iteration.objective
      (iteration.point k) (iteration.point (k + 1) - iteration.point k)) :
    Summable (fun k ↦ -inner ℝ (gradient iteration.objective (iteration.point k))
      (iteration.point (k + 1) - iteration.point k)) := by
  have hnonnegative : ∀ k, 0 ≤
      -inner ℝ (gradient iteration.objective (iteration.point k))
        (iteration.point (k + 1) - iteration.point k) := by
    intro k
    have hneg := iteration.gradientInnerDisplacementNeg k (hStep k)
    simpa only [DFP.gradients_apply] using (neg_pos.mpr hneg).le
  have hbelow := objectiveLowerBoundOfHessian iteration.objective hf hμ hHessian
  apply summableCostsOfDescent (F := fun k ↦ iteration.objective (iteration.point k))
    (hWolfe 0).c₁_pos hnonnegative
  · intro k
    exact hbelow (iteration.point k)
  · intro k
    have harmijo := (hWolfe k).armijo
    simpa only [add_sub_cancel, mul_neg, sub_neg_eq_add] using harmijo

/-- Helper for lem:planar-degeneration: strong convexity and Armijo bound
the squared physical displacement by its predicted decrease. -/
theorem stepSquareBound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {f : E → ℝ} {x y : E}
    {μ c₁ c₂ : ℝ} (hf : ContDiff ℝ 2 f) (hμ : 0 < μ)
    (hHessian : ∀ z v,
      μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient f) z v) v)
    (hWolfe : LineSearch.IsWeakWolfe c₁ c₂ f x (y - x)) :
    ‖y - x‖ ^ 2 ≤ (2 * (1 - c₁) / μ) * (-inner ℝ (gradient f x) (y - x)) := by
  have hfirst := hf.firstOrderOfHessianLowerBound f μ hμ hHessian x y
  have harmijo := hWolfe.armijo
  rw [add_sub_cancel] at harmijo
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hμ).mpr
  nlinarith

/-- Helper for lem:planar-degeneration: the squared physical step lengths
of the classical DFP orbit are summable. -/
theorem summableStepSquares {n : ℕ}
    (iteration : DFP.InverseIteration (Fin n)) {μ c₁ c₂ : ℝ}
    (hf : ContDiff ℝ 2 iteration.objective) (hμ : 0 < μ)
    (hHessian : ∀ x v,
      μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient iteration.objective) x v) v)
    (hStep : ∀ k, 0 < iteration.stepLength k)
    (hWolfe : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ iteration.objective
      (iteration.point k) (iteration.point (k + 1) - iteration.point k)) :
    Summable (fun k ↦ ‖iteration.point (k + 1) - iteration.point k‖ ^ 2) := by
  have hsum := (summablePredictedDecrease iteration hf hμ hHessian hStep hWolfe).mul_left
    (2 * (1 - c₁) / μ)
  apply Summable.of_nonneg_of_le
    (fun k ↦ sq_nonneg ‖iteration.point (k + 1) - iteration.point k‖)
    (fun k ↦ stepSquareBound hf hμ hHessian (hWolfe k)) hsum

/-- Helper for lem:planar-degeneration: the physical DFP step lengths tend
to zero, by square summability derived from strong convexity and Armijo. -/
theorem stepNormTendstoZero {n : ℕ}
    (iteration : DFP.InverseIteration (Fin n)) {μ c₁ c₂ : ℝ}
    (hf : ContDiff ℝ 2 iteration.objective) (hμ : 0 < μ)
    (hHessian : ∀ x v,
      μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient iteration.objective) x v) v)
    (hStep : ∀ k, 0 < iteration.stepLength k)
    (hWolfe : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ iteration.objective
      (iteration.point k) (iteration.point (k + 1) - iteration.point k)) :
    Tendsto (fun k ↦ ‖iteration.point (k + 1) - iteration.point k‖) atTop (𝓝 0) := by
  have hsum := summableStepSquares iteration hf hμ hHessian hStep hWolfe
  have hsqrt := hsum.tendsto_atTop_zero.sqrt
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hsqrt

/-- Helper for lem:planar-degeneration: a strong-convexity sublevel set
lies in an explicit ball about its initial point. -/
theorem sublevelRadiusBound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} {μ : ℝ} (hf : ContDiff ℝ 2 f) (hμ : 0 < μ)
    (hHessian : ∀ z v : E,
      μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient f) z v) v)
    {x₀ x : E} (hx : f x ≤ f x₀) :
    ‖x - x₀‖ ≤ 2 * ‖gradient f x₀‖ / μ := by
  have hfirst := hf.firstOrderOfHessianLowerBound f μ hμ hHessian x₀ x
  have hinner : -(‖gradient f x₀‖ * ‖x - x₀‖) ≤
      inner ℝ (gradient f x₀) (x - x₀) :=
    neg_le_of_abs_le (abs_real_inner_le_norm _ _)
  apply (le_div_iff₀ hμ).mpr
  by_contra hlarge
  have hstrict : 2 * ‖gradient f x₀‖ < ‖x - x₀‖ * μ := lt_of_not_ge hlarge
  have hnorm : 0 < ‖x - x₀‖ := by
    by_contra hnot
    have hz : ‖x - x₀‖ = 0 := le_antisymm (le_of_not_gt hnot) (norm_nonneg _)
    rw [hz, zero_mul] at hstrict
    nlinarith [norm_nonneg (gradient f x₀)]
  nlinarith [mul_lt_mul_of_pos_right hstrict hnorm]

/-- Helper for lem:planar-degeneration: in a proper Hilbert space, a
positive global Hessian lower bound makes each initial sublevel compact. -/
theorem compactInitialSublevel
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [ProperSpace E]
    {f : E → ℝ} {μ : ℝ} (hf : ContDiff ℝ 2 f) (hμ : 0 < μ)
    (hHessian : ∀ z v : E,
      μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient f) z v) v) (x₀ : E) :
    IsCompact {x | f x ≤ f x₀} := by
  have hclosed : IsClosed {x | f x ≤ f x₀} :=
    isClosed_le hf.continuous continuous_const
  apply (isCompact_closedBall x₀ (2 * ‖gradient f x₀‖ / μ)).of_isClosed_subset hclosed
  intro x hx
  rw [Metric.mem_closedBall, dist_eq_norm]
  exact sublevelRadiusBound hf hμ hHessian hx

/-- Helper for thm:planar-convergence: the strongly convex objective
attains a global minimum, obtained by minimizing on an initial sublevel. -/
theorem existsGlobalMinimizerOfHessian
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [ProperSpace E]
    {f : E → ℝ} {μ : ℝ} (hf : ContDiff ℝ 2 f) (hμ : 0 < μ)
    (hHessian : ∀ z v : E,
      μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient f) z v) v) :
    ∃ xstar, ∀ x, f xstar ≤ f x := by
  have hcompact := compactInitialSublevel hf hμ hHessian (0 : E)
  have hzero : (0 : E) ∈ {x | f x ≤ f 0} := by simp
  have hnonempty : ({x | f x ≤ f 0} : Set E).Nonempty := ⟨0, hzero⟩
  obtain ⟨xstar, hxstar, hmin⟩ := hcompact.exists_isMinOn hnonempty hf.continuous.continuousOn
  refine ⟨xstar, ?_⟩
  intro x
  by_cases hx : f x ≤ f 0
  · exact hmin hx
  · have hlevel : f xstar ≤ f 0 := hxstar
    exact hlevel.trans (le_of_lt (lt_of_not_ge hx))

/-- Helper for thm:planar-convergence: a global minimizer has zero
gradient, by Fermat's theorem and the canonical gradient-dual identity. -/
theorem gradientZeroOfGlobalMinimizer
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} {xstar : E} (hmin : ∀ x, f xstar ≤ f x) :
    gradient f xstar = 0 := by
  have hlocal : IsLocalMin f xstar := Eventually.of_forall hmin
  apply (InnerProductSpace.toDual ℝ E).injective
  rw [toDual_gradient, hlocal.fderiv_eq_zero, map_zero]

/-- Helper for thm:planar-convergence: strong convexity turns the objective
gap above a stationary point into a bound on the squared point distance. -/
theorem distanceSquareBoundOfStationaryPoint
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} {μ : ℝ} (hf : ContDiff ℝ 2 f) (hμ : 0 < μ)
    (hHessian : ∀ z v : E,
      μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient f) z v) v)
    {xstar : E} (hstar : gradient f xstar = 0) (x : E) :
    ‖x - xstar‖ ^ 2 ≤ (2 / μ) * (f x - f xstar) := by
  have hfirst := hf.firstOrderOfHessianLowerBound f μ hμ hHessian xstar x
  rw [hstar, inner_zero_left, add_zero] at hfirst
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hμ).mpr
  nlinarith

/-- Helper for thm:planar-convergence: the minimizer of an objective with
a positive global Hessian lower bound is unique. -/
theorem existsUniqueGlobalMinimizerOfHessian
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [ProperSpace E]
    {f : E → ℝ} {μ : ℝ} (hf : ContDiff ℝ 2 f) (hμ : 0 < μ)
    (hHessian : ∀ z v : E,
      μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient f) z v) v) :
    ∃! xstar, ∀ x, f xstar ≤ f x := by
  obtain ⟨xstar, hmin⟩ := existsGlobalMinimizerOfHessian hf hμ hHessian
  refine ⟨xstar, hmin, ?_⟩
  intro y hy
  have hvalues : f y = f xstar := le_antisymm (hy xstar) (hmin y)
  have hdistance := distanceSquareBoundOfStationaryPoint hf hμ hHessian
    (gradientZeroOfGlobalMinimizer hmin) y
  rw [hvalues, sub_self, mul_zero] at hdistance
  have hnorm : ‖y - xstar‖ = 0 := by nlinarith [norm_nonneg (y - xstar)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

/-- Helper for thm:planar-convergence: convergence of objective values to
the minimum implies convergence of points, using the strong-convexity gap. -/
theorem pointTendstoOfObjectiveTendsto
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} {μ : ℝ} (hf : ContDiff ℝ 2 f) (hμ : 0 < μ)
    (hHessian : ∀ z v : E,
      μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient f) z v) v)
    {xstar : E} (hstar : gradient f xstar = 0) {x : ℕ → E}
    (hvalues : Tendsto (fun k ↦ f (x k)) atTop (𝓝 (f xstar))) :
    Tendsto x atTop (𝓝 xstar) := by
  have hgap : Tendsto (fun k ↦ (2 / μ) * (f (x k) - f xstar)) atTop (𝓝 0) := by
    simpa using (hvalues.sub_const (f xstar)).const_mul (2 / μ)
  have hsq : Tendsto (fun k ↦ ‖x k - xstar‖ ^ 2) atTop (𝓝 0) :=
    squeeze_zero (fun k ↦ sq_nonneg ‖x k - xstar‖)
      (fun k ↦ distanceSquareBoundOfStationaryPoint hf hμ hHessian hstar (x k)) hgap
  have hnorm : Tendsto (fun k ↦ ‖x k - xstar‖) atTop (𝓝 0) := by
    simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hsq.sqrt
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hnorm

/-- Helper for lem:planar-degeneration: on the compact initial sublevel,
both the gradient and the Hessian have a common finite positive norm bound. -/
theorem uniformDifferentialBoundsOnSublevel
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [ProperSpace E]
    {f : E → ℝ} {μ : ℝ} (hf : ContDiff ℝ 2 f) (hμ : 0 < μ)
    (hHessian : ∀ z v : E,
      μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient f) z v) v) (x₀ : E) :
    ∃ M > 0, ∀ x, f x ≤ f x₀ →
      ‖gradient f x‖ ≤ M ∧ ‖fderiv ℝ (gradient f) x‖ ≤ M := by
  have hcompact := compactInitialSublevel hf hμ hHessian x₀
  have hfOrder : ContDiff ℝ ((1 : ℕ∞) + 1) f := by
    convert hf using 1
    norm_num
  have hgradient : ContDiff ℝ 1 (gradient f) := hfOrder.gradient_succ (n := 1)
  have hHessianContinuous : Continuous (fderiv ℝ (gradient f)) :=
    hgradient.continuous_fderiv one_ne_zero
  obtain ⟨G, hG⟩ := hcompact.exists_bound_of_continuousOn hgradient.continuous.continuousOn
  obtain ⟨B, hB⟩ := hcompact.exists_bound_of_continuousOn hHessianContinuous.continuousOn
  refine ⟨max 1 (max G B), ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  · intro x hx
    constructor
    · exact (hG x hx).trans ((le_max_left G B).trans (le_max_right _ _))
    · exact (hB x hx).trans ((le_max_right G B).trans (le_max_right _ _))

/-- Helper for lem:planar-degeneration: the global Hessian lower bound
controls every objective gap by the squared gradient norm. -/
theorem objectiveGapBoundByGradient
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} {μ : ℝ} (hf : ContDiff ℝ 2 f) (hμ : 0 < μ)
    (hHessian : ∀ z v : E,
      μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient f) z v) v) (x y : E) :
    2 * μ * (f x - f y) ≤ ‖gradient f x‖ ^ 2 := by
  have hfirst := hf.firstOrderOfHessianLowerBound f μ hμ hHessian x y
  have hinner : -(‖gradient f x‖ * ‖y - x‖) ≤ inner ℝ (gradient f x) (y - x) :=
    neg_le_of_abs_le (abs_real_inner_le_norm _ _)
  have hfactor : 0 ≤ 2 * μ := by positivity
  have hfirstScaled := mul_le_mul_of_nonneg_left hfirst hfactor
  have hinnerScaled := mul_le_mul_of_nonneg_left hinner hfactor
  nlinarith [sq_nonneg (μ * ‖y - x‖ - ‖gradient f x‖)]

/-- Helper for lem:planar-degeneration: objective values along an admissible
DFP sequence decrease to a finite limit bounded above by every iterate value. -/
theorem objectiveValuesHaveLimit {n : ℕ}
    (iteration : DFP.InverseIteration (Fin n)) {c₁ c₂ : ℝ}
    (hStep : ∀ k, 0 < iteration.stepLength k)
    (hWolfe : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ iteration.objective
      (iteration.point k) (iteration.point (k + 1) - iteration.point k))
    {xstar : EuclideanSpace ℝ (Fin n)}
    (hmin : ∀ x, iteration.objective xstar ≤ iteration.objective x) :
    ∃ F, Tendsto (fun k ↦ iteration.objective (iteration.point k)) atTop (𝓝 F) ∧
      iteration.objective xstar ≤ F ∧ ∀ k, F ≤ iteration.objective (iteration.point k) := by
  have hanti := iteration.objectiveValuesAntitoneOfWeakWolfe hStep hWolfe
  have hbounded : BddBelow (Set.range (fun k ↦ iteration.objective (iteration.point k))) := by
    refine ⟨iteration.objective xstar, ?_⟩
    rintro y ⟨k, rfl⟩
    exact hmin (iteration.point k)
  refine ⟨⨅ k, iteration.objective (iteration.point k),
    tendsto_atTop_ciInf hanti hbounded, ?_, ?_⟩
  · exact le_ciInf (fun k ↦ hmin (iteration.point k))
  · intro k
    exact ciInf_le hbounded k

/-- Helper for lem:planar-degeneration: a nonconvergent strongly convex
DFP orbit has gradient norms bounded uniformly away from zero. -/
theorem gradientLowerBoundOfNonconvergence {n : ℕ}
    (iteration : DFP.InverseIteration (Fin n)) {μ c₁ c₂ : ℝ}
    (hf : ContDiff ℝ 2 iteration.objective) (hμ : 0 < μ)
    (hHessian : ∀ x v,
      μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient iteration.objective) x v) v)
    (hStep : ∀ k, 0 < iteration.stepLength k)
    (hWolfe : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ iteration.objective
      (iteration.point k) (iteration.point (k + 1) - iteration.point k))
    {xstar : EuclideanSpace ℝ (Fin n)}
    (hmin : ∀ x, iteration.objective xstar ≤ iteration.objective x)
    (hnot : ¬ Tendsto iteration.point atTop (𝓝 xstar)) :
    ∃ Nmin > 0, ∀ k, Nmin ≤ ‖gradient iteration.objective (iteration.point k)‖ := by
  obtain ⟨F, hF, hminF, hFk⟩ := objectiveValuesHaveLimit iteration hStep hWolfe hmin
  have hstrict : iteration.objective xstar < F := by
    apply lt_of_le_of_ne hminF
    intro heq
    apply hnot
    apply pointTendstoOfObjectiveTendsto hf hμ hHessian (gradientZeroOfGlobalMinimizer hmin)
    rwa [← heq] at hF
  have hgap : 0 < 2 * μ * (F - iteration.objective xstar) := by positivity
  refine ⟨Real.sqrt (2 * μ * (F - iteration.objective xstar)),
    Real.sqrt_pos.mpr hgap, ?_⟩
  intro k
  have hbound := objectiveGapBoundByGradient hf hμ hHessian (iteration.point k) xstar
  have hfactor : 0 ≤ 2 * μ := by positivity
  have hvalue := mul_le_mul_of_nonneg_left (hFk k) hfactor
  have hsqrt := Real.sq_sqrt hgap.le
  nlinarith [norm_nonneg (gradient iteration.objective (iteration.point k))]

/-- Helper for lem:planar-degeneration: a global positive Hessian lower
bound makes the initial sublevel convex, so all accepted step segments stay inside it. -/
theorem convexInitialSublevel
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} {μ : ℝ} (hf : ContDiff ℝ 2 f) (hμ : 0 < μ)
    (hHessian : ∀ z v : E,
      μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient f) z v) v) (x₀ : E) :
    Convex ℝ {x | f x ≤ f x₀} := by
  have hstrong := hf.strongConvexOnOfHessianLowerBound f μ hμ hHessian
  have hconvex := (hstrong.strictConvexOn hμ).convexOn
  simpa only [Set.mem_univ, true_and] using hconvex.convex_le (f x₀)

/-- Helper for lem:planar-degeneration: on the actual DFP orbit, secant
norms and predicted decreases have common quadratic-scale bounds. -/
theorem secantBoundsAlongOrbit {n : ℕ}
    (iteration : DFP.InverseIteration (Fin n)) {μ c₁ c₂ : ℝ}
    (hf : ContDiff ℝ 2 iteration.objective) (hμ : 0 < μ)
    (hHessian : ∀ x v,
      μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient iteration.objective) x v) v)
    (hStep : ∀ k, 0 < iteration.stepLength k)
    (hWolfe : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ iteration.objective
      (iteration.point k) (iteration.point (k + 1) - iteration.point k)) :
    ∃ M > 0, ∀ k,
      ‖gradient iteration.objective (iteration.point (k + 1)) -
        gradient iteration.objective (iteration.point k)‖ ≤
          M * ‖iteration.point (k + 1) - iteration.point k‖ ∧
      -inner ℝ (gradient iteration.objective (iteration.point k))
        (iteration.point (k + 1) - iteration.point k) ≤
          (M / (1 - c₂)) * ‖iteration.point (k + 1) - iteration.point k‖ ^ 2 := by
  obtain ⟨M, hM, hbound⟩ := uniformDifferentialBoundsOnSublevel hf hμ hHessian
    (iteration.point 0)
  have hconvex := convexInitialSublevel hf hμ hHessian (iteration.point 0)
  have hmem := iteration.pointMemObjectiveSublevelOfWeakWolfe hStep hWolfe
  have hfOrder : ContDiff ℝ ((1 : ℕ∞) + 1) iteration.objective := by
    convert hf using 1
    norm_num
  have hgradient : ContDiff ℝ 1 (gradient iteration.objective) :=
    hfOrder.gradient_succ (n := 1)
  refine ⟨M, hM, ?_⟩
  intro k
  have hsec : ‖gradient iteration.objective (iteration.point (k + 1)) -
      gradient iteration.objective (iteration.point k)‖ ≤
        M * ‖iteration.point (k + 1) - iteration.point k‖ :=
    hconvex.norm_image_sub_le_of_norm_fderiv_le
      (fun x _ ↦ hgradient.differentiable_one.differentiableAt)
      (fun x hx ↦ (hbound x hx).2)
      ((DFP.mem_objectiveSublevel_iff iteration (iteration.point k)).mp (hmem k))
      ((DFP.mem_objectiveSublevel_iff iteration (iteration.point (k + 1))).mp (hmem (k + 1)))
  refine ⟨hsec, ?_⟩
  have hcurvature := (hWolfe k).weakCurvature
  rw [add_sub_cancel] at hcurvature
  have hpair := real_inner_le_norm
    (gradient iteration.objective (iteration.point (k + 1)) -
      gradient iteration.objective (iteration.point k))
    (iteration.point (k + 1) - iteration.point k)
  rw [inner_sub_left] at hpair
  have hsecScaled := mul_le_mul_of_nonneg_right hsec
    (norm_nonneg (iteration.point (k + 1) - iteration.point k))
  have hden : 0 < 1 - c₂ := sub_pos.mpr (hWolfe k).c₂_lt_one
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hden).mpr
  nlinarith

/-- Helper for lem:planar-degeneration: orthogonal coordinate changes
preserve positive definiteness of the inverse Hessian. -/
theorem orthogonalCoordinatesPosDef {H R : Matrix (Fin 2) (Fin 2) ℝ}
    (hH : H.PosDef) (hR : R ∈ Matrix.orthogonalGroup (Fin 2) ℝ) :
    (R.transpose * H * R).PosDef := by
  have hcancel : R.transpose * R = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (Fin 2) ℝ).mp hR
  have hleft : Function.LeftInverse R.transpose.mulVec R.mulVec := by
    intro v
    rw [Matrix.mulVec_mulVec, hcancel, Matrix.one_mulVec]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    hH.conjTranspose_mul_mul_same hleft.injective

/-- Helper for lem:planar-degeneration: orthogonal coordinate changes
preserve the determinant used to define the free secant coefficient. -/
theorem orthogonalCoordinatesDet (H R : Matrix (Fin 2) (Fin 2) ℝ)
    (hR : R ∈ Matrix.orthogonalGroup (Fin 2) ℝ) :
    (R.transpose * H * R).det = H.det := by
  have hcancel : R.transpose * R = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (Fin 2) ℝ).mp hR
  have hdet : R.det * R.det = 1 := by
    simpa only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] using
      congrArg Matrix.det hcancel
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  calc
    R.det * H.det * R.det = H.det * (R.det * R.det) := by ring
    _ = H.det := by rw [hdet, mul_one]

/-- Helper for lem:planar-degeneration: the physical secant equation
transports to the corresponding equation in an orthonormal frame. -/
theorem orthogonalCoordinatesSecant {H R : Matrix (Fin 2) (Fin 2) ℝ}
    (hR : R ∈ Matrix.orthogonalGroup (Fin 2) ℝ) {u v : Fin 2 → ℝ}
    (hsec : H *ᵥ (R *ᵥ v) = R *ᵥ u) :
    (R.transpose * H * R) *ᵥ v = u := by
  have hcancel : R.transpose * R = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (Fin 2) ℝ).mp hR
  calc
    (R.transpose * H * R) *ᵥ v = R.transpose *ᵥ (H *ᵥ (R *ᵥ v)) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    _ = R.transpose *ᵥ (R *ᵥ u) := by rw [hsec]
    _ = u := by rw [Matrix.mulVec_mulVec, hcancel, Matrix.one_mulVec]

/-- Helper for lem:planar-degeneration: the transverse matrix entry in
any secant-aligned orthonormal frame equals curvature times the physical determinant. -/
theorem orthogonalSecantFreeCoefficient {H R : Matrix (Fin 2) (Fin 2) ℝ}
    {κ β : ℝ} (hH : H.PosDef) (hR : R ∈ Matrix.orthogonalGroup (Fin 2) ℝ)
    (hκ : κ ≠ 0) (hsec : H *ᵥ (R *ᵥ ![κ, β]) = R *ᵥ ![1, 0]) :
    (R.transpose * H * R) 1 1 = κ * H.det := by
  have hK := orthogonalCoordinatesPosDef hH hR
  have hsecK := orthogonalCoordinatesSecant hR hsec
  rw [transverseEntry_eq_curvature_mul_det hK.isHermitian hκ hsecK,
    orthogonalCoordinatesDet H R hR]

/-- Helper for lem:planar-degeneration: the secant-coordinate quadratic
form splits into a nonnegative longitudinal square and a free-coefficient square. -/
theorem secantQuadraticDecomposition {H : Matrix (Fin 2) (Fin 2) ℝ} {κ β : ℝ}
    (hH : H.IsHermitian) (hκ : κ ≠ 0)
    (hsec : H *ᵥ ![κ, β] = ![1, 0]) (g : Fin 2 → ℝ) :
    g ⬝ᵥ (H *ᵥ g) = (g 0) ^ 2 / κ + H 1 1 * (g 1 - β / κ * g 0) ^ 2 := by
  have hsym : H 1 0 = H 0 1 := by simpa using hH.apply 0 1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [hsym, secantLongitudinal hH hκ hsec, secantOffDiagonal hH hκ hsec]
  field_simp
  ring

/-- Helper for lem:planar-degeneration: the transverse square gives a
lower bound on the secant-coordinate gradient energy. -/
theorem secantEnergyLowerBound {H : Matrix (Fin 2) (Fin 2) ℝ} {κ β : ℝ}
    (hH : H.IsHermitian) (hκ : 0 < κ)
    (hsec : H *ᵥ ![κ, β] = ![1, 0]) (g : Fin 2 → ℝ) :
    H 1 1 * (g 1 - β / κ * g 0) ^ 2 ≤ g ⬝ᵥ (H *ᵥ g) := by
  rw [secantQuadraticDecomposition hH hκ.ne' hsec g]
  exact le_add_of_nonneg_left (div_nonneg (sq_nonneg _) hκ.le)

/-- Helper for lem:planar-degeneration: the secant-coordinate search
direction is the sum of its longitudinal and free-coefficient components. -/
theorem secantActionDecomposition {H : Matrix (Fin 2) (Fin 2) ℝ} {κ β : ℝ}
    (hH : H.IsHermitian) (hκ : κ ≠ 0)
    (hsec : H *ᵥ ![κ, β] = ![1, 0]) (g : Fin 2 → ℝ) :
    (WithLp.toLp 2 (H *ᵥ g) : EuclideanSpace ℝ (Fin 2)) =
      (g 0 / κ) • WithLp.toLp 2 ![1, 0] +
        (H 1 1 * (g 1 - β / κ * g 0)) • WithLp.toLp 2 ![-β / κ, 1] := by
  have hsym : H 1 0 = H 0 1 := by simpa using hH.apply 0 1
  ext i
  fin_cases i
  · norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two, PiLp.toLp_apply,
      PiLp.add_apply, PiLp.smul_apply, secantLongitudinal hH hκ hsec,
      secantOffDiagonal hH hκ hsec]
    field_simp
    ring
  · norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two, PiLp.toLp_apply,
      PiLp.add_apply, PiLp.smul_apply, hsym, secantOffDiagonal hH hκ hsec]
    field_simp
    ring

/-- Helper for lem:planar-degeneration: the exact secant decomposition
bounds the search-direction norm by the longitudinal component and the free coefficient. -/
theorem secantActionNormBound {H : Matrix (Fin 2) (Fin 2) ℝ} {κ β : ℝ}
    (hH : H.PosDef) (hκ : 0 < κ)
    (hsec : H *ᵥ ![κ, β] = ![1, 0]) (g : Fin 2 → ℝ) :
    ‖(WithLp.toLp 2 (H *ᵥ g) : EuclideanSpace ℝ (Fin 2))‖ ≤
      |g 0| / κ + H 1 1 * |g 1 - β / κ * g 0| *
        ‖(WithLp.toLp 2 ![-β / κ, 1] : EuclideanSpace ℝ (Fin 2))‖ := by
  have hunit : ‖(WithLp.toLp 2 ![1, 0] : EuclideanSpace ℝ (Fin 2))‖ = 1 := by
    simp [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  rw [secantActionDecomposition hH.isHermitian hκ.ne' hsec g]
  have htriangle := norm_add_le
    ((g 0 / κ) • (WithLp.toLp 2 ![1, 0] : EuclideanSpace ℝ (Fin 2)))
    ((H 1 1 * (g 1 - β / κ * g 0)) •
      (WithLp.toLp 2 ![-β / κ, 1] : EuclideanSpace ℝ (Fin 2)))
  simpa only [norm_smul, Real.norm_eq_abs, abs_div, abs_mul,
    abs_of_pos hκ, abs_of_pos hH.diag_pos, hunit, mul_one] using htriangle

/-- Helper for lem:planar-degeneration: a quadratic bound on the predicted
decrease of a positive multiple of `-v` gives the corresponding energy-to-direction bound. -/
theorem energyDirectionBound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {g v s : E} {α C : ℝ} (hα : 0 < α) (hstep : s = α • (-v))
    (hdescent : -inner ℝ g s ≤ C * ‖s‖ ^ 2) :
    inner ℝ g v ≤ C * ‖s‖ * ‖v‖ := by
  have hnorm : ‖s‖ = α * ‖v‖ := by
    rw [hstep, norm_smul, norm_neg, Real.norm_eq_abs, abs_of_pos hα]
  have hpair : -inner ℝ g s = α * inner ℝ g v := by
    rw [hstep, inner_smul_right, inner_neg_right]
    ring
  rw [hpair, hnorm] at hdescent
  rw [hnorm]
  apply (mul_le_mul_iff_right₀ hα).mp
  nlinarith [hdescent]

/-- Helper for lem:planar-degeneration: the Euclidean norm of a planar
vector is bounded by the sum of its coordinate absolute values. -/
theorem planarNormLeCoordinateAbsSum (g : Fin 2 → ℝ) :
    ‖(WithLp.toLp 2 g : EuclideanSpace ℝ (Fin 2))‖ ≤ |g 0| + |g 1| := by
  have hsq := EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 g)
  simp only [Fin.sum_univ_two] at hsq
  nlinarith [sq_abs (g 0), sq_abs (g 1), abs_nonneg (g 0), abs_nonneg (g 1),
    norm_nonneg (WithLp.toLp 2 g), mul_nonneg (abs_nonneg (g 0)) (abs_nonneg (g 1))]

/-- Helper for lem:planar-degeneration: a bounded secant tilt and a small
longitudinal gradient component force a lower bound on the transverse pairing. -/
theorem transversePairingLowerBound (g : Fin 2 → ℝ) {b B N : ℝ}
    (htilt : |b| ≤ B)
    (hgradient : N ≤ ‖(WithLp.toLp 2 g : EuclideanSpace ℝ (Fin 2))‖)
    (hlongitudinal : (1 + B) * |g 0| ≤ N / 2) :
    N / 2 ≤ |g 1 - b * g 0| := by
  have hnorm := planarNormLeCoordinateAbsSum g
  have htriangle := abs_add_le (g 1 - b * g 0) (b * g 0)
  rw [sub_add_cancel, abs_mul] at htriangle
  have htiltProduct := mul_le_mul_of_nonneg_right htilt (abs_nonneg (g 0))
  linarith

/-- Helper for lem:planar-degeneration: a nonvanishing gradient and a small
longitudinal component give a uniform multiple of the free coefficient as an energy lower bound. -/
theorem secantEnergyLowerBoundOfGradientNorm
    {H : Matrix (Fin 2) (Fin 2) ℝ} {κ β B N : ℝ}
    (hH : H.PosDef) (hκ : 0 < κ)
    (hsec : H *ᵥ ![κ, β] = ![1, 0]) (g : Fin 2 → ℝ)
    (hN : 0 ≤ N) (htilt : |β / κ| ≤ B)
    (hgradient : N ≤ ‖(WithLp.toLp 2 g : EuclideanSpace ℝ (Fin 2))‖)
    (hlongitudinal : (1 + B) * |g 0| ≤ N / 2) :
    (N ^ 2 / 4) * H 1 1 ≤ g ⬝ᵥ (H *ᵥ g) := by
  have hpairing := transversePairingLowerBound g htilt hgradient hlongitudinal
  have hsquare : N ^ 2 / 4 ≤ (g 1 - β / κ * g 0) ^ 2 := by
    nlinarith [sq_abs (g 1 - β / κ * g 0)]
  have hscaled := mul_le_mul_of_nonneg_left hsquare (hH.diag_pos (i := 1)).le
  have henergy := secantEnergyLowerBound hH.isHermitian hκ hsec g
  nlinarith

/-- Helper for lem:planar-degeneration: the transpose of an orthogonal
frame is orthogonal as well. -/
theorem orthogonalTranspose {R : Matrix (Fin 2) (Fin 2) ℝ}
    (hR : R ∈ Matrix.orthogonalGroup (Fin 2) ℝ) :
    R.transpose ∈ Matrix.orthogonalGroup (Fin 2) ℝ := by
  apply (Matrix.mem_orthogonalGroup_iff (Fin 2) ℝ).mpr
  rw [Matrix.transpose_transpose]
  exact (Matrix.mem_orthogonalGroup_iff' (Fin 2) ℝ).mp hR

/-- Helper for lem:planar-degeneration: the inverse-Hessian action
commutes with passage to orthonormal secant coordinates. -/
theorem orthogonalCoordinatesAction (H R : Matrix (Fin 2) (Fin 2) ℝ)
    (hR : R ∈ Matrix.orthogonalGroup (Fin 2) ℝ) (g : Fin 2 → ℝ) :
    (R.transpose * H * R) *ᵥ (R.transpose *ᵥ g) = R.transpose *ᵥ (H *ᵥ g) := by
  simpa only [Matrix.transpose_transpose] using
    Matrix.conjugate_mulVec_of_mem_orthogonalGroup R.transpose H (orthogonalTranspose hR) g

/-- Helper for lem:planar-degeneration: the physical gradient energy
agrees with its expression in orthonormal secant coordinates. -/
theorem orthogonalCoordinatesEnergy (H R : Matrix (Fin 2) (Fin 2) ℝ)
    (hR : R ∈ Matrix.orthogonalGroup (Fin 2) ℝ) (g : Fin 2 → ℝ) :
    (R.transpose *ᵥ g) ⬝ᵥ ((R.transpose * H * R) *ᵥ (R.transpose *ᵥ g)) =
      g ⬝ᵥ (H *ᵥ g) := by
  rw [orthogonalCoordinatesAction H R hR g]
  exact Matrix.dotProduct_mulVec_eq_of_mem_orthogonalGroup R.transpose
    (orthogonalTranspose hR) g (H *ᵥ g)

/-- Helper for lem:planar-degeneration: the physical search-direction
norm agrees with its expression in orthonormal secant coordinates. -/
theorem orthogonalCoordinatesActionNorm (H R : Matrix (Fin 2) (Fin 2) ℝ)
    (hR : R ∈ Matrix.orthogonalGroup (Fin 2) ℝ) (g : Fin 2 → ℝ) :
    ‖(WithLp.toLp 2 ((R.transpose * H * R) *ᵥ (R.transpose *ᵥ g)) :
      EuclideanSpace ℝ (Fin 2))‖ = ‖WithLp.toLp 2 (H *ᵥ g)‖ := by
  rw [orthogonalCoordinatesAction H R hR g]
  exact Matrix.norm_toLp_mulVec_eq_of_mem_orthogonalGroup R.transpose
    (orthogonalTranspose hR) (H *ᵥ g)

/-- Helper for lem:planar-degeneration: the weak-Wolfe upper descent
bound controls the actual inverse-Hessian energy relative to its direction norm. -/
theorem orbitEnergyDirectionBound {n : ℕ}
    (iteration : DFP.InverseIteration (Fin n)) {μ c₁ c₂ : ℝ}
    (hf : ContDiff ℝ 2 iteration.objective) (hμ : 0 < μ)
    (hHessian : ∀ x v,
      μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient iteration.objective) x v) v)
    (hStep : ∀ k, 0 < iteration.stepLength k)
    (hWolfe : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ iteration.objective
      (iteration.point k) (iteration.point (k + 1) - iteration.point k)) :
    ∃ C > 0, ∀ k,
      let g := gradient iteration.objective (iteration.point k)
      let v : EuclideanSpace ℝ (Fin n) :=
        WithLp.toLp 2 (iteration.inverseHessian k *ᵥ WithLp.ofLp g)
      inner ℝ g v ≤ C * ‖iteration.point (k + 1) - iteration.point k‖ * ‖v‖ := by
  obtain ⟨M, hM, hbounds⟩ := secantBoundsAlongOrbit iteration hf hμ hHessian hStep hWolfe
  have hden : 0 < 1 - c₂ := sub_pos.mpr (hWolfe 0).c₂_lt_one
  refine ⟨M / (1 - c₂), div_pos hM hden, ?_⟩
  intro k
  have hstep : iteration.point (k + 1) - iteration.point k =
      iteration.stepLength k •
        (-(WithLp.toLp 2 (iteration.inverseHessian k *ᵥ
          WithLp.ofLp (gradient iteration.objective (iteration.point k))) :
            EuclideanSpace ℝ (Fin n))) := by
    rw [iteration.pointSucc k, DFP.steps_apply, DFP.directions_apply, DFP.gradients_apply]
    abel
  exact energyDirectionBound (hStep k) hstep (hbounds k).2

/-- Helper for lem:planar-degeneration: every step of an infinite
positive-step DFP orbit is nonzero. -/
theorem orbitStepNormPos {n : ℕ}
    (iteration : DFP.InverseIteration (Fin n)) (k : ℕ)
    (hStep : 0 < iteration.stepLength k) :
    0 < ‖iteration.point (k + 1) - iteration.point k‖ := by
  apply norm_pos_iff.mpr
  intro hzero
  have hdescent := iteration.gradientInnerDisplacementNeg k hStep
  rw [hzero, inner_zero_right] at hdescent
  exact lt_irrefl 0 hdescent

/-- Helper for lem:planar-degeneration: the original DFP recurrence
implies the exact secant equation between actual point and gradient differences. -/
theorem orbitSecantEquation {n : ℕ}
    (iteration : DFP.InverseIteration (Fin n)) (k : ℕ) :
    iteration.inverseHessian (k + 1) *ᵥ
        WithLp.ofLp (gradient iteration.objective (iteration.point (k + 1)) -
          gradient iteration.objective (iteration.point k)) =
      WithLp.ofLp (iteration.point (k + 1) - iteration.point k) := by
  have hden := iteration.denominators_spec k
  have hsec := Matrix.inverseDFPUpdate_mulVec_secant hden.1 hden.2
  rw [← iteration.inverseHessianSucc k] at hsec
  have hstep : iteration.point (k + 1) - iteration.point k =
      DFP.steps iteration.stepLength
        (DFP.directions iteration.inverseHessian
          (DFP.gradients iteration.objective iteration.point)) k := by
    rw [iteration.pointSucc k]
    abel
  simpa only [DFP.gradientChanges_apply, DFP.gradients_apply, hstep] using hsec

/-- Helper for lem:planar-degeneration: normalizing the displacement and
gradient change by the same step length preserves the exact secant equation. -/
theorem normalizedOrbitSecantEquation {n : ℕ}
    (iteration : DFP.InverseIteration (Fin n)) (k : ℕ) :
    iteration.inverseHessian (k + 1) *ᵥ
        WithLp.ofLp (‖iteration.point (k + 1) - iteration.point k‖⁻¹ •
          (gradient iteration.objective (iteration.point (k + 1)) -
            gradient iteration.objective (iteration.point k))) =
      WithLp.ofLp (‖iteration.point (k + 1) - iteration.point k‖⁻¹ •
        (iteration.point (k + 1) - iteration.point k)) := by
  simp only [WithLp.ofLp_smul, Matrix.mulVec_smul, orbitSecantEquation]

/-- Helper for lem:planar-degeneration: the new gradient's component
along a normalized old step is small whenever descent and secants have quadratic-scale bounds. -/
theorem longitudinalGradientBound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g gNext s : E) {C M : ℝ}
    (hdescent : inner ℝ g s ≤ 0)
    (hdecrease : -inner ℝ g s ≤ C * ‖s‖ ^ 2)
    (hsecant : ‖gNext - g‖ ≤ M * ‖s‖) :
    |inner ℝ (‖s‖⁻¹ • s) gNext| ≤ (C + M) * ‖s‖ := by
  by_cases hs : s = 0
  · simp [hs]
  have hnorm : 0 < ‖s‖ := norm_pos_iff.mpr hs
  have hsplit : inner ℝ s gNext = inner ℝ g s + inner ℝ (gNext - g) s := by
    rw [inner_sub_left, real_inner_comm s gNext]
    ring
  have htriangle := abs_add_le (inner ℝ g s) (inner ℝ (gNext - g) s)
  rw [abs_of_nonpos hdescent] at htriangle
  have hsecantPair := abs_real_inner_le_norm (gNext - g) s
  have hsecantScaled := mul_le_mul_of_nonneg_right hsecant (norm_nonneg s)
  have htotal : |inner ℝ s gNext| ≤ (C + M) * ‖s‖ ^ 2 := by
    rw [hsplit]
    nlinarith
  rw [real_inner_smul_left, abs_mul, abs_inv, abs_norm, ← div_eq_inv_mul]
  apply (div_le_iff₀ hnorm).mpr
  nlinarith

/-- Helper for lem:planar-degeneration: on the actual DFP orbit the
new gradient has a uniformly small component along the previous normalized step. -/
theorem orbitLongitudinalGradientBound {n : ℕ}
    (iteration : DFP.InverseIteration (Fin n)) {μ c₁ c₂ : ℝ}
    (hf : ContDiff ℝ 2 iteration.objective) (hμ : 0 < μ)
    (hHessian : ∀ x v,
      μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient iteration.objective) x v) v)
    (hStep : ∀ k, 0 < iteration.stepLength k)
    (hWolfe : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ iteration.objective
      (iteration.point k) (iteration.point (k + 1) - iteration.point k)) :
    ∃ C > 0, ∀ k,
      |inner ℝ (‖iteration.point (k + 1) - iteration.point k‖⁻¹ •
          (iteration.point (k + 1) - iteration.point k))
        (gradient iteration.objective (iteration.point (k + 1)))| ≤
      C * ‖iteration.point (k + 1) - iteration.point k‖ := by
  obtain ⟨M, hM, hbounds⟩ := secantBoundsAlongOrbit iteration hf hμ hHessian hStep hWolfe
  have hden : 0 < 1 - c₂ := sub_pos.mpr (hWolfe 0).c₂_lt_one
  have hC : 0 < M / (1 - c₂) + M := add_pos (div_pos hM hden) hM
  refine ⟨M / (1 - c₂) + M, hC, ?_⟩
  intro k
  have hdescent : inner ℝ (gradient iteration.objective (iteration.point k))
      (iteration.point (k + 1) - iteration.point k) ≤ 0 := by
    simpa only [DFP.gradients_apply] using
      (iteration.gradientInnerDisplacementNeg k (hStep k)).le
  exact longitudinalGradientBound _ _ _ hdescent (hbounds k).2 (hbounds k).1

/-- Helper for lem:planar-degeneration: simultaneous secant normalization
expresses curvature as the secant pairing divided by squared step length. -/
theorem normalizedSecantCurvature
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (s y : E) :
    inner ℝ (‖s‖⁻¹ • s) (‖s‖⁻¹ • y) = inner ℝ y s / ‖s‖ ^ 2 := by
  rw [real_inner_smul_left, real_inner_smul_right, real_inner_comm s y]
  ring

/-- Helper for lem:planar-degeneration: the normalized secant curvature
of every physical DFP step is bounded below by the strong-convexity constant. -/
theorem normalizedOrbitCurvatureLowerBound {n : ℕ}
    (iteration : DFP.InverseIteration (Fin n)) {μ : ℝ}
    (hf : ContDiff ℝ 2 iteration.objective) (hμ : 0 < μ)
    (hHessian : ∀ x v,
      μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient iteration.objective) x v) v)
    (k : ℕ) (hStep : 0 < iteration.stepLength k) :
    let s := iteration.point (k + 1) - iteration.point k
    let y := gradient iteration.objective (iteration.point (k + 1)) -
      gradient iteration.objective (iteration.point k)
    μ ≤ inner ℝ (‖s‖⁻¹ • s) (‖s‖⁻¹ • y) := by
  dsimp only
  rw [normalizedSecantCurvature]
  apply (le_div_iff₀ (sq_pos_of_pos (orbitStepNormPos iteration k hStep))).mpr
  exact inner_gradient_sub_ge_of_hessian_lower_bound iteration.objective μ hf hμ
    hHessian (iteration.point k) (iteration.point (k + 1))

/-- Helper for lem:planar-degeneration: the first column of the canonical
oriented planar frame is its defining vector. -/
theorem planarFrameFirstColumn (u : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) :
    EuclideanPlane.frame u i 0 = u i := by
  have hcolumn := congrFun (EuclideanPlane.frame_mulVec u 1 0) i
  simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using hcolumn

/-- Helper for lem:planar-degeneration: the second column of the canonical
oriented planar frame is the positively rotated defining vector. -/
theorem planarFrameSecondColumn (u : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) :
    EuclideanPlane.frame u i 1 = EuclideanPlane.perp u i := by
  have hcolumn := congrFun (EuclideanPlane.frame_mulVec u 0 1) i
  simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using hcolumn

/-- Helper for lem:planar-degeneration: coordinates in the canonical
planar frame are the two inner products with its columns. -/
theorem planarFrameCoordinates (u v : EuclideanSpace ℝ (Fin 2)) :
    (EuclideanPlane.frame u).transpose *ᵥ WithLp.ofLp v =
      ![inner ℝ u v, inner ℝ (EuclideanPlane.perp u) v] := by
  ext i
  fin_cases i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.transpose_apply, planarFrameFirstColumn, EuclideanSpace.inner_eq_star_dotProduct]
    ring
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.transpose_apply, planarFrameSecondColumn, EuclideanSpace.inner_eq_star_dotProduct]
    ring

/-- Helper for lem:planar-degeneration: normalizing a nonzero step gives
an orthogonal frame with that step as its first direction. -/
theorem normalizedStepFrameOrthogonal
    (s : EuclideanSpace ℝ (Fin 2)) (hs : s ≠ 0) :
    EuclideanPlane.frame (‖s‖⁻¹ • s) ∈ Matrix.orthogonalGroup (Fin 2) ℝ := by
  have hnorm : ‖‖s‖⁻¹ • s‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hs)]
  have hspecial := (EuclideanPlane.frame_mem_specialOrthogonalGroup_iff _).mpr hnorm
  exact (Matrix.mem_specialOrthogonalGroup_iff.mp hspecial).1

/-- Helper for lem:planar-degeneration: a unit planar step and its
secant vector give the standard secant equation in the step's oriented frame. -/
theorem planarSecantFrameSpecification
    (H : Matrix (Fin 2) (Fin 2) ℝ) (u v : EuclideanSpace ℝ (Fin 2))
    (hu : ‖u‖ = 1) (hsec : H *ᵥ WithLp.ofLp v = WithLp.ofLp u) :
    ((EuclideanPlane.frame u).transpose * H * EuclideanPlane.frame u) *ᵥ
      ![inner ℝ u v, inner ℝ (EuclideanPlane.perp u) v] = ![1, 0] := by
  have hspecial := (EuclideanPlane.frame_mem_specialOrthogonalGroup_iff u).mpr hu
  have hR := (Matrix.mem_specialOrthogonalGroup_iff.mp hspecial).1
  have hcancel : EuclideanPlane.frame u * (EuclideanPlane.frame u).transpose = 1 :=
    (Matrix.mem_orthogonalGroup_iff (Fin 2) ℝ).mp hR
  have hvector : EuclideanPlane.frame u *ᵥ
      ![inner ℝ u v, inner ℝ (EuclideanPlane.perp u) v] = WithLp.ofLp v := by
    rw [← planarFrameCoordinates, Matrix.mulVec_mulVec, hcancel, Matrix.one_mulVec]
  have hfirst : EuclideanPlane.frame u *ᵥ ![1, 0] = WithLp.ofLp u := by
    ext i
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using planarFrameFirstColumn u i
  have hsource : H *ᵥ (EuclideanPlane.frame u *ᵥ
      ![inner ℝ u v, inner ℝ (EuclideanPlane.perp u) v]) =
        EuclideanPlane.frame u *ᵥ ![1, 0] := by
    rw [hvector, hfirst]
    exact hsec
  exact orthogonalCoordinatesSecant hR hsource

/-- Helper for lem:planar-degeneration: in the previous-step frame, the
actual DFP matrix satisfies the standard planar secant equation. -/
theorem orbitPlanarSecantFrameSpecification
    (iteration : DFP.InverseIteration (Fin 2)) (k : ℕ)
    (hStep : 0 < iteration.stepLength k) :
    let s := iteration.point (k + 1) - iteration.point k
    let u := ‖s‖⁻¹ • s
    let v := ‖s‖⁻¹ • (gradient iteration.objective (iteration.point (k + 1)) -
      gradient iteration.objective (iteration.point k))
    ((EuclideanPlane.frame u).transpose * iteration.inverseHessian (k + 1) *
      EuclideanPlane.frame u) *ᵥ ![inner ℝ u v, inner ℝ (EuclideanPlane.perp u) v] =
        ![1, 0] := by
  dsimp only
  have hnorm : ‖‖iteration.point (k + 1) - iteration.point k‖⁻¹ •
      (iteration.point (k + 1) - iteration.point k)‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
      inv_mul_cancel₀ (orbitStepNormPos iteration k hStep).ne']
  exact planarSecantFrameSpecification _ _ _ hnorm (normalizedOrbitSecantEquation iteration k)

/-- Helper for lem:planar-degeneration: a positive curvature lower bound
and a bound on the transverse secant control its normalized tilt. -/
theorem secantTiltBound {μ κ β M : ℝ} (hμ : 0 < μ) (hκ : μ ≤ κ)
    (hβ : |β| ≤ M) : |β / κ| ≤ M / μ := by
  have hκpos := hμ.trans_le hκ
  have hM : 0 ≤ M := (abs_nonneg β).trans hβ
  rw [abs_div, abs_of_pos hκpos]
  apply (div_le_iff₀ hκpos).mpr
  calc
    |β| ≤ M := hβ
    _ = (M / μ) * μ := (div_mul_cancel₀ M hμ.ne').symm
    _ ≤ (M / μ) * κ := mul_le_mul_of_nonneg_left hκ (div_nonneg hM hμ.le)

/-- Helper for lem:planar-degeneration: uniformly bounded gradients and
secant tilts bound the matrix action by the old step scale plus the free coefficient. -/
theorem secantActionUniformBound
    {H : Matrix (Fin 2) (Fin 2) ℝ} {κ β μ A B G ell : ℝ}
    (hH : H.PosDef) (hμ : 0 < μ) (hκ : μ ≤ κ)
    (hsec : H *ᵥ ![κ, β] = ![1, 0]) (g : Fin 2 → ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hG : 0 ≤ G) (hell : 0 ≤ ell)
    (htilt : |β / κ| ≤ B)
    (hgradient : ‖(WithLp.toLp 2 g : EuclideanSpace ℝ (Fin 2))‖ ≤ G)
    (hlongitudinal : |g 0| ≤ A * ell) :
    ‖(WithLp.toLp 2 (H *ᵥ g) : EuclideanSpace ℝ (Fin 2))‖ ≤
      (A / μ + G * (1 + B) ^ 2) * (ell + H 1 1) := by
  have hκpos := hμ.trans_le hκ
  have hfree : 0 ≤ H 1 1 := (hH.diag_pos (i := 1)).le
  have hcoord (i : Fin 2) : |g i| ≤ G := by
    have hbound := (PiLp.norm_apply_le (WithLp.toLp 2 g) i).trans hgradient
    simpa only [Real.norm_eq_abs] using hbound
  have hpair : |g 1 - β / κ * g 0| ≤ (1 + B) * G := by
    have htriangle := abs_sub (g 1) (β / κ * g 0)
    rw [abs_mul] at htriangle
    have hproduct := mul_le_mul htilt (hcoord 0) (abs_nonneg (g 0)) hB
    nlinarith [hcoord 1]
  have hvector : ‖(WithLp.toLp 2 ![-β / κ, 1] : EuclideanSpace ℝ (Fin 2))‖ ≤ 1 + B := by
    have hnorm := planarNormLeCoordinateAbsSum ![-β / κ, 1]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, abs_one, neg_div, abs_neg] at hnorm
    have hsum : |β / κ| + 1 ≤ 1 + B := by linarith
    simpa only [neg_div] using hnorm.trans hsum
  have hlong : |g 0| / κ ≤ (A / μ) * ell := by
    apply (div_le_iff₀ hκpos).mpr
    calc
      |g 0| ≤ A * ell := hlongitudinal
      _ = ((A / μ) * ell) * μ := by field_simp
      _ ≤ ((A / μ) * ell) * κ :=
        mul_le_mul_of_nonneg_left hκ (mul_nonneg (div_nonneg hA hμ.le) hell)
  have htransverse : H 1 1 * |g 1 - β / κ * g 0| *
      ‖(WithLp.toLp 2 ![-β / κ, 1] : EuclideanSpace ℝ (Fin 2))‖ ≤
        H 1 1 * (G * (1 + B) ^ 2) := by
    have hpositive : 0 ≤ H 1 1 * ((1 + B) * G) := by positivity
    have hbound := mul_le_mul (mul_le_mul_of_nonneg_left hpair hfree)
      hvector (norm_nonneg _) hpositive
    nlinarith [hbound]
  have haction := secantActionNormBound hH hκpos hsec g
  have hcross₁ := mul_nonneg (div_nonneg hA hμ.le) hfree
  have hcross₂ := mul_nonneg (mul_nonneg hG (sq_nonneg (1 + B))) hell
  nlinarith

/-- Helper for lem:planar-degeneration: uniform secant-coordinate
estimates yield an eventual product bound and vanishing of the free matrix entry. -/
theorem secantSequenceDegeneration
    (H : ℕ → Matrix (Fin 2) (Fin 2) ℝ) (g : ℕ → Fin 2 → ℝ)
    (κ β ell : ℕ → ℝ) {μ A B G N C : ℝ}
    (hμ : 0 < μ) (hA : 0 < A) (hB : 0 ≤ B) (hG : 0 < G)
    (hN : 0 < N) (hC : 0 < C)
    (hH : ∀ k, (H k).PosDef) (hκ : ∀ k, μ ≤ κ k)
    (hsec : ∀ k, H k *ᵥ ![κ k, β k] = ![1, 0])
    (hell : ∀ k, 0 ≤ ell k) (hellLimit : Tendsto ell atTop (𝓝 0))
    (htilt : ∀ k, |β k / κ k| ≤ B)
    (hgradientLower : ∀ k, N ≤ ‖(WithLp.toLp 2 (g k) : EuclideanSpace ℝ (Fin 2))‖)
    (hgradientUpper : ∀ k, ‖(WithLp.toLp 2 (g k) : EuclideanSpace ℝ (Fin 2))‖ ≤ G)
    (hlongitudinal : ∀ k, |g k 0| ≤ A * ell k)
    (henergy : ∀ k, g k ⬝ᵥ (H k *ᵥ g k) ≤ C * ell (k + 1) *
      ‖(WithLp.toLp 2 (H k *ᵥ g k) : EuclideanSpace ℝ (Fin 2))‖) :
    (∃ K > 0, ∀ᶠ k in atTop, 0 < H k 1 1 ∧ H k 1 1 ≤ K * ell k * ell (k + 1)) ∧
      Tendsto (fun k ↦ H k 1 1) atTop (𝓝 0) := by
  let D := A / μ + G * (1 + B) ^ 2
  have hD : 0 < D := by
    dsimp only [D]
    positivity
  have ha : 0 < N ^ 2 / 4 := by positivity
  have hlongSmall : ∀ᶠ k in atTop, (1 + B) * (A * ell k) < N / 2 := by
    have hlim : Tendsto (fun k ↦ (1 + B) * (A * ell k)) atTop (𝓝 0) := by
      simpa using (hellLimit.const_mul A).const_mul (1 + B)
    exact hlim.eventually (eventually_lt_nhds (half_pos hN))
  have henergyBound : ∀ᶠ k in atTop,
      (N ^ 2 / 4) * H k 1 1 ≤ (C * D) * ell (k + 1) * (ell k + H k 1 1) := by
    filter_upwards [hlongSmall] with k hk
    have hlong : (1 + B) * |g k 0| ≤ N / 2 := by
      have hfactor : 0 ≤ 1 + B := by positivity
      exact (mul_le_mul_of_nonneg_left (hlongitudinal k) hfactor).trans hk.le
    have hlower := secantEnergyLowerBoundOfGradientNorm (hH k) (hμ.trans_le (hκ k))
      (hsec k) (g k) hN.le (htilt k) (hgradientLower k) hlong
    have hupper := secantActionUniformBound (hH k) hμ (hκ k) (hsec k) (g k)
      hA.le hB hG.le (hell k) (htilt k) (hgradientUpper k) (hlongitudinal k)
    have hfactor : 0 ≤ C * ell (k + 1) := mul_nonneg hC.le (hell (k + 1))
    have hscaled := mul_le_mul_of_nonneg_left hupper hfactor
    dsimp only [D]
    nlinarith [henergy k]
  have hnonnegative : ∀ᶠ k in atTop, 0 ≤ H k 1 1 :=
    Eventually.of_forall (fun k ↦ (hH k).diag_pos.le)
  have hzero := freeCoefficientTendstoZero ha hellLimit hnonnegative henergyBound
  refine ⟨?_, hzero⟩
  have hconstant : 0 < 2 * (C * D) / (N ^ 2 / 4) := by positivity
  refine ⟨2 * (C * D) / (N ^ 2 / 4), hconstant, ?_⟩
  have hsmall : ∀ᶠ k in atTop, (C * D) * ell (k + 1) < (N ^ 2 / 4) / 2 := by
    have hlim : Tendsto (fun k ↦ (C * D) * ell (k + 1)) atTop (𝓝 0) := by
      simpa using (hellLimit.comp (tendsto_add_atTop_nat 1)).const_mul (C * D)
    exact hlim.eventually (eventually_lt_nhds (half_pos ha))
  filter_upwards [henergyBound, hsmall] with k hk hs
  exact ⟨(hH k).diag_pos,
    freeCoefficientProductBound ha (hH k).diag_pos.le hs.le hk⟩

/-- Helper for lem:planar-degeneration: failure of convergence of the
actual planar DFP orbit forces its free secant coefficient to vanish, with
an eventual bound by the product of adjacent physical step lengths.
The index `k` here represents the paper's coefficient at iteration `k + 1`. -/
theorem orbitFreeCoefficientDegeneration
    (iteration : DFP.InverseIteration (Fin 2)) {μ c₁ c₂ : ℝ}
    (hf : ContDiff ℝ 2 iteration.objective) (hμ : 0 < μ)
    (hHessian : ∀ x v,
      μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient iteration.objective) x v) v)
    (hStep : ∀ k, 0 < iteration.stepLength k)
    (hWolfe : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ iteration.objective
      (iteration.point k) (iteration.point (k + 1) - iteration.point k))
    {xstar : EuclideanSpace ℝ (Fin 2)}
    (hmin : ∀ x, iteration.objective xstar ≤ iteration.objective x)
    (hnot : ¬ Tendsto iteration.point atTop (𝓝 xstar)) :
    let s := fun k ↦ iteration.point (k + 1) - iteration.point k
    let y := fun k ↦ gradient iteration.objective (iteration.point (k + 1)) -
      gradient iteration.objective (iteration.point k)
    let lam := fun k ↦ (inner ℝ (y k) (s k) / ‖s k‖ ^ 2) *
      (iteration.inverseHessian (k + 1)).det
    (∃ K > 0, ∀ᶠ k in atTop, 0 < lam k ∧ lam k ≤ K * ‖s k‖ * ‖s (k + 1)‖) ∧
      Tendsto lam atTop (𝓝 0) := by
  let s := fun k ↦ iteration.point (k + 1) - iteration.point k
  let y := fun k ↦ gradient iteration.objective (iteration.point (k + 1)) -
    gradient iteration.objective (iteration.point k)
  let ell := fun k ↦ ‖s k‖
  let u := fun k ↦ (ell k)⁻¹ • s k
  let v := fun k ↦ (ell k)⁻¹ • y k
  let R := fun k ↦ EuclideanPlane.frame (u k)
  let K := fun k ↦ (R k).transpose * iteration.inverseHessian (k + 1) * R k
  let g := fun k ↦ (R k).transpose *ᵥ
    WithLp.ofLp (gradient iteration.objective (iteration.point (k + 1)))
  let κ := fun k ↦ inner ℝ (u k) (v k)
  let β := fun k ↦ inner ℝ (EuclideanPlane.perp (u k)) (v k)
  let lam := fun k ↦ (inner ℝ (y k) (s k) / ‖s k‖ ^ 2) *
    (iteration.inverseHessian (k + 1)).det
  obtain ⟨M, hM, hsecBounds⟩ := secantBoundsAlongOrbit iteration hf hμ hHessian hStep hWolfe
  obtain ⟨G, hG, hdiffBounds⟩ := uniformDifferentialBoundsOnSublevel hf hμ hHessian
    (iteration.point 0)
  obtain ⟨N, hN, hgradLower⟩ :=
    gradientLowerBoundOfNonconvergence iteration hf hμ hHessian hStep hWolfe hmin hnot
  obtain ⟨A, hA, hlongBound⟩ := orbitLongitudinalGradientBound iteration hf hμ hHessian hStep hWolfe
  obtain ⟨C, hC, henergyBound⟩ := orbitEnergyDirectionBound iteration hf hμ hHessian hStep hWolfe
  have hmem := iteration.pointMemObjectiveSublevelOfWeakWolfe hStep hWolfe
  have hellPos (k : ℕ) : 0 < ell k := orbitStepNormPos iteration k (hStep k)
  have hellLimit : Tendsto ell atTop (𝓝 0) :=
    stepNormTendstoZero iteration hf hμ hHessian hStep hWolfe
  have hu (k : ℕ) : ‖u k‖ = 1 := by
    dsimp only [u]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
    exact inv_mul_cancel₀ (hellPos k).ne'
  have hR (k : ℕ) : R k ∈ Matrix.orthogonalGroup (Fin 2) ℝ := by
    have hspecial := (EuclideanPlane.frame_mem_specialOrthogonalGroup_iff (u k)).mpr (hu k)
    exact (Matrix.mem_specialOrthogonalGroup_iff.mp hspecial).1
  have hK (k : ℕ) : (K k).PosDef :=
    orthogonalCoordinatesPosDef (iteration.inverseHessianPosDef (k + 1)) (hR k)
  have hsec (k : ℕ) : K k *ᵥ ![κ k, β k] = ![1, 0] :=
    orbitPlanarSecantFrameSpecification iteration k (hStep k)
  have hκ (k : ℕ) : μ ≤ κ k :=
    normalizedOrbitCurvatureLowerBound iteration hf hμ hHessian k (hStep k)
  have hv (k : ℕ) : ‖v k‖ ≤ M := by
    dsimp only [v]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (hellPos k), ← div_eq_inv_mul]
    apply (div_le_iff₀ (hellPos k)).mpr
    exact (hsecBounds k).1
  have hβ (k : ℕ) : |β k| ≤ M := by
    have hpair := abs_real_inner_le_norm (EuclideanPlane.perp (u k)) (v k)
    rw [EuclideanPlane.perp.norm_map, hu k, one_mul] at hpair
    exact hpair.trans (hv k)
  have htilt (k : ℕ) : |β k / κ k| ≤ M / μ := secantTiltBound hμ (hκ k) (hβ k)
  have hgNorm (k : ℕ) : ‖(WithLp.toLp 2 (g k) : EuclideanSpace ℝ (Fin 2))‖ =
      ‖gradient iteration.objective (iteration.point (k + 1))‖ := by
    exact Matrix.norm_toLp_mulVec_eq_of_mem_orthogonalGroup (R k).transpose
      (orthogonalTranspose (hR k)) _
  have hgLower (k : ℕ) : N ≤ ‖(WithLp.toLp 2 (g k) : EuclideanSpace ℝ (Fin 2))‖ := by
    rw [hgNorm]
    exact hgradLower (k + 1)
  have hgUpper (k : ℕ) : ‖(WithLp.toLp 2 (g k) : EuclideanSpace ℝ (Fin 2))‖ ≤ G := by
    rw [hgNorm]
    have hlevel := (DFP.mem_objectiveSublevel_iff iteration _).mp (hmem (k + 1))
    exact (hdiffBounds _ hlevel).1
  have hgFirst (k : ℕ) : g k 0 =
      inner ℝ (u k) (gradient iteration.objective (iteration.point (k + 1))) := by
    have hcoordinates := congrFun (planarFrameCoordinates (u k)
      (gradient iteration.objective (iteration.point (k + 1)))) 0
    simpa only [Matrix.cons_val_zero] using hcoordinates
  have hlong (k : ℕ) : |g k 0| ≤ A * ell k := by
    rw [hgFirst]
    exact hlongBound k
  have henergy (k : ℕ) : g k ⬝ᵥ (K k *ᵥ g k) ≤ C * ell (k + 1) *
      ‖(WithLp.toLp 2 (K k *ᵥ g k) : EuclideanSpace ℝ (Fin 2))‖ := by
    dsimp only [g, K]
    rw [orthogonalCoordinatesEnergy _ _ (hR k), orthogonalCoordinatesActionNorm _ _ (hR k)]
    have hphysical := henergyBound (k + 1)
    dsimp only at hphysical
    rw [EuclideanSpace.inner_eq_star_dotProduct] at hphysical
    simp only [star_trivial] at hphysical
    rw [dotProduct_comm] at hphysical
    exact hphysical
  have hfree (k : ℕ) : K k 1 1 = lam k := by
    calc
      K k 1 1 = κ k * (K k).det :=
        transverseEntry_eq_curvature_mul_det (hK k).isHermitian (hμ.trans_le (hκ k)).ne' (hsec k)
      _ = κ k * (iteration.inverseHessian (k + 1)).det := by
        rw [orthogonalCoordinatesDet _ _ (hR k)]
      _ = lam k := by
        dsimp only [κ, u, v, ell, lam]
        rw [normalizedSecantCurvature]
  have hresult := secantSequenceDegeneration K g κ β ell hμ hA (div_nonneg hM.le hμ.le)
    hG hN hC hK hκ hsec (fun k ↦ (hellPos k).le) hellLimit htilt hgLower hgUpper hlong henergy
  simpa only [hfree, lam, ell, s, y] using hresult

/-- Helper for lem:planar-degeneration: the free secant coefficient
controls the Euclidean operator norm of the whole secant-coordinate matrix. -/
theorem secantOperatorNormBound
    {H : Matrix (Fin 2) (Fin 2) ℝ} {κ β μ B : ℝ}
    (hH : H.PosDef) (hμ : 0 < μ) (hκ : μ ≤ κ)
    (hsec : H *ᵥ ![κ, β] = ![1, 0]) (hB : 0 ≤ B) (htilt : |β / κ| ≤ B) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) H‖ ≤ (1 / μ + (1 + B) ^ 2) * (1 + H 1 1) := by
  have hfree : 0 < H 1 1 := hH.diag_pos
  have hconstant : 0 ≤ (1 / μ + (1 + B) ^ 2) * (1 + H 1 1) := by positivity
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hconstant
  intro x hx
  have hcoord : |x 0| ≤ 1 := by
    simpa only [Real.norm_eq_abs, hx] using PiLp.norm_apply_le x 0
  have hnorm : ‖(WithLp.toLp 2 (WithLp.ofLp x) : EuclideanSpace ℝ (Fin 2))‖ ≤ 1 := hx.le
  have hlong : |WithLp.ofLp x 0| ≤ (1 : ℝ) * 1 := by simpa using hcoord
  have hbound := secantActionUniformBound hH hμ hκ hsec (WithLp.ofLp x)
    zero_le_one hB zero_le_one zero_le_one htilt hnorm hlong
  have hrepr : Matrix.toEuclideanCLM (𝕜 := ℝ) H x =
      WithLp.toLp 2 (H *ᵥ WithLp.ofLp x) := by
    exact Matrix.toEuclideanCLM_toLp H (WithLp.ofLp x)
  simpa only [one_mul, ← hrepr] using hbound

/-- Helper for lem:planar-degeneration: an operator norm bound in an
orthonormal coordinate system is also a bound in physical coordinates. -/
theorem physicalOperatorNormBoundOfCoordinates
    (H R : Matrix (Fin 2) (Fin 2) ℝ) (hR : R ∈ Matrix.orthogonalGroup (Fin 2) ℝ)
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (R.transpose * H * R)‖ ≤ B) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) H‖ ≤ B := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hB
  intro x hx
  have hnorm : ‖(WithLp.toLp 2 (R.transpose *ᵥ WithLp.ofLp x) :
      EuclideanSpace ℝ (Fin 2))‖ = 1 := by
    rw [Matrix.norm_toLp_mulVec_eq_of_mem_orthogonalGroup R.transpose (orthogonalTranspose hR)]
    exact hx
  have haction := (Matrix.toEuclideanCLM (𝕜 := ℝ) (R.transpose * H * R)).le_of_opNorm_le
    hbound (WithLp.toLp 2 (R.transpose *ᵥ WithLp.ofLp x))
  rw [Matrix.toEuclideanCLM_toLp, orthogonalCoordinatesActionNorm H R hR,
    hnorm, mul_one] at haction
  exact haction

/-- Helper for lem:planar-degeneration: the physical inverse Hessian is
bounded in terms of its normalized secant curvature and determinant. -/
theorem planarPhysicalSecantOperatorBound
    (H : Matrix (Fin 2) (Fin 2) ℝ) (u v : EuclideanSpace ℝ (Fin 2))
    {μ M : ℝ} (hH : H.PosDef) (hu : ‖u‖ = 1)
    (hsec : H *ᵥ WithLp.ofLp v = WithLp.ofLp u)
    (hμ : 0 < μ) (hκ : μ ≤ inner ℝ u v) (hv : ‖v‖ ≤ M) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) H‖ ≤
      (1 / μ + (1 + M / μ) ^ 2) * (1 + inner ℝ u v * H.det) := by
  have hM : 0 ≤ M := (norm_nonneg v).trans hv
  have hspecial := (EuclideanPlane.frame_mem_specialOrthogonalGroup_iff u).mpr hu
  have hR := (Matrix.mem_specialOrthogonalGroup_iff.mp hspecial).1
  have hK := orthogonalCoordinatesPosDef hH hR
  have hsecK := planarSecantFrameSpecification H u v hu hsec
  have hβ : |inner ℝ (EuclideanPlane.perp u) v| ≤ M := by
    have hpair := abs_real_inner_le_norm (EuclideanPlane.perp u) v
    rw [EuclideanPlane.perp.norm_map, hu, one_mul] at hpair
    exact hpair.trans hv
  have htilt := secantTiltBound hμ hκ hβ
  have hbound := secantOperatorNormBound hK hμ hκ hsecK (div_nonneg hM hμ.le) htilt
  have hfree : ((EuclideanPlane.frame u).transpose * H * EuclideanPlane.frame u) 1 1 =
      inner ℝ u v * H.det := by
    rw [transverseEntry_eq_curvature_mul_det hK.isHermitian (hμ.trans_le hκ).ne' hsecK,
      orthogonalCoordinatesDet H (EuclideanPlane.frame u) hR]
  rw [hfree] at hbound
  have hlam : 0 < inner ℝ u v * H.det := by
    rw [← hfree]
    exact hK.diag_pos
  have hconstant : 0 ≤ (1 / μ + (1 + M / μ) ^ 2) * (1 + inner ℝ u v * H.det) := by
    positivity
  exact physicalOperatorNormBoundOfCoordinates H (EuclideanPlane.frame u) hR hconstant hbound

/-- Helper for lem:planar-degeneration: if a strongly convex planar DFP
orbit fails to converge, its inverse-Hessian operators remain uniformly bounded. -/
theorem orbitInverseHessianBoundedOfNonconvergence
    (iteration : DFP.InverseIteration (Fin 2)) {μ c₁ c₂ : ℝ}
    (hf : ContDiff ℝ 2 iteration.objective) (hμ : 0 < μ)
    (hHessian : ∀ x v,
      μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient iteration.objective) x v) v)
    (hStep : ∀ k, 0 < iteration.stepLength k)
    (hWolfe : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ iteration.objective
      (iteration.point k) (iteration.point (k + 1) - iteration.point k))
    {xstar : EuclideanSpace ℝ (Fin 2)}
    (hmin : ∀ x, iteration.objective xstar ≤ iteration.objective x)
    (hnot : ¬ Tendsto iteration.point atTop (𝓝 xstar)) :
    ∃ B > 0, ∀ k, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (iteration.inverseHessian k)‖ ≤ B := by
  let s := fun k ↦ iteration.point (k + 1) - iteration.point k
  let y := fun k ↦ gradient iteration.objective (iteration.point (k + 1)) -
    gradient iteration.objective (iteration.point k)
  let lam := fun k ↦ (inner ℝ (y k) (s k) / ‖s k‖ ^ 2) *
    (iteration.inverseHessian (k + 1)).det
  have hlim : Tendsto lam atTop (𝓝 0) :=
    (orbitFreeCoefficientDegeneration iteration hf hμ hHessian hStep hWolfe hmin hnot).2
  obtain ⟨L, hL⟩ := hlim.bddAbove_range
  obtain ⟨M, hM, hsecBounds⟩ := secantBoundsAlongOrbit iteration hf hμ hHessian hStep hWolfe
  let a := 1 / μ + (1 + M / μ) ^ 2
  have ha : 0 < a := by
    dsimp only [a]
    positivity
  have hsuccessor (k : ℕ) :
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (iteration.inverseHessian (k + 1))‖ ≤
        a * (1 + max 0 L) := by
    have hnorm : 0 < ‖s k‖ := orbitStepNormPos iteration k (hStep k)
    have hu : ‖‖s k‖⁻¹ • s k‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hnorm.ne']
    have hv : ‖‖s k‖⁻¹ • y k‖ ≤ M := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, ← div_eq_inv_mul]
      apply (div_le_iff₀ hnorm).mpr
      exact (hsecBounds k).1
    have hκ : μ ≤ inner ℝ (‖s k‖⁻¹ • s k) (‖s k‖⁻¹ • y k) :=
      normalizedOrbitCurvatureLowerBound iteration hf hμ hHessian k (hStep k)
    have hbound := planarPhysicalSecantOperatorBound (iteration.inverseHessian (k + 1))
      (‖s k‖⁻¹ • s k) (‖s k‖⁻¹ • y k) (iteration.inverseHessianPosDef (k + 1)) hu
      (normalizedOrbitSecantEquation iteration k) hμ hκ hv
    have hbound' :
        ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (iteration.inverseHessian (k + 1))‖ ≤
          a * (1 + lam k) := by
      simpa only [normalizedSecantCurvature] using hbound
    have hlam : lam k ≤ max 0 L := (hL (Set.mem_range_self k)).trans (le_max_right _ _)
    have hscaled := mul_le_mul_of_nonneg_left hlam ha.le
    nlinarith
  let B := max ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (iteration.inverseHessian 0)‖
    (a * (1 + max 0 L)) + 1
  have hB : 0 < B := by
    dsimp only [B]
    positivity
  refine ⟨B, hB, ?_⟩
  intro k
  cases k with
  | zero =>
    have hmax := le_max_left ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (iteration.inverseHessian 0)‖
      (a * (1 + max 0 L))
    dsimp only [B]
    linarith
  | succ k =>
    have hmax := le_max_right ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (iteration.inverseHessian 0)‖
      (a * (1 + max 0 L))
    have hbound := hsuccessor k
    dsimp only [B]
    exact hbound.trans (hmax.trans (le_add_of_nonneg_right zero_le_one))

/-- Helper for thm:planar-convergence: a Lipschitz derivative on a segment
gives a uniform quadratic first-order remainder. -/
theorem quadraticRemainderOfLipschitzDerivative
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {x y : E} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ z ∈ segment ℝ x y, DifferentiableAt ℝ f z)
    (hderiv : ∀ z ∈ segment ℝ x y,
      ‖fderiv ℝ f z - fderiv ℝ f x‖ ≤ L * ‖z - x‖) :
    ‖f y - f x - fderiv ℝ f x (y - x)‖ ≤ L * ‖y - x‖ ^ 2 := by
  have hbound : ∀ z ∈ segment ℝ x y,
      ‖fderiv ℝ f z - fderiv ℝ f x‖ ≤ L * ‖y - x‖ := by
    intro z hz
    exact (hderiv z hz).trans
      (mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hz) hL)
  have hmean := (convex_segment x y).norm_image_sub_le_of_norm_fderiv_le'
    hf hbound (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  simpa only [pow_two, mul_assoc] using hmean

/-- Helper for thm:planar-convergence: local Lipschitz Hessian regularity
on a compact initial sublevel yields one finite Lipschitz constant there. -/
theorem hessianLipschitzOnInitialSublevel
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [ProperSpace E]
    {f : E → ℝ} {μ : ℝ} (hf : ContDiff ℝ 2 f) (hμ : 0 < μ)
    (hHessian : ∀ z v : E,
      μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient f) z v) v) (x₀ : E)
    (hLip : LocallyLipschitzOn {x | f x ≤ f x₀} (fderiv ℝ (gradient f))) :
    ∃ L ≥ 0, ∀ x, f x ≤ f x₀ → ∀ y, f y ≤ f x₀ →
      ‖fderiv ℝ (gradient f) y - fderiv ℝ (gradient f) x‖ ≤ L * ‖y - x‖ := by
  obtain ⟨L, hL⟩ := hLip.exists_lipschitzOnWith_of_compact
    (compactInitialSublevel hf hμ hHessian x₀)
  refine ⟨(L : ℝ), L.coe_nonneg, ?_⟩
  intro x hx y hy
  simpa only [dist_eq_norm] using hL.dist_le_mul y hy x hx

/-- Helper for thm:planar-convergence: the actual gradient secants along
the DFP orbit have a uniform quadratic Hessian-linearization remainder. -/
theorem orbitGradientTaylorRemainder {n : ℕ}
    (iteration : DFP.InverseIteration (Fin n)) {μ c₁ c₂ : ℝ}
    (hf : ContDiff ℝ 2 iteration.objective) (hμ : 0 < μ)
    (hHessian : ∀ x v,
      μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient iteration.objective) x v) v)
    (hStep : ∀ k, 0 < iteration.stepLength k)
    (hWolfe : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ iteration.objective
      (iteration.point k) (iteration.point (k + 1) - iteration.point k))
    (hLip : LocallyLipschitzOn (DFP.objectiveSublevel iteration)
      (fderiv ℝ (gradient iteration.objective))) :
    ∃ L ≥ 0, ∀ k,
      ‖gradient iteration.objective (iteration.point (k + 1)) -
        gradient iteration.objective (iteration.point k) -
        fderiv ℝ (gradient iteration.objective) (iteration.point k)
          (iteration.point (k + 1) - iteration.point k)‖ ≤
        L * ‖iteration.point (k + 1) - iteration.point k‖ ^ 2 := by
  have hlevelEq : DFP.objectiveSublevel iteration =
      {x | iteration.objective x ≤ iteration.objective (iteration.point 0)} := by
    ext x
    exact DFP.mem_objectiveSublevel_iff iteration x
  rw [hlevelEq] at hLip
  obtain ⟨L, hL, hbound⟩ := hessianLipschitzOnInitialSublevel hf hμ hHessian
    (iteration.point 0) hLip
  have hconvex := convexInitialSublevel hf hμ hHessian (iteration.point 0)
  have hmem := iteration.pointMemObjectiveSublevelOfWeakWolfe hStep hWolfe
  rw [hlevelEq] at hmem
  have hfOrder : ContDiff ℝ ((1 : ℕ∞) + 1) iteration.objective := by
    convert hf using 1
    norm_num
  have hgradient : ContDiff ℝ 1 (gradient iteration.objective) :=
    hfOrder.gradient_succ (n := 1)
  refine ⟨L, hL, ?_⟩
  intro k
  apply quadraticRemainderOfLipschitzDerivative hL
  · intro z _
    exact hgradient.differentiable_one.differentiableAt
  · intro z hz
    have hzLevel := hconvex.segment_subset (hmem k) (hmem (k + 1)) hz
    exact hbound _ (hmem k) z hzLevel

/-- Helper for thm:planar-convergence: the reciprocal correction cancels
the linear term of the logarithm, leaving a uniform quadratic remainder. -/
theorem logReciprocalQuadraticRemainder {r : ℝ} (hr : |r| ≤ 1 / 2) :
    |Real.log (1 + r) + (1 + r)⁻¹ - 1| ≤ 4 * r ^ 2 := by
  have hden : 0 < 1 + r := by
    have hlow := (abs_le.mp hr).1
    linarith
  have hsplit : Real.log (1 + r) + (1 + r)⁻¹ - 1 =
      (Real.log (1 + r) - r) + r ^ 2 / (1 + r) := by
    field_simp
    ring
  have hrational : |r ^ 2 / (1 + r)| ≤ 2 * r ^ 2 := by
    rw [abs_div, abs_of_nonneg (sq_nonneg r), abs_of_pos hden]
    apply (div_le_iff₀ hden).mpr
    have hlow := (abs_le.mp hr).1
    nlinarith [mul_le_mul_of_nonneg_left hlow (sq_nonneg r)]
  rw [hsplit]
  have htriangle := abs_add_le (Real.log (1 + r) - r) (r ^ 2 / (1 + r))
  linarith [logOneAddQuadraticRemainder hr]

/-- Helper for thm:planar-convergence: normalized vector increments have
an exact finite-difference identity that isolates the tangent cancellation. -/
theorem normalizedIncrementPairingIdentity
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a t h : E) {N Nnext : ℝ} (hpair : inner ℝ a t = 2) :
    inner ℝ a ((N / Nnext) • t + Nnext⁻¹ • h - t) =
      inner ℝ a h / Nnext + 2 * (N / Nnext - 1) := by
  rw [inner_sub_right, inner_add_right, real_inner_smul_right,
    real_inner_smul_right, hpair]
  ring

/-- Helper for thm:planar-convergence: the exact normalized increment
and logarithmic amplitude increment cancel to quadratic order. -/
theorem normalizedIncrementLogBound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a t tNext h : E) {N Nnext : ℝ} (hN : 0 < N) (hNnext : 0 < Nnext)
    (hpair : inner ℝ a t = 2)
    (hnext : tNext = (N / Nnext) • t + Nnext⁻¹ • h)
    (hr : |(Nnext - N) / N| ≤ 1 / 2) :
    |inner ℝ a (tNext - t) + 2 * (Real.log Nnext - Real.log N)| ≤
      |inner ℝ a h| / Nnext + 8 * ((Nnext - N) / N) ^ 2 := by
  let r := (Nnext - N) / N
  have hratio : 1 + r = Nnext / N := by
    dsimp only [r]
    field_simp
    ring
  have hinverse : N / Nnext = (1 + r)⁻¹ := by rw [hratio, inv_div]
  have hlog : Real.log Nnext - Real.log N = Real.log (1 + r) := by
    rw [hratio, Real.log_div hNnext.ne' hN.ne']
  have hidentity : inner ℝ a (tNext - t) + 2 * (Real.log Nnext - Real.log N) =
      inner ℝ a h / Nnext + 2 * (Real.log (1 + r) + (1 + r)⁻¹ - 1) := by
    rw [hnext, normalizedIncrementPairingIdentity a t h hpair, hinverse, hlog]
    ring
  have hremainder := logReciprocalQuadraticRemainder hr
  rw [hidentity]
  have htriangle := abs_add_le (inner ℝ a h / Nnext)
    (2 * (Real.log (1 + r) + (1 + r)⁻¹ - 1))
  rw [abs_div, abs_of_pos hNnext, abs_mul] at htriangle
  norm_num only at htriangle
  dsimp only [r] at htriangle ⊢
  linarith

/-- Helper for thm:planar-convergence: right-angle rotation is
orthogonal to its argument. -/
theorem innerPerpSelf (x : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ x (EuclideanPlane.perp x) = 0 := by
  rw [EuclideanPlane.perp_apply]
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two]
  ring

/-- Helper for thm:planar-convergence: the coefficient field that
corrects the logarithmic determinant along the gradient's unit tangent. -/
noncomputable def tangentCoefficient
    (A : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2))
    (t : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  (2 / inner ℝ t (A t)) • A t

/-- Helper for thm:planar-convergence: the coefficient field pairs
with the unit tangent to give exactly two. -/
theorem tangentCoefficientPairing
    (A : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2))
    (t : EuclideanSpace ℝ (Fin 2)) (hcurv : inner ℝ t (A t) ≠ 0) :
    inner ℝ (tangentCoefficient A t) t = 2 := by
  rw [tangentCoefficient, real_inner_smul_left]
  have hpair : inner ℝ (A t) t = inner ℝ t (A t) := real_inner_comm _ _
  calc
    (2 / inner ℝ t (A t)) * inner ℝ (A t) t =
        (2 / inner ℝ t (A t)) * inner ℝ t (A t) :=
      congrArg (fun z : ℝ ↦ (2 / inner ℝ t (A t)) * z) hpair
    _ = 2 := div_mul_cancel₀ 2 hcurv

/-- Helper for thm:planar-convergence: the coefficient field annihilates
the rotated tangential Hessian image exactly. -/
theorem tangentCoefficientCancellation
    (A : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2))
    (t : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ (tangentCoefficient A t) (EuclideanPlane.perp (A t)) = 0 := by
  rw [tangentCoefficient, real_inner_smul_left, innerPerpSelf, mul_zero]

/-- Helper for thm:planar-convergence: the tangential secant term cancels
and only the Taylor remainder and departure from a tangent step remain. -/
theorem tangentCoefficientSecantBound
    (A : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2))
    (t s y : EuclideanSpace ℝ (Fin 2)) (d : ℝ) :
    |inner ℝ (tangentCoefficient A t) (EuclideanPlane.perp y)| ≤
      ‖tangentCoefficient A t‖ * (‖y - A s‖ + ‖A‖ * ‖s - d • t‖) := by
  have hsplit : EuclideanPlane.perp y = EuclideanPlane.perp (y - A s) +
      EuclideanPlane.perp (A (s - d • t)) + d • EuclideanPlane.perp (A t) := by
    simp only [map_sub, map_smul]
    module
  have hpair : inner ℝ (tangentCoefficient A t) (EuclideanPlane.perp y) =
      inner ℝ (tangentCoefficient A t)
        (EuclideanPlane.perp (y - A s) + EuclideanPlane.perp (A (s - d • t))) := by
    rw [hsplit, inner_add_right, real_inner_smul_right,
      tangentCoefficientCancellation, mul_zero, add_zero]
  rw [hpair]
  have hinner := abs_real_inner_le_norm (tangentCoefficient A t)
    (EuclideanPlane.perp (y - A s) + EuclideanPlane.perp (A (s - d • t)))
  have hsum := norm_add_le (EuclideanPlane.perp (y - A s))
    (EuclideanPlane.perp (A (s - d • t)))
  rw [EuclideanPlane.perp.norm_map, EuclideanPlane.perp.norm_map] at hsum
  have haction := A.le_opNorm (s - d • t)
  have hnorm : ‖EuclideanPlane.perp (y - A s) + EuclideanPlane.perp (A (s - d • t))‖ ≤
      ‖y - A s‖ + ‖A‖ * ‖s - d • t‖ := by linarith
  exact hinner.trans (mul_le_mul_of_nonneg_left hnorm (norm_nonneg _))

/-- Helper for thm:planar-convergence: any planar vector decomposes
exactly into its normal and positively oriented tangent components. -/
theorem planarNormalTangentDecomposition
    (ν s : EuclideanSpace ℝ (Fin 2)) (hν : ‖ν‖ = 1) :
    s = inner ℝ ν s • ν + inner ℝ (EuclideanPlane.perp ν) s • EuclideanPlane.perp ν := by
  have hunit := EuclideanSpace.real_norm_sq_eq ν
  rw [hν, one_pow, Fin.sum_univ_two] at hunit
  have hfirst := congrArg (fun r : ℝ ↦ r * s 0) hunit
  have hsecond := congrArg (fun r : ℝ ↦ r * s 1) hunit
  ext i
  fin_cases i
  · simp [PiLp.add_apply, PiLp.smul_apply, EuclideanSpace.inner_eq_star_dotProduct,
      EuclideanPlane.perp_apply, dotProduct, Fin.sum_univ_two]
    nlinarith
  · simp [PiLp.add_apply, PiLp.smul_apply, EuclideanSpace.inner_eq_star_dotProduct,
      EuclideanPlane.perp_apply, dotProduct, Fin.sum_univ_two]
    nlinarith

/-- Helper for thm:planar-convergence: the distance from a planar step
to its tangential projection is its normal component's absolute value. -/
theorem normNormalResidual
    (ν s : EuclideanSpace ℝ (Fin 2)) (hν : ‖ν‖ = 1) :
    ‖s - inner ℝ (EuclideanPlane.perp ν) s • EuclideanPlane.perp ν‖ = |inner ℝ ν s| := by
  have hdecomp := planarNormalTangentDecomposition ν s hν
  have hresidual : s - inner ℝ (EuclideanPlane.perp ν) s • EuclideanPlane.perp ν =
      inner ℝ ν s • ν := by
    exact sub_eq_iff_eq_add.mpr hdecomp
  rw [hresidual, norm_smul, Real.norm_eq_abs, hν, mul_one]

/-- Helper for thm:planar-convergence: rotating a normalized gradient
increment gives the exact normalization identity used by tangent cancellation. -/
theorem normalizedPerpIncrement
    (g gNext : EuclideanSpace ℝ (Fin 2)) (hg : g ≠ 0) :
    ‖gNext‖⁻¹ • EuclideanPlane.perp gNext =
      (‖g‖ / ‖gNext‖) • (‖g‖⁻¹ • EuclideanPlane.perp g) +
        ‖gNext‖⁻¹ • EuclideanPlane.perp (gNext - g) := by
  have hnorm : ‖g‖ ≠ 0 := norm_ne_zero_iff.mpr hg
  have hcancel : (‖g‖ / ‖gNext‖) * ‖g‖⁻¹ = ‖gNext‖⁻¹ := by
    field_simp
  rw [smul_smul, hcancel, map_sub, smul_sub]
  module

/-- Helper for thm:planar-convergence: for two nonzero gradients, the
rotated normalized-gradient increment and twice the log-norm increment
cancel up to the rotated secant pairing and a quadratic relative norm change. -/
theorem gradientTangentLogBound
    (g gNext : EuclideanSpace ℝ (Fin 2))
    (A : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2))
    (hg : g ≠ 0) (hgNext : gNext ≠ 0)
    (hcurv : inner ℝ (‖g‖⁻¹ • EuclideanPlane.perp g)
      (A (‖g‖⁻¹ • EuclideanPlane.perp g)) ≠ 0)
    (hrelative : |(‖gNext‖ - ‖g‖) / ‖g‖| ≤ 1 / 2) :
    let t := ‖g‖⁻¹ • EuclideanPlane.perp g
    let tNext := ‖gNext‖⁻¹ • EuclideanPlane.perp gNext
    |inner ℝ (tangentCoefficient A t) (tNext - t) +
      2 * (Real.log ‖gNext‖ - Real.log ‖g‖)| ≤
      |inner ℝ (tangentCoefficient A t) (EuclideanPlane.perp (gNext - g))| / ‖gNext‖ +
        8 * ((‖gNext‖ - ‖g‖) / ‖g‖) ^ 2 := by
  dsimp only
  exact normalizedIncrementLogBound _ _ _ _ (norm_pos_iff.mpr hg) (norm_pos_iff.mpr hgNext)
    (tangentCoefficientPairing A _ hcurv) (normalizedPerpIncrement g gNext hg) hrelative

/-- Helper for thm:planar-convergence: positive tangential curvature
and a bounded Hessian give a uniform norm bound on the correcting coefficient. -/
theorem tangentCoefficientNormBound
    (A : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2))
    (t : EuclideanSpace ℝ (Fin 2)) {μ M : ℝ}
    (ht : ‖t‖ = 1) (hμ : 0 < μ) (hcurv : μ ≤ inner ℝ t (A t))
    (hA : ‖A‖ ≤ M) : ‖tangentCoefficient A t‖ ≤ 2 * M / μ := by
  have hratio : |2 / inner ℝ t (A t)| ≤ 2 / μ := by
    have htwo : |(2 : ℝ)| ≤ 2 := by norm_num
    exact secantTiltBound hμ hcurv htwo
  have himage : ‖A t‖ ≤ M := by
    simpa only [ht, mul_one] using A.le_of_opNorm_le hA t
  rw [tangentCoefficient, norm_smul, Real.norm_eq_abs]
  have hpositive : 0 ≤ 2 / μ := by positivity
  have hproduct := mul_le_mul hratio himage (norm_nonneg (A t)) hpositive
  simpa only [div_mul_eq_mul_div] using hproduct

/-- Helper for thm:planar-convergence: the descent bound makes the
normal part of the step quadratic in its length when the gradient stays nonzero. -/
theorem stepNormalResidualBound
    (g s : EuclideanSpace ℝ (Fin 2)) {N C : ℝ}
    (hN : 0 < N) (hg : N ≤ ‖g‖) (hC : 0 ≤ C)
    (hdescent : inner ℝ g s ≤ 0) (hdecrease : -inner ℝ g s ≤ C * ‖s‖ ^ 2) :
    let t := ‖g‖⁻¹ • EuclideanPlane.perp g
    ‖s - inner ℝ t s • t‖ ≤ (C / N) * ‖s‖ ^ 2 := by
  dsimp only
  have hgpos := hN.trans_le hg
  have hunit : ‖‖g‖⁻¹ • g‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hgpos.ne']
  have hresidual := normNormalResidual (‖g‖⁻¹ • g) s hunit
  rw [map_smul] at hresidual
  rw [hresidual, real_inner_smul_left, abs_mul, abs_inv, abs_norm,
    abs_of_nonpos hdescent, ← div_eq_inv_mul]
  apply (div_le_iff₀ hgpos).mpr
  have hfactor : 0 ≤ (C / N) * ‖s‖ ^ 2 := by positivity
  calc
    -inner ℝ g s ≤ C * ‖s‖ ^ 2 := hdecrease
    _ = ((C / N) * ‖s‖ ^ 2) * N := by field_simp
    _ ≤ ((C / N) * ‖s‖ ^ 2) * ‖g‖ := mul_le_mul_of_nonneg_left hg hfactor

/-- Helper for thm:planar-convergence: a gradient secant bound and a
positive gradient lower bound control relative changes of gradient norm. -/
theorem relativeGradientNormBound
    {E : Type*} [NormedAddCommGroup E] (g gNext : E) {N M ell : ℝ}
    (hN : 0 < N) (hg : N ≤ ‖g‖) (hsec : ‖gNext - g‖ ≤ M * ell) :
    |(‖gNext‖ - ‖g‖) / ‖g‖| ≤ (M / N) * ell := by
  have hnorm := (abs_norm_sub_norm_le gNext g).trans hsec
  have hquotient := secantTiltBound hN hg hnorm
  simpa only [div_mul_eq_mul_div] using hquotient

/-- Helper for thm:planar-convergence: a quadratic gradient Taylor
remainder and quadratic normal step component give quadratic cancellation
between tangent transport and logarithmic gradient-norm change. -/
theorem gradientTangentLogQuadraticBound
    (g gNext s : EuclideanSpace ℝ (Fin 2))
    (A : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2))
    {μ N M C L : ℝ} (hμ : 0 < μ) (hN : 0 < N)
    (hg : N ≤ ‖g‖) (hgNext : N ≤ ‖gNext‖) (hC : 0 ≤ C)
    (hA : ‖A‖ ≤ M)
    (hcurv : μ ≤ inner ℝ (‖g‖⁻¹ • EuclideanPlane.perp g)
      (A (‖g‖⁻¹ • EuclideanPlane.perp g)))
    (hsec : ‖gNext - g‖ ≤ M * ‖s‖)
    (hTaylor : ‖gNext - g - A s‖ ≤ L * ‖s‖ ^ 2)
    (hdescent : inner ℝ g s ≤ 0) (hdecrease : -inner ℝ g s ≤ C * ‖s‖ ^ 2)
    (hsmall : (M / N) * ‖s‖ ≤ 1 / 2) :
    let t := ‖g‖⁻¹ • EuclideanPlane.perp g
    let tNext := ‖gNext‖⁻¹ • EuclideanPlane.perp gNext
    |inner ℝ (tangentCoefficient A t) (tNext - t) +
      2 * (Real.log ‖gNext‖ - Real.log ‖g‖)| ≤
        ((2 * M / μ) * (L + M * (C / N)) / N + 8 * (M / N) ^ 2) * ‖s‖ ^ 2 := by
  let t := ‖g‖⁻¹ • EuclideanPlane.perp g
  have hgpos := hN.trans_le hg
  have hgNextPos := hN.trans_le hgNext
  have hM : 0 ≤ M := (norm_nonneg A).trans hA
  have ht : ‖t‖ = 1 := by
    dsimp only [t]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, EuclideanPlane.perp.norm_map,
      inv_mul_cancel₀ hgpos.ne']
  have hcoef := tangentCoefficientNormBound A t ht hμ hcurv hA
  have hnormal := stepNormalResidualBound g s hN hg hC hdescent hdecrease
  have hraw := tangentCoefficientSecantBound A t s (gNext - g) (inner ℝ t s)
  have hcoefPos : 0 ≤ 2 * M / μ := by positivity
  have hnormalScaled := mul_le_mul hA hnormal (norm_nonneg _) hM
  have hins : ‖gNext - g - A s‖ + ‖A‖ * ‖s - inner ℝ t s • t‖ ≤
      (L + M * (C / N)) * ‖s‖ ^ 2 := by nlinarith
  have hinsPos : 0 ≤ ‖gNext - g - A s‖ + ‖A‖ * ‖s - inner ℝ t s • t‖ := by positivity
  have hnum : |inner ℝ (tangentCoefficient A t) (EuclideanPlane.perp (gNext - g))| ≤
      ((2 * M / μ) * (L + M * (C / N))) * ‖s‖ ^ 2 := by
    have hproduct := mul_le_mul hcoef hins hinsPos hcoefPos
    nlinarith
  have hnumDiv := secantTiltBound hN hgNext hnum
  rw [abs_div, abs_of_pos hgNextPos] at hnumDiv
  have hrelative := relativeGradientNormBound g gNext hN hg hsec
  have hrelativeSmall := hrelative.trans hsmall
  have hcurvNe : inner ℝ t (A t) ≠ 0 := (hμ.trans_le hcurv).ne'
  have hbound := gradientTangentLogBound g gNext A (norm_pos_iff.mp hgpos)
    (norm_pos_iff.mp hgNextPos) hcurvNe hrelativeSmall
  have hratioPos : 0 ≤ (M / N) * ‖s‖ := by positivity
  have hsquare : ((‖gNext‖ - ‖g‖) / ‖g‖) ^ 2 ≤ (M / N) ^ 2 * ‖s‖ ^ 2 := by
    have hproduct := mul_le_mul hrelative hrelative
      (abs_nonneg ((‖gNext‖ - ‖g‖) / ‖g‖)) hratioPos
    simpa only [← pow_two, sq_abs, mul_pow] using hproduct
  dsimp only at hbound ⊢
  dsimp only [t] at hnumDiv
  rw [← div_mul_eq_mul_div] at hnumDiv
  nlinarith

/-- Helper for thm:planar-convergence: the positive unit tangent to the
level curve is the right-angle rotation of the normalized gradient. -/
noncomputable def gradientUnitTangent
    (f : EuclideanSpace ℝ (Fin 2) → ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) := ‖gradient f x‖⁻¹ • EuclideanPlane.perp (gradient f x)

/-- Helper for thm:planar-convergence: the gradient transport coefficient
is evaluated at the physical Hessian and the unit level-set tangent. -/
noncomputable def gradientTransportCoefficient
    (f : EuclideanSpace ℝ (Fin 2) → ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) :=
  tangentCoefficient (fderiv ℝ (gradient f) x) (gradientUnitTangent f x)

/-- Helper for thm:planar-convergence: at a nonstationary point, the
gradient tangent has unit norm. -/
theorem gradientUnitTangentNorm
    (f : EuclideanSpace ℝ (Fin 2) → ℝ) (x : EuclideanSpace ℝ (Fin 2))
    (hg : gradient f x ≠ 0) : ‖gradientUnitTangent f x‖ = 1 := by
  rw [gradientUnitTangent, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
    EuclideanPlane.perp.norm_map, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hg)]

/-- Helper for thm:planar-convergence: local Lipschitz Hessian regularity
gives the quadratic tangent-log cancellation estimate along every sufficiently
late step of the actual nonconvergent DFP orbit. -/
theorem orbitTangentLogQuadraticBound
    (iteration : DFP.InverseIteration (Fin 2)) {μ c₁ c₂ : ℝ}
    (hf : ContDiff ℝ 2 iteration.objective) (hμ : 0 < μ)
    (hHessian : ∀ x v,
      μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient iteration.objective) x v) v)
    (hStep : ∀ k, 0 < iteration.stepLength k)
    (hWolfe : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ iteration.objective
      (iteration.point k) (iteration.point (k + 1) - iteration.point k))
    (hLip : LocallyLipschitzOn (DFP.objectiveSublevel iteration)
      (fderiv ℝ (gradient iteration.objective)))
    {xstar : EuclideanSpace ℝ (Fin 2)}
    (hmin : ∀ x, iteration.objective xstar ≤ iteration.objective x)
    (hnot : ¬ Tendsto iteration.point atTop (𝓝 xstar)) :
    ∃ Q ≥ 0, ∀ᶠ k in atTop,
      |inner ℝ (gradientTransportCoefficient iteration.objective (iteration.point k))
          (gradientUnitTangent iteration.objective (iteration.point (k + 1)) -
            gradientUnitTangent iteration.objective (iteration.point k)) +
        2 * (Real.log ‖gradient iteration.objective (iteration.point (k + 1))‖ -
          Real.log ‖gradient iteration.objective (iteration.point k)‖)| ≤
        Q * ‖iteration.point (k + 1) - iteration.point k‖ ^ 2 := by
  obtain ⟨N, hN, hgradient⟩ :=
    gradientLowerBoundOfNonconvergence iteration hf hμ hHessian hStep hWolfe hmin hnot
  obtain ⟨M₁, hM₁, hsecBounds⟩ := secantBoundsAlongOrbit iteration hf hμ hHessian hStep hWolfe
  obtain ⟨M₂, hM₂, hdiffBounds⟩ := uniformDifferentialBoundsOnSublevel hf hμ hHessian
    (iteration.point 0)
  obtain ⟨L, hL, hTaylor⟩ := orbitGradientTaylorRemainder iteration hf hμ hHessian hStep hWolfe hLip
  let M := M₁ + M₂
  let C := M₁ / (1 - c₂)
  have hM : 0 < M := add_pos hM₁ hM₂
  have hC : 0 < C := div_pos hM₁ (sub_pos.mpr (hWolfe 0).c₂_lt_one)
  have hM₁le : M₁ ≤ M := le_add_of_nonneg_right hM₂.le
  have hM₂le : M₂ ≤ M := le_add_of_nonneg_left hM₁.le
  let Q := (2 * M / μ) * (L + M * (C / N)) / N + 8 * (M / N) ^ 2
  have hQ : 0 ≤ Q := by
    dsimp only [Q]
    positivity
  refine ⟨Q, hQ, ?_⟩
  have hsmall : ∀ᶠ k in atTop,
      (M / N) * ‖iteration.point (k + 1) - iteration.point k‖ ≤ 1 / 2 := by
    have hlimit := (stepNormTendstoZero iteration hf hμ hHessian hStep hWolfe).const_mul (M / N)
    have hlimitZero : Tendsto
        (fun k ↦ (M / N) * ‖iteration.point (k + 1) - iteration.point k‖) atTop (𝓝 0) := by
      simpa using hlimit
    have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
    exact (hlimitZero.eventually (eventually_lt_nhds hhalf)).mono (fun _ hk ↦ hk.le)
  have hmem := iteration.pointMemObjectiveSublevelOfWeakWolfe hStep hWolfe
  filter_upwards [hsmall] with k hk
  have hg : gradient iteration.objective (iteration.point k) ≠ 0 :=
    norm_pos_iff.mp (hN.trans_le (hgradient k))
  have ht := gradientUnitTangentNorm iteration.objective (iteration.point k) hg
  have hcurv := hHessian (iteration.point k)
    (gradientUnitTangent iteration.objective (iteration.point k))
  rw [ht, one_pow, mul_one, real_inner_comm] at hcurv
  have hlevel := (DFP.mem_objectiveSublevel_iff iteration _).mp (hmem k)
  have hA := ((hdiffBounds _ hlevel).2).trans hM₂le
  have hsec := ((hsecBounds k).1).trans
    (mul_le_mul_of_nonneg_right hM₁le (norm_nonneg (iteration.point (k + 1) - iteration.point k)))
  have hdescent : inner ℝ (gradient iteration.objective (iteration.point k))
      (iteration.point (k + 1) - iteration.point k) ≤ 0 := by
    simpa only [DFP.gradients_apply] using
      (iteration.gradientInnerDisplacementNeg k (hStep k)).le
  exact gradientTangentLogQuadraticBound _ _ _ _ hμ hN (hgradient k) (hgradient (k + 1))
    hC.le hA hcurv hsec (hTaylor k) hdescent (hsecBounds k).2 hk

/-- Helper for thm:planar-convergence: orient a unit step toward the
chosen tangent, using the positive sign when the tangential pairing is zero. -/
noncomputable def tangentOrientation
    (t u : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  if inner ℝ t u < 0 then -1 else 1

/-- Helper for thm:planar-convergence: the tangent orientation is a sign. -/
theorem tangentOrientationSign (t u : EuclideanSpace ℝ (Fin 2)) :
    tangentOrientation t u = 1 ∨ tangentOrientation t u = -1 := by
  by_cases h : inner ℝ t u < 0
  · exact Or.inr (if_pos h)
  · exact Or.inl (if_neg h)

/-- Helper for thm:planar-convergence: tangent orientation preserves norms. -/
theorem tangentOrientationAbs (t u : EuclideanSpace ℝ (Fin 2)) :
    |tangentOrientation t u| = 1 := by
  rcases tangentOrientationSign t u with h | h
  · rw [h, abs_one]
  · rw [h, abs_neg, abs_one]

/-- Helper for thm:planar-convergence: orientation replaces the
tangential component by its absolute value. -/
theorem tangentOrientationPairing (t u : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ (tangentOrientation t u • u) t = |inner ℝ t u| := by
  have hscalar : tangentOrientation t u * inner ℝ t u = |inner ℝ t u| := by
    by_cases h : inner ℝ t u < 0
    · rw [tangentOrientation, if_pos h, neg_one_mul, abs_of_neg h]
    · rw [tangentOrientation, if_neg h, one_mul, abs_of_nonneg (le_of_not_gt h)]
  rw [real_inner_smul_left]
  have hcomm : inner ℝ u t = inner ℝ t u := real_inner_comm _ _
  exact (congrArg (fun r : ℝ ↦ tangentOrientation t u * r) hcomm).trans hscalar

/-- Helper for thm:planar-convergence: squared normal and tangent
components of a planar unit vector add to one. -/
theorem planarUnitComponentSquares
    (ν u : EuclideanSpace ℝ (Fin 2)) (hν : ‖ν‖ = 1) (hu : ‖u‖ = 1) :
    (inner ℝ ν u) ^ 2 + (inner ℝ (EuclideanPlane.perp ν) u) ^ 2 = 1 := by
  have hspecial := (EuclideanPlane.frame_mem_specialOrthogonalGroup_iff ν).mpr hν
  have hR := (Matrix.mem_specialOrthogonalGroup_iff.mp hspecial).1
  have hcoordinates : ‖(WithLp.toLp 2
      ![inner ℝ ν u, inner ℝ (EuclideanPlane.perp ν) u] : EuclideanSpace ℝ (Fin 2))‖ = 1 := by
    rw [← planarFrameCoordinates]
    have hnorm := Matrix.norm_toLp_mulVec_eq_of_mem_orthogonalGroup
      (EuclideanPlane.frame ν).transpose (orthogonalTranspose hR) (WithLp.ofLp u)
    exact hnorm.trans hu
  have hsquare := EuclideanSpace.real_norm_sq_eq
    (WithLp.toLp 2 ![inner ℝ ν u, inner ℝ (EuclideanPlane.perp ν) u])
  rw [hcoordinates, one_pow, Fin.sum_univ_two] at hsquare
  exact hsquare.symm

/-- Helper for thm:planar-convergence: after orienting a planar unit
vector toward the tangent, its distance to that tangent is controlled by
twice its normal component, including either original step direction. -/
theorem orientedUnitStepTangentBound
    (ν u : EuclideanSpace ℝ (Fin 2)) (hν : ‖ν‖ = 1) (hu : ‖u‖ = 1) :
    ‖tangentOrientation (EuclideanPlane.perp ν) u • u - EuclideanPlane.perp ν‖ ≤
      2 * |inner ℝ ν u| := by
  have hnorm : ‖tangentOrientation (EuclideanPlane.perp ν) u • u‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, tangentOrientationAbs, hu, mul_one]
  have ht : ‖EuclideanPlane.perp ν‖ = 1 := (EuclideanPlane.perp.norm_map ν).trans hν
  have hcomponents := planarUnitComponentSquares ν u hν hu
  have hdistance := norm_sub_sq_real
    (tangentOrientation (EuclideanPlane.perp ν) u • u) (EuclideanPlane.perp ν)
  rw [hnorm, ht, tangentOrientationPairing, one_pow] at hdistance
  have hnormalSq := sq_abs (inner ℝ ν u)
  have htangentSq := sq_abs (inner ℝ (EuclideanPlane.perp ν) u)
  have htangent : |inner ℝ (EuclideanPlane.perp ν) u| ≤ 1 := by
    nlinarith [sq_nonneg (inner ℝ ν u), abs_nonneg (inner ℝ (EuclideanPlane.perp ν) u)]
  have hproduct := mul_nonneg (abs_nonneg (inner ℝ (EuclideanPlane.perp ν) u))
    (sub_nonneg.mpr htangent)
  nlinarith [norm_nonneg (tangentOrientation (EuclideanPlane.perp ν) u • u -
    EuclideanPlane.perp ν), abs_nonneg (inner ℝ ν u)]

/-- Helper for thm:planar-convergence: the normalized physical step
has a small normal component under the quadratic descent bound. -/
theorem normalizedStepNormalBound
    (g s : EuclideanSpace ℝ (Fin 2)) {N C : ℝ}
    (hN : 0 < N) (hg : N ≤ ‖g‖) (hC : 0 ≤ C) (hs : s ≠ 0)
    (hdescent : inner ℝ g s ≤ 0) (hdecrease : -inner ℝ g s ≤ C * ‖s‖ ^ 2) :
    |inner ℝ (‖g‖⁻¹ • g) (‖s‖⁻¹ • s)| ≤ (C / N) * ‖s‖ := by
  have hgpos := hN.trans_le hg
  have hspos := norm_pos_iff.mpr hs
  have hunit : ‖‖g‖⁻¹ • g‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hgpos.ne']
  have hnormal := stepNormalResidualBound g s hN hg hC hdescent hdecrease
  dsimp only at hnormal
  have hresidual := normNormalResidual (‖g‖⁻¹ • g) s hunit
  rw [map_smul] at hresidual
  rw [hresidual] at hnormal
  rw [real_inner_smul_right, abs_mul, abs_inv, abs_norm, ← div_eq_inv_mul]
  apply (div_le_iff₀ hspos).mpr
  nlinarith

/-- Helper for thm:planar-convergence: orienting the physical step
toward the level-set tangent gives an error linear in its step length. -/
theorem orientedStepTangentBound
    (g s : EuclideanSpace ℝ (Fin 2)) {N C : ℝ}
    (hN : 0 < N) (hg : N ≤ ‖g‖) (hC : 0 ≤ C) (hs : s ≠ 0)
    (hdescent : inner ℝ g s ≤ 0) (hdecrease : -inner ℝ g s ≤ C * ‖s‖ ^ 2) :
    let t := ‖g‖⁻¹ • EuclideanPlane.perp g
    let u := ‖s‖⁻¹ • s
    ‖tangentOrientation t u • u - t‖ ≤ (2 * C / N) * ‖s‖ := by
  have hgpos := hN.trans_le hg
  have hunitG : ‖‖g‖⁻¹ • g‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hgpos.ne']
  have hunitS : ‖‖s‖⁻¹ • s‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hs)]
  have hbound := orientedUnitStepTangentBound (‖g‖⁻¹ • g) (‖s‖⁻¹ • s) hunitG hunitS
  rw [map_smul] at hbound
  have hnormal := normalizedStepNormalBound g s hN hg hC hs hdescent hdecrease
  dsimp only
  calc
    _ ≤ 2 * ((C / N) * ‖s‖) :=
      hbound.trans (mul_le_mul_of_nonneg_left hnormal zero_le_two)
    _ = (2 * C / N) * ‖s‖ := by ring

/-- Helper for thm:planar-convergence: a common orientation sign
preserves the normalized secant equation and does not enlarge the Taylor remainder. -/
theorem orientedSecantTaylorBound
    (A : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2))
    (s y t : EuclideanSpace ℝ (Fin 2)) {σ M L E : ℝ}
    (hs : s ≠ 0) (hσ : |σ| = 1) (hA : ‖A‖ ≤ M)
    (hTaylor : ‖y - A s‖ ≤ L * ‖s‖ ^ 2)
    (herror : ‖σ • (‖s‖⁻¹ • s) - t‖ ≤ E * ‖s‖) :
    ‖σ • (‖s‖⁻¹ • y) - A t‖ ≤ (L + M * E) * ‖s‖ := by
  have hspos := norm_pos_iff.mpr hs
  have hM : 0 ≤ M := (norm_nonneg A).trans hA
  have hsplit : σ • (‖s‖⁻¹ • y) - A t =
      σ • (‖s‖⁻¹ • (y - A s)) + A (σ • (‖s‖⁻¹ • s) - t) := by
    simp only [map_sub, map_smul, smul_sub]
    module
  have hfirst : ‖σ • (‖s‖⁻¹ • (y - A s))‖ ≤ L * ‖s‖ := by
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      hσ, one_mul, abs_inv, abs_norm, ← div_eq_inv_mul]
    apply (div_le_iff₀ hspos).mpr
    nlinarith
  have hsecond : ‖A (σ • (‖s‖⁻¹ • s) - t)‖ ≤ M * (E * ‖s‖) := by
    exact (A.le_opNorm _).trans (mul_le_mul hA herror (norm_nonneg _) hM)
  rw [hsplit]
  have htriangle := norm_add_le (σ • (‖s‖⁻¹ • (y - A s))) (A (σ • (‖s‖⁻¹ • s) - t))
  nlinarith

/-- Helper for thm:planar-convergence: the canonical signed normalized
step direction is oriented toward the current gradient tangent. -/
noncomputable def orientedOrbitStep (iteration : DFP.InverseIteration (Fin 2))
    (k : ℕ) : EuclideanSpace ℝ (Fin 2) :=
  let s := iteration.point (k + 1) - iteration.point k
  let u := ‖s‖⁻¹ • s
  tangentOrientation (gradientUnitTangent iteration.objective (iteration.point k)) u • u

/-- Helper for thm:planar-convergence: orient the normalized gradient
secant by the same sign used for the physical step direction. -/
noncomputable def orientedOrbitSecant (iteration : DFP.InverseIteration (Fin 2))
    (k : ℕ) : EuclideanSpace ℝ (Fin 2) :=
  let s := iteration.point (k + 1) - iteration.point k
  let u := ‖s‖⁻¹ • s
  let y := gradient iteration.objective (iteration.point (k + 1)) -
    gradient iteration.objective (iteration.point k)
  tangentOrientation (gradientUnitTangent iteration.objective (iteration.point k)) u • (‖s‖⁻¹ • y)

/-- Helper for thm:planar-convergence: the canonically oriented physical
step direction has unit norm. -/
theorem orientedOrbitStepNorm (iteration : DFP.InverseIteration (Fin 2)) (k : ℕ)
    (hStep : 0 < iteration.stepLength k) : ‖orientedOrbitStep iteration k‖ = 1 := by
  rw [orientedOrbitStep]
  rw [norm_smul, Real.norm_eq_abs, tangentOrientationAbs, one_mul,
    norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
    inv_mul_cancel₀ (orbitStepNormPos iteration k hStep).ne']

/-- Helper for thm:planar-convergence: orientation preserves the exact
secant equation for the actual inverse-Hessian sequence. -/
theorem orientedOrbitSecantEquation (iteration : DFP.InverseIteration (Fin 2)) (k : ℕ) :
    iteration.inverseHessian (k + 1) *ᵥ WithLp.ofLp (orientedOrbitSecant iteration k) =
      WithLp.ofLp (orientedOrbitStep iteration k) := by
  simp only [orientedOrbitStep, orientedOrbitSecant, WithLp.ofLp_smul, Matrix.mulVec_smul]
  have hsec := normalizedOrbitSecantEquation iteration k
  simp only [WithLp.ofLp_smul, Matrix.mulVec_smul] at hsec
  rw [hsec]

/-- Helper for thm:planar-convergence: a common sign preserves real
inner products, so orientation leaves normalized secant curvature unchanged. -/
theorem commonSignInner
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v : E) {σ : ℝ} (hσ : |σ| = 1) : inner ℝ (σ • u) (σ • v) = inner ℝ u v := by
  have hsquare : σ ^ 2 = 1 := by
    have h := sq_abs σ
    rw [hσ, one_pow] at h
    exact h.symm
  rw [real_inner_smul_left, real_inner_smul_right]
  calc
    σ * (σ * inner ℝ u v) = σ ^ 2 * inner ℝ u v := by ring
    _ = inner ℝ u v := by rw [hsquare, one_mul]

/-- Helper for thm:planar-convergence: oriented orbit curvature is
exactly the original normalized gradient secant curvature. -/
theorem orientedOrbitCurvature (iteration : DFP.InverseIteration (Fin 2)) (k : ℕ) :
    inner ℝ (orientedOrbitStep iteration k) (orientedOrbitSecant iteration k) =
      inner ℝ (gradient iteration.objective (iteration.point (k + 1)) -
        gradient iteration.objective (iteration.point k))
        (iteration.point (k + 1) - iteration.point k) /
      ‖iteration.point (k + 1) - iteration.point k‖ ^ 2 := by
  rw [orientedOrbitStep, orientedOrbitSecant]
  rw [commonSignInner _ _ (tangentOrientationAbs _ _), normalizedSecantCurvature]

/-- Helper for thm:planar-convergence: on the actual DFP orbit,
the canonically oriented step approximates the gradient tangent and the
oriented secant approximates its Hessian image, uniformly to first order in step length. -/
theorem orbitOrientedSecantApproximation
    (iteration : DFP.InverseIteration (Fin 2)) {μ c₁ c₂ : ℝ}
    (hf : ContDiff ℝ 2 iteration.objective) (hμ : 0 < μ)
    (hHessian : ∀ x v,
      μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient iteration.objective) x v) v)
    (hStep : ∀ k, 0 < iteration.stepLength k)
    (hWolfe : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ iteration.objective
      (iteration.point k) (iteration.point (k + 1) - iteration.point k))
    (hLip : LocallyLipschitzOn (DFP.objectiveSublevel iteration)
      (fderiv ℝ (gradient iteration.objective)))
    {xstar : EuclideanSpace ℝ (Fin 2)}
    (hmin : ∀ x, iteration.objective xstar ≤ iteration.objective x)
    (hnot : ¬ Tendsto iteration.point atTop (𝓝 xstar)) :
    ∃ E > 0, ∃ V ≥ 0, ∀ k,
      ‖orientedOrbitStep iteration k -
        gradientUnitTangent iteration.objective (iteration.point k)‖ ≤
          E * ‖iteration.point (k + 1) - iteration.point k‖ ∧
      ‖orientedOrbitSecant iteration k -
        fderiv ℝ (gradient iteration.objective) (iteration.point k)
          (gradientUnitTangent iteration.objective (iteration.point k))‖ ≤
          V * ‖iteration.point (k + 1) - iteration.point k‖ := by
  obtain ⟨N, hN, hgradient⟩ :=
    gradientLowerBoundOfNonconvergence iteration hf hμ hHessian hStep hWolfe hmin hnot
  obtain ⟨M₁, hM₁, hsecBounds⟩ := secantBoundsAlongOrbit iteration hf hμ hHessian hStep hWolfe
  obtain ⟨M₂, hM₂, hdiffBounds⟩ := uniformDifferentialBoundsOnSublevel hf hμ hHessian
    (iteration.point 0)
  obtain ⟨L, hL, hTaylor⟩ := orbitGradientTaylorRemainder iteration hf hμ hHessian hStep hWolfe hLip
  let C := M₁ / (1 - c₂)
  let E := 2 * C / N
  have hC : 0 < C := div_pos hM₁ (sub_pos.mpr (hWolfe 0).c₂_lt_one)
  have hE : 0 < E := by
    dsimp only [E]
    positivity
  have hV : 0 ≤ L + M₂ * E := by positivity
  refine ⟨E, hE, L + M₂ * E, hV, ?_⟩
  have hmem := iteration.pointMemObjectiveSublevelOfWeakWolfe hStep hWolfe
  intro k
  have hs : iteration.point (k + 1) - iteration.point k ≠ 0 :=
    norm_pos_iff.mp (orbitStepNormPos iteration k (hStep k))
  have hdescent : inner ℝ (gradient iteration.objective (iteration.point k))
      (iteration.point (k + 1) - iteration.point k) ≤ 0 := by
    simpa only [DFP.gradients_apply] using
      (iteration.gradientInnerDisplacementNeg k (hStep k)).le
  have herror : ‖orientedOrbitStep iteration k -
      gradientUnitTangent iteration.objective (iteration.point k)‖ ≤
        E * ‖iteration.point (k + 1) - iteration.point k‖ :=
    orientedStepTangentBound _ _ hN (hgradient k) hC.le hs hdescent (hsecBounds k).2
  refine ⟨herror, ?_⟩
  have hlevel := (DFP.mem_objectiveSublevel_iff iteration _).mp (hmem k)
  have hA := (hdiffBounds _ hlevel).2
  exact orientedSecantTaylorBound _ _ _ _ hs (tangentOrientationAbs _ _) hA (hTaylor k) herror

/-- Helper for thm:planar-convergence: normalization is Lipschitz
between vectors whose norms have a common positive lower bound. -/
theorem normalizationDifferenceBound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g gNext : E) {N : ℝ} (hN : 0 < N) (hg : N ≤ ‖g‖) (hgNext : N ≤ ‖gNext‖) :
    ‖‖gNext‖⁻¹ • gNext - ‖g‖⁻¹ • g‖ ≤ (2 / N) * ‖gNext - g‖ := by
  have hgpos := hN.trans_le hg
  have hnpos := hN.trans_le hgNext
  have hcoeff : ‖gNext‖ * ‖g‖⁻¹ = 1 + (‖gNext‖ - ‖g‖) / ‖g‖ := by
    field_simp
    ring
  have hsplit : ‖gNext‖ • (‖gNext‖⁻¹ • gNext - ‖g‖⁻¹ • g) =
      (gNext - g) - ((‖gNext‖ - ‖g‖) / ‖g‖) • g := by
    rw [smul_sub, smul_smul, smul_smul, mul_inv_cancel₀ hnpos.ne', one_smul,
      hcoeff, add_smul, one_smul]
    module
  have hcorrection : ‖((‖gNext‖ - ‖g‖) / ‖g‖) • g‖ = |‖gNext‖ - ‖g‖| := by
    rw [norm_smul, Real.norm_eq_abs, abs_div, abs_norm, div_mul_cancel₀ _ hgpos.ne']
  have htriangle := norm_sub_le (gNext - g) (((‖gNext‖ - ‖g‖) / ‖g‖) • g)
  rw [hcorrection, ← hsplit, norm_smul, Real.norm_eq_abs, abs_norm] at htriangle
  have hscale := mul_le_mul_of_nonneg_right hgNext
    (norm_nonneg (‖gNext‖⁻¹ • gNext - ‖g‖⁻¹ • g))
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hN).mpr
  nlinarith [abs_norm_sub_norm_le gNext g]

/-- Helper for thm:planar-convergence: right-angle rotation preserves
the Lipschitz estimate for the normalized gradient tangent. -/
theorem tangentDifferenceBound
    (g gNext : EuclideanSpace ℝ (Fin 2)) {N : ℝ}
    (hN : 0 < N) (hg : N ≤ ‖g‖) (hgNext : N ≤ ‖gNext‖) :
    ‖‖gNext‖⁻¹ • EuclideanPlane.perp gNext - ‖g‖⁻¹ • EuclideanPlane.perp g‖ ≤
      (2 / N) * ‖gNext - g‖ := by
  have hbound := normalizationDifferenceBound g gNext hN hg hgNext
  have hnorm := EuclideanPlane.perp.norm_map (‖gNext‖⁻¹ • gNext - ‖g‖⁻¹ • g)
  rw [map_sub, map_smul, map_smul] at hnorm
  exact hnorm.le.trans hbound

/-- Helper for thm:planar-convergence: the actual unit tangent changes
by at most a fixed multiple of the physical step length on a nonconvergent orbit. -/
theorem orbitTangentVariationBound
    (iteration : DFP.InverseIteration (Fin 2)) {μ c₁ c₂ : ℝ}
    (hf : ContDiff ℝ 2 iteration.objective) (hμ : 0 < μ)
    (hHessian : ∀ x v,
      μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient iteration.objective) x v) v)
    (hStep : ∀ k, 0 < iteration.stepLength k)
    (hWolfe : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ iteration.objective
      (iteration.point k) (iteration.point (k + 1) - iteration.point k))
    {xstar : EuclideanSpace ℝ (Fin 2)}
    (hmin : ∀ x, iteration.objective xstar ≤ iteration.objective x)
    (hnot : ¬ Tendsto iteration.point atTop (𝓝 xstar)) :
    ∃ T > 0, ∀ k,
      ‖gradientUnitTangent iteration.objective (iteration.point (k + 1)) -
        gradientUnitTangent iteration.objective (iteration.point k)‖ ≤
        T * ‖iteration.point (k + 1) - iteration.point k‖ := by
  obtain ⟨N, hN, hgradient⟩ :=
    gradientLowerBoundOfNonconvergence iteration hf hμ hHessian hStep hWolfe hmin hnot
  obtain ⟨M, hM, hsec⟩ := secantBoundsAlongOrbit iteration hf hμ hHessian hStep hWolfe
  have hT : 0 < (2 / N) * M := by positivity
  refine ⟨(2 / N) * M, hT, ?_⟩
  intro k
  have hbound := tangentDifferenceBound _ _ hN (hgradient k) (hgradient (k + 1))
  have hfactor : 0 ≤ 2 / N := by positivity
  have hscaled := mul_le_mul_of_nonneg_left (hsec k).1 hfactor
  exact hbound.trans (hscaled.trans_eq (mul_assoc _ _ _).symm)

/-- Helper for thm:planar-convergence: variations of a unit tangent
and a bounded linear operator control the variation of their product. -/
theorem operatorUnitVectorVariation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A B : E →L[ℝ] E) (t u : E) (hu : ‖u‖ = 1) :
    ‖B u - A t‖ ≤ ‖B - A‖ + ‖A‖ * ‖u - t‖ := by
  have hsplit : B u - A t = (B - A) u + A (u - t) := by
    rw [sub_apply, map_sub]
    module
  rw [hsplit]
  have htriangle := norm_add_le ((B - A) u) (A (u - t))
  have hfirst := (B - A).le_opNorm u
  rw [hu, mul_one] at hfirst
  have hsecond := A.le_opNorm (u - t)
  linarith

/-- Helper for thm:planar-convergence: pointwise first-order
approximation and controlled target variation give controlled approximant variation. -/
theorem variationBoundOfApproximation
    {E : Type*} [NormedAddCommGroup E] (p q : ℕ → E) (ell : ℕ → ℝ)
    {A T : ℝ} (hT : 0 ≤ T) (hell : ∀ k, 0 ≤ ell k)
    (herror : ∀ k, ‖p k - q k‖ ≤ A * ell k)
    (hvariation : ∀ k, ‖q (k + 1) - q k‖ ≤ T * ell k) :
    ∀ k, ‖p (k + 1) - p k‖ ≤ (A + T) * (ell k + ell (k + 1)) := by
  intro k
  have htriangle := dist_triangle (p (k + 1)) (q (k + 1)) (p k)
  have htriangle' := dist_triangle (q (k + 1)) (q k) (p k)
  simp only [dist_eq_norm] at htriangle htriangle'
  have hsym : ‖q k - p k‖ = ‖p k - q k‖ := norm_sub_rev _ _
  have hcross := mul_nonneg hT (hell (k + 1))
  nlinarith [herror k, herror (k + 1), hvariation k]

/-- Helper for thm:planar-convergence: local Lipschitz Hessian
regularity controls changes of its action on the actual unit tangent. -/
theorem orbitHessianTangentVariationBound
    (iteration : DFP.InverseIteration (Fin 2)) {μ c₁ c₂ : ℝ}
    (hf : ContDiff ℝ 2 iteration.objective) (hμ : 0 < μ)
    (hHessian : ∀ x v,
      μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient iteration.objective) x v) v)
    (hStep : ∀ k, 0 < iteration.stepLength k)
    (hWolfe : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ iteration.objective
      (iteration.point k) (iteration.point (k + 1) - iteration.point k))
    (hLip : LocallyLipschitzOn (DFP.objectiveSublevel iteration)
      (fderiv ℝ (gradient iteration.objective)))
    {xstar : EuclideanSpace ℝ (Fin 2)}
    (hmin : ∀ x, iteration.objective xstar ≤ iteration.objective x)
    (hnot : ¬ Tendsto iteration.point atTop (𝓝 xstar)) :
    ∃ S ≥ 0, ∀ k,
      ‖fderiv ℝ (gradient iteration.objective) (iteration.point (k + 1))
          (gradientUnitTangent iteration.objective (iteration.point (k + 1))) -
        fderiv ℝ (gradient iteration.objective) (iteration.point k)
          (gradientUnitTangent iteration.objective (iteration.point k))‖ ≤
        S * ‖iteration.point (k + 1) - iteration.point k‖ := by
  obtain ⟨T, hT, htangent⟩ :=
    orbitTangentVariationBound iteration hf hμ hHessian hStep hWolfe hmin hnot
  obtain ⟨M, hM, hdiffBounds⟩ := uniformDifferentialBoundsOnSublevel hf hμ hHessian
    (iteration.point 0)
  have hlevelEq : DFP.objectiveSublevel iteration =
      {x | iteration.objective x ≤ iteration.objective (iteration.point 0)} := by
    ext x
    exact DFP.mem_objectiveSublevel_iff iteration x
  rw [hlevelEq] at hLip
  obtain ⟨L, hL, hhessianLip⟩ := hessianLipschitzOnInitialSublevel hf hμ hHessian
    (iteration.point 0) hLip
  have hS : 0 ≤ L + M * T := by positivity
  refine ⟨L + M * T, hS, ?_⟩
  intro k
  have hmem := iteration.pointMemObjectiveSublevelOfWeakWolfe hStep hWolfe
  rw [hlevelEq] at hmem
  have hg : gradient iteration.objective (iteration.point (k + 1)) ≠ 0 := by
    simpa only [DFP.gradients_apply] using iteration.gradientNeZeroOfSecantDenominator (k + 1)
  have ht := gradientUnitTangentNorm iteration.objective (iteration.point (k + 1)) hg
  have hbound := operatorUnitVectorVariation
    (fderiv ℝ (gradient iteration.objective) (iteration.point k))
    (fderiv ℝ (gradient iteration.objective) (iteration.point (k + 1)))
    (gradientUnitTangent iteration.objective (iteration.point k))
    (gradientUnitTangent iteration.objective (iteration.point (k + 1))) ht
  have hHdiff := hhessianLip _ (hmem k) _ (hmem (k + 1))
  have hHnorm := (hdiffBounds _ (hmem k)).2
  have hproduct := mul_le_mul hHnorm (htangent k) (norm_nonneg _) hM.le
  nlinarith

/-- Helper for thm:planar-convergence: both oriented normalized
secant vectors vary at the sum of adjacent step scales along the actual orbit. -/
theorem orbitOrientedSecantVariationBound
    (iteration : DFP.InverseIteration (Fin 2)) {μ c₁ c₂ : ℝ}
    (hf : ContDiff ℝ 2 iteration.objective) (hμ : 0 < μ)
    (hHessian : ∀ x v,
      μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient iteration.objective) x v) v)
    (hStep : ∀ k, 0 < iteration.stepLength k)
    (hWolfe : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ iteration.objective
      (iteration.point k) (iteration.point (k + 1) - iteration.point k))
    (hLip : LocallyLipschitzOn (DFP.objectiveSublevel iteration)
      (fderiv ℝ (gradient iteration.objective)))
    {xstar : EuclideanSpace ℝ (Fin 2)}
    (hmin : ∀ x, iteration.objective xstar ≤ iteration.objective x)
    (hnot : ¬ Tendsto iteration.point atTop (𝓝 xstar)) :
    ∃ D > 0, ∀ k,
      ‖orientedOrbitStep iteration (k + 1) - orientedOrbitStep iteration k‖ +
        ‖orientedOrbitSecant iteration (k + 1) - orientedOrbitSecant iteration k‖ ≤
        D * (‖iteration.point (k + 1) - iteration.point k‖ +
          ‖iteration.point (k + 2) - iteration.point (k + 1)‖) := by
  obtain ⟨E, hE, V, hV, happrox⟩ :=
    orbitOrientedSecantApproximation iteration hf hμ hHessian hStep hWolfe hLip hmin hnot
  obtain ⟨T, hT, htangent⟩ :=
    orbitTangentVariationBound iteration hf hμ hHessian hStep hWolfe hmin hnot
  obtain ⟨S, hS, hHessianTangent⟩ :=
    orbitHessianTangentVariationBound iteration hf hμ hHessian hStep hWolfe hLip hmin hnot
  have hstep := variationBoundOfApproximation (orientedOrbitStep iteration)
    (fun k ↦ gradientUnitTangent iteration.objective (iteration.point k))
    (fun k ↦ ‖iteration.point (k + 1) - iteration.point k‖)
    hT.le (fun k ↦ norm_nonneg _) (fun k ↦ (happrox k).1) htangent
  have hsecant := variationBoundOfApproximation (orientedOrbitSecant iteration)
    (fun k ↦ fderiv ℝ (gradient iteration.objective) (iteration.point k)
      (gradientUnitTangent iteration.objective (iteration.point k)))
    (fun k ↦ ‖iteration.point (k + 1) - iteration.point k‖)
    hS (fun k ↦ norm_nonneg _) (fun k ↦ (happrox k).2) hHessianTangent
  have hD : 0 < E + T + V + S := by positivity
  refine ⟨E + T + V + S, hD, ?_⟩
  intro k
  have hu := hstep k
  have hv := hsecant k
  nlinarith

/-- Helper for thm:planar-convergence: global strong convexity makes
the physical secant pairing strictly positive at every positive DFP step. -/
theorem orbitSecantPairingPos {n : ℕ}
    (iteration : DFP.InverseIteration (Fin n)) {μ : ℝ}
    (hf : ContDiff ℝ 2 iteration.objective) (hμ : 0 < μ)
    (hHessian : ∀ x v,
      μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient iteration.objective) x v) v)
    (k : ℕ) (hStep : 0 < iteration.stepLength k) :
    0 < inner ℝ (gradient iteration.objective (iteration.point (k + 1)) -
      gradient iteration.objective (iteration.point k))
      (iteration.point (k + 1) - iteration.point k) := by
  have hlower := inner_gradient_sub_ge_of_hessian_lower_bound iteration.objective μ hf hμ
    hHessian (iteration.point k) (iteration.point (k + 1))
  have hpositive := mul_pos hμ (sq_pos_of_pos (orbitStepNormPos iteration k hStep))
  exact hpositive.trans_le hlower

/-- Helper for thm:planar-convergence: the original DFP iteration has
the exact determinant ratio expressed in physical gradient and point differences. -/
theorem orbitDeterminantRecurrence {n : ℕ}
    (iteration : DFP.InverseIteration (Fin n)) {μ : ℝ}
    (hf : ContDiff ℝ 2 iteration.objective) (hμ : 0 < μ)
    (hHessian : ∀ x v,
      μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient iteration.objective) x v) v)
    (k : ℕ) (hStep : 0 < iteration.stepLength k) :
    let s := iteration.point (k + 1) - iteration.point k
    let y := gradient iteration.objective (iteration.point (k + 1)) -
      gradient iteration.objective (iteration.point k)
    (iteration.inverseHessian (k + 1)).det = (iteration.inverseHessian k).det *
      (inner ℝ y s /
        inner ℝ y (Matrix.toEuclideanCLM (𝕜 := ℝ) (iteration.inverseHessian k) y)) := by
  have hstep : iteration.point (k + 1) - iteration.point k =
      DFP.steps iteration.stepLength (DFP.directions iteration.inverseHessian
        (DFP.gradients iteration.objective iteration.point)) k := by
    rw [iteration.pointSucc k]
    abel
  have hpair := orbitSecantPairingPos iteration hf hμ hHessian k hStep
  have hsy : 0 <
      WithLp.ofLp (DFP.steps iteration.stepLength (DFP.directions iteration.inverseHessian
        (DFP.gradients iteration.objective iteration.point)) k) ⬝ᵥ
      WithLp.ofLp (DFP.gradientChanges (DFP.gradients iteration.objective iteration.point) k) := by
    rw [← hstep, DFP.gradientChanges_apply, DFP.gradients_apply, DFP.gradients_apply]
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] using hpair
  dsimp only
  rw [iteration.inverseHessianSucc k,
    Matrix.det_inverseDFPUpdate (iteration.inverseHessianPosDef k) hsy]
  rw [Matrix.inner_toEuclideanCLM, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [star_trivial, DFP.gradientChanges_apply, DFP.gradients_apply, hstep]

/-- Helper for thm:planar-convergence: positive curvature lower bounds
control the difference of reciprocal curvatures. -/
theorem reciprocalCurvatureDifference {a b μ : ℝ}
    (hμ : 0 < μ) (ha : μ ≤ a) (hb : μ ≤ b) :
    |a⁻¹ - b⁻¹| ≤ |a - b| / μ ^ 2 := by
  have haPos := hμ.trans_le ha
  have hbPos := hμ.trans_le hb
  have hidentity : a⁻¹ - b⁻¹ = (b - a) / (a * b) := by
    field_simp
  have hproduct : μ ^ 2 ≤ a * b := by
    simpa only [pow_two] using mul_le_mul ha hb hμ.le haPos.le
  have hnumerator : |b - a| ≤ |a - b| := le_of_eq (abs_sub_comm _ _)
  rw [hidentity]
  exact secantTiltBound (sq_pos_of_pos hμ) hproduct hnumerator

/-- Helper for thm:planar-convergence: dividing nearby bounded vectors
by uniformly positive curvatures preserves a quantitative variation bound. -/
theorem scaledSecantQuotientDifference
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v w : E) {a b μ M : ℝ} (hμ : 0 < μ) (ha : μ ≤ a) (hb : μ ≤ b)
    (hw : ‖w‖ ≤ M) :
    ‖(2 / a) • v - (2 / b) • w‖ ≤
      (2 / μ) * ‖v - w‖ + (2 * M / μ ^ 2) * |a - b| := by
  have hM : 0 ≤ M := (norm_nonneg w).trans hw
  have hsplit : (2 / a) • v - (2 / b) • w =
      (2 / a) • (v - w) + (2 / a - 2 / b) • w := by
    rw [smul_sub, sub_smul]
    module
  have htwo : |(2 : ℝ)| ≤ 2 := by norm_num
  have hratio := secantTiltBound hμ ha htwo
  have hreciprocal := reciprocalCurvatureDifference hμ ha hb
  have hcoeff : |2 / a - 2 / b| ≤ (2 / μ ^ 2) * |a - b| := by
    have hidentity : 2 / a - 2 / b = 2 * (a⁻¹ - b⁻¹) := by ring
    have habs : |2 / a - 2 / b| = 2 * |a⁻¹ - b⁻¹| := by
      rw [hidentity, abs_mul]
      norm_num
    rw [habs]
    calc
      2 * |a⁻¹ - b⁻¹| ≤ 2 * (|a - b| / μ ^ 2) :=
        mul_le_mul_of_nonneg_left hreciprocal zero_le_two
      _ = (2 / μ ^ 2) * |a - b| := by ring
  have htriangle := norm_add_le ((2 / a) • (v - w)) ((2 / a - 2 / b) • w)
  simp only [norm_smul, Real.norm_eq_abs] at htriangle
  have hfirst := mul_le_mul_of_nonneg_right hratio (norm_nonneg (v - w))
  have hcoeffPos : 0 ≤ (2 / μ ^ 2) * |a - b| := by positivity
  have hsecond := mul_le_mul hcoeff hw (norm_nonneg w) hcoeffPos
  have hnormalize : (2 / μ ^ 2) * |a - b| * M = (2 * M / μ ^ 2) * |a - b| := by ring
  rw [hnormalize] at hsecond
  rw [hsplit]
  nlinarith

/-- Helper for thm:planar-convergence: curvature differences are
controlled by changes of the unit direction and its bounded secant image. -/
theorem secantCurvatureVariation
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v t w : E) {M : ℝ} (hu : ‖u‖ = 1) (hw : ‖w‖ ≤ M) :
    |inner ℝ u v - inner ℝ t w| ≤ ‖v - w‖ + M * ‖u - t‖ := by
  have hidentity : inner ℝ u v - inner ℝ t w =
      inner ℝ u (v - w) + inner ℝ (u - t) w := by
    rw [inner_sub_right, inner_sub_left]
    ring
  have htriangle := abs_add_le (inner ℝ u (v - w)) (inner ℝ (u - t) w)
  have hfirst := abs_real_inner_le_norm u (v - w)
  rw [hu, one_mul] at hfirst
  have hsecond := abs_real_inner_le_norm (u - t) w
  have hproduct := mul_le_mul_of_nonneg_left hw (norm_nonneg (u - t))
  rw [hidentity]
  nlinarith

/-- Helper for thm:planar-convergence: first-order direction and
secant-image errors give a first-order error in the correcting coefficient. -/
theorem secantCoefficientApproximationBound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v t w : E) {μ M U V ell : ℝ}
    (hμ : 0 < μ) (hu : ‖u‖ = 1) (hw : ‖w‖ ≤ M)
    (hcurv : μ ≤ inner ℝ u v) (href : μ ≤ inner ℝ t w)
    (huError : ‖u - t‖ ≤ U * ell) (hvError : ‖v - w‖ ≤ V * ell) :
    ‖(2 / inner ℝ u v) • v - (2 / inner ℝ t w) • w‖ ≤
      ((2 / μ) * V + (2 * M / μ ^ 2) * (V + M * U)) * ell := by
  have hM : 0 ≤ M := (norm_nonneg w).trans hw
  have hcurvature := secantCurvatureVariation u v t w hu hw
  have herrorProduct := mul_le_mul_of_nonneg_left huError hM
  have hcurvError : |inner ℝ u v - inner ℝ t w| ≤ (V + M * U) * ell := by
    nlinarith
  have hbound := scaledSecantQuotientDifference v w hμ hcurv href hw
  have hfactor₁ : 0 ≤ 2 / μ := by positivity
  have hfactor₂ : 0 ≤ 2 * M / μ ^ 2 := by positivity
  have hfirst := mul_le_mul_of_nonneg_left hvError hfactor₁
  have hsecond := mul_le_mul_of_nonneg_left hcurvError hfactor₂
  nlinarith

/-- Helper for thm:planar-convergence: the Hessian lower bound
specializes to positive curvature in the unit tangent direction. -/
theorem gradientTangentCurvatureLower
    (f : EuclideanSpace ℝ (Fin 2) → ℝ) (μ : ℝ)
    (hHessian : ∀ x v, μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient f) x v) v)
    (x : EuclideanSpace ℝ (Fin 2)) (hg : gradient f x ≠ 0) :
    μ ≤ inner ℝ (gradientUnitTangent f x) (fderiv ℝ (gradient f) x (gradientUnitTangent f x)) := by
  have hbound := hHessian x (gradientUnitTangent f x)
  rw [gradientUnitTangentNorm f x hg, one_pow, mul_one, real_inner_comm] at hbound
  exact hbound

/-- Helper for thm:planar-convergence: orienting the physical secant
preserves its positive curvature lower bound. -/
theorem orientedOrbitCurvatureLower
    (iteration : DFP.InverseIteration (Fin 2)) {μ : ℝ}
    (hf : ContDiff ℝ 2 iteration.objective) (hμ : 0 < μ)
    (hHessian : ∀ x v,
      μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient iteration.objective) x v) v)
    (k : ℕ) (hStep : 0 < iteration.stepLength k) :
    μ ≤ inner ℝ (orientedOrbitStep iteration k) (orientedOrbitSecant iteration k) := by
  rw [orientedOrbitCurvature]
  have hbound := normalizedOrbitCurvatureLowerBound iteration hf hμ hHessian k hStep
  simpa only [normalizedSecantCurvature] using hbound

/-- Helper for thm:planar-convergence: the oriented secant coefficient
approximates the Hessian tangent coefficient to first order along the actual orbit. -/
theorem orbitSecantCoefficientApproximation
    (iteration : DFP.InverseIteration (Fin 2)) {μ c₁ c₂ : ℝ}
    (hf : ContDiff ℝ 2 iteration.objective) (hμ : 0 < μ)
    (hHessian : ∀ x v,
      μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient iteration.objective) x v) v)
    (hStep : ∀ k, 0 < iteration.stepLength k)
    (hWolfe : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ iteration.objective
      (iteration.point k) (iteration.point (k + 1) - iteration.point k))
    (hLip : LocallyLipschitzOn (DFP.objectiveSublevel iteration)
      (fderiv ℝ (gradient iteration.objective)))
    {xstar : EuclideanSpace ℝ (Fin 2)}
    (hmin : ∀ x, iteration.objective xstar ≤ iteration.objective x)
    (hnot : ¬ Tendsto iteration.point atTop (𝓝 xstar)) :
    ∃ Q ≥ 0, ∀ k,
      ‖(2 / inner ℝ (orientedOrbitStep iteration k) (orientedOrbitSecant iteration k)) •
          orientedOrbitSecant iteration k -
        gradientTransportCoefficient iteration.objective (iteration.point k)‖ ≤
        Q * ‖iteration.point (k + 1) - iteration.point k‖ := by
  obtain ⟨E, hE, V, hV, happrox⟩ :=
    orbitOrientedSecantApproximation iteration hf hμ hHessian hStep hWolfe hLip hmin hnot
  obtain ⟨M, hM, hdiffBounds⟩ := uniformDifferentialBoundsOnSublevel hf hμ hHessian
    (iteration.point 0)
  have hQ : 0 ≤ (2 / μ) * V + (2 * M / μ ^ 2) * (V + M * E) := by positivity
  refine ⟨(2 / μ) * V + (2 * M / μ ^ 2) * (V + M * E), hQ, ?_⟩
  intro k
  have hg : gradient iteration.objective (iteration.point k) ≠ 0 := by
    simpa only [DFP.gradients_apply] using iteration.gradientNeZeroOfSecantDenominator k
  have ht := gradientUnitTangentNorm iteration.objective (iteration.point k) hg
  have hmem := iteration.pointMemObjectiveSublevelOfWeakWolfe hStep hWolfe k
  have hlevel := (DFP.mem_objectiveSublevel_iff iteration _).mp hmem
  have hA := (hdiffBounds _ hlevel).2
  have himage : ‖fderiv ℝ (gradient iteration.objective) (iteration.point k)
      (gradientUnitTangent iteration.objective (iteration.point k))‖ ≤ M := by
    simpa only [ht, mul_one] using
      (fderiv ℝ (gradient iteration.objective) (iteration.point k)).le_of_opNorm_le hA
        (gradientUnitTangent iteration.objective (iteration.point k))
  have hcurv := orientedOrbitCurvatureLower iteration hf hμ hHessian k (hStep k)
  have href := gradientTangentCurvatureLower iteration.objective μ hHessian (iteration.point k) hg
  exact secantCoefficientApproximationBound _ _ _ _ hμ
    (orientedOrbitStepNorm iteration k (hStep k)) himage hcurv href (happrox k).1 (happrox k).2

/-- Helper for thm:planar-convergence: the actual Hessian tangent
coefficient varies by at most a fixed multiple of physical step length. -/
theorem orbitTransportCoefficientVariation
    (iteration : DFP.InverseIteration (Fin 2)) {μ c₁ c₂ : ℝ}
    (hf : ContDiff ℝ 2 iteration.objective) (hμ : 0 < μ)
    (hHessian : ∀ x v,
      μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient iteration.objective) x v) v)
    (hStep : ∀ k, 0 < iteration.stepLength k)
    (hWolfe : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ iteration.objective
      (iteration.point k) (iteration.point (k + 1) - iteration.point k))
    (hLip : LocallyLipschitzOn (DFP.objectiveSublevel iteration)
      (fderiv ℝ (gradient iteration.objective)))
    {xstar : EuclideanSpace ℝ (Fin 2)}
    (hmin : ∀ x, iteration.objective xstar ≤ iteration.objective x)
    (hnot : ¬ Tendsto iteration.point atTop (𝓝 xstar)) :
    ∃ Q ≥ 0, ∀ k,
      ‖gradientTransportCoefficient iteration.objective (iteration.point (k + 1)) -
        gradientTransportCoefficient iteration.objective (iteration.point k)‖ ≤
        Q * ‖iteration.point (k + 1) - iteration.point k‖ := by
  obtain ⟨T, hT, htangent⟩ :=
    orbitTangentVariationBound iteration hf hμ hHessian hStep hWolfe hmin hnot
  obtain ⟨S, hS, hHessianTangent⟩ :=
    orbitHessianTangentVariationBound iteration hf hμ hHessian hStep hWolfe hLip hmin hnot
  obtain ⟨M, hM, hdiffBounds⟩ := uniformDifferentialBoundsOnSublevel hf hμ hHessian
    (iteration.point 0)
  have hQ : 0 ≤ (2 / μ) * S + (2 * M / μ ^ 2) * (S + M * T) := by positivity
  refine ⟨(2 / μ) * S + (2 * M / μ ^ 2) * (S + M * T), hQ, ?_⟩
  intro k
  have hg (j : ℕ) : gradient iteration.objective (iteration.point j) ≠ 0 := by
    simpa only [DFP.gradients_apply] using iteration.gradientNeZeroOfSecantDenominator j
  have ht := gradientUnitTangentNorm iteration.objective (iteration.point k) (hg k)
  have htNext := gradientUnitTangentNorm iteration.objective (iteration.point (k + 1)) (hg (k + 1))
  have hmem := iteration.pointMemObjectiveSublevelOfWeakWolfe hStep hWolfe k
  have hlevel := (DFP.mem_objectiveSublevel_iff iteration _).mp hmem
  have hA := (hdiffBounds _ hlevel).2
  have himage : ‖fderiv ℝ (gradient iteration.objective) (iteration.point k)
      (gradientUnitTangent iteration.objective (iteration.point k))‖ ≤ M := by
    simpa only [ht, mul_one] using
      (fderiv ℝ (gradient iteration.objective) (iteration.point k)).le_of_opNorm_le hA
        (gradientUnitTangent iteration.objective (iteration.point k))
  have hcurv := gradientTangentCurvatureLower iteration.objective μ hHessian
    (iteration.point (k + 1)) (hg (k + 1))
  have href := gradientTangentCurvatureLower iteration.objective μ hHessian
    (iteration.point k) (hg k)
  exact secantCoefficientApproximationBound _ _ _ _ hμ htNext himage hcurv href
    (htangent k) (hHessianTangent k)

/-- Helper for thm:planar-convergence: the correcting coefficient
field stays uniformly bounded along the actual DFP orbit. -/
theorem orbitTransportCoefficientBound
    (iteration : DFP.InverseIteration (Fin 2)) {μ c₁ c₂ : ℝ}
    (hf : ContDiff ℝ 2 iteration.objective) (hμ : 0 < μ)
    (hHessian : ∀ x v,
      μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient iteration.objective) x v) v)
    (hStep : ∀ k, 0 < iteration.stepLength k)
    (hWolfe : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ iteration.objective
      (iteration.point k) (iteration.point (k + 1) - iteration.point k)) :
    ∃ B > 0, ∀ k,
      ‖gradientTransportCoefficient iteration.objective (iteration.point k)‖ ≤ B := by
  obtain ⟨M, hM, hdiffBounds⟩ := uniformDifferentialBoundsOnSublevel hf hμ hHessian
    (iteration.point 0)
  have hB : 0 < 2 * M / μ := by positivity
  refine ⟨2 * M / μ, hB, ?_⟩
  intro k
  have hg : gradient iteration.objective (iteration.point k) ≠ 0 := by
    simpa only [DFP.gradients_apply] using iteration.gradientNeZeroOfSecantDenominator k
  have ht := gradientUnitTangentNorm iteration.objective (iteration.point k) hg
  have hcurv := gradientTangentCurvatureLower iteration.objective μ hHessian (iteration.point k) hg
  have hmem := iteration.pointMemObjectiveSublevelOfWeakWolfe hStep hWolfe k
  have hlevel := (DFP.mem_objectiveSublevel_iff iteration _).mp hmem
  exact tangentCoefficientNormBound _ _ ht hμ hcurv (hdiffBounds _ hlevel).2

/-- Helper for thm:planar-convergence: the relative curvature
increment of two successive oriented secant pairs. -/
noncomputable def relativeCurvatureIncrement
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v du dv : E) : ℝ :=
  (inner ℝ v du + inner ℝ u dv + inner ℝ du dv) / inner ℝ u v

/-- Helper for thm:planar-convergence: the relative quadratic-form
increment measured by the preceding inverse Hessian. -/
noncomputable def relativeQuadraticIncrement
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (H : E →L[ℝ] E) (u v dv : E) : ℝ :=
  (2 * inner ℝ u dv + inner ℝ dv (H dv)) / inner ℝ u v

/-- Helper for thm:planar-convergence: the relative curvature
increment recovers the next curvature exactly. -/
theorem relativeCurvatureIncrementSpec
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v du dv : E) (hκ : inner ℝ u v ≠ 0) :
    inner ℝ (u + du) (v + dv) =
      inner ℝ u v * (1 + relativeCurvatureIncrement u v du dv) := by
  have hcomm : inner ℝ du v = inner ℝ v du := real_inner_comm _ _
  rw [inner_add_left, inner_add_right, inner_add_right, hcomm, relativeCurvatureIncrement]
  field_simp
  ring

/-- Helper for thm:planar-convergence: symmetry and the old secant
equation identify the new quadratic form with its relative increment. -/
theorem relativeQuadraticIncrementSpec
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (H : E →L[ℝ] E) (u v dv : E) (hκ : inner ℝ u v ≠ 0)
    (hSymm : ∀ x y, inner ℝ x (H y) = inner ℝ (H x) y) (hsec : H v = u) :
    inner ℝ (v + dv) (H (v + dv)) =
      inner ℝ u v * (1 + relativeQuadraticIncrement H u v dv) := by
  have hcomm : inner ℝ v u = inner ℝ u v := real_inner_comm _ _
  have hcomm' : inner ℝ dv u = inner ℝ u dv := real_inner_comm _ _
  rw [map_add, inner_add_left, inner_add_right, inner_add_right,
    hsec, hcomm, hcomm', hSymm v dv, hsec, relativeQuadraticIncrement]
  field_simp
  ring

/-- Helper for thm:planar-convergence: the first-order change in the
secant vector cancels exactly from the normalized determinant increment. -/
theorem relativeIncrementCancellation
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (H : E →L[ℝ] E) (u v du dv : E) :
    2 * relativeCurvatureIncrement u v du dv - relativeQuadraticIncrement H u v dv =
      2 * inner ℝ v du / inner ℝ u v +
        (2 * inner ℝ du dv - inner ℝ dv (H dv)) / inner ℝ u v := by
  rw [relativeCurvatureIncrement, relativeQuadraticIncrement]
  ring

/-- Helper for thm:planar-convergence: the quadratic-form remainder
is bounded without any positive lower bound on the inverse Hessian. -/
theorem secantQuadraticRemainderBound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (H : E →L[ℝ] E) (du dv : E) {B : ℝ} (hH : ‖H‖ ≤ B) :
    |2 * inner ℝ du dv - inner ℝ dv (H dv)| ≤
      2 * ‖du‖ * ‖dv‖ + B * ‖dv‖ ^ 2 := by
  have htriangle := abs_sub (2 * inner ℝ du dv) (inner ℝ dv (H dv))
  have hnormTwo : |2 * inner ℝ du dv| = 2 * |inner ℝ du dv| := by
    norm_num [abs_mul]
  rw [hnormTwo] at htriangle
  have hcross := abs_real_inner_le_norm du dv
  have hquadratic := abs_real_inner_le_norm dv (H dv)
  have hoperator := H.le_of_opNorm_le hH dv
  have hscaled := mul_le_mul_of_nonneg_left hoperator (norm_nonneg dv)
  nlinarith only [htriangle, hcross, hquadratic, hscaled]

/-- Helper for thm:planar-convergence: the logarithmic determinant
increment differs from its tangent-linear part by quadratic secant errors. -/
theorem secantLogIncrementRemainderBound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (H : E →L[ℝ] E) (u v du dv : E) {μ B lam lamNext : ℝ}
    (hμ : 0 < μ) (hκ : μ ≤ inner ℝ u v) (hH : ‖H‖ ≤ B) (hlam : 0 < lam)
    (hP : |relativeCurvatureIncrement u v du dv| ≤ 1 / 2)
    (hQ : |relativeQuadraticIncrement H u v dv| ≤ 1 / 2)
    (hrec : lamNext = lam * (1 + relativeCurvatureIncrement u v du dv) ^ 2 /
      (1 + relativeQuadraticIncrement H u v dv)) :
    |Real.log lamNext - Real.log lam - 2 * inner ℝ v du / inner ℝ u v| ≤
      4 * relativeCurvatureIncrement u v du dv ^ 2 +
      2 * relativeQuadraticIncrement H u v dv ^ 2 +
      (2 * ‖du‖ * ‖dv‖ + B * ‖dv‖ ^ 2) / μ := by
  have hPpos : 0 < 1 + relativeCurvatureIncrement u v du dv := by
    have hlow := (abs_le.mp hP).1
    linarith
  have hQpos : 0 < 1 + relativeQuadraticIncrement H u v dv := by
    have hlow := (abs_le.mp hQ).1
    linarith
  have hlog := normalizedDeterminantLogIncrement hlam hPpos hQpos hrec
  have hlogError := logDeterminantQuadraticRemainder hP hQ
  have hquadratic := secantQuadraticRemainderBound H du dv hH
  have hquotient := secantTiltBound hμ hκ hquadratic
  have hsplit : Real.log lamNext - Real.log lam - 2 * inner ℝ v du / inner ℝ u v =
      (2 * Real.log (1 + relativeCurvatureIncrement u v du dv) -
        Real.log (1 + relativeQuadraticIncrement H u v dv) -
        (2 * relativeCurvatureIncrement u v du dv - relativeQuadraticIncrement H u v dv)) +
      (2 * inner ℝ du dv - inner ℝ dv (H dv)) / inner ℝ u v := by
    rw [hlog, relativeIncrementCancellation]
    ring
  rw [hsplit]
  exact (abs_add_le _ _).trans (add_le_add hlogError hquotient)

/-- Helper for thm:planar-convergence: a common nonzero normalization
and orientation scale cancels from the exact DFP determinant ratio. -/
theorem commonScaledSecantRatio
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (H : E →L[ℝ] E) (s y : E) {r : ℝ} (hr : r ≠ 0) :
    inner ℝ (r • s) (r • y) / inner ℝ (r • y) (H (r • y)) =
      inner ℝ y s / inner ℝ y (H y) := by
  simp only [map_smul, real_inner_smul_left, real_inner_smul_right]
  have hcomm : inner ℝ s y = inner ℝ y s := real_inner_comm _ _
  rw [hcomm]
  calc
    (r * (r * inner ℝ y s)) / (r * (r * inner ℝ y (H y))) =
        ((r * r) * inner ℝ y s) / ((r * r) * inner ℝ y (H y)) := by ring
    _ = inner ℝ y s / inner ℝ y (H y) := mul_div_mul_left _ _ (mul_ne_zero hr hr)

/-- Helper for thm:planar-convergence: the oriented normalized secant
ratio equals the physical DFP determinant ratio. -/
theorem orientedOrbitSecantRatio
    (iteration : DFP.InverseIteration (Fin 2)) (k : ℕ)
    (hStep : 0 < iteration.stepLength k) :
    inner ℝ (orientedOrbitStep iteration k) (orientedOrbitSecant iteration k) /
      inner ℝ (orientedOrbitSecant iteration k)
        (Matrix.toEuclideanCLM (𝕜 := ℝ) (iteration.inverseHessian k)
          (orientedOrbitSecant iteration k)) =
    let s := iteration.point (k + 1) - iteration.point k
    let y := gradient iteration.objective (iteration.point (k + 1)) -
      gradient iteration.objective (iteration.point k)
    inner ℝ y s / inner ℝ y (Matrix.toEuclideanCLM (𝕜 := ℝ) (iteration.inverseHessian k) y) := by
  simp only [orientedOrbitStep, orientedOrbitSecant, smul_smul]
  apply commonScaledSecantRatio
  apply mul_ne_zero
  · intro hzero
    have habs := tangentOrientationAbs
      (gradientUnitTangent iteration.objective (iteration.point k))
      (‖iteration.point (k + 1) - iteration.point k‖⁻¹ •
        (iteration.point (k + 1) - iteration.point k))
    rw [hzero, abs_zero] at habs
    exact zero_ne_one habs
  · exact inv_ne_zero (orbitStepNormPos iteration k hStep).ne'

/-- Helper for thm:planar-convergence: the actual DFP determinant
recurrence is unchanged by canonical secant orientation and normalization. -/
theorem orientedOrbitDeterminantRecurrence
    (iteration : DFP.InverseIteration (Fin 2)) {μ : ℝ}
    (hf : ContDiff ℝ 2 iteration.objective) (hμ : 0 < μ)
    (hHessian : ∀ x v,
      μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient iteration.objective) x v) v)
    (k : ℕ) (hStep : 0 < iteration.stepLength k) :
    (iteration.inverseHessian (k + 1)).det = (iteration.inverseHessian k).det *
      (inner ℝ (orientedOrbitStep iteration k) (orientedOrbitSecant iteration k) /
        inner ℝ (orientedOrbitSecant iteration k)
          (Matrix.toEuclideanCLM (𝕜 := ℝ) (iteration.inverseHessian k)
            (orientedOrbitSecant iteration k))) := by
  rw [orientedOrbitSecantRatio iteration k hStep]
  exact orbitDeterminantRecurrence iteration hf hμ hHessian k hStep

/-- Helper for thm:planar-convergence: the free coefficient of the
matrix after step `k`, equal to the paper's coefficient with index `k + 1`. -/
noncomputable def orbitFreeCoefficient
    (iteration : DFP.InverseIteration (Fin 2)) (k : ℕ) : ℝ :=
  inner ℝ (orientedOrbitStep iteration k) (orientedOrbitSecant iteration k) *
    (iteration.inverseHessian (k + 1)).det

/-- Helper for thm:planar-convergence: the oriented free coefficient
has the same physical secant formula used by the degeneration theorem. -/
theorem orbitFreeCoefficientPhysicalFormula
    (iteration : DFP.InverseIteration (Fin 2)) (k : ℕ) :
    orbitFreeCoefficient iteration k =
      (inner ℝ (gradient iteration.objective (iteration.point (k + 1)) -
        gradient iteration.objective (iteration.point k))
        (iteration.point (k + 1) - iteration.point k) /
        ‖iteration.point (k + 1) - iteration.point k‖ ^ 2) *
        (iteration.inverseHessian (k + 1)).det := by
  rw [orbitFreeCoefficient, orientedOrbitCurvature]

/-- Helper for thm:planar-convergence: every free coefficient of the
positive-step strongly convex DFP orbit is strictly positive. -/
theorem orbitFreeCoefficientPos
    (iteration : DFP.InverseIteration (Fin 2)) {μ : ℝ}
    (hf : ContDiff ℝ 2 iteration.objective) (hμ : 0 < μ)
    (hHessian : ∀ x v,
      μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient iteration.objective) x v) v)
    (k : ℕ) (hStep : 0 < iteration.stepLength k) :
    0 < orbitFreeCoefficient iteration k := by
  rw [orbitFreeCoefficient]
  exact mul_pos (hμ.trans_le (orientedOrbitCurvatureLower iteration hf hμ hHessian k hStep))
    (iteration.inverseHessianPosDef (k + 1)).det_pos

/-- Helper for thm:planar-convergence: the free coefficient in
oriented coordinates tends to zero under nonconvergence. -/
theorem orbitFreeCoefficientTendstoZero
    (iteration : DFP.InverseIteration (Fin 2)) {μ c₁ c₂ : ℝ}
    (hf : ContDiff ℝ 2 iteration.objective) (hμ : 0 < μ)
    (hHessian : ∀ x v,
      μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient iteration.objective) x v) v)
    (hStep : ∀ k, 0 < iteration.stepLength k)
    (hWolfe : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ iteration.objective
      (iteration.point k) (iteration.point (k + 1) - iteration.point k))
    {xstar : EuclideanSpace ℝ (Fin 2)}
    (hmin : ∀ x, iteration.objective xstar ≤ iteration.objective x)
    (hnot : ¬ Tendsto iteration.point atTop (𝓝 xstar)) :
    Tendsto (orbitFreeCoefficient iteration) atTop (𝓝 0) := by
  have hlimit :=
    (orbitFreeCoefficientDegeneration iteration hf hμ hHessian hStep hWolfe hmin hnot).2
  exact (tendsto_congr (fun k ↦ orbitFreeCoefficientPhysicalFormula iteration k)).mpr hlimit

/-- Helper for thm:planar-convergence: the oriented matrix secant
equation also holds in the canonical Euclidean operator representation. -/
theorem orientedOrbitOperatorSecantEquation
    (iteration : DFP.InverseIteration (Fin 2)) (k : ℕ) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (iteration.inverseHessian (k + 1))
      (orientedOrbitSecant iteration k) = orientedOrbitStep iteration k := by
  apply WithLp.ofLp_injective 2
  rw [Matrix.ofLp_toEuclideanCLM]
  exact orientedOrbitSecantEquation iteration k

/-- Helper for thm:planar-convergence: positive-definite matrices
act as symmetric operators on Euclidean space. -/
theorem positiveMatrixOperatorSymmetry
    {H : Matrix (Fin 2) (Fin 2) ℝ} (hH : H.PosDef)
    (x y : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ x (Matrix.toEuclideanCLM (𝕜 := ℝ) H y) =
      inner ℝ (Matrix.toEuclideanCLM (𝕜 := ℝ) H x) y := by
  have hself : IsSelfAdjoint (Matrix.toEuclideanCLM (𝕜 := ℝ) H) :=
    hH.isHermitian.isSelfAdjoint.map Matrix.toEuclideanCLM
  exact (hself.isSymmetric x y).symm

/-- Helper for thm:planar-convergence: the relative curvature
increment is controlled by the total secant variation when the secant change is small. -/
theorem relativeCurvatureIncrementBound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v du dv : E) {μ M : ℝ} (hμ : 0 < μ) (hκ : μ ≤ inner ℝ u v)
    (hu : ‖u‖ = 1) (hv : ‖v‖ ≤ M) (hdv : ‖dv‖ ≤ 1) :
    |relativeCurvatureIncrement u v du dv| ≤ ((M + 2) / μ) * (‖du‖ + ‖dv‖) := by
  have hM : 0 ≤ M := (norm_nonneg v).trans hv
  have htriangle := abs_add_le (inner ℝ v du + inner ℝ u dv) (inner ℝ du dv)
  have htriangle' := abs_add_le (inner ℝ v du) (inner ℝ u dv)
  have hfirst := abs_real_inner_le_norm v du
  have hfirst' := mul_le_mul_of_nonneg_right hv (norm_nonneg du)
  have hsecond := abs_real_inner_le_norm u dv
  rw [hu, one_mul] at hsecond
  have hcross := abs_real_inner_le_norm du dv
  have hsmall := mul_le_mul_of_nonneg_left hdv (norm_nonneg du)
  have hMdv := mul_nonneg hM (norm_nonneg dv)
  have hnum : |inner ℝ v du + inner ℝ u dv + inner ℝ du dv| ≤
      (M + 2) * (‖du‖ + ‖dv‖) := by
    nlinarith only [htriangle, htriangle', hfirst, hfirst', hsecond, hcross, hsmall,
      hMdv, norm_nonneg du, norm_nonneg dv]
  have hquotient := secantTiltBound hμ hκ hnum
  simpa only [relativeCurvatureIncrement, div_mul_eq_mul_div] using hquotient

/-- Helper for thm:planar-convergence: the relative quadratic-form
increment is uniformly controlled by the secant change and the operator norm. -/
theorem relativeQuadraticIncrementBound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (H : E →L[ℝ] E) (u v dv : E) {μ B : ℝ}
    (hμ : 0 < μ) (hκ : μ ≤ inner ℝ u v) (hH : ‖H‖ ≤ B)
    (hu : ‖u‖ = 1) (hdv : ‖dv‖ ≤ 1) :
    |relativeQuadraticIncrement H u v dv| ≤ ((2 + B) / μ) * ‖dv‖ := by
  have hB : 0 ≤ B := (norm_nonneg H).trans hH
  have htriangle := abs_add_le (2 * inner ℝ u dv) (inner ℝ dv (H dv))
  have htwo : |2 * inner ℝ u dv| = 2 * |inner ℝ u dv| := by norm_num [abs_mul]
  rw [htwo] at htriangle
  have hfirst := abs_real_inner_le_norm u dv
  rw [hu, one_mul] at hfirst
  have hsecond := abs_real_inner_le_norm dv (H dv)
  have hoperator := H.le_of_opNorm_le hH dv
  have hscaled := mul_le_mul_of_nonneg_left hoperator (norm_nonneg dv)
  have hdvSquare : ‖dv‖ ^ 2 ≤ ‖dv‖ := by nlinarith [norm_nonneg dv]
  have hsmall := mul_le_mul_of_nonneg_left hdvSquare hB
  have hnum : |2 * inner ℝ u dv + inner ℝ dv (H dv)| ≤ (2 + B) * ‖dv‖ := by
    nlinarith only [htriangle, hfirst, hsecond, hscaled, hsmall]
  have hquotient := secantTiltBound hμ hκ hnum
  simpa only [relativeQuadraticIncrement, div_mul_eq_mul_div] using hquotient

/-- Helper for thm:planar-convergence: the bounded gradient secants
give a uniform bound for the actual oriented normalized secant vectors. -/
theorem orientedOrbitSecantBound
    (iteration : DFP.InverseIteration (Fin 2)) {μ c₁ c₂ : ℝ}
    (hf : ContDiff ℝ 2 iteration.objective) (hμ : 0 < μ)
    (hHessian : ∀ x v,
      μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient iteration.objective) x v) v)
    (hStep : ∀ k, 0 < iteration.stepLength k)
    (hWolfe : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ iteration.objective
      (iteration.point k) (iteration.point (k + 1) - iteration.point k)) :
    ∃ M > 0, ∀ k, ‖orientedOrbitSecant iteration k‖ ≤ M := by
  obtain ⟨M, hM, hbounds⟩ := secantBoundsAlongOrbit iteration hf hμ hHessian hStep hWolfe
  refine ⟨M, hM, ?_⟩
  intro k
  rw [orientedOrbitSecant, norm_smul, Real.norm_eq_abs, tangentOrientationAbs, one_mul,
    norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, ← div_eq_inv_mul]
  apply (div_le_iff₀ (orbitStepNormPos iteration k (hStep k))).mpr
  exact (hbounds k).1

/-- Helper for thm:planar-convergence: the relative curvature
increment between successive canonically oriented orbit secants. -/
noncomputable def orbitRelativeCurvature (iteration : DFP.InverseIteration (Fin 2)) (k : ℕ) : ℝ :=
  relativeCurvatureIncrement (orientedOrbitStep iteration k) (orientedOrbitSecant iteration k)
    (orientedOrbitStep iteration (k + 1) - orientedOrbitStep iteration k)
    (orientedOrbitSecant iteration (k + 1) - orientedOrbitSecant iteration k)

/-- Helper for thm:planar-convergence: the relative quadratic-form
increment measured by the actual inverse Hessian following the old secant. -/
noncomputable def orbitRelativeQuadratic (iteration : DFP.InverseIteration (Fin 2)) (k : ℕ) : ℝ :=
  relativeQuadraticIncrement (Matrix.toEuclideanCLM (𝕜 := ℝ) (iteration.inverseHessian (k + 1)))
    (orientedOrbitStep iteration k) (orientedOrbitSecant iteration k)
    (orientedOrbitSecant iteration (k + 1) - orientedOrbitSecant iteration k)

/-- Helper for thm:planar-convergence: the actual free coefficient
satisfies the normalized determinant recurrence on the logarithm's local domain. -/
theorem orbitFreeCoefficientNormalizedRecurrence
    (iteration : DFP.InverseIteration (Fin 2)) {μ : ℝ}
    (hf : ContDiff ℝ 2 iteration.objective) (hμ : 0 < μ)
    (hHessian : ∀ x v,
      μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient iteration.objective) x v) v)
    (hStep : ∀ k, 0 < iteration.stepLength k)
    (k : ℕ) (hQ : |orbitRelativeQuadratic iteration k| ≤ 1 / 2) :
    orbitFreeCoefficient iteration (k + 1) =
      orbitFreeCoefficient iteration k * (1 + orbitRelativeCurvature iteration k) ^ 2 /
        (1 + orbitRelativeQuadratic iteration k) := by
  have hκ : inner ℝ (orientedOrbitStep iteration k) (orientedOrbitSecant iteration k) ≠ 0 :=
    (hμ.trans_le (orientedOrbitCurvatureLower iteration hf hμ hHessian k (hStep k))).ne'
  have hcurvature := relativeCurvatureIncrementSpec
    (orientedOrbitStep iteration k) (orientedOrbitSecant iteration k)
    (orientedOrbitStep iteration (k + 1) - orientedOrbitStep iteration k)
    (orientedOrbitSecant iteration (k + 1) - orientedOrbitSecant iteration k) hκ
  simp only [add_sub_cancel] at hcurvature
  have hquadratic := relativeQuadraticIncrementSpec
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (iteration.inverseHessian (k + 1)))
    (orientedOrbitStep iteration k) (orientedOrbitSecant iteration k)
    (orientedOrbitSecant iteration (k + 1) - orientedOrbitSecant iteration k) hκ
    (positiveMatrixOperatorSymmetry (iteration.inverseHessianPosDef (k + 1)))
    (orientedOrbitOperatorSecantEquation iteration k)
  simp only [add_sub_cancel] at hquadratic
  have hQpos : 0 < 1 + orbitRelativeQuadratic iteration k := by
    have hlow := (abs_le.mp hQ).1
    linarith
  rw [orbitFreeCoefficient, orbitFreeCoefficient,
    orientedOrbitDeterminantRecurrence iteration hf hμ hHessian (k + 1) (hStep (k + 1)),
    hcurvature, hquadratic]
  dsimp only [orbitRelativeCurvature, orbitRelativeQuadratic] at hQpos ⊢
  field_simp

/-- Helper for thm:planar-convergence: uniform secant and operator
bounds make the logarithmic determinant error quadratic in total secant variation. -/
theorem secantLogIncrementUniformBound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (H : E →L[ℝ] E) (u v du dv : E) {μ M B lam lamNext : ℝ}
    (hμ : 0 < μ) (hκ : μ ≤ inner ℝ u v) (hH : ‖H‖ ≤ B)
    (hu : ‖u‖ = 1) (hv : ‖v‖ ≤ M) (hdv : ‖dv‖ ≤ 1) (hlam : 0 < lam)
    (hP : |relativeCurvatureIncrement u v du dv| ≤ 1 / 2)
    (hQ : |relativeQuadraticIncrement H u v dv| ≤ 1 / 2)
    (hrec : lamNext = lam * (1 + relativeCurvatureIncrement u v du dv) ^ 2 /
      (1 + relativeQuadraticIncrement H u v dv)) :
    |Real.log lamNext - Real.log lam - 2 * inner ℝ v du / inner ℝ u v| ≤
      (4 * ((M + 2) / μ) ^ 2 + 2 * ((2 + B) / μ) ^ 2 + (2 + B) / μ) *
        (‖du‖ + ‖dv‖) ^ 2 := by
  have hM : 0 ≤ M := (norm_nonneg v).trans hv
  have hB : 0 ≤ B := (norm_nonneg H).trans hH
  have hAP : 0 ≤ (M + 2) / μ := by positivity
  have hAQ : 0 ≤ (2 + B) / μ := by positivity
  have hδ : 0 ≤ ‖du‖ + ‖dv‖ := add_nonneg (norm_nonneg du) (norm_nonneg dv)
  have hPbound := relativeCurvatureIncrementBound u v du dv hμ hκ hu hv hdv
  have hQbound : |relativeQuadraticIncrement H u v dv| ≤
      ((2 + B) / μ) * (‖du‖ + ‖dv‖) := by
    have hbound := relativeQuadraticIncrementBound H u v dv hμ hκ hH hu hdv
    have hcross := mul_nonneg hAQ (norm_nonneg du)
    nlinarith only [hbound, hcross]
  have hPsquare : relativeCurvatureIncrement u v du dv ^ 2 ≤
      ((M + 2) / μ) ^ 2 * (‖du‖ + ‖dv‖) ^ 2 := by
    have hproduct := mul_le_mul hPbound hPbound (abs_nonneg _) (mul_nonneg hAP hδ)
    simpa only [← pow_two, sq_abs, mul_pow] using hproduct
  have hQsquare : relativeQuadraticIncrement H u v dv ^ 2 ≤
      ((2 + B) / μ) ^ 2 * (‖du‖ + ‖dv‖) ^ 2 := by
    have hproduct := mul_le_mul hQbound hQbound (abs_nonneg _) (mul_nonneg hAQ hδ)
    simpa only [← pow_two, sq_abs, mul_pow] using hproduct
  have hcross : ‖du‖ * ‖dv‖ ≤ (‖du‖ + ‖dv‖) ^ 2 := by
    nlinarith [sq_nonneg ‖du‖, sq_nonneg ‖dv‖, mul_nonneg (norm_nonneg du) (norm_nonneg dv)]
  have hvsquare : ‖dv‖ ^ 2 ≤ (‖du‖ + ‖dv‖) ^ 2 := by
    nlinarith [sq_nonneg ‖du‖, mul_nonneg (norm_nonneg du) (norm_nonneg dv)]
  have hBscaled := mul_le_mul_of_nonneg_left hvsquare hB
  have hnumerator : 2 * ‖du‖ * ‖dv‖ + B * ‖dv‖ ^ 2 ≤
      (2 + B) * (‖du‖ + ‖dv‖) ^ 2 := by
    nlinarith only [hcross, hBscaled]
  have hquadratic : (2 * ‖du‖ * ‖dv‖ + B * ‖dv‖ ^ 2) / μ ≤
      ((2 + B) / μ) * (‖du‖ + ‖dv‖) ^ 2 := by
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right hnumerator hμ.le
  have hbound := secantLogIncrementRemainderBound H u v du dv hμ hκ hH hlam hP hQ hrec
  nlinarith only [hbound, hPsquare, hQsquare, hquadratic]

/-- Helper for thm:planar-convergence: the actual logarithmic free
coefficient increment differs from its oriented secant-linear term by a
uniform multiple of the two adjacent squared step lengths. -/
theorem orbitLogIncrementRemainderBound
    (iteration : DFP.InverseIteration (Fin 2)) {μ c₁ c₂ : ℝ}
    (hf : ContDiff ℝ 2 iteration.objective) (hμ : 0 < μ)
    (hHessian : ∀ x v,
      μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient iteration.objective) x v) v)
    (hStep : ∀ k, 0 < iteration.stepLength k)
    (hWolfe : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ iteration.objective
      (iteration.point k) (iteration.point (k + 1) - iteration.point k))
    (hLip : LocallyLipschitzOn (DFP.objectiveSublevel iteration)
      (fderiv ℝ (gradient iteration.objective)))
    {xstar : EuclideanSpace ℝ (Fin 2)}
    (hmin : ∀ x, iteration.objective xstar ≤ iteration.objective x)
    (hnot : ¬ Tendsto iteration.point atTop (𝓝 xstar)) :
    ∃ R ≥ 0, ∀ᶠ k in atTop,
      |Real.log (orbitFreeCoefficient iteration (k + 1)) -
        Real.log (orbitFreeCoefficient iteration k) -
        inner ℝ ((2 / inner ℝ (orientedOrbitStep iteration k) (orientedOrbitSecant iteration k)) •
          orientedOrbitSecant iteration k)
          (orientedOrbitStep iteration (k + 1) - orientedOrbitStep iteration k)| ≤
        R * (‖iteration.point (k + 1) - iteration.point k‖ ^ 2 +
          ‖iteration.point (k + 2) - iteration.point (k + 1)‖ ^ 2) := by
  obtain ⟨M, hM, hsecant⟩ := orientedOrbitSecantBound iteration hf hμ hHessian hStep hWolfe
  obtain ⟨B, hB, hoperator⟩ :=
    orbitInverseHessianBoundedOfNonconvergence iteration hf hμ hHessian hStep hWolfe hmin hnot
  obtain ⟨D, hD, hvariation⟩ :=
    orbitOrientedSecantVariationBound iteration hf hμ hHessian hStep hWolfe hLip hmin hnot
  let ell := fun k ↦ ‖iteration.point (k + 1) - iteration.point k‖
  let du := fun k ↦ orientedOrbitStep iteration (k + 1) - orientedOrbitStep iteration k
  let dv := fun k ↦ orientedOrbitSecant iteration (k + 1) - orientedOrbitSecant iteration k
  let δ := fun k ↦ ‖du k‖ + ‖dv k‖
  let AP := (M + 2) / μ
  let AQ := (2 + B) / μ
  let F := 4 * AP ^ 2 + 2 * AQ ^ 2 + AQ
  have hAP : 0 ≤ AP := by
    dsimp only [AP]
    positivity
  have hAQ : 0 ≤ AQ := by
    dsimp only [AQ]
    positivity
  have hF : 0 ≤ F := by
    dsimp only [F]
    positivity
  have hδ (k : ℕ) : 0 ≤ δ k := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hδbound (k : ℕ) : δ k ≤ D * (ell k + ell (k + 1)) := hvariation k
  have hellLimit : Tendsto ell atTop (𝓝 0) :=
    stepNormTendstoZero iteration hf hμ hHessian hStep hWolfe
  have hδlimit : Tendsto δ atTop (𝓝 0) := by
    have hupper : Tendsto (fun k ↦ D * (ell k + ell (k + 1))) atTop (𝓝 0) := by
      simpa using (hellLimit.add (hellLimit.comp (tendsto_add_atTop_nat 1))).const_mul D
    exact squeeze_zero hδ hδbound hupper
  have hsmall (a : ℝ) : ∀ᶠ k in atTop, a * δ k < 1 / 2 := by
    have hlimit : Tendsto (fun k ↦ a * δ k) atTop (𝓝 0) := by
      simpa using hδlimit.const_mul a
    have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
    exact hlimit.eventually (eventually_lt_nhds hhalf)
  have hR : 0 ≤ 2 * F * D ^ 2 := by positivity
  refine ⟨2 * F * D ^ 2, hR, ?_⟩
  filter_upwards [hsmall 1, hsmall AP, hsmall AQ] with k hk hkP hkQ
  have hdv : ‖dv k‖ ≤ 1 := by
    dsimp only [δ] at hk
    nlinarith [norm_nonneg (du k)]
  have hκ := orientedOrbitCurvatureLower iteration hf hμ hHessian k (hStep k)
  have hu := orientedOrbitStepNorm iteration k (hStep k)
  have hPbound : |orbitRelativeCurvature iteration k| ≤ AP * δ k :=
    relativeCurvatureIncrementBound _ _ _ _ hμ hκ hu (hsecant k) hdv
  have hQbound : |orbitRelativeQuadratic iteration k| ≤ AQ * ‖dv k‖ :=
    relativeQuadraticIncrementBound _ _ _ _ hμ hκ (hoperator (k + 1)) hu hdv
  have hP : |orbitRelativeCurvature iteration k| ≤ 1 / 2 := hPbound.trans hkP.le
  have hQ : |orbitRelativeQuadratic iteration k| ≤ 1 / 2 := by
    dsimp only [δ] at hkQ
    have hcross := mul_nonneg hAQ (norm_nonneg (du k))
    nlinarith only [hQbound, hkQ, hcross]
  have hrec := orbitFreeCoefficientNormalizedRecurrence iteration hf hμ hHessian hStep k hQ
  have hbound :
      |Real.log (orbitFreeCoefficient iteration (k + 1)) -
        Real.log (orbitFreeCoefficient iteration k) -
        2 * inner ℝ (orientedOrbitSecant iteration k) (du k) /
          inner ℝ (orientedOrbitStep iteration k) (orientedOrbitSecant iteration k)| ≤
        F * δ k ^ 2 :=
    secantLogIncrementUniformBound _ _ _ _ _ hμ hκ (hoperator (k + 1)) hu (hsecant k) hdv
      (orbitFreeCoefficientPos iteration hf hμ hHessian k (hStep k)) hP hQ hrec
  have hell (j : ℕ) : 0 ≤ ell j := norm_nonneg _
  have hscalePos : 0 ≤ D * (ell k + ell (k + 1)) := by positivity
  have hδsquare : δ k ^ 2 ≤ D ^ 2 * (ell k + ell (k + 1)) ^ 2 := by
    have hproduct := mul_le_mul (hδbound k) (hδbound k) (hδ k) hscalePos
    simpa only [← pow_two, mul_pow] using hproduct
  have hsum : (ell k + ell (k + 1)) ^ 2 ≤ 2 * (ell k ^ 2 + ell (k + 1) ^ 2) := by
    nlinarith [sq_nonneg (ell k - ell (k + 1))]
  have hscaledSum := mul_le_mul_of_nonneg_left hsum (sq_nonneg D)
  have hδfinal := hδsquare.trans hscaledSum
  have hscaled := mul_le_mul_of_nonneg_left hδfinal hF
  rw [real_inner_smul_left, div_mul_eq_mul_div]
  nlinarith only [hbound, hscaled]

/-- Helper for thm:planar-convergence: the error between the
oriented step and the physical gradient tangent. -/
noncomputable def orbitTangentError (iteration : DFP.InverseIteration (Fin 2))
    (k : ℕ) : EuclideanSpace ℝ (Fin 2) :=
  orientedOrbitStep iteration k - gradientUnitTangent iteration.objective (iteration.point k)

/-- Helper for thm:planar-convergence: the small scalar correction
that compensates for orientation errors in logarithmic determinant transport. -/
noncomputable def orbitLogCorrection (iteration : DFP.InverseIteration (Fin 2)) (k : ℕ) : ℝ :=
  inner ℝ (gradientTransportCoefficient iteration.objective (iteration.point k))
    (orbitTangentError iteration k)

/-- Helper for thm:planar-convergence: the corrected logarithmic
quantity whose increments are summable on a hypothetical nonconvergent orbit. -/
noncomputable def orbitCorrectedLog (iteration : DFP.InverseIteration (Fin 2)) (k : ℕ) : ℝ :=
  Real.log (orbitFreeCoefficient iteration k) - orbitLogCorrection iteration k +
    2 * Real.log ‖gradient iteration.objective (iteration.point k)‖

/-- Helper for thm:planar-convergence: the logarithmic correction
tends to zero because the coefficient stays bounded and the orientation error vanishes. -/
theorem orbitLogCorrectionTendstoZero
    (iteration : DFP.InverseIteration (Fin 2)) {μ c₁ c₂ : ℝ}
    (hf : ContDiff ℝ 2 iteration.objective) (hμ : 0 < μ)
    (hHessian : ∀ x v,
      μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient iteration.objective) x v) v)
    (hStep : ∀ k, 0 < iteration.stepLength k)
    (hWolfe : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ iteration.objective
      (iteration.point k) (iteration.point (k + 1) - iteration.point k))
    (hLip : LocallyLipschitzOn (DFP.objectiveSublevel iteration)
      (fderiv ℝ (gradient iteration.objective)))
    {xstar : EuclideanSpace ℝ (Fin 2)}
    (hmin : ∀ x, iteration.objective xstar ≤ iteration.objective x)
    (hnot : ¬ Tendsto iteration.point atTop (𝓝 xstar)) :
    Tendsto (orbitLogCorrection iteration) atTop (𝓝 0) := by
  obtain ⟨E, hE, V, hV, happrox⟩ :=
    orbitOrientedSecantApproximation iteration hf hμ hHessian hStep hWolfe hLip hmin hnot
  obtain ⟨B, hB, hcoef⟩ := orbitTransportCoefficientBound iteration hf hμ hHessian hStep hWolfe
  have hnorm (k : ℕ) : ‖orbitLogCorrection iteration k‖ ≤
      (B * E) * ‖iteration.point (k + 1) - iteration.point k‖ := by
    rw [orbitLogCorrection, Real.norm_eq_abs]
    have hinner := abs_real_inner_le_norm
      (gradientTransportCoefficient iteration.objective (iteration.point k))
      (orbitTangentError iteration k)
    have hproduct := mul_le_mul (hcoef k) (happrox k).1 (norm_nonneg _) hB.le
    exact hinner.trans (hproduct.trans_eq (mul_assoc _ _ _).symm)
  have hupper : Tendsto
      (fun k ↦ (B * E) * ‖iteration.point (k + 1) - iteration.point k‖) atTop (𝓝 0) := by
    simpa using (stepNormTendstoZero iteration hf hμ hHessian hStep hWolfe).const_mul (B * E)
  have hnormLimit :=
    squeeze_zero (fun k ↦ norm_nonneg (orbitLogCorrection iteration k)) hnorm hupper
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hnormLimit

/-- Helper for thm:planar-convergence: the corrected log increment
splits exactly into determinant error, coefficient approximation error,
tangent cancellation, and the coefficient-variation correction. -/
theorem correctedLogIncrementIdentity
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (l n : ℕ → ℝ) (u t a c : ℕ → E) (k : ℕ) :
    (l (k + 1) - inner ℝ (a (k + 1)) (u (k + 1) - t (k + 1)) + 2 * n (k + 1)) -
      (l k - inner ℝ (a k) (u k - t k) + 2 * n k) =
      (l (k + 1) - l k - inner ℝ (c k) (u (k + 1) - u k)) +
      inner ℝ (c k - a k) (u (k + 1) - u k) +
      (inner ℝ (a k) (t (k + 1) - t k) + 2 * (n (k + 1) - n k)) -
      inner ℝ (a (k + 1) - a k) (u (k + 1) - t (k + 1)) := by
  simp only [inner_sub_left, inner_sub_right]
  ring

/-- Helper for thm:planar-convergence: the four error bounds in the
corrected logarithmic identity yield one quadratic increment bound. -/
theorem correctedLogIncrementBound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (l n : ℕ → ℝ) (u t a c : ℕ → E) (ell : ℕ → ℝ) (k : ℕ)
    {R C D T A V : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hT : 0 ≤ T)
    (hA : 0 ≤ A) (hV : 0 ≤ V) (hell : ∀ j, 0 ≤ ell j)
    (hlog : |l (k + 1) - l k - inner ℝ (c k) (u (k + 1) - u k)| ≤
      R * (ell k ^ 2 + ell (k + 1) ^ 2))
    (hcoef : ‖c k - a k‖ ≤ C * ell k)
    (hstep : ‖u (k + 1) - u k‖ ≤ D * (ell k + ell (k + 1)))
    (htangent : |inner ℝ (a k) (t (k + 1) - t k) + 2 * (n (k + 1) - n k)| ≤
      T * ell k ^ 2)
    (hvariation : ‖a (k + 1) - a k‖ ≤ A * ell k)
    (herror : ‖u (k + 1) - t (k + 1)‖ ≤ V * ell (k + 1)) :
    |(l (k + 1) - inner ℝ (a (k + 1)) (u (k + 1) - t (k + 1)) + 2 * n (k + 1)) -
      (l k - inner ℝ (a k) (u k - t k) + 2 * n k)| ≤
      (R + 2 * C * D + T + A * V) * (ell k ^ 2 + ell (k + 1) ^ 2) := by
  have hcoefInner := abs_real_inner_le_norm (c k - a k) (u (k + 1) - u k)
  have hcoefProduct := mul_le_mul hcoef hstep (norm_nonneg _) (mul_nonneg hC (hell k))
  have hcross : ell k * (ell k + ell (k + 1)) ≤
      2 * (ell k ^ 2 + ell (k + 1) ^ 2) := by
    nlinarith [sq_nonneg (ell k - ell (k + 1)), sq_nonneg (ell (k + 1))]
  have hcrossScaled := mul_le_mul_of_nonneg_left hcross (mul_nonneg hC hD)
  have hcoefBound : |inner ℝ (c k - a k) (u (k + 1) - u k)| ≤
      (2 * C * D) * (ell k ^ 2 + ell (k + 1) ^ 2) := by
    nlinarith only [hcoefInner, hcoefProduct, hcrossScaled]
  have hcorrectionInner := abs_real_inner_le_norm (a (k + 1) - a k) (u (k + 1) - t (k + 1))
  have hcorrectionProduct := mul_le_mul hvariation herror (norm_nonneg _) (mul_nonneg hA (hell k))
  have hadjacent : ell k * ell (k + 1) ≤ ell k ^ 2 + ell (k + 1) ^ 2 := by
    nlinarith [sq_nonneg (ell k - ell (k + 1)), sq_nonneg (ell k), sq_nonneg (ell (k + 1))]
  have hadjacentScaled := mul_le_mul_of_nonneg_left hadjacent (mul_nonneg hA hV)
  have hcorrectionBound : |inner ℝ (a (k + 1) - a k) (u (k + 1) - t (k + 1))| ≤
      (A * V) * (ell k ^ 2 + ell (k + 1) ^ 2) := by
    nlinarith only [hcorrectionInner, hcorrectionProduct, hadjacentScaled]
  have htangentExtra := mul_nonneg hT (sq_nonneg (ell (k + 1)))
  rw [correctedLogIncrementIdentity l n u t a c k]
  have htriangle := abs_sub
    ((l (k + 1) - l k - inner ℝ (c k) (u (k + 1) - u k)) +
      inner ℝ (c k - a k) (u (k + 1) - u k) +
      (inner ℝ (a k) (t (k + 1) - t k) + 2 * (n (k + 1) - n k)))
    (inner ℝ (a (k + 1) - a k) (u (k + 1) - t (k + 1)))
  have htriangle' := abs_add_le
    ((l (k + 1) - l k - inner ℝ (c k) (u (k + 1) - u k)) +
      inner ℝ (c k - a k) (u (k + 1) - u k))
    (inner ℝ (a k) (t (k + 1) - t k) + 2 * (n (k + 1) - n k))
  have htriangle'' := abs_add_le
    (l (k + 1) - l k - inner ℝ (c k) (u (k + 1) - u k))
    (inner ℝ (c k - a k) (u (k + 1) - u k))
  nlinarith only [htriangle, htriangle', htriangle'', hlog, hcoefBound,
    htangent, htangentExtra, hcorrectionBound]

/-- Helper for thm:planar-convergence: the corrected logarithmic
quantity on the actual DFP orbit has uniformly quadratic eventual increments. -/
theorem orbitCorrectedLogIncrementBound
    (iteration : DFP.InverseIteration (Fin 2)) {μ c₁ c₂ : ℝ}
    (hf : ContDiff ℝ 2 iteration.objective) (hμ : 0 < μ)
    (hHessian : ∀ x v,
      μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient iteration.objective) x v) v)
    (hStep : ∀ k, 0 < iteration.stepLength k)
    (hWolfe : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ iteration.objective
      (iteration.point k) (iteration.point (k + 1) - iteration.point k))
    (hLip : LocallyLipschitzOn (DFP.objectiveSublevel iteration)
      (fderiv ℝ (gradient iteration.objective)))
    {xstar : EuclideanSpace ℝ (Fin 2)}
    (hmin : ∀ x, iteration.objective xstar ≤ iteration.objective x)
    (hnot : ¬ Tendsto iteration.point atTop (𝓝 xstar)) :
    ∃ K ≥ 0, ∀ᶠ k in atTop,
      |orbitCorrectedLog iteration (k + 1) - orbitCorrectedLog iteration k| ≤
        K * (‖iteration.point (k + 1) - iteration.point k‖ ^ 2 +
          ‖iteration.point (k + 2) - iteration.point (k + 1)‖ ^ 2) := by
  obtain ⟨R, hR, hlog⟩ :=
    orbitLogIncrementRemainderBound iteration hf hμ hHessian hStep hWolfe hLip hmin hnot
  obtain ⟨C, hC, hcoef⟩ :=
    orbitSecantCoefficientApproximation iteration hf hμ hHessian hStep hWolfe hLip hmin hnot
  obtain ⟨D, hD, hstep⟩ :=
    orbitOrientedSecantVariationBound iteration hf hμ hHessian hStep hWolfe hLip hmin hnot
  obtain ⟨T, hT, htangent⟩ :=
    orbitTangentLogQuadraticBound iteration hf hμ hHessian hStep hWolfe hLip hmin hnot
  obtain ⟨A, hA, hvariation⟩ :=
    orbitTransportCoefficientVariation iteration hf hμ hHessian hStep hWolfe hLip hmin hnot
  obtain ⟨V, hV, _, _, herror⟩ :=
    orbitOrientedSecantApproximation iteration hf hμ hHessian hStep hWolfe hLip hmin hnot
  have hK : 0 ≤ R + 2 * C * D + T + A * V := by positivity
  refine ⟨R + 2 * C * D + T + A * V, hK, ?_⟩
  filter_upwards [hlog, htangent] with k hkLog hkTangent
  have hstepOnly : ‖orientedOrbitStep iteration (k + 1) - orientedOrbitStep iteration k‖ ≤
      D * (‖iteration.point (k + 1) - iteration.point k‖ +
        ‖iteration.point (k + 2) - iteration.point (k + 1)‖) := by
    have htotal := hstep k
    nlinarith only [htotal,
      norm_nonneg (orientedOrbitSecant iteration (k + 1) - orientedOrbitSecant iteration k)]
  exact correctedLogIncrementBound
    (fun j ↦ Real.log (orbitFreeCoefficient iteration j))
    (fun j ↦ Real.log ‖gradient iteration.objective (iteration.point j)‖)
    (orientedOrbitStep iteration)
    (fun j ↦ gradientUnitTangent iteration.objective (iteration.point j))
    (fun j ↦ gradientTransportCoefficient iteration.objective (iteration.point j))
    (fun j ↦ (2 / inner ℝ (orientedOrbitStep iteration j) (orientedOrbitSecant iteration j)) •
      orientedOrbitSecant iteration j)
    (fun j ↦ ‖iteration.point (j + 1) - iteration.point j‖) k
    hC hD.le hT hA hV.le (fun j ↦ norm_nonneg _)
    hkLog (hcoef k) hstepOnly hkTangent (hvariation k) (herror (k + 1)).1

/-- Helper for thm:planar-convergence: the absolute increments of
the actual corrected logarithmic quantity form a summable series. -/
theorem orbitCorrectedLogIncrementsSummable
    (iteration : DFP.InverseIteration (Fin 2)) {μ c₁ c₂ : ℝ}
    (hf : ContDiff ℝ 2 iteration.objective) (hμ : 0 < μ)
    (hHessian : ∀ x v,
      μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient iteration.objective) x v) v)
    (hStep : ∀ k, 0 < iteration.stepLength k)
    (hWolfe : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ iteration.objective
      (iteration.point k) (iteration.point (k + 1) - iteration.point k))
    (hLip : LocallyLipschitzOn (DFP.objectiveSublevel iteration)
      (fderiv ℝ (gradient iteration.objective)))
    {xstar : EuclideanSpace ℝ (Fin 2)}
    (hmin : ∀ x, iteration.objective xstar ≤ iteration.objective x)
    (hnot : ¬ Tendsto iteration.point atTop (𝓝 xstar)) :
    Summable (fun k ↦ |orbitCorrectedLog iteration (k + 1) - orbitCorrectedLog iteration k|) := by
  obtain ⟨K, hK, hbound⟩ :=
    orbitCorrectedLogIncrementBound iteration hf hμ hHessian hStep hWolfe hLip hmin hnot
  have hsquares := summableStepSquares iteration hf hμ hHessian hStep hWolfe
  have hnext : Summable (fun k ↦ ‖iteration.point (k + 2) - iteration.point (k + 1)‖ ^ 2) :=
    hsquares.comp_injective Nat.succ_injective
  have hmajorant : Summable (fun k ↦ K *
      (‖iteration.point (k + 1) - iteration.point k‖ ^ 2 +
        ‖iteration.point (k + 2) - iteration.point (k + 1)‖ ^ 2)) :=
    (hsquares.add hnext).mul_left K
  apply hmajorant.of_norm_bounded_eventually_nat
  filter_upwards [hbound] with k hk
  simpa only [Real.norm_eq_abs, abs_abs] using hk

/-- Helper for thm:planar-convergence: the corrected logarithmic
quantity rules out nonconvergence of a planar DFP orbit with locally Lipschitz Hessian. -/
theorem tendstoMinimizerOfLocallyLipschitzHessian
    (iteration : DFP.InverseIteration (Fin 2)) {μ c₁ c₂ : ℝ}
    (hf : ContDiff ℝ 2 iteration.objective) (hμ : 0 < μ)
    (hHessian : ∀ x v,
      μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient iteration.objective) x v) v)
    (hStep : ∀ k, 0 < iteration.stepLength k)
    (hWolfe : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ iteration.objective
      (iteration.point k) (iteration.point (k + 1) - iteration.point k))
    (hLip : LocallyLipschitzOn (DFP.objectiveSublevel iteration)
      (fderiv ℝ (gradient iteration.objective)))
    {xstar : EuclideanSpace ℝ (Fin 2)}
    (hmin : ∀ x, iteration.objective xstar ≤ iteration.objective x) :
    Tendsto iteration.point atTop (𝓝 xstar) ∧
      Tendsto (fun k ↦ ‖gradient iteration.objective (iteration.point k)‖) atTop (𝓝 0) := by
  have hpoint : Tendsto iteration.point atTop (𝓝 xstar) := by
    by_contra hnot
    have hpositive (k : ℕ) : 0 < orbitFreeCoefficient iteration k :=
      orbitFreeCoefficientPos iteration hf hμ hHessian k (hStep k)
    have hgradient (k : ℕ) : 0 < ‖gradient iteration.objective (iteration.point k)‖ := by
      apply norm_pos_iff.mpr
      simpa only [DFP.gradients_apply] using iteration.gradientNeZeroOfSecantDenominator k
    obtain ⟨M, _, hdiffBounds⟩ := uniformDifferentialBoundsOnSublevel hf hμ hHessian
      (iteration.point 0)
    have hupper (k : ℕ) : ‖gradient iteration.objective (iteration.point k)‖ ≤ M := by
      have hmem := iteration.pointMemObjectiveSublevelOfWeakWolfe hStep hWolfe k
      have hlevel := (DFP.mem_objectiveSublevel_iff iteration _).mp hmem
      exact (hdiffBounds _ hlevel).1
    have hcorrection := orbitLogCorrectionTendstoZero
      iteration hf hμ hHessian hStep hWolfe hLip hmin hnot
    have hincrements := orbitCorrectedLogIncrementsSummable
      iteration hf hμ hHessian hStep hWolfe hLip hmin hnot
    obtain ⟨δ, hδ, hlower⟩ := positiveLowerBoundOfCorrectedLog hpositive hgradient hupper
      hcorrection hincrements
    have hzero := orbitFreeCoefficientTendstoZero iteration hf hμ hHessian hStep hWolfe hmin hnot
    exact not_tendsto_zero_of_eventually_positive_lower_bound hδ hlower hzero
  have hfOrder : ContDiff ℝ ((1 : ℕ∞) + 1) iteration.objective := by
    convert hf using 1
    norm_num
  have hgradientCont : ContDiff ℝ 1 (gradient iteration.objective) :=
    hfOrder.gradient_succ (n := 1)
  have hgradientLimit := (hgradientCont.continuous.tendsto xstar).comp hpoint
  have hstationary := gradientZeroOfGlobalMinimizer hmin
  refine ⟨hpoint, ?_⟩
  simpa only [hstationary, norm_zero, Function.comp_def] using hgradientLimit.norm

/-- Helper for thm:planar-convergence (infinite-orbit branch): every positive-step
classical planar DFP orbit on a globally strongly convex C2 objective with
locally Lipschitz Hessian on its initial sublevel converges to the unique
minimizer, and its gradient norms converge to zero. The weak Wolfe
coefficients are arbitrary fixed admissible coefficients. -/
theorem existsUniqueLimitOfLocallyLipschitzHessian
    (iteration : DFP.InverseIteration (Fin 2)) {μ c₁ c₂ : ℝ}
    (hf : ContDiff ℝ 2 iteration.objective) (hμ : 0 < μ)
    (hHessian : ∀ x v,
      μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient iteration.objective) x v) v)
    (hStep : ∀ k, 0 < iteration.stepLength k)
    (hWolfe : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ iteration.objective
      (iteration.point k) (iteration.point (k + 1) - iteration.point k))
    (hLip : LocallyLipschitzOn (DFP.objectiveSublevel iteration)
      (fderiv ℝ (gradient iteration.objective))) :
    ∃! xstar, (∀ x, iteration.objective xstar ≤ iteration.objective x) ∧
      Tendsto iteration.point atTop (𝓝 xstar) ∧
      Tendsto (fun k ↦ ‖gradient iteration.objective (iteration.point k)‖) atTop (𝓝 0) := by
  obtain ⟨xstar, hmin, hunique⟩ := existsUniqueGlobalMinimizerOfHessian hf hμ hHessian
  have hconvergence := tendstoMinimizerOfLocallyLipschitzHessian
    iteration hf hμ hHessian hStep hWolfe hLip hmin
  refine ⟨xstar, ⟨hmin, hconvergence⟩, ?_⟩
  intro y hy
  exact hunique y hy.1

/-- Helper for thm:planar-convergence: every stationary point of the
globally strongly convex objective is a global minimizer. This verifies
the finite-termination branch independently of any infinite-orbit encoding. -/
theorem stationaryPointMinimizes
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} {μ : ℝ} (hf : ContDiff ℝ 2 f) (hμ : 0 < μ)
    (hHessian : ∀ x v, μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient f) x v) v)
    {xstar : E} (hstationary : gradient f xstar = 0) : ∀ x, f xstar ≤ f x := by
  intro x
  have hfirst := hf.firstOrderOfHessianLowerBound f μ hμ hHessian xstar x
  rw [hstationary, inner_zero_left, add_zero] at hfirst
  have hnonnegative : 0 ≤ μ / 2 * ‖x - xstar‖ ^ 2 := by positivity
  linarith

/-- Helper for thm:planar-convergence: a strongly convex C3 objective
satisfies the Hessian regularity needed by the planar convergence theorem. -/
theorem existsUniqueLimitOfC3
    (iteration : DFP.InverseIteration (Fin 2)) {μ c₁ c₂ : ℝ}
    (hf : ContDiff ℝ 3 iteration.objective) (hμ : 0 < μ)
    (hHessian : ∀ x v,
      μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient iteration.objective) x v) v)
    (hStep : ∀ k, 0 < iteration.stepLength k)
    (hWolfe : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ iteration.objective
      (iteration.point k) (iteration.point (k + 1) - iteration.point k)) :
    ∃! xstar, (∀ x, iteration.objective xstar ≤ iteration.objective x) ∧
      Tendsto iteration.point atTop (𝓝 xstar) ∧
      Tendsto (fun k ↦ ‖gradient iteration.objective (iteration.point k)‖) atTop (𝓝 0) := by
  have htwoThree : (2 : WithTop ℕ∞) ≤ 3 := by norm_num
  have hfOrder : ContDiff ℝ ((2 : ℕ∞) + 1) iteration.objective := by
    convert hf using 1
    norm_num
  have hgradient : ContDiff ℝ 2 (gradient iteration.objective) := hfOrder.gradient_succ (n := 2)
  have hderivativeOrder : (1 : WithTop ℕ∞) + 1 ≤ 2 := by norm_num
  have hHessianSmooth : ContDiff ℝ 1 (fderiv ℝ (gradient iteration.objective)) :=
    hgradient.fderiv_right hderivativeOrder
  have hLip : LocallyLipschitzOn (DFP.objectiveSublevel iteration)
      (fderiv ℝ (gradient iteration.objective)) :=
    hHessianSmooth.locallyLipschitz.locallyLipschitzOn
  exact existsUniqueLimitOfLocallyLipschitzHessian iteration (hf.of_le htwoThree)
    hμ hHessian hStep hWolfe hLip

/-- Helper for eq:counterexample-nonlipschitz: a planar uniformly
convex weak-Wolfe counterexample cannot have a locally Lipschitz Hessian
on its initial objective sublevel. -/
theorem counterexampleHessianNotLocallyLipschitz
    {m M c₁ c₂ : ℝ} (counterexample : DFP.WolfeCounterexample (Fin 2) m M c₁ c₂)
    (hm : 0 < m) :
    ¬ LocallyLipschitzOn (DFP.objectiveSublevel counterexample.iteration)
      (fderiv ℝ (gradient counterexample.iteration.objective)) := by
  intro hLip
  have hHessian (x v : EuclideanSpace ℝ (Fin 2)) :
      m * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient counterexample.iteration.objective) x v) v := by
    have hbound := ((counterexample.hessianBounds.at x).quadraticForm v).1
    simpa only [hessian_def] using hbound
  obtain ⟨xstar, hresult, _⟩ := existsUniqueLimitOfLocallyLipschitzHessian
    counterexample.iteration counterexample.objectiveContDiff hm hHessian
    counterexample.stepLengthPos counterexample.weakWolfe hLip
  have hzero : Tendsto
      (fun k ↦ ‖DFP.gradients counterexample.iteration.objective counterexample.iteration.point k‖)
      atTop (𝓝 0) := by
    simpa only [DFP.gradients_apply] using hresult.2.2
  exact DFP.not_tendsto_zero_of_pos_limit counterexample.gradientLimitPos
    counterexample.gradientNormTendsto hzero

/-- Helper for thm:planar-convergence: a nonstationary raw DFP step
from a positive-definite matrix has strictly positive secant curvature under weak Wolfe. -/
theorem rawOrbitSecantCurvaturePos
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} {α : ℕ → ℝ}
    {x g : ℕ → EuclideanSpace ℝ (Fin 2)} {H : ℕ → Matrix (Fin 2) (Fin 2) ℝ}
    (orbit : DFP.IsOrbit f α x g H) {c₁ c₂ : ℝ} (k : ℕ)
    (hH : (H k).PosDef) (hg : g k ≠ 0)
    (hWolfe : LineSearch.IsWeakWolfe c₁ c₂ f (x k) (x (k + 1) - x k)) :
    0 < WithLp.ofLp (DFP.steps α (DFP.directions H g) k) ⬝ᵥ
      WithLp.ofLp (DFP.gradientChanges g k) := by
  have hcoordinates : WithLp.ofLp (g k) ≠ 0 := by
    intro hzero
    apply hg
    apply WithLp.ofLp_injective 2
    simpa only [WithLp.ofLp_zero] using hzero
  have henergy : 0 < WithLp.ofLp (g k) ⬝ᵥ (H k *ᵥ WithLp.ofLp (g k)) := by
    simpa only [star_trivial] using hH.dotProduct_mulVec_pos hcoordinates
  have hstep : x (k + 1) - x k = DFP.steps α (DFP.directions H g) k := by
    rw [orbit.pointSucc k]
    abel
  have hdescent : inner ℝ (g k) (x (k + 1) - x k) < 0 := by
    rw [hstep, DFP.steps_apply, DFP.directions_apply,
      real_inner_smul_right, inner_neg_right, EuclideanSpace.inner_eq_star_dotProduct]
    simp only [star_trivial]
    have hcomm : (H k *ᵥ WithLp.ofLp (g k)) ⬝ᵥ WithLp.ofLp (g k) =
        WithLp.ofLp (g k) ⬝ᵥ (H k *ᵥ WithLp.ofLp (g k)) := dotProduct_comm _ _
    rw [hcomm]
    nlinarith [orbit.stepLengthPos k]
  have hcurvature := hWolfe.weakCurvature
  rw [add_sub_cancel, (orbit.gradientAt k).gradient,
    (orbit.gradientAt (k + 1)).gradient] at hcurvature
  have hpair : 0 < inner ℝ (g (k + 1) - g k) (x (k + 1) - x k) := by
    rw [inner_sub_left]
    have hstrict := mul_neg_of_pos_of_neg (sub_pos.mpr hWolfe.c₂_lt_one) hdescent
    nlinarith
  rw [hstep, EuclideanSpace.inner_eq_star_dotProduct] at hpair
  simpa only [star_trivial, DFP.gradientChanges_apply] using hpair

/-- Helper for thm:planar-convergence: initial positive definiteness
propagates along every nonstationary raw DFP orbit satisfying weak Wolfe. -/
theorem rawOrbitPositiveDefinite
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} {α : ℕ → ℝ}
    {x g : ℕ → EuclideanSpace ℝ (Fin 2)} {H : ℕ → Matrix (Fin 2) (Fin 2) ℝ}
    (orbit : DFP.IsOrbit f α x g H) {c₁ c₂ : ℝ}
    (hH₀ : (H 0).PosDef) (hg : ∀ k, g k ≠ 0)
    (hWolfe : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ f (x k) (x (k + 1) - x k)) :
    ∀ k, (H k).PosDef := by
  intro k
  induction k with
  | zero => exact hH₀
  | succ k ih =>
    rw [orbit.inverseHessianSucc k]
    exact ih.inverseDFPUpdate (rawOrbitSecantCurvaturePos orbit k ih (hg k) (hWolfe k))

/-- Helper for thm:planar-convergence: the nonstationary raw orbit
converges using only initial positive definiteness, with all later
well-definedness conditions derived from the DFP and Wolfe equations. -/
theorem rawOrbitConvergenceOfNonstationary
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} {α : ℕ → ℝ}
    {x g : ℕ → EuclideanSpace ℝ (Fin 2)} {H : ℕ → Matrix (Fin 2) (Fin 2) ℝ}
    (orbit : DFP.IsOrbit f α x g H) {μ c₁ c₂ : ℝ}
    (hf : ContDiff ℝ 2 f) (hμ : 0 < μ)
    (hHessian : ∀ z v, μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient f) z v) v)
    (hH₀ : (H 0).PosDef) (hg : ∀ k, g k ≠ 0)
    (hWolfe : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ f (x k) (x (k + 1) - x k))
    (hLip : LocallyLipschitzOn {z | f z ≤ f (x 0)} (fderiv ℝ (gradient f))) :
    ∃! xstar, (∀ z, f xstar ≤ f z) ∧ Tendsto x atTop (𝓝 xstar) ∧
      Tendsto (fun k ↦ ‖gradient f (x k)‖) atTop (𝓝 0) := by
  have hPosDef := rawOrbitPositiveDefinite orbit hH₀ hg hWolfe
  have hDenominator (k : ℕ) :
      WithLp.ofLp (DFP.steps α (DFP.directions H g) k) ⬝ᵥ
        WithLp.ofLp (DFP.gradientChanges g k) ≠ 0 :=
    (rawOrbitSecantCurvaturePos orbit k (hPosDef k) (hg k) (hWolfe k)).ne'
  let iteration := orbit.toInverseIteration hPosDef hDenominator
  have hfEq : iteration.objective = f := orbit.toInverseIteration_objective hPosDef hDenominator
  have hxEq : iteration.point = x := orbit.toInverseIteration_point_eq hPosDef hDenominator
  have hαEq : iteration.stepLength = α := orbit.toInverseIteration_stepLength hPosDef hDenominator
  have hSmooth : ContDiff ℝ 2 iteration.objective := by
    rw [hfEq]
    exact hf
  have hLower (z v : EuclideanSpace ℝ (Fin 2)) :
      μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient iteration.objective) z v) v := by
    rw [hfEq]
    exact hHessian z v
  have hStep (k : ℕ) : 0 < iteration.stepLength k := by
    rw [hαEq]
    exact orbit.stepLengthPos k
  have hWeak (k : ℕ) : LineSearch.IsWeakWolfe c₁ c₂ iteration.objective
      (iteration.point k) (iteration.point (k + 1) - iteration.point k) := by
    rw [hfEq, hxEq]
    exact hWolfe k
  have hlevel : DFP.objectiveSublevel iteration = {z | f z ≤ f (x 0)} := by
    ext z
    rw [DFP.mem_objectiveSublevel_iff, hfEq, hxEq, Set.mem_setOf_eq]
  have hLocal : LocallyLipschitzOn (DFP.objectiveSublevel iteration)
      (fderiv ℝ (gradient iteration.objective)) := by
    rw [hlevel, hfEq]
    exact hLip
  have hresult := existsUniqueLimitOfLocallyLipschitzHessian iteration hSmooth hμ hLower
    hStep hWeak hLocal
  simpa only [hfEq, hxEq] using hresult

/-- Helper for thm:planar-convergence: after a raw orbit reaches a
stationary point, its algebraically continued point sequence remains there. -/
theorem rawOrbitStationaryTail
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} {α : ℕ → ℝ}
    {x g : ℕ → EuclideanSpace ℝ (Fin 2)} {H : ℕ → Matrix (Fin 2) (Fin 2) ℝ}
    (orbit : DFP.IsOrbit f α x g H) {k : ℕ} (hg : g k = 0) :
    ∀ j, x (k + j) = x k := by
  have hstationary : gradient f (x k) = 0 := (orbit.gradientAt k).gradient.trans hg
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    have hzero : g (k + j) = 0 := by
      rw [← (orbit.gradientAt (k + j)).gradient, ih]
      exact hstationary
    rw [Nat.add_succ, Nat.succ_eq_add_one,
      orbit.pointSucc, DFP.steps_apply, DFP.directions_apply, hzero]
    simp only [WithLp.ofLp_zero, Matrix.mulVec_zero, WithLp.toLp_zero, neg_zero,
      smul_zero, add_zero]
    exact ih

/-- thm:planar-convergence: from an arbitrary positive-definite
initial inverse Hessian, a classical planar DFP orbit satisfying fixed weak
Wolfe conditions converges to the unique minimizer of a globally strongly
convex C2 objective with locally Lipschitz Hessian on its initial sublevel.
The statement includes a stationary hit through the constant algebraic
continuation of the point sequence; later matrix positivity is not assumed. -/
theorem rawOrbitConvergence
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} {α : ℕ → ℝ}
    {x g : ℕ → EuclideanSpace ℝ (Fin 2)} {H : ℕ → Matrix (Fin 2) (Fin 2) ℝ}
    (orbit : DFP.IsOrbit f α x g H) {μ c₁ c₂ : ℝ}
    (hf : ContDiff ℝ 2 f) (hμ : 0 < μ)
    (hHessian : ∀ z v, μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient f) z v) v)
    (hH₀ : (H 0).PosDef)
    (hWolfe : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ f (x k) (x (k + 1) - x k))
    (hLip : LocallyLipschitzOn {z | f z ≤ f (x 0)} (fderiv ℝ (gradient f))) :
    ∃! xstar, (∀ z, f xstar ≤ f z) ∧ Tendsto x atTop (𝓝 xstar) ∧
      Tendsto (fun k ↦ ‖gradient f (x k)‖) atTop (𝓝 0) := by
  classical
  by_cases hnonstationary : ∀ k, g k ≠ 0
  · exact rawOrbitConvergenceOfNonstationary orbit hf hμ hHessian hH₀ hnonstationary hWolfe hLip
  · push Not at hnonstationary
    obtain ⟨k, hg⟩ := hnonstationary
    have hstationary : gradient f (x k) = 0 := (orbit.gradientAt k).gradient.trans hg
    have hminHit := stationaryPointMinimizes hf hμ hHessian hstationary
    obtain ⟨xstar, hmin, hunique⟩ := existsUniqueGlobalMinimizerOfHessian hf hμ hHessian
    have hhit : x k = xstar := hunique (x k) hminHit
    have htail := rawOrbitStationaryTail orbit hg
    have heventual : ∀ᶠ j in atTop, x j = xstar := by
      filter_upwards [eventually_ge_atTop k] with j hj
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
      exact (htail d).trans hhit
    have hpoint : Tendsto x atTop (𝓝 xstar) :=
      (tendsto_congr' heventual).mpr tendsto_const_nhds
    have hfOrder : ContDiff ℝ ((1 : ℕ∞) + 1) f := by
      convert hf using 1
      norm_num
    have hgradient : ContDiff ℝ 1 (gradient f) := hfOrder.gradient_succ (n := 1)
    have hgradientLimit := (hgradient.continuous.tendsto xstar).comp hpoint
    have hzero := gradientZeroOfGlobalMinimizer hmin
    have hnorm : Tendsto (fun j ↦ ‖gradient f (x j)‖) atTop (𝓝 0) := by
      simpa only [Function.comp_def, hzero, norm_zero] using hgradientLimit.norm
    refine ⟨xstar, ⟨hmin, hpoint, hnorm⟩, ?_⟩
    intro y hy
    exact hunique y hy.1

/-- Helper for thm:planar-convergence: the manuscript's hypothesis of
a locally Lipschitz Hessian on an open neighborhood of the initial sublevel
implies the sublevel regularity used by the convergence proof. -/
theorem rawOrbitConvergenceOfNeighborhood
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} {α : ℕ → ℝ}
    {x g : ℕ → EuclideanSpace ℝ (Fin 2)} {H : ℕ → Matrix (Fin 2) (Fin 2) ℝ}
    (orbit : DFP.IsOrbit f α x g H) {μ c₁ c₂ : ℝ}
    (hf : ContDiff ℝ 2 f) (hμ : 0 < μ)
    (hHessian : ∀ z v, μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient f) z v) v)
    (hH₀ : (H 0).PosDef)
    (hWolfe : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ f (x k) (x (k + 1) - x k))
    (hNeighborhood : ∃ U : Set (EuclideanSpace ℝ (Fin 2)), IsOpen U ∧
      {z | f z ≤ f (x 0)} ⊆ U ∧ LocallyLipschitzOn U (fderiv ℝ (gradient f))) :
    ∃! xstar, (∀ z, f xstar ≤ f z) ∧ Tendsto x atTop (𝓝 xstar) ∧
      Tendsto (fun k ↦ ‖gradient f (x k)‖) atTop (𝓝 0) := by
  obtain ⟨U, _, hsubset, hLip⟩ := hNeighborhood
  exact rawOrbitConvergence orbit hf hμ hHessian hH₀ hWolfe (hLip.mono hsubset)

/-- Helper for thm:planar-convergence: the C3 specialization applies
to raw DFP trajectories with only initial positive definiteness. -/
theorem rawOrbitConvergenceOfC3
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} {α : ℕ → ℝ}
    {x g : ℕ → EuclideanSpace ℝ (Fin 2)} {H : ℕ → Matrix (Fin 2) (Fin 2) ℝ}
    (orbit : DFP.IsOrbit f α x g H) {μ c₁ c₂ : ℝ}
    (hf : ContDiff ℝ 3 f) (hμ : 0 < μ)
    (hHessian : ∀ z v, μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient f) z v) v)
    (hH₀ : (H 0).PosDef)
    (hWolfe : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ f (x k) (x (k + 1) - x k)) :
    ∃! xstar, (∀ z, f xstar ≤ f z) ∧ Tendsto x atTop (𝓝 xstar) ∧
      Tendsto (fun k ↦ ‖gradient f (x k)‖) atTop (𝓝 0) := by
  have htwoThree : (2 : WithTop ℕ∞) ≤ 3 := by norm_num
  have hfOrder : ContDiff ℝ ((2 : ℕ∞) + 1) f := by
    convert hf using 1
    norm_num
  have hgradient : ContDiff ℝ 2 (gradient f) := hfOrder.gradient_succ (n := 2)
  have hderivativeOrder : (1 : WithTop ℕ∞) + 1 ≤ 2 := by norm_num
  have hHessianSmooth : ContDiff ℝ 1 (fderiv ℝ (gradient f)) :=
    hgradient.fderiv_right hderivativeOrder
  exact rawOrbitConvergence orbit (hf.of_le htwoThree) hμ hHessian hH₀ hWolfe
    hHessianSmooth.locallyLipschitz.locallyLipschitzOn

/-- Helper for thm:planar-convergence: Armijo decrease on a strongly
convex objective forces the accepted displacement to have nonpositive
initial directional derivative. -/
theorem armijoDescentOfHessianLowerBound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} {μ c₁ : ℝ} (hf : ContDiff ℝ 2 f) (hμ : 0 < μ)
    (hHessian : ∀ z v, μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient f) z v) v)
    {x s : E} (hc₁ : c₁ < 1)
    (hArmijo : f (x + s) ≤ f x + c₁ * inner ℝ (gradient f x) s) :
    inner ℝ (gradient f x) s ≤ 0 := by
  have hfirst := hf.firstOrderOfHessianLowerBound f μ hμ hHessian x (x + s)
  rw [add_sub_cancel_left] at hfirst
  have hnonnegative : 0 ≤ μ / 2 * ‖s‖ ^ 2 := by positivity
  by_contra hpositive
  have hproduct := mul_pos (sub_pos.mpr hc₁) (lt_of_not_ge hpositive)
  nlinarith



/-! The next interface records the exact two-dimensional residual geometry used in
the manuscript's Hölder sharpness argument. -/

/-- Helper for eq:counterexample-nonlipschitz: in two dimensions, the residual of
the symmetric secant matrix `1 + εS` from the identity has Euclidean norm
`|ε|` times the norm of the secant step, where `S` exchanges the coordinates. -/
theorem planarSecantResidualNorm
    (ε : ℝ) (v : EuclideanSpace ℝ (Fin 2)) :
    ‖WithLp.toLp 2
        (((1 + ε • (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ)) - 1) *ᵥ
          WithLp.ofLp v)‖ = |ε| * ‖v‖ := by
  let S : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]
  have hS : S ∈ Matrix.orthogonalGroup (Fin 2) ℝ := by
    apply (Matrix.mem_orthogonalGroup_iff (Fin 2) ℝ).mpr
    ext i j
    fin_cases i <;> fin_cases j <;> simp [S, Matrix.mul_apply, Fin.sum_univ_two]
  have hsub : (1 + ε • S - 1 : Matrix (Fin 2) (Fin 2) ℝ) = ε • S := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [S]
  rw [hsub, Matrix.smul_mulVec, WithLp.toLp_smul, norm_smul,
    Real.norm_eq_abs, Matrix.norm_toLp_mulVec_eq_of_mem_orthogonalGroup S hS]

/-- Helper for eq:counterexample-nonlipschitz: an abstract DFP phase whose secant
matrix is `1 + εS` has gradient-change residual exactly `|ε|` times its step norm. -/
theorem abstractSecantResidualNorm
    {z : DFP.AbstractSecantStep (Fin 2)} (ε : ℝ)
    (hA : z.secantMatrix = !![1, ε; ε, 1]) :
    ‖WithLp.toLp 2 (z.gradientChange - z.displacement)‖ =
      |ε| * ‖WithLp.toLp 2 z.displacement‖ := by
  rw [z.gradientChange_def, hA]
  have hvec :
      (!![1, ε; ε, 1] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ z.displacement -
          z.displacement =
        ((1 + ε • (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ)) - 1) *ᵥ
          z.displacement := by
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [hvec]
  simpa only [WithLp.ofLp_toLp] using
    planarSecantResidualNorm ε (WithLp.toLp 2 z.displacement)


/-- Helper for eq:counterexample-nonlipschitz: a planar secant residual of size
`εₖ‖sₖ‖`, together with `‖sₖ‖/εₖ² → C > 0`, cannot satisfy a Hölder remainder
bound of order `1 + β` when `β > 1/2`. -/
theorem holderExponent_le_half_of_planarSecantResidual
    {ε sn : ℕ → ℝ} {β L C : ℝ}
    (hε : Tendsto ε atTop (𝓝 0))
    (hεpos : ∀ᶠ k in atTop, 0 < ε k)
    (hsn : Tendsto (fun k ↦ sn k / (ε k) ^ 2) atTop (𝓝 C))
    (hC : 0 < C) (hβ : 1 / 2 < β) (hL : 0 < L)
    (hresidual : ∀ᶠ k in atTop,
      ε k * sn k ≤ L * (sn k) ^ (1 + β)) : False := by
  have hδ : 0 < 2 * β - 1 := by
    linarith
  have hApos : ∀ᶠ k in atTop, 0 < sn k / (ε k) ^ 2 :=
    hsn.eventually (eventually_gt_nhds hC)
  have hratio : Tendsto (fun k ↦ (sn k) ^ β / ε k) atTop (𝓝 0) := by
    have hApow : Tendsto (fun k ↦ (sn k / (ε k) ^ 2) ^ β)
        atTop (𝓝 (C ^ β)) := by
      exact hsn.rpow tendsto_const_nhds (Or.inl (ne_of_gt hC))
    have hEpow : Tendsto (fun k ↦ (ε k) ^ (2 * β - 1))
        atTop (𝓝 0) := by
      have h := hε.rpow tendsto_const_nhds (Or.inr hδ)
      simpa only [Real.zero_rpow (ne_of_gt hδ)] using h
    have hprod : Tendsto
        (fun k ↦ (sn k / (ε k) ^ 2) ^ β * (ε k) ^ (2 * β - 1))
        atTop (𝓝 0) := by
      simpa only [mul_zero] using hApow.mul hEpow
    have heq : (fun k ↦ (sn k) ^ β / ε k) =ᶠ[atTop]
        (fun k ↦ (sn k / (ε k) ^ 2) ^ β * (ε k) ^ (2 * β - 1)) := by
      filter_upwards [hApos, hεpos] with k hAk hεk
      have hden : 0 < (ε k) ^ 2 := sq_pos_of_pos hεk
      have hsnpos : 0 < sn k := by
        have hmul := mul_pos hAk hden
        rwa [div_mul_cancel₀ _ (ne_of_gt hden)] at hmul
      have hsnFactor : sn k = (sn k / (ε k) ^ 2) * (ε k) ^ 2 := by
        exact (div_mul_cancel₀ _ (ne_of_gt hden)).symm
      have hsnPow : (sn k) ^ β =
          (sn k / (ε k) ^ 2) ^ β * ((ε k) ^ 2) ^ β := by
        conv_lhs => rw [hsnFactor]
        rw [Real.mul_rpow (div_nonneg (le_of_lt hsnpos) hden.le) hden.le]
      have hratioEq : (sn k) ^ β / ε k =
          (sn k / (ε k) ^ 2) ^ β * (ε k) ^ (2 * β - 1) := by
        rw [hsnPow]
        have hpowtwo : (ε k) ^ 2 = ε k ^ (2 : ℝ) := by
          exact (Real.rpow_natCast (ε k) 2).symm
        rw [hpowtwo, ← Real.rpow_mul hεk.le]
        rw [Real.rpow_sub hεk (2 * β) 1, Real.rpow_one]
        ring
      exact hratioEq
    exact hprod.congr' heq.symm
  have hone : ∀ᶠ k in atTop, (1 : ℝ) ≤ L * ((sn k) ^ β / ε k) := by
    filter_upwards [hresidual, hApos, hεpos] with k hk hAk hεk
    have hden : 0 < (ε k) ^ 2 := sq_pos_of_pos hεk
    have hsnpos : 0 < sn k := by
      have hmul := mul_pos hAk hden
      rwa [div_mul_cancel₀ _ (ne_of_gt hden)] at hmul
    have hresidual' : ε k * sn k ≤ (L * (sn k) ^ β) * sn k := by
      simpa [Real.rpow_add hsnpos, mul_assoc, mul_left_comm, mul_comm] using hk
    have hdivSn : ε k ≤ L * (sn k) ^ β := by
      exact le_of_mul_le_mul_right hresidual' hsnpos
    have hdesired : (1 : ℝ) ≤ (L * (sn k) ^ β) / ε k :=
      (le_div_iff₀ hεk).2 (by simpa using hdivSn)
    simpa [mul_div_assoc] using hdesired
  have hsmall : ∀ᶠ k in atTop, (sn k) ^ β / ε k < 1 / (L + 1) := by
    exact hratio.eventually (eventually_lt_nhds (by positivity))
  obtain ⟨k, hk⟩ := (hone.and hsmall).exists
  have hden : 0 < L + 1 := by
    linarith
  have hupper : L * ((sn k) ^ β / ε k) < 1 := by
    calc
      L * ((sn k) ^ β / ε k) < L * (1 / (L + 1)) :=
        mul_lt_mul_of_pos_left hk.2 hL
      _ < 1 := by
        field_simp
        linarith
  exact (not_lt_of_ge hk.1) hupper

/-- Helper for eq:holder-hessian-bound: the third derivative of a scaled linear bump
is controlled by the third and second derivatives of its cutoff, with the expected
quadratic inverse-scale factor. -/
theorem norm_iteratedFDeriv_three_scaledLinearBump_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [Nontrivial E]
    (χ : E → ℝ) (hχ : ContDiff ℝ (3 : WithTop ℕ∞) χ)
    {M0 M2 M3 : ℝ} (hM0 : ∀ y, ‖χ y‖ ≤ M0)
    (hM2 : ∀ y, ‖iteratedFDeriv ℝ 2 χ y‖ ≤ M2)
    (hM3 : ∀ y, ‖iteratedFDeriv ℝ 3 χ y‖ ≤ M3)
    (hχ_support : tsupport χ ⊆ Metric.ball 0 1)
    (x : E) (ρ : ℝ) (a z : E) (hρ : 0 < ρ)
    (hz : z ∈ tsupport (AffineBump.scaledLinearBump χ x ρ a)) :
    ‖iteratedFDeriv ℝ 3 (AffineBump.scaledLinearBump χ x ρ a) z‖ ≤
      (M3 + 3 * M2) * ‖a‖ / ρ ^ 2 := by
  let A : E →L[ℝ] E := ρ⁻¹ • ContinuousLinearMap.id ℝ E
  let b : E := -(ρ⁻¹ • x)
  have hA : ∀ w : E, A w + b = ρ⁻¹ • (w - x) := by
    intro w
    dsimp only [A, b]
    simp only [smul_apply, ContinuousLinearMap.id_apply]
    rw [smul_sub]
    simp only [sub_eq_add_neg]
  have hAnorm : ‖A‖ ≤ ρ⁻¹ := by
    dsimp only [A]
    rw [norm_smul, ContinuousLinearMap.norm_id]
    rw [Real.norm_eq_abs, abs_inv, abs_of_pos hρ]
    simp
  have hχ2 : ContDiff ℝ (2 : WithTop ℕ∞) χ := by
    apply hχ.of_le
    norm_num
  have hχ3 : ContDiff ℝ (3 : WithTop ℕ∞) χ := hχ
  have hf : ContDiff ℝ (3 : WithTop ℕ∞) (fun w : E => χ (A w + b)) := by
    exact hχ3.comp ((A.contDiff).add contDiff_const)
  let glin : E → ℝ := fun w => inner ℝ a (w - x)
  have hg : ContDiff ℝ (3 : WithTop ℕ∞) glin := by
    dsimp only [glin]
    exact (contDiff_const : ContDiff ℝ (3 : WithTop ℕ∞) (fun _ : E ↦ a)).inner ℝ
      (contDiff_id.sub (contDiff_const : ContDiff ℝ (3 : WithTop ℕ∞) (fun _ : E ↦ x)))
  have hfg : (fun w => χ (A w + b) * glin w) =
      AffineBump.scaledLinearBump χ x ρ a := by
    funext w
    rw [AffineBump.scaledLinearBump_apply, hA]
  have hM2nonneg : 0 ≤ M2 := (norm_nonneg _).trans (hM2 0)
  have hM3nonneg : 0 ≤ M3 := (norm_nonneg _).trans (hM3 0)
  have hcomp2 : ∀ w, ‖iteratedFDeriv ℝ 2 (fun t : E => χ (A t + b)) w‖ ≤
      M2 * (ρ⁻¹) ^ 2 := by
    intro w
    have hcomp := norm_iteratedFDeriv_comp_affine_le 2 χ A b hχ2 w
    have hcomp' : ‖iteratedFDeriv ℝ 2 (fun t : E => χ (A t + b)) w‖ ≤
        ‖iteratedFDeriv ℝ 2 χ (ρ⁻¹ • (w - x))‖ * ‖A‖ ^ 2 := by
      simpa only [hA w] using hcomp
    calc
      ‖iteratedFDeriv ℝ 2 (fun t : E => χ (A t + b)) w‖ ≤
          ‖iteratedFDeriv ℝ 2 χ (ρ⁻¹ • (w - x))‖ * ‖A‖ ^ 2 := hcomp'
      _ ≤ M2 * (ρ⁻¹) ^ 2 := by
        exact mul_le_mul (hM2 _) (pow_le_pow_left₀ (norm_nonneg _) hAnorm 2)
          (pow_nonneg (norm_nonneg _) 2) hM2nonneg
  have hcomp3 : ∀ w, ‖iteratedFDeriv ℝ 3 (fun t : E => χ (A t + b)) w‖ ≤
      M3 * (ρ⁻¹) ^ 3 := by
    intro w
    have hcomp := norm_iteratedFDeriv_comp_affine_le 3 χ A b hχ3 w
    have hcomp' : ‖iteratedFDeriv ℝ 3 (fun t : E => χ (A t + b)) w‖ ≤
        ‖iteratedFDeriv ℝ 3 χ (ρ⁻¹ • (w - x))‖ * ‖A‖ ^ 3 := by
      simpa only [hA w] using hcomp
    calc
      ‖iteratedFDeriv ℝ 3 (fun t : E => χ (A t + b)) w‖ ≤
          ‖iteratedFDeriv ℝ 3 χ (ρ⁻¹ • (w - x))‖ * ‖A‖ ^ 3 := hcomp'
      _ ≤ M3 * (ρ⁻¹) ^ 3 := by
        exact mul_le_mul (hM3 _) (pow_le_pow_left₀ (norm_nonneg _) hAnorm 3)
          (pow_nonneg (norm_nonneg _) 3) hM3nonneg
  have hcomp0 : ∀ w, ‖iteratedFDeriv ℝ 0 (fun t : E => χ (A t + b)) w‖ ≤ M0 := by
    intro w
    rw [norm_iteratedFDeriv_zero]
    exact hM0 _
  have hlinDeriv : fderiv ℝ glin = fun _ => innerSL ℝ a := by
    funext w
    have hsub : HasFDerivAt (fun y : E ↦ y - x)
        (ContinuousLinearMap.id ℝ E) w := by
      convert (hasFDerivAt_id (𝕜 := ℝ) w).sub (hasFDerivAt_const x w) using 1
      · ext y
        rfl
      · simp
    have hinner := fderiv_inner_apply
      (f := fun _ : E ↦ a) (g := fun y : E ↦ y - x)
      ℝ (differentiableAt_const (c := a)) hsub.differentiableAt
    rw [hsub.fderiv] at hinner
    ext y
    simpa [Function.id_def, innerSL_apply_apply] using hinner y
  have hlin1 : ∀ w, ‖iteratedFDeriv ℝ 1 glin w‖ ≤ ‖a‖ := by
    intro w
    rw [norm_iteratedFDeriv_one, hlinDeriv]
    exact (innerSL_apply_norm ℝ a).le
  have hlin0 : ‖iteratedFDeriv ℝ 0 glin z‖ ≤ ‖a‖ * ρ := by
    rw [norm_iteratedFDeriv_zero]
    have hzclosed := AffineBump.tsupport_scaledLinearBump_subset_closedBall
      χ hχ_support x ρ a hρ hz
    have hdist : ‖z - x‖ ≤ ρ := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hzclosed
    exact (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left hdist (norm_nonneg a))
  have hlin2 : ∀ w, ‖iteratedFDeriv ℝ 2 glin w‖ = 0 := by
    intro w
    rw [← norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := glin) (n := 1), hlinDeriv]
    simp [iteratedFDeriv_const_of_ne (by norm_num : 1 ≠ 0)]
  have hlin3 : ∀ w, ‖iteratedFDeriv ℝ 3 glin w‖ = 0 := by
    intro w
    rw [← norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := glin) (n := 2), hlinDeriv]
    simp [iteratedFDeriv_const_of_ne (by norm_num : 2 ≠ 0)]
  have hprod := norm_iteratedFDeriv_mul_le hf hg z (n := 3)
    (by rfl : (3 : WithTop ℕ∞) ≤ (3 : WithTop ℕ∞))
  have hprod' : ‖iteratedFDeriv ℝ 3
      (AffineBump.scaledLinearBump χ x ρ a) z‖ ≤
      ∑ i ∈ Finset.range (3 + 1),
        (Nat.choose 3 i : ℝ) * ‖iteratedFDeriv ℝ i (fun t : E => χ (A t + b)) z‖ *
          ‖iteratedFDeriv ℝ (3 - i) glin z‖ := by
    rw [← hfg]
    exact hprod
  calc
    ‖iteratedFDeriv ℝ 3
        (AffineBump.scaledLinearBump χ x ρ a) z‖ ≤
        |χ (A z + b)| * ‖iteratedFDeriv ℝ (3 - 0) glin z‖ +
            3 * ‖fderiv ℝ (fun t : E => χ (A t + b)) z‖ *
              ‖iteratedFDeriv ℝ (3 - 1) glin z‖ +
          3 * ‖iteratedFDeriv ℝ 2 (fun t : E => χ (A t + b)) z‖ *
              ‖iteratedFDeriv ℝ (3 - 2) glin z‖ +
        ‖iteratedFDeriv ℝ 3 (fun t : E => χ (A t + b)) z‖ *
            ‖iteratedFDeriv ℝ (3 - 3) glin z‖ := by
      norm_num [Finset.sum_range_succ] at hprod'
      exact hprod'
    _ ≤ 3 * (M2 * (ρ⁻¹) ^ 2) * ‖a‖ +
        (M3 * (ρ⁻¹) ^ 3) * (‖a‖ * ρ) := by
      rw [hlin3 z, hlin2 z]
      simp only [mul_zero, add_zero, zero_add]
      gcongr
      · exact hcomp2 z
      · exact hlin1 z
      · exact hcomp3 z
    _ = (M3 + 3 * M2) * ‖a‖ / ρ ^ 2 := by
      field_simp [hρ.ne']
      ring

/-- Helper for eq:holder-hessian-bound: a uniform third-derivative bound yields a
Lipschitz estimate for the second Fréchet derivative. -/
theorem norm_hessian_sub_le_of_thirdFDeriv
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {f : E → ℝ} {B : ℝ} (hf : ContDiff ℝ (3 : WithTop ℕ∞) f)
    (hbound : ∀ z, ‖iteratedFDeriv ℝ 3 f z‖ ≤ B) (x y : E) :
    ‖fderiv ℝ (fderiv ℝ f) y - fderiv ℝ (fderiv ℝ f) x‖ ≤ B * ‖y - x‖ := by
  have horder₁ : (2 : WithTop ℕ∞) + 1 ≤ (3 : WithTop ℕ∞) := by norm_num
  have hf2 : ContDiff ℝ (2 : WithTop ℕ∞) (fderiv ℝ f) :=
    hf.fderiv_right horder₁
  have horder₂ : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞) := by norm_num
  have hf1 : ContDiff ℝ (1 : WithTop ℕ∞) (fderiv ℝ (fderiv ℝ f)) :=
    hf2.fderiv_right horder₂
  have hbound' : ∀ z, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ f)) z‖ ≤ B := by
    intro z
    calc
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ f)) z‖ =
          ‖iteratedFDeriv ℝ 1 (fderiv ℝ (fderiv ℝ f)) z‖ :=
        (norm_iteratedFDeriv_one (𝕜 := ℝ) (fderiv ℝ (fderiv ℝ f))).symm
      _ = ‖iteratedFDeriv ℝ 2 (fderiv ℝ f) z‖ := by
        rw [norm_iteratedFDeriv_fderiv]
      _ = ‖iteratedFDeriv ℝ 3 f z‖ := by
        rw [norm_iteratedFDeriv_fderiv]
      _ ≤ B := hbound z
  exact Convex.norm_image_sub_le_of_norm_fderiv_le
    (s := Set.univ) (f := fderiv ℝ (fderiv ℝ f)) (C := B) (x := x) (y := y)
    (fun z _ ↦ hf1.differentiable_one z) (fun z _ ↦ hbound' z) convex_univ
    (Set.mem_univ x) (Set.mem_univ y)
/-- Helper for eq:holder-hessian-bound: the Hessian of each endpoint bump is
Lipschitz with the inverse scale predicted by the shrinking construction. -/
theorem endpointBumpHessianLipschitz
    (curve : DFP.TwoLeg.SlowCurve) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ K > 0,
      ∀ ε₀ ∈ Set.Ioc 0 εbar,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
        ∀ Clim : EuclideanSpace ℝ (Fin 2),
          Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
            ∀ Glim > 0,
              Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) →
                ∀ k z w,
                  ‖fderiv ℝ (fderiv ℝ (orbit.endpointBump Clim Glim k)) z -
                      fderiv ℝ (fderiv ℝ (orbit.endpointBump Clim Glim k)) w‖ ≤
                    K / (orbit.state (k / 2)).ε * ‖z - w‖ := by
  obtain ⟨ηRadius, hηRadius, cLower, hcLower, cUpper, hcUpper,
      hRadius⟩ := curve.interpolationRadiusUniformBounds
  obtain ⟨ηCorrection, hηCorrection, Kcorrection, hKcorrection,
      hCorrection⟩ := DFP.TwoPhaseOrbit.slowCurveEndpointCorrectionUniformBound
    curve.shape curve.high curve.isInvariant curve.shapeRemainder curve.highRemainder
  obtain ⟨ηPos, hηPos, hPos⟩ := DFP.TwoLeg.slowCurveForwardOrbitPos
    curve.shape curve.high curve.isInvariant curve.shapeRemainder curve.highRemainder
  let εbar := min ηRadius (min ηCorrection ηPos)
  have hεbarPos : 0 < εbar := by
    dsimp only [εbar]
    exact lt_min hηRadius.1 (lt_min hηCorrection.1 hηPos)
  have hεbarLt : εbar < (1 / 4 : ℝ) :=
    (min_le_left _ _).trans_lt hηRadius.2
  let M0 := EuclideanPlane.smoothCutoffDerivBound 0
  let M2 := EuclideanPlane.smoothCutoffDerivBound 2
  let M3 := EuclideanPlane.smoothCutoffDerivBound 3
  have hM2 : 0 ≤ M2 := by
    dsimp only [M2]
    exact EuclideanPlane.smoothCutoffDerivBound_nonneg 2
  have hM3 : 0 ≤ M3 := by
    dsimp only [M3]
    exact EuclideanPlane.smoothCutoffDerivBound_nonneg 3
  let Kthird := (M3 + 3 * M2) * Kcorrection / cLower ^ 2
  let K := Kthird + 1
  have hKthird : 0 ≤ Kthird := by
    dsimp only [Kthird]
    positivity
  have hK : 0 < K := by
    dsimp only [K]
    linarith
  refine ⟨εbar, ⟨hεbarPos, hεbarLt⟩, K, hK, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
  have hεRadius : ε₀ ∈ Set.Ioc 0 ηRadius :=
    ⟨hε₀.1, hε₀.2.trans (min_le_left _ _ )⟩
  have hεCorrection : ε₀ ∈ Set.Ioc 0 ηCorrection :=
    ⟨hε₀.1, hε₀.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hεPos : ε₀ ∈ Set.Ioc 0 ηPos :=
    ⟨hε₀.1, hε₀.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  intro Clim hClim Glim hGlim hGlimTendsto k z w
  have hRadiusData := hRadius ε₀ hεRadius Clim hClim Glim hGlim hGlimTendsto k
  have hCorrectionData := hCorrection ε₀ hεCorrection Clim hClim k
  have hcoord (j : ℕ) :
      (orbit.state j).ε =
        (DFP.TwoLeg.stateMap^[j]
          (ε₀, curve.shape ε₀, curve.high ε₀)).1 := by
    have hc := DFP.TwoPhaseOrbit.ofSlowCurve_coordinates
      curve.shape curve.high ε₀ j
    have hc' : (orbit.state j).coordinates =
        DFP.TwoLeg.stateMap^[j]
          (ε₀, curve.shape ε₀, curve.high ε₀) := by
      simpa only [orbit] using hc
    simpa only [DFP.TwoPhaseOrbit.State.coordinates_def] using
      congrArg Prod.fst hc'
  have hscalePos (j : ℕ) : 0 < (orbit.state j).ε := by
    rw [hcoord j]
    exact (hPos ε₀ hεPos j).1
  let e := (orbit.state (k / 2)).ε
  let R := orbit.endpointRadius k
  let ρ := orbit.interpolationRadius Clim Glim k
  let a := orbit.endpointCorrection Clim k
  have he : 0 < e := by
    simpa only [e] using hscalePos (k / 2)
  have hR : R = e ^ 2 := by
    simpa only [R, e] using DFP.TwoPhaseOrbit.endpointRadius_def orbit k
  have hRpos : 0 < R := by
    rw [hR]
    positivity
  have hρLower : cLower * R ≤ ρ := by
    simpa only [ρ, R] using hRadiusData.1
  have hρ : 0 < ρ := by
    exact (mul_pos hcLower hRpos).trans_le hρLower
  have ha : ‖a‖ ≤ Kcorrection * e ^ 3 := by
    simpa only [a, e] using hCorrectionData
  have hthree : (3 : WithTop ℕ∞) ≤ ∞ := by
    have hnat : (3 : ℕ∞) ≤ ⊤ := le_top
    exact WithTop.coe_le_coe.mpr hnat
  have hcutoff : ContDiff ℝ (3 : WithTop ℕ∞) EuclideanPlane.smoothCutoff := by
    exact EuclideanPlane.contDiff_smoothCutoff.of_le hthree
  have hcoef : 0 ≤ M3 + 3 * M2 := by positivity
  have hρLower' : cLower * e ^ 2 ≤ ρ := by
    simpa only [hR] using hρLower
  have hρsq : (cLower * e ^ 2) ^ 2 ≤ ρ ^ 2 := by
    exact pow_le_pow_left₀ (mul_nonneg hcLower.le (sq_nonneg e)) hρLower' 2
  have hρsqPos : 0 < ρ ^ 2 := pow_pos hρ 2
  have hthird : ∀ u, ‖iteratedFDeriv ℝ 3
      (orbit.endpointBump Clim Glim k) u‖ ≤ Kthird / e := by
    intro u
    by_cases hu : u ∈ tsupport (orbit.endpointBump Clim Glim k)
    · have hbase := norm_iteratedFDeriv_three_scaledLinearBump_le
        EuclideanPlane.smoothCutoff hcutoff
        (fun y ↦ by simpa only [M0] using EuclideanPlane.norm_smoothCutoff_le y)
        (fun y ↦ by
          simpa only [M2] using EuclideanPlane.norm_iteratedFDeriv_smoothCutoff_le 2 y)
        (fun y ↦ by
          simpa only [M3] using EuclideanPlane.norm_iteratedFDeriv_smoothCutoff_le 3 y)
        EuclideanPlane.tsupport_smoothCutoff_subset (orbit.endpoint k) ρ a u hρ
        (by simpa only [DFP.TwoPhaseOrbit.endpointBump_eq_scaledLinearBump] using hu)
      rw [DFP.TwoPhaseOrbit.endpointBump_eq_scaledLinearBump]
      change ‖iteratedFDeriv ℝ 3
          (AffineBump.scaledLinearBump EuclideanPlane.smoothCutoff
            (orbit.endpoint k) ρ a) u‖ ≤ Kthird / e
      calc
        ‖iteratedFDeriv ℝ 3
            (AffineBump.scaledLinearBump EuclideanPlane.smoothCutoff
              (orbit.endpoint k) ρ a) u‖ ≤
            (M3 + 3 * M2) * ‖a‖ / ρ ^ 2 := by
          simpa only [M3, M2] using hbase
        _ ≤ Kthird / e := by
          apply (div_le_iff₀ hρsqPos).2
          calc
            (M3 + 3 * M2) * ‖a‖ ≤
            (M3 + 3 * M2) * (Kcorrection * e ^ 3) :=
          mul_le_mul_of_nonneg_left ha hcoef
        _ = (Kthird / e) * (cLower * e ^ 2) ^ 2 := by
          dsimp only [Kthird]
          field_simp [hcLower.ne', he.ne']
        _ ≤ (Kthird / e) * ρ ^ 2 := by
          exact mul_le_mul_of_nonneg_left hρsq
            (div_nonneg hKthird (le_of_lt he))
    · rw [iteratedFDeriv_eq_zero_of_notMem_tsupport
        (orbit.endpointBump Clim Glim k) 3 hu, norm_zero]
      exact div_nonneg hKthird (le_of_lt he)
  have hf3 : ContDiff ℝ (3 : WithTop ℕ∞)
      (orbit.endpointBump Clim Glim k) := by
    exact (DFP.TwoPhaseOrbit.contDiff_endpointBump orbit Clim Glim k).of_le
      hthree
  have hL := norm_hessian_sub_le_of_thirdFDeriv hf3 hthird w z
  calc
    ‖fderiv ℝ (fderiv ℝ (orbit.endpointBump Clim Glim k)) z -
        fderiv ℝ (fderiv ℝ (orbit.endpointBump Clim Glim k)) w‖ ≤
        Kthird / e * ‖z - w‖ := hL
    _ ≤ K / e * ‖z - w‖ := by
      gcongr
      dsimp only [K]
      linarith
/-- Helper for eq:holder-hessian-bound: the minimum of a uniform size bound and an
inverse-scale Lipschitz bound has the square-root interpolation estimate used in the bump sum. -/
theorem min_scaled_le_sqrt
    {A B e d : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (he : 0 < e) (hd : 0 ≤ d) :
    min (2 * A * e) (B / e * d) ≤ Real.sqrt (2 * A * B) * Real.sqrt d := by
  by_cases hd0 : d = 0
  · subst d
    simp only [mul_zero, Real.sqrt_zero, mul_zero]
    simp
  have hdpos : 0 < d := lt_of_le_of_ne hd (Ne.symm hd0)
  have hsqrtAB : 0 ≤ Real.sqrt (2 * A * B) := Real.sqrt_nonneg _
  have hsqrtd : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hsqAB : (Real.sqrt (2 * A * B)) ^ 2 = 2 * A * B := by
    rw [Real.sq_sqrt]
    positivity
  have hsqd : (Real.sqrt d) ^ 2 = d := by
    rw [Real.sq_sqrt hd]
  have hsqrtProd : (Real.sqrt (2 * A * B) * Real.sqrt d) ^ 2 =
      2 * A * B * d := by
    calc
      (Real.sqrt (2 * A * B) * Real.sqrt d) ^ 2 =
          (Real.sqrt (2 * A * B)) ^ 2 * (Real.sqrt d) ^ 2 := by rw [mul_pow]
      _ = 2 * A * B * d := by rw [hsqAB, hsqd]
  by_cases hab : 2 * A * e ≤ B / e * d
  · apply le_trans (le_of_eq (min_eq_left hab))
    have hmul : (2 * A * e) * (2 * A * e) ≤
        (B / e * d) * (2 * A * e) :=
      mul_le_mul_of_nonneg_right hab (by positivity)
    have hsq : (2 * A * e) ^ 2 ≤
        (Real.sqrt (2 * A * B) * Real.sqrt d) ^ 2 := by
      rw [hsqrtProd]
      calc
        (2 * A * e) ^ 2 ≤ (B / e * d) * (2 * A * e) := by
          simpa only [pow_two] using hmul
        _ = 2 * A * B * d := by
          field_simp [he.ne']
    exact le_of_sq_le_sq hsq (by positivity)
  · have hba : B / e * d ≤ 2 * A * e := le_of_not_ge hab
    apply le_trans (le_of_eq (min_eq_right hba))
    have hmul : (B / e * d) * (B / e * d) ≤
        (2 * A * e) * (B / e * d) :=
      mul_le_mul_of_nonneg_right hba (by positivity)
    have hsq : (B / e * d) ^ 2 ≤
        (Real.sqrt (2 * A * B) * Real.sqrt d) ^ 2 := by
      rw [hsqrtProd]
      calc
        (B / e * d) ^ 2 ≤ (2 * A * e) * (B / e * d) := by
          simpa only [pow_two] using hmul
        _ = 2 * A * B * d := by
          field_simp [he.ne']
    exact le_of_sq_le_sq hsq (by positivity)

/-- Helper for eq:holder-hessian-bound: equality of second Fréchet derivatives follows
from equality of the corresponding second iterated derivatives. -/
theorem fderiv_fderiv_eq_of_iteratedFDeriv_two_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {x : E}
    (h : iteratedFDeriv ℝ 2 f x = iteratedFDeriv ℝ 2 g x) :
    fderiv ℝ (fderiv ℝ f) x = fderiv ℝ (fderiv ℝ g) x := by
  ext u v
  have h' := congrArg (fun T => T ![u, v]) h
  simpa [iteratedFDeriv_two_apply] using h'

/-- Helper for eq:holder-hessian-bound: disjoint shrinking bumps with a uniform local
square-root Hessian modulus have the same modulus after zero-extension. -/
theorem holder_of_disjoint_finsum_hessian
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (Γ : Set E) (x : ℕ → E) (ρ : ℕ → ℝ) (ψ : ℕ → E → ℝ) (F : E → ℝ) (L : ℝ)
    (hΓ : IsClosed Γ)
    (hcluster : ∀ y, MapClusterPt y atTop x → y ∈ Γ)
    (hρ0 : Tendsto ρ atTop (𝓝 0))
    (hballs : Set.univ.PairwiseDisjoint (fun k ↦ Metric.closedBall (x k) (ρ k)))
    (hsupport : ∀ k, tsupport (ψ k) ⊆ Metric.closedBall (x k) (ρ k))
    (hdisjointΓ : ∀ k, Disjoint (tsupport (ψ k)) Γ)
    (hHessianEq : fderiv ℝ (fderiv ℝ F) =
      Γᶜ.indicator (fderiv ℝ (fderiv ℝ (fun z ↦ ∑ᶠ k, ψ k z))))
    (hlocal : ∀ k u v, ‖fderiv ℝ (fderiv ℝ (ψ k)) u -
        fderiv ℝ (fderiv ℝ (ψ k)) v‖ ≤ L * ‖u - v‖ ^ (1 / 2 : ℝ))
    (hL : 0 ≤ L) (u v : E) :
    ‖fderiv ℝ (fderiv ℝ F) u - fderiv ℝ (fderiv ℝ F) v‖ ≤
      2 * L * ‖u - v‖ ^ (1 / 2 : ℝ) := by
  have hsumHessianAt : ∀ z, z ∈ Γᶜ →
      (∃ k, z ∈ tsupport (ψ k)) → ∀ k, z ∈ tsupport (ψ k) →
        fderiv ℝ (fderiv ℝ (fun y ↦ ∑ᶠ n, ψ n y)) z =
          fderiv ℝ (fderiv ℝ (ψ k)) z := by
    intro z hzΓ hactive k hzk
    have hz0 := iteratedFDeriv_finsum_eq_of_mem_tsupport Γ x ρ ψ hcluster hρ0 hballs
      hsupport hzΓ hzk (j := 2)
    exact fderiv_fderiv_eq_of_iteratedFDeriv_two_eq hz0
  have hsumHessianZero : ∀ z, z ∈ Γᶜ →
      (¬ ∃ k, z ∈ tsupport (ψ k)) →
      fderiv ℝ (fderiv ℝ (fun y ↦ ∑ᶠ n, ψ n y)) z = 0 := by
    intro z hzΓ hna
    have hz0 := iteratedFDeriv_finsum_eq_zero Γ x ρ ψ hcluster hρ0 hsupport hzΓ
      (fun k ↦ fun hzk ↦ hna ⟨k, hzk⟩) (j := 2)
    have hz0' : iteratedFDeriv ℝ 2 (fun y ↦ ∑ᶠ n, ψ n y) z =
        iteratedFDeriv ℝ 2 (fun _ : E ↦ (0 : ℝ)) z := by
      simpa using hz0
    exact (fderiv_fderiv_eq_of_iteratedFDeriv_two_eq hz0').trans (by simp)
  have hzero (k : ℕ) (z : E) (hz : z ∉ tsupport (ψ k)) :
      fderiv ℝ (fderiv ℝ (ψ k)) z = 0 := by
    have hz0 : iteratedFDeriv ℝ 2 (ψ k) z =
        iteratedFDeriv ℝ 2 (fun _ : E ↦ (0 : ℝ)) z := by
      rw [iteratedFDeriv_eq_zero_of_notMem_tsupport (ψ k) 2 hz]
      simp
    exact (fderiv_fderiv_eq_of_iteratedFDeriv_two_eq hz0).trans (by simp)
  have hglobalCircle (z : E) (hz : z ∈ Γ) :
      fderiv ℝ (fderiv ℝ F) z = 0 := by
    rw [hHessianEq]
    simp [hz]
  have hglobalActive (z : E) (hzΓ : z ∈ Γᶜ) (k : ℕ)
      (hzk : z ∈ tsupport (ψ k)) :
      fderiv ℝ (fderiv ℝ F) z = fderiv ℝ (fderiv ℝ (ψ k)) z := by
    rw [hHessianEq]
    simp only [Set.indicator_of_mem hzΓ]
    exact hsumHessianAt z hzΓ ⟨k, hzk⟩ k hzk
  have hglobalZero (z : E) (hzΓ : z ∈ Γᶜ)
      (hna : ¬ ∃ k, z ∈ tsupport (ψ k)) :
      fderiv ℝ (fderiv ℝ F) z = 0 := by
    rw [hHessianEq]
    simp only [Set.indicator_of_mem hzΓ]
    exact hsumHessianZero z hzΓ hna
  have hglobalNoActive (z : E) (hna : ¬ ∃ k, z ∈ tsupport (ψ k)) :
      fderiv ℝ (fderiv ℝ F) z = 0 := by
    by_cases hzΓ : z ∈ Γ
    · exact hglobalCircle z hzΓ
    · exact hglobalZero z hzΓ hna
  by_cases hu : ∃ k, u ∈ tsupport (ψ k)
  · obtain ⟨ku, hku⟩ := hu
    have huΓ : u ∉ Γ := by
      intro huΓ
      exact Set.disjoint_left.mp (hdisjointΓ ku) hku huΓ
    by_cases hv : ∃ k, v ∈ tsupport (ψ k)
    · obtain ⟨kv, hkv⟩ := hv
      have hvΓ : v ∉ Γ := by
        intro hvΓ
        exact Set.disjoint_left.mp (hdisjointΓ kv) hkv hvΓ
      have huΓ' : u ∈ Γᶜ := huΓ
      have hvΓ' : v ∈ Γᶜ := hvΓ
      by_cases hEq : ku = kv
      · subst kv
        rw [hglobalActive u huΓ' ku hku, hglobalActive v hvΓ' ku hkv]
        calc
          ‖fderiv ℝ (fderiv ℝ (ψ ku)) u -
              fderiv ℝ (fderiv ℝ (ψ ku)) v‖ ≤
              L * ‖u - v‖ ^ (1 / 2 : ℝ) := hlocal ku u v
          _ ≤ 2 * L * ‖u - v‖ ^ (1 / 2 : ℝ) := by
            exact mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (norm_nonneg _) _)
      · have hkv_u : u ∉ tsupport (ψ kv) := by
          intro hkuv
          have heq := hballs.elim_set (Set.mem_univ ku) (Set.mem_univ kv) u
            (hsupport ku hku) (hsupport kv hkuv)
          exact hEq heq
        have hku_v : v ∉ tsupport (ψ ku) := by
          intro hkuv
          have heq := hballs.elim_set (Set.mem_univ ku) (Set.mem_univ kv) v
            (hsupport ku hkuv) (hsupport kv hkv)
          exact hEq heq
        rw [hglobalActive u huΓ' ku hku, hglobalActive v hvΓ' kv hkv]
        let Hk := fderiv ℝ (fderiv ℝ (ψ ku))
        let Hl := fderiv ℝ (fderiv ℝ (ψ kv))
        have hkuZero := hzero ku v hku_v
        have hkvZero := hzero kv u hkv_u
        change ‖Hk u - Hl v‖ ≤ _
        calc
          ‖Hk u - Hl v‖ ≤ ‖Hk u - 0‖ + ‖0 - Hl v‖ := by
            convert norm_add_le (Hk u - 0) (0 - Hl v) using 1 <;> abel
          _ = ‖Hk u - Hk v‖ + ‖Hl u - Hl v‖ := by
            dsimp [Hk, Hl]
            rw [hkuZero, hkvZero]
          _ ≤ L * ‖u - v‖ ^ (1 / 2 : ℝ) +
              L * ‖u - v‖ ^ (1 / 2 : ℝ) :=
            add_le_add (hlocal ku u v) (hlocal kv u v)
          _ = 2 * L * ‖u - v‖ ^ (1 / 2 : ℝ) := by ring
    · rw [hglobalActive u huΓ ku hku, hglobalNoActive v hv]
      let Hk := fderiv ℝ (fderiv ℝ (ψ ku))
      have hkuZero := hzero ku v (fun hvk ↦ hv ⟨ku, hvk⟩)
      change ‖Hk u - 0‖ ≤ _
      calc
        ‖Hk u - 0‖ = ‖Hk u - Hk v‖ := by
          dsimp [Hk]
          rw [hkuZero]
        _ ≤ L * ‖u - v‖ ^ (1 / 2 : ℝ) := hlocal ku u v
        _ ≤ 2 * L * ‖u - v‖ ^ (1 / 2 : ℝ) := by
          exact mul_le_mul_of_nonneg_right (by linarith)
            (Real.rpow_nonneg (norm_nonneg _) _)
  · by_cases hv : ∃ k, v ∈ tsupport (ψ k)
    · obtain ⟨kv, hkv⟩ := hv
      have hvΓ : v ∉ Γ := by
        intro hvΓ
        exact Set.disjoint_left.mp (hdisjointΓ kv) hkv hvΓ
      rw [hglobalNoActive u hu, hglobalActive v hvΓ kv hkv]
      let Hk := fderiv ℝ (fderiv ℝ (ψ kv))
      have hkvZero := hzero kv u (fun huk ↦ hu ⟨kv, huk⟩)
      change ‖0 - Hk v‖ ≤ _
      calc
        ‖0 - Hk v‖ = ‖Hk u - Hk v‖ := by
          dsimp [Hk]
          rw [hkvZero]
        _ ≤ L * ‖u - v‖ ^ (1 / 2 : ℝ) := hlocal kv u v
        _ ≤ 2 * L * ‖u - v‖ ^ (1 / 2 : ℝ) := by
          exact mul_le_mul_of_nonneg_right (by linarith)
            (Real.rpow_nonneg (norm_nonneg _) _)
    · rw [hglobalNoActive u hu, hglobalNoActive v hv]
      simpa only [sub_self, norm_zero] using
        (mul_nonneg (mul_nonneg (by norm_num) hL)
          (Real.rpow_nonneg (norm_nonneg _) _))


/-- Helper for eq:holder-hessian-bound: the endpoint-bump family has a uniform local
square-root Hessian modulus after combining its scale and inverse-scale estimates. -/
theorem endpointBumpHessianHolder (curve : DFP.TwoLeg.SlowCurve) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ L > 0,
      ∀ ε₀ ∈ Set.Ioc 0 εbar,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
        ∀ Clim : EuclideanSpace ℝ (Fin 2),
          Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
            ∀ Glim > 0,
              Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) →
                ∀ k u v,
                  ‖fderiv ℝ (fderiv ℝ (orbit.endpointBump Clim Glim k)) u -
                      fderiv ℝ (fderiv ℝ (orbit.endpointBump Clim Glim k)) v‖ ≤
                    L * ‖u - v‖ ^ (1 / 2 : ℝ) := by
  obtain ⟨ηLip, hηLip, KLip, hKLip, hLip⟩ := endpointBumpHessianLipschitz curve
  obtain ⟨ηBounds, hηBounds, Kvalue, hKvalue, Kgradient, hKgradient,
      Khessian, hKhessian, hBounds⟩ := curve.endpointBumpUniformBounds
  obtain ⟨ηPos, hηPos, hPos⟩ := DFP.TwoLeg.slowCurveForwardOrbitPos
    curve.shape curve.high curve.isInvariant curve.shapeRemainder curve.highRemainder
  let εbar := min ηLip (min ηBounds ηPos)
  have hεbarPos : 0 < εbar := by
    dsimp only [εbar]
    exact lt_min hηLip.1 (lt_min hηBounds.1 hηPos)
  have hεbarLt : εbar < (1 / 4 : ℝ) :=
    (min_le_left _ _).trans_lt hηLip.2
  let L := Real.sqrt (2 * Khessian * KLip)
  have hL : 0 < L := by
    dsimp only [L]
    have hprod : 0 < 2 * Khessian * KLip := by positivity
    exact Real.sqrt_pos.2 hprod
  refine ⟨εbar, ⟨hεbarPos, hεbarLt⟩, L, hL, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
  have hεLip : ε₀ ∈ Set.Ioc 0 ηLip :=
    ⟨hε₀.1, hε₀.2.trans (min_le_left _ _ )⟩
  have hεBounds : ε₀ ∈ Set.Ioc 0 ηBounds :=
    ⟨hε₀.1, hε₀.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hεPos : ε₀ ∈ Set.Ioc 0 ηPos :=
    ⟨hε₀.1, hε₀.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  intro Clim hClim Glim hGlim hGlimTendsto k u v
  have hLipData := hLip ε₀ hεLip Clim hClim Glim hGlim hGlimTendsto k u v
  have hBoundsData := hBounds ε₀ hεBounds Clim hClim Glim hGlim hGlimTendsto
  have hcoord (j : ℕ) :
      (orbit.state j).ε =
        (DFP.TwoLeg.stateMap^[j]
          (ε₀, curve.shape ε₀, curve.high ε₀)).1 := by
    have hc := DFP.TwoPhaseOrbit.ofSlowCurve_coordinates
      curve.shape curve.high ε₀ j
    have hc' : (orbit.state j).coordinates =
        DFP.TwoLeg.stateMap^[j]
          (ε₀, curve.shape ε₀, curve.high ε₀) := by
      simpa only [orbit] using hc
    simpa only [DFP.TwoPhaseOrbit.State.coordinates_def] using
      congrArg Prod.fst hc'
  have hscalePos (j : ℕ) : 0 < (orbit.state j).ε := by
    rw [hcoord j]
    exact (hPos ε₀ hεPos j).1
  let e := (orbit.state (k / 2)).ε
  have he : 0 < e := by
    simpa only [e] using hscalePos (k / 2)
  have hHessBound (z : EuclideanSpace ℝ (Fin 2)) :
      ‖fderiv ℝ (fderiv ℝ (orbit.endpointBump Clim Glim k)) z‖ ≤ Khessian * e := by
    by_cases hz : z ∈ tsupport (orbit.endpointBump Clim Glim k)
    · simpa only [e] using (hBoundsData k z hz).2.2
    · have hz0 : iteratedFDeriv ℝ 2 (orbit.endpointBump Clim Glim k) z =
          iteratedFDeriv ℝ 2 (fun _ : EuclideanSpace ℝ (Fin 2) ↦ (0 : ℝ)) z := by
        rw [iteratedFDeriv_eq_zero_of_notMem_tsupport
          (orbit.endpointBump Clim Glim k) 2 hz]
        simp
      have hzero := fderiv_fderiv_eq_of_iteratedFDeriv_two_eq hz0
      rw [hzero]
      simpa only [fderiv_fun_const, fderiv_zero, Pi.zero_apply, norm_zero, ge_iff_le] using
        (mul_nonneg hKhessian.le (le_of_lt he))
  have hmin :
      ‖fderiv ℝ (fderiv ℝ (orbit.endpointBump Clim Glim k)) u -
          fderiv ℝ (fderiv ℝ (orbit.endpointBump Clim Glim k)) v‖ ≤
        min (2 * Khessian * e) (KLip / e * ‖u - v‖) := by
    refine le_min ?_ ?_
    · calc
        ‖fderiv ℝ (fderiv ℝ (orbit.endpointBump Clim Glim k)) u -
            fderiv ℝ (fderiv ℝ (orbit.endpointBump Clim Glim k)) v‖ ≤
            ‖fderiv ℝ (fderiv ℝ (orbit.endpointBump Clim Glim k)) u‖ +
              ‖fderiv ℝ (fderiv ℝ (orbit.endpointBump Clim Glim k)) v‖ :=
          norm_sub_le _ _
        _ ≤ Khessian * e + Khessian * e :=
          add_le_add (hHessBound u) (hHessBound v)
        _ = 2 * Khessian * e := by ring
    · exact hLipData
  calc
    ‖fderiv ℝ (fderiv ℝ (orbit.endpointBump Clim Glim k)) u -
        fderiv ℝ (fderiv ℝ (orbit.endpointBump Clim Glim k)) v‖ ≤
        min (2 * Khessian * e) (KLip / e * ‖u - v‖) := hmin
    _ ≤ Real.sqrt (2 * Khessian * KLip) * Real.sqrt ‖u - v‖ := by
      exact min_scaled_le_sqrt (A := Khessian) (B := KLip) (e := e)
        (d := ‖u - v‖) hKhessian.le hKLip.le he (norm_nonneg _)
    _ = L * ‖u - v‖ ^ (1 / 2 : ℝ) := by
      dsimp only [L]
      simp only [Real.sqrt_eq_rpow]


/-- Helper for eq:holder-hessian-bound: the Euclidean-plane Hessian norm of a difference
agrees with the norm of the corresponding difference of second Fréchet derivatives. -/
theorem norm_euclideanHessian_sub_eq_norm_secondFDeriv_sub
    (f : EuclideanSpace ℝ (Fin 2) → ℝ) (x y : EuclideanSpace ℝ (Fin 2)) :
    ‖EuclideanPlane.hessian f x - EuclideanPlane.hessian f y‖ =
      ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y‖ := by
  let E := EuclideanSpace ℝ (Fin 2)
  let R : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearMap
  have hRiesz (z : E) :
      fderiv ℝ (gradient f) z = R ∘L fderiv ℝ (fderiv ℝ f) z := by
    unfold gradient
    have hfun :
        (fun w ↦ (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f w)) =
          (InnerProductSpace.toDual ℝ E).symm ∘ fderiv ℝ f := rfl
    rw [hfun]
    exact LinearIsometryEquiv.comp_fderiv
      (InnerProductSpace.toDual ℝ E).symm
  rw [EuclideanPlane.hessian_def f x, EuclideanPlane.hessian_def f y,
    hRiesz x, hRiesz y]
  have hcomp : R ∘L fderiv ℝ (fderiv ℝ f) x -
      R ∘L fderiv ℝ (fderiv ℝ f) y =
      R ∘L (fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y) := by
    ext u v
    simp [ContinuousLinearMap.comp_apply]
  rw [hcomp]
  exact LinearIsometry.norm_toContinuousLinearMap_comp
    (InnerProductSpace.toDual ℝ E).symm.toLinearIsometry


/-- Helper for eq:holder-hessian-bound: the full endpoint-bump correction has a global
one-half Hölder Hessian modulus after zero-extension across the limit circle. -/
theorem bumpCorrectionHessianHolder (curve : DFP.TwoLeg.SlowCurve) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ L > 0,
      ∀ ε₀ ∈ Set.Ioc 0 εbar,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
        ∀ Clim : EuclideanSpace ℝ (Fin 2),
          Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
            ∀ Glim > 0,
              Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) →
                ∀ u v,
                  ‖EuclideanPlane.hessian (orbit.bumpCorrection Clim Glim) u -
                      EuclideanPlane.hessian (orbit.bumpCorrection Clim Glim) v‖ ≤
                    L * ‖u - v‖ ^ (1 / 2 : ℝ) := by
  obtain ⟨ηRadius, hηRadius, hRadius⟩ := curve.interpolationRadius_pos
  obtain ⟨ηShrink, hηShrink, hShrink⟩ := curve.interpolationRadiusTendstoZero
  obtain ⟨ηCluster, hηCluster, hCluster⟩ := curve.endpointClusterPt_mem_limitCircle
  obtain ⟨ηBalls, hηBalls, hBalls⟩ := curve.pairwiseDisjointInterpolationClosedBalls
  obtain ⟨ηCircle, hηCircle, hCircle⟩ :=
    curve.interpolationClosedBallDisjointLimitCircle
  obtain ⟨ηJets, hηJets, hJets⟩ := curve.endpointBumpSecondOrderJetsVanish
  obtain ⟨ηHolder, hηHolder, Llocal, hLlocal, hHolder⟩ :=
    endpointBumpHessianHolder curve
  let εbar := min ηRadius
    (min ηShrink (min ηCluster (min ηBalls (min ηCircle (min ηJets ηHolder)))))
  have hεbarPos : 0 < εbar := by
    dsimp only [εbar]
    exact lt_min hηRadius.1
      (lt_min hηShrink.1 (lt_min hηCluster.1
        (lt_min hηBalls.1 (lt_min hηCircle.1 (lt_min hηJets.1 hηHolder.1)))))
  have hεbarLt : εbar < (1 / 4 : ℝ) :=
    (min_le_left _ _).trans_lt hηRadius.2
  have hεbarLeRadius : εbar ≤ ηRadius := by
    dsimp only [εbar]
    exact min_le_left _ _
  have hεbarLeShrink : εbar ≤ ηShrink := by
    dsimp only [εbar]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hεbarLeCluster : εbar ≤ ηCluster := by
    dsimp only [εbar]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεbarLeBalls : εbar ≤ ηBalls := by
    dsimp only [εbar]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hεbarLeCircle : εbar ≤ ηCircle := by
    dsimp only [εbar]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hεbarLeJets : εbar ≤ ηJets := by
    dsimp only [εbar]
    exact (((((min_le_right _ _).trans (min_le_right _ _)).trans
      (min_le_right _ _)).trans (min_le_right _ _)).trans
      (min_le_right _ _)).trans (min_le_left _ _)
  have hεbarLeHolder : εbar ≤ ηHolder := by
    dsimp only [εbar]
    exact (((((min_le_right _ _).trans (min_le_right _ _)).trans
      (min_le_right _ _)).trans (min_le_right _ _)).trans
      (min_le_right _ _)).trans (min_le_right _ _)
  let L := 2 * Llocal
  have hL : 0 < L := by
    dsimp only [L]
    linarith
  refine ⟨εbar, ⟨hεbarPos, hεbarLt⟩, L, hL, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
  have hεRadius : ε₀ ∈ Set.Ioc 0 ηRadius :=
    ⟨hε₀.1, hε₀.2.trans hεbarLeRadius⟩
  have hεShrink : ε₀ ∈ Set.Ioc 0 ηShrink :=
    ⟨hε₀.1, hε₀.2.trans hεbarLeShrink⟩
  have hεCluster : ε₀ ∈ Set.Ioc 0 ηCluster :=
    ⟨hε₀.1, hε₀.2.trans hεbarLeCluster⟩
  have hεBalls : ε₀ ∈ Set.Ioc 0 ηBalls :=
    ⟨hε₀.1, hε₀.2.trans hεbarLeBalls⟩
  have hεCircle : ε₀ ∈ Set.Ioc 0 ηCircle :=
    ⟨hε₀.1, hε₀.2.trans hεbarLeCircle⟩
  have hεJets : ε₀ ∈ Set.Ioc 0 ηJets :=
    ⟨hε₀.1, hε₀.2.trans hεbarLeJets⟩
  have hεHolder : ε₀ ∈ Set.Ioc 0 ηHolder :=
    ⟨hε₀.1, hε₀.2.trans hεbarLeHolder⟩
  intro Clim hClim Glim hGlim hGlimTendsto u v
  have hRadiusPos : ∀ k : ℕ, 0 < orbit.interpolationRadius Clim Glim k := by
    simpa only [orbit] using
      hRadius ε₀ hεRadius Clim hClim Glim hGlim hGlimTendsto
  have hRadiusZero : Tendsto
      (fun k : ℕ ↦ orbit.interpolationRadius Clim Glim k) atTop (𝓝 0) := by
    simpa only [orbit] using
      hShrink ε₀ hεShrink Clim hClim Glim hGlim hGlimTendsto
  have hBallsData : Set.univ.PairwiseDisjoint (fun k : ℕ ↦
      Metric.closedBall (orbit.endpoint k)
        (orbit.interpolationRadius Clim Glim k)) := by
    simpa only [orbit] using
      hBalls ε₀ hεBalls Clim hClim Glim hGlim hGlimTendsto
  have hCircleData : ∀ k : ℕ, Disjoint
      (Metric.closedBall (orbit.endpoint k)
        (orbit.interpolationRadius Clim Glim k))
      (DFP.TwoPhaseOrbit.limitCircle Clim Glim) := by
    simpa only [orbit] using
      hCircle ε₀ hεCircle Clim hClim Glim hGlim hGlimTendsto
  let Γ : Set (EuclideanSpace ℝ (Fin 2)) :=
    DFP.TwoPhaseOrbit.limitCircle Clim Glim
  have hClosed : IsClosed Γ := by
    simpa only [Γ] using DFP.TwoPhaseOrbit.isClosed_limitCircle Clim Glim hGlim
  have hClusterData : ∀ y, MapClusterPt y atTop orbit.endpoint → y ∈ Γ := by
    intro y hy
    simpa only [Γ, orbit] using
      (hCluster ε₀ hεCluster Clim hClim Glim hGlim hGlimTendsto y hy)
  have hSupport (k : ℕ) : tsupport (orbit.endpointBump Clim Glim k) ⊆
      Metric.closedBall (orbit.endpoint k)
        (orbit.interpolationRadius Clim Glim k) :=
    DFP.TwoPhaseOrbit.endpointBump_tsupport_subset_interpolationClosedBall
      orbit Clim Glim hRadiusPos k
  have hTwoLe : (2 : WithTop ℕ∞) ≤ ∞ := by
    have hTwoNat : (2 : ℕ∞) ≤ ⊤ := le_top
    exact WithTop.coe_le_coe.mpr hTwoNat
  have hSmooth (k : ℕ) : ContDiff ℝ 2 (orbit.endpointBump Clim Glim k) :=
    (DFP.TwoPhaseOrbit.contDiff_endpointBump orbit Clim Glim k).of_le hTwoLe
  have hJetsData := hJets ε₀ hεJets Clim hClim Glim hGlim hGlimTendsto
  have hValueDecay : ∀ η > 0, ∃ δ > 0, ∀ k z,
      z ∈ Γᶜ → z ∈ tsupport (orbit.endpointBump Clim Glim k) →
        Metric.infDist z Γ < δ →
          ‖orbit.endpointBump Clim Glim k z‖ / Metric.infDist z Γ ^ 2 < η := by
    intro η hη
    obtain ⟨δ, hδ, hbound⟩ := hJetsData η hη
    refine ⟨δ, hδ, ?_⟩
    intro k z _ hz hzδ
    simpa only [Γ, orbit] using (hbound k z hz hzδ).1
  have hGradientDecay : ∀ η > 0, ∃ δ > 0, ∀ k z,
      z ∈ Γᶜ → z ∈ tsupport (orbit.endpointBump Clim Glim k) →
        Metric.infDist z Γ < δ →
          ‖fderiv ℝ (orbit.endpointBump Clim Glim k) z‖ /
              Metric.infDist z Γ < η := by
    intro η hη
    obtain ⟨δ, hδ, hbound⟩ := hJetsData η hη
    refine ⟨δ, hδ, ?_⟩
    intro k z _ hz hzδ
    simpa only [Γ, orbit] using (hbound k z hz hzδ).2.1
  have hValueDecayIterated : ∀ η > 0, ∃ δ > 0, ∀ k z,
      z ∈ Γᶜ → z ∈ tsupport (orbit.endpointBump Clim Glim k) →
        Metric.infDist z Γ < δ →
          ‖iteratedFDeriv ℝ 0 (orbit.endpointBump Clim Glim k) z‖ /
              Metric.infDist z Γ ^ 2 < η := by
    intro η hη
    obtain ⟨δ, hδ, hbound⟩ := hValueDecay η hη
    refine ⟨δ, hδ, ?_⟩
    intro k z hzΓ hzk hzδ
    simpa only [norm_iteratedFDeriv_zero] using hbound k z hzΓ hzk hzδ
  have hGradientDecayIterated : ∀ η > 0, ∃ δ > 0, ∀ k z,
      z ∈ Γᶜ → z ∈ tsupport (orbit.endpointBump Clim Glim k) →
        Metric.infDist z Γ < δ →
          ‖iteratedFDeriv ℝ 1 (orbit.endpointBump Clim Glim k) z‖ /
              Metric.infDist z Γ ^ 1 < η := by
    intro η hη
    obtain ⟨δ, hδ, hbound⟩ := hGradientDecay η hη
    refine ⟨δ, hδ, ?_⟩
    intro k z hzΓ hzk hzδ
    simpa only [norm_iteratedFDeriv_one, pow_one] using hbound k z hzΓ hzk hzδ
  have hvalueIterated := tendsto_norm_iteratedFDeriv_finsum_div_infDist_pow
    2 0 2 Γ orbit.endpoint (fun k ↦ orbit.interpolationRadius Clim Glim k)
      (fun k ↦ orbit.endpointBump Clim Glim k) hClosed hClusterData
      (fun k ↦ (hRadiusPos k).le) hRadiusZero hBallsData hSupport hSmooth
      (by omega) hValueDecayIterated
  have hderivIterated := tendsto_norm_iteratedFDeriv_finsum_div_infDist_pow
    2 1 1 Γ orbit.endpoint (fun k ↦ orbit.interpolationRadius Clim Glim k)
      (fun k ↦ orbit.endpointBump Clim Glim k) hClosed hClusterData
      (fun k ↦ (hRadiusPos k).le) hRadiusZero hBallsData hSupport hSmooth
      (by omega) hGradientDecayIterated
  have hvalue : Tendsto
      (fun z ↦ ‖∑ᶠ k, orbit.endpointBump Clim Glim k z‖ /
        Metric.infDist z Γ ^ 2)
      (Filter.comap (fun z ↦ Metric.infDist z Γ) (𝓝 0) ⊓ Filter.principal Γᶜ)
      (𝓝 0) := by
    simpa only [norm_iteratedFDeriv_zero] using hvalueIterated
  have hderiv : Tendsto
      (fun z ↦ ‖fderiv ℝ (fun w ↦ ∑ᶠ k, orbit.endpointBump Clim Glim k w) z‖ /
        Metric.infDist z Γ)
      (Filter.comap (fun z ↦ Metric.infDist z Γ) (𝓝 0) ⊓ Filter.principal Γᶜ)
      (𝓝 0) := by
    simpa only [norm_iteratedFDeriv_one, pow_one] using hderivIterated
  have hsmoothOutside : ContDiffOn ℝ 2
      (fun z ↦ ∑ᶠ k, orbit.endpointBump Clim Glim k z) Γᶜ :=
    contDiffOn_finsum_outside 2 Γ orbit.endpoint
      (fun k ↦ orbit.interpolationRadius Clim Glim k)
      (fun k ↦ orbit.endpointBump Clim Glim k) hClosed hClusterData hRadiusZero
      hSupport hSmooth
  have hFderivEq := IsClosed.fderiv_fderiv_indicator_compl Γ
      (fun z ↦ ∑ᶠ k, orbit.endpointBump Clim Glim k z) hClosed hsmoothOutside
      hvalue hderiv
  have hFunctionEq :
      Γᶜ.indicator (fun z ↦ ∑ᶠ k, orbit.endpointBump Clim Glim k z) =
        orbit.bumpCorrection Clim Glim := by
    funext z
    by_cases hz : z ∈ Γ
    · have hzComplement : z ∉ Γᶜ := by
        simpa only [Set.mem_compl_iff, not_not] using hz
      rw [Set.indicator_of_notMem hzComplement]
      have hZero (k : ℕ) : orbit.endpointBump Clim Glim k z = 0 := by
        by_contra hk
        have hzSupport : z ∈ tsupport (orbit.endpointBump Clim Glim k) :=
          subset_tsupport (orbit.endpointBump Clim Glim k) hk
        have hzBall := hSupport k hzSupport
        exact Set.disjoint_left.mp (hCircleData k) hzBall hz
      rw [DFP.TwoPhaseOrbit.bumpCorrection_apply]
      exact (finsum_eq_zero_of_forall_eq_zero (fun k ↦ hZero k)).symm
    · have hzComplement : z ∈ Γᶜ := by
        simpa only [Set.mem_compl_iff] using hz
      rw [Set.indicator_of_mem hzComplement]
      exact (DFP.TwoPhaseOrbit.bumpCorrection_apply orbit Clim Glim z).symm
  have hHessianEq :
      fderiv ℝ (fderiv ℝ (orbit.bumpCorrection Clim Glim)) =
        Γᶜ.indicator (fderiv ℝ (fderiv ℝ
          (fun z ↦ ∑ᶠ k, orbit.endpointBump Clim Glim k z))) := by
    calc
      fderiv ℝ (fderiv ℝ (orbit.bumpCorrection Clim Glim)) =
          fderiv ℝ (fderiv ℝ
            (Γᶜ.indicator (fun z ↦ ∑ᶠ k, orbit.endpointBump Clim Glim k z))) := by
        rw [hFunctionEq]
      _ = _ := hFderivEq
  have hdisjointΓ : ∀ k, Disjoint
      (tsupport (orbit.endpointBump Clim Glim k)) Γ := by
    intro k
    exact Set.disjoint_of_subset_left (hSupport k) (hCircleData k)
  have hlocal : ∀ k a b, ‖fderiv ℝ (fderiv ℝ
      (orbit.endpointBump Clim Glim k)) a -
        fderiv ℝ (fderiv ℝ (orbit.endpointBump Clim Glim k)) b‖ ≤
      Llocal * ‖a - b‖ ^ (1 / 2 : ℝ) := by
    intro k a b
    simpa only [orbit] using
      hHolder ε₀ hεHolder Clim hClim Glim hGlim hGlimTendsto k a b
  have hgeneric := holder_of_disjoint_finsum_hessian
    Γ orbit.endpoint (fun k ↦ orbit.interpolationRadius Clim Glim k)
      (fun k ↦ orbit.endpointBump Clim Glim k) (orbit.bumpCorrection Clim Glim)
      Llocal hClosed hClusterData hRadiusZero hBallsData hSupport hdisjointΓ hHessianEq
      hlocal hLlocal.le u v
  calc
    ‖EuclideanPlane.hessian (orbit.bumpCorrection Clim Glim) u -
        EuclideanPlane.hessian (orbit.bumpCorrection Clim Glim) v‖ =
        ‖fderiv ℝ (fderiv ℝ (orbit.bumpCorrection Clim Glim)) u -
          fderiv ℝ (fderiv ℝ (orbit.bumpCorrection Clim Glim)) v‖ :=
      norm_euclideanHessian_sub_eq_norm_secondFDeriv_sub
        (orbit.bumpCorrection Clim Glim) u v
    _ ≤ 2 * Llocal * ‖u - v‖ ^ (1 / 2 : ℝ) := hgeneric
    _ = L * ‖u - v‖ ^ (1 / 2 : ℝ) := by rfl


/-- Helper for eq:holder-hessian-bound: adding the translated quadratic preserves the
one-half Hölder modulus of the concrete endpoint-bump Hessian. -/
theorem realizedObjectiveHessianHolder (curve : DFP.TwoLeg.SlowCurve) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ L > 0,
      ∀ ε₀ ∈ Set.Ioc 0 εbar,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
        ∀ Clim : EuclideanSpace ℝ (Fin 2),
          Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
            ∀ Glim > 0,
              Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) →
                ∀ u v,
                  ‖EuclideanPlane.hessian (orbit.realizedObjective Clim Glim) u -
                      EuclideanPlane.hessian (orbit.realizedObjective Clim Glim) v‖ ≤
                    L * ‖u - v‖ ^ (1 / 2 : ℝ) := by
  obtain ⟨ηHolder, hηHolder, L, hL, hHolder⟩ := bumpCorrectionHessianHolder curve
  obtain ⟨ηRegular, hηRegular, hRegular⟩ :=
    curve.bumpCorrectionContDiffTwoAndZeroJets
  let εbar := min ηHolder ηRegular
  have hεbarPos : 0 < εbar := by
    dsimp only [εbar]
    exact lt_min hηHolder.1 hηRegular.1
  have hεbarLt : εbar < (1 / 4 : ℝ) :=
    (min_le_left _ _).trans_lt hηHolder.2
  have hεbarLeHolder : εbar ≤ ηHolder := by
    dsimp only [εbar]
    exact min_le_left _ _
  have hεbarLeRegular : εbar ≤ ηRegular := by
    dsimp only [εbar]
    exact min_le_right _ _
  refine ⟨εbar, ⟨hεbarPos, hεbarLt⟩, L, hL, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
  have hεHolder : ε₀ ∈ Set.Ioc 0 ηHolder :=
    ⟨hε₀.1, hε₀.2.trans hεbarLeHolder⟩
  have hεRegular : ε₀ ∈ Set.Ioc 0 ηRegular :=
    ⟨hε₀.1, hε₀.2.trans hεbarLeRegular⟩
  intro Clim hClim Glim hGlim hGlimTendsto u v
  have hPsi : ContDiff ℝ 2 (orbit.bumpCorrection Clim Glim) := by
    simpa only [orbit] using
      (hRegular ε₀ hεRegular Clim hClim Glim hGlim hGlimTendsto).1
  have hobj : orbit.realizedObjective Clim Glim =
      (fun z ↦ (1 / 2 : ℝ) * ‖z - Clim‖ ^ 2 + orbit.bumpCorrection Clim Glim z) := by
    funext z
    exact DFP.TwoPhaseOrbit.realizedObjective_apply orbit Clim Glim z
  have hHessianObj (z : EuclideanSpace ℝ (Fin 2)) :
      EuclideanPlane.hessian (orbit.realizedObjective Clim Glim) z =
        (1 : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) +
          EuclideanPlane.hessian (orbit.bumpCorrection Clim Glim) z := by
    calc
      EuclideanPlane.hessian (orbit.realizedObjective Clim Glim) z =
          fderiv ℝ (gradient (orbit.realizedObjective Clim Glim)) z := by
            rw [EuclideanPlane.hessian_def]
      _ = fderiv ℝ (gradient
          (fun y ↦ (1 / 2 : ℝ) * ‖y - Clim‖ ^ 2 +
            orbit.bumpCorrection Clim Glim y)) z := by rw [hobj]
      _ = 1 + fderiv ℝ (gradient (orbit.bumpCorrection Clim Glim)) z :=
        HessianPerturbation.fderiv_gradient_halfNormSq_sub_add Clim
          (orbit.bumpCorrection Clim Glim) z hPsi
      _ = (1 : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) +
          EuclideanPlane.hessian (orbit.bumpCorrection Clim Glim) z := by
        rw [EuclideanPlane.hessian_def]
  rw [hHessianObj u, hHessianObj v]
  simpa only [add_sub_add_left_eq_sub] using
    (hHolder ε₀ hεHolder Clim hClim Glim hGlim hGlimTendsto u v)


/-- Helper for eq:holder-hessian-bound: the canonical invariant slow curve supplied
by the two-phase construction admits the concrete global one-half Hölder Hessian
bound for its realized objective. -/
theorem existsRealizedObjectiveHessianHolder :
    ∃ curve : DFP.TwoLeg.SlowCurve,
      ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ L > 0,
        ∀ ε₀ ∈ Set.Ioc 0 εbar,
          let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
          ∀ Clim : EuclideanSpace ℝ (Fin 2),
            Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
              ∀ Glim > 0,
                Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) →
                  ∀ u v,
                    ‖EuclideanPlane.hessian (orbit.realizedObjective Clim Glim) u -
                        EuclideanPlane.hessian (orbit.realizedObjective Clim Glim) v‖ ≤
                      L * ‖u - v‖ ^ (1 / 2 : ℝ) := by
  obtain ⟨p, h, _, _, _, hInvariant, hpJet, hhJet, _⟩ :=
    DFP.TwoLeg.exists_localForwardInvariantSlowCurve
  let curve := DFP.TwoLeg.SlowCurve.ofAsymptotics p h hpJet hhJet hInvariant
  obtain ⟨εbar, hεbar, L, hL, hHolder⟩ := realizedObjectiveHessianHolder curve
  exact ⟨curve, εbar, hεbar, L, hL, hHolder⟩


end DFP.PlanarConvergence
