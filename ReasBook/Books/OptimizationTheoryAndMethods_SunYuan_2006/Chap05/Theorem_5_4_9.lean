/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Assumption_5_4_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Theorem_5_4_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Theorem_5_4_9.Convergence
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Theorem_5_4_9.Update
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Theorem_5_4_9.Iteration
import Mathlib.Analysis.Calculus.ContDiff.Operations

noncomputable section

section Chapter05Theorem549

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "Operator" => Point →L[ℝ] Point

/-- Helper for Chapter05 Theorem 5.4.9: the support hypothesis turns any sufficiently small start
into an admissible invertible initial pair in `domU`. -/
lemma smallStartAdmissible_of_support
    {D : Set Point} {F : Point → Point}
    (hF : HasQuasiNewtonLocalConvergenceAssumptions D F)
    {domU : Set (Point × Operator)} {U : JacobianUpdateFunction Point}
    (hSupport :
      SupportsLocalWellDefinedJacobianIteration U F hF.xStar (fderiv ℝ F hF.xStar) domU) :
    ∃ ε > 0, ∃ δ > 0, ∀ x0 B0,
      ‖x0 - hF.xStar‖ < ε →
      ‖B0 - fderiv ℝ F hF.xStar‖ < δ →
      (x0, B0) ∈ domU ∧ B0.IsInvertible := by
  -- Unpack the source-side small-start admissibility clause verbatim.
  exact hSupport.1

/-- Helper for Chapter05 Theorem 5.4.9: an admissible invertible initial pair extends to a raw
quasi-Newton orbit that stays in `domU` and follows the update rule `U`. -/
lemma existsOrbitInDomOfSupportedSmallStart
    {D : Set Point} {F : Point → Point}
    (hF : HasQuasiNewtonLocalConvergenceAssumptions D F)
    {domU : Set (Point × Operator)} {U : JacobianUpdateFunction Point}
    (hSupport :
      SupportsLocalWellDefinedJacobianIteration U F hF.xStar (fderiv ℝ F hF.xStar) domU)
    {x0 : Point} {B0 : Operator}
    (h0 : (x0, B0) ∈ domU)
    (hB0 : B0.IsInvertible) :
    ∃ x : ℕ → Point, ∃ B : ℕ → Operator,
      x 0 = x0 ∧
      B 0 = B0 ∧
      (∀ k : ℕ, (x k, B k) ∈ domU) ∧
      (∀ k : ℕ, (B k).IsInvertible) ∧
      (∀ k : ℕ, x (k + 1) = quasiNewtonNextIterate F (x k) (B k)) ∧
      (∀ k : ℕ, B (k + 1) ∈ U (x k) (B k)) := by
  classical
  let nextState :
      {p : Point × Operator // p ∈ domU ∧ p.2.IsInvertible} →
        {p : Point × Operator // p ∈ domU ∧ p.2.IsInvertible} := fun p ↦
          let Bnext : Operator := Classical.choose (hSupport.2.1 p.1.1 p.1.2 p.2.1 p.2.2)
          let hBnext_mem : Bnext ∈ U p.1.1 p.1.2 := Classical.choose_spec
            (hSupport.2.1 p.1.1 p.1.2 p.2.1 p.2.2)
          let hAdvance := hSupport.2.2 p.1.1 p.1.2 Bnext p.2.1 p.2.2 hBnext_mem
          ⟨(quasiNewtonNextIterate F p.1.1 p.1.2, Bnext), hAdvance.2, hAdvance.1⟩
  let orbit : ℕ → {p : Point × Operator // p ∈ domU ∧ p.2.IsInvertible} :=
    Nat.rec ⟨(x0, B0), h0, hB0⟩ fun _ p ↦ nextState p
  refine ⟨fun k ↦ (orbit k).1.1, fun k ↦ (orbit k).1.2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- The recursive orbit starts from the prescribed initial iterate.
    rfl
  · -- The recursive orbit starts from the prescribed initial Jacobian approximation.
    rfl
  · -- Every recursive state stays in the admissibility set by construction.
    intro k
    exact (orbit k).2.1
  · -- Every recursive Jacobian approximation stays invertible by construction.
    intro k
    exact (orbit k).2.2
  · -- The first component of each successor state is the quasi-Newton next iterate.
    intro k
    change (nextState (orbit k)).1.1 = quasiNewtonNextIterate F (orbit k).1.1 (orbit k).1.2
    simp [nextState]
  · -- The second component of each successor state is chosen from the update set `U`.
    intro k
    change (nextState (orbit k)).1.2 ∈ U (orbit k).1.1 (orbit k).1.2
    change
      Classical.choose
          (hSupport.2.1 (orbit k).1.1 (orbit k).1.2 (orbit k).2.1 (orbit k).2.2) ∈
        U (orbit k).1.1 (orbit k).1.2
    exact Classical.choose_spec
      (hSupport.2.1 (orbit k).1.1 (orbit k).1.2 (orbit k).2.1 (orbit k).2.2)

/-- Helper for Chapter05 Theorem 5.4.9: near the reference Jacobian `fderiv ℝ F hF.xStar`, the
operator norms of the formal inverses are uniformly bounded. -/
lemma inverseNormBoundNearReferenceJacobian
    {D : Set Point} {F : Point → Point}
    (hF : HasQuasiNewtonLocalConvergenceAssumptions D F) :
    ∃ ρ > 0, ∃ ξ > 0, ∀ ⦃B : Operator⦄,
      ‖B - fderiv ℝ F hF.xStar‖ < ρ →
      ‖B.inverse‖ ≤ ξ := by
  let DFstar : Operator := fderiv ℝ F hF.xStar
  have hInverse :
      ContinuousAt (fun A : Operator ↦ A.inverse) DFstar := by
    exact (hF.fderiv_isInvertible.contDiffAt_map_inverse (𝕜 := ℝ) (n := 1)).continuousAt
  have hNear :
      {B : Operator | ‖B.inverse - DFstar.inverse‖ < 1} ∈ nhds DFstar := by
    simpa [Set.preimage, DFstar, Metric.mem_ball, dist_eq_norm] using
      hInverse (Metric.ball_mem_nhds DFstar.inverse zero_lt_one)
  rcases Metric.mem_nhds_iff.mp hNear with ⟨ρ, hρ, hρsub⟩
  refine ⟨ρ, hρ, ‖DFstar.inverse‖ + 1, add_pos_of_nonneg_of_pos (norm_nonneg _) zero_lt_one, ?_⟩
  intro B hB
  have hBball : B ∈ Metric.ball DFstar ρ := by
    simpa [Metric.mem_ball, dist_eq_norm, DFstar] using hB
  have hclose : ‖B.inverse - DFstar.inverse‖ < 1 := hρsub hBball
  have htriangle :
      ‖B.inverse‖ ≤ ‖B.inverse - DFstar.inverse‖ + ‖DFstar.inverse‖ := by
    calc
      ‖B.inverse‖ = ‖(B.inverse - DFstar.inverse) + DFstar.inverse‖ := by
        rw [sub_add_cancel]
      _ ≤ ‖B.inverse - DFstar.inverse‖ + ‖DFstar.inverse‖ := norm_add_le _ _
  have hsum :
      ‖B.inverse - DFstar.inverse‖ + ‖DFstar.inverse‖ ≤ 1 + ‖DFstar.inverse‖ := by
    nlinarith [show 0 ≤ ‖DFstar.inverse‖ by exact norm_nonneg _,
      show ‖B.inverse - DFstar.inverse‖ ≤ 1 by exact le_of_lt hclose]
  simpa [add_comm] using htriangle.trans hsum

/-- Helper for Chapter05 Theorem 5.4.9: one quasi-Newton step is controlled by the current
iterate error and Jacobian-approximation error. -/
lemma quasiNewtonNextError_le
    {D : Set Point} {F : Point → Point}
    (hF : HasQuasiNewtonLocalConvergenceAssumptions D F)
    {x : Point} {B : Operator}
    (hx : x ∈ D)
    (hB : B.IsInvertible) :
    ‖quasiNewtonNextIterate F x B - hF.xStar‖ ≤
      ‖B.inverse‖ *
        ((max hF.gamma 0 * ‖x - hF.xStar‖ + ‖B - fderiv ℝ F hF.xStar‖) * ‖x - hF.xStar‖) := by
  let DFstar : Operator := fderiv ℝ F hF.xStar
  let e : Point := x - hF.xStar
  let remainder : Point := -F x + F hF.xStar + DFstar e
  have himage :
      B (quasiNewtonNextIterate F x B - hF.xStar) =
        remainder + (B - DFstar) e := by
    -- Rewrite the next-step error after applying `B`, then isolate the linearization remainder
    -- and the Jacobian approximation defect.
    calc
      B (quasiNewtonNextIterate F x B - hF.xStar)
          = B (e - B.inverse (F x)) := by
              simp [quasiNewtonNextIterate, e, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      _ = B e - F x := by
            rw [map_sub, hB.self_apply_inverse]
      _ = DFstar e + (B - DFstar) e - F x := by
            simp [DFstar, sub_eq_add_neg, add_left_comm, add_comm]
      _ = remainder + (B - DFstar) e := by
            simp [remainder, hF.map_xStar, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  have hstep :
      quasiNewtonNextIterate F x B - hF.xStar = B.inverse (remainder + (B - DFstar) e) := by
    -- Apply the formal inverse of `B` to the exact step identity.
    have hleft :
        B.inverse (B (quasiNewtonNextIterate F x B - hF.xStar)) =
          quasiNewtonNextIterate F x B - hF.xStar := by
      simpa using hB.inverse_apply_self (quasiNewtonNextIterate F x B - hF.xStar)
    exact hleft.symm.trans <| congrArg B.inverse himage
  have hremainder :
      ‖remainder‖ ≤ max hF.gamma 0 * ‖e‖ * ‖e‖ := by
    -- The Chapter 5 Taylor remainder estimate controls the nonlinear term at `xStar`.
    have hremainder_eq :
        remainder = -(F x - F hF.xStar - DFstar e) := by
      simp [remainder, sub_eq_add_neg]
      abel
    calc
      ‖remainder‖ = ‖F x - F hF.xStar - DFstar e‖ := by
          rw [hremainder_eq, norm_neg]
      _ ≤ max hF.gamma 0 * (‖x - hF.xStar‖ + 2 * ‖hF.xStar - hF.xStar‖) * ‖x - hF.xStar‖ := by
            exact linearizationRemainder_le_errorControl F hF hx hF.xStar_mem
      _ = max hF.gamma 0 * ‖e‖ * ‖e‖ := by simp [e]
  have hdefect :
      ‖(B - DFstar) e‖ ≤ ‖B - DFstar‖ * ‖e‖ :=
    (B - DFstar).le_opNorm e
  have hfactor :
      ((max hF.gamma 0 * ‖x - hF.xStar‖ + ‖B - DFstar‖) * ‖x - hF.xStar‖) =
        max hF.gamma 0 * ‖e‖ * ‖e‖ + ‖B - DFstar‖ * ‖e‖ := by
    calc
      ((max hF.gamma 0 * ‖x - hF.xStar‖ + ‖B - DFstar‖) * ‖x - hF.xStar‖)
          = (max hF.gamma 0 * ‖x - hF.xStar‖) * ‖x - hF.xStar‖ +
              ‖B - DFstar‖ * ‖x - hF.xStar‖ := by
                rw [add_mul]
      _ = max hF.gamma 0 * ‖e‖ * ‖e‖ + ‖B - DFstar‖ * ‖e‖ := by
            simp [e]
  -- Put the exact step identity and the two norm bounds together.
  calc
    ‖quasiNewtonNextIterate F x B - hF.xStar‖ = ‖B.inverse (remainder + (B - DFstar) e)‖ := by
        rw [hstep]
    _ ≤ ‖B.inverse‖ * ‖remainder + (B - DFstar) e‖ := B.inverse.le_opNorm _
    _ ≤ ‖B.inverse‖ * (‖remainder‖ + ‖(B - DFstar) e‖) := by
          exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
    _ ≤ ‖B.inverse‖ * (max hF.gamma 0 * ‖e‖ * ‖e‖ + ‖B - DFstar‖ * ‖e‖) := by
          exact mul_le_mul_of_nonneg_left (add_le_add hremainder hdefect) (norm_nonneg _)
    _ = ‖B.inverse‖ * ((max hF.gamma 0 * ‖x - hF.xStar‖ + ‖B - DFstar‖) * ‖x - hF.xStar‖) := by
          rw [hfactor]

/-- Helper for Chapter05 Theorem 5.4.9: a uniform inverse bound and a uniform Jacobian-error
bound turn the one-step quasi-Newton estimate into the fixed half-rate contraction
`‖xₖ₊₁ - x*‖ ≤ ε * (1 / 2)^(k + 1)`. -/
lemma halfRateNextError_of_uniformBounds
    {D : Set Point} {F : Point → Point}
    (hF : HasQuasiNewtonLocalConvergenceAssumptions D F)
    {x : Point} {B : Operator} {ξ ε δ : ℝ} {k : ℕ}
    (hx : x ∈ D)
    (hB : B.IsInvertible)
    (hinv : ‖B.inverse‖ ≤ ξ)
    (hBclose : ‖B - fderiv ℝ F hF.xStar‖ ≤ 2 * δ)
    (hxerr : ‖x - hF.xStar‖ ≤ ε * (1 / 2 : ℝ) ^ k)
    (hcontract : ξ * (max hF.gamma 0 * ε + 2 * δ) ≤ 1 / 2) :
    ‖quasiNewtonNextIterate F x B - hF.xStar‖ ≤ ε * (1 / 2 : ℝ) ^ (k + 1) := by
  have hξ_nonneg : 0 ≤ ξ := by
    exact le_trans (norm_nonneg _) hinv
  have hδ_nonneg : 0 ≤ δ := by
    nlinarith [norm_nonneg (B - fderiv ℝ F hF.xStar), hBclose]
  have hεpow_nonneg : 0 ≤ ε * (1 / 2 : ℝ) ^ k := by
    exact le_trans (norm_nonneg _) hxerr
  have hpow_pos : 0 < (1 / 2 : ℝ) ^ k := by
    positivity
  have hε_nonneg : 0 ≤ ε := by
    nlinarith
  have hpow_le_one : (1 / 2 : ℝ) ^ k ≤ 1 := by
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hγ_nonneg : 0 ≤ max hF.gamma 0 := by
    simp
  have hstep :=
    quasiNewtonNextError_le hF hx hB
  have hinner :
      (max hF.gamma 0 * ‖x - hF.xStar‖ + ‖B - fderiv ℝ F hF.xStar‖) * ‖x - hF.xStar‖ ≤
        (max hF.gamma 0 * (ε * (1 / 2 : ℝ) ^ k) + 2 * δ) * (ε * (1 / 2 : ℝ) ^ k) := by
    gcongr
  have hεpow_le_ε : ε * (1 / 2 : ℝ) ^ k ≤ ε := by
    exact mul_le_of_le_one_right hε_nonneg hpow_le_one
  have hcoeff :
      max hF.gamma 0 * (ε * (1 / 2 : ℝ) ^ k) + 2 * δ ≤ max hF.gamma 0 * ε + 2 * δ := by
    nlinarith
  -- Apply the one-step estimate, then isolate the common contraction coefficient.
  calc
    ‖quasiNewtonNextIterate F x B - hF.xStar‖
        ≤ ‖B.inverse‖ *
            ((max hF.gamma 0 * ‖x - hF.xStar‖ + ‖B - fderiv ℝ F hF.xStar‖) *
              ‖x - hF.xStar‖) := hstep
    _ ≤ ξ * ((max hF.gamma 0 * (ε * (1 / 2 : ℝ) ^ k) + 2 * δ) * (ε * (1 / 2 : ℝ) ^ k)) := by
          exact mul_le_mul hinv hinner (by positivity) hξ_nonneg
    _ ≤ ξ * ((max hF.gamma 0 * ε + 2 * δ) * (ε * (1 / 2 : ℝ) ^ k)) := by
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcoeff hεpow_nonneg) hξ_nonneg
    _ = (ξ * (max hF.gamma 0 * ε + 2 * δ)) * (ε * (1 / 2 : ℝ) ^ k) := by
          ring
    _ ≤ (1 / 2 : ℝ) * (ε * (1 / 2 : ℝ) ^ k) := by
          exact mul_le_mul_of_nonneg_right hcontract hεpow_nonneg
    _ = ε * (1 / 2 : ℝ) ^ (k + 1) := by
          rw [pow_succ']
          ring

/-- Helper for Chapter05 Theorem 5.4.9: `quasiNewtonSigma F xStar x B` is bounded by any common
upper bound for the current and next iterate errors. -/
lemma quasiNewtonSigma_le_of_error_bounds
    {F : Point → Point} {xStar x : Point} {B : Operator} {r : ℝ}
    (hx : ‖x - xStar‖ ≤ r)
    (hnext : ‖quasiNewtonNextIterate F x B - xStar‖ ≤ r) :
    quasiNewtonSigma F xStar x B ≤ r := by
  -- Normalize `σ` to a maximum of the two endpoint errors.
  simpa [quasiNewtonSigma, max_le_iff] using And.intro hx hnext

/-- Helper for Chapter05 Theorem 5.4.9: a dyadic error bound immediately packages linear
convergence with witness `C = ε` and `q = 1 / 2`. -/
lemma linearlyConvergesTo_of_halfRate
    (x : ℕ → Point) (xStar : Point) {ε : ℝ}
    (hε_nonneg : 0 ≤ ε)
    (hx : ∀ k : ℕ, ‖x k - xStar‖ ≤ ε * (1 / 2 : ℝ) ^ k) :
    LinearlyConvergesTo x xStar := by
  -- Use the explicit geometric bound as the owner witness.
  refine ⟨ε, 1 / 2, hε_nonneg, ?_, hx⟩
  constructor <;> norm_num

/-- Helper for Chapter05 Theorem 5.4.9: under the additive update inequality `(5.4.40)`, a raw
quasi-Newton orbit satisfies the uniform domain, iterate, and Jacobian-error bounds needed for
the dyadic half-rate argument. -/
lemma additiveUpdateOrbitInvariants
    {D : Set Point} {F : Point → Point}
    (hF : HasQuasiNewtonLocalConvergenceAssumptions D F)
    {domU : Set (Point × Operator)} {U : JacobianUpdateFunction Point}
    {γu ρD ρ ξ ε δ : ℝ}
    (hball : Metric.ball hF.xStar ρD ⊆ D)
    (hε_pos : 0 < ε)
    (hε_lt_ρD : ε < ρD)
    (hinverse : ∀ ⦃B : Operator⦄, ‖B - fderiv ℝ F hF.xStar‖ < ρ → ‖B.inverse‖ ≤ ξ)
    (hadd :
      ∀ x B Bnext,
        (x, B) ∈ domU →
        B.IsInvertible →
        Bnext ∈ U x B →
          ‖Bnext - fderiv ℝ F hF.xStar‖ ≤
            ‖B - fderiv ℝ F hF.xStar‖ +
              (γu / 2) * (‖quasiNewtonNextIterate F x B - hF.xStar‖ + ‖x - hF.xStar‖))
    (h2δ_lt_ρ : 2 * δ < ρ)
    (hγuε : 3 * max γu 0 * ε ≤ 2 * δ)
    (hcontract : ξ * (max hF.gamma 0 * ε + 2 * δ) ≤ 1 / 2)
    {x : ℕ → Point} {B : ℕ → Operator}
    (hx0 : ‖x 0 - hF.xStar‖ ≤ ε)
    (hB0 : ‖B 0 - fderiv ℝ F hF.xStar‖ ≤ δ)
    (hinDom : ∀ k : ℕ, (x k, B k) ∈ domU)
    (hInv : ∀ k : ℕ, (B k).IsInvertible)
    (hStep : ∀ k : ℕ, x (k + 1) = quasiNewtonNextIterate F (x k) (B k))
    (hUpd : ∀ k : ℕ, B (k + 1) ∈ U (x k) (B k)) :
    ∀ k : ℕ,
      x k ∈ D ∧
        ‖x k - hF.xStar‖ ≤ ε * (1 / 2 : ℝ) ^ k ∧
          ‖B k - fderiv ℝ F hF.xStar‖ ≤ 2 * δ - δ * (1 / 2 : ℝ) ^ k := by
  have hδ_nonneg : 0 ≤ δ := by
    nlinarith [norm_nonneg (B 0 - fderiv ℝ F hF.xStar), hB0]
  intro k
  induction k with
  | zero =>
      -- The initial state is small enough to lie in the domain ball and satisfy the dyadic bound.
      refine ⟨?_, ?_, ?_⟩
      · apply hball
        simpa [Metric.mem_ball, dist_eq_norm] using lt_of_le_of_lt hx0 hε_lt_ρD
      · simpa using hx0
      · have hδ_eq : 2 * δ - δ = δ := by ring
        simpa [hδ_eq] using hB0
  | succ k hk =>
      rcases hk with ⟨hxkD, hxk, hBk⟩
      have hpow_nonneg : 0 ≤ (1 / 2 : ℝ) ^ k := by
        positivity
      have hBk_two_delta : ‖B k - fderiv ℝ F hF.xStar‖ ≤ 2 * δ := by
        nlinarith
      have hBk_lt_ρ : ‖B k - fderiv ℝ F hF.xStar‖ < ρ := by
        exact lt_of_le_of_lt hBk_two_delta h2δ_lt_ρ
      have hInvBound : ‖(B k).inverse‖ ≤ ξ := hinverse hBk_lt_ρ
      have hnext_raw :
          ‖quasiNewtonNextIterate F (x k) (B k) - hF.xStar‖ ≤
            ε * (1 / 2 : ℝ) ^ (k + 1) := by
        -- The current iterate and Jacobian approximation fit the uniform contraction lemma.
        exact
          halfRateNextError_of_uniformBounds hF hxkD (hInv k) hInvBound hBk_two_delta hxk
            hcontract
      have hnext :
          ‖x (k + 1) - hF.xStar‖ ≤ ε * (1 / 2 : ℝ) ^ (k + 1) := by
        simpa [hStep k] using hnext_raw
      have hpow_lt_one : (1 / 2 : ℝ) ^ (k + 1) < 1 := by
        exact pow_lt_one₀ (by norm_num) (by norm_num) (Nat.succ_ne_zero _)
      have hxnext_lt_ρD : ‖x (k + 1) - hF.xStar‖ < ρD := by
        calc
          ‖x (k + 1) - hF.xStar‖ ≤ ε * (1 / 2 : ℝ) ^ (k + 1) := hnext
          _ < ε := mul_lt_of_lt_one_right hε_pos hpow_lt_one
          _ < ρD := hε_lt_ρD
      have hxnextD : x (k + 1) ∈ D := by
        apply hball
        simpa [Metric.mem_ball, dist_eq_norm] using hxnext_lt_ρD
      have hγu_scaled :
          (γu / 2) * (‖quasiNewtonNextIterate F (x k) (B k) - hF.xStar‖ + ‖x k - hF.xStar‖) ≤
            (max γu 0 / 2) *
              (‖quasiNewtonNextIterate F (x k) (B k) - hF.xStar‖ + ‖x k - hF.xStar‖) := by
        have hsum_nonneg :
            0 ≤
              ‖quasiNewtonNextIterate F (x k) (B k) - hF.xStar‖ + ‖x k - hF.xStar‖ := by
          positivity
        have hcoef : γu / 2 ≤ max γu 0 / 2 := by
          nlinarith [le_max_left γu 0]
        exact mul_le_mul_of_nonneg_right hcoef hsum_nonneg
      have hBk_succ_raw :
          ‖B (k + 1) - fderiv ℝ F hF.xStar‖ ≤
            ‖B k - fderiv ℝ F hF.xStar‖ +
              (max γu 0 / 2) *
                (‖quasiNewtonNextIterate F (x k) (B k) - hF.xStar‖ + ‖x k - hF.xStar‖) := by
        exact le_trans (hadd (x k) (B k) (B (k + 1)) (hinDom k) (hInv k) (hUpd k)) <|
          add_le_add_right hγu_scaled _
      have hγuε_quarter : (3 * max γu 0 * ε) / 4 ≤ δ / 2 := by
        nlinarith
      have hBk_succ :
          ‖B (k + 1) - fderiv ℝ F hF.xStar‖ ≤
            2 * δ - δ * (1 / 2 : ℝ) ^ (k + 1) := by
        -- The additive update contributes at most one more dyadic Jacobian increment.
        calc
          ‖B (k + 1) - fderiv ℝ F hF.xStar‖
              ≤ ‖B k - fderiv ℝ F hF.xStar‖ +
                  (max γu 0 / 2) *
                    (‖quasiNewtonNextIterate F (x k) (B k) - hF.xStar‖ + ‖x k - hF.xStar‖) :=
                hBk_succ_raw
          _ ≤ (2 * δ - δ * (1 / 2 : ℝ) ^ k) +
                (max γu 0 / 2) * (ε * (1 / 2 : ℝ) ^ (k + 1) + ε * (1 / 2 : ℝ) ^ k) := by
                gcongr
          _ = (2 * δ - δ * (1 / 2 : ℝ) ^ k) +
                ((3 * max γu 0 * ε) / 4) * (1 / 2 : ℝ) ^ k := by
                rw [pow_succ']
                ring
          _ ≤ (2 * δ - δ * (1 / 2 : ℝ) ^ k) + (δ / 2) * (1 / 2 : ℝ) ^ k := by
                exact add_le_add_right (mul_le_mul_of_nonneg_right hγuε_quarter hpow_nonneg) _
          _ = 2 * δ - δ * (1 / 2 : ℝ) ^ (k + 1) := by
                rw [pow_succ']
                ring
      exact ⟨hxnextD, hnext, hBk_succ⟩

/-- Helper for Chapter05 Theorem 5.4.9: under the `σ`-controlled update inequality `(5.4.41)`, a
raw quasi-Newton orbit satisfies the same dyadic iterate and Jacobian-error bounds as in the
additive branch. -/
lemma sigmaUpdateOrbitInvariants
    {D : Set Point} {F : Point → Point}
    (hF : HasQuasiNewtonLocalConvergenceAssumptions D F)
    {domU : Set (Point × Operator)} {U : JacobianUpdateFunction Point}
    {α1 α2 ρD ρ ξ ε δ : ℝ}
    (hball : Metric.ball hF.xStar ρD ⊆ D)
    (hε_pos : 0 < ε)
    (hε_lt_ρD : ε < ρD)
    (hinverse : ∀ ⦃B : Operator⦄, ‖B - fderiv ℝ F hF.xStar‖ < ρ → ‖B.inverse‖ ≤ ξ)
    (hsigma :
      ∀ x B Bnext,
        (x, B) ∈ domU →
        B.IsInvertible →
        Bnext ∈ U x B →
          ‖Bnext - fderiv ℝ F hF.xStar‖ ≤
            (1 + α1 * quasiNewtonSigma F hF.xStar x B) * ‖B - fderiv ℝ F hF.xStar‖ +
              α2 * quasiNewtonSigma F hF.xStar x B)
    (h2δ_lt_ρ : 2 * δ < ρ)
    (hαεδ : 2 * (2 * max α1 0 * δ + max α2 0) * ε ≤ δ)
    (hcontract : ξ * (max hF.gamma 0 * ε + 2 * δ) ≤ 1 / 2)
    {x : ℕ → Point} {B : ℕ → Operator}
    (hx0 : ‖x 0 - hF.xStar‖ ≤ ε)
    (hB0 : ‖B 0 - fderiv ℝ F hF.xStar‖ ≤ δ)
    (hinDom : ∀ k : ℕ, (x k, B k) ∈ domU)
    (hInv : ∀ k : ℕ, (B k).IsInvertible)
    (hStep : ∀ k : ℕ, x (k + 1) = quasiNewtonNextIterate F (x k) (B k))
    (hUpd : ∀ k : ℕ, B (k + 1) ∈ U (x k) (B k)) :
    ∀ k : ℕ,
      x k ∈ D ∧
        ‖x k - hF.xStar‖ ≤ ε * (1 / 2 : ℝ) ^ k ∧
          ‖B k - fderiv ℝ F hF.xStar‖ ≤ 2 * δ - δ * (1 / 2 : ℝ) ^ k := by
  have hδ_nonneg : 0 ≤ δ := by
    nlinarith [norm_nonneg (B 0 - fderiv ℝ F hF.xStar), hB0]
  intro k
  induction k with
  | zero =>
      -- The initial state already satisfies the claimed dyadic bounds.
      refine ⟨?_, ?_, ?_⟩
      · apply hball
        simpa [Metric.mem_ball, dist_eq_norm] using lt_of_le_of_lt hx0 hε_lt_ρD
      · simpa using hx0
      · have hδ_eq : 2 * δ - δ = δ := by ring
        simpa [hδ_eq] using hB0
  | succ k hk =>
      rcases hk with ⟨hxkD, hxk, hBk⟩
      have hpow_nonneg : 0 ≤ (1 / 2 : ℝ) ^ k := by
        positivity
      have hBk_two_delta : ‖B k - fderiv ℝ F hF.xStar‖ ≤ 2 * δ := by
        nlinarith
      have hBk_lt_ρ : ‖B k - fderiv ℝ F hF.xStar‖ < ρ := by
        exact lt_of_le_of_lt hBk_two_delta h2δ_lt_ρ
      have hInvBound : ‖(B k).inverse‖ ≤ ξ := hinverse hBk_lt_ρ
      have hnext_raw :
          ‖quasiNewtonNextIterate F (x k) (B k) - hF.xStar‖ ≤
            ε * (1 / 2 : ℝ) ^ (k + 1) := by
        -- Reuse the common half-rate contraction once the Jacobian error is uniformly bounded.
        exact
          halfRateNextError_of_uniformBounds hF hxkD (hInv k) hInvBound hBk_two_delta hxk
            hcontract
      have hnext :
          ‖x (k + 1) - hF.xStar‖ ≤ ε * (1 / 2 : ℝ) ^ (k + 1) := by
        simpa [hStep k] using hnext_raw
      have hpow_lt_one : (1 / 2 : ℝ) ^ (k + 1) < 1 := by
        exact pow_lt_one₀ (by norm_num) (by norm_num) (Nat.succ_ne_zero _)
      have hxnext_lt_ρD : ‖x (k + 1) - hF.xStar‖ < ρD := by
        calc
          ‖x (k + 1) - hF.xStar‖ ≤ ε * (1 / 2 : ℝ) ^ (k + 1) := hnext
          _ < ε := mul_lt_of_lt_one_right hε_pos hpow_lt_one
          _ < ρD := hε_lt_ρD
      have hxnextD : x (k + 1) ∈ D := by
        apply hball
        simpa [Metric.mem_ball, dist_eq_norm] using hxnext_lt_ρD
      have hσ_bound :
          quasiNewtonSigma F hF.xStar (x k) (B k) ≤ ε * (1 / 2 : ℝ) ^ k := by
        apply quasiNewtonSigma_le_of_error_bounds
        · exact hxk
        · calc
            ‖quasiNewtonNextIterate F (x k) (B k) - hF.xStar‖
                ≤ ε * (1 / 2 : ℝ) ^ (k + 1) := hnext_raw
            _ ≤ ε * (1 / 2 : ℝ) ^ k := by
                  rw [pow_succ']
                  nlinarith
      have hσ_nonneg : 0 ≤ quasiNewtonSigma F hF.xStar (x k) (B k) := by
        simp [quasiNewtonSigma]
      have hα1_scaled :
          α1 * quasiNewtonSigma F hF.xStar (x k) (B k) ≤
            max α1 0 * quasiNewtonSigma F hF.xStar (x k) (B k) := by
        exact mul_le_mul_of_nonneg_right (by exact le_max_left _ _) hσ_nonneg
      have hα2_scaled :
          α2 * quasiNewtonSigma F hF.xStar (x k) (B k) ≤
            max α2 0 * quasiNewtonSigma F hF.xStar (x k) (B k) := by
        exact mul_le_mul_of_nonneg_right (by exact le_max_left _ _) hσ_nonneg
      have hBk_succ_raw :
          ‖B (k + 1) - fderiv ℝ F hF.xStar‖ ≤
            (1 + max α1 0 * quasiNewtonSigma F hF.xStar (x k) (B k)) *
                ‖B k - fderiv ℝ F hF.xStar‖ +
              max α2 0 * quasiNewtonSigma F hF.xStar (x k) (B k) := by
        have hraw := hsigma (x k) (B k) (B (k + 1)) (hinDom k) (hInv k) (hUpd k)
        have hmul :
            (1 + α1 * quasiNewtonSigma F hF.xStar (x k) (B k)) *
                ‖B k - fderiv ℝ F hF.xStar‖ ≤
              (1 + max α1 0 * quasiNewtonSigma F hF.xStar (x k) (B k)) *
                ‖B k - fderiv ℝ F hF.xStar‖ := by
          exact mul_le_mul_of_nonneg_right (by nlinarith) (norm_nonneg _)
        linarith
      have hαεδ_half : (2 * max α1 0 * δ + max α2 0) * ε ≤ δ / 2 := by
        nlinarith
      have hαincrement :
          (2 * max α1 0 * δ + max α2 0) * (ε * (1 / 2 : ℝ) ^ k) ≤
            (δ / 2) * (1 / 2 : ℝ) ^ k := by
        calc
          (2 * max α1 0 * δ + max α2 0) * (ε * (1 / 2 : ℝ) ^ k)
              = ((2 * max α1 0 * δ + max α2 0) * ε) * (1 / 2 : ℝ) ^ k := by
                  ring
          _ ≤ (δ / 2) * (1 / 2 : ℝ) ^ k := by
                exact mul_le_mul_of_nonneg_right hαεδ_half hpow_nonneg
      have hBk_succ :
          ‖B (k + 1) - fderiv ℝ F hF.xStar‖ ≤
            2 * δ - δ * (1 / 2 : ℝ) ^ (k + 1) := by
        -- The `σ`-term is controlled by the current dyadic iterate bound, so the Jacobian error
        -- gains the same one-step dyadic increment as in the additive branch.
        calc
          ‖B (k + 1) - fderiv ℝ F hF.xStar‖
              ≤ (1 + max α1 0 * quasiNewtonSigma F hF.xStar (x k) (B k)) *
                    ‖B k - fderiv ℝ F hF.xStar‖ +
                  max α2 0 * quasiNewtonSigma F hF.xStar (x k) (B k) :=
                hBk_succ_raw
          _ = ‖B k - fderiv ℝ F hF.xStar‖ +
                (max α1 0 * quasiNewtonSigma F hF.xStar (x k) (B k)) *
                  ‖B k - fderiv ℝ F hF.xStar‖ +
                max α2 0 * quasiNewtonSigma F hF.xStar (x k) (B k) := by
                ring
          _ ≤ ‖B k - fderiv ℝ F hF.xStar‖ +
                (max α1 0 * quasiNewtonSigma F hF.xStar (x k) (B k)) * (2 * δ) +
                max α2 0 * quasiNewtonSigma F hF.xStar (x k) (B k) := by
                gcongr
          _ = ‖B k - fderiv ℝ F hF.xStar‖ +
                (2 * max α1 0 * δ + max α2 0) *
                  quasiNewtonSigma F hF.xStar (x k) (B k) := by
                ring
          _ ≤ (2 * δ - δ * (1 / 2 : ℝ) ^ k) +
                (2 * max α1 0 * δ + max α2 0) * (ε * (1 / 2 : ℝ) ^ k) := by
                gcongr
          _ ≤ (2 * δ - δ * (1 / 2 : ℝ) ^ k) + (δ / 2) * (1 / 2 : ℝ) ^ k := by
                exact add_le_add_right hαincrement _
          _ = 2 * δ - δ * (1 / 2 : ℝ) ^ (k + 1) := by
                rw [pow_succ']
                ring
      exact ⟨hxnextD, hnext, hBk_succ⟩

/-- Chapter05 Theorem 5.4.9: if `F : ℝ^n → ℝ^n` satisfies
`HasQuasiNewtonLocalConvergenceAssumptions D F`, and `U` is a set-valued Jacobian update rule
such that either all admissible updates satisfy the additive estimate `(5.4.40)` with some
constant `γu`, or all admissible updates satisfy the `σ`-estimate `(5.4.41)` for some constants
`α₁`, `α₂`, on an admissibility set `domU`, with the source-side well-definedness conditions for
small admissible starts and admissible update selections folded into that update hypothesis, where
`σ(xₖ, xₖ₊₁) = max ‖xₖ - hF.xStar‖ ‖xₖ₊₁ - hF.xStar‖`, then there exist constants `ε` and `δ`
such that every initial pair `(x₀, B₀)` with `‖x₀ - hF.xStar‖ < ε` and
`‖B₀ - fderiv ℝ F hF.xStar‖ < δ` generates a well-defined iteration `(5.4.38)`-`(5.4.39)`,
and every such iteration has iterate sequence converging linearly to `hF.xStar`. -/
theorem jacobianQuasiNewtonSmallStartConvergence_of_update_condition
    (D : Set Point) (F : Point → Point)
    (hF : HasQuasiNewtonLocalConvergenceAssumptions D F)
    (domU : Set (Point × Operator))
    (U : JacobianUpdateFunction Point)
    (h_update :
      (∃ γu : ℝ,
        SatisfiesAdditiveLocalUpdateBound U F hF.xStar (fderiv ℝ F hF.xStar) domU γu) ∨
        ∃ α1 α2,
          SatisfiesSigmaLocalUpdateBound U F hF.xStar (fderiv ℝ F hF.xStar) domU α1 α2) :
    ∃ ε > 0, ∃ δ > 0, ∀ x0 B0,
      ‖x0 - hF.xStar‖ < ε →
      ‖B0 - fderiv ℝ F hF.xStar‖ < δ →
      JacobianQuasiNewtonSmallStartConvergence D F domU U hF.xStar x0 B0 := by
  let DFstar : Operator := fderiv ℝ F hF.xStar
  let γF0 : ℝ := max hF.gamma 0
  have hγF0_nonneg : 0 ≤ γF0 := by
    simp [γF0]
  have hγF0_add_one_pos : 0 < γF0 + 1 := by
    linarith
  have hDnhds : D ∈ nhds hF.xStar := hF.open_domain.mem_nhds hF.xStar_mem
  rcases Metric.mem_nhds_iff.mp hDnhds with ⟨ρD, hρD_pos, hball⟩
  rcases inverseNormBoundNearReferenceJacobian hF with ⟨ρ, hρ_pos, ξ, hξ_pos, hInverseBound⟩
  -- Route correction: instead of an abstract rate `q`, fix the executable dyadic rate `1 / 2`
  -- and prove branch-specific orbit invariants that directly feed the packaged convergence owner.
  rcases h_update with ⟨γu, hAdd⟩ | ⟨α1, α2, hSigma⟩
  · let γu0 : ℝ := max γu 0
    have hγu0_nonneg : 0 ≤ γu0 := by
      simp [γu0]
    let hSupport := hAdd.1
    let hAddBound := hAdd.2
    rcases smallStartAdmissible_of_support hF hSupport with ⟨εs, hεs_pos, δs, hδs_pos, hsmall⟩
    let δ : ℝ := min (δs / 2) (min (ρ / 4) (1 / (8 * ξ)))
    have hδ_pos : 0 < δ := by
      dsimp [δ]
      refine lt_min (half_pos hδs_pos) ?_
      refine lt_min ?_ ?_
      · nlinarith
      · positivity
    have hδ_le_δs_half : δ ≤ δs / 2 := by
      dsimp [δ]
      exact min_le_left _ _
    have hδ_lt_δs : δ < δs := by
      have hhalf_lt : δs / 2 < δs := by
        nlinarith
      exact lt_of_le_of_lt hδ_le_δs_half hhalf_lt
    have hδ_le_rho_quarter : δ ≤ ρ / 4 := by
      dsimp [δ]
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    have hδ_le_inv : δ ≤ 1 / (8 * ξ) := by
      dsimp [δ]
      exact le_trans (min_le_right _ _) (min_le_right _ _)
    have h2δ_lt_ρ : 2 * δ < ρ := by
      nlinarith
    let ε : ℝ :=
      min (εs / 2) (min (ρD / 2) (min (δ / (3 * γu0 + 1)) (1 / (4 * ξ * (γF0 + 1)))))
    have hε_pos : 0 < ε := by
      dsimp [ε]
      refine lt_min (half_pos hεs_pos) ?_
      refine lt_min (half_pos hρD_pos) ?_
      refine lt_min ?_ ?_
      · positivity
      · positivity
    have hε_le_εs_half : ε ≤ εs / 2 := by
      dsimp [ε]
      exact min_le_left _ _
    have hε_lt_εs : ε < εs := by
      have hhalf_lt : εs / 2 < εs := by
        nlinarith
      exact lt_of_le_of_lt hε_le_εs_half hhalf_lt
    have hε_le_ρD_half : ε ≤ ρD / 2 := by
      dsimp [ε]
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    have hε_lt_ρD : ε < ρD := by
      have hhalf_lt : ρD / 2 < ρD := by
        nlinarith
      exact lt_of_le_of_lt hε_le_ρD_half hhalf_lt
    have hε_le_δratio : ε ≤ δ / (3 * γu0 + 1) := by
      dsimp [ε]
      exact le_trans (min_le_right _ _) <|
        le_trans (min_le_right _ _) (min_le_left _ _)
    have hε_le_inv : ε ≤ 1 / (4 * ξ * (γF0 + 1)) := by
      dsimp [ε]
      exact le_trans (min_le_right _ _) <|
        le_trans (min_le_right _ _) (min_le_right _ _)
    have hγuε : 3 * γu0 * ε ≤ 2 * δ := by
      have hden_pos : 0 < 3 * γu0 + 1 := by
        nlinarith
      have htmp : ε * (3 * γu0 + 1) ≤ δ := by
        exact (le_div_iff₀ hden_pos).mp hε_le_δratio
      nlinarith
    have hγpart :
        ξ * (γF0 * ε) ≤ 1 / 4 := by
      have hγF0ε :
          γF0 * ε ≤ (γF0 + 1) * ε := by
        nlinarith
      have hmain :
          (γF0 + 1) * ε ≤ (γF0 + 1) * (1 / (4 * ξ * (γF0 + 1))) := by
        exact mul_le_mul_of_nonneg_left hε_le_inv (by linarith)
      have hrewrite :
          (γF0 + 1) * (1 / (4 * ξ * (γF0 + 1))) = 1 / (4 * ξ) := by
        field_simp [hξ_pos.ne', hγF0_add_one_pos.ne']
      have htmp : γF0 * ε ≤ 1 / (4 * ξ) := by
        exact hγF0ε.trans (hmain.trans_eq hrewrite)
      have hmul : ξ * (γF0 * ε) ≤ ξ * (1 / (4 * ξ)) := by
        exact mul_le_mul_of_nonneg_left htmp (le_of_lt hξ_pos)
      have hξrewrite : ξ * (1 / (4 * ξ)) = 1 / 4 := by
        field_simp [hξ_pos.ne']
      exact hmul.trans_eq hξrewrite
    have hδpart : ξ * (2 * δ) ≤ 1 / 4 := by
      have htwoδ :
          2 * δ ≤ 2 * (1 / (8 * ξ)) := by
        exact mul_le_mul_of_nonneg_left hδ_le_inv (by positivity)
      have htwoδ' : 2 * δ ≤ 1 / (4 * ξ) := by
        have hrewrite : 2 * (1 / (8 * ξ)) = 1 / (4 * ξ) := by
          field_simp [hξ_pos.ne']
          ring
        exact htwoδ.trans_eq hrewrite
      have hmul : ξ * (2 * δ) ≤ ξ * (1 / (4 * ξ)) := by
        exact mul_le_mul_of_nonneg_left htwoδ' (le_of_lt hξ_pos)
      have hξrewrite : ξ * (1 / (4 * ξ)) = 1 / 4 := by
        field_simp [hξ_pos.ne']
      exact hmul.trans_eq hξrewrite
    have hcontract : ξ * (γF0 * ε + 2 * δ) ≤ 1 / 2 := by
      nlinarith [hγpart, hδpart]
    refine ⟨ε, hε_pos, δ, hδ_pos, ?_⟩
    intro x0 B0 hx0 hB0
    have h0small := hsmall x0 B0 (lt_trans hx0 hε_lt_εs) (lt_trans hB0 hδ_lt_δs)
    rcases h0small with ⟨h0dom, hB0inv⟩
    have hLinear :
        ∀ A : JacobianQuasiNewtonIteration D F domU U x0 B0,
          LinearlyConvergesTo A.x hF.xStar := by
      intro A
      have hOrbit :=
        additiveUpdateOrbitInvariants hF hball hε_pos hε_lt_ρD hInverseBound hAddBound h2δ_lt_ρ
          hγuε hcontract
            (x := A.x) (B := A.B)
            (by simpa [A.x_zero] using le_of_lt hx0)
            (by simpa [A.B_zero, DFstar] using le_of_lt hB0)
            A.in_dom A.matrices_invertible A.step_eq A.update_mem
      exact
        linearlyConvergesTo_of_halfRate A.x hF.xStar (le_of_lt hε_pos) fun k ↦
          (hOrbit k).2.1
    have hExistsIteration :
        ∃ A : JacobianQuasiNewtonIteration D F domU U x0 B0, LinearlyConvergesTo A.x hF.xStar := by
      rcases existsOrbitInDomOfSupportedSmallStart hF hSupport h0dom hB0inv with
        ⟨x, B, hxzero, hBzero, hinDom, hInvAll, hStepAll, hUpdAll⟩
      have hIteratesMem :
          ∀ k : ℕ, x k ∈ D := by
        intro k
        exact (additiveUpdateOrbitInvariants hF hball hε_pos hε_lt_ρD hInverseBound hAddBound
          h2δ_lt_ρ hγuε hcontract
            (x := x) (B := B)
            (by simpa [hxzero] using le_of_lt hx0)
            (by simpa [hBzero, DFstar] using le_of_lt hB0)
            hinDom hInvAll hStepAll hUpdAll k).1
      let A : JacobianQuasiNewtonIteration D F domU U x0 B0 :=
        { x := x
          B := B
          x_zero := hxzero
          B_zero := hBzero
          iterates_mem := hIteratesMem
          in_dom := hinDom
          matrices_invertible := hInvAll
          step_eq := hStepAll
          update_mem := hUpdAll }
      exact ⟨A, hLinear A⟩
    exact
      { exists_iteration := hExistsIteration
        linear := hLinear }
  · let α10 : ℝ := max α1 0
    let α20 : ℝ := max α2 0
    have hα10_nonneg : 0 ≤ α10 := by
      simp [α10]
    have hα20_nonneg : 0 ≤ α20 := by
      simp [α20]
    let hSupport := hSigma.1
    let hSigmaBound := hSigma.2
    rcases smallStartAdmissible_of_support hF hSupport with ⟨εs, hεs_pos, δs, hδs_pos, hsmall⟩
    let δ : ℝ := min (δs / 2) (min (ρ / 4) (1 / (8 * ξ)))
    have hδ_pos : 0 < δ := by
      dsimp [δ]
      refine lt_min (half_pos hδs_pos) ?_
      refine lt_min ?_ ?_
      · nlinarith
      · positivity
    have hδ_le_δs_half : δ ≤ δs / 2 := by
      dsimp [δ]
      exact min_le_left _ _
    have hδ_lt_δs : δ < δs := by
      have hhalf_lt : δs / 2 < δs := by
        nlinarith
      exact lt_of_le_of_lt hδ_le_δs_half hhalf_lt
    have hδ_le_inv : δ ≤ 1 / (8 * ξ) := by
      dsimp [δ]
      exact le_trans (min_le_right _ _) (min_le_right _ _)
    have hδ_le_rho_quarter : δ ≤ ρ / 4 := by
      dsimp [δ]
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    have h2δ_lt_ρ : 2 * δ < ρ := by
      nlinarith
    let ε : ℝ :=
      min (εs / 2)
        (min (ρD / 2)
          (min (δ / (2 * (2 * α10 * δ + α20 + 1))) (1 / (4 * ξ * (γF0 + 1)))))
    have hε_pos : 0 < ε := by
      dsimp [ε]
      refine lt_min (half_pos hεs_pos) ?_
      refine lt_min (half_pos hρD_pos) ?_
      refine lt_min ?_ ?_
      · positivity
      · positivity
    have hε_le_εs_half : ε ≤ εs / 2 := by
      dsimp [ε]
      exact min_le_left _ _
    have hε_lt_εs : ε < εs := by
      have hhalf_lt : εs / 2 < εs := by
        nlinarith
      exact lt_of_le_of_lt hε_le_εs_half hhalf_lt
    have hε_le_ρD_half : ε ≤ ρD / 2 := by
      dsimp [ε]
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    have hε_lt_ρD : ε < ρD := by
      have hhalf_lt : ρD / 2 < ρD := by
        nlinarith
      exact lt_of_le_of_lt hε_le_ρD_half hhalf_lt
    have hε_le_sigmaRatio : ε ≤ δ / (2 * (2 * α10 * δ + α20 + 1)) := by
      dsimp [ε]
      exact le_trans (min_le_right _ _) <|
        le_trans (min_le_right _ _) (min_le_left _ _)
    have hε_le_inv : ε ≤ 1 / (4 * ξ * (γF0 + 1)) := by
      dsimp [ε]
      exact le_trans (min_le_right _ _) <|
        le_trans (min_le_right _ _) (min_le_right _ _)
    have hαεδ : 2 * (2 * α10 * δ + α20) * ε ≤ δ := by
      have hden_pos : 0 < 2 * (2 * α10 * δ + α20 + 1) := by
        positivity
      have htmp : ε * (2 * (2 * α10 * δ + α20 + 1)) ≤ δ := by
        exact (le_div_iff₀ hden_pos).mp hε_le_sigmaRatio
      nlinarith
    have hγpart :
        ξ * (γF0 * ε) ≤ 1 / 4 := by
      have hγF0ε :
          γF0 * ε ≤ (γF0 + 1) * ε := by
        nlinarith
      have hmain :
          (γF0 + 1) * ε ≤ (γF0 + 1) * (1 / (4 * ξ * (γF0 + 1))) := by
        exact mul_le_mul_of_nonneg_left hε_le_inv (by linarith)
      have hrewrite :
          (γF0 + 1) * (1 / (4 * ξ * (γF0 + 1))) = 1 / (4 * ξ) := by
        field_simp [hξ_pos.ne', hγF0_add_one_pos.ne']
      have htmp : γF0 * ε ≤ 1 / (4 * ξ) := by
        exact hγF0ε.trans (hmain.trans_eq hrewrite)
      have hmul : ξ * (γF0 * ε) ≤ ξ * (1 / (4 * ξ)) := by
        exact mul_le_mul_of_nonneg_left htmp (le_of_lt hξ_pos)
      have hξrewrite : ξ * (1 / (4 * ξ)) = 1 / 4 := by
        field_simp [hξ_pos.ne']
      exact hmul.trans_eq hξrewrite
    have hδpart : ξ * (2 * δ) ≤ 1 / 4 := by
      have htwoδ :
          2 * δ ≤ 2 * (1 / (8 * ξ)) := by
        exact mul_le_mul_of_nonneg_left hδ_le_inv (by positivity)
      have htwoδ' : 2 * δ ≤ 1 / (4 * ξ) := by
        have hrewrite : 2 * (1 / (8 * ξ)) = 1 / (4 * ξ) := by
          field_simp [hξ_pos.ne']
          ring
        exact htwoδ.trans_eq hrewrite
      have hmul : ξ * (2 * δ) ≤ ξ * (1 / (4 * ξ)) := by
        exact mul_le_mul_of_nonneg_left htwoδ' (le_of_lt hξ_pos)
      have hξrewrite : ξ * (1 / (4 * ξ)) = 1 / 4 := by
        field_simp [hξ_pos.ne']
      exact hmul.trans_eq hξrewrite
    have hcontract : ξ * (γF0 * ε + 2 * δ) ≤ 1 / 2 := by
      nlinarith [hγpart, hδpart]
    refine ⟨ε, hε_pos, δ, hδ_pos, ?_⟩
    intro x0 B0 hx0 hB0
    have h0small := hsmall x0 B0 (lt_trans hx0 hε_lt_εs) (lt_trans hB0 hδ_lt_δs)
    rcases h0small with ⟨h0dom, hB0inv⟩
    have hLinear :
        ∀ A : JacobianQuasiNewtonIteration D F domU U x0 B0,
          LinearlyConvergesTo A.x hF.xStar := by
      intro A
      have hOrbit :=
        sigmaUpdateOrbitInvariants hF hball hε_pos hε_lt_ρD hInverseBound hSigmaBound h2δ_lt_ρ
          hαεδ hcontract
            (x := A.x) (B := A.B)
            (by simpa [A.x_zero] using le_of_lt hx0)
            (by simpa [A.B_zero, DFstar] using le_of_lt hB0)
            A.in_dom A.matrices_invertible A.step_eq A.update_mem
      exact
        linearlyConvergesTo_of_halfRate A.x hF.xStar (le_of_lt hε_pos) fun k ↦
          (hOrbit k).2.1
    have hExistsIteration :
        ∃ A : JacobianQuasiNewtonIteration D F domU U x0 B0, LinearlyConvergesTo A.x hF.xStar := by
      rcases existsOrbitInDomOfSupportedSmallStart hF hSupport h0dom hB0inv with
        ⟨x, B, hxzero, hBzero, hinDom, hInvAll, hStepAll, hUpdAll⟩
      have hIteratesMem :
          ∀ k : ℕ, x k ∈ D := by
        intro k
        exact (sigmaUpdateOrbitInvariants hF hball hε_pos hε_lt_ρD hInverseBound hSigmaBound
          h2δ_lt_ρ hαεδ hcontract
            (x := x) (B := B)
            (by simpa [hxzero] using le_of_lt hx0)
            (by simpa [hBzero, DFstar] using le_of_lt hB0)
            hinDom hInvAll hStepAll hUpdAll k).1
      let A : JacobianQuasiNewtonIteration D F domU U x0 B0 :=
        { x := x
          B := B
          x_zero := hxzero
          B_zero := hBzero
          iterates_mem := hIteratesMem
          in_dom := hinDom
          matrices_invertible := hInvAll
          step_eq := hStepAll
          update_mem := hUpdAll }
      exact ⟨A, hLinear A⟩
    exact
      { exists_iteration := hExistsIteration
        linear := hLinear }

end Chapter05Theorem549
