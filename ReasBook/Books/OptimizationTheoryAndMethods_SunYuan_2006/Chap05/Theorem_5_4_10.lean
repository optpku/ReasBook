/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Assumption_5_4_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Theorem_5_4_9
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Theorem_5_4_10.Update
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Theorem_5_4_10.Iteration
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Theorem_5_4_10.Convergence
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section

section Chapter05Theorem5410

variable {n : ℕ}

-- Local declaration justification (source-local notation): this file formalizes one fixed
-- Euclidean ambient space from the source statement, and a public alias for that ambient model
-- would be a vacuous wrapper with no reuse outside the numbered item surface.
local notation "Point" => EuclideanSpace ℝ (Fin n)
-- Local declaration justification (source-local notation): this numbered item uses one ambient
-- operator space throughout, and introducing a public owner only for the alias would add a
-- meaningless wrapper instead of mathematical API.
local notation "Operator" => Point →L[ℝ] Point

/-- Helper for Chapter05 Theorem 5.4.10: the inverse-side support hypothesis already contains the
small-start admissibility and initial invertibility clause needed to start the iteration. -/
lemma smallStartAdmissible_of_inverseSupport
    {D : Set Point} {F : Point → Point}
    (hF : HasQuasiNewtonLocalConvergenceAssumptions D F)
    {domU : Set (Point × Operator)} {U : JacobianUpdateFunction Point}
    (hSupport :
      SupportsLocalWellDefinedInverseJacobianIteration U F hF.xStar hF.referenceInverse domU) :
    ∃ ε > 0, ∃ δ > 0, ∀ x0 H0,
      ‖x0 - hF.xStar‖ < ε →
      ‖H0 - hF.referenceInverse‖ < δ →
      (x0, H0) ∈ domU ∧ H0.IsInvertible := by
  -- Unpack the source-side small-start admissibility clause verbatim.
  exact hSupport.1

/-- Helper for Chapter05 Theorem 5.4.10: an admissible invertible initial inverse pair extends to
a raw inverse quasi-Newton orbit that stays in `domU`, stays invertible, and follows `U`. -/
lemma existsInverseOrbitInDomOfSupportedSmallStart
    {D : Set Point} {F : Point → Point}
    (hF : HasQuasiNewtonLocalConvergenceAssumptions D F)
    {domU : Set (Point × Operator)} {U : JacobianUpdateFunction Point}
    (hSupport :
      SupportsLocalWellDefinedInverseJacobianIteration U F hF.xStar hF.referenceInverse domU)
    {x0 : Point} {H0 : Operator}
    (h0 : (x0, H0) ∈ domU)
    (hH0 : H0.IsInvertible) :
    ∃ x : ℕ → Point, ∃ H : ℕ → Operator,
      x 0 = x0 ∧
      H 0 = H0 ∧
      (∀ k : ℕ, (x k, H k) ∈ domU) ∧
      (∀ k : ℕ, (H k).IsInvertible) ∧
      (∀ k : ℕ, x (k + 1) = inverseQuasiNewtonNextIterate F (x k) (H k)) ∧
      (∀ k : ℕ, H (k + 1) ∈ U (x k) (H k)) := by
  classical
  let nextState :
      {p : Point × Operator // p ∈ domU ∧ p.2.IsInvertible} →
        {p : Point × Operator // p ∈ domU ∧ p.2.IsInvertible} := fun p ↦
          let Hnext : Operator := Classical.choose (hSupport.2.1 p.1.1 p.1.2 p.2.1 p.2.2)
          let hHnext_mem : Hnext ∈ U p.1.1 p.1.2 := Classical.choose_spec
            (hSupport.2.1 p.1.1 p.1.2 p.2.1 p.2.2)
          let hAdvance := hSupport.2.2 p.1.1 p.1.2 Hnext p.2.1 p.2.2 hHnext_mem
          ⟨(inverseQuasiNewtonNextIterate F p.1.1 p.1.2, Hnext), hAdvance.2, hAdvance.1⟩
  let orbit : ℕ → {p : Point × Operator // p ∈ domU ∧ p.2.IsInvertible} :=
    Nat.rec ⟨(x0, H0), h0, hH0⟩ fun _ p ↦ nextState p
  refine ⟨fun k ↦ (orbit k).1.1, fun k ↦ (orbit k).1.2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- The recursive inverse orbit starts from the prescribed initial iterate.
    rfl
  · -- The recursive inverse orbit starts from the prescribed initial inverse approximation.
    rfl
  · -- Every recursive inverse state stays in the admissibility set by construction.
    intro k
    exact (orbit k).2.1
  · -- Every recursive inverse approximation stays invertible by construction.
    intro k
    exact (orbit k).2.2
  · -- The first component of each successor state is the inverse quasi-Newton next iterate.
    intro k
    change (nextState (orbit k)).1.1 = inverseQuasiNewtonNextIterate F (orbit k).1.1 (orbit k).1.2
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

/-- Helper for Chapter05 Theorem 5.4.10: near the reference inverse derivative
`hF.referenceInverse`, the inverse approximations themselves have uniformly bounded norm. -/
lemma normBoundNearReferenceInverse
    {D : Set Point} {F : Point → Point}
    (hF : HasQuasiNewtonLocalConvergenceAssumptions D F) :
    ∃ ρ > 0, ∃ ξ > 0, ∀ ⦃H : Operator⦄,
      ‖H - hF.referenceInverse‖ < ρ →
      ‖H‖ ≤ ξ := by
  refine
    ⟨1, zero_lt_one, ‖hF.referenceInverse‖ + 1,
      add_pos_of_nonneg_of_pos (norm_nonneg _) zero_lt_one, ?_⟩
  intro H hH
  have htriangle :
      ‖H‖ ≤ ‖H - hF.referenceInverse‖ + ‖hF.referenceInverse‖ := by
    calc
      ‖H‖ = ‖(H - hF.referenceInverse) + hF.referenceInverse‖ := by
        rw [sub_add_cancel]
      _ ≤ ‖H - hF.referenceInverse‖ + ‖hF.referenceInverse‖ := norm_add_le _ _
  have hsum :
      ‖H - hF.referenceInverse‖ + ‖hF.referenceInverse‖ ≤ 1 + ‖hF.referenceInverse‖ := by
    nlinarith [show ‖H - hF.referenceInverse‖ ≤ 1 by exact le_of_lt hH,
      show 0 ≤ ‖hF.referenceInverse‖ by exact norm_nonneg _]
  simpa [add_comm] using htriangle.trans hsum

/-- Helper for Chapter05 Theorem 5.4.10: one inverse quasi-Newton step is controlled by the
current iterate error and inverse-approximation error. -/
lemma inverseQuasiNewtonNextError_le
    {D : Set Point} {F : Point → Point}
    (hF : HasQuasiNewtonLocalConvergenceAssumptions D F)
    {x : Point} {H : Operator}
    (hx : x ∈ D) :
    ‖inverseQuasiNewtonNextIterate F x H - hF.xStar‖ ≤
      (‖H‖ * (max hF.gamma 0 * ‖x - hF.xStar‖) +
        ‖fderiv ℝ F hF.xStar‖ * ‖H - hF.referenceInverse‖) * ‖x - hF.xStar‖ := by
  let DFstar : Operator := fderiv ℝ F hF.xStar
  let e : Point := x - hF.xStar
  let remainder : Point := -F x + F hF.xStar + DFstar e
  have hRef_apply : hF.referenceInverse (DFstar e) = e := by
    simpa [DFstar, HasQuasiNewtonLocalConvergenceAssumptions.referenceInverse] using
      hF.fderiv_isInvertible.inverse_apply_self e
  have hsplit :
      hF.referenceInverse (DFstar e) =
        H (DFstar e) + (hF.referenceInverse - H) (DFstar e) := by
    calc
      hF.referenceInverse (DFstar e)
          = H (DFstar e) + (hF.referenceInverse (DFstar e) - H (DFstar e)) := by
              abel_nf
      _ = H (DFstar e) + (hF.referenceInverse - H) (DFstar e) := by
            rfl
  have hsubComm :
      hF.referenceInverse (DFstar e) - H (F x) =
        -H (F x) + hF.referenceInverse (DFstar e) := by
    calc
      hF.referenceInverse (DFstar e) - H (F x)
          = hF.referenceInverse (DFstar e) + (-H (F x)) := by
              rw [sub_eq_add_neg]
      _ = -H (F x) + hF.referenceInverse (DFstar e) := add_comm _ _
  have hremainder_eq : remainder = DFstar e - F x := by
    simp [remainder, hF.map_xStar, sub_eq_add_neg]
    abel_nf
  have hstep :
      inverseQuasiNewtonNextIterate F x H - hF.xStar =
        H remainder + (hF.referenceInverse - H) (DFstar e) := by
    -- Rewrite the inverse step around `hF.referenceInverse` and the linearization remainder.
    calc
      inverseQuasiNewtonNextIterate F x H - hF.xStar = e - H (F x) := by
        simp [inverseQuasiNewtonNextIterate, e, sub_eq_add_neg]
        abel_nf
      _ = hF.referenceInverse (DFstar e) - H (F x) := by
        exact congrArg (fun y ↦ y - H (F x)) hRef_apply.symm
      _ = -H (F x) + hF.referenceInverse (DFstar e) := hsubComm
      _ = H (DFstar e) - H (F x) + (hF.referenceInverse - H) (DFstar e) := by
        rw [hsplit, sub_eq_add_neg]
        abel_nf
      _ = H (DFstar e - F x) + (hF.referenceInverse - H) (DFstar e) := by
        have hmap : H (DFstar e - F x) = H (DFstar e) - H (F x) := by
          rw [map_sub]
        rw [hmap]
      _ = H remainder + (hF.referenceInverse - H) (DFstar e) := by
        rw [hremainder_eq]
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
      _ = max hF.gamma 0 * ‖e‖ * ‖e‖ := by
            simp [e]
  have hdefect :
      ‖(hF.referenceInverse - H) (DFstar e)‖ ≤
        ‖H - hF.referenceInverse‖ * (‖DFstar‖ * ‖e‖) := by
    -- Move the inverse-approximation defect to the rewrite-friendly `H - hF.referenceInverse`.
    have hswap :
        (hF.referenceInverse - H) (DFstar e) = -((H - hF.referenceInverse) (DFstar e)) := by
      simp
    calc
      ‖(hF.referenceInverse - H) (DFstar e)‖ = ‖(H - hF.referenceInverse) (DFstar e)‖ := by
          rw [hswap, norm_neg]
      _ ≤ ‖H - hF.referenceInverse‖ * ‖DFstar e‖ :=
            (H - hF.referenceInverse).le_opNorm (DFstar e)
      _ ≤ ‖H - hF.referenceInverse‖ * (‖DFstar‖ * ‖e‖) := by
            exact mul_le_mul_of_nonneg_left (DFstar.le_opNorm e) (norm_nonneg _)
  have hfactor :
      ‖H‖ * (max hF.gamma 0 * ‖e‖ * ‖e‖) +
          ‖DFstar‖ * ‖H - hF.referenceInverse‖ * ‖e‖ =
        (‖H‖ * (max hF.gamma 0 * ‖e‖) +
          ‖DFstar‖ * ‖H - hF.referenceInverse‖) * ‖e‖ := by
    ring
  -- Combine the exact step identity with the remainder and defect bounds.
  calc
    ‖inverseQuasiNewtonNextIterate F x H - hF.xStar‖ =
        ‖H remainder + (hF.referenceInverse - H) (DFstar e)‖ := by
          rw [hstep]
    _ ≤ ‖H remainder‖ + ‖(hF.referenceInverse - H) (DFstar e)‖ := norm_add_le _ _
    _ ≤ ‖H‖ * ‖remainder‖ + ‖(hF.referenceInverse - H) (DFstar e)‖ := by
          exact add_le_add (H.le_opNorm _) le_rfl
    _ ≤ ‖H‖ * (max hF.gamma 0 * ‖e‖ * ‖e‖) +
          ‖H - hF.referenceInverse‖ * (‖DFstar‖ * ‖e‖) := by
          exact add_le_add (mul_le_mul_of_nonneg_left hremainder (norm_nonneg _)) hdefect
    _ = ‖H‖ * (max hF.gamma 0 * ‖e‖ * ‖e‖) +
          ‖DFstar‖ * ‖H - hF.referenceInverse‖ * ‖e‖ := by
          ring
    _ = (‖H‖ * (max hF.gamma 0 * ‖x - hF.xStar‖) +
          ‖fderiv ℝ F hF.xStar‖ * ‖H - hF.referenceInverse‖) * ‖x - hF.xStar‖ := by
          simpa [e, DFstar] using hfactor

/-- Helper for Chapter05 Theorem 5.4.10: a uniform inverse bound and a uniform bound on
`‖H - hF.referenceInverse‖` turn the inverse step estimate into the dyadic half-rate
contraction `‖xₖ₊₁ - x*‖ ≤ ε * (1 / 2)^(k + 1)`. -/
lemma inverseHalfRateNextError_of_uniformBounds
    {D : Set Point} {F : Point → Point}
    (hF : HasQuasiNewtonLocalConvergenceAssumptions D F)
    {x : Point} {H : Operator} {ξ ε δ : ℝ} {k : ℕ}
    (hx : x ∈ D)
    (hHnorm : ‖H‖ ≤ ξ)
    (hHclose : ‖H - hF.referenceInverse‖ ≤ 2 * δ)
    (hxerr : ‖x - hF.xStar‖ ≤ ε * (1 / 2 : ℝ) ^ k)
    (hcontract :
      ξ * (max hF.gamma 0 * ε) + ‖fderiv ℝ F hF.xStar‖ * (2 * δ) ≤ 1 / 2) :
    ‖inverseQuasiNewtonNextIterate F x H - hF.xStar‖ ≤ ε * (1 / 2 : ℝ) ^ (k + 1) := by
  let DFstar : Operator := fderiv ℝ F hF.xStar
  have hξ_nonneg : 0 ≤ ξ := by
    exact le_trans (norm_nonneg _) hHnorm
  have hδ_nonneg : 0 ≤ δ := by
    nlinarith [norm_nonneg (H - hF.referenceInverse), hHclose]
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
    inverseQuasiNewtonNextError_le (hF := hF) (x := x) (H := H) hx
  have hinner :
      (‖H‖ * (max hF.gamma 0 * ‖x - hF.xStar‖) + ‖DFstar‖ * ‖H - hF.referenceInverse‖) *
          ‖x - hF.xStar‖ ≤
        (ξ * (max hF.gamma 0 * (ε * (1 / 2 : ℝ) ^ k)) + ‖DFstar‖ * (2 * δ)) *
          (ε * (1 / 2 : ℝ) ^ k) := by
    gcongr
  have hεpow_le_ε : ε * (1 / 2 : ℝ) ^ k ≤ ε := by
    exact mul_le_of_le_one_right hε_nonneg hpow_le_one
  have hcoeff :
      ξ * (max hF.gamma 0 * (ε * (1 / 2 : ℝ) ^ k)) + ‖DFstar‖ * (2 * δ) ≤
        ξ * (max hF.gamma 0 * ε) + ‖DFstar‖ * (2 * δ) := by
    have hγcoeff :
        max hF.gamma 0 * (ε * (1 / 2 : ℝ) ^ k) ≤ max hF.gamma 0 * ε := by
      exact mul_le_mul_of_nonneg_left hεpow_le_ε hγ_nonneg
    have hγterm :
        ξ * (max hF.gamma 0 * (ε * (1 / 2 : ℝ) ^ k)) ≤ ξ * (max hF.gamma 0 * ε) := by
      exact mul_le_mul_of_nonneg_left hγcoeff hξ_nonneg
    simpa [add_comm, add_left_comm, add_assoc] using
      add_le_add_right hγterm (‖DFstar‖ * (2 * δ))
  -- Apply the one-step estimate, then isolate the common contraction coefficient.
  calc
    ‖inverseQuasiNewtonNextIterate F x H - hF.xStar‖
        ≤ (‖H‖ * (max hF.gamma 0 * ‖x - hF.xStar‖) +
            ‖DFstar‖ * ‖H - hF.referenceInverse‖) * ‖x - hF.xStar‖ := hstep
    _ ≤ (ξ * (max hF.gamma 0 * (ε * (1 / 2 : ℝ) ^ k)) + ‖DFstar‖ * (2 * δ)) *
          (ε * (1 / 2 : ℝ) ^ k) := hinner
    _ ≤ (ξ * (max hF.gamma 0 * ε) + ‖DFstar‖ * (2 * δ)) * (ε * (1 / 2 : ℝ) ^ k) := by
          exact mul_le_mul_of_nonneg_right hcoeff hεpow_nonneg
    _ ≤ (1 / 2 : ℝ) * (ε * (1 / 2 : ℝ) ^ k) := by
          exact mul_le_mul_of_nonneg_right hcontract hεpow_nonneg
    _ = ε * (1 / 2 : ℝ) ^ (k + 1) := by
          rw [pow_succ']
          ring

/-- Helper for Chapter05 Theorem 5.4.10: `inverseQuasiNewtonSigma x xNext xStar` is bounded by
any common upper bound for the current and next iterate errors. -/
lemma inverseQuasiNewtonSigma_le_of_error_bounds
    {x xNext xStar : Point} {r : ℝ}
    (hx : ‖x - xStar‖ ≤ r)
    (hnext : ‖xNext - xStar‖ ≤ r) :
    inverseQuasiNewtonSigma x xNext xStar ≤ r := by
  -- Normalize the inverse-side `σ` quantity to a maximum of the two endpoint errors.
  simpa [inverseQuasiNewtonSigma, max_le_iff] using And.intro hx hnext

/-- Helper for Chapter05 Theorem 5.4.10: under the inverse additive update inequality `(5.4.60)`,
a raw inverse quasi-Newton orbit satisfies the uniform domain, iterate, and inverse-error bounds
needed for the dyadic half-rate argument. -/
lemma inverseAdditiveUpdateOrbitInvariants
    {D : Set Point} {F : Point → Point}
    (hF : HasQuasiNewtonLocalConvergenceAssumptions D F)
    {domU : Set (Point × Operator)} {U : JacobianUpdateFunction Point}
    {γu ρD ρ ξ ε δ : ℝ}
    (hball : Metric.ball hF.xStar ρD ⊆ D)
    (hε_pos : 0 < ε)
    (hε_lt_ρD : ε < ρD)
    (hnorm : ∀ ⦃H : Operator⦄, ‖H - hF.referenceInverse‖ < ρ → ‖H‖ ≤ ξ)
    (hadd :
      ∀ x H Hnext,
        (x, H) ∈ domU →
        Hnext ∈ U x H →
          ‖Hnext - hF.referenceInverse‖ ≤
            ‖H - hF.referenceInverse‖ +
              (γu / 2) *
                (‖inverseQuasiNewtonNextIterate F x H - hF.xStar‖ + ‖x - hF.xStar‖))
    (h2δ_lt_ρ : 2 * δ < ρ)
    (hγuε : 3 * max γu 0 * ε ≤ 2 * δ)
    (hcontract :
      ξ * (max hF.gamma 0 * ε) + ‖fderiv ℝ F hF.xStar‖ * (2 * δ) ≤ 1 / 2)
    {x : ℕ → Point} {H : ℕ → Operator}
    (hx0 : ‖x 0 - hF.xStar‖ ≤ ε)
    (hH0 : ‖H 0 - hF.referenceInverse‖ ≤ δ)
    (hinDom : ∀ k : ℕ, (x k, H k) ∈ domU)
    (hStep : ∀ k : ℕ, x (k + 1) = inverseQuasiNewtonNextIterate F (x k) (H k))
    (hUpd : ∀ k : ℕ, H (k + 1) ∈ U (x k) (H k)) :
    ∀ k : ℕ,
      x k ∈ D ∧
        ‖x k - hF.xStar‖ ≤ ε * (1 / 2 : ℝ) ^ k ∧
          ‖H k - hF.referenceInverse‖ ≤ 2 * δ - δ * (1 / 2 : ℝ) ^ k := by
  have hδ_nonneg : 0 ≤ δ := by
    nlinarith [norm_nonneg (H 0 - hF.referenceInverse), hH0]
  intro k
  induction k with
  | zero =>
      -- The initial inverse state is small enough to lie in the domain ball and satisfy the
      -- dyadic bound.
      refine ⟨?_, ?_, ?_⟩
      · apply hball
        simpa [Metric.mem_ball, dist_eq_norm] using lt_of_le_of_lt hx0 hε_lt_ρD
      · simpa using hx0
      · have hδ_eq : 2 * δ - δ = δ := by
          ring
        simpa [hδ_eq] using hH0
  | succ k hk =>
      rcases hk with ⟨hxkD, hxk, hHk⟩
      have hpow_nonneg : 0 ≤ (1 / 2 : ℝ) ^ k := by
        positivity
      have hHk_two_delta : ‖H k - hF.referenceInverse‖ ≤ 2 * δ := by
        nlinarith
      have hHk_lt_ρ : ‖H k - hF.referenceInverse‖ < ρ := by
        exact lt_of_le_of_lt hHk_two_delta h2δ_lt_ρ
      have hNormBound : ‖H k‖ ≤ ξ := hnorm hHk_lt_ρ
      have hnext_raw :
          ‖inverseQuasiNewtonNextIterate F (x k) (H k) - hF.xStar‖ ≤
            ε * (1 / 2 : ℝ) ^ (k + 1) := by
        -- The current iterate and inverse approximation fit the uniform contraction lemma.
        exact inverseHalfRateNextError_of_uniformBounds hF hxkD hNormBound hHk_two_delta hxk
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
          (γu / 2) * (‖inverseQuasiNewtonNextIterate F (x k) (H k) - hF.xStar‖ +
              ‖x k - hF.xStar‖) ≤
            (max γu 0 / 2) *
              (‖inverseQuasiNewtonNextIterate F (x k) (H k) - hF.xStar‖ +
                ‖x k - hF.xStar‖) := by
        have hsum_nonneg :
            0 ≤ ‖inverseQuasiNewtonNextIterate F (x k) (H k) - hF.xStar‖ +
                ‖x k - hF.xStar‖ := by
          positivity
        have hcoef : γu / 2 ≤ max γu 0 / 2 := by
          nlinarith [le_max_left γu 0]
        exact mul_le_mul_of_nonneg_right hcoef hsum_nonneg
      have hHk_succ_raw :
          ‖H (k + 1) - hF.referenceInverse‖ ≤
            ‖H k - hF.referenceInverse‖ +
              (max γu 0 / 2) *
                (‖inverseQuasiNewtonNextIterate F (x k) (H k) - hF.xStar‖ +
                  ‖x k - hF.xStar‖) := by
        exact le_trans (hadd (x k) (H k) (H (k + 1)) (hinDom k) (hUpd k)) <|
          add_le_add_right hγu_scaled _
      have hγuε_quarter : (3 * max γu 0 * ε) / 4 ≤ δ / 2 := by
        nlinarith
      have hHk_succ :
          ‖H (k + 1) - hF.referenceInverse‖ ≤
            2 * δ - δ * (1 / 2 : ℝ) ^ (k + 1) := by
        -- The additive inverse update contributes at most one more dyadic error increment.
        calc
          ‖H (k + 1) - hF.referenceInverse‖
              ≤ ‖H k - hF.referenceInverse‖ +
                  (max γu 0 / 2) *
                    (‖inverseQuasiNewtonNextIterate F (x k) (H k) - hF.xStar‖ +
                      ‖x k - hF.xStar‖) :=
                hHk_succ_raw
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
      exact ⟨hxnextD, hnext, hHk_succ⟩

/-- Helper for Chapter05 Theorem 5.4.10: under the inverse `σ`-controlled update inequality
`(5.4.61)`, a raw inverse quasi-Newton orbit satisfies the same dyadic iterate and inverse-error
bounds as in the additive branch. -/
lemma inverseSigmaUpdateOrbitInvariants
    {D : Set Point} {F : Point → Point}
    (hF : HasQuasiNewtonLocalConvergenceAssumptions D F)
    {domU : Set (Point × Operator)} {U : JacobianUpdateFunction Point}
    {α1 α2 ρD ρ ξ ε δ : ℝ}
    (hball : Metric.ball hF.xStar ρD ⊆ D)
    (hε_pos : 0 < ε)
    (hε_lt_ρD : ε < ρD)
    (hnorm : ∀ ⦃H : Operator⦄, ‖H - hF.referenceInverse‖ < ρ → ‖H‖ ≤ ξ)
    (hsigma :
      ∀ x H Hnext,
        (x, H) ∈ domU →
        Hnext ∈ U x H →
          ‖Hnext - hF.referenceInverse‖ ≤
            (1 + α1 *
                inverseQuasiNewtonSigma x (inverseQuasiNewtonNextIterate F x H) hF.xStar) *
              ‖H - hF.referenceInverse‖ +
            α2 *
              inverseQuasiNewtonSigma x (inverseQuasiNewtonNextIterate F x H) hF.xStar)
    (h2δ_lt_ρ : 2 * δ < ρ)
    (hαεδ : 2 * (2 * max α1 0 * δ + max α2 0) * ε ≤ δ)
    (hcontract :
      ξ * (max hF.gamma 0 * ε) + ‖fderiv ℝ F hF.xStar‖ * (2 * δ) ≤ 1 / 2)
    {x : ℕ → Point} {H : ℕ → Operator}
    (hx0 : ‖x 0 - hF.xStar‖ ≤ ε)
    (hH0 : ‖H 0 - hF.referenceInverse‖ ≤ δ)
    (hinDom : ∀ k : ℕ, (x k, H k) ∈ domU)
    (hStep : ∀ k : ℕ, x (k + 1) = inverseQuasiNewtonNextIterate F (x k) (H k))
    (hUpd : ∀ k : ℕ, H (k + 1) ∈ U (x k) (H k)) :
    ∀ k : ℕ,
      x k ∈ D ∧
        ‖x k - hF.xStar‖ ≤ ε * (1 / 2 : ℝ) ^ k ∧
          ‖H k - hF.referenceInverse‖ ≤ 2 * δ - δ * (1 / 2 : ℝ) ^ k := by
  have hδ_nonneg : 0 ≤ δ := by
    nlinarith [norm_nonneg (H 0 - hF.referenceInverse), hH0]
  intro k
  induction k with
  | zero =>
      -- The initial inverse state already satisfies the claimed dyadic bounds.
      refine ⟨?_, ?_, ?_⟩
      · apply hball
        simpa [Metric.mem_ball, dist_eq_norm] using lt_of_le_of_lt hx0 hε_lt_ρD
      · simpa using hx0
      · have hδ_eq : 2 * δ - δ = δ := by
          ring
        simpa [hδ_eq] using hH0
  | succ k hk =>
      rcases hk with ⟨hxkD, hxk, hHk⟩
      have hpow_nonneg : 0 ≤ (1 / 2 : ℝ) ^ k := by
        positivity
      have hHk_two_delta : ‖H k - hF.referenceInverse‖ ≤ 2 * δ := by
        nlinarith
      have hHk_lt_ρ : ‖H k - hF.referenceInverse‖ < ρ := by
        exact lt_of_le_of_lt hHk_two_delta h2δ_lt_ρ
      have hNormBound : ‖H k‖ ≤ ξ := hnorm hHk_lt_ρ
      have hnext_raw :
          ‖inverseQuasiNewtonNextIterate F (x k) (H k) - hF.xStar‖ ≤
            ε * (1 / 2 : ℝ) ^ (k + 1) := by
        -- Reuse the common inverse half-rate contraction once the inverse error is uniformly
        -- bounded.
        exact inverseHalfRateNextError_of_uniformBounds hF hxkD hNormBound hHk_two_delta hxk
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
          inverseQuasiNewtonSigma (x k) (inverseQuasiNewtonNextIterate F (x k) (H k)) hF.xStar ≤
            ε * (1 / 2 : ℝ) ^ k := by
        apply inverseQuasiNewtonSigma_le_of_error_bounds
        · exact hxk
        · calc
            ‖inverseQuasiNewtonNextIterate F (x k) (H k) - hF.xStar‖
                ≤ ε * (1 / 2 : ℝ) ^ (k + 1) := hnext_raw
            _ ≤ ε * (1 / 2 : ℝ) ^ k := by
                  rw [pow_succ']
                  nlinarith
      have hσ_nonneg :
          0 ≤ inverseQuasiNewtonSigma (x k) (inverseQuasiNewtonNextIterate F (x k) (H k))
            hF.xStar := by
        simp [inverseQuasiNewtonSigma]
      have hα1_scaled :
          α1 *
              inverseQuasiNewtonSigma (x k) (inverseQuasiNewtonNextIterate F (x k) (H k))
                hF.xStar ≤
            max α1 0 *
              inverseQuasiNewtonSigma (x k) (inverseQuasiNewtonNextIterate F (x k) (H k))
                hF.xStar := by
        exact mul_le_mul_of_nonneg_right (by exact le_max_left _ _) hσ_nonneg
      have hα2_scaled :
          α2 *
              inverseQuasiNewtonSigma (x k) (inverseQuasiNewtonNextIterate F (x k) (H k))
                hF.xStar ≤
            max α2 0 *
              inverseQuasiNewtonSigma (x k) (inverseQuasiNewtonNextIterate F (x k) (H k))
                hF.xStar := by
        exact mul_le_mul_of_nonneg_right (by exact le_max_left _ _) hσ_nonneg
      have hHk_succ_raw :
          ‖H (k + 1) - hF.referenceInverse‖ ≤
            (1 +
                max α1 0 *
                  inverseQuasiNewtonSigma (x k)
                    (inverseQuasiNewtonNextIterate F (x k) (H k)) hF.xStar) *
                ‖H k - hF.referenceInverse‖ +
              max α2 0 *
                inverseQuasiNewtonSigma (x k)
                  (inverseQuasiNewtonNextIterate F (x k) (H k)) hF.xStar := by
        have hraw := hsigma (x k) (H k) (H (k + 1)) (hinDom k) (hUpd k)
        have hmul :
            (1 +
                α1 *
                  inverseQuasiNewtonSigma (x k)
                    (inverseQuasiNewtonNextIterate F (x k) (H k)) hF.xStar) *
                ‖H k - hF.referenceInverse‖ ≤
              (1 +
                  max α1 0 *
                    inverseQuasiNewtonSigma (x k)
                      (inverseQuasiNewtonNextIterate F (x k) (H k)) hF.xStar) *
                ‖H k - hF.referenceInverse‖ := by
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
      have hHk_succ :
          ‖H (k + 1) - hF.referenceInverse‖ ≤
            2 * δ - δ * (1 / 2 : ℝ) ^ (k + 1) := by
        -- The inverse-side `σ`-term is controlled by the current dyadic iterate bound, so the
        -- inverse error gains the same one-step dyadic increment as in the additive branch.
        calc
          ‖H (k + 1) - hF.referenceInverse‖
              ≤ (1 +
                    max α1 0 *
                      inverseQuasiNewtonSigma (x k)
                        (inverseQuasiNewtonNextIterate F (x k) (H k)) hF.xStar) *
                    ‖H k - hF.referenceInverse‖ +
                  max α2 0 *
                    inverseQuasiNewtonSigma (x k)
                      (inverseQuasiNewtonNextIterate F (x k) (H k)) hF.xStar :=
                hHk_succ_raw
          _ = ‖H k - hF.referenceInverse‖ +
                (max α1 0 *
                    inverseQuasiNewtonSigma (x k)
                      (inverseQuasiNewtonNextIterate F (x k) (H k)) hF.xStar) *
                  ‖H k - hF.referenceInverse‖ +
                max α2 0 *
                  inverseQuasiNewtonSigma (x k)
                    (inverseQuasiNewtonNextIterate F (x k) (H k)) hF.xStar := by
                ring
          _ ≤ ‖H k - hF.referenceInverse‖ +
                (max α1 0 *
                    inverseQuasiNewtonSigma (x k)
                      (inverseQuasiNewtonNextIterate F (x k) (H k)) hF.xStar) * (2 * δ) +
                max α2 0 *
                  inverseQuasiNewtonSigma (x k)
                    (inverseQuasiNewtonNextIterate F (x k) (H k)) hF.xStar := by
                gcongr
          _ = ‖H k - hF.referenceInverse‖ +
                (2 * max α1 0 * δ + max α2 0) *
                  inverseQuasiNewtonSigma (x k)
                    (inverseQuasiNewtonNextIterate F (x k) (H k)) hF.xStar := by
                ring
          _ ≤ (2 * δ - δ * (1 / 2 : ℝ) ^ k) +
                (2 * max α1 0 * δ + max α2 0) * (ε * (1 / 2 : ℝ) ^ k) := by
                gcongr
          _ ≤ (2 * δ - δ * (1 / 2 : ℝ) ^ k) + (δ / 2) * (1 / 2 : ℝ) ^ k := by
                exact add_le_add_right hαincrement _
          _ = 2 * δ - δ * (1 / 2 : ℝ) ^ (k + 1) := by
                rw [pow_succ']
                ring
      exact ⟨hxnextD, hnext, hHk_succ⟩

/-- Helper for Chapter05 Theorem 5.4.10: the inverse update hypotheses yield radii that make
every sufficiently small start admissible, initially invertible, and inverse-side linearly
convergent. -/
lemma existsSmallStartInverseConvergenceData
    {D : Set Point} {F : Point → Point}
    (hF : HasQuasiNewtonLocalConvergenceAssumptions D F)
    (domU : Set (Point × Operator))
    (U : JacobianUpdateFunction Point)
    (h_update :
      (∃ γ : ℝ,
        SatisfiesInverseAdditiveLocalUpdateBound U F hF.xStar hF.referenceInverse domU γ) ∨
      ∃ α₁ α₂ : ℝ,
        SatisfiesInverseSigmaLocalUpdateBound U F hF.xStar hF.referenceInverse domU α₁ α₂) :
    ∃ ε > 0, ∃ δ > 0,
      ∀ x0 : Point, ∀ H0 : Operator,
        ‖x0 - hF.xStar‖ < ε →
        ‖H0 - hF.referenceInverse‖ < δ →
          (x0, H0) ∈ domU ∧
            H0.IsInvertible ∧
              InverseJacobianQuasiNewtonSmallStartConvergence D F domU U hF.xStar x0 H0 := by
  let DFstar : Operator := fderiv ℝ F hF.xStar
  let γF0 : ℝ := max hF.gamma 0
  let DFplus : ℝ := ‖DFstar‖ + 1
  have hγF0_nonneg : 0 ≤ γF0 := by
    simp [γF0]
  have hγF0_add_one_pos : 0 < γF0 + 1 := by
    linarith
  have hDFplus_pos : 0 < DFplus := by
    dsimp [DFplus]
    positivity
  have hDFstar_le_DFplus : ‖DFstar‖ ≤ DFplus := by
    dsimp [DFplus]
    nlinarith [norm_nonneg DFstar]
  have hDnhds : D ∈ nhds hF.xStar := hF.open_domain.mem_nhds hF.xStar_mem
  rcases Metric.mem_nhds_iff.mp hDnhds with ⟨ρD, hρD_pos, hball⟩
  rcases normBoundNearReferenceInverse hF with ⟨ρ, hρ_pos, ξ, hξ_pos, hNormBound⟩
  -- Route correction: the inverse hypotheses control `H` directly, so we reuse the dyadic
  -- half-rate skeleton from Theorem 5.4.9 inside inverse variables instead of transporting the
  -- update inequality to Jacobian approximations first.
  rcases h_update with ⟨γu, hAdd⟩ | ⟨α1, α2, hSigma⟩
  · let γu0 : ℝ := max γu 0
    have hγu0_nonneg : 0 ≤ γu0 := by
      simp [γu0]
    let hSupport := hAdd.1
    have hAddBound :
        ∀ x H Hnext,
          (x, H) ∈ domU →
          Hnext ∈ U x H →
            ‖Hnext - hF.referenceInverse‖ ≤
              ‖H - hF.referenceInverse‖ +
                (γu / 2) *
                  (‖inverseQuasiNewtonNextIterate F x H - hF.xStar‖ + ‖x - hF.xStar‖) := by
      intro x H Hnext hx hHnext
      exact hAdd.2 hx hHnext
    rcases smallStartAdmissible_of_inverseSupport hF hSupport with
      ⟨εs, hεs_pos, δs, hδs_pos, hsmall⟩
    let δ : ℝ := min (δs / 2) (min (ρ / 4) (1 / (8 * DFplus)))
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
    have hδ_le_inv : δ ≤ 1 / (8 * DFplus) := by
      dsimp [δ]
      exact le_trans (min_le_right _ _) (min_le_right _ _)
    have h2δ_lt_ρ : 2 * δ < ρ := by
      nlinarith
    let ε : ℝ :=
      min (εs / 2)
        (min (ρD / 2) (min (δ / (3 * γu0 + 1)) (1 / (4 * ξ * (γF0 + 1)))))
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
      have hγF0ε : γF0 * ε ≤ (γF0 + 1) * ε := by
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
    have hδpart : ‖DFstar‖ * (2 * δ) ≤ 1 / 4 := by
      have htwoδ :
          2 * δ ≤ 2 * (1 / (8 * DFplus)) := by
        exact mul_le_mul_of_nonneg_left hδ_le_inv (by positivity)
      have htwoδ' : 2 * δ ≤ 1 / (4 * DFplus) := by
        have hrewrite : 2 * (1 / (8 * DFplus)) = 1 / (4 * DFplus) := by
          field_simp [hDFplus_pos.ne']
          ring
        exact htwoδ.trans_eq hrewrite
      have hmul : ‖DFstar‖ * (2 * δ) ≤ ‖DFstar‖ * (1 / (4 * DFplus)) := by
        exact mul_le_mul_of_nonneg_left htwoδ' (norm_nonneg _)
      have hupper :
          ‖DFstar‖ * (1 / (4 * DFplus)) ≤ DFplus * (1 / (4 * DFplus)) := by
        exact mul_le_mul_of_nonneg_right hDFstar_le_DFplus (by positivity)
      have hrewrite : DFplus * (1 / (4 * DFplus)) = 1 / 4 := by
        field_simp [hDFplus_pos.ne']
      exact hmul.trans (hupper.trans_eq hrewrite)
    have hcontract :
        ξ * (γF0 * ε) + ‖DFstar‖ * (2 * δ) ≤ 1 / 2 := by
      nlinarith [hγpart, hδpart]
    refine ⟨ε, hε_pos, δ, hδ_pos, ?_⟩
    intro x0 H0 hx0 hH0
    have h0small := hsmall x0 H0 (lt_trans hx0 hε_lt_εs) (lt_trans hH0 hδ_lt_δs)
    rcases h0small with ⟨h0dom, hH0inv⟩
    have hLinear :
        ∀ A : InverseJacobianQuasiNewtonIteration D F domU U x0 H0,
          LinearlyConvergesTo A.x hF.xStar := by
      intro A
      have hOrbit :=
        inverseAdditiveUpdateOrbitInvariants hF hball hε_pos hε_lt_ρD hNormBound hAddBound
          h2δ_lt_ρ hγuε hcontract
            (x := A.x) (H := A.H)
            (by simpa [A.x_zero] using le_of_lt hx0)
            (by simpa [A.H_zero] using le_of_lt hH0)
            A.in_dom A.step_eq A.update_mem
      exact
        linearlyConvergesTo_of_halfRate A.x hF.xStar (le_of_lt hε_pos) fun k ↦ (hOrbit k).2.1
    have hExistsIteration :
        ∃ A : InverseJacobianQuasiNewtonIteration D F domU U x0 H0,
          LinearlyConvergesTo A.x hF.xStar := by
      rcases existsInverseOrbitInDomOfSupportedSmallStart hF hSupport h0dom hH0inv with
        ⟨x, H, hxzero, hHzero, hinDom, hInvAll, hStepAll, hUpdAll⟩
      have hIteratesMem : ∀ k : ℕ, x k ∈ D := by
        intro k
        exact (inverseAdditiveUpdateOrbitInvariants hF hball hε_pos hε_lt_ρD hNormBound
          hAddBound h2δ_lt_ρ hγuε hcontract
            (x := x) (H := H)
            (by simpa [hxzero] using le_of_lt hx0)
            (by simpa [hHzero] using le_of_lt hH0)
            hinDom hStepAll hUpdAll k).1
      let A : InverseJacobianQuasiNewtonIteration D F domU U x0 H0 :=
        { x := x
          H := H
          x_zero := hxzero
          H_zero := hHzero
          iterates_mem := hIteratesMem
          in_dom := hinDom
          step_eq := hStepAll
          update_mem := hUpdAll }
      exact ⟨A, hLinear A⟩
    exact ⟨h0dom, hH0inv, ⟨hExistsIteration, hLinear⟩⟩
  · let α10 : ℝ := max α1 0
    let α20 : ℝ := max α2 0
    have hα10_nonneg : 0 ≤ α10 := by
      simp [α10]
    have hα20_nonneg : 0 ≤ α20 := by
      simp [α20]
    let hSupport := hSigma.1
    have hSigmaBound :
        ∀ x H Hnext,
          (x, H) ∈ domU →
          Hnext ∈ U x H →
            ‖Hnext - hF.referenceInverse‖ ≤
              (1 + α1 * inverseQuasiNewtonSigma x (inverseQuasiNewtonNextIterate F x H)
                    hF.xStar) *
                ‖H - hF.referenceInverse‖ +
              α2 * inverseQuasiNewtonSigma x (inverseQuasiNewtonNextIterate F x H) hF.xStar := by
      intro x H Hnext hx hHnext
      exact hSigma.2 hx hHnext
    rcases smallStartAdmissible_of_inverseSupport hF hSupport with
      ⟨εs, hεs_pos, δs, hδs_pos, hsmall⟩
    let δ : ℝ := min (δs / 2) (min (ρ / 4) (1 / (8 * DFplus)))
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
    have hδ_le_inv : δ ≤ 1 / (8 * DFplus) := by
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
    have hε_le_δratio : ε ≤ δ / (2 * (2 * α10 * δ + α20 + 1)) := by
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
        exact (le_div_iff₀ hden_pos).mp hε_le_δratio
      nlinarith
    have hγpart :
        ξ * (γF0 * ε) ≤ 1 / 4 := by
      have hγF0ε : γF0 * ε ≤ (γF0 + 1) * ε := by
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
    have hδpart : ‖DFstar‖ * (2 * δ) ≤ 1 / 4 := by
      have htwoδ :
          2 * δ ≤ 2 * (1 / (8 * DFplus)) := by
        exact mul_le_mul_of_nonneg_left hδ_le_inv (by positivity)
      have htwoδ' : 2 * δ ≤ 1 / (4 * DFplus) := by
        have hrewrite : 2 * (1 / (8 * DFplus)) = 1 / (4 * DFplus) := by
          field_simp [hDFplus_pos.ne']
          ring
        exact htwoδ.trans_eq hrewrite
      have hmul : ‖DFstar‖ * (2 * δ) ≤ ‖DFstar‖ * (1 / (4 * DFplus)) := by
        exact mul_le_mul_of_nonneg_left htwoδ' (norm_nonneg _)
      have hupper :
          ‖DFstar‖ * (1 / (4 * DFplus)) ≤ DFplus * (1 / (4 * DFplus)) := by
        exact mul_le_mul_of_nonneg_right hDFstar_le_DFplus (by positivity)
      have hrewrite : DFplus * (1 / (4 * DFplus)) = 1 / 4 := by
        field_simp [hDFplus_pos.ne']
      exact hmul.trans (hupper.trans_eq hrewrite)
    have hcontract :
        ξ * (γF0 * ε) + ‖DFstar‖ * (2 * δ) ≤ 1 / 2 := by
      nlinarith [hγpart, hδpart]
    refine ⟨ε, hε_pos, δ, hδ_pos, ?_⟩
    intro x0 H0 hx0 hH0
    have h0small := hsmall x0 H0 (lt_trans hx0 hε_lt_εs) (lt_trans hH0 hδ_lt_δs)
    rcases h0small with ⟨h0dom, hH0inv⟩
    have hLinear :
        ∀ A : InverseJacobianQuasiNewtonIteration D F domU U x0 H0,
          LinearlyConvergesTo A.x hF.xStar := by
      intro A
      have hOrbit :=
        inverseSigmaUpdateOrbitInvariants hF hball hε_pos hε_lt_ρD hNormBound hSigmaBound
          h2δ_lt_ρ hαεδ hcontract
            (x := A.x) (H := A.H)
            (by simpa [A.x_zero] using le_of_lt hx0)
            (by simpa [A.H_zero] using le_of_lt hH0)
            A.in_dom A.step_eq A.update_mem
      exact
        linearlyConvergesTo_of_halfRate A.x hF.xStar (le_of_lt hε_pos) fun k ↦ (hOrbit k).2.1
    have hExistsIteration :
        ∃ A : InverseJacobianQuasiNewtonIteration D F domU U x0 H0,
          LinearlyConvergesTo A.x hF.xStar := by
      rcases existsInverseOrbitInDomOfSupportedSmallStart hF hSupport h0dom hH0inv with
        ⟨x, H, hxzero, hHzero, hinDom, hInvAll, hStepAll, hUpdAll⟩
      have hIteratesMem : ∀ k : ℕ, x k ∈ D := by
        intro k
        exact (inverseSigmaUpdateOrbitInvariants hF hball hε_pos hε_lt_ρD hNormBound
          hSigmaBound h2δ_lt_ρ hαεδ hcontract
            (x := x) (H := H)
            (by simpa [hxzero] using le_of_lt hx0)
            (by simpa [hHzero] using le_of_lt hH0)
            hinDom hStepAll hUpdAll k).1
      let A : InverseJacobianQuasiNewtonIteration D F domU U x0 H0 :=
        { x := x
          H := H
          x_zero := hxzero
          H_zero := hHzero
          iterates_mem := hIteratesMem
          in_dom := hinDom
          step_eq := hStepAll
          update_mem := hUpdAll }
      exact ⟨A, hLinear A⟩
    exact ⟨h0dom, hH0inv, ⟨hExistsIteration, hLinear⟩⟩

namespace InverseJacobianQuasiNewtonSmallStartConvergence

/-- Chapter05 Theorem 5.4.10: let `F : ℝ^n → ℝ^n` satisfy Chapter05 Assumption 5.4.1, and let
`U` be a set-valued inverse quasi-Newton update rule on pairs `(xₖ, Hₖ)`. Assume that every
admissible update satisfies either the inverse-side additive estimate `(5.4.60)` or the
inverse-side `σ`-estimate `(5.4.61)` relative to the reference inverse derivative
`hF.referenceInverse = F'(x*)⁻¹`, with the source-side small-start admissibility and update
well-definedness conditions folded into that inverse update hypothesis. Then there exist
constants `ε` and `δ` such that every initial pair `(x₀, H₀)` with
`‖x₀ - hF.xStar‖ < ε` and `‖H₀ - hF.referenceInverse‖ < δ` admits a canonical inverse-side run
whose underlying Jacobian-side realization lives on the inverse-induced bridge data
`jacobianDomOfInverse domU`, `jacobianUpdateOfInverse U`; every such inverse-side run has
iterate sequence converging linearly to `hF.xStar`. -/
theorem ofUpdateCondition
    {D : Set Point} {F : Point → Point}
    (hF : HasQuasiNewtonLocalConvergenceAssumptions D F)
    (domU : Set (Point × Operator))
    (U : JacobianUpdateFunction Point)
    (h_update :
      (∃ γ : ℝ,
        SatisfiesInverseAdditiveLocalUpdateBound U F hF.xStar hF.referenceInverse domU γ) ∨
      ∃ α₁ α₂ : ℝ,
        SatisfiesInverseSigmaLocalUpdateBound U F hF.xStar hF.referenceInverse domU α₁ α₂) :
    ∃ ε > 0, ∃ δ > 0,
      ∀ x0 : Point, ∀ H0 : Operator,
        ‖x0 - hF.xStar‖ < ε →
        ‖H0 - hF.referenceInverse‖ < δ →
          InverseJacobianQuasiNewtonSmallStartConvergence D F domU U hF.xStar x0 H0 := by
  -- Reuse the theorem-local helper that also records small-start admissibility and initial
  -- invertibility; the public theorem only needs the packaged convergence owner.
  rcases existsSmallStartInverseConvergenceData hF domU U h_update with ⟨ε, hε, δ, hδ, hsmall⟩
  refine ⟨ε, hε, δ, hδ, ?_⟩
  intro x0 H0 hx0 hH0
  exact (hsmall x0 H0 hx0 hH0).2.2

end InverseJacobianQuasiNewtonSmallStartConvergence

namespace JacobianQuasiNewtonSmallStartConvergence

/-- Theorem 5.4.10 packaged back into the canonical Jacobian-side small-start owner on the
inverse-induced bridge data. -/
theorem ofInverseUpdateCondition
    {D : Set Point} {F : Point → Point}
    (hF : HasQuasiNewtonLocalConvergenceAssumptions D F)
    (domU : Set (Point × Operator))
    (U : JacobianUpdateFunction Point)
    (h_update :
      (∃ γ : ℝ,
        SatisfiesInverseAdditiveLocalUpdateBound U F hF.xStar hF.referenceInverse domU γ) ∨
      ∃ α₁ α₂ : ℝ,
        SatisfiesInverseSigmaLocalUpdateBound U F hF.xStar hF.referenceInverse domU α₁ α₂) :
    ∃ ε > 0, ∃ δ > 0,
      ∀ x0 : Point, ∀ H0 : Operator,
        ‖x0 - hF.xStar‖ < ε →
        ‖H0 - hF.referenceInverse‖ < δ →
          JacobianQuasiNewtonSmallStartConvergence D F (jacobianDomOfInverse domU)
            (jacobianUpdateOfInverse U) hF.xStar x0 H0.inverse := by
  rcases existsSmallStartInverseConvergenceData hF domU U h_update with
    ⟨ε, hε, δ, hδ, hsmall⟩
  refine ⟨ε, hε, δ, hδ, ?_⟩
  intro x0 H0 hx0 hH0
  rcases hsmall x0 H0 hx0 hH0 with ⟨_, hH0inv, hconv⟩
  have hSupport :
      SupportsLocalWellDefinedInverseJacobianIteration U F hF.xStar hF.referenceInverse domU := by
    rcases h_update with ⟨γ, hAdd⟩ | ⟨α₁, α₂, hSigma⟩
    · exact hAdd.1
    · exact hSigma.1
  have hInvertibleAll :
      ∀ A : InverseJacobianQuasiNewtonIteration D F domU U x0 H0, ∀ k : ℕ,
        (A.H k).IsInvertible := by
    intro A k
    induction k with
    | zero =>
        -- The small-start admissibility clause supplies the initial invertibility.
        simpa [A.H_zero] using hH0inv
    | succ k hk =>
        -- The support hypothesis propagates invertibility through every admissible update.
        exact (hSupport.2.2 (A.x k) (A.H k) (A.H (k + 1)) (A.in_dom k) hk (A.update_mem k)).1
  exact hconv.toJacobian hInvertibleAll

end JacobianQuasiNewtonSmallStartConvergence

end Chapter05Theorem5410
