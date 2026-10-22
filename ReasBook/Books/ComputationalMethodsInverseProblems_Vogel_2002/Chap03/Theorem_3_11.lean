/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap03.Theorem_3_11.Convergence
public import Mathlib.Analysis.InnerProductSpace.Rayleigh
public import Mathlib.Order.Filter.Extr

public section

noncomputable section

namespace Newton

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Backend generalized Newton error estimate: if the Hessian near `fStar` is the
genuine second Fréchet derivative of `J`, `hModel : HasQuadraticConvergenceModel J fStar K μ`
bundles `gradient J fStar = 0`, self-adjoint strong positivity of `hessian J fStar`,
`K`-Lipschitz continuity of `f ↦ hessian J f`, and the explicit lower bound
`μ * ‖h‖ ^ 2 ≤ inner ℝ (hessian J fStar h) h`, and the initial iterate satisfies
`StartsInConvergenceBall f fStar K μ`, then the Newton iterates satisfy the quadratic
error estimate
`‖f (v + 1) - fStar‖ ≤ convergenceConstant K μ * ‖f v - fStar‖ ^ 2`. -/
theorem quadraticErrorBound
    (J : H → ℝ) (f : ℕ → H) (fStar : H) {K : NNReal} {μ : ℝ}
    (hSecondDerivative :
      ∀ᶠ y in nhds fStar,
        HasFDerivAt J (fderiv ℝ J y) y ∧
          HasFDerivAt (fderiv ℝ J) (fderiv ℝ (fderiv ℝ J) y) y)
    (hModel : HasQuadraticConvergenceModel J fStar K μ)
    (hNewton : IsIterateSequence J f)
    (h0 : StartsInConvergenceBall f fStar K μ) :
    ∀ v : ℕ,
      ‖f (v + 1) - fStar‖ ≤
        convergenceConstant K μ * ‖f v - fStar‖ ^ 2 := by
  -- Route correction: the standard Newton remainder estimate needs `fderiv ℝ J` to have the
  -- displayed derivative on every point of the segment from `fStar` to `f v`, or at least on a
  -- neighborhood containing the public convergence ball. The current hypothesis only supplies this
  -- derivative eventually at `fStar`, so the analytic core is not available for arbitrary starts
  -- satisfying `StartsInConvergenceBall`.
  sorry

/-- Backend generalized Newton convergence statement corresponding to
`quadraticErrorBound`. Under the same hypotheses, if the initial iterate satisfies
`StartsInConvergenceBall f fStar K μ`, then the Newton iterates converge to `fStar`. -/
theorem tendsto_fStar
    (J : H → ℝ) (f : ℕ → H) (fStar : H) {K : NNReal} {μ : ℝ}
    (hSecondDerivative :
      ∀ᶠ y in nhds fStar,
        HasFDerivAt J (fderiv ℝ J y) y ∧
          HasFDerivAt (fderiv ℝ J) (fderiv ℝ (fderiv ℝ J) y) y)
    (hModel : HasQuadraticConvergenceModel J fStar K μ)
    (hNewton : IsIterateSequence J f)
    (h0 : StartsInConvergenceBall f fStar K μ) :
    Filter.Tendsto f Filter.atTop (nhds fStar) := by
  -- Route correction: convergence is downstream of `quadraticErrorBound`, so the same missing
  -- neighborhood/segment regularity blocks the proof here as well.
  sorry

/-- The source `lambda_min (H_*)` represented by the infimum Rayleigh quotient of
`hessian J fStar`. -/
def hessianLambdaMin (J : H → ℝ) (fStar : H) : ℝ :=
  ⨅ x : {h : H // h ≠ 0}, ContinuousLinearMap.rayleighQuotient (hessian J fStar) x

/-- The Newton convergence constant `c_* = gamma / lambda_min (H_*)` from Theorem 3.11,
using `hessianLambdaMin J fStar` as the chosen Lean representation of `lambda_min (H_*)`. -/
def cStar (J : H → ℝ) (fStar : H) (γ : NNReal) : ℝ :=
  (γ : ℝ) / hessianLambdaMin J fStar

/-- Helper for Theorem 3.11: self-adjoint strong positivity of `hessian J fStar`
forces the chosen Rayleigh-quotient representation `hessianLambdaMin J fStar`
of `lambda_min (H_*)` to be positive. -/
theorem hessianLambdaMin_pos
    [Nontrivial H]
    (J : H → ℝ) (fStar : H)
    (hHess :
      ContinuousLinearMap.SelfAdjointStronglyPositive (hessian J fStar)) :
    0 < hessianLambdaMin J fStar := by
  -- Extract a uniform positive quadratic-form lower bound from the SPD Hessian.
  obtain ⟨c0, hc0, hc0_bound⟩ := hHess.exists_inner_lowerBound
  obtain ⟨x0, hx0⟩ := exists_ne (0 : H)
  -- Local instance justification (nonzero Rayleigh family): `le_ciInf` needs a witness in the
  -- nonzero subtype, and any nonzero vector provided by `Nontrivial H` supplies one.
  letI : Nonempty {h : H // h ≠ 0} := ⟨⟨x0, hx0⟩⟩
  have hrayleighLower :
      ∀ x : {h : H // h ≠ 0},
        c0 ≤ ContinuousLinearMap.rayleighQuotient (hessian J fStar) x := by
    intro x
    have hxnorm : 0 < ‖(x : H)‖ ^ 2 := by
      exact sq_pos_of_pos (norm_pos_iff.mpr x.property)
    -- Divide the quadratic-form bound by `‖x‖²` to obtain a Rayleigh-quotient lower bound.
    exact
      (le_div_iff₀ hxnorm).2 <| by
        simpa [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply]
          using hc0_bound (x : H)
  have hlower :
      c0 ≤ hessianLambdaMin J fStar := by
    -- The infimum stays above any common lower bound of the whole Rayleigh family.
    rw [hessianLambdaMin]
    exact le_ciInf hrayleighLower
  exact lt_of_lt_of_le hc0 hlower

/-- Helper for Theorem 3.11: the source quantity `hessianLambdaMin J fStar`
gives the quadratic-form lower bound corresponding to `lambda_min (H_*)`. -/
theorem hessianLambdaMin_inner_lowerBound
    [Nontrivial H]
    (J : H → ℝ) (fStar : H)
    (hHess :
      ContinuousLinearMap.SelfAdjointStronglyPositive (hessian J fStar))
    (h : H) :
    hessianLambdaMin J fStar * ‖h‖ ^ 2 ≤ inner ℝ (hessian J fStar h) h := by
  by_cases hh : h = 0
  · -- The zero vector contributes no quadratic-form mass.
    simp [hh]
  · obtain ⟨c0, hc0, hc0_bound⟩ := hHess.exists_inner_lowerBound
    let xh : {h : H // h ≠ 0} := ⟨h, hh⟩
    have hBddBelow :
        BddBelow
          (Set.range fun x : {h : H // h ≠ 0} ↦
            ContinuousLinearMap.rayleighQuotient (hessian J fStar) x) := by
      refine ⟨c0, ?_⟩
      rintro _ ⟨x, rfl⟩
      have hxnorm : 0 < ‖(x : H)‖ ^ 2 := by
        exact sq_pos_of_pos (norm_pos_iff.mpr x.property)
      exact
        (le_div_iff₀ hxnorm).2 <| by
          simpa [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply]
            using hc0_bound (x : H)
    have hle :
        hessianLambdaMin J fStar ≤
          ContinuousLinearMap.rayleighQuotient (hessian J fStar) xh := by
      -- Compare the infimum with the Rayleigh quotient of the current nonzero direction.
      rw [hessianLambdaMin]
      exact ciInf_le hBddBelow xh
    have hnormsq_nonneg : 0 ≤ ‖h‖ ^ 2 := sq_nonneg ‖h‖
    have hnormsq_pos : 0 < ‖h‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hh)
    calc
      hessianLambdaMin J fStar * ‖h‖ ^ 2
          ≤ ContinuousLinearMap.rayleighQuotient (hessian J fStar) xh * ‖h‖ ^ 2 := by
            exact mul_le_mul_of_nonneg_right hle hnormsq_nonneg
      _ = (hessian J fStar).reApplyInnerSelf h := by
            dsimp [xh]
            field_simp [ContinuousLinearMap.rayleighQuotient, hnormsq_pos.ne']
      _ = inner ℝ (hessian J fStar h) h := by
            simp [ContinuousLinearMap.reApplyInnerSelf_apply]

/-- Helper for Theorem 3.11: the source hypotheses package into the backend
`HasQuadraticConvergenceModel` when the spectral lower bound is represented by
`hessianLambdaMin J fStar`. -/
theorem hasQuadraticConvergenceModel_of_sourceHypotheses
    [Nontrivial H]
    (J : H → ℝ) (fStar : H) {γ : NNReal}
    (hgrad : gradient J fStar = 0)
    (hHess :
      ContinuousLinearMap.SelfAdjointStronglyPositive (hessian J fStar))
    (hLip : LipschitzWith γ (hessian J)) :
    HasQuadraticConvergenceModel J fStar γ (hessianLambdaMin J fStar) := by
  -- Package the source-facing stationary, SPD, and Lipschitz hypotheses into the backend owner.
  refine HasQuadraticConvergenceModel.ofComponents hgrad hHess hLip ?_ ?_
  · exact hessianLambdaMin_pos J fStar hHess
  · intro h
    exact hessianLambdaMin_inner_lowerBound J fStar hHess h

/-- thm_3_11. Theorem 3.11. If `gradient J fStar = 0`, `hessian J fStar` is self-adjoint
strongly positive, `f ↦ hessian J f` is `γ`-Lipschitz, and `gradient J` genuinely has
derivative `hessian J` near `fStar`, then with
`c_* = cStar J fStar γ = γ / hessianLambdaMin J fStar`, every Newton iterate sequence
started in `‖f 0 - fStar‖ < 1 / (2 * cStar J fStar γ)` converges to `fStar` and satisfies
the quadratic estimate `(3.19)`. The positivity and lower-bound facts attached to
`hessianLambdaMin J fStar` are derived from the source SPD hypothesis on
`hessian J fStar`, rather than assumed as part of the public theorem surface. -/
theorem newtonConvergesWithQuadraticEstimate
    (J : H → ℝ) (f : ℕ → H) (fStar : H) {γ : NNReal}
    (hSecondDerivative :
      ∀ᶠ y in nhds fStar,
        HasFDerivAt J (fderiv ℝ J y) y ∧
          HasFDerivAt (fderiv ℝ J) (fderiv ℝ (fderiv ℝ J) y) y)
    (hgrad : gradient J fStar = 0)
    (hHess :
      ContinuousLinearMap.SelfAdjointStronglyPositive (hessian J fStar))
    (hLip : LipschitzWith γ (hessian J))
    (hNewton : IsIterateSequence J f)
    (h0 : ‖f 0 - fStar‖ < 1 / (2 * cStar J fStar γ)) :
    Filter.Tendsto f Filter.atTop (nhds fStar) ∧
      ∀ v : ℕ,
        ‖f (v + 1) - fStar‖ ≤ cStar J fStar γ * ‖f v - fStar‖ ^ 2 := by
  obtain hH | hH := subsingleton_or_nontrivial H
  · -- In the subsingleton case the initial strict inequality collapses to `0 < 0`.
    letI : Subsingleton H := hH
    have hEmpty : IsEmpty {h : H // h ≠ 0} := by
      refine ⟨fun x ↦ ?_⟩
      exact x.property (Subsingleton.elim x.1 0)
    letI : IsEmpty {h : H // h ≠ 0} := hEmpty
    have hLambda : hessianLambdaMin J fStar = 0 := by
      rw [hessianLambdaMin, iInf_of_isEmpty]
      simpa using (Real.sInf_empty : sInf (∅ : Set ℝ) = 0)
    have hFalse : False := by
      have hcontr : ‖f 0 - fStar‖ < 0 := by
        simpa [cStar, hLambda] using h0
      exact (not_lt_of_ge (norm_nonneg _)) hcontr
    exact False.elim hFalse
  · -- In the genuine Hilbert-space case, hand the source hypotheses to the backend package.
    letI : Nontrivial H := hH
    have hModel :
        HasQuadraticConvergenceModel J fStar γ (hessianLambdaMin J fStar) :=
      hasQuadraticConvergenceModel_of_sourceHypotheses J fStar hgrad hHess hLip
    have hStart :
        StartsInConvergenceBall f fStar γ (hessianLambdaMin J fStar) := by
      -- Rewrite the source radius hypothesis into the backend start-ball predicate.
      rw [startsInConvergenceBall_iff, convergenceConstant_eq]
      simpa [cStar] using h0
    refine ⟨?_, ?_⟩
    · -- The backend convergence theorem gives `f v ⟶ fStar`.
      exact tendsto_fStar J f fStar hSecondDerivative hModel hNewton hStart
    · -- The backend recurrence is already in the source quadratic-error form after rewriting.
      intro v
      calc
        ‖f (v + 1) - fStar‖ ≤
            convergenceConstant γ (hessianLambdaMin J fStar) * ‖f v - fStar‖ ^ 2 :=
          quadraticErrorBound J f fStar hSecondDerivative hModel hNewton hStart v
        _ = cStar J fStar γ * ‖f v - fStar‖ ^ 2 := by
          rw [convergenceConstant_eq]
          simp [cStar]

end Newton
