/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Algorithm_8_2_4.Clauses

public section

/- Current Chapter 8 primal-dual Newton item for total variation-penalized
least-squares minimization in two space dimensions.

The reusable clause owners live in `Book.Ch8.Algorithm_8_2_4.Clauses`. This
source-facing file keeps the displayed formulas literal in the two ambiguous
print positions: the fourth summand of `L̄_v` still uses the explicit operator
parameter `Dv`, and the `Δv` assignment keeps the printed leading term
`-u_v + ...`.
-/

/-- Algorithm 8.2.4. Source-facing surface checks packaging the displayed
primal-dual Newton clauses from the current Chapter 8 item.

This theorem packages the four displayed clause owners from
`Book.Ch8.Algorithm_8_2_4.Clauses` without normalizing the two printed
ambiguities in the source: the fourth diffusion summand still uses the
parameter `Dv`, and the `Δv` clause keeps the printed leading term
`-u_v + ...`. -/
theorem Algorithm_8_2_4_surface_checks {κ : Type*} {ι : Type*} {δ : Type*}
    [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    [Fintype δ] [DecidableEq δ]
    {ψ' ψ'' : (ι → ℝ) → δ → ℝ}
    {K : Matrix κ ι ℝ} {Dx Dy Dv : Matrix δ ι ℝ} {α : ℝ} {d : κ → ℝ}
    {f0 : ι → ℝ} {u0 v0 : δ → ℝ}
    {f : ℕ → ι → ℝ} {uDual vDual wVec : ℕ → δ → ℝ}
    {bInv E11 E12 E21 E22 : ℕ → Matrix δ δ ℝ}
    {lbar : ℕ → Matrix ι ι ℝ} {r deltaF : ℕ → ι → ℝ}
    {deltaU deltaV : ℕ → δ → ℝ}
    {τ : ℕ → ℝ} {𝒞star : Set ((δ → ℝ) × (δ → ℝ))}
    (h_init : TVPrimalDualNewton.IsInitialized f0 u0 v0 f uDual vDual)
    (h_intermediate : TVPrimalDualNewton.HasIntermediateAssignments
      ψ' ψ'' K Dx Dy Dv α d f uDual vDual wVec bInv E11 E12 E21 E22 lbar r)
    (h_newton : TVPrimalDualNewton.HasNewtonAndDualIncrements
      K Dx Dy α f uDual bInv E11 E12 E21 E22 lbar r deltaF deltaU deltaV)
    (h_update : TVPrimalDualNewton.HasPrimalDualUpdate
      f uDual vDual deltaF deltaU deltaV τ 𝒞star) :
    TVPrimalDualNewton.IsInitialized f0 u0 v0 f uDual vDual ∧
      TVPrimalDualNewton.HasIntermediateAssignments
        ψ' ψ'' K Dx Dy Dv α d f uDual vDual wVec bInv E11 E12 E21 E22 lbar r ∧
      TVPrimalDualNewton.HasNewtonAndDualIncrements
        K Dx Dy α f uDual bInv E11 E12 E21 E22 lbar r deltaF deltaU deltaV ∧
      TVPrimalDualNewton.HasPrimalDualUpdate
        f uDual vDual deltaF deltaU deltaV τ 𝒞star := by
  -- Package the verified clause-level surface without guessing a stronger run owner.
  refine ⟨h_init, ?_⟩
  refine ⟨h_intermediate, ?_⟩
  exact ⟨h_newton, h_update⟩

/- Step (1). Source-facing initialization clause. -/
#check
  TVPrimalDualNewton.IsInitialized

/- Step (2). Source-facing intermediate diagonal, diffusion, and residual
clauses. -/
#check
  TVPrimalDualNewton.HasIntermediateAssignments

/- Step (3). Source-facing Newton-step and dual-increment clauses, preserving
the printed `Δv := -u_v + ...` formula. -/
#check
  TVPrimalDualNewton.HasNewtonAndDualIncrements

/-
Algorithm 8.2.4 (4). Source-facing primal-update, maximal-feasible-step, and
dual-update clauses.
-/
#check
  TVPrimalDualNewton.HasPrimalDualUpdate
