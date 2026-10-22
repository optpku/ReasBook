/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/Required_Lean_mathlib_Infrastructure_for_the_DFP_Counterexample/Infrastructure_I_11_Signed_analytic_square_root_branch.lean
-/

module

public import ReasLib.Analysis.Analytic.Sqrt

public section

open scoped Topology

/- Infrastructure I.11 (Signed analytic square-root branch) (1): If `q` is analytic at
`0` and satisfies `q 0 = 1`, then `ε ↦ ε * √(q ε)` is analytic across `0`.
The local branch condition is discharged by the analytic square-root construction. -/
#check (Real.analyticAt_signedSqrtBranch :
  ∀ (q : ℝ → ℝ), AnalyticAt ℝ q 0 → q 0 = 1 →
    AnalyticAt ℝ (fun ε ↦ ε * √(q ε)) 0)
/- Infrastructure I.11 (Signed analytic square-root branch) (2): On a sufficiently small
right neighborhood of `0`, the signed branch `ε ↦ ε * √(q ε)` agrees with the positive
square root of `ε ^ 2 * q ε`. -/
#check (Real.signedSqrtBranch_eventuallyEq_sqrt :
  ∀ (q : ℝ → ℝ),
    (fun ε : ℝ ↦ ε * √(q ε)) =ᶠ[𝓝[>] 0] (fun ε ↦ √(ε ^ 2 * q ε)))
/- Infrastructure I.11 (Signed analytic square-root branch) (3): If `q` is analytic at
`0` and satisfies `q 0 = 1`, the signed branch `ε ↦ ε * √(q ε)` has derivative `1`. -/
#check (Real.hasDerivAt_signedSqrtBranch :
  ∀ (q : ℝ → ℝ), AnalyticAt ℝ q 0 → q 0 = 1 →
    HasDerivAt (fun ε : ℝ ↦ ε * √(q ε)) 1 0)
