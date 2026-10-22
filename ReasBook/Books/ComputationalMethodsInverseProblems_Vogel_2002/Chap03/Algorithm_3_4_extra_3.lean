/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap03.Algorithm_3_4_extra_3.QuadraticBacktracking

public section

namespace LineSearch

/-- Algorithm 3.4-extra-3. Under explicit derivative data `HasDerivAt φ d₀ 0`,
formula `(3.30)` for the quadratic backtracking update is
`quadraticBacktrackingStep φ τ₀ = -d₀ * τ₀ ^ 2 / (2 * (φ τ₀ - φ 0 - d₀ * τ₀))`. -/
theorem quadraticBacktrackingStep_eq_of_hasDerivAt {φ : ℝ → ℝ} {τ₀ d₀ : ℝ}
    (h0 : HasDerivAt φ d₀ 0) :
    quadraticBacktrackingStep φ τ₀ =
      -d₀ * τ₀ ^ 2 / (2 * (φ τ₀ - φ 0 - d₀ * τ₀)) := by
  rw [quadraticBacktrackingStep_def]
  simp [h0.deriv]

end LineSearch
