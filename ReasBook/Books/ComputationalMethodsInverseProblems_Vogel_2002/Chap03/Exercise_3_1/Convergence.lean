/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2

public section

universe u

namespace ConvergenceRate

/-- The displayed inequality `(3.1)` from Definition 3.1, separated from the
shared convergence setup `Filter.Tendsto f Filter.atTop (nhds fStar)`. -/
def linearEstimate {H : Type u} [NormedAddCommGroup H]
    (f : ℕ → H) (fStar : H) : Prop :=
  ∃ c : ℝ,
    0 < c ∧
      c < 1 ∧
        ∃ v0 : ℕ, ∀ v ≥ v0, ‖f (v + 1) - fStar‖ ≤ c * ‖f v - fStar‖

/-- Unfolding form of `ConvergenceRate.linearEstimate`. -/
theorem linearEstimate_iff {H : Type u} [NormedAddCommGroup H]
    (f : ℕ → H) (fStar : H) :
    linearEstimate f fStar ↔
      ∃ c : ℝ,
        0 < c ∧
          c < 1 ∧
            ∃ v0 : ℕ, ∀ v ≥ v0, ‖f (v + 1) - fStar‖ ≤ c * ‖f v - fStar‖ :=
  Iff.rfl

/-- The displayed inequality `(3.2)` from Definition 3.1, separated from the
shared convergence setup `Filter.Tendsto f Filter.atTop (nhds fStar)`. -/
def superlinearEstimate {H : Type u} [NormedAddCommGroup H]
    (f : ℕ → H) (fStar : H) : Prop :=
  ∃ c : ℕ → ℝ,
    (∀ v : ℕ, 0 < c v) ∧
      Filter.Tendsto c Filter.atTop (nhds 0) ∧
        ∃ v0 : ℕ, ∀ v ≥ v0, ‖f (v + 1) - fStar‖ ≤ c v * ‖f v - fStar‖

/-- Unfolding form of `ConvergenceRate.superlinearEstimate`. -/
theorem superlinearEstimate_iff {H : Type u} [NormedAddCommGroup H]
    (f : ℕ → H) (fStar : H) :
    superlinearEstimate f fStar ↔
      ∃ c : ℕ → ℝ,
        (∀ v : ℕ, 0 < c v) ∧
          Filter.Tendsto c Filter.atTop (nhds 0) ∧
            ∃ v0 : ℕ, ∀ v ≥ v0, ‖f (v + 1) - fStar‖ ≤ c v * ‖f v - fStar‖ :=
  Iff.rfl

/-- The displayed inequality `(3.3)` from Definition 3.1, separated from the
shared convergence setup `Filter.Tendsto f Filter.atTop (nhds fStar)`. -/
def quadraticEstimate {H : Type u} [NormedAddCommGroup H]
    (f : ℕ → H) (fStar : H) : Prop :=
  ∃ C : ℝ,
    0 < C ∧
      ∃ v0 : ℕ, ∀ v ≥ v0, ‖f (v + 1) - fStar‖ ≤ C * ‖f v - fStar‖ ^ 2

/-- Unfolding form of `ConvergenceRate.quadraticEstimate`. -/
theorem quadraticEstimate_iff {H : Type u} [NormedAddCommGroup H]
    (f : ℕ → H) (fStar : H) :
    quadraticEstimate f fStar ↔
      ∃ C : ℝ,
        0 < C ∧
          ∃ v0 : ℕ, ∀ v ≥ v0, ‖f (v + 1) - fStar‖ ≤ C * ‖f v - fStar‖ ^ 2 :=
  Iff.rfl

end ConvergenceRate
