/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Definition_14_1_extra_4

noncomputable section

open scoped ClarkeDirectionalDerivative ClarkeDifferential

section

universe u

variable {X : Type u} [NormedAddCommGroup X]

/-- A global Lipschitz condition on `f` yields the local Lipschitz hypothesis required by the
Chapter 14 Clarke differential at every point. -/
theorem locallyLipschitzAt_of_lipschitzOnWith_univ
    (f : X → ℝ) (x : X) {K : NNReal} (h_lipschitz : LipschitzOnWith K f Set.univ) :
    LocallyLipschitzAt f x := by
  refine ⟨1, zero_lt_one, K, ?_⟩
  intro y hy z hz
  simpa using h_lipschitz (by simp) (by simp)

section

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

local notation "DualSpace" => X →L[ℝ] ℝ

-- This item is a bridge/view file: Chapter 14 already owns the Clarke stationarity API in
-- `Definition_14_1_extra_4`, and the source here adds the whole-space optimality consequence.

/-- For the unconstrained problem `min_{x ∈ X} f x`, every global minimizer is Clarke
stationary once `f` is locally Lipschitz at the minimizer. This is the canonical Chapter 14
bridge from whole-space optimality to the existing owner `IsClarkeStationaryPoint f xStar`. -/
theorem isClarkeStationaryPoint_of_isMinOn
    (f : X → ℝ) {xStar : X}
    (h_min : IsMinOn f Set.univ xStar)
    (h_local : LocallyLipschitzAt f xStar) :
    IsClarkeStationaryPoint f xStar := by
  have h_localMin : IsLocalMin f xStar := h_min.isLocalMin (by simp)
  exact h_localMin.isClarkeStationaryPoint h_local

/-- Chapter14 Definition 14.2-extra-1: for the unconstrained problem `min_{x ∈ X} f x` on a
normed space, if `xStar` is a solution and `f` is locally Lipschitz at `xStar`, then the zero
functional belongs to the canonical whole-space Clarke differential `(∂ᶜ f) xStar`. -/
theorem zero_mem_clarkeDifferential_of_isMinOn
    (f : X → ℝ) {xStar : X}
    (h_min : IsMinOn f Set.univ xStar)
    (h_local : LocallyLipschitzAt f xStar) :
    (0 : DualSpace) ∈ (∂ᶜ f) xStar := by
  exact isClarkeStationaryPoint_iff_zero_mem_clarkeDifferential.mp
    (isClarkeStationaryPoint_of_isMinOn f h_min h_local)

#print axioms zero_mem_clarkeDifferential_of_isMinOn

end

end
