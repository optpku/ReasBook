/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.GeneralizedStrongSolutionAPI

open MeasureTheory ProbabilityTheory

noncomputable section

namespace ProbabilityTheory

/-- Item-owned weak-solution package for Exercise 26.2.1: a generalized weak solution with
explicit initial datum and path-valued Brownian input. This is the local source-faithful carrier
needed by the invariant-distribution statements without importing the later exercise file. -/
structure GeneralizedWeakSDESolution {n m : ℕ}
    (μ₀ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ₀]
    (σ : NNReal → (Fin n → ℝ) → Fin n → Fin m → ℝ)
    (b : NNReal → (Fin n → ℝ) → Fin n → ℝ) where
  Ω : Type _
  instMeasurableSpace : MeasurableSpace Ω
  μ : Measure Ω
  instIsProbabilityMeasure : IsProbabilityMeasure μ
  ℱ : Filtration NNReal instMeasurableSpace
  X : Ω → EuclideanPathSpace n
  W : NNReal → Ω → Fin m → ℝ
  brownian : IsStandardBrownianMotionVector μ W.toEuclidean ∧ Adapted ℱ W
  adapted : Adapted ℱ (fun t ω ↦ X ω t)
  initialLaw : HasLaw (fun ω ↦ X ω 0) μ₀ μ
  ξ : Ω → Fin n → ℝ
  Wpath : Ω → EuclideanPathSpace m
  w_eq : W = pathProcess Wpath
  initial_state_eq : (fun ω ↦ X ω 0) =ᵐ[μ] ξ
  initial_data_measurable : Measurable[ℱ 0] ξ
  independent_initial_brownian : IndepFun ξ Wpath μ
  brownian_path : GeneralizedSDEBrownianMotion μ ℱ Wpath
  solves_strong_sde : SolvesStrongGeneralizedSDE σ b μ ℱ ξ Wpath X

attribute [instance] GeneralizedWeakSDESolution.instMeasurableSpace
attribute [instance] GeneralizedWeakSDESolution.instIsProbabilityMeasure

/-- The law of the state-path random variable carried by a generalized weak solution. -/
abbrev GeneralizedWeakSDESolution.statePathLaw
    {n m : ℕ} {μ₀ : Measure (Fin n → ℝ)} [IsProbabilityMeasure μ₀]
    {σ : NNReal → (Fin n → ℝ) → Fin n → Fin m → ℝ}
    {b : NNReal → (Fin n → ℝ) → Fin n → ℝ}
    (L : GeneralizedWeakSDESolution μ₀ σ b) :
    Measure (EuclideanPathSpace n) :=
  L.μ.map L.X

/-- A generalized weak solution is weakly unique if every other generalized weak solution with
the same initial distribution induces the same state-path law. -/
def GeneralizedWeakSDESolution.IsWeaklyUnique
    {n m : ℕ} {μ₀ : Measure (Fin n → ℝ)} [IsProbabilityMeasure μ₀]
    {σ : NNReal → (Fin n → ℝ) → Fin n → Fin m → ℝ}
    {b : NNReal → (Fin n → ℝ) → Fin n → ℝ}
    (L : GeneralizedWeakSDESolution μ₀ σ b) : Prop :=
  ∀ L' : GeneralizedWeakSDESolution μ₀ σ b, L'.statePathLaw = L.statePathLaw

end ProbabilityTheory
