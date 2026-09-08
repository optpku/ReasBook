module

public import ReasLib.Analysis.Calculus.LocalCutoff.GraphJetTransform
public import ReasLib.Analysis.Calculus.FiniteTaylorJet.Ext

public section

open scoped NNReal

universe u

namespace LocalCutoff.GraphTransform

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X]
variable {radius slope : ℝ≥0}

/-- The derivative-constructed order-`r` jet associated with a graph. -/
noncomputable def holonomicJet (r : ℕ) (ζ : SmallLipschitzGraph X radius slope) :
    ℝ → FiniteTaylorJet ℝ ℝ X r :=
  fun u ↦ FiniteTaylorJet.ofFunction ℝ r (ζ : ℝ → X) u

/-- The constant coefficient of a holonomic graph jet is the graph value. -/
theorem holonomicJet_constantCoeff (r : ℕ) (ζ : SmallLipschitzGraph X radius slope)
    (u : ℝ) :
    (holonomicJet r ζ u).constantCoeff = ζ u := by
  rw [holonomicJet, FiniteTaylorJet.constantCoeff_ofFunction]

/-- Every coefficient of a holonomic graph jet is the factorial-normalized
iterated Fréchet derivative of the graph. -/
theorem holonomicJet_coeff (r : ℕ) (ζ : SmallLipschitzGraph X radius slope)
    (u : ℝ) (n : Fin (r + 1)) :
    (holonomicJet r ζ u).coeff n =
      ((n : ℕ).factorial : ℝ)⁻¹ • iteratedFDeriv ℝ (n : ℕ) (ζ : ℝ → X) u := by
  rw [holonomicJet, FiniteTaylorJet.coeff_ofFunction]

/-- A bounded graph jet is holonomic when its stored family is the
derivative-constructed family of its graph. -/
def IsHolonomic (r : ℕ) (J : BoundedGraphJet X radius slope r) : Prop :=
  ∀ u, J.jet u = holonomicJet r J.graph u

/-- A derivative-constructed family realizes a bounded graph jet whenever
explicit coefficient bounds are supplied. -/
noncomputable def boundedHolonomicGraphJet (r : ℕ) (ζ : SmallLipschitzGraph X radius slope)
    (coeffBound : Fin (r + 1) → ℝ≥0)
    (hcoeffBound : ∀ u n, ‖(holonomicJet r ζ u).coeff n‖ ≤ (coeffBound n : ℝ)) :
    BoundedGraphJet X radius slope r :=
  { graph := ζ
    jet := holonomicJet r ζ
    coeffBound := coeffBound
    constantCoeff_eq := fun u ↦ holonomicJet_constantCoeff r ζ u
    coeff_le := hcoeffBound }

/-- The bounded realization has the original graph as its graph component. -/
theorem boundedHolonomicGraphJet_graph (r : ℕ) (ζ : SmallLipschitzGraph X radius slope)
    (coeffBound : Fin (r + 1) → ℝ≥0)
    (hcoeffBound : ∀ u n, ‖(holonomicJet r ζ u).coeff n‖ ≤ (coeffBound n : ℝ)) :
    (boundedHolonomicGraphJet r ζ coeffBound hcoeffBound).graph = ζ := by
  rfl

/-- The bounded realization stores the derivative-constructed jet family. -/
theorem boundedHolonomicGraphJet_jet (r : ℕ) (ζ : SmallLipschitzGraph X radius slope)
    (coeffBound : Fin (r + 1) → ℝ≥0)
    (hcoeffBound : ∀ u n, ‖(holonomicJet r ζ u).coeff n‖ ≤ (coeffBound n : ℝ))
    (u : ℝ) :
    (boundedHolonomicGraphJet r ζ coeffBound hcoeffBound).jet u = holonomicJet r ζ u := by
  rfl

/-- The bounded realization is holonomic. -/
theorem boundedHolonomicGraphJet_isHolonomic (r : ℕ)
    (ζ : SmallLipschitzGraph X radius slope)
    (coeffBound : Fin (r + 1) → ℝ≥0)
    (hcoeffBound : ∀ u n, ‖(holonomicJet r ζ u).coeff n‖ ≤ (coeffBound n : ℝ)) :
    IsHolonomic r (boundedHolonomicGraphJet r ζ coeffBound hcoeffBound) := by
  intro u
  rw [boundedHolonomicGraphJet_graph]
  exact boundedHolonomicGraphJet_jet r ζ coeffBound hcoeffBound u

/-- ContDiff regularity transfers to the graph component of a bounded
holonomic realization. -/
theorem boundedHolonomicGraphJet_contDiff (r : ℕ)
    (ζ : SmallLipschitzGraph X radius slope) (hζ : ContDiff ℝ r ζ)
    (coeffBound : Fin (r + 1) → ℝ≥0)
    (hcoeffBound : ∀ u n, ‖(holonomicJet r ζ u).coeff n‖ ≤ (coeffBound n : ℝ)) :
    ContDiff ℝ r (boundedHolonomicGraphJet r ζ coeffBound hcoeffBound).graph := by
  rw [boundedHolonomicGraphJet_graph]
  exact hζ

/-- The top coefficient of a holonomic bounded graph jet is the normalized
`r`-th iterated Fréchet derivative of its graph. -/
theorem holonomic_topCoeff_eq_iteratedFDeriv (r : ℕ)
    (J : BoundedGraphJet X radius slope r) (hJ : IsHolonomic r J) (u : ℝ) :
    (J.jet u).coeff ⟨r, Nat.lt_succ_self r⟩ =
      ((r : ℕ).factorial : ℝ)⁻¹ • iteratedFDeriv ℝ r (J.graph : ℝ → X) u := by
  rw [hJ u, holonomicJet_coeff]

end LocalCutoff.GraphTransform
