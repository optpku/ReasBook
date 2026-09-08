module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Tactic.Linarith

public section

open Filter
open scoped Topology

namespace DFP.TwoLeg

/-- The four DFP slow-graph coefficient equations uniquely determine the cubic
and quartic shape coefficients. -/
theorem slowGraphShapeCoefficients (P₃ H₃ P₄ H₄ : ℝ)
    (h_cubicP : 3 * H₃ - 5 * P₃ + 174 = 0)
    (h_cubicH : 8 - H₃ = 0)
    (h_quarticP : 3 * H₄ - 5 * P₄ - 9 = 0)
    (h_quarticH : H₄ = 0) :
    ((P₃, H₃), (P₄, H₄)) = (((198 / 5 : ℝ), 8), (-(9 / 5), 0)) := by
  have hH₃ : H₃ = 8 := by
    linarith
  have hP₃ : P₃ = 198 / 5 := by
    linarith
  have hH₄ : H₄ = 0 := h_quarticH
  have hP₄ : P₄ = -(9 / 5) := by
    linarith
  rw [hP₃, hH₃, hP₄, hH₄]

/-- Substituting the fixed cubic and quartic coefficients into a fifth-order
`p`-coordinate jet gives the fixed slow-graph `p`-coordinate jet. -/
theorem slowGraphPJet (p : ℝ → ℝ) (P₃ P₄ : ℝ)
    (h_pJet :
      (fun ε ↦ p ε - (2 + P₃ * ε ^ 3 + P₄ * ε ^ 4)) =O[𝓝 0]
        (fun ε ↦ ε ^ 5))
    (h_cubic : P₃ = 198 / 5)
    (h_quartic : P₄ = -(9 / 5)) :
      (fun ε ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
      (fun ε ↦ ε ^ 5) := by
  rw [h_cubic, h_quartic] at h_pJet
  convert h_pJet using 1
  ext ε
  ring

/-- Substituting the fixed cubic and zero quartic coefficients into a
fifth-order `h`-coordinate jet gives the fixed slow-graph `h`-coordinate jet. -/
theorem slowGraphHJet (h : ℝ → ℝ) (H₃ H₄ : ℝ)
    (h_hJet :
      (fun ε ↦ h ε - (1 + H₃ * ε ^ 3 + H₄ * ε ^ 4)) =O[𝓝 0]
        (fun ε ↦ ε ^ 5))
    (h_cubic : H₃ = 8)
    (h_quartic : H₄ = 0) :
    (fun ε ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε ↦ ε ^ 5) := by
  simpa [h_cubic, h_quartic] using h_hJet

end DFP.TwoLeg
