module

public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.LeadingTransverse

public section

/-!
# Basic interfaces for the leading transverse map

This companion supplies the definitional formulas, exact Fréchet derivative, and fixed
coefficient of the affine leading transverse map without depending on the asymptotic theorem.
-/

noncomputable section

namespace DFP.TwoLeg.Mixed

/-- The weighted-path transverse increment unfolds to the corresponding mixed-map output. -/
theorem transverseIncrement_eq (ε P J : ℝ) :
    transverseIncrement ε (P, J) =
      let y := map ε (input (ε, P, J) (ε ^ 2))
      (y.2.1 - 2, y.2.2 - 1) := by
  rfl

/-- The affine leading transverse map evaluates by its displayed coordinate formula. -/
theorem leadingTransverse_eq (P J : ℝ) :
    leadingTransverse (P, J) = ((6 * J - P + 348) / 9, 8) := by
  rfl

/-- The Fréchet derivative of the affine leading transverse map is constant, with rows
`(-1 / 9, 2 / 3)` and `(0, 0)`. -/
theorem leadingTransverse_fderiv (z v : ℝ × ℝ) :
    fderiv ℝ leadingTransverse z v =
      ((-(1 : ℝ) / 9) * v.1 + ((2 : ℝ) / 3) * v.2, 0) := by
  let L₁ : (ℝ × ℝ) →L[ℝ] ℝ :=
    ((-(1 : ℝ) / 9) • ContinuousLinearMap.fst ℝ ℝ ℝ) +
      (((2 : ℝ) / 3) • ContinuousLinearMap.snd ℝ ℝ ℝ)
  let L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) := L₁.prod 0
  let c : ℝ × ℝ := ((348 : ℝ) / 9, 8)
  have hfun : leadingTransverse = fun w => L w + c := by
    funext w
    rcases w with ⟨P, J⟩
    rw [leadingTransverse_eq]
    simp [L, L₁, c]
    ring
  have hderiv : HasFDerivAt (fun w => L w + c) L z :=
    L.hasFDerivAt.add_const c
  rw [hfun, hderiv.fderiv]
  simp [L, L₁]

/-- The coefficient pair `(198 / 5, 8)` is fixed by the affine leading map. -/
theorem leadingTransverse_fixed :
    leadingTransverse ((198 / 5 : ℝ), 8) = ((198 / 5 : ℝ), 8) := by
  rw [leadingTransverse_eq]
  norm_num

end DFP.TwoLeg.Mixed
