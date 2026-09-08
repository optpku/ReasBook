module

public import ReasLib.Analysis.Calculus.LocalCutoff.GraphJetTransform

public section

open scoped NNReal

universe u

namespace LocalCutoff.GraphTransform.JetTransform

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [FiniteDimensional ℝ X]
variable {radius slope : ℝ≥0}

/-- Helper for Infrastructure I.16: the distinguished all-ones branch of a
live top-updated stable jet is its outer coefficient evaluated on repeated
degree-one values of the inverse-coordinate jet. -/
theorem liveAllOnesBranch_apply_one
    (r : ℕ) (hr : 0 < r) (χ : ℝ × X → ℝ) (ρ : ℝ) (L : X →L[ℝ] X)
    (N : ℝ × X → ℝ × X) (J : BoundedGraphJet X radius slope r)
    (a : BoundedContinuousFunction ℝ (ℝ [×r]→L[ℝ] X))
    (u ū : ℝ) (inverse : ℝ → ℝ) :
    ((stableJet r χ ρ L N
        (topUpdatedGraphJet r hr J a) u).toFormalMultilinearSeries.compAlongComposition
          (FiniteTaylorJet.ofFunction ℝ r inverse ū).toFormalMultilinearSeries
          (Composition.ones r)) (fun _ : Fin r ↦ (1 : ℝ)) =
      (stableJet r χ ρ L N
          (topUpdatedGraphJet r hr J a) u).toFormalMultilinearSeries
          (Composition.ones r).length
        (fun _ : Fin (Composition.ones r).length ↦
          (FiniteTaylorJet.ofFunction ℝ r inverse ū).toFormalMultilinearSeries 1
            (fun _ : Fin 1 ↦ (1 : ℝ))) := by
  rw [FormalMultilinearSeries.compAlongComposition_apply,
    FormalMultilinearSeries.applyComposition_ones]

/-- Infrastructure I.16: fixed lower endpoint jets rewrite the live
distinguished branch as the factorial-normalized predecessor secant minus the
explicit defect between that transported secant and the live stable top term. -/
theorem liveAllOnesBranch_eq_normalizedPredecessorSecant_sub
    (r : ℕ) (hr : 0 < r) (χ : ℝ × X → ℝ) (ρ : ℝ) (L : X →L[ℝ] X)
    (N : ℝ × X → ℝ × X) (J : BoundedGraphJet X radius slope r)
    (a : BoundedContinuousFunction ℝ (ℝ [×r]→L[ℝ] X))
    (u ū t : ℝ) (inverse : ℝ → ℝ) (predecessor : ℝ → X)
    (y₁ y₀ : ℝ) (K₁ K₀ : FiniteTaylorJet ℝ ℝ X (r - 1))
    (liveDefect : X)
    (hK₁ : K₁ = FiniteTaylorJet.ofFunction ℝ (r - 1) predecessor y₁)
    (hK₀ : K₀ = FiniteTaylorJet.ofFunction ℝ (r - 1) predecessor y₀)
    (hliveDefect :
      (r.factorial : ℝ)⁻¹ •
          (t⁻¹ • (((r - 1).factorial : ℝ) •
            ((K₁.coeff ⟨r - 1, Nat.lt_succ_self (r - 1)⟩ -
                K₀.coeff ⟨r - 1, Nat.lt_succ_self (r - 1)⟩)
              (fun _ : Fin (r - 1) ↦ (1 : ℝ))))) -
        (stableJet r χ ρ L N
            (topUpdatedGraphJet r hr J a) u).toFormalMultilinearSeries
            (Composition.ones r).length
          (fun _ : Fin (Composition.ones r).length ↦
            (FiniteTaylorJet.ofFunction ℝ r inverse ū).toFormalMultilinearSeries
              1
              (fun _ : Fin 1 ↦ (1 : ℝ))) =
        liveDefect) :
    ((stableJet r χ ρ L N
        (topUpdatedGraphJet r hr J a) u).toFormalMultilinearSeries.compAlongComposition
          (FiniteTaylorJet.ofFunction ℝ r inverse ū).toFormalMultilinearSeries
          (Composition.ones r)) (fun _ : Fin r ↦ (1 : ℝ)) =
      (r.factorial : ℝ)⁻¹ •
          (t⁻¹ •
            (iteratedFDeriv ℝ (r - 1) predecessor y₁
                (fun _ : Fin (r - 1) ↦ (1 : ℝ)) -
              iteratedFDeriv ℝ (r - 1) predecessor y₀
                (fun _ : Fin (r - 1) ↦ (1 : ℝ)))) -
        liveDefect := by
  rw [liveAllOnesBranch_apply_one r hr χ ρ L N J a u ū inverse]
  have hfactorial : (((r - 1).factorial : ℝ)) ≠ 0 := by
    positivity
  have hfactorial_cancel (z : X) :
      ((r - 1).factorial : ℝ) •
          (((r - 1).factorial : ℝ)⁻¹ • z) = z := by
    rw [smul_smul, mul_inv_cancel₀ hfactorial, one_smul]
  have hnormalized :
      (r.factorial : ℝ)⁻¹ •
          (t⁻¹ • (((r - 1).factorial : ℝ) •
            ((K₁.coeff ⟨r - 1, Nat.lt_succ_self (r - 1)⟩ -
                K₀.coeff ⟨r - 1, Nat.lt_succ_self (r - 1)⟩)
              (fun _ : Fin (r - 1) ↦ (1 : ℝ))))) =
        (r.factorial : ℝ)⁻¹ •
          (t⁻¹ •
            (iteratedFDeriv ℝ (r - 1) predecessor y₁
                (fun _ : Fin (r - 1) ↦ (1 : ℝ)) -
              iteratedFDeriv ℝ (r - 1) predecessor y₀
                (fun _ : Fin (r - 1) ↦ (1 : ℝ)))) := by
    rw [hK₁, hK₀, sub_apply,
      FiniteTaylorJet.coeff_ofFunction_apply,
      FiniteTaylorJet.coeff_ofFunction_apply]
    simp only [Fin.val_mk]
    rw [← smul_sub, hfactorial_cancel]
  rw [← hnormalized, ← hliveDefect]
  abel

end LocalCutoff.GraphTransform.JetTransform
