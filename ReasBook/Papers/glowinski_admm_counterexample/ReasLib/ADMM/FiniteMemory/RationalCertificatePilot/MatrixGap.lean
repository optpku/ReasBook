module
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificatePilot.MatrixAssembly
@[expose] public section
namespace ADMM.FiniteMemory.Reconstruction.MatrixAssembly

/-- Weighted position difference for one interpolation normal. -/
def interpolationMoment {ℓ : ℕ} (μ : Block → Option (Fin ℓ) → Option (Fin ℓ) → ℚ)
    (b : Block) (d : Option (Fin ℓ)) (i : Fin (ℓ + 1) × Fin 2) : ℚ :=
  ∑ a : Option (Fin ℓ), μ b a d *
    (interpolationPosition b a (unitVector i) - interpolationPosition b d (unitVector i))

/-- Columnwise interpolation summation keeps the sparse normal outside the sum. -/
theorem interpolation_column {ℓ : ℕ} (μ : Block → Option (Fin ℓ) → Option (Fin ℓ) → ℚ)
    (γ : ℚ) (b : Block) (d : Option (Fin ℓ)) (i j : Fin (ℓ + 1) × Fin 2) :
    (∑ a : Option (Fin ℓ), μ b a d * interpolationEntry γ b a d i j) =
      -(interpolationNormal γ b d (unitVector i) * interpolationMoment μ b d j +
        interpolationNormal γ b d (unitVector j) * interpolationMoment μ b d i) / 2 := by
  have term (a : Option (Fin ℓ)) :
      μ b a d * interpolationEntry γ b a d i j =
      -((interpolationNormal γ b d (unitVector i) *
          (μ b a d * (interpolationPosition b a (unitVector j) -
            interpolationPosition b d (unitVector j)))) +
        (interpolationNormal γ b d (unitVector j) *
          (μ b a d * (interpolationPosition b a (unitVector i) -
            interpolationPosition b d (unitVector i))))) / 2 := by
    unfold interpolationEntry
    ring
  simp_rw [term]
  simp only [← Finset.sum_div, Finset.sum_neg_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, interpolationMoment]

/-- Reorder all directed interpolation terms by their shared normal. -/
theorem interpolation_gap_factored {ℓ : ℕ}
    (μ : Block → Option (Fin ℓ) → Option (Fin ℓ) → ℚ)
    (γ : ℚ) (i j : Fin (ℓ + 1) × Fin 2) :
    (∑ b : Block, ∑ a : Option (Fin ℓ), ∑ d : Option (Fin ℓ),
      μ b a d * interpolationEntry γ b a d i j) =
    ∑ b : Block, ∑ d : Option (Fin ℓ),
      -(interpolationNormal γ b d (unitVector i) * interpolationMoment μ b d j +
        interpolationNormal γ b d (unitVector j) * interpolationMoment μ b d i) / 2 := by
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.sum_comm]
  simp only [interpolation_column]

/-- Only the current two coordinates contribute to the strict norm term. -/
theorem currentPairMatrix_apply {ℓ : ℕ} (i j : Fin (ℓ + 1) × Fin 2) :
    currentPairMatrix ℓ i j = unitVector i (0, 0) * unitVector j (0, 0) +
      unitVector i (0, 1) * unitVector j (0, 1) := by
  change (((unitVector i (0, 0) + unitVector j (0, 0)) ^ 2 +
      (unitVector i (0, 1) + unitVector j (0, 1)) ^ 2) -
    (unitVector i (0, 0) ^ 2 + unitVector i (0, 1) ^ 2) -
    (unitVector j (0, 0) ^ 2 + unitVector j (0, 1) ^ 2)) / 2 = _
  ring

end ADMM.FiniteMemory.Reconstruction.MatrixAssembly
