module

import Book.Lemma_3_2

noncomputable section

open scoped EuclideanSpace

section

variable (n : ℕ) (h_n : 2 ≤ n)
variable (ι : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
variable (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1)
variable (g : ℕ → EuclideanSpace ℝ (Fin 2)) (δ : ℕ → ℝ) (a b : ℝ)
variable (hdata : PlanarGradient.IsAlternatingScale σ g δ a b)

/- Notation 4.1: for `2 ≤ n`, transport the alternating-scale planar gradients,
perturbations, and candidate iterates through a chosen linear isometry `ι`; their
images lie in the fixed two-dimensional subspace `LinearMap.range ι.toLinearMap`. -/
#check (
  let V := LinearMap.range ι.toLinearMap
  let gEmbedded := fun k ↦ ι (g k)
  let ΔEmbedded := fun k ↦
    ι (PlanarGradient.perturbation EuclideanPlane.orientation (g k) (δ k))
  let xEmbedded := fun k ↦
    ι (PlanarGradient.candidate EuclideanPlane.orientation (g k) (δ k))
  (⟨h_n, hσ, hdata,
    (LinearMap.finrank_range_of_inj ι.injective).trans finrank_euclideanSpace_fin,
    fun k ↦ LinearMap.mem_range_self ι.toLinearMap (g k),
    fun k ↦ LinearMap.mem_range_self ι.toLinearMap
      (PlanarGradient.perturbation EuclideanPlane.orientation (g k) (δ k)),
    fun k ↦ LinearMap.mem_range_self ι.toLinearMap
      (PlanarGradient.candidate EuclideanPlane.orientation (g k) (δ k))⟩ :
    2 ≤ n ∧ σ ∈ Set.Ioo 0 1 ∧ PlanarGradient.IsAlternatingScale σ g δ a b ∧
      Module.finrank ℝ V = 2 ∧ (∀ k, gEmbedded k ∈ V) ∧
      (∀ k, ΔEmbedded k ∈ V) ∧ ∀ k, xEmbedded k ∈ V))

end
