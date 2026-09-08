module

public import ReasLib.Analysis.Calculus.LocalCutoff.GraphJetTransform.FiniteTaylorJetTransport

public section

universe u v

namespace FiniteTaylorJet

variable {F : Type u} {G : Type v}
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Infrastructure I.16: two endpoint identifications with scalar-source
`ofFunction` compositions transport a finite-jet coefficient secant, evaluated
on the all-ones vector, to its mixed inner/outer secant decomposition. -/
theorem coeff_sub_apply_one_decompose_of_comp_ofFunction_eq
    {m : ℕ} {J₁ J₀ : FiniteTaylorJet ℝ ℝ G m}
    {f₁ f₀ : ℝ → F} {g₁ g₀ : F → G} {x₁ x₀ : ℝ}
    (h₁ : J₁ =
      comp (ofFunction ℝ m g₁ (f₁ x₁)) (ofFunction ℝ m f₁ x₁))
    (h₀ : J₀ =
      comp (ofFunction ℝ m g₀ (f₀ x₀)) (ofFunction ℝ m f₀ x₀))
    (n : Fin (m + 1)) :
    (J₁.coeff n - J₀.coeff n) (fun _ : Fin (n : ℕ) ↦ (1 : ℝ)) =
      ((comp (ofFunction ℝ m g₁ (f₁ x₁))
          (ofFunction ℝ m f₁ x₁)).coeff n -
        (comp (ofFunction ℝ m g₁ (f₁ x₁))
          (ofFunction ℝ m f₀ x₀)).coeff n)
          (fun _ : Fin (n : ℕ) ↦ (1 : ℝ)) +
      ((comp (ofFunction ℝ m g₁ (f₁ x₁))
          (ofFunction ℝ m f₀ x₀)).coeff n -
        (comp (ofFunction ℝ m g₀ (f₀ x₀))
          (ofFunction ℝ m f₀ x₀)).coeff n)
          (fun _ : Fin (n : ℕ) ↦ (1 : ℝ)) := by
  rw [h₁, h₀]
  simp only [sub_apply]
  abel

/-- Helper for Infrastructure I.16: endpoint identifications with smooth
`ofFunction` compositions turn an all-ones coefficient secant into the
factorial-normalized secant of the corresponding iterated derivatives. -/
theorem coeff_sub_apply_one_eq_iteratedFDeriv_sub_of_comp_ofFunction_eq
    {m : ℕ} {J₁ J₀ : FiniteTaylorJet ℝ ℝ G m}
    {f₁ f₀ : ℝ → F} {g₁ g₀ : F → G} {x₁ x₀ : ℝ}
    (h₁ : J₁ =
      comp (ofFunction ℝ m g₁ (f₁ x₁)) (ofFunction ℝ m f₁ x₁))
    (h₀ : J₀ =
      comp (ofFunction ℝ m g₀ (f₀ x₀)) (ofFunction ℝ m f₀ x₀))
    (hf₁ : ContDiffAt ℝ m f₁ x₁) (hg₁ : ContDiffAt ℝ m g₁ (f₁ x₁))
    (hf₀ : ContDiffAt ℝ m f₀ x₀) (hg₀ : ContDiffAt ℝ m g₀ (f₀ x₀))
    (n : Fin (m + 1)) :
    (J₁.coeff n - J₀.coeff n) (fun _ : Fin (n : ℕ) ↦ (1 : ℝ)) =
      ((n : ℕ).factorial : ℝ)⁻¹ •
        (iteratedFDeriv ℝ (n : ℕ) (g₁ ∘ f₁) x₁
            (fun _ : Fin (n : ℕ) ↦ (1 : ℝ)) -
          iteratedFDeriv ℝ (n : ℕ) (g₀ ∘ f₀) x₀
            (fun _ : Fin (n : ℕ) ↦ (1 : ℝ))) := by
  rw [h₁, h₀, sub_apply,
    comp_ofFunction_coeff_apply_one hf₁ hg₁ n,
    comp_ofFunction_coeff_apply_one hf₀ hg₀ n, smul_sub]

end FiniteTaylorJet
