/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap19.Definition_19_1
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E]

-- Proof sketch: for each `x ∉ A`, combine the integrability of `f` and `g` under `κ x`, use
-- linearity of the integral, and substitute the harmonicity identities for `f` and `g`.
/-- Theorem 19.2: if `f` and `g` are harmonic outside `A` for a kernel `κ`, then every linear
combination `α • f + β • g` is harmonic outside `A` as well. -/
theorem IsHarmonicOutside.smul_add
    {κ : Kernel E E} {A : Set E} {f g : E → ℝ}
    (hf : IsHarmonicOutside κ A f) (hg : IsHarmonicOutside κ A g) (α β : ℝ) :
    IsHarmonicOutside κ A (α • f + β • g) := by
  intro x hx
  rcases hf hx with ⟨hf_int, hf_eq⟩
  rcases hg hx with ⟨hg_int, hg_eq⟩
  -- Combine the two row-wise integrability statements using linearity of `Integrable`.
  have h_integrable : Integrable (α • f + β • g) (κ x) :=
    (hf_int.smul α).add (hg_int.smul β)
  -- Move the harmonicity identities through scalar multiplication before adding them.
  have hf_smul :
      α • f x = ∫ y, (α • f) y ∂κ x := by
    calc
      α • f x = α • (∫ y, f y ∂κ x) := by rw [hf_eq]
      _ = ∫ y, (α • f) y ∂κ x := by
        simpa [Pi.smul_apply] using
          (integral_smul α (fun y : E ↦ f y) (μ := κ x)).symm
  have hg_smul :
      β • g x = ∫ y, (β • g) y ∂κ x := by
    calc
      β • g x = β • (∫ y, g y ∂κ x) := by rw [hg_eq]
      _ = ∫ y, (β • g) y ∂κ x := by
        simpa [Pi.smul_apply] using
          (integral_smul β (fun y : E ↦ g y) (μ := κ x)).symm
  refine ⟨h_integrable, ?_⟩
  -- Rewrite the pointwise value using the harmonicity identities for `f` and `g`.
  calc
    (α • f + β • g) x = α • f x + β • g x := by
      simp
    _ = ∫ y, (α • f) y ∂κ x + ∫ y, (β • g) y ∂κ x := by
      rw [hf_smul, hg_smul]
    _ = ∫ y, (α • f + β • g) y ∂κ x := by
      simpa [Pi.add_apply] using
        (integral_add' (hf_int.smul α) (hg_int.smul β)).symm

end ProbabilityTheory
