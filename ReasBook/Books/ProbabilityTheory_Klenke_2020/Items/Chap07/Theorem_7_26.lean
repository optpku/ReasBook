/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped InnerProductSpace

universe u

section

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/- The Fréchet-Riesz representation theorem in mathlib is the canonical equivalence
`InnerProductSpace.toDual ℝ V`, identifying vectors in a real Hilbert space with continuous linear
functionals via the inner product. -/
recall InnerProductSpace.toDual

/-- Theorem 7.26: every continuous linear functional on a real Hilbert space is represented by a
unique vector, equivalently the unique preimage of `F` under `InnerProductSpace.toDual ℝ V`. -/
theorem existsUnique_inner_right_eq_of_continuousLinearMap (F : V →L[ℝ] ℝ) :
    ∃! f : V, ∀ x : V, F x = inner ℝ x f := by
  let f := (InnerProductSpace.toDual ℝ V).symm F
  have hF : InnerProductSpace.toDual ℝ V f = F := by
    change InnerProductSpace.toDual ℝ V ((InnerProductSpace.toDual ℝ V).symm F) = F
    exact (InnerProductSpace.toDual ℝ V).apply_symm_apply F
  have hf : ∀ x : V, F x = inner ℝ x f := by
    intro x
    calc
      F x = (InnerProductSpace.toDual ℝ V f) x := by rw [hF]
      _ = inner ℝ f x := rfl
      _ = inner ℝ x f := real_inner_comm _ _
  refine ⟨f, hf, ?_⟩
  · intro g hg
    apply (InnerProductSpace.toDual ℝ V).injective
    ext x
    calc
      (InnerProductSpace.toDual ℝ V g) x = F x := by
        simpa [InnerProductSpace.toDual_apply_apply, real_inner_comm] using (hg x).symm
      _ = (InnerProductSpace.toDual ℝ V f) x := by rw [hF]

end
