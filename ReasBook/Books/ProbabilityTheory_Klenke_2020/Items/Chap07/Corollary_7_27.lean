/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap07.Theorem_7_26

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open SeparationQuotient
open scoped InnerProductSpace

universe u

section

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [c : PreInnerProductSpace.Core ℝ V]

attribute [local instance] InnerProductSpace.Core.toSeminormedAddCommGroup

local instance : InnerProductSpace ℝ V := InnerProductSpace.ofCore c

variable [CompleteSpace V]

local instance : CompleteSpace (SeparationQuotient V) :=
  SeparationQuotient.completeSpace_iff.2 inferInstance

/-- Corollary 7.27: Every continuous real linear functional on a complete real semi-inner-product
space is given by pairing with some vector. -/
theorem exists_inner_right_eq_of_continuousLinearMap (F : V →L[ℝ] ℝ) :
    ∃ f : V, ∀ x : V, F x = inner ℝ x f := by
  let Fq : SeparationQuotient V →L[ℝ] ℝ :=
    liftCLM F fun x y hxy ↦ (hxy.map <| map_continuous F).eq
  obtain ⟨f, hf, -⟩ :=
    existsUnique_inner_right_eq_of_continuousLinearMap Fq
  refine ⟨outCLM ℝ V f, ?_⟩
  intro x
  calc
    F x = Fq (mk x) := by simp [Fq]
    _ = inner ℝ (mk x) f := hf (mk x)
    _ = inner ℝ (mk x) (mk (outCLM ℝ V f)) := by rw [mk_outCLM]
    _ = inner ℝ x (outCLM ℝ V f) := by simpa using (inner_mk_mk x (outCLM ℝ V f))

end
