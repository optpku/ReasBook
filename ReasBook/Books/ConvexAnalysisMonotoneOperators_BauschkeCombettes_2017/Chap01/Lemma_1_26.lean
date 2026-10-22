/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {X : Type u} [TopologicalSpace X]

/-
Lemma 1.26 (1): the extended-real statement in the text is the `EReal` specialization of the
canonical mathlib theorem `lowerSemicontinuous_iSup`.
-/
recall lowerSemicontinuous_iSup

private theorem lowerSemicontinuous_iInf_fintype {I : Type v} [Fintype I]
    {f : I → X → EReal} (hf : ∀ i, LowerSemicontinuous (f i)) :
    LowerSemicontinuous fun x ↦ ⨅ i, f i x := by
  classical
  have h_induction : ∀ (J : Type v) [Fintype J], ∀ (g : J → X → EReal),
      (∀ j, LowerSemicontinuous (g j)) →
        LowerSemicontinuous (fun x ↦ ⨅ j, g j x) := by
    intro J _
    refine Fintype.induction_empty_option
      (P := fun J _ ↦ ∀ (g : J → X → EReal), (∀ j, LowerSemicontinuous (g j)) →
        LowerSemicontinuous (fun x ↦ ⨅ j, g j x)) ?_ ?_ ?_ J
    · intro A B _ e hB g hg
      let gA : A → X → EReal := fun a x ↦ g (e a) x
      have hgA : ∀ a, LowerSemicontinuous (gA a) := by
        intro a
        simpa [gA] using hg (e a)
      have hA : LowerSemicontinuous (fun x ↦ ⨅ a, gA a x) := hB gA hgA
      have hiInf_eq : (fun x ↦ ⨅ a, gA a x) = fun x ↦ ⨅ b, g b x := by
        funext x
        exact Equiv.iInf_congr e (fun a ↦ rfl)
      simpa [hiInf_eq] using hA
    · intro g hg
      have hempty : (fun x ↦ ⨅ j : PEmpty, g j x) = fun _ : X ↦ (⊤ : EReal) := by
        funext x
        simp
      simpa [hempty] using
        (lowerSemicontinuous_const : LowerSemicontinuous (fun _ : X ↦ (⊤ : EReal)))
    · intro A _ hA g hg
      have hnone : LowerSemicontinuous (g none) := hg none
      have hsome : LowerSemicontinuous (fun x ↦ ⨅ a, g (some a) x) := by
        exact hA (fun a x ↦ g (some a) x) (fun a ↦ hg (some a))
      simpa [iInf_option] using hnone.inf hsome
  exact h_induction I f hf

/-- Lemma 1.26 (2): for a finite family of lower semicontinuous extended-real-valued functions,
the pointwise minimum, written as a finite infimum, is lower semicontinuous. -/
theorem lowerSemicontinuous_iInf_of_finite {I : Type v} [Finite I] {f : I → X → EReal}
    (hf : ∀ i, LowerSemicontinuous (f i)) : LowerSemicontinuous fun x ↦ ⨅ i, f i x := by
  classical
  let _ : Fintype I := Fintype.ofFinite I
  simpa using lowerSemicontinuous_iInf_fintype hf
