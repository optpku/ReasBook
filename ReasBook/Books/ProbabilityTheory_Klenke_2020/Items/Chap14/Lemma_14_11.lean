/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap01.Definition_1_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Definition_14_9

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Set

universe u v

variable {I : Type u} {Ω : I → Type v}

-- `MeasureTheory.squareCylinders` is the owner abstraction for total coordinate families with
-- `univ` fillers. Lemma 14.11 is more general: it concerns the source-facing family
-- `𝓩^{ℰ,R} = ⋃ J, restrictedRectangularCylinderSetsWithBase ℰ J`, where enlarging the finite base
-- under intersections does not require `univ ∈ ℰ i` because the overlap coordinates are handled
-- by intersecting the prescribed coordinate sets.
/-- Lemma 14.11: if each coordinate family `ℰ i` is closed under binary intersections, then the
family of all finite-base `ℰ`-rectangular cylinders is closed under binary intersections. -/
theorem isInterClosed_iUnion_restrictedRectangularCylinderSetsWithBase
    (ℰ : ∀ i, Set (Set (Ω i))) (hℰ : ∀ i, IsInterClosed (ℰ i)) :
    IsInterClosed (⋃ J : Finset I, restrictedRectangularCylinderSetsWithBase ℰ J) := by
  classical
  refine ⟨?_⟩
  intro s t hs ht
  rw [mem_iUnion] at hs ht ⊢
  rcases hs with ⟨J₁, hs⟩
  rcases ht with ⟨J₂, ht⟩
  rcases hs with ⟨A₁, hA₁, rfl⟩
  rcases ht with ⟨A₂, hA₂, rfl⟩
  have hA₁' : ∀ j : J₁, A₁ j ∈ ℰ j.1 := by
    simpa [mem_pi] using hA₁
  have hA₂' : ∀ j : J₂, A₂ j ∈ ℰ j.1 := by
    simpa [mem_pi] using hA₂
  let K : Finset I := J₁ ∪ J₂
  let B : ∀ j : K, Set (Ω j.1) := fun j ↦
    if hj₁ : j.1 ∈ J₁ then
      if hj₂ : j.1 ∈ J₂ then
        A₁ ⟨j.1, hj₁⟩ ∩ A₂ ⟨j.1, hj₂⟩
      else
        A₁ ⟨j.1, hj₁⟩
    else
      A₂ ⟨j.1, by
        have hjK : j.1 ∈ K := j.2
        simpa [K] using (Finset.mem_union.mp hjK).resolve_left hj₁⟩
  have hB : B ∈ pi univ (fun j : K ↦ ℰ j.1) := by
    rw [mem_pi]
    intro j _
    dsimp [B]
    by_cases hj₁ : j.1 ∈ J₁
    · by_cases hj₂ : j.1 ∈ J₂
      · simpa [B, hj₁, hj₂] using
          (hℰ j.1).inter_mem (hA₁' ⟨j.1, hj₁⟩) (hA₂' ⟨j.1, hj₂⟩)
      · simpa [hj₁, hj₂] using hA₁' ⟨j.1, hj₁⟩
    ·
      have hj₂ : j.1 ∈ J₂ := by
        have hjK : j.1 ∈ K := j.2
        simpa [K] using (Finset.mem_union.mp hjK).resolve_left hj₁
      simpa [hj₁, hj₂] using hA₂' ⟨j.1, hj₂⟩
  refine ⟨K, B, hB, ?_⟩
  ext y
  change y ∈ cylinder K (pi univ B) ↔
    y ∈ cylinder J₁ (pi univ A₁) ∩ cylinder J₂ (pi univ A₂)
  constructor
  · intro hy
    rw [mem_cylinder, mem_pi] at hy
    rw [mem_inter_iff, mem_cylinder, mem_cylinder, mem_pi, mem_pi]
    refine ⟨?_, ?_⟩
    · intro j _
      have hyj := hy ⟨j.1, Finset.mem_union.mpr <| Or.inl j.2⟩ (mem_univ _)
      by_cases hj₂ : j.1 ∈ J₂
      ·
        have hyj' : y j.1 ∈ A₁ j ∩ A₂ ⟨j.1, hj₂⟩ := by
          simpa [B, K, j.2, hj₂] using hyj
        exact hyj'.1
      · simpa [B, K, j.2, hj₂] using hyj
    · intro j _
      have hyj := hy ⟨j.1, Finset.mem_union.mpr <| Or.inr j.2⟩ (mem_univ _)
      by_cases hj₁ : j.1 ∈ J₁
      ·
        have hyj' : y j.1 ∈ A₁ ⟨j.1, hj₁⟩ ∩ A₂ j := by
          simpa [B, K, hj₁, j.2] using hyj
        exact hyj'.2
      · simpa [B, K, hj₁, j.2] using hyj
  · intro hy
    rw [mem_cylinder, mem_pi]
    rw [mem_inter_iff, mem_cylinder, mem_cylinder, mem_pi, mem_pi] at hy
    intro j _
    dsimp [B]
    by_cases hj₁ : j.1 ∈ J₁
    · have hy₁ : y j.1 ∈ A₁ ⟨j.1, hj₁⟩ := hy.1 ⟨j.1, hj₁⟩ (mem_univ _)
      by_cases hj₂ : j.1 ∈ J₂
      ·
        have hy₂ : y j.1 ∈ A₂ ⟨j.1, hj₂⟩ := hy.2 ⟨j.1, hj₂⟩ (mem_univ _)
        simpa [B, K, hj₁, hj₂] using And.intro hy₁ hy₂
      · simpa [hj₁, hj₂] using hy₁
    ·
      have hj₂ : j.1 ∈ J₂ := by
        have hjK : j.1 ∈ K := j.2
        simpa [K] using (Finset.mem_union.mp hjK).resolve_left hj₁
      simpa [hj₁, hj₂] using hy.2 ⟨j.1, hj₂⟩ (mem_univ _)

/-- Companion bridge: Lemma 14.11 also yields the weaker mathlib `IsPiSystem` formulation. -/
theorem isPiSystem_iUnion_restrictedRectangularCylinderSetsWithBase
    (ℰ : ∀ i, Set (Set (Ω i))) (hℰ : ∀ i, IsInterClosed (ℰ i)) :
    IsPiSystem (⋃ J : Finset I, restrictedRectangularCylinderSetsWithBase ℰ J) :=
  (isInterClosed_iUnion_restrictedRectangularCylinderSetsWithBase ℰ hℰ).isPiSystem
