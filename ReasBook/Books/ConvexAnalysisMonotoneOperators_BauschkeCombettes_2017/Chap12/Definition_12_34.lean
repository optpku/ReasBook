/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Tactic.Recall
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_7
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Definition_8_7

-- Declarations for this item will be appended below by the statement pipeline.

open Set

noncomputable section

universe u v

namespace ERealFunction

variable {H : Type u} {K : Type v}

/-- The infimal postcomposition of `f` along `L` is the infimum of the values of `f` on each
fiber of `L`. -/
noncomputable def infimalPostcomposition (L : H → K) (f : H → EReal) : K → EReal :=
  fun y ↦ sInf (f '' (L ⁻¹' {y}))

infixr:70 " ▷ " => fun L f y ↦
  ERealFunction.infimalPostcomposition L (fun x ↦ (f x : EReal)) y

/-- The value of `L ▷ f` at `y` is the infimum of the values of `f` on the fiber `L ⁻¹' {y}`. -/
theorem infimalPostcomposition_apply {α : Type*} [CoeTC α EReal]
    (L : H → K) (f : H → α) (y : K) :
    (L ▷ f) y = sInf ((fun x ↦ (f x : EReal)) '' (L ⁻¹' {y})) :=
  rfl

/- Definition 12.34: the infimal postcomposition of a function `f` by a map `L` is the canonical
owner `infimalPostcomposition`, written `L ▷ f`. -/
recall infimalPostcomposition

namespace infimalPostcomposition

/-- Exactness at `y` means that `(L ▷ f) y` is attained on the fiber `L ⁻¹' {y}` by a finite value
of `f`. -/
def ExactAt (L : H → K) (f : H → Set.Ioi (⊥ : EReal)) (y : K) : Prop :=
  ∃ x : H, x ∈ effectiveDomain f ∧ L x = y ∧ (L ▷ f) y = (f x : EReal)

/-- Exactness at `y` is equivalently membership of `y` in `dom (L ▷ f)` together with a point of
the fiber `L ⁻¹' {y}` attaining `(L ▷ f) y`. -/
theorem exactAt_iff_exists_eq (L : H → K) (f : H → Set.Ioi (⊥ : EReal)) (y : K) :
    ExactAt L f y ↔ y ∈ dom (L ▷ f) ∧ ∃ x : H, L x = y ∧ (L ▷ f) y = (f x : EReal) := by
  constructor
  · rintro ⟨x, hxdom, hxLy, hxy⟩
    refine ⟨?_, ⟨x, hxLy, hxy⟩⟩
    rw [mem_dom_iff, hxy]
    simpa [effectiveDomain] using hxdom
  · rintro ⟨hy, x, hxLy, hxy⟩
    refine ⟨x, ?_, hxLy, hxy⟩
    rw [mem_dom_iff] at hy
    simpa [effectiveDomain] using (show (f x : EReal) < ⊤ by rwa [hxy] at hy)

/-- Exactness at `y` is equivalently attainment of the fiberwise infimum defining `(L ▷ f) y` by
a point of the fiber where `f` is finite. -/
theorem exactAt_iff_exists_isMinOn (L : H → K) (f : H → Set.Ioi (⊥ : EReal)) (y : K) :
    ExactAt L f y ↔
      ∃ x ∈ L ⁻¹' {y}, x ∈ effectiveDomain f ∧ IsMinOn f.asEReal (L ⁻¹' {y}) x := by
  let fiber : Set H := L ⁻¹' {y}
  have happly : (L ▷ f) y = sInf (f.asEReal '' fiber) := by
    simpa [fiber] using (infimalPostcomposition_apply L f y)
  constructor
  · rintro ⟨x, hxdom, hxLy, hxy⟩
    have hxmem : x ∈ fiber := by
      simpa [fiber] using hxLy
    have hsInf : (f x : EReal) = sInf (f.asEReal '' fiber) := by
      rw [← hxy, happly]
    refine ⟨x, hxmem, hxdom, ?_⟩
    rw [isMinOn_iff]
    intro z hzmem
    have hsInf_le : sInf (f.asEReal '' fiber) ≤ f.asEReal z :=
      (isGLB_sInf_image f.asEReal fiber).1 ⟨z, hzmem, rfl⟩
    simpa [hsInf] using hsInf_le
  · rintro ⟨x, hxmem, hxdom, hmin⟩
    refine ⟨x, hxdom, ?_, ?_⟩
    · simpa [fiber] using hxmem
    · exact happly.trans (eq_sInf_image_of_isMinOn hxmem hmin).symm

/-- Exactness of `L ▷ f` means exactness at every point of the domain of the infimal
postcomposition. -/
def Exact (L : H → K) (f : H → Set.Ioi (⊥ : EReal)) : Prop :=
  ∀ ⦃y : K⦄, y ∈ dom (L ▷ f) → ExactAt L f y

end infimalPostcomposition

end ERealFunction
