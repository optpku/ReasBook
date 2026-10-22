/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Set

universe u

namespace ERealFunction

variable {X : Type u}

/-- Definition 1.7 (1): the infimum of an extended-real-valued function over a set is the infimum
of its image on that set, namely `sInf (f '' C)`. -/
theorem isGLB_sInf_image (f : X → EReal) (C : Set X) :
    IsGLB (f '' C) (sInf (f '' C)) :=
  isGLB_sInf (f '' C)

/-- Definition 1.7 (3): a minimizer of `f` on `C` realizes the infimum of `f` on `C`. -/
theorem eq_sInf_image_of_isMinOn {f : X → EReal} {C : Set X} {x : X}
    (hx : x ∈ C) (hmin : IsMinOn f C x) :
    f x = sInf (f '' C) := by
  have hglb : IsGLB (f '' C) (f x) := by
    simpa only [mem_image] using hmin.isGLB hx
  exact hglb.unique (isGLB_sInf_image f C)

/-- Definition 1.7 (2): a function achieves its infimum over `C` exactly when some point of `C`
is a minimizer, equivalently when some point of `C` evaluates to `sInf (f '' C)`. -/
theorem exists_isMinOn_iff_exists_eq_sInf_image (f : X → EReal) (C : Set X) :
    (∃ x ∈ C, IsMinOn f C x) ↔ ∃ x ∈ C, f x = sInf (f '' C) := by
  constructor
  · rintro ⟨x, hxC, hmin⟩
    exact ⟨x, hxC, eq_sInf_image_of_isMinOn hxC hmin⟩
  · rintro ⟨x, hxC, hx⟩
    refine ⟨x, hxC, ?_⟩
    rw [isMinOn_iff]
    intro y hyC
    have hsInf_le : sInf (f '' C) ≤ f y := by
      exact (isGLB_sInf_image f C).1 (mem_image_of_mem f hyC)
    simpa [hx] using hsInf_le

/-- Definition 1.7 (4): the supremum of an extended-real-valued function over a set is the
supremum of its image on that set, namely `sSup (f '' C)`. -/
theorem isLUB_sSup_image (f : X → EReal) (C : Set X) :
    IsLUB (f '' C) (sSup (f '' C)) :=
  isLUB_sSup (f '' C)

/-- Definition 1.7 (6): a maximizer of `f` on `C` realizes the supremum of `f` on `C`. -/
theorem eq_sSup_image_of_isMaxOn {f : X → EReal} {C : Set X} {x : X}
    (hx : x ∈ C) (hmax : IsMaxOn f C x) :
    f x = sSup (f '' C) := by
  have hlub : IsLUB (f '' C) (f x) := by
    simpa only [mem_image] using hmax.isLUB hx
  exact hlub.unique (isLUB_sSup_image f C)

/-- Definition 1.7 (5): a function achieves its supremum over `C` exactly when some point of `C`
is a maximizer, equivalently when some point of `C` evaluates to `sSup (f '' C)`. -/
theorem exists_isMaxOn_iff_exists_eq_sSup_image (f : X → EReal) (C : Set X) :
    (∃ x ∈ C, IsMaxOn f C x) ↔ ∃ x ∈ C, f x = sSup (f '' C) := by
  constructor
  · rintro ⟨x, hxC, hmax⟩
    exact ⟨x, hxC, eq_sSup_image_of_isMaxOn hxC hmax⟩
  · rintro ⟨x, hxC, hx⟩
    refine ⟨x, hxC, ?_⟩
    rw [isMaxOn_iff]
    intro y hyC
    have hy_le : f y ≤ sSup (f '' C) := by
      exact (isLUB_sSup_image f C).1 (mem_image_of_mem f hyC)
    simpa [hx] using hy_le

end ERealFunction
