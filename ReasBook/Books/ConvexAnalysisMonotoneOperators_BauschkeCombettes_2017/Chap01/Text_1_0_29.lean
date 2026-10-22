/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter

universe u

namespace Net

variable {A : Type u} [Preorder A] [IsDirectedOrder A]

/-- The limit inferior of a net is the supremum of the infima of its tails. -/
-- Proof sketch: unfold `Net.liminf`, rewrite `Filter.liminf` with
-- `Filter.liminf_eq_sSup_sInf`, and specialize `Filter.mem_atTop_sets` to identify the sets in
-- `atTop` with the tails `Set.Ici a`.
theorem liminf_eq_sSup_tail_sInf [Nonempty A] (ξ : A → EReal) :
    Filter.liminf ξ atTop = sSup (Set.range fun a : A ↦ sInf (ξ '' Set.Ici a)) := by
  refine le_antisymm ?_ ?_
  · calc
      Filter.liminf ξ atTop
          = sSup ((fun I ↦ sInf (ξ '' I)) '' (atTop : Filter A).sets) := by
              simpa using (Filter.liminf_eq_sSup_sInf (atTop : Filter A) ξ)
      _ ≤ sSup (Set.range fun a : A ↦ sInf (ξ '' Set.Ici a)) := by
            refine sSup_le ?_
            intro r hr
            rcases hr with ⟨I, hI, rfl⟩
            rcases mem_atTop_sets.mp hI with ⟨a, ha⟩
            exact le_trans (sInf_le_sInf (Set.image_mono ha)) (le_sSup ⟨a, rfl⟩)
  · calc
      sSup (Set.range fun a : A ↦ sInf (ξ '' Set.Ici a))
          ≤ sSup ((fun I ↦ sInf (ξ '' I)) '' (atTop : Filter A).sets) := by
            refine sSup_le ?_
            intro r hr
            rcases hr with ⟨a, rfl⟩
            exact le_sSup ⟨Set.Ici a, mem_atTop_sets.mpr ⟨a, fun _ hb ↦ hb⟩, rfl⟩
      _ = Filter.liminf ξ atTop := by
            simpa using (Filter.liminf_eq_sSup_sInf (atTop : Filter A) ξ).symm

/-- The limit superior of a net is the infimum of the suprema of its tails. -/
-- Proof sketch: unfold `Net.limsup`, rewrite `Filter.limsup` with
-- `Filter.limsup_eq_sInf_sSup`, and use `Filter.mem_atTop_sets` to replace sets in `atTop` by the
-- tails `Set.Ici a`.
theorem limsup_eq_sInf_tail_sSup [Nonempty A] (ξ : A → EReal) :
    Filter.limsup ξ atTop = sInf (Set.range fun a : A ↦ sSup (ξ '' Set.Ici a)) := by
  refine le_antisymm ?_ ?_
  · calc
      Filter.limsup ξ atTop
          = sInf ((fun I ↦ sSup (ξ '' I)) '' (atTop : Filter A).sets) := by
              simpa using (Filter.limsup_eq_sInf_sSup (atTop : Filter A) ξ)
      _ ≤ sInf (Set.range fun a : A ↦ sSup (ξ '' Set.Ici a)) := by
            refine le_sInf ?_
            intro r hr
            rcases hr with ⟨a, rfl⟩
            exact sInf_le_of_le
              ⟨Set.Ici a, mem_atTop_sets.mpr ⟨a, fun _ hb ↦ hb⟩, rfl⟩ le_rfl
  · calc
      sInf (Set.range fun a : A ↦ sSup (ξ '' Set.Ici a))
          ≤ sInf ((fun I ↦ sSup (ξ '' I)) '' (atTop : Filter A).sets) := by
            refine le_sInf ?_
            intro r hr
            rcases hr with ⟨I, hI, rfl⟩
            rcases mem_atTop_sets.mp hI with ⟨a, ha⟩
            exact sInf_le_of_le ⟨a, rfl⟩ (sSup_le_sSup (Set.image_mono ha))
      _ = Filter.limsup ξ atTop := by
            simpa using (Filter.limsup_eq_sInf_sSup (atTop : Filter A) ξ).symm

/-- Text 1.0.29: for an extended-real-valued net indexed by a nonempty directed set, the limit
inferior is the supremum of the infima of the tails and the limit superior is the infimum of the
suprema of the tails. -/
-- Proof sketch: combine `Net.liminf_eq_sSup_tail_sInf` and `Net.limsup_eq_sInf_tail_sSup`.
theorem tail_liminf_limsup_formulas [Nonempty A] (ξ : A → EReal) :
    Filter.liminf ξ atTop = sSup (Set.range fun a : A ↦ sInf (ξ '' Set.Ici a)) ∧
      Filter.limsup ξ atTop = sInf (Set.range fun a : A ↦ sSup (ξ '' Set.Ici a)) := by
  exact ⟨liminf_eq_sSup_tail_sInf ξ, limsup_eq_sInf_tail_sSup ξ⟩

end Net
