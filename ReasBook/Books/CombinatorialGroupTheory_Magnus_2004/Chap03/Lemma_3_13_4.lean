/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

set_option autoImplicit false

/-!
Primary domain: cumulative displacement bounds for isometric scalar actions on pseudometric spaces.

Layer triage:
- `source-facing`: the displacement of a point under a finite successive scalar translate.
- `core/canonical`: `IsIsometricSMul G V` is the owner hypothesis for isometric scalar actions,
  `dist_smul` is the owner one-step invariance lemma, and `List.foldl_append` is the canonical
  snoc decomposition for the successive-translate path.
- `bridge/view`: none; the textbook statement is already a direct estimate on the canonical action.

Domain sampling:
1. `IsIsometricSMul G V` is mathlib's owner predicate for isometric scalar actions.
2. `dist_smul` is the canonical distance-preservation lemma for one translate.
3. `List.foldl_append` is the canonical API for peeling the last step off a successive translate.
4. `dist_triangle` is the owner polygon inequality on a pseudometric space.
-/

section

variable {G : Type u} {V : Type v} [PseudoMetricSpace V] [SMul G V]
variable [IsIsometricSMul G V]

/-- Lemma 3-13-4: for an isometric scalar action on a pseudometric space, the displacement of a point
under a finite successive translate is at most the sum of the individual displacements. -/
theorem dist_foldl_smul_le_sum_dist_smul (v : V) (gs : List G) :
    dist v (gs.foldl (fun x g ↦ g • x) v) ≤ (gs.map fun g ↦ dist v (g • v)).sum := by
  induction gs using List.reverseRecOn with
  | nil =>
      simp
  | append_singleton hs g ih =>
    calc
      dist v ((hs ++ [g]).foldl (fun x g ↦ g • x) v)
          = dist v (g • (hs.foldl (fun x h ↦ h • x) v)) := by
              simp [List.foldl_append]
      _ ≤ dist v (g • v) + dist (g • v) (g • (hs.foldl (fun x g ↦ g • x) v)) := by
            simpa using dist_triangle v (g • v) (g • (hs.foldl (fun x g ↦ g • x) v))
      _ = dist v (g • v) + dist v (hs.foldl (fun x g ↦ g • x) v) := by
            simp
      _ ≤ dist v (g • v) + (hs.map fun h ↦ dist v (h • v)).sum := by
            simpa [add_comm] using add_le_add_left ih (dist v (g • v))
      _ = ((hs ++ [g]).map fun h ↦ dist v (h • v)).sum := by
            simp [List.map_append, add_comm]

end
