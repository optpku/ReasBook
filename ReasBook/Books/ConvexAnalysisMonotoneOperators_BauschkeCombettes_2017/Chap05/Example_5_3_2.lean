/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Definition_4_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap05.Definition_5_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {H : Type u} [NormedAddCommGroup H]
variable {D : Set H}

-- Proof sketch: for each ambient fixed point of `T`, apply quasinonexpansiveness to the iterate
-- `(T^[n]) x₀` and use `T ((T^[n]) x₀) = (T^[n.succ]) x₀` to obtain the one-step Fejér
-- inequality.
/-- Example 5.3.2: the Picard iterates of a quasinonexpansive self-map are Fejér monotone with
respect to the ambient realization of its fixed-point set. -/
theorem quasinonexpansive_iterates_fejer_monotone
    (T : D → D) (hT : IsQuasinonexpansiveOn (fun x : D ↦ (T x : H))) (x₀ : D) :
    FejerMonotone (Subtype.val '' Function.fixedPoints T) (fun n ↦ (T^[n] x₀ : H)) := by
  -- Unfold Fejer monotonicity and represent the ambient point by a subtype fixed point.
  intro z hz n
  rcases hz with ⟨y, hyfix, rfl⟩
  -- Convert the subtype fixed-point equality into the ambient equality used by `hT`.
  have hy : (T y : H) = y := by
    exact congrArg Subtype.val (Function.mem_fixedPoints_iff.mp hyfix)
  -- Apply quasinonexpansiveness to the nth iterate and rewrite the successor iterate.
  simpa [dist_eq_norm, Function.iterate_succ_apply', Nat.succ_eq_add_one] using
    hT ((T^[n]) x₀) y hy

end
