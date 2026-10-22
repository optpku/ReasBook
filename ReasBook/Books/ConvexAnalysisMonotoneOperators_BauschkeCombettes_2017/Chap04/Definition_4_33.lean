/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]
variable {D : Set H}

/-- Definition 4.33: a map `T : D → H` is averaged with constant `α` when `α ∈ ]0, 1[` and
there is a nonexpansive map `R : D → H` such that `T = (1 - α) Id + α R`. -/
def AveragedWith (α : ℝ) (T : D → H) : Prop :=
  α ∈ Set.Ioo (0 : ℝ) 1 ∧
    ∃ R : D → H, LipschitzWith 1 R ∧
      T = fun x : D ↦ (1 - α) • (x : H) + α • R x

/-- An `α`-averaged map has averaging parameter `α ∈ ]0, 1[`. -/
theorem AveragedWith.mem_Ioo {α : ℝ} {T : D → H} (hT : AveragedWith α T) :
    α ∈ Set.Ioo (0 : ℝ) 1 :=
  hT.1

-- Proof sketch: unfold `AveragedWith`.
/-- A map is `α`-averaged exactly when `α ∈ ]0, 1[` and it is the affine combination of the
identity on `D` with a nonexpansive companion map. -/
theorem averagedWith_iff {α : ℝ} {T : D → H} :
    AveragedWith α T ↔
      α ∈ Set.Ioo (0 : ℝ) 1 ∧
        ∃ R : D → H, LipschitzWith 1 R ∧
          T = fun x : D ↦ (1 - α) • (x : H) + α • R x := by
  rfl

/-- A self-map is `α`-averaged when it is `α`-averaged on the whole space. -/
def Averaged (α : ℝ) (T : H → H) : Prop :=
  AveragedWith α (fun x : (Set.univ : Set H) ↦ T x)

/-- Unfolding `Averaged` recovers the whole-space restriction formulation. -/
@[simp] theorem averaged_iff_averagedWith_univ {α : ℝ} {T : H → H} :
    Averaged α T ↔ AveragedWith α (fun x : (Set.univ : Set H) ↦ T x) := by
  rfl

end
