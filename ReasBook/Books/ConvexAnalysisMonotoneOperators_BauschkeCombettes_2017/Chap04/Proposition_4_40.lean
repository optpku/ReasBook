/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Definition_4_33

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]
variable {D : Set H} {α lam : ℝ} {T : D → H}

/-- Helper for Proposition 4.40: substituting the affine companion of an averaged map into the
relaxed map formula yields the expected new affine companion. -/
private lemma relaxedMap_eq_affine {R : D → H}
    (hT : T = fun x : D ↦ (1 - α) • (x : H) + α • R x) :
    (fun x : D ↦ (1 - lam) • (x : H) + lam • T x) =
      fun x : D ↦ (1 - lam * α) • (x : H) + (lam * α) • R x := by
  ext x
  calc
    (1 - lam) • (x : H) + lam • T x
        = (1 - lam) • (x : H) + lam • ((1 - α) • (x : H) + α • R x) := by
            simp [hT]
    _ = (1 - lam) • (x : H) + (lam * (1 - α)) • (x : H) + (lam * α) • R x := by
          rw [smul_add, ← mul_smul, ← mul_smul]
          simp [add_assoc]
    _ = ((1 - lam) + lam * (1 - α)) • (x : H) + (lam * α) • R x := by
          rw [← add_smul]
    _ = (1 - lam * α) • (x : H) + (lam * α) • R x := by
          congr 1
          ring_nf

/-- Helper for Proposition 4.40: if the relaxed map has affine companion with coefficient
`lam * α`, then solving the identity for `T` recovers the original affine companion when
`lam ≠ 0`. -/
private lemma affine_of_relaxedMap_eq {R : D → H} (hlam0 : lam ≠ 0)
    (hS : (fun x : D ↦ (1 - lam) • (x : H) + lam • T x) =
      fun x : D ↦ (1 - lam * α) • (x : H) + (lam * α) • R x) :
    T = fun x : D ↦ (1 - α) • (x : H) + α • R x := by
  ext x
  have hx := congrArg (fun f ↦ f x) hS
  have hx' : (1 - lam) • (x : H) + lam • T x =
      (1 - lam) • (x : H) + lam • ((1 - α) • (x : H) + α • R x) := by
    calc
      (1 - lam) • (x : H) + lam • T x
          = (1 - lam * α) • (x : H) + (lam * α) • R x := hx
      _ = ((1 - lam) + lam * (1 - α)) • (x : H) + (lam * α) • R x := by
            congr 1
            ring_nf
      _ = (1 - lam) • (x : H) + (lam * (1 - α)) • (x : H) + (lam * α) • R x := by
            rw [add_smul]
      _ = (1 - lam) • (x : H) + lam • ((1 - α) • (x : H) + α • R x) := by
            rw [smul_add, ← mul_smul, ← mul_smul]
            simp [add_assoc]
  have hx'' : lam • T x = lam • ((1 - α) • (x : H) + α • R x) := by
    exact add_left_cancel hx'
  have hx''' := congrArg (fun y : H ↦ lam⁻¹ • y) hx''
  simpa [smul_smul, hlam0] using hx'''

-- Proof sketch: expand `AveragedWith α T` using the canonical affine-companion description,
-- substitute this identity into the relaxation `x ↦ (1 - λ) • x + λ • T x`, and simplify to
-- `(1 - λ * α) • Id + (λ * α) • R`; for the converse, solve the same affine identity for `T`.
/-- Proposition 4.40: if `α ∈ (0,1)` and `λ ∈ (0, 1 / α)`, then `T` is `α`-averaged if and only
if the relaxation `x ↦ (1 - λ) • x + λ • T x` is `(λ * α)`-averaged. -/
theorem averagedWith_iff_averagedWith_relaxedMap
    (hα : α ∈ Set.Ioo (0 : ℝ) 1) (hlam : lam ∈ Set.Ioo (0 : ℝ) (1 / α)) :
    AveragedWith α T ↔
      AveragedWith (lam * α) (fun x : D ↦ (1 - lam) • (x : H) + lam • T x) := by
  have hlam_mul : lam * α ∈ Set.Ioo (0 : ℝ) 1 := by
    refine ⟨mul_pos hlam.1 hα.1, ?_⟩
    have hlt : lam * α < (1 / α) * α := by
      exact mul_lt_mul_of_pos_right hlam.2 hα.1
    have hα0 : α ≠ 0 := ne_of_gt hα.1
    simpa [div_eq_mul_inv, hα0] using hlt
  rw [averagedWith_iff, averagedWith_iff]
  constructor
  · rintro ⟨_, R, hR, hT⟩
    exact ⟨hlam_mul, R, hR, relaxedMap_eq_affine hT⟩
  · rintro ⟨_, R, hR, hS⟩
    exact ⟨hα, R, hR, affine_of_relaxedMap_eq (ne_of_gt hlam.1) hS⟩

end
