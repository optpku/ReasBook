/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_26

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open PointedCone

local notation "Q" => reciprocalEpigraphOnPositiveRay

/- Definition 2.28 is source-facing in the convex-geometry domain of pointed cone hulls in `ℝ²`.

Sampled owner-style declarations:
- `reciprocalEpigraphOnPositiveRay`
- `mem_reciprocalEpigraphOnPositiveRay_iff`
- `PointedCone.hull`
- `PointedCone.ofConeComb`

Best owner abstraction:
- `PointedCone.hull ℝ reciprocalEpigraphOnPositiveRay`

Primitive data:
- the owner set `Q = reciprocalEpigraphOnPositiveRay`

Derived API:
- the product-set description `Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)` of the open positive quadrant;
- the coordinate membership view of the underlying set of `𝒦(Q)`.

Source/core/bridge triage:
- source-facing: the textbook set equality for `𝒦(Q)`;
- core/canonical: `PointedCone.hull ℝ reciprocalEpigraphOnPositiveRay`;
- bridge/view: the membership theorem below. -/

/-- Definition 2.28: the pointed conic hull `𝒦(Q)` of
`Q = reciprocalEpigraphOnPositiveRay` is the open positive quadrant together with the origin. -/
theorem conicHull_reciprocalEpigraphOnPositiveRay_eq_openPositiveQuadrant_or_origin :
    (hull ℝ Q : Set (ℝ × ℝ)) =
      (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) ∪ ({0} : Set (ℝ × ℝ)) := by
  let positiveQuadrantOrOrigin : PointedCone ℝ (ℝ × ℝ) :=
    PointedCone.ofConeComb
      ({x : ℝ × ℝ | x = 0 ∨ 0 < x.1 ∧ 0 < x.2})
      ⟨0, Or.inl rfl⟩
      (fun x hx y hy a ha b hb ↦ by
        rcases hx with rfl | hx
        · rcases hy with rfl | hy
          · exact Or.inl (by simp)
          · rcases eq_or_lt_of_le hb with rfl | hb
            · exact Or.inl (by simp)
            · exact Or.inr (by
                simpa using And.intro (mul_pos hb hy.1) (mul_pos hb hy.2))
        · rcases hy with rfl | hy
          · rcases eq_or_lt_of_le ha with rfl | ha
            · exact Or.inl (by simp)
            · exact Or.inr (by
                simpa using And.intro (mul_pos ha hx.1) (mul_pos ha hx.2))
          · rcases eq_or_lt_of_le ha with rfl | ha
            · rcases eq_or_lt_of_le hb with rfl | hb
              · exact Or.inl (by simp)
              · exact Or.inr (by
                  simpa using And.intro (mul_pos hb hy.1) (mul_pos hb hy.2))
            · rcases eq_or_lt_of_le hb with rfl | hb
              · exact Or.inr (by
                  simpa using And.intro (mul_pos ha hx.1) (mul_pos ha hx.2))
              · exact Or.inr
                  ⟨add_pos (mul_pos ha hx.1) (mul_pos hb hy.1),
                    add_pos (mul_pos ha hx.2) (mul_pos hb hy.2)⟩)
  have hHull :
      hull ℝ Q ≤ positiveQuadrantOrOrigin := by
    refine Submodule.span_le.mpr ?_
    intro y hy
    have hy' := (mem_reciprocalEpigraphOnPositiveRay_iff y).1 hy
    exact Or.inr ⟨hy'.1, lt_of_lt_of_le (one_div_pos.mpr hy'.1) hy'.2⟩
  ext x
  constructor
  · intro hx
    rcases hHull hx with rfl | hx
    · exact Or.inr (by simp)
    · exact Or.inl (by simpa using hx)
  · rintro (hx | rfl)
    · have hx : 0 < x.1 ∧ 0 < x.2 := by simpa using hx
      let r : ℝ := Real.sqrt (x.1 * x.2)
      have hr_pos : 0 < r := by
        dsimp [r]
        exact Real.sqrt_pos.2 (mul_pos hx.1 hx.2)
      let y : ℝ × ℝ := (x.1 / r, x.2 / r)
      have hy_mem : y ∈ Q := by
        refine (mem_reciprocalEpigraphOnPositiveRay_iff y).2 ?_
        constructor
        · dsimp [y]
          exact div_pos hx.1 hr_pos
        · dsimp [y]
          have hr_sq : r ^ 2 = x.1 * x.2 := by
            dsimp [r]
            rw [Real.sq_sqrt (mul_nonneg hx.1.le hx.2.le)]
          have hInv : 1 / (x.1 / r) = r / x.1 := by
            field_simp [hr_pos.ne', hx.1.ne']
          rw [hInv]
          have hEq : r ^ 2 / x.1 = x.2 := by
            field_simp [hx.1.ne']
            nlinarith [hr_sq]
          have hdiv : r / x.1 ≤ x.2 / r := by
            rw [le_div_iff₀ hr_pos]
            have hmul : r / x.1 * r = r ^ 2 / x.1 := by
              field_simp [hx.1.ne']
            rw [hmul]
            exact hEq.le
          exact hdiv
      have hy_hull : y ∈ (hull ℝ Q : Set (ℝ × ℝ)) :=
        subset_hull hy_mem
      have hx_eq : x = r • y := by
        ext <;> dsimp [y] <;> field_simp [hr_pos.ne']
      rw [hx_eq]
      exact (hull ℝ Q).smul_mem hr_pos.le hy_hull
    · exact (hull ℝ Q).zero_mem

/-- Membership in `𝒦(Q)` means either being the origin or having both coordinates strictly
positive. -/
theorem mem_conicHull_reciprocalEpigraphOnPositiveRay_iff (x : ℝ × ℝ) :
    x ∈ (hull ℝ Q : Set (ℝ × ℝ)) ↔
      x = 0 ∨ 0 < x.1 ∧ 0 < x.2 := by
  rw [conicHull_reciprocalEpigraphOnPositiveRay_eq_openPositiveQuadrant_or_origin]
  simp [or_comm]
