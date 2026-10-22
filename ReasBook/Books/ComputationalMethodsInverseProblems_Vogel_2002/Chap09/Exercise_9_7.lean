/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Prop_9_15.Projector

public section

namespace NonnegativeOrthant

/-- Exercise 9.7. The orthant projection operator `projector n` from `(9.23)`
has coordinates given by `(9.24)`: for each `i`, `(projector n f) i = max (f i)
0`. -/
theorem projector_apply_eq_max
    (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n))
    (i : Fin n) :
    projector n f i = max (f i) 0 := by
  let g : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 fun j ↦ max (f j) 0
  have hg_apply (j : Fin n) : g j = max (f j) 0 := by
    simp [g]
  have hg_mem : g ∈ feasibleSet n := by
    rw [mem_feasibleSet]
    intro j
    rw [hg_apply]
    exact le_max_right _ _
  have hg_inner : ∀ w ∈ feasibleSet n, inner ℝ (f - g) (w - g) ≤ 0 := by
    intro w hw
    rw [PiLp.inner_apply]
    refine Finset.sum_nonpos fun j _ ↦ ?_
    by_cases hfj : 0 ≤ f j
    · simp [hg_apply, max_eq_left hfj]
    · have hfj_neg : f j < 0 := lt_of_not_ge hfj
      have hwj : 0 ≤ w j := (mem_feasibleSet.mp hw) j
      simpa [hg_apply, max_eq_right hfj_neg.le, Real.inner_apply] using
        (mul_nonpos_of_nonneg_of_nonpos hwj hfj_neg.le : w j * f j ≤ 0)
  have hg_norm :
      ‖f - g‖ = ⨅ w : feasibleSet n, ‖f - w‖ := by
    exact
      (norm_eq_iInf_iff_real_inner_le_zero (closedConvex_feasibleSet n).convex hg_mem).2
        hg_inner
  have hg_min : IsMinOn (fun v ↦ ‖f - v‖) (feasibleSet n) g := by
    rw [isMinOn_iff]
    intro w hw
    calc
      ‖f - g‖ = ⨅ z : feasibleSet n, ‖f - z‖ := hg_norm
      _ ≤ ‖f - (⟨w, hw⟩ : feasibleSet n)‖ := by
        apply ciInf_le
        use 0
        rintro y ⟨z, rfl⟩
        exact norm_nonneg _
      _ = ‖f - w‖ := by rfl
  have hproj : projector n f = g := by
    rw [projector_eq_proj]
    exact
      EuclideanProjection.eq_proj_of_mem_of_isMinOn
        (feasibleSet n)
        (feasibleSet_nonempty n)
        (closedConvex_feasibleSet n)
        f
        g
        hg_mem
        hg_min
  simpa [hg_apply] using congrArg (fun u ↦ u i) hproj

end NonnegativeOrthant
