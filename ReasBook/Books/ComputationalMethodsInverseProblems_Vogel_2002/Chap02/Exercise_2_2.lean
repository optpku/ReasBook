/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Example_2_3

public section

open scoped ENNReal

namespace RealL2

/-- A real sequence lies in `Memℓp d ∞` exactly when its absolute values are bounded above. -/
theorem memℓp_infty_iff_bddAbove_abs {d : ℕ → ℝ} :
    Memℓp d ∞ ↔ BddAbove (Set.range fun j ↦ |d j|) := by
  simpa [Real.norm_eq_abs] using
    (memℓp_infty_iff : Memℓp d ∞ ↔ BddAbove (Set.range fun j ↦ ‖d j‖))

/-- Exercise 2.2 (1). The coordinatewise diagonal operator from Example 2.3 is bounded if and
only if the coefficient sequence `j ↦ d j` has uniformly bounded absolute values. -/
theorem diagonal_bounded_iff_bddAbove (d : ℕ → ℝ) :
    (∃ D : lp (fun _ : ℕ ↦ ℝ) 2 →L[ℝ] lp (fun _ : ℕ ↦ ℝ) 2, ∀ f j, D f j = d j * f j) ↔
      BddAbove (Set.range fun j ↦ |d j|) := by
  rw [diagonal_bounded_iff, memℓp_infty_iff_bddAbove_abs]

/-- The `lp ... ∞` norm of a bounded real coefficient sequence is the supremum of the absolute
values of its entries. -/
theorem norm_eq_ciSup_abs (d : lp (fun _ : ℕ ↦ ℝ) ∞) :
    ‖d‖ = ⨆ j, |d j| := by
  simpa [Real.norm_eq_abs] using (lp.norm_eq_ciSup d)

/-- Exercise 2.2 (2). The operator norm of the bounded diagonal operator from Example 2.3 equals
the supremum of the absolute values of its coefficients. -/
theorem norm_diagonal_eq_ciSup_abs (d : lp (fun _ : ℕ ↦ ℝ) ∞) :
    ‖diagonal d‖ = ⨆ j, |d j| := by
  rw [norm_diagonal, norm_eq_ciSup_abs]

end RealL2
