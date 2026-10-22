/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Normed.Lp.lpHolder
public import Mathlib.Analysis.Normed.Operator.Mul

public section

open scoped ENNReal

noncomputable section

namespace RealL2

/-- The bounded diagonal operator on real `lp (fun _ : ℕ ↦ ℝ) 2` determined by `d`. -/
noncomputable def diagonal (d : lp (fun _ : ℕ ↦ ℝ) ∞) :
    lp (fun _ : ℕ ↦ ℝ) 2 →L[ℝ] lp (fun _ : ℕ ↦ ℝ) 2 :=
  lp.mapCLM 2
    (fun j => ContinuousLinearMap.mul ℝ ℝ (d j))
    (norm_nonneg ‖d‖)
    (fun j =>
      (ContinuousLinearMap.opNorm_mul_apply ℝ ℝ (d j)).le.trans
        ((lp.norm_eq_ciSup d).symm ▸
          (le_ciSup (memℓp_infty_iff.mp d.prop) j).trans_eq
            (Real.norm_of_nonneg (Real.iSup_nonneg fun i => norm_nonneg (d i))).symm))

/-- The diagonal operator acts by coordinatewise multiplication. -/
theorem diagonal_apply (d : lp (fun _ : ℕ ↦ ℝ) ∞) (f : lp (fun _ : ℕ ↦ ℝ) 2) (j : ℕ) :
    diagonal d f j = d j * f j := by
  rfl

/-- The diagonal operator sends a basis vector to the correspondingly scaled basis vector. -/
theorem diagonal_single (d : lp (fun _ : ℕ ↦ ℝ) ∞) (j : ℕ) (a : ℝ) :
    diagonal d (lp.single 2 j a) = lp.single 2 j (d j * a) := by
  ext k
  by_cases hk : k = j
  · subst hk
    simp [diagonal_apply]
  · simp [diagonal_apply, hk]

end RealL2
