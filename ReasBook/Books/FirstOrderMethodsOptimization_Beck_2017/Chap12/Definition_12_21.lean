/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_7
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Definition_12_12
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Definition_12_13

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Matrix.Norms.Frobenius

noncomputable section

section

variable {rows cols : ℕ}

local notation "M" => Matrix (Fin rows) (Fin cols) ℝ

/-
Definition 12.21 is a `bridge/view`: the source item fixes the isotropic total-variation
regularizer in the Chapter 12.12 two-dimensional denoising owner.

Domain sampling against the nearby matrix-space API gives:
- `core/canonical`: `two_dimensional_total_variation_denoising_objective` from
  Definition 12.12, the matrix denoising owner specialized to a matrix regularizer `TV`;
- `source-facing`: the isotropic total-variation owner `TV_I` from Definition 12.13;
- `source-facing`: `PosReal` from Definition 6.7, the chapter's owner for positive source
  parameters;
- `derived API`: `denoising_problem_objective_apply`, specialized to the Chapter 12.12 owner;
- `derived API`: `isotropic_two_dimensional_total_variation_formula`, the textbook expansion of
  `TV_I` on nonempty matrices.

Primitive data here are only the datum `d`, the isotropic regularizer `TV_I`, and the positive
regularization parameter `λ`, encoded canonically as `PosReal`. The objective itself should
therefore be presented as the `TV_I` and `PosReal` specialization of the existing
Chapter 12.12 owner rather than by widening the source parameter to a bare real scalar, and its
pointwise expansion should be derived from `denoising_problem_objective_apply`. -/

/- Definition 12.21 is the direct specialization of the canonical Chapter 12.12 owner to the
isotropic regularizer `TV_I` and the chapter's positive parameter type `PosReal`. -/
recall two_dimensional_total_variation_denoising_objective
recall denoising_problem_objective_apply

set_option linter.hashCommand false

/- In source notation, the isotropic denoising objective is exactly
`two_dimensional_total_variation_denoising_objective TV_I`. -/
#check fun (d : M) (lam : PosReal) ↦
  two_dimensional_total_variation_denoising_objective TV_I d lam

/- Its pointwise evaluation, still with the source parameter `lam : PosReal`, is the
corresponding direct specialization of `denoising_problem_objective_apply`. -/
#check fun (d : M) (lam : PosReal) ↦
  denoising_problem_objective_apply d
    (fun y ↦ ↑((lam : ℝ) * TV_I y))
    (id : M → M)

-- Proof sketch: combine the specialized Chapter 12.12 apply formula with
-- `isotropic_two_dimensional_total_variation_formula` to expand the isotropic regularizer into
-- the explicit interior and boundary finite-difference sums from the textbook.
/-- On a nonempty `(rows + 1) × (cols + 1)` matrix, the isotropic denoising objective expands to
the textbook formula with the full `TV_I` finite-difference sum. -/
theorem isotropic_two_dimensional_total_variation_denoising_objective_formula
    (d x : Matrix (Fin (rows + 1)) (Fin (cols + 1)) ℝ) (lam : PosReal) :
    two_dimensional_total_variation_denoising_objective TV_I d lam x =
      ((‖x - d‖ ^ (2 : ℕ) / 2 : ℝ) : EReal) +
        ↑((lam : ℝ) *
          ((∑ i : Fin rows, ∑ j : Fin cols,
              Real.sqrt
                ((x (Fin.castSucc i) (Fin.castSucc j) - x (Fin.castSucc i) j.succ) ^ (2 : ℕ) +
                  (x (Fin.castSucc i) (Fin.castSucc j) - x i.succ (Fin.castSucc j)) ^
                    (2 : ℕ))) +
            ∑ j : Fin cols, |x (Fin.last rows) (Fin.castSucc j) - x (Fin.last rows) j.succ| +
            ∑ i : Fin rows, |x (Fin.castSucc i) (Fin.last cols) - x i.succ (Fin.last cols)|)) := by
  rw [two_dimensional_total_variation_denoising_objective,
    denoising_problem_objective_apply,
    isotropic_two_dimensional_total_variation_formula]
  simp [id]

end
