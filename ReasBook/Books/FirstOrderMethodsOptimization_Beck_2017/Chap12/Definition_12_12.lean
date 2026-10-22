/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_7
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Definition_12_10

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Matrix Matrix.Norms.Frobenius

noncomputable section

section

variable {m n : ℕ}

local notation "Mmn" => Matrix (Fin m) (Fin n) ℝ

/-
Definition 12.12 is `source-facing`: it fixes the two-dimensional total-variation denoising
objective on `ℝ^(m × n)` with a matrix-side total-variation regularizer `TV`.

Domain sampling against the nearby project owners gives:
- `source-facing`: the matrix denoising objective
  `x ↦ (1 / 2) ‖x - d‖_F^2 + λ TV(x)`;
- `core/canonical`: `denoising_problem_objective` from Definition 12.10, the chapter owner for
  quadratic-data-fidelity denoising models;
- `derived API`: `denoising_problem_objective_apply`, whose specialization gives the pointwise
  formula below.

Primitive data here are only the matrix datum `d`, the positive scalar parameter `λ : PosReal`,
and the regularizer `TV : Mmn → ℝ`. The public owner should therefore be the direct
specialization of the Chapter 12 denoising owner to the matrix space and identity map, with the
pointwise formula derived from that owner rather than from a parallel real-valued helper. -/

/-- Definition 12.12: the two-dimensional total variation denoising problem is the minimization
of the Chapter 12 denoising objective specialized to the matrix space, the identity map, and a
matrix-side regularizer. -/
abbrev two_dimensional_total_variation_denoising_objective
    (TV : Mmn → ℝ) (d : Mmn) (lam : PosReal) : Mmn → EReal :=
  denoising_problem_objective d
    (fun x ↦ ↑((lam : ℝ) * TV x))
    id

/- The companion apply theorem follows the nearby Chapter 12 pattern from
`denoising_problem_objective_apply`. -/
/-- Evaluating the companion `EReal` denoising objective at `x` gives
`(1 / 2) ‖x - d‖_F^2 + λ TV(x)`. -/
@[simp] theorem two_dimensional_total_variation_denoising_objective_apply
    (TV : Mmn → ℝ) (d x : Mmn) (lam : PosReal) :
    two_dimensional_total_variation_denoising_objective TV d lam x =
      ((‖x - d‖ ^ (2 : ℕ) / 2 : ℝ) : EReal) + ↑((lam : ℝ) * TV x) := rfl

end
