/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap11.Definition_11_4
import FirstOrderMethodsOptimization_Beck_2017.Chap11.Lemma_11_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open scoped Gradient

/- Proposition 11.1 is `bridge/view` in the Chapter 11 block proximal-gradient domain. The owner
objects already live upstream in `Definition_11_4`:
- `BlockProximalGradientAssumptions` is the ambient block-problem owner;
- `block_coordinate_update` is the canonical one-block update map;
- `IsBlockProximalGradientProblem.gradient_mapping_def` is the canonical residual formula.

The primitive data here are only the owner `hproblem`, the selected block `i`, and the current
point `x`. The step-norm inequality is derived API: it rewrites the canonical sufficient-decrease
estimate from the gradient-mapping form into the full-update norm form. -/

section

variable {ι : Type u} [Fintype ι] {Ei : ι → Type v}
variable [∀ i, NormedAddCommGroup (Ei i)] [∀ i, InnerProductSpace ℝ (Ei i)]
variable {Lf : NNReal} {Li : (i : ι) → PosReal}
variable {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
variable {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
variable {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ}

local notation "F" => composite_model_objective f (separableSum g)

namespace BlockProximalGradientAssumptions

-- Proof sketch: apply the owner theorem
-- `BlockProximalGradientAssumptions.block_partial_gradient_sufficient_decrease` at the textbook
-- stepsize `M = L_i`. Rewrite the residual through the canonical owner theorem
-- `IsBlockProximalGradientProblem.gradient_mapping_def`, so the factor
-- `(1 / (2 L_i)) ‖G^i_{L_i}(x)‖²` becomes `(L_i / 2) ‖x_i - T_{L_i}^i(x)‖²`. Then identify the
-- full one-block update with `block_coordinate_update x i (T_{L_i}^i(x) - x_i)` and use
-- `Pi.norm_single` to rewrite that block residual norm as the full-step norm `‖x - x⁺‖`.
/-- Proposition 11.1: under the standing assumptions of the block proximal-gradient method, the
sufficient decrease inequality can be written in terms of the full one-block updated vector
`x⁺ = block_coordinate_update x i (T[Li i; hproblem] x i - x i)`, as
`F(x) - F(x⁺) ≥ (L_i / 2) ‖x - x⁺‖²`. -/
theorem block_partial_gradient_sufficient_decrease_step_norm
    (hproblem : BlockProximalGradientAssumptions f g block_gradient XStar FOpt Lf Li)
    (i : ι) [ProperSpace (Ei i)] (x : effective_domain (separableSum g)) :
    let hcore : IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li :=
      hproblem.toIsBlockProximalGradientProblem;
    let xPlus :=
      block_coordinate_update x.1 i (T[Li i; hcore] x.1 i - x.1 i);
    F x.1 - F xPlus ≥
      ((((Li i : ℝ) / 2) * ‖x.1 - xPlus‖ ^ (2 : ℕ) : ℝ) : EReal) := by
  let hcore : IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li :=
    hproblem.toIsBlockProximalGradientProblem
  let x' : (j : ι) → Ei j := x
  let xPlus := block_coordinate_update x' i (T[Li i; hcore] x' i - x' i)
  have hdecrease :
      F x' - F xPlus ≥
        ((((1 : ℝ) / (2 * (Li i : ℝ))) *
            ‖G[Li i; hcore] x' i‖ ^ (2 : ℕ) : ℝ) : EReal) := by
    simpa [hcore, x', xPlus] using hproblem.block_partial_gradient_sufficient_decrease i x
  have hdecrease' :
      F x' - F xPlus ≥
        ((((1 : ℝ) / (2 * (Li i : ℝ))) *
            ‖(Li i : ℝ) • (x' i - T[Li i; hcore] x' i)‖ ^ (2 : ℕ) : ℝ) : EReal) := by
    simpa only [IsBlockProximalGradientProblem.gradient_mapping_def] using hdecrease
  have hstep :
      x' - xPlus = 𝒰[i] (x' i - T[Li i; hcore] x' i) := by
    classical
    ext j
    by_cases hj : j = i
    · subst j
      simp [xPlus, block_coordinate_update_apply_same]
    · simp [xPlus, block_coordinate_update_apply_ne, hj]
  have hnorm :
      ‖x' - xPlus‖ = ‖x' i - T[Li i; hcore] x' i‖ := by
    classical
    rw [hstep]
    have hsingle :
        ‖Pi.single i (x' i - T[Li i; hcore] x' i)‖ =
          ‖x' i - T[Li i; hcore] x' i‖ := by
      simpa using (Pi.norm_single (x' i - T[Li i; hcore] x' i))
    simpa using hsingle
  have hcoeff :
      (((1 : ℝ) / (2 * (Li i : ℝ))) *
          ‖(Li i : ℝ) • (x' i - T[Li i; hcore] x' i)‖ ^ (2 : ℕ) : ℝ) =
        (((Li i : ℝ) / 2) * ‖x' - xPlus‖ ^ (2 : ℕ) : ℝ) := by
    have hLi_ne : (Li i : ℝ) ≠ 0 := ne_of_gt (Li i).2
    rw [norm_smul, Real.norm_of_nonneg (show 0 ≤ (Li i : ℝ) by exact le_of_lt (Li i).2), hnorm]
    field_simp [hLi_ne]
  have hcoeffE :
      (((((1 : ℝ) / (2 * (Li i : ℝ))) *
            ‖(Li i : ℝ) • (x' i - T[Li i; hcore] x' i)‖ ^ (2 : ℕ) : ℝ)) : EReal) =
        ((((Li i : ℝ) / 2) * ‖x' - xPlus‖ ^ (2 : ℕ) : ℝ) : EReal) :=
    congrArg (fun r : ℝ ↦ (r : EReal)) hcoeff
  rw [hcoeffE] at hdecrease'
  simpa [hcore, x', xPlus] using hdecrease'

end BlockProximalGradientAssumptions

end
