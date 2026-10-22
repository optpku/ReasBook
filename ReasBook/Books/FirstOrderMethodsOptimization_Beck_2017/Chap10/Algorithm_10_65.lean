/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

variable {n : ℕ}

local notation "E" => Fin n → ℝ

/- Algorithm 10.65 is `source-facing`: the textbook specifies a concrete recursion on the
coordinate vector `x^k ∈ ℝ^n`, together with a noncanonical choice of a maximizing index
`i_k ∈ arg max_i |A_i x^k + b_i|`.

Domain sampling against the surrounding project and the nearby block-coordinate API gives:
- the main public owner should remain the recursive iterate sequence itself, as in Algorithms 8.6,
  8.9, and 10.61;
- the primitive one-step data are the current point, the selected index, and the scalar
  displacement in that coordinate, whose canonical coordinate-space realization is `Pi.single`;
- the noncanonical `arg max` choice should remain explicit as an index-selection rule;
- the maximizing condition should be recorded separately by an admissibility predicate rather than
  hidden behind a chosen witness.

Because the source simultaneously uses rows `A_i`, coordinates `x_j`, and a one-coordinate update,
the faithful ambient model stays the coordinate space `Fin n → ℝ`. -/

/-- Algorithm 10.65: given row vectors `A_i`, affine offsets `b_i`, a positive parameter
`L_f^(1)`, an initial point `x^0 = x0`, and a rule selecting an index `i_k`, Algorithm G1
generates the iterate sequence by keeping all coordinates except the selected one fixed and
updating
`x_(i_k)^(k+1) = x_(i_k)^k - (1 / L_f^(1)) (A_(i_k) x^k + b_(i_k))`. -/
def max_row_residual_coordinate_method
    (A : Fin n → E) (b : Fin n → ℝ) (Lf1 : PosReal)
    (i : ℕ → E → Fin n) (x0 : E) : ℕ → E
  | 0 => x0
  | k + 1 =>
      let xk := max_row_residual_coordinate_method A b Lf1 i x0 k
      let ik := i k xk
      xk + Pi.single ik (- (dotProduct (A ik) xk + b ik) / (Lf1 : ℝ))

/-- An index-selection rule is admissible for Algorithm G1 when, at each iterate `x^k`, the
selected index `i_k` attains the maximum of the residual profile
`j ↦ |A_j x^k + b_j|`. -/
def max_row_residual_coordinate_method_is_admissible
    (A : Fin n → E) (b : Fin n → ℝ) (Lf1 : PosReal)
    (i : ℕ → E → Fin n) (x0 : E) : Prop :=
  ∀ k,
    let xk := max_row_residual_coordinate_method A b Lf1 i x0 k
    ∀ j : Fin n, |dotProduct (A j) xk + b j| ≤ |dotProduct (A (i k xk)) xk + b (i k xk)|

section

variable (A : Fin n → E) (b : Fin n → ℝ) (Lf1 : PosReal) (i : ℕ → E → Fin n) (x0 : E)

local notation "x[" k "]" => max_row_residual_coordinate_method A b Lf1 i x0 k

-- Proof sketch: unfold the recursive definition of `max_row_residual_coordinate_method` at `0`.
/-- The Algorithm G1 iterate sequence starts at the prescribed initial point `x^0 = x0`. -/
theorem max_row_residual_coordinate_method_zero :
    x[0] = x0 := rfl

-- Proof sketch: unfold the recursive definition of `max_row_residual_coordinate_method` at
-- `k + 1`; the successor branch is exactly the single-coordinate displacement at the selected
-- index, equivalently the source one-coordinate update.
/-- One step of Algorithm G1 adds the single-coordinate displacement
`-((A_(i_k) x^k + b_(i_k)) / L_f^(1)) e_(i_k)`, equivalently updating only the selected
coordinate `i_k` and leaving all others unchanged. -/
theorem max_row_residual_coordinate_method_succ (k : ℕ) :
    x[k + 1] =
      x[k] + Pi.single (i k x[k])
        (- (dotProduct (A (i k x[k])) x[k] + b (i k x[k])) / (Lf1 : ℝ)) := rfl

-- Proof sketch: unfold `max_row_residual_coordinate_method_is_admissible`, specialize at `k`,
-- and evaluate the stored maximality inequality at the competitor index `j`.
set_option linter.unusedVariables false in
/-- Under the admissibility condition, the selected index at iteration `k` has residual at least
as large as every competing index. -/
theorem max_row_residual_coordinate_method_selected_index_maximizes
    (h : max_row_residual_coordinate_method_is_admissible A b Lf1 i x0) (k : ℕ) (j : Fin n) :
    |dotProduct (A j) x[k] + b j| ≤ |dotProduct (A (i k x[k])) x[k] + b (i k x[k])| :=
  h k j

end

end
