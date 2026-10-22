/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_3
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Definition_12_19

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped SoftThreshold

section

variable (n : ℕ)

local notation "En" => EuclideanSpace ℝ (Fin n)
local notation "Em" => EuclideanSpace ℝ (Fin (n - 1))

/- Algorithm 12.10 is `source-facing` in the subsection on one-dimensional total variation
denoising.

Domain sampling against the nearby project owners identifies:
- `T_[·]` from Chapter 6 Definition 6.3 as the canonical owner for the vector soft-thresholding
  map in the dual update;
- the standard adjacent-index surface `Fin.castSucc` / `Fin.succ` together with `D[·]` and
  `Dᵀ[·]` from Chapter 12 Definition 12.19 as the source-facing owner of the one-dimensional TV
  difference operator API;
- the explicit recursion pattern from the other Chapter 12 algorithm files as the right
  `source-facing` owner shape for the iterates themselves.

This splits the API into:
- `bridge/view`: the explicit step-(a)/(b) maps, with the one-dimensional TV difference
  operator API reused from Definition 12.19;
- `source-facing`: the DPG iterate families for Algorithm 12.10, reusing the same signal-length
  owner parameter `n : ℕ` as the shared step-(a)/(b) maps and the positive regularization
  parameter `lam : PosReal`. -/

/-- The step-(a) primal point `x = Dᵀ y + d` attached to the current dual iterate `y`. -/
def one_dimensional_total_variation_dpg_primal_point
    (d : En) (y : Em) :
    En :=
  Dᵀ[n] y + d

/-- Expanding the primal point yields the textbook step-(a) formula `x = Dᵀ y + d`. -/
@[simp] theorem one_dimensional_total_variation_dpg_primal_point_eq
    (d : En) (y : Em) :
    one_dimensional_total_variation_dpg_primal_point n d y =
      Dᵀ[n] y + d :=
  rfl

/-- The step-(b) dual update
`y - (1 / 4) D x + (1 / 4) T_[4 λ](D x - 4 y)` used in the DPG method for one-dimensional total
variation denoising. -/
def one_dimensional_total_variation_dpg_dual_update
    (lam : PosReal) (x : En) (y : Em) :
    Em :=
  y - (1 / 4 : ℝ) • D[n] x +
    (1 / 4 : ℝ) •
      T_[4 * (lam : ℝ)] (D[n] x - (4 : ℝ) • y)

/-- Expanding the dual update yields the textbook step-(b) formula
`y - (1 / 4) D x + (1 / 4) T_[4 λ](D x - 4 y)`. -/
@[simp] theorem one_dimensional_total_variation_dpg_dual_update_eq
    (lam : PosReal) (x : En) (y : Em) :
    one_dimensional_total_variation_dpg_dual_update n lam x y =
      y - (1 / 4 : ℝ) • D[n] x +
        (1 / 4 : ℝ) •
          T_[4 * (lam : ℝ)] (D[n] x - (4 : ℝ) • y) :=
  rfl

end

section

variable (n : ℕ) (d : EuclideanSpace ℝ (Fin n)) (lam : PosReal)
variable (y0 : EuclideanSpace ℝ (Fin (n - 1)))

/-- Algorithm 12.10: for the one-dimensional total variation denoising problem
`min_x {(1 / 2) ‖x - d‖₂² + λ ‖D x‖₁}`, with signal length `n`, positive regularization
parameter `λ` encoded by `lam : PosReal`, and an initial dual point `y⁰ ∈ ℝ^(n-1)`, this
recursive sequence generates the DPG dual iterates by
`x^k = Dᵀ y^k + d` and
`y^(k+1) = y^k - (1 / 4) D x^k + (1 / 4) T_[4 λ](D x^k - 4 y^k)`. -/
def one_dimensional_total_variation_dpg :
    ℕ → EuclideanSpace ℝ (Fin (n - 1))
  | 0 => y0
  | k + 1 =>
      let yk := one_dimensional_total_variation_dpg k
      let xk := one_dimensional_total_variation_dpg_primal_point n d yk
      one_dimensional_total_variation_dpg_dual_update n lam xk yk

/-- The primal sequence `x^k = Dᵀ y^k + d` derived from the DPG dual iterates. -/
def one_dimensional_total_variation_dpg_x :
    ℕ → EuclideanSpace ℝ (Fin n) :=
  fun k ↦
    one_dimensional_total_variation_dpg_primal_point n d
      (one_dimensional_total_variation_dpg n d lam y0 k)

section

local notation "y[" k "]" => one_dimensional_total_variation_dpg n d lam y0 k
local notation "x[" k "]" => one_dimensional_total_variation_dpg_x n d lam y0 k

/-- The DPG dual sequence starts from the prescribed initialization `y⁰ = y0`. -/
@[simp] theorem one_dimensional_total_variation_dpg_zero :
    y[0] = y0 :=
  rfl

/-- At every iteration `k`, the derived primal point satisfies the step-(a) formula
`x^k = Dᵀ y^k + d`. -/
theorem one_dimensional_total_variation_dpg_x_eq (k : ℕ) :
    x[k] = Dᵀ[n] (y[k]) + d :=
  rfl

/-- At every iteration `k`, the successor dual iterate satisfies the step-(b) update formula of
Algorithm 12.10. -/
theorem one_dimensional_total_variation_dpg_succ (k : ℕ) :
    y[k + 1] = one_dimensional_total_variation_dpg_dual_update n lam x[k] y[k] := by
  simp [one_dimensional_total_variation_dpg, one_dimensional_total_variation_dpg_x]

end

end
