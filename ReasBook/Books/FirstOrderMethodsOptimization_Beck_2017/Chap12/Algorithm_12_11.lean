/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap10.Algorithm_10_13
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Algorithm_12_10

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

variable (n : ℕ)

/- Algorithm 12.11 is `source-facing` in the subsection on one-dimensional total variation
denoising.

Domain sampling against the nearby project owners identifies:
- `one_dimensional_total_variation_dpg_primal_point` and
  `one_dimensional_total_variation_dpg_dual_update` from Algorithm 12.10 as the canonical owners
  of the shared step-(a) / step-(b) primitives for one-dimensional TV denoising;
- `fista_momentum_sequence` and `fista_momentum_update` from Algorithm 10.13 as the canonical
  Chapter 10 owners of the scalar recurrence `t_(k+1) = (1 + √(1 + 4 t_k^2)) / 2`.

This separates the API into:
- `source-facing`: the named iterate families `u^k`, `y^k`, and `w^k`;
- `bridge/view`: the recursive iterate state storing the current dual iterate, extrapolated
  iterate, and momentum value needed for the exact FDPG step-(d) update.

The scalar sequence `t_k` itself is already owned upstream by `fista_momentum_sequence`, so this
file reuses that canonical owner directly on theorem surfaces instead of introducing a parallel
public momentum definition carrying the TV problem-data binders. Matching Algorithm 12.10, the
source-facing iterate owners keep the canonical signal-length parameter `n : ℕ` and the positive
regularization parameter `lam : PosReal`. -/

private structure OneDimensionalTotalVariationFDPGState (n : ℕ) where
  yCur : EuclideanSpace ℝ (Fin (n - 1))
  wCur : EuclideanSpace ℝ (Fin (n - 1))
  tCur : ℝ

private def one_dimensional_total_variation_fdpg_initial_state
    (y0 : EuclideanSpace ℝ (Fin (n - 1))) : OneDimensionalTotalVariationFDPGState n :=
  { yCur := y0
    wCur := y0
    tCur := fista_momentum_sequence 0 }

private def one_dimensional_total_variation_fdpg_state_update
    (d : EuclideanSpace ℝ (Fin n)) (lam : PosReal) (k : ℕ)
    (state : OneDimensionalTotalVariationFDPGState n) :
    OneDimensionalTotalVariationFDPGState n :=
  let u := one_dimensional_total_variation_dpg_primal_point n d state.wCur
  let yNext := one_dimensional_total_variation_dpg_dual_update n lam u state.wCur
  let tNext := fista_momentum_sequence (k + 1)
  { yCur := yNext
    wCur := yNext + ((fista_momentum_sequence k - 1) / tNext) • (yNext - state.yCur)
    tCur := tNext }

private def one_dimensional_total_variation_fdpg_state
    (d : EuclideanSpace ℝ (Fin n)) (lam : PosReal)
    (y0 : EuclideanSpace ℝ (Fin (n - 1))) :
    ℕ → OneDimensionalTotalVariationFDPGState n
  | 0 => one_dimensional_total_variation_fdpg_initial_state n y0
  | k + 1 =>
      one_dimensional_total_variation_fdpg_state_update n d lam k
        (one_dimensional_total_variation_fdpg_state d lam y0 k)

/-- Algorithm 12.11: for the one-dimensional total variation denoising problem
`min_x { (1 / 2) ‖x - d‖_2^2 + λ ‖D x‖_1 }`, with signal length `n`, positive regularization
parameter `λ` encoded by `lam : PosReal`, and initialization `w⁰ = y⁰ = y0 ∈ ℝ^(n-1)`,
the iterate families below generate the FDPG recursion with
`u^k = Dᵀ w^k + d`,
`y^(k+1) = w^k - (1 / 4) D u^k + (1 / 4) T_[4 λ] (D u^k - 4 w^k)`,
`t_(k+1) = (1 + √(1 + 4 t_k^2)) / 2`,
and
`w^(k+1) = y^(k+1) + ((t_k - 1) / t_(k+1)) (y^(k+1) - y^k)`. -/
def one_dimensional_total_variation_fdpg_y
    (d : EuclideanSpace ℝ (Fin n)) (lam : PosReal)
    (y0 : EuclideanSpace ℝ (Fin (n - 1))) :
    ℕ → EuclideanSpace ℝ (Fin (n - 1)) :=
  fun k ↦ (one_dimensional_total_variation_fdpg_state n d lam y0 k).yCur

/-- The one-dimensional TV FDPG extrapolated sequence `w^k`. -/
def one_dimensional_total_variation_fdpg_w
    (d : EuclideanSpace ℝ (Fin n)) (lam : PosReal)
    (y0 : EuclideanSpace ℝ (Fin (n - 1))) :
    ℕ → EuclideanSpace ℝ (Fin (n - 1)) :=
  fun k ↦ (one_dimensional_total_variation_fdpg_state n d lam y0 k).wCur

/-- The auxiliary primal sequence `u^k = Dᵀ w^k + d` derived from the one-dimensional TV FDPG
iterates. -/
def one_dimensional_total_variation_fdpg_u
    (d : EuclideanSpace ℝ (Fin n)) (lam : PosReal)
    (y0 : EuclideanSpace ℝ (Fin (n - 1))) :
    ℕ → EuclideanSpace ℝ (Fin n) :=
  fun k ↦
    one_dimensional_total_variation_dpg_primal_point n d
      (one_dimensional_total_variation_fdpg_w n d lam y0 k)

section

/-- The one-dimensional TV FDPG dual sequence starts from the prescribed initialization
`y⁰ = y0`. -/
@[simp] theorem one_dimensional_total_variation_fdpg_y_zero
    (d : EuclideanSpace ℝ (Fin n)) (lam : PosReal)
    (y0 : EuclideanSpace ℝ (Fin (n - 1))) :
    one_dimensional_total_variation_fdpg_y n d lam y0 0 = y0 :=
  rfl

/-- The one-dimensional TV FDPG extrapolated sequence starts from `w⁰ = y⁰ = y0`. -/
@[simp] theorem one_dimensional_total_variation_fdpg_w_zero
    (d : EuclideanSpace ℝ (Fin n)) (lam : PosReal)
    (y0 : EuclideanSpace ℝ (Fin (n - 1))) :
    one_dimensional_total_variation_fdpg_w n d lam y0 0 = y0 :=
  rfl

/-- At every iteration `k`, the auxiliary point satisfies the step-(a) formula
`u^k = Dᵀ w^k + d`. -/
theorem one_dimensional_total_variation_fdpg_u_eq
    (d : EuclideanSpace ℝ (Fin n)) (lam : PosReal)
    (y0 : EuclideanSpace ℝ (Fin (n - 1))) (k : ℕ) :
    one_dimensional_total_variation_fdpg_u n d lam y0 k =
      Dᵀ[n] (one_dimensional_total_variation_fdpg_w n d lam y0 k) + d :=
  rfl

/-- At every iteration `k`, the next dual iterate is obtained from the shared one-dimensional TV
DPG dual-update owner evaluated at `u^k` and `w^k`. -/
theorem one_dimensional_total_variation_fdpg_y_succ
    (d : EuclideanSpace ℝ (Fin n)) (lam : PosReal)
    (y0 : EuclideanSpace ℝ (Fin (n - 1))) (k : ℕ) :
    one_dimensional_total_variation_fdpg_y n d lam y0 (k + 1) =
      one_dimensional_total_variation_dpg_dual_update n lam
        (one_dimensional_total_variation_fdpg_u n d lam y0 k)
        (one_dimensional_total_variation_fdpg_w n d lam y0 k) :=
  rfl

/-- At every iteration `k`, the extrapolated successor satisfies the textbook FDPG step-(d)
formula with the canonical FISTA momentum sequence. -/
theorem one_dimensional_total_variation_fdpg_w_succ
    (d : EuclideanSpace ℝ (Fin n)) (lam : PosReal)
    (y0 : EuclideanSpace ℝ (Fin (n - 1))) (k : ℕ) :
    one_dimensional_total_variation_fdpg_w n d lam y0 (k + 1) =
      one_dimensional_total_variation_fdpg_y n d lam y0 (k + 1) +
        ((fista_momentum_sequence k - 1) / fista_momentum_sequence (k + 1)) •
          (one_dimensional_total_variation_fdpg_y n d lam y0 (k + 1) -
            one_dimensional_total_variation_fdpg_y n d lam y0 k) :=
  rfl

end

end
