/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Algorithm_12_2
import FirstOrderMethodsOptimization_Beck_2017.Chap11.Definition_11_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

noncomputable section

universe u

section

variable {ι : Type*}
variable {E : Type u}
variable [NormedAddCommGroup E] [Module ℝ E]

/- Algorithm 12.15 is `source-facing`: it gives the block-coordinate primal-representation form of
the dual block proximal-gradient method.

Domain sampling against the chapter owners shows that the correct owner chain is:
- `dual_proximal_gradient_primal_y_step` from Algorithm 12.2 for the active-block primal
  proximal update;
- `dual_proximal_gradient_primal_x_argmax` from Algorithm 12.2 for the primal argmax condition,
  specialized here to `LinearMap.id` and the aggregated block sum `∑ j, y j`;
- `block_coordinate_update` from Definition 11.4 for re-inserting the updated active block into the
  full block vector.

Primitive data are therefore only the selected block, the current primal point, and the current
block vector; the blockwise affine/proximal formula is derived through the canonical one-block
owner rather than duplicated locally. -/

/-- The admissible block-vector updates in step (c) of the dual block proximal-gradient method:
only the selected block `i` is replaced, and its new value is obtained from the Chapter 12 primal
proximal `y`-step specialized to the identity map and the reciprocal stepsize `σ⁻¹`. -/
def dual_block_proximal_gradient_primal_y_step
    (g : ι → E → EReal) (σ : PosReal) (x : E) (y : ι → E) (i : ι) :
    Set (ι → E) :=
  (fun yiNext ↦ block_coordinate_update y i (yiNext - y i)) ''
    dual_proximal_gradient_primal_y_step (g i) LinearMap.id x (y i) σ⁻¹

-- Proof sketch: unfold `dual_block_proximal_gradient_primal_y_step`; membership is equivalent to
-- choosing an updated active block from the canonical one-block primal owner and then reinserting
-- it into the full block vector through `block_coordinate_update`.
/-- Membership in `dual_block_proximal_gradient_primal_y_step g σ x y i` is equivalent to choosing
an updated active block `y_i^+` from the canonical one-block primal owner and replacing only the
selected coordinate `i`. -/
theorem mem_dual_block_proximal_gradient_primal_y_step_iff
    {g : ι → E → EReal} {σ : PosReal} {x : E} {y yNext : ι → E} {i : ι} :
    yNext ∈ dual_block_proximal_gradient_primal_y_step g σ x y i ↔
      ∃ yiNext ∈ dual_proximal_gradient_primal_y_step (g i) LinearMap.id x (y i) σ⁻¹,
        block_coordinate_update y i (yiNext - y i) = yNext := by
  rfl

end

section

variable {ι : Type*} [Fintype ι]
variable {E : Type u}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Algorithm 12.15: given an initialization `y⁰ = y0` in the finite block family `ι → E` and a
block-selection rule `block : ℕ → ι`, a pair of sequences `(x^k, y^k)` follows the dual block
proximal-gradient method in primal representation when every iteration `k` satisfies
`x^k ∈ argmax_x {⟪x, ∑ j, y_j^k⟫ - f(x)}` and the next block vector `y^(k+1)` is obtained by
updating only the selected coordinate `block k` through the proximal rule
`y_i^k - σ x^k + σ prox_{g_i / σ}(x^k - y_i^k / σ)`. -/
class is_dual_block_proximal_gradient_primal_trajectory
    (f : E → EReal) (g : ι → E → EReal) (σ : PosReal) (block : ℕ → ι)
    (y0 : ι → E) (x : ℕ → E) (y : ℕ → ι → E) : Prop where
  /-- The trajectory starts from the prescribed initialization `y⁰ = y0`. -/
  zero : y 0 = y0
  /-- At each iteration, the primal point lies in the aggregated argmax set and the next block
  vector is obtained by the selected one-block proximal update. -/
  step :
    ∀ k : ℕ,
      x k ∈ dual_proximal_gradient_primal_x_argmax f LinearMap.id (∑ j, y k j) ∧
        y (k + 1) ∈ dual_block_proximal_gradient_primal_y_step g σ (x k) (y k) (block k)

/-- Coercion from an Algorithm 12.15 primal trajectory to its primitive per-iteration update
clause. -/
instance is_dual_block_proximal_gradient_primal_trajectory.instCoeFun
    (f : E → EReal) (g : ι → E → EReal) (σ : PosReal) (block : ℕ → ι)
    (y0 : ι → E) (x : ℕ → E) (y : ℕ → ι → E) :
    CoeFun
      (is_dual_block_proximal_gradient_primal_trajectory f g σ block y0 x y)
      (fun _ ↦
        ∀ k : ℕ,
          x k ∈ dual_proximal_gradient_primal_x_argmax f LinearMap.id (∑ j, y k j) ∧
            y (k + 1) ∈ dual_block_proximal_gradient_primal_y_step g σ (x k) (y k) (block k))
    where
  coe h := h.step

-- Proof sketch: extract the initialization equation from the first conjunct of
-- `is_dual_block_proximal_gradient_primal_trajectory`.
/-- A dual block proximal-gradient primal trajectory starts from the prescribed initialization
`y⁰ = y0`. -/
theorem is_dual_block_proximal_gradient_primal_trajectory_zero
    {f : E → EReal} {g : ι → E → EReal} {σ : PosReal} {block : ℕ → ι}
    {y0 : ι → E} {x : ℕ → E} {y : ℕ → ι → E}
    (h : is_dual_block_proximal_gradient_primal_trajectory f g σ block y0 x y) :
    y 0 = y0 :=
  h.1

-- Proof sketch: specialize the defining universal clause of
-- `is_dual_block_proximal_gradient_primal_trajectory` at the iteration index `k`.
/-- At every iteration `k`, a dual block proximal-gradient primal trajectory chooses `x^k` from
the aggregated argmax set and updates only the selected block `block k` through the corresponding
one-block proximal step. -/
theorem is_dual_block_proximal_gradient_primal_trajectory_step
    {f : E → EReal} {g : ι → E → EReal} {σ : PosReal} {block : ℕ → ι}
    {y0 : ι → E} {x : ℕ → E} {y : ℕ → ι → E}
    (h : is_dual_block_proximal_gradient_primal_trajectory f g σ block y0 x y) (k : ℕ) :
    x k ∈ dual_proximal_gradient_primal_x_argmax f LinearMap.id (∑ j, y k j) ∧
      y (k + 1) ∈ dual_block_proximal_gradient_primal_y_step g σ (x k) (y k) (block k) :=
  h.2 k

end

section

variable {p : ℕ}

/-- The cyclic block-selection rule corresponding to the textbook choice
`i_k = (k mod p) + 1`, written in zero-based `Fin p` indexing. -/
def dual_block_proximal_gradient_cyclic_block_index (p : ℕ) [NeZero p] (k : ℕ) : Fin p :=
  ⟨k % p, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne p))⟩

-- Proof sketch: unfold `dual_block_proximal_gradient_cyclic_block_index`; the underlying natural
-- number of the chosen `Fin p` index is definitionally the remainder `k % p`.
/-- The cyclic block-selection rule evaluates to the remainder class of `k` modulo `p`. -/
theorem dual_block_proximal_gradient_cyclic_block_index_val
    (p : ℕ) [NeZero p] (k : ℕ) :
    (dual_block_proximal_gradient_cyclic_block_index p k : ℕ) = k % p :=
  rfl

end
