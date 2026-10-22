/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Algorithm_12_1
import FirstOrderMethodsOptimization_Beck_2017.Chap11.Definition_11_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped BigOperators

noncomputable section

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Algorithm 12.14 is `core/canonical` for the block-coordinate dual representation: it isolates
the dual iterate sequence `y^k` and its one-block update set, while the later primal
representation of Algorithm 12.15 packages the auxiliary argmax sequence `x^k`.

Domain sampling against the existing project owners gives:
- `dual_based_proximal_gradient_dual_step` from Algorithm 12.1 as the canonical owner for the
  one-block dual proximal update;
- `block_coordinate_update` from Definition 11.4 as the canonical owner for replacing a single
  block in a tuple `Fin p → E`;
- a trajectory predicate, rather than a chosen recursive sequence, as the natural statement-level
  owner because the source allows an arbitrary block-choice sequence `i_k` and the proximal step is
  represented set-valuedly in the project API.

The gradient term is kept explicit as a map `grad_f_conj : E → E`, representing the textbook
gradient `∇ f*`. -/

/-- The one-block dual update set for the dual block proximal-gradient method: at block `i`, it
replaces `y i` by a proximal point of `σ G_i` at
`y i - σ grad_f_conj (∑ j, y j)` and leaves the remaining blocks unchanged. -/
def dual_block_proximal_gradient_dual_step
    {p : ℕ} (G : Fin p → E → EReal) (grad_f_conj : E → E) (σ : PosReal)
    (i : Fin p) (y : Fin p → E) : Set (Fin p → E) :=
  (fun yiNext ↦ block_coordinate_update y i (yiNext - y i)) ''
    dual_based_proximal_gradient_dual_step
      (G i)
      (fun _ : E ↦ grad_f_conj (∑ j : Fin p, y j))
      σ⁻¹
      (y i)

-- Proof sketch: unfold `dual_block_proximal_gradient_dual_step`; membership in the image of
-- `fun yiNext ↦ block_coordinate_update y i (yiNext - y i)` is equivalent to changing only the
-- `i`th block, with the new value lying
-- in the proximal set of `σ G_i` at the forward-gradient point
-- `y i - σ grad_f_conj (∑ j, y j)`.
/-- A block vector belongs to the one-step dual block update set exactly when its selected block
is a proximal point of `σ G_i` at the forward-gradient point and every nonselected block is
unchanged. -/
theorem mem_dual_block_proximal_gradient_dual_step_iff
    {p : ℕ} {G : Fin p → E → EReal} {grad_f_conj : E → E} {σ : PosReal}
    {i : Fin p} {y yNext : Fin p → E} :
    yNext ∈ dual_block_proximal_gradient_dual_step G grad_f_conj σ i y ↔
      yNext i ∈ prox[(((σ : ℝ) : EReal) • G i)]
        (y i - (σ : ℝ) • grad_f_conj (∑ j : Fin p, y j)) ∧
        ∀ j : Fin p, j ≠ i → yNext j = y j := by
  have hσ0 : (σ : ℝ) ≠ 0 := by
    exact ne_of_gt σ.2
  have hσ : ((1 / (σ⁻¹ : PosReal) : PosReal) : ℝ) = (σ : ℝ) := by
    change (1 : ℝ) / ((σ : ℝ)⁻¹) = (σ : ℝ)
    field_simp [hσ0]
  constructor
  · rintro ⟨yiNext, hyiNext, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [mem_dual_based_proximal_gradient_dual_step_iff] at hyiNext
      simpa [block_coordinate_update, hσ, sub_eq_add_neg]
        using hyiNext
    · intro j hj
      simp [block_coordinate_update_apply_ne, hj]
  · rintro ⟨hyiNext, hyRest⟩
    refine ⟨yNext i, ?_, ?_⟩
    · rw [mem_dual_based_proximal_gradient_dual_step_iff]
      simpa [hσ]
        using hyiNext
    · ext j
      by_cases hj : j = i
      · subst hj
        simp [block_coordinate_update, sub_eq_add_neg]
      · simp [block_coordinate_update_apply_ne, hj, hyRest j hj]

/-- Algorithm 12.14: given an initialization `y⁰ = y0 ∈ E^p`, a positive parameter `σ`, and a
block-choice sequence `i_k ∈ {1, …, p}`, a sequence `y` follows the dual block proximal-gradient
method in dual representation when `y 0 = y0` and every successor iterate updates only the chosen
block `i_k` by a proximal step of `σ G_(i_k)` at
`y_(i_k)^k - σ ∇ f*(∑ j, y_j^k)`, with `grad_f_conj` representing `∇ f*`. -/
class is_dual_block_proximal_gradient_dual_trajectory
    {p : ℕ} (G : Fin p → E → EReal) (grad_f_conj : E → E) (σ : PosReal)
    (block_choice : ℕ → Fin p) (y0 : Fin p → E) (y : ℕ → Fin p → E) : Prop where
  /-- The trajectory starts from the prescribed initialization `y⁰ = y0`. -/
  zero : y 0 = y0
  /-- At each iteration, the next block vector is obtained by the selected one-block dual
  proximal update. -/
  step :
    ∀ k : ℕ,
      y (k + 1) ∈ dual_block_proximal_gradient_dual_step G grad_f_conj σ (block_choice k) (y k)

/-- Coercion from an Algorithm 12.14 dual trajectory to its primitive per-iteration update
clause. -/
instance is_dual_block_proximal_gradient_dual_trajectory.instCoeFun
    {p : ℕ} (G : Fin p → E → EReal) (grad_f_conj : E → E) (σ : PosReal)
    (block_choice : ℕ → Fin p) (y0 : Fin p → E) (y : ℕ → Fin p → E) :
    CoeFun
      (is_dual_block_proximal_gradient_dual_trajectory G grad_f_conj σ block_choice y0 y)
      (fun _ ↦
        ∀ k : ℕ,
          y (k + 1) ∈
            dual_block_proximal_gradient_dual_step G grad_f_conj σ (block_choice k) (y k))
    where
  coe h := h.step

-- Proof sketch: extract the initialization equation from the first conjunct of
-- `is_dual_block_proximal_gradient_dual_trajectory`.
/-- A dual block proximal-gradient dual trajectory starts from the prescribed initialization
`y⁰ = y0`. -/
theorem is_dual_block_proximal_gradient_dual_trajectory_zero
    {p : ℕ} {G : Fin p → E → EReal} {grad_f_conj : E → E} {σ : PosReal}
    {block_choice : ℕ → Fin p} {y0 : Fin p → E} {y : ℕ → Fin p → E}
    (h : is_dual_block_proximal_gradient_dual_trajectory
      G grad_f_conj σ block_choice y0 y) :
    y 0 = y0 :=
  h.zero

-- Proof sketch: specialize the defining universal clause of
-- `is_dual_block_proximal_gradient_dual_trajectory` at the iteration index `k`.
/-- At each iteration `k`, a dual block proximal-gradient trajectory updates `y^(k+1)` through the
one-block proximal step set determined by the chosen index `i_k = block_choice k`. -/
theorem is_dual_block_proximal_gradient_dual_trajectory_step
    {p : ℕ} {G : Fin p → E → EReal} {grad_f_conj : E → E} {σ : PosReal}
    {block_choice : ℕ → Fin p} {y0 : Fin p → E} {y : ℕ → Fin p → E}
    (h : is_dual_block_proximal_gradient_dual_trajectory
      G grad_f_conj σ block_choice y0 y)
    (k : ℕ) :
    y (k + 1) ∈ dual_block_proximal_gradient_dual_step G grad_f_conj σ (block_choice k) (y k) :=
  h.step k

end
