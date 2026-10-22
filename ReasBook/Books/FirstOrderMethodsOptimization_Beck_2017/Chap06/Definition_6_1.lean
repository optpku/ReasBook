/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

variable {E : Type u} [NormedAddCommGroup E]

/-- The proximal objective at `x` is the function `u ↦ f u + (1 / 2) * ‖u - x‖^2`. -/
def proximal_objective (f : E → EReal) (x : E) : E → EReal :=
  fun u ↦ f u + ((((1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ)) : ℝ) : EReal)

-- Proof sketch: unfold `proximal_objective`; the displayed identity is exactly its defining
-- formula.
/-- Evaluating the proximal objective at `u` expands to `f u + (1 / 2) ‖u - x‖²`. -/
@[simp] theorem proximal_objective_apply (f : E → EReal) (x u : E) :
    proximal_objective f x u = f u + ((((1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ)) : ℝ) : EReal) :=
  rfl

/-- Definition 6.1: the proximal mapping of an extended-real-valued function sends `x` to the set
of minimizers of the proximal objective `u ↦ f u + (1 / 2) * ‖u - x‖^2`. This source-facing
set-valued formulation keeps the textbook `arg min` semantics without choosing a minimizer before
existence and uniqueness are established. -/
def prox (f : E → EReal) (x : E) : Set E :=
  {u | IsMinOn (proximal_objective f x) Set.univ u}

notation "prox[" f "]" => prox f

-- Proof sketch: unfold `prox`; membership in the resulting set is by definition the
-- statement that the candidate point is a global minimizer of the proximal objective.
/-- A point `u` belongs to `prox[f] x` exactly when it globally minimizes the proximal objective at
`x`. -/
@[simp]
theorem mem_proximal_mapping_iff {f : E → EReal} {x u : E} :
    u ∈ prox[f] x ↔ IsMinOn (proximal_objective f x) Set.univ u :=
  Iff.rfl

-- Proof sketch: rewrite proximal membership as a global minimizer statement for the two proximal
-- objectives. After cancelling the common additive constant, division by the positive scalar `a`
-- preserves the ordering and identifies the two minimizer relations.
/-- If two proximal objectives differ by multiplication by a positive scalar and addition of a
finite real constant, then they have the same proximal mapping. -/
theorem prox_eq_of_proximal_objective_eq_pos_mul_add_const
    {f g : E → EReal} {x y : E} {a c : ℝ} (ha : 0 < a)
    (hobj : ∀ u : E,
      proximal_objective f x u =
        ((a : ℝ) : EReal) * proximal_objective g y u + (c : EReal)) :
    prox[f] x = prox[g] y := by
  have hscale_pos : 0 < ((a : ℝ) : EReal) := by
    exact_mod_cast ha
  have hscale_top : ((a : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top _
  have hscale_bot : ((a : ℝ) : EReal) ≠ ⊥ := EReal.coe_ne_bot _
  have hscale_zero : ((a : ℝ) : EReal) ≠ 0 := by
    exact_mod_cast ha.ne'
  ext u
  rw [mem_proximal_mapping_iff, mem_proximal_mapping_iff, isMinOn_univ_iff, isMinOn_univ_iff]
  constructor
  · intro hu v
    have huv := hu v
    rw [hobj u, hobj v] at huv
    have huv' :
        (((a : ℝ) : EReal) * proximal_objective g y u) ≤
          (((a : ℝ) : EReal) * proximal_objective g y v) :=
      ((EReal.addLECancellable_coe c).add_le_add_iff_right).mp huv
    have huv'' :
        ((((a : ℝ) : EReal) * proximal_objective g y u) / ((a : ℝ) : EReal)) ≤
          ((((a : ℝ) : EReal) * proximal_objective g y v) / ((a : ℝ) : EReal)) :=
      EReal.monotone_div_right_of_nonneg hscale_pos.le huv'
    rw [mul_comm (((a : ℝ) : EReal)) (proximal_objective g y u),
      mul_comm (((a : ℝ) : EReal)) (proximal_objective g y v)] at huv''
    rw [← EReal.mul_div_right, ← EReal.mul_div_right,
      EReal.div_mul_cancel hscale_bot hscale_top hscale_zero,
      EReal.div_mul_cancel hscale_bot hscale_top hscale_zero] at huv''
    exact huv''
  · intro hu v
    have huv' :
        (((a : ℝ) : EReal) * proximal_objective g y u) ≤
          (((a : ℝ) : EReal) * proximal_objective g y v) :=
      mul_le_mul_of_nonneg_left (hu v) hscale_pos.le
    have huv := ((EReal.addLECancellable_coe c).add_le_add_iff_right).mpr huv'
    calc
      proximal_objective f x u = (((a : ℝ) : EReal) * proximal_objective g y u) + (c : EReal) :=
        hobj u
      _ ≤ (((a : ℝ) : EReal) * proximal_objective g y v) + (c : EReal) := huv
      _ = proximal_objective f x v := (hobj v).symm

-- Proof sketch: apply the owner-level positive-affine invariance theorem above with scale `a = 1`
-- and the same base point on both sides.
/-- Adding a finite real constant to an extended-real-valued objective does not change its
proximal mapping. -/
@[simp] theorem prox_add_const (f : E → EReal) (c : ℝ) :
    prox[fun y : E ↦ f y + (c : EReal)] = prox[f] := by
  funext x
  have hobjective (u : E) :
      proximal_objective (fun y : E ↦ f y + (c : EReal)) x u =
        ((1 : ℝ) : EReal) * proximal_objective f x u + (c : EReal) := by
    simp [proximal_objective, add_assoc, add_left_comm, add_comm]
  simpa using prox_eq_of_proximal_objective_eq_pos_mul_add_const zero_lt_one hobjective

end
