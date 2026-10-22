/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_1

-- Declarations for this item will be appended below by the statement pipeline.

universe v

section

variable {p : ℕ} {Ei : Fin p → Type v}

/- `prompt_add/` is absent in this workspace, so the statement design is sampled directly from the
nearby block-coordinate files. Algorithm 14.1 is `source-facing`: it gives a cyclic block
minimization rule with nonunique per-block argmin choices, so the public owner should be a
trajectory predicate rather than a recursively chosen update map.

Domain sampling against the local API identifies the relevant canonical owners:
- `effective_domain` for the initialization clause `x⁰ ∈ dom(F)`;
- `IsMinOn` for each blockwise argmin condition; and
- `Function.update` for inserting the current block candidate into the old iterate while keeping
  the later blocks fixed.

To preserve the Gauss-Seidel ordering of the algorithm, the block objective at index `i` is stated
against the mixed state that uses the already updated blocks from `x^(k+1)` before `i`, the
candidate value `x_i`, and the old blocks from `x^k` after `i`. -/

/-- The mixed block state used in the `i`-th alternating-minimization subproblem: blocks strictly
before `i` come from the next outer iterate `xNext`, the `i`-th block is the candidate value
`xi`, and blocks from `i + 1` onward remain those of the current iterate `xk`. -/
def alternating_minimization_partial_state
    (xk xNext : (i : Fin p) → Ei i) (i : Fin p) (xi : Ei i) : (j : Fin p) → Ei j :=
  fun j ↦ if j.1 < i.1 then xNext j else Function.update xk i xi j

-- Proof sketch: unfold `alternating_minimization_partial_state`; at the updated block `i`, the
-- inequality `i.1 < i.1` is false, so the value is read from `Function.update xk i xi`, which is
-- definitionally `xi`.
/-- At the active block, `alternating_minimization_partial_state xk xNext i xi` takes the candidate
value `xi`. -/
@[simp] theorem alternating_minimization_partial_state_apply_self
    (xk xNext : (i : Fin p) → Ei i) (i : Fin p) (xi : Ei i) :
    alternating_minimization_partial_state xk xNext i xi i = xi := by
  -- Unfold the mixed state at the active block; the strict inequality branch is impossible.
  simp [alternating_minimization_partial_state]

-- Proof sketch: with `xNext = xk`, the mixed state
-- `alternating_minimization_partial_state xk xk i xi` agrees pointwise with
-- `Function.update xk i xi`.
/-- In the fixed-base case `xNext = xk`, the Chapter 14 mixed state is exactly the block update
`Function.update xk i xi`. -/
@[simp] theorem alternating_minimization_partial_state_base
    (xk : (i : Fin p) → Ei i) (i : Fin p) (xi : Ei i) :
    alternating_minimization_partial_state xk xk i xi = Function.update xk i xi := by
  funext j
  by_cases hji : j = i
  · subst hji
    simp [alternating_minimization_partial_state]
  · simp [alternating_minimization_partial_state, hji]

/-- The `i`-th block objective of alternating minimization obtained by freezing the earlier blocks
at their updated values from `xNext` and the later blocks at their old values from `xk`. -/
def alternating_minimization_block_objective
    (F : ((i : Fin p) → Ei i) → EReal)
    (xk xNext : (i : Fin p) → Ei i) (i : Fin p) : Ei i → EReal :=
  fun xi ↦ F (alternating_minimization_partial_state xk xNext i xi)

-- Proof sketch: unfold `alternating_minimization_block_objective`; evaluation at `xi` is exactly
-- `F` applied to the mixed block state used in the `i`-th subproblem.
/-- Evaluating the `i`-th alternating-minimization block objective at `xi` applies `F` to the
corresponding mixed block state. -/
@[simp] theorem alternating_minimization_block_objective_apply
    (F : ((i : Fin p) → Ei i) → EReal)
    (xk xNext : (i : Fin p) → Ei i) (i : Fin p) (xi : Ei i) :
    alternating_minimization_block_objective F xk xNext i xi =
      F (alternating_minimization_partial_state xk xNext i xi) := by
  -- Evaluating the block objective is just applying its defining lambda term.
  rfl

-- Proof sketch: with `xNext = xk`, the mixed state
-- `alternating_minimization_partial_state xk xk i xi` agrees pointwise with
-- `Function.update xk i xi`.
/-- In the fixed-base case `xNext = xk`, the Chapter 14 one-block objective evaluates by updating
only the active block `i`. -/
@[simp] theorem alternating_minimization_block_objective_base_apply
    (F : ((i : Fin p) → Ei i) → EReal) (xk : (i : Fin p) → Ei i) (i : Fin p) (xi : Ei i) :
    alternating_minimization_block_objective F xk xk i xi = F (Function.update xk i xi) := by
  rw [alternating_minimization_block_objective_apply, alternating_minimization_partial_state_base]

/-- Algorithm 14.1: a sequence of block vectors `x^k` follows the alternating minimization method
for `F` when `x^0 ∈ dom(F)` and, for every outer iteration `k` and every zero-based block
`i : Fin p` corresponding to textbook block `i + 1`, the updated block `x_i^(k+1)` minimizes the
mixed subproblem
`xi ↦ F(x_1^(k+1), ..., x_(i-1)^(k+1), xi, x_(i+1)^k, ..., x_p^k)`. -/
class is_alternating_minimization_trajectory
    (F : ((i : Fin p) → Ei i) → EReal) (x : ℕ → (i : Fin p) → Ei i) : Prop where
  zero_mem_effective_domain : x 0 ∈ effective_domain F
  step_isMinOn (k : ℕ) (i : Fin p) :
    IsMinOn
      (alternating_minimization_block_objective F (x k) (x (k + 1)) i)
      Set.univ
      (x (k + 1) i)

/-- An alternating-minimization trajectory canonically yields the effective-domain fact for its
initial iterate. -/
instance alternating_minimization_trajectory_zero_fact
    {F : ((i : Fin p) → Ei i) → EReal} {x : ℕ → (i : Fin p) → Ei i}
    [h : is_alternating_minimization_trajectory F x] :
    Fact (x 0 ∈ effective_domain F) where
  out := h.zero_mem_effective_domain

-- Proof sketch: extract the initialization clause from the first conjunct of
-- `is_alternating_minimization_trajectory F x`.
/-- An alternating-minimization trajectory starts from a point of `dom(F)`. -/
@[simp] theorem is_alternating_minimization_trajectory_zero
    {F : ((i : Fin p) → Ei i) → EReal} {x : ℕ → (i : Fin p) → Ei i}
    (h : is_alternating_minimization_trajectory F x) :
    x 0 ∈ effective_domain F := by
  -- This is the initialization field stored in the trajectory predicate.
  exact h.zero_mem_effective_domain

-- Proof sketch: specialize the defining universal blockwise optimality clause of
-- `is_alternating_minimization_trajectory F x` at the chosen outer iteration `k` and block `i`.
/-- At each outer iteration and each block, an alternating-minimization trajectory chooses the
next block value from the argmin set of the corresponding mixed block objective. -/
theorem is_alternating_minimization_trajectory_step
    {F : ((i : Fin p) → Ei i) → EReal} {x : ℕ → (i : Fin p) → Ei i}
    (h : is_alternating_minimization_trajectory F x) (k : ℕ) (i : Fin p) :
    IsMinOn
      (alternating_minimization_block_objective F (x k) (x (k + 1)) i)
      Set.univ
      (x (k + 1) i) := by
  -- This is the blockwise minimization field of the trajectory predicate.
  exact h.step_isMinOn k i

end
