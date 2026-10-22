/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap11.Algorithm_11_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe v

open scoped Gradient

section

variable {p : ℕ} {Ei : Fin p → Type v}
variable [∀ i, NormedAddCommGroup (Ei i)] [∀ i, InnerProductSpace ℝ (Ei i)]
variable [∀ i, ProperSpace (Ei i)]

variable {f : ((i : Fin p) → Ei i) → EReal} {g : (i : Fin p) → Ei i → EReal}
variable {block_gradient : (i : Fin p) → ((j : Fin p) → Ei j) → Ei i}
variable {XStar : Set ((i : Fin p) → Ei i)} {FOpt : ℝ}
variable {Lf : NNReal} {Li : (i : Fin p) → PosReal}

/- Algorithm 11.4 is `source-facing`. The owner abstractions are the raw ambient-product inner and
outer iterate sequences below; downstream files should derive domain-membership views from these
owners instead of redefining parallel subtype-valued iterate families. -/

/-- Starting from an outer iterate `x^k`, the inner stage `x^{k,i}` of the cyclic block
proximal-gradient method is obtained by successively applying the first `min i p` one-block
updates in cyclic order. -/
def cyclic_block_proximal_gradient_inner_iterate
    (hproblem : BlockProximalGradientAssumptions f g block_gradient XStar FOpt Lf Li)
    (xk : (i : Fin p) → Ei i) (i : ℕ) : (j : Fin p) → Ei j :=
  Fin.foldl (min i p)
    (fun x j ↦
      let i' : Fin p := Fin.castLE (Nat.min_le_right i p) j
      let xi' : Ei i' := hproblem.prox_point (Li i') i' x
      block_coordinate_update x i' (xi' - x i'))
    xk

/-- Algorithm 11.4: for an initial point `x^0 ∈ int(dom f)`, the cyclic block proximal gradient
method generates outer iterates `x^k` by setting `x^{k,0} = x^k`, then cycling through the block
updates `x^{k,i} = x^{k,i-1} + U_i(T_{L_i}(x^{k,i-1}) - x_i^{k,i-1})`, and finally defining
`x^{k+1} = x^{k,p}`. -/
def cyclic_block_proximal_gradient_method
    (hproblem : BlockProximalGradientAssumptions f g block_gradient XStar FOpt Lf Li)
    (x0 : interior (effective_domain f)) : ℕ → ((i : Fin p) → Ei i)
  | 0 => x0
  | k + 1 =>
      cyclic_block_proximal_gradient_inner_iterate hproblem
        (cyclic_block_proximal_gradient_method hproblem x0 k) p

section

variable (hproblem : BlockProximalGradientAssumptions f g block_gradient XStar FOpt Lf Li)
variable (x0 : interior (effective_domain f))

local notation "x[" k "]" =>
  cyclic_block_proximal_gradient_method hproblem x0 k

local notation "x[" k "," i "]" =>
  cyclic_block_proximal_gradient_inner_iterate hproblem x[k] i

-- Proof sketch: unfold `cyclic_block_proximal_gradient_inner_iterate`; the truncated fold length
-- is `min 0 p = 0`, so the fold returns the starting outer iterate unchanged.
/-- The initial inner stage of a CBPG cycle is the current outer iterate. -/
@[simp] theorem cyclic_block_proximal_gradient_inner_iterate_zero
    (xk : (i : Fin p) → Ei i) :
    cyclic_block_proximal_gradient_inner_iterate hproblem xk 0 = xk := by
  simp [cyclic_block_proximal_gradient_inner_iterate]

-- Proof sketch: rewrite `min (i + 1) p = i + 1` using `i < p`, then split the fold over the
-- first `i + 1` block indices into the prefix of length `i` followed by the last update in block
-- `⟨i, hi⟩`. Rewrite that last one-block update through
-- `block_proximal_gradient_update_eq_add_block_embedding` from Algorithm 11.3 so the public
-- statement uses the source-facing textbook form `x + 𝒰[i](...)`.
/-- Helper for Algorithm 11.4: the prefix fold occurring in the `(i + 1)`-stage decomposition is
exactly the stage-`i` CBPG inner iterate. -/
lemma cyclic_block_proximal_gradient_prefix_fold_eq_inner_iterate
    (xk : (i : Fin p) → Ei i) {i : ℕ} (hi : i < p) :
    Fin.foldl i
      (fun x j ↦
        let i' : Fin p := j.castSucc.castLE (Nat.succ_le_of_lt hi)
        let xi' : Ei i' := hproblem.prox_point (Li i') i' x
        block_coordinate_update x i' (xi' - x i'))
      xk =
    cyclic_block_proximal_gradient_inner_iterate hproblem xk i := by
  -- The prefix fold uses the same block indices as stage `i`, once the cast is normalized.
  calc
    Fin.foldl i
        (fun x j ↦
          let i' : Fin p := j.castSucc.castLE (Nat.succ_le_of_lt hi)
          let xi' : Ei i' := hproblem.prox_point (Li i') i' x
          block_coordinate_update x i' (xi' - x i'))
        xk =
      Fin.foldl i
        (fun x j ↦
          let i' : Fin p := Fin.castLE (Nat.le_of_lt hi) j
          let xi' : Ei i' := hproblem.prox_point (Li i') i' x
          block_coordinate_update x i' (xi' - x i'))
        xk := by
      -- The casted prefix indices are definitionally the same `Fin p` elements.
      congr with x j
    _ =
      cyclic_block_proximal_gradient_inner_iterate hproblem xk i := by
      -- Rewriting `min i p = i` recovers the owner definition of the stage-`i` inner iterate.
      simpa [cyclic_block_proximal_gradient_inner_iterate] using
        congrArg (fun F => F xk) <|
          (Fin.foldl_congr
            (w := Nat.min_eq_left (Nat.le_of_lt hi))
            (f := fun x j ↦
              let i' : Fin p := Fin.castLE (Nat.min_le_right i p) j
              let xi' : Ei i' := hproblem.prox_point (Li i') i' x
              block_coordinate_update x i' (xi' - x i'))).symm

/-- Helper for Algorithm 11.4: the final index selected by the `(i + 1)`-stage fold is the block
`⟨i, hi⟩`. -/
lemma cyclic_block_proximal_gradient_last_cast_eq
    {i : ℕ} (hi : i < p) :
    Fin.castLE (Nat.succ_le_of_lt hi) (Fin.last i) = (⟨i, hi⟩ : Fin p) := by
  -- The last element of `Fin (i + 1)` has value `i`, so the cast lands in the expected block.
  rfl

/-- Advancing one inner stage applies the one-block CBPG update in the next cyclic block, written
in the source-facing form `x + 𝒰[i](...)`. -/
theorem cyclic_block_proximal_gradient_inner_iterate_succ
    (xk : (i : Fin p) → Ei i) {i : ℕ} (hi : i < p) :
    let i' : Fin p := ⟨i, hi⟩
    let x' := cyclic_block_proximal_gradient_inner_iterate hproblem xk i
    let xi' : Ei i' := hproblem.prox_point (Li i') i' x'
    cyclic_block_proximal_gradient_inner_iterate hproblem xk (i + 1) =
      x' + 𝒰[i'] (xi' - x' i') := by
  have hsucc :
      cyclic_block_proximal_gradient_inner_iterate hproblem xk (i + 1) =
        Fin.foldl (i + 1)
          (fun x j ↦
            let i' : Fin p := Fin.castLE (Nat.succ_le_of_lt hi) j
            let xi' : Ei i' := hproblem.prox_point (Li i') i' x
            block_coordinate_update x i' (xi' - x i'))
          xk := by
    -- The truncation length is `i + 1` because the current block index satisfies `i < p`.
    simpa [cyclic_block_proximal_gradient_inner_iterate] using
      congrArg (fun F => F xk) <|
        (Fin.foldl_congr
          (w := Nat.min_eq_left (Nat.succ_le_of_lt hi))
          (f := fun x j ↦
            let i' : Fin p := Fin.castLE (Nat.min_le_right (i + 1) p) j
            let xi' : Ei i' := hproblem.prox_point (Li i') i' x
            block_coordinate_update x i' (xi' - x i')))
  -- Split the `(i + 1)`-stage fold into the stage-`i` prefix and the final block update.
  rw [hsucc, Fin.foldl_succ_last,
    cyclic_block_proximal_gradient_prefix_fold_eq_inner_iterate
      (hproblem := hproblem) (Li := Li) xk hi,
    cyclic_block_proximal_gradient_last_cast_eq (p := p) hi]
  -- The final fold step is exactly the source-facing block update `x + 𝒰[i'] (...)`.
  rfl

-- Proof sketch: unfold the recursive definition of `cyclic_block_proximal_gradient_method` at
-- `0`.
/-- The CBPG outer sequence starts at the prescribed initial point `x^0`. -/
@[simp] theorem cyclic_block_proximal_gradient_method_zero :
    x[0] = x0 :=
  rfl

-- Proof sketch: specialize `cyclic_block_proximal_gradient_inner_iterate_zero` to the outer
-- iterate `x[k]`.
/-- At each outer iteration `k`, the initial inner stage `x^{k,0}` agrees with the current outer
iterate `x^k`. -/
@[simp] theorem cyclic_block_proximal_gradient_method_inner_zero (k : ℕ) :
    x[k, 0] = x[k] := by
  simp

-- Proof sketch: apply `cyclic_block_proximal_gradient_inner_iterate_succ` to the base point
-- `x[k]`; this identifies the next stage with the source-facing one-block update in block
-- `⟨i, hi⟩`.
/-- For `i < p`, the next inner stage of CBPG is obtained by the one-block prox-gradient update of
the current stage in block `⟨i, hi⟩`, in the textbook form `x + 𝒰[i](...)` corresponding to
block `i + 1`. -/
theorem cyclic_block_proximal_gradient_method_inner_succ
    (k : ℕ) {i : ℕ} (hi : i < p) :
    let i' : Fin p := ⟨i, hi⟩
    let xi' : Ei i' := hproblem.prox_point (Li i') i' x[k, i]
    x[k, i + 1] = x[k, i] + 𝒰[i'] (xi' - x[k, i] i') := by
  simpa using
    cyclic_block_proximal_gradient_inner_iterate_succ hproblem x[k] hi

-- Proof sketch: unfold `cyclic_block_proximal_gradient_method` at `k + 1`; by definition the
-- next outer iterate is the terminal inner stage of the current cycle.
/-- Each outer CBPG iterate is the terminal inner stage of the preceding full block cycle:
`x^{k+1} = x^{k,p}`. -/
theorem cyclic_block_proximal_gradient_method_succ (k : ℕ) :
    x[k + 1] = x[k, p] :=
  rfl

end

end
