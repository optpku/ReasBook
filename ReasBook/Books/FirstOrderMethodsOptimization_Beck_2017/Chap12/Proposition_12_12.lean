/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Definition_12_19
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Proposition_12_10
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Proposition_12_11

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

noncomputable section

section

variable {n : ℕ}

local notation "En" => EuclideanSpace ℝ (Fin n)

open EuclideanSpace
open WithLp (toLp ofLp)

/- Proposition 12.12 is `source-facing`: it computes the proximal mapping of the second split
total-variation block `g₂` introduced in Proposition 12.11.

Domain sampling against the existing chapter API identifies:

- `core/canonical`: `prox[...]` from Chapter 6 and
  `one_dimensional_total_variation_odd_edge_penalty` from Proposition 12.11;
- `bridge/view`: Proposition 12.10's pairwise two-coordinate shrinkage formula, used here through
  `pair_difference_prox_correction` on each odd-start pair `(1,2), (3,4), ...`;
- the finite Euclidean product `EuclideanSpace ℝ (Fin n)` as the chapter's canonical realization
  of `ℝ^n`.

Primitive data are therefore only the existing split-block owner and the pairwise correction.
This file removes the duplicated local two-coordinate and odd-start penalty owners, and keeps only
the new explicit proximal point plus the singleton proximal formula for that canonical owner. -/

-- This block is the statement-pipeline's legacy self-contained copy of the Proposition 12.11
-- owner layer. Keep it file-local so importing both proposition modules does not redeclare the
-- canonical global owners supplied by `Proposition_12_11`.
namespace Proposition12_12Internal

/-- The `i`-th even-starting adjacent edge determines a canonical edge index in `Fin (n - 1)`. -/
theorem one_dimensional_total_variation_even_edge_lt (i : Fin (n / 2)) :
    2 * i.1 < n - 1 := by
  cases n with
  | zero =>
      exact i.elim0
  | succ n =>
      have hi : i.1 < (Nat.succ n) / 2 := i.is_lt
      omega

/-- The `i`-th even-starting adjacent edge, viewed as an edge of the canonical first-difference
operator `D[n]`. -/
def one_dimensional_total_variation_even_edge (i : Fin (n / 2)) : Fin (n - 1) :=
  ⟨2 * i.1, one_dimensional_total_variation_even_edge_lt i⟩

/-- The even edge index has underlying value `2 i`. -/
@[simp] theorem one_dimensional_total_variation_even_edge_val (i : Fin (n / 2)) :
    (one_dimensional_total_variation_even_edge i).1 = 2 * i.1 :=
  rfl

/-- The `i`-th odd-starting adjacent edge determines a canonical edge index in `Fin (n - 1)`. -/
theorem one_dimensional_total_variation_odd_edge_lt (i : Fin ((n - 1) / 2)) :
    2 * i.1 + 1 < n - 1 := by
  cases n with
  | zero =>
      exact i.elim0
  | succ n =>
      have hi : i.1 < n / 2 := i.is_lt
      omega

/-- The `i`-th odd-starting adjacent edge, viewed as an edge of the canonical first-difference
operator `D[n]`. -/
def one_dimensional_total_variation_odd_edge (i : Fin ((n - 1) / 2)) : Fin (n - 1) :=
  ⟨2 * i.1 + 1, one_dimensional_total_variation_odd_edge_lt i⟩

/-- The odd edge index has underlying value `2 i + 1`. -/
@[simp] theorem one_dimensional_total_variation_odd_edge_val (i : Fin ((n - 1) / 2)) :
    (one_dimensional_total_variation_odd_edge i).1 = 2 * i.1 + 1 :=
  rfl

/-- The first split total-variation block over the even-start adjacent edges. -/
def one_dimensional_total_variation_even_edge_penalty (lam : PosReal) : En → EReal :=
  fun x ↦
    (((lam : ℝ) *
        ∑ i : Fin (n / 2),
          |D[n] x (one_dimensional_total_variation_even_edge i)| : ℝ) : EReal)

/-- Evaluating the even-edge split penalty gives the scaled sum over the even-starting adjacent
TV edges. -/
@[simp] theorem one_dimensional_total_variation_even_edge_penalty_apply (lam : PosReal) (x : En) :
    one_dimensional_total_variation_even_edge_penalty lam x =
      (((lam : ℝ) *
          ∑ i : Fin (n / 2),
            |D[n] x (one_dimensional_total_variation_even_edge i)| : ℝ) : EReal) :=
  rfl

/-- The second split total-variation block over the odd-start adjacent edges. -/
def one_dimensional_total_variation_odd_edge_penalty (lam : PosReal) : En → EReal :=
  fun x ↦
    (((lam : ℝ) *
        ∑ i : Fin ((n - 1) / 2),
          |D[n] x (one_dimensional_total_variation_odd_edge i)| : ℝ) : EReal)

/-- Evaluating the odd-edge split penalty gives the scaled sum over the odd-starting adjacent TV
edges. -/
@[simp] theorem one_dimensional_total_variation_odd_edge_penalty_apply (lam : PosReal) (x : En) :
    one_dimensional_total_variation_odd_edge_penalty lam x =
      (((lam : ℝ) *
          ∑ i : Fin ((n - 1) / 2),
            |D[n] x (one_dimensional_total_variation_odd_edge i)| : ℝ) : EReal) :=
  rfl

/-- The left endpoint of the `i`-th even-starting edge is the coordinate `2 i`. -/
@[simp] theorem one_dimensional_total_variation_even_edge_left_val (i : Fin (n / 2)) :
    (one_dimensional_total_variation_edge_left (one_dimensional_total_variation_even_edge i)).1 =
      2 * i.1 := by
  simp [one_dimensional_total_variation_even_edge]

/-- The right endpoint of the `i`-th even-starting edge is the coordinate `2 i + 1`. -/
@[simp] theorem one_dimensional_total_variation_even_edge_right_val (i : Fin (n / 2)) :
    (one_dimensional_total_variation_edge_right (one_dimensional_total_variation_even_edge i)).1 =
      2 * i.1 + 1 := by
  simp [one_dimensional_total_variation_even_edge]

/-- The correction term attached to one even-start pair in the explicit even-edge proximal
point. -/
private def evenEdgeProxSummand (lam : PosReal) (x : En) (i : Fin (n / 2)) : En :=
  let e := one_dimensional_total_variation_even_edge i
  let l := one_dimensional_total_variation_edge_left e
  let r := one_dimensional_total_variation_edge_right e
  pair_difference_prox_correction lam
      (x l)
      (x r) •
    ((single l (1 : ℝ) : En) - single r (1 : ℝ))

/-- The explicit proximal point obtained by applying the two-coordinate correction independently to
all even-start pairs `(0,1), (2,3), ...` and leaving any last unpaired coordinate fixed. -/
def one_dimensional_total_variation_even_edge_prox_point (lam : PosReal) (x : En) : En :=
  x + ∑ i : Fin (n / 2), evenEdgeProxSummand lam x i

/-- Expanding `one_dimensional_total_variation_even_edge_prox_point` gives the explicit sum of the
even-start pairwise shrinkage corrections. -/
@[simp] theorem one_dimensional_total_variation_even_edge_prox_point_eq (lam : PosReal) (x : En) :
    one_dimensional_total_variation_even_edge_prox_point lam x =
      x +
        ∑ i : Fin (n / 2),
          let e := one_dimensional_total_variation_even_edge i
          let l := one_dimensional_total_variation_edge_left e
          let r := one_dimensional_total_variation_edge_right e
          pair_difference_prox_correction lam
              (x l)
              (x r) •
            ((single l (1 : ℝ) : En) - single r (1 : ℝ)) :=
  rfl

/-- Rebuild a vector in `ℝ^(n+2)` from its head pair and tail block. -/
def prepend_pair (p : EuclideanSpace ℝ (Fin 2)) (w : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin (n + 2)) :=
  toLp 2 (Fin.cons (p 0) (Fin.cons (p 1) w))

/-- The rebuilt vector has head coordinate `p 0`. -/
@[simp] theorem prepend_pair_zero (p : EuclideanSpace ℝ (Fin 2))
    (w : EuclideanSpace ℝ (Fin n)) :
    prepend_pair p w 0 = p 0 := by
  simp [prepend_pair]

/-- The rebuilt vector has second coordinate `p 1`. -/
@[simp] theorem prepend_pair_one (p : EuclideanSpace ℝ (Fin 2))
    (w : EuclideanSpace ℝ (Fin n)) :
    prepend_pair p w 1 = p 1 := by
  simp [prepend_pair]

/-- Dropping the first two coordinates of the rebuilt vector recovers the tail block. -/
@[simp] theorem prepend_pair_double_tail (p : EuclideanSpace ℝ (Fin 2))
    (w : EuclideanSpace ℝ (Fin n)) :
    toLp 2 (Fin.tail (Fin.tail (prepend_pair p w))) = w := by
  ext i
  simp [prepend_pair, Fin.tail]

/-- Reading the first two coordinates of the rebuilt vector recovers the input pair. -/
@[simp] theorem prepend_pair_head_pair (p : EuclideanSpace ℝ (Fin 2))
    (w : EuclideanSpace ℝ (Fin n)) :
    toLp 2 ![prepend_pair p w 0, prepend_pair p w 1] = p := by
  ext i
  fin_cases i <;> simp [prepend_pair]

/-- Every vector in `ℝ^(n+2)` is recovered from its head pair and double tail. -/
@[simp] theorem prepend_pair_reconstruct (x : EuclideanSpace ℝ (Fin (n + 2))) :
    prepend_pair (toLp 2 ![x 0, x 1]) (toLp 2 (Fin.tail (Fin.tail x))) = x := by
  ext i
  refine Fin.cases ?_ ?_ i
  · simp [prepend_pair]
  · intro i
    refine Fin.cases ?_ ?_ i
    · simp [prepend_pair]
    · intro j
      simp [prepend_pair, Fin.tail]

/-- On `ℝ^(n+2)`, the even-edge penalty splits into the first pair penalty and the even-edge
penalty on the double tail. -/
theorem one_dimensional_total_variation_even_edge_penalty_eq_head_pair_add_tail
    (lam : PosReal) (x : EuclideanSpace ℝ (Fin (n + 2))) :
    one_dimensional_total_variation_even_edge_penalty lam x =
      pair_difference_penalty (lam : ℝ) (toLp 2 ![x 0, x 1]) +
        one_dimensional_total_variation_even_edge_penalty lam
          (toLp 2 (Fin.tail (Fin.tail x))) := by
  rw [one_dimensional_total_variation_even_edge_penalty_apply,
    one_dimensional_total_variation_even_edge_penalty_apply, pair_difference_penalty]
  have hhalf : (n + 2) / 2 = n / 2 + 1 := by
    omega
  let f : Fin (n / 2 + 1) → ℝ := fun i ↦
    |D[n + 2] x
        (one_dimensional_total_variation_even_edge (Fin.cast hhalf.symm i))|
  have hsum_cast :
      ∑ i : Fin ((n + 2) / 2),
          |D[n + 2] x (one_dimensional_total_variation_even_edge i)| =
        ∑ i : Fin (n / 2 + 1), f i := by
    exact Fintype.sum_equiv (finCongr hhalf)
      (fun i : Fin ((n + 2) / 2) ↦
        |D[n + 2] x (one_dimensional_total_variation_even_edge i)|)
      f
      (fun i ↦ by simp [f])
  rw [hsum_cast, Fin.sum_univ_succ]
  have hhead : f 0 = |x 0 - x 1| := by
    simpa [f, hhalf, one_dimensional_total_variation_even_edge] using
      congrArg abs
        (one_dimensional_total_variation_difference_operator_apply_edge x
          (one_dimensional_total_variation_even_edge (Fin.cast hhalf.symm 0)))
  have htail :
      ∑ i : Fin (n / 2), f i.succ =
        ∑ i : Fin (n / 2),
            |D[n] (toLp 2 (Fin.tail (Fin.tail x)))
                (one_dimensional_total_variation_even_edge i)| := by
    apply Finset.sum_congr rfl
    intro i hi
    have hterm :
        f i.succ =
          |D[n] (toLp 2 (Fin.tail (Fin.tail x)))
              (one_dimensional_total_variation_even_edge i)| := by
      have hleft :
          one_dimensional_total_variation_edge_left
              (one_dimensional_total_variation_even_edge
                (Fin.cast hhalf.symm i.succ)) =
            (one_dimensional_total_variation_edge_left
              (one_dimensional_total_variation_even_edge i)).succ.succ := by
        apply Fin.ext
        simp [one_dimensional_total_variation_even_edge]
        omega
      have hright :
          one_dimensional_total_variation_edge_right
              (one_dimensional_total_variation_even_edge
                (Fin.cast hhalf.symm i.succ)) =
            (one_dimensional_total_variation_edge_right
              (one_dimensional_total_variation_even_edge i)).succ.succ := by
        apply Fin.ext
        simp [one_dimensional_total_variation_even_edge]
        omega
      rw [show f i.succ =
          |D[n + 2] x
              (one_dimensional_total_variation_even_edge
                (Fin.cast hhalf.symm i.succ))| by rfl]
      rw [one_dimensional_total_variation_difference_operator_apply_edge,
        one_dimensional_total_variation_difference_operator_apply_edge, hleft, hright]
      simp [Fin.tail]
    simpa using hterm
  rw [hhead, htail]
  simp [mul_add]

/-- On `ℝ^(n+2)`, the explicit even-edge proximal point is the pairwise proximal point on the first
two coordinates followed by the even-edge proximal point on the tail. -/
theorem one_dimensional_total_variation_even_edge_prox_point_eq_cons_pair_prox_point
    (lam : PosReal) (x : EuclideanSpace ℝ (Fin (n + 2))) :
    one_dimensional_total_variation_even_edge_prox_point lam x =
      toLp 2
        (Fin.cons ((pair_difference_prox_point (lam : ℝ) (x 0) (x 1)) 0)
          (Fin.cons ((pair_difference_prox_point (lam : ℝ) (x 0) (x 1)) 1)
            (one_dimensional_total_variation_even_edge_prox_point lam
              (toLp 2 (Fin.tail (Fin.tail x)))))) := by
  have hhalf : (n + 2) / 2 = n / 2 + 1 := by
    omega
  let g : Fin (n / 2 + 1) → EuclideanSpace ℝ (Fin (n + 2)) := fun i ↦
    let e :=
      one_dimensional_total_variation_even_edge (Fin.cast hhalf.symm i)
    let l := one_dimensional_total_variation_edge_left e
    let r := one_dimensional_total_variation_edge_right e
    pair_difference_prox_correction lam
        (x l)
        (x r) •
      ((single l (1 : ℝ) : EuclideanSpace ℝ (Fin (n + 2))) - single r (1 : ℝ))
  have hsum_cast :
      (∑ i : Fin ((n + 2) / 2),
          let e := one_dimensional_total_variation_even_edge i
          let l := one_dimensional_total_variation_edge_left e
          let r := one_dimensional_total_variation_edge_right e
          pair_difference_prox_correction lam
              (x l)
              (x r) •
            ((single l (1 : ℝ) : EuclideanSpace ℝ (Fin (n + 2))) - single r (1 : ℝ))) =
        ∑ i : Fin (n / 2 + 1), g i := by
    exact Fintype.sum_equiv (finCongr hhalf)
      (fun i : Fin ((n + 2) / 2) ↦
        let e := one_dimensional_total_variation_even_edge i
        let l := one_dimensional_total_variation_edge_left e
        let r := one_dimensional_total_variation_edge_right e
        pair_difference_prox_correction lam
            (x l)
            (x r) •
          ((single l (1 : ℝ) : EuclideanSpace ℝ (Fin (n + 2))) - single r (1 : ℝ)))
      g
      (fun i ↦ by simp [g])
  have hhead_left :
      one_dimensional_total_variation_edge_left
          (one_dimensional_total_variation_even_edge (Fin.cast hhalf.symm 0)) = 0 := by
    apply Fin.ext
    simp [one_dimensional_total_variation_even_edge]
  have hhead_right :
      one_dimensional_total_variation_edge_right
          (one_dimensional_total_variation_even_edge (Fin.cast hhalf.symm 0)) = 1 := by
    apply Fin.ext
    simp [one_dimensional_total_variation_even_edge]
  ext j
  refine Fin.cases ?_ ?_ j
  · rw [one_dimensional_total_variation_even_edge_prox_point_eq,
      one_dimensional_total_variation_even_edge_prox_point_eq, hsum_cast, Fin.sum_univ_succ]
    have htail_zero : ∑ i : Fin (n / 2), (g i.succ) 0 = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hleft :
          one_dimensional_total_variation_edge_left
              (one_dimensional_total_variation_even_edge
                (Fin.cast hhalf.symm i.succ)) =
            (one_dimensional_total_variation_edge_left
              (one_dimensional_total_variation_even_edge i)).succ.succ := by
        apply Fin.ext
        simp [one_dimensional_total_variation_even_edge]
        omega
      have hright :
          one_dimensional_total_variation_edge_right
              (one_dimensional_total_variation_even_edge
                (Fin.cast hhalf.symm i.succ)) =
            (one_dimensional_total_variation_edge_right
              (one_dimensional_total_variation_even_edge i)).succ.succ := by
        apply Fin.ext
        simp [one_dimensional_total_variation_even_edge]
        omega
      simp [g, hleft, hright]
    simp only [WithLp.ofLp_add, WithLp.ofLp_sum, WithLp.ofLp_smul, WithLp.ofLp_sub,
      Pi.add_apply, Finset.sum_apply, PiLp.ofLp_single, Fin.cons_zero]
    rw [htail_zero]
    simp [g, hhead_left, hhead_right, pair_difference_prox_point]
  · intro j
    refine Fin.cases ?_ ?_ j
    · rw [one_dimensional_total_variation_even_edge_prox_point_eq,
        one_dimensional_total_variation_even_edge_prox_point_eq, hsum_cast, Fin.sum_univ_succ]
      have htail_zero : ∑ i : Fin (n / 2), (g i.succ) 1 = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        have hleft :
            one_dimensional_total_variation_edge_left
                (one_dimensional_total_variation_even_edge
                  (Fin.cast hhalf.symm i.succ)) =
              (one_dimensional_total_variation_edge_left
                (one_dimensional_total_variation_even_edge i)).succ.succ := by
          apply Fin.ext
          simp [one_dimensional_total_variation_even_edge]
          omega
        have hright :
            one_dimensional_total_variation_edge_right
                (one_dimensional_total_variation_even_edge
                  (Fin.cast hhalf.symm i.succ)) =
              (one_dimensional_total_variation_edge_right
                (one_dimensional_total_variation_even_edge i)).succ.succ := by
          apply Fin.ext
          simp [one_dimensional_total_variation_even_edge]
          omega
        have hleft_ne :
            one_dimensional_total_variation_edge_left
                (one_dimensional_total_variation_even_edge
                  (Fin.cast hhalf.symm i.succ)) ≠ 1 := by
          rw [hleft]
          simpa using Fin.succ_succ_ne_one
            (one_dimensional_total_variation_edge_left
              (one_dimensional_total_variation_even_edge i))
        have hright_ne :
            one_dimensional_total_variation_edge_right
                (one_dimensional_total_variation_even_edge
                  (Fin.cast hhalf.symm i.succ)) ≠ 1 := by
          rw [hright]
          simpa using Fin.succ_succ_ne_one
            (one_dimensional_total_variation_edge_right
              (one_dimensional_total_variation_even_edge i))
        simp [g, hleft_ne, hright_ne]
      simp only [WithLp.ofLp_add, WithLp.ofLp_sum, WithLp.ofLp_smul, WithLp.ofLp_sub,
        Pi.add_apply, Finset.sum_apply, PiLp.ofLp_single, Fin.cons_succ, Fin.cons_zero]
      have htail_zero' : ∑ c : Fin (n / 2), (g c.succ) (Fin.succ 0) = 0 := by
        simpa using htail_zero
      rw [htail_zero']
      simp [g, hhead_left, hhead_right, pair_difference_prox_point, sub_eq_add_neg]
    · intro k
      rw [one_dimensional_total_variation_even_edge_prox_point_eq,
        one_dimensional_total_variation_even_edge_prox_point_eq, hsum_cast, Fin.sum_univ_succ]
      have hk_ne_zero : k.succ.succ ≠ 0 := by
        simp
      have hk_ne_one : k.succ.succ ≠ 1 := by
        simpa using Fin.succ_succ_ne_one k
      have hhead_zero : (g 0) k.succ.succ = 0 := by
        simp [g, hhead_left, hhead_right, hk_ne_zero, hk_ne_one]
      have htail_eq :
          ∑ i : Fin (n / 2), (g i.succ) k.succ.succ =
            (∑ i : Fin (n / 2),
                let e := one_dimensional_total_variation_even_edge i
                let l := one_dimensional_total_variation_edge_left e
                let r := one_dimensional_total_variation_edge_right e
                pair_difference_prox_correction lam
                    ((toLp 2 (Fin.tail (Fin.tail x))) l)
                    ((toLp 2 (Fin.tail (Fin.tail x))) r) •
                  ((single l (1 : ℝ) : EuclideanSpace ℝ (Fin n)) - single r (1 : ℝ))) k := by
        rw [WithLp.ofLp_sum, Finset.sum_apply]
        refine Finset.sum_congr rfl ?_
        intro i hi
        have hleft :
            one_dimensional_total_variation_edge_left
                (one_dimensional_total_variation_even_edge
                  (Fin.cast hhalf.symm i.succ)) =
              (one_dimensional_total_variation_edge_left
                (one_dimensional_total_variation_even_edge i)).succ.succ := by
          apply Fin.ext
          simp [one_dimensional_total_variation_even_edge]
          omega
        have hright :
            one_dimensional_total_variation_edge_right
                (one_dimensional_total_variation_even_edge
                  (Fin.cast hhalf.symm i.succ)) =
              (one_dimensional_total_variation_edge_right
                (one_dimensional_total_variation_even_edge i)).succ.succ := by
          apply Fin.ext
          simp [one_dimensional_total_variation_even_edge]
          omega
        simp [g, hleft, hright, Fin.tail]
      simp only [WithLp.ofLp_add, WithLp.ofLp_sum, WithLp.ofLp_smul, WithLp.ofLp_sub,
        Pi.add_apply, Finset.sum_apply, PiLp.ofLp_single, Fin.cons_succ]
      rw [hhead_zero, htail_eq]
      simp [Fin.tail]

/-- The explicit even-edge proximal point is the canonical `prepend_pair` reassembly of the
head-pair proximal point and the recursive tail proximal point. -/
theorem one_dimensional_total_variation_even_edge_prox_point_eq_prepend_pair
    (lam : PosReal) (x : EuclideanSpace ℝ (Fin (n + 2))) :
    one_dimensional_total_variation_even_edge_prox_point lam x =
      prepend_pair
        (pair_difference_prox_point (lam : ℝ) (x 0) (x 1))
        (one_dimensional_total_variation_even_edge_prox_point lam
          (toLp 2 (Fin.tail (Fin.tail x)))) := by
  simpa [prepend_pair] using
    (one_dimensional_total_variation_even_edge_prox_point_eq_cons_pair_prox_point lam x)

/-- In `ℝ^(n+2)`, the squared Euclidean distance splits into the head pair and double-tail
contributions. -/
theorem one_dimensional_total_variation_double_tail_norm_sq_split
    (x u : EuclideanSpace ℝ (Fin (n + 2))) :
    ‖u - x‖ ^ (2 : ℕ) =
      (u 0 - x 0) ^ (2 : ℕ) + (u 1 - x 1) ^ (2 : ℕ) +
        ‖(toLp 2 (Fin.tail (Fin.tail u))) - (toLp 2 (Fin.tail (Fin.tail x)))‖ ^ (2 : ℕ) := by
  have htail :
      ∑ i : Fin (n + 1), (u - x) i.succ ^ (2 : ℕ) =
        (u 1 - x 1) ^ (2 : ℕ) +
          ‖(toLp 2 (Fin.tail (Fin.tail u))) - (toLp 2 (Fin.tail (Fin.tail x)))‖ ^ (2 : ℕ) := by
    have htail_sum :
        ∑ i : Fin (n + 1), (u - x) i.succ ^ (2 : ℕ) =
          ‖toLp 2 (Fin.tail u - Fin.tail x)‖ ^ (2 : ℕ) := by
      simpa [Fin.tail, sub_eq_add_neg, pow_two] using
        (EuclideanSpace.real_norm_sq_eq (toLp 2 (Fin.tail u - Fin.tail x))).symm
    have htail_full := EuclideanSpace.real_norm_sq_eq (toLp 2 (Fin.tail u - Fin.tail x))
    rw [Fin.sum_univ_succ] at htail_full
    have hdouble_sum :
        ∑ i : Fin n, (toLp 2 (Fin.tail u - Fin.tail x)) i.succ ^ (2 : ℕ) =
          ‖(toLp 2 (Fin.tail (Fin.tail u))) - (toLp 2 (Fin.tail (Fin.tail x)))‖ ^ (2 : ℕ) := by
      simpa [Fin.tail, sub_eq_add_neg, pow_two] using
        (EuclideanSpace.real_norm_sq_eq
          ((toLp 2 (Fin.tail (Fin.tail u))) - (toLp 2 (Fin.tail (Fin.tail x))))).symm
    calc
      ∑ i : Fin (n + 1), (u - x) i.succ ^ (2 : ℕ) =
          ‖toLp 2 (Fin.tail u - Fin.tail x)‖ ^ (2 : ℕ) := htail_sum
      _ = (u 1 - x 1) ^ (2 : ℕ) +
            ‖(toLp 2 (Fin.tail (Fin.tail u))) - (toLp 2 (Fin.tail (Fin.tail x)))‖ ^ (2 : ℕ) := by
            rw [htail_full, hdouble_sum]
            simp [Fin.tail, sub_eq_add_neg, pow_two, add_comm]
  have hfull := EuclideanSpace.real_norm_sq_eq (u - x)
  rw [Fin.sum_univ_succ] at hfull
  calc
    ‖u - x‖ ^ (2 : ℕ) = (u - x) 0 ^ (2 : ℕ) + ∑ i : Fin (n + 1), (u - x) i.succ ^ (2 : ℕ) := by
      simpa using hfull
    _ = (u 0 - x 0) ^ (2 : ℕ) + (u 1 - x 1) ^ (2 : ℕ) +
          ‖(toLp 2 (Fin.tail (Fin.tail u))) - (toLp 2 (Fin.tail (Fin.tail x)))‖ ^ (2 : ℕ) := by
      rw [htail]
      simp [sub_eq_add_neg, pow_two, add_assoc, add_comm]

/-- On `ℝ^(n+2)`, the proximal objective of the even-edge penalty splits into the head-pair
problem and the recursive tail problem. -/
theorem one_dimensional_total_variation_even_edge_proximal_objective_split
    (lam : PosReal) (x u : EuclideanSpace ℝ (Fin (n + 2))) :
    proximal_objective (one_dimensional_total_variation_even_edge_penalty lam) x u =
      proximal_objective (pair_difference_penalty (lam : ℝ)) (toLp 2 ![x 0, x 1])
          (toLp 2 ![u 0, u 1]) +
        proximal_objective (one_dimensional_total_variation_even_edge_penalty lam)
          (toLp 2 (Fin.tail (Fin.tail x))) (toLp 2 (Fin.tail (Fin.tail u))) := by
  rw [proximal_objective_apply, proximal_objective_apply, proximal_objective_apply,
    one_dimensional_total_variation_even_edge_penalty_eq_head_pair_add_tail]
  have hpair :
      ‖(toLp 2 ![u 0, u 1]) - (toLp 2 ![x 0, x 1])‖ ^ (2 : ℕ) =
        (u 0 - x 0) ^ (2 : ℕ) + (u 1 - x 1) ^ (2 : ℕ) := by
    have hpair_norm :=
      EuclideanSpace.real_norm_sq_eq ((toLp 2 ![u 0, u 1]) - (toLp 2 ![x 0, x 1]))
    simpa [Fin.sum_univ_two, pow_two, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      hpair_norm
  have hnorm :
      ((((1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ)) : ℝ) : EReal) =
        (((((1 / 2 : ℝ) * ‖(toLp 2 ![u 0, u 1]) - (toLp 2 ![x 0, x 1])‖ ^ (2 : ℕ)) : ℝ)) : EReal) +
          ((((1 / 2 : ℝ) *
              ‖(toLp 2 (Fin.tail (Fin.tail u))) - (toLp 2 (Fin.tail (Fin.tail x)))‖ ^ (2 : ℕ)) :
              ℝ) : EReal) := by
    exact_mod_cast
      (show
        (1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ) =
          (1 / 2 : ℝ) * ‖(toLp 2 ![u 0, u 1]) - (toLp 2 ![x 0, x 1])‖ ^ (2 : ℕ) +
            (1 / 2 : ℝ) *
              ‖(toLp 2 (Fin.tail (Fin.tail u))) - (toLp 2 (Fin.tail (Fin.tail x)))‖ ^ (2 : ℕ) by
        nlinarith [one_dimensional_total_variation_double_tail_norm_sq_split x u, hpair])
  rw [hnorm]
  simp [add_assoc, add_left_comm, add_comm]

/-- Specializing the even-edge objective split to a rebuilt vector records the decomposition into a
head-pair problem and a recursive tail problem. -/
theorem one_dimensional_total_variation_even_edge_proximal_objective_prepend_pair
    (lam : PosReal) (x : EuclideanSpace ℝ (Fin (n + 2)))
    (p : EuclideanSpace ℝ (Fin 2)) (w : EuclideanSpace ℝ (Fin n)) :
    proximal_objective (one_dimensional_total_variation_even_edge_penalty lam) x
        (prepend_pair p w) =
      proximal_objective (pair_difference_penalty (lam : ℝ)) (toLp 2 ![x 0, x 1]) p +
        proximal_objective (one_dimensional_total_variation_even_edge_penalty lam)
          (toLp 2 (Fin.tail (Fin.tail x))) w := by
  have hp : toLp 2 ![p 0, p 1] = p := by
    ext i
    fin_cases i <;> simp
  simpa [hp] using
    (one_dimensional_total_variation_even_edge_proximal_objective_split lam x (prepend_pair p w))

/-- The pair proximal objective is always finite, so it can be cancelled as a real summand in
`EReal` inequalities. -/
theorem pair_difference_proximal_objective_eq_coe
    (lam : ℝ) (x u : EuclideanSpace ℝ (Fin 2)) :
    ∃ r : ℝ, proximal_objective (pair_difference_penalty lam) x u = (r : EReal) := by
  refine ⟨lam * |u 0 - u 1| + (1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ), ?_⟩
  simp [proximal_objective_apply, pair_difference_penalty, EReal.coe_add]

/-- The recursive even-edge proximal objective is always finite, so it can be cancelled as a real
summand in `EReal` inequalities. -/
theorem one_dimensional_total_variation_even_edge_proximal_objective_eq_coe
    (lam : PosReal) (x u : En) :
    ∃ r : ℝ,
      proximal_objective (one_dimensional_total_variation_even_edge_penalty lam) x u =
        (r : EReal) := by
  refine ⟨(lam : ℝ) *
      ∑ i : Fin (n / 2), |D[n] u (one_dimensional_total_variation_even_edge i)| +
        (1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ), ?_⟩
  simp [proximal_objective_apply, one_dimensional_total_variation_even_edge_penalty_apply,
    EReal.coe_add]

/-- On `ℝ^(n+2)`, proximal membership for the even-edge penalty factorizes into the head-pair
problem and the recursive tail problem. -/
theorem mem_prox_one_dimensional_total_variation_even_edge_penalty_iff_head_pair_double_tail
    (lam : PosReal) (x u : EuclideanSpace ℝ (Fin (n + 2))) :
    u ∈ prox[one_dimensional_total_variation_even_edge_penalty lam] x ↔
      toLp 2 ![u 0, u 1] ∈ prox[pair_difference_penalty (lam : ℝ)] (toLp 2 ![x 0, x 1]) ∧
        toLp 2 (Fin.tail (Fin.tail u)) ∈
          prox[one_dimensional_total_variation_even_edge_penalty lam]
            (toLp 2 (Fin.tail (Fin.tail x))) := by
  constructor
  · intro hu
    have htail_min :
        toLp 2 (Fin.tail (Fin.tail u)) ∈
          prox[one_dimensional_total_variation_even_edge_penalty lam]
            (toLp 2 (Fin.tail (Fin.tail x))) := by
      rw [mem_proximal_mapping_iff] at hu ⊢
      rw [isMinOn_univ_iff] at hu ⊢
      intro w
      let v : EuclideanSpace ℝ (Fin (n + 2)) := prepend_pair (toLp 2 ![u 0, u 1]) w
      have huv := hu v
      have hu_split :=
        one_dimensional_total_variation_even_edge_proximal_objective_split lam x u
      have hv_split :
          proximal_objective
              (one_dimensional_total_variation_even_edge_penalty lam) x v =
            proximal_objective (pair_difference_penalty (lam : ℝ)) (toLp 2 ![x 0, x 1])
                (toLp 2 ![u 0, u 1]) +
              proximal_objective
                (one_dimensional_total_variation_even_edge_penalty lam)
                (toLp 2 (Fin.tail (Fin.tail x))) w := by
        simpa [v] using
          (one_dimensional_total_variation_even_edge_proximal_objective_prepend_pair lam x (toLp 2 ![u 0, u 1]) w)
      rw [hu_split, hv_split] at huv
      obtain ⟨r, hr⟩ :=
        pair_difference_proximal_objective_eq_coe
          (lam : ℝ) (toLp 2 ![x 0, x 1]) (toLp 2 ![u 0, u 1])
      rw [hr] at huv
      exact (EReal.addLECancellable_coe r).add_le_add_iff_left.mp huv
    have hhead_min :
        toLp 2 ![u 0, u 1] ∈ prox[pair_difference_penalty (lam : ℝ)] (toLp 2 ![x 0, x 1]) := by
      rw [mem_proximal_mapping_iff] at hu ⊢
      rw [isMinOn_univ_iff] at hu ⊢
      intro p
      let v : EuclideanSpace ℝ (Fin (n + 2)) :=
        prepend_pair p (toLp 2 (Fin.tail (Fin.tail u)))
      have huv := hu v
      have hu_split :=
        one_dimensional_total_variation_even_edge_proximal_objective_split lam x u
      have hv_split :
          proximal_objective
              (one_dimensional_total_variation_even_edge_penalty lam) x v =
            proximal_objective (pair_difference_penalty (lam : ℝ)) (toLp 2 ![x 0, x 1]) p +
              proximal_objective
                (one_dimensional_total_variation_even_edge_penalty lam)
                (toLp 2 (Fin.tail (Fin.tail x))) (toLp 2 (Fin.tail (Fin.tail u))) := by
        simpa [v] using
          (one_dimensional_total_variation_even_edge_proximal_objective_prepend_pair lam x p (toLp 2 (Fin.tail (Fin.tail u))))
      rw [hu_split, hv_split] at huv
      obtain ⟨r, hr⟩ :=
        one_dimensional_total_variation_even_edge_proximal_objective_eq_coe lam (toLp 2 (Fin.tail (Fin.tail x))) (toLp 2 (Fin.tail (Fin.tail u)))
      rw [hr] at huv
      exact (EReal.addLECancellable_coe r).add_le_add_iff_right.mp huv
    exact ⟨hhead_min, htail_min⟩
  · rintro ⟨hhead_min, htail_min⟩
    rw [mem_proximal_mapping_iff]
    rw [isMinOn_univ_iff]
    intro v
    have hsplit_u :=
      one_dimensional_total_variation_even_edge_proximal_objective_split lam x u
    have hsplit_v :=
      one_dimensional_total_variation_even_edge_proximal_objective_split lam x v
    rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hhead_min htail_min
    rw [hsplit_u, hsplit_v]
    have hhead_le := hhead_min (toLp 2 ![v 0, v 1])
    have htail_le := htail_min (toLp 2 (Fin.tail (Fin.tail v)))
    exact add_le_add hhead_le htail_le

/-- The proximal mapping of the even-edge split total-variation block is a singleton given by the
explicit pairwise correction formula on each even-start pair. -/
theorem prox_one_dimensional_total_variation_even_edge_penalty_eq_singleton
    (lam : PosReal) (x : En) :
    prox[one_dimensional_total_variation_even_edge_penalty lam] x =
      {one_dimensional_total_variation_even_edge_prox_point lam x} := by
  induction n using Nat.twoStepInduction with
  | zero =>
      have hpen0 :
          one_dimensional_total_variation_even_edge_penalty lam =
            (0 : EuclideanSpace ℝ (Fin 0) → EReal) := by
        funext u
        simp [one_dimensional_total_variation_even_edge_penalty_apply]
      calc
        prox[one_dimensional_total_variation_even_edge_penalty lam] x = {x} := by
          rw [hpen0]
          simpa using prox_zero_eq_singleton x
        _ = {one_dimensional_total_variation_even_edge_prox_point lam x} := by
          congr 1
          simp [one_dimensional_total_variation_even_edge_prox_point_eq]
  | one =>
      have hpen1 :
          one_dimensional_total_variation_even_edge_penalty lam =
            (0 : EuclideanSpace ℝ (Fin 1) → EReal) := by
        funext u
        simp [one_dimensional_total_variation_even_edge_penalty_apply]
      calc
        prox[one_dimensional_total_variation_even_edge_penalty lam] x = {x} := by
          rw [hpen1]
          simpa using prox_zero_eq_singleton x
        _ = {one_dimensional_total_variation_even_edge_prox_point lam x} := by
          congr 1
          simp [one_dimensional_total_variation_even_edge_prox_point_eq]
  | more n ih =>
      ext u
      constructor
      · intro hu
        rw [Set.mem_singleton_iff]
        have hu_factor :
            toLp 2 ![u 0, u 1] ∈ prox[pair_difference_penalty (lam : ℝ)] (toLp 2 ![x 0, x 1]) ∧
              toLp 2 (Fin.tail (Fin.tail u)) ∈
                prox[one_dimensional_total_variation_even_edge_penalty lam]
                  (toLp 2 (Fin.tail (Fin.tail x))) := by
          exact
            (mem_prox_one_dimensional_total_variation_even_edge_penalty_iff_head_pair_double_tail lam x u).1 hu
        rcases hu_factor with ⟨hhead_min, htail_min⟩
        have hhead_eq :
            toLp 2 ![u 0, u 1] = pair_difference_prox_point (lam : ℝ) (x 0) (x 1) := by
          rw [prox_pair_difference_penalty_eq_singleton (lam : ℝ) lam.2.le (x 0) (x 1)] at hhead_min
          simpa using hhead_min
        have htail_eq :
            toLp 2 (Fin.tail (Fin.tail u)) =
              one_dimensional_total_variation_even_edge_prox_point lam
                (toLp 2 (Fin.tail (Fin.tail x))) := by
          rw [ih (toLp 2 (Fin.tail (Fin.tail x)))] at htail_min
          simpa using htail_min
        calc
          u =
              prepend_pair
                (pair_difference_prox_point (lam : ℝ) (x 0) (x 1))
                (one_dimensional_total_variation_even_edge_prox_point lam
                  (toLp 2 (Fin.tail (Fin.tail x)))) := by
            rw [← prepend_pair_reconstruct u]
            rw [hhead_eq, htail_eq]
          _ = one_dimensional_total_variation_even_edge_prox_point lam x := by
            symm
            exact one_dimensional_total_variation_even_edge_prox_point_eq_prepend_pair lam x
      · intro hu
        rw [Set.mem_singleton_iff] at hu
        subst hu
        apply
          (mem_prox_one_dimensional_total_variation_even_edge_penalty_iff_head_pair_double_tail lam x
            (one_dimensional_total_variation_even_edge_prox_point lam x)).2
        have hhead_min :
            toLp 2
                ![(one_dimensional_total_variation_even_edge_prox_point lam x) 0,
                  (one_dimensional_total_variation_even_edge_prox_point lam x) 1] ∈
              prox[pair_difference_penalty (lam : ℝ)] (toLp 2 ![x 0, x 1]) := by
          rw [one_dimensional_total_variation_even_edge_prox_point_eq_prepend_pair lam x]
          rw [prox_pair_difference_penalty_eq_singleton (lam : ℝ) lam.2.le (x 0) (x 1)]
          ext i
          fin_cases i <;> simp [pair_difference_prox_point]
        have htail_min :
            toLp 2
                (Fin.tail
                  (Fin.tail
                    (one_dimensional_total_variation_even_edge_prox_point lam x))) ∈
              prox[one_dimensional_total_variation_even_edge_penalty lam]
                (toLp 2 (Fin.tail (Fin.tail x))) := by
          rw [one_dimensional_total_variation_even_edge_prox_point_eq_prepend_pair lam x]
          rw [ih (toLp 2 (Fin.tail (Fin.tail x)))]
          simp
        exact ⟨hhead_min, htail_min⟩

end Proposition12_12Internal

private def oddEdgeProxSummand (lam : PosReal) (x : En) (i : Fin ((n - 1) / 2)) : En :=
  let e := one_dimensional_total_variation_odd_edge i
  let l := one_dimensional_total_variation_edge_left e
  let r := one_dimensional_total_variation_edge_right e
  pair_difference_prox_correction lam
      (x l)
      (x r) •
    ((single l (1 : ℝ) : En) - single r (1 : ℝ))

/-- The explicit proximal point obtained by applying the two-coordinate shrinkage independently to
all odd-start adjacent pairs `(1,2), (3,4), ...` and leaving the remaining coordinates fixed. -/
def one_dimensional_total_variation_odd_edge_prox_point (lam : PosReal) (x : En) : En :=
  x + ∑ i : Fin ((n - 1) / 2), oddEdgeProxSummand lam x i

-- Proof sketch: unfold `one_dimensional_total_variation_odd_edge_prox_point`; the right-hand side
-- is exactly
-- the sum of the pairwise corrections along the basis differences
-- `e_(2 i + 1) - e_(2 i + 2)`.
/-- Expanding `one_dimensional_total_variation_odd_edge_prox_point` gives the explicit sum of the
odd-start pairwise shrinkage corrections. -/
@[simp] theorem one_dimensional_total_variation_odd_edge_prox_point_eq (lam : PosReal) (x : En) :
    one_dimensional_total_variation_odd_edge_prox_point lam x =
      x +
        ∑ i : Fin ((n - 1) / 2),
          let e := one_dimensional_total_variation_odd_edge i
          let l := one_dimensional_total_variation_edge_left e
          let r := one_dimensional_total_variation_edge_right e
          pair_difference_prox_correction lam
              (x l)
              (x r) •
            ((single l (1 : ℝ) : En) - single r (1 : ℝ)) :=
  rfl

/-- Helper for Proposition 12.12: after dropping the first coordinate of a vector in
`ℝ^(n+1)`, the odd-edge penalty becomes the even-edge penalty on the tail coordinates. -/
theorem one_dimensional_total_variation_odd_edge_penalty_eq_even_edge_penalty_tail
    (lam : PosReal) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    one_dimensional_total_variation_odd_edge_penalty lam x =
      one_dimensional_total_variation_even_edge_penalty lam (toLp 2 (Fin.tail x)) := by
  -- Expand both penalties and identify the same adjacent differences after the index shift.
  rw [one_dimensional_total_variation_odd_edge_penalty_apply,
    one_dimensional_total_variation_even_edge_penalty_apply]
  congr 2
  apply Finset.sum_congr rfl
  intro i hi
  rw [one_dimensional_total_variation_difference_operator_apply_edge,
    one_dimensional_total_variation_difference_operator_apply_edge]
  have hleft :
      one_dimensional_total_variation_edge_left
          (one_dimensional_total_variation_odd_edge i) =
        (one_dimensional_total_variation_edge_left
          (one_dimensional_total_variation_even_edge i)).succ := by
    apply Fin.ext
    simp [one_dimensional_total_variation_odd_edge, one_dimensional_total_variation_even_edge]
  have hright :
      one_dimensional_total_variation_edge_right
          (one_dimensional_total_variation_odd_edge i) =
        (one_dimensional_total_variation_edge_right
          (one_dimensional_total_variation_even_edge i)).succ := by
    apply Fin.ext
    simp [one_dimensional_total_variation_odd_edge, one_dimensional_total_variation_even_edge]
  rw [hleft, hright]
  simp [Fin.tail]

/-- Helper for Proposition 12.12: on `ℝ^(n+1)`, the odd-edge proximal point keeps the first
coordinate and applies the even-edge proximal point to the tail coordinates. -/
theorem one_dimensional_total_variation_odd_edge_prox_point_eq_cons_even_edge_prox_point
    (lam : PosReal) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    one_dimensional_total_variation_odd_edge_prox_point lam x =
      toLp 2
        (Fin.cons (x 0)
          (one_dimensional_total_variation_even_edge_prox_point lam
            (toLp 2 (Fin.tail x)))) := by
  -- Compare coordinates: the odd-edge correction never touches index `0`, and on the tail it is
  -- exactly the even-edge correction from Proposition 12.11 after shifting the indices.
  ext j
  refine Fin.cases ?_ ?_ j
  · rw [one_dimensional_total_variation_odd_edge_prox_point_eq]
    simp only [Fin.cons_zero]
    have hsum :
        ∑ i : Fin ((n + 1 - 1) / 2),
            (let e := one_dimensional_total_variation_odd_edge i
             let l := one_dimensional_total_variation_edge_left e
             let r := one_dimensional_total_variation_edge_right e
             pair_difference_prox_correction lam (x l) (x r) •
               ((single l (1 : ℝ) : EuclideanSpace ℝ (Fin (n + 1))) - single r (1 : ℝ))) 0 = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hleft_ne :
          one_dimensional_total_variation_edge_left
              (one_dimensional_total_variation_odd_edge i) ≠ 0 := by
        intro h
        have hval := congrArg Fin.val h
        simp [one_dimensional_total_variation_odd_edge] at hval
      have hright_ne :
          one_dimensional_total_variation_edge_right
              (one_dimensional_total_variation_odd_edge i) ≠ 0 := by
        intro h
        have hval := congrArg Fin.val h
        simp [one_dimensional_total_variation_odd_edge] at hval
      simp [hleft_ne, hright_ne]
    simpa using hsum
  · intro j
    rw [one_dimensional_total_variation_odd_edge_prox_point_eq,
      one_dimensional_total_variation_even_edge_prox_point_eq]
    simp [Fin.cons, Fin.tail]
    congr 2
    funext i
    have hleft :
        one_dimensional_total_variation_edge_left
            (one_dimensional_total_variation_odd_edge i) =
          (one_dimensional_total_variation_edge_left
            (one_dimensional_total_variation_even_edge i)).succ := by
      apply Fin.ext
      simp [one_dimensional_total_variation_odd_edge, one_dimensional_total_variation_even_edge]
    have hright :
        one_dimensional_total_variation_edge_right
            (one_dimensional_total_variation_odd_edge i) =
          (one_dimensional_total_variation_edge_right
            (one_dimensional_total_variation_even_edge i)).succ := by
      apply Fin.ext
      simp [one_dimensional_total_variation_odd_edge, one_dimensional_total_variation_even_edge]
    rw [hleft, hright]
    congr 1
    simp [Pi.single_apply]

/-- Helper for Proposition 12.12: the odd-edge proximal point fixes the head coordinate. -/
@[simp] theorem one_dimensional_total_variation_odd_edge_prox_point_zero
    (lam : PosReal) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    one_dimensional_total_variation_odd_edge_prox_point lam x 0 = x 0 := by
  -- Read the head coordinate from the explicit `Fin.cons` decomposition.
  rw [one_dimensional_total_variation_odd_edge_prox_point_eq_cons_even_edge_prox_point lam x]
  simp

/-- Helper for Proposition 12.12: the tail of the odd-edge proximal point is exactly the
even-edge proximal point of the tail data. -/
@[simp] theorem one_dimensional_total_variation_tail_odd_edge_prox_point
    (lam : PosReal) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    toLp 2 (Fin.tail (one_dimensional_total_variation_odd_edge_prox_point lam x)) =
      one_dimensional_total_variation_even_edge_prox_point lam (toLp 2 (Fin.tail x)) := by
  -- Apply `Fin.tail` to the `Fin.cons` decomposition to remove the untouched head coordinate.
  simpa using congrArg (fun y : EuclideanSpace ℝ (Fin (n + 1)) ↦ toLp 2 (Fin.tail y))
    (one_dimensional_total_variation_odd_edge_prox_point_eq_cons_even_edge_prox_point lam x)

/-- Helper for Proposition 12.12: in `ℝ^(n+1)`, the squared Euclidean distance splits into the
head-coordinate contribution and the squared norm of the tail difference. -/
theorem one_dimensional_total_variation_tail_norm_sq_split
    (x u : EuclideanSpace ℝ (Fin (n + 1))) :
    ‖u - x‖ ^ (2 : ℕ) =
      (u 0 - x 0) ^ (2 : ℕ) +
        ‖(toLp 2 (Fin.tail u)) - (toLp 2 (Fin.tail x))‖ ^ (2 : ℕ) := by
  -- Expand the squared norm as the sum of squared coordinates and separate the head term.
  have hfull := EuclideanSpace.real_norm_sq_eq (u - x)
  have htail := EuclideanSpace.real_norm_sq_eq ((toLp 2 (Fin.tail u)) - (toLp 2 (Fin.tail x)))
  rw [Fin.sum_univ_succ] at hfull
  calc
    ‖u - x‖ ^ (2 : ℕ) = (u - x) 0 ^ (2 : ℕ) + ∑ i : Fin n, (u - x) i.succ ^ (2 : ℕ) := by
      simpa using hfull
    _ = (u 0 - x 0) ^ (2 : ℕ) +
          ∑ i : Fin n, ((toLp 2 (Fin.tail u)) - (toLp 2 (Fin.tail x))) i ^ (2 : ℕ) := by
      simp [Fin.tail, sub_eq_add_neg, pow_two, add_comm]
    _ = (u 0 - x 0) ^ (2 : ℕ) +
          ‖(toLp 2 (Fin.tail u)) - (toLp 2 (Fin.tail x))‖ ^ (2 : ℕ) := by
      rw [← htail]

/-- Helper for Proposition 12.12: in `ℝ^(n+1)`, the proximal objective of the odd-edge penalty
splits into the even-edge proximal objective on the tail plus the scalar quadratic term for the
first coordinate. -/
theorem one_dimensional_total_variation_odd_edge_proximal_objective_split
    (lam : PosReal) (x u : EuclideanSpace ℝ (Fin (n + 1))) :
    proximal_objective (one_dimensional_total_variation_odd_edge_penalty lam) x u =
      proximal_objective (one_dimensional_total_variation_even_edge_penalty lam)
          (toLp 2 (Fin.tail x)) (toLp 2 (Fin.tail u)) +
        ((((1 / 2 : ℝ) * (u 0 - x 0) ^ (2 : ℕ)) : ℝ) : EReal) := by
  -- Rewrite the odd penalty through the tail and split the quadratic term coordinatewise.
  rw [proximal_objective_apply, proximal_objective_apply,
    one_dimensional_total_variation_odd_edge_penalty_eq_even_edge_penalty_tail]
  have hnorm :
      ((((1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ)) : ℝ) : EReal) =
        ((((1 / 2 : ℝ) * ‖(toLp 2 (Fin.tail u)) - (toLp 2 (Fin.tail x))‖ ^ (2 : ℕ)) : ℝ) :
          EReal) +
          ((((1 / 2 : ℝ) * (u 0 - x 0) ^ (2 : ℕ)) : ℝ) : EReal) := by
    exact_mod_cast (show
      (1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ) =
        (1 / 2 : ℝ) * ‖(toLp 2 (Fin.tail u)) - (toLp 2 (Fin.tail x))‖ ^ (2 : ℕ) +
          (1 / 2 : ℝ) * (u 0 - x 0) ^ (2 : ℕ) by
      nlinarith [one_dimensional_total_variation_tail_norm_sq_split x u])
  rw [hnorm]
  simp [add_assoc]

/-- Helper for Proposition 12.12: specializing the odd-edge objective split to an explicit
`Fin.cons` vector records the source-proof decomposition into a free head coordinate and the even
tail problem. -/
theorem one_dimensional_total_variation_odd_edge_proximal_objective_cons
    (lam : PosReal) (x : EuclideanSpace ℝ (Fin (n + 1))) (a : ℝ)
    (z : EuclideanSpace ℝ (Fin n)) :
    proximal_objective (one_dimensional_total_variation_odd_edge_penalty lam) x
        (toLp 2 (Fin.cons a z)) =
      proximal_objective (one_dimensional_total_variation_even_edge_penalty lam)
          (toLp 2 (Fin.tail x)) z +
        ((((1 / 2 : ℝ) * (a - x 0) ^ (2 : ℕ)) : ℝ) : EReal) := by
  -- Specialize the tail-splitting identity to the explicit `head :: tail` reconstruction.
  simpa using
    (one_dimensional_total_variation_odd_edge_proximal_objective_split lam x (toLp 2 (Fin.cons a z)))

/-- Helper for Proposition 12.12: resetting the head coordinate to `x 0` removes the scalar
quadratic term from the odd-edge objective split. -/
@[simp] theorem one_dimensional_total_variation_odd_edge_proximal_objective_cons_head
    (lam : PosReal) (x : EuclideanSpace ℝ (Fin (n + 1))) (z : EuclideanSpace ℝ (Fin n)) :
    proximal_objective (one_dimensional_total_variation_odd_edge_penalty lam) x
        (toLp 2 (Fin.cons (x 0) z)) =
      proximal_objective (one_dimensional_total_variation_even_edge_penalty lam)
          (toLp 2 (Fin.tail x)) z := by
  -- The added scalar correction vanishes because the reconstructed vector keeps the original head.
  rw [one_dimensional_total_variation_odd_edge_proximal_objective_cons]
  simp

/-- Helper for Proposition 12.12: odd-edge proximal membership factorizes into the untouched head
coordinate and the even-edge proximal problem on the tail block. -/
theorem mem_prox_one_dimensional_total_variation_odd_edge_penalty_iff_head_eq_tail_mem
    (lam : PosReal) (x u : EuclideanSpace ℝ (Fin (n + 1))) :
    u ∈ prox[one_dimensional_total_variation_odd_edge_penalty lam] x ↔
      u 0 = x 0 ∧
        toLp 2 (Fin.tail u) ∈
          prox[one_dimensional_total_variation_even_edge_penalty lam]
            (toLp 2 (Fin.tail x)) := by
  constructor
  · intro hu
    have htail_min :
        toLp 2 (Fin.tail u) ∈
          prox[one_dimensional_total_variation_even_edge_penalty lam]
            (toLp 2 (Fin.tail x)) := by
      -- Freeze the head coordinate at `x 0` and compare only the tail competitors.
      rw [mem_proximal_mapping_iff] at hu ⊢
      rw [isMinOn_univ_iff] at hu ⊢
      intro z
      let v : EuclideanSpace ℝ (Fin (n + 1)) := toLp 2 (Fin.cons (x 0) z)
      have huv := hu v
      have hu_split :=
        one_dimensional_total_variation_odd_edge_proximal_objective_split lam x u
      have hv_split :
          proximal_objective
              (one_dimensional_total_variation_odd_edge_penalty lam) x v =
            proximal_objective
                (one_dimensional_total_variation_even_edge_penalty lam)
                (toLp 2 (Fin.tail x)) z := by
        simpa [v] using
          (one_dimensional_total_variation_odd_edge_proximal_objective_cons_head lam x z)
      have hhead_nonneg :
          (0 : EReal) ≤ ((((1 / 2 : ℝ) * (u 0 - x 0) ^ (2 : ℕ)) : ℝ) : EReal) := by
        positivity
      rw [hu_split, hv_split] at huv
      have hdrop :
          proximal_objective (one_dimensional_total_variation_even_edge_penalty lam)
              (toLp 2 (Fin.tail x)) (toLp 2 (Fin.tail u)) ≤
            proximal_objective (one_dimensional_total_variation_even_edge_penalty lam)
              (toLp 2 (Fin.tail x)) (toLp 2 (Fin.tail u)) +
                ((((1 / 2 : ℝ) * (u 0 - x 0) ^ (2 : ℕ)) : ℝ) : EReal) := by
        simpa using le_add_of_nonneg_right hhead_nonneg
      exact le_trans hdrop huv
    have hhead : u 0 = x 0 := by
      -- Reset only the head coordinate; minimality forces the extra scalar term to vanish.
      let v : EuclideanSpace ℝ (Fin (n + 1)) := toLp 2 (Fin.cons (x 0) (Fin.tail u))
      have huv :
          proximal_objective
              (one_dimensional_total_variation_odd_edge_penalty lam) x u ≤
            proximal_objective
              (one_dimensional_total_variation_odd_edge_penalty lam) x v := by
        rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hu
        exact hu v
      have hu_split :=
        one_dimensional_total_variation_odd_edge_proximal_objective_split lam x u
      have hv_split :
          proximal_objective
              (one_dimensional_total_variation_odd_edge_penalty lam) x v =
            proximal_objective
                (one_dimensional_total_variation_even_edge_penalty lam)
                (toLp 2 (Fin.tail x)) (toLp 2 (Fin.tail u)) := by
        simpa [v] using
          (one_dimensional_total_variation_odd_edge_proximal_objective_cons_head lam x (toLp 2 (Fin.tail u)))
      rw [hu_split, hv_split] at huv
      have hnonneg :
          (0 : EReal) ≤ ((((1 / 2 : ℝ) * (u 0 - x 0) ^ (2 : ℕ)) : ℝ) : EReal) := by
        positivity
      obtain ⟨r, hr⟩ :=
        one_dimensional_total_variation_even_edge_proximal_objective_eq_coe lam (toLp 2 (Fin.tail x)) (toLp 2 (Fin.tail u))
      have hsum_le : r + (1 / 2 : ℝ) * (u 0 - x 0) ^ (2 : ℕ) ≤ r := by
        rw [hr] at huv
        exact_mod_cast huv
      have hle_zero :
          ((((1 / 2 : ℝ) * (u 0 - x 0) ^ (2 : ℕ)) : ℝ) : EReal) ≤ 0 := by
        have hle_zero_real : (1 / 2 : ℝ) * (u 0 - x 0) ^ (2 : ℕ) ≤ 0 := by
          linarith
        exact_mod_cast hle_zero_real
      have hzero :
          ((((1 / 2 : ℝ) * (u 0 - x 0) ^ (2 : ℕ)) : ℝ) : EReal) = 0 :=
        le_antisymm hle_zero hnonneg
      have hzero_real : (1 / 2 : ℝ) * (u 0 - x 0) ^ (2 : ℕ) = 0 := by
        exact_mod_cast hzero
      have hsq : (u 0 - x 0) ^ (2 : ℕ) = 0 := by
        linarith
      have hsub : u 0 - x 0 = 0 := by
        exact eq_zero_of_pow_eq_zero hsq
      linarith
    exact ⟨hhead, htail_min⟩
  · rintro ⟨hhead, htail_min⟩
    rw [mem_proximal_mapping_iff]
    rw [isMinOn_univ_iff]
    intro v
    -- Compare the split odd objective against the minimized tail objective and the nonnegative
    -- scalar head correction.
    have hsplit_u :=
      one_dimensional_total_variation_odd_edge_proximal_objective_split lam x u
    have hsplit_v :=
      one_dimensional_total_variation_odd_edge_proximal_objective_split lam x v
    rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at htail_min
    rw [hsplit_u, hsplit_v]
    have htail_le := htail_min (toLp 2 (Fin.tail v))
    have hhead_zero :
        ((((1 / 2 : ℝ) * (u 0 - x 0) ^ (2 : ℕ)) : ℝ) : EReal) = 0 := by
      simp [hhead]
    have hhead_nonneg :
        (0 : EReal) ≤ ((((1 / 2 : ℝ) * (v 0 - x 0) ^ (2 : ℕ)) : ℝ) : EReal) := by
      positivity
    have htail_le' :
        proximal_objective (one_dimensional_total_variation_even_edge_penalty lam)
            (toLp 2 (Fin.tail x)) (toLp 2 (Fin.tail u)) +
            ((((1 / 2 : ℝ) * (u 0 - x 0) ^ (2 : ℕ)) : ℝ) : EReal) ≤
          proximal_objective (one_dimensional_total_variation_even_edge_penalty lam)
            (toLp 2 (Fin.tail x)) (toLp 2 (Fin.tail v)) := by
      rw [hhead_zero]
      simpa using htail_le
    calc
      proximal_objective (one_dimensional_total_variation_even_edge_penalty lam)
          (toLp 2 (Fin.tail x)) (toLp 2 (Fin.tail u)) +
          ((((1 / 2 : ℝ) * (u 0 - x 0) ^ (2 : ℕ)) : ℝ) : EReal)
          ≤
        proximal_objective (one_dimensional_total_variation_even_edge_penalty lam)
          (toLp 2 (Fin.tail x)) (toLp 2 (Fin.tail v)) := htail_le'
      _ ≤
        proximal_objective (one_dimensional_total_variation_even_edge_penalty lam)
          (toLp 2 (Fin.tail x)) (toLp 2 (Fin.tail v)) +
          ((((1 / 2 : ℝ) * (v 0 - x 0) ^ (2 : ℕ)) : ℝ) : EReal) :=
            le_add_of_nonneg_right hhead_nonneg

-- Route correction: keep the textbook tail-reduction route through the even-edge problem on
-- `Fin.tail x`, and package the `Fin.cons` specialization explicitly instead of adding a new
-- block-separable transport layer in this file.
-- Proof sketch: use the separability of `one_dimensional_total_variation_odd_edge_penalty lam`
-- across the
-- disjoint odd-start adjacent pairs, apply
-- `prox_pair_difference_penalty_eq_singleton` on each two-coordinate block, and observe that all
-- untouched coordinates remain fixed.
/-- Proposition 12.12: for the split total-variation block
`g₂(x) = λ ∑ |x_(2 i + 1) - x_(2 i + 2)|`, realized on `Fin n` as the odd-start adjacent pairs
`(1,2), (3,4), ...`, the proximal mapping is the singleton containing the point obtained by the
explicit pairwise shrinkage formula on each such pair, for the chapter's positive parameter
`lam : PosReal`. -/
theorem prox_one_dimensional_total_variation_odd_edge_penalty_eq_singleton
    (lam : PosReal) (x : En) :
    prox[one_dimensional_total_variation_odd_edge_penalty lam] x =
      {one_dimensional_total_variation_odd_edge_prox_point lam x} := by
  cases n with
  | zero =>
      -- With no coordinates, the odd-edge penalty is identically zero and the proximal map fixes
      -- the unique point.
      have hpen0 :
          one_dimensional_total_variation_odd_edge_penalty lam =
            (0 : EuclideanSpace ℝ (Fin 0) → EReal) := by
        funext u
        simp [one_dimensional_total_variation_odd_edge_penalty_apply]
      calc
        prox[one_dimensional_total_variation_odd_edge_penalty lam] x = {x} := by
          rw [hpen0]
          simpa using prox_zero_eq_singleton x
        _ = {one_dimensional_total_variation_odd_edge_prox_point lam x} := by
          congr 1
          simp [one_dimensional_total_variation_odd_edge_prox_point_eq]
  | succ n =>
      -- Reduce the odd-edge problem on `ℝ^(n+1)` to the even-edge problem on the tail.
      ext u
      constructor
      · intro hu
        rw [Set.mem_singleton_iff]
        have hu_factor :
            u 0 = x 0 ∧
            toLp 2 (Fin.tail u) ∈
              prox[one_dimensional_total_variation_even_edge_penalty lam]
                (toLp 2 (Fin.tail x)) := by
          exact
            (mem_prox_one_dimensional_total_variation_odd_edge_penalty_iff_head_eq_tail_mem lam x u).1 hu
        rcases hu_factor with ⟨hhead, htail_min⟩
        have htail_eq :
            toLp 2 (Fin.tail u) =
              one_dimensional_total_variation_even_edge_prox_point lam
                (toLp 2 (Fin.tail x)) := by
          rw [prox_one_dimensional_total_variation_even_edge_penalty_eq_singleton lam (toLp 2 (Fin.tail x))] at htail_min
          simpa using htail_min
        calc
          u =
              toLp 2
                (Fin.cons (x 0)
                  (one_dimensional_total_variation_even_edge_prox_point lam
                    (toLp 2 (Fin.tail x)))) := by
            ext j
            refine Fin.cases ?_ ?_ j
            · simpa using hhead
            · intro j
              simpa [hhead] using congrArg (fun y : EuclideanSpace ℝ (Fin n) ↦ y j) htail_eq
          _ = one_dimensional_total_variation_odd_edge_prox_point lam x := by
            symm
            exact one_dimensional_total_variation_odd_edge_prox_point_eq_cons_even_edge_prox_point lam x
      · intro hu
        rw [Set.mem_singleton_iff] at hu
        subst hu
        apply
          (mem_prox_one_dimensional_total_variation_odd_edge_penalty_iff_head_eq_tail_mem lam x
            (one_dimensional_total_variation_odd_edge_prox_point lam x)).2
        have htail_min :
            toLp 2
                (Fin.tail
                  (one_dimensional_total_variation_odd_edge_prox_point lam x)) ∈
              prox[one_dimensional_total_variation_even_edge_penalty lam]
                (toLp 2 (Fin.tail x)) := by
          rw [one_dimensional_total_variation_tail_odd_edge_prox_point lam x]
          rw [prox_one_dimensional_total_variation_even_edge_penalty_eq_singleton lam (toLp 2 (Fin.tail x))]
          simp
        have hhead :
            one_dimensional_total_variation_odd_edge_prox_point lam x 0 = x 0 := by
          -- The decomposition theorem already records that the head coordinate is unchanged.
          simpa using one_dimensional_total_variation_odd_edge_prox_point_zero lam x
        exact ⟨hhead, htail_min⟩

end
