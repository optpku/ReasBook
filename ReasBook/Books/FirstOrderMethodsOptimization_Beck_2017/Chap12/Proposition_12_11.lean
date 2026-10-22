/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Definition_12_19
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Proposition_12_10

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
open EuclideanSpace
open WithLp (toLp ofLp)

noncomputable section

section

variable {n : ℕ}

local notation "En" => EuclideanSpace ℝ (Fin n)

/- Proposition 12.11 is `source-facing` in the one-dimensional total-variation examples. Domain
sampling against Proposition 12.10, Chapter 6 Definition 6.1, and the nearby Euclidean finite
product files identifies the following owner split:

- `source-facing`: the two split total-variation penalties `g₁` and `g₂` on `ℝ^n`;
- `core/canonical`: the Chapter 6 proximal-set operator `prox[...]` on `EuclideanSpace ℝ (Fin n)`;
- `bridge/view`: Proposition 12.10's explicit two-coordinate proximal formula, applied
  independently to the disjoint pairs `(0,1), (2,3), ...`, together with the canonical adjacent
  edge endpoint maps from Definition 12.19.

Accordingly, this file keeps the concrete even-edge and odd-edge penalties and the explicit
pairwise correction owner `pair_difference_prox_correction` visible, but it now derives their
indexing from the canonical adjacent-edge owner `D[·]` from Definition 12.19. The public bridge
layer is therefore the even/odd subfamily of `Fin (n - 1)` edge indices, while the main labeled
entry remains the singleton formula for the proximal mapping of `g₁`. The companion definition of
`g₂` is included because the source introduces both split blocks in the same proposition, even
though only `g₁` is analyzed here. -/

-- Proof sketch: if `i < n / 2`, then `2 i + 1 < n`, so `2 i < n - 1`; this is exactly the range
-- condition for an adjacent edge index of `D[n]`.
/-- The `i`-th even-starting adjacent edge determines a canonical edge index in `Fin (n - 1)`. -/
theorem one_dimensional_total_variation_even_edge_lt (i : Fin (n / 2)) :
    2 * i.1 < n - 1 := by
  -- Reduce the degenerate `n = 0` case to the empty index type, then finish the positive-length
  -- cases by Presburger arithmetic on `i.is_lt`.
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

-- Proof sketch: if `i < (n - 1) / 2`, then `2 i + 2 < n`, so `2 i + 1 < n - 1`; this is the
-- odd-start edge index in the canonical adjacent-edge family.
/-- The `i`-th odd-starting adjacent edge determines a canonical edge index in `Fin (n - 1)`. -/
theorem one_dimensional_total_variation_odd_edge_lt (i : Fin ((n - 1) / 2)) :
    2 * i.1 + 1 < n - 1 := by
  -- Reduce the degenerate `n = 0` case to the empty index type, then rewrite `n - 1` in the
  -- successor case and close the arithmetic bound with `omega`.
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

/-- The first split total-variation block
`g₁(x) = λ ∑ |x_(2 i) - x_(2 i + 1)|`, for the chapter's positive parameter `lam : PosReal`,
realized as the sum over the even-starting adjacent edges of the canonical difference operator
`D[n]`. -/
def one_dimensional_total_variation_even_edge_penalty (lam : PosReal) : En → EReal :=
  fun x ↦
    (((lam : ℝ) *
        ∑ i : Fin (n / 2),
          |D[n] x (one_dimensional_total_variation_even_edge i)| : ℝ) : EReal)

-- Proof sketch: unfold `one_dimensional_total_variation_even_edge_penalty`; the displayed
-- even-start pair sum
-- is its defining formula.
/-- Evaluating the even-edge split penalty gives the scaled sum over the even-starting adjacent
TV edges. -/
@[simp] theorem one_dimensional_total_variation_even_edge_penalty_apply (lam : PosReal) (x : En) :
    one_dimensional_total_variation_even_edge_penalty lam x =
      (((lam : ℝ) *
          ∑ i : Fin (n / 2),
            |D[n] x (one_dimensional_total_variation_even_edge i)| : ℝ) : EReal) :=
  rfl

/-- The second split total-variation block
`g₂(x) = λ ∑ |x_(2 i + 1) - x_(2 i + 2)|`, for the chapter's positive parameter
`lam : PosReal`, realized as the sum over the odd-starting adjacent edges of the canonical
difference operator `D[n]`. -/
def one_dimensional_total_variation_odd_edge_penalty (lam : PosReal) : En → EReal :=
  fun x ↦
    (((lam : ℝ) *
        ∑ i : Fin ((n - 1) / 2),
          |D[n] x (one_dimensional_total_variation_odd_edge i)| : ℝ) : EReal)

-- Proof sketch: unfold `one_dimensional_total_variation_odd_edge_penalty`; the displayed odd-start
-- pair sum
-- is its defining formula.
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

-- Proof sketch: unfold `one_dimensional_total_variation_even_edge_prox_point`; the right-hand side
-- is exactly
-- the sum of the pairwise corrections along the basis differences
-- `e_(2 i) - e_(2 i + 1)`.
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

/-- Helper for Proposition 12.11: rebuild a vector in `ℝ^(n+2)` from its head pair and double
tail. -/
def prepend_pair (p : EuclideanSpace ℝ (Fin 2)) (w : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin (n + 2)) :=
  toLp 2 (Fin.cons (p 0) (Fin.cons (p 1) w))

/-- Helper for Proposition 12.11: the rebuilt vector has head coordinate `p 0`. -/
@[simp] theorem prepend_pair_zero (p : EuclideanSpace ℝ (Fin 2))
    (w : EuclideanSpace ℝ (Fin n)) :
    prepend_pair p w 0 = p 0 := by
  -- Read the first coordinate from the `Fin.cons` reconstruction.
  simp [prepend_pair]

/-- Helper for Proposition 12.11: the rebuilt vector has second coordinate `p 1`. -/
@[simp] theorem prepend_pair_one (p : EuclideanSpace ℝ (Fin 2))
    (w : EuclideanSpace ℝ (Fin n)) :
    prepend_pair p w 1 = p 1 := by
  -- Read the second coordinate from the same reconstruction.
  simp [prepend_pair]

/-- Helper for Proposition 12.11: dropping the first two coordinates of the rebuilt vector
recovers the tail block. -/
@[simp] theorem prepend_pair_double_tail (p : EuclideanSpace ℝ (Fin 2))
    (w : EuclideanSpace ℝ (Fin n)) :
    toLp 2 (Fin.tail (Fin.tail (prepend_pair p w))) = w := by
  -- After removing the head pair, only the tail block remains.
  ext i
  simp [prepend_pair, Fin.tail]

/-- Helper for Proposition 12.11: reading the first two coordinates of the rebuilt vector
recovers the input pair. -/
@[simp] theorem prepend_pair_head_pair (p : EuclideanSpace ℝ (Fin 2))
    (w : EuclideanSpace ℝ (Fin n)) :
    toLp 2 ![prepend_pair p w 0, prepend_pair p w 1] = p := by
  -- The head coordinates of `prepend_pair p w` were defined to be exactly `p`.
  ext i
  fin_cases i <;> simp [prepend_pair]

/-- Helper for Proposition 12.11: every vector in `ℝ^(n+2)` is recovered from its head pair and
double tail. -/
@[simp] theorem prepend_pair_reconstruct (x : EuclideanSpace ℝ (Fin (n + 2))) :
    prepend_pair (toLp 2 ![x 0, x 1]) (toLp 2 (Fin.tail (Fin.tail x))) = x := by
  -- Check the head coordinates and the tail coordinates separately.
  ext i
  refine Fin.cases ?_ ?_ i
  · simp [prepend_pair]
  · intro i
    refine Fin.cases ?_ ?_ i
    · simp [prepend_pair]
    · intro j
      simp [prepend_pair, Fin.tail]

/-- Helper for Proposition 12.11: on `ℝ^(n+2)`, the even-edge penalty splits into the first
two-coordinate pair penalty and the even-edge penalty on the double tail. -/
theorem one_dimensional_total_variation_even_edge_penalty_eq_head_pair_add_tail
    (lam : PosReal) (x : EuclideanSpace ℝ (Fin (n + 2))) :
    @one_dimensional_total_variation_even_edge_penalty (n + 2) lam x =
      pair_difference_penalty (lam : ℝ) (toLp 2 ![x 0, x 1]) +
        @one_dimensional_total_variation_even_edge_penalty (n) lam
          (toLp 2 (Fin.tail (Fin.tail x))) := by
  -- Reindex the even-starting edges into the head pair plus the shifted tail pairs.
  rw [one_dimensional_total_variation_even_edge_penalty_apply,
    one_dimensional_total_variation_even_edge_penalty_apply, pair_difference_penalty]
  have hhalf : (n + 2) / 2 = n / 2 + 1 := by
    omega
  let f : Fin (n / 2 + 1) → ℝ := fun i ↦
    |D[n + 2] x
        (@one_dimensional_total_variation_even_edge (n + 2) (Fin.cast hhalf.symm i))|
  have hsum_cast :
      ∑ i : Fin ((n + 2) / 2),
          |D[n + 2] x (@one_dimensional_total_variation_even_edge (n + 2) i)| =
        ∑ i : Fin (n / 2 + 1), f i := by
    exact Fintype.sum_equiv (finCongr hhalf)
      (fun i : Fin ((n + 2) / 2) ↦
        |D[n + 2] x (@one_dimensional_total_variation_even_edge (n + 2) i)|)
      f
      (fun i ↦ by simp [f])
  rw [hsum_cast, Fin.sum_univ_succ]
  have hhead : f 0 = |x 0 - x 1| := by
    simpa [f, hhalf, one_dimensional_total_variation_even_edge] using
      congrArg abs
        (@one_dimensional_total_variation_difference_operator_apply_edge (n + 2) x
          (@one_dimensional_total_variation_even_edge (n + 2) (Fin.cast hhalf.symm 0)))
  have htail :
      ∑ i : Fin (n / 2), f i.succ =
        ∑ i : Fin (n / 2),
            |D[n] (toLp 2 (Fin.tail (Fin.tail x)))
                (@one_dimensional_total_variation_even_edge (n) i)| := by
    apply Finset.sum_congr rfl
    intro i hi
    have hterm :
        f i.succ =
          |D[n] (toLp 2 (Fin.tail (Fin.tail x)))
              (@one_dimensional_total_variation_even_edge (n) i)| := by
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
              (@one_dimensional_total_variation_even_edge (n + 2)
                (Fin.cast hhalf.symm i.succ))| by rfl]
      rw [one_dimensional_total_variation_difference_operator_apply_edge,
        one_dimensional_total_variation_difference_operator_apply_edge, hleft, hright]
      simp [Fin.tail]
    simpa using hterm
  rw [hhead, htail]
  simp [mul_add]

/-- Helper for Proposition 12.11: on `ℝ^(n+2)`, the explicit even-edge proximal point is the
pairwise proximal point on the first two coordinates followed by the even-edge proximal point on
the double tail. -/
theorem one_dimensional_total_variation_even_edge_prox_point_eq_cons_pair_prox_point
    (lam : PosReal) (x : EuclideanSpace ℝ (Fin (n + 2))) :
    one_dimensional_total_variation_even_edge_prox_point lam x =
      toLp 2
        (Fin.cons ((pair_difference_prox_point (lam : ℝ) (x 0) (x 1)) 0)
          (Fin.cons ((pair_difference_prox_point (lam : ℝ) (x 0) (x 1)) 1)
            (one_dimensional_total_variation_even_edge_prox_point lam
              (toLp 2 (Fin.tail (Fin.tail x)))))) := by
  -- Separate the first pair correction from the shifted tail corrections coordinatewise.
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
    have hhead_eq :
        x 0 + g 0 0 = (pair_difference_prox_point (lam : ℝ) (x 0) (x 1)) 0 := by
      dsimp only [g]
      rw [hhead_left, hhead_right]
      simp [pair_difference_prox_point]
    have hcoord :
        x 0 + (g 0 0 + ∑ i : Fin (n / 2), (g i.succ) 0) =
          (pair_difference_prox_point (lam : ℝ) (x 0) (x 1)) 0 := by
      rw [htail_zero]
      simpa [add_assoc] using hhead_eq
    simpa [Finset.sum_apply, add_assoc] using hcoord
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
        have hone_ne_left :
            (1 : Fin (n + 2)) ≠
              (one_dimensional_total_variation_edge_left
                (one_dimensional_total_variation_even_edge i)).succ.succ := by
          simpa using
            (one_dimensional_total_variation_edge_left
              (one_dimensional_total_variation_even_edge i)).succ_succ_ne_one.symm
        have hone_ne_right :
            (1 : Fin (n + 2)) ≠
              (one_dimensional_total_variation_edge_right
                (one_dimensional_total_variation_even_edge i)).succ.succ := by
          simpa using
            (one_dimensional_total_variation_edge_right
              (one_dimensional_total_variation_even_edge i)).succ_succ_ne_one.symm
        simp [g, hleft, hright, hone_ne_left, hone_ne_right]
      have hhead_eq :
          x 1 + g 0 1 = (pair_difference_prox_point (lam : ℝ) (x 0) (x 1)) 1 := by
        dsimp only [g]
        rw [hhead_left, hhead_right]
        simp [sub_eq_add_neg, pair_difference_prox_point]
      have hcoord :
          x 1 + (g 0 1 + ∑ i : Fin (n / 2), (g i.succ) 1) =
            (pair_difference_prox_point (lam : ℝ) (x 0) (x 1)) 1 := by
        rw [htail_zero]
        simpa [add_assoc] using hhead_eq
      simpa [Finset.sum_apply, add_assoc] using hcoord
    · intro k
      rw [one_dimensional_total_variation_even_edge_prox_point_eq,
        one_dimensional_total_variation_even_edge_prox_point_eq, hsum_cast, Fin.sum_univ_succ]
      have hhead_zero : (g 0) k.succ.succ = 0 := by
        have hk_ne_zero : (k.succ.succ : Fin (n + 2)) ≠ 0 := by
          exact Fin.succ_ne_zero _
        have hk_ne_one : (k.succ.succ : Fin (n + 2)) ≠ 1 := by
          exact k.succ_succ_ne_one
        simp [g, hhead_left, hhead_right, hk_ne_zero, hk_ne_one]
      have htail_eq :
          ∑ i : Fin (n / 2), (g i.succ) k.succ.succ =
            ∑ i : Fin (n / 2),
              (let e := one_dimensional_total_variation_even_edge i
                let l := one_dimensional_total_variation_edge_left e
                let r := one_dimensional_total_variation_edge_right e
                pair_difference_prox_correction lam
                    ((toLp 2 (Fin.tail (Fin.tail x))) l)
                    ((toLp 2 (Fin.tail (Fin.tail x))) r) *
                  (((single l (1 : ℝ) : EuclideanSpace ℝ (Fin n)) - single r (1 : ℝ)) k)) := by
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
      have hcoord :
          x k.succ.succ + (g 0 k.succ.succ + ∑ i : Fin (n / 2), (g i.succ) k.succ.succ) =
            (one_dimensional_total_variation_even_edge_prox_point lam
              (toLp 2 (Fin.tail (Fin.tail x)))) k := by
        rw [hhead_zero]
        have htail_coord := congrArg (fun t : ℝ ↦ x k.succ.succ + t) htail_eq
        simpa [one_dimensional_total_variation_even_edge_prox_point_eq, Finset.sum_apply,
          Fin.tail, add_assoc, Pi.single_apply] using htail_coord
      simpa [Finset.sum_apply, add_assoc] using hcoord

/-- Helper for Proposition 12.11: the explicit proximal point is the canonical `prepend_pair`
reassembly of the head-pair proximal point and the recursive tail proximal point. -/
theorem one_dimensional_total_variation_even_edge_prox_point_eq_prepend_pair
    (lam : PosReal) (x : EuclideanSpace ℝ (Fin (n + 2))) :
    one_dimensional_total_variation_even_edge_prox_point lam x =
      prepend_pair
        (pair_difference_prox_point (lam : ℝ) (x 0) (x 1))
        (one_dimensional_total_variation_even_edge_prox_point lam
          (toLp 2 (Fin.tail (Fin.tail x)))) := by
  -- Repackage the coordinatewise `Fin.cons` description through the canonical builder.
  simpa [prepend_pair] using
    (one_dimensional_total_variation_even_edge_prox_point_eq_cons_pair_prox_point lam x)

/-- Helper for Proposition 12.11: in `ℝ^(n+2)`, the squared Euclidean distance splits into the
two head-coordinate contributions and the squared norm of the double-tail difference. -/
theorem one_dimensional_total_variation_double_tail_norm_sq_split
    (x u : EuclideanSpace ℝ (Fin (n + 2))) :
    ‖u - x‖ ^ (2 : ℕ) =
      (u 0 - x 0) ^ (2 : ℕ) + (u 1 - x 1) ^ (2 : ℕ) +
        ‖(toLp 2 (Fin.tail (Fin.tail u))) - (toLp 2 (Fin.tail (Fin.tail x)))‖ ^ (2 : ℕ) := by
  -- Expand the full norm and the tail norm, then identify the remaining sum with the double tail.
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

/-- Helper for Proposition 12.11: on `ℝ^(n+2)`, the proximal objective of the even-edge penalty
splits into the proximal objective of the first pair and the even-edge proximal objective on the
double tail. -/
theorem one_dimensional_total_variation_even_edge_proximal_objective_split
    (lam : PosReal) (x u : EuclideanSpace ℝ (Fin (n + 2))) :
    proximal_objective (@one_dimensional_total_variation_even_edge_penalty (n + 2) lam) x u =
      proximal_objective (pair_difference_penalty (lam : ℝ)) (toLp 2 ![x 0, x 1])
          (toLp 2 ![u 0, u 1]) +
        proximal_objective (@one_dimensional_total_variation_even_edge_penalty (n) lam)
          (toLp 2 (Fin.tail (Fin.tail x))) (toLp 2 (Fin.tail (Fin.tail u))) := by
  -- Rewrite the penalty and quadratic terms into the pair block plus the double-tail block.
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
    exact_mod_cast (show
      (1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ) =
        (1 / 2 : ℝ) * ‖(toLp 2 ![u 0, u 1]) - (toLp 2 ![x 0, x 1])‖ ^ (2 : ℕ) +
          (1 / 2 : ℝ) *
            ‖(toLp 2 (Fin.tail (Fin.tail u))) - (toLp 2 (Fin.tail (Fin.tail x)))‖ ^ (2 : ℕ) by
      nlinarith [one_dimensional_total_variation_double_tail_norm_sq_split x u, hpair])
  rw [hnorm]
  simp [add_assoc, add_left_comm, add_comm]

/-- Helper for Proposition 12.11: specializing the objective split to a rebuilt vector records
the source decomposition into a head pair problem and a recursive tail problem. -/
theorem one_dimensional_total_variation_even_edge_proximal_objective_prepend_pair
    (lam : PosReal) (x : EuclideanSpace ℝ (Fin (n + 2)))
    (p : EuclideanSpace ℝ (Fin 2)) (w : EuclideanSpace ℝ (Fin n)) :
    proximal_objective (@one_dimensional_total_variation_even_edge_penalty (n + 2) lam) x
        (prepend_pair p w) =
      proximal_objective (pair_difference_penalty (lam : ℝ)) (toLp 2 ![x 0, x 1]) p +
        proximal_objective (@one_dimensional_total_variation_even_edge_penalty (n) lam)
          (toLp 2 (Fin.tail (Fin.tail x))) w := by
  -- Specialize the split identity and then read back the reconstructed head pair and double tail.
  have hp : toLp 2 ![p 0, p 1] = p := by
    ext i
    fin_cases i <;> simp
  rw [one_dimensional_total_variation_even_edge_proximal_objective_split]
  simp [hp]

/-- Helper for Proposition 12.11: the pair proximal objective is always finite, so it can be
cancelled as a real summand in `EReal` inequalities. -/
theorem pair_difference_proximal_objective_eq_coe
    (lam : ℝ) (x u : EuclideanSpace ℝ (Fin 2)) :
    ∃ r : ℝ, proximal_objective (pair_difference_penalty lam) x u = (r : EReal) := by
  -- Unfold the pair penalty and the quadratic term; both are ordinary real quantities.
  refine ⟨lam * |u 0 - u 1| + (1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ), ?_⟩
  simp [proximal_objective_apply, pair_difference_penalty, EReal.coe_add]

/-- Helper for Proposition 12.11: the recursive even-edge proximal objective is always finite, so
it can be cancelled as a real summand in `EReal` inequalities. -/
theorem one_dimensional_total_variation_even_edge_proximal_objective_eq_coe
    (lam : PosReal) (x u : En) :
    ∃ r : ℝ,
      proximal_objective (one_dimensional_total_variation_even_edge_penalty lam) x u =
        (r : EReal) := by
  -- Unfold the even-edge penalty and the quadratic term; they are both coercions of real sums.
  refine ⟨(lam : ℝ) *
      ∑ i : Fin (n / 2), |D[n] u (one_dimensional_total_variation_even_edge i)| +
        (1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ), ?_⟩
  simp [proximal_objective_apply, one_dimensional_total_variation_even_edge_penalty_apply,
    EReal.coe_add]

/-- Helper for Proposition 12.11: on `ℝ^(n+2)`, proximal membership factorizes into the head pair
problem and the recursive double-tail problem. -/
theorem mem_prox_one_dimensional_total_variation_even_edge_penalty_iff_head_pair_double_tail
    (lam : PosReal) (x u : EuclideanSpace ℝ (Fin (n + 2))) :
    u ∈ prox[@one_dimensional_total_variation_even_edge_penalty (n + 2) lam] x ↔
      toLp 2 ![u 0, u 1] ∈ prox[pair_difference_penalty (lam : ℝ)] (toLp 2 ![x 0, x 1]) ∧
        toLp 2 (Fin.tail (Fin.tail u)) ∈
          prox[@one_dimensional_total_variation_even_edge_penalty (n) lam]
            (toLp 2 (Fin.tail (Fin.tail x))) := by
  constructor
  · intro hu
    -- Freeze the head pair and vary only the tail block to read off recursive optimality.
    have htail_min :
        toLp 2 (Fin.tail (Fin.tail u)) ∈
          prox[@one_dimensional_total_variation_even_edge_penalty (n) lam]
            (toLp 2 (Fin.tail (Fin.tail x))) := by
      rw [mem_proximal_mapping_iff] at hu ⊢
      rw [isMinOn_univ_iff] at hu ⊢
      intro w
      let v : EuclideanSpace ℝ (Fin (n + 2)) := prepend_pair (toLp 2 ![u 0, u 1]) w
      have huv := hu v
      have hu_split :=
        @one_dimensional_total_variation_even_edge_proximal_objective_split (n) lam x u
      have hv_split :
          proximal_objective
              (@one_dimensional_total_variation_even_edge_penalty (n + 2) lam) x v =
            proximal_objective (pair_difference_penalty (lam : ℝ)) (toLp 2 ![x 0, x 1])
                (toLp 2 ![u 0, u 1]) +
              proximal_objective
                (@one_dimensional_total_variation_even_edge_penalty (n) lam)
                (toLp 2 (Fin.tail (Fin.tail x))) w := by
        simpa [v] using
          (@one_dimensional_total_variation_even_edge_proximal_objective_prepend_pair
            (n) lam x (toLp 2 ![u 0, u 1]) w)
      rw [hu_split, hv_split] at huv
      obtain ⟨r, hr⟩ :=
        pair_difference_proximal_objective_eq_coe
          (lam : ℝ) (toLp 2 ![x 0, x 1]) (toLp 2 ![u 0, u 1])
      rw [hr] at huv
      exact ((EReal.addLECancellable_coe r).add_le_add_iff_left).mp huv
    -- Freeze the tail block and vary only the head pair to read off the pairwise proximality.
    have hhead_min :
        toLp 2 ![u 0, u 1] ∈ prox[pair_difference_penalty (lam : ℝ)] (toLp 2 ![x 0, x 1]) := by
      rw [mem_proximal_mapping_iff] at hu ⊢
      rw [isMinOn_univ_iff] at hu ⊢
      intro p
      let v : EuclideanSpace ℝ (Fin (n + 2)) :=
        prepend_pair p (toLp 2 (Fin.tail (Fin.tail u)))
      have huv := hu v
      have hu_split :=
        @one_dimensional_total_variation_even_edge_proximal_objective_split (n) lam x u
      have hv_split :
          proximal_objective
              (@one_dimensional_total_variation_even_edge_penalty (n + 2) lam) x v =
            proximal_objective (pair_difference_penalty (lam : ℝ)) (toLp 2 ![x 0, x 1]) p +
              proximal_objective
                (@one_dimensional_total_variation_even_edge_penalty (n) lam)
                (toLp 2 (Fin.tail (Fin.tail x))) (toLp 2 (Fin.tail (Fin.tail u))) := by
        simpa [v] using
          (@one_dimensional_total_variation_even_edge_proximal_objective_prepend_pair
            (n) lam x p (toLp 2 (Fin.tail (Fin.tail u))))
      rw [hu_split, hv_split] at huv
      obtain ⟨r, hr⟩ :=
        @one_dimensional_total_variation_even_edge_proximal_objective_eq_coe
          (n) lam (toLp 2 (Fin.tail (Fin.tail x))) (toLp 2 (Fin.tail (Fin.tail u)))
      rw [hr] at huv
      exact ((EReal.addLECancellable_coe r).add_le_add_iff_right).mp huv
    exact ⟨hhead_min, htail_min⟩
  · rintro ⟨hhead_min, htail_min⟩
    rw [mem_proximal_mapping_iff]
    rw [isMinOn_univ_iff]
    intro v
    -- Once both blocks are separately minimal, add the two block inequalities after splitting.
    have hsplit_u :=
      @one_dimensional_total_variation_even_edge_proximal_objective_split (n) lam x u
    have hsplit_v :=
      @one_dimensional_total_variation_even_edge_proximal_objective_split (n) lam x v
    rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hhead_min htail_min
    rw [hsplit_u, hsplit_v]
    have hhead_le := hhead_min (toLp 2 ![v 0, v 1])
    have htail_le := htail_min (toLp 2 (Fin.tail (Fin.tail v)))
    exact add_le_add hhead_le htail_le

-- Proof sketch: use the separability of `one_dimensional_total_variation_even_edge_penalty lam`
-- across the
-- disjoint even-start pairs, apply Proposition 12.10's two-coordinate proximal formula on each
-- block, and reassemble the unique minimizer as the sum of the independent pairwise corrections.
/-- Proposition 12.11: for the first split total-variation block
`g₁(x) = λ ∑ |x_(2 i) - x_(2 i + 1)|`, realized on `Fin n` as the even-start adjacent pairs
`(0,1), (2,3), ...`, the proximal mapping is the singleton containing the point obtained by the
explicit pairwise correction formula on each such pair, for the chapter's positive parameter
`lam : PosReal`. -/
theorem prox_one_dimensional_total_variation_even_edge_penalty_eq_singleton
    (lam : PosReal) (x : En) :
    prox[one_dimensional_total_variation_even_edge_penalty lam] x =
      {one_dimensional_total_variation_even_edge_prox_point lam x} := by
  -- Prove the singleton formula by peeling off one disjoint pair at a time.
  induction n using Nat.twoStepInduction with
  | zero =>
      have hpen0 :
          @one_dimensional_total_variation_even_edge_penalty (0) lam =
            (0 : EuclideanSpace ℝ (Fin 0) → EReal) := by
        funext u
        simp [one_dimensional_total_variation_even_edge_penalty_apply]
      calc
        prox[@one_dimensional_total_variation_even_edge_penalty (0) lam] x = {x} := by
          rw [hpen0]
          simpa using prox_zero_eq_singleton x
        _ = {@one_dimensional_total_variation_even_edge_prox_point (0) lam x} := by
          congr 1
          simp [one_dimensional_total_variation_even_edge_prox_point_eq]
  | one =>
      have hpen1 :
          @one_dimensional_total_variation_even_edge_penalty (1) lam =
            (0 : EuclideanSpace ℝ (Fin 1) → EReal) := by
        funext u
        simp [one_dimensional_total_variation_even_edge_penalty_apply]
      calc
        prox[@one_dimensional_total_variation_even_edge_penalty (1) lam] x = {x} := by
          rw [hpen1]
          simpa using prox_zero_eq_singleton x
        _ = {@one_dimensional_total_variation_even_edge_prox_point (1) lam x} := by
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
                prox[@one_dimensional_total_variation_even_edge_penalty (n) lam]
                  (toLp 2 (Fin.tail (Fin.tail x))) := by
          exact
            (@mem_prox_one_dimensional_total_variation_even_edge_penalty_iff_head_pair_double_tail
              (n) lam x u).1 hu
        rcases hu_factor with ⟨hhead_min, htail_min⟩
        have hhead_eq :
            toLp 2 ![u 0, u 1] = pair_difference_prox_point (lam : ℝ) (x 0) (x 1) := by
          rw [prox_pair_difference_penalty_eq_singleton (lam : ℝ) lam.2.le (x 0) (x 1)] at hhead_min
          simpa using hhead_min
        have htail_eq :
            toLp 2 (Fin.tail (Fin.tail u)) =
              @one_dimensional_total_variation_even_edge_prox_point (n) lam
                (toLp 2 (Fin.tail (Fin.tail x))) := by
          rw [ih (toLp 2 (Fin.tail (Fin.tail x)))] at htail_min
          simpa using htail_min
        calc
          u =
              prepend_pair
                (pair_difference_prox_point (lam : ℝ) (x 0) (x 1))
                (@one_dimensional_total_variation_even_edge_prox_point (n) lam
                  (toLp 2 (Fin.tail (Fin.tail x)))) := by
            rw [← prepend_pair_reconstruct u]
            rw [hhead_eq, htail_eq]
          _ = @one_dimensional_total_variation_even_edge_prox_point (n + 2) lam x := by
            symm
            exact
              @one_dimensional_total_variation_even_edge_prox_point_eq_prepend_pair
                (n) lam x
      · intro hu
        rw [Set.mem_singleton_iff] at hu
        subst hu
        apply
          (@mem_prox_one_dimensional_total_variation_even_edge_penalty_iff_head_pair_double_tail
            (n) lam x
            (@one_dimensional_total_variation_even_edge_prox_point (n + 2) lam x)).2
        have hhead_min :
            toLp 2
                ![(@one_dimensional_total_variation_even_edge_prox_point (n + 2) lam x) 0,
                  (@one_dimensional_total_variation_even_edge_prox_point (n + 2) lam x) 1] ∈
              prox[pair_difference_penalty (lam : ℝ)] (toLp 2 ![x 0, x 1]) := by
          rw [@one_dimensional_total_variation_even_edge_prox_point_eq_prepend_pair (n) lam x]
          rw [prox_pair_difference_penalty_eq_singleton (lam : ℝ) lam.2.le (x 0) (x 1)]
          ext i
          fin_cases i <;> simp [pair_difference_prox_point]
        have htail_min :
            toLp 2
                (Fin.tail
                  (Fin.tail
                    (@one_dimensional_total_variation_even_edge_prox_point (n + 2) lam x))) ∈
              prox[@one_dimensional_total_variation_even_edge_penalty (n) lam]
                (toLp 2 (Fin.tail (Fin.tail x))) := by
          rw [@one_dimensional_total_variation_even_edge_prox_point_eq_prepend_pair (n) lam x]
          rw [ih (toLp 2 (Fin.tail (Fin.tail x)))]
          simp
        exact ⟨hhead_min, htail_min⟩

end
