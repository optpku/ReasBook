/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Definition_12_14
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Definition_12_19

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

noncomputable section

section

variable {n : ℕ}

local notation "En" => EuclideanSpace ℝ (Fin (n + 1))

/- Definition 12.20 is a `bridge/view`: Definition 12.19 already owns the adjacent-edge
one-dimensional total-variation penalty and its denoising objective, while Definition 12.14
already recalls the canonical finite-sum/composite owner layer.

Domain sampling in the surrounding Chapter 12 API identifies:
- `source-facing`: the alternating even-edge and odd-edge pieces of the one-dimensional TV
  regularizer;
- `core/canonical`: `one_dimensional_total_variation` and
  `one_dimensional_total_variation_denoising_objective` from Definition 12.19;
- `core/canonical`: `finite_sum_objective` and `composite_model_objective`, recalled in
  Definition 12.14;
- `bridge/view`: the two-block family formed from the even-edge and odd-edge penalties.

Primitive data here are rebuilt locally from Definition 12.19: this file defines the even-start
and odd-start adjacent-edge subfamilies of `D[n + 1]` together with their split penalties, then
packages those canonical split blocks into the later finite-sum bridge API relating
Definition 12.19 to Definition 12.14. -/

-- Proof sketch: if `i < (n + 1) / 2`, then `2 i < n`; this is exactly the range condition for
-- the even-start adjacent edges of `D[n + 1]`.
/-- Helper for Definition 12.20: the `i`-th even-starting adjacent edge gives a valid edge index
for the one-dimensional TV difference operator on `ℝ^(n+1)`. -/
theorem one_dimensional_total_variation_split_even_edge_lt
    (i : Fin ((n + 1) / 2)) :
    2 * i.1 < n := by
  -- The floor bound on `i` is enough to keep the doubled index inside the `n` edges.
  have hi : i.1 < (n + 1) / 2 := i.is_lt
  omega

/-- Helper for Definition 12.20: the `i`-th even-starting adjacent edge of `D[n + 1]`. -/
def one_dimensional_total_variation_split_even_edge
    (i : Fin ((n + 1) / 2)) : Fin n :=
  ⟨2 * i.1, one_dimensional_total_variation_split_even_edge_lt i⟩

/-- Helper for Definition 12.20: the even-start edge index has underlying value `2 i`. -/
@[simp] theorem one_dimensional_total_variation_split_even_edge_val
    (i : Fin ((n + 1) / 2)) :
    (one_dimensional_total_variation_split_even_edge i).1 = 2 * i.1 :=
  rfl

-- Proof sketch: if `i < n / 2`, then `2 i + 1 < n`; this is exactly the range condition for
-- the odd-start adjacent edges of `D[n + 1]`.
/-- Helper for Definition 12.20: the `i`-th odd-starting adjacent edge gives a valid edge index
for the one-dimensional TV difference operator on `ℝ^(n+1)`. -/
theorem one_dimensional_total_variation_split_odd_edge_lt
    (i : Fin (n / 2)) :
    2 * i.1 + 1 < n := by
  -- The floor bound on `i` is enough to keep the shifted doubled index inside the `n` edges.
  have hi : i.1 < n / 2 := i.is_lt
  omega

/-- Helper for Definition 12.20: the `i`-th odd-starting adjacent edge of `D[n + 1]`. -/
def one_dimensional_total_variation_split_odd_edge
    (i : Fin (n / 2)) : Fin n :=
  ⟨2 * i.1 + 1, one_dimensional_total_variation_split_odd_edge_lt i⟩

/-- Helper for Definition 12.20: the odd-start edge index has underlying value `2 i + 1`. -/
@[simp] theorem one_dimensional_total_variation_split_odd_edge_val
    (i : Fin (n / 2)) :
    (one_dimensional_total_variation_split_odd_edge i).1 = 2 * i.1 + 1 :=
  rfl

/-- Helper for Definition 12.20: the first split block
`g₁(x) = λ ∑ |x_(2 i) - x_(2 i + 1)|`, written as the sum over the even-start adjacent edges of
`D[n + 1]`. -/
def one_dimensional_total_variation_split_even_edge_penalty
    (lam : PosReal) : En → EReal :=
  fun x ↦
    (((lam : ℝ) *
        ∑ i : Fin ((n + 1) / 2),
          |D[n + 1] x (one_dimensional_total_variation_split_even_edge i)| : ℝ) : EReal)

-- Proof sketch: unfold the split even-edge penalty; the displayed sum is its defining formula.
/-- Helper for Definition 12.20: evaluating the even-start split penalty gives the scaled sum over
the even-start adjacent edges. -/
@[simp] theorem one_dimensional_total_variation_split_even_edge_penalty_apply
    (lam : PosReal) (x : En) :
    one_dimensional_total_variation_split_even_edge_penalty lam x =
      (((lam : ℝ) *
          ∑ i : Fin ((n + 1) / 2),
            |D[n + 1] x (one_dimensional_total_variation_split_even_edge i)| : ℝ) : EReal) :=
  rfl

/-- Helper for Definition 12.20: the second split block
`g₂(x) = λ ∑ |x_(2 i + 1) - x_(2 i + 2)|`, written as the sum over the odd-start adjacent edges
of `D[n + 1]`. -/
def one_dimensional_total_variation_split_odd_edge_penalty
    (lam : PosReal) : En → EReal :=
  fun x ↦
    (((lam : ℝ) *
        ∑ i : Fin (n / 2),
          |D[n + 1] x (one_dimensional_total_variation_split_odd_edge i)| : ℝ) : EReal)

-- Proof sketch: unfold the split odd-edge penalty; the displayed sum is its defining formula.
/-- Helper for Definition 12.20: evaluating the odd-start split penalty gives the scaled sum over
the odd-start adjacent edges. -/
@[simp] theorem one_dimensional_total_variation_split_odd_edge_penalty_apply
    (lam : PosReal) (x : En) :
    one_dimensional_total_variation_split_odd_edge_penalty lam x =
      (((lam : ℝ) *
          ∑ i : Fin (n / 2),
            |D[n + 1] x (one_dimensional_total_variation_split_odd_edge i)| : ℝ) : EReal) :=
  rfl

local notation "G[" lam "]" =>
  (![one_dimensional_total_variation_split_even_edge_penalty lam,
    one_dimensional_total_variation_split_odd_edge_penalty lam] :
      Fin 2 → En → EReal)

/-- Evaluating the canonical finite-sum aggregate of the two split penalties gives the sum of the
even-edge and odd-edge blocks. -/
@[simp] theorem one_dimensional_total_variation_split_penalties_apply
    (lam : PosReal) (x : En) :
    finite_sum_objective G[lam] x =
      one_dimensional_total_variation_split_even_edge_penalty lam x +
        one_dimensional_total_variation_split_odd_edge_penalty lam x := by
  -- The two-block finite sum is exactly the sum of the two split penalties.
  rw [finite_sum_objective_apply, Fin.sum_univ_two]
  simp

/-- Helper for Definition 12.20: the even-edge and odd-edge families together enumerate all
adjacent-edge indices. -/
private def alternating_edge_index :
    Fin ((n + 1) / 2) ⊕ Fin (n / 2) → Fin n :=
  Sum.elim
    (fun i ↦ one_dimensional_total_variation_split_even_edge i)
    (fun i ↦ one_dimensional_total_variation_split_odd_edge i)

/-- Helper for Definition 12.20: the parity split of adjacent-edge indices is bijective. -/
private theorem alternating_edge_index_bijective :
    Function.Bijective (@alternating_edge_index n) := by
  constructor
  · intro a b hab
    -- Compare the two parity branches separately, reducing each case to arithmetic on values.
    cases a with
    | inl i =>
        cases b with
        | inl j =>
            -- Equal even-branch images force the same halved edge index.
            have hijVal : 2 * i.1 = 2 * j.1 := by
              simpa [alternating_edge_index] using congrArg Fin.val hab
            have hij : i = j := by
              apply Fin.ext
              omega
            simp [hij]
        | inr j =>
            -- Route correction: the mixed branch is impossible because an even number is not odd.
            have hijVal : 2 * i.1 = 2 * j.1 + 1 := by
              simpa [alternating_edge_index] using congrArg Fin.val hab
            have : False := by
              omega
            exact False.elim this
    | inr i =>
        cases b with
        | inl j =>
            -- The same parity contradiction rules out the other mixed branch.
            have hijVal : 2 * i.1 + 1 = 2 * j.1 := by
              simpa [alternating_edge_index] using congrArg Fin.val hab
            have : False := by
              omega
            exact False.elim this
        | inr j =>
            -- Equal odd-branch images again force the same halved edge index.
            have hijVal : 2 * i.1 + 1 = 2 * j.1 + 1 := by
              simpa [alternating_edge_index] using congrArg Fin.val hab
            have hij : i = j := by
              apply Fin.ext
              omega
            simp [hij]
  · intro e
    -- Reconstruct the unique preimage by splitting the edge index into even and odd cases.
    rcases Nat.even_or_odd e.1 with he | ho
    · rcases even_iff_exists_two_mul.mp he with ⟨k, hk⟩
      -- The even case lands in the left summand with index `k`.
      refine ⟨Sum.inl ⟨k, ?_⟩, ?_⟩
      · omega
      · apply Fin.ext
        simpa [alternating_edge_index] using hk.symm
    · rcases odd_iff_exists_bit1.mp ho with ⟨k, hk⟩
      -- The odd case lands in the right summand with index `k`.
      refine ⟨Sum.inr ⟨k, ?_⟩, ?_⟩
      · omega
      · apply Fin.ext
        simpa [alternating_edge_index] using hk.symm

/-- Helper for Definition 12.20: the absolute first-difference sum splits into its even-start and
odd-start edge blocks. -/
theorem adjacent_edge_abs_sum_eq_even_edge_abs_sum_add_odd_edge_abs_sum
    (x : En) :
    (∑ e : Fin n, |D[n + 1] x e|) =
      (∑ i : Fin ((n + 1) / 2),
        |D[n + 1] x (one_dimensional_total_variation_split_even_edge i)|) +
      (∑ i : Fin (n / 2),
        |D[n + 1] x (one_dimensional_total_variation_split_odd_edge i)|) := by
  -- Reindex the full adjacent-edge sum by the parity partition of the edge set.
  calc
    (∑ e : Fin n, |D[n + 1] x e|) =
        ∑ s : Fin ((n + 1) / 2) ⊕ Fin (n / 2),
          |D[n + 1] x (alternating_edge_index s)| := by
          symm
          exact Fintype.sum_bijective
            (@alternating_edge_index n)
            (@alternating_edge_index_bijective n)
            (fun s ↦ |D[n + 1] x ((@alternating_edge_index n) s)|)
            (fun e ↦ |D[n + 1] x e|)
            (fun _ ↦ rfl)
    _ =
        (∑ i : Fin ((n + 1) / 2),
          |D[n + 1] x (one_dimensional_total_variation_split_even_edge i)|) +
        (∑ i : Fin (n / 2),
          |D[n + 1] x (one_dimensional_total_variation_split_odd_edge i)|) := by
          rw [Fintype.sum_sum_type]
          simp [alternating_edge_index]

/-- Helper for Definition 12.20: the total-variation seminorm is the sum of the even-start and
odd-start edge absolute-value blocks. -/
theorem one_dimensional_total_variation_eq_even_edge_abs_sum_add_odd_edge_abs_sum
    (x : En) :
    one_dimensional_total_variation x =
      (∑ i : Fin ((n + 1) / 2),
        |D[n + 1] x (one_dimensional_total_variation_split_even_edge i)|) +
      (∑ i : Fin (n / 2),
        |D[n + 1] x (one_dimensional_total_variation_split_odd_edge i)|) := by
  -- Expand the `ℓ¹` norm of the first-difference vector and apply the parity split.
  rw [one_dimensional_total_variation, EuclideanSpace.l1Norm_eq_sum_abs]
  exact adjacent_edge_abs_sum_eq_even_edge_abs_sum_add_odd_edge_abs_sum x

/-- The full one-dimensional total-variation penalty splits into the sum of the even-edge and
odd-edge penalties. -/
theorem one_dimensional_total_variation_penalty_eq_split_penalties
    (lam : PosReal) (x : En) :
    ↑((lam : ℝ) * one_dimensional_total_variation x) =
      one_dimensional_total_variation_split_even_edge_penalty lam x +
        one_dimensional_total_variation_split_odd_edge_penalty lam x := by
  -- Rewrite both split penalties into their defining scaled edge sums.
  rw [one_dimensional_total_variation_split_even_edge_penalty_apply,
    one_dimensional_total_variation_split_odd_edge_penalty_apply, ← EReal.coe_add]
  -- Collapse the total-variation term to the same pair of edge blocks before distributing `λ`.
  congr 1
  rw [one_dimensional_total_variation_eq_even_edge_abs_sum_add_odd_edge_abs_sum]
  rw [mul_add]

/-- Definition 12.20 [Splitting of the one-dimensional total variation denoising objective]:
the one-dimensional total-variation denoising objective is exactly the Chapter 12.14
two-block composite objective whose block family is given by the even-edge and odd-edge split
penalties. -/
theorem one_dimensional_total_variation_denoising_fits_dual_block_model
    (d : En) (lam : PosReal) :
    one_dimensional_total_variation_denoising_objective d lam =
      composite_model_objective
        (denoising_data_fidelity d)
        (finite_sum_objective G[lam]) := by
  ext x
  rw [one_dimensional_total_variation_denoising_objective_apply,
    composite_model_objective_apply]
  rw [one_dimensional_total_variation_penalty_eq_split_penalties,
    one_dimensional_total_variation_split_penalties_apply]
  rfl

/-- Pointwise form of Definition 12.20: evaluating the one-dimensional total-variation denoising
objective gives the quadratic fidelity term plus the even-edge and odd-edge split penalties. -/
theorem one_dimensional_total_variation_denoising_objective_apply_eq_split_penalties
    (d x : En) (lam : PosReal) :
    one_dimensional_total_variation_denoising_objective d lam x =
      denoising_data_fidelity d x +
        one_dimensional_total_variation_split_even_edge_penalty lam x +
        one_dimensional_total_variation_split_odd_edge_penalty lam x := by
  rw [one_dimensional_total_variation_denoising_fits_dual_block_model,
    composite_model_objective_apply, one_dimensional_total_variation_split_penalties_apply]
  simp [add_assoc]

end
