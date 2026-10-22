/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_6
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Example_6_50

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
open InnerProductSpace (toDualMap)
open WithLp (toLp)

noncomputable section

section

variable {ι : Type*} [Fintype ι]

local notation "E" => EuclideanSpace ℝ ι
local notation "unitWeights" => (fun _ : ι ↦ (1 : NNReal))
local notation "unitBox" => (fun _ : ι ↦ (1 : ENNReal))

/- Example 6.51 is `source-facing`: the textbook object is the sum of the `k` largest coordinate
absolute values on `ℝ^n`. Domain sampling in the same chapter shows that the right owner split is:
- `source-facing`: the new function `sum_k_largest_abs`,
- `bridge/view`: Example 6.50's `sum_of_k_largest_values`, applied to the coordinatewise absolute
  value vector,
- `core/canonical`: Definition 6.6's `weighted_l1_box_constraint_set`, together with the chapter
  owners `support_function`, `prox[...]`, and `metricProjection`.
The local file should therefore not re-own the dual constraint set as a bespoke predicate. -/

/-- The function sending `x` to the sum of its `k` largest coordinate absolute values. -/
def sum_k_largest_abs (k : ℕ) (x : E) : ℝ :=
  sum_of_k_largest_values k (toLp 2 fun i ↦ |x i|)

section

variable (k : ℕ)

local notation "C" => weighted_l1_box_constraint_set unitWeights unitBox (k : ℝ)
private theorem hC_nonempty :
    (weighted_l1_box_constraint_set unitWeights unitBox (k : ℝ) : Set E).Nonempty :=
  weighted_l1_box_constraint_set_nonempty_of_nonneg
    unitWeights unitBox (k : ℝ) (by exact_mod_cast Nat.zero_le k)
private theorem hC_closed :
    IsClosed (weighted_l1_box_constraint_set unitWeights unitBox (k : ℝ) : Set E) :=
  weighted_l1_box_constraint_set_isClosed unitWeights unitBox (k : ℝ)
private theorem hC_convex :
    Convex ℝ (weighted_l1_box_constraint_set unitWeights unitBox (k : ℝ) : Set E) :=
  weighted_l1_box_constraint_set_convex unitWeights unitBox (k : ℝ)

private def constraintProjectionPoint (y : E) : E :=
  (metricProjection C
    (hC_nonempty k)
    (hC_closed k)
    (hC_convex k)
    y : E)

local notation "P" => constraintProjectionPoint k

/-- Helper for Example 6.51: if `k` does not exceed the number of coordinates, any vector with
entries in `[0, 1]` and total mass at most `k` can be enlarged coordinatewise to one with total
mass exactly `k`. -/
private theorem exists_capped_simplex_extension
    {n k : ℕ} (hk : k ≤ n) (b : Fin n → ℝ)
    (hb0 : ∀ j, 0 ≤ b j) (hb1 : ∀ j, b j ≤ 1)
    (hsum : ∑ j : Fin n, b j ≤ k) :
    ∃ c : Fin n → ℝ,
      (∑ j : Fin n, c j) = k ∧ ∀ j, 0 ≤ c j ∧ c j ≤ 1 ∧ b j ≤ c j := by
  induction n generalizing k with
  | zero =>
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      subst hk0
      refine ⟨b, ?_, ?_⟩
      · have hsum0 : ∑ j : Fin 0, b j ≤ (0 : ℝ) := by
          simpa using hsum
        have hnonneg : (0 : ℝ) ≤ ∑ j : Fin 0, b j := by
          exact Finset.sum_nonneg fun j _ ↦ hb0 j
        have hs : (∑ j : Fin 0, b j) = (0 : ℝ) := le_antisymm hsum0 hnonneg
        simpa using hs
      · intro j
        exact False.elim (Fin.elim0 j)
  | succ n ih =>
      cases k with
      | zero =>
          refine ⟨b, ?_, ?_⟩
          · have hsum0 : ∑ j : Fin (n + 1), b j ≤ (0 : ℝ) := by
              simpa using hsum
            have hnonneg : (0 : ℝ) ≤ ∑ j : Fin (n + 1), b j := by
              exact Finset.sum_nonneg fun j _ ↦ hb0 j
            have hs : (∑ j : Fin (n + 1), b j) = (0 : ℝ) := le_antisymm hsum0 hnonneg
            simpa using hs
          · intro j
            exact ⟨hb0 j, hb1 j, le_rfl⟩
      | succ k =>
          let bRest : Fin n → ℝ := fun j ↦ b j.succ
          have hbRest0 : ∀ j, 0 ≤ bRest j := by
            intro j
            exact hb0 j.succ
          have hbRest1 : ∀ j, bRest j ≤ 1 := by
            intro j
            exact hb1 j.succ
          have hsum_split : b 0 + ∑ j : Fin n, bRest j ≤ k + 1 := by
            simpa [bRest, Fin.sum_univ_succ, add_comm, add_assoc] using hsum
          by_cases hsmall : ∑ j : Fin n, bRest j ≤ k
          · have hk_rest : k ≤ n := Nat.le_of_succ_le_succ hk
            obtain ⟨cRest, hcRest_sum, hcRest_bounds⟩ :=
              ih hk_rest bRest hbRest0 hbRest1 hsmall
            refine ⟨Fin.cons 1 cRest, ?_, ?_⟩
            · simp [Fin.sum_univ_succ, hcRest_sum, add_comm]
            · -- Keep the tail from the induction hypothesis and spend the new unit of mass at `0`.
              rw [Fin.forall_fin_succ]
              constructor
              · constructor
                · norm_num
                constructor
                · norm_num
                · exact hb1 0
              · intro j
                simpa [bRest, Fin.cons_succ] using hcRest_bounds j
          · have hlarge : (k : ℝ) < ∑ j : Fin n, bRest j := by
              linarith
            let c0 : ℝ := (k + 1 : ℝ) - ∑ j : Fin n, bRest j
            refine ⟨Fin.cons c0 bRest, ?_, ?_⟩
            · -- In the remaining case, the tail already carries more than `k`, so the head is the
              -- unique fractional amount needed to make the total exactly `k + 1`.
              rw [Fin.sum_univ_succ]
              simp [Fin.cons_zero, Fin.cons_succ, c0, bRest]
            · rw [Fin.forall_fin_succ]
              constructor
              · have hrest_le : ∑ j : Fin n, bRest j ≤ k + 1 := by
                  have hb00 : 0 ≤ b 0 := hb0 0
                  linarith [hsum_split]
                have hc0_nonneg : 0 ≤ c0 := by
                  dsimp [c0]
                  linarith
                have hc0_le_one : c0 ≤ 1 := by
                  dsimp [c0]
                  linarith
                have hb0_le : b 0 ≤ c0 := by
                  dsimp [c0]
                  linarith [hsum_split]
                exact ⟨hc0_nonneg, hc0_le_one, hb0_le⟩
              · intro j
                exact ⟨hbRest0 j, hbRest1 j, le_rfl⟩

/-- Helper for Example 6.51: once `k` is at least the number of coordinates, the sum of the `k`
largest absolute values stops changing. -/
private theorem sum_k_largest_abs_stabilizes_above_card
    (hk : Fintype.card ι ≤ k) (x : E) :
    sum_k_largest_abs k x = sum_k_largest_abs (Fintype.card ι) x := by
  -- Above the ambient dimension, `take k` already captures the entire sorted coordinate list.
  unfold sum_k_largest_abs sum_of_k_largest_values
  change
    (List.take k
        ((List.ofFn fun i : Fin (Fintype.card ι) ↦
            |x ((Fintype.equivFin ι).symm i)|).mergeSort
          fun x₁ x₂ ↦ decide (x₁ ≥ x₂))).sum =
      (List.take (Fintype.card ι)
        ((List.ofFn fun i : Fin (Fintype.card ι) ↦
            |x ((Fintype.equivFin ι).symm i)|).mergeSort
          fun x₁ x₂ ↦ decide (x₁ ≥ x₂))).sum
  have htakek :
      List.take k
          ((List.ofFn fun i : Fin (Fintype.card ι) ↦
              |x ((Fintype.equivFin ι).symm i)|).mergeSort
            fun x₁ x₂ ↦ decide (x₁ ≥ x₂)) =
        ((List.ofFn fun i : Fin (Fintype.card ι) ↦
            |x ((Fintype.equivFin ι).symm i)|).mergeSort
          fun x₁ x₂ ↦ decide (x₁ ≥ x₂)) := by
    apply (List.take_eq_self_iff _).2
    simp [List.length_mergeSort, hk]
  have htaken :
      List.take (Fintype.card ι)
          ((List.ofFn fun i : Fin (Fintype.card ι) ↦
              |x ((Fintype.equivFin ι).symm i)|).mergeSort
            fun x₁ x₂ ↦ decide (x₁ ≥ x₂)) =
        ((List.ofFn fun i : Fin (Fintype.card ι) ↦
            |x ((Fintype.equivFin ι).symm i)|).mergeSort
          fun x₁ x₂ ↦ decide (x₁ ≥ x₂)) := by
    apply (List.take_eq_self_iff _).2
    simp [List.length_mergeSort]
  rw [htakek, htaken]

/-- Helper for Example 6.51: above the ambient dimension, the `ℓ¹` bound in the unit box is
redundant. -/
private theorem unit_box_l1_constraint_stabilizes_above_card
    (hk : Fintype.card ι ≤ k) :
    (weighted_l1_box_constraint_set unitWeights unitBox (k : ℝ) : Set E) =
      weighted_l1_box_constraint_set unitWeights unitBox (Fintype.card ι : ℝ) := by
  ext z
  rw [mem_weighted_l1_box_constraint_set_iff, mem_weighted_l1_box_constraint_set_iff]
  constructor
  · intro hz
    refine ⟨?_, hz.2⟩
    -- Under the unit-box constraints, the coordinatewise absolute values sum to at most `card ι`.
    calc
      ∑ i : ι, (1 : ℝ) * |z i| = ∑ i : ι, |z i| := by
        simp
      _ ≤ ∑ i : ι, (1 : ℝ) := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        have hi1 : ENNReal.ofReal |z i| ≤ (1 : ENNReal) := hz.2 i
        norm_num at hi1
        exact hi1
      _ = Fintype.card ι := by simp
  · intro hz
    exact ⟨le_trans hz.1 (by exact_mod_cast hk), hz.2⟩

/-- Helper for Example 6.51: when `k ≤ card`, every feasible point of the unit-box `ℓ¹`
constraint set gives a pairing bounded above by the support value coming from Example 6.50 applied
to `|x|`. -/
private theorem support_function_constraint_set_le_sum_k_largest_abs_of_le_card
    (hk : k ≤ Fintype.card ι) (x : E) :
    support_function C (toDualMap ℝ E x) ≤ (sum_k_largest_abs k x : EReal) := by
  let absx : E := toLp 2 fun i ↦ |x i|
  have habs :
      (sum_k_largest_abs k x : EReal) =
        support_function (sum_of_k_largest_constraint_set ι k) (toDualMap ℝ E absx) := by
    -- Rewrite the source-facing absolute-value sum through Example 6.50.
    simpa [sum_k_largest_abs, absx] using
      (sum_of_k_largest_values_eq_support_function_constraint_set (ι := ι) hk absx)
  rw [support_function_apply]
  apply sSup_le
  rintro _ ⟨z, hz, rfl⟩
  rw [mem_weighted_l1_box_constraint_set_iff] at hz
  let b : Fin (Fintype.card ι) → ℝ := fun j ↦ |z ((Fintype.equivFin ι).symm j)|
  have hb0 : ∀ j, 0 ≤ b j := by
    intro j
    exact abs_nonneg _
  have hb1 : ∀ j, b j ≤ 1 := by
    intro j
    have hj : ENNReal.ofReal |z ((Fintype.equivFin ι).symm j)| ≤ (1 : ENNReal) :=
      hz.2 ((Fintype.equivFin ι).symm j)
    norm_num at hj
    simpa [b] using hj
  have hsum_b : ∑ j : Fin (Fintype.card ι), b j ≤ k := by
    -- Reindex the absolute-value sum into `Fin (card ι)` so the extension lemma applies.
    have hzsum : ∑ i : ι, |z i| ≤ k := by
      simpa using hz.1
    calc
      ∑ j : Fin (Fintype.card ι), b j
          = ∑ i : ι, |z i| := by
              exact
                Fintype.sum_equiv (Fintype.equivFin ι).symm
                  (fun j : Fin (Fintype.card ι) ↦ b j)
                  (fun i : ι ↦ |z i|)
                  (fun j ↦ by simp [b])
      _ ≤ k := hzsum
  obtain ⟨c, hc_sum, hc_bounds⟩ :=
    exists_capped_simplex_extension hk b hb0 hb1 hsum_b
  let y : E := toLp 2 fun i ↦ c (Fintype.equivFin ι i)
  have hy_mem : y ∈ sum_of_k_largest_constraint_set ι k := by
    constructor
    · -- The extension lemma ensures the transported vector has total mass exactly `k`.
      calc
        ∑ i : ι, y i
            = ∑ j : Fin (Fintype.card ι), c j := by
                exact
                  Fintype.sum_equiv (Fintype.equivFin ι)
                    (fun i : ι ↦ y i)
                    (fun j : Fin (Fintype.card ι) ↦ c j)
                    (fun i ↦ by simp [y])
        _ = k := hc_sum
    · intro i
      have hci := hc_bounds (Fintype.equivFin ι i)
      exact ⟨hci.1, hci.2.1⟩
  have hy_ge_absz : ∀ i : ι, |z i| ≤ y i := by
    intro i
    simpa [b, y] using (hc_bounds (Fintype.equivFin ι i)).2.2
  have hpair_le :
      ((toDualMap ℝ E x) z : ℝ) ≤ ((toDualMap ℝ E absx) y : ℝ) := by
    -- First dominate the signed pairing by the pairing against `|x|`, then replace `|z|` by the
    -- simplex extension `y`.
    calc
      ((toDualMap ℝ E x) z : ℝ) = ∑ i : ι, x i * z i := by
        simpa [InnerProductSpace.toDualMap_apply_apply, dotProduct, mul_comm] using
          (EuclideanSpace.inner_toLp_toLp x.ofLp z.ofLp)
      _ ≤ ∑ i : ι, |x i| * |z i| := by
            refine Finset.sum_le_sum fun i _ ↦ ?_
            calc
              x i * z i ≤ |x i * z i| := le_abs_self _
              _ = |x i| * |z i| := by rw [abs_mul]
      _ ≤ ∑ i : ι, |x i| * y i := by
            refine Finset.sum_le_sum fun i _ ↦ ?_
            exact mul_le_mul_of_nonneg_left (hy_ge_absz i) (abs_nonneg _)
      _ = ∑ i : ι, absx i * y i := by
            simp [absx]
      _ = ((toDualMap ℝ E absx) y : ℝ) := by
            symm
            simpa [InnerProductSpace.toDualMap_apply_apply, dotProduct, mul_comm] using
              (EuclideanSpace.inner_toLp_toLp absx.ofLp y.ofLp)
  calc
    (((toDualMap ℝ E x) z : ℝ) : EReal) ≤ (((toDualMap ℝ E absx) y : ℝ) : EReal) := by
      exact_mod_cast hpair_le
    _ ≤ support_function (sum_of_k_largest_constraint_set ι k) (toDualMap ℝ E absx) := by
          rw [support_function_apply]
          exact le_sSup ⟨y, hy_mem, by simp⟩
    _ = (sum_k_largest_abs k x : EReal) := by
          symm
          exact habs

/-- Helper for Example 6.51: when `k ≤ card`, a simplex maximizer for `|x|` can be signed
coordinatewise to produce a feasible point of the unit-box `ℓ¹` constraint set with the same
pairing value. -/
private theorem sum_k_largest_abs_le_support_function_constraint_set_of_le_card
    (hk : k ≤ Fintype.card ι) (x : E) :
    (sum_k_largest_abs k x : EReal) ≤ support_function C (toDualMap ℝ E x) := by
  let absx : E := toLp 2 fun i ↦ |x i|
  have habs :
      (sum_k_largest_abs k x : EReal) =
        support_function (sum_of_k_largest_constraint_set ι k) (toDualMap ℝ E absx) := by
    -- Rewrite the source-facing absolute-value sum through Example 6.50.
    simpa [sum_k_largest_abs, absx] using
      (sum_of_k_largest_values_eq_support_function_constraint_set (ι := ι) hk absx)
  rw [habs, support_function_apply]
  apply sSup_le
  rintro _ ⟨y, hy, rfl⟩
  let sy : E := toLp 2 fun i ↦ (if 0 ≤ x i then (1 : ℝ) else -1) * y i
  have hsy_mem : sy ∈ C := by
    rw [mem_weighted_l1_box_constraint_set_iff]
    constructor
    · -- The signed lift preserves the coordinatewise absolute values, so it preserves the `ℓ¹`
      -- mass as well.
      calc
        ∑ i : ι, (1 : ℝ) * |sy i| = ∑ i : ι, |sy i| := by
          simp
        _ = ∑ i : ι, y i := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          have hy0 : 0 ≤ y i := (hy.2 i).1
          by_cases hxi : 0 ≤ x i
          · simp [sy, hxi, hy0]
          · simp [sy, hxi, hy0]
        _ = k := hy.1
      exact le_rfl
    · intro i
      -- The same absolute-value preservation keeps the point inside the unit box.
      have hy0 : 0 ≤ y i := (hy.2 i).1
      have hy1 : y i ≤ 1 := (hy.2 i).2
      have hsy_abs : |sy i| = y i := by
        by_cases hxi : 0 ≤ x i
        · simp [sy, hxi, hy0]
        · simp [sy, hxi, hy0]
      by_cases hxi : 0 ≤ x i
      · simpa [hsy_abs] using hy1
      · simpa [hsy_abs] using hy1
  have hcoord :
      ∀ i : ι, x i * (if 0 ≤ x i then (1 : ℝ) else -1) = |x i| := by
    intro i
    by_cases hxi : 0 ≤ x i
    · simp [hxi, abs_of_nonneg hxi]
    · have hxi' : x i ≤ 0 := le_of_not_ge hxi
      simp [hxi, abs_of_nonpos hxi']
  have hpair_eq :
      ((toDualMap ℝ E absx) y : ℝ) = ((toDualMap ℝ E x) sy : ℝ) := by
    -- The chosen sign makes each coordinate contribution equal to `|x i| * y i`.
    calc
      ((toDualMap ℝ E absx) y : ℝ) = ∑ i : ι, |x i| * y i := by
        simpa [absx, InnerProductSpace.toDualMap_apply_apply, dotProduct, mul_comm] using
          (EuclideanSpace.inner_toLp_toLp absx.ofLp y.ofLp)
      _ = ∑ i : ι, (x i * (if 0 ≤ x i then (1 : ℝ) else -1)) * y i := by
            refine Finset.sum_congr rfl fun i _ ↦ ?_
            rw [hcoord i]
      _ = ∑ i : ι, x i * sy i := by
            refine Finset.sum_congr rfl fun i _ ↦ ?_
            simp [sy]
      _ = ((toDualMap ℝ E x) sy : ℝ) := by
            symm
            simpa [InnerProductSpace.toDualMap_apply_apply, dotProduct, mul_comm] using
              (EuclideanSpace.inner_toLp_toLp x.ofLp sy.ofLp)
  calc
    (((toDualMap ℝ E absx) y : ℝ) : EReal) = (((toDualMap ℝ E x) sy : ℝ) : EReal) := by
      exact congrArg (fun r : ℝ ↦ (r : EReal)) hpair_eq
    _ ≤ support_function C (toDualMap ℝ E x) := by
          rw [support_function_apply]
          exact le_sSup ⟨sy, hsy_mem, by simp⟩

-- Proof sketch: in the active branch `k ≤ card`, compare the support function of the unit-box
-- `ℓ¹` set with Example 6.50 applied to `|x|`. The upper bound uses the capped-simplex extension
-- lemma above, and the lower bound uses the coordinatewise sign lift of a simplex maximizer.
/-- Helper for Example 6.51: when `k` does not exceed the ambient dimension, the sum of the `k`
largest coordinate absolute values is the support function of the unit-box `ℓ¹`-constraint set
from Definition 6.6. -/
private theorem sum_k_largest_abs_eq_support_function_constraint_set_of_le_card
    (hk : k ≤ Fintype.card ι) (x : E) :
    (sum_k_largest_abs k x : EReal) = support_function C (toDualMap ℝ E x) := by
  -- Route correction: the exact-mass capped simplex from Example 6.50 is still the governing
  -- object. The new work is only to pass between `≤ k` box weights and exact-mass simplex weights.
  apply le_antisymm
  · exact sum_k_largest_abs_le_support_function_constraint_set_of_le_card (k := k) hk x
  · exact support_function_constraint_set_le_sum_k_largest_abs_of_le_card (k := k) hk x

-- Proof sketch: apply Example 6.50 to the nonnegative vector `fun i ↦ |x i|`, then identify the
-- capped-simplex maximization variables with signed variables in the owner set `C`. The support
-- value is attained by matching the signs of the `k` largest coordinates of `x`.
/-- The sum of the `k` largest coordinate absolute values is the support function of the unit-box
`ℓ¹`-constraint set from Definition 6.6. -/
theorem sum_k_largest_abs_eq_support_function_constraint_set
    (x : E) :
    (sum_k_largest_abs k x : EReal) = support_function C (toDualMap ℝ E x) := by
  by_cases hk : k ≤ Fintype.card ι
  · -- In the non-saturated branch, the support-function bridge comes from the two comparison
    -- lemmas above.
    exact sum_k_largest_abs_eq_support_function_constraint_set_of_le_card (k := k) hk x
  · have hcard : Fintype.card ι ≤ k := Nat.le_of_lt (Nat.lt_of_not_ge hk)
    -- Above the ambient dimension, both the function and the constraint set stabilize at
    -- `k = card ι`.
    rw [sum_k_largest_abs_stabilizes_above_card (k := k) hcard x]
    rw [unit_box_l1_constraint_stabilizes_above_card (k := k) hcard]
    exact
      sum_k_largest_abs_eq_support_function_constraint_set_of_le_card
        (k := Fintype.card ι) le_rfl x

-- Proof sketch: rewrite `sum_k_largest_abs k` with
-- `sum_k_largest_abs_eq_support_function_constraint_set`, then apply Theorem 6.46 to the owner
-- set `C`. The required nonempty/closed/convex hypotheses come from the owner API in
-- Definition 6.6.
/-- Example 6.51: if `λ > 0`, then the proximal set of the sum of the `k` largest coordinate
absolute values is the singleton containing `x - λ P_C(x / λ)`, where
`C = {y | ∑ i, |y i| ≤ k, |y i| ≤ 1}` and `P_C` is the metric projection onto `C`. Specializing
to `ι = Fin n` recovers the textbook `ℝ^n` statement. -/
theorem prox_sum_k_largest_abs_eq_singleton_sub_smul_metricProjection
    (lam : ℝ) (hlam : 0 < lam) (x : E) :
    prox[fun y : E ↦ (lam : EReal) * (sum_k_largest_abs k y : EReal)] x =
      {x - lam • P (lam⁻¹ • x)} := by
  let lamPos : PosReal := ⟨lam, hlam⟩
  have hpenalty :
      (fun y : E ↦ (lam : EReal) * (sum_k_largest_abs k y : EReal)) =
        (((lam : ℝ) : EReal) • σ[C]) := by
    funext y
    -- Rewrite the source-facing penalty through the support-function identity proved above.
    rw [Pi.smul_apply, support_function_primal_apply,
      sum_k_largest_abs_eq_support_function_constraint_set (k := k) y]
    simp [smul_eq_mul]
  -- With the support-function bridge in place, Theorem 6.46 applies verbatim.
  rw [hpenalty]
  simpa [constraintProjectionPoint, lamPos] using
    (prox_support_function_eq_singleton_sub_smul_metricProjection
      (weighted_l1_box_constraint_set unitWeights unitBox (k : ℝ))
      (hC_nonempty k)
      ((hC_closed k).isComplete)
      (hC_convex k)
      lamPos x)

end

end
