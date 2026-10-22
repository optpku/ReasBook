/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_2
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open scoped BigOperators

section

variable {ι : Type u} {Ei : ι → Type v}
variable [∀ i, NormedAddCommGroup (Ei i)] [∀ i, InnerProductSpace ℝ (Ei i)]

/- `prompt_add/` is absent in this workspace, so the statement design is sampled directly from the
nearby Chapter 13 one-space conditional-gradient owners and the Chapter 11 block-optimization API.
The owner abstractions are:

- Chapter 10's `composite_model_objective` for the block linearized objective
  `v ↦ ⟪v, ∇_i f(x)⟫ + g_i(v)`;
- Chapter 8's `unconstrained_problem_solutions` for the source-facing block argmin set;
- the generalized Chapter 13 gap pattern "subproblem value at `x_i` minus subproblem value at
  `v`", specialized blockwise;
- the finite sum owner `∑ i` for the total block norm `S(x)`.

This item is `source-facing`: the source chooses blockwise minimizers `p_i(x)`, but that choice is
not canonical. The public API therefore keeps the canonical argmin set and supremum gap as owners,
and records any chosen block oracle separately through an explicit selection predicate. -/

/-- The `i`-th block linearized subproblem at `x`, namely
`v ↦ ⟪v, ∇_i f(x)⟫ + g_i(v)`. This is the Chapter 10 composite objective specialized to the
block-affine term `v ↦ ⟪v, ∇_i f(x)⟫`. -/
abbrev partial_conditional_gradient_subproblem
    (g : (i : ι) → Ei i → EReal)
    (block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i)
    (x : (j : ι) → Ei j) (i : ι) : Ei i → EReal :=
  composite_model_objective
    (fun v ↦ ((inner ℝ v (block_gradient i x) : ℝ) : EReal))
    (g i)

-- Proof sketch: unfold `partial_conditional_gradient_subproblem`; evaluation at `v` is exactly
-- the displayed one-block linearized objective value.
/-- Evaluating the `i`-th block linearized subproblem at `v` gives
`⟪v, ∇_i f(x)⟫ + g_i(v)`. -/
@[simp] theorem partial_conditional_gradient_subproblem_apply
    (g : (i : ι) → Ei i → EReal)
    (block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i)
    (x : (j : ι) → Ei j) (i : ι) (v : Ei i) :
    partial_conditional_gradient_subproblem g block_gradient x i v =
      ((inner ℝ v (block_gradient i x) : ℝ) : EReal) + g i v :=
  composite_model_objective_apply _ _ _

/-- The `i`-th block argmin set consists of the minimizers of the block linearized subproblem
`v ↦ ⟪v, ∇_i f(x)⟫ + g_i(v)`. -/
abbrev partial_conditional_gradient_argmin
    (g : (i : ι) → Ei i → EReal)
    (block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i)
    (x : (j : ι) → Ei j) (i : ι) : Set (Ei i) :=
  unconstrained_problem_solutions (partial_conditional_gradient_subproblem g block_gradient x i)

-- Proof sketch: `partial_conditional_gradient_argmin` is exactly the Chapter 8 unconstrained
-- solution-set owner applied to the `i`-th block subproblem.
/-- The Chapter 13 block argmin set is exactly the Chapter 8 unconstrained solution set of the
`i`-th block linearized subproblem. -/
theorem partial_conditional_gradient_argmin_def
    (g : (i : ι) → Ei i → EReal)
    (block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i)
    (x : (j : ι) → Ei j) (i : ι) :
    partial_conditional_gradient_argmin g block_gradient x i =
      unconstrained_problem_solutions
        (partial_conditional_gradient_subproblem g block_gradient x i) :=
  rfl

-- Proof sketch: rewrite membership in the Chapter 8 unconstrained solution-set owner.
/-- A point `v` lies in the `i`-th block argmin set exactly when it globally minimizes the block
linearized subproblem. -/
@[simp] theorem mem_partial_conditional_gradient_argmin_iff
    {g : (i : ι) → Ei i → EReal}
    {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
    {x : (j : ι) → Ei j} {i : ι} {v : Ei i} :
    v ∈ partial_conditional_gradient_argmin g block_gradient x i ↔
      IsMinOn (partial_conditional_gradient_subproblem g block_gradient x i) Set.univ v :=
  mem_unconstrained_problem_solutions_iff

/-- The `i`-th block gap objective at `x`, namely the value of the block linearized subproblem at
`x_i` minus its value at `v`. Equivalently, this is
`v ↦ ⟪∇_i f(x), x_i - v⟫ + g_i(x_i) - g_i(v)`. -/
def partial_conditional_gradient_gap_objective
    (g : (i : ι) → Ei i → EReal)
    (block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i)
    (x : (j : ι) → Ei j) (i : ι) : Ei i → EReal :=
  fun v ↦
    partial_conditional_gradient_subproblem g block_gradient x i (x i) -
      partial_conditional_gradient_subproblem g block_gradient x i v

-- Proof sketch: unfold `partial_conditional_gradient_gap_objective` and
-- `partial_conditional_gradient_subproblem`, then regroup the constant term
-- `⟪∇_i f(x), x_i⟫ + g_i(x_i)` against `⟪v, ∇_i f(x)⟫ + g_i(v)` to obtain the displayed gap
-- formula.
/-- Evaluating the `i`-th block gap objective at `v` gives
`⟪∇_i f(x), x_i - v⟫ + g_i(x_i) - g_i(v)`. -/
theorem partial_conditional_gradient_gap_objective_apply
    (g : (i : ι) → Ei i → EReal)
    (block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i)
    (x : (j : ι) → Ei j) (i : ι) (v : Ei i) :
    partial_conditional_gradient_gap_objective g block_gradient x i v =
      ((inner ℝ (block_gradient i x) (x i - v) : ℝ) : EReal) + g i (x i) - g i v := by
  -- Rewrite the real linear part as the difference of two block subproblem linear terms.
  have h_inner :
      (inner ℝ (x i) (block_gradient i x) : ℝ) -
          (inner ℝ v (block_gradient i x) : ℝ) =
        inner ℝ (block_gradient i x) (x i - v) := by
    rw [← inner_sub_left, real_inner_comm]
  -- Then regroup the `EReal` subtraction so the finite linear term is isolated from `g_i`.
  rw [partial_conditional_gradient_gap_objective]
  rw [partial_conditional_gradient_subproblem_apply, partial_conditional_gradient_subproblem_apply]
  calc
    (((inner ℝ (x i) (block_gradient i x) : ℝ) : EReal) + g i (x i)) -
        (((inner ℝ v (block_gradient i x) : ℝ) : EReal) + g i v)
      = (g i (x i) +
          ((((inner ℝ (x i) (block_gradient i x) : ℝ) -
              (inner ℝ v (block_gradient i x) : ℝ)) : ℝ) : EReal)) - g i v := by
          rw [sub_eq_add_neg]
          rw [EReal.neg_add (.inl (EReal.coe_ne_bot _)) (.inl (EReal.coe_ne_top _))]
          simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    _ = (g i (x i) + ((inner ℝ (block_gradient i x) (x i - v) : ℝ) : EReal)) - g i v := by
          rw [h_inner]
    _ = ((inner ℝ (block_gradient i x) (x i - v) : ℝ) : EReal) + g i (x i) - g i v := by
          rw [add_comm]

/-- Definition 13.17: the `i`-th partial conditional-gradient norm `S_i(x)` is the supremum of
the block gap objective
`v ↦ ⟪∇_i f(x), x_i - v⟫ + g_i(x_i) - g_i(v)` over the `i`-th block space. -/
def partial_conditional_gradient_norm
    (g : (i : ι) → Ei i → EReal)
    (block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i)
    (x : (j : ι) → Ei j) (i : ι) : EReal :=
  sSup (Set.range (partial_conditional_gradient_gap_objective g block_gradient x i))

/- Block-specific notation for the `i`-th conditional-gradient quantity `S_i(x)`.
The `S[...]` spelling is already the public one-space notation from Text 13.2, so the block
variant uses a distinct parser token and can be imported together with that owner. -/
notation "Sᵇ[" g ", " block_gradient "; " i "](" x ")" =>
  partial_conditional_gradient_norm g block_gradient x i

-- Proof sketch: unfold `partial_conditional_gradient_norm`; this is exactly the order-theoretic
-- supremum form of the textbook maximization problem defining `S_i(x)`.
/-- The partial conditional-gradient norm is the supremum of the values of the block gap objective
over all block search points. -/
theorem partial_conditional_gradient_norm_eq_sSup_gap_objective
    (g : (i : ι) → Ei i → EReal)
    (block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i)
    (x : (j : ι) → Ei j) (i : ι) :
    Sᵇ[g, block_gradient; i](x) =
      sSup (Set.range (partial_conditional_gradient_gap_objective g block_gradient x i)) :=
  rfl

/-- Helper for Definition 13.17: if one block subproblem value is no larger than another, then
the corresponding gap value is no smaller. -/
lemma partial_conditional_gradient_gap_objective_le_of_subproblem_le
    {g : (i : ι) → Ei i → EReal}
    {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
    {x : (j : ι) → Ei j} {i : ι} {y z : Ei i}
    (hzy :
      partial_conditional_gradient_subproblem g block_gradient x i z ≤
        partial_conditional_gradient_subproblem g block_gradient x i y) :
    partial_conditional_gradient_gap_objective g block_gradient x i y ≤
      partial_conditional_gradient_gap_objective g block_gradient x i z := by
  -- Both gap values subtract from the same base value, so the smaller subproblem value gives
  -- the larger gap.
  rw [partial_conditional_gradient_gap_objective, partial_conditional_gradient_gap_objective]
  exact EReal.sub_le_sub le_rfl hzy

-- Proof sketch: write the gap objective as a constant minus the block linearized subproblem.
-- Any minimizer of the subproblem is therefore a maximizer of the gap objective, so its value is a
-- greatest element of the range.
/-- Any minimizer of the `i`-th block linearized subproblem realizes a global maximum of the
corresponding block gap objective. -/
theorem partial_conditional_gradient_gap_objective_isGreatest_of_mem_argmin
    {g : (i : ι) → Ei i → EReal}
    {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
    {x : (j : ι) → Ei j} {i : ι} {v : Ei i}
    (hv : v ∈ partial_conditional_gradient_argmin g block_gradient x i) :
    IsGreatest (Set.range (partial_conditional_gradient_gap_objective g block_gradient x i))
      (partial_conditional_gradient_gap_objective g block_gradient x i v) := by
  -- Rewrite argmin membership as the pointwise minimality of the block linearized subproblem.
  rw [mem_partial_conditional_gradient_argmin_iff, isMinOn_univ_iff] at hv
  refine ⟨Set.mem_range_self v, ?_⟩
  -- The gap is a fixed base value minus the subproblem value, so a minimizer maximizes the gap.
  rintro _ ⟨y, rfl⟩
  exact partial_conditional_gradient_gap_objective_le_of_subproblem_le (hv y)

-- Proof sketch: combine
-- `partial_conditional_gradient_norm_eq_sSup_gap_objective` with
-- `partial_conditional_gradient_gap_objective_isGreatest_of_mem_argmin`; the supremum of a set
-- with a greatest element is that element.
/-- If `v` minimizes the `i`-th block linearized subproblem, then `S_i(x)` is exactly the gap
value at `v`. -/
theorem partial_conditional_gradient_norm_eq_of_mem_argmin
    {g : (i : ι) → Ei i → EReal}
    {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
    {x : (j : ι) → Ei j} {i : ι} {v : Ei i}
    (hv : v ∈ partial_conditional_gradient_argmin g block_gradient x i) :
    Sᵇ[g, block_gradient; i](x) =
      partial_conditional_gradient_gap_objective g block_gradient x i v := by
  -- Replace the norm by the supremum of the gap range and identify that supremum with its
  -- greatest element coming from the chosen block minimizer.
  rw [partial_conditional_gradient_norm_eq_sSup_gap_objective]
  exact (partial_conditional_gradient_gap_objective_isGreatest_of_mem_argmin hv).csSup_eq

section

variable [Fintype ι]

/-- The total block conditional-gradient norm `S(x)` is the sum of the partial norms `S_i(x)` over
all blocks. -/
def block_conditional_gradient_norm
    (g : (i : ι) → Ei i → EReal)
    (block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i)
    (x : (j : ι) → Ei j) : EReal :=
  ∑ i : ι, partial_conditional_gradient_norm g block_gradient x i

/- Block-specific notation for the total conditional-gradient quantity `S(x)`. -/
notation "Sᵇ[" g ", " block_gradient "](" x ")" =>
  block_conditional_gradient_norm g block_gradient x

-- Proof sketch: unfold `block_conditional_gradient_norm`; the owner is definitionally the finite
-- sum of the blockwise norms.
/-- Expanding the total block conditional-gradient norm gives the sum of the partial norms
`∑ i, S_i(x)`. -/
theorem block_conditional_gradient_norm_eq_sum
    (g : (i : ι) → Ei i → EReal)
    (block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i)
    (x : (j : ι) → Ei j) :
    Sᵇ[g, block_gradient](x) =
      ∑ i : ι, Sᵇ[g, block_gradient; i](x) :=
  rfl

end

/-- A partial conditional-gradient selection chooses, for every block `i` and point `x`, one
minimizer of the `i`-th block linearized subproblem. -/
def IsPartialConditionalGradientSelection
    (g : (i : ι) → Ei i → EReal)
    (block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i)
    (selection : (i : ι) → ((j : ι) → Ei j) → Ei i) : Prop :=
  ∀ (i : ι) (x : (j : ι) → Ei j),
    selection i x ∈ partial_conditional_gradient_argmin g block_gradient x i

-- Proof sketch: apply `partial_conditional_gradient_norm_eq_of_mem_argmin` to the selected block
-- point `selection i x`, using the defining property of `IsPartialConditionalGradientSelection`.
/-- A chosen partial conditional-gradient selection realizes each partial norm `S_i(x)` as the gap
value at the selected point `p_i(x)`. -/
theorem partial_conditional_gradient_norm_eq_of_selection
    {g : (i : ι) → Ei i → EReal}
    {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
    {selection : (i : ι) → ((j : ι) → Ei j) → Ei i}
    (hselection : IsPartialConditionalGradientSelection g block_gradient selection)
    (x : (j : ι) → Ei j) (i : ι) :
    Sᵇ[g, block_gradient; i](x) =
      partial_conditional_gradient_gap_objective g block_gradient x i (selection i x) :=
  partial_conditional_gradient_norm_eq_of_mem_argmin (hselection i x)

end
