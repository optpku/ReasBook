/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Definition_13_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- `prompt_add/` is absent in this workspace, so the domain sample is taken from the project
owners already used by Definition 13.4:

- `composite_model_objective` from Chapter 10 for the linearized objective sum;
- `unconstrained_problem_solutions` from Chapter 8 for the argmin set of that objective;
- `generalized_conditional_gradient_subproblem` from Definition 13.4 as the source-facing owner.

Text 13.2 is therefore a `bridge/view` item: it does not introduce a new optimization owner beyond
that subproblem, but records the canonical gap-function and supremum views derived from it. The
primitive data remains the subproblem `p ↦ ⟪p, ∇ f(x)⟫ + g(p)`, while the gap objective and norm
are derived API. -/

/-- The generalized conditional-gradient gap objective at `x`, namely the function
`p ↦ ⟪∇ f(x), x - p⟫ + g(x) - g(p)`. -/
def generalized_conditional_gradient_gap_objective
    (f : E → ℝ) (g : E → EReal) (x : E) : E → EReal :=
  fun p ↦
    generalized_conditional_gradient_subproblem f g x x -
      generalized_conditional_gradient_subproblem f g x p

-- Proof sketch: unfold `generalized_conditional_gradient_gap_objective` as the value of the
-- linearized subproblem at `x` minus its value at `p`, then expand both subproblem values and
-- regroup the inner-product terms to obtain
-- `⟪∇ f(x), x - p⟫ + g(x) - g(p)`.
/-- Evaluating the generalized conditional-gradient gap objective at `p` gives the displayed
formula `⟪∇ f(x), x - p⟫ + g(x) - g(p)`. -/
theorem generalized_conditional_gradient_gap_objective_apply
    (f : E → ℝ) (g : E → EReal) (x p : E) :
    generalized_conditional_gradient_gap_objective f g x p =
      ((inner ℝ (∇ f x) (x - p) : ℝ) : EReal) + g x - g p := by
  -- Expand the gap as the value of the linearized subproblem at `x` minus its value at `p`.
  rw [generalized_conditional_gradient_gap_objective,
    generalized_conditional_gradient_subproblem_apply,
    generalized_conditional_gradient_subproblem_apply]
  -- Normalize the negated subproblem value and then combine the finite inner-product terms.
  have hneg :
      -((((inner ℝ p (∇ f x) : ℝ) : EReal) + g p)) =
        -((inner ℝ p (∇ f x) : ℝ) : EReal) - g p := by
    exact EReal.neg_add (by simp) (by simp)
  have hcoe :
      (((inner ℝ x (∇ f x) : ℝ) : EReal) + -((inner ℝ p (∇ f x) : ℝ) : EReal)) =
        (((inner ℝ x (∇ f x) - inner ℝ p (∇ f x) : ℝ) : EReal)) := by
    rw [← sub_eq_add_neg, ← EReal.coe_sub]
  have hinner :
      inner ℝ x (∇ f x) - inner ℝ p (∇ f x) =
        inner ℝ (∇ f x) (x - p) := by
    rw [real_inner_comm (∇ f x) x, real_inner_comm (∇ f x) p, ← inner_sub_right]
  calc
    (((inner ℝ x (∇ f x) : ℝ) : EReal) + g x) -
        (((inner ℝ p (∇ f x) : ℝ) : EReal) + g p) =
      (((inner ℝ x (∇ f x) : ℝ) : EReal) + g x) +
        (-((inner ℝ p (∇ f x) : ℝ) : EReal) - g p) := by
          rw [sub_eq_add_neg, hneg]
    _ =
      ((((inner ℝ x (∇ f x) : ℝ) : EReal) + -((inner ℝ p (∇ f x) : ℝ) : EReal)) + g x) -
        g p := by
          simp only [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    _ = (((inner ℝ x (∇ f x) - inner ℝ p (∇ f x) : ℝ) : EReal) + g x) - g p := by
          rw [hcoe]
    _ = ((inner ℝ (∇ f x) (x - p) : ℝ) : EReal) + g x - g p := by
          rw [hinner]

/-- The generalized conditional-gradient norm at `x`, viewed canonically as the supremum of the
gap objective values over all search points `p`. -/
def generalized_conditional_gradient_norm
    (f : E → ℝ) (g : E → EReal) (x : E) : EReal :=
  sSup (Set.range (generalized_conditional_gradient_gap_objective f g x))

/- Textbook notation for the generalized conditional-gradient norm `S(x)` with ambient smooth term
`f` and nonsmooth term `g`. -/
notation "S[" f ", " g "](" x ")" => generalized_conditional_gradient_norm f g x

-- Proof sketch: unfold `generalized_conditional_gradient_norm`; this is exactly the order-theoretic
-- supremum form of the textbook maximization problem defining `S(x)`.
/-- The generalized conditional-gradient norm is exactly the supremum of the gap-objective values
over all search points. -/
theorem generalized_conditional_gradient_norm_eq_sSup_gap_objective
    (f : E → ℝ) (g : E → EReal) (x : E) :
    S[f, g](x) = sSup (Set.range (generalized_conditional_gradient_gap_objective f g x)) :=
  rfl

-- Proof sketch: rewrite `S[f, g](x)` using the supremum form of the gap objective, then replace
-- the gap objective by its explicit formula `⟪∇ f(x), x - p⟫ + g(x) - g(p)` pointwise.
/-- Text 13.2: by Definition 13.4, the generalized conditional-gradient quantity `S(x)` can be
written as the supremum of the values
`⟪∇ f(x), x - p⟫ + g(x) - g(p)` over all `p ∈ E`. -/
theorem generalized_conditional_gradient_norm_eq_sSup_inner_sub_add_sub
    (f : E → ℝ) (g : E → EReal) (x : E) :
    S[f, g](x) =
      sSup (Set.range (fun p ↦ ((inner ℝ (∇ f x) (x - p) : ℝ) : EReal) + g x - g p)) := by
  rw [generalized_conditional_gradient_norm_eq_sSup_gap_objective]
  apply congrArg sSup
  ext z
  constructor
  · rintro ⟨p, rfl⟩
    refine ⟨p, ?_⟩
    exact (generalized_conditional_gradient_gap_objective_apply f g x p).symm
  · rintro ⟨p, hp⟩
    refine ⟨p, ?_⟩
    exact (generalized_conditional_gradient_gap_objective_apply f g x p).trans hp

/-- Helper for Text 13.2: if one linearized subproblem value is no larger than another, then the
corresponding generalized conditional-gradient gap value is no smaller. -/
lemma generalized_conditional_gradient_gap_objective_le_of_subproblem_le
    {f : E → ℝ} {g : E → EReal} {x y z : E}
    (hzy :
      generalized_conditional_gradient_subproblem f g x z ≤
        generalized_conditional_gradient_subproblem f g x y) :
    generalized_conditional_gradient_gap_objective f g x y ≤
      generalized_conditional_gradient_gap_objective f g x z := by
  -- Both gap values subtract from the same base value, so the smaller subproblem value gives the
  -- larger gap value.
  rw [generalized_conditional_gradient_gap_objective]
  rw [generalized_conditional_gradient_gap_objective]
  exact EReal.sub_le_sub le_rfl hzy

-- Proof sketch: expand the gap objective as a constant minus the linearized subproblem.
-- A minimizer of the subproblem therefore becomes a maximizer of the gap objective on `Set.univ`,
-- and hence yields a greatest element of its range.
/-- Any minimizer of the generalized conditional-gradient linearized subproblem at `x` realizes a
global maximum of the gap objective. -/
theorem generalized_conditional_gradient_gap_objective_isGreatest_of_mem_argmin
    {f : E → ℝ} {g : E → EReal} {x p : E}
    (hp : p ∈ generalized_conditional_gradient_argmin f g x) :
    IsGreatest (Set.range (generalized_conditional_gradient_gap_objective f g x))
      (generalized_conditional_gradient_gap_objective f g x p) := by
  -- Rewrite argmin membership as pointwise minimality of the linearized subproblem.
  rw [mem_generalized_conditional_gradient_argmin_iff, isMinOn_univ_iff] at hp
  refine ⟨Set.mem_range_self p, ?_⟩
  -- The gap is a fixed base value minus the subproblem value, so a minimizer maximizes the gap.
  rintro _ ⟨y, rfl⟩
  exact generalized_conditional_gradient_gap_objective_le_of_subproblem_le (hp y)

-- Proof sketch: rewrite by `generalized_conditional_gradient_norm_eq_sSup_gap_objective`, then
-- combine the resulting `sSup` with
-- `generalized_conditional_gradient_gap_objective_isGreatest_of_mem_argmin`; the supremum of a
-- range with a greatest element is that greatest value.
/-- Choosing any minimizer `p ∈ generalized_conditional_gradient_argmin f g x` realizes the
generalized conditional-gradient norm as the corresponding maximal gap value. -/
theorem generalized_conditional_gradient_norm_eq_of_mem_argmin
    {f : E → ℝ} {g : E → EReal} {x p : E}
    (hp : p ∈ generalized_conditional_gradient_argmin f g x) :
    S[f, g](x) = generalized_conditional_gradient_gap_objective f g x p := by
  -- Replace the norm by the supremum of the gap range and identify that supremum with its
  -- greatest element coming from the chosen minimizer.
  rw [generalized_conditional_gradient_norm_eq_sSup_gap_objective]
  exact (generalized_conditional_gradient_gap_objective_isGreatest_of_mem_argmin hp).csSup_eq

end
