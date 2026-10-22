/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Definition_9_2
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Text_13_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

section

/- Definition 13.6 is `source-facing`: the textbook lists three concrete stepsize strategies for
the generalized conditional-gradient method.

Domain sampling against the local optimization API gives the relevant canonical shapes already used
in the project:
- explicit scalar-valued rules such as `polyak_stepsize`;
- constant strategy sequences such as `proximal_gradient_constant_stepsize_strategy`;
- exact-line-search minimizer sets such as `exact_line_search_stepsizes` and
  `non_euclidean_exact_line_search_stepsizes`.

The clean public interface is therefore three primitive owners:
- two explicit scalar rules for the predefined diminishing and adaptive cases;
- one set-valued exact-line-search owner recording the admissible minimizers on `[0, 1]`.

The trajectory-level predicates saying that a generalized conditional-gradient method uses one of
these rules are derived API, so they belong below and are stated directly in terms of these
owners rather than as parallel local formulas inside later theorem files.

No extra wrapper or package is introduced, since the mathematics here is exactly the displayed
formulas. -/

/-- Definition 13.6 (1): the predefined diminishing stepsize strategy for the generalized
conditional-gradient method uses the scalar `t_k = 2 / (k + 2)` at iteration `k`. -/
def conditional_gradient_predefined_diminishing_stepsize (k : ℕ) : ℝ :=
  2 / (k + 2 : ℝ)

/-- Evaluating the predefined diminishing conditional-gradient stepsize reproduces the textbook
formula `2 / (k + 2)`. -/
@[simp] theorem conditional_gradient_predefined_diminishing_stepsize_eq (k : ℕ) :
    conditional_gradient_predefined_diminishing_stepsize k = 2 / (k + 2 : ℝ) :=
  rfl

end

section

variable {E : Type u} [NormedAddCommGroup E]

/-- Definition 13.6 (2): the adaptive stepsize strategy at the current iterate `x` and search
point `p` uses the current gap value `Sx` through the scalar
`min {1, Sx / (L_f ‖p - x‖²)}` on the nondegenerate branch `L_f ≠ 0` and `p ≠ x`, while the
degenerate cases `L_f = 0` or `‖p - x‖ = 0` are recorded explicitly by the fallback value `1`. -/
def conditional_gradient_adaptive_stepsize
    (Sx : ℝ) (Lf : NNReal) (x p : E) : ℝ :=
  if ‖p - x‖ = 0 ∨ Lf = 0 then 1
  else min (1 : ℝ) (Sx / ((Lf : ℝ) * ‖p - x‖ ^ (2 : ℕ)))

/-- Expanding the adaptive conditional-gradient stepsize exposes the guarded textbook formula. -/
@[simp] theorem conditional_gradient_adaptive_stepsize_eq
    (Sx : ℝ) (Lf : NNReal) (x p : E) :
    conditional_gradient_adaptive_stepsize Sx Lf x p =
      if ‖p - x‖ = 0 ∨ Lf = 0 then 1
      else min (1 : ℝ) (Sx / ((Lf : ℝ) * ‖p - x‖ ^ (2 : ℕ))) :=
  rfl

/-- If the search point agrees with the current iterate, the adaptive conditional-gradient
stepsize takes its explicit fallback value `1`. -/
@[simp] theorem conditional_gradient_adaptive_stepsize_eq_one_of_eq
    (Sx : ℝ) (Lf : NNReal) (x : E) :
    conditional_gradient_adaptive_stepsize Sx Lf x x = 1 := by
  simp [conditional_gradient_adaptive_stepsize]

/-- If `L_f = 0`, the adaptive conditional-gradient stepsize takes its explicit fallback
value `1`. -/
@[simp] theorem conditional_gradient_adaptive_stepsize_eq_one_of_Lf_eq_zero
    (Sx : ℝ) (x p : E) {Lf : NNReal} (hLf : Lf = 0) :
    conditional_gradient_adaptive_stepsize Sx Lf x p = 1 := by
  simp [conditional_gradient_adaptive_stepsize, hLf]

/-- On the nondegenerate branch `L_f ≠ 0` and `p ≠ x`, the adaptive conditional-gradient
stepsize is the textbook minimum `min {1, Sx / (L_f ‖p - x‖²)}`. -/
theorem conditional_gradient_adaptive_stepsize_of_ne
    (Sx : ℝ) {Lf : NNReal} {x p : E} (hp : p ≠ x) (hLf : Lf ≠ 0) :
    conditional_gradient_adaptive_stepsize Sx Lf x p =
      min (1 : ℝ) (Sx / ((Lf : ℝ) * ‖p - x‖ ^ (2 : ℕ))) := by
  have hnorm : ‖p - x‖ ≠ 0 := by
    intro hnorm
    apply hp
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
  simp [conditional_gradient_adaptive_stepsize, hnorm, hLf]

end

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/-- Definition 13.6 (3): the exact line search stepsizes at the current iterate `x` and search
point `p` are the scalars `t ∈ [0, 1]` that minimize the one-dimensional restriction
`u ↦ F (x + u (p - x))`. -/
def conditional_gradient_exact_line_search_stepsizes
    (F : E → EReal) (x p : E) : Set ℝ :=
  Set.Icc (0 : ℝ) 1 ∩
    {t | IsMinOn (fun u ↦ F (x + u • (p - x))) (Set.Icc (0 : ℝ) 1) t}

/-- A scalar belongs to the conditional-gradient exact line search set exactly when it lies in
`[0, 1]` and minimizes `u ↦ F (x + u (p - x))` on that interval. -/
@[simp] theorem mem_conditional_gradient_exact_line_search_stepsizes_iff
    {F : E → EReal} {x p : E} {t : ℝ} :
    t ∈ conditional_gradient_exact_line_search_stepsizes F x p ↔
      t ∈ Set.Icc (0 : ℝ) 1 ∧
        IsMinOn (fun u ↦ F (x + u • (p - x))) (Set.Icc (0 : ℝ) 1) t :=
  by
    -- Expand the exact-line-search owner so membership becomes the feasibility/minimality
    -- conjunction displayed in Definition 13.6.
    simp [conditional_gradient_exact_line_search_stepsizes]

end

section

/-- A generalized conditional-gradient trajectory uses the predefined diminishing stepsize rule
when each stepsize is `tₖ = 2 / (k + 2)`. -/
def uses_generalized_conditional_gradient_predefined_stepsize_rule
    (t : ℕ → Set.Icc (0 : ℝ) 1) : Prop :=
  ∀ k : ℕ, (t k : ℝ) = conditional_gradient_predefined_diminishing_stepsize k

end

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]
variable (f : E → ℝ) (g : E → EReal)

local notation "F" => composite_model_objective f.toEReal g

/-- A generalized conditional-gradient trajectory uses exact line search when each stepsize
belongs to the Definition 13.6 exact-line-search set for the composite objective along the segment
from `xᵏ` to `pᵏ`. -/
def uses_generalized_conditional_gradient_exact_line_search_rule
    (x p : ℕ → E) (t : ℕ → Set.Icc (0 : ℝ) 1) : Prop :=
  ∀ k : ℕ,
    (t k : ℝ) ∈ conditional_gradient_exact_line_search_stepsizes F (x k) (p k)

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (f : E → ℝ) (g : E → EReal)

/-- A generalized conditional-gradient trajectory uses the adaptive stepsize rule when each
stepsize is obtained by applying the Definition 13.6 adaptive owner to the Chapter 13 gap
quantity `S`, provided that this gap value is finite at the current iterate. -/
def uses_generalized_conditional_gradient_adaptive_stepsize_rule
    (Lf : NNReal) (x p : ℕ → E) (t : ℕ → Set.Icc (0 : ℝ) 1) : Prop :=
  ∀ k : ℕ,
    S[f, g](x k) ≠ ⊤ ∧
      S[f, g](x k) ≠ ⊥ ∧
      (t k : ℝ) =
        conditional_gradient_adaptive_stepsize (S[f, g](x k)).toReal Lf (x k) (p k)

/-- Theorem 13.9 uses either the adaptive rule or exact line search. -/
def uses_generalized_conditional_gradient_adaptive_or_exact_stepsize_rule
    (Lf : NNReal) (x p : ℕ → E) (t : ℕ → Set.Icc (0 : ℝ) 1) : Prop :=
  uses_generalized_conditional_gradient_adaptive_stepsize_rule f g Lf x p t ∨
    uses_generalized_conditional_gradient_exact_line_search_rule f g x p t

/-- A generalized conditional-gradient trajectory uses one of the three textbook stepsize
strategies when it uses either the predefined diminishing rule, the adaptive rule, or exact line
search. -/
def uses_generalized_conditional_gradient_standard_stepsize_rule
    (Lf : NNReal) (x p : ℕ → E) (t : ℕ → Set.Icc (0 : ℝ) 1) : Prop :=
  uses_generalized_conditional_gradient_predefined_stepsize_rule t ∨
    uses_generalized_conditional_gradient_adaptive_or_exact_stepsize_rule f g Lf x p t

end
