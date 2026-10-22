/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_10
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Theorem_4_3
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_6
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Definition_12_4
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Proposition_12_7
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Proposition_12_8

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped BigOperators

section

variable {E : Type u}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Definition 12.17 is `source-facing`: for the finite-sum model
`min_x {f x + ∑ i : Fin p, g i x}`, the textbook introduces the block dual objective
`q(y) = -f*(∑ i, y_i) - ∑ i, g_i*(-y_i)`, its optimal value `q_opt`, and the corresponding
optimal dual set `Λ*`.

The `core/canonical` Chapter 12 owner is still Definition 12.4's
`dual_based_proximal_gradient_lagrange_dual_objective_primal`, specialized to the separable block
sum `PiLp.separableSum g` and the diagonal duplication operator `dual_block_duplication E p`.
The public API here should therefore expose the source-facing block objective and value directly on
the block space `Fin p → E`, together with the canonical optimal-set owner defined from `IsMaxOn`,
with only a bridge theorem back to the Chapter 12.4 owner. -/

/-- Definition 12.17: the block dual objective
`q(y) = -f*(∑ i, y_i) - ∑ i, g_i*(-y_i)` for the finite-sum dual block proximal-gradient model. -/
def dual_block_proximal_gradient_dual_objective
    {p : ℕ} (f : E → EReal) (g : Fin p → E → EReal) : (Fin p → E) → EReal :=
  fun y ↦ -((f∗) (∑ i : Fin p, y i)) - ∑ i : Fin p, ((g i)∗) (-y i)

/-- Evaluating the block dual objective at `y` gives the textbook formula
`-f*(∑ i, y_i) - ∑ i, g_i*(-y_i)`. -/
@[simp] theorem dual_block_proximal_gradient_dual_objective_apply
    {p : ℕ} (f : E → EReal) (g : Fin p → E → EReal) (y : Fin p → E) :
    dual_block_proximal_gradient_dual_objective f g y =
      -((f∗) (∑ i : Fin p, y i)) - ∑ i : Fin p, ((g i)∗) (-y i) :=
  rfl

/-- Definition 12.17: the block dual problem value `q_opt` is the supremum of the range of the
block dual objective `q`. -/
def dual_block_proximal_gradient_dual_problem_value
    {p : ℕ} (f : E → EReal) (g : Fin p → E → EReal) : EReal :=
  sSup (Set.range (dual_block_proximal_gradient_dual_objective f g))

/-- Expanding `q_opt` gives the supremum of the attained values of the block dual objective `q`. -/
theorem dual_block_proximal_gradient_dual_problem_value_eq_sSup
    {p : ℕ} (f : E → EReal) (g : Fin p → E → EReal) :
    dual_block_proximal_gradient_dual_problem_value f g =
      sSup (Set.range (dual_block_proximal_gradient_dual_objective f g)) :=
  rfl

/-- The canonical optimal-set owner `Λ*` for the block dual objective `q`. -/
def dual_block_proximal_gradient_dual_optimal_set
    {p : ℕ} (f : E → EReal) (g : Fin p → E → EReal) : Set (Fin p → E) :=
  {yStar | IsMaxOn (dual_block_proximal_gradient_dual_objective f g) Set.univ yStar}

end

@[inherit_doc dual_block_proximal_gradient_dual_objective]
notation "q(" f ", " g ")" => dual_block_proximal_gradient_dual_objective f g

@[inherit_doc dual_block_proximal_gradient_dual_problem_value]
notation "q_opt(" f ", " g ")" => dual_block_proximal_gradient_dual_problem_value f g

@[inherit_doc dual_block_proximal_gradient_dual_optimal_set]
notation "Λ*(" f ", " g ")" => dual_block_proximal_gradient_dual_optimal_set f g

section

variable {E : Type u}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

-- Proof sketch: unfold `dual_block_proximal_gradient_dual_optimal_set`; membership is
-- definitionally the `IsMaxOn` condition for the block dual objective on all of `E^p`.
/-- Membership in the block dual optimal set means being a global maximizer of the dual objective
`q`. -/
@[simp] theorem mem_dual_block_proximal_gradient_dual_optimal_set
    {p : ℕ} (f : E → EReal) (g : Fin p → E → EReal) (yStar : Fin p → E) :
    yStar ∈ Λ*(f, g) ↔
      IsMaxOn (q(f, g)) Set.univ yStar :=
  Iff.rfl

/-- Any optimal dual point attains the canonical block dual problem value `q_opt`. -/
theorem dual_block_proximal_gradient_dual_objective_eq_dual_problem_value_of_mem_optimal_set
    {p : ℕ} (f : E → EReal) (g : Fin p → E → EReal)
    {yStar : Fin p → E} (hyStar : yStar ∈ Λ*(f, g)) :
    q(f, g) yStar = q_opt(f, g) := by
  have hmax :
      ∀ yBar : Fin p → E, q(f, g) yBar ≤ q(f, g) yStar := by
    simpa [mem_dual_block_proximal_gradient_dual_optimal_set, isMaxOn_univ_iff] using hyStar
  rw [dual_block_proximal_gradient_dual_problem_value_eq_sSup]
  refine Eq.symm <|
    (show IsGreatest (Set.range (q(f, g))) (q(f, g) yStar) from ?_).csSup_eq
  refine ⟨Set.mem_range_self yStar, ?_⟩
  intro z hz
  rcases hz with ⟨yBar, rfl⟩
  exact hmax yBar

/-- Shared Chapter 12 companion for Definition 12.17: once both the optimal dual point and the
sampled dual point are finite, the `EReal` dual gap rewrites to the scalar gap after applying
`toReal`. -/
theorem dual_gap_toReal_eq_of_mem_finite_domain
    {p : ℕ} (f : E → EReal) (g : Fin p → E → EReal)
    {yBar yStar : Fin p → E}
    (hyStar : yStar ∈ Λ*(f, g))
    (hyStar_finite : yStar ∈ finite_domain (q(f, g)))
    (hyBar_finite : yBar ∈ finite_domain (q(f, g))) :
    (q_opt(f, g) - q(f, g) yBar).toReal =
      EReal.toReal (q_opt(f, g)) - (q(f, g) yBar).toReal := by
  have hqOpt_ne_top : q_opt(f, g) ≠ ⊤ := by
    rw [← dual_block_proximal_gradient_dual_objective_eq_dual_problem_value_of_mem_optimal_set
      f g hyStar]
    exact (mem_finite_domain.mp hyStar_finite).1.ne
  have hqOpt_ne_bot : q_opt(f, g) ≠ ⊥ := by
    rw [← dual_block_proximal_gradient_dual_objective_eq_dual_problem_value_of_mem_optimal_set
      f g hyStar]
    exact (mem_finite_domain.mp hyStar_finite).2
  have hyBar_ne_top : q(f, g) yBar ≠ ⊤ := by
    exact (mem_finite_domain.mp hyBar_finite).1.ne
  have hyBar_ne_bot : q(f, g) yBar ≠ ⊥ := by
    exact (mem_finite_domain.mp hyBar_finite).2
  rw [EReal.toReal_sub hqOpt_ne_top hqOpt_ne_bot hyBar_ne_top hyBar_ne_bot]

/-- Shared Chapter 12 companion for Definition 12.17: every source-facing dual value is bounded
above by the canonical dual optimum `q_opt`. -/
theorem dual_objective_le_dual_problem_value
    {p : ℕ} (f : E → EReal) (g : Fin p → E → EReal) (v : Fin p → E) :
    q(f, g) v ≤ q_opt(f, g) := by
  rw [dual_block_proximal_gradient_dual_problem_value_eq_sSup]
  exact le_sSup ⟨v, rfl⟩

section

variable [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- Helper for Definition 12.17: the Riesz functional of a negated block vector is the coordinate
sum functional after transporting `PiLp` points to ordinary block families. -/
theorem toDualMap_neg_eq_lsum_comp_continuousLinearEquiv
    {p : ℕ} (y : PiLp (2 : ENNReal) (fun _ : Fin p ↦ E)) :
    (InnerProductSpace.toDualMap ℝ (PiLp (2 : ENNReal) (fun _ : Fin p ↦ E)) (-y) :
        Module.Dual ℝ (PiLp (2 : ENNReal) (fun _ : Fin p ↦ E))) =
      (((LinearMap.lsum ℝ (fun _ : Fin p ↦ E) ℝ
          (fun i : Fin p ↦ InnerProductSpace.toDualMap ℝ E (-y i))).comp
        (PiLp.continuousLinearEquiv (2 : ENNReal) ℝ (fun _ : Fin p ↦ E)).toLinearMap) :
          Module.Dual ℝ (PiLp (2 : ENNReal) (fun _ : Fin p ↦ E))) := by
  -- Evaluate both linear functionals on an arbitrary test block vector and expand the product inner
  -- product into the coordinate sum.
  ext z
  simp [LinearMap.lsum_apply, InnerProductSpace.toDualMap_apply_apply, PiLp.inner_apply]

omit [FiniteDimensional ℝ E] in
/-- Helper for Definition 12.17: transporting the `PiLp` block-separable conjugate through the
canonical coordinate equivalence reduces it to the plain finite-product conjugate from Theorem 4.3.
-/
theorem conjugate_function_separableSum_eq_conjugate_function_coordinate_sum
    {p : ℕ} (g : Fin p → E → EReal)
    (y : PiLp (2 : ENNReal) (fun _ : Fin p ↦ E)) :
    conjugate_function (PiLp.separableSum g)
      ((((LinearMap.lsum ℝ (fun _ : Fin p ↦ E) ℝ
          (fun i : Fin p ↦ InnerProductSpace.toDualMap ℝ E (-y i))).comp
        (PiLp.continuousLinearEquiv (2 : ENNReal) ℝ (fun _ : Fin p ↦ E)).toLinearMap) :
          Module.Dual ℝ (PiLp (2 : ENNReal) (fun _ : Fin p ↦ E)))) =
      conjugate_function (fun z : Fin p → E ↦ ∑ i : Fin p, g i (z i))
        (LinearMap.lsum ℝ (fun _ : Fin p ↦ E) ℝ
          (fun i : Fin p ↦ InnerProductSpace.toDualMap ℝ E (-y i))) := by
  let e : PiLp (2 : ENNReal) (fun _ : Fin p ↦ E) ≃L[ℝ] (Fin p → E) :=
    PiLp.continuousLinearEquiv (2 : ENNReal) ℝ (fun _ : Fin p ↦ E)
  -- Rewrite the conjugate supremum on `PiLp` and transport its range through the coordinate
  -- equivalence `e`.
  rw [conjugate_function_apply, conjugate_function_apply]
  have hrange :
      Set.range (fun x : PiLp (2 : ENNReal) (fun _ : Fin p ↦ E) ↦
        ((((LinearMap.lsum ℝ (fun _ : Fin p ↦ E) ℝ
            (fun i : Fin p ↦ InnerProductSpace.toDualMap ℝ E (-y i))).comp e.toLinearMap)
            x : ℝ) : EReal) - PiLp.separableSum g x) =
        Set.range (fun z : Fin p → E ↦
          (((LinearMap.lsum ℝ (fun _ : Fin p ↦ E) ℝ
              (fun i : Fin p ↦ InnerProductSpace.toDualMap ℝ E (-y i))) z : ℝ) : EReal) -
            ∑ i : Fin p, g i (z i)) := by
    -- The coordinate equivalence is bijective, so composing with it does not change the set of
    -- attainable affine-perturbation values in the conjugate formula.
    ext r
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨e x, ?_⟩
      simp [e]
    · rintro ⟨z, rfl⟩
      refine ⟨e.symm z, ?_⟩
      simp [e]
  rw [hrange]

omit [FiniteDimensional ℝ E] in
/-- Helper for Definition 12.17: the conjugate of the block-separable sum at `-y` is the sum of
the coordinate conjugates. -/
theorem conjugate_function_primal_separableSum_neg_eq_sum
    {p : ℕ} (g : Fin p → E → EReal)
    (hg_proper : ∀ i : Fin p, IsProperExtendedRealFunction (g i))
    (y : PiLp (2 : ENNReal) (fun _ : Fin p ↦ E)) :
    ((PiLp.separableSum g)∗) (-y) =
      ∑ i : Fin p, ((g i)∗) (-y i) := by
  -- Rewrite the primal conjugate through the Riesz map and transport the `PiLp` supremum to the
  -- coordinate product where Theorem 4.3 applies directly.
  rw [conjugate_function_primal_apply, toDualMap_neg_eq_lsum_comp_continuousLinearEquiv]
  rw [conjugate_function_separableSum_eq_conjugate_function_coordinate_sum]
  simpa [conjugate_function_primal_apply] using
    (conjugate_function_separable_sum_eq_sum_conjugate_function g hg_proper
      (fun i : Fin p ↦ InnerProductSpace.toDualMap ℝ E (-y i)))

-- Proof sketch: evaluate the Chapter 12.4 primal-space dual objective on the diagonal
-- duplication operator `dual_block_duplication E p`, then identify the adjoint term with
-- `∑ i, y i` and rewrite the separable conjugate term with
-- `conjugate_function_separable_sum_eq_sum_conjugate_function`, which now uses the canonical
-- properness owner on the block functions `g i`.
/-- The Chapter 12.4 dual objective specialized to the block-separable model agrees with the
source-facing block dual objective from Definition 12.17, under the canonical block-properness
hypothesis needed for the separable-conjugate bridge. -/
theorem dual_block_proximal_gradient_lagrange_dual_objective_primal_eq_dual_objective
    {p : ℕ} (f : E → EReal) (g : Fin p → E → EReal)
    (hg_proper : ∀ i : Fin p, IsProperExtendedRealFunction (g i))
    (y : PiLp (2 : ENNReal) (fun _ : Fin p ↦ E)) :
    dual_based_proximal_gradient_lagrange_dual_objective_primal f
      (PiLp.separableSum g) (dual_block_duplication E p) y =
      q(f, g) y := by
  -- Route correction: keep the Chapter 12.4 owner intact and bridge only the adjoint and
  -- separable-conjugate terms to the textbook block formula.
  rw [dual_based_proximal_gradient_lagrange_dual_objective_primal_apply,
    dual_block_proximal_gradient_dual_objective_apply]
  -- The two bridge lemmas exactly match the source proof: the duplication adjoint sums the blocks,
  -- and the conjugate of the separable sum splits coordinatewise.
  rw [dual_block_duplication_linear_adjoint_apply,
    conjugate_function_primal_separableSum_neg_eq_sum (g := g) hg_proper]

end

end
