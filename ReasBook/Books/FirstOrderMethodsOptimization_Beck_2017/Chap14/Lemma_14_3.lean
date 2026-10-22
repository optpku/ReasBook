/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap05.Lemma_5_7
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_10
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_3
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_6
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_30
import FirstOrderMethodsOptimization_Beck_2017.Chap11.Definition_11_4
import FirstOrderMethodsOptimization_Beck_2017.Chap11.Lemma_11_3
import FirstOrderMethodsOptimization_Beck_2017.Chap14.Algorithm_14_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe v

open scoped Gradient

section

variable {Ei : Fin 2 → Type v}

/- `Lemma 14.3` is `source-facing`: its public step data are the exact alternating-minimization
half-step `x^{k+1/2}` and next iterate `x^{k+1}` from the Chapter 14 Gauss-Seidel minimization
rule, not a Chapter 11 prox-gradient update map.

This file now reuses the canonical Chapter 11/14 owners from `Chap11.Definition_11_4` and
`Chap14.Algorithm_14_3` directly. Its local API is therefore limited to the genuinely
Lemma 14.3-specific two-block bridges needed to compare each exact alternating-minimization
subproblem with the corresponding one-block prox-gradient candidate. -/

section LocalSupport

variable [∀ i, NormedAddCommGroup (Ei i)]

/-- Helper for Lemma 14.3: a zero block displacement leaves the ambient point unchanged. -/
@[simp] theorem block_coordinate_update_zero
    (x : (i : Fin 2) → Ei i) (i : Fin 2) :
    block_coordinate_update x i 0 = x := by
  -- The zero single-coordinate perturbation is the zero function, so the update is trivial.
  ext j
  by_cases hji : j = i
  · subst j
    simp [block_coordinate_update]
  · simp [block_coordinate_update]

/-- Helper for Lemma 14.3: updating block `i` by the residual to a target value reaches that
target exactly. -/
@[simp] theorem block_coordinate_update_apply_target
    (x : (i : Fin 2) → Ei i) (i : Fin 2) (yi : Ei i) :
    block_coordinate_update x i (yi - x i) i = yi := by
  -- Replacing the active block by the residual displacement lands exactly at the target.
  simp [block_coordinate_update, sub_eq_add_neg, add_left_comm]

/-- Helper for Lemma 14.3: updating block `i` by the residual to a target value is the direct
`Function.update` to that target. -/
theorem block_coordinate_update_eq_update_target
    (x : (i : Fin 2) → Ei i) (i : Fin 2) (yi : Ei i) :
    block_coordinate_update x i (yi - x i) = Function.update x i yi := by
  rw [block_coordinate_update_eq_update]
  simp [sub_eq_add_neg, add_left_comm]

end LocalSupport

section Comparison

variable {f : ((i : Fin 2) → Ei i) → EReal} {g : (i : Fin 2) → Ei i → EReal}
variable {block_gradient : (i : Fin 2) → ((j : Fin 2) → Ei j) → Ei i}
variable {XStar : Set ((i : Fin 2) → Ei i)} {FOpt : ℝ}
variable {Li : (i : Fin 2) → PosReal}

local notation "F" => composite_model_objective f (separableSum g)

variable {xk : effective_domain (separableSum g)} {xNext : (i : Fin 2) → Ei i}

local notation "xHalf" => alternating_minimization_partial_state xk xNext 0 (xNext 0)

/-- Helper for Lemma 14.3: in the first subproblem of a two-block cycle, the Chapter 14 mixed
state is just the direct update of the first coordinate. -/
lemma alternating_minimization_partial_state_zero_eq_update
    (xk xNext : (j : Fin 2) → Ei j) (xi : Ei 0) :
    alternating_minimization_partial_state xk xNext 0 xi =
      Function.update xk 0 xi := by
  funext j
  fin_cases j
  · simp [alternating_minimization_partial_state, Function.update]
  · simp [alternating_minimization_partial_state, Function.update]

/-- Helper for Lemma 14.3: in the second subproblem, the mixed state is the half-step with only
the second coordinate replaced by the candidate value. -/
lemma alternating_minimization_partial_state_one_eq_update_half
    (xk xNext : (j : Fin 2) → Ei j) (xi : Ei 1) :
    alternating_minimization_partial_state xk xNext 1 xi =
      Function.update (alternating_minimization_partial_state xk xNext 0 (xNext 0)) 1 xi := by
  funext j
  fin_cases j
  · simp [alternating_minimization_partial_state, Function.update]
  · simp [alternating_minimization_partial_state, Function.update]

/-- Helper for Lemma 14.3: updating the half-step at the second block by the chosen next-block
value recovers the full next iterate. -/
lemma half_step_update_second_eq_next
    (xk xNext : (j : Fin 2) → Ei j) :
    Function.update (alternating_minimization_partial_state xk xNext 0 (xNext 0)) 1 (xNext 1) =
      xNext := by
  funext j
  fin_cases j
  · simp [alternating_minimization_partial_state, Function.update]
  · simp [Function.update]

section UpdateSupport

variable [∀ i, NormedAddCommGroup (Ei i)]

/-- Helper for Lemma 14.3: two successive updates of the same block add their displacements. -/
lemma block_coordinate_update_add
    {i : Fin 2} (x : (j : Fin 2) → Ei j) (d e : Ei i) :
    block_coordinate_update (block_coordinate_update x i d) i e =
      block_coordinate_update x i (d + e) := by
  classical
  ext j
  by_cases hji : j = i
  · subst j
    simp [block_coordinate_update, add_left_comm, add_comm]
  · simp [block_coordinate_update, hji]

/-- Helper for Lemma 14.3: re-updating a block by the residual displacement reaches the target
value directly. -/
lemma block_coordinate_update_sub
    {i : Fin 2} (x : (j : Fin 2) → Ei j) (d e : Ei i) :
    block_coordinate_update (block_coordinate_update x i d) i (e - d) =
      block_coordinate_update x i e := by
  -- Collapse the second displacement into a single update on the original state.
  calc
    block_coordinate_update (block_coordinate_update x i d) i (e - d) =
        block_coordinate_update x i (d + (e - d)) := by
      rw [block_coordinate_update_add]
    _ = block_coordinate_update x i e := by
      congr 2
      abel

/-- Helper for Lemma 14.3: affine combinations commute with a fixed block update. -/
lemma block_coordinate_update_affine_combination
    [∀ i, NormedSpace ℝ (Ei i)]
    {i : Fin 2} (x : (j : Fin 2) → Ei j) (d e : Ei i)
    {a b : ℝ} (hab : a + b = 1) :
    a • block_coordinate_update x i d + b • block_coordinate_update x i e =
      block_coordinate_update x i (a • d + b • e) := by
  classical
  ext j
  by_cases hji : j = i
  · subst j
    calc
      a • block_coordinate_update x i d i + b • block_coordinate_update x i e i =
          (a • x i + b • x i) + (a • d + b • e) := by
            simp [block_coordinate_update, smul_add, add_assoc, add_left_comm, add_comm]
      _ = (a + b) • x i + (a • d + b • e) := by
        rw [← add_smul]
      _ = x i + (a • d + b • e) := by
        simp [hab]
      _ = block_coordinate_update x i (a • d + b • e) i := by
        simp [block_coordinate_update]
  · calc
      a • block_coordinate_update x i d j + b • block_coordinate_update x i e j =
          a • x j + b • x j := by
            simp [block_coordinate_update, hji]
      _ = (a + b) • x j := by
        rw [← add_smul]
      _ = block_coordinate_update x i (a • d + b • e) j := by
        simp [block_coordinate_update, hji, hab]

/-- Helper for Lemma 14.3: replacing one finite block by another finite block value preserves the
effective domain of the two-block separable sum. -/
lemma block_coordinate_update_mem_effective_domain_separableSum
    (hg_proper : ∀ j : Fin 2, IsProperExtendedRealFunction (g j))
    {i : Fin 2} {x : (j : Fin 2) → Ei j}
    (hx : x ∈ effective_domain (separableSum g))
    {yi : Ei i} (hyi : yi ∈ effective_domain (g i)) :
    block_coordinate_update x i (yi - x i) ∈ effective_domain (separableSum g) := by
  -- Route correction: for two blocks it is cheaper to rewrite each branch explicitly than to
  -- rebuild a general inactive-penalty API.
  fin_cases i
  · have hx1 : x 1 ∈ effective_domain (g 1) :=
      block_mem_effective_domain_of_mem_separableSum_effective_domain g hg_proper hx 1
    change Ei 0 at yi
    change yi ∈ effective_domain (g 0) at hyi
    have hact : x 0 + (yi - x 0) = yi := by
      abel
    have hsum_ne_top : g 0 yi + g 1 (x 1) ≠ ⊤ :=
      EReal.add_ne_top (mem_effective_domain.mp hyi).ne (mem_effective_domain.mp hx1).ne
    refine mem_effective_domain.mpr (lt_top_iff_ne_top.mpr ?_)
    -- The first updated point has coordinates `(yi, x 1)`, so both regularizer terms stay finite.
    intro htop
    change separableSum g (block_coordinate_update x 0 (yi - x 0)) = ⊤ at htop
    have hcoord0 : block_coordinate_update x 0 (yi - x 0) 0 = x 0 + (yi - x 0) := by
      simp [block_coordinate_update]
    have hcoord1 : block_coordinate_update x 0 (yi - x 0) 1 = x 1 := by
      simp [block_coordinate_update]
    rw [separableSum_apply, Fin.sum_univ_two, hcoord0, hcoord1] at htop
    rw [hact] at htop
    have hsum_top : g 0 yi + g 1 (x 1) = ⊤ := htop
    exact hsum_ne_top hsum_top
  · have hx0 : x 0 ∈ effective_domain (g 0) :=
      block_mem_effective_domain_of_mem_separableSum_effective_domain g hg_proper hx 0
    change Ei 1 at yi
    change yi ∈ effective_domain (g 1) at hyi
    have hact : x 1 + (yi - x 1) = yi := by
      abel
    have hsum_ne_top : g 0 (x 0) + g 1 yi ≠ ⊤ :=
      EReal.add_ne_top (mem_effective_domain.mp hx0).ne (mem_effective_domain.mp hyi).ne
    refine mem_effective_domain.mpr (lt_top_iff_ne_top.mpr ?_)
    -- The second updated point has coordinates `(x 0, yi)`, so the same finite-sum argument
    -- applies in the other branch.
    intro htop
    change separableSum g (block_coordinate_update x 1 (yi - x 1)) = ⊤ at htop
    have hcoord0 : block_coordinate_update x 1 (yi - x 1) 0 = x 0 := by
      simp [block_coordinate_update]
    have hcoord1 : block_coordinate_update x 1 (yi - x 1) 1 = x 1 + (yi - x 1) := by
      simp [block_coordinate_update]
    rw [separableSum_apply, Fin.sum_univ_two, hcoord0, hcoord1] at htop
    rw [hact] at htop
    have hsum_top : g 0 (x 0) + g 1 yi = ⊤ := htop
    exact hsum_ne_top hsum_top

/-- Helper for Lemma 14.3: replacing one block by a target value splits the full objective into
the active block term plus the frozen inactive penalty. -/
lemma block_update_full_objective_split
    {i : Fin 2} {x : (j : Fin 2) → Ei j} (yi : Ei i) :
    F (block_coordinate_update x i (yi - x i)) =
      f (block_coordinate_update x i (yi - x i)) + g i yi +
        ∑ j ∈ Finset.univ.erase i, g j (x j) := by
  fin_cases i
  · -- For the first block, the inactive penalty is exactly the second coordinate term.
    change Ei 0 at yi
    have hsum0 : ∑ j ∈ Finset.univ.erase 0, g j (x j) = g 1 (x 1) := by
      rw [show (Finset.univ.erase (0 : Fin 2)) = ({1} : Finset (Fin 2)) by decide]
      simp
    have hact : x 0 + (yi - x 0) = yi := by
      abel
    calc
      F (block_coordinate_update x 0 (yi - x 0)) =
          f (block_coordinate_update x 0 (yi - x 0)) +
            (g 0 (x 0 + (yi - x 0)) + g 1 (x 1)) := by
              rw [composite_model_objective_apply, separableSum_apply, Fin.sum_univ_two]
              simp [block_coordinate_update]
      _ = f (block_coordinate_update x 0 (yi - x 0)) + g 0 yi +
            ∑ j ∈ Finset.univ.erase 0, g j (x j) := by
              rw [hact, hsum0]
              simp [add_assoc]
  · -- The second-block branch is the symmetric decomposition.
    change Ei 1 at yi
    have hsum1 : ∑ j ∈ Finset.univ.erase 1, g j (x j) = g 0 (x 0) := by
      rw [show (Finset.univ.erase (1 : Fin 2)) = ({0} : Finset (Fin 2)) by decide]
      simp
    have hact : x 1 + (yi - x 1) = yi := by
      abel
    calc
      F (block_coordinate_update x 1 (yi - x 1)) =
          f (block_coordinate_update x 1 (yi - x 1)) +
            (g 0 (x 0) + g 1 (x 1 + (yi - x 1))) := by
              rw [composite_model_objective_apply, separableSum_apply, Fin.sum_univ_two]
              simp [block_coordinate_update, add_assoc, add_comm]
      _ = f (block_coordinate_update x 1 (yi - x 1)) + g 1 yi +
            ∑ j ∈ Finset.univ.erase 1, g j (x j) := by
              rw [hact, hsum1]
              simp [add_assoc, add_comm]

end UpdateSupport

section AlternatingStep

variable [∀ i, NormedAddCommGroup (Ei i)] [∀ i, NormedSpace ℝ (Ei i)]
variable (hstep : IsAlternatingMinimizationCompositeStep f g xk xNext)

/-- Helper for Lemma 14.3: the exact first-block minimizer beats every first-block competitor in
the full composite objective. -/
lemma first_block_exact_step_le_candidate
    (hstep : IsAlternatingMinimizationCompositeStep f g xk xNext)
    (xi : Ei 0) :
    F xHalf ≤ F (Function.update (xk : (j : Fin 2) → Ei j) 0 xi) := by
  -- Specialize the exact first-block minimizer at the arbitrary competitor `xi`.
  have hmin :
      f (block_coordinate_update (xk : (j : Fin 2) → Ei j) 0
          (xNext 0 - (xk : (j : Fin 2) → Ei j) 0)) +
          g 0 (xNext 0) ≤
        f (block_coordinate_update (xk : (j : Fin 2) → Ei j) 0
          (xi - (xk : (j : Fin 2) → Ei j) 0)) +
          g 0 xi := by
    simpa only [alternating_minimization_composite_block_objective_apply,
      alternating_minimization_partial_state_zero_eq_update,
      ← block_coordinate_update_eq_update_target] using
      (isMinOn_iff.mp (hstep.block_isMinOn 0)) xi (by simp)
  -- Add the frozen second-block penalty and rewrite both sides back to the full objective.
  have hmin_full :
      f (block_coordinate_update (xk : (j : Fin 2) → Ei j) 0
          (xNext 0 - (xk : (j : Fin 2) → Ei j) 0)) +
          g 0 (xNext 0) +
          ∑ j ∈ Finset.univ.erase 0, g j ((xk : (j : Fin 2) → Ei j) j) ≤
        f (block_coordinate_update (xk : (j : Fin 2) → Ei j) 0
          (xi - (xk : (j : Fin 2) → Ei j) 0)) +
          g 0 xi +
          ∑ j ∈ Finset.univ.erase 0, g j ((xk : (j : Fin 2) → Ei j) j) := by
    simpa [add_assoc, add_left_comm, add_comm] using
      add_le_add_right hmin (∑ j ∈ Finset.univ.erase 0, g j ((xk : (j : Fin 2) → Ei j) j))
  calc
    F xHalf =
        F (block_coordinate_update (xk : (j : Fin 2) → Ei j) 0
          (xNext 0 - (xk : (j : Fin 2) → Ei j) 0)) := by
          rw [alternating_minimization_partial_state_zero_eq_update,
            ← block_coordinate_update_eq_update_target]
    _ =
        f (block_coordinate_update (xk : (j : Fin 2) → Ei j) 0
          (xNext 0 - (xk : (j : Fin 2) → Ei j) 0)) +
          g 0 (xNext 0) +
          ∑ j ∈ Finset.univ.erase 0, g j ((xk : (j : Fin 2) → Ei j) j) := by
          rw [block_update_full_objective_split (x := (xk : (j : Fin 2) → Ei j)) (yi := xNext 0)]
    _ ≤
        f (block_coordinate_update (xk : (j : Fin 2) → Ei j) 0
          (xi - (xk : (j : Fin 2) → Ei j) 0)) +
          g 0 xi +
          ∑ j ∈ Finset.univ.erase 0, g j ((xk : (j : Fin 2) → Ei j) j) :=
      hmin_full
    _ = F (block_coordinate_update (xk : (j : Fin 2) → Ei j) 0
          (xi - (xk : (j : Fin 2) → Ei j) 0)) := by
          rw [block_update_full_objective_split (x := (xk : (j : Fin 2) → Ei j)) (yi := xi)]
    _ = F (Function.update (xk : (j : Fin 2) → Ei j) 0 xi) := by
          rw [block_coordinate_update_eq_update_target]

/-- Helper for Lemma 14.3: the exact half-step remains in the effective domain of the
block-separable regularizer. -/
lemma half_step_mem_effective_domain
    (hstep : IsAlternatingMinimizationCompositeStep f g xk xNext) :
    xHalf ∈ effective_domain (separableSum g) := by
  -- Compare the exact half-step against the original point to show the composite objective
  -- stays finite at `xHalf`.
  have hhalf_le : F xHalf ≤ F xk :=
    by simpa using first_block_exact_step_le_candidate hstep ((xk : (j : Fin 2) → Ei j) 0)
  have hmodel : IsAlternatingMinimizationCompositeModel f g :=
    hstep.toIsAlternatingMinimizationCompositeModel
  have hxk_int : (xk : (j : Fin 2) → Ei j) ∈ interior (effective_domain f) :=
    hmodel.g_effective_domain_subset_interior_f_effective_domain xk.2
  have hF_xk_ne_top : F xk ≠ ⊤ := by
    rw [composite_model_objective_apply]
    exact
      EReal.add_ne_top
        (mem_effective_domain.mp (interior_subset hxk_int)).ne
        (mem_effective_domain.mp xk.2).ne
  have hF_xHalf_ne_top : F xHalf ≠ ⊤ := by
    exact ne_of_lt (lt_of_le_of_lt hhalf_le (lt_top_iff_ne_top.mpr hF_xk_ne_top))
  -- If the separable sum were `⊤` at `xHalf`, then the full objective would also be `⊤`.
  have hsum_ne_top : separableSum g xHalf ≠ ⊤ := by
    intro hsum_top
    have hF_top : F xHalf = ⊤ := by
      rw [composite_model_objective_apply, hsum_top]
      exact EReal.add_top_of_ne_bot (hmodel.f_ne_bot xHalf)
    exact hF_xHalf_ne_top hF_top
  exact mem_effective_domain.mpr (lt_top_iff_ne_top.mpr hsum_ne_top)

/-- Helper for Lemma 14.3: the exact second-block minimizer beats every second-block competitor in
the full composite objective. -/
lemma second_block_exact_step_le_candidate
    (hstep : IsAlternatingMinimizationCompositeStep f g xk xNext)
    (xi : Ei 1) :
    F xNext ≤ F (Function.update xHalf 1 xi) := by
  -- Specialize the exact second-block minimizer at the arbitrary competitor `xi`.
  have hmin :
      f (block_coordinate_update xHalf 1 (xNext 1 - xHalf 1)) + g 1 (xNext 1) ≤
        f (block_coordinate_update xHalf 1 (xi - xHalf 1)) + g 1 xi := by
    simpa only [alternating_minimization_composite_block_objective_apply,
      alternating_minimization_partial_state_one_eq_update_half,
      half_step_update_second_eq_next,
      ← block_coordinate_update_eq_update_target] using
      (isMinOn_iff.mp (hstep.block_isMinOn 1)) xi (by simp)
  -- Add the frozen first-block penalty and rewrite back to the full objective.
  have hmin_full :
      f (block_coordinate_update xHalf 1 (xNext 1 - xHalf 1)) +
          g 1 (xNext 1) +
          ∑ j ∈ Finset.univ.erase 1, g j (xHalf j) ≤
        f (block_coordinate_update xHalf 1 (xi - xHalf 1)) +
          g 1 xi +
          ∑ j ∈ Finset.univ.erase 1, g j (xHalf j) := by
    simpa [add_assoc, add_left_comm, add_comm] using
      add_le_add_right hmin (∑ j ∈ Finset.univ.erase 1, g j (xHalf j))
  calc
    F xNext = F (Function.update xHalf 1 (xNext 1)) := by
      simpa using congrArg F
        (half_step_update_second_eq_next (xk := (xk : (j : Fin 2) → Ei j)) (xNext := xNext)).symm
    _ = F (block_coordinate_update xHalf 1 (xNext 1 - xHalf 1)) := by
      rw [← block_coordinate_update_eq_update_target]
    _ =
        f (block_coordinate_update xHalf 1 (xNext 1 - xHalf 1)) +
          g 1 (xNext 1) +
          ∑ j ∈ Finset.univ.erase 1, g j (xHalf j) := by
          rw [block_update_full_objective_split (x := xHalf) (yi := xNext 1)]
    _ ≤
        f (block_coordinate_update xHalf 1 (xi - xHalf 1)) +
          g 1 xi +
          ∑ j ∈ Finset.univ.erase 1, g j (xHalf j) :=
      hmin_full
    _ = F (block_coordinate_update xHalf 1 (xi - xHalf 1)) := by
          rw [block_update_full_objective_split (x := xHalf) (yi := xi)]
    _ = F (Function.update xHalf 1 xi) := by
          rw [block_coordinate_update_eq_update_target]

end AlternatingStep

section SufficientDecrease

variable [∀ i, NormedAddCommGroup (Ei i)] [∀ i, InnerProductSpace ℝ (Ei i)]

-- Proof sketch: since `xNext 0` is an exact minimizer of the first frozen-block subproblem,
-- `F xHalf` is at most the value at any competitor, in particular the first-block prox-gradient
-- candidate from Lemma 11.3. Applying
-- `block_partial_gradient_sufficient_decrease_of_block_lipschitz` to the current iterate `xk`
-- and block `0` then yields the displayed lower bound.
/-- First sufficient-decrease estimate for Lemma 14.3: if
`hcore : IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li`
supplies the Chapter 11 blockwise derivative and Lipschitz clauses extracted from the two-block
Assumption 14.12 setting, then the decrease from `x^k` to the exact half-step `x^{k+1/2}` is
bounded below by the squared first-block gradient mapping. -/
theorem alternating_minimization_two_block_half_step_sufficient_decrease
    [ProperSpace (Ei 0)]
    (hstep : IsAlternatingMinimizationCompositeStep f g xk xNext)
    (hcore : IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li) :
    F xk - F xHalf ≥
      ((((1 : ℝ) / (2 * (Li 0 : ℝ))) *
          ‖G[Li 0; hcore] xk 0‖ ^ (2 : ℕ) : ℝ) : EReal) := by
  let xPg : (j : Fin 2) → Ei j :=
    block_coordinate_update
      (xk : (j : Fin 2) → Ei j)
      0
      (T[Li 0; hcore] (xk : (j : Fin 2) → Ei j) 0 - (xk : (j : Fin 2) → Ei j) 0)
  let c : EReal :=
    ((((1 : ℝ) / (2 * (Li 0 : ℝ))) *
        ‖G[Li 0; hcore] (xk : (j : Fin 2) → Ei j) 0‖ ^ (2 : ℕ) : ℝ) : EReal)
  have hconvex : Convex ℝ (effective_domain f) := by
    intro x hx y hy a b ha hb hab
    simpa using
      hstep.toIsAlternatingMinimizationCompositeModel.f_effective_domain_convex
        hx hy ha hb hab
  -- First compare the exact half-step with the Chapter 11 prox-gradient candidate at block `0`.
  have hcandidate : F xHalf ≤ F xPg := by
    calc
      F xHalf ≤
          F (Function.update (xk : (j : Fin 2) → Ei j) 0
            (T[Li 0; hcore] (xk : (j : Fin 2) → Ei j) 0)) :=
        first_block_exact_step_le_candidate hstep (T[Li 0; hcore] (xk : (j : Fin 2) → Ei j) 0)
      _ = F xPg := by
        simp [xPg, block_coordinate_update_eq_update_target]
  -- Then import the one-block sufficient-decrease bound for the prox-gradient candidate.
  have hprox : F xk - F xPg ≥ c := by
    simpa [xPg, c] using
      IsBlockProximalGradientProblem.block_partial_gradient_sufficient_decrease_of_block_lipschitz
        (hproblem := hcore)
        (hf_effective_domain_convex := hconvex)
        (i := (0 : Fin 2))
        (M := Li 0)
        (h_block_gradient_lipschitz := fun x d hx hxd ↦ by
          simpa using hcore.block_partial_gradient_lipschitz 0 hx hxd)
        xk
  have hxHalf_eff : xHalf ∈ effective_domain (separableSum g) :=
    half_step_mem_effective_domain hstep
  have hxHalf_int : xHalf ∈ interior (effective_domain f) :=
    hcore.mem_interior_effective_domain_of_mem_g_effective_domain hxHalf_eff
  have hF_xHalf_ne_bot : F xHalf ≠ ⊥ := by
    rw [composite_model_objective_apply, EReal.add_ne_bot_iff]
    exact ⟨hcore.f_ne_bot xHalf, (separableSum_proper g hcore.block_g_proper).ne_bot xHalf⟩
  have hF_xHalf_ne_top : F xHalf ≠ ⊤ := by
    rw [composite_model_objective_apply]
    exact
      EReal.add_ne_top
        (mem_effective_domain.mp (interior_subset hxHalf_int)).ne
        (mem_effective_domain.mp hxHalf_eff).ne
  -- Replace the prox-gradient comparison point by the exact half-step in the additive form.
  have hadd : c + F xHalf ≤ F xk := by
    calc
      c + F xHalf ≤ c + F xPg := by
        simpa [add_assoc, add_left_comm, add_comm] using add_le_add_right hcandidate c
      _ ≤ F xk := EReal.add_le_of_le_sub hprox
  have hresult : c ≤ F xk - F xHalf :=
    (EReal.le_sub_iff_add_le (Or.inl hF_xHalf_ne_bot) (Or.inl hF_xHalf_ne_top)).2 hadd
  simpa [c]
    using hresult

-- Proof sketch: now compare the exact second-block minimizer `xNext 1` against the second-block
-- prox-gradient candidate starting from the exact half-step `xHalf`. Since `xNext 1` minimizes
-- the second frozen-block objective, `F xNext` is no larger than the prox-gradient comparison
-- value. Apply the Chapter 11 one-block sufficient-decrease estimate at `xHalf` and block `1`.
/-- Second sufficient-decrease estimate for Lemma 14.3: under the same canonical
block-proximal-gradient owner `hcore`, the decrease from the exact half-step `x^{k+1/2}` to the
exact next iterate `x^{k+1}` is bounded below by the squared second-block gradient mapping. -/
theorem alternating_minimization_two_block_next_step_sufficient_decrease
    [ProperSpace (Ei 1)]
    (hstep : IsAlternatingMinimizationCompositeStep f g xk xNext)
    (hcore : IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li) :
    F xHalf - F xNext ≥
      ((((1 : ℝ) / (2 * (Li 1 : ℝ))) *
          ‖G[Li 1; hcore] xHalf 1‖ ^ (2 : ℕ) : ℝ) : EReal) := by
  let xPg : (j : Fin 2) → Ei j :=
    block_coordinate_update xHalf 1 (T[Li 1; hcore] xHalf 1 - xHalf 1)
  let c : EReal :=
    ((((1 : ℝ) / (2 * (Li 1 : ℝ))) *
        ‖G[Li 1; hcore] xHalf 1‖ ^ (2 : ℕ) : ℝ) : EReal)
  have hconvex : Convex ℝ (effective_domain f) := by
    intro x hx y hy a b ha hb hab
    simpa using
      hstep.toIsAlternatingMinimizationCompositeModel.f_effective_domain_convex
        hx hy ha hb hab
  have hxHalf_eff : xHalf ∈ effective_domain (separableSum g) :=
    half_step_mem_effective_domain hstep
  -- Compare the exact second-block step with the Chapter 11 prox-gradient candidate at `xHalf`.
  have hcandidate : F xNext ≤ F xPg := by
    calc
      F xNext ≤ F (Function.update xHalf 1 (T[Li 1; hcore] xHalf 1)) :=
        second_block_exact_step_le_candidate hstep (T[Li 1; hcore] xHalf 1)
      _ = F xPg := by
        simp [xPg, block_coordinate_update_eq_update_target]
  have hprox : F xHalf - F xPg ≥ c := by
    simpa [xPg, c] using
      IsBlockProximalGradientProblem.block_partial_gradient_sufficient_decrease_of_block_lipschitz
        (hproblem := hcore)
        (hf_effective_domain_convex := hconvex)
        (i := (1 : Fin 2))
        (M := Li 1)
        (h_block_gradient_lipschitz := fun x d hx hxd ↦ by
          simpa using hcore.block_partial_gradient_lipschitz 1 hx hxd)
        ⟨xHalf, hxHalf_eff⟩
  have hxHalf_int : xHalf ∈ interior (effective_domain f) :=
    hcore.mem_interior_effective_domain_of_mem_g_effective_domain hxHalf_eff
  have hF_xNext_ne_bot : F xNext ≠ ⊥ := by
    rw [composite_model_objective_apply, EReal.add_ne_bot_iff]
    exact ⟨hcore.f_ne_bot xNext, (separableSum_proper g hcore.block_g_proper).ne_bot xNext⟩
  have hF_xHalf_ne_top : F xHalf ≠ ⊤ := by
    rw [composite_model_objective_apply]
    exact
      EReal.add_ne_top
        (mem_effective_domain.mp (interior_subset hxHalf_int)).ne
        (mem_effective_domain.mp hxHalf_eff).ne
  have hF_xNext_ne_top : F xNext ≠ ⊤ := by
    exact ne_of_lt (lt_of_le_of_lt (second_block_exact_step_le_candidate hstep (xHalf 1))
      (by simpa using (lt_top_iff_ne_top.mpr hF_xHalf_ne_top)))
  -- Convert the prox-gradient decrease into the exact-step decrease in additive form.
  have hadd : c + F xNext ≤ F xHalf := by
    calc
      c + F xNext ≤ c + F xPg := by
        simpa [add_assoc, add_left_comm, add_comm] using add_le_add_right hcandidate c
      _ ≤ F xHalf := EReal.add_le_of_le_sub hprox
  have hresult : c ≤ F xHalf - F xNext :=
    (EReal.le_sub_iff_add_le (Or.inl hF_xNext_ne_bot) (Or.inl hF_xNext_ne_top)).2 hadd
  simpa [c]
    using hresult

-- Proof sketch: package the two source inequalities into the single textbook statement.
/-- Lemma 14.3: under Assumption 14.12 in its canonical Chapter 11/14 owner form, each half-step
of the two-block alternating minimization method satisfies the corresponding sufficient-decrease
estimate for the active block. -/
theorem alternating_minimization_two_block_sufficient_decrease
    [ProperSpace (Ei 0)] [ProperSpace (Ei 1)]
    (hstep : IsAlternatingMinimizationCompositeStep f g xk xNext)
    (hcore : IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li) :
    F xk - F xHalf ≥
        ((((1 : ℝ) / (2 * (Li 0 : ℝ))) *
            ‖G[Li 0; hcore] xk 0‖ ^ (2 : ℕ) : ℝ) : EReal) ∧
      F xHalf - F xNext ≥
        ((((1 : ℝ) / (2 * (Li 1 : ℝ))) *
            ‖G[Li 1; hcore] xHalf 1‖ ^ (2 : ℕ) : ℝ) : EReal) := by
  constructor
  · exact alternating_minimization_two_block_half_step_sufficient_decrease hstep hcore
  · exact alternating_minimization_two_block_next_step_sufficient_decrease hstep hcore

end SufficientDecrease

end Comparison

end
