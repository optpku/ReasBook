/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

noncomputable section

universe u v

variable {ι : Type u}

/-- The positive population weights `m_j` used in the continuous location model. -/
abbrev ContinuousLocationWeights (ι : Type u) :=
  ι → {m : ℝ // 0 < m}

namespace ContinuousLocationWeights

@[simp] theorem weights_pos (weights : ContinuousLocationWeights ι) (j : ι) :
    0 < (weights j : ℝ) :=
  (weights j).2

end ContinuousLocationWeights

section

variable [Fintype ι]
variable (E : Type v) [NormedAddCommGroup E]

/-- The dual feasible set `Q₂`, consisting of tuples whose components all have norm at most `1`. -/
def continuousLocationDualAdmissibleSet : Set (ι → E) :=
  {u | ∀ j, ‖u j‖ ≤ 1}

/-- The weighted Euclidean norm on dual tuples used to define the prox-function `d₂`. -/
def continuousLocationDualTupleNorm
    (weights : ContinuousLocationWeights ι) (u : ι → E) : ℝ :=
  Real.sqrt (∑ j, (weights j : ℝ) * ‖u j‖ ^ (2 : ℕ))

/-- The prox-function `d₂(u) = (1 / 2) \sum_j m_j \|u_j\|^2`, written via the weighted
tuple norm. -/
def continuousLocationDualProxFunction
    (weights : ContinuousLocationWeights ι) : (ι → E) → ℝ :=
  fun u ↦ (1 / 2 : ℝ) * (continuousLocationDualTupleNorm E weights u) ^ (2 : ℕ)

end

section

variable [Fintype ι]

/-- The total population weight `P = \sum_j m_j` in the continuous location model. -/
def continuousLocationTotalPopulation (weights : ContinuousLocationWeights ι) : ℝ :=
  ∑ j, (weights j : ℝ)

end

variable [Fintype ι]

-- Proof sketch: unfold `continuousLocationTotalPopulation`.
/-- Expanding `continuousLocationTotalPopulation` gives the finite sum `\sum_j m_j`. -/
theorem continuousLocationTotalPopulation_def
    (weights : ContinuousLocationWeights ι) :
    continuousLocationTotalPopulation weights = ∑ j, (weights j : ℝ) :=
  rfl

section

variable [Fintype ι]
variable (E : Type v) [NormedAddCommGroup E]

/-- The quantity `D₂`, defined as the maximal value of the prox-function `d₂` on the dual
feasible set `Q₂`. -/
def continuousLocationDualProxMaximum (weights : ContinuousLocationWeights ι) : ℝ :=
  sSup (continuousLocationDualProxFunction E weights '' continuousLocationDualAdmissibleSet E)

end

section

variable (E : Type v) [NormedAddCommGroup E]

-- Proof sketch: unfold `continuousLocationDualProxMaximum`.
/-- Expanding `continuousLocationDualProxMaximum` gives the supremum of `d₂` over `Q₂`. -/
theorem continuousLocationDualProxMaximum_def
    (weights : ContinuousLocationWeights ι) :
    continuousLocationDualProxMaximum E weights =
      sSup
        (continuousLocationDualProxFunction E weights ''
          continuousLocationDualAdmissibleSet E) :=
  rfl

/-- Helper for Text 6 1 4 2 Population Interpretation: the prox-function is the weighted
quadratic `\frac12 \sum_j m_j \|u_j\|^2`. -/
lemma continuousLocationDualProxFunction_eq_half_weighted_sum_sq_norm
    (weights : ContinuousLocationWeights ι) (u : ι → E) :
    continuousLocationDualProxFunction E weights u =
      (1 / 2 : ℝ) * ∑ j, (weights j : ℝ) * ‖u j‖ ^ (2 : ℕ) := by
  -- Squaring the tuple norm removes the outer square root because each summand is nonnegative.
  have hnonneg : 0 ≤ ∑ j, (weights j : ℝ) * ‖u j‖ ^ (2 : ℕ) := by
    refine Finset.sum_nonneg ?_
    intro j _
    exact mul_nonneg (le_of_lt (ContinuousLocationWeights.weights_pos weights j))
      (sq_nonneg ‖u j‖)
  rw [continuousLocationDualProxFunction, continuousLocationDualTupleNorm, Real.sq_sqrt hnonneg]

/-- Helper for Text 6 1 4 2 Population Interpretation: every admissible tuple has prox-value at
most half of the total population weight. -/
lemma continuousLocationDualProxFunction_le_half_totalPopulation_of_mem
    (weights : ContinuousLocationWeights ι) {u : ι → E}
    (hu : u ∈ continuousLocationDualAdmissibleSet E) :
    continuousLocationDualProxFunction E weights u ≤
      continuousLocationTotalPopulation weights / 2 := by
  -- Each feasibility constraint `‖u_j‖ ≤ 1` upgrades to `‖u_j‖^2 ≤ 1`.
  have hsquare_le_one : ∀ j, ‖u j‖ ^ (2 : ℕ) ≤ 1 := by
    intro j
    nlinarith [norm_nonneg (u j), hu j]
  have hsum_le :
      ∑ j, (weights j : ℝ) * ‖u j‖ ^ (2 : ℕ) ≤
        ∑ j, (weights j : ℝ) := by
    -- Summing the coordinatewise inequalities gives the global quadratic bound.
    refine Finset.sum_le_sum ?_
    intro j _
    calc
      (weights j : ℝ) * ‖u j‖ ^ (2 : ℕ) ≤ (weights j : ℝ) * 1 := by
        exact mul_le_mul_of_nonneg_left (hsquare_le_one j)
          (le_of_lt (ContinuousLocationWeights.weights_pos weights j))
      _ = (weights j : ℝ) := by simp
  -- Rewrite the prox-function and compare it to the total population sum.
  rw [continuousLocationDualProxFunction_eq_half_weighted_sum_sq_norm]
  simpa [continuousLocationTotalPopulation_def, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    using
      (mul_le_mul_of_nonneg_left hsum_le (show 0 ≤ (1 / 2 : ℝ) by norm_num))

/-- Helper for Text 6 1 4 2 Population Interpretation: if every component has unit norm, then the
prox-function attains exactly half of the total population weight. -/
lemma continuousLocationDualProxFunction_eq_half_totalPopulation_of_forall_norm_eq_one
    (weights : ContinuousLocationWeights ι) {u : ι → E}
    (hu : ∀ j, ‖u j‖ = 1) :
    continuousLocationDualProxFunction E weights u =
      continuousLocationTotalPopulation weights / 2 := by
  -- Unit norms force each quadratic term to collapse to its weight.
  rw [continuousLocationDualProxFunction_eq_half_weighted_sum_sq_norm]
  have hsum_eq :
      ∑ j, (weights j : ℝ) * ‖u j‖ ^ (2 : ℕ) =
        ∑ j, (weights j : ℝ) := by
    refine Finset.sum_congr rfl ?_
    intro j _
    simp [hu j]
  rw [hsum_eq]
  simp [continuousLocationTotalPopulation_def, div_eq_mul_inv, mul_comm]

-- Proof sketch: in a nontrivial real normed space, choose for each block `u_j` a unit vector;
-- then every component saturates the constraint `‖u_j‖ ≤ 1`, so `d₂(u) = (1 / 2) * ∑_j m_j`.
-- The reverse inequality follows because each admissible block has norm at most `1`, hence
-- `‖u_j‖^2 ≤ 1` in the weighted sum defining `d₂`.
/-- Text 6 1 4 2 Population Interpretation: in a nontrivial real normed space, the maximal value
`D₂` of the prox-function `d₂` on `Q₂` equals `P / 2`, where `P = \sum_j m_j` is the total
population weight of the model. -/
theorem continuousLocationDualProxMaximum_eq_half_totalPopulation
    [NormedSpace ℝ E] [Nontrivial E] (weights : ContinuousLocationWeights ι) :
    continuousLocationDualProxMaximum E weights = continuousLocationTotalPopulation weights / 2 :=
by
  let s : Set ℝ :=
    continuousLocationDualProxFunction E weights '' continuousLocationDualAdmissibleSet E
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  let e : E := (‖x‖⁻¹ : ℝ) • x
  let uStar : ι → E := fun _ ↦ e
  have huStar_norm : ∀ j, ‖uStar j‖ = 1 := by
    -- The normalized nonzero vector gives a unit vector in every coordinate.
    intro j
    simpa [uStar, e] using (norm_smul_inv_norm (𝕜 := ℝ) (x := x) hx)
  have huStar_mem : uStar ∈ continuousLocationDualAdmissibleSet E := by
    -- The constant unit tuple lies in the coordinatewise unit ball.
    intro j
    rw [huStar_norm j]
  have huStar_value :
      continuousLocationDualProxFunction E weights uStar =
        continuousLocationTotalPopulation weights / 2 := by
    -- Saturating every coordinate makes the prox-function hit the target value.
    exact continuousLocationDualProxFunction_eq_half_totalPopulation_of_forall_norm_eq_one
      E weights huStar_norm
  have huStar_image : continuousLocationDualProxFunction E weights uStar ∈ s := by
    exact ⟨uStar, huStar_mem, rfl⟩
  have hUpper : ∀ y ∈ s, y ≤ continuousLocationTotalPopulation weights / 2 := by
    -- Every image point comes from an admissible tuple, so the universal upper bound applies.
    intro y hy
    rcases hy with ⟨u, hu, rfl⟩
    exact continuousLocationDualProxFunction_le_half_totalPopulation_of_mem E weights hu
  have hBdd : BddAbove s := by
    exact ⟨continuousLocationTotalPopulation weights / 2, hUpper⟩
  have hsSup :
      sSup s = continuousLocationTotalPopulation weights / 2 := by
    refine le_antisymm ?_ ?_
    · -- The supremum is bounded above by the common admissible upper bound.
      exact csSup_le ⟨_, huStar_image⟩ hUpper
    · -- The explicit unit tuple shows the upper bound is attained inside the image.
      exact le_csSup_of_le hBdd huStar_image (le_of_eq huStar_value.symm)
  simpa [continuousLocationDualProxMaximum_def, s] using hsSup

end

end
