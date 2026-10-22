/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.MetricSpace.HausdorffDistance
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Algorithm_14_3_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Lemma_14_3_2

noncomputable section

open Filter Metric

section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "DualSpace" => StrongDual ℝ E

open scoped Subgradient

-- Domain sampling for this item:
-- * primary domain: convex subgradient methods on real Hilbert spaces;
-- * core/canonical Chapter 14 owners reused here: the subgradient surface `∂ f(x)`,
--   `normalizedSubgradientDirection`, `sunYuanOptimalSolutionSet`, `optimalValue`, and the chapter owner
--   `SubgradientMethod`;
-- * source-facing bridge kept here: the Polyak recursion with the source stopping branch
--   "if the current iterate is optimal, keep it fixed";
-- * canonical bridge added below: under the stronger regime where every iterate remains
--   nonoptimal, the Polyak recursion refines to the chapter owner `SubgradientMethod`.

/-- The linear rate `q = (1 - λ * (2 - λ) * (cHat / cBar)^2)^(1 / 2)` from the source theorem. -/
def polyakSubgradientLinearRate (lam cBar cHat : ℝ) : ℝ :=
  Real.sqrt (1 - lam * (2 - lam) * (cHat / cBar) ^ (2 : ℕ))

/-- Unfolding `polyakSubgradientLinearRate lam cBar cHat` gives the source formula for `q`. -/
@[simp] theorem polyakSubgradientLinearRate_eq (lam cBar cHat : ℝ) :
    polyakSubgradientLinearRate lam cBar cHat =
      Real.sqrt (1 - lam * (2 - lam) * (cHat / cBar) ^ (2 : ℕ)) :=
  rfl

/-- `HasPolyakSubgradientGeometricRate x xStar q` records the source geometric estimate
`‖x (k + 1) - xStar‖ ≤ M * q ^ k` with some positive constant `M` and rate `q < 1`. -/
def HasPolyakSubgradientGeometricRate (x : ℕ → E) (xStar : E) (q : ℝ) : Prop :=
  q < 1 ∧
    ∃ M : Set.Ioi (0 : ℝ),
      ∀ k : ℕ, ‖x (k + 1) - xStar‖ ≤ M.1 * q ^ k

section

omit [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Unfolding `HasPolyakSubgradientGeometricRate x xStar q` gives the source geometric estimate
with explicit `q < 1` and a positive constant `M`. -/
theorem hasPolyakSubgradientGeometricRate_iff
    (x : ℕ → E) (xStar : E) (q : ℝ) :
    HasPolyakSubgradientGeometricRate x xStar q ↔
      q < 1 ∧
        ∃ M : Set.Ioi (0 : ℝ),
          ∀ k : ℕ, ‖x (k + 1) - xStar‖ ≤ M.1 * q ^ k :=
  Iff.rfl

end

section

omit [CompleteSpace E]

/-- If the zero functional lies in the subdifferential of `f` at `x`, then `x` is a global
minimizer of `f`. -/
theorem mem_sunYuanOptimalSolutionSet_of_zero_mem_subdifferential
    (f : E → ℝ) {x : E} (h_zero : (0 : DualSpace) ∈ ∂ f(x)) :
    x ∈ S⋆[f] := by
  -- The zero subgradient inequality is exactly the global-minimizer inequality on `Set.univ`.
  rw [mem_sunYuanOptimalSolutionSet_iff, isMinOn_univ_iff]
  simpa using (mem_subdifferential_iff f x (0 : DualSpace)).1 h_zero

end

section

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Helper for Chapter14 Theorem 14.3.6: a point lies in the optimal solution set exactly when
its objective value equals the optimal value. -/
theorem mem_sunYuanOptimalSolutionSet_iff_eq_optimalValue
    (f : E → ℝ) (h_solution : Set.Nonempty S⋆[f]) (x : E) :
    x ∈ S⋆[f] ↔ f x = f⋆[f] := by
  constructor
  · intro hx
    -- A global minimizer gives a lower bound for the whole range, so its value is the infimum.
    rw [mem_sunYuanOptimalSolutionSet_iff, isMinOn_univ_iff] at hx
    have h_bddBelow : BddBelow (Set.range f) := ⟨f x, by
      rintro _ ⟨y, rfl⟩
      exact hx y⟩
    apply le_antisymm
    · refine le_csInf ⟨f x, ⟨x, rfl⟩⟩ ?_
      rintro _ ⟨y, rfl⟩
      exact hx y
    · simpa [optimalValue_eq_sInf_range] using
        (csInf_le h_bddBelow (show f x ∈ Set.range f by exact ⟨x, rfl⟩))
  · intro hx
    -- Equality with `f⋆[f]` turns the universal lower bound from `sInf` into optimality.
    rw [mem_sunYuanOptimalSolutionSet_iff, isMinOn_univ_iff]
    rcases h_solution with ⟨xStar, hxStar⟩
    have hxStar_min : IsMinOn f Set.univ xStar := by
      simpa [mem_sunYuanOptimalSolutionSet_iff] using hxStar
    have hxStar_lower : ∀ y : E, f xStar ≤ f y := by
      simpa [isMinOn_univ_iff] using hxStar_min
    have h_bddBelow : BddBelow (Set.range f) := ⟨f xStar, by
      rintro _ ⟨y, rfl⟩
      exact hxStar_lower y⟩
    intro y
    have hy_lower : f⋆[f] ≤ f y := by
      simpa [optimalValue_eq_sInf_range] using
        (csInf_le h_bddBelow (show f y ∈ Set.range f by exact ⟨y, rfl⟩))
    simpa [hx] using hy_lower

end

/-- `IsPolyakSubgradientMethod f x g lam` records Algorithm 14.3.1 started at `x 1`, with
`g (k + 1) ∈ ∂ f(x (k + 1))` for every stage. If `x (k + 1)` is not optimal, then the
source Polyak update `(14.3.34)` is written on the chapter owner `normalizedSubgradientDirection`
as
`x (k + 2) = x (k + 1) + (λ * (f (x (k + 1)) - f⋆[f]) / ‖g (k + 1)‖) •
normalizedSubgradientDirection (g (k + 1))`; equivalently, this is the usual expanded Riesz-map
formula from the source. If `x (k + 1)` is optimal, the next iterate stays fixed at
`x (k + 1)`. -/
structure IsPolyakSubgradientMethod
    (f : E → ℝ) (x : ℕ → E) (g : ℕ → DualSpace) (lam : ℝ) : Prop where
  subgradient_mem (k : ℕ) :
    g (k + 1) ∈ ∂ f(x (k + 1))
  iterate_succ_of_not_optimal (k : ℕ)
      (hk : x (k + 1) ∉ S⋆[f]) :
      x (k + 2) =
        x (k + 1) +
          (lam * (f (x (k + 1)) - f⋆[f]) / ‖g (k + 1)‖) •
            normalizedSubgradientDirection (g (k + 1))
  iterate_succ_of_optimal (k : ℕ)
      (hk : x (k + 1) ∈ S⋆[f]) :
      x (k + 2) = x (k + 1)

namespace IsPolyakSubgradientMethod

variable {f : E → ℝ} {x : ℕ → E} {g : ℕ → DualSpace} {lam : ℝ}

private theorem eq_add_one_of_one_le {k : ℕ} (hk : 1 ≤ k) :
    ∃ m : ℕ, k = m + 1 := by
  -- Reindex every positive stage as the source stage `m + 1`.
  refine ⟨k - 1, ?_⟩
  have hk_pos : 0 < k := lt_of_lt_of_le (by decide : 0 < 1) hk
  simpa [Nat.succ_eq_add_one] using (Nat.succ_pred_eq_of_pos hk_pos).symm

/-- In a Polyak recursion, a nonoptimal iterate cannot carry the zero subgradient, because
`0 ∈ ∂ f(x)` already forces `x ∈ S⋆[f]`. -/
theorem subgradient_ne_zero_of_not_optimal
    (g : ℕ → DualSpace) (h_method : IsPolyakSubgradientMethod f x g lam) (k : ℕ)
    (hk : x (k + 1) ∉ S⋆[f]) :
    g (k + 1) ≠ (0 : DualSpace) := by
  -- If the chosen subgradient vanished, the previous bridge would make the iterate optimal.
  intro hg_zero
  apply hk
  have h_zero_mem : (0 : DualSpace) ∈ ∂ f(x (k + 1)) := by
    simpa [hg_zero] using h_method.subgradient_mem k
  exact mem_sunYuanOptimalSolutionSet_of_zero_mem_subdifferential f h_zero_mem

section

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- If the optimal solution set is nonempty, then the Polyak numerator `f(x_(k+1)) - f⋆[f]` is
strictly positive at every nonoptimal iterate. -/
theorem objectiveGap_pos_of_not_optimal
    (h_solution : Set.Nonempty S⋆[f]) (k : ℕ)
    (hk : x (k + 1) ∉ S⋆[f]) :
    0 < f (x (k + 1)) - f⋆[f] := by
  -- The source theorem assumes `S⋆[f]` is nonempty; the strict gap itself follows because
  -- equality with `f⋆[f]` would already imply optimality.
  rcases h_solution with ⟨xStar, hxStar⟩
  have hxStar_min : IsMinOn f Set.univ xStar := by
    simpa [mem_sunYuanOptimalSolutionSet_iff] using hxStar
  have hxStar_lower : ∀ y : E, f xStar ≤ f y := by
    simpa [isMinOn_univ_iff] using hxStar_min
  have h_bddBelow : BddBelow (Set.range f) := ⟨f xStar, by
    rintro _ ⟨y, rfl⟩
    exact hxStar_lower y⟩
  have h_lower : f⋆[f] ≤ f (x (k + 1)) := by
    simpa [optimalValue_eq_sInf_range] using
      (csInf_le h_bddBelow (show f (x (k + 1)) ∈ Set.range f by exact ⟨x (k + 1), rfl⟩))
  have h_ne : f (x (k + 1)) ≠ f⋆[f] := by
    intro h_eq
    apply hk
    exact (mem_sunYuanOptimalSolutionSet_iff_eq_optimalValue f ⟨xStar, hxStar⟩ (x (k + 1))).2 h_eq
  exact sub_pos.mpr (lt_of_le_of_ne h_lower (Ne.symm h_ne))

end

/-- Helper for Chapter14 Theorem 14.3.6: every positive stage in the Polyak recursion carries the
recorded subgradient membership needed by the chapter owner `SubgradientMethod`. -/
theorem polyak_subgradient_mem_at
    (g : ℕ → DualSpace)
    (h_method : IsPolyakSubgradientMethod f x g lam) {k : ℕ} (hk : 1 ≤ k) :
    g k ∈ ∂ f(x k) := by
  -- Reindex the positive stage `k` back to the source indexing `m + 1`.
  obtain ⟨m, rfl⟩ := eq_add_one_of_one_le hk
  simpa using h_method.subgradient_mem m

/-- Helper for Chapter14 Theorem 14.3.6: under perpetual nonoptimality, every chosen Polyak
subgradient has strictly positive norm at every positive stage. -/
theorem polyak_subgradient_norm_pos_at
    (g : ℕ → DualSpace)
    (h_method : IsPolyakSubgradientMethod f x g lam)
    (h_nonoptimal : ∀ k : ℕ, x (k + 1) ∉ S⋆[f]) {k : ℕ} (hk : 1 ≤ k) :
    0 < ‖g k‖ := by
  -- The nonoptimality hypothesis excludes the zero subgradient after reindexing.
  obtain ⟨m, rfl⟩ := eq_add_one_of_one_le hk
  exact norm_pos_iff.mpr (subgradient_ne_zero_of_not_optimal g h_method m (h_nonoptimal m))

/-- Helper for Chapter14 Theorem 14.3.6: the Polyak stepsize formula is positive at every
positive stage when the iterate stays nonoptimal. -/
theorem polyak_stepSize_pos_at
    (g : ℕ → DualSpace)
    (h_method : IsPolyakSubgradientMethod f x g lam)
    (h_solution : Set.Nonempty S⋆[f])
    (hLam_pos : 0 < lam)
    (h_nonoptimal : ∀ k : ℕ, x (k + 1) ∉ S⋆[f]) {k : ℕ} (hk : 1 ≤ k) :
    0 < lam * (f (x k) - f⋆[f]) / ‖g k‖ := by
  -- Reindex to the source stage `m + 1`, then combine positivity of the gap and norm.
  obtain ⟨m, rfl⟩ := eq_add_one_of_one_le hk
  have h_gap :
      0 < f (x (m + 1)) - f⋆[f] :=
    objectiveGap_pos_of_not_optimal h_solution m (h_nonoptimal m)
  have h_norm :
      0 < ‖g (m + 1)‖ :=
    polyak_subgradient_norm_pos_at g h_method h_nonoptimal (show 1 ≤ m + 1 by simp)
  exact div_pos (mul_pos hLam_pos h_gap) h_norm

/-- Helper for Chapter14 Theorem 14.3.6: at every positive stage, the chapter-owner iterate update
matches the source Polyak recursion when the iterate is nonoptimal. -/
theorem polyak_iterate_succ_at
    (g : ℕ → DualSpace)
    (h_method : IsPolyakSubgradientMethod f x g lam)
    (h_nonoptimal : ∀ k : ℕ, x (k + 1) ∉ S⋆[f]) {k : ℕ} (hk : 1 ≤ k) :
    x (k + 1) =
      x k +
        (lam * (f (x k) - f⋆[f]) / ‖g k‖) • normalizedSubgradientDirection (g k) := by
  -- Reindex the positive stage and rewrite the source step into the chapter-owner form.
  obtain ⟨m, rfl⟩ := eq_add_one_of_one_le hk
  simpa [Nat.add_assoc] using h_method.iterate_succ_of_not_optimal m (h_nonoptimal m)

/-- Under the stronger regime that every recorded iterate remains nonoptimal, the Polyak
recursion refines to the chapter owner `SubgradientMethod`, with the same objective,
initial point, iterates, chosen subgradients, and Polyak step-size formula. -/
def toSubgradientMethod
    (g : ℕ → DualSpace)
    (h_method : IsPolyakSubgradientMethod f x g lam)
    (h_solution : Set.Nonempty S⋆[f])
    (hLam_pos : 0 < lam)
    (h_nonoptimal : ∀ k : ℕ, x (k + 1) ∉ S⋆[f]) :
    SubgradientMethod E where
  objective := f
  initialPoint := x 1
  iterate := x
  subgradient := g
  stepSize := (fun k ↦ lam * (f (x k) - f⋆[f]) / (‖g k‖ : ℝ) : ℕ → ℝ)
  iterate_one := rfl
  subgradient_mem := fun _ hk ↦ polyak_subgradient_mem_at g h_method hk
  subgradient_norm_pos := fun _ hk ↦ polyak_subgradient_norm_pos_at g h_method h_nonoptimal hk
  stepSize_pos := fun _ hk ↦ polyak_stepSize_pos_at g h_method h_solution hLam_pos h_nonoptimal hk
  iterate_succ := fun _ hk ↦ polyak_iterate_succ_at g h_method h_nonoptimal hk

end IsPolyakSubgradientMethod

/-- Helper for Chapter14 Theorem 14.3.6: when the optimal solution set is nonempty, the optimal
value is a lower bound for every objective value. -/
lemma optimalValue_le_of_nonempty_solution
    (f : E → ℝ) (h_solution : Set.Nonempty S⋆[f]) (z : E) :
    f⋆[f] ≤ f z := by
  rcases h_solution with ⟨xStar, hxStar⟩
  have hxStar_min : IsMinOn f Set.univ xStar := by
    simpa [mem_sunYuanOptimalSolutionSet_iff] using hxStar
  have hxStar_lower : ∀ y : E, f xStar ≤ f y := by
    simpa [isMinOn_univ_iff] using hxStar_min
  have h_bddBelow : BddBelow (Set.range f) := ⟨f xStar, by
    rintro _ ⟨y, rfl⟩
    exact hxStar_lower y⟩
  -- The infimum of the range is below every point of the range.
  simpa [optimalValue_eq_sInf_range] using
    (csInf_le h_bddBelow (show f z ∈ Set.range f by exact ⟨z, rfl⟩))

/-- Helper for Chapter14 Theorem 14.3.6: the normalized negative subgradient direction has unit
norm whenever the chosen subgradient is nonzero. -/
lemma normalizedSubgradientDirection_norm_eq_one
    (ξ : DualSpace) (hξ : 0 < ‖ξ‖) :
    ‖normalizedSubgradientDirection ξ‖ = 1 := by
  -- Expand the direction into the normalized Riesz representative and simplify the norm.
  rw [normalizedSubgradientDirection_eq, norm_smul]
  simp only [Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg ξ)), norm_neg,
    LinearIsometryEquiv.norm_map]
  field_simp [ne_of_gt hξ]

/-- Helper for Chapter14 Theorem 14.3.6: every subgradient controls the objective gap by the
distance to any optimal point. -/
lemma objectiveGap_le_subgradientNorm_mul_dist
    (f : E → ℝ)
    (h_solution : Set.Nonempty S⋆[f])
    {z y : E} (hy : y ∈ S⋆[f]) {ξ : DualSpace} (hξ : ξ ∈ ∂ f(z)) :
    f z - f⋆[f] ≤ ‖ξ‖ * ‖z - y‖ := by
  have hy_eq : f y = f⋆[f] :=
    (mem_sunYuanOptimalSolutionSet_iff_eq_optimalValue f h_solution y).1 hy
  have h_subgrad :
      f y ≥ f z + ξ (y - z) :=
    (mem_subdifferential_iff f z ξ).1 hξ y
  have h_eval :
      ξ (y - z) = -ξ (z - y) := by
    simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  have h_opnorm :
      ξ (z - y) ≤ ‖ξ‖ * ‖z - y‖ := by
    exact le_trans (le_abs_self _) (by
      simpa [Real.norm_eq_abs] using ξ.le_opNorm (z - y))
  rw [h_eval] at h_subgrad
  -- Insert the minimizer identity and then bound the resulting dual evaluation by the operator
  -- norm estimate.
  calc
    f z - f⋆[f] ≤ ξ (z - y) := by
      rw [← hy_eq]
      linarith
    _ ≤ ‖ξ‖ * ‖z - y‖ := h_opnorm

/-- Helper for Chapter14 Theorem 14.3.6: every subgradient controls the objective gap directly by
the distance from the current point to the optimal solution set. -/
lemma objectiveGap_le_subgradientNorm_mul_infDist
    (f : E → ℝ)
    (h_solution : Set.Nonempty S⋆[f])
    {z : E} {ξ : DualSpace} (hξ : ξ ∈ ∂ f(z)) :
    f z - f⋆[f] ≤ ‖ξ‖ * infDist z (S⋆[f]) := by
  by_cases hnorm : ‖ξ‖ = 0
  · -- A zero-norm subgradient is the zero functional, so the point is already optimal.
    have hξ_zero : ξ = 0 := norm_eq_zero.mp hnorm
    have hz_mem : z ∈ S⋆[f] := by
      apply mem_sunYuanOptimalSolutionSet_of_zero_mem_subdifferential f
      simpa [hξ_zero] using hξ
    have hz_eq : f z = f⋆[f] :=
      (mem_sunYuanOptimalSolutionSet_iff_eq_optimalValue f h_solution z).1 hz_mem
    rw [hz_eq, sub_self, hnorm, zero_mul]
  · have hnorm_ne : 0 ≠ ‖ξ‖ := by
      simpa [eq_comm] using hnorm
    have hnorm_pos : 0 < ‖ξ‖ := lt_of_le_of_ne (norm_nonneg _) hnorm_ne
    have h_div_le :
        (f z - f⋆[f]) / ‖ξ‖ ≤ infDist z (S⋆[f]) := by
      -- Divide the pointwise distance bound by the positive norm, then pass to the infimum.
      refine (Metric.le_infDist h_solution).2 ?_
      intro y hy
      exact (div_le_iff₀ hnorm_pos).2 <| by
        simpa [dist_eq_norm, mul_comm, mul_left_comm, mul_assoc] using
          objectiveGap_le_subgradientNorm_mul_dist f h_solution hy hξ
    -- Multiply the infimum bound back by `‖ξ‖` to recover the original gap.
    calc
      f z - f⋆[f] = ‖ξ‖ * ((f z - f⋆[f]) / ‖ξ‖) := by
        field_simp [hnorm]
      _ ≤ ‖ξ‖ * infDist z (S⋆[f]) :=
        mul_le_mul_of_nonneg_left h_div_le (norm_nonneg _)

/-- Helper for Chapter14 Theorem 14.3.6: one Polyak step satisfies the textbook squared-distance
estimate against any optimal point. -/
lemma polyak_sqdist_step_le
    (f : E → ℝ) (x : ℕ → E) (g : ℕ → DualSpace) (lam : ℝ)
    (h_solution : Set.Nonempty S⋆[f])
    (hLam_pos : 0 < lam)
    (h_method : IsPolyakSubgradientMethod f x g lam)
    {y : E} (hy : y ∈ S⋆[f]) (k : ℕ)
    (hk : x (k + 1) ∉ S⋆[f]) :
    ‖x (k + 2) - y‖ ^ 2 ≤
      ‖x (k + 1) - y‖ ^ 2 -
        lam * (2 - lam) * (f (x (k + 1)) - f⋆[f]) ^ 2 / ‖g (k + 1)‖ ^ 2 := by
  let gap : ℝ := f (x (k + 1)) - f⋆[f]
  let α : ℝ := lam * gap / ‖g (k + 1)‖
  have hg_ne : g (k + 1) ≠ (0 : DualSpace) :=
    IsPolyakSubgradientMethod.subgradient_ne_zero_of_not_optimal g h_method k hk
  have hg_norm_pos : 0 < ‖g (k + 1)‖ := norm_pos_iff.mpr hg_ne
  have hg_norm_ne : ‖g (k + 1)‖ ≠ 0 := ne_of_gt hg_norm_pos
  have hgap_nonneg : 0 ≤ gap := by
    dsimp [gap]
    exact sub_nonneg.mpr (optimalValue_le_of_nonempty_solution f h_solution (x (k + 1)))
  have hα_nonneg : 0 ≤ α := by
    dsimp [α]
    exact div_nonneg (mul_nonneg hLam_pos.le hgap_nonneg) (norm_nonneg _)
  have hy_eq : f y = f⋆[f] :=
    (mem_sunYuanOptimalSolutionSet_iff_eq_optimalValue f h_solution y).1 hy
  have h_subgrad :
      f y ≥ f (x (k + 1)) + g (k + 1) (y - x (k + 1)) :=
    (mem_subdifferential_iff f (x (k + 1)) (g (k + 1))).1 (h_method.subgradient_mem k) y
  have h_eval :
      g (k + 1) (y - x (k + 1)) ≤ -gap := by
    dsimp [gap] at *
    rw [hy_eq] at h_subgrad
    linarith
  have hcoeff_nonneg : 0 ≤ 2 * α / ‖g (k + 1)‖ := by
    exact div_nonneg (mul_nonneg (by positivity) hα_nonneg) (norm_nonneg _)
  have hterm_le :
      (2 * α / ‖g (k + 1)‖) * g (k + 1) (y - x (k + 1)) + α ^ 2 ≤
        -lam * (2 - lam) * gap ^ 2 / ‖g (k + 1)‖ ^ 2 := by
    have hmul :
        (2 * α / ‖g (k + 1)‖) * g (k + 1) (y - x (k + 1)) ≤
          (2 * α / ‖g (k + 1)‖) * (-gap) := by
      exact mul_le_mul_of_nonneg_left h_eval hcoeff_nonneg
    have hcalc :
        (2 * α / ‖g (k + 1)‖) * (-gap) + α ^ 2 =
          -lam * (2 - lam) * gap ^ 2 / ‖g (k + 1)‖ ^ 2 := by
      dsimp [α]
      field_simp [hg_norm_ne]
      ring
    calc
      (2 * α / ‖g (k + 1)‖) * g (k + 1) (y - x (k + 1)) + α ^ 2
          ≤ (2 * α / ‖g (k + 1)‖) * (-gap) + α ^ 2 := by
            simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hmul (α ^ 2)
      _ = -lam * (2 - lam) * gap ^ 2 / ‖g (k + 1)‖ ^ 2 := hcalc
  -- Rewrite the Polyak update and insert the subgradient inequality at the minimizer `y`.
  rw [h_method.iterate_succ_of_not_optimal k hk]
  rw [norm_sq_subgradient_step_eq hg_norm_pos α]
  calc
    ‖x (k + 1) - y‖ ^ 2 +
        (2 * α / ‖g (k + 1)‖) * g (k + 1) (y - x (k + 1)) + α ^ 2
        ≤ ‖x (k + 1) - y‖ ^ 2 +
            (-lam * (2 - lam) * gap ^ 2 / ‖g (k + 1)‖ ^ 2) := by
              simpa [add_assoc, add_left_comm, add_comm] using
                add_le_add_left hterm_le (‖x (k + 1) - y‖ ^ 2)
    _ = ‖x (k + 1) - y‖ ^ 2 -
          lam * (2 - lam) * gap ^ 2 / ‖g (k + 1)‖ ^ 2 := by ring

/-- Helper for Chapter14 Theorem 14.3.6: the distance from the Polyak iterates to the optimal
solution set never increases. -/
lemma polyak_infDist_nonincreasing
    (f : E → ℝ) (x : ℕ → E) (g : ℕ → DualSpace) (lam : ℝ)
    (h_convex : ConvexOn ℝ Set.univ f)
    (h_solution : Set.Nonempty S⋆[f])
    (hLam_pos : 0 < lam)
    (hLam_lt_two : lam < 2)
    (h_method : IsPolyakSubgradientMethod f x g lam) :
    ∀ k : ℕ, infDist (x (k + 2)) (S⋆[f]) ≤ infDist (x (k + 1)) (S⋆[f]) := by
  intro k
  by_cases hk : x (k + 1) ∈ S⋆[f]
  case pos =>
    -- At an optimal iterate the Polyak recursion stays fixed.
    simpa [h_method.iterate_succ_of_optimal k hk, infDist_zero_of_mem hk]
  case neg =>
    let _ := h_convex
    -- Route correction: avoid the blocked exact projection layer and use an `ε`-near minimizer
    -- from `Metric.infDist_lt_iff`, which is enough for the one-step Fejer decrease.
    refine le_of_forall_pos_lt_add' ?_
    intro ε hε
    have hlt :
        infDist (x (k + 1)) (S⋆[f]) < infDist (x (k + 1)) (S⋆[f]) + ε :=
      lt_add_of_pos_right _ hε
    rcases (Metric.infDist_lt_iff h_solution).1 hlt with ⟨y, hy, hy_dist⟩
    have hsq :=
      polyak_sqdist_step_le f x g lam h_solution hLam_pos h_method hy k hk
    have hdecr_nonneg :
        0 ≤ lam * (2 - lam) * (f (x (k + 1)) - f⋆[f]) ^ 2 / ‖g (k + 1)‖ ^ 2 := by
      have h_two_sub_nonneg : 0 ≤ 2 - lam := sub_nonneg.mpr hLam_lt_two.le
      positivity
    have hsq_drop :
        ‖x (k + 2) - y‖ ^ 2 ≤ ‖x (k + 1) - y‖ ^ 2 := by
      calc
        ‖x (k + 2) - y‖ ^ 2
            ≤ ‖x (k + 1) - y‖ ^ 2 -
                lam * (2 - lam) * (f (x (k + 1)) - f⋆[f]) ^ 2 / ‖g (k + 1)‖ ^ 2 := hsq
        _ ≤ ‖x (k + 1) - y‖ ^ 2 := by nlinarith
    have hnorm :
        ‖x (k + 2) - y‖ ≤ ‖x (k + 1) - y‖ :=
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hsq_drop
    calc
      infDist (x (k + 2)) (S⋆[f]) ≤ dist (x (k + 2)) y := Metric.infDist_le_dist_of_mem hy
      _ = ‖x (k + 2) - y‖ := by rw [dist_eq_norm]
      _ ≤ ‖x (k + 1) - y‖ := hnorm
      _ = dist (x (k + 1)) y := by rw [dist_eq_norm]
      _ < infDist (x (k + 1)) (S⋆[f]) + ε := hy_dist

/-- Helper for Chapter14 Theorem 14.3.6: one Polyak step contracts the distance to the optimal
solution set by the linear rate `q`. -/
lemma polyak_decrease_term_ge_rate_sq_mul_infDist_sq
    (f : E → ℝ) (x : ℕ → E) (g : ℕ → DualSpace) (lam cBar cHat : ℝ)
    (h_solution : Set.Nonempty S⋆[f])
    (hLam_pos : 0 < lam)
    (hLam_lt_two : lam < 2)
    (hcBar : 0 < cBar)
    (hcHat : 0 < cHat)
    (h_method : IsPolyakSubgradientMethod f x g lam)
    (h_subgradient_bound :
      ∀ z (ξ : DualSpace),
        infDist z (S⋆[f]) ≤ infDist (x 1) (S⋆[f]) →
          ξ ∈ ∂ f(z) →
            ‖ξ‖ ≤ cBar)
    (h_error_bound :
      ∀ z : E,
        infDist z (S⋆[f]) ≤ infDist (x 1) (S⋆[f]) →
          cHat * infDist z (S⋆[f]) ≤ f z - f⋆[f])
    (k : ℕ)
    (hk_region : infDist (x (k + 1)) (S⋆[f]) ≤ infDist (x 1) (S⋆[f]))
    (hk : x (k + 1) ∉ S⋆[f]) :
    lam * (2 - lam) * (cHat / cBar) ^ 2 * infDist (x (k + 1)) (S⋆[f]) ^ 2 ≤
      lam * (2 - lam) * (f (x (k + 1)) - f⋆[f]) ^ 2 / ‖g (k + 1)‖ ^ 2 := by
  let d : ℝ := infDist (x (k + 1)) (S⋆[f])
  let gap : ℝ := f (x (k + 1)) - f⋆[f]
  let gnorm : ℝ := ‖g (k + 1)‖
  have hgnorm_pos : 0 < gnorm := by
    -- Nonoptimal iterates cannot carry the zero subgradient, so the denominator is positive.
    dsimp [gnorm]
    exact norm_pos_iff.mpr <|
      IsPolyakSubgradientMethod.subgradient_ne_zero_of_not_optimal g h_method k hk
  have hgnorm_le : gnorm ≤ cBar := by
    -- The theorem hypotheses bound every subgradient on the invariant distance region.
    dsimp [gnorm]
    exact h_subgradient_bound _ _ hk_region (h_method.subgradient_mem k)
  have hd_nonneg : 0 ≤ d := by
    dsimp [d]
    exact infDist_nonneg
  have hgap_nonneg : 0 ≤ gap := by
    -- The error bound gives the objective gap a nonnegative lower bound.
    dsimp [gap]
    exact le_trans (mul_nonneg hcHat.le hd_nonneg) (h_error_bound _ hk_region)
  have hratio :
      (cHat / cBar) * d ≤ gap / gnorm := by
    -- First divide the error bound by `cBar`, then enlarge the denominator to `‖g‖`.
    have herror_div :
        (cHat * d) / cBar ≤ gap / cBar := by
      exact div_le_div_of_nonneg_right (h_error_bound _ hk_region) hcBar.le
    have hdenom_mono :
        gap / cBar ≤ gap / gnorm := by
      exact div_le_div_of_nonneg_left hgap_nonneg hgnorm_pos hgnorm_le
    calc
      (cHat / cBar) * d = (cHat * d) / cBar := by
        field_simp [hcBar.ne']
      _ ≤ gap / cBar := herror_div
      _ ≤ gap / gnorm := hdenom_mono
  have hratio_sq :
      ((cHat / cBar) * d) ^ 2 ≤ (gap / gnorm) ^ 2 := by
    -- Square only after recording nonnegativity on both sides.
    refine (sq_le_sq₀ ?_ ?_).2 hratio
    · exact mul_nonneg (div_nonneg hcHat.le hcBar.le) hd_nonneg
    · exact div_nonneg hgap_nonneg hgnorm_pos.le
  have hfactor_nonneg : 0 ≤ lam * (2 - lam) := by
    nlinarith
  have hmul :
      lam * (2 - lam) * (((cHat / cBar) * d) ^ 2) ≤
        lam * (2 - lam) * ((gap / gnorm) ^ 2) := by
    exact mul_le_mul_of_nonneg_left hratio_sq hfactor_nonneg
  have hsq_right : (gap / gnorm) ^ 2 = gap ^ 2 / gnorm ^ 2 := by
    field_simp [pow_two, hgnorm_pos.ne']
  -- This finishes the source algebraic bridge from the error bound to the decrease term.
  calc
    lam * (2 - lam) * (cHat / cBar) ^ 2 * infDist (x (k + 1)) (S⋆[f]) ^ 2
        = lam * (2 - lam) * (((cHat / cBar) * d) ^ 2) := by
            dsimp [d]
            ring
    _ ≤ lam * (2 - lam) * ((gap / gnorm) ^ 2) := hmul
    _ = lam * (2 - lam) * gap ^ 2 / gnorm ^ 2 := by
          rw [hsq_right]
          ring

/-- Helper for Chapter14 Theorem 14.3.6: one Polyak step contracts the distance to the optimal
solution set by the linear rate `q`. -/
lemma polyak_quadratic_perturbation_absorbed_by_epsilon
    {q d ε δ : ℝ}
    (hq_nonneg : 0 ≤ q)
    (hd_nonneg : 0 ≤ d)
    (hε_pos : 0 < ε)
    (hδ_nonneg : 0 ≤ δ)
    (hδ_le_one : δ ≤ 1)
    (hδ_le : δ ≤ ε ^ 2 / (2 * d + 1)) :
    q ^ 2 * d ^ 2 + 2 * d * δ + δ ^ 2 ≤ (q * d + ε) ^ 2 := by
  have hden_pos : 0 < 2 * d + 1 := by
    -- The denominator in the source choice `δ := min 1 (ε^2 / (2 * d + 1))` is strictly positive.
    nlinarith
  have hδ_sq_le : δ ^ 2 ≤ δ := by
    -- Since `0 ≤ δ ≤ 1`, the quadratic perturbation is dominated by its linear part.
    have hmul : δ * δ ≤ δ * 1 := mul_le_mul_of_nonneg_left hδ_le_one hδ_nonneg
    simpa [pow_two] using hmul
  have hsmall : 2 * d * δ + δ ^ 2 ≤ ε ^ 2 := by
    -- Multiply the source upper bound on `δ` back by the positive denominator.
    have hmul :
        δ * (2 * d + 1) ≤ (ε ^ 2 / (2 * d + 1)) * (2 * d + 1) :=
      mul_le_mul_of_nonneg_right hδ_le hden_pos.le
    have hcancel :
        (ε ^ 2 / (2 * d + 1)) * (2 * d + 1) = ε ^ 2 := by
      field_simp [hden_pos.ne']
    have hprod : (2 * d + 1) * δ ≤ ε ^ 2 := by
      calc
        (2 * d + 1) * δ = δ * (2 * d + 1) := by ring
        _ ≤ (ε ^ 2 / (2 * d + 1)) * (2 * d + 1) := hmul
        _ = ε ^ 2 := hcancel
    calc
      2 * d * δ + δ ^ 2 = δ ^ 2 + 2 * d * δ := by ring
      _ ≤ δ + 2 * d * δ := by
        nlinarith [hδ_sq_le]
      _ = (2 * d + 1) * δ := by ring
      _ ≤ ε ^ 2 := hprod
  -- The absorbed perturbation fits inside the positive cross term of `(q * d + ε)^2`.
  have hcross_nonneg : 0 ≤ 2 * q * d * ε := by
    positivity
  calc
    q ^ 2 * d ^ 2 + 2 * d * δ + δ ^ 2 = q ^ 2 * d ^ 2 + (2 * d * δ + δ ^ 2) := by
      ring
    _ ≤ q ^ 2 * d ^ 2 + ε ^ 2 := by
      nlinarith [hsmall]
    _ ≤ q ^ 2 * d ^ 2 + 2 * q * d * ε + ε ^ 2 := by
      nlinarith [hcross_nonneg]
    _ = (q * d + ε) ^ 2 := by
      ring

/-- Helper for Chapter14 Theorem 14.3.6: one Polyak step contracts the distance to the optimal
solution set by the linear rate `q`. -/
lemma polyak_infDist_contracts_once
    (f : E → ℝ) (x : ℕ → E) (g : ℕ → DualSpace) (lam cBar cHat : ℝ)
    (h_convex : ConvexOn ℝ Set.univ f)
    (h_solution : Set.Nonempty S⋆[f])
    (hLam_pos : 0 < lam)
    (hLam_lt_two : lam < 2)
    (hcBar : 0 < cBar)
    (hcHat : 0 < cHat)
    (h_method : IsPolyakSubgradientMethod f x g lam)
    (h_subgradient_bound :
      ∀ z (ξ : DualSpace),
        infDist z (S⋆[f]) ≤ infDist (x 1) (S⋆[f]) →
          ξ ∈ ∂ f(z) →
            ‖ξ‖ ≤ cBar)
    (h_error_bound :
      ∀ z : E,
        infDist z (S⋆[f]) ≤ infDist (x 1) (S⋆[f]) →
          cHat * infDist z (S⋆[f]) ≤ f z - f⋆[f]) :
    ∀ k : ℕ,
      infDist (x (k + 1)) (S⋆[f]) ≤ infDist (x 1) (S⋆[f]) →
        infDist (x (k + 2)) (S⋆[f]) ≤
          polyakSubgradientLinearRate lam cBar cHat * infDist (x (k + 1)) (S⋆[f]) := by
  intro k hk_region
  let _ := h_convex
  let d : ℝ := infDist (x (k + 1)) (S⋆[f])
  let gap : ℝ := f (x (k + 1)) - f⋆[f]
  let q : ℝ := polyakSubgradientLinearRate lam cBar cHat
  have hd_nonneg : 0 ≤ d := by
    -- The distance to the optimal solution set is always nonnegative.
    dsimp [d]
    exact infDist_nonneg
  have hgap_nonneg : 0 ≤ gap := by
    -- Every objective value dominates the optimal value once the solution set is nonempty.
    dsimp [gap]
    exact sub_nonneg.mpr (optimalValue_le_of_nonempty_solution f h_solution (x (k + 1)))
  by_cases hk : x (k + 1) ∈ S⋆[f]
  · -- At an optimal iterate the Polyak recursion stays fixed, so the contraction is trivial.
    have hq_nonneg : 0 ≤ q := by
      dsimp [q, polyakSubgradientLinearRate]
      exact Real.sqrt_nonneg _
    calc
      infDist (x (k + 2)) (S⋆[f]) = 0 := by
        simpa [h_method.iterate_succ_of_optimal k hk] using
          (infDist_zero_of_mem hk : infDist (x (k + 1)) (S⋆[f]) = 0)
      _ ≤ q * infDist (x (k + 1)) (S⋆[f]) := by
        have : 0 ≤ q * infDist (x (k + 1)) (S⋆[f]) := by
          exact mul_nonneg hq_nonneg infDist_nonneg
        simpa using this
  · -- Route correction: prove the one-step contraction directly from an `ε`-near minimizer.
    have hgap_le :
        gap ≤ ‖g (k + 1)‖ * d := by
      -- The direct gap-to-`infDist` estimate avoids introducing a nearest-point projection.
      dsimp [gap, d]
      simpa using
        objectiveGap_le_subgradientNorm_mul_infDist f h_solution (h_method.subgradient_mem k)
    have hd_pos : 0 < d := by
      -- If `d = 0`, then the gap bound would force the current iterate to be optimal.
      have hd_ne : d ≠ 0 := by
        intro hd_zero
        have hgap_zero : gap = 0 := by
          have hgap_nonpos : gap ≤ 0 := by
            simpa [d, hd_zero] using hgap_le
          exact le_antisymm hgap_nonpos hgap_nonneg
        apply hk
        exact (mem_sunYuanOptimalSolutionSet_iff_eq_optimalValue f h_solution (x (k + 1))).2
          (sub_eq_zero.mp hgap_zero)
      exact lt_of_le_of_ne hd_nonneg hd_ne.symm
    have hgnorm_le : ‖g (k + 1)‖ ≤ cBar := by
      -- The standing region hypothesis feeds the uniform subgradient bound.
      exact h_subgradient_bound _ _ hk_region (h_method.subgradient_mem k)
    have herror : cHat * d ≤ gap := by
      -- The error bound supplies the lower control of the objective gap by the distance.
      dsimp [d, gap]
      simpa using h_error_bound (x (k + 1)) hk_region
    have hcHat_mul_le : cHat * d ≤ cBar * d := by
      calc
        cHat * d ≤ gap := herror
        _ ≤ ‖g (k + 1)‖ * d := hgap_le
        _ ≤ cBar * d := mul_le_mul_of_nonneg_right hgnorm_le hd_nonneg
    have hcHat_le_cBar : cHat ≤ cBar := by
      -- Since the iterate is genuinely nonoptimal, the distance factor can be cancelled.
      nlinarith
    have hfactor_nonneg : 0 ≤ lam * (2 - lam) := by
      nlinarith
    have hratio_nonneg : 0 ≤ cHat / cBar := by
      exact div_nonneg hcHat.le hcBar.le
    have hratio_le_one : cHat / cBar ≤ 1 := by
      exact (div_le_iff₀ hcBar).2 <| by simpa using hcHat_le_cBar
    have hratio_sq_le_one : (cHat / cBar) ^ (2 : ℕ) ≤ 1 := by
      nlinarith [hratio_nonneg, hratio_le_one]
    have hprod_le_one : lam * (2 - lam) * (cHat / cBar) ^ (2 : ℕ) ≤ 1 := by
      have hlam_le_one : lam * (2 - lam) ≤ 1 := by
        nlinarith [sq_nonneg (lam - 1)]
      have hmul :
          lam * (2 - lam) * (cHat / cBar) ^ (2 : ℕ) ≤
            lam * (2 - lam) * 1 := by
        exact mul_le_mul_of_nonneg_left hratio_sq_le_one hfactor_nonneg
      exact le_trans (by simpa using hmul) hlam_le_one
    have hrad_nonneg :
        0 ≤ 1 - lam * (2 - lam) * (cHat / cBar) ^ (2 : ℕ) := by
      nlinarith
    have hq_nonneg : 0 ≤ q := by
      dsimp [q, polyakSubgradientLinearRate]
      exact Real.sqrt_nonneg _
    have hq_sq :
        q ^ (2 : ℕ) = 1 - lam * (2 - lam) * (cHat / cBar) ^ (2 : ℕ) := by
      dsimp [q, polyakSubgradientLinearRate]
      simpa [pow_two] using Real.sq_sqrt hrad_nonneg
    refine le_of_forall_pos_lt_add' ?_
    intro ε hε_pos
    let δ : ℝ := min 1 (ε ^ (2 : ℕ) / (2 * d + 1))
    have hden_pos : 0 < 2 * d + 1 := by
      nlinarith
    have hδ_nonneg : 0 ≤ δ := by
      dsimp [δ]
      refine le_min zero_le_one ?_
      positivity
    have hδ_le_one : δ ≤ 1 := by
      dsimp [δ]
      exact min_le_left _ _
    have hδ_le : δ ≤ ε ^ (2 : ℕ) / (2 * d + 1) := by
      dsimp [δ]
      exact min_le_right _ _
    have hδ_pos : 0 < δ := by
      -- The source perturbation choice is strictly positive because `ε > 0`.
      dsimp [δ]
      have hfrac_pos : 0 < ε ^ (2 : ℕ) / (2 * d + 1) := by
        positivity
      exact lt_min zero_lt_one hfrac_pos
    rcases (Metric.infDist_lt_iff h_solution).1 (lt_add_of_pos_right d hδ_pos) with
      ⟨y, hy, hy_dist⟩
    have hdist_sq_lt : ‖x (k + 1) - y‖ ^ 2 < (d + δ) ^ 2 := by
      -- Squaring preserves the strict inequality because both sides are nonnegative.
      rw [dist_eq_norm] at hy_dist
      have h_rhs_nonneg : 0 ≤ d + δ := add_nonneg hd_nonneg hδ_nonneg
      exact (sq_lt_sq₀ (norm_nonneg _) h_rhs_nonneg).2 hy_dist
    have hdecrease :
        lam * (2 - lam) * (cHat / cBar) ^ (2 : ℕ) * d ^ (2 : ℕ) ≤
          lam * (2 - lam) * (f (x (k + 1)) - f⋆[f]) ^ (2 : ℕ) / ‖g (k + 1)‖ ^ (2 : ℕ) := by
      -- The error-bound term rewrites exactly into the target rate factor on `d`.
      dsimp [d]
      simpa using
        polyak_decrease_term_ge_rate_sq_mul_infDist_sq f x g lam cBar cHat h_solution
          hLam_pos hLam_lt_two hcBar hcHat h_method h_subgradient_bound h_error_bound
          k hk_region hk
    have hstep_sq :
        ‖x (k + 2) - y‖ ^ 2 ≤
          ‖x (k + 1) - y‖ ^ 2 -
            lam * (2 - lam) * (cHat / cBar) ^ (2 : ℕ) * d ^ (2 : ℕ) := by
      -- Replace the textbook decrease term by its lower geometric-rate bound.
      have hsq :=
        polyak_sqdist_step_le f x g lam h_solution hLam_pos h_method hy k hk
      nlinarith
    have hsq_lt :
        ‖x (k + 2) - y‖ ^ 2 <
          q ^ (2 : ℕ) * d ^ (2 : ℕ) + 2 * d * δ + δ ^ (2 : ℕ) := by
      calc
        ‖x (k + 2) - y‖ ^ 2
            ≤ ‖x (k + 1) - y‖ ^ 2 -
                lam * (2 - lam) * (cHat / cBar) ^ (2 : ℕ) * d ^ (2 : ℕ) := hstep_sq
        _ < (d + δ) ^ (2 : ℕ) -
              lam * (2 - lam) * (cHat / cBar) ^ (2 : ℕ) * d ^ (2 : ℕ) := by
                nlinarith [hdist_sq_lt]
        _ = q ^ (2 : ℕ) * d ^ (2 : ℕ) + 2 * d * δ + δ ^ (2 : ℕ) := by
              rw [hq_sq]
              ring
    have habsorb :
        q ^ (2 : ℕ) * d ^ (2 : ℕ) + 2 * d * δ + δ ^ (2 : ℕ) ≤ (q * d + ε) ^ (2 : ℕ) :=
      polyak_quadratic_perturbation_absorbed_by_epsilon hq_nonneg hd_nonneg hε_pos hδ_nonneg
        hδ_le_one hδ_le
    have hy_next_dist : dist (x (k + 2)) y < q * d + ε := by
      -- The absorbed squared estimate gives the desired strict distance estimate.
      rw [dist_eq_norm]
      have h_rhs_nonneg : 0 ≤ q * d + ε := by
        positivity
      have hsq_final :
          ‖x (k + 2) - y‖ ^ 2 < (q * d + ε) ^ (2 : ℕ) :=
        lt_of_lt_of_le hsq_lt habsorb
      exact (sq_lt_sq₀ (norm_nonneg _) h_rhs_nonneg).1 hsq_final
    calc
      infDist (x (k + 2)) (S⋆[f]) ≤ dist (x (k + 2)) y := Metric.infDist_le_dist_of_mem hy
      _ < q * d + ε := hy_next_dist
      _ = polyakSubgradientLinearRate lam cBar cHat * infDist (x (k + 1)) (S⋆[f]) + ε := by
        simp [q, d]

/-- Helper for Chapter14 Theorem 14.3.6: the invariant region
`infDist (x (k + 1)) (S⋆[f]) ≤ infDist (x 1) (S⋆[f])` holds at every iterate. -/
lemma polyak_infDist_le_initial
    (f : E → ℝ) (x : ℕ → E) (g : ℕ → DualSpace) (lam : ℝ)
    (h_convex : ConvexOn ℝ Set.univ f)
    (h_solution : Set.Nonempty S⋆[f])
    (hLam_pos : 0 < lam)
    (hLam_lt_two : lam < 2)
    (h_method : IsPolyakSubgradientMethod f x g lam) :
    ∀ k : ℕ, infDist (x (k + 1)) (S⋆[f]) ≤ infDist (x 1) (S⋆[f]) := by
  intro k
  induction k with
  | zero =>
      -- The invariant is exact at the initial iterate.
      simpa
  | succ k ih =>
      -- One Fejer-monotone step keeps the iterate inside the same distance region.
      exact le_trans
        (polyak_infDist_nonincreasing f x g lam h_convex h_solution hLam_pos hLam_lt_two
          h_method k)
        ih

/-- Helper for Chapter14 Theorem 14.3.6: the source linear rate `q` always satisfies `q < 1`
under the positivity assumptions on `λ`, `cBar`, and `cHat`. -/
lemma polyakSubgradientLinearRate_lt_one
    {lam cBar cHat : ℝ}
    (hLam_pos : 0 < lam)
    (hLam_lt_two : lam < 2)
    (hcBar : 0 < cBar)
    (hcHat : 0 < cHat) :
    polyakSubgradientLinearRate lam cBar cHat < 1 := by
  let r : ℝ := 1 - lam * (2 - lam) * (cHat / cBar) ^ (2 : ℕ)
  have hprod_pos : 0 < lam * (2 - lam) * (cHat / cBar) ^ (2 : ℕ) := by
    have hratio_pos : 0 < cHat / cBar := div_pos hcHat hcBar
    positivity
  have hr_lt_one : r < 1 := by
    dsimp [r]
    nlinarith
  by_cases hr_nonneg : 0 ≤ r
  · -- If the radicand is nonnegative, `sqrt` preserves the strict upper bound by `1`.
    have hq_sq_lt : polyakSubgradientLinearRate lam cBar cHat ^ (2 : ℕ) < 1 := by
      dsimp [polyakSubgradientLinearRate, r] at hr_nonneg hr_lt_one ⊢
      rw [Real.sq_sqrt hr_nonneg]
      simpa [pow_two] using hr_lt_one
    have habs : |polyakSubgradientLinearRate lam cBar cHat| < |(1 : ℝ)| :=
      (sq_lt_sq).1 <| by simpa [pow_two] using hq_sq_lt
    exact lt_of_le_of_lt (le_abs_self _) <| by simpa using habs
  · -- If the radicand is nonpositive, `sqrt` collapses to `0`, so the claim is immediate.
    have hr_nonpos : r ≤ 0 := le_of_not_ge hr_nonneg
    rw [polyakSubgradientLinearRate, Real.sqrt_eq_zero_of_nonpos hr_nonpos]
    norm_num

/-- Helper for Chapter14 Theorem 14.3.6: iterating the one-step contraction yields a geometric
bound on the distance from the Polyak iterates to the optimal solution set. -/
lemma polyak_infDist_geometric_bound
    (f : E → ℝ) (x : ℕ → E) (g : ℕ → DualSpace) (lam cBar cHat : ℝ)
    (h_convex : ConvexOn ℝ Set.univ f)
    (h_solution : Set.Nonempty S⋆[f])
    (hLam_pos : 0 < lam)
    (hLam_lt_two : lam < 2)
    (hcBar : 0 < cBar)
    (hcHat : 0 < cHat)
    (h_method : IsPolyakSubgradientMethod f x g lam)
    (h_subgradient_bound :
      ∀ z (ξ : DualSpace),
        infDist z (S⋆[f]) ≤ infDist (x 1) (S⋆[f]) →
          ξ ∈ ∂ f(z) →
            ‖ξ‖ ≤ cBar)
    (h_error_bound :
      ∀ z : E,
        infDist z (S⋆[f]) ≤ infDist (x 1) (S⋆[f]) →
          cHat * infDist z (S⋆[f]) ≤ f z - f⋆[f]) :
    ∀ k : ℕ,
      infDist (x (k + 1)) (S⋆[f]) ≤
        (polyakSubgradientLinearRate lam cBar cHat) ^ k * infDist (x 1) (S⋆[f]) := by
  let q : ℝ := polyakSubgradientLinearRate lam cBar cHat
  have hq_nonneg : 0 ≤ q := by
    dsimp [q, polyakSubgradientLinearRate]
    exact Real.sqrt_nonneg _
  intro k
  induction k with
  | zero =>
      -- The geometric estimate is exact at the initial iterate.
      simp [q]
  | succ k ih =>
      -- One contraction step followed by the induction hypothesis gives the next bound.
      have hk_region :
          infDist (x (k + 1)) (S⋆[f]) ≤ infDist (x 1) (S⋆[f]) :=
        polyak_infDist_le_initial f x g lam h_convex h_solution hLam_pos hLam_lt_two h_method k
      calc
        infDist (x (k + 2)) (S⋆[f])
            ≤ q * infDist (x (k + 1)) (S⋆[f]) := by
                simpa [q] using
                  polyak_infDist_contracts_once f x g lam cBar cHat h_convex h_solution hLam_pos
                    hLam_lt_two hcBar hcHat h_method h_subgradient_bound h_error_bound
                    k hk_region
        _ ≤ q * (q ^ k * infDist (x 1) (S⋆[f])) :=
              mul_le_mul_of_nonneg_left ih hq_nonneg
        _ = q ^ (k + 1) * infDist (x 1) (S⋆[f]) := by
              rw [pow_succ']
              ring

/-- Helper for Chapter14 Theorem 14.3.6: each Polyak step length is bounded by `lam` times the
current distance to the optimal solution set. -/
lemma polyak_step_norm_le_infDist
    (f : E → ℝ) (x : ℕ → E) (g : ℕ → DualSpace) (lam : ℝ)
    (h_convex : ConvexOn ℝ Set.univ f)
    (h_solution : Set.Nonempty S⋆[f])
    (hLam_pos : 0 < lam)
    (h_method : IsPolyakSubgradientMethod f x g lam) :
    ∀ k : ℕ,
      ‖x (k + 2) - x (k + 1)‖ ≤ lam * infDist (x (k + 1)) (S⋆[f]) := by
  intro k
  by_cases hk : x (k + 1) ∈ S⋆[f]
  · -- At an optimal iterate, the source recursion stays fixed and the distance is zero.
    rw [h_method.iterate_succ_of_optimal k hk, sub_self, norm_zero]
    rw [infDist_zero_of_mem hk, mul_zero]
  · -- Route correction: use the direct `infDist` gap estimate instead of choosing a projection.
    let _ := h_convex
    have hg_ne :
        g (k + 1) ≠ (0 : DualSpace) :=
      IsPolyakSubgradientMethod.subgradient_ne_zero_of_not_optimal g h_method k hk
    have hg_norm_pos : 0 < ‖g (k + 1)‖ := norm_pos_iff.mpr hg_ne
    let gap : ℝ := f (x (k + 1)) - f⋆[f]
    have hgap_nonneg : 0 ≤ gap := by
      dsimp [gap]
      exact sub_nonneg.mpr (optimalValue_le_of_nonempty_solution f h_solution (x (k + 1)))
    have hstep_nonneg : 0 ≤ lam * gap / ‖g (k + 1)‖ := by
      dsimp [gap]
      exact div_nonneg (mul_nonneg hLam_pos.le (sub_nonneg.mpr
        (optimalValue_le_of_nonempty_solution f h_solution (x (k + 1))))) (norm_nonneg _)
    have hgap_le :
        gap ≤ ‖g (k + 1)‖ * infDist (x (k + 1)) (S⋆[f]) := by
      -- Replace the old nearest-point step by the direct `infDist` bound proved above.
      dsimp [gap]
      simpa using
        objectiveGap_le_subgradientNorm_mul_infDist f h_solution (h_method.subgradient_mem k)
    rw [h_method.iterate_succ_of_not_optimal k hk]
    calc
      ‖x (k + 1) +
          (lam * gap / ‖g (k + 1)‖) • normalizedSubgradientDirection (g (k + 1)) -
          x (k + 1)‖
          = ‖(lam * gap / ‖g (k + 1)‖) • normalizedSubgradientDirection (g (k + 1))‖ := by
              simp
      _ = ‖lam * gap / ‖g (k + 1)‖‖ * ‖normalizedSubgradientDirection (g (k + 1))‖ := by
            rw [norm_smul]
      _ = lam * gap / ‖g (k + 1)‖ := by
            rw [normalizedSubgradientDirection_norm_eq_one _ hg_norm_pos]
            rw [Real.norm_of_nonneg hstep_nonneg]
            ring
      _ ≤ lam * infDist (x (k + 1)) (S⋆[f]) := by
            have hmul :
                lam * gap ≤ lam * (‖g (k + 1)‖ * infDist (x (k + 1)) (S⋆[f])) := by
              nlinarith [hgap_le, hLam_pos]
            exact (div_le_iff₀ hg_norm_pos).2 (by
              simpa [mul_assoc, mul_left_comm, mul_comm] using hmul)

namespace IsPolyakSubgradientMethod

/-- Chapter14 Theorem 14.3.6: let `f : E → ℝ` be convex on a finite-dimensional real inner-product
space, with nonempty optimal solution set.
Assume that every subgradient on the sublevel-distance region
`infDist z (S⋆[f]) ≤ infDist (x 1) (S⋆[f])` is bounded by `cBar` and that
`f z - f⋆[f]` dominates `cHat * infDist z (S⋆[f])` there. Then every execution of the
Polyak recursion converges to some `xStar ∈ S⋆[f]`, and the source geometric estimate holds with
rate `q = polyakSubgradientLinearRate lam cBar cHat < 1`, recorded by
`HasPolyakSubgradientGeometricRate`. -/
theorem exists_tendsto_with_geometricRate
    [FiniteDimensional ℝ E]
    (f : E → ℝ) (x : ℕ → E) (g : ℕ → DualSpace) (lam cBar cHat : ℝ)
    (h_convex : ConvexOn ℝ Set.univ f)
    (h_solution : Set.Nonempty S⋆[f])
    (hLam_pos : 0 < lam)
    (hLam_lt_two : lam < 2)
    (hcBar : 0 < cBar)
    (hcHat : 0 < cHat)
    (h_method : IsPolyakSubgradientMethod f x g lam)
    (h_subgradient_bound :
      ∀ z (ξ : DualSpace),
        infDist z (S⋆[f]) ≤ infDist (x 1) (S⋆[f]) →
          ξ ∈ ∂ f(z) →
            ‖ξ‖ ≤ cBar)
    (h_error_bound :
      ∀ z : E,
        infDist z (S⋆[f]) ≤ infDist (x 1) (S⋆[f]) →
          cHat * infDist z (S⋆[f]) ≤ f z - f⋆[f]) :
    ∃ xStar ∈ S⋆[f],
      Tendsto (fun k : ℕ ↦ x (k + 1)) atTop (nhds xStar) ∧
        HasPolyakSubgradientGeometricRate x xStar
          (polyakSubgradientLinearRate lam cBar cHat) := by
  let q : ℝ := polyakSubgradientLinearRate lam cBar cHat
  let C : ℝ := lam * infDist (x 1) (S⋆[f])
  have hq_lt_one : q < 1 := by
    -- The source rate is strictly below `1` under the standing positivity hypotheses.
    simpa [q] using polyakSubgradientLinearRate_lt_one hLam_pos hLam_lt_two hcBar hcHat
  have hq_nonneg : 0 ≤ q := by
    -- The rate is a square root, so it is automatically nonnegative.
    dsimp [q, polyakSubgradientLinearRate]
    exact Real.sqrt_nonneg _
  have hstep_geometric :
      ∀ k : ℕ, dist (x (k + 1)) (x (k + 2)) ≤ C * q ^ k := by
    intro k
    -- The one-step Polyak bound and the geometric `infDist` decay give a geometric step size.
    calc
      dist (x (k + 1)) (x (k + 2)) = ‖x (k + 2) - x (k + 1)‖ := by
        rw [dist_eq_norm, norm_sub_rev]
      _ ≤ lam * infDist (x (k + 1)) (S⋆[f]) := by
        simpa using polyak_step_norm_le_infDist f x g lam h_convex h_solution hLam_pos h_method k
      _ ≤ lam * (q ^ k * infDist (x 1) (S⋆[f])) := by
        gcongr
        simpa [q] using
          polyak_infDist_geometric_bound f x g lam cBar cHat h_convex h_solution hLam_pos
            hLam_lt_two hcBar hcHat h_method h_subgradient_bound h_error_bound k
      _ = C * q ^ k := by
        dsimp [C]
        ring
  let u : ℕ → E := fun k ↦ x (k + 1)
  have hu_cauchy : CauchySeq u := by
    -- Geometrically summable successive differences make the reindexed iterate sequence Cauchy.
    simpa [u] using cauchySeq_of_le_geometric (f := u) q C hq_lt_one hstep_geometric
  rcases cauchySeq_tendsto_of_complete hu_cauchy with ⟨xStar, hu_tendsto⟩
  have hgap_geometric :
      ∀ k : ℕ, f (x (k + 1)) - f⋆[f] ≤ cBar * q ^ k * infDist (x 1) (S⋆[f]) := by
    intro k
    have hk_gap :
        f (x (k + 1)) - f⋆[f] ≤ ‖g (k + 1)‖ * infDist (x (k + 1)) (S⋆[f]) := by
      -- Every chosen subgradient bounds the current objective gap by the current `infDist`.
      simpa using
        objectiveGap_le_subgradientNorm_mul_infDist f h_solution (h_method.subgradient_mem k)
    have hk_region :
        infDist (x (k + 1)) (S⋆[f]) ≤ infDist (x 1) (S⋆[f]) :=
      polyak_infDist_le_initial f x g lam h_convex h_solution hLam_pos hLam_lt_two h_method k
    have hk_norm :
        ‖g (k + 1)‖ ≤ cBar :=
      h_subgradient_bound _ _ hk_region (h_method.subgradient_mem k)
    have hk_infDist :
        infDist (x (k + 1)) (S⋆[f]) ≤ q ^ k * infDist (x 1) (S⋆[f]) := by
      simpa [q] using
        polyak_infDist_geometric_bound f x g lam cBar cHat h_convex h_solution hLam_pos
          hLam_lt_two hcBar hcHat h_method h_subgradient_bound h_error_bound k
    have hk_infDist_nonneg : 0 ≤ infDist (x (k + 1)) (S⋆[f]) := infDist_nonneg
    calc
      f (x (k + 1)) - f⋆[f] ≤ ‖g (k + 1)‖ * infDist (x (k + 1)) (S⋆[f]) := hk_gap
      _ ≤ cBar * infDist (x (k + 1)) (S⋆[f]) := by
        gcongr
      _ ≤ cBar * (q ^ k * infDist (x 1) (S⋆[f])) := by
        gcongr
      _ = cBar * q ^ k * infDist (x 1) (S⋆[f]) := by ring
  have hpow_tendsto_zero : Tendsto (fun k : ℕ ↦ q ^ k) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq_nonneg hq_lt_one
  have hgap_upper_tendsto_zero :
      Tendsto (fun k : ℕ ↦ cBar * q ^ k * infDist (x 1) (S⋆[f])) atTop (nhds 0) := by
    -- Multiplying the geometric rate by a fixed constant preserves convergence to `0`.
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (Filter.Tendsto.const_mul (cBar * infDist (x 1) (S⋆[f])) hpow_tendsto_zero)
  have hgap_tendsto_zero :
      Tendsto (fun k : ℕ ↦ f (x (k + 1)) - f⋆[f]) atTop (nhds 0) := by
    -- The nonnegative objective gap is squeezed between `0` and the geometric majorant.
    refine squeeze_zero
      (fun k ↦ sub_nonneg.mpr (optimalValue_le_of_nonempty_solution f h_solution (x (k + 1))))
      hgap_geometric hgap_upper_tendsto_zero
  have hcontAt : ContinuousAt f xStar := by
    -- Convexity on `univ` gives continuity at the limit point.
    have h_univ_nhds : Set.univ ∈ nhds xStar := by simp
    exact (h_convex.continuousOn isOpen_univ).continuousAt h_univ_nhds
  have hf_tendsto_limit :
      Tendsto (fun k : ℕ ↦ f (x (k + 1))) atTop (nhds (f xStar)) := by
    -- Continuity transports the iterate convergence through the objective.
    change Tendsto (f ∘ u) atTop (nhds (f xStar))
    exact hcontAt.tendsto.comp hu_tendsto
  have hf_tendsto_opt :
      Tendsto (fun k : ℕ ↦ f (x (k + 1))) atTop (nhds (f⋆[f])) := by
    -- The vanishing gap means the objective values themselves converge to `f⋆[f]`.
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      hgap_tendsto_zero.add_const (f⋆[f])
  have hxStar_eq : f xStar = f⋆[f] :=
    tendsto_nhds_unique hf_tendsto_limit hf_tendsto_opt
  have hxStar_mem : xStar ∈ S⋆[f] :=
    (mem_sunYuanOptimalSolutionSet_iff_eq_optimalValue f h_solution xStar).2 hxStar_eq
  have hone_sub_q_pos : 0 < 1 - q := sub_pos.mpr hq_lt_one
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg hLam_pos.le infDist_nonneg
  have htail :
      ∀ k : ℕ, dist (u k) xStar ≤ C * q ^ k / (1 - q) := by
    intro k
    -- The same geometric step estimate controls the distance to the limit.
    simpa using
      dist_le_of_le_geometric_of_tendsto (f := u) q C hq_lt_one hstep_geometric hu_tendsto k
  let M : Set.Ioi (0 : ℝ) :=
    ⟨C / (1 - q) + 1, by
      have hC_div_nonneg : 0 ≤ C / (1 - q) := div_nonneg hC_nonneg hone_sub_q_pos.le
      have h_one_le : (1 : ℝ) ≤ C / (1 - q) + 1 := by
        exact le_add_of_nonneg_left hC_div_nonneg
      exact lt_of_lt_of_le zero_lt_one h_one_le⟩
  refine ⟨xStar, hxStar_mem, ?_, ?_⟩
  · -- Return the convergence of the source indexing `x (k + 1)`.
    simpa [u] using hu_tendsto
  · refine ⟨hq_lt_one, M, ?_⟩
    intro k
    have hpow_nonneg : 0 ≤ q ^ k := pow_nonneg hq_nonneg _
    have hcoeff_le : C / (1 - q) ≤ M.1 := by
      dsimp [M]
      linarith
    -- The geometric tail bound is dominated by the chosen positive witness `M`.
    calc
      ‖x (k + 1) - xStar‖ = dist (u k) xStar := by
        change ‖u k - xStar‖ = dist (u k) xStar
        rw [dist_eq_norm]
      _ ≤ C * q ^ k / (1 - q) := htail k
      _ = (C / (1 - q)) * q ^ k := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        ring
      _ ≤ M.1 * q ^ k := by
        exact mul_le_mul_of_nonneg_right hcoeff_le hpow_nonneg

end IsPolyakSubgradientMethod

#print axioms polyakSubgradientLinearRate
#print axioms IsPolyakSubgradientMethod

end
