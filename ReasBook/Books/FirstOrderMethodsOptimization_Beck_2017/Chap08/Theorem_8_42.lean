/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_4
import FirstOrderMethodsOptimization_Beck_2017.Chap08.DualConstraintVector

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators

universe u

section

variable {E : Type u} {m : ℕ}

local notation "Λ" => EuclideanSpace ℝ (Fin m)

/- Theorem 8.42 is `source-facing`: it bounds the Euclidean norm of a dual multiplier in the
superlevel set `S_μ` using the strict-feasibility slack at a Slater point `xBar`. The canonical
owner for the dual objective is Chapter 3's `lagrangian_dual_objective`; the reusable Chapter 8
bridge `dual_constraint_vector` supplies the Euclidean constraint vector attached to the
coordinatewise family `g i x`. -/

/-- The dual-objective superlevel set `S_μ = {λ ∈ ℝ₊^m : q(λ) ≥ μ}` for the inequality-constrained
problem with ambient set `X`, objective `f`, and constraint family `g`. -/
def dual_objective_superlevel_set
    (X : Set E) (f : E → ℝ) (g : Fin m → E → ℝ) (μ : ℝ) : Set Λ :=
  {lam |
    (∀ i : Fin m, 0 ≤ lam i) ∧
      (μ : EReal) ≤ lagrangian_dual_objective X f (dual_constraint_vector g) lam}

-- Proof sketch: unfold `dual_objective_superlevel_set`; membership is exactly coordinatewise
-- nonnegativity together with the dual-objective lower bound `μ ≤ q(λ)`.
/-- Membership in `dual_objective_superlevel_set X f g μ` means that `λ` is coordinatewise
nonnegative and satisfies `μ ≤ q(λ)`. -/
@[simp] theorem mem_dual_objective_superlevel_set
    {X : Set E} {f : E → ℝ} {g : Fin m → E → ℝ} {μ : ℝ} {lam : Λ} :
    lam ∈ dual_objective_superlevel_set X f g μ ↔
      (∀ i : Fin m, 0 ≤ lam i) ∧
        (μ : EReal) ≤ lagrangian_dual_objective X f (dual_constraint_vector g) lam := by
  rfl

/-- The smallest strict-feasibility slack `min_i {-g_i(x)}` of the constraint family `g` at the
point `x`. -/
def strict_feasibility_margin [NeZero m] (g : Fin m → E → ℝ) (x : E) : ℝ :=
  ((Finset.univ).image fun i : Fin m ↦ -g i x).min'
    (Finset.univ_nonempty.image fun i : Fin m ↦ -g i x)

-- Proof sketch: unfold `strict_feasibility_margin`; it is definitionally the finite minimum of
-- the values `-g i x` over the nonempty index set `Fin m`.
/-- `strict_feasibility_margin g x` is the finite minimum of the slacks `-g_i(x)`. -/
@[simp] theorem strict_feasibility_margin_def [NeZero m]
    (g : Fin m → E → ℝ) (x : E) :
    strict_feasibility_margin g x =
      ((Finset.univ).image fun i : Fin m ↦ -g i x).min'
        (Finset.univ_nonempty.image fun i : Fin m ↦ -g i x) := by
  rfl

/-- Helper for Theorem 8.42: strict feasibility makes the common slack
`strict_feasibility_margin g xBar` positive. -/
lemma strict_feasibility_margin_pos [NeZero m]
    {g : Fin m → E → ℝ} {xBar : E}
    (hgBar : ∀ i : Fin m, g i xBar < 0) :
    0 < strict_feasibility_margin g xBar := by
  -- The minimum slack is itself one of the slacks `-g_i(xBar)`, and each such slack is positive.
  rw [strict_feasibility_margin_def]
  rcases Finset.mem_image.mp
      (Finset.min'_mem
        ((Finset.univ).image fun i : Fin m ↦ -g i xBar)
        (Finset.univ_nonempty.image fun i : Fin m ↦ -g i xBar)) with
    ⟨i, -, hi⟩
  rw [← hi]
  exact neg_pos.mpr (hgBar i)

/-- Helper for Theorem 8.42: the strict-feasibility margin is bounded above by each individual
slack `-g_i(xBar)`. -/
lemma strict_feasibility_margin_le_neg_constraint [NeZero m]
    {g : Fin m → E → ℝ} {xBar : E} (i : Fin m) :
    strict_feasibility_margin g xBar ≤ -g i xBar := by
  -- The minimum of the finite slack set is below every element of that set.
  rw [strict_feasibility_margin_def]
  exact Finset.min'_le
    ((Finset.univ).image fun j : Fin m ↦ -g j xBar)
    (-g i xBar)
    (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)

/-- Helper for Theorem 8.42: the source inequality first bounds the coordinate sum of a
superlevel multiplier by the Slater margin. -/
lemma sum_le_div_strict_feasibility_margin_of_mem_dual_objective_superlevel_set
    [NeZero m]
    {X : Set E} {f : E → ℝ} {g : Fin m → E → ℝ} {μ : ℝ}
    {xBar : E} {lam : Λ}
    (hxBar : xBar ∈ X)
    (hgBar : ∀ i : Fin m, g i xBar < 0)
    (hLam : lam ∈ dual_objective_superlevel_set X f g μ) :
    (∑ i, lam i) ≤ (f xBar - μ) / strict_feasibility_margin g xBar := by
  rcases (mem_dual_objective_superlevel_set.mp hLam) with ⟨hnonneg, hμ_le⟩
  have hmargin_pos : 0 < strict_feasibility_margin g xBar :=
    strict_feasibility_margin_pos (g := g) hgBar
  have hq_le :
      lagrangian_dual_objective X f (dual_constraint_vector g) lam ≤
        ((lagrangian f (dual_constraint_vector g) lam xBar : ℝ) : EReal) := by
    -- Evaluate the infimum defining `q(λ)` at the witness `xBar ∈ X`.
    rw [lagrangian_dual_objective_eq_sInf]
    exact sInf_le (Set.mem_image_of_mem
      (fun x : E ↦ ((lagrangian f (dual_constraint_vector g) lam x : ℝ) : EReal)) hxBar)
  have hμ_le_lagrangian :
      (μ : EReal) ≤ ((lagrangian f (dual_constraint_vector g) lam xBar : ℝ) : EReal) :=
    le_trans hμ_le hq_le
  have hμ_le_real : μ ≤ lagrangian f (dual_constraint_vector g) lam xBar := by
    exact_mod_cast hμ_le_lagrangian
  have hweighted_le : ∑ i, lam i * (-g i xBar) ≤ f xBar - μ := by
    -- This is the textbook inequality `-∑ λ_i g_i(xBar) ≤ f(xBar) - μ`.
    have hμ_le_real' : μ ≤ f xBar + ∑ i, lam i * g i xBar := by
      simpa [lagrangian_apply, dotProduct] using hμ_le_real
    have hneg_sum_le : -(∑ i, lam i * g i xBar) ≤ f xBar - μ := by
      linarith
    simpa using hneg_sum_le
  have hmargin_mul_sum :
      strict_feasibility_margin g xBar * ∑ i, lam i ≤
        ∑ i, lam i * (-g i xBar) := by
    -- Compare termwise using that every slack dominates the common minimum margin.
    calc
      strict_feasibility_margin g xBar * ∑ i, lam i
          = ∑ i, strict_feasibility_margin g xBar * lam i := by
              rw [Finset.mul_sum]
      _ ≤ ∑ i, lam i * (-g i xBar) := by
        refine Finset.sum_le_sum ?_
        intro i hi
        have hmul :
            strict_feasibility_margin g xBar * lam i ≤
              (-g i xBar) * lam i :=
          mul_le_mul_of_nonneg_right
            (strict_feasibility_margin_le_neg_constraint (g := g) (xBar := xBar) i)
            (hnonneg i)
        simpa [mul_comm] using hmul
  -- Divide by the positive margin to recover the bound on `∑ i, lam i`.
  refine (le_div_iff₀ hmargin_pos).mpr ?_
  calc
    (∑ i, lam i) * strict_feasibility_margin g xBar
        = strict_feasibility_margin g xBar * ∑ i, lam i := by ring
    _ ≤ ∑ i, lam i * (-g i xBar) := hmargin_mul_sum
    _ ≤ f xBar - μ := hweighted_le

/-- Helper for Theorem 8.42: on the nonnegative orthant, the Euclidean norm is bounded by the sum
of the coordinates. -/
lemma norm_le_sum_coords_of_nonneg
    {lam : Λ} (hnonneg : ∀ i : Fin m, 0 ≤ lam i) :
    ‖lam‖ ≤ ∑ i, lam i := by
  have hsum_nonneg : 0 ≤ ∑ i, lam i := by
    exact Finset.sum_nonneg fun i hi ↦ hnonneg i
  have hcoord_le_sum : ∀ i : Fin m, lam i ≤ ∑ j, lam j := by
    intro i
    exact Finset.single_le_sum (fun j hj ↦ hnonneg j) (Finset.mem_univ i)
  have hsum_sq_le : ∑ i, lam i ^ (2 : ℕ) ≤ (∑ i, lam i) ^ (2 : ℕ) := by
    -- Each square `λ_i²` is bounded by `λ_i * ∑ j λ_j`, and summing gives `(\sum_i λ_i)^2`.
    calc
      ∑ i, lam i ^ (2 : ℕ) = ∑ i, lam i * lam i := by
        simp [pow_two]
      _ ≤ ∑ i, lam i * ∑ j, lam j := by
        refine Finset.sum_le_sum ?_
        intro i hi
        exact mul_le_mul_of_nonneg_left (hcoord_le_sum i) (hnonneg i)
      _ = (∑ i, lam i) * ∑ j, lam j := by
        rw [Finset.sum_mul]
      _ = (∑ i, lam i) ^ (2 : ℕ) := by
        ring
  -- Convert the Euclidean norm to the square-root formula and compare squares.
  rw [EuclideanSpace.norm_eq]
  refine (Real.sqrt_le_iff.mpr ?_)
  constructor
  · exact hsum_nonneg
  · simpa [Real.norm_eq_abs, abs_of_nonneg, hnonneg] using hsum_sq_le

-- Proof sketch: use that `λ ∈ S_μ` means `μ ≤ q(λ)`, then bound `q(λ)` above by the Lagrangian
-- value at the strict feasible point `xBar`. Rearranging yields
-- `∑ i λ_i (-g_i(xBar)) ≤ f xBar - μ`; since each `λ_i ≥ 0` and each slack is at least
-- `strict_feasibility_margin g xBar`, obtain
-- `∑ i λ_i ≤ (f xBar - μ) / strict_feasibility_margin g xBar`.
-- Finally use `‖λ‖ ≤ ∑ i λ_i` for a coordinatewise nonnegative Euclidean vector.
/-- Theorem 8.42: if `xBar ∈ X` is a strict feasible point, as supplied by Assumption 8.41(E),
then every multiplier `λ` in the superlevel set `S_μ` of the dual objective satisfies the
Euclidean-norm bound `‖λ‖ ≤ (f(xBar) - μ) / min_i {-g_i(xBar)}`. -/
theorem norm_le_div_strict_feasibility_margin_of_mem_dual_objective_superlevel_set
    [NeZero m]
    (X : Set E) (f : E → ℝ) (g : Fin m → E → ℝ) (μ : ℝ) (xBar : E) (lam : Λ)
    (hxBar : xBar ∈ X)
    (hgBar : ∀ i : Fin m, g i xBar < 0)
    (hLam : lam ∈ dual_objective_superlevel_set X f g μ) :
    ‖lam‖ ≤ (f xBar - μ) / strict_feasibility_margin g xBar := by
  rcases (mem_dual_objective_superlevel_set.mp hLam) with ⟨hnonneg, -⟩
  -- Follow the source proof: first bound the coordinate sum, then use `ℓ₂ ≤ ℓ₁` on `ℝ₊^m`.
  calc
    ‖lam‖ ≤ ∑ i, lam i := norm_le_sum_coords_of_nonneg hnonneg
    _ ≤ (f xBar - μ) / strict_feasibility_margin g xBar :=
      sum_le_div_strict_feasibility_margin_of_mem_dual_objective_superlevel_set
        (hxBar := hxBar) (hgBar := hgBar) hLam

end
