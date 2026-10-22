/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Basic
import Mathlib.Order.Hom.CompleteLattice
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Notation_8_2_extra_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Theorem_8_4_1

noncomputable section

section Chapter08Exercise810

local notation "Point" => Fin 2 → ℝ

namespace ConstrainedOptimizationProblem

local notation "EPoint" => EuclideanSpace ℝ (Fin 2)

/-- Helper for Chapter08 Exercise 8.10: the KKT stationarity clause is expressed through the
Euclidean transport of the canonical Lagrangian. -/
def euclideanLagrangian
    (problem : _root_.ConstrainedOptimizationProblem 2 1 (∅ : Set (Fin 1)) (Set.univ : Set (Fin 1)))
    (lamStar : Fin 1 → ℝ) :
    EPoint → ℝ :=
  fun x ↦ problem.lagrangian ((EuclideanSpace.equiv (Fin 2) ℝ) x) lamStar

/-- Helper for Chapter08 Exercise 8.10: the local KKT owner specialized to the single-constraint
problems used in this item. -/
@[mk_iff]
class IsKKTPoint
    (problem : _root_.ConstrainedOptimizationProblem 2 1 (∅ : Set (Fin 1)) (Set.univ : Set (Fin 1)))
    (xStar : Point) (lamStar : Fin 1 → ℝ) : Prop where
  feasible : xStar ∈ problem
  dualFeasible : ∀ i ∈ problem.ineqIndices, 0 ≤ lamStar i
  stationarity : gradient (problem.euclideanLagrangian lamStar) (WithLp.toLp 2 xStar) = 0
  complementarySlackness :
    ∀ i ∈ problem.ineqIndices, lamStar i * problem.constraint i xStar = 0

end ConstrainedOptimizationProblem

local notation "EPoint" => EuclideanSpace ℝ (Fin 2)

-- Domain sampling:
-- * primary domain: constrained optimization / local duality for a single inequality problem
--   in `ℝ²`
-- * inspected owner declarations:
--   `ConstrainedOptimizationProblem.lagrangian` from `Definition_8_1_1`
--   the chapter notation bridge `𝓛[problem](x, lam)` from `Notation_8_2_extra_2`
--   `ConstrainedOptimizationProblem.euclideanLagrangian` and
--   `ConstrainedOptimizationProblem.IsKKTPoint` from `Theorem_8_2_7`
--   `ConstrainedOptimizationProblem.dualObjective` from `Theorem_8_4_1`
--   `IsLocalMinOn` / `IsLocalMaxOn` from mathlib `Topology.Order.LocalExtr`
-- * owner abstraction chosen here: the Chapter 8 constrained-problem owner
--   `exercise810Problem σ : ConstrainedOptimizationProblem 2 1 ∅ Set.univ`
-- * primitive data: the source objective and the single inequality constraint `x 0 ≥ 0`
-- * derived API kept here: the source scalar-`λ` bridge to the canonical KKT and dual-owner
--   surfaces via the canonical singleton vector literal `![λ]`

/-- The primal objective in Exercise 8.10 is
`(σ / 2) * (x 0)^2 + (1 / 2) * (x 1)^2 + x 0`. -/
def exercise810Objective (σ : ℝ) (x : Point) : ℝ :=
  (σ / 2) * (x 0) ^ (2 : ℕ) + ((1 : ℝ) / 2) * (x 1) ^ (2 : ℕ) + x 0

/-- The single inequality constraint of Exercise 8.10 is `x 0 ≥ 0`, encoded as the constraint
function `x ↦ x 0`. -/
def exercise810Constraint (x : Point) : ℝ :=
  x 0

/-- The Chapter 8 constrained-optimization owner specialized to Exercise 8.10. -/
def exercise810Problem (σ : ℝ) :
    ConstrainedOptimizationProblem 2 1 (∅ : Set (Fin 1)) (Set.univ : Set (Fin 1)) where
  objective := exercise810Objective σ
  constraint := fun _ x ↦ exercise810Constraint x
  eqIndices_union_ineqIndices := by simp
  eqIndices_disjoint_ineqIndices := by simp

/-- The feasible set of `exercise810Problem σ` is exactly the half-space `x 0 ≥ 0`. -/
theorem mem_exercise810Problem_feasibleSet_iff (σ : ℝ) (x : Point) :
    x ∈ (exercise810Problem σ).feasibleSet ↔ 0 ≤ x 0 := by
  simp [exercise810Problem, exercise810Constraint, ConstrainedOptimizationProblem.feasibleSet]

/-- The canonical Lagrangian of `exercise810Problem σ` specializes to the source formula
`L(x, λ) = f(x) - λ * x 0`. -/
theorem exercise810Problem_lagrangian_eq (σ lam : ℝ) (x : Point) :
    𝓛[exercise810Problem σ](x, ![lam]) =
      exercise810Objective σ x - lam * x 0 := by
  simp [exercise810Problem, exercise810Constraint, ConstrainedOptimizationProblem.lagrangian]

/-- The source scalar multiplier `λ` is admissible exactly when the corresponding one-coordinate
multiplier vector is admissible for the Chapter 8 dual owner. -/
theorem exercise810SingletonMultiplier_mem_admissibleMultiplierSet_iff
    (problem : ConstrainedOptimizationProblem 2 1
      (∅ : Set (Fin 1)) (Set.univ : Set (Fin 1))) (lam : ℝ) :
    ![lam] ∈ problem.admissibleMultiplierSet ↔
      lam ∈ Set.Ici (0 : ℝ) := by
  rw [ConstrainedOptimizationProblem.mem_admissibleMultiplierSet_iff]
  constructor
  · intro h
    exact h 0
  · intro hlam i
    fin_cases i
    simpa using hlam

/-- For Exercise 8.10, the canonical KKT owner at the origin is equivalent to the source scalar
conditions: `λ` is dual feasible and the canonical Euclidean Lagrangian is stationary at `0`. -/
theorem exercise810_isKKTPointAtOrigin_iff (σ lam : ℝ) :
    (exercise810Problem σ).IsKKTPoint 0 ![lam] ↔
      lam ∈ Set.Ici (0 : ℝ) ∧
        gradient ((exercise810Problem σ).euclideanLagrangian ![lam]) 0 = 0 := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have hlam :
          ![lam] ∈ (exercise810Problem σ).admissibleMultiplierSet := by
        rw [ConstrainedOptimizationProblem.mem_admissibleMultiplierSet_iff]
        intro i
        fin_cases i
        exact h.dualFeasible 0 (by
          simp [ConstrainedOptimizationProblem.ineqIndices])
      exact
        (exercise810SingletonMultiplier_mem_admissibleMultiplierSet_iff
          (exercise810Problem σ) lam).mp hlam
    · simpa using h.stationarity
  · rintro ⟨hlam, hstationary⟩
    have hlamVec :
        ![lam] ∈ (exercise810Problem σ).admissibleMultiplierSet :=
      (exercise810SingletonMultiplier_mem_admissibleMultiplierSet_iff
        (exercise810Problem σ) lam).mpr hlam
    have hlamVec' :
        ∀ i : Fin 1, 0 ≤ ![lam] i :=
      (ConstrainedOptimizationProblem.mem_admissibleMultiplierSet_iff
        (exercise810Problem σ) ![lam]).mp hlamVec
    refine
      { feasible := by
          change (0 : Point) ∈ (exercise810Problem σ).feasibleSet
          exact (mem_exercise810Problem_feasibleSet_iff σ 0).2 le_rfl
        dualFeasible := by
          intro i hi
          exact hlamVec' i
        stationarity := by
          simpa using hstationary
        complementarySlackness := ?_ }
    intro i hi
    fin_cases i
    simp [exercise810Problem, exercise810Constraint]

/-- Helper for Chapter08 Exercise 8.10: the `i`-th Euclidean coordinate projection has gradient
`eᵢ`. -/
theorem exercise810_hasGradientAt_euclidean_coordinate_projection
    (i : Fin 2) (x : EPoint) :
    HasGradientAt (fun y : EPoint ↦ y i) (EuclideanSpace.single i (1 : ℝ)) x := by
  -- The Fréchet-Riesz map identifies the coordinate vector `eᵢ` with evaluation at the
  -- `i`-th coordinate.
  rw [hasGradientAt_iff_hasFDerivAt]
  have hdual :
      InnerProductSpace.toDual ℝ EPoint (EuclideanSpace.single i (1 : ℝ)) =
        PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) i := by
    ext v
    simp [InnerProductSpace.toDual_apply_apply, EuclideanSpace.inner_single_left]
  simpa [hdual] using
    (PiLp.hasFDerivAt_apply (p := 2) (𝕜 := ℝ) (E := fun _ : Fin 2 ↦ ℝ) x i)

/-- Helper for Chapter08 Exercise 8.10: the quadratic coordinate term has zero gradient at the
origin. -/
theorem exercise810_coordinate_square_hasGradientAt_origin (i : Fin 2) :
    HasGradientAt (fun y : EPoint ↦ y i ^ (2 : ℕ)) 0 0 := by
  have hcoord :
      HasFDerivAt (fun y : EPoint ↦ y i)
        (InnerProductSpace.toDual ℝ EPoint (EuclideanSpace.single i (1 : ℝ))) (0 : EPoint) :=
    (exercise810_hasGradientAt_euclidean_coordinate_projection i 0).hasFDerivAt
  have hpow :
      HasDerivAt (fun z : ℝ ↦ z ^ (2 : ℕ)) (0 : ℝ) ((fun y : EPoint ↦ y i) 0) := by
    simpa using (hasDerivAt_pow 2 ((fun y : EPoint ↦ y i) 0))
  -- Route correction: isolate the one-dimensional power derivative before reassembling the
  -- Euclidean gradient, instead of unfolding the transported Lagrangian directly.
  have hcomp := hpow.comp_hasFDerivAt (0 : EPoint) hcoord
  change HasGradientAt ((fun z : ℝ ↦ z ^ (2 : ℕ)) ∘ fun y : EPoint ↦ y i) 0 0
  have hgrad_zero :
      HasGradientAt ((fun z : ℝ ↦ z ^ (2 : ℕ)) ∘ fun y : EPoint ↦ y i)
        ((InnerProductSpace.toDual ℝ EPoint).symm (0 : StrongDual ℝ EPoint)) 0 := by
    simpa using hcomp.hasGradientAt
  simpa using hgrad_zero

/-- Helper for Chapter08 Exercise 8.10: after transporting to Euclidean coordinates, the
Lagrangian is the source polynomial in the two coordinates. -/
theorem exercise810_euclideanLagrangian_eq_explicit (σ lam : ℝ) :
    (exercise810Problem σ).euclideanLagrangian ![lam] =
      fun y : EPoint ↦
        (σ / 2) * (y 0 ^ (2 : ℕ)) + ((1 : ℝ) / 2) * (y 1 ^ (2 : ℕ)) + (1 - lam) * y 0 := by
  -- Rewrite the transported owner back to the source two-variable polynomial.
  ext y
  rw [ConstrainedOptimizationProblem.euclideanLagrangian, exercise810Problem_lagrangian_eq]
  simp [exercise810Objective]
  ring

/-- Helper for Chapter08 Exercise 8.10: the explicit Euclidean Lagrangian has derivative
`z ↦ (1 - λ) * z 0` at the origin. -/
theorem exercise810_euclideanLagrangian_fderiv_at_origin (σ lam : ℝ) (z : EPoint) :
    fderiv ℝ
        (fun y : EPoint ↦
          (σ / 2) * (y 0 ^ (2 : ℕ)) + ((1 : ℝ) / 2) * (y 1 ^ (2 : ℕ)) + (1 - lam) * y 0)
        0 z =
      (1 - lam) * z 0 := by
  let g : EPoint → ℝ :=
    (fun y : EPoint ↦ (σ / 2) * (y 0 ^ (2 : ℕ))) +
      ((fun y : EPoint ↦ ((1 : ℝ) / 2) * (y 1 ^ (2 : ℕ))) +
        fun y : EPoint ↦ (1 - lam) * y 0)
  let L : StrongDual ℝ EPoint :=
    (1 - lam) • InnerProductSpace.toDual ℝ EPoint (EuclideanSpace.single 0 (1 : ℝ))
  have hg :
      g =
        (fun y : EPoint ↦
          (σ / 2) * (y 0 ^ (2 : ℕ)) + ((1 : ℝ) / 2) * (y 1 ^ (2 : ℕ)) + (1 - lam) * y 0) := by
    ext y
    simp [g, add_assoc]
  have hsquare0 :
      HasFDerivAt (fun y : EPoint ↦ y 0 ^ (2 : ℕ)) (0 : StrongDual ℝ EPoint) 0 := by
    simpa using (exercise810_coordinate_square_hasGradientAt_origin 0).hasFDerivAt
  have hsquare1 :
      HasFDerivAt (fun y : EPoint ↦ y 1 ^ (2 : ℕ)) (0 : StrongDual ℝ EPoint) 0 := by
    simpa using (exercise810_coordinate_square_hasGradientAt_origin 1).hasFDerivAt
  have hcoord0 :
      HasFDerivAt (fun y : EPoint ↦ y 0)
        (InnerProductSpace.toDual ℝ EPoint (EuclideanSpace.single 0 (1 : ℝ))) (0 : EPoint) :=
    (exercise810_hasGradientAt_euclidean_coordinate_projection 0 0).hasFDerivAt
  have hlinear :
      HasFDerivAt (fun y : EPoint ↦ (1 - lam) * y 0) L (0 : EPoint) := by
    simpa [L] using hcoord0.const_mul (1 - lam)
  have hsum :
      HasFDerivAt g
        (((σ / 2) • (0 : StrongDual ℝ EPoint)) + (((1 : ℝ) / 2) • (0 : StrongDual ℝ EPoint) + L))
        (0 : EPoint) := by
    -- The two quadratic summands contribute zero derivative at the origin; only the linear term
    -- remains.
    exact (hsquare0.const_mul (σ / 2)).add ((hsquare1.const_mul ((1 : ℝ) / 2)).add hlinear)
  rw [← hg]
  calc
    fderiv ℝ g 0 z
      = ((((σ / 2) • (0 : StrongDual ℝ EPoint)) +
            (((1 : ℝ) / 2) • (0 : StrongDual ℝ EPoint) + L)) z) := by
          rw [hsum.fderiv]
    _ = (1 - lam) * z 0 := by
      simp [L, InnerProductSpace.toDual_apply_apply, EuclideanSpace.inner_single_left]

/-- Helper for Chapter08 Exercise 8.10: the transported Lagrangian has gradient
`(1 - λ, 0)` at the origin for every `σ`. -/
theorem exercise810_euclideanLagrangian_gradient_at_origin (σ lam : ℝ) :
    gradient ((exercise810Problem σ).euclideanLagrangian ![lam]) 0 =
      EuclideanSpace.single 0 (1 - lam) := by
  -- Route correction: first freeze the transported Lagrangian into the explicit source
  -- polynomial, then compute its `fderiv` at `0` before converting back through `toDual`.
  have hfderiv :
      fderiv ℝ
          (fun y : EPoint ↦
            (σ / 2) * (y 0 ^ (2 : ℕ)) + ((1 : ℝ) / 2) * (y 1 ^ (2 : ℕ)) + (1 - lam) * y 0)
          0 =
        InnerProductSpace.toDual ℝ EPoint (EuclideanSpace.single 0 (1 - lam)) := by
    ext z
    simp [InnerProductSpace.toDual_apply_apply, EuclideanSpace.inner_single_left]
    simpa using exercise810_euclideanLagrangian_fderiv_at_origin σ lam z
  -- The computed derivative is exactly the Riesz image of the coordinate vector `(1 - λ, 0)`.
  rw [exercise810_euclideanLagrangian_eq_explicit, gradient, hfderiv]
  exact
    (InnerProductSpace.toDual ℝ EPoint).symm_apply_apply
      (EuclideanSpace.single 0 (1 - lam))

/-- Helper for Chapter08 Exercise 8.10: for `σ = 1`, completing the square isolates the
`λ`-dependent constant term in the Lagrangian. -/
theorem exercise810SigmaOne_lagrangian_completed_square (lam : ℝ) (x : Point) :
    𝓛[exercise810Problem 1](x, ![lam]) =
      ((x 0 - (lam - 1)) ^ (2 : ℕ)) / 2 + (x 1 ^ (2 : ℕ)) / 2 -
        ((lam - 1) ^ (2 : ℕ)) / 2 := by
  -- The source computation is a direct completion-of-the-square identity.
  rw [exercise810Problem_lagrangian_eq]
  simp [exercise810Objective]
  ring

/-- Helper for Chapter08 Exercise 8.10: for `σ = 1`, the completed-square formula is minimized
at `x = ![lam - 1, 0]`. -/
theorem exercise810SigmaOne_attains_dualObjective (lam : ℝ) :
    IsMinOn (fun x : Point ↦ 𝓛[exercise810Problem 1](x, ![lam])) Set.univ ![lam - 1, 0] := by
  -- The completed squares are both nonnegative, so the explicit center minimizes the
  -- Lagrangian on all of `ℝ²`.
  rw [isMinOn_univ_iff]
  intro x
  rw [exercise810SigmaOne_lagrangian_completed_square]
  rw [exercise810SigmaOne_lagrangian_completed_square]
  have hnonneg :
      0 ≤ ((x 0 - (lam - 1)) ^ (2 : ℕ)) / 2 + (x 1 ^ (2 : ℕ)) / 2 := by
    positivity
  simpa only [Fin.isValue, Matrix.cons_val_zero, sub_self, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, zero_div, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    add_zero, zero_sub, neg_le_sub_iff_le_add, le_add_iff_nonneg_left] using hnonneg

/-- Helper for Chapter08 Exercise 8.10: an attained minimizer of the Lagrangian computes the
dual objective at the same multiplier, without any admissibility side condition. -/
theorem exercise810_dualObjective_of_attained_minimizer
    {σ lam : ℝ} {x0 : Point}
    (hmin : IsMinOn (fun x : Point ↦ 𝓛[exercise810Problem σ](x, ![lam])) Set.univ x0) :
    (exercise810Problem σ).dualObjective ![lam] =
      ((𝓛[exercise810Problem σ](x0, ![lam]) : ℝ) : WithBot ℝ) := by
  -- Route correction: compute the infimum directly from the minimizing point, instead of routing
  -- through the stronger attained-dual-feasible owner that also requires admissibility.
  refine le_antisymm ?_ ?_
  · have hx :
        ((𝓛[exercise810Problem σ](x0, ![lam]) : ℝ) : WithBot ℝ) ∈
          Set.range (fun y : Point ↦
            ((𝓛[exercise810Problem σ](y, ![lam]) : ℝ) : WithBot ℝ)) :=
      ⟨x0, rfl⟩
    simpa [ConstrainedOptimizationProblem.dualObjective_eq] using csInf_le' hx
  · rw [ConstrainedOptimizationProblem.dualObjective_eq]
    refine (le_csInf_iff'' ?_).2 ?_
    · exact ⟨_, ⟨x0, rfl⟩⟩
    · intro z hz
      rcases hz with ⟨y, rfl⟩
      have hxy :
          𝓛[exercise810Problem σ](x0, ![lam]) ≤
            𝓛[exercise810Problem σ](y, ![lam]) :=
        (isMinOn_univ_iff.mp hmin) y
      simpa using
        (show ((𝓛[exercise810Problem σ](x0, ![lam]) : ℝ) : WithBot ℝ) ≤
            ((𝓛[exercise810Problem σ](y, ![lam]) : ℝ) : WithBot ℝ) from
          by exact_mod_cast hxy)

/-- Helper for Chapter08 Exercise 8.10: for `σ = 1`, the dual objective admits the explicit
quadratic closed form at every real multiplier. -/
theorem exercise810SigmaOne_dualObjective_formula_aux (lam : ℝ) :
    (exercise810Problem 1).dualObjective ![lam] =
      (((-((lam - 1) ^ (2 : ℕ))) / 2 : ℝ) : WithBot ℝ) := by
  have hdual :=
    exercise810_dualObjective_of_attained_minimizer
      (σ := 1) (lam := lam) (x0 := ![lam - 1, 0])
      (exercise810SigmaOne_attains_dualObjective lam)
  -- Evaluate the minimized completed-square value at its center.
  have hvalue :
      𝓛[exercise810Problem 1](![lam - 1, 0], ![lam]) =
        (-((lam - 1) ^ (2 : ℕ))) / 2 := by
    rw [exercise810Problem_lagrangian_eq]
    simp [exercise810Objective]
    ring
  simpa [hvalue] using hdual

/-- Helper for Chapter08 Exercise 8.10: if `λ ≠ 1` is dual-feasible for `σ = 1`, then moving
slightly toward `1` stays feasible and strictly improves the dual value. -/
theorem exercise810SigmaOne_exists_nearby_better_dualValue
    {lam : ℝ} (hlam : lam ∈ Set.Ici (0 : ℝ)) (hlam_ne : lam ≠ 1) :
    ∀ ε > 0, ∃ μ ∈ Set.Ici (0 : ℝ), |μ - lam| < ε ∧
      (exercise810Problem 1).dualObjective ![lam] <
        (exercise810Problem 1).dualObjective ![μ] := by
  intro ε hε
  rcases lt_or_gt_of_ne hlam_ne with hlam_lt | hlam_gt
  · let δ : ℝ := min (ε / 2) ((1 - lam) / 2)
    have hδ_pos : 0 < δ := by
      dsimp [δ]
      positivity
    have hδ_eps : δ < ε := by
      have hhalf_lt : ε / 2 < ε := by nlinarith
      exact lt_of_le_of_lt (min_le_left _ _) hhalf_lt
    have hδ_gap : δ < 1 - lam := by
      have hhalf_lt : (1 - lam) / 2 < 1 - lam := by nlinarith
      exact lt_of_le_of_lt (min_le_right _ _) hhalf_lt
    refine ⟨lam + δ, ?_, ?_, ?_⟩
    · -- Moving right from a feasible `λ` keeps the multiplier feasible.
      exact add_nonneg hlam hδ_pos.le
    · -- The perturbation size is exactly `δ`.
      simpa [Real.dist_eq, δ, abs_of_nonneg hδ_pos.le] using hδ_eps
    · have hsq :
          (lam + δ - 1) ^ (2 : ℕ) < (lam - 1) ^ (2 : ℕ) := by
        nlinarith [hδ_pos, hδ_gap, hlam_lt]
      rw [exercise810SigmaOne_dualObjective_formula_aux,
        exercise810SigmaOne_dualObjective_formula_aux]
      exact_mod_cast (by nlinarith)
  · let δ : ℝ := min (ε / 2) ((lam - 1) / 2)
    have hδ_pos : 0 < δ := by
      dsimp [δ]
      positivity
    have hδ_eps : δ < ε := by
      have hhalf_lt : ε / 2 < ε := by nlinarith
      exact lt_of_le_of_lt (min_le_left _ _) hhalf_lt
    have hδ_gap : δ < lam - 1 := by
      have hhalf_lt : (lam - 1) / 2 < lam - 1 := by nlinarith
      exact lt_of_le_of_lt (min_le_right _ _) hhalf_lt
    refine ⟨lam - δ, ?_, ?_, ?_⟩
    · -- Moving left but staying within half the gap to `1` preserves nonnegativity.
      have hμ_pos : 0 < lam - δ := by
        nlinarith
      exact hμ_pos.le
    · -- The perturbation size is again exactly `δ`.
      have habs : |(lam - δ) - lam| = δ := by
        rw [show (lam - δ) - lam = -δ by ring]
        rw [abs_neg]
        simp [abs_of_pos hδ_pos]
      have hdist : |(lam - δ) - lam| < ε := by
        rw [habs]
        exact hδ_eps
      simpa using hdist
    · have hsq :
          (lam - δ - 1) ^ (2 : ℕ) < (lam - 1) ^ (2 : ℕ) := by
        nlinarith [hδ_pos, hδ_gap, hlam_gt]
      rw [exercise810SigmaOne_dualObjective_formula_aux,
        exercise810SigmaOne_dualObjective_formula_aux]
      exact_mod_cast (by nlinarith)

/-- Helper for Chapter08 Exercise 8.10: for `σ = -1`, the Lagrangian is unbounded below along
the horizontal ray `x = ![t, 0]`. -/
theorem exercise810SigmaNegOne_lagrangian_unbounded_below (lam a : ℝ) :
    ∃ t : ℝ, 𝓛[exercise810Problem (-1)](![t, 0], ![lam]) < a := by
  let t : ℝ := 2 * (|1 - lam| + |a| + 1)
  refine ⟨t, ?_⟩
  have hlinear :
      (1 - lam) * t ≤ |1 - lam| * t := by
    gcongr
    exact le_abs_self (1 - lam)
  have htail :
      -t * (|a| + 1) ≤ -(|a| + 1) := by
    have ht_ge_one : 1 ≤ t := by
      dsimp [t]
      nlinarith [abs_nonneg (1 - lam), abs_nonneg a]
    have hmul : |a| + 1 ≤ t * (|a| + 1) := by
      nlinarith [ht_ge_one, abs_nonneg a]
    nlinarith
  have ha_lt : -(|a| + 1) < a := by
    have hbound : -|a| ≤ a := neg_abs_le a
    nlinarith
  -- Along the horizontal ray, the negative quadratic term dominates the linear term.
  calc
    𝓛[exercise810Problem (-1)](![t, 0], ![lam])
        = -(t ^ (2 : ℕ)) / 2 + (1 - lam) * t := by
          rw [exercise810Problem_lagrangian_eq]
          simp [exercise810Objective, t]
          ring
    _ ≤ -(t ^ (2 : ℕ)) / 2 + |1 - lam| * t := by gcongr
    _ = -t * (|a| + 1) := by
          dsimp [t]
          ring
    _ ≤ -(|a| + 1) := htail
    _ < a := ha_lt

/-- For `σ = 1`, the origin is a local minimizer of the primal problem in Exercise 8.10. -/
theorem exercise810SigmaOne_origin_isLocalMinOn :
    IsLocalMinOn (exercise810Problem 1) (exercise810Problem 1).feasibleSet 0 := by
  change IsLocalMinOn (exercise810Objective 1) (exercise810Problem 1).feasibleSet 0
  refine
    (show IsMinOn (exercise810Objective 1) (exercise810Problem 1).feasibleSet 0 from ?_).localize
  rw [isMinOn_iff]
  intro x hx
  have hx0 : 0 ≤ x 0 := (mem_exercise810Problem_feasibleSet_iff 1 x).mp hx
  have hnonneg :
      0 ≤ (1 / 2 : ℝ) * (x 0 ^ (2 : ℕ)) + (1 / 2 : ℝ) * (x 1 ^ (2 : ℕ)) + x 0 := by
    nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), hx0]
  -- On the feasible half-space every term in the explicit objective is nonnegative.
  simpa [exercise810Objective] using hnonneg

/-- For `σ = 1`, the multiplier at the primal local minimizer `0` is `λ = 1`. -/
theorem exercise810SigmaOne_origin_hasMultiplierOne :
    (exercise810Problem 1).IsKKTPoint 0 ![1] := by
  -- The explicit origin gradient shows the transported Lagrangian is stationary for `λ = 1`.
  rw [exercise810_isKKTPointAtOrigin_iff]
  refine ⟨by simp, ?_⟩
  have hzero : EuclideanSpace.single 0 (0 : ℝ) = (0 : EPoint) := by
    ext i
    fin_cases i <;> simp
  simpa [hzero] using exercise810_euclideanLagrangian_gradient_at_origin 1 1

/-- For `σ = 1`, the dual objective is the quadratic
`λ ↦ -((λ - 1)^2) / 2`. -/
theorem exercise810SigmaOne_dualObjective_formula (lam : ℝ) :
    (exercise810Problem 1).dualObjective ![lam] =
      (((-((lam - 1) ^ (2 : ℕ))) / 2 : ℝ) : WithBot ℝ) := by
  simpa using exercise810SigmaOne_dualObjective_formula_aux lam

/-- For `σ = 1`, the dual problem has a local maximizer at `λ = 1`. -/
theorem exercise810SigmaOne_one_isLocalMaxOn :
    IsLocalMaxOn
      (fun lam ↦ (exercise810Problem 1).dualObjective ![lam])
      (Set.Ici (0 : ℝ)) 1 := by
  refine (show IsMaxOn
    (fun lam ↦ (exercise810Problem 1).dualObjective ![lam])
    (Set.Ici (0 : ℝ)) 1 from ?_).localize
  rw [isMaxOn_iff]
  intro μ hμ
  rw [exercise810SigmaOne_dualObjective_formula, exercise810SigmaOne_dualObjective_formula]
  have hreal :
      (((-((μ - 1) ^ (2 : ℕ))) / 2 : ℝ)) ≤ (((-((1 - 1) ^ (2 : ℕ))) / 2 : ℝ)) := by
    nlinarith [sq_nonneg (μ - 1)]
  exact_mod_cast hreal

/-- For `σ = 1`, every local dual solution on `Set.Ici 0` agrees with the primal multiplier
`λ = 1`. -/
theorem exercise810SigmaOne_localDualSolution_eq_primalMultiplier
    {lam : ℝ} (hlam : lam ∈ Set.Ici (0 : ℝ))
    (hdual : IsLocalMaxOn
      (fun μ ↦ (exercise810Problem 1).dualObjective ![μ])
      (Set.Ici (0 : ℝ)) lam) :
    lam = 1 := by
  by_contra hlam_ne
  change
    {μ : ℝ |
        (exercise810Problem 1).dualObjective ![μ] ≤
          (exercise810Problem 1).dualObjective ![lam]} ∈
      nhdsWithin lam (Set.Ici (0 : ℝ)) at hdual
  rcases Metric.mem_nhdsWithin_iff.mp hdual with ⟨ε, hε, hεball⟩
  rcases exercise810SigmaOne_exists_nearby_better_dualValue hlam hlam_ne ε hε with
    ⟨μ, hμ_feas, hμ_close, hμ_better⟩
  have hμ_mem : μ ∈ Metric.ball lam ε ∩ Set.Ici (0 : ℝ) := by
    refine ⟨?_, hμ_feas⟩
    simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hμ_close
  have hμ_local :
      (exercise810Problem 1).dualObjective ![μ] ≤
        (exercise810Problem 1).dualObjective ![lam] :=
    hεball hμ_mem
  exact not_lt_of_ge hμ_local hμ_better

/-- Helper for Chapter08 Exercise 8.10: within the feasible half-space, points sufficiently near
the origin still satisfy `x 0 < 1`. -/
theorem exercise810_sigmaNegOne_lt_one_neighborhood :
    {x : Point | x 0 < 1} ∈ nhdsWithin (0 : Point) ((exercise810Problem (-1)).feasibleSet) := by
  have hopen :
      {x : Point | x 0 < 1} ∈ nhds (0 : Point) := by
    -- The first coordinate is continuous, so the strict inequality defines an open neighborhood
    -- of the origin.
    have hset_open : IsOpen {x : Point | x 0 < 1} :=
      isOpen_lt (continuous_apply 0) continuous_const
    exact hset_open.mem_nhds (by simp)
  exact mem_nhdsWithin_of_mem_nhds hopen

/-- Helper for Chapter08 Exercise 8.10: on the feasible side with `x 0 < 1`, the `σ = -1`
objective is nonnegative. -/
theorem exercise810_sigmaNegOne_objective_nonneg_of_feasible_lt_one
    {x : Point} (hx : x ∈ (exercise810Problem (-1)).feasibleSet) (hx_lt : x 0 < 1) :
    0 ≤ exercise810Objective (-1) x := by
  have hx0 : 0 ≤ x 0 := (mem_exercise810Problem_feasibleSet_iff (-1) x).mp hx
  have hx0_sq_le : x 0 ^ (2 : ℕ) ≤ x 0 := by
    nlinarith
  have hnonneg :
      0 ≤ x 0 - (x 0 ^ (2 : ℕ)) / 2 + (x 1 ^ (2 : ℕ)) / 2 := by
    -- The source one-dimensional inequality `0 ≤ x₀ - x₀² / 2` combines with the nonnegative
    -- second quadratic term.
    nlinarith [hx0_sq_le, sq_nonneg (x 1)]
  have hobjective :
      exercise810Objective (-1) x =
        x 0 - (x 0 ^ (2 : ℕ)) / 2 + (x 1 ^ (2 : ℕ)) / 2 := by
    simp [exercise810Objective]
    ring
  rw [hobjective]
  exact hnonneg

/-- For `σ = -1`, the origin is still a local minimizer of the primal problem in Exercise 8.10.
-/
theorem exercise810SigmaNegOne_origin_isLocalMinOn :
    IsLocalMinOn (exercise810Problem (-1)) (exercise810Problem (-1)).feasibleSet 0 := by
  change
    IsLocalMinOn (exercise810Objective (-1)) (exercise810Problem (-1)).feasibleSet 0
  change
    ∀ᶠ x in nhdsWithin (0 : Point) ((exercise810Problem (-1)).feasibleSet),
      exercise810Objective (-1) 0 ≤ exercise810Objective (-1) x
  -- Work directly in `nhdsWithin`: the feasible filter already keeps points in the half-space,
  -- and the new neighborhood lemma adds `x 0 < 1`.
  filter_upwards [self_mem_nhdsWithin, exercise810_sigmaNegOne_lt_one_neighborhood] with x hx hx_lt
  have hnonneg :=
    exercise810_sigmaNegOne_objective_nonneg_of_feasible_lt_one hx hx_lt
  simpa [exercise810Objective] using hnonneg

/-- For `σ = -1`, the primal local minimizer `0` still has the multiplier `λ = 1`. -/
theorem exercise810SigmaNegOne_origin_hasMultiplierOne :
    (exercise810Problem (-1)).IsKKTPoint 0 ![1] := by
  -- The same origin-gradient computation works for `σ = -1` because the quadratic terms vanish
  -- at the origin.
  rw [exercise810_isKKTPointAtOrigin_iff]
  refine ⟨by simp, ?_⟩
  have hzero : EuclideanSpace.single 0 (0 : ℝ) = (0 : EPoint) := by
    ext i
    fin_cases i <;> simp
  simpa [hzero] using exercise810_euclideanLagrangian_gradient_at_origin (-1) 1

/-- For `σ = -1`, the dual value is identically `⊥ = -∞`. -/
theorem exercise810SigmaNegOne_dualObjective_eq_bot (lam : ℝ) :
    (exercise810Problem (-1)).dualObjective ![lam] = ⊥ := by
  by_contra hbot
  obtain ⟨b, hb⟩ := WithBot.ne_bot_iff_exists.mp hbot
  rcases exercise810SigmaNegOne_lagrangian_unbounded_below lam (b - 1) with ⟨t, ht⟩
  have hle :
      (exercise810Problem (-1)).dualObjective ![lam] ≤
        ((𝓛[exercise810Problem (-1)](![t, 0], ![lam]) : ℝ) : WithBot ℝ) :=
    ConstrainedOptimizationProblem.dualObjective_le_lagrangian
      (problem := exercise810Problem (-1)) ![t, 0] ![lam]
  have hle_coe :
      ((b : ℝ) : WithBot ℝ) ≤
        ((𝓛[exercise810Problem (-1)](![t, 0], ![lam]) : ℝ) : WithBot ℝ) := by
    simpa [hb] using hle
  have hle_real :
      b ≤ 𝓛[exercise810Problem (-1)](![t, 0], ![lam]) := by
    exact_mod_cast hle_coe
  linarith

/-- For `σ = -1`, every feasible multiplier is a local dual solution because the dual value is
constantly `⊥`. -/
theorem exercise810SigmaNegOne_everyFeasibleMultiplier_isLocalMaxOn
    {lam : ℝ} (_hlam : lam ∈ Set.Ici (0 : ℝ)) :
    IsLocalMaxOn
      (fun μ ↦ (exercise810Problem (-1)).dualObjective ![μ])
      (Set.Ici (0 : ℝ)) lam := by
  refine (show IsMaxOn
    (fun μ ↦ (exercise810Problem (-1)).dualObjective ![μ])
    (Set.Ici (0 : ℝ)) lam from ?_).localize
  rw [isMaxOn_iff]
  intro μ hμ
  simp [exercise810SigmaNegOne_dualObjective_eq_bot]

/-- For `σ = -1`, a local dual solution need not agree with the primal multiplier `λ = 1`. -/
theorem exercise810SigmaNegOne_localDualSolution_needNotEqualPrimalMultiplier :
    ∃ lam ∈ Set.Ici (0 : ℝ),
      lam ≠ 1 ∧
        IsLocalMaxOn
          (fun μ ↦ (exercise810Problem (-1)).dualObjective ![μ])
          (Set.Ici (0 : ℝ)) lam := by
  refine ⟨0, by simp, by simp, ?_⟩
  exact exercise810SigmaNegOne_everyFeasibleMultiplier_isLocalMaxOn (by simp)

/-- Chapter08 Exercise 8.10: the dual problem is the one-variable maximization problem in the
multiplier `λ`; for `σ = 1`, the local dual solution agrees with the primal multiplier `λ = 1`,
while for `σ = -1` there are local dual solutions different from the primal multiplier. -/
theorem exercise810_duality_behavior :
    (IsLocalMinOn (exercise810Problem 1) (exercise810Problem 1).feasibleSet 0 ∧
      (exercise810Problem 1).IsKKTPoint 0 ![1] ∧
      IsLocalMaxOn
        (fun lam ↦ (exercise810Problem 1).dualObjective ![lam])
        (Set.Ici (0 : ℝ)) 1 ∧
      ∀ {lam : ℝ},
        lam ∈ Set.Ici (0 : ℝ) →
          IsLocalMaxOn
            (fun μ ↦ (exercise810Problem 1).dualObjective ![μ])
            (Set.Ici (0 : ℝ)) lam →
          lam = 1) ∧
    (IsLocalMinOn (exercise810Problem (-1)) (exercise810Problem (-1)).feasibleSet 0 ∧
      (exercise810Problem (-1)).IsKKTPoint 0 ![1] ∧
      ∃ lam ∈ Set.Ici (0 : ℝ),
        lam ≠ 1 ∧
          IsLocalMaxOn
            (fun μ ↦ (exercise810Problem (-1)).dualObjective ![μ])
            (Set.Ici (0 : ℝ)) lam) := by
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · exact exercise810SigmaOne_origin_isLocalMinOn
    · exact exercise810SigmaOne_origin_hasMultiplierOne
    · exact exercise810SigmaOne_one_isLocalMaxOn
    · intro lam hlam hdual
      exact exercise810SigmaOne_localDualSolution_eq_primalMultiplier hlam hdual
  · refine ⟨?_, ?_, ?_⟩
    · exact exercise810SigmaNegOne_origin_isLocalMinOn
    · exact exercise810SigmaNegOne_origin_hasMultiplierOne
    · exact exercise810SigmaNegOne_localDualSolution_needNotEqualPrimalMultiplier

end Chapter08Exercise810
