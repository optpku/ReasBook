/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Group.Bounds
import Mathlib.Order.Filter.AtTopBot.Basic
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap08.subgradient

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
open WithLp

-- The Chapter 8 owner for the affine subgradient inequality on a comparison set is
-- `IsSubgradientAtOn` from `Integer.Chapters.Chap08.subgradient`. This file reuses that owner
-- and adds the projected subgradient iteration layer on top of it.
-- Semantic recall note: `lean_leansearch` found only generic bounded-set lemmas, not a canonical
-- bounded-subgradient owner, so the source-faithful boundedness hypothesis remains quantified
-- directly over `IsSubgradientAtOn`.

section Theorem811

variable {n : ℕ}

/-- Helper for Theorem 8.11: the Euclidean norm on `Fin n → ℝ`, realized via the canonical
embedding into `EuclideanSpace ℝ (Fin n)`. -/
noncomputable abbrev euclideanNorm (x : Fin n → ℝ) : ℝ :=
  ‖toLp 2 x‖

/-- Helper for Theorem 8.11: unfolding `euclideanNorm` identifies it with the norm of the
canonical `toLp 2` image. -/
theorem euclideanNorm_eq_norm_toLp
    (x : Fin n → ℝ) :
    euclideanNorm x = ‖toLp 2 x‖ :=
  rfl

/-- Helper for Theorem 8.11: the Euclidean distance on `Fin n → ℝ`, realized through the
canonical `toLp 2` embedding into `EuclideanSpace ℝ (Fin n)`. -/
noncomputable abbrev euclideanDist
    (x y : Fin n → ℝ) : ℝ :=
  dist (toLp 2 x) (toLp 2 y)

/-- Helper for Theorem 8.11: unfolding `euclideanDist` identifies it with the distance between
the corresponding Euclidean-space points. -/
theorem euclideanDist_eq_dist_toLp
    (x y : Fin n → ℝ) :
    euclideanDist x y = dist (toLp 2 x) (toLp 2 y) :=
  rfl

/-- Helper for Theorem 8.11: the Euclidean inner product on `Fin n → ℝ` agrees with the
coordinatewise dot-product formula. -/
theorem realInner_toLp_eq_sum_mul
    (x y : Fin n → ℝ) :
    inner ℝ (toLp 2 x) (toLp 2 y) = ∑ i, x i * y i := by
  simpa [dotProduct, mul_comm] using EuclideanSpace.inner_toLp_toLp x y

/-- A projection operator onto `P` together with the textbook Euclidean metric property that
projecting does not increase the distance to points already in `P`. -/
structure ProjectionOnto (P : Set (Fin n → ℝ)) where
  toFun : (Fin n → ℝ) → (Fin n → ℝ)
  mapsTo : Set.MapsTo toFun Set.univ P
  dist_le : ∀ x y, y ∈ P → euclideanDist (toFun x) y ≤ euclideanDist x y

namespace ProjectionOnto

/-- A projection operator onto `P` is used as a function on ambient vectors. -/
instance (P : Set (Fin n → ℝ)) :
    CoeFun (ProjectionOnto P) (fun _ ↦ (Fin n → ℝ) → (Fin n → ℝ)) where
  coe proj := proj.toFun

/-- Applying a projection operator lands in the feasible set. -/
theorem map_mem
    {P : Set (Fin n → ℝ)}
    (proj : ProjectionOnto P)
    (x : Fin n → ℝ) :
    proj x ∈ P :=
  proj.mapsTo (by simp)

end ProjectionOnto

/-- One projected subgradient step from `x` with chosen subgradient `s` and stepsize `α`. -/
def projected_subgradient_step
    {P : Set (Fin n → ℝ)}
    (proj : ProjectionOnto P)
    (x s : Fin n → ℝ)
    (α : ℝ) : Fin n → ℝ :=
  proj (fun i ↦ x i - α * s i)

/-- A projected subgradient step always lies in the feasible set `P`. -/
theorem projected_subgradient_step_mem
    {P : Set (Fin n → ℝ)}
    (proj : ProjectionOnto P)
    (x s : Fin n → ℝ)
    (α : ℝ) :
    projected_subgradient_step proj x s α ∈ P :=
  proj.map_mem _

/-- The running best objective value up to time `t`, corresponding to the textbook sequence
`g_best^1, g_best^2, ...` after shifting to Lean's `0`-based indexing. -/
noncomputable def subgradient_best_value
    (g : (Fin n → ℝ) → ℝ)
    (x : ℕ → Fin n → ℝ)
    (t : ℕ) : ℝ :=
  (Finset.range (t + 1)).inf' (by simp) (fun k ↦ g (x k))

/-- The running best value is bounded above by the current objective value. -/
theorem subgradient_best_value_le_current
    (g : (Fin n → ℝ) → ℝ)
    (x : ℕ → Fin n → ℝ)
    (t : ℕ) :
    subgradient_best_value g x t ≤ g (x t) := by
  rw [subgradient_best_value]
  exact Finset.inf'_le _ (by simp [Finset.mem_range])

/-- Helper for Theorem 8.11: the running best value up to time `k` is bounded above by every
objective value appearing in the first `k + 1` iterates. -/
theorem subgradient_best_value_le_of_mem_range
    (g : (Fin n → ℝ) → ℝ)
    (x : ℕ → Fin n → ℝ)
    {k t : ℕ}
    (ht : t ∈ Finset.range (k + 1)) :
    subgradient_best_value g x k ≤ g (x t) := by
  rw [subgradient_best_value]
  exact Finset.inf'_le _ ht

/-- `IsProjectedSubgradientMethodSequence g P proj α x s` means that `x` starts in `P` and evolves
by projected subgradient steps for `g` with stepsizes `α` and chosen subgradients `s`. -/
def IsProjectedSubgradientMethodSequence
    (g : (Fin n → ℝ) → ℝ)
    (P : Set (Fin n → ℝ))
    (proj : ProjectionOnto P)
    (α : ℕ → ℝ)
    (x s : ℕ → Fin n → ℝ) : Prop :=
  x 0 ∈ P ∧
    ∀ t : ℕ,
      IsSubgradientAtOn g P (x t) (s t) ∧
        x (t + 1) = projected_subgradient_step proj (x t) (s t) (α t)

/-- Unfolding `IsProjectedSubgradientMethodSequence` gives the stagewise projected-subgradient
update rule together with the subgradient condition at each iterate. -/
theorem is_projected_subgradient_method_sequence_iff
    (g : (Fin n → ℝ) → ℝ)
    (P : Set (Fin n → ℝ))
    (proj : ProjectionOnto P)
    (α : ℕ → ℝ)
    (x s : ℕ → Fin n → ℝ) :
    IsProjectedSubgradientMethodSequence g P proj α x s ↔
      x 0 ∈ P ∧
        ∀ t : ℕ,
          IsSubgradientAtOn g P (x t) (s t) ∧
            x (t + 1) = projected_subgradient_step proj (x t) (s t) (α t) :=
  Iff.rfl

namespace IsProjectedSubgradientMethodSequence

/-- The initial iterate of a projected subgradient method sequence lies in the feasible set. -/
theorem zero_mem
    {g : (Fin n → ℝ) → ℝ}
    {P : Set (Fin n → ℝ)}
    {proj : ProjectionOnto P}
    {α : ℕ → ℝ}
    {x s : ℕ → Fin n → ℝ}
    (hmethod : IsProjectedSubgradientMethodSequence g P proj α x s) :
    x 0 ∈ P :=
  hmethod.1

/-- Each chosen direction in a projected subgradient method sequence is a subgradient at the
current iterate. -/
theorem isSubgradientAtOn
    {g : (Fin n → ℝ) → ℝ}
    {P : Set (Fin n → ℝ)}
    {proj : ProjectionOnto P}
    {α : ℕ → ℝ}
    {x s : ℕ → Fin n → ℝ}
    (hmethod : IsProjectedSubgradientMethodSequence g P proj α x s)
    (t : ℕ) :
    IsSubgradientAtOn g P (x t) (s t) :=
  (hmethod.2 t).1

/-- Each projected subgradient iterate is obtained from the previous iterate by one projected
subgradient step. -/
theorem step_eq
    {g : (Fin n → ℝ) → ℝ}
    {P : Set (Fin n → ℝ)}
    {proj : ProjectionOnto P}
    {α : ℕ → ℝ}
    {x s : ℕ → Fin n → ℝ}
    (hmethod : IsProjectedSubgradientMethodSequence g P proj α x s)
    (t : ℕ) :
    x (t + 1) = projected_subgradient_step proj (x t) (s t) (α t) :=
  (hmethod.2 t).2

/-- Every iterate after the initial point of a projected subgradient method sequence remains in
the feasible set. -/
theorem succ_mem
    {g : (Fin n → ℝ) → ℝ}
    {P : Set (Fin n → ℝ)}
    {proj : ProjectionOnto P}
    {α : ℕ → ℝ}
    {x s : ℕ → Fin n → ℝ}
    (hmethod : IsProjectedSubgradientMethodSequence g P proj α x s)
    (t : ℕ) :
    x (t + 1) ∈ P := by
  rw [step_eq hmethod t]
  exact projected_subgradient_step_mem proj (x t) (s t) (α t)

/-- Helper for Theorem 8.11: every iterate of a projected subgradient method sequence stays in the
feasible set `P`. -/
theorem mem
    {g : (Fin n → ℝ) → ℝ}
    {P : Set (Fin n → ℝ)}
    {proj : ProjectionOnto P}
    {α : ℕ → ℝ}
    {x s : ℕ → Fin n → ℝ}
    (hmethod : IsProjectedSubgradientMethodSequence g P proj α x s) :
    ∀ t : ℕ, x t ∈ P
  | 0 => hmethod.zero_mem
  | t + 1 => hmethod.succ_mem t

end IsProjectedSubgradientMethodSequence

/-- Helper for Theorem 8.11: a greatest lower bound of `g '' P` can be approximated from above by
feasible objective values. -/
lemma existsFeasible_lt_add_of_isGLB
    (g : (Fin n → ℝ) → ℝ)
    (P : Set (Fin n → ℝ))
    {gStar eps : ℝ}
    (hfinite : IsGLB (g '' P) gStar)
    (hε : 0 < eps) :
    ∃ y ∈ P, g y < gStar + eps := by
  -- Approximate the GLB by a point of the image set lying in the short interval above it.
  rcases hfinite.exists_between_self_add hε with ⟨z, hz, _, hzlt⟩
  rcases hz with ⟨y, hy, rfl⟩
  exact ⟨y, hy, hzlt⟩

/-- Helper for Theorem 8.11: one projected subgradient step satisfies the textbook squared-distance
recursion against any feasible comparison point `y ∈ P`. -/
lemma projectedSubgradientStep_sqDist_le
    (g : (Fin n → ℝ) → ℝ)
    (P : Set (Fin n → ℝ))
    (proj : ProjectionOnto P)
    (x s y xNext : Fin n → ℝ)
    (α : ℝ)
    (S : NNReal)
    (hy : y ∈ P)
    (hsubgrad : IsSubgradientAtOn g P x s)
    (hstep : xNext = projected_subgradient_step proj x s α)
    (hα : 0 ≤ α)
    (hS : euclideanNorm s ≤ S) :
    euclideanDist xNext y ^ 2 ≤
      euclideanDist x y ^ 2 - 2 * α * (g x - g y) + α ^ 2 * (S : ℝ) ^ 2 := by
  -- First compare the projected point with the unprojected affine step.
  have hproj :
      euclideanDist xNext y ≤ euclideanDist (fun i ↦ x i - α * s i) y := by
    rw [hstep]
    exact proj.dist_le _ _ hy
  have hprojSq :
      euclideanDist xNext y ^ 2 ≤ euclideanDist (fun i ↦ x i - α * s i) y ^ 2 := by
    exact sq_le_sq.mpr (by
      simpa [abs_of_nonneg dist_nonneg] using hproj)
  -- Rewrite the subgradient inequality into the inner-product cross-term bound.
  have hsumGap :
      g x - g y ≤ ∑ i, (x i - y i) * s i := by
    have hgy := hsubgrad y hy
    have hsum :
        ∑ i, s i * (y i - x i) = -∑ i, (x i - y i) * s i := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl ?_
      intro i hi
      ring
    rw [hsum] at hgy
    have hgy' : g x + (-(∑ i, (x i - y i) * s i)) ≤ g y := hgy
    nlinarith
  have hinner :
      inner ℝ (toLp 2 x - toLp 2 y) (toLp 2 s) = ∑ i, (x i - y i) * s i := by
    simpa using realInner_toLp_eq_sum_mul (fun i ↦ x i - y i) s
  have hcross :
      g x - g y ≤ inner ℝ (toLp 2 x - toLp 2 y) (toLp 2 s) := by
    rw [hinner]
    exact hsumGap
  -- Bound the quadratic subgradient term by the uniform norm bound `S`.
  have hnorm :
      ‖toLp 2 s‖ ≤ (S : ℝ) := by
    simpa [euclideanNorm_eq_norm_toLp] using hS
  have hnormSq :
      ‖toLp 2 s‖ ^ 2 ≤ (S : ℝ) ^ 2 := by
    exact sq_le_sq.mpr (by
      simpa [abs_of_nonneg (by positivity : 0 ≤ ‖toLp 2 s‖),
        abs_of_nonneg (show 0 ≤ (S : ℝ) by exact_mod_cast S.2)] using hnorm)
  have hquad :
      α ^ 2 * ‖toLp 2 s‖ ^ 2 ≤ α ^ 2 * (S : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_left hnormSq (sq_nonneg α)
  -- Expand the squared norm of the affine step and insert the two bounds above.
  have hvec :
      toLp 2 (fun i ↦ x i - α * s i) - toLp 2 y =
        (toLp 2 x - toLp 2 y) - α • toLp 2 s := by
    ext i
    simp
    ring
  have hraw :
      euclideanDist (fun i ↦ x i - α * s i) y ^ 2 =
        euclideanDist x y ^ 2 - 2 * α * inner ℝ (toLp 2 x - toLp 2 y) (toLp 2 s) +
          α ^ 2 * ‖toLp 2 s‖ ^ 2 := by
    calc
      euclideanDist (fun i ↦ x i - α * s i) y ^ 2
          = ‖toLp 2 (fun i ↦ x i - α * s i) - toLp 2 y‖ ^ 2 := by
              rw [euclideanDist_eq_dist_toLp, dist_eq_norm]
      _ = ‖(toLp 2 x - toLp 2 y) - α • toLp 2 s‖ ^ 2 := by
            rw [hvec]
      _ = ‖toLp 2 x - toLp 2 y‖ ^ 2 -
            2 * inner ℝ (toLp 2 x - toLp 2 y) (α • toLp 2 s) +
              ‖α • toLp 2 s‖ ^ 2 := by
            rw [norm_sub_sq_real]
      _ = ‖toLp 2 x - toLp 2 y‖ ^ 2 -
            2 * α * inner ℝ (toLp 2 x - toLp 2 y) (toLp 2 s) +
              α ^ 2 * ‖toLp 2 s‖ ^ 2 := by
            rw [inner_smul_right]
            have hsmul :
                ‖α • toLp 2 s‖ ^ 2 = α ^ 2 * ‖toLp 2 s‖ ^ 2 := by
              rw [norm_smul, Real.norm_of_nonneg hα]
              ring
            rw [hsmul]
            ring_nf
      _ = euclideanDist x y ^ 2 -
            2 * α * inner ℝ (toLp 2 x - toLp 2 y) (toLp 2 s) +
              α ^ 2 * ‖toLp 2 s‖ ^ 2 := by
            rw [euclideanDist_eq_dist_toLp, dist_eq_norm]
  have hrawLe :
      euclideanDist (fun i ↦ x i - α * s i) y ^ 2 ≤
        euclideanDist x y ^ 2 - 2 * α * (g x - g y) + α ^ 2 * (S : ℝ) ^ 2 := by
    rw [hraw]
    nlinarith [hcross, hquad]
  exact hprojSq.trans hrawLe

/-- Helper for Theorem 8.11: the one-step squared-distance recursion can be rearranged into a
bound on the current objective gap. -/
lemma projectedSubgradientStep_gap_le
    (g : (Fin n → ℝ) → ℝ)
    (P : Set (Fin n → ℝ))
    (proj : ProjectionOnto P)
    (x s y xNext : Fin n → ℝ)
    (α : ℝ)
    (S : NNReal)
    (hy : y ∈ P)
    (hsubgrad : IsSubgradientAtOn g P x s)
    (hstep : xNext = projected_subgradient_step proj x s α)
    (hα : 0 ≤ α)
    (hS : euclideanNorm s ≤ S) :
    2 * α * (g x - g y) ≤
      euclideanDist x y ^ 2 - euclideanDist xNext y ^ 2 + α ^ 2 * (S : ℝ) ^ 2 := by
  -- Move the squared-distance term to the right-hand side of the one-step recursion.
  have hsq := projectedSubgradientStep_sqDist_le g P proj x s y xNext α S hy hsubgrad hstep hα hS
  nlinarith

/-- Helper for Theorem 8.11: summing the one-step recursion yields a telescoped bound for the
weighted current gaps against a feasible comparison point `y ∈ P`. -/
lemma projectedSubgradient_currentGapSum_le
    (g : (Fin n → ℝ) → ℝ)
    (P : Set (Fin n → ℝ))
    (proj : ProjectionOnto P)
    (α : ℕ → ℝ)
    (x s : ℕ → Fin n → ℝ)
    (S : NNReal)
    (hmethod : IsProjectedSubgradientMethodSequence g P proj α x s)
    (hα_nonneg : ∀ t : ℕ, 0 ≤ α t)
    (hbounded :
      ∀ ⦃y subg : Fin n → ℝ⦄,
        y ∈ P →
          IsSubgradientAtOn g P y subg →
            euclideanNorm subg ≤ S)
    {y : Fin n → ℝ}
    (hy : y ∈ P)
    (k : ℕ) :
    2 * (∑ t ∈ Finset.range (k + 1), α t * (g (x t) - g y)) ≤
      euclideanDist (x 0) y ^ 2 - euclideanDist (x (k + 1)) y ^ 2 +
        (S : ℝ) ^ 2 * ∑ t ∈ Finset.range (k + 1), α t ^ 2 := by
  induction k with
  | zero =>
      -- The base case is exactly the one-step recursion at `t = 0`.
      have hsubgrad : IsSubgradientAtOn g P (x 0) (s 0) := hmethod.isSubgradientAtOn 0
      have hnorm : euclideanNorm (s 0) ≤ S := hbounded (hmethod.mem 0) hsubgrad
      simpa [Finset.sum_range_one, hmethod.step_eq 0, mul_comm, mul_left_comm, mul_assoc] using
        projectedSubgradientStep_gap_le g P proj (x 0) (s 0) y (x 1) (α 0) S hy hsubgrad
          (hmethod.step_eq 0) (hα_nonneg 0) hnorm
  | succ k ih =>
      -- Add the next one-step recursion and let the distance terms telescope.
      have hsubgrad : IsSubgradientAtOn g P (x (k + 1)) (s (k + 1)) :=
        hmethod.isSubgradientAtOn (k + 1)
      have hnorm : euclideanNorm (s (k + 1)) ≤ S :=
        hbounded (hmethod.mem (k + 1)) hsubgrad
      have hstep :
          2 * α (k + 1) * (g (x (k + 1)) - g y) ≤
            euclideanDist (x (k + 1)) y ^ 2 - euclideanDist (x (k + 2)) y ^ 2 +
              α (k + 1) ^ 2 * (S : ℝ) ^ 2 := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using
          projectedSubgradientStep_gap_le g P proj (x (k + 1)) (s (k + 1)) y (x (k + 2))
            (α (k + 1)) S hy hsubgrad (hmethod.step_eq (k + 1)) (hα_nonneg (k + 1)) hnorm
      calc
        2 * (∑ t ∈ Finset.range (k + 2), α t * (g (x t) - g y))
            = 2 * (∑ t ∈ Finset.range (k + 1), α t * (g (x t) - g y)) +
                2 * α (k + 1) * (g (x (k + 1)) - g y) := by
                  rw [Finset.sum_range_succ]
                  ring
        _ ≤ (euclideanDist (x 0) y ^ 2 - euclideanDist (x (k + 1)) y ^ 2 +
              (S : ℝ) ^ 2 * ∑ t ∈ Finset.range (k + 1), α t ^ 2) +
              (euclideanDist (x (k + 1)) y ^ 2 - euclideanDist (x (k + 2)) y ^ 2 +
                α (k + 1) ^ 2 * (S : ℝ) ^ 2) := by
              gcongr
        _ = euclideanDist (x 0) y ^ 2 - euclideanDist (x (k + 2)) y ^ 2 +
              (S : ℝ) ^ 2 * ∑ t ∈ Finset.range (k + 2), α t ^ 2 := by
              conv_lhs => rw [Finset.sum_range_succ]
              conv_rhs => rw [Finset.sum_range_succ, Finset.sum_range_succ]
              ring_nf

/-- Helper for Theorem 8.11: the telescoped current-gap estimate also bounds the weighted gap of
the running best value `g_best^k`. -/
lemma projectedSubgradient_bestValue_mul_gap_le
    (g : (Fin n → ℝ) → ℝ)
    (P : Set (Fin n → ℝ))
    (proj : ProjectionOnto P)
    (α : ℕ → ℝ)
    (x s : ℕ → Fin n → ℝ)
    (S : NNReal)
    (hmethod : IsProjectedSubgradientMethodSequence g P proj α x s)
    (hα_nonneg : ∀ t : ℕ, 0 ≤ α t)
    (hbounded :
      ∀ ⦃y subg : Fin n → ℝ⦄,
        y ∈ P →
          IsSubgradientAtOn g P y subg →
            euclideanNorm subg ≤ S)
    {y : Fin n → ℝ}
    (hy : y ∈ P)
    (k : ℕ) :
    2 * ((Finset.range (k + 1)).sum α) * (subgradient_best_value g x k - g y) ≤
      euclideanDist (x 0) y ^ 2 + (S : ℝ) ^ 2 * ∑ t ∈ Finset.range (k + 1), α t ^ 2 := by
  -- Compare the constant `g_best^k` term-by-term with the current gaps and use the telescoped sum.
  have hbest :
      ∑ t ∈ Finset.range (k + 1), α t * (subgradient_best_value g x k - g y) ≤
        ∑ t ∈ Finset.range (k + 1), α t * (g (x t) - g y) := by
    refine Finset.sum_le_sum ?_
    intro t ht
    have hbestLe : subgradient_best_value g x k ≤ g (x t) :=
      subgradient_best_value_le_of_mem_range g x ht
    exact mul_le_mul_of_nonneg_left (by linarith) (hα_nonneg t)
  have hcurrent :=
    projectedSubgradient_currentGapSum_le g P proj α x s S hmethod hα_nonneg hbounded hy k
  calc
    2 * ((Finset.range (k + 1)).sum α) * (subgradient_best_value g x k - g y)
        = 2 * ∑ t ∈ Finset.range (k + 1), α t * (subgradient_best_value g x k - g y) := by
            rw [mul_assoc, ← Finset.sum_mul]
    _ ≤ 2 * ∑ t ∈ Finset.range (k + 1), α t * (g (x t) - g y) := by
          exact mul_le_mul_of_nonneg_left hbest (by positivity)
    _ ≤ euclideanDist (x 0) y ^ 2 - euclideanDist (x (k + 1)) y ^ 2 +
          (S : ℝ) ^ 2 * ∑ t ∈ Finset.range (k + 1), α t ^ 2 := hcurrent
    _ ≤ euclideanDist (x 0) y ^ 2 + (S : ℝ) ^ 2 * ∑ t ∈ Finset.range (k + 1), α t ^ 2 := by
          nlinarith [sq_nonneg (euclideanDist (x (k + 1)) y)]

/-- Helper for Theorem 8.11: if `α t → 0`, all stepsizes are nonnegative, and the partial sums of
`α` diverge, then the ratio `∑ α_t^2 / ∑ α_t` tends to `0`. -/
lemma partialSquareSumDivPartialSum_tendsto_zero
    (α : ℕ → ℝ)
    (hα_nonneg : ∀ t : ℕ, 0 ≤ α t)
    (hα_tendsto_zero : Filter.Tendsto α Filter.atTop (nhds 0))
    (hα_sum_diverges :
      Filter.Tendsto
        (fun k : ℕ ↦ (Finset.range (k + 1)).sum α)
        Filter.atTop
        Filter.atTop) :
    Filter.Tendsto
      (fun k : ℕ ↦
        ((Finset.range (k + 1)).sum (fun t ↦ α t ^ 2)) /
          ((Finset.range (k + 1)).sum α))
      Filter.atTop
      (nhds 0) := by
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  -- After a finite prefix, every square is bounded by `(ε / 4) * α_t`.
  rcases (Metric.tendsto_atTop.1 hα_tendsto_zero) (ε / 4) (by positivity) with ⟨N0, hN0⟩
  let C : ℝ := (Finset.range N0).sum (fun t ↦ α t ^ 2)
  obtain ⟨N1, hN1⟩ :
      ∃ N1, ∀ n ≥ N1, max 1 (4 * C / ε) ≤ (Finset.range (n + 1)).sum α := by
    simpa [Filter.eventually_atTop, C] using
      (Filter.tendsto_atTop.1 hα_sum_diverges (max 1 (4 * C / ε)))
  refine ⟨max N0 N1, ?_⟩
  intro n hn
  have hn0 : N0 ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hn1 : N1 ≤ n := le_trans (Nat.le_max_right _ _) hn
  have hsmall : ∀ t ≥ N0, α t < ε / 4 := by
    intro t ht
    have ht' := hN0 t ht
    simpa [Real.dist_eq, abs_of_nonneg (hα_nonneg t)] using ht'
  have hsumLower : max 1 (4 * C / ε) ≤ (Finset.range (n + 1)).sum α :=
    hN1 n hn1
  have hsumPos : 0 < (Finset.range (n + 1)).sum α := by
    have hsumPos1 : 1 ≤ (Finset.range (n + 1)).sum α :=
      le_trans (le_max_left _ _) hsumLower
    exact lt_of_lt_of_le zero_lt_one hsumPos1
  have hsumSquaresDecomp :
      (Finset.range (n + 1)).sum (fun t ↦ α t ^ 2) =
        C + ∑ t ∈ Finset.Ico N0 (n + 1), α t ^ 2 := by
    have hN0le : N0 ≤ n + 1 := Nat.le_trans hn0 (Nat.le_succ n)
    dsimp [C]
    rw [Finset.sum_range_add_sum_Ico _ hN0le]
  have hsumDecomp :
      (Finset.range (n + 1)).sum α =
        (Finset.range N0).sum α + ∑ t ∈ Finset.Ico N0 (n + 1), α t := by
    have hN0le : N0 ≤ n + 1 := Nat.le_trans hn0 (Nat.le_succ n)
    rw [Finset.sum_range_add_sum_Ico _ hN0le]
  have htailSq :
      ∑ t ∈ Finset.Ico N0 (n + 1), α t ^ 2 ≤
        (ε / 4) * ∑ t ∈ Finset.Ico N0 (n + 1), α t := by
    calc
      ∑ t ∈ Finset.Ico N0 (n + 1), α t ^ 2
          ≤ ∑ t ∈ Finset.Ico N0 (n + 1), (ε / 4) * α t := by
              refine Finset.sum_le_sum ?_
              intro t ht
              have htN0 : N0 ≤ t := (Finset.mem_Ico.mp ht).1
              have hαle : α t ≤ ε / 4 := (hsmall t htN0).le
              have hαnn : 0 ≤ α t := hα_nonneg t
              nlinarith
      _ = (ε / 4) * ∑ t ∈ Finset.Ico N0 (n + 1), α t := by
            rw [← Finset.mul_sum]
  have htailLeTotal :
      ∑ t ∈ Finset.Ico N0 (n + 1), α t ≤ (Finset.range (n + 1)).sum α := by
    have hprefixNonneg : 0 ≤ (Finset.range N0).sum α := by
      exact Finset.sum_nonneg fun t _ ↦ hα_nonneg t
    rw [hsumDecomp]
    linarith
  have hsumSquaresLe :
      (Finset.range (n + 1)).sum (fun t ↦ α t ^ 2) ≤
        C + (ε / 4) * (Finset.range (n + 1)).sum α := by
    rw [hsumSquaresDecomp]
    nlinarith [htailSq, htailLeTotal]
  have hCle :
      C ≤ (ε / 4) * (Finset.range (n + 1)).sum α := by
    have hLower2 : 4 * C / ε ≤ (Finset.range (n + 1)).sum α :=
      le_trans (le_max_right _ _) hsumLower
    have hScaled := mul_le_mul_of_nonneg_left hLower2 (show 0 ≤ ε / 4 by positivity)
    field_simp [hε.ne'] at hScaled
    nlinarith [hScaled]
  have hratioLe :
      ((Finset.range (n + 1)).sum (fun t ↦ α t ^ 2)) / ((Finset.range (n + 1)).sum α) ≤
        C / ((Finset.range (n + 1)).sum α) + ε / 4 := by
    calc
      ((Finset.range (n + 1)).sum (fun t ↦ α t ^ 2)) / ((Finset.range (n + 1)).sum α)
          ≤ (C + (ε / 4) * (Finset.range (n + 1)).sum α) / ((Finset.range (n + 1)).sum α) := by
              exact div_le_div_of_nonneg_right hsumSquaresLe hsumPos.le
      _ = C / ((Finset.range (n + 1)).sum α) + ε / 4 := by
            field_simp [hsumPos.ne']

  have hCdivLe :
      C / ((Finset.range (n + 1)).sum α) ≤ ε / 4 := by
    exact (div_le_iff₀ hsumPos).2 hCle
  have hratioLt :
      ((Finset.range (n + 1)).sum (fun t ↦ α t ^ 2)) / ((Finset.range (n + 1)).sum α) < ε := by
    calc
      ((Finset.range (n + 1)).sum (fun t ↦ α t ^ 2)) / ((Finset.range (n + 1)).sum α)
          ≤ C / ((Finset.range (n + 1)).sum α) + ε / 4 := hratioLe
      _ ≤ ε / 4 + ε / 4 := by gcongr
      _ < ε := by linarith
  have hratioNonneg :
      0 ≤ ((Finset.range (n + 1)).sum (fun t ↦ α t ^ 2)) / ((Finset.range (n + 1)).sum α) := by
    exact div_nonneg (Finset.sum_nonneg fun t _ ↦ sq_nonneg (α t)) hsumPos.le
  rw [Real.dist_eq]
  simpa [abs_of_nonneg hratioNonneg] using hratioLt

/-- Theorem 8.11 (Poljak [310]). Assume that problem `(8.9)` has finite value `g⋆`, and that the
length of all subgradients of `g` is bounded by a constant `S ∈ ℝ≥0`. If the sequence `(α_t)`
converges to `0` and its partial sums diverge to `+∞`, then the sequence `(g_best^t)` generated by
the subgradient algorithm converges to `g⋆`. -/
theorem projected_subgradient_best_value_tendsto_optimal_value
    (g : (Fin n → ℝ) → ℝ)
    (P : Set (Fin n → ℝ))
    (proj : ProjectionOnto P)
    (α : ℕ → ℝ)
    (x s : ℕ → Fin n → ℝ)
    (gStar : ℝ)
    (S : NNReal)
    (hfinite : IsGLB (g '' P) gStar)
    (hmethod : IsProjectedSubgradientMethodSequence g P proj α x s)
    (hα_nonneg : ∀ t : ℕ, 0 ≤ α t)
    (hbounded :
      ∀ ⦃y subg : Fin n → ℝ⦄,
        y ∈ P →
          IsSubgradientAtOn g P y subg →
            euclideanNorm subg ≤ S)
    (hα_tendsto_zero : Filter.Tendsto α Filter.atTop (nhds 0))
    (hα_sum_diverges :
      Filter.Tendsto
        (fun k : ℕ ↦ (Finset.range (k + 1)).sum α)
        Filter.atTop
        Filter.atTop) :
    Filter.Tendsto
      (fun t : ℕ ↦ subgradient_best_value g x t)
      Filter.atTop
      (nhds gStar) := by
  -- The lower bound `gStar ≤ g_best^t` holds at every stage because every iterate stays feasible.
  have hlower :
      ∀ t : ℕ, gStar ≤ subgradient_best_value g x t := by
    intro t
    rw [subgradient_best_value]
    exact Finset.le_inf' (s := Finset.range (t + 1)) (f := fun k ↦ g (x k)) (by simp)
      (fun k hk ↦ hfinite.1 ⟨x k, hmethod.mem k, rfl⟩)
  have hratio :=
    partialSquareSumDivPartialSum_tendsto_zero α hα_nonneg hα_tendsto_zero hα_sum_diverges
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  -- Choose a feasible comparison point whose objective value is within `ε / 2` of `gStar`.
  rcases existsFeasible_lt_add_of_isGLB g P hfinite (show 0 < ε / 2 by positivity) with
    ⟨y, hy, hylt⟩
  let D0 : ℝ := euclideanDist (x 0) y ^ 2
  let δ : ℝ := ε / (2 * ((S : ℝ) ^ 2 + 1))
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  rcases (Metric.tendsto_atTop.1 hratio) δ hδ with ⟨Nratio, hNratio⟩
  obtain ⟨Nsum, hNsum⟩ :
      ∃ Nsum, ∀ n ≥ Nsum, max 1 (2 * D0 / ε) ≤ (Finset.range (n + 1)).sum α := by
    simpa [Filter.eventually_atTop, D0] using
      (Filter.tendsto_atTop.1 hα_sum_diverges (max 1 (2 * D0 / ε)))
  refine ⟨max Nratio Nsum, ?_⟩
  intro n hn
  have hnratio : Nratio ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hnsum : Nsum ≤ n := le_trans (Nat.le_max_right _ _) hn
  let sumAlpha : ℝ := (Finset.range (n + 1)).sum α
  let sumSquare : ℝ := (Finset.range (n + 1)).sum (fun t ↦ α t ^ 2)
  let ratio : ℝ := sumSquare / sumAlpha
  have hsumLower : max 1 (2 * D0 / ε) ≤ sumAlpha := hNsum n hnsum
  have hsumPos : 0 < sumAlpha := by
    have hsumPos1 : 1 ≤ sumAlpha := le_trans (le_max_left _ _) hsumLower
    exact lt_of_lt_of_le zero_lt_one hsumPos1
  have hratioNonneg : 0 ≤ ratio := by
    dsimp [ratio, sumSquare, sumAlpha]
    exact div_nonneg (Finset.sum_nonneg fun t _ ↦ sq_nonneg (α t)) hsumPos.le
  have hratioLt : ratio < δ := by
    have hratioDist := hNratio n hnratio
    change dist ratio 0 < δ at hratioDist
    rw [Real.dist_eq] at hratioDist
    simpa [abs_of_nonneg hratioNonneg] using hratioDist
  have hmaster :=
    projectedSubgradient_bestValue_mul_gap_le g P proj α x s S hmethod hα_nonneg hbounded hy n
  have hgap :
      subgradient_best_value g x n - g y ≤
        D0 / (2 * sumAlpha) + (S : ℝ) ^ 2 / 2 * ratio := by
    have hdiv :
        subgradient_best_value g x n - g y ≤
          (D0 + (S : ℝ) ^ 2 * sumSquare) / (2 * sumAlpha) := by
      refine (le_div_iff₀ (by positivity : 0 < 2 * sumAlpha)).2 ?_
      simpa [D0, sumSquare, sumAlpha, mul_comm, mul_left_comm, mul_assoc] using hmaster
    calc
      subgradient_best_value g x n - g y
          ≤ (D0 + (S : ℝ) ^ 2 * sumSquare) / (2 * sumAlpha) := hdiv
      _ = D0 / (2 * sumAlpha) + (S : ℝ) ^ 2 / 2 * ratio := by
            dsimp [ratio]
            field_simp [hsumPos.ne']
  have hDtermLe :
      D0 / (2 * sumAlpha) ≤ ε / 4 := by
    have hLower2 : 2 * D0 / ε ≤ sumAlpha := le_trans (le_max_right _ _) hsumLower
    have hScaled := mul_le_mul_of_nonneg_left hLower2 (show 0 ≤ ε / 2 by positivity)
    field_simp [hε.ne'] at hScaled
    have hD0Le : D0 ≤ (ε / 2) * sumAlpha := by
      nlinarith [hScaled]
    have hD0Div : D0 / sumAlpha ≤ ε / 2 := by
      exact (div_le_iff₀ hsumPos).2 hD0Le
    calc
      D0 / (2 * sumAlpha) = (D0 / sumAlpha) / 2 := by
        field_simp [hsumPos.ne']
      _ ≤ (ε / 2) / 2 := by
        exact div_le_div_of_nonneg_right hD0Div (by positivity)
      _ = ε / 4 := by ring
  have hStermLe :
      (S : ℝ) ^ 2 / 2 * ratio ≤ ε / 4 := by
    have hratioLe : ratio ≤ δ := hratioLt.le
    have hmul :
        (S : ℝ) ^ 2 / 2 * ratio ≤ (S : ℝ) ^ 2 / 2 * δ := by
      exact mul_le_mul_of_nonneg_left hratioLe (by positivity)
    have hmul' :
        (S : ℝ) ^ 2 / 2 * δ ≤ ε / 4 := by
      dsimp [δ]
      have hden : 0 < 2 * ((S : ℝ) ^ 2 + 1) := by positivity
      field_simp [hden.ne']
      nlinarith [sq_nonneg (S : ℝ), hε]
    exact hmul.trans hmul'
  have hupper :
      subgradient_best_value g x n < gStar + ε := by
    have hgapLe : subgradient_best_value g x n - g y ≤ ε / 2 := by
      nlinarith [hgap, hDtermLe, hStermLe]
    nlinarith [hgapLe, hylt]
  -- Combine the global lower bound with the eventual upper bound.
  -- This turns the one-sided estimate into a distance bound around `gStar`.
  have hdist :
      dist (subgradient_best_value g x n) gStar < ε := by
    have hnonneg : 0 ≤ subgradient_best_value g x n - gStar := sub_nonneg.mpr (hlower n)
    have hsub : subgradient_best_value g x n - gStar < ε := by
      nlinarith [hupper]
    simpa [Real.dist_eq, abs_of_nonneg hnonneg] using hsub
  exact hdist

end Theorem811
