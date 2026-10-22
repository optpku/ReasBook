/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap03.Lemma_3_5_feasible_set
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_23

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} {m : ℕ}

/- Lemma 3.5 is `source-facing` in the chapter's finite-family inequality-constrained
optimization API. The relevant owner abstractions are:
1. mathlib's `IsMinOn` for minimizers on a set;
2. Chapter 3's `coordinatewiseMax` for the maximum of finitely many real quantities.
The primitive source-facing data are therefore only:
1. the feasible set cut out by the inequality family `g`;
2. the `(m + 1)`-tuple consisting of the objective gap and the constraint values.
The residual objective itself is derived from that tuple through the owner `coordinatewiseMax`,
so the file no longer keeps a parallel ad hoc finite-maximum encoding. -/
recall inequality_feasible_set
recall mem_inequality_feasible_set
recall coordinatewiseMax

variable {g : Fin m → E → ℝ}

/-- The coordinate vector whose last entry is the objective gap `f x - fbar` and whose first `m`
entries are the inequality values `g i x`. -/
def optimality_residual_coordinates
    (f : E → ℝ) (fbar : ℝ) (g : Fin m → E → ℝ) (x : E) : Fin (m + 1) → ℝ :=
  Fin.snoc (fun i ↦ g i x) (f x - fbar)

/-- The residual objective obtained by taking the coordinatewise maximum of the objective gap
`f x - fbar` and all inequality values `g i x`. -/
noncomputable def optimality_residual (f : E → ℝ) (fbar : ℝ) (g : Fin m → E → ℝ) : E → ℝ :=
  fun x ↦ coordinatewiseMax (optimality_residual_coordinates f fbar g x)

variable {f : E → ℝ} {fbar : ℝ}

/-- On the first `m` coordinates, `optimality_residual_coordinates` records the constraint
values. -/
@[simp] theorem optimality_residual_coordinates_castSucc
    (x : E) (i : Fin m) :
    optimality_residual_coordinates f fbar g x i.castSucc = g i x := by
  simp [optimality_residual_coordinates]

/-- On the last coordinate, `optimality_residual_coordinates` records the objective gap. -/
@[simp] theorem optimality_residual_coordinates_last
    (x : E) :
    optimality_residual_coordinates f fbar g x (Fin.last m) = f x - fbar := by
  simp [optimality_residual_coordinates]

-- Proof sketch: unfold `optimality_residual`; the fold starts at `f x - fbar`, and every later
-- coordinate of `optimality_residual_coordinates` is bounded above by its supremum, so the
-- objective-gap entry is bounded above by the resulting coordinatewise maximum.
/-- The objective gap `f x - fbar` is bounded above by the residual objective. -/
theorem objective_gap_le_optimality_residual
    (x : E) :
    f x - fbar ≤ optimality_residual f fbar g x := by
  simpa [optimality_residual, coordinatewiseMax] using
    le_ciSup (Finite.bddAbove_range (optimality_residual_coordinates f fbar g x)) (Fin.last m)

-- Proof sketch: each coordinate of `optimality_residual_coordinates` is bounded above by its
-- supremum, so every constraint entry is bounded above by the resulting coordinatewise maximum.
/-- Every individual constraint value is bounded above by the residual objective. -/
theorem constraint_le_optimality_residual
    (x : E) (i : Fin m) :
    g i x ≤ optimality_residual f fbar g x := by
  simpa [optimality_residual, coordinatewiseMax] using
    le_ciSup (Finite.bddAbove_range (optimality_residual_coordinates f fbar g x)) i.castSucc

/-- Helper for Lemma 3.5: the residual objective vanishes at every feasible point whose objective
value is exactly `fbar`. -/
theorem optimality_residual_eq_zero_of_feasible_of_eq_fbar
    (x : E) (hxfeas : x ∈ inequality_feasible_set g) (hfx : f x = fbar) :
    optimality_residual f fbar g x = 0 := by
  rw [mem_inequality_feasible_set] at hxfeas
  refine le_antisymm ?_ ?_
  · -- Bound each coordinate of the finite maximum above by `0`.
    rw [optimality_residual, coordinatewiseMax]
    refine ciSup_le (fun i ↦ ?_)
    refine Fin.lastCases ?_ (fun i ↦ ?_) i
    · simp [hfx, optimality_residual_coordinates]
    · simpa [optimality_residual_coordinates] using hxfeas i
  · -- The objective-gap coordinate already gives the reverse inequality.
    simpa [hfx] using objective_gap_le_optimality_residual (f := f) (fbar := fbar) (g := g) x

/-- Helper for Lemma 3.5: if `fbar` is the least feasible objective value, then the residual
objective is nonnegative everywhere. -/
theorem zero_le_optimality_residual_of_isLeast
    (hfbar : IsLeast (f '' inequality_feasible_set g) fbar) (x : E) :
    0 ≤ optimality_residual f fbar g x := by
  by_cases hxfeas : x ∈ inequality_feasible_set g
  · -- On feasible points, the objective-gap coordinate is already nonnegative.
    have hfbar_le : fbar ≤ f x := hfbar.2 ⟨x, hxfeas, rfl⟩
    calc
      0 ≤ f x - fbar := sub_nonneg.mpr hfbar_le
      _ ≤ optimality_residual f fbar g x :=
        objective_gap_le_optimality_residual (f := f) (fbar := fbar) (g := g) x
  · -- On infeasible points, a violated constraint gives a positive residual coordinate.
    rw [mem_inequality_feasible_set] at hxfeas
    push Not at hxfeas
    rcases hxfeas with ⟨i, hi⟩
    calc
      0 ≤ g i x := le_of_lt hi
      _ ≤ optimality_residual f fbar g x :=
        constraint_le_optimality_residual (f := f) (fbar := fbar) (g := g) x i

/-- Helper for Lemma 3.5: a nonpositive residual value forces both feasibility and the objective
bound `f x ≤ fbar`. -/
theorem feasible_and_obj_le_of_optimality_residual_le_zero
    (x : E) (hx : optimality_residual f fbar g x ≤ 0) :
    x ∈ inequality_feasible_set g ∧ f x ≤ fbar := by
  refine ⟨?_, ?_⟩
  · -- Every constraint is bounded above by the nonpositive residual.
    rw [mem_inequality_feasible_set]
    intro i
    exact le_trans (constraint_le_optimality_residual (f := f) (fbar := fbar) (g := g) x i) hx
  · -- The objective-gap coordinate gives the claimed upper bound on `f x`.
    exact sub_nonpos.mp <|
      le_trans (objective_gap_le_optimality_residual (f := f) (fbar := fbar) (g := g) x) hx

-- Proof sketch: let `S = inequality_feasible_set g`. The hypothesis `hfbar` says precisely that
-- `fbar` is the least feasible objective value. If `x ∈ S` and `x` minimizes `f` on `S`, then
-- `f x = fbar`, so every entry in the finite max defining
-- `optimality_residual f fbar g x` is at most `0`, while the objective-gap term is exactly `0`;
-- hence `x` globally minimizes the residual. Conversely, if `x` globally minimizes the residual,
-- compare against a feasible point attaining `fbar` from `hfbar` to deduce the minimum residual
-- value is `0`; then `objective_gap_le_optimality_residual` and
-- `constraint_le_optimality_residual` force `f x ≤ fbar` and all constraints `g i x ≤ 0`. Using
-- the lower-bound part of `hfbar`, conclude `f x = fbar`, so `x` is a feasible minimizer of `f`.
/-- Lemma 3.5: if `fbar` is the minimum value of `f` on the inequality-feasible set determined by
`g`, then the optimal set of the constrained problem coincides with the global minimizer set of
the residual objective `x ↦ max {f x - fbar, g 0 x, …, g (m - 1) x}`. -/
theorem inequality_constrained_optimal_set_eq_global_minimizers_optimality_residual
    (hfbar : IsLeast (f '' inequality_feasible_set g) fbar) :
    {x | x ∈ inequality_feasible_set g ∧ IsMinOn f (inequality_feasible_set g) x} =
      {x | IsMinOn (optimality_residual f fbar g) Set.univ x} := by
  -- Compare both sets pointwise and use the residual value `0` as the common bridge.
  ext x
  constructor
  · intro hx
    change IsMinOn (optimality_residual f fbar g) Set.univ x
    rcases hx with ⟨hxfeas, hxmin⟩
    rcases hfbar.1 with ⟨xbar, hxbarfeas, hxbarval⟩
    rw [isMinOn_iff] at hxmin
    rw [isMinOn_univ_iff]
    -- The feasible minimizer must achieve the least feasible value `fbar`.
    have hfx_le : f x ≤ fbar := by
      simpa [hxbarval] using hxmin xbar hxbarfeas
    have hfbar_le : fbar ≤ f x := hfbar.2 ⟨x, hxfeas, rfl⟩
    have hfx : f x = fbar := le_antisymm hfx_le hfbar_le
    -- Normalize the residual at `x` to `0`, then compare with the global nonnegativity bound.
    have hxzero :
        optimality_residual f fbar g x = 0 :=
      optimality_residual_eq_zero_of_feasible_of_eq_fbar
        (f := f) (fbar := fbar) (g := g) x hxfeas hfx
    intro y
    calc
      optimality_residual f fbar g x = 0 := hxzero
      _ ≤ optimality_residual f fbar g y :=
        zero_le_optimality_residual_of_isLeast (f := f) (fbar := fbar) (g := g) hfbar y
  · intro hx
    change x ∈ inequality_feasible_set g ∧ IsMinOn f (inequality_feasible_set g) x
    rcases hfbar.1 with ⟨xbar, hxbarfeas, hxbarval⟩
    change IsMinOn (optimality_residual f fbar g) Set.univ x at hx
    rw [isMinOn_univ_iff] at hx
    -- Compare the residual minimizer against a feasible point that attains `fbar`.
    have hxle_zero : optimality_residual f fbar g x ≤ 0 := by
      calc
        optimality_residual f fbar g x ≤ optimality_residual f fbar g xbar := hx xbar
        _ = 0 :=
          optimality_residual_eq_zero_of_feasible_of_eq_fbar
            (f := f) (fbar := fbar) (g := g) xbar hxbarfeas hxbarval
    -- A nonpositive residual value recovers the original feasibility and objective bound.
    rcases feasible_and_obj_le_of_optimality_residual_le_zero
        (f := f) (fbar := fbar) (g := g) x hxle_zero with ⟨hxfeas, hfx_le⟩
    refine ⟨hxfeas, ?_⟩
    rw [isMinOn_iff]
    intro y hy
    -- Feasible comparison points have value at least `fbar`, so `x` is optimal on the feasible set.
    exact le_trans hfx_le (hfbar.2 ⟨y, hy, rfl⟩)

/-- Under the optimal-value hypothesis `hfbar`, minimizing `f` on the inequality-feasible set is
equivalent to globally minimizing the residual objective. -/
theorem isMinOn_optimality_residual_univ_iff
    (hfbar : IsLeast (f '' inequality_feasible_set g) fbar) (x : E) :
    (x ∈ inequality_feasible_set g ∧ IsMinOn f (inequality_feasible_set g) x) ↔
      IsMinOn (optimality_residual f fbar g) Set.univ x := by
  simpa using congrArg (fun s : Set E ↦ x ∈ s)
    (inequality_constrained_optimal_set_eq_global_minimizers_optimality_residual hfbar)

end
