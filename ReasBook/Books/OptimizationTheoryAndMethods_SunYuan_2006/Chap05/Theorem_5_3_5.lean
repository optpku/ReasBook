/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Algorithm_5_1_4
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Assumption_5_3_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Corollary_5_1_6
import Mathlib.Order.Filter.AtTopBot.Basic

noncomputable section

open Filter

section Chapter05Theorem535

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

-- Domain sampling for this refine pass:
-- * primary domain: exact-line-search DFP quasi-Newton runs on the Chapter 5 Euclidean surface;
-- * sampled project owners in the minimal closure:
--   `DfpMethod`,
--   `DfpMethod.IsExactLineSearchOnQuadratic`,
--   `GeneralQuasiNewtonMethod.HasExactLineSearchOnNonnegativeRay`,
--   `HasQuasiNewtonGlobalConvergenceAssumptions`,
--   `bfgsWithWolfePowell_tendsto_to_minimizer`;
-- * best owner abstraction: the source-facing DFP owner `DfpMethod`, together with the
--   canonical exact-line-search owner
--   `A.toGeneralQuasiNewtonMethod.HasExactLineSearchOnNonnegativeRay` and the canonical
--   quasi-Newton termination/tail owner `GeneralQuasiNewtonMethod`;
-- * source-facing minimizer layer: Chapter 5 convergence theorems are organized around
--   `IsMinOn f (quasiNewtonLevelSet f A.x0) xStar`;
-- * primitive source-facing data used here: exact line search, zero stopping tolerance, and the
--   owner-level frozen-tail convention already carried by `GeneralQuasiNewtonMethod`;
-- * derived API here: level-set membership, secant-curvature positivity, and the generated-stage
--   DFP curvature conditions forced by Assumption 5.3.1.

namespace DfpMethod

/-- At every nonterminal DFP stage, the displacement is nonzero because the DFP secant
denominator is primitive data of `DfpMethod`. -/
theorem step_ne_zero
    {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {A : DfpMethod f} {k : ℕ}
    (hk : A.ε < ‖A.g k‖) :
    A (k + 1) - A k ≠ 0 := by
  intro hs
  apply A.secant_denom_ne_zero k hk
  simp [hs]

/-- At every nonterminal DFP stage, the secant vector is nonzero because the same primitive DFP
denominator cannot vanish. -/
theorem secant_ne_zero
    {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {A : DfpMethod f} {k : ℕ}
    (hk : A.ε < ‖A.g k‖) :
    A.g (k + 1) - A.g k ≠ 0 := by
  intro hy
  have hy' : (A.g (k + 1)).ofLp - (A.g k).ofLp = 0 := by
    simpa using congrArg (fun v ↦ v.ofLp) hy
  apply A.secant_denom_ne_zero k hk
  simp [hy']

/-- Exact line search together with zero stopping tolerance keeps every iterate in the canonical
Chapter 5 level set `quasiNewtonLevelSet f A.x0`. The owner-level frozen-tail convention on
`GeneralQuasiNewtonMethod` handles the post-termination tail. -/
theorem x_mem_levelSet
    {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {A : DfpMethod f}
    (hExactLineSearch : A.toGeneralQuasiNewtonMethod.HasExactLineSearchOnNonnegativeRay)
    (hε : A.ε = 0)
    (k : ℕ) :
    A k ∈ quasiNewtonLevelSet f A.x0 := by
  sorry

/-- A current nonterminal DFP stage forces every earlier stage to be nonterminal as well, at the
level of the canonical quasi-Newton owner
`A.toGeneralQuasiNewtonMethod.GeneratedThrough`. -/
theorem toGeneralQuasiNewtonMethod_generatedThrough
    {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {A : DfpMethod f}
    {k : ℕ} (hk : A.ε < ‖A.g k‖) :
    A.toGeneralQuasiNewtonMethod.GeneratedThrough (k + 1) := by
  intro i hi
  let hnotTermK : ¬ A.terminatedAt k := not_le_of_gt hk
  let hnotTermI : ¬ A.terminatedAt i := fun hiTerm ↦
    hnotTermK (A.terminatedAt_mono hiTerm (Nat.le_of_lt_succ hi))
  exact lt_of_not_ge hnotTermI

/-- Every nonterminal exact-line-search DFP stage sits inside the canonical generated-through
owner `A.GeneratedThrough (k + 1)`. -/
theorem generatedThrough
    {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ} {D : Set (EuclideanSpace ℝ (Fin n))}
    {A : DfpMethod f}
    (hExactLineSearch : A.toGeneralQuasiNewtonMethod.HasExactLineSearchOnNonnegativeRay)
    (hε : A.ε = 0)
    {k : ℕ}
    (h_assumption : HasQuasiNewtonGlobalConvergenceAssumptions D f A.x0)
    (hk : A.ε < ‖A.g k‖) :
    A.GeneratedThrough (k + 1) := by
  sorry

/-- Under Chapter05 Assumption 5.3.1, every nonterminal stage of an exact-line-search DFP run has
positive secant curvature. This is derived from exact line search, level-set containment, and the
level-set lower Hessian bound, not stored as primitive run data. -/
theorem secant_curvature_pos
    {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ} {D : Set (EuclideanSpace ℝ (Fin n))}
    {A : DfpMethod f}
    (hExactLineSearch : A.toGeneralQuasiNewtonMethod.HasExactLineSearchOnNonnegativeRay)
    (hε : A.ε = 0)
    {k : ℕ}
    (h_assumption : HasQuasiNewtonGlobalConvergenceAssumptions D f A.x0)
    (hk : A.ε < ‖A.g k‖) :
    0 < dotProduct (A (k + 1) - A k) (A.g (k + 1) - A.g k) := by
  sorry

/-- Under exact line search and Chapter05 Assumption 5.3.1, every nonterminal DFP stage has the
canonical positive-definite inverse-Hessian approximation `A.matrix k`. -/
theorem matrix_posDef
    {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ} {D : Set (EuclideanSpace ℝ (Fin n))}
    {A : DfpMethod f}
    (hExactLineSearch : A.toGeneralQuasiNewtonMethod.HasExactLineSearchOnNonnegativeRay)
    (hε : A.ε = 0)
    {k : ℕ}
    (h_assumption : HasQuasiNewtonGlobalConvergenceAssumptions D f A.x0)
    (hk : A.ε < ‖A.g k‖) :
    (A.matrix k).PosDef :=
  dfpMethod_matrix_posDef A k
    (generatedThrough hExactLineSearch hε h_assumption hk)

/-- At every nonterminal exact-line-search DFP stage, the metric curvature
`yᵀ H_k y = dotProduct y ((A.matrix k).mulVec y)` is positive. -/
theorem metric_curvature_pos
    {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ} {D : Set (EuclideanSpace ℝ (Fin n))}
    {A : DfpMethod f}
    (hExactLineSearch : A.toGeneralQuasiNewtonMethod.HasExactLineSearchOnNonnegativeRay)
    (hε : A.ε = 0)
    {k : ℕ}
    (h_assumption : HasQuasiNewtonGlobalConvergenceAssumptions D f A.x0)
    (hk : A.ε < ‖A.g k‖) :
    0 < dotProduct (A.g (k + 1) - A.g k) ((A.matrix k).mulVec (A.g (k + 1) - A.g k)) := by
  have hPos : (A.matrix k).PosDef :=
    matrix_posDef hExactLineSearch hε h_assumption hk
  have hy : A.g (k + 1) - A.g k ≠ 0 := A.secant_ne_zero hk
  have hy' : (A.g (k + 1) - A.g k).ofLp ≠ 0 := by
    intro hzero
    apply hy
    ext i
    exact congrArg (fun v ↦ v i) hzero
  simpa using hPos.dotProduct_mulVec_pos hy'

/-- Every nonterminal exact-line-search DFP stage carries the exact line-search minimizer, the
canonical positive-definite inverse-Hessian approximation, the source secant-curvature condition
derived from Chapter05 Assumption 5.3.1, the induced positive metric curvature, and the DFP
inverse update. -/
theorem exactLineSearch_stepSpec
    {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ} {D : Set (EuclideanSpace ℝ (Fin n))}
    {A : DfpMethod f}
    (hExactLineSearch : A.toGeneralQuasiNewtonMethod.HasExactLineSearchOnNonnegativeRay)
    (hε : A.ε = 0)
    {k : ℕ}
    (h_assumption : HasQuasiNewtonGlobalConvergenceAssumptions D f A.x0)
    (hk : A.ε < ‖A.g k‖) :
    IsMinOn (lineSearchObjective f (A k) (A.d k)) (Set.Ici 0) (A.α k) ∧
      (A.matrix k).PosDef ∧
      satisfiesCurvatureCondition (A (k + 1) - A k) (A.g (k + 1) - A.g k) ∧
      0 < dotProduct (A.g (k + 1) - A.g k) ((A.matrix k).mulVec (A.g (k + 1) - A.g k)) ∧
      A.matrix (k + 1) =
        dfpInverseUpdate (A.matrix k) (A (k + 1) - A k) (A.g (k + 1) - A.g k) := by
  have hPos : (A.matrix k).PosDef :=
    matrix_posDef hExactLineSearch hε h_assumption hk
  refine ⟨hExactLineSearch.isMinOn k, hPos,
    satisfiesCurvatureCondition_iff_dotProduct_pos.mpr
      (secant_curvature_pos hExactLineSearch hε h_assumption hk),
    metric_curvature_pos hExactLineSearch hε h_assumption hk,
    A.matrix_update_eq hk⟩

end DfpMethod

/-- Chapter05 Theorem 5.3.5: suppose `f` satisfies Chapter05 Assumption 5.3.1. Then, for a
source-facing DFP method `A` with exact line search on the nonnegative ray and zero stopping
tolerance, the iterate sequence converges to the given minimizer `xStar` of `f` on the Chapter 5
level set `quasiNewtonLevelSet f A.x0`. The exact-line-search property is carried by the
canonical owner `A.toGeneralQuasiNewtonMethod.HasExactLineSearchOnNonnegativeRay`, and the
post-termination frozen-tail convention is already primitive owner data on
`GeneralQuasiNewtonMethod`, so no extra theorem-local bridge hypothesis is needed. The
secant-curvature facts needed by the DFP positivity machinery are still derived from the Chapter 5
assumption package rather than stored as extra run data. -/
theorem dfpWithExactLineSearch_tendsto_to_minimizer
    {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (D : Set (EuclideanSpace ℝ (Fin n)))
    (A : DfpMethod f)
    (hExactLineSearch : A.toGeneralQuasiNewtonMethod.HasExactLineSearchOnNonnegativeRay)
    (hε : A.ε = 0)
    (h_assumption : HasQuasiNewtonGlobalConvergenceAssumptions D f A.x0)
    (xStar : EuclideanSpace ℝ (Fin n))
    (hxStar : IsMinOn f (quasiNewtonLevelSet f A.x0) xStar) :
    Tendsto A atTop (nhds xStar) := by
  sorry

/-- If the comparison point `xStar` is already a global minimizer of `f`, then it is in
particular a minimizer on the Chapter 5 level set `quasiNewtonLevelSet f A.x0`, so the
exact-line-search DFP iterate sequence `A` converges to `xStar` as well. -/
theorem dfpWithExactLineSearch_tendsto_to_globalMinimizer
    {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (D : Set (EuclideanSpace ℝ (Fin n)))
    (A : DfpMethod f)
    (hExactLineSearch : A.toGeneralQuasiNewtonMethod.HasExactLineSearchOnNonnegativeRay)
    (hε : A.ε = 0)
    (h_assumption : HasQuasiNewtonGlobalConvergenceAssumptions D f A.x0)
    (xStar : EuclideanSpace ℝ (Fin n)) (hxStar : IsMinOn f Set.univ xStar) :
    Tendsto A atTop (nhds xStar) := by
  exact dfpWithExactLineSearch_tendsto_to_minimizer
    f D A hExactLineSearch hε h_assumption xStar <|
    hxStar.on_subset (Set.subset_univ _)

end Chapter05Theorem535
