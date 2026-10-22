/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap01.Construction_1_5_5
import AlgebraicTopology_May_1999.Chap01.Lemma_1_5_4
import AlgebraicTopology_May_1999.Chap01.Definition_1_5_8

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open FundamentalGroup
open scoped unitInterval

/-- Helper for Lemma 1.5.9: the lift-index map on `π₁(S¹, 1)` depends only on the homotopy
class of the chosen loop. -/
-- Proof sketch: use `FundamentalGroup.fromPath_eq_iff_homotopic` to identify the two loop
-- classes, then apply `circleFundamentalGroupLiftIndex` to that equality.
theorem circleFundamentalGroupLiftIndex_eq_of_homotopic_loops
    (γ₀ γ₁ : Path (1 : Circle) 1) (h : γ₀.Homotopic γ₁) :
    circleFundamentalGroupLiftIndex (FundamentalGroup.fromPath ⟦γ₀⟧) =
      circleFundamentalGroupLiftIndex (FundamentalGroup.fromPath ⟦γ₁⟧) := by
  apply congrArg circleFundamentalGroupLiftIndex
  exact (FundamentalGroupoid.fromPath_eq_iff_homotopic γ₀ γ₁).2 h

/-- Lemma 1.5.9: the lift-index map `j` is well defined on loop classes in `π₁(S¹, 1)`, and on
the standard loop `f_n` it returns the integer `n`. -/
-- Proof sketch: identify `j([f_n])` with the endpoint of the canonical lift of `f_n` via
-- `circleFundamentalGroupLiftIndex_spec`, then evaluate that lift using `standardLoopLift_apply`
-- at `1` to obtain the endpoint `n`.
theorem circleFundamentalGroupLiftIndex_standardLoop (n : ℤ) :
    circleFundamentalGroupLiftIndex (standardLoopClass n) = n := by
  have hlift :
      standardLoopLift n =
        real_fourierChar_isCoveringMap.liftPath (standardLoop n).toContinuousMap 0
          (circle_path_start_eq_fourierChar_zero (standardLoop n)) := by
    apply (real_fourierChar_isCoveringMap.eq_liftPath_iff'
      (circle_path_start_eq_fourierChar_zero (standardLoop n))).2
    constructor
    · ext s
      exact congrArg Subtype.val (standardLoop_factors_through_fourierChar n s).symm
    · simp [standardLoopLift]
  have hlift_apply :
      real_fourierChar_isCoveringMap.liftPath (standardLoop n).toContinuousMap 0
          (circle_path_start_eq_fourierChar_zero (standardLoop n)) 1 =
        standardLoopLift n 1 := by
    simpa using DFunLike.congr_fun hlift.symm 1
  have hspec :
      ((circleFundamentalGroupLiftIndex (standardLoopClass n) : ℤ) : ℝ) =
        standardLoopLift n 1 := by
    simpa [standardLoopClass] using
      (circleFundamentalGroupLiftIndex_spec (standardLoop n)).trans hlift_apply
  have hendpoint : standardLoopLift n 1 = (n : ℝ) := by
    rw [standardLoopLift_apply n 1]
    norm_num
  exact Int.cast_injective <| hspec.trans hendpoint
