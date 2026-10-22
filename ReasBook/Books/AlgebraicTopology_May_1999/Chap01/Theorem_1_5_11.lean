/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap01.Lemma_1_5_4
import AlgebraicTopology_May_1999.Chap01.Lemma_1_5_9
import AlgebraicTopology_May_1999.Chap01.Lemma_1_5_10

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open FundamentalGroup

/-- The standard loop class `standardLoopClass 1` generates `π₁(S¹, 1)`. -/
theorem standardLoopClass_one_zpowers_eq_top :
    Subgroup.zpowers (standardLoopClass 1 : FundamentalGroup Circle 1) = ⊤ := by
  refine (Subgroup.eq_top_iff' _).2 fun γ ↦ ?_
  rw [Subgroup.mem_zpowers_iff]
  refine ⟨circleFundamentalGroupLiftIndex γ, ?_⟩
  apply circleFundamentalGroupLiftIndex_injective
  rw [standardLoopClass_one_zpow, circleFundamentalGroupLiftIndex_standardLoop]

instance : Infinite (FundamentalGroup Circle 1) := by
  have hstandardLoopClass : Function.Injective standardLoopClass := by
    intro m n h
    have hindex := congrArg circleFundamentalGroupLiftIndex h
    change
      circleFundamentalGroupLiftIndex (standardLoopClass m) =
        circleFundamentalGroupLiftIndex (standardLoopClass n) at hindex
    rwa [circleFundamentalGroupLiftIndex_standardLoop, circleFundamentalGroupLiftIndex_standardLoop]
      at hindex
  exact Infinite.of_injective standardLoopClass hstandardLoopClass

/- Theorem 1.5.11: the canonical infinite-cyclic owner `intEquivOfZPowersEqTop` specializes the
generator theorem above to identify `π₁(S¹, 1)` with `Multiplicative ℤ`. -/
#check
  (intEquivOfZPowersEqTop (standardLoopClass 1) standardLoopClass_one_zpowers_eq_top :
    Multiplicative ℤ ≃* FundamentalGroup Circle (1 : Circle))

/- Evaluation of the canonical equivalence is already the owner theorem
`intEquivOfZPowersEqTop_apply`; combined with `standardLoopClass_one_zpow`, it sends
`Multiplicative.ofAdd n` to `standardLoopClass n`. -/
#check
  (intEquivOfZPowersEqTop_apply (standardLoopClass 1) standardLoopClass_one_zpowers_eq_top :
    ∀ a : Multiplicative ℤ,
      intEquivOfZPowersEqTop (standardLoopClass 1) standardLoopClass_one_zpowers_eq_top a =
        standardLoopClass 1 ^ Multiplicative.toAdd a)

#print standardLoopClass_one_zpowers_eq_top
