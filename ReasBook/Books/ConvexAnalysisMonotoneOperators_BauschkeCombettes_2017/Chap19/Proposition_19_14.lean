/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_31
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_3
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_2
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Definition_13_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Proposition_16_60
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap19.Definition_19_11

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u v

namespace ERealFunction

section ParametricDuality

variable {H : Type u} {K : Type v}

section Basic

variable [NormedAddCommGroup K] [InnerProductSpace ℝ K]

-- Proof sketch: Proposition 19.12 identifies `perturbationDualObjective F` with the
-- Fenchel conjugate
-- `(Prod.snd ▷ F)∗`. Fermat's rule rewrites the argmin set of that conjugate as the zero set of
-- its subdifferential, and the Fenchel--Young/subdifferential correspondence for the conjugate
-- turns that zero condition into membership in `∂ ((Prod.snd ▷ F)∗∗) (0)`.
/-- Proposition 19.14 (1): the dual solution set `U = Argmin (perturbationDualObjective F)`
equals the subdifferential of the biconjugate of the value function at the origin. -/
theorem argmin_perturbationDualObjective_eq_subdifferential_biconjugate_valueFunction_zero
    (F : H × K → Set.Ioi (⊥ : EReal)) (hproper : IsProper ((Prod.snd ▷ F)∗)) :
    Argmin (perturbationDualObjective F) = (∂ ((Prod.snd ▷ F)∗∗)) 0 :=
  sorry

-- Proof sketch: Proposition 16.4 gives lower semicontinuity at every subdifferentiability point.
/-- Subdifferentiability of the value function at the origin forces lower semicontinuity there. -/
theorem lowerSemicontinuousAt_valueFunction_zero_of_subdifferentiableAt
    (F : H × K → Set.Ioi (⊥ : EReal))
    (hsub : SubdifferentiableAt (Prod.snd ▷ F) (0 : K)) :
    LowerSemicontinuousAt (Prod.snd ▷ F) 0 :=
  sorry

-- Proof sketch: Proposition 16.5 identifies `ϑ(0)` with `ϑ**(0)` at a subdifferentiability
-- point, and the biconjugate of an extended-real-valued function cannot take the value `⊤`
-- there.
/-- Subdifferentiability of the value function at the origin excludes the value `⊤` there. -/
theorem valueFunction_zero_ne_top_of_subdifferentiableAt
    (F : H × K → Set.Ioi (⊥ : EReal))
    (hsub : SubdifferentiableAt (Prod.snd ▷ F) (0 : K)) :
    (Prod.snd ▷ F) 0 ≠ ⊤ :=
  sorry

-- Proof sketch: Proposition 16.5 identifies `ϑ(0)` with `ϑ**(0)` at a subdifferentiability
-- point, and that biconjugate value cannot equal `⊥`.
/-- Subdifferentiability of the value function at the origin excludes the value `⊥` there. -/
theorem valueFunction_zero_ne_bot_of_subdifferentiableAt
    (F : H × K → Set.Ioi (⊥ : EReal))
    (hsub : SubdifferentiableAt (Prod.snd ▷ F) (0 : K)) :
    (Prod.snd ▷ F) 0 ≠ ⊥ :=
  sorry

end Basic

section Complete

variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

-- Proof sketch: clause (1) identifies the dual solution set with `∂ϑ**(0)`, and Proposition
-- 16.5 transfers subdifferentiability of `ϑ` at `0` to subdifferentiability of `ϑ**` there.
/-- Subdifferentiability of the value function at the origin yields a dual minimizer. -/
theorem argmin_perturbationDualObjective_nonempty_of_subdifferentiableAt_valueFunction_zero
    (F : H × K → Set.Ioi (⊥ : EReal)) (hproper : IsProper ((Prod.snd ▷ F)∗))
    (hsub : SubdifferentiableAt (Prod.snd ▷ F) (0 : K)) :
    (Argmin (perturbationDualObjective F)).Nonempty :=
  sorry

-- Proof sketch: lower semicontinuity and membership of `0` in the effective domain give
-- `ϑ(0) = ϑ**(0)` by Proposition 13.44. Clause (1) identifies the dual solution set with
-- `∂ϑ**(0)`, and `ϑ** ≤ ϑ` upgrades a dual minimizer to subdifferentiability of `ϑ` at `0`.
/-- Lower semicontinuity, finiteness, and dual attainment at the origin imply
subdifferentiability of the value function there. -/
theorem
    subdifferentiableAt_valueFunction_zero_of_lscAt_of_finite_of_dualArgmin_nonempty
    (F : H × K → Set.Ioi (⊥ : EReal)) (hconv : IsConvex (Prod.snd ▷ F))
    (hproper : IsProper ((Prod.snd ▷ F)∗))
    (hlsc : LowerSemicontinuousAt (Prod.snd ▷ F) 0)
    (hzero : 0 ∈ effectiveDom (Prod.snd ▷ F))
    (hdual : (Argmin (perturbationDualObjective F)).Nonempty) :
    SubdifferentiableAt (Prod.snd ▷ F) (0 : K) :=
  sorry

-- Proof sketch: under the right-hand side of clause (2), Proposition 13.44 gives
-- `(Prod.snd ▷ F) 0 = (Prod.snd ▷ F)∗∗ 0` from the effective-domain hypothesis. Combining this
-- with clause (1) and the inequality `(Prod.snd ▷ F)∗∗ ≤ Prod.snd ▷ F` upgrades the dual-solution
-- set from `∂(ϑ**)(0)` to `∂ϑ(0)`.
/-- Under the lower-semicontinuity, finiteness, and dual-attainment hypotheses at the origin, the
dual solution set equals the subdifferential of the value function there. -/
theorem
    argmin_perturbationDualObjective_eq_subdifferential_valueFunction_zero
    (F : H × K → Set.Ioi (⊥ : EReal)) (hconv : IsConvex (Prod.snd ▷ F))
    (hproper : IsProper ((Prod.snd ▷ F)∗))
    (hlsc : LowerSemicontinuousAt (Prod.snd ▷ F) 0)
    (hzero : 0 ∈ effectiveDom (Prod.snd ▷ F))
    (hdual : (Argmin (perturbationDualObjective F)).Nonempty) :
    Argmin (perturbationDualObjective F) = (∂ (Prod.snd ▷ F)) 0 :=
  sorry

-- Proof sketch: Proposition 19.13 gives `(Prod.snd ▷ F) 0 = - inf perturbationDualObjective`
-- from lower semicontinuity and the effective-domain hypothesis at the origin. The primal
-- infimum is exactly `(Prod.snd ▷ F) 0` by Definition 19.11, so the primal and dual optimal
-- values agree up to sign.
/-- Under the lower-semicontinuity, finiteness, and dual-attainment hypotheses at the origin, the
primal infimum equals the negative dual infimum. -/
theorem
    perturbationPrimalObjective_inf_eq_neg_perturbationDualObjective_inf_of_lscAt_and_finite
    (F : H × K → Set.Ioi (⊥ : EReal)) (hconv : IsConvex (Prod.snd ▷ F))
    (hlsc : LowerSemicontinuousAt (Prod.snd ▷ F) 0)
    (hzero : 0 ∈ effectiveDom (Prod.snd ▷ F)) :
    sInf (Set.range (perturbationPrimalObjective F)) =
      -sInf (Set.range (perturbationDualObjective F)) :=
  sorry

end Complete

end ParametricDuality

end ERealFunction
