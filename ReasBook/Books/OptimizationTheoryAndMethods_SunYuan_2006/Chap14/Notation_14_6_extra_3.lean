/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Lemma_14_6_2

noncomputable section

open scoped CompositeNonsmooth

section

variable {n m : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "ValuePoint" => EuclideanSpace ℝ (Fin m)

-- Domain sampling across the local Section 14.6 files shows that `Lemma_14_6_2` already owns
-- the canonical specialized composite nonsmooth API:
-- * `subdifferential`
-- * `compositeNonsmoothJacobianTranspose`
-- * `compositeNonsmoothChi`
-- * `compositeNonsmoothPsiValueSet`
-- * `compositeNonsmoothPsi`
-- * `compositeNonsmoothDirectionalValueSet`
-- * `compositeNonsmoothDF`
-- This notation item is therefore a bridge/view layer: it keeps only the extra
-- maximal-attainment companions for `(14.6.5)`.

/- Chapter14 Notation 14.6-extra-3: the source quantities `(14.6.4)`-`(14.6.6)` are the
canonical Section 14.6 owners already introduced in `Lemma_14_6_2`. -/

#check
  fun (h : ValuePoint → ℝ) (f : Point → ValuePoint) (x d : Point) ↦
    compositeNonsmoothChi h f x d

#check
  fun (h : ValuePoint → ℝ) (f : Point → ValuePoint) (t : ℝ) (x : Point) ↦
    compositeNonsmoothPsi h f t x

#check
  fun (h : ValuePoint → ℝ) (f : Point → ValuePoint) (x d : Point) ↦
    compositeNonsmoothDF h f x d

#check
  fun (problem : CompositeNonsmoothOptimizationProblem n m) (x d : Point) ↦
    DF[problem](x, d)

/-- If the bounded-step source value set from `(14.6.5)` has greatest element `r`, then the
specialized value `ψ_t(x)` is exactly `r`. -/
theorem compositeNonsmoothPsi_eq_of_isGreatest
    (h : ValuePoint → ℝ) (f : Point → ValuePoint) (t : ℝ) (x : Point) (r : ℝ)
    (hr : IsGreatest (compositeNonsmoothPsiValueSet h f x t) r) :
    compositeNonsmoothPsi h f t x = r := by
  simpa [compositeNonsmoothPsi] using hr.csSup_eq

/-- If the bounded-step source value set from `(14.6.5)` has a greatest element, then the
specialized value `ψ_t(x)` is itself that greatest element. -/
theorem compositeNonsmoothPsi_isGreatest
    (h : ValuePoint → ℝ) (f : Point → ValuePoint) (t : ℝ) (x : Point) (r : ℝ)
    (hr : IsGreatest (compositeNonsmoothPsiValueSet h f x t) r) :
    IsGreatest (compositeNonsmoothPsiValueSet h f x t) (compositeNonsmoothPsi h f t x) := by
  rw [compositeNonsmoothPsi_eq_of_isGreatest h f t x r hr]
  exact hr

#print axioms compositeNonsmoothPsi_eq_of_isGreatest
#print axioms compositeNonsmoothPsi_isGreatest

end
