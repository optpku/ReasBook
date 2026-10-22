/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_13
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Definition_6_38
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap20.Proposition_20_27

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise Set

universe u

namespace Function

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A single-valued operator is hemicontinuous on `C` when every scalar slice along segments
starting at points of `C` satisfies Rockafellar's right-limit condition. -/
def IsHemicontinuousOn (A : H → H) (C : Set H) : Prop :=
  ∀ x y : C, ∀ z : H,
    Filter.Tendsto (fun α : ℝ ↦ ⟪z, A ((1 - α) • (x : H) + α • (y : H))⟫_ℝ)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds ⟪z, A x⟫_ℝ)

-- Proof sketch: rewrite the segment parameterization
-- `(1 - α) • x + α • y = x + α • (y - x)` and then apply the global hemicontinuity hypothesis
-- with direction `y - x`.
/-- Global hemicontinuity implies Rockafellar hemicontinuity on every subset. -/
theorem IsHemicontinuous.isHemicontinuousOn {A : H → H} (hA : A.IsHemicontinuous) (C : Set H) :
    A.IsHemicontinuousOn C := sorry

section

variable [CompleteSpace H]

-- Proof sketch: use the maximal-monotonicity criterion from Definition 20.20. A graph point
-- monotonically related to `gra (ofFunction C A + N[C])` first lies over `C` by maximal
-- monotonicity of `N[C]` (Example 20.26); then apply the monotonicity hypothesis on `C` and let
-- the segment parameter tend to `0` via hemicontinuity to show that the residual vector belongs to
-- `N[C]`, hence the point already lies in the graph of the sum.
/-- Proposition 20.49: if `C` is a nonempty closed convex subset of a real Hilbert space and `A`
is monotone and hemicontinuous on `C` in Rockafellar's sense, then the sum of the restricted
singleton-valued operator `ofFunction C (fun x ↦ A x)` with the normal cone operator `N[C]` is
maximally monotone. -/
theorem ofFunction_add_normalCone_isMaximallyMonotone_of_monotoneOn_hemicontinuousOn
    {C : Set H} (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (A : H → H) (hA_mono : (SetValuedOperator.ofFunction C (fun x : C ↦ A x)).IsMonotone)
    (hA_hemi : A.IsHemicontinuousOn C) :
    Maximal SetValuedOperator.IsMonotone
      (SetValuedOperator.ofFunction C (fun x : C ↦ A x) + N[C]) := sorry

end

end Function
