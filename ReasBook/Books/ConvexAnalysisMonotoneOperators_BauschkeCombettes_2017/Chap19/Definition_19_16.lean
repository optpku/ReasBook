/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Proposition_13_33

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Set
open scoped InnerProductSpace

universe u v

namespace ERealFunction

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- Definition 19.16: the Lagrangian associated with
`F : H × K → ]-∞,+∞]` is the extended-real-valued function
`(x, v) ↦ inf_y (F(x, y) - ⟪y, v⟫)`, expressed through the canonical first-projection
infimal postcomposition owner. -/
def lagrangian (F : H × K → Set.Ioi (⊥ : EReal)) (x : H) (v : K) : EReal :=
  (Prod.fst ▷ fun p : H × K ↦ (F p : EReal) - (⟪p.2, v⟫_ℝ : EReal)) x

notation3:max "ℒ[" F "]" => lagrangian F

/-- Evaluating the Lagrangian gives the canonical fiberwise `iInf` formula
`inf_y (F(x, y) - ⟪y, v⟫)`. -/
@[simp] theorem lagrangian_apply (F : H × K → Set.Ioi (⊥ : EReal)) (x : H) (v : K) :
    ℒ[F] x v = ⨅ y : K, (F (x, y) : EReal) - (⟪y, v⟫_ℝ : EReal) := by
  simpa [lagrangian] using
    (infimalPostcomposition_fst_apply
      (fun p : H × K ↦ (F p : EReal) - (⟪p.2, v⟫_ℝ : EReal)) x)

-- Proof sketch: specialize mathlib's `isSaddlePointOn_iff` to the whole spaces `H` and `K`, then
-- rewrite the resulting `iSup`/`iInf` expressions as the supremum and infimum of the two fibers of
-- the Lagrangian.
/-- A pair `(x, v)` is a saddle point of the Lagrangian exactly when the value `ℒ[F] x v` is
simultaneously the supremum of the `v`-fiber at `x` and the infimum of the `x`-fiber at `v`. -/
theorem lagrangian_isSaddlePointOn_iff
    (F : H × K → Set.Ioi (⊥ : EReal)) (x : H) (v : K) :
    IsSaddlePointOn (univ : Set H) (univ : Set K) (ℒ[F]) x v ↔
      sSup (Set.range fun w : K ↦ ℒ[F] x w) = ℒ[F] x v ∧
        sInf (Set.range fun z : H ↦ ℒ[F] z v) = ℒ[F] x v := by
  have hsaddle :
      IsSaddlePointOn (univ : Set H) (univ : Set K) (ℒ[F]) x v ↔
        (⨆ w ∈ (univ : Set K), ℒ[F] x w) = ℒ[F] x v ∧
          (⨅ z ∈ (univ : Set H), ℒ[F] z v) = ℒ[F] x v :=
    isSaddlePointOn_iff (by simp) (by simp)
  simpa [sSup_range, sInf_range] using
    hsaddle

end ERealFunction
