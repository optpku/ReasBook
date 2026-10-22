/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Filter

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Definition 4.26: `T : D → H` is demiclosed at `u` if every sequence in `D` that converges
weakly to some `x ∈ D` and whose image under `T` converges strongly to `u` satisfies `T x = u`. -/
def DemiclosedAt (D : Set H) (T : D → H) (u : H) : Prop :=
  ∀ ⦃xₙ : ℕ → D⦄ ⦃x : D⦄,
    Tendsto (fun n ↦ toWeakSpace ℝ H (xₙ n : H)) atTop (nhds (toWeakSpace ℝ H (x : H))) →
      Tendsto (fun n ↦ T (xₙ n)) atTop (nhds u) →
      T x = u

/-- A map on a subset of a real Hilbert space is demiclosed if it is demiclosed at every codomain
point. -/
def Demiclosed (D : Set H) (T : D → H) : Prop :=
  ∀ u, DemiclosedAt D T u

/-- Demiclosedness is exactly demiclosedness at each codomain point. -/
theorem demiclosed_iff {D : Set H} {T : D → H} :
    Demiclosed D T ↔ ∀ u, DemiclosedAt D T u := Iff.rfl
