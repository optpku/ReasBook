/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped Topology

universe u

variable {X : Type u} [TopologicalSpace X]

/-- Text 1.0.46: A point `x` is a sequential cluster point of a sequence `u` if some subsequence of
`u` converges to `x`. -/
def IsSequentialClusterPt (u : ℕ → X) (x : X) : Prop :=
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 x)

/-- `IsSequentialClusterPt u x` means that some strictly monotone subsequence of `u` converges to
`x`. -/
theorem isSequentialClusterPt_iff_exists_subseq_tendsto {u : ℕ → X} {x : X} :
    IsSequentialClusterPt u x ↔
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 x) :=
  Iff.rfl

/-- A sequential cluster point is a cluster point in the canonical filter-based sense. -/
theorem IsSequentialClusterPt.mapClusterPt {u : ℕ → X} {x : X}
    (hx : IsSequentialClusterPt u x) :
    MapClusterPt x atTop u := by
  rcases hx with ⟨φ, hφ, hφt⟩
  have hsubcluster : MapClusterPt x atTop (u ∘ φ) := hφt.mapClusterPt
  simpa [Function.comp] using hsubcluster.of_comp hφ.tendsto_atTop

/-- A sequential cluster point is witnessed by a strictly monotone subsequence converging to the
given point. -/
-- Proof sketch: unfold `IsSequentialClusterPt`; the required subsequence is exactly the witness in
-- the definition.
theorem IsSequentialClusterPt.exists_subseq_tendsto {u : ℕ → X} {x : X}
    (hx : IsSequentialClusterPt u x) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 x) :=
  isSequentialClusterPt_iff_exists_subseq_tendsto.mp hx
