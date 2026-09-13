/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.MetricSpace.Basic

/-!
# Tail-dense sequence extraction

This module records strictly increasing subsequence extraction from a
tail-dense sequence in a metric space.
-/

public section

open Filter Topology

universe u v

/-- If a sequence in a metric space visits every neighborhood strictly after every
index, then each point is the limit of a strictly increasing subsequence. -/
theorem exists_strictMono_subseq_tendsto
    {X : Type u} [MetricSpace X] (x : ℕ → X)
    (h_tail : ∀ b : X, ∀ U ∈ 𝓝 b, ∀ N : ℕ, ∃ n : ℕ, N < n ∧ x n ∈ U)
    (a : X) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a) := by
  -- Turn the strict tail-visit hypothesis into the cluster-point condition.
  apply MapClusterPt.tendsto_subseq
  rw [mapClusterPt_iff_frequently]
  intro U hU
  rw [frequently_atTop']
  exact h_tail a U hU
