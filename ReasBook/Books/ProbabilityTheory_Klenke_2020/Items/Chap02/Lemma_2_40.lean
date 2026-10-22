/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Set MeasureTheory

universe u

/-- The lattice `ℤ^d`, realized as integer-valued functions on `Fin d`. -/
abbrev LatticePoint (d : ℕ) := Fin d → ℤ

variable {Ω : Type u} [MeasurableSpace Ω] {d : ℕ}

/-- The open cluster of a site `x` for a percolation connectivity event family `connectionEvent`,
viewed as the random set of lattice points connected to `x`. -/
def openCluster
    (connectionEvent : LatticePoint d → LatticePoint d → Set Ω)
    (x : LatticePoint d) : Ω → Set (LatticePoint d) :=
  fun ω ↦ {y | ω ∈ connectionEvent x y}

/-- The size of the open cluster at `x`, represented as the extended cardinality of the random set
of sites connected to `x`. -/
noncomputable def openClusterSize
    (connectionEvent : LatticePoint d → LatticePoint d → Set Ω)
    (x : LatticePoint d) : Ω → ℕ∞ :=
  fun ω ↦ (openCluster connectionEvent x ω).encard

/-- The open-cluster size is the extended cardinality of the open cluster. -/
theorem openClusterSize_def {Ω : Type u} {d : ℕ}
    (connectionEvent : LatticePoint d → LatticePoint d → Set Ω)
    (x : LatticePoint d) :
    openClusterSize connectionEvent x = fun ω ↦ (openCluster connectionEvent x ω).encard := rfl

-- Proof sketch: for a measurable event, the `{0,1}`-valued indicator is measurable by the
-- standard measurability criterion for indicator functions of measurable sets.
/-- Lemma 2.40: For sites `x, y ∈ ℤ^d`, if the connectivity event `{ω | ω ∈ connectionEvent x y}`
is measurable, then its indicator function is a random variable. -/
theorem measurable_connection_indicator
    (connectionEvent : LatticePoint d → LatticePoint d → Set Ω)
    (hmeas : ∀ x y : LatticePoint d, MeasurableSet (connectionEvent x y))
    (x y : LatticePoint d) :
    Measurable ((connectionEvent x y).indicator (fun _ : Ω ↦ (1 : ℕ))) := by
  -- The connectivity indicator is the indicator of a constant measurable function on a measurable
  -- event.
  exact Measurable.indicator measurable_const (hmeas x y)

/-- Helper for Lemma 2.40: membership in the random open cluster is exactly the underlying
connectivity event. -/
lemma openCluster_mem_iff
    {Ω : Type u} {d : ℕ}
    (connectionEvent : LatticePoint d → LatticePoint d → Set Ω)
    (x y : LatticePoint d) (ω : Ω) :
    y ∈ openCluster connectionEvent x ω ↔ ω ∈ connectionEvent x y := by
  -- Unfolding `openCluster` turns set membership into the original connectivity event.
  rfl

/-- Helper for Lemma 2.40: if every connectivity event is measurable, then the random open cluster
is measurable as a `Set`-valued map. -/
lemma measurable_openCluster
    (connectionEvent : LatticePoint d → LatticePoint d → Set Ω)
    (hmeas : ∀ x y : LatticePoint d, MeasurableSet (connectionEvent x y))
    (x : LatticePoint d) :
    Measurable (openCluster connectionEvent x) := by
  -- A `Set`-valued map is measurable once each coordinate membership predicate is measurable.
  refine measurable_set_iff.2 ?_
  intro y
  -- Rewrite the membership event back to the given measurable connectivity event.
  have hmem : MeasurableSet {ω | y ∈ openCluster connectionEvent x ω} := by
    simpa [openCluster_mem_iff] using hmeas x y
  exact measurableSet_setOf.1 hmem

-- Proof sketch: view `openClusterSize connectionEvent x` as the composition of the random set
-- `ω ↦ {y | ω ∈ connectionEvent x y}` with `Set.encard`, and use countability of `ℤ^d` together
-- with the coordinatewise measurability of the connectivity events.
/-- If every connectivity event is measurable, then the cluster size `# C^p(x)`, interpreted as
the extended cardinality of the random cluster, is a random variable. -/
theorem measurable_openClusterSize
    (connectionEvent : LatticePoint d → LatticePoint d → Set Ω)
    (hmeas : ∀ x y : LatticePoint d, MeasurableSet (connectionEvent x y))
    (x : LatticePoint d) :
    Measurable (openClusterSize connectionEvent x) := by
  -- The cluster size is `Set.encard` applied to the measurable random set `openCluster`.
  simpa [openClusterSize_def] using
    measurable_encard.comp (measurable_openCluster connectionEvent hmeas x)
