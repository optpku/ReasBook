module

public import ReasLib.Topology.Sequences
public import Mathlib.Topology.MetricSpace.Basic

public section

open Filter

universe u

variable {X : Type u} [MetricSpace X]

/- Infrastructure I.24a (Closedness of a sequence range after adjoining its at-infinity cluster set) -/
#check (IsClosed.union_range_of_mapClusterPt (X := X) :
  ∀ {Γ : Set X} (hΓ : IsClosed Γ) (x : ℕ → X)
    (hcluster : ∀ y, MapClusterPt y atTop x → y ∈ Γ), IsClosed (Γ ∪ Set.range x))
