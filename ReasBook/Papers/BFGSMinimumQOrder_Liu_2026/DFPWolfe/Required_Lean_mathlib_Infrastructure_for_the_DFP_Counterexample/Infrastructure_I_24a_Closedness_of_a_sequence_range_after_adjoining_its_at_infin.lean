/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/Required_Lean_mathlib_Infrastructure_for_the_DFP_Counterexample/Infrastructure_I_24a_Closedness_of_a_sequence_range_after_adjoining_its_at_infin.lean
-/

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
