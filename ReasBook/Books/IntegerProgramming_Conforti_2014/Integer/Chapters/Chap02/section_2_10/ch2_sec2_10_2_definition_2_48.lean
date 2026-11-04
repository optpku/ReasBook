/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_10.ch2_sec2_10_2_definition_2_48.Flow
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_10.ch2_sec2_10_2_definition_2_48.Model

public section

/-!
Fixed-charge multicommodity network design model.

The reusable owner is `FixedChargeMulticommodityNetworkDesign`, with constructor companion
`FixedChargeMulticommodityNetworkDesign.ofNetworkData`, feasible region
`FixedChargeMulticommodityNetworkDesign.feasibleSet`, objective
`FixedChargeMulticommodityNetworkDesign.objectiveValue`, and attained-value set
`FixedChargeMulticommodityNetworkDesign.objectiveValues`.
-/

/- Definition 2.48 [Fixed-charge multicommodity network design problem]: the directed-network
mixed-integer model with binary arc-opening variables, commodity flow-balance constraints,
shared arc capacities, and fixed-charge objective is formalized by the declarations below. -/

#check FixedChargeMulticommodityNetworkDesign
#check FixedChargeMulticommodityNetworkDesign.ofNetworkData
#check FixedChargeMulticommodityNetworkDesign.feasibleSet
#check FixedChargeMulticommodityNetworkDesign.mem_feasibleSet_iff
#check FixedChargeMulticommodityNetworkDesign.objectiveValue
#check FixedChargeMulticommodityNetworkDesign.objectiveValue_def
#check FixedChargeMulticommodityNetworkDesign.objectiveValues

namespace FixedChargeMulticommodityNetworkDesign

/-- Definition 2.48 (fixed-charge multicommodity network design problem): for a problem instance
`P`, membership of `r` in `P.objectiveValues` is equivalent to the existence of arc-opening
variables `x` and commodity flows `y` satisfying the source flow-balance equations, shared
capacity inequalities, nonnegativity constraints on `y`, binary constraints on `x`, and
`P.objectiveValue (x, y) = r`. -/
theorem mem_objectiveValues_iff
    {N : Type u} {A : Type v} {K : Type w}
    [Fintype A] [Fintype K]
    {P : FixedChargeMulticommodityNetworkDesign N A K}
    {r : ℝ} :
    r ∈ P.objectiveValues ↔
      ∃ x : A → ℝ, ∃ y : K → A → ℝ,
        (x, y) ∈ P.feasibleSet ∧ P.objectiveValue (x, y) = r := by
  constructor
  · intro hr
    rcases mem_objectiveValues_iff_exists_feasible P r |>.mp hr with ⟨xy, hxy, hobj⟩
    exact ⟨xy.1, xy.2, hxy, hobj⟩
  · rintro ⟨x, y, hxy, hobj⟩
    exact mem_objectiveValues_iff_exists_feasible P r |>.mpr ⟨(x, y), hxy, hobj⟩

end FixedChargeMulticommodityNetworkDesign
