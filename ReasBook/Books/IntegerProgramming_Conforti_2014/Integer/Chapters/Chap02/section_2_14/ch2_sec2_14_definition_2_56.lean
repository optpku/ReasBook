/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_definition_2_9.Optimization

public section

namespace CombinatorialAuction

variable {N n : ℕ}

/-- The bids whose bundle contains object `i`. -/
def bidsForObject
    (bundles : Fin n → Finset (Fin N))
    (i : Fin N) :
    Finset (Fin n) :=
  Finset.univ.filter (fun j ↦ i ∈ bundles j)

/-- Membership in `bidsForObject bundles i` means exactly that bid `j` contains object `i`. -/
theorem mem_bidsForObject_iff
    {bundles : Fin n → Finset (Fin N)}
    {i : Fin N}
    {j : Fin n} :
    j ∈ bidsForObject bundles i ↔ i ∈ bundles j := by
  -- Unfold the filtered universal set and retain its incidence predicate.
  simp [bidsForObject]

/--
Definition 2.56 (set packing formulation of combinatorial auctions): the feasible accepted-bid
vectors are exactly the binary vectors `x` for which each object `i` belongs to at most one
accepted bundle. -/
def feasibleSet
    (bundles : Fin n → Finset (Fin N)) :
    Set (Fin n → ℤ) :=
  SetFamilyOptimization.packingFeasibleSet (bidsForObject bundles)

/-- The combinatorial-auction feasible set is exactly the generic set-packing feasible set for
the translated family `bidsForObject bundles`. -/
theorem feasibleSet_eq_packingFeasibleSet
    (bundles : Fin n → Finset (Fin N)) :
    feasibleSet bundles =
      SetFamilyOptimization.packingFeasibleSet (bidsForObject bundles) := by
  -- The auction feasible set is defined by this generic packing construction.
  rfl

/-- Membership in `feasibleSet bundles` is exactly the binary condition together with the packing
inequalities `∑ j in bidsForObject bundles i, x j ≤ 1` for each object `i`. -/
theorem mem_feasibleSet_iff
    {bundles : Fin n → Finset (Fin N)}
    {x : Fin n → ℤ} :
    x ∈ feasibleSet bundles ↔
      (∀ j, x j = 0 ∨ x j = 1) ∧
        (∀ i, (bidsForObject bundles i).sum x ≤ 1) := by
  -- Transport the generic packing characterization through the feasible-set alias.
  exact SetFamilyOptimization.mem_packingFeasibleSet_iff

/-- The attained objective values of the combinatorial-auction winner determination problem with
bid values `values`. -/
def objectiveValues
    (bundles : Fin n → Finset (Fin N))
    (values : Fin n → ℝ) :
    Set ℝ :=
  SetFamilyOptimization.packingObjectiveValues (bidsForObject bundles) values

/-- The combinatorial-auction attained-value set is exactly the generic set-packing attained-value
set for `bidsForObject bundles` and `values`. -/
theorem objectiveValues_eq_packingObjectiveValues
    (bundles : Fin n → Finset (Fin N))
    (values : Fin n → ℝ) :
    objectiveValues bundles values =
      SetFamilyOptimization.packingObjectiveValues (bidsForObject bundles) values := by
  -- The attained-value set is defined by the generic packing construction.
  rfl

/--
remote integer-programming sorry cleanup Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_definition_2_56.lean

Membership in `objectiveValues bundles values` means that some feasible accepted-bid vector
attains the value under the generic objective `SetFamilyOptimization.objective values`. -/
theorem mem_objectiveValues_iff
    {bundles : Fin n → Finset (Fin N)}
    {values : Fin n → ℝ}
    {r : ℝ} :
    r ∈ objectiveValues bundles values ↔
      ∃ x : Fin n → ℤ,
        x ∈ feasibleSet bundles ∧ SetFamilyOptimization.objective values x = r := by
  -- Transport attained-value membership through both auction aliases.
  exact SetFamilyOptimization.mem_packingObjectiveValues_iff

end CombinatorialAuction

/-!
Set-packing formulation of combinatorial auctions.

This item is formalized by the reusable owner namespace `CombinatorialAuction`, with source-facing
bundle translation `CombinatorialAuction.bidsForObject`, feasible set
`CombinatorialAuction.feasibleSet`, and attained-value set
`CombinatorialAuction.objectiveValues`. The linear objective is the generic
`SetFamilyOptimization.objective`.
-/

/- The textbook winner-determination problem for bid bundles `bundles` and bid values `values` is
formalized by `CombinatorialAuction.feasibleSet bundles`, the generic linear objective
`SetFamilyOptimization.objective values`, and
`CombinatorialAuction.objectiveValues bundles values`. -/
#check CombinatorialAuction.bidsForObject
#check CombinatorialAuction.mem_bidsForObject_iff
#check CombinatorialAuction.feasibleSet
#check CombinatorialAuction.feasibleSet_eq_packingFeasibleSet
#check CombinatorialAuction.mem_feasibleSet_iff
#check SetFamilyOptimization.objective
#check CombinatorialAuction.objectiveValues
#check CombinatorialAuction.objectiveValues_eq_packingObjectiveValues
#check CombinatorialAuction.mem_objectiveValues_iff
#print axioms CombinatorialAuction.mem_objectiveValues_iff

end
