/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.SimpleGraph.Coloring.VertexColoring
public import Mathlib.Data.Set.Defs

public section

open scoped BigOperators

namespace SimpleGraph
namespace NodeColoring

universe u v

variable {V : Type u} {C : Type v} [Fintype V] [Fintype C]

/-- The node-color formulation objective is the sum of the color-usage variables. -/
def objective
    (y : C → ℤ) :
    ℤ :=
  ∑ c, y c

/-- Unfolding equation for `objective`. -/
theorem objective_def
    (y : C → ℤ) :
    objective y = ∑ c, y c := by
  -- Unfolding the objective exposes exactly the defining finite sum.
  rfl

/-- A node-color formulation solution is feasible when adjacent vertices do not share a color,
every color indicator dominates the vertex-color indicators, each vertex receives exactly one
color, and all `x` and `y` variables are binary. -/
def feasible
    (G : SimpleGraph V)
    (x : V → C → ℤ)
    (y : C → ℤ) :
    Prop :=
  (∀ u v : V, G.Adj u v → ∀ c : C, x u c + x v c ≤ 1) ∧
    (∀ vtx : V, ∀ c : C, x vtx c ≤ y c) ∧
    (∀ vtx : V, ∑ c, x vtx c = 1) ∧
    (∀ vtx : V, ∀ c : C, x vtx c = 0 ∨ x vtx c = 1) ∧
      ∀ c : C, y c = 0 ∨ y c = 1

/-- Membership in `feasible G x y` is exactly the conjunction of the adjacency, linking,
assignment, and binary constraints of the node-color formulation. -/
theorem feasible_iff
    {G : SimpleGraph V}
    {x : V → C → ℤ}
    {y : C → ℤ} :
    feasible G x y ↔
      (∀ u v : V, G.Adj u v → ∀ c : C, x u c + x v c ≤ 1) ∧
        (∀ vtx : V, ∀ c : C, x vtx c ≤ y c) ∧
        (∀ vtx : V, ∑ c, x vtx c = 1) ∧
        (∀ vtx : V, ∀ c : C, x vtx c = 0 ∨ x vtx c = 1) ∧
          ∀ c : C, y c = 0 ∨ y c = 1 := by
  -- The right-hand side is the conjunction used to define feasibility.
  rfl

/-- The objective values attained by feasible node-color formulations on `G` with color type
`C`. -/
def objectiveValues
    (G : SimpleGraph V) :
    Set ℤ :=
  {r | ∃ x : V → C → ℤ, ∃ y : C → ℤ, feasible G x y ∧ objective y = r}

/-- Membership in `objectiveValues G` means that some feasible node-color variables attain the
value `r`. -/
theorem mem_objectiveValues_iff
    {G : SimpleGraph V}
    {r : ℤ} :
    r ∈ objectiveValues (C := C) G ↔
      ∃ x : V → C → ℤ, ∃ y : C → ℤ, feasible G x y ∧ objective y = r := by
  -- Set-builder membership unfolds to the witnesses in the definition.
  rfl

/-- Under the source adequacy hypothesis `Fintype.card C ≥ ENat.toNat G.chromaticNumber`,
membership in `objectiveValues (C := C) G` is exactly the existence of feasible node-color
variables attaining the value `r`. This keeps the reusable owner `objectiveValues` general while
recording the textbook side condition for Definition 2.55 (2). -/
theorem mem_objectiveValues_iff_of_card_ge_chromaticNumber
    {G : SimpleGraph V}
    {r : ℤ}
    (h_card_ge_chromaticNumber : Fintype.card C ≥ ENat.toNat G.chromaticNumber) :
    r ∈ objectiveValues (C := C) G ↔
      ∃ x : V → C → ℤ, ∃ y : C → ℤ, feasible G x y ∧ objective y = r := by
  -- The cardinality hypothesis records source adequacy; membership itself uses the general API.
  exact mem_objectiveValues_iff

/-- The indicator variables extracted from a graph coloring by recording whether vertex `v` uses
color `c`. -/
noncomputable def vertexColorIndicator
    {G : SimpleGraph V}
    (κ : G.Coloring C) :
    V → C → ℤ :=
  -- An explicit classical decision keeps the noncomputable definition proof-free.
  fun vtx c ↦ @ite ℤ (κ vtx = c) (Classical.propDecidable _) 1 0

/-- The color-usage variables extracted from a graph coloring by recording whether some vertex
uses the color `c`. -/
noncomputable def usedColorIndicator
    {G : SimpleGraph V}
    (κ : G.Coloring C) :
    C → ℤ :=
  -- Usage is the proof-free characteristic function of the inhabited color class.
  fun c ↦ @ite ℤ (∃ vtx : V, κ vtx = c) (Classical.propDecidable _) 1 0

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_definition_2_55/NodeColoring.lean

Every graph coloring determines feasible node-color formulation variables via
`vertexColorIndicator` and `usedColorIndicator`. -/
theorem feasible_ofColoring
    {G : SimpleGraph V}
    (κ : G.Coloring C) :
    feasible G (vertexColorIndicator κ) (usedColorIndicator κ) := by
  classical
  -- Expose the five constraints and verify them from properness and the two indicators.
  rw [feasible_iff]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro u v huv c
    by_cases huc : κ u = c
    · have hvc : κ v ≠ c := by
        intro hvc
        exact κ.valid huv (huc.trans hvc.symm)
      -- Properness makes the second adjacent indicator vanish.
      simp [vertexColorIndicator, huc, hvc]
    · -- If the first indicator vanishes, the other is automatically at most one.
      by_cases hvc : κ v = c
      · simp [vertexColorIndicator, huc, hvc]
      · simp [vertexColorIndicator, huc, hvc]
  · intro vtx c
    by_cases hvc : κ vtx = c
    · have hused : ∃ w : V, κ w = c := ⟨vtx, hvc⟩
      -- The vertex itself witnesses that its selected color is marked as used.
      simp [vertexColorIndicator, usedColorIndicator, hvc, hused]
    · -- An unselected color contributes zero at this vertex.
      by_cases hused : ∃ w : V, κ w = c
      · simp [vertexColorIndicator, usedColorIndicator, hvc, hused]
      · simp [vertexColorIndicator, usedColorIndicator, hvc, hused]
  · intro vtx
    -- Isolate the unique unit summand indexed by the vertex's selected color.
    rw [Finset.sum_eq_single (κ vtx)]
    · simp [vertexColorIndicator]
    · intro c _ hc
      simp [vertexColorIndicator, hc.symm]
    · simp
  · intro vtx c
    by_cases hvc : κ vtx = c
    · right
      simp [vertexColorIndicator, hvc]
    · left
      simp [vertexColorIndicator, hvc]
  · intro c
    by_cases hused : ∃ vtx : V, κ vtx = c
    · right
      simp [usedColorIndicator, hused]
    · left
      simp [usedColorIndicator, hused]

end NodeColoring
end SimpleGraph

end
