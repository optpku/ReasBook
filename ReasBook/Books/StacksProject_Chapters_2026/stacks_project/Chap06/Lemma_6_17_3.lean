module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Topology.Sheaves.Sheafify
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopCat
open TopologicalSpace

noncomputable section

universe u

section

variable {X : TopCat.{u}} (ℱ : X.Presheaf (Type u)) (𝒢 : X.Sheaf (Type u))
local notation "J" => Opens.grothendieckTopology X

/- Domain-style sampling for Lemma 6.17.3:
- primary domain: sheafification of set-valued presheaves on a topological space;
- sampled owner API:
  `CategoryTheory.sheafificationAdjunction`,
  `CategoryTheory.toSheafify`,
  `CategoryTheory.sheafifyLift`,
  `CategoryTheory.toSheafify_sheafifyLift`,
  `CategoryTheory.sheafifyLift_unique`;
- best owner abstraction: the sheafification adjunction
  `sheafificationAdjunction J (Type u)`, with `toSheafify J` as the unit and
  `sheafifyLift J` as the derived universal morphism API;
- primitive data: the presheaf `ℱ`, the sheaf `𝒢`, and a morphism `φ : ℱ ⟶ 𝒢.presheaf`;
- derived API: the factorization of `φ` through `toSheafify J ℱ` and its uniqueness.

Source/core/bridge triage:
- `source-facing`: the Stacks-style unique factorization of maps `ℱ ⟶ 𝒢.presheaf` through
  the sheafification unit;
- `core/canonical`: the sheafification adjunction `sheafificationAdjunction J (Type u)`;
- `bridge/view`: the specialized lift `sheafifyLift J φ 𝒢.property` and its uniqueness theorem
  on underlying presheaves. -/

/- Lemma 6.17.3: for a set-valued presheaf `ℱ` and a sheaf `𝒢` on `X`, every morphism
`φ : ℱ ⟶ 𝒢.presheaf` factors uniquely through the canonical sheafification unit.
The canonical owner surface is the adjunction hom-equivalence together with the specialized
lift API below. -/
recall CategoryTheory.sheafificationAdjunction
recall CategoryTheory.sheafifyLift
recall CategoryTheory.toSheafify_sheafifyLift
recall CategoryTheory.sheafifyLift_unique

variable {ℱ 𝒢}

/- The owner equivalence for this topological-space specialization. -/
#check (sheafificationAdjunction J (Type u)).homEquiv ℱ 𝒢

/- Source-facing specialization: the universal factorization is the canonical lift
`sheafifyLift J φ 𝒢.property`. -/
#check (fun φ : ℱ ⟶ 𝒢.presheaf ↦ sheafifyLift J φ 𝒢.property :
  (ℱ ⟶ 𝒢.presheaf) → (sheafify J ℱ ⟶ 𝒢.presheaf))

/- The factorization equation is exactly `toSheafify_sheafifyLift`. -/
#check (fun φ : ℱ ⟶ 𝒢.presheaf ↦ toSheafify_sheafifyLift J φ 𝒢.property :
  ∀ φ : ℱ ⟶ 𝒢.presheaf, toSheafify J ℱ ≫ sheafifyLift J φ 𝒢.property = φ)

/- Uniqueness is exactly `sheafifyLift_unique`. -/
#check (fun φ : ℱ ⟶ 𝒢.presheaf ↦ fun γ : sheafify J ℱ ⟶ 𝒢.presheaf ↦
  sheafifyLift_unique J φ 𝒢.property γ)

end
