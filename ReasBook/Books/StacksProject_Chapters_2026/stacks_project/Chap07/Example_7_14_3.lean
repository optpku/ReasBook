module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Definition_7_14_1

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {J J' : GrothendieckTopology C}

/- Domain-style sampling for Example 7.14.3:
- primary domain: Grothendieck topologies, continuous functors, and morphisms of sites;
- sampled owner API:
  `Presheaf.IsSheaf.of_le`,
  `RepresentablyFlat.id`,
  `IsMorphismOfSites`;
- source/core/bridge triage:
  `source-facing`: topology comparison for `J' ≤ J` on the fixed category `C`;
  `core/canonical`: `Functor.IsContinuous` and `IsMorphismOfSites`;
  `bridge/view`: the identity-functor continuity instance below and the thin theorem deriving the
  site-morphism owner.

Primitive data here are only the continuity proof for `𝟭 C` under `J' ≤ J`. The
representable-flat part is already canonical for the identity functor, and the
morphism-of-sites structure is derived API from the chapter owner constructor. -/

-- Proof sketch: if `ℱ` is a `J`-sheaf and `J' ≤ J`, then the sheaf condition for `J'` follows
-- immediately from `Presheaf.IsSheaf.of_le hle`. Since precomposition with the identity functor
-- is definitionally the same presheaf, this is exactly continuity of `𝟭 C`.
/-- The identity functor is continuous `(C, J') → (C, J)` whenever `J' ≤ J`, i.e. whenever every
`J'`-covering sieve is also `J`-covering. -/
instance id_isContinuous_of_le (hle : J' ≤ J) :
    Functor.IsContinuous (𝟭 C) J' J where
  op_comp_isSheaf_of_types G := by
    rw [← isSheaf_iff_isSheaf_of_type]
    simpa using (Presheaf.IsSheaf.of_le hle G.property)

-- Proof sketch: combine `id_isContinuous_of_le hle` with `RepresentablyFlat.id`, then apply the
-- canonical owner instance for a continuous representably flat functor.
/-- Example 7.14.3: if `J' ≤ J` are Grothendieck topologies on `C`, so every `J'`-covering is a
`J`-covering, then the identity functor on `C` defines a morphism of sites
`\mathcal C_J \to \mathcal C_{J'}`. -/
theorem id_isMorphismOfSites_of_le (hle : J' ≤ J) :
    IsMorphismOfSites J' J (𝟭 C) := by
  let _ : Functor.IsContinuous (𝟭 C) J' J := id_isContinuous_of_le hle
  exact isMorphismOfSites_of_isContinuous_representablyFlat J' J (𝟭 C)

end CategoryTheory
