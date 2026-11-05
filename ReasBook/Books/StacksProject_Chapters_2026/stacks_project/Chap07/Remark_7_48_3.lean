module

public import Mathlib.CategoryTheory.Sites.Coverage
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Definition_7_8_2

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace Coverage

open SemiRepresentableFamily.Over

/-- Helper for Remark 7.48.3: a fixed-target cover family packaged with the universe parameters
used by this file's site API. -/
abbrev CoverFamily (X : C) := SemiRepresentableFamily.Over.{max u v} X

/- Domain-style sampling for Remark 7.48.3:
- primary domain: sites via `Coverage`, `Precoverage`, and `toGrothendieck`;
- sampled owner API:
  `Precoverage.toGrothendieck_le_iff_le_toPrecoverage`,
  `Precoverage.toGrothendieck_mono`,
  `Coverage.toGrothendieck_toPrecoverage`,
  `SemiRepresentableFamily.Over.IsCovering`,
  `Presieve.exists_eq_ofArrows`;
- source/core/bridge triage:
  `source-facing`: this remark-level invariance statement for tautological enlargements;
  `core/canonical`: `Precoverage.toGrothendieck`;
  `bridge/view`: `SemiRepresentableFamily.Over.toPresieve`,
  `toSieve_eq_of_tautologicallyEquivalent`,
  `Presieve.exists_eq_ofArrows`.

Primitive data are the inclusion `K.toPrecoverage ≤ L` and the fact that every `L`-covering
family is tautologically equivalent to a `K`-covering family with the same target. The equality
of Grothendieck topologies is derived API.
-/

-- Proof sketch: `hK` gives one inequality by monotonicity. For the reverse inequality, every
-- `L`-cover is tautologically equivalent to some `K`-cover, hence generates the same sieve as that
-- `K`-cover; therefore it already belongs to `K.toGrothendieck.toPrecoverage`.
/-- Remark 7.48.3: if `L` contains the original covering families of the site `K` and every
`L`-covering family is tautologically equivalent to a `K`-covering family with the same target,
then `L` defines the same Grothendieck topology as `K`. -/
theorem toGrothendieck_eq_of_tautological_enlargement
    {K : Coverage C} {L : Precoverage C}
    (hK : K.toPrecoverage ≤ L)
    (hL : ∀ ⦃X : C⦄ (𝒱 : CoverFamily X)
      (_ : IsCovering L 𝒱),
      ∃ 𝒰 : CoverFamily X,
        IsCovering K.toPrecoverage 𝒰 ∧ TautologicallyEquivalent 𝒰 𝒱) :
    L.toGrothendieck = K.toGrothendieck := by
  apply le_antisymm
  · rw [Precoverage.toGrothendieck_le_iff_le_toPrecoverage]
    intro X R hR
    rw [GrothendieckTopology.mem_toPrecoverage_iff]
    rcases R.exists_eq_ofArrows with ⟨ι, Y, f, rfl⟩
    let 𝒱 : CoverFamily X := ofArrows Y f
    have h𝒱 : IsCovering L 𝒱 := by
      simpa [𝒱, IsCovering] using hR
    rcases hL 𝒱 h𝒱 with ⟨𝒰, h𝒰, h𝒰𝒱⟩
    change 𝒱.toSieve ∈ K.toGrothendieck X
    rw [← toSieve_eq_of_tautologicallyEquivalent h𝒰𝒱,
      ← Coverage.toGrothendieck_toPrecoverage K]
    simpa using Precoverage.generate_mem_toGrothendieck h𝒰
  · simpa [Coverage.toGrothendieck_toPrecoverage] using Precoverage.toGrothendieck_mono hK

end Coverage

end CategoryTheory
