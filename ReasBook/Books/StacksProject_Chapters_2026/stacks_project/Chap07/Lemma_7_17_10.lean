module

public import stacks_project.Chap07.Lemma_7_17_10.Comparison

@[expose] public section

set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

open CategoryTheory Limits Opposite
open CategoryTheory.GrothendieckTopology

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {K : Precoverage C}
variable [K.HasPullbacks] [K.IsStableUnderBaseChange]
variable [HasWeakSheafify K.toCoverage.toGrothendieck (Type (max u v))]

local notation "J" => K.toCoverage.toGrothendieck

section

variable (β : Ordinal.{max u v}) (F : Set.Iio β ⥤ Sheaf K.toCoverage.toGrothendieck (Type (max u v)))
variable (hcover : ∀ (U : C) (R : Presieve U),
  R ∈ K U → Cardinal.lift (Cardinal.mk R.uncurry) < β.cof)

include F

include hcover

/-- Under the small-cover cofinality hypothesis of Lemma 7.17.10, the canonical comparison map is
injective. This is the injective half of the source-facing bijectivity statement for the canonical
owner map `colimit.post`. -/
theorem sheafFilteredColimitSectionsComparison_injective_of_coveringPresieveCardinal_lt_cof
    (U : C) :
    Function.Injective
      (colimit.post F ((sheafSections J (Type (max u v))).obj (op U))) := by
  -- The comparison map is an isomorphism once the presheaf colimit is known to be a sheaf.
  haveI : IsIso (colimit.post F ((sheafSections J (Type (max u v))).obj (op U))) :=
    comparison_isIso_of_coveringPresieveCardinal_lt_cof β F hcover U
  exact
    (ConcreteCategory.bijective_of_isIso
      (colimit.post F ((sheafSections J (Type (max u v))).obj (op U)))).1

/-- Under the small-cover cofinality hypothesis of Lemma 7.17.10, the canonical comparison map is
surjective. This is the surjective half of the source-facing bijectivity statement for the
canonical owner map `colimit.post`. -/
theorem sheafFilteredColimitSectionsComparison_surjective_of_coveringPresieveCardinal_lt_cof
    (U : C) :
    Function.Surjective
      (colimit.post F ((sheafSections J (Type (max u v))).obj (op U))) := by
  -- The same isomorphism gives the surjective half immediately.
  haveI : IsIso (colimit.post F ((sheafSections J (Type (max u v))).obj (op U))) :=
    comparison_isIso_of_coveringPresieveCardinal_lt_cof β F hcover U
  exact
    (ConcreteCategory.bijective_of_isIso
      (colimit.post F ((sheafSections J (Type (max u v))).obj (op U)))).2

/-- Lemma 7.17.10: let `K` be a chosen precoverage presenting a site on `C`, with site-local
pullbacks and base-change stability. If the cofinality of `β` dominates the cardinality of every
`K`-covering presieve of each object `U`, then for every `U` the canonical map from the filtered
colimit of the section sets `F i (U)` to the section set of the colimit sheaf is bijective. -/
theorem sheafFilteredColimitSectionsComparison_bijective_of_coveringPresieveCardinal_lt_cof
    (U : C) :
    Function.Bijective
      (colimit.post F ((sheafSections J (Type (max u v))).obj (op U))) :=
  ⟨sheafFilteredColimitSectionsComparison_injective_of_coveringPresieveCardinal_lt_cof
      β F hcover U,
    sheafFilteredColimitSectionsComparison_surjective_of_coveringPresieveCardinal_lt_cof
      β F hcover U⟩


end

end CategoryTheory
