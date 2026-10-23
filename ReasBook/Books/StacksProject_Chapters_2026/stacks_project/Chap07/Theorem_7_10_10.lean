module

public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import Mathlib.CategoryTheory.Sites.Plus
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Tactic.Recall
public import stacks_project.Chap07.Definition_7_3_1

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.
-- Route correction: the previous local `PlusNotation` shim is unavailable in this item-per-file
-- target, so we use the canonical owner notation-free form `J.plusObj ℱ` directly.

open CategoryTheory Opposite
open GrothendieckTopology Plus

universe v u

section

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable (ℱ : Cᵒᵖ ⥤ Type (max u v))

/-- Helper for Theorem 7.10.10: a separated presheaf is injective against any covering family of
restrictions. -/
private theorem eq_of_restrict_eq_of_isSeparated (hℱ : Presieve.IsSeparated J ℱ) :
    ∀ ⦃X : C⦄ (S : J.Cover X) (x y : ℱ.obj (op X)),
      (∀ I : S.Arrow, ℱ.map I.f.op x = ℱ.map I.f.op y) → x = y := by
  -- Turn the covering family into the sieve-level separatedness predicate supplied by `hℱ`.
  intro X S x y hxy
  exact (hℱ S S.condition).ext fun Y f hf ↦ hxy ⟨Y, f, hf⟩

-- Proof sketch: use the explicit separatedness criterion proved by `Plus.sep`, which exactly
-- says that two sections of `J.plusObj ℱ`
-- agreeing after restriction to a covering must already be equal.
/-- Theorem 7.10.10 (1): the plus construction `J.plusObj ℱ` of a presheaf of sets is
separated. -/
theorem plusObj_isSeparated :
    Presieve.IsSeparated J (J.plusObj ℱ) := by
  -- `Plus.sep` is the packaged common-refinement argument from the source proof.
  intro U S hS x t₁ t₂ ht₁ ht₂
  exact Plus.sep ℱ ⟨S, hS⟩ t₁ t₂ fun I ↦ (ht₁ I.f I.hf).trans (ht₂ I.f I.hf).symm

-- Proof sketch: unpack `Presieve.IsSeparated J ℱ` into the coverwise injectivity hypothesis used
-- by `Plus.isSheaf_of_sep`, and then apply that theorem directly.
/-- Theorem 7.10.10 (2), first assertion: if `ℱ` is separated, then `J.plusObj ℱ` is a sheaf. -/
theorem plusObj_isSheaf_of_isSeparated (hℱ : Presieve.IsSeparated J ℱ) :
    Presheaf.IsSheaf J (J.plusObj ℱ) := by
  -- Feed the bridge lemma into the owner theorem implementing the gluing argument.
  exact Plus.isSheaf_of_sep ℱ (eq_of_restrict_eq_of_isSeparated J ℱ hℱ)

-- Proof sketch: `Plus.inj_of_sep` gives the objectwise injectivity statement for `J.toPlus ℱ`
-- once we feed it the coverwise separatedness condition coming directly from `hℱ`.
/-- Theorem 7.10.10 (2), second assertion: if `ℱ` is separated, then the canonical map
`ℱ ⟶ J.plusObj ℱ` is injective in the sense of Definition 7.3.1. -/
theorem toPlus_injective_of_isSeparated (hℱ : Presieve.IsSeparated J ℱ) :
    ∀ U : C, Function.Injective ((J.toPlus ℱ).app (op U)) := by
  -- This is exactly the objectwise injectivity statement owned by `Plus.inj_of_sep`.
  exact Plus.inj_of_sep ℱ (eq_of_restrict_eq_of_isSeparated J ℱ hℱ)

-- Proof sketch: Definition 7.3.1 already identifies the objectwise injectivity statement with the
-- canonical owner `Mono`.
/-- Companion to Theorem 7.10.10 (2): if `ℱ` is separated, then the canonical map
`ℱ ⟶ J.plusObj ℱ` is a monomorphism of presheaves. -/
theorem toPlus_mono_of_isSeparated (hℱ : Presieve.IsSeparated J ℱ) :
    Mono (J.toPlus ℱ) := by
  -- Translate the objectwise injectivity result into the categorical monomorphism criterion.
  exact (Presheaf.mono_iff_injective (J.toPlus ℱ)).2
    (toPlus_injective_of_isSeparated J ℱ hℱ)

/- Theorem 7.10.10 (3): if `ℱ` is already a sheaf, then the canonical map `ℱ ⟶ J.plusObj ℱ` is an
isomorphism. This is exactly the canonical owner theorem
`GrothendieckTopology.isIso_toPlus_of_isSheaf`. -/
recall GrothendieckTopology.isIso_toPlus_of_isSheaf

/- Theorem 7.10.10 (4): the iterated plus construction `J.plusObj (J.plusObj ℱ)` is always a
sheaf. This is exactly the canonical owner theorem
`GrothendieckTopology.Plus.isSheaf_plus_plus`. -/
recall GrothendieckTopology.Plus.isSheaf_plus_plus

end
