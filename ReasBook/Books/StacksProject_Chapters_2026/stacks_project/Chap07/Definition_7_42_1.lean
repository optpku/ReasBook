module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Lemma_7_12_4

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits

universe u v

namespace CategoryTheory.GrothendieckTopology

open scoped SheafifiedRepresentable

variable {C : Type u} [Category.{v} C]

/-
Domain-style sampling for Definition 7.42.1:
- primary domain: sheafified representables in the topos `Sh(C, J)` and initial objects there;
- sampled owner declarations:
  `GrothendieckTopology.sheafifiedRepresentable`,
  `CategoryTheory.GrothendieckTopology.SheafifiedRepresentable.h[_]^#[_]`,
  `CategoryTheory.Limits.IsInitial`,
  `CategoryTheory.Limits.IsInitial.ofIso`;
- best owner abstraction: the canonical sheaf object `h[U]^#[J]` together with the initial-object
  owner `IsInitial`;
- primitive data: only the site `(C, J)` and the object `U : C`;
- derived API: any equivalence with the canonical map `∅^# ⟶ h[U]^#[J]` being an isomorphism or
  with bottom-sieve covering belongs downstream, not in this owner file.

Source/core/bridge triage:
- `source-facing`: the Stacks Project predicate that `U` is sheaf theoretically empty;
- `core/canonical`: the witness-valued owner `IsInitial (h[U]^#[J])`;
- `bridge/view`: later reformulations via unique sections and the bottom covering sieve.

Because `IsInitial` is witness-valued rather than `Prop`-valued, this file keeps only the
source-facing existence predicate and does not introduce any extra wrapper data around the
canonical owner.
-/
/-- Definition 7.42.1: an object `U` of a site `(C, J)` is sheaf theoretically empty if the
sheafified representable `h_U^#`, written canonically elsewhere as `h[U]^#[J]`, is initial in the
sheaf category. Since mathlib's canonical owner `IsInitial` is witness-valued rather than
`Prop`-valued, the source-facing predicate is exactly the proposition that such a witness exists,
with no extra package data beyond that canonical witness. This is equivalent to the source
formulation that the canonical morphism `∅^# ⟶ h_U^#` is an isomorphism. -/
def IsSheafTheoreticallyEmpty (J : GrothendieckTopology C) (U : C) : Prop :=
  Nonempty (IsInitial h[U]^#[J])

namespace IsSheafTheoreticallyEmpty

-- Proof sketch: unfold `J.IsSheafTheoreticallyEmpty U`; it is definitionally the proposition that
-- the sheafified representable `h[U]^#[J]` admits an `IsInitial` witness.
/-- A sheaf theoretically empty object has an initial sheafified representable witness. -/
theorem nonempty_isInitial {J : GrothendieckTopology C} {U : C}
    (hU : J.IsSheafTheoreticallyEmpty U) :
    Nonempty (IsInitial h[U]^#[J]) := by
  -- Unfolding the definition identifies the hypothesis with the target witness proposition.
  simpa [GrothendieckTopology.IsSheafTheoreticallyEmpty] using hU

end IsSheafTheoreticallyEmpty

end CategoryTheory.GrothendieckTopology
