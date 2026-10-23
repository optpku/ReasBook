module

public import Mathlib.Topology.Sheaves.AddCommGrpCat
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Tactic.Recall
public import stacks_project.Chap06.Lemma_6_15_2
public import stacks_project.Chap06.Lemma_6_32_4

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open TopCat
open TopologicalSpace

noncomputable section

universe u

/-- Helper for Lemma 6.32.3: in `AddCommGrpCat`, the unique map to the terminal object is an
isomorphism exactly when the source object is zero. -/
private theorem addCommGrpCat_isIso_terminal_from_iff_isZero (A : AddCommGrpCat.{u}) :
    IsIso (terminal.from A) ↔ IsZero A := by
  -- Rewrite the terminal morphism to the zero morphism so the standard zero-map criterion applies.
  have h :
      terminal.from A = (0 : A ⟶ ⊤_ AddCommGrpCat.{u}) := by
    simpa using
      (terminalIsTerminal.isZero).eq_of_tgt
        (terminal.from A) (0 : A ⟶ ⊤_ AddCommGrpCat.{u})
  -- After that rewrite, being an isomorphism is equivalent to both source and target being zero.
  rw [h, isIsoZero_iff_source_target_isZero]
  constructor
  · rintro ⟨hA, _⟩
    exact hA
  · intro hA
    exact ⟨hA, terminalIsTerminal.isZero⟩

section

variable {X : TopCat.{u}} {Z : Set X}

/- Domain-style sampling for Lemma 6.32.3:
- primary domain: sheaf pushforward along the inclusion of a closed subset in `TopCat`;
- sampled owner API:
  `TopCat.subsetInclusion`,
  `subsetSheafPushforward_fullyFaithful`,
  `closedSubsetSheafPushforward_essImage_iff_stalk_isTerminal_of_not_mem`,
  `IsTerminal.isZero`,
  `isIsoZero_iff_source_target_isZero`;
- `source-facing`: the abelian-sheaf reformulation in terms of zero stalks away from `Z`;
- `core/canonical`: the algebraic-structure pushforward owner theorem from Lemma 6.32.4;
- `bridge/view`: rewriting terminal stalks as zero objects.

Primitive data are only the closed subset `Z`, its canonical inclusion
`TopCat.subsetInclusion X Z`, and the sheaf `ℱ`. The fully faithful statement is already owned
upstream at the subset level, so this file keeps only the source-facing zero-stalk criterion as
new API. -/

local notation "iZ" => X.closedSubsetInclusion Z

/- Full-faithfulness of `i_* : Ab(Z) ⥤ Ab(X)` (closed inclusion) — the first half of Stacks 00AG.
The owner is `subsetSheafPushforward_fullyFaithful` (in `ClosedSubsetInclusion`), the `AddCommGrpCat`
specialization being immediate; it is built as the right adjoint of the pullback–pushforward
adjunction with invertible counit. The `FullyFaithful` datum is sorry-free (the counit-iso `Prop`
`subsetSheafPushforward_counit_isIso` is currently deferred). This file owns the essential-image
half (below). -/
recall subsetSheafPushforward_fullyFaithful

-- Proof sketch: Lemma 6.32.4 characterizes the essential image by terminal stalks outside `Z`,
-- and in `AddCommGrpCat` terminal objects are exactly zero objects.
/-- Lemma 6.32.3: a sheaf of abelian groups on `X` lies in the essential image of pushforward
from a closed subset `Z ⊆ X` if and only if all of its stalks at points of `X \setminus Z` are
zero. -/
theorem closedSubsetAbelianSheafPushforward_essImage_iff_stalk_isZero_of_not_mem
    (hZ : IsClosed Z) (ℱ : X.Sheaf AddCommGrpCat.{u}) :
    (Sheaf.pushforward AddCommGrpCat.{u} iZ).essImage ℱ ↔
      ∀ x : X, x ∉ Z → IsZero (ℱ.presheaf.stalk x) := by
  -- Specialize the imported closed-subset criterion and translate terminal stalks into zero stalks.
  simpa [addCommGrpCat_isIso_terminal_from_iff_isZero] using
    (closedSubsetSheafPushforward_essImage_iff_stalk_isTerminal_of_not_mem Z hZ ℱ)

end
