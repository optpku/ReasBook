module

public import Mathlib.CategoryTheory.Filtered.FinallySmall
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Presentable.Directed
import Mathlib.Tactic.Recall
@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe w v u

namespace CategoryTheory

variable {𝓘 : Type u} [Category.{v} 𝓘]

/- Domain-style sampling for Lemma 4.21.5:
- primary domain: filtered/cofiltered diagram comparison via final and initial functors, together
  with directed-poset presentations of filtered categories;
- sampled owner API:
  `FinallySmall.exists_of_isFiltered`,
  `IsFiltered.exists_directed`,
  `IsDirectedOrder`,
  `Functor.Final.hasColimit_of_comp`,
  `Functor.Final.colimit_pre_isIso`,
  `Functor.Initial.hasLimit_of_comp`,
  `Functor.Initial.limit_pre_isIso`;
- owner abstraction: the canonical small filtered approximation theorem
  `FinallySmall.exists_of_isFiltered` for a filtered finally small category, together with
  transport of colimits and limits along final and initial functors;
- primitive data: a filtered category together with the finally-small owner structure needed to
  produce a small filtered category mapping finally into it;
- derived API: the directed-set presentation obtained from the small filtered model, expressed
  using the canonical owner class `IsDirectedOrder`, and the colimit/limit transfer and
  comparison isomorphisms induced by the resulting final functor. -/

/- Source/core/bridge triage for Lemma 4.21.5:
- `source-facing`: `exists_final_from_directed`, giving a directed-set presentation for a
  filtered category without collapsing the statement to the small-category theorem;
- `core/canonical`: `FinallySmall.exists_of_isFiltered`, `IsFiltered.exists_directed`,
  `Functor.Final.hasColimit_of_comp`,
  `Functor.Final.colimit_pre_isIso`, `Functor.Initial.hasLimit_of_comp`, and
  `Functor.Initial.limit_pre_isIso`;
- `bridge/view`: compose the final functor from a directed poset to the small filtered category
  produced by `FinallySmall.exists_of_isFiltered` with the final functor from that category to the
  original category; the limit half is the opposite-side initial-functor view of the same
  comparison. -/

/-- Helper for Lemma 4.21.5: a final functor out of a small filtered category transports the
directed-poset presentation produced by `IsFiltered.exists_directed` to the target category. -/
lemma exists_final_from_directed_of_final {J : Type w} [SmallCategory J] [IsFiltered J]
    (y : J ⥤ 𝓘) [y.Final] :
    ∃ (I : Type w) (_ : PartialOrder I) (_ : Nonempty I) (_ : IsDirectedOrder I)
      (x : I ⥤ 𝓘), x.Final := by
  -- First replace the small filtered source category by its canonical directed-poset model.
  obtain ⟨I, hIord, hIdir, hInonempty, x, hx⟩ := IsFiltered.exists_directed J
  let _ : PartialOrder I := hIord
  let _ : Nonempty I := hInonempty
  let _ : IsDirectedOrder I := hIdir
  let _ : x.Final := hx
  -- Then compose the two final functors to obtain the directed presentation of the target.
  exact ⟨I, inferInstance, inferInstance, inferInstance, x ⋙ y, inferInstance⟩

/-- Lemma 4.21.5: a filtered, locally small, finally small category admits a final functor from a
nonempty directed partially ordered set. This keeps the source-facing statement at the general
category level, while expressing directedness through the canonical owner class
`IsDirectedOrder` from Definition 4.21.1 and using the owner theorems
`FinallySmall.exists_of_isFiltered` and `IsFiltered.exists_directed` only to build the canonical
bridge to a directed poset. -/
theorem exists_final_from_directed (𝓘 : Type u) [Category.{v} 𝓘] [IsFiltered 𝓘]
    [LocallySmall.{w} 𝓘] [FinallySmall.{w} 𝓘] :
    ∃ (I : Type w) (_ : PartialOrder I) (_ : Nonempty I) (_ : IsDirectedOrder I)
      (x : I ⥤ 𝓘), x.Final := by
  -- First pass to the canonical small filtered model supplied by final smallness.
  obtain ⟨J, hJ, hJfilt, y, hy⟩ := FinallySmall.exists_of_isFiltered.{w} 𝓘
  let _ : SmallCategory J := hJ
  let _ : IsFiltered J := hJfilt
  let _ : y.Final := hy
  -- The helper packages the directed presentation of the small model and the final composition.
  exact exists_final_from_directed_of_final y

/- Small-model core used in the proof of `exists_final_from_directed`: for a small filtered
category, the directed-set presentation is exactly `IsFiltered.exists_directed`. -/
recall IsFiltered.exists_directed

/- Lemma 4.21.5 (1): if `x : I ⥤ 𝓘` is final, then any colimit of `x ⋙ M` induces a colimit of
`M`. This is exactly the canonical theorem `Functor.Final.hasColimit_of_comp`. -/
recall Functor.Final.hasColimit_of_comp

/- Lemma 4.21.5 (1), comparison morphism: for a final functor `x : I ⥤ 𝓘`, the canonical map
`colimit.pre M x` is an isomorphism whenever `M` has a colimit. This is exactly the canonical
instance `Functor.Final.colimit_pre_isIso`. -/
recall Functor.Final.colimit_pre_isIso

/- Lemma 4.21.5 (2): dually, if `x : I ⥤ 𝓘` is final, then any limit of `x.op ⋙ M` induces a
limit of `M`. This is exactly the canonical theorem `Functor.Initial.hasLimit_of_comp`. -/
recall Functor.Initial.hasLimit_of_comp

/- Lemma 4.21.5 (2), comparison morphism: for a final functor `x : I ⥤ 𝓘`, the canonical map
`limit.pre M x.op` is an isomorphism whenever `M` has a limit. This is exactly the canonical
instance `Functor.Initial.limit_pre_isIso`. -/
recall Functor.Initial.limit_pre_isIso

end CategoryTheory
