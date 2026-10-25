module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.Sheaves.Forget
public import Mathlib.Topology.Sheaves.LocalPredicate
@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace Limits

noncomputable section

/- Domain-style sampling for Example 6.9.3:
- primary domain: sheaves of continuous real-valued functions on a topological space, with the
  source-facing object carried as a presheaf of `ℝ`-algebras;
- sampled owner declarations:
  `TopCat.presheafToTop`,
  `TopCat.sheafToTop`,
  `TopCat.Presheaf.isSheaf_iff_isSheaf_comp`,
  `TopCat.Hom.equivContinuousMap`;
- owner abstraction: the `CommAlgCat ℝ`-valued presheaf of continuous real-valued functions on
  opens of `X`;
- primitive data: the section object `C(U, ℝ)` on each open `U` and the restriction maps given by
  precomposition via `ContinuousMap.compRightAlgHom`;
- derived API: the bridge to the canonical `Type`-valued owner of continuous maps, the sheaf
  proof, and the packaged sheaf.

Source/core/bridge triage:
- `source-facing`: `continuousRealFunctionsPresheaf X`, the presheaf of continuous real-valued
  functions viewed as `ℝ`-algebras;
- `core/canonical`: the mathlib owner `TopCat.presheafToTop X (TopCat.of ℝ)` together with the
  sheaf `TopCat.sheafToTop (TopCat.of ℝ)`;
- `bridge/view`: `continuousRealFunctionsPresheafForgetToTypesIso X`, identifying the underlying
  set-valued presheaf of the `ℝ`-algebra owner with the canonical `TopCat`-valued owner.
-/

/-- Helper for Example 6.9.3: the forgetful functor from `ℝ`-algebras to types preserves limits,
so the sheaf condition can be checked after forgetting the algebra structure. -/
private instance : PreservesLimits (forget (CommAlgCat.{0} ℝ)) := by
  -- Reduce the needed preservation statement to the standard chain of forgetful functors.
  simpa using
    (inferInstance :
      PreservesLimits ((commAlgCatEquivUnder (CommRingCat.of ℝ)).functor ⋙
        Under.forget (CommRingCat.of ℝ) ⋙ forget CommRingCat))

/-- The presheaf on `X` sending an open set `U` to the `ℝ`-algebra `C⁰(U, ℝ)` of continuous
real-valued functions, with restriction maps given by precomposition. -/
def continuousRealFunctionsPresheaf (X : TopCat.{0}) : TopCat.Presheaf (CommAlgCat.{0} ℝ) X where
  obj U := CommAlgCat.of ℝ C(U.unop, ℝ)
  map {U V} i := CommAlgCat.ofHom <|
    ContinuousMap.compRightAlgHom ℝ ℝ (((Opens.toTopCat X).map i.unop).hom)
  map_id U := by
    ext f
    rfl
  map_comp i j := by
    ext f
    rfl

/-- Forgetting the `ℝ`-algebra structure on `continuousRealFunctionsPresheaf X` recovers the
canonical type-valued presheaf of continuous maps into `ℝ`. -/
def continuousRealFunctionsPresheafForgetToTypesIso (X : TopCat.{0}) :
    continuousRealFunctionsPresheaf X ⋙ forget (CommAlgCat.{0} ℝ) ≅
      TopCat.presheafToTop X (TopCat.of ℝ) :=
  NatIso.ofComponents
    (fun U ↦
      (TopCat.Hom.equivContinuousMap ((Opens.toTopCat X).obj U.unop) (TopCat.of ℝ)).symm.toIso)
    fun {_ _} i ↦ by
      ext f
      rfl

/-- Example 6.9.3: the presheaf `U ↦ C⁰(U, ℝ)` of continuous real-valued functions on `X`,
viewed as a presheaf of `ℝ`-algebras, satisfies the sheaf condition. -/
theorem continuous_real_functions_presheaf_isSheaf (X : TopCat.{0}) :
    (continuousRealFunctionsPresheaf X).IsSheaf := by
  -- Check the sheaf condition after forgetting to the underlying type-valued presheaf.
  apply (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget (CommAlgCat.{0} ℝ)) _).2
  -- Transport the canonical sheaf of continuous maps along the comparison isomorphism.
  exact TopCat.Presheaf.isSheaf_of_iso (continuousRealFunctionsPresheafForgetToTypesIso X).symm
    (TopCat.sheafToTop (TopCat.of ℝ)).2

/-- The sheaf of continuous real-valued functions on `X`, carried as a sheaf of `ℝ`-algebras. -/
abbrev continuousRealFunctionsSheaf (X : TopCat.{0}) : TopCat.Sheaf (CommAlgCat.{0} ℝ) X :=
  ⟨continuousRealFunctionsPresheaf X, continuous_real_functions_presheaf_isSheaf X⟩
